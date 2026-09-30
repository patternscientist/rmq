//! Owned clients of the compiled Lean lifecycle ABI.
//!
//! Every live native object borrows the initializing runtime, and every type
//! holding such an object is neither `Send` nor `Sync`. Query transfer requires
//! `&mut Owner`; a failure after native take is represented by an empty owner.
//! Result buffers and optional observations are independently owned. Borrowed
//! bytes cannot outlive their result. No API exports a raw operational handle.
//!
//! ```compile_fail
//! use packed_rmq::lifecycle::LifecycleRuntime;
//! fn send<T: Send>() {}
//! send::<LifecycleRuntime>();
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::LifecycleRuntime;
//! fn sync<T: Sync>() {}
//! sync::<LifecycleRuntime>();
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Owner;
//! fn send<T: Send>() {}
//! send::<Owner<'static>>();
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Owner;
//! fn sync<T: Sync>() {}
//! sync::<Owner<'static>>();
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Observation;
//! fn send<T: Send>() {}
//! send::<Observation<'static>>();
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Observation;
//! fn sync<T: Sync>() {}
//! sync::<Observation<'static>>();
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Owner;
//! fn clone_owner(owner: &Owner<'_>) { let _ = Owner::clone(owner); }
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Owner;
//! fn immutable_query(owner: &Owner<'_>) { let _ = owner.query(&[], &[], false); }
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Natural;
//! fn escape_bytes<'a>(answer: Natural<'a>) -> &'a [u8] { answer.bytes() }
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::Owner;
//! fn alias(owner: &Owner<'_>) { let _ = owner.raw; }
//! ```
//! ```compile_fail
//! use packed_rmq::lifecycle::{LifecycleRuntime, Model, Owner};
//! fn escape_runtime() -> Owner<'static> {
//!     let runtime = LifecycleRuntime::new().unwrap();
//!     let bytes = runtime.profile(0).unwrap().endpoint(&[0]).unwrap();
//!     runtime.build_first(Model::Comparison, &[], &bytes, &bytes, false).unwrap().0
//! }
//! ```

use super::RUNTIME_CLAIMED;
use std::ffi::c_void;
use std::fmt;
use std::marker::PhantomData;
use std::ptr::{self, NonNull};
use std::rc::Rc;
use std::sync::atomic::Ordering;

pub const MAX_INPUT_COUNT: usize = 4096;
pub const MAX_MAGNITUDE_BYTES: usize = 4096;
pub const MAX_TOTAL_MAGNITUDE_BYTES: usize = 16_777_216;

#[repr(C)]
#[derive(Clone, Copy)]
struct Bytes { data: *const u8, size: usize }
impl Bytes { fn borrowed(bytes: &[u8]) -> Self { Self { data: bytes.as_ptr(), size: bytes.len() } } }

#[repr(C)]
struct ForeignInt { negative: u8, magnitude: Bytes }

#[link(name = "packed_rmq_lifecycle", kind = "raw-dylib")]
extern "C" {
    fn packed_lifecycle_init() -> i32;
    fn packed_lifecycle_profile(count: usize, width: *mut usize, bytes: *mut usize) -> i32;
    fn packed_lifecycle_build_first(model: u8, input: *const ForeignInt, count: usize,
        left: Bytes, right: Bytes, observe: u8, owner: *mut *mut c_void,
        answer: *mut *mut c_void, diagnostics: *mut *mut c_void) -> i32;
    fn packed_lifecycle_query(owner: *mut *mut c_void, left: Bytes, right: Bytes,
        observe: u8, answer: *mut *mut c_void, diagnostics: *mut *mut c_void) -> i32;
    fn packed_lifecycle_result_bytes(answer: *const c_void) -> Bytes;
    fn packed_lifecycle_result_free(answer: *mut c_void);
    fn packed_lifecycle_owner_free(owner: *mut *mut c_void);
    fn packed_lifecycle_observation_free(diagnostics: *mut c_void);
    fn packed_lifecycle_inspect(owner: *const c_void, info: *mut OwnerInfo) -> i32;
    fn packed_lifecycle_observation_counter(diagnostics: *const c_void,
        category: u8, value: *mut *mut c_void) -> i32;
    fn packed_lifecycle_observation_read_count(diagnostics: *const c_void, count: *mut usize) -> i32;
    fn packed_lifecycle_observation_read(diagnostics: *const c_void, index: usize,
        address: *mut *mut c_void, has_reply: *mut u8, reply: *mut *mut c_void) -> i32;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Format, InputDomain, Limit, Thread, Initialization, State, ModelFault,
    FuelExhausted, Allocation, ControlledFailure, RuntimeAlreadyClaimed,
    InvalidForeignResult, UnknownNative(i32),
}
impl Error {
    fn status(code: i32) -> Result<(), Self> {
        match code {
            0 => Ok(()), 1 => Err(Self::Format), 2 => Err(Self::InputDomain),
            3 => Err(Self::Limit), 4 => Err(Self::Thread), 5 => Err(Self::Initialization),
            6 => Err(Self::State), 7 => Err(Self::ModelFault), 8 => Err(Self::FuelExhausted),
            9 => Err(Self::Allocation), 10 => Err(Self::ControlledFailure),
            other => Err(Self::UnknownNative(other)),
        }
    }
}
impl fmt::Display for Error { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") } }
impl std::error::Error for Error {}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Model { Word = 0, Comparison = 1 }

/// Borrowed arbitrary-width sign/magnitude. High zero padding is permitted.
/// Constructors reject negative zero; no fixed-width host integer is involved.
#[derive(Clone, Copy, Debug)]
pub struct SignedInteger<'input> { negative: bool, magnitude: &'input [u8] }
impl<'input> SignedInteger<'input> {
    pub fn new(negative: bool, magnitude: &'input [u8]) -> Result<Self, Error> {
        if magnitude.is_empty() { return Err(Error::Format); }
        if magnitude.len() > MAX_MAGNITUDE_BYTES { return Err(Error::Limit); }
        if negative && magnitude.iter().all(|byte| *byte == 0) { return Err(Error::Format); }
        Ok(Self { negative, magnitude })
    }
    pub fn is_negative(&self) -> bool { self.negative }
    pub fn magnitude(&self) -> &[u8] { self.magnitude }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile { width_bits: usize, width_bytes: usize }
impl Profile {
    pub fn width_bits(self) -> usize { self.width_bits }
    pub fn width_bytes(self) -> usize { self.width_bytes }

    /// Pads an unsigned little-endian magnitude to the exact endpoint width.
    /// Empty input denotes zero here; the resulting ABI span is nonempty.
    pub fn endpoint(self, magnitude: &[u8]) -> Result<Vec<u8>, Error> {
        if magnitude.get(self.width_bytes..).unwrap_or(&[]).iter().any(|b| *b != 0) {
            return Err(Error::Format);
        }
        let mut word = vec![0; self.width_bytes];
        let copied = magnitude.len().min(word.len());
        word[..copied].copy_from_slice(&magnitude[..copied]);
        let high_bits = self.width_bits % 8;
        if high_bits != 0 && word.last().copied().unwrap_or(0) >> high_bits != 0 {
            return Err(Error::Format);
        }
        Ok(word)
    }
}

/// Acquisition claims the crate-wide guard before invoking C and never clears
/// it, including initialization failure. The Lean runtime lives until exit, separate from model resources.
pub struct LifecycleRuntime { _thread: PhantomData<Rc<()>> }
impl LifecycleRuntime {
    pub fn new() -> Result<Self, Error> {
        if RUNTIME_CLAIMED.compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire).is_err() {
            return Err(Error::RuntimeAlreadyClaimed);
        }
        Error::status(unsafe { packed_lifecycle_init() })?;
        Ok(Self { _thread: PhantomData })
    }

    pub fn profile(&self, count: usize) -> Result<Profile, Error> {
        if count > MAX_INPUT_COUNT { return Err(Error::Limit); }
        let (mut width_bits, mut width_bytes) = (0, 0);
        Error::status(unsafe { packed_lifecycle_profile(count, &mut width_bits, &mut width_bytes) })?;
        if width_bits == 0 || width_bytes == 0 || width_bits.checked_add(7).map(|x| x / 8) != Some(width_bytes) {
            return Err(Error::InvalidForeignResult);
        }
        Ok(Profile { width_bits, width_bytes })
    }

    /// Executes the real first query. Input buffers are borrowed for this call
    /// and may be dropped as soon as it returns. Publication follows retirement
    /// and native repacking; no running builder can be obtained through this API.
    pub fn build_first<'runtime>(&'runtime self, model: Model, input: &[SignedInteger<'_>],
        left: &[u8], right: &[u8], observe: bool) -> Result<(Owner<'runtime>, QueryResult<'runtime>), Error> {
        if input.len() > MAX_INPUT_COUNT { return Err(Error::Limit); }
        let mut total = 0usize;
        for value in input {
            total = total.checked_add(value.magnitude.len()).ok_or(Error::Limit)?;
            if total > MAX_TOTAL_MAGNITUDE_BYTES { return Err(Error::Limit); }
        }
        let foreign: Vec<ForeignInt> = input.iter().map(|value| ForeignInt {
            negative: u8::from(value.negative), magnitude: Bytes::borrowed(value.magnitude),
        }).collect();
        let (mut raw, mut answer, mut diagnostics) = (ptr::null_mut(), ptr::null_mut(), ptr::null_mut());
        let status = unsafe { packed_lifecycle_build_first(model as u8, foreign.as_ptr(), foreign.len(),
            Bytes::borrowed(left), Bytes::borrowed(right), u8::from(observe),
            &mut raw, &mut answer, &mut diagnostics) };
        if let Err(error) = Error::status(status) {
            // The ABI promises empty outputs on rejection. Defensive cleanup
            // also owns any initialized foreign outputs if that promise fails.
            unsafe { release_outputs(&mut raw, answer, diagnostics); }
            return Err(error);
        }
        let owner = Owner { raw: NonNull::new(raw), runtime: self };
        if owner.raw.is_none() {
            unsafe { release_results(answer, diagnostics); }
            return Err(Error::InvalidForeignResult);
        }
        let result = unsafe { QueryResult::from_raw(self, answer, diagnostics, observe) }?;
        // An actual inspect also validates produced metadata before exposing it.
        owner.inspect()?;
        Ok((owner, result))
    }
}

unsafe fn release_results(answer: *mut c_void, diagnostics: *mut c_void) {
    if !answer.is_null() { packed_lifecycle_result_free(answer); }
    if !diagnostics.is_null() { packed_lifecycle_observation_free(diagnostics); }
}
unsafe fn release_outputs(owner: &mut *mut c_void, answer: *mut c_void, diagnostics: *mut c_void) {
    if !(*owner).is_null() { packed_lifecycle_owner_free(owner); }
    release_results(answer, diagnostics);
}

/// Owned arbitrary-width unsigned bytes. The native result object owns storage;
/// the view returned by `bytes` is tied to this object's borrow.
pub struct Natural<'runtime> {
    raw: NonNull<c_void>, view: Bytes, _runtime: &'runtime LifecycleRuntime,
}
impl<'runtime> Natural<'runtime> {
    unsafe fn from_raw(runtime: &'runtime LifecycleRuntime, raw: *mut c_void) -> Result<Self, Error> {
        let raw = NonNull::new(raw).ok_or(Error::InvalidForeignResult)?;
        let view = packed_lifecycle_result_bytes(raw.as_ptr());
        if view.data.is_null() || view.size == 0 || view.size > isize::MAX as usize {
            packed_lifecycle_result_free(raw.as_ptr());
            return Err(Error::InvalidForeignResult);
        }
        Ok(Self { raw, view, _runtime: runtime })
    }
    pub fn bytes(&self) -> &[u8] {
        // The C contract keeps this validated view live until result_free.
        unsafe { std::slice::from_raw_parts(self.view.data, self.view.size) }
    }
    pub fn is_zero(&self) -> bool { self.bytes().iter().all(|b| *b == 0) }
}
impl Drop for Natural<'_> { fn drop(&mut self) { unsafe { packed_lifecycle_result_free(self.raw.as_ptr()); } } }

pub struct QueryResult<'runtime> {
    pub answer: Natural<'runtime>,
    pub observation: Option<Observation<'runtime>>,
}
impl<'runtime> QueryResult<'runtime> {
    unsafe fn from_raw(runtime: &'runtime LifecycleRuntime, answer: *mut c_void,
        diagnostics: *mut c_void, observe: bool) -> Result<Self, Error> {
        let observation = NonNull::new(diagnostics).map(|raw| Observation { raw, runtime });
        if observation.is_some() != observe {
            if !answer.is_null() { packed_lifecycle_result_free(answer); }
            return Err(Error::InvalidForeignResult);
        }
        Ok(Self { answer: Natural::from_raw(runtime, answer)?, observation })
    }

    /// None packet is zero. A nonzero packet is index+1; subtraction works on
    /// byte limbs and never narrows through a host-sized integer.
    pub fn index_magnitude(&self) -> Option<Vec<u8>> {
        if self.answer.is_zero() { return None; }
        let mut bytes = self.answer.bytes().to_vec();
        for byte in &mut bytes {
            if *byte == 0 { *byte = 255; } else { *byte -= 1; break; }
        }
        while bytes.len() > 1 && bytes.last() == Some(&0) { bytes.pop(); }
        Some(bytes)
    }
}

/// A nullable private slot records post-take native failure. An empty owner
/// rejects subsequent calls and destruction is harmless. No Clone is supplied.
pub struct Owner<'runtime> { raw: Option<NonNull<c_void>>, runtime: &'runtime LifecycleRuntime }
impl<'runtime> Owner<'runtime> {
    pub fn is_live(&self) -> bool { self.raw.is_some() }
    pub fn query(&mut self, left: &[u8], right: &[u8], observe: bool) -> Result<QueryResult<'runtime>, Error> {
        let mut raw = self.raw.ok_or(Error::State)?.as_ptr();
        let (mut answer, mut diagnostics) = (ptr::null_mut(), ptr::null_mut());
        let status = unsafe { packed_lifecycle_query(&mut raw, Bytes::borrowed(left),
            Bytes::borrowed(right), u8::from(observe), &mut answer, &mut diagnostics) };
        self.raw = NonNull::new(raw);
        if let Err(error) = Error::status(status) {
            unsafe { release_results(answer, diagnostics); }
            return Err(error);
        }
        if self.raw.is_none() {
            unsafe { release_results(answer, diagnostics); }
            return Err(Error::InvalidForeignResult);
        }
        unsafe { QueryResult::from_raw(self.runtime, answer, diagnostics, observe) }
    }
    pub fn inspect(&self) -> Result<OwnerInfo, Error> {
        let mut info = OwnerInfo::default();
        let raw = self.raw.ok_or(Error::State)?;
        Error::status(unsafe { packed_lifecycle_inspect(raw.as_ptr(), &mut info) })?;
        Ok(info)
    }
    /// Profile is reconstructed from produced metadata, rather than cached input.
    pub fn profile(&self) -> Result<Profile, Error> {
        let info = self.inspect()?;
        let width_bytes = info.width_bits.checked_add(7).ok_or(Error::InvalidForeignResult)? / 8;
        if info.width_bits == 0 || width_bytes == 0 { return Err(Error::InvalidForeignResult); }
        Ok(Profile { width_bits: info.width_bits, width_bytes })
    }
}
impl Drop for Owner<'_> {
    fn drop(&mut self) {
        if let Some(raw) = self.raw.take() {
            let mut pointer = raw.as_ptr();
            unsafe { packed_lifecycle_owner_free(&mut pointer); }
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct ArrayInfo {
    pub initialized: usize, pub capacity: usize, pub requested_bytes: usize,
    /// Opaque receipt only; this is not a dereferenceable public handle.
    pub identity: usize,
}
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct OwnerInfo {
    pub count: usize, pub memory_extent: usize, pub width_bits: usize,
    pub arrays: [ArrayInfo; 4],
    pub reachable_objects: usize, pub scalar_occurrences: usize, pub boxed_integers: usize,
    pub runtime_reported_object_bytes: usize,
    pub repacked_arrays: usize, pub copied_entries: usize,
    pub exclusive_owner: u8, pub exact_capacities: u8, pub no_retained_operational_roots: u8,
    pub boxed_digit_requested_bytes: usize,
}

// Windows x64 ABI sizes, including the padding before the final size_t.
const _: [(); 32] = [(); std::mem::size_of::<ArrayInfo>()];
const _: [(); 216] = [(); std::mem::size_of::<OwnerInfo>()];
const _: [(); 8] = [(); std::mem::align_of::<OwnerInfo>()];

#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum Category {
    Read, Register, Arithmetic, Comparison, Branch, Control, Write, Allocation,
    KeyRead, OracleComparison, NumericRelease, KeyRelease, KeyRegisterRelease,
    RequestAdmission, ControlEntry, Steps,
}
pub struct Observation<'runtime> { raw: NonNull<c_void>, runtime: &'runtime LifecycleRuntime }
impl<'runtime> Observation<'runtime> {
    pub fn counter(&self, category: Category) -> Result<Natural<'runtime>, Error> {
        let mut value = ptr::null_mut();
        let status = unsafe { packed_lifecycle_observation_counter(self.raw.as_ptr(), category as u8, &mut value) };
        if let Err(error) = Error::status(status) {
            unsafe { release_results(value, ptr::null_mut()); }
            return Err(error);
        }
        unsafe { Natural::from_raw(self.runtime, value) }
    }
    pub fn read_count(&self) -> Result<usize, Error> {
        let mut count = 0;
        Error::status(unsafe { packed_lifecycle_observation_read_count(self.raw.as_ptr(), &mut count) })?;
        Ok(count)
    }
    pub fn read(&self, index: usize) -> Result<ReadReceipt<'runtime>, Error> {
        let (mut address, mut reply) = (ptr::null_mut(), ptr::null_mut());
        let mut has_reply = 0;
        let status = unsafe { packed_lifecycle_observation_read(self.raw.as_ptr(), index,
            &mut address, &mut has_reply, &mut reply) };
        if let Err(error) = Error::status(status) {
            unsafe { release_results(address, ptr::null_mut()); release_results(reply, ptr::null_mut()); }
            return Err(error);
        }
        if has_reply > 1 || (has_reply == 0 && !reply.is_null()) {
            unsafe { release_results(address, ptr::null_mut()); release_results(reply, ptr::null_mut()); }
            return Err(Error::InvalidForeignResult);
        }
        let address = match unsafe { Natural::from_raw(self.runtime, address) } {
            Ok(value) => value,
            Err(error) => {
                unsafe { release_results(reply, ptr::null_mut()); }
                return Err(error);
            }
        };
        let reply = if has_reply == 1 { Some(unsafe { Natural::from_raw(self.runtime, reply) }?) } else { None };
        Ok(ReadReceipt { address, reply })
    }
}
impl Drop for Observation<'_> {
    fn drop(&mut self) { unsafe { packed_lifecycle_observation_free(self.raw.as_ptr()); } }
}
pub struct ReadReceipt<'runtime> { pub address: Natural<'runtime>, pub reply: Option<Natural<'runtime>> }
