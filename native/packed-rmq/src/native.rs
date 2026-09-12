//! ABI 1 frontend for the proved binary loader and byte-limb executor.
//! The computational core is generated from Lean. This module only marshals
//! byte spans, owns handles and copies result text on the initializing thread.
use std::ffi::CStr;
use std::marker::PhantomData;
use std::os::raw::{c_char, c_void};
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::atomic::Ordering;
use super::RUNTIME_CLAIMED;

pub const MAX_IMAGE_BYTES: usize = 134_217_728;
pub const MAX_ENDPOINT_BYTES: usize = 512;
pub const MAX_FUEL: usize = 1_000_000;
pub const QUERY_FUEL: usize = 837_572;

#[link(name = "packed_rmq", kind = "raw-dylib")]
extern "C" {
    fn packed_rmq_init() -> i32;
    fn packed_rmq_load(bytes: *const u8, length: usize) -> *mut c_void;
    fn packed_rmq_load_status(result: *const c_void) -> i32;
    fn packed_rmq_load_error(result: *const c_void) -> *const c_char;
    fn packed_rmq_loaded_image(result: *const c_void) -> *const c_void;
    fn packed_rmq_word_bytes(image: *const c_void) -> usize;
    fn packed_rmq_load_free(result: *mut c_void);
    fn packed_rmq_query(image: *const c_void, left: *const u8, left_length: usize,
        right: *const u8, right_length: usize, fuel: usize, reads: u8) -> *mut c_void;
    fn packed_rmq_query_status(result: *const c_void) -> i32;
    fn packed_rmq_query_text(result: *const c_void) -> *const c_char;
    fn packed_rmq_query_free(result: *mut c_void);
}

/// One process-lifetime Lean runtime. Neither Send nor Sync. The shared atomic
/// also prevents mixing this API with the older textual route in one process.
pub struct NativeRuntime { _thread: PhantomData<Rc<()>> }

impl NativeRuntime {
    pub fn new() -> Result<Self, String> {
        if RUNTIME_CLAIMED.compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire).is_err() {
            return Err("one Lean runtime per process".into());
        }
        if unsafe { packed_rmq_init() } != 0 {
            return Err("Lean initialization failed".into());
        }
        Ok(Self { _thread: PhantomData })
    }

    /// Validates and retains the exact binary image once. The image borrows this
    /// runtime and owns its load result; caller bytes may be released immediately.
    pub fn load<'runtime>(&'runtime self, bytes: &[u8]) -> Result<NativeImage<'runtime>, String> {
        if bytes.len() > MAX_IMAGE_BYTES { return Err("image byte limit".into()); }
        let pointer = NonNull::new(unsafe { packed_rmq_load(bytes.as_ptr(), bytes.len()) })
            .ok_or_else(|| "native load bridge failure".to_owned())?;
        let owner = LoadOwner(pointer);
        if unsafe { packed_rmq_load_status(pointer.as_ptr()) } != 0 {
            return Err(copy_text(unsafe { packed_rmq_load_error(pointer.as_ptr()) })?);
        }
        if unsafe { packed_rmq_loaded_image(pointer.as_ptr()) }.is_null() {
            return Err("native image handle missing".into());
        }
        Ok(NativeImage { owner, _runtime: self })
    }
}

struct LoadOwner(NonNull<c_void>);
impl Drop for LoadOwner {
    fn drop(&mut self) { unsafe { packed_rmq_load_free(self.0.as_ptr()) }; }
}
struct QueryOwner(NonNull<c_void>);
impl Drop for QueryOwner {
    fn drop(&mut self) { unsafe { packed_rmq_query_free(self.0.as_ptr()) }; }
}

fn copy_text(pointer: *const c_char) -> Result<String, String> {
    if pointer.is_null() { return Err("native text handle missing".into()); }
    unsafe { CStr::from_ptr(pointer) }.to_str().map(str::to_owned)
        .map_err(|_| "non-UTF8 native result".to_owned())
}

/// Retains an immutable loaded store. `query` serializes calls through a mutable
/// borrow. The runtime reference keeps this object on its initializing thread.
pub struct NativeImage<'runtime> {
    owner: LoadOwner,
    _runtime: &'runtime NativeRuntime,
}

impl NativeImage<'_> {
    pub fn word_bytes(&self) -> usize {
        unsafe { packed_rmq_word_bytes(packed_rmq_loaded_image(self.owner.0.as_ptr())) }
    }

    /// Canonical little-endian endpoint bytes must have exactly ceil(width/8)
    /// bytes and zero high padding. Validation occurs inside the proved core.
    /// Default query fuel is QUERY_FUEL; reads=false omits read observation logs.
    /// Successful execution may report running, halted, or a checked machine fault.
    pub fn query(&mut self, left: &[u8], right: &[u8], fuel: usize,
        observe_reads: bool) -> Result<String, String> {
        if left.len() > MAX_ENDPOINT_BYTES || right.len() > MAX_ENDPOINT_BYTES || fuel > MAX_FUEL {
            return Err("query host limit".into());
        }
        let image = unsafe { packed_rmq_loaded_image(self.owner.0.as_ptr()) };
        let pointer = NonNull::new(unsafe { packed_rmq_query(image,
            left.as_ptr(), left.len(), right.as_ptr(), right.len(), fuel, u8::from(observe_reads)) })
            .ok_or_else(|| "native query bridge failure".to_owned())?;
        let _owner = QueryOwner(pointer);
        let text = copy_text(unsafe { packed_rmq_query_text(pointer.as_ptr()) })?;
        match unsafe { packed_rmq_query_status(pointer.as_ptr()) } {
            0 => Ok(text),
            1 => Err(text),
            _ => Err("invalid native query status".into()),
        }
    }
}
