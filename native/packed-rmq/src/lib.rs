//! Native frontends to the proved Lean execution core.
//! `native` loads binary images and executes checked byte-limb words.
//! The older textual route remains available for its recorded experiment.
//! Compilation/runtime/FFI remain explicit assumptions. One initializing thread.
pub mod native;
use std::ffi::{CStr, CString};
use std::marker::PhantomData;
use std::os::raw::{c_char, c_void};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};

static RUNTIME_CLAIMED: AtomicBool = AtomicBool::new(false);

#[cfg(not(all(windows, target_env = "msvc", target_arch = "x86_64")))]
compile_error!("The route experiment currently supports Windows x64 MSVC Rust only.");

#[link(name = "packed_route", kind = "raw-dylib")]
extern "C" {
    fn packed_route_init() -> i32;
    fn packed_route_eval(program: *const c_char, program_len: usize,
        fixture: *const c_char, fixture_len: usize, reads: u8) -> *mut c_void;
    fn packed_route_text(result: *mut c_void) -> *const c_char;
    fn packed_route_free(result: *mut c_void);
}

/// Not Send or Sync: the experiment keeps Lean on the initializing OS thread.
pub struct RouteRuntime { _thread: PhantomData<Rc<()>> }

impl RouteRuntime {
    pub fn new() -> Result<Self, String> {
        if RUNTIME_CLAIMED.compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire).is_err() {
            return Err("one route runtime per process".into());
        }
        // C owns the process-lifetime runtime; calls are serialized by the API contract.
        if unsafe { packed_route_init() } != 0 { return Err("Lean initialization failed".into()); }
        Ok(Self { _thread: PhantomData })
    }

    pub fn evaluate(&mut self, program: &str, fixture: &str, observe_reads: bool) -> Result<String, String> {
        if program.len() > 50_000_000 || fixture.len() > 1_000_000 {
            return Err("text size limit".into());
        }
        let p = CString::new(program).map_err(|_| "program contains NUL")?;
        let f = CString::new(fixture).map_err(|_| "fixture contains NUL")?;
        // C copies arguments into Lean-owned strings and returns an owned Lean string handle.
        let output = unsafe { packed_route_eval(p.as_ptr(), p.as_bytes().len(),
            f.as_ptr(), f.as_bytes().len(), u8::from(observe_reads)) };
        if output.is_null() { return Err("native bridge failure".into()); }
        let text = unsafe { CStr::from_ptr(packed_route_text(output)) }.to_str().map(str::to_owned)
            .map_err(|_| "non-UTF8 native result".to_owned());
        unsafe { packed_route_free(output) };
        text
    }
}
