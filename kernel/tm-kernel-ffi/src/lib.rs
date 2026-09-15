//! The whole Rust surface of the Lean kernel: **one function, `String -> String`.**
//!
//! Nothing but a UTF-8 string crosses the boundary, so there is no marshalling
//! to get wrong, no `lean_object*` for Rust to hold, and no thread-safety
//! protocol to remember. The parser and the serializer live in the kernel, so
//! the UI hands over the text of every file and gets text back.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::sync::Once;

extern "C" {
    fn tm_kernel_init() -> i32;
    fn tm_kernel_call_c(req: *const c_char) -> *mut c_char;
    fn tm_kernel_free(p: *mut c_char);
}

/// **The kernel's identity** (stage 5 D9 W3, design §9.8): FNV-1a-64 of the static archive this crate links, as 16 hex
/// digits (`build.rs`). A replay cache written by another kernel is rebuilt once.
pub const KERNEL_ID: &str = env!("TM_KERNEL_ID");

static INIT: Once = Once::new();
static mut INIT_RC: i32 = -1;

/// The kernel faulted: it returned nothing, or something that is not a
/// response. A fault is loud and recoverable; it is never a wrong answer.
#[derive(Debug)]
pub enum KernelFault {
    InitFailed(i32),
    NulInRequest,
    NoResponse,
    NotUtf8,
}

/// Initialise the Lean runtime. Idempotent; measured at 0.6-2.0 ms, once.
pub fn init() -> Result<(), KernelFault> {
    INIT.call_once(|| unsafe { INIT_RC = tm_kernel_init() });
    match unsafe { INIT_RC } {
        0 => Ok(()),
        rc => Err(KernelFault::InitFailed(rc)),
    }
}

/// Apply a request to the kernel and return its response.
///
/// The request carries the raw text of every file plus the commands to apply;
/// the response carries the raw text of every file, or a structured error.
pub fn call(request: &str) -> Result<String, KernelFault> {
    init()?;
    let c = CString::new(request).map_err(|_| KernelFault::NulInRequest)?;
    let raw = unsafe { tm_kernel_call_c(c.as_ptr()) };
    if raw.is_null() {
        return Err(KernelFault::NoResponse);
    }
    let out = unsafe { CStr::from_ptr(raw) }
        .to_str()
        .map(|s| s.to_owned())
        .map_err(|_| KernelFault::NotUtf8);
    unsafe { tm_kernel_free(raw) };
    out
}
