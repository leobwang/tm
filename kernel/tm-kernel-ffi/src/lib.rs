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

/// **The per-verb kernel-call counter's env var** (stage 5, the instrument
/// design §14.6 asks for beside T11: "the per-verb kernel-call count against
/// R14's baseline table").
///
/// When it is set, every call through [`call`] writes one line to stderr:
/// `kernel call: <kind>`. It lives here, at the FFI, because this is the one
/// door — `tm/src/cli/kernel_bridge.rs` and `tm/src/cli/kernel_log.rs` each
/// reach the kernel on their own, so a counter in either would miss the other,
/// and a call site added later cannot forget this one.
///
/// **Before the switch the `log` count is 0 for every verb**, because nothing
/// under `tm/src` calls the kernel's `log` op yet; `tm/tests/kernel_call_counts.rs`
/// records that baseline and asserts it, so a half-switched binary fails a test
/// rather than being noticed later.
pub const TRACE_CALLS_ENV: &str = "TM_TRACE_KERNEL_CALLS";

/// Which kind of request this is, by the one literal each builder emits and no
/// other does: `"capacity":` (`kernel_capacity::request`), `"log":{`
/// (`kernel_log::request`), `"emit":[` (`kernel_log::render_values`, the writer
/// S2 added under **D16**), `"cmds":` (`kernel_bridge`'s apply). This crate may
/// depend on nothing (AGENTS R7), so it is a substring test and not a parse —
/// a *document line* containing one of these literals would be miscounted, which
/// is acceptable in a diagnostic that no answer depends on.
///
/// `emit` gets its own name rather than falling into `other` on purpose: after
/// S2 every appending verb makes one, so it is a per-verb cost the call-count
/// instrument must be able to see and pin (`tm/tests/kernel_call_counts.rs`).
fn trace_kind(request: &str) -> &'static str {
    if request.contains(r#""capacity":"#) {
        "capacity"
    } else if request.contains(r#""log":{"#) {
        "log"
    } else if request.contains(r#""emit":["#) {
        "emit"
    } else if request.contains(r#""cmds":"#) {
        "apply"
    } else {
        "other"
    }
}

/// Apply a request to the kernel and return its response.
///
/// The request carries the raw text of every file plus the commands to apply;
/// the response carries the raw text of every file, or a structured error.
pub fn call(request: &str) -> Result<String, KernelFault> {
    init()?;
    if std::env::var_os(TRACE_CALLS_ENV).is_some() {
        eprintln!("kernel call: {}", trace_kind(request));
    }
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
