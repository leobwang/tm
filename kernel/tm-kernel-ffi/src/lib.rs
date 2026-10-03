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
/// `kernel call: <kind>[+<kind>…]` — **one line per call**, naming every
/// section that call carries ([`trace_kinds`]). It lives here, at the FFI,
/// because this is the one door — `tm/src/cli/kernel_bridge.rs` and
/// `tm/src/cli/kernel_log.rs` each reach the kernel on their own, so a counter
/// in either would miss the other, and a call site added later cannot forget
/// this one.
///
/// Counting the lines is therefore counting **calls**; counting the names is
/// counting **sections**, and since L9 those are different numbers for a
/// capacity verb (README gaps 275 and 278).
///
/// **Before the switch the `log` count is 0 for every verb**, because nothing
/// under `tm/src` calls the kernel's `log` op yet; `tm/tests/kernel_call_counts.rs`
/// records that baseline and asserts it, so a half-switched binary fails a test
/// rather than being noticed later.
pub const TRACE_CALLS_ENV: &str = "TM_TRACE_KERNEL_CALLS";

/// **The request itself, traced** (W-42 repair, README gaps 4200 and 4335):
/// when this is set beside [`TRACE_CALLS_ENV`], every call also writes the
/// request it carries as one more stderr line, `kernel request: <json>` — the
/// whole text, which is one line because the binary's JSON writer escapes
/// every newline. It exists for one instrument: T18 in `tm/tests/cli_latency.rs`
/// takes the planner request `tm check` builds (the request R3's `tm plan`
/// sends) and asks it again with §9.1's `overtime` what-if added, the call R3's
/// TUI overtime box makes, which no shipped verb sends before the swap. A
/// diagnostic, like the call trace: no answer depends on it.
pub const TRACE_REQUESTS_ENV: &str = "TM_TRACE_KERNEL_REQUESTS";

/// **Every section this request carries**, by the one literal each builder
/// emits and no other does: `"capacity":` (`kernel_capacity::request`),
/// `"log":{` (`kernel_log::request`, and `kernel_log::capacity_log_section`
/// spliced into a capacity request), `"emit":[` (`kernel_log::render_values`,
/// the writer S2 added under **D16**), `"cmds":` (`kernel_bridge`'s apply).
/// This crate may depend on nothing (AGENTS R7), so it is a substring test and
/// not a parse — a *document line* containing one of these literals would be
/// miscounted, which is acceptable in a diagnostic that no answer depends on.
///
/// `emit` gets its own name rather than falling into `other` on purpose: after
/// S2 every appending verb makes one, so it is a per-verb cost the call-count
/// instrument must be able to see and pin (`tm/tests/kernel_call_counts.rs`).
///
/// **One request can carry more than one section, and since L9 one does**
/// (README **gap 278**). A capacity request carries a `log` section as well —
/// that is D24's seam, and it is a second replay of the log inside the verb's
/// own call (**gap 275**). This used to answer `"capacity"` and stop, because
/// it tested `"capacity":` first and returned; the replay was then invisible to
/// `tm/tests/kernel_call_counts.rs`, which pins the `log` column exactly. So it
/// now names **all** of them, in a fixed order, and [`call`] joins them with
/// `+` on the one line it writes per call: a capacity verb traces
/// `kernel call: capacity+log`.
///
/// The order is fixed (capacity, log, emit, walls, apply, planner) so the line is a
/// stable key, and a request matching nothing is `other` — never the empty
/// list, which would trace a blank name.
///
/// **`walls` is the `emit` section's object form** (`"emit":{`, W-37 track T,
/// README gap 3139): the question D61's housekeeping asks the kernel while a
/// block runs. It carries the whole tree and a `log` section but no `cmds`, so
/// without its own name it traced as `log` alone and the whole-tree load it is
/// was invisible to every column (README gap 3247).
fn trace_kinds(request: &str) -> Vec<&'static str> {
    let mut kinds = Vec::new();
    if request.contains(r#""capacity":"#) {
        kinds.push("capacity");
    }
    if request.contains(r#""log":{"#) {
        kinds.push("log");
    }
    if request.contains(r#""emit":["#) {
        kinds.push("emit");
    }
    if request.contains(r#""emit":{"#) {
        kinds.push("walls");
    }
    if request.contains(r#""cmds":"#) {
        kinds.push("apply");
    }
    // The `planner` section — the day R3's `tm plan` asks for (W-41 repair,
    // README gap 4142): `tm check` sends it today, and it is the costliest call
    // the binary makes, so a verb that starts sending it shows up by name.
    if request.contains(r#""planner":{"#) {
        kinds.push("planner");
    }
    if kinds.is_empty() {
        kinds.push("other");
    }
    kinds
}

/// Apply a request to the kernel and return its response.
///
/// The request carries the raw text of every file plus the commands to apply;
/// the response carries the raw text of every file, or a structured error.
pub fn call(request: &str) -> Result<String, KernelFault> {
    init()?;
    if std::env::var_os(TRACE_CALLS_ENV).is_some() {
        eprintln!("kernel call: {}", trace_kinds(request).join("+"));
        if std::env::var_os(TRACE_REQUESTS_ENV).is_some() {
            eprintln!("kernel request: {request}");
        }
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
