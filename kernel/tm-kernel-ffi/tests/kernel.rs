//! Rust calls the Lean kernel and checks the answers.
//!
//! These are not proofs. They check that the plumbing carries the proved
//! behaviour all the way to a Rust caller.

use tm_kernel_ffi::call;

const WEEK: &str = r##"{"path":"week/2026-W37.md","grain":1,"ix":35,"lines":[
  "---","week: 2026-W37","---","# Milestones",
  "- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1",
  "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b ^t3",
  "","# Tasks",
  "  - [?] 2 15m Ask Prof. Lee  on-event:reply/7d waiting:2026-09-05 ^a4",
  "<!-- tm:plan -->"]}"##;

const MONTH: &str = r##"{"path":"month/2026-09.md","grain":2,"ix":8,"lines":[
  "# Outcomes",
  "- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1"]}"##;

fn req(cmds: &str) -> String {
    format!("{{\"docs\":[{WEEK},{MONTH}],\"cmds\":{cmds}}}")
}

#[test]
fn round_trip_is_byte_faithful() {
    let out = call(&req("[]")).unwrap();
    // every line comes back exactly as it went in, including front matter,
    // headings, the blank line, the two-space indent, the column padding and
    // the generated-block comment
    assert!(out.contains(r#""- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1""#), "{out}");
    assert!(out.contains(r#""  - [?] 2 15m Ask Prof. Lee  on-event:reply/7d waiting:2026-09-05 ^a4""#), "{out}");
    assert!(out.contains(r#""<!-- tm:plan -->""#), "{out}");
    assert!(out.contains(r#""week: 2026-W37""#), "{out}");
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
}

#[test]
fn move_relocates_the_line_verbatim() {
    let out = call(&req(r#"[{"op":"move","id":"m1","doc":1}]"#)).unwrap();
    let month = out.split(r#"{"lines":"#).nth(2).unwrap();
    assert!(month.contains("Finish ch.5 exercises        @O1 ^m1"), "{out}");
    let week = out.split(r#"{"lines":"#).nth(1).unwrap();
    assert!(!week.contains("^m1"), "the line must leave the week file: {out}");
}

#[test]
fn demote_leaves_a_tombstone_in_the_closed_file() {
    let out = call(&req(r#"[{"op":"demote","id":"m1","doc":1,"period":37}]"#)).unwrap();
    // exactly today's tm file format: two lines, one id, both `[-]`,
    // in two different files
    assert_eq!(out.matches("^m1").count(), 2, "{out}");
    assert_eq!(out.matches("- [-] 5 6b Finish").count(), 2, "{out}");
}

/// **The bug this rebuild exists to make impossible.**
///
/// `horizon::move_line -> move_to` (horizon.rs:943) appends to the destination
/// without asking whether it already holds the id. The `against` spike found
/// 164 depth-2 sequences still reachable at tm HEAD that end this way. Here the
/// same sequence is refused, and the plan is left untouched.
#[test]
fn move_into_the_tombstones_file_is_refused() {
    let out = call(&req(
        r#"[{"op":"demote","id":"m1","doc":1,"period":37},{"op":"move","id":"m1","doc":0}]"#,
    ))
    .unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"occupied"}}"#, "{out}");
}

/// `tm edit ^id est=` reported success and changed nothing, because `est:`
/// overrides the leading estimate and the command wrote the leading slot.
#[test]
fn edit_est_actually_changes_what_the_kernel_reads() {
    let out = call(&req(r#"[{"op":"est","id":"t3","min":45}]"#)).unwrap();
    assert!(out.contains("est:45m"), "{out}");
    assert!(!out.contains("est:1b"), "{out}");
    // and nothing else on the line moved
    assert!(out.contains("- [>] 4 2b Exercises 5.3-5.5            @m1 est:45m ^t3"), "{out}");
}

/// `tm check`'s `dup-id` is an acceptance rule, not a diagnostic that runs
/// afterwards: a duplicate id never becomes a plan value at all.
#[test]
fn duplicate_ids_are_rejected_at_load() {
    let out = call(
        r#"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["- [ ] a ^x1","- [ ] b ^x1"]}],"cmds":[]}"#,
    )
    .unwrap();
    assert_eq!(out, r#"{"err":{"dupId":"x1"}}"#, "{out}");
}

/// A plain `structure Horizon where depth : Nat` accepted `horizon: 99`.
/// `Fin 3` plus a smart constructor does not.
#[test]
fn out_of_range_grain_is_rejected_at_the_boundary() {
    let out = call(r#"{"docs":[{"path":"w.md","grain":99,"ix":0,"lines":[]}],"cmds":[]}"#).unwrap();
    assert!(out.contains("out of range"), "{out}");
}

#[test]
fn unknown_id_is_a_structured_error() {
    let out = call(&req(r#"[{"op":"drop","id":"zz"}]"#)).unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"noSuchId"}}"#, "{out}");
}

#[test]
fn malformed_json_does_not_panic_the_host() {
    let out = call("{ not json").unwrap();
    assert!(out.contains("bad json"), "{out}");
}
