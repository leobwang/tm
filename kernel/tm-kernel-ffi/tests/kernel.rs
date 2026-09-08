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
    let month = out.split(r#""lines":"#).nth(2).unwrap();
    assert!(month.contains("Finish ch.5 exercises        @O1 ^m1"), "{out}");
    let week = out.split(r#""lines":"#).nth(1).unwrap();
    assert!(!week.contains("^m1"), "the line must leave the week file: {out}");
}

/// The response carries each document's horizon back, because the request
/// carries it in: a demotion's two lines are told apart by the regions of their
/// files, so a response that dropped them would be one the kernel could not
/// read (see `the_kernel_reads_back_what_it_writes`).
#[test]
fn the_response_carries_each_documents_horizon() {
    let out = call(&req("[]")).unwrap();
    assert!(out.contains(r#"{"grain":1,"ix":35,"lines":"#), "{out}");
    assert!(out.contains(r#"{"grain":2,"ix":8,"lines":"#), "{out}");
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
/// 426 depth-2 command pairs reachable on tm `main` end this way. Here the
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

// ---------------------------------------------------------------------------
// The audit's findings, each as the exact request that reproduced it.
// ---------------------------------------------------------------------------

/// **Error 1.** A `[-]` line did not round trip *with no commands at all*:
/// `entitiesOfDoc` sent `Glyph.demoted` to `live free` with no archive, and
/// `glyphAt` rendered `[ ]`. The kernel rewrote the user's file on a read.
///
/// A demotion is two lines, so a lone `[-]` has no entity that renders it and
/// is now a named diagnostic rather than a silent rewrite.
#[test]
fn a_lone_demoted_line_is_rejected_not_rewritten() {
    let out = call(r##"{"docs":[{"path":"w.md","lines":["- [-] 5 6b Old work ^m1"]}],"cmds":[]}"##)
        .unwrap();
    assert_eq!(out, r##"{"err":{"orphanDemotion":"m1"}}"##, "{out}");
}

/// …and the shape a `demote` actually writes — two `[-]` lines of one id in two
/// files — now loads, and comes back byte for byte. The first loader rejected
/// it as a duplicate id, so the kernel could not read its own output.
#[test]
fn the_two_line_demotion_form_round_trips() {
    let out = call(&pair("[]")).unwrap();
    assert_eq!(out.matches("- [-] 5 6b Old work ^m1").count(), 2, "{out}");
    assert!(!out.contains("- [ ]"), "no box may change on a read: {out}");
}

/// The two-line demotion form, as `demote` writes it: `w.md` is the week that
/// was closed, `m.md` the month it was filed into.
fn pair(cmds: &str) -> String {
    format!(
        r##"{{"docs":[{{"path":"w.md","grain":1,"ix":35,"lines":["- [-] 5 6b Old work ^m1"]}},
              {{"path":"m.md","grain":2,"ix":8,"lines":["- [-] 5 6b Old work ^m1"]}}],"cmds":{cmds}}}"##
    )
}

/// **The defect an audit found in the first fix of Error 1.** Both lines of a
/// demotion read `[-]`, so *both* orientations of the pair are entities that
/// render exactly those two lines: `pairedEntity` tried one and then the other
/// and the first that worked won, which made the tombstone whichever line the
/// host happened to list second. Listing the same two files the other way round
/// moved which file a `drop` marked.
///
/// The tombstone is now the line in the horizon that was closed — the week —
/// whatever order the documents arrive in.
#[test]
fn which_line_is_the_tombstone_does_not_depend_on_the_document_order() {
    let forwards = call(&pair(r#"[{"op":"drop","id":"m1"}]"#)).unwrap();
    let backwards = call(
        r##"{"docs":[{"path":"m.md","grain":2,"ix":8,"lines":["- [-] 5 6b Old work ^m1"]},
              {"path":"w.md","grain":1,"ix":35,"lines":["- [-] 5 6b Old work ^m1"]}],
             "cmds":[{"op":"drop","id":"m1"}]}"##,
    )
    .unwrap();
    // the live line is the one in the month file, and it is the one that drops
    for out in [&forwards, &backwards] {
        let month = out.split(r#""lines":"#).find(|s| s.contains("m.md")).unwrap();
        let week = out.split(r#""lines":"#).find(|s| s.contains("w.md")).unwrap();
        assert!(month.contains("- [~] 5 6b Old work ^m1"), "{out}");
        assert!(week.contains("- [-] 5 6b Old work ^m1"), "the tombstone stays: {out}");
    }
}

/// …and where the request declares no horizons there is nothing to decide it
/// with, so the loader says so instead of choosing. `tm`'s own files always
/// declare one; a request that does not is a host bug, and this is the
/// diagnostic for it.
#[test]
fn two_demoted_lines_with_no_horizons_are_rejected_by_name() {
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["- [-] 5 6b Old work ^m1"]},{"path":"m.md","lines":["- [-] 5 6b Old work ^m1"]}],"cmds":[]}"##,
    )
    .unwrap();
    assert_eq!(out, r##"{"err":{"ambiguousDemotion":"m1"}}"##, "{out}");
}

/// The other half of the same rule: the kernel may not *write* a pair it could
/// not read. A demotion files work forward — §6.3's close targets a region that
/// is not yet closed — so a `demote` into a finer file, and a `move` that would
/// carry a demoted line back behind its own tombstone, are refused.
#[test]
fn a_demotion_may_not_file_work_backwards() {
    let back = call(
        r##"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["- [ ] 5 6b Old work ^m1"]},
              {"path":"d.md","grain":0,"ix":250,"lines":[]}],
             "cmds":[{"op":"demote","id":"m1","doc":1,"period":37}]}"##,
    )
    .unwrap();
    assert_eq!(back, r##"{"err":{"kernel":"badHorizon"}}"##, "{back}");

    let moved = call(
        r##"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["- [-] 5 6b Old work ^m1"]},
              {"path":"m.md","grain":2,"ix":8,"lines":["- [-] 5 6b Old work ^m1"]},
              {"path":"d.md","grain":0,"ix":250,"lines":[]}],
             "cmds":[{"op":"move","id":"m1","doc":2}]}"##,
    )
    .unwrap();
    assert_eq!(moved, r##"{"err":{"kernel":"badHorizon"}}"##, "{moved}");
}

/// The whole pipeline, end to end: demote, then feed the kernel's own output
/// back in with no commands. Nothing moves.
#[test]
fn the_kernel_reads_back_what_it_writes() {
    let start = r##"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["# Tasks","- [ ] 5 6b Old work ^m1"]},{"path":"m.md","grain":2,"ix":8,"lines":["# Outcomes"]}],"cmds":[{"op":"demote","id":"m1","doc":1,"period":37}]}"##;
    let once = call(start).unwrap();
    let docs = once.trim_start_matches(r##"{"ok":{"docs":"##).trim_end_matches("}}");
    let twice = call(&format!(r##"{{"docs":{docs},"cmds":[]}}"##)).unwrap();
    assert_eq!(once, twice, "the kernel must be able to read its own output");
}

/// **Error 2.** `move` to a document index that does not exist deleted the
/// item and returned `ok`: `renderDocAt` renders the indices that are there,
/// so the line simply was not emitted. The destination is now a `Dest`,
/// which carries a proof that the index is a document of this plan.
#[test]
fn move_to_a_document_that_does_not_exist_is_refused() {
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["- [ ] 5 6b Old work ^m1"]}],"cmds":[{"op":"move","id":"m1","doc":7}]}"##,
    )
    .unwrap();
    assert_eq!(out, r##"{"err":{"kernel":"badHorizon"}}"##, "{out}");
}

/// **Error 3.** Two documents sharing a path are one file on disk, so an
/// index-level uniqueness theorem said nothing about it: a demote put two
/// `^m1` lines into `w.md` with every stated theorem still true.
#[test]
fn two_documents_may_not_share_a_path() {
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["- [ ] 5 6b Old work ^m1"]},{"path":"w.md","lines":[]}],"cmds":[]}"##,
    )
    .unwrap();
    assert_eq!(out, r##"{"err":{"duplicatePath":"w.md"}}"##, "{out}");
}

/// **Warning 6.** One `tm edit est=` from a line the kernel accepts used to
/// produce a line the kernel could no longer parse: the id token of `- [ ]^m1`
/// carries no separator, so the inserted token ran into it.
#[test]
fn edit_est_cannot_produce_an_unparseable_line() {
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["- [ ]^m1"]}],"cmds":[{"op":"est","id":"m1","min":45}]}"##,
    )
    .unwrap();
    assert!(out.contains("est:45m"), "{out}");
    assert!(out.contains("^m1"), "the id token must survive: {out}");
    // and the result is still an item line, so a second edit lands on it
    let out2 = call(
        r##"{"docs":[{"path":"w.md","lines":["- [ ]est:45m ^m1"]}],"cmds":[{"op":"est","id":"m1","min":90}]}"##,
    )
    .unwrap();
    assert!(out2.contains("est:90m"), "{out2}");
}

/// **Warning 7.** `LErr.badLine` was dead code: a line with an item's shape
/// that did not parse was silently reclassified as prose, kept, and written
/// back. Accept or reject is the whole contract of a boundary.
#[test]
fn a_malformed_item_line_is_rejected_not_treated_as_prose() {
    for (lines, why) in [
        (r##"["- [ ] no id here"]"##, "noId"),
        (r##"["- [ ] two ids ^a1 ^a2"]"##, "manyIds"),
        (r##"["- [Z] bad box ^a1"]"##, "badState"),
    ] {
        let out = call(&format!(r##"{{"docs":[{{"path":"w.md","lines":{lines}}}],"cmds":[]}}"##))
            .unwrap();
        assert!(out.contains("badLine"), "{out}");
        assert!(out.contains(why), "{out}");
    }
    // a line that is not an item at all is still prose, and survives verbatim
    let out = call(r###"{"docs":[{"path":"w.md","lines":["## A heading","  plain text"]}],"cmds":[]}"###)
        .unwrap();
    assert!(out.contains("## A heading") && out.contains("plain text"), "{out}");
}

/// …and `dupId` named the wrong id: it reported the head of the id list
/// rather than the one that repeated.
#[test]
fn the_duplicate_diagnostic_names_the_duplicate() {
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["- [ ] a ^aa","- [ ] b ^bb","- [ ] c ^bb"]}],"cmds":[]}"##,
    )
    .unwrap();
    assert!(out.contains("bb") && !out.contains("aa"), "{out}");
}
