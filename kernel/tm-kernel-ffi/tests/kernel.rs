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
    assert!(
        out.contains(r#""- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1""#),
        "{out}"
    );
    assert!(
        out.contains(r#""  - [?] 2 15m Ask Prof. Lee  on-event:reply/7d waiting:2026-09-05 ^a4""#),
        "{out}"
    );
    assert!(out.contains(r#""<!-- tm:plan -->""#), "{out}");
    assert!(out.contains(r#""week: 2026-W37""#), "{out}");
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
}

#[test]
fn move_relocates_the_line_verbatim() {
    let out = call(&req(r#"[{"op":"move","id":"m1","doc":1}]"#)).unwrap();
    let month = out.split(r#""lines":"#).nth(2).unwrap();
    assert!(
        month.contains("Finish ch.5 exercises        @O1 ^m1"),
        "{out}"
    );
    let week = out.split(r#""lines":"#).nth(1).unwrap();
    assert!(
        !week.contains("^m1"),
        "the line must leave the week file: {out}"
    );
}

/// The response carries each document's horizon back, because the request
/// carries it in: a demotion's two lines are told apart by the regions of their
/// files, so a response that dropped them would be one the kernel could not
/// read (see `the_kernel_reads_back_what_it_writes`).
#[test]
fn the_response_carries_each_documents_horizon() {
    let out = call(&req("[]")).unwrap();
    // Key order is the kernel's build order since J5 (`jemit` over an assoc
    // list: path, lines, grain, ix) — `Json.mkObj` used to sort them.  The
    // region still closes each document object.
    assert!(out.contains(r#"{"path":"week/2026-W37.md","lines":["#), "{out}");
    assert!(out.contains(r#"],"grain":1,"ix":35}"#), "{out}");
    assert!(out.contains(r#"{"path":"month/2026-09.md","lines":["#), "{out}");
    assert!(out.contains(r#"],"grain":2,"ix":8}"#), "{out}");
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
    assert!(
        out.contains("- [>] 4 2b Exercises 5.3-5.5            @m1 est:45m ^t3"),
        "{out}"
    );
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
/// The first fix refused a lone `[-]` as `orphanDemotion`, on the reading that
/// "a demotion is two lines". That reading is wrong and the corpus found it:
/// §6.3's `tm close month` carries the `month/…#Demoted` copy into the next
/// month file and touches nothing else, so a `# Demoted` section holds `[-]`
/// lines whose partner is in a file the host need not have handed over —
/// §4.3's own `month/2026-09.md` is one. So `[-]` standing alone is a state
/// (`Status.demoted`), and the line comes back byte for byte.
#[test]
fn a_lone_demoted_line_round_trips() {
    let out = call(r##"{"docs":[{"path":"w.md","lines":["- [-] 5 6b Old work ^m1"]}],"cmds":[]}"##)
        .unwrap();
    // Byte for byte, in the kernel's build order (J5: `path` before `lines`).
    assert_eq!(
        out, r##"{"ok":{"docs":[{"path":"w.md","lines":["- [-] 5 6b Old work ^m1"]}],"report":{"closes":[]}}}"##,
        "{out}"
    );
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
    // the live line is the one in the month file, and it is the one that drops.
    // Each document object opens with its path (J5's build order), so a
    // segment after `{"path":` is exactly one document.
    for out in [&forwards, &backwards] {
        let month = out
            .split(r#"{"path":"#)
            .find(|s| s.starts_with(r#""m.md""#))
            .unwrap();
        let week = out
            .split(r#"{"path":"#)
            .find(|s| s.starts_with(r#""w.md""#))
            .unwrap();
        assert!(month.contains("- [~] 5 6b Old work ^m1"), "{out}");
        assert!(
            week.contains("- [-] 5 6b Old work ^m1"),
            "the tombstone stays: {out}"
        );
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

/// §4.3's own demotion pair — the record live in the week, the archive copy
/// under `month/…# Demoted`, and **two lines whose bytes differ**, because
/// §6.3's close puts `est:` = remaining and a `demoted:` stamp on the copy.
/// This was `splitLine: m2` (one entity, one token vector) and then
/// `notADemotion: m2` (the tombstone was taken to be the line in the earlier
/// horizon, which is the week line, which reads `[ ]`). It is the pair that
/// kept three of the five fixture trees from a whole-plan round trip.
///
/// Since the owner's D6 the month carries `^O2`, the outcome both lines name
/// (§4.3's own month file): without it the request is refused
/// `itemCheck: danglingParent` (kernel/README.md gap 22, closed at stage 4 final
/// step 3). The fixture was fixed, not the check.
#[test]
fn the_spec_demotion_pair_round_trips() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,
              "lines":["# Milestones","- [ ] 4 6b Rollback path passes tests   @O2 ^m2"]},
             {"path":"month/2026-09.md","grain":2,"ix":8,
              "lines":["# Outcomes","- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2","# Demoted","- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"]}],
             "cmds":[]}"##,
    )
    .unwrap();
    assert!(
        out.contains(r#"- [ ] 4 6b Rollback path passes tests   @O2 ^m2"#),
        "{out}"
    );
    assert!(
        out.contains(r#"- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"#),
        "{out}"
    );
}

/// §6.3 gives an item **one** archive record. `demote` is the week close; the
/// month close "moves them to the next month file", which is `move`. So a
/// second `demote` of a `[-]` record is refused rather than picking one of the
/// two lines to drop — overwrite the standing tombstone and `w.md` comes back
/// empty with `ok`; keep it and the line the record is leaving disappears
/// instead. (An *open* line with a standing record is not this case: since
/// kernel/README.md gap 53 it is merged into the record, and the open line is
/// what stays behind as the tombstone.)
#[test]
fn a_second_demotion_is_refused_rather_than_dropping_a_line() {
    let out = call(
        r##"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["- [-] 5 6b Old work ^m1"]},
              {"path":"m.md","grain":2,"ix":8,"lines":["- [-] 5 6b Old work ^m1"]},
              {"path":"n.md","grain":2,"ix":9,"lines":[]}],
             "cmds":[{"op":"demote","id":"m1","doc":2,"period":38}]}"##,
    )
    .unwrap();
    assert_eq!(out, r##"{"err":{"kernel":"alreadyDemoted"}}"##, "{out}");
}

/// §6.3's week close, whole: the week line stays where it was and becomes
/// `[-]` with its bytes untouched, and the copy filed into the month carries
/// the `demoted:` stamp. The stamp is on the **copy** only — one token vector
/// for both sites put it in the week file too, which §6.3 does not say.
#[test]
fn a_close_stamps_the_copy_and_leaves_the_week_line_alone() {
    let out = call(
        r##"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["- [ ] 5 6b Work ^m1"]},
              {"path":"m.md","grain":2,"ix":8,"lines":[]}],
             "cmds":[{"op":"demote","id":"m1","doc":1,"period":37}]}"##,
    )
    .unwrap();
    let week = out
        .split(r#"{"path":"#)
        .find(|s| s.starts_with(r#""w.md""#))
        .unwrap();
    assert!(
        week.contains("- [-] 5 6b Work ^m1"),
        "no stamp in the week file: {out}"
    );
    assert!(out.contains("- [-] 5 6b Work demoted:W37 ^m1"), "{out}");
}

/// **The `demote` verb files its record into `# Demoted`** (kernel/README.md
/// gap 20's remainder, stage 4 step 9): at the end of the section, ahead of the
/// heading after it — the week close's landing (`demoteSpot`), not the end of
/// the file where stage 3 put it. `Boundary.lean`'s
/// `the_demote_verb_files_into_demoted_ahead_of_the_next_section`, at the FFI.
#[test]
fn demote_files_the_record_at_the_end_of_demoted() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,"lines":["# Tasks","- [ ] 2 1b Draft the outline ^m1","- [ ] 3 2b Rollback path passes tests ^m2"]},
              {"path":"month/2026-09.md","grain":2,"ix":8,"lines":["# Outcomes","# Demoted","# Notes"]}],
             "cmds":[{"op":"demote","id":"m1","doc":1,"period":37},{"op":"demote","id":"m2","doc":1,"period":37}]}"##,
    )
    .unwrap();
    assert!(
        out.contains(r##"{"path":"month/2026-09.md","lines":["# Outcomes","# Demoted","- [-] 2 1b Draft the outline demoted:W37 ^m1","- [-] 3 2b Rollback path passes tests demoted:W37 ^m2","# Notes"]"##),
        "{out}"
    );
}

/// **`readopt` is a demoted line or it is nothing** (§6.3: "moves a *demoted
/// line* into the current week, `[-]` -> `[ ]`, stamp kept"). Run on §4.3's
/// fixture — where the record is already `[ ]` and the tombstone is the line
/// carrying `est:` = remaining and the stamp — consuming the tombstone threw
/// both away and returned `ok`. "Stamp kept" was exactly what was lost.
/// (The month carries `^O2` since D6, as above: the fixture's `@O2` resolves.)
#[test]
fn readopt_of_a_live_record_is_refused_rather_than_losing_the_stamp() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,
              "lines":["- [ ] 4 6b Rollback path passes tests   @O2 ^m2"]},
             {"path":"month/2026-09.md","grain":2,"ix":8,
              "lines":["# Outcomes","- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2","# Demoted","- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"]}],
             "cmds":[{"op":"readopt","id":"m2","doc":0}]}"##,
    )
    .unwrap();
    assert_eq!(out, r##"{"err":{"kernel":"notDemoted"}}"##, "{out}");
}

/// ...and on a record that really is `[-]` it works, and §6.3's "stamp kept"
/// is kept: the tombstone is consumed, the record moves, `demoted:W37` stays.
#[test]
fn readopt_of_a_demoted_record_keeps_the_stamp() {
    let out = call(
        r##"{"docs":[{"path":"w.md","grain":1,"ix":35,"lines":["- [-] 5 6b Old work ^m1"]},
              {"path":"m.md","grain":2,"ix":8,"lines":["- [-] 5 6b Old work demoted:W37 ^m1"]},
              {"path":"n.md","grain":1,"ix":36,"lines":[]}],
             "cmds":[{"op":"readopt","id":"m1","doc":2}]}"##,
    )
    .unwrap();
    assert!(out.contains("- [ ] 5 6b Old work demoted:W37 ^m1"), "{out}");
    assert_eq!(
        out.matches("Old work").count(),
        1,
        "the tombstone is consumed: {out}"
    );
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
    let docs = once
        .trim_start_matches(r##"{"ok":{"docs":"##)
        .trim_end_matches(r##","report":{"closes":[]}}}"##);
    let twice = call(&format!(r##"{{"docs":{docs},"cmds":[]}}"##)).unwrap();
    assert_eq!(
        once, twice,
        "the kernel must be able to read its own output"
    );
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
        let out = call(&format!(
            r##"{{"docs":[{{"path":"w.md","lines":{lines}}}],"cmds":[]}}"##
        ))
        .unwrap();
        assert!(out.contains("badLine"), "{out}");
        assert!(out.contains(why), "{out}");
    }
    // a line that is not an item at all is still prose, and survives verbatim
    let out =
        call(r###"{"docs":[{"path":"w.md","lines":["## A heading","  plain text"]}],"cmds":[]}"###)
            .unwrap();
    assert!(
        out.contains("## A heading") && out.contains("plain text"),
        "{out}"
    );
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

/// `tm rank ^id n` moves a line *within* its own file — the verb `move` cannot
/// express.  `freshRank` never reuses a rank, so the user-specified rank has to
/// be free; rank 10 is past the last line of the week file.
#[test]
fn rank_moves_a_line_within_its_own_file() {
    let out = call(&req(r#"[{"op":"rank","id":"m1","rank":10}]"#)).unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
    let week = out.split(r#""lines":"#).nth(1).unwrap();
    // the line is byte-identical, and it left no copy behind...
    assert!(
        week.contains(r#""- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1""#),
        "{out}"
    );
    // ...but it now sits below the generated-block comment, which sat below it
    let moved = week.find("^m1").unwrap();
    let comment = week.find("tm:plan").unwrap();
    assert!(
        comment < moved,
        "m1 must have moved *down* the file: {week}"
    );
}

/// A rank an existing line already owns is not free: a document's ranks are
/// the prose ranks and the item ranks in one list, so `rank m1 5` would put
/// two lines at index 5 and dies at `mapAt`'s planWf re-check as `badHorizon`
/// — with the file untouched (error responses carry no docs at all).
#[test]
fn rank_onto_a_taken_rank_is_refused_and_writes_nothing() {
    let out = call(&req(r#"[{"op":"rank","id":"m1","rank":5}]"#)).unwrap();
    assert!(out.contains(r#""kernel":"badHorizon""#), "{out}");
    // and nothing was written at all: an error response carries no documents
    assert!(
        !out.contains("lines"),
        "error response must not rewrite anything: {out}"
    );
}

/// The wire form of L20a (`rank_is_idempotent`): the same `rank` twice is
/// byte-identical to the same `rank` once, so `tm rank` is not a source of
/// spurious diffs.
#[test]
fn rank_twice_is_byte_identical_to_rank_once() {
    let once = call(&req(r#"[{"op":"rank","id":"m1","rank":10}]"#)).unwrap();
    let twice = call(&req(
        r#"[{"op":"rank","id":"m1","rank":10},{"op":"rank","id":"m1","rank":10}]"#,
    ))
    .unwrap();
    assert!(once.starts_with(r#"{"ok":"#) && twice.starts_with(r#"{"ok":"#));
    assert_eq!(once, twice);
}

/// `tm add` through the whole FFI: the host supplies a seed, L21's `freshId`
/// names an id nothing claims, and the new line arrives in the requested file
/// rendered like every other item — a box and a trailing id, nothing else.
#[test]
fn add_inserts_a_fresh_id_into_the_requested_file() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,"lines":["# Tasks"]}],
             "cmds":[{"op":"add","seed":9,"doc":0,"title":"Buy paint"}]}"##,
    )
    .unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
    assert!(out.contains(r#""- [ ] Buy paint ^9""#), "{out}");
    assert!(
        out.contains(r#""grain":1,"ix":35"#),
        "the response must carry the document's region back: {out}"
    );
}

/// The `add` bite (§5.8): a day file's items must sit under `# Pinned`, and an
/// add into `# Tasks` builds a post-state that fails `planWf`'s `sectionsWf`.
/// `insertFresh` refuses by name rather than writing a broken tree — the same
/// rule that gives `plan-conflicts/` its `sectionDiscipline` fault.  The
/// response carries no documents at all; nothing was written.
#[test]
fn add_outside_a_day_files_pinned_section_is_refused_by_name() {
    let out = call(
        r##"{"docs":[{"path":"day/2026-09-07.md","lines":["# Tasks"]}],
             "cmds":[{"op":"add","seed":3,"doc":0,"title":"Buy paint"}]}"##,
    )
    .unwrap();
    assert!(out.contains(r#""kernel":"badItem""#), "{out}");
    assert!(
        !out.contains("lines"),
        "error response must not rewrite anything: {out}"
    );
}

/// Sequential adds must not collide: each `add` reads the store the previous
/// one inserted into, so both ids (L21) and ranks (`freshRank`) grow between
/// the two commands.
#[test]
fn two_adds_in_one_request_get_two_ids_and_two_ranks() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,"lines":["# Tasks"]}],
             "cmds":[{"op":"add","seed":9,"doc":0,"title":"A"},{"op":"add","seed":9,"doc":0,"title":"B"}]}"##,
    )
    .unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
    let a = out.find(r#""- [ ] A ^9""#);
    let b = out.find(r#""- [ ] B ^10""#);
    assert!(a.is_some(), "{out}");
    assert!(
        b.is_some(),
        "the second add must not reuse the first's id: {out}"
    );
    // The "two ranks" half of this test's name, asserted directly: the second
    // add's freshRank is strictly larger, so its line renders below the first's.
    assert!(
        a.unwrap() < b.unwrap(),
        "the second add's higher rank must render after the first's line: {out}"
    );
}

/// The five named title refusals ride the free-text `err`, not a kernel name —
/// the bytes would not render back, so the parser refuses before any plan
/// exists.  (Lean-side the same five are `parseCmd_rejects_add_title_variants`.)
#[test]
fn add_titles_are_refused_by_name() {
    for (title, why) in [
        (r"a\nb", "titleNewline"),
        (r"a\tb", "titleTab"),
        ("steal ^m1", "titleId"),
        ("", "titleBlank"),
        (" padded ", "titleEdge"),
    ] {
        let out = call(&format!(
            r#"{{"docs":[],"cmds":[{{"op":"add","seed":1,"doc":0,"title":"{title}"}}]}}"#
        ))
        .unwrap();
        assert!(out.contains(why), "{title}: {out}");
    }
}

// ---------------------------------------------------------------------------
// The widened edit: {"op":"edit","id","key","value"} — keyed set, empty value
// = unset — plus gap 32's tab guard on the whole edit path, est op included.
// Lean-side twins: the_edit_path_writes_what_the_field_path_reads,
// parseCmd_rejects_edit_variants, edit_of_a_tabbed_line_is_refused,
// est_of_a_tabbed_line_is_refused, unset_of_an_absent_key_is_refused.
// ---------------------------------------------------------------------------

/// A keyed edit goes through the same field grammar the loader reads: the
/// value is parsed by the key's own parser, written by the key's own setter,
/// and the whole line's other bytes are untouched.
#[test]
fn edit_keyed_pref_writes_through_the_field_grammar() {
    let out = call(&req(
        r#"[{"op":"edit","id":"t3","key":"pref","value":"07:30"}]"#,
    ))
    .unwrap();
    assert!(
        out.contains(r#""- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b pref:07:30 ^t3""#),
        "{out}"
    );
}

/// The standing est op and the keyed est edit are one path (Lean:
/// the_est_op_is_the_keyed_est_edit, definitional) — same bytes out.
#[test]
fn edit_keyed_est_matches_the_est_op() {
    let keyed = call(&req(
        r#"[{"op":"edit","id":"t3","key":"est","value":"45m"}]"#,
    ))
    .unwrap();
    let op = call(&req(r#"[{"op":"est","id":"t3","min":45}]"#)).unwrap();
    assert_eq!(keyed, op, "keyed:\n{keyed}\nop:\n{op}");
    assert!(
        keyed.contains(r#""- [>] 4 2b Exercises 5.3-5.5            @m1 est:45m ^t3""#),
        "{keyed}"
    );
}

/// An empty value is the unset form: the key's token is removed, separator
/// and all, and nothing else on the line moves.
#[test]
fn edit_with_an_empty_value_unsets_the_key() {
    let out = call(&req(r#"[{"op":"edit","id":"t3","key":"est","value":""}]"#)).unwrap();
    assert!(
        out.contains(r#""- [>] 4 2b Exercises 5.3-5.5            @m1 ^t3""#),
        "{out}"
    );
    assert!(!out.contains("est:1b"), "{out}");
}

/// The three parse-tier refusals, each by name: not a key, a key the edit
/// path is not wired for (README gap 40), a value the field grammar refuses.
/// `ci:7` is the Fin 6 smart constructor biting through the wire (R10).
#[test]
fn edit_refusals_are_named() {
    for (key, value, why) in [
        ("size", "3", r#"{"err":"unknownKey size"}"#),
        ("demoted", "W37", r#"{"err":"keyNotWired demoted"}"#),
        ("ci", "7", r#"{"err":"badValue ci"}"#),
        ("est", "3d", r#"{"err":"badValue est"}"#),
    ] {
        let out = call(&req(&format!(
            r#"[{{"op":"edit","id":"t3","key":"{key}","value":"{value}"}}]"#
        )))
        .unwrap();
        assert_eq!(out, why, "{key}={value}: {out}");
    }
}

// ---------------------------------------------------------------------------
// Gap 40's bridges: eight more keys on the wire — due, at, win, every,
// on-event, loc, waiting, after. Lean-side twins:
// the_eight_bridged_keys_accept_their_spec_values,
// parseCmd_refuses_the_bridged_keys_bad_values, parseCmd_reads_the_bridged_keys,
// edit_of_a_dangling_after_is_refused_by_name,
// edit_of_a_cyclic_after_is_refused_by_name, applyCmd_after_succeeds,
// the_year_9999_rollover_parses_but_the_edit_refuses_it.
// ---------------------------------------------------------------------------

/// One keyed edit against the fixture, asserting the whole rewritten line.
fn edit_writes(id: &str, key: &str, value: &str, line: &str) {
    let out = call(&req(&format!(
        r#"[{{"op":"edit","id":"{id}","key":"{key}","value":"{value}"}}]"#
    )))
    .unwrap();
    assert!(
        out.contains(&format!("\"{line}\"")),
        "{key}={value} should write {line:?}: {out}"
    );
}

#[test]
fn edit_keyed_due_writes_both_forms() {
    edit_writes("t3", "due", "2026-09-11", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b due:2026-09-11 ^t3");
    edit_writes("t3", "due", "2026-09-11T23:59", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b due:2026-09-11T23:59 ^t3");
}

#[test]
fn edit_keyed_at_writes_the_short_end() {
    edit_writes("t3", "at", "2026-09-07T12:50/13:50", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b at:2026-09-07T12:50/13:50 ^t3");
    // A long end on the start's own day is written back in the short form.
    edit_writes("t3", "at", "2026-09-07T12:50/2026-09-07T13:50", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b at:2026-09-07T12:50/13:50 ^t3");
}

#[test]
fn edit_keyed_win_writes_the_overnight_window() {
    edit_writes("t3", "win", "22:00-02:00", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b win:22:00-02:00 ^t3");
}

#[test]
fn edit_keyed_every_writes_the_canonical_rule() {
    // `daily` is read and `day` is written — the field's canonical rendering.
    edit_writes("t3", "every", "daily", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b every:day ^t3");
    edit_writes("t3", "every", "Mon,Wed,Fri", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b every:Mon,Wed,Fri ^t3");
}

#[test]
fn edit_keyed_on_event_replaces_in_place() {
    edit_writes("a4", "on-event", "reply", "  - [?] 2 15m Ask Prof. Lee  on-event:reply waiting:2026-09-05 ^a4");
}

#[test]
fn edit_keyed_loc_writes_a_name_and_an_enum() {
    edit_writes("t3", "loc", "lounge", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b loc:lounge ^t3");
    edit_writes("t3", "loc", "library", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b loc:library ^t3");
}

#[test]
fn edit_keyed_waiting_replaces_in_place() {
    edit_writes("a4", "waiting", "2026-09-20", "  - [?] 2 15m Ask Prof. Lee  on-event:reply/7d waiting:2026-09-20 ^a4");
}

#[test]
fn edit_keyed_after_writes_a_dependency_the_plan_holds() {
    edit_writes("t3", "after", "^m1,event:visa", "- [>] 4 2b Exercises 5.3-5.5            @m1 est:1b after:^m1,event:visa ^t3");
}

/// `after` meets the plan tier, and both refusals are named: an id no item
/// carries is `danglingDep`, a dependency on itself (or a two-item loop) is
/// `depCycle` — never `badHorizon`, and nothing is written.
#[test]
fn edit_keyed_after_refuses_a_dangling_or_cyclic_dependency_by_name() {
    for (id, value, why) in [
        ("t3", "^zz", r#"{"err":{"kernel":"danglingDep"}}"#),
        ("t3", "^t3", r#"{"err":{"kernel":"depCycle"}}"#),
    ] {
        let out = call(&req(&format!(
            r#"[{{"op":"edit","id":"{id}","key":"after","value":"{value}"}}]"#
        )))
        .unwrap();
        assert_eq!(out, why, "after={value}: {out}");
    }
    let out = call(&req(
        r#"[{"op":"edit","id":"m1","key":"after","value":"^t3"},{"op":"edit","id":"t3","key":"after","value":"^m1"}]"#,
    ))
    .unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"depCycle"}}"#, "{out}");
}

/// A value each bridged key's own grammar refuses is `badValue <k>`, by name —
/// and so are `loc:`'s word bound (a space) and `at:`'s one false bridge, the
/// year-9999 short end the loader reads but no four-digit year can write.
#[test]
fn the_bridged_keys_refuse_bad_values_by_name() {
    for (key, value) in [
        ("due", "2026-02-30"),
        ("at", "2026-09-07T13:50/2026-09-06T12:00"),
        ("at", "9999-12-31T23:00/01:00"),
        ("win", "25:00-13:00"),
        ("every", "0d"),
        ("on-event", "re ply"),
        ("loc", "a b"),
        ("waiting", "2026-9-20"),
        ("after", "^"),
    ] {
        let out = call(&req(&format!(
            r#"[{{"op":"edit","id":"t3","key":"{key}","value":"{value}"}}]"#
        )))
        .unwrap();
        assert_eq!(out, format!(r#"{{"err":"badValue {key}"}}"#), "{key}={value}: {out}");
    }
}

/// Gap 32, refused loudly instead of shipped wrong: `Text.isSp` is space-only,
/// so a tab hides tokens from this kernel — on such a line Rust's edit and a
/// kernel edit could write two different `est:` slots.  Any edit addressed to
/// a line whose raw bytes carry a tab is `tabbedLine`, by name.
#[test]
fn edit_of_a_tabbed_line_is_refused_loudly() {
    let out = call(
        r#"{"docs":[{"path":"w.md","lines":["- [ ] 2b Fix\tthe bug ^m1"]}],"cmds":[{"op":"edit","id":"m1","key":"est","value":"45m"}]}"#,
    )
    .unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"tabbedLine"}}"#, "{out}");
}

/// ...and the standing est op sits behind the same guard — the one behaviour
/// change to a shipped op from this widening, on the refusal side only.
#[test]
fn the_est_op_refuses_the_same_tabbed_line() {
    let out = call(
        r#"{"docs":[{"path":"w.md","lines":["- [ ] 2b Fix\tthe bug ^m1"]}],"cmds":[{"op":"est","id":"m1","min":45}]}"#,
    )
    .unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"tabbedLine"}}"#, "{out}");
}

/// Unsetting a key the line does not carry is a named refusal, not a success
/// that removed nothing.
#[test]
fn unset_of_a_key_the_line_does_not_carry_is_refused() {
    let out = call(&req(r#"[{"op":"edit","id":"t3","key":"pref","value":""}]"#)).unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"keyAbsent"}}"#, "{out}");
}

// ---------------------------------------------------------------------------
// J5, the request side: the kernel reads every request with its own `jparse`
// and every field through `jget` — no `Lean.Json` on the wire.  Lean-side
// twins: junescape_accepts_the_host_short_escapes,
// parseCmd_refuses_a_duplicate_field, run_refuses_cmds_that_are_not_an_array,
// respond_names_a_parse_refusal, the_response_call_emits_parses_back.
// ---------------------------------------------------------------------------

/// Every spelling a JSON host may use inside a line reads to the characters it
/// spells: a quote and a backslash, serde_json's short escapes (`\t`, `\b`,
/// `\f`) and `\/`, a control byte as a lowercase quad, `é` as an uppercase
/// and a lowercase quad, and raw UTF-8 (a two-byte letter, a four-byte emoji).
/// The response spells them the kernel's way, which is serde_json's since stage
/// 5 D9 B4 (`jescape`: short forms for quote, backslash, `\b`, `\t`, `\n`,
/// `\f`, `\r`; a lowercase quad for every other control byte; `\/` and
/// uppercase quads are read, never written).  This is the host-agreement
/// obligation, evidenced rather than proved.
#[test]
fn the_request_reads_every_escape_a_host_writes() {
    let emoji = '\u{1F600}';
    let out = call(&format!(
        r#"{{"docs":[{{"path":"w.md","lines":["q\"b\\s\tt\u0001c\/s\bb\ff\u00E9\u00e9 {}{emoji}"]}}],"cmds":[]}}"#,
        '\u{e9}'
    ))
    .unwrap();
    assert_eq!(
        out,
        format!(
            r#"{{"ok":{{"docs":[{{"path":"w.md","lines":["q\"b\\s\tt\u0001c/s\bb\ff{e}{e} {e}{emoji}"]}}],"report":{{"closes":[]}}}}}}"#,
            e = '\u{e9}'
        ),
        "{out}"
    );
}

/// A field sent twice is refused by name.  `Lean.Json`'s parser and
/// serde_json's `Value` both keep the last pair silently; the kernel reads
/// neither, because picking one is picking between two readings (§5.6).
#[test]
fn a_duplicate_field_is_refused_by_name() {
    let out = call(&req(r#"[{"op":"drop","id":"t3","id":"m1"}]"#)).unwrap();
    assert_eq!(out, r#"{"err":"duplicateKey id"}"#, "{out}");
    let out = call(r#"{"docs":[],"docs":[],"cmds":[]}"#).unwrap();
    assert_eq!(out, r#"{"err":"duplicateKey docs"}"#, "{out}");
}

/// A `cmds` that is present but not an array used to read as "no commands" —
/// an `ok` with nothing changed, for a request that asked for a change.  An
/// absent `cmds` is still a read.
#[test]
fn cmds_that_are_not_an_array_are_refused() {
    let out = call(&req("3")).unwrap();
    assert_eq!(out, r#"{"err":"array expected"}"#, "{out}");
    let out = call(r#"{"docs":[]}"#).unwrap();
    assert_eq!(out, r#"{"ok":{"docs":[],"report":{"closes":[]}}}"#, "{out}");
}

/// A malformed request is refused with the parser's own name for the reason —
/// and a *lone* surrogate escape is refused by name (README gap 42).  Since
/// stage 5 A2 a surrogate pair is read, as serde_json reads it:
/// `a_surrogate_pair_is_read_and_a_lone_surrogate_refused`.
#[test]
fn a_parse_refusal_names_its_reason() {
    assert_eq!(call("{ not json").unwrap(), r#"{"err":"bad json: expectedKey n"}"#);
    assert_eq!(call(r#"{"docs":[]"#).unwrap(), r#"{"err":"bad json: unterminatedObject"}"#);
    assert_eq!(
        call(r#"{"docs":[{"path":"w.md","lines":["\ud83d"]}]}"#).unwrap(),
        r#"{"err":"bad json: badEscape surrogateEscape 55357"}"#
    );
}

// ---------------------------------------------------------------------------
// Stage 5 A2 (design §5.1): JSON gains an exact decimal; gaps 42 and 43 read as
// serde_json reads.  This crate has no serde_json (R7), so the host's verdict on
// the same bytes is checked beside these in `tm/src/cli/kernel_bridge.rs`
// (`the_kernel_reads_numerals_and_surrogates_as_serde_reads_them`).
// ---------------------------------------------------------------------------

const EMPTY_OK: &str = r#"{"ok":{"docs":[],"report":{"closes":[]}}}"#;

/// `-0.5` and `1e5` at a key no reader reads are accepted, where before A2 the
/// whole request was `bad json` (`notAValue -`, `trailingGarbage e`).
#[test]
fn a_decimal_and_an_exponent_parse() {
    for n in ["-0.5", "1e5", "1E+05", "2.50e-3", "-0"] {
        let req = format!(r#"{{"docs":[],"x":{n}}}"#);
        assert_eq!(call(&req).unwrap(), EMPTY_OK, "{n}");
    }
}

/// `007` is refused by name (gap 43, closed); before A2 the kernel read it as
/// `7`.  So is a numeral that stops where a digit must follow.  A lone `0` and
/// `0.5` still read.
#[test]
fn a_leading_zero_is_refused_by_name() {
    for (n, why) in [("007", "leadingZero"), ("-01", "leadingZero"), ("1.", "missingDigit ."),
                     ("1e", "missingDigit e"), ("-", "missingDigit -")] {
        let req = format!(r#"{{"docs":[],"x":{n}}}"#);
        assert_eq!(call(&req).unwrap(), format!(r#"{{"err":"bad json: {why}"}}"#), "{n}");
    }
    for n in ["0", "0.5"] {
        let req = format!(r#"{{"docs":[],"x":{n}}}"#);
        assert_eq!(call(&req).unwrap(), EMPTY_OK, "{n}");
    }
}

/// A request number that is not a natural is refused by the field's reader, not
/// as `bad json` (which is what `-3` got before A2), and the same field carrying
/// a natural reads.
#[test]
fn a_request_minus_three_is_refused_by_its_reader() {
    let out = call(&req(r#"[{"op":"est","id":"m1","min":-3}]"#)).unwrap();
    assert_eq!(out, r#"{"err":"Natural number expected"}"#, "{out}");
    let out = call(&req(r#"[{"op":"move","id":"m1","doc":1.5}]"#)).unwrap();
    assert_eq!(out, r#"{"err":"Natural number expected"}"#, "{out}");
    let out = call(r#"{"docs":[],"blockMin":1.5}"#).unwrap();
    assert_eq!(out, r#"{"err":"badBlockMin"}"#, "{out}");
    let out = call(&req(r#"[{"op":"est","id":"m1","min":3}]"#)).unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
}

/// A surrogate pair is read as the one astral character it stands for, and the
/// line comes back as raw UTF-8 (gap 42, closed).  A lone high or low surrogate
/// is refused by name.
#[test]
fn a_surrogate_pair_is_read_and_a_lone_surrogate_refused() {
    let req = r#"{"docs":[{"path":"w.md","lines":["a \ud83d\ude00 b"]}],"cmds":[]}"#;
    assert_eq!(
        call(req).unwrap(),
        "{\"ok\":{\"docs\":[{\"path\":\"w.md\",\"lines\":[\"a \u{1F600} b\"]}],\"report\":{\"closes\":[]}}}"
    );
    for (esc, v) in [(r"\ud83d", 55357), (r"\ude00", 56832), (r"\ud83d\u0041", 55357), (r"\ud83dx", 55357)] {
        let req = format!(r#"{{"docs":[{{"path":"w.md","lines":["{esc}"]}}]}}"#);
        assert_eq!(
            call(&req).unwrap(),
            format!(r#"{{"err":"bad json: badEscape surrogateEscape {v}"}}"#),
            "{esc}"
        );
    }
}

/// The codec's per-character recursions run as their `@[csimp]` twins
/// (`jescape_eq_jescapeTR`, `jscan_eq_jscanTR`, `junescape_eq_junescapeTR`).
/// Without them a single 100 000-character line overflowed a 2 MiB stack —
/// the size of this test thread — and aborted the whole process.  A line of a
/// million request bytes, every other character a quote escaped on the way in
/// and on the way out, reads and writes back byte for byte.
#[test]
fn a_million_character_line_does_not_exhaust_the_stack() {
    let line = "a\\\"".repeat(333_334);
    let out = call(&format!(r#"{{"docs":[{{"path":"w.md","lines":["{line}"]}}],"cmds":[]}}"#))
        .unwrap();
    assert_eq!(out, format!(r#"{{"ok":{{"docs":[{{"path":"w.md","lines":["{line}"]}}],"report":{{"closes":[]}}}}}}"#));
}

/// **A comment is prose** (step 4, kernel/README.md 2026-09-12).  A starter
/// template's guidance comment held example item lines, so a fresh `tm init`
/// tree refused every kernel-backed verb.  Inside `<!-- … -->` an example
/// carrying the live item's own id, a broken item shape and a month-only
/// heading are all prose: the tree loads, comes back byte for byte, and a
/// command on `^m1` changes the live line and not the example.
#[test]
fn an_item_line_inside_a_comment_is_prose() {
    let doc = r##"{"path":"week/2026-W37.md","grain":1,"ix":35,"lines":["# Tasks","<!-- e.g.","    - [ ] 3 1b Example ^m1","- [Z] broken","# Demoted","-->","- [ ] 5 6b Finish the report ^m1"]}"##;
    let out = call(&format!(r#"{{"docs":[{doc}],"cmds":[]}}"#)).unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
    assert!(
        out.contains(r##"["# Tasks","<!-- e.g.","    - [ ] 3 1b Example ^m1","- [Z] broken","# Demoted","-->","- [ ] 5 6b Finish the report ^m1"]"##),
        "{out}"
    );
    let out = call(&format!(
        r#"{{"docs":[{doc}],"cmds":[{{"op":"est","id":"m1","min":90}}]}}"#
    ))
    .unwrap();
    assert!(out.contains(r#""    - [ ] 3 1b Example ^m1""#), "{out}");
    assert!(out.contains("est:90m"), "{out}");
    assert_eq!(out.matches("est:90m").count(), 1, "{out}");
    // The over-bite guard: with the markers gone the example is an item
    // again, and the repeated id is refused.
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["    - [ ] 3 1b Example ^m1","- [ ] 5 6b Finish the report ^m1"]}],"cmds":[]}"##,
    )
    .unwrap();
    assert_eq!(out, r#"{"err":{"dupId":"m1"}}"#, "{out}");
}

/// A comment still open at the end of a file is refused by name, at its
/// opener's line (0-based, as `badLine`), rather than silently swallowing
/// every item below it.
#[test]
fn an_unterminated_comment_is_refused_by_name() {
    let out = call(
        r##"{"docs":[{"path":"w.md","lines":["# Tasks","<!-- todo","- [ ] 3 x ^t1"]}],"cmds":[]}"##,
    )
    .unwrap();
    assert_eq!(
        out,
        r#"{"err":{"unterminatedComment":{"path":"w.md","line":1}}}"#,
        "{out}"
    );
}

// ---------------------------------------------------------------------------
// Stage 4 step 5 (2026-09-12): `close` and `autoClose` on the wire, `now` and
// `blockMin` in the request, and the per-item `report` under `ok` (D3).

/// The week close of `Boundary.lean`'s `closeWeekWitness`, closed on Monday
/// 2026-09-07: regions are the kernel's real calendar numbers.
const CLOSE_WEEK_DOCS: &str = r##"[{"path":"week/2026-W36.md","grain":1,"ix":105694,"lines":["# Tasks","- [ ] 4 6b Rollback path passes tests ^m2","- [x] 2 1b Send the draft ^t1","- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1","- [ ] 1 15m Standup every:day ^r1"]},{"path":"week/2026-W37.md","grain":1,"ix":105695,"lines":["# Tasks"]},{"path":"month/2026-09.md","grain":2,"ix":24308,"lines":["# Outcomes","- [ ] 5 !1 Lean through ch.8 ^O1","# Demoted","# Notes"]}]"##;

/// **The report is populated on a real close, through `String -> String`.**
/// The same lines `the_week_close_copies_carries_and_leaves_the_rest` decides,
/// and the same entries `the_week_close_reports_each_line` decides: the wall
/// carried from document 0 into the live week, unstamped, 120 minutes; the open
/// line copied into the month, stamped `W36`, 300 minutes at a 50-minute block.
/// Minutes are a numerator and a denominator — the kernel never divides.
#[test]
fn a_week_close_reports_each_line_it_touched() {
    let out = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{CLOSE_WEEK_DOCS},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(
        out,
        concat!(
            r##"{"ok":{"docs":["##,
            r##"{"path":"week/2026-W36.md","lines":["# Tasks","- [-] 4 6b Rollback path passes tests ^m2","- [x] 2 1b Send the draft ^t1","- [ ] 1 15m Standup every:day ^r1"],"grain":1,"ix":105694},"##,
            r##"{"path":"week/2026-W37.md","lines":["# Tasks","- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1"],"grain":1,"ix":105695},"##,
            r##"{"path":"month/2026-09.md","lines":["# Outcomes","- [ ] 5 !1 Lean through ch.8 ^O1","# Demoted","- [-] 4 6b Rollback path passes tests demoted:W36 ^m2","# Notes"],"grain":2,"ix":24308}],"##,
            r##""report":{"closes":["##,
            // Source order (kernel/README.md gap 59): `^m2` at rank 1 before
            // `^x1` at rank 3 — the fold used to take them the other way round.
            r##"{"id":"m2","grain":1,"did":"copy","from":0,"to":2,"stamp":"W36","min":{"num":300,"den":1}},"##,
            r##"{"id":"x1","grain":1,"did":"carry","from":0,"to":1,"stamp":null,"min":{"num":120,"den":1}}"##,
            r##"]}}}"##
        ),
        "{out}"
    );
    // L16 at the wire: the kernel's own output, closed again at the same
    // instant, changes nothing and reports nothing.
    let docs = out
        .trim_start_matches(r##"{"ok":{"docs":"##)
        .split(r##","report":"##)
        .next()
        .unwrap();
    let twice = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{docs},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(twice, format!(r#"{{"ok":{{"docs":{docs},"report":{{"closes":[]}}}}}}"#));
}

/// **`now` is never invented, and a malformed clock is refused by name.**  A
/// close without `now` is `nowAbsent`; without `blockMin`, `blockMinAbsent`; a
/// `now` that is not a real date is `badNow` — even on a request with no close;
/// a zero block is `badBlockMin`.  None of them writes anything.
#[test]
fn the_clock_is_refused_by_name() {
    let close = r#"[{"op":"close","grain":1}]"#;
    let out = call(&format!(r#"{{"blockMin":50,"docs":{CLOSE_WEEK_DOCS},"cmds":{close}}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"nowAbsent"}"#);
    let out = call(&format!(r#"{{"now":"2026-09-07","docs":{CLOSE_WEEK_DOCS},"cmds":[{{"op":"autoClose"}}]}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"blockMinAbsent"}"#);
    let out = call(&format!(r#"{{"now":"2026-02-30","blockMin":50,"docs":{CLOSE_WEEK_DOCS},"cmds":{close}}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"badNow"}"#);
    let out = call(&format!(r#"{{"now":"2026-9-7","docs":{CLOSE_WEEK_DOCS},"cmds":[]}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"badNow"}"#);
    let out = call(&format!(r#"{{"now":739870,"docs":{CLOSE_WEEK_DOCS},"cmds":[]}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"badNow"}"#);
    let out = call(&format!(r#"{{"now":"2026-09-07","blockMin":0,"docs":{CLOSE_WEEK_DOCS},"cmds":{close}}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"badBlockMin"}"#);
    let out = call(&format!(r#"{{"now":"2026-09-07","blockMin":50,"docs":{CLOSE_WEEK_DOCS},"cmds":[{{"op":"close","grain":3}}]}}"#)).unwrap();
    assert_eq!(out, r#"{"err":"grain 3 out of range (0..2)"}"#);
    // a request that closes nothing still needs no clock
    let out = call(&format!(r#"{{"docs":{CLOSE_WEEK_DOCS},"cmds":[]}}"#)).unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
}

/// A close refusal reaches the host by name, and carries no report: without
/// the month file the week close has nowhere to file its record.
#[test]
fn a_refused_close_is_named_and_reports_nothing() {
    let docs = CLOSE_WEEK_DOCS.split(r##",{"path":"month/2026-09.md""##).next().unwrap().to_string() + "]";
    let out = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{docs},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(out, r#"{"err":{"kernel":"noTarget"}}"#);
}

/// `Boundary.lean`'s `closeOverdueWitness`: 2026-W36 holding every dated case
/// the owner's D7 and D8 route, closed on Monday 2026-09-07.
const CLOSE_OVERDUE_DOCS: &str = r##"[{"path":"week/2026-W36.md","grain":1,"ix":105694,"lines":["# Tasks","- [ ] 4 2b Pset two due:2026-09-04 ^d1","- [ ] 3 1b Essay draft due:2026-09-20 ^d2","- [ ] 2 1b Quiz prep due:2026-09-03 on-miss:expire ^d3","- [ ] 5 2h Lab session at:2026-09-02T10:00/12:00 ^x2","- [ ] 1 1h Reading group at:2026-09-01T15:00/16:00 on-miss:next ^x3","- [ ] 2 1b Pset three due:2026-09-05T23:59 ^d4"]},{"path":"week/2026-W37.md","grain":1,"ix":105695,"lines":["# Tasks"]},{"path":"month/2026-09.md","grain":2,"ix":24308,"lines":["# Outcomes","- [ ] 5 !1 Lean through ch.8 ^O1","# Demoted"]},{"path":"backlog.md","lines":["# Untied","- [ ] 2 30m Insurance claim ^a1","# Overdue","# Later","- [ ] 1 1b Someday ^a2"]}]"##;

/// **Gap 55 closed, at the wire** (the owner's D7 and D8).  The same lines
/// `the_week_close_routes_dated_work_on_a_loaded_plan` decides and the same
/// entries `the_week_close_reports_the_overdue_route` decides: the three lines
/// past due with `persist` are `moveOverdue` into the backlog's `# Overdue`,
/// unstamped and byte for byte; the not-yet-due line and the past-due
/// `on-miss:expire` one are `copy` into `# Demoted`, keeping their `due:`; the
/// wall that is over with `on-miss:next` stays.  Closed again at the same
/// instant, nothing changes and nothing is reported (L16).
#[test]
fn a_week_close_routes_dated_work_on_the_wire() {
    let out = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{CLOSE_OVERDUE_DOCS},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(
        out,
        concat!(
            r##"{"ok":{"docs":["##,
            r##"{"path":"week/2026-W36.md","lines":["# Tasks","- [-] 3 1b Essay draft due:2026-09-20 ^d2","- [-] 2 1b Quiz prep due:2026-09-03 on-miss:expire ^d3","- [ ] 1 1h Reading group at:2026-09-01T15:00/16:00 on-miss:next ^x3"],"grain":1,"ix":105694},"##,
            r##"{"path":"week/2026-W37.md","lines":["# Tasks"],"grain":1,"ix":105695},"##,
            r##"{"path":"month/2026-09.md","lines":["# Outcomes","- [ ] 5 !1 Lean through ch.8 ^O1","# Demoted","- [-] 3 1b Essay draft due:2026-09-20 demoted:W36 ^d2","- [-] 2 1b Quiz prep due:2026-09-03 on-miss:expire demoted:W36 ^d3"],"grain":2,"ix":24308},"##,
            r##"{"path":"backlog.md","lines":["# Untied","- [ ] 2 30m Insurance claim ^a1","# Overdue","- [ ] 4 2b Pset two due:2026-09-04 ^d1","- [ ] 5 2h Lab session at:2026-09-02T10:00/12:00 ^x2","- [ ] 2 1b Pset three due:2026-09-05T23:59 ^d4","# Later","- [ ] 1 1b Someday ^a2"]}],"##,
            r##""report":{"closes":["##,
            r##"{"id":"d1","grain":1,"did":"moveOverdue","from":0,"to":3,"stamp":null,"min":{"num":100,"den":1}},"##,
            r##"{"id":"d2","grain":1,"did":"copy","from":0,"to":2,"stamp":"W36","min":{"num":50,"den":1}},"##,
            r##"{"id":"d3","grain":1,"did":"copy","from":0,"to":2,"stamp":"W36","min":{"num":50,"den":1}},"##,
            r##"{"id":"x2","grain":1,"did":"moveOverdue","from":0,"to":3,"stamp":null,"min":{"num":120,"den":1}},"##,
            r##"{"id":"d4","grain":1,"did":"moveOverdue","from":0,"to":3,"stamp":null,"min":{"num":50,"den":1}}"##,
            r##"]}}}"##
        ),
        "{out}"
    );
    // Without `# Overdue` the backlog is `noSection`: the kernel never
    // chooses where a heading goes (kernel/README.md gap 56).
    let no_section = CLOSE_OVERDUE_DOCS.replace(r##""# Overdue","##, "");
    let refused = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{no_section},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(refused, r#"{"err":{"kernel":"noSection"}}"#);
    let docs = out
        .trim_start_matches(r##"{"ok":{"docs":"##)
        .split(r##","report":"##)
        .next()
        .unwrap();
    let twice = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{docs},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(twice, format!(r#"{{"ok":{{"docs":{docs},"report":{{"closes":[]}}}}}}"#));
}

/// `Boundary.lean`'s `closeFoldWitness`: 2026-W36 with a stale `2b` milestone
/// whose subtasks add up to `3b` (and a grandchild with no estimate), a `6b`
/// milestone whose two `1b` subtasks it covers — one of them dated, with a
/// standing `# Demoted` record in September.
const CLOSE_FOLD_DOCS: &str = r##"[{"path":"week/2026-W36.md","grain":1,"ix":105694,"lines":["# Milestones","- [ ] 2b Stale milestone ^p1","- [ ] 6b Covered milestone ^p2","# Tasks","- [ ] 2b Part one @p1 ^c1","- [ ] 1b Part two @p1 ^c2","- [ ] Grandchild @c1 ^c4","- [ ] 1b Covered part @p2 ^c3","- [ ] 1b Dated part @p2 due:2026-09-30 ^c5"]},{"path":"month/2026-09.md","grain":2,"ix":24308,"lines":["# Outcomes","# Demoted","- [-] 1b Dated part @p2 est:1b due:2026-09-30 demoted:W35 ^c5"]}]"##;

/// **Goal B3's repair on the wire** (kernel/README.md "Stage 4 final, step 4";
/// `the_week_close_folds_dropped_children_on_a_loaded_plan` and
/// `the_week_close_reports_the_fold` decide the same request): the week close
/// drops each unfinished task under a milestone it files, `[~]` in place, and
/// floors the milestone's record by §6.4's `max` — `^p1` carries `est:3b`, `^p2`
/// only its stamp; `^c5`'s standing record stays unmerged.  The report names
/// `copyFolding` and `dropIntoParent`.  Closed again at the same instant,
/// nothing changes and nothing is reported (L16).
#[test]
fn a_week_close_folds_dropped_children_on_the_wire() {
    let out = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{CLOSE_FOLD_DOCS},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(
        out,
        concat!(
            r##"{"ok":{"docs":["##,
            r##"{"path":"week/2026-W36.md","lines":["# Milestones","- [-] 2b Stale milestone ^p1","- [-] 6b Covered milestone ^p2","# Tasks","- [~] 2b Part one @p1 ^c1","- [~] 1b Part two @p1 ^c2","- [~] Grandchild @c1 ^c4","- [~] 1b Covered part @p2 ^c3","- [~] 1b Dated part @p2 due:2026-09-30 ^c5"],"grain":1,"ix":105694},"##,
            r##"{"path":"month/2026-09.md","lines":["# Outcomes","# Demoted","- [-] 1b Dated part @p2 est:1b due:2026-09-30 demoted:W35 ^c5","- [-] 2b Stale milestone est:3b demoted:W36 ^p1","- [-] 6b Covered milestone demoted:W36 ^p2"],"grain":2,"ix":24308}],"##,
            r##""report":{"closes":["##,
            r##"{"id":"p1","grain":1,"did":"copyFolding","from":0,"to":1,"stamp":"W36","min":{"num":150,"den":1}},"##,
            r##"{"id":"p2","grain":1,"did":"copyFolding","from":0,"to":1,"stamp":"W36","min":{"num":300,"den":1}},"##,
            r##"{"id":"c1","grain":1,"did":"dropIntoParent","from":0,"to":0,"stamp":null,"min":{"num":100,"den":1}},"##,
            r##"{"id":"c2","grain":1,"did":"dropIntoParent","from":0,"to":0,"stamp":null,"min":{"num":50,"den":1}},"##,
            r##"{"id":"c4","grain":1,"did":"dropIntoParent","from":0,"to":0,"stamp":null,"min":null},"##,
            r##"{"id":"c3","grain":1,"did":"dropIntoParent","from":0,"to":0,"stamp":null,"min":{"num":50,"den":1}},"##,
            r##"{"id":"c5","grain":1,"did":"dropIntoParent","from":0,"to":0,"stamp":null,"min":{"num":50,"den":1}}"##,
            r##"]}}}"##
        ),
        "{out}"
    );
    // The block length is the fold's unit: at 60 minutes a block, `^p1`'s
    // subtasks are 180 minutes against its own 120, and the record says `3b`.
    let at60 = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":60,"docs":{CLOSE_FOLD_DOCS},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert!(at60.contains(r##""- [-] 2b Stale milestone est:3b demoted:W36 ^p1""##), "{at60}");
    let docs = out
        .trim_start_matches(r##"{"ok":{"docs":"##)
        .split(r##","report":"##)
        .next()
        .unwrap();
    let twice = call(&format!(
        r#"{{"now":"2026-09-07","blockMin":50,"docs":{docs},"cmds":[{{"op":"close","grain":1}}]}}"#
    ))
    .unwrap();
    assert_eq!(twice, format!(r#"{{"ok":{{"docs":{docs},"report":{{"closes":[]}}}}}}"#));
}

/// `Boundary.lean`'s `staleWitness`: a tree last closed in June, caught up on
/// Saturday 2026-09-12.
const STALE_DOCS: &str = r##"[{"path":"day/2026-06-12.md","grain":0,"ix":739778,"lines":["# Pinned","- [>] 2 20m Call the bank ^p1","- [x] 1 10m Water the plants ^p2"]},{"path":"day/2026-08-29.md","grain":0,"ix":739856,"lines":["# Pinned","- [>] 3 1h Draft the letter ^p3"]},{"path":"week/2026-W24.md","grain":1,"ix":105682,"lines":["# Tasks","- [ ] 4 6b Rollback path passes tests ^m2","- [x] 2 1b Send the draft ^t1","- [ ] 1 15m Standup every:day ^r1"]},{"path":"week/2026-W35.md","grain":1,"ix":105693,"lines":["# Tasks","- [ ] 3 2b Read chapter four ^m3","- [ ] 5 2h Midterm at:2026-10-20T10:00/12:00 ^x1"]},{"path":"week/2026-W37.md","grain":1,"ix":105695,"lines":["# Tasks","- [ ] 3 1b Review the drafts ^t5"]},{"path":"month/2026-06.md","grain":2,"ix":24305,"lines":["# Outcomes","- [ ] 5 !1 Old outcome ^O7","- [x] 3 !2 Done outcome ^O8","# Demoted","- [-] 4 3b Carried record est:3b demoted:W22 ^m9"]},{"path":"month/2026-09.md","grain":2,"ix":24308,"lines":["# Outcomes","- [ ] 5 !1 Lean through ch.8 ^O1","# Demoted"]}]"##;

/// **AGENTS §8.2's acceptance clause at the FFI: a three-month-stale tree
/// catches up in one call, losing nothing — and the report says so, per item.**
/// Owed by step 4 ("the FFI-level witness waits on the wire step").  The files
/// are the ones `the_stale_catch_up_observed` decides; the report names seven
/// lines, each once (`autoCloseR_names_each_line_at_most_once`), each with at
/// most one stamp; a second `autoClose` at the same instant changes nothing
/// and reports nothing (L19b).
#[test]
fn a_three_month_stale_tree_catches_up_in_one_call_and_reports_each_line() {
    let out = call(&format!(
        r#"{{"now":"2026-09-12","blockMin":50,"docs":{STALE_DOCS},"cmds":[{{"op":"autoClose"}}]}}"#
    ))
    .unwrap();
    let (docs, report) = out
        .trim_start_matches(r##"{"ok":{"docs":"##)
        .split_once(r##","report":"##)
        .unwrap_or_else(|| panic!("{out}"));
    assert_eq!(
        report,
        concat!(
            // Each grain's entries in source order — document, then rank
            // (kernel/README.md gap 59; before it every pair below was the
            // other way round).
            r##"{"closes":["##,
            r##"{"id":"p1","grain":0,"did":"moveReopening","from":0,"to":4,"stamp":"D12","min":{"num":20,"den":1}},"##,
            r##"{"id":"p3","grain":0,"did":"moveReopening","from":1,"to":4,"stamp":"D29","min":{"num":60,"den":1}},"##,
            r##"{"id":"m2","grain":1,"did":"copy","from":2,"to":6,"stamp":"W24","min":{"num":300,"den":1}},"##,
            r##"{"id":"m3","grain":1,"did":"copy","from":3,"to":6,"stamp":"W35","min":{"num":100,"den":1}},"##,
            r##"{"id":"x1","grain":1,"did":"carry","from":3,"to":4,"stamp":null,"min":{"num":120,"den":1}},"##,
            r##"{"id":"O7","grain":2,"did":"move","from":5,"to":6,"stamp":null,"min":null},"##,
            r##"{"id":"m9","grain":2,"did":"move","from":5,"to":6,"stamp":null,"min":{"num":150,"den":1}}"##,
            r##"]}}}"##
        ),
        "{out}"
    );
    // And the files keep it: the June day's `^p1` above the August day's `^p3`
    // in 2026-W37, and W24's record above W35's in September's `# Demoted`.
    assert!(
        docs.contains(r#""- [ ] 2 20m Call the bank demoted:D12 ^p1","- [ ] 3 1h Draft the letter demoted:D29 ^p3""#),
        "{out}"
    );
    assert!(
        docs.contains(r#""- [-] 4 6b Rollback path passes tests demoted:W24 ^m2","- [-] 3 2b Read chapter four demoted:W35 ^m3""#),
        "{out}"
    );
    assert!(docs.contains(r#""- [ ] 2 20m Call the bank demoted:D12 ^p1""#), "{out}");
    assert!(docs.contains(r#""- [-] 4 6b Rollback path passes tests demoted:W24 ^m2""#), "{out}");
    assert!(!docs.contains("demoted:D12,") && !docs.contains("demoted:D29,"), "{out}");
    let twice = call(&format!(
        r#"{{"now":"2026-09-12","blockMin":50,"docs":{docs},"cmds":[{{"op":"autoClose"}}]}}"#
    ))
    .unwrap();
    assert_eq!(twice, format!(r#"{{"ok":{{"docs":{docs},"report":{{"closes":[]}}}}}}"#));
}

/// **D6 on the wire: a parent is read off its line, and the tree is refused whole
/// when a link dangles** (kernel/README.md gap 22, closed at stage 4 final step 3;
/// `Boundary.lean`'s `a_typod_parent_refuses_the_whole_tree_by_name`). A week line
/// naming `@O9`, which no line carries, refuses every request by name — a command
/// included, which never runs, so there is nothing to write — and the same tree
/// with the typo fixed loads and round-trips.
#[test]
fn a_dangling_parent_refuses_the_whole_tree_by_name() {
    let typo = WEEK.replace("@O1 ^m1", "@O9 ^m1");
    assert_ne!(typo, WEEK, "the fixture no longer carries the line this test edits");
    for cmds in ["[]", r#"[{"op":"drop","id":"t3"}]"#] {
        let out = call(&format!("{{\"docs\":[{typo},{MONTH}],\"cmds\":{cmds}}}")).unwrap();
        assert_eq!(out, r##"{"err":{"itemCheck":"danglingParent"}}"##, "{cmds}: {out}");
    }
    let out = call(&req("[]")).unwrap();
    assert!(out.starts_with(r#"{"ok":"#), "{out}");
}

/// **A parent cycle refuses the whole tree, by its own name** — `parentCycle`,
/// not `danglingParent`: both links of `plan-conflicts`' ouroboros resolve.
/// `Boundary.lean`'s `a_parent_cycle_refuses_the_whole_tree_by_name`.
#[test]
fn a_parent_cycle_refuses_the_whole_tree_by_name() {
    let cyclic = WEEK.replace(
        r##""","# Tasks","##,
        r##""","# Tasks","- [ ] 3 1b Ouroboros head @y2 ^y1","- [ ] 3 1b Ouroboros tail @y1 ^y2","##,
    );
    assert_ne!(cyclic, WEEK, "the fixture no longer carries the heading this test edits");
    let out = call(&format!("{{\"docs\":[{cyclic},{MONTH}],\"cmds\":[]}}")).unwrap();
    assert_eq!(out, r##"{"err":{"itemCheck":"parentCycle"}}"##, "{out}");
}

/// **A parent resolves against the whole tree, and only there.** The week's
/// `@O1` names the month's outcome: handed over with the month, the week loads;
/// handed over alone, it is refused `danglingParent`. This is why the corpus
/// harness loads whole trees only (the owner's D6; AGENTS §7.1 check 6), and why
/// the host sends every file of the plan with every request.
#[test]
fn a_parent_in_another_file_resolves_only_in_the_whole_tree() {
    let whole = call(&req("[]")).unwrap();
    assert!(whole.starts_with(r#"{"ok":"#), "{whole}");
    let alone = call(&format!("{{\"docs\":[{WEEK}],\"cmds\":[]}}")).unwrap();
    assert_eq!(alone, r##"{"err":{"itemCheck":"danglingParent"}}"##, "{alone}");
}

/// **`add` links a parent its title names** — the title's `@O1` is read off the
/// line the kernel writes, like every field (D6) — and a title naming an id the
/// tree does not carry is refused `badItem` by the post-state's whole-plan check
/// rather than written.
#[test]
fn add_reads_a_parent_off_its_title_and_refuses_a_dangling_one() {
    let ok = call(&req(r#"[{"op":"add","seed":9,"doc":0,"title":"Read ch.7 @O1"}]"#)).unwrap();
    assert!(ok.starts_with(r#"{"ok":"#), "{ok}");
    assert!(ok.contains("Read ch.7 @O1 ^"), "{ok}");
    let bad = call(&req(r#"[{"op":"add","seed":9,"doc":0,"title":"Read ch.7 @O9"}]"#)).unwrap();
    assert_eq!(bad, r##"{"err":{"kernel":"badItem"}}"##, "{bad}");
}

// ---------------------------------------------------------------------------
// Stage 5 D9 B4: the `tz` and `log` sections of a request (Boundary.lean's
// `runWithLog`).  Lean-side twins: the_log_op_reads_a_four_line_tail,
// the_log_section_refuses_by_name, the_response_shapes_emit_in_build_order.
// ---------------------------------------------------------------------------

/// **The `log` op, by line.**  From line 1: a `drop` (a header with its id and,
/// since stage 5 D9 C6, its day 739,865, its mask bit and its display; and its
/// rendering in serde's bytes with the `tm log` column), a blank line, a line
/// that is not UTF-8 (`null`), and `{"ev":7}` (no `t`).  The answer comes after
/// `report`; the lines are the Lean witness's, byte for byte.  (B4 sent them from
/// line 7.)  Since W3 a request asking for headers resumes (from the empty checkpoint
/// here), so it carries `now`, and the answer ends with `reseal`.
#[test]
fn the_log_op_answers_by_line() {
    let out = call(r#"{"docs":[],"now":"2026-09-07","tz":{"key":"UTC","base":"+00:00:00","then":[]},"log":{"ckpt":null,"from":1,"lines":["{\"t\":\"2026-09-07T09:00:00Z\",\"ev\":\"drop\",\"id\":\"a1\"}","",null,"{\"ev\":7}"],"terminated":true,"want":{"headersFrom":1,"render":[1,2]}}}"#).unwrap();
    assert_eq!(
        out,
        r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":4,"warnings":[{"line":3,"w":"invalidUtf8"},{"line":4,"w":"noT"}],"facts":null,"headers":[[1,"drop","a1",739865,false,"2026-09-07 09:00"]],"render":[[1,"{\"t\":\"2026-09-07T09:00:00+00:00\",\"ev\":\"drop\",\"id\":\"a1\"}","2026-09-07 09:00"],[2,null,null]],"reseal":null}}}"#
    );
}

/// **The undo mask on the wire** (stage 5 D9 C1; Boundary.lean's
/// `the_log_op_answers_the_cancelled_lines`): a note, its undo, a blank line and
/// a note, from line 1, facts asked. The note on line 1 and its undo on line 2
/// are cancelled; `facts` sits after `warnings`, and is `null` when not asked.
/// C6 (design §8.4's view): the one day, 2026-09-07 (day 739,865 from 0001-01-01)
/// in UTC, has no record (notes create no day), a seam whose latest stamp is line
/// 4's note at 09:00:00 UTC (second 63,924,368,400 from 0001-01-01), and the
/// headers of the three entries, lines 1 and 2 cancelled; the blank line has none.
/// Nothing is done, no instance, no event, no replay warning, no demotion, close,
/// drop, leak or unknown event; the log has three entries.  W3: the facts are the
/// resume's answer in the codec shapes (the empty checkpoint's ledger day and horizon,
/// 0; a header's stamp and written offset in place of its display), and `reseal` ends
/// the answer.
#[test]
fn the_log_op_answers_the_cancelled_lines() {
    let utc = r#"{"key":"UTC","base":"+00:00:00","then":[]}"#;
    let lines = r#"["{\"t\":\"2026-09-07T09:00:00Z\",\"ev\":\"note\",\"text\":\"a\"}","{\"t\":\"2026-09-07T09:01:00Z\",\"ev\":\"undo\",\"of\":\"note\"}","","{\"t\":\"2026-09-07T09:00:00Z\",\"ev\":\"note\",\"text\":\"a\"}"]"#;
    let out = call(&format!(r#"{{"docs":[],"now":"2026-09-07","tz":{utc},"log":{{"ckpt":null,"from":1,"lines":{lines},"terminated":true,"want":{{"facts":true}}}}}}"#)).unwrap();
    assert_eq!(
        out,
        r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":4,"warnings":[],"facts":{"ledgerDay":0,"horizon":0,"items":[],"window":[],"instOther":[],"named":[],"days":[[739865,null,[null,[],[63924368400,0,false,0]],[],[],[],[],[],[[1,"note",null,true,[63924368400,0],[false,0]],[2,"undo",null,true,[63924368460,0],[false,0]],[4,"note",null,false,[63924368400,0],[false,0]]]]],"open":{"block":null,"interrupt":null},"lastDay":null,"lastEffective":[63924368400,0,false,0],"entryCount":3,"unknown":0,"longestLeak":null,"replayWarnings":[],"warnings":{"first":[],"overflow":0}},"headers":[],"render":[],"reseal":null}}}"#
    );
    let out = call(&format!(r#"{{"docs":[],"tz":{utc},"log":{{"ckpt":null,"from":1,"lines":{lines},"terminated":true,"want":{{"facts":false}}}}}}"#)).unwrap();
    assert!(out.contains(r#""warnings":[],"facts":null,"headers":[]"#), "{out}");
}

/// **The completion family on the wire** (stage 5 D9 C4; Boundary.lean's
/// `the_log_op_answers_the_completion_facts`): `routine s #1 maybe` at 09:00, `skip
/// s #1` at 09:01 and `event x` at 09:02. The unknown status is one replay warning
/// naming line 1 and `maybe`; the instance is the last record in file order, the
/// `skip`, an all-time instance (`#1` names no date); nothing is done; `event x` is
/// its own latest by instant and by date.  C6: in §8.4's view, grouped by where
/// each fact lives.  W3: in the codec shapes (an instance `[[item, inst], [stamp,
/// status, raw, actual]]`, `skipped` as 4; a named record `[[name, id], [[line,
/// stamp], [date, [line, stamp]]]]`; a replay warning `[line, raw]`).
#[test]
fn the_log_op_answers_the_completion_facts() {
    let utc = r#"{"key":"UTC","base":"+00:00:00","then":[]}"#;
    let lines = r##"["{\"t\":\"2026-09-07T09:00:00Z\",\"ev\":\"routine\",\"item\":\"s\",\"inst\":\"#1\",\"status\":\"maybe\"}","{\"t\":\"2026-09-07T09:01:00Z\",\"ev\":\"skip\",\"item\":\"s\",\"inst\":\"#1\"}","{\"t\":\"2026-09-07T09:02:00Z\",\"ev\":\"event\",\"name\":\"x\"}"]"##;
    let out = call(&format!(r#"{{"docs":[],"now":"2026-09-07","tz":{utc},"log":{{"ckpt":null,"from":1,"lines":{lines},"terminated":true,"want":{{"facts":true}}}}}}"#)).unwrap();
    assert_eq!(
        out,
        r##"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":3,"warnings":[],"facts":{"ledgerDay":0,"horizon":0,"items":[],"window":[],"instOther":[[["s","#1"],[[63924368460,0,false,0],4,"skipped",null]]],"named":[[["x",null],[[3,[63924368520,0,false,0]],[739865,[3,[63924368520,0,false,0]]]]]],"days":[[739865,null,[null,[],[63924368520,0,false,0]],[],[],[],[],[],[[1,"routine","s",false,[63924368400,0],[false,0]],[2,"skip","s",false,[63924368460,0],[false,0]],[3,"event",null,false,[63924368520,0],[false,0]]]]],"open":{"block":null,"interrupt":null},"lastDay":null,"lastEffective":[63924368520,0,false,0],"entryCount":3,"unknown":0,"longestLeak":null,"replayWarnings":[[1,"maybe"]],"warnings":{"first":[],"overflow":0}},"headers":[],"render":[],"reseal":null}}}"##
    );
}

/// **The day family on the wire** (stage 5 D9 C5; Boundary.lean's
/// `the_log_op_answers_the_day_facts`): `energy` at 09:00, the day's `wake` at 06:00
/// (slept 420) logged after it, and a `leak` gap of 20 minutes answered at 09:30. The
/// energy observation reads the wake's 420 (late binding); the day's record (a
/// positional array) holds the 09:10–09:30 `Idle` segment, the wake, its sleep, 20 leak
/// minutes, the longest 20 and the idle record; the global longest leak is the gap.
/// C6: in §8.4's view, the day's seam and headers beside its record.  W3: in the codec
/// shapes (the idle segment's kind is `[5, "leak"]`).
#[test]
fn the_log_op_answers_the_day_facts() {
    let utc = r#"{"key":"UTC","base":"+00:00:00","then":[]}"#;
    let lines = r#"["{\"t\":\"2026-09-07T09:00:00Z\",\"ev\":\"energy\",\"pred\":3,\"rep\":4,\"loc\":\"h\"}","{\"t\":\"2026-09-07T06:00:00Z\",\"ev\":\"wake\",\"slept_min\":420}","{\"t\":\"2026-09-07T09:30:00Z\",\"ev\":\"idle\",\"attributed\":\"leak\",\"min\":20}"]"#;
    let out = call(&format!(r#"{{"docs":[],"now":"2026-09-07","tz":{utc},"log":{{"ckpt":null,"from":1,"lines":{lines},"terminated":true,"want":{{"facts":true}}}}}}"#)).unwrap();
    assert_eq!(
        out,
        r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":3,"warnings":[],"facts":{"ledgerDay":0,"horizon":0,"items":[],"window":[],"instOther":[],"named":[],"days":[[739865,[null,[],0,0,0,[0,0,0,0,0,0],[],[],0,[],[[[63924369000,0,false,0],[63924370200,0,false,0],[5,"leak"]]],[63924357600,0,false,0],420,null,null,null,null,null,[],20,20,[[[63924370200,0,false,0],739865,"leak",20]],[],0,0,0,0,null],[null,[],[63924370200,0,false,0]],[[1,[63924368400,0,false,0],739865,3,4,0.0,"h",420,null,null,false]],[],[],[],[],[[1,"energy",null,false,[63924368400,0],[false,0]],[2,"wake",null,false,[63924357600,0],[false,0]],[3,"idle",null,false,[63924370200,0],[false,0]]]]],"open":{"block":null,"interrupt":null},"lastDay":739865,"lastEffective":[63924370200,0,false,0],"entryCount":3,"unknown":0,"longestLeak":[[63924370200,0,false,0],739865,20],"replayWarnings":[],"warnings":{"first":[],"overflow":0}},"headers":[],"render":[],"reseal":null}}}"#
    );
}

/// **The section's refusals, by name**, and a request without `tz` or `log`
/// answered as before.
#[test]
fn the_log_section_refuses_by_name() {
    let utc = r#"{"key":"UTC","base":"+00:00:00","then":[]}"#;
    for (req, want) in [
        (r#"{"docs":[],"log":{}}"#.to_string(), r#"{"err":{"log":"tzAbsent"}}"#),
        // W3: a checkpoint is read by its own smart decoder (G0's `badCkpt <field>`), and the reseal policy by field.
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"ckpt":{{}}}}}}"#), r#"{"err":{"log":{"badCkpt":"v"}}}"#),
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":[],"terminated":true,"reseal":{{}}}}}}"#), r#"{"err":{"log":{"badLogReq":"keepDays"}}}"#),
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":[],"terminated":true,"reseal":7}}}}"#), r#"{"err":{"log":{"badLogReq":"reseal"}}}"#),
        (format!(r#"{{"docs":[],"now":"2026-09-07","tz":{utc},"log":{{"from":1,"lines":[],"terminated":true,"reseal":{{"keepDays":32}}}}}}"#), r#"{"err":{"log":{"badLogReq":"keepDays"}}}"#),
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":[],"terminated":true,"want":{{"facts":7}}}}}}"#), r#"{"err":{"log":{"badLogReq":"facts"}}}"#),
        // W3: C1/C6's from-line-one rule is gone: a resume needs `now`, and its tail starts at the checkpoint's cut.
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":["x"],"terminated":true,"want":{{"facts":true}}}}}}"#), r#"{"err":{"log":{"badLogReq":"now"}}}"#),
        (format!(r#"{{"docs":[],"now":"2026-09-07","tz":{utc},"log":{{"from":2,"lines":["x"],"terminated":true,"want":{{"facts":true}}}}}}"#), r#"{"err":{"log":"cutMismatch"}}"#),
        (format!(r#"{{"docs":[],"now":"2026-09-07","tz":{utc},"log":{{"from":2,"lines":["x"],"terminated":true,"want":{{"headersFrom":2}}}}}}"#), r#"{"err":{"log":"cutMismatch"}}"#),
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":[7],"terminated":true}}}}"#), r#"{"err":{"log":{"badLogReq":"lines"}}}"#),
        (format!(r#"{{"docs":[],"tz":{utc},"log":{{"from":1,"lines":["x"],"terminated":true,"want":{{"render":[2]}}}}}}"#), r#"{"err":{"log":{"renderNotInTail":{"line":2}}}}"#),
        (r#"{"docs":[],"tz":{"key":"UTC","base":"-00:00:00","then":[]}}"#.to_string(), r#"{"err":{"log":{"badTz":"base"}}}"#),
        (r#"{"docs":[],"tz":{"key":"UTC","base":"+00:00:00","then":[["2026-03-08T08:00:00Z","+01:00:00"],["2026-03-08T08:00:00Z","+00:00:00"]]}}"#.to_string(), r#"{"err":{"log":{"badTz":"unsorted"}}}"#),
        (r#"{"docs":[],"tz":{"key":"UTC","base":"+00:00:00","then":[["2026-03-08T02:00:00-06:00","+01:00:00"]]}}"#.to_string(), r#"{"err":{"log":{"badTz":"instant"}}}"#),
        (format!(r#"{{"docs":[],"tz":{utc}}}"#), r#"{"ok":{"docs":[],"report":{"closes":[]}}}"#),
    ] {
        assert_eq!(call(&req).unwrap(), want, "{req}");
    }
}

// ===========================================================================
// Stage 5 D10 step L6: capacity on the wire (design §13.6; Boundary.lean's
// section "Stage 5 D10 L6").  A request may carry `tz` and `capacity`; the
// response gains `lookahead` after `report`, every unit count a digit string
// (D17), and every refusal is `{"err":{"capacity":"<name> <key>"}}`.
// ===========================================================================

/// Chicago's 2026 rules: two transitions (`Cal.chicago2026`).
const CHICAGO_2026: &str = r#""tz":{"key":"America/Chicago","base":"-06:00:00","then":[["2026-03-08T08:00:00Z","-05:00:00"],["2026-11-01T07:00:00Z","-06:00:00"]]}"#;

/// The fork's `capacity_lookahead.rs` week as the capacity section: the shipped
/// `config.toml` tables (`p_lounge` 0.9 Monday to Thursday, 0.8 Friday, 0.5
/// Saturday, 0.4 Sunday; arrival 07:00 weekdays, 10:00 weekends), the shipped
/// prior curves, `[day]`, `home_max_ci` and `[priority]`, woken at 06:05, seven
/// days, and — since stage 6 step L9 — **day 0's own inputs** instead of a day-0
/// histogram: the `at` stamp (07:00 on the spec Monday), `state.json`'s runtime
/// facts (nothing stored, at the lounge, no `--allow-home`) and the `[energy]`
/// decimals the posterior (R5) and the sleep debt (R10) read.  The kernel derives
/// day 0 from them and from this call's own replay (L5's `specInput`).
const SPEC_CAPACITY: &str = concat!(
    r#""capacity":{"pLounge":{"config":{"Mon":{"num":"9","den":"10"},"Tue":{"num":"9","den":"10"},"Wed":{"num":"9","den":"10"},"Thu":{"num":"9","den":"10"},"Fri":{"num":"8","den":"10"},"Sat":{"num":"5","den":"10"},"Sun":{"num":"4","den":"10"}}},"#,
    r#""arrival":{"config":{"Mon":"07:00","Tue":"07:00","Wed":"07:00","Thu":"07:00","Fri":"07:00","Sat":"10:00","Sun":"10:00"}},"#,
    r#""wake":{"sec":21900,"ns":0},"#,
    r#""prior":{"lounge":[{"from":{"num":0,"den":1},"to":{"num":1,"den":1},"level":4},{"from":{"num":1,"den":1},"to":{"num":5,"den":1},"level":5},{"from":{"num":5,"den":1},"to":{"num":8,"den":1},"level":4},{"from":{"num":8,"den":1},"to":{"num":10,"den":1},"level":3},{"from":{"num":10,"den":1},"to":null,"level":2}],"#,
    r#""home":[{"from":{"num":0,"den":1},"to":{"num":1,"den":1},"level":3},{"from":{"num":1,"den":1},"to":{"num":4,"den":1},"level":4},{"from":{"num":4,"den":1},"to":{"num":8,"den":1},"level":3},{"from":{"num":8,"den":1},"level":2}]},"#,
    r#""homeMaxCi":3,"day":{"breakMin":20,"breakAfterBlocks":2,"minLastBlockMin":30,"windowHours":{"num":8,"den":1},"windowCap":"19:00","budgetRatio":{"num":75,"den":100}},"#,
    r#""priority":{"bins":[{"num":5,"den":10},{"num":25,"den":100},{"num":1,"den":10}],"safety":{"num":13,"den":10},"defaultPriority":3},"#,
    r#""days":7,"at":"2026-09-07T07:00:00-05:00","#,
    r#""state":{"date":null,"window":null,"budget":null,"arrival":null,"loc":"lounge","allowHome":false},"#,
    r#""posterior":{"fullHours":{"num":3,"den":1},"zeroHours":{"num":6,"den":1}},"#,
    r#""sleep":{"shiftModel":null,"shiftConfig":{"neg":false,"num":1,"den":1},"underHours":{"num":7,"den":1}}}"#
);

/// **The `log` section every capacity request carries since step L9** (gap 93):
/// day 0 is derived from the replay of the *same* call (D24's seam), so a capacity
/// request without one is refused `day0WithoutLog`.  This log is empty, so today
/// has no sleep reading and no energy report.
const CAP_LOG: &str =
    r#""log":{"ckpt":null,"from":1,"lines":[],"terminated":true,"reseal":null,"want":{"facts":true,"headersFrom":null,"render":[]},"sealed":null}"#;

fn capacity_req(docs: &str, capacity: &str) -> String {
    capacity_req_log(docs, CAP_LOG, capacity)
}

/// The same, with the `log` section named (the test that asks for both answers).
fn capacity_req_log(docs: &str, log: &str, capacity: &str) -> String {
    format!(r#"{{"docs":[{docs}],"now":"2026-09-07","blockMin":60,{CHICAGO_2026},{log},{capacity}}}"#)
}

/// One day of the response, minutes per level times `capDen` as digit strings.
fn day_units(date: &str, minutes: [u128; 6]) -> String {
    let units: Vec<String> = minutes.iter().map(|m| format!("\"{}\"", m * 1_000_000_000_000_000_000u128)).collect();
    format!(r#"{{"day":"{date}","numAt":[{}]}}"#, units.join(","))
}

/// **The spec week in exact units** (D10, D17).  Day 0 is the **kernel's own**
/// since step L9: arriving at 07:00 with nothing stored and no walls, §8.1's
/// window runs to 15:00 and its seven blocks hold 240 minutes at level 4 and 180
/// at 5 (`Look.the_day_zero_histogram_is_not_limited_to_the_budget`; the request
/// used to hand in `[0, 0, 0, 60, 170, 180]`, a 410-minute split of the §4.3 day
/// that nothing derived).  Every later day mixes the two locations'
/// budget-limited days at its own weekday's weight.  Tuesday (`Look.the_expected_tuesday`: 36, 162, 162) and
/// Sunday (`Look.sunday_mixes_at_its_own_weight`: 72, 192, 48, 48) are decided
/// witnesses in `Lookahead.lean`; this checks the same numbers reach Rust, and
/// that units past `u64` read as `u128`.
#[test]
fn capacity_answers_the_spec_week_in_units() {
    let out = call(&capacity_req("", SPEC_CAPACITY)).unwrap();
    let days = [
        day_units("2026-09-07", [0, 0, 0, 0, 240, 180]),
        day_units("2026-09-08", [0, 0, 0, 36, 162, 162]),
        day_units("2026-09-09", [0, 0, 0, 36, 162, 162]),
        day_units("2026-09-10", [0, 0, 0, 36, 162, 162]),
        day_units("2026-09-11", [0, 0, 0, 72, 144, 144]),
        day_units("2026-09-12", [0, 0, 60, 180, 60, 60]),
        day_units("2026-09-13", [0, 0, 72, 192, 48, 48]),
    ];
    // The response carries the `log` answer too since L9 (the section day 0 is derived from), so
    // the exact bytes asserted are the lookahead's and the build order around them.
    assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"#), "{out}");
    assert!(
        out.ends_with(&format!(
            r#","lookahead":{{"den":"1000000000000000000","days":[{}]}}}}}}"#,
            days.join(",")
        )),
        "{out}"
    );
    // A unit count past u64 reads as u128 (170 minutes is 1.7·10^20 units).
    let units: u128 = "240000000000000000000".parse().unwrap();
    assert!(units > u64::MAX as u128);
    assert!(out.contains(r#""240000000000000000000""#), "{out}");
}

/// **The response carries the first `min(days, 7)` days** (design D10-8), and a
/// lookahead of zero days carries none.
#[test]
fn capacity_emits_at_most_seven_days() {
    let two = call(&capacity_req("", &SPEC_CAPACITY.replace(r#""days":7"#, r#""days":2"#))).unwrap();
    assert_eq!(two.matches(r#""day":"#).count(), 2, "{two}");
    let ten = call(&capacity_req("", &SPEC_CAPACITY.replace(r#""days":7"#, r#""days":10"#))).unwrap();
    assert_eq!(ten.matches(r#""day":"#).count(), 7, "{ten}");
    let none = call(&capacity_req("", &SPEC_CAPACITY.replace(r#""days":7"#, r#""days":0"#))).unwrap();
    assert!(none.ends_with(r#""lookahead":{"den":"1000000000000000000","days":[]}}}"#), "{none}");
}

/// **A calendar wall takes its hours out of the lookahead** (L2's walls through
/// `wallIndex`, indexed once from the loaded plan).  With Wednesday's weight
/// certain (1/1), Wednesday is the lounge's day: 180 minutes at 5 and 180 at 4.
/// The §4.3 meeting (12:50–13:50) moves the window's end and keeps the budget
/// (`a_loaded_wednesday_wall_moves_the_window_and_keeps_the_budget`).  A wall over
/// 07:00–19:00 moves the whole day: E7 extends the window by the wall's twelve
/// hours past the cap (L2's `windowEnd`; the cap bounds only the base), so the
/// free time is 19:00–03:00, 12.9 hours and more after the 06:05 wake, where the
/// lounge's prior is `10+`'s level 2: the 360-minute budget at level 2.
#[test]
fn a_calendar_wall_takes_its_hours_out_of_the_lookahead() {
    let certain = SPEC_CAPACITY.replace(r#""Wed":{"num":"9","den":"10"}"#, r#""Wed":{"num":"1","den":"1"}"#);
    let wed = |docs: &str| -> String {
        let out = call(&capacity_req(docs, &certain)).unwrap();
        let at = out.find(r#"{"day":"2026-09-09""#).unwrap_or_else(|| panic!("{out}"));
        out[at..].split('}').next().unwrap().to_string() + "}"
    };
    assert_eq!(wed(""), day_units("2026-09-09", [0, 0, 0, 0, 180, 180]));
    let meeting = r#"{"path":"calendar/2026-W37.md","lines":["- [ ] 3 Meeting w/ host      at:2026-09-09T12:50/13:50 loc:zoom ^g1"]}"#;
    assert_eq!(wed(meeting), day_units("2026-09-09", [0, 0, 0, 0, 180, 180]));
    let all_day = r#"{"path":"calendar/2026-W37.md","lines":["- [ ] 3 Offsite      at:2026-09-09T07:00/19:00 loc:zoom ^g1"]}"#;
    assert_eq!(wed(all_day), day_units("2026-09-09", [0, 0, 360, 0, 0, 0]));
}

/// **Merged (D9 B4 with D10 L6): one request carries `log` and `capacity`**, and
/// the answer is `docs`, `report`, `log`, then `lookahead` (design §10.2;
/// `runCap_answers_docs_report_log_lookahead`).  The `log` answer is the one a
/// request without `capacity` gets, and the `lookahead` the one a request
/// without `log` gets.  A refused `log` section refuses first.
#[test]
fn a_request_with_log_and_capacity_answers_both_in_build_order() {
    let log = r#""log":{"from":1,"lines":["{\"t\":\"2026-09-07T09:00:00Z\",\"ev\":\"drop\",\"id\":\"x\"}"],"terminated":true,"want":{"facts":true,"headersFrom":1}}"#;
    let both = call(&capacity_req_log("", log, SPEC_CAPACITY)).unwrap();
    let cap_only = call(&capacity_req("", SPEC_CAPACITY)).unwrap();
    let log_only = call(&format!(r#"{{"docs":[],"now":"2026-09-07","blockMin":60,{CHICAGO_2026},{log}}}"#)).unwrap();
    let log_at = both.find(r#","log":"#).expect("log key");
    let look_at = both.find(r#","lookahead":"#).expect("lookahead key");
    assert!(both.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":1,"#), "{both}");
    assert!(log_at < look_at);
    assert_eq!(&both[..look_at], &log_only[..log_only.len() - 2], "the log answer is the log op's");
    assert_eq!(&both[look_at..], &cap_only[cap_only.find(r#","lookahead":"#).unwrap()..], "the lookahead is the capacity op's");
    let refused = call(&capacity_req_log("", r#""log":{"from":0,"lines":[],"terminated":true}"#, SPEC_CAPACITY)).unwrap();
    assert_eq!(refused, r#"{"err":{"log":{"badLogReq":"from"}}}"#);
}

/// **A request without `capacity` is answered exactly as before**
/// (`callExport_without_capacity_is_call`), even when it carries `tz`.
#[test]
fn a_request_without_capacity_is_answered_as_before() {
    let plain = call(&req("[]")).unwrap();
    let with_tz = call(&format!("{{\"docs\":[{WEEK},{MONTH}],\"cmds\":[],{CHICAGO_2026}}}")).unwrap();
    assert_eq!(plain, with_tz);
    assert!(!plain.contains("lookahead"), "{plain}");
}

/// **Every capacity refusal is named** (design §13.6's table, §10.3; R10): one
/// edit of the spec request at a time, each refused with its name and key.
#[test]
fn every_capacity_refusal_is_named() {
    let base = capacity_req("", SPEC_CAPACITY);
    assert!(call(&base).unwrap().starts_with(r#"{"ok":"#));
    // Three refusals move to the **`log`** section at step L9, because every capacity request now
    // carries one and it reads the clock and the zone first.  The capacity section's own names are
    // still reachable — from a request with no `log` section — and are asserted below the loop.
    assert_eq!(
        call(&base.replacen(r#""now":"2026-09-07","#, "", 1)).unwrap(),
        r#"{"err":{"log":{"badLogReq":"now"}}}"#
    );
    assert_eq!(call(&base.replacen(r#""tz":{"#, r#""tzz":{"#, 1)).unwrap(), r#"{"err":{"log":"tzAbsent"}}"#);
    assert_eq!(
        call(&format!(r#"{{"docs":[],"blockMin":60,{CHICAGO_2026},{SPEC_CAPACITY}}}"#)).unwrap(),
        r#"{"err":{"capacity":"nowAbsent"}}"#
    );
    assert_eq!(
        call(&format!(r#"{{"docs":[],"now":"2026-09-07","blockMin":60,{SPEC_CAPACITY}}}"#)).unwrap(),
        r#"{"err":{"capacity":"tzAbsent"}}"#
    );
    // A capacity request with no `log` section has no replay to derive day 0 from (gap 93).
    assert_eq!(
        call(&format!(r#"{{"docs":[],"now":"2026-09-07","blockMin":60,{CHICAGO_2026},{SPEC_CAPACITY}}}"#)).unwrap(),
        r#"{"err":{"capacity":"day0WithoutLog"}}"#
    );
    // A lookahead past year 9999 needs its `at` stamp to move with its `now` (`nowDisagrees` is
    // checked at `mkInput?`, before the calendar bound).
    let far = base
        .replacen(r#""now":"2026-09-07""#, r#""now":"9999-12-30""#, 1)
        .replacen(r#""at":"2026-09-07T07:00:00-05:00""#, r#""at":"9999-12-30T07:00:00-05:00""#, 1);
    assert_eq!(call(&far).unwrap(), r#"{"err":{"capacity":"lookaheadTooLong"}}"#);
    let cases: &[(&str, &str, &str)] = &[
        (r#""blockMin":60,"#, "", "blockMinAbsent"),
        (r#""blockMin":60,"#, r#""blockMin":1441,"#, "badDay blockMin"),
        (r#""capacity":{"#, r#""capacity":7,"x":{"#, "badCapacity capacity"),
        (r#""pLounge":{"#, r#""pLoungeX":{"#, "badCapacity pLounge"),
        (r#""pLounge":{"config""#, r#""pLounge":{"model":[],"config""#, "badCapacity pLounge.model"),
        (r#""pLounge":{"config""#, r#""pLounge":{"cfg""#, "badCapacity pLounge.config"),
        (r#""Mon":{"num":"9","den":"10"}"#, r#""Mon":{"num":"9","den":"10000000000000000000"}"#, "weightPrecision pLounge.config.Mon"),
        (r#""Sat":{"num":"5","den":"10"}"#, r#""Sat":{"num":"12","den":"10"}"#, "weightAboveOne pLounge.config.Sat"),
        (r#""Fri":{"num":"8","den":"10"}"#, r#""Fri":{"num":8,"den":10}"#, "badWeight pLounge.config.Fri"),
        (r#""Thu":{"num":"9","den":"10"}"#, r#""Thu":{"num":"9","den":"0"}"#, "badWeight pLounge.config.Thu"),
        (r#","Sun":{"num":"4","den":"10"}}"#, "}", "badWeight pLounge.config.Sun"),
        (
            r#""pLounge":{"config""#,
            r#""pLounge":{"model":{"Wed":{"num":"1","den":"3"}},"config""#,
            "weightPrecision pLounge.model.Wed",
        ),
        (r#""arrival":{"#, r#""arrivalX":{"#, "badCapacity arrival"),
        (r#""arrival":{"config""#, r#""arrival":{"model":{"Tue":"7:00"},"config""#, "badClock arrival.model.Tue"),
        (r#""Thu":"07:00""#, r#""Thu":"24:00""#, "badClock arrival.config.Thu"),
        (r#""wake":{"sec":21900,"ns":0}"#, r#""wake":{"sec":86400,"ns":0}"#, "badWake"),
        (r#""wake":{"sec":21900,"ns":0}"#, r#""wake":"06:05""#, "badWake"),
        (r#""homeMaxCi":3"#, r#""energy":{"lounge":[4,5,5]},"homeMaxCi":3"#, "badCurve energy.lounge"),
        (r#""homeMaxCi":3"#, r#""energy":{"home":[3,4,4,4,3,3,3,2,2,2,2,256]},"homeMaxCi":3"#, "badCurve energy.home"),
        (r#""homeMaxCi":3"#, r#""energy":[],"homeMaxCi":3"#, "badCapacity energy"),
        (r#""prior":{"#, r#""priorX":{"#, "badCapacity prior"),
        (r#""prior":{"lounge""#, r#""prior":{"home":[],"lounge""#, "badPrior prior.home"),
        (r#""from":{"num":8,"den":1},"level":2}"#, r#""from":{"num":8,"den":1},"level":6}"#, "badLevel prior.home"),
        (
            r#"{"from":{"num":0,"den":1},"to":{"num":1,"den":1},"level":4}"#,
            r#"{"from":{"num":0,"den":1},"to":{"num":0,"den":1},"level":4}"#,
            "badStep prior.lounge",
        ),
        (
            r#"{"from":{"num":0,"den":1},"to":{"num":1,"den":1},"level":3}"#,
            r#"{"from":{"num":0,"den":1000001},"to":{"num":1,"den":1},"level":3}"#,
            "badStep prior.home",
        ),
        (
            r#"{"from":{"num":8,"den":1},"level":2}"#,
            r#"{"from":{"num":0,"den":1},"level":2}"#,
            "badStep prior.home",
        ),
        (r#""homeMaxCi":3"#, r#""homeMaxCi":6"#, "badCap homeMaxCi"),
        (r#""day":{"#, r#""dayX":{"#, "badCapacity day"),
        (r#""breakMin":20"#, r#""breakMin":1441"#, "badDay breakMin"),
        (r#""breakAfterBlocks":2"#, r#""breakAfterBlocks":65"#, "badDay breakAfterBlocks"),
        (r#""minLastBlockMin":30"#, r#""minLastBlockMin":0"#, "badDay minLastBlockMin"),
        (r#""windowHours":{"num":8,"den":1}"#, r#""windowHours":{"num":0,"den":1}"#, "badDay windowHours"),
        (r#""windowCap":"19:00""#, r#""windowCap":"19:60""#, "badClock day.windowCap"),
        (r#""budgetRatio":{"num":75,"den":100}"#, r#""budgetRatio":{"num":75,"den":0}"#, "badDay budgetRatio"),
        (r#""priority":{"#, r#""priorityX":{"#, "badCapacity priority"),
        (
            r#""bins":[{"num":5,"den":10},{"num":25,"den":100},{"num":1,"den":10}]"#,
            r#""bins":[{"num":1,"den":10},{"num":5,"den":10}]"#,
            "badBins",
        ),
        (r#""safety":{"num":13,"den":10}"#, r#""safety":{"num":0,"den":10}"#, "badSafety"),
        (r#""defaultPriority":3"#, r#""defaultPriority":5"#, "badDefaultPriority"),
        (r#""days":7"#, r#""days":"7""#, "badCapacity days"),
        (r#""days":7"#, r#""days":3661"#, "lookaheadTooLong"),
        // Stage 6 step L9: day 0's own inputs, each refused by name.
        (r#""at":"2026-09-07T07:00:00-05:00""#, r#""at":"not a stamp""#, "badAt at"),
        (r#""at":"2026-09-07T07:00:00-05:00""#, r#""at":"2026-09-08T07:00:00-05:00""#, "nowDisagrees at"),
        (r#""loc":"lounge""#, r#""loc":3"#, "badState state.loc"),
        (r#""allowHome":false"#, r#""allowHome":null"#, "badState state.allowHome"),
        (r#""state":{"#, r#""stateX":{"#, "badCapacity state"),
        (r#""fullHours":{"num":3,"den":1}"#, r#""fullHours":{"num":3,"den":0}"#, "badPosterior posterior.fullHours"),
        (r#""zeroHours":{"num":6,"den":1}"#, r#""zeroHours":{"num":6000000,"den":1}"#, "badPosterior posterior.zeroHours"),
        (r#""posterior":{"#, r#""posteriorX":{"#, "badCapacity posterior"),
        (r#""underHours":{"num":7,"den":1}"#, r#""underHours":{"num":7,"den":0}"#, "badSleep sleep.underHours"),
        (r#""shiftConfig":{"neg":false,"num":1,"den":1}"#, r#""shiftConfig":{"neg":3,"num":1,"den":1}"#, "badSleep sleep.shiftConfig"),
        (r#""shiftModel":null"#, r#""shiftModel":{"neg":false,"num":1,"den":0}"#, "badSleep sleep.shiftModel"),
        (r#""sleep":{"#, r#""sleepX":{"#, "badCapacity sleep"),
    ];
    for (from, to, name) in cases {
        assert_eq!(base.matches(from).count(), 1, "the edit {from:?} is not unique in the request");
        let out = call(&base.replacen(from, to, 1)).unwrap();
        assert_eq!(out, format!(r#"{{"err":{{"capacity":"{name}"}}}}"#), "{from:?} -> {to:?}");
    }
    // Merged with the D9 track's B4 (README gap 108): `tz` has one reader, B4's `readTz`, and a
    // malformed zone is refused by B4's `readLogSection` before the capacity section is read, with
    // B4's names (`transition` and `unsorted` were L6's `then` and `table`).  Only an absent zone
    // is the capacity section's refusal (`tzAbsent` above).
    let zone_cases: &[(&str, &str, &str)] = &[
        (r#""tz":{"key""#, r#""tz":3,"tzz":{"key""#, "shape"),
        (r#""key":"America/Chicago","#, "", "key"),
        (r#""base":"-06:00:00""#, r#""base":"-06:00""#, "base"),
        (r#"[["2026-03-08T08:00:00Z","-05:00:00"],"#, r#"["2026-03-08T08:00:00Z","#, "transition"),
        (
            r#""2026-03-08T08:00:00Z","-05:00:00"],["2026-11-01T07:00:00Z""#,
            r#""2026-11-01T07:00:00Z","-05:00:00"],["2026-03-08T08:00:00Z""#,
            "unsorted",
        ),
    ];
    for (from, to, why) in zone_cases {
        assert_eq!(base.matches(from).count(), 1, "the edit {from:?} is not unique in the request");
        let out = call(&base.replacen(from, to, 1)).unwrap();
        assert_eq!(out, format!(r#"{{"err":{{"log":{{"badTz":"{why}"}}}}}}"#), "{from:?} -> {to:?}");
    }
    // A `capacity` carried twice is `jget`'s refusal, as for every key the kernel reads.
    let twice = call(&base.replacen(r#""capacity":{"#, r#""capacity":{},"capacity":{"#, 1)).unwrap();
    assert_eq!(twice, r#"{"err":"duplicateKey capacity"}"#);
}

// ===========================================================================
// Stage 5 D10 step L8, kernel half: the grants on the wire (design §13.6,
// §13.8; Boundary.lean's L6 section, extended, and "Stage 5 D10 L8").  A
// capacity request may carry `candidates`; `lookahead` then gains `grants`,
// one per candidate in request order.  Gap 109: a capacity request with
// commands is refused by name.
// ===========================================================================

/// One candidate record, with `window`, `optional`, `overdue`, `mandatory` and
/// `hot` false (a test edits the text to set one).
fn cand(id: &str, ci: u8, root_prio: &str, remaining: u64, due: &str, wall: bool, yesterday: &str) -> String {
    format!(
        r#"{{"id":"{id}","ci":{ci},"rootPrio":{root_prio},"remaining":{remaining},"due":{due},"window":false,"wall":{wall},"optional":false,"overdue":false,"mandatory":false,"hot":false,"yesterday":{yesterday}}}"#
    )
}

/// The spec capacity for two days (day 0's 420 derived minutes at levels 4 and 5,
/// Tuesday's 36/162/162) with `candidates`.
fn spec_with_candidates(hysteresis: bool, items: &[String]) -> String {
    let base = SPEC_CAPACITY.replace(r#""days":7,"#, r#""days":2,"#);
    format!(r#"{},"candidates":{{"hysteresis":{hysteresis},"items":[{}]}}}}"#, &base[..base.len() - 1], items.join(","))
}

/// The five candidates of `Look.witnessCands`, on the spec days.
fn witness_items() -> Vec<String> {
    vec![
        cand("w", 3, "null", 60, r#""2026-09-07""#, true, "null"),
        cand("a2", 3, "null", 600, r#""2026-09-08""#, false, "null"),
        cand("a1", 3, "1", 30, r#""2026-09-07""#, false, "7"),
        cand("o", 3, "null", 20, r#""2026-09-07""#, false, "null").replace(r#""optional":false"#, r#""optional":true"#),
        cand("r", 2, "1", 50, "null", false, "null"),
    ]
}

/// **The grants, in request order, in exact units** (gaps 80 and 107).  The wall
/// and the optional enter nothing.  `^a1` (due Monday, listed third) is served
/// first: **420** minutes available at levels ≥ 3 — day 0 derived, step L9, where
/// the handed-in histogram used to say 410 — 39 reserved (R1's ceiling of
/// 30 × 1.3), `u = 39/420` in the `+3` bin, `p = k + 3 = 4` with its written
/// `!1`, held at 6 by yesterday's 7 (§7.4).  `^a2` (due Tuesday) then sees the
/// 381 minutes left plus Tuesday's 360: 741 against 780, IMPOSSIBLE, `p = 0`,
/// 39 minutes short.  `^r` is undated, pure rank: `k + 2 = 3`.  Without
/// hysteresis `^a1` is its raw 4.
#[test]
fn capacity_answers_grants_in_request_order() {
    let out = call(&capacity_req("", &spec_with_candidates(true, &witness_items()))).unwrap();
    let e18 = |m: u128| (m * 1_000_000_000_000_000_000u128).to_string();
    let grants = [
        r#"{"id":"w","class":"wall","k":3,"p":null,"rawP":null,"need":0,"until":null,"avail":"0","allocation":"0","shortfall":"0","bin":null}"#.to_string(),
        format!(
            r#"{{"id":"a2","class":"impossible","k":3,"p":0,"rawP":0,"need":780,"until":"2026-09-08","avail":"{}","allocation":"{}","shortfall":"{}","bin":null}}"#,
            e18(741),
            e18(741),
            e18(39)
        ),
        format!(
            r#"{{"id":"a1","class":"dated","k":1,"p":6,"rawP":4,"need":39,"until":"2026-09-07","avail":"{}","allocation":"{}","shortfall":"0","bin":3}}"#,
            e18(420),
            e18(39)
        ),
        r#"{"id":"o","class":"optional","k":3,"p":5,"rawP":5,"need":26,"until":null,"avail":"0","allocation":"0","shortfall":"0","bin":null}"#.to_string(),
        r#"{"id":"r","class":"rank","k":1,"p":3,"rawP":3,"need":65,"until":null,"avail":"0","allocation":"0","shortfall":"0","bin":null}"#.to_string(),
    ];
    let days = [day_units("2026-09-07", [0, 0, 0, 0, 240, 180]), day_units("2026-09-08", [0, 0, 0, 36, 162, 162])];
    // The response carries the `log` answer too since L9; the bytes asserted are the lookahead's.
    assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"#), "{out}");
    assert!(
        out.ends_with(&format!(
            r#","lookahead":{{"den":"1000000000000000000","days":[{}],"grants":[{}]}}}}}}"#,
            days.join(","),
            grants.join(",")
        )),
        "{out}"
    );
    let plain = call(&capacity_req("", &spec_with_candidates(false, &witness_items()))).unwrap();
    assert!(plain.contains(r#"{"id":"a1","class":"dated","k":1,"p":4,"rawP":4,"#), "{plain}");
    // No candidates: no `grants` key, and the lookahead is L6's, byte for byte.
    let none = call(&capacity_req("", SPEC_CAPACITY.replace(r#""days":7,"#, r#""days":2,"#).as_str())).unwrap();
    assert!(!none.contains("grants"), "{none}");
    let empty = call(&capacity_req("", &spec_with_candidates(true, &[]))).unwrap();
    assert_eq!(empty, none.replacen(r#"]}}}"#, r#"],"grants":[]}}}"#, 1));
}

/// **Every candidate refusal is named** (R10), and **gap 109: a capacity
/// request with commands is refused** (`runCap_refuses_commands_beside_capacity`).
#[test]
fn every_candidate_refusal_is_named() {
    let base = capacity_req("", &spec_with_candidates(true, &witness_items()));
    assert!(call(&base).unwrap().starts_with(r#"{"ok":"#));
    let cases: &[(&str, &str, &str)] = &[
        (r#"{"id":"a2","ci":3,"#, r#"{"id":"a2","ci":6,"#, "badCandidate 1 ci"),
        (r#""id":"a1","ci":3,"rootPrio":1"#, r#""id":"a1","ci":3,"rootPrio":5"#, "badCandidate 2 rootPrio"),
        (r#""remaining":600"#, r#""remaining":4294967296"#, "badCandidate 1 remaining"),
        (r#""remaining":600,"due":"2026-09-08""#, r#""remaining":600,"due":"2026-02-30""#, "badCandidate 1 due"),
        (r#""remaining":60,"due":"2026-09-07","window":false,"wall":true"#, r#""remaining":60,"due":"2026-09-07","window":false,"wall":"yes""#, "badCandidate 0 wall"),
        (r#""yesterday":7"#, r#""yesterday":8"#, "badCandidate 2 yesterday"),
        (r#"{"id":"r","#, r#"{"idx":"r","#, "badCandidate 4 id"),
        (r#""hysteresis":true,"#, "", "badCapacity candidates"),
        (r#""candidates":{"#, r#""candidates":[],"x":{"#, "badCapacity candidates"),
    ];
    for (from, to, name) in cases {
        assert_eq!(base.matches(from).count(), 1, "the edit {from:?} is not unique in the request");
        let out = call(&base.replacen(from, to, 1)).unwrap();
        assert_eq!(out, format!(r#"{{"err":{{"capacity":"{name}"}}}}"#), "{from:?} -> {to:?}");
    }
    let long_id = cand(&"x".repeat(1025), 3, "null", 30, "null", false, "null");
    let out = call(&capacity_req("", &spec_with_candidates(true, &[long_id]))).unwrap();
    assert_eq!(out, r#"{"err":{"capacity":"badCandidate 0 id"}}"#);
    let many: Vec<String> = (0..1025).map(|i| cand(&format!("c{i}"), 3, "null", 30, "null", false, "null")).collect();
    let out = call(&capacity_req("", &spec_with_candidates(true, &many))).unwrap();
    assert_eq!(out, r#"{"err":{"capacity":"tooManyCandidates"}}"#);
    let at_the_bound = call(&capacity_req("", &spec_with_candidates(true, &many[..1024]))).unwrap();
    assert_eq!(at_the_bound.matches(r#"{"id":"c"#).count(), 1024);
    // Gap 109: the walls are the documents as sent, so capacity and commands are never answered together.
    let doc = r#"{"path":"weeks/2026-W37.md","lines":["- [ ] Draft est:30m ^m1"]}"#;
    let with_cmd = format!(
        r#"{{"docs":[{doc}],"cmds":[{{"op":"est","id":"m1","min":45}}],"now":"2026-09-07","blockMin":60,{CHICAGO_2026},{CAP_LOG},{SPEC_CAPACITY}}}"#
    );
    assert_eq!(call(&with_cmd).unwrap(), r#"{"err":{"capacity":"capacityWithCommands"}}"#);
    let without = with_cmd.replacen(r#""cmds":[{"op":"est","id":"m1","min":45}],"#, "", 1);
    assert!(call(&without).unwrap().starts_with(r#"{"ok":{"docs":[{"path":"weeks/2026-W37.md""#));
    let empty_cmds = with_cmd.replacen(r#"[{"op":"est","id":"m1","min":45}]"#, "[]", 1);
    assert_eq!(call(&empty_cmds).unwrap(), call(&without).unwrap());
}

/// A candidate record with a `floor` object appended (stage 5 D10 L8 host half, gap 79).
fn with_floor(rec: &str, floor: &str) -> String {
    format!("{},\"floor\":{floor}}}", rec.strip_suffix('}').expect("a record"))
}

/// **The floor pass reads what the pass left** (`Look.prioritiesWithFloors`, gap 79).
/// `^a2` owes 100 minutes (need 130), so after `^a1`'s 39 and `^a2`'s 130 the pass
/// leaves 251 minutes at levels ≥ 3 on Monday (day 0 derived, step L9: 420, where
/// the handed-in histogram used to say 410) and all of Tuesday's 360.  `^r` (level
/// 2, undated, `!1`) has a floor of 120 minutes (need 156): to Tuesday it sees 611,
/// `u ≈ 0.26`, the `+1` bin, `p = 2`; to Monday 251, `u ≈ 0.62`, the `+0` bin,
/// `p = 1`.  The optional's floor of 10 minutes shows 251 available and 13 allocated
/// and stays `p = 5`.  `^a1`'s floor is ignored (it enters the pass), and a floor
/// reserves nothing: `^a2`'s grant is the same with and without the floors.
#[test]
fn a_floor_is_answered_over_what_the_pass_left() {
    let e18 = |m: u128| (m * 1_000_000_000_000_000_000u128).to_string();
    let mut items = witness_items();
    items[1] = items[1].replace(r#""remaining":600"#, r#""remaining":100"#);
    let bare = call(&capacity_req("", &spec_with_candidates(true, &items))).unwrap();
    items[2] = with_floor(&items[2], r#"{"left":30,"until":"2026-09-07"}"#);
    items[3] = with_floor(&items[3], r#"{"left":10,"until":"2026-09-07"}"#);
    items[4] = with_floor(&items[4], r#"{"left":120,"until":"2026-09-08"}"#);
    let out = call(&capacity_req("", &spec_with_candidates(true, &items))).unwrap();
    let r = format!(
        r#"{{"id":"r","class":"floor","k":1,"p":2,"rawP":2,"need":156,"until":"2026-09-08","avail":"{}","allocation":"{}","shortfall":"0","bin":1}}"#,
        e18(611),
        e18(156)
    );
    assert!(out.contains(&r), "{out}");
    let o = format!(
        r#"{{"id":"o","class":"optional","k":3,"p":5,"rawP":5,"need":13,"until":"2026-09-07","avail":"{}","allocation":"{}","shortfall":"0","bin":3}}"#,
        e18(251),
        e18(13)
    );
    assert!(out.contains(&o), "{out}");
    // The grants of the candidates that enter are the same bytes with and without floors.
    let grant_of = |resp: &str, id: &str| -> String {
        let at = resp.find(&format!(r#"{{"id":"{id}","#)).expect("a grant");
        resp[at..at + resp[at..].find('}').expect("its end") + 1].to_string()
    };
    for id in ["w", "a2", "a1"] {
        assert_eq!(grant_of(&out, id), grant_of(&bare, id), "{id}");
    }
    items[4] = items[4].replace(r#""until":"2026-09-08""#, r#""until":"2026-09-07""#);
    let monday = call(&capacity_req("", &spec_with_candidates(true, &items))).unwrap();
    assert!(
        monday.contains(&format!(
            r#"{{"id":"r","class":"floor","k":1,"p":1,"rawP":1,"need":156,"until":"2026-09-07","avail":"{}","allocation":"{}","shortfall":"0","bin":0}}"#,
            e18(251),
            e18(156)
        )),
        "{monday}"
    );
    // A floor the pass left nothing for is IMPOSSIBLE: the whole of `^a2`'s 600 minutes.
    let mut starved = witness_items();
    starved[4] = with_floor(&starved[4], r#"{"left":120,"until":"2026-09-08"}"#);
    let out = call(&capacity_req("", &spec_with_candidates(true, &starved))).unwrap();
    assert!(
        out.contains(&format!(
            r#"{{"id":"r","class":"impossible","k":1,"p":0,"rawP":0,"need":156,"until":"2026-09-08","avail":"0","allocation":"0","shortfall":"{}","bin":null}}"#,
            e18(156)
        )),
        "{out}"
    );
    // Every floor refusal is named by the record's position.
    for (floor, at) in [
        (r#"{"left":4294967296,"until":"2026-09-08"}"#, 4),
        (r#"{"left":120,"until":"2026-02-30"}"#, 4),
        (r#"{"left":120}"#, 4),
        ("1", 4),
    ] {
        let mut bad = witness_items();
        bad[at] = with_floor(&bad[at], floor);
        let out = call(&capacity_req("", &spec_with_candidates(true, &bad))).unwrap();
        assert_eq!(out, format!(r#"{{"err":{{"capacity":"badCandidate {at} floor"}}}}"#), "{floor}");
    }
    let mut null = witness_items();
    null[4] = with_floor(&null[4], "null");
    assert_eq!(
        call(&capacity_req("", &spec_with_candidates(true, &null))).unwrap(),
        call(&capacity_req("", &spec_with_candidates(true, &witness_items()))).unwrap()
    );
}
