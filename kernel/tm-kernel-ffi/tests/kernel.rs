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
    assert_eq!(
        out, r##"{"ok":{"docs":[{"lines":["- [-] 5 6b Old work ^m1"],"path":"w.md"}]}}"##,
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
    // the live line is the one in the month file, and it is the one that drops
    for out in [&forwards, &backwards] {
        let month = out
            .split(r#""lines":"#)
            .find(|s| s.contains("m.md"))
            .unwrap();
        let week = out
            .split(r#""lines":"#)
            .find(|s| s.contains("w.md"))
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
#[test]
fn the_spec_demotion_pair_round_trips() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,
              "lines":["# Milestones","- [ ] 4 6b Rollback path passes tests   @O2 ^m2"]},
             {"path":"month/2026-09.md","grain":2,"ix":8,
              "lines":["# Demoted","- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"]}],
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
/// second `demote` is refused rather than picking one of the two lines to
/// drop — overwrite the standing tombstone and `w.md` comes back empty with
/// `ok`; keep it and the line the record is leaving disappears instead.
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
        .split("{\"grain\"")
        .find(|s| s.contains("w.md"))
        .unwrap();
    assert!(
        week.contains("- [-] 5 6b Work ^m1"),
        "no stamp in the week file: {out}"
    );
    assert!(out.contains("- [-] 5 6b Work demoted:W37 ^m1"), "{out}");
}

/// **`readopt` is a demoted line or it is nothing** (§6.3: "moves a *demoted
/// line* into the current week, `[-]` -> `[ ]`, stamp kept"). Run on §4.3's
/// fixture — where the record is already `[ ]` and the tombstone is the line
/// carrying `est:` = remaining and the stamp — consuming the tombstone threw
/// both away and returned `ok`. "Stamp kept" was exactly what was lost.
#[test]
fn readopt_of_a_live_record_is_refused_rather_than_losing_the_stamp() {
    let out = call(
        r##"{"docs":[{"path":"week/2026-W37.md","grain":1,"ix":35,
              "lines":["- [ ] 4 6b Rollback path passes tests   @O2 ^m2"]},
             {"path":"month/2026-09.md","grain":2,"ix":8,
              "lines":["# Demoted","- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"]}],
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
        .trim_end_matches("}}");
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
