//! **`.tm/cache/replay/tz.json` is served only when it is this binary's zone table** — when its text
//! matches the digest it opens with (the W-44 repair, README gap 4613: D93's rule for the replay
//! cache's month files and D98's for its checkpoint, reached at the third file of that directory) AND,
//! since the owner's **D104** (README gaps 4621 and 4711; stage 6 W-46 track H), when its table reads
//! what the binary's own zone database reads at every second the kernel can read through it
//! (`tz_table::agrees`). A table that fails either is rebuilt — on disk when the cache can be written,
//! in memory when it cannot — and never served. Driven through the binary.
//!
//! **The defect the digest closed, as the W-44 critic drove it.**  The zone table is the one fact of
//! the cache that decides which local DATE an instant falls on.  One offset of a cached table changed
//! by hand or by a disk fault, its `key` kept, was served as written: at 23:58 every verb was refused
//! `nowDisagrees` (the request's `now` and the table disagree about the date), and at 00:10 the
//! evening's twenty minutes were credited to the NEXT day — a day's minutes moved to another date with
//! nothing said, the silent wrong answer D93 names.
//!
//! **The defect D104 closes.**  A digest says a file is what its writer wrote, never that its writer
//! read the zone as this binary does.  Until W-46 the same edit with its digest RECOMPUTED — a table a
//! binary could have written — was served, and this file asserted so ("a table whose digest matches is
//! trusted as written (D13)", in the test then named only_the_digest_stands_between_a_changed_offset_and_the_days_minutes).
//! The W-45 switch measured what that costs once the kernel plans the day: the kernel planned in the
//! cached table while the host decoded the day's instants in chrono-tz's, so `tm plan`, `tm now` and
//! `tm review day` faulted "this is a bug in tm" and `tm check` said `no problems` — two readers of one
//! zone (AGENTS §5.3).  D104 withdraws "trusted as written" for the zone table: a table that disagrees
//! with the binary is stale, not authoritative (D13: the cache is derived), and is rebuilt.  The
//! restated assertion is [`a_changed_offset_never_reaches_the_days_minutes_whether_or_not_its_digest_matches`];
//! the CLASS — every way a served table can disagree, against every planning verb, the history and the
//! unwritable cache included — is [`every_planted_table_answers_as_a_cache_less_tree`]; the check's own
//! two directions are [`the_check_refuses_every_edit_of_a_table_and_accepts_its_probe`] and
//! [`every_span_of_every_zone_outlasts_the_checks_step_and_every_probe_agrees`], the second the measured
//! fact the check's one-day grid stands on.

mod cli_common;

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use std::fs;
use std::path::Path;

use cli_common::{ckpt_redigested, Out, Tm};
use serde_json::Value;
use tempfile::TempDir;
use tz_table::ZoneTable;

/// The evening the critic drove: a wake at 23:30 on Sunday 2026-09-06, `^m1` 23:35-23:55.
fn evening() -> Tm {
    let tm = Tm::empty();
    tm.ok_at("2026-09-06T23:00:00-05:00", &["init", "--example"]);
    tm.ok_at("2026-09-06T23:30:00-05:00", &["wake", "23:30"]);
    tm.ok_at("2026-09-06T23:35:00-05:00", &["start", "^m1", "--energy", "3"]);
    tm.ok_at("2026-09-06T23:55:00-05:00", &["stop"]);
    tm
}

fn zone_file(tm: &Tm) -> std::path::PathBuf {
    tm.plan.join(".tm/cache/replay/tz.json")
}

/// `tm review day`'s date and block minutes at `now`.
fn reviewed(tm: &Tm, now: &str) -> (String, u64) {
    let v = tm.json_at(now, &["review", "day"]);
    (v["review"]["date"].as_str().expect("a date").to_string(), v["review"]["block_min"].as_u64().expect("block_min"))
}

/// The table with the offset in force from 2026-03-08 (Chicago's spring change) moved from
/// `-05:00:00` to `-03:00:00`, every other byte kept — the digest as it was.
fn planted(tm: &Tm) -> String {
    let text = fs::read_to_string(zone_file(tm)).expect("tz.json");
    let from = "[\"2026-03-08T08:00:00Z\",\"-05:00:00\"]";
    assert_eq!(text.matches(from).count(), 1, "the 2026 spring change, once");
    text.replace(from, "[\"2026-03-08T08:00:00Z\",\"-03:00:00\"]")
}

#[test]
fn the_zone_table_opens_with_the_digest_of_the_rest_of_its_text() {
    let tm = evening();
    let text = fs::read_to_string(zone_file(&tm)).expect("tz.json written by the first capacity verb");
    assert!(text.starts_with("{\"digest\":\""), "{}", &text[..text.len().min(80)]);
    assert_eq!(ckpt_redigested(&text), text, "the digest is the harness's FNV-1a-64 of the rest of the text");
}

/// **The assertion D104 restates** (README gap 4621).  The planted offset with its digest RECOMPUTED —
/// a table a binary could have written — is rebuilt and never served: the evening's minutes stay
/// Sunday's at 00:10 Monday, and the file is rewritten with the probe.  Before W-46 this was the bite of
/// the W-44 repair's test and read the other way: the re-digested edit was served, the minutes moved to
/// Monday, and the test said "a table whose digest matches is trusted as written (D13)" — the sentence
/// D104 withdraws.  With the digest left as it was the table is rebuilt as before (W-44), at both
/// instants the critic drove.
#[test]
fn a_changed_offset_never_reaches_the_days_minutes_whether_or_not_its_digest_matches() {
    let tm = evening();
    let sunday = ("2026-09-06".to_string(), 20);
    assert_eq!(reviewed(&tm, "2026-09-06T23:58:00-05:00"), sunday);
    assert_eq!(reviewed(&tm, "2026-09-07T00:10:00-05:00"), ("2026-09-07".to_string(), 0));
    let truth = fs::read_to_string(zone_file(&tm)).expect("tz.json");

    let consistent = ckpt_redigested(&planted(&tm));
    fs::write(zone_file(&tm), &consistent).expect("a table a binary could have written");
    assert_eq!(
        reviewed(&tm, "2026-09-07T00:10:00-05:00"),
        ("2026-09-07".to_string(), 0),
        "a table whose digest matches and whose offsets the binary's zone database does not read was served (D104)"
    );
    assert_eq!(fs::read_to_string(zone_file(&tm)).expect("rewritten"), truth, "the probe is written back (D104)");

    fs::write(zone_file(&tm), &truth).expect("the table as the binary wrote it");
    fs::write(zone_file(&tm), planted(&tm)).expect("the planted table, its digest as it was");
    assert_ne!(fs::read_to_string(zone_file(&tm)).expect("tz.json"), truth);
    assert_eq!(reviewed(&tm, "2026-09-06T23:58:00-05:00"), sunday, "a table that does not match its digest was served");
    assert_eq!(fs::read_to_string(zone_file(&tm)).expect("rewritten"), truth, "the probe is written back");
    fs::write(zone_file(&tm), planted(&tm)).expect("planted again");
    assert_eq!(reviewed(&tm, "2026-09-07T00:10:00-05:00"), ("2026-09-07".to_string(), 0));
}

/// **`tm check` meets the day the planning verbs meet** (README gaps 4711 and 4742, the W-45
/// repair) — an instrument landed BEFORE the change it watches (D21). On the tree above — the
/// planted offset with its digest recomputed — `tm check` and `tm plan` must agree on whether the
/// day reads: both answer, or neither does. Before R3 both answer (fork 4748911's planner plans
/// `tm plan`'s day, and `tm check` asks the kernel for the day it will plan, P78). With R3 built as
/// the W-45 switch first built it, `tm plan`, `tm now` and `tm review day` faulted on this tree
/// (README gap 4621, the R3 BLOCKER) while `tm check` sent the request, never decoded the answer,
/// and printed `no problems` at exit 0 (gap 4711) — the switch's archived commit reads the answer
/// with the one decoder `tm plan` reads it with (`kernel_capacity::read_day`, gap 4742). The owner's
/// ruling on gap 4621 is D104 (W-46): the table is rebuilt before either verb reads it, so both
/// answer, on the unswitched binary and the switched one alike; this test holds under either.
#[test]
fn tm_check_reads_the_day_with_the_decoder_tm_plan_reads_it_with() {
    let tm = evening();
    fs::write(zone_file(&tm), ckpt_redigested(&planted(&tm))).expect("a table a binary could have written");
    let now = "2026-09-07T00:10:00-05:00";
    let check = tm.run_at(now, &["check"]);
    let plan = tm.run_at(now, &["--json", "plan"]);
    assert_eq!(
        check.code == 0,
        plan.code == 0,
        "`tm check` and `tm plan` disagree about whether the day reads:\n  check {}: {}{}\n  plan  {}: {}{}",
        check.code,
        check.stdout,
        check.stderr,
        plan.code,
        &plan.stdout[..plan.stdout.len().min(300)],
        plan.stderr
    );
    if plan.code != 0 {
        assert!(!check.stdout.contains("no problems"), "`tm check` says no problems on a tree `tm plan` cannot plan: {}", check.stdout);
    }
}

// ------------------------------------------------------------------------------------------------
// D104 as a CLASS (stage 6 W-46 track H).
// ------------------------------------------------------------------------------------------------

/// `from` copied into a fresh temporary directory.
fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("create dir");
    for entry in fs::read_dir(from).expect("read dir") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

/// Every file under `root`, by path relative to it, with its bytes.
fn files_of(root: &Path) -> Vec<(String, Vec<u8>)> {
    fn walk(root: &Path, dir: &Path, out: &mut Vec<(String, Vec<u8>)>) {
        let mut entries: Vec<_> = fs::read_dir(dir).expect("read dir").map(|e| e.expect("entry")).collect();
        entries.sort_by_key(|e| e.file_name());
        for e in entries {
            if e.file_type().expect("file type").is_dir() {
                walk(root, &e.path(), out);
            } else {
                let rel = e.path().strip_prefix(root).expect("under the root").to_string_lossy().into_owned();
                out.push((rel, fs::read(e.path()).expect("read file")));
            }
        }
    }
    let mut out = Vec::new();
    walk(root, root, &mut out);
    out
}

/// Every file of a plan directory as [`files_of`] reads it, the replay cache's generation tags named
/// alike: `kernel_log::fresh_gen` draws a tag from the clock, the process and a random key, so two trees
/// that replay one log alike write two tags — in the checkpoint, in its digest, and in the sealed month
/// files' names — and nothing else of theirs differs.
fn files_normalized(root: &Path) -> Vec<(String, Vec<u8>)> {
    let files = files_of(root);
    let mut tags: Vec<(String, &str)> = Vec::new();
    if let Some((_, b)) = files.iter().find(|(r, _)| r == ".tm/cache/replay/ckpt.json") {
        let text = String::from_utf8_lossy(b).into_owned();
        let digest = text.get(11..27).expect("the checkpoint opens with its digest").to_string();
        let v: Value = serde_json::from_str(&format!("{{{}", text.get(29..).expect("then the rest"))).expect("the checkpoint");
        for (key, name) in [("gen", "<gen>"), ("prevGen", "<prevGen>")] {
            if let Some(g) = v[key].as_str().filter(|g| !g.is_empty()) {
                tags.push((g.to_string(), name));
            }
        }
        tags.push((digest, "<digest>"));
    }
    let mut out: Vec<(String, Vec<u8>)> = files
        .into_iter()
        .map(|(rel, bytes)| {
            let (mut rel, mut text) = (rel, String::from_utf8_lossy(&bytes).into_owned());
            for (tag, name) in &tags {
                rel = rel.replace(tag.as_str(), name);
                text = text.replace(tag.as_str(), name);
            }
            (rel, text.into_bytes())
        })
        .collect();
    out.sort();
    out
}

/// The world's plan directory copied, with its replay cache replaced: no cache at all (`None`), or a
/// cache holding `tz.json` alone, with `text` (`Some`).  With the cache empty of everything else, the
/// first verb replays the whole log through the table it is served — history included.
fn copy_with_cache(world: &Tm, zone: Option<&str>) -> Tm {
    let tmp = TempDir::new().expect("temp dir");
    let plan = tmp.path().join("plan");
    copy_dir(&world.plan, &plan);
    fs::remove_dir_all(plan.join(".tm/cache")).expect("the world has a cache");
    if let Some(text) = zone {
        fs::create_dir_all(plan.join(".tm/cache/replay")).expect("the cache directory");
        fs::write(plan.join(".tm/cache/replay/tz.json"), text).expect("the planted table");
    }
    Tm { tmp, plan }
}

/// A table written back as `tz.json` writes it, its digest recomputed — a file a binary COULD have
/// written, so only D104's check stands between it and the kernel.
fn written(table: &ZoneTable) -> String {
    tz_table::cache_text(&table.to_wire())
}

/// One planted world: what is planted, where the comparison runs, and the verbs it runs.
struct Plant {
    name: &'static str,
    zone: String,
    unwritable: bool,
    steps: Vec<(&'static str, Vec<&'static str>)>,
}

/// The verbs that plan or read a day, run in order at `now` (they write, and the two trees stay in step).
fn day_verbs(now: &'static str) -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        (now, vec!["--json", "plan"]),
        (now, vec!["--json", "now"]),
        (now, vec!["--json", "review", "day"]),
        (now, vec!["--json", "review", "week"]),
        (now, vec!["check"]),
        (now, vec!["plan"]),
    ]
}

fn said(o: &Out) -> String {
    format!("exit {}\n--- stdout\n{}\n--- stderr\n{}", o.code, o.stdout, o.stderr)
}

/// **Every planted table answers as a cache-less tree** (the owner's D104, as a CLASS; README gaps 4621
/// and 4711).  The evening world (Sunday 2026-09-06, `^m1` 23:35-23:55) is copied twice for each plant:
/// once with `.tm/cache/replay/` holding ONLY the planted `tz.json` — so the first verb replays the
/// whole log, history and all, through whatever table it is served — and once with no cache at all.
/// The verbs that plan or read a day run on both, in the same order at the same instants, and must say
/// the same — exit code, stdout and stderr, verb by verb — and leave the same files, the cache included
/// (the rebuilt `tz.json` is the probe, as the cache-less tree's is).  The plants, every one with its
/// digest RECOMPUTED, so only D104's check refuses it:
///
/// * **offset** — the W-44 edit: the offset in force from 2026-03-08 moved to `-03:00:00` (the planned
///   day's own span);
/// * **truncated** — every transition from 2026-03-08 on dropped: the table reads `-06:00:00` from
///   2025-11-02 to 2200;
/// * **foreign** — Europe/Berlin's table under Chicago's key;
/// * **another key** — Europe/Berlin's table under its own key (refused by the key before D104 too: the
///   control);
/// * **history** — the offset edit again, asked at 2026-11-10 09:00 CST, when the planned day, its
///   lookahead and its walls are in the next span and the edit falls only in the log's history: the
///   evening of 2026-09-06, which `tm review day --date 2026-09-06` reads;
/// * **lookahead** — the 2026-11-01 fall-back moved a week later, asked on Thursday 2026-10-29, when the
///   planned day and the log are before it and only the days ahead fall in the moved week;
/// * **unwritable** — the offset edit in a cache directory the binary cannot write: rebuilt in memory
///   and never served, the planted file left as it was (D93's path), against a cache-less tree whose
///   cache directory cannot be written either.
///
/// Before D104 every plant but the control moves an answer (W-46 track H's block in kernel/README.md,
/// each driven on the unswitched binary of `16aaafc`); since it, none does.
#[test]
fn every_planted_table_answers_as_a_cache_less_tree() {
    let world = evening();
    let truth_text = fs::read_to_string(zone_file(&world)).expect("tz.json");
    let truth = ZoneTable::from_wire(&tz_table::from_cache_text(&truth_text).expect("the digest matches")).expect("a table");
    assert_eq!(truth, tz_table::probe(chrono_tz::America::Chicago), "the world's table is the probe");
    let spring = 1_772_956_800; // 2026-03-08T08:00:00Z
    let fall = 1_793_516_400; // 2026-11-01T07:00:00Z
    assert!(truth.transitions.iter().any(|&(t, o)| t == spring && o == -5 * 3600), "the 2026 spring change");
    assert!(truth.transitions.iter().any(|&(t, o)| t == fall && o == -6 * 3600), "the 2026 fall-back");

    let mut offset = truth.clone();
    offset.transitions.iter_mut().filter(|(t, _)| *t == spring).for_each(|p| p.1 = -3 * 3600);
    let mut truncated = truth.clone();
    truncated.transitions.retain(|&(t, _)| t < spring);
    let berlin = tz_table::probe(chrono_tz::Europe::Berlin);
    let foreign = ZoneTable { key: truth.key.clone(), ..berlin.clone() };
    let mut lookahead = truth.clone();
    lookahead.transitions.iter_mut().filter(|(t, _)| *t == fall).for_each(|p| p.0 += 7 * 86_400);

    let sep7 = "2026-09-07T00:10:00-05:00";
    let plants = vec![
        Plant { name: "offset", zone: written(&offset), unwritable: false, steps: day_verbs(sep7) },
        Plant { name: "truncated", zone: written(&truncated), unwritable: false, steps: day_verbs(sep7) },
        Plant { name: "foreign", zone: written(&foreign), unwritable: false, steps: day_verbs(sep7) },
        Plant { name: "another key", zone: written(&berlin), unwritable: false, steps: day_verbs(sep7) },
        Plant {
            name: "history",
            zone: written(&offset),
            unwritable: false,
            steps: vec![
                ("2026-11-10T09:00:00-06:00", vec!["--json", "review", "day", "--date", "2026-09-06"]),
                ("2026-11-10T09:00:00-06:00", vec!["--json", "review", "week", "--date", "2026-09-06"]),
                ("2026-11-10T09:00:00-06:00", vec!["--json", "plan"]),
                ("2026-11-10T09:00:00-06:00", vec!["--json", "now"]),
                ("2026-11-10T09:00:00-06:00", vec!["check"]),
            ],
        },
        Plant { name: "lookahead", zone: written(&lookahead), unwritable: false, steps: day_verbs("2026-10-29T09:00:00-05:00") },
        Plant { name: "unwritable", zone: written(&offset), unwritable: true, steps: day_verbs(sep7) },
    ];

    let mut moved = Vec::new();
    for p in &plants {
        let planted = copy_with_cache(&world, Some(&p.zone));
        let bare = copy_with_cache(&world, None);
        let lock = |tm: &Tm| {
            let dir = tm.plan.join(".tm/cache/replay");
            fs::create_dir_all(&dir).expect("the cache directory");
            let mut perm = fs::metadata(&dir).expect("metadata").permissions();
            perm.set_readonly(true);
            fs::set_permissions(&dir, perm).expect("read-only");
        };
        if p.unwritable {
            lock(&planted);
            lock(&bare);
        }
        for (now, args) in &p.steps {
            // Each tree's own directory named alike, so a notice that names its path compares.
            let run = |tm: &Tm| {
                let o = tm.run_at(now, args);
                let here = tm.plan.to_string_lossy().into_owned();
                Out { code: o.code, stdout: o.stdout.replace(&here, "<plan>"), stderr: o.stderr.replace(&here, "<plan>") }
            };
            let (a, b) = (run(&planted), run(&bare));
            if (a.code, &a.stdout, &a.stderr) != (b.code, &b.stdout, &b.stderr) {
                moved.push(format!(
                    "{}: `tm {}` at {now}\n=== planted\n{}\n=== cache-less\n{}",
                    p.name,
                    args.join(" "),
                    said(&a),
                    said(&b)
                ));
            }
        }
        let cache = |tm: &Tm| tm.plan.join(".tm/cache/replay");
        if p.unwritable {
            assert_eq!(
                fs::read_to_string(cache(&planted).join("tz.json")).expect("the planted file"),
                p.zone,
                "unwritable: the planted file is left as it was"
            );
            for tm in [&planted, &bare] {
                let mut perm = fs::metadata(cache(tm)).expect("metadata").permissions();
                #[allow(clippy::permissions_set_readonly_false)]
                perm.set_readonly(false);
                fs::set_permissions(cache(tm), perm).expect("writable again");
            }
            fs::remove_file(cache(&planted).join("tz.json")).expect("the planted file");
        }
        let (fa, fb) = (files_normalized(&planted.plan), files_normalized(&bare.plan));
        if fa != fb {
            let differ: Vec<String> = fa
                .iter()
                .map(|(r, _)| r.clone())
                .chain(fb.iter().map(|(r, _)| r.clone()))
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .filter(|r| fa.iter().find(|x| &x.0 == r) != fb.iter().find(|x| &x.0 == r))
                .collect();
            moved.push(format!("{}: the files differ: {differ:?}", p.name));
        }
    }
    assert!(moved.is_empty(), "{} answer(s) moved by a planted table (D104):\n\n{}", moved.len(), moved.join("\n\n"));
}

/// **The check refuses every edit of a table and accepts its probe** (D104; AGENTS §5.8, both
/// directions of a check): Chicago's probe is accepted; every one of these is refused — another
/// tzdb's key, another zone's key, the base a second off, each transition deleted, the table cut after
/// each transition, each transition moved a second or an hour either way, each transition's offset a
/// second off, a transition that changes nothing inserted, and another zone's table under this key.
/// Cut, deleted and moved by an hour are the edits a check of the transitions alone would accept:
/// the one-day grid refuses them.
#[test]
fn the_check_refuses_every_edit_of_a_table_and_accepts_its_probe() {
    let tz = chrono_tz::America::Chicago;
    let truth = tz_table::probe(tz);
    assert!(tz_table::agrees(tz, &truth), "the probe is refused");
    let n = truth.transitions.len();
    assert!(n > 300, "Chicago's table has {n} transitions");
    let mut refused = 0usize;
    let mut refuse = |t: ZoneTable, what: String| {
        assert!(!tz_table::agrees(tz, &t), "{what} was accepted");
        refused += 1;
    };
    refuse(ZoneTable { key: format!("America/Chicago|2025a|{}", tz_table::SPAN), ..truth.clone() }, "another tzdb's key".into());
    refuse(ZoneTable { key: tz_table::key_of(chrono_tz::America::Denver), ..truth.clone() }, "another zone's key".into());
    refuse(ZoneTable { base: truth.base + 1, ..truth.clone() }, "the base a second off".into());
    for i in 0..n {
        let mut t = truth.clone();
        t.transitions.remove(i);
        refuse(t, format!("transition {i} deleted"));
        let mut t = truth.clone();
        t.transitions.truncate(i);
        refuse(t, format!("the table cut before transition {i}"));
        for d in [-3600, -1, 1, 3600] {
            let mut t = truth.clone();
            t.transitions[i].0 += d;
            refuse(t, format!("transition {i} moved {d:+} s"));
        }
        let mut t = truth.clone();
        t.transitions[i].1 += 1;
        refuse(t, format!("transition {i}'s offset a second off"));
    }
    let mut t = truth.clone();
    t.transitions.insert(1, (truth.transitions[0].0 + 86_400, truth.transitions[0].1));
    refuse(t, "a transition that changes nothing".into());
    refuse(ZoneTable { key: truth.key.clone(), ..tz_table::probe(chrono_tz::Europe::Berlin) }, "Berlin's table under Chicago's key".into());
    assert_eq!(refused, 5 + 7 * n, "every edit was asked");

    // And the wire: a value the one encoder would not write is no table (`ZoneTable::from_wire`).
    let wire = truth.to_wire();
    assert_eq!(ZoneTable::from_wire(&wire), Some(truth.clone()));
    let mut extra = wire.clone();
    extra["note"] = Value::String("x".into());
    assert_eq!(ZoneTable::from_wire(&extra), None, "a key the encoder does not write");
    let respelled = serde_json::from_str::<Value>(&wire.to_string().replacen("\"-06:00:00\"", "\"-6:00:00\"", 1)).expect("json");
    assert_eq!(ZoneTable::from_wire(&respelled), None, "an offset the encoder does not spell so");
    let zulu = serde_json::from_str::<Value>(&wire.to_string().replacen("Z\"", "+00:00\"", 1)).expect("json");
    assert_eq!(ZoneTable::from_wire(&zulu), None, "an instant the encoder does not spell so");
}

/// **The fact D104's grid stands on, measured and held** (`tz_table::CHECK_STEP`): over every zone of
/// the binary's chrono-tz, every span — between two changes, or between a change and an end of the
/// span — is longer than the check's step, so a table that agrees at its own transitions and on the
/// grid agrees everywhere; and every zone's probe passes the check (a check a legitimate table fails is
/// a trapdoor, AGENTS §5.8).  Measured at W-46 (chrono-tz 0.10.4, tzdb 2025b): 597 zones, the shortest
/// span 601,200 s.  A chrono-tz upgrade that brings a span the step does not outlast fails here, by
/// zone, before the check can accept a table with a change missing.
#[test]
fn every_span_of_every_zone_outlasts_the_checks_step_and_every_probe_agrees() {
    let zones: Vec<chrono_tz::Tz> = chrono_tz::TZ_VARIANTS.to_vec();
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    let chunks: Vec<Vec<chrono_tz::Tz>> = zones.chunks(zones.len().div_ceil(workers)).map(<[chrono_tz::Tz]>::to_vec).collect();
    let results: Vec<(i64, String, Vec<String>)> = std::thread::scope(|s| {
        let handles: Vec<_> = chunks
            .into_iter()
            .map(|chunk| {
                s.spawn(move || {
                    let (mut shortest, mut at, mut refused) = (i64::MAX, String::new(), Vec::new());
                    for tz in chunk {
                        let t = tz_table::probe(tz);
                        if !tz_table::agrees(tz, &t) {
                            refused.push(tz.name().to_string());
                        }
                        let mut points = vec![tz_table::SPAN_FROM];
                        points.extend(t.transitions.iter().map(|&(s, _)| s));
                        points.push(tz_table::SPAN_TO);
                        for w in points.windows(2) {
                            if w[1] - w[0] < shortest {
                                shortest = w[1] - w[0];
                                at = format!("{} from {}", tz.name(), tz_table::fmt_instant(w[0]));
                            }
                        }
                    }
                    (shortest, at, refused)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("a sweep")).collect()
    });
    let refused: Vec<&String> = results.iter().flat_map(|r| &r.2).collect();
    assert!(refused.is_empty(), "the check refuses the probe of {refused:?}");
    let (shortest, at) = results.iter().map(|r| (r.0, r.1.clone())).min().expect("zones");
    eprintln!("D104's sweep: {} zones (tzdb {}), the shortest span {shortest} s ({at})", zones.len(), chrono_tz::IANA_TZDB_VERSION);
    assert!(
        shortest > tz_table::CHECK_STEP,
        "a span of {shortest} s ({at}) does not outlast the check's step of {} s: the grid could miss a change",
        tz_table::CHECK_STEP
    );
}

/// `text` with its comments cut away and its string literals kept: a `//` or `/*` inside a string is
/// the string's, and a raw string runs to its closing `"` and hashes.
fn code_of(text: &str) -> String {
    let b = text.as_bytes();
    let (mut out, mut i) = (String::new(), 0usize);
    while i < b.len() {
        match b[i] {
            b'/' if b.get(i + 1) == Some(&b'/') => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i += 2;
            }
            b'r' if matches!(b.get(i + 1), Some(b'#') | Some(b'"')) && (i == 0 || !b[i - 1].is_ascii_alphanumeric()) => {
                let hashes = b[i + 1..].iter().take_while(|&&c| c == b'#').count();
                if b.get(i + 1 + hashes) != Some(&b'"') {
                    out.push('r');
                    i += 1;
                    continue;
                }
                let close: String = std::iter::once('"').chain(std::iter::repeat_n('#', hashes)).collect();
                let start = i;
                let body = i + 2 + hashes;
                let end = text[body..].find(&close).map_or(b.len(), |k| body + k + close.len());
                out.push_str(&text[start..end]);
                i = end;
            }
            b'"' => {
                let start = i;
                i += 1;
                while i < b.len() && b[i] != b'"' {
                    i += if b[i] == b'\\' { 2 } else { 1 };
                }
                i = (i + 1).min(b.len());
                out.push_str(&text[start..i]);
            }
            _ => {
                let c = text[i..].chars().next().expect("a char");
                out.push(c);
                i += c.len_utf8();
            }
        }
    }
    out
}

/// **`tz_table::wire_for` is the one door to `tz.json`** (the owner's D104 as a class, from the source
/// side): the check is in `wire_for`, so it covers every request that carries a zone table only if no
/// other code reads the file. Measured at W-46 by body shape: every request section that carries a
/// `tz` — the capacity and planner request (`kernel_capacity::reads`), the walls request
/// (`day::call_the_walls`), and every `log` request (`kernel_log::wrap_log`, whose table is
/// `Ctx::tz_wire`'s or `lifecycle::line_warnings`') — takes its table from a `wire_for` call. This holds
/// the other half as a property of the source: no Rust file of `tm/src` or `tm-core/src` but
/// `tm/src/cli/tz_table.rs` names the file, by its name or by `CACHE_FILE`, in code.
#[test]
fn no_file_but_the_zone_table_names_its_cache_in_code() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    fn rust_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        for e in fs::read_dir(dir).expect("read dir") {
            let p = e.expect("entry").path();
            if p.is_dir() {
                rust_files(&p, out);
            } else if p.extension().is_some_and(|x| x == "rs") {
                out.push(p);
            }
        }
    }
    let mut files = Vec::new();
    for dir in ["tm/src", "tm-core/src"] {
        rust_files(&root.join(dir), &mut files);
    }
    assert!(files.len() > 40, "the walk reached {} files", files.len());
    let mut readers = Vec::new();
    for f in &files {
        let rel = f.strip_prefix(&root).expect("under the root").to_string_lossy().into_owned();
        let code = code_of(&fs::read_to_string(f).expect("a source file"));
        if (code.contains("tz.json") || code.contains("CACHE_FILE")) && rel != "tm/src/cli/tz_table.rs" {
            readers.push(rel);
        }
    }
    assert!(readers.is_empty(), "code outside tz_table.rs names the zone cache: {readers:?}");
    let own = code_of(&fs::read_to_string(root.join("tm/src/cli/tz_table.rs")).expect("tz_table.rs"));
    assert!(own.contains("\"tz.json\"") && own.contains("CACHE_FILE"), "the scan reads code: tz_table.rs names its own file");
    assert!(!code_of("// tz.json\nlet x = 1; /* CACHE_FILE */").contains("tz.json"), "comments are cut");
    assert!(code_of("let s = \"// tz.json\";").contains("tz.json"), "a string keeps its `//`");
}

/// **The process remembers the one text it found to be its own table, by zone and whole text** (D104's
/// `tz_table::served`): a text the check accepted is served again unchecked, so the memory must never
/// serve a text it was not shown, nor a table for another zone. In one process: Chicago's table read and
/// remembered; the same file asked for Kolkata is Kolkata's probe and is rewritten; Chicago's table again,
/// re-digested with one offset changed — a text the process has not seen — is refused and rebuilt.
#[test]
fn the_process_remembers_a_checked_table_by_zone_and_whole_text() {
    let (chicago, kolkata) = (chrono_tz::America::Chicago, chrono_tz::Asia::Kolkata);
    let dir = TempDir::new().expect("temp dir");
    let cache = dir.path().join("replay");
    let file = cache.join(tz_table::CACHE_FILE);
    let truth = tz_table::probe(chicago).to_wire();
    assert_eq!(tz_table::wire_for(Some(&cache), chicago), truth, "probed and written");
    assert_eq!(tz_table::wire_for(Some(&cache), chicago), truth, "read, checked and remembered");
    assert_eq!(tz_table::wire_for(Some(&cache), kolkata), tz_table::probe(kolkata).to_wire(), "another zone is never served Chicago's");
    assert_eq!(fs::read_to_string(&file).expect("rewritten"), tz_table::cache_text(&tz_table::probe(kolkata).to_wire()));
    fs::write(&file, tz_table::cache_text(&truth)).expect("Chicago's again");
    assert_eq!(tz_table::wire_for(Some(&cache), chicago), truth, "remembered again");
    let mut edited = ZoneTable::from_wire(&truth).expect("a table");
    edited.transitions[200].1 += 60;
    fs::write(&file, tz_table::cache_text(&edited.to_wire())).expect("an edit, its digest recomputed");
    assert_eq!(tz_table::wire_for(Some(&cache), chicago), truth, "a text the process had not checked was served");
    assert_eq!(fs::read_to_string(&file).expect("rewritten"), tz_table::cache_text(&truth), "and it is rebuilt");
}

/// **A day before a zone's first change is planned in the offset the host decodes it in** (the
/// W-46 audit, README gap 4902). The table began in 1900 and read every earlier second at its
/// 1900 offset, while chrono-tz reads local mean time before a zone's first change — America/Chicago
/// is −05:50:36 before 12:09:24 local on 1883-11-18 — so after R3 `tm plan`, `tm now`, `tm check` and
/// `tm review day` at such an instant faulted on the day's hash (the kernel planned in −06:00, the
/// host decoded in −05:50:36), where fork 4748911's planner, which never read the table, planned
/// it. The span begins in 1800, before tzdb's earliest change (Asia/Manila's, 1844), so each verb
/// answers at an instant either side of Chicago's change, on a tree with no cache and on one whose
/// cache the first verb wrote.
#[test]
fn a_day_before_the_zones_first_change_is_planned_in_the_hosts_offset() {
    let tm = cli_common::Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    for now in ["1850-07-01T12:00:00-06:00", "1883-11-17T12:00:00-06:00", "1883-11-18T13:00:00-06:00"] {
        for verb in [&["plan"][..], &["now"][..], &["check"][..], &["review", "day"][..]] {
            let out = tm.run_at(now, verb);
            assert!(
                !out.stderr.contains("kernel fault") && !out.stdout.contains("kernel fault"),
                "`tm {}` at {now}: {}{}",
                verb.join(" "),
                out.stdout,
                out.stderr
            );
            assert!(out.code == 0 || verb == ["check"], "`tm {}` at {now} exits {}: {}", verb.join(" "), out.code, out.stderr);
        }
    }
    let table = tz_table::from_cache_text(
        &fs::read_to_string(tm.plan.join(".tm/cache/replay").join(tz_table::CACHE_FILE)).expect("the cache the verbs wrote"),
    )
    .expect("the cache's digest matches its table");
    assert_eq!(table["base"], "-05:50:36", "the base is Chicago's local mean time: {table}");
}
