//! The `--json` matrix (AGENTS.md §8.1 scope item 7; the fourth row of
//! PLAN-lean-kernel.md §4's integration-bug table — G3, "`--json` never
//! reached the error path").
//!
//! Every §13 verb × {success, error} × {plain, `--json`}, table-driven,
//! against the built binary on a fresh `plan-basic` copy per leg. Asserted:
//!
//! * **success/plain** — exit 0;
//! * **success/json** — exit 0 and stdout is one JSON document;
//! * **error/plain** — the expected exit code, nothing on stdout, and the
//!   human line `tm: …` on stderr;
//! * **error/json** — the same exit code and stderr is one JSON document
//!   carrying the documented error keys (`ok:false`, `kind`, `message`,
//!   `exit_code`) — `out::ErrorDoc`'s shape, the one `cli_errors.rs` pins
//!   field-by-field for a sample; this matrix pins that *every verb's*
//!   failure reaches it.
//!
//! Verbs whose legs need state carry setup commands (a `done` needs a
//! running block) or run against an empty directory (`plan` cannot fail on
//! the healthy fixture, so its error leg is "not a plan directory").
//!
//! Named exceptions, not silently skipped:
//! * `tm tui` has **no headless success leg** — it needs a tty, and that
//!   refusal *is* its error leg here (both renderings of it).
//! * `tm init` and `tm check` sit outside the table: `init` runs without a
//!   plan directory, and a failed `check` reports its problem document on
//!   **stdout** with exit 2 (§13 reserves 2 for validation problems; the
//!   stderr error doc is for the verb itself failing). Each has its own
//!   test below, all four legs.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// Where a row's error leg runs.
#[derive(Clone, Copy)]
enum ErrWhere {
    /// On the fixture (after `setup_err`, if any).
    Fixture,
    /// Against an empty directory: "not a plan directory".
    EmptyDir,
}

struct Case {
    /// The §13 verb, for messages.
    verb: &'static str,
    /// Commands run (and asserted ok) before the success leg.
    setup_ok: &'static [&'static [&'static str]],
    /// The success invocation.
    ok: &'static [&'static str],
    /// Commands run before the error leg.
    setup_err: &'static [&'static [&'static str]],
    /// The failing invocation.
    err: &'static [&'static str],
    err_where: ErrWhere,
    /// Its exit code (§13: 1 error, 3 conflict).
    err_code: i32,
}

const C: Case = Case {
    verb: "",
    setup_ok: &[],
    ok: &[],
    setup_err: &[],
    err: &[],
    err_where: ErrWhere::Fixture,
    err_code: 1,
};

/// A running block for the clock verbs' success legs.
const RUNNING: &[&[&str]] = &[&["start", "^t3", "--energy", "4"]];

/// The table. Success and error arguments were each probed by hand against
/// the built binary before being pinned here; the *shape* assertions are the
/// test, the arguments are just the cheapest way to reach each leg.
const CASES: &[Case] = &[
    Case { verb: "wake", ok: &["wake", "06:05", "--slept", "8h10m"], err: &["wake", "99:99"], ..C },
    Case { verb: "arrive", ok: &["arrive", "lounge"], err: &["arrive", "--at", "99:99"], ..C },
    Case { verb: "plan", ok: &["plan"], err: &["plan"], err_where: ErrWhere::EmptyDir, ..C },
    Case { verb: "now", ok: &["now"], err: &["now"], err_where: ErrWhere::EmptyDir, ..C },
    Case { verb: "start", ok: &["start", "^t3", "--energy", "4"], err: &["start", "^nope"], ..C },
    Case { verb: "done", setup_ok: RUNNING, ok: &["done"], err: &["done"], ..C },
    Case { verb: "extend", setup_ok: RUNNING, ok: &["extend", "1b"], err: &["extend"], ..C },
    Case { verb: "stop", setup_ok: RUNNING, ok: &["stop"], err: &["stop"], ..C },
    Case { verb: "break", ok: &["break", "20m"], err: &["break"], err_where: ErrWhere::EmptyDir, ..C },
    Case { verb: "interrupt", setup_ok: RUNNING, ok: &["interrupt"], err: &["interrupt"], err_where: ErrWhere::EmptyDir, ..C },
    Case {
        verb: "resume",
        setup_ok: &[&["start", "^t3", "--energy", "4"], &["interrupt"]],
        ok: &["resume"],
        err: &["resume"],
        ..C
    },
    Case { verb: "pause", setup_ok: RUNNING, ok: &["pause"], err: &["pause"], ..C },
    Case { verb: "energy", ok: &["energy", "4"], err: &["energy", "9"], ..C },
    Case { verb: "idle", ok: &["idle", "w"], err: &["idle", "zz"], ..C },
    Case { verb: "add", ok: &["add", "Buy stamps", "--to", "week"], err: &["add", "x", "--to", "nowhere"], ..C },
    Case { verb: "edit", ok: &["edit", "^t3", "est=2b"], err: &["edit", "^nope", "est=2b"], ..C },
    Case { verb: "move", ok: &["move", "^t1", "week"], err: &["move", "^nope", "week"], ..C },
    Case { verb: "rank", ok: &["rank", "^t3", "1"], err: &["rank", "^nope", "1"], ..C },
    Case { verb: "demote", ok: &["demote", "^t4"], err: &["demote", "^nope"], ..C },
    Case {
        verb: "readopt",
        setup_ok: &[&["demote", "^t4"]],
        ok: &["readopt", "^t4"],
        err: &["readopt", "^nope"],
        ..C
    },
    Case { verb: "drop", ok: &["drop", "^t1"], err: &["drop", "^nope"], ..C },
    Case { verb: "event", ok: &["event", "delivered"], err: &["event", "delivered", "^nope"], ..C },
    Case { verb: "skip", ok: &["skip", "laundry"], err: &["skip", "nope"], ..C },
    Case { verb: "routine", ok: &["routine", "done", "breakfast", "--min", "20"], err: &["routine", "done", "nope"], ..C },
    // G4's own verb: the month-only flag on a day close is §6.3's sentence,
    // and it has to be a JSON document too.
    Case { verb: "close", ok: &["close", "day"], err: &["close", "day", "--drop", "^x"], ..C },
    Case { verb: "sync-cal", ok: &["sync-cal"], err: &["sync-cal"], err_where: ErrWhere::EmptyDir, ..C },
    Case { verb: "review", ok: &["review", "day"], err: &["review", "day", "--date", "garbage"], ..C },
    Case { verb: "model", ok: &["model", "--show"], err: &["model", "--show"], err_where: ErrWhere::EmptyDir, ..C },
    Case { verb: "log", ok: &["log", "--tail", "2"], err: &["log", "--since", "garbage"], ..C },
    Case {
        verb: "undo",
        setup_ok: &[&["wake", "06:05"]],
        ok: &["undo"],
        err: &["undo"],
        err_where: ErrWhere::EmptyDir,
        ..C
    },
    Case { verb: "triage", ok: &["triage"], err: &["triage"], err_where: ErrWhere::EmptyDir, ..C },
    // `tm tui` headless: the tty refusal is the error leg; the success leg
    // needs a terminal and is deliberately absent (named in the module doc).
    Case { verb: "tui", ok: &[], err: &["tui"], ..C },
];

/// stderr parsed as the one JSON error document `out::ErrorDoc` emits.
fn err_doc(verb: &str, stderr: &str) -> Value {
    serde_json::from_str(stderr).unwrap_or_else(|e| {
        panic!("[{verb}] --json error is not one JSON document ({e}): {stderr:?}")
    })
}

fn run_setup(tm: &Tm, setup: &[&[&str]]) {
    for cmd in setup {
        tm.ok(cmd);
    }
}

#[test]
fn every_verb_succeeds_plain_and_as_json() {
    for case in CASES {
        if case.ok.is_empty() {
            continue; // tui: named above
        }
        // Plain.
        let tm = Tm::new();
        run_setup(&tm, case.setup_ok);
        let out = tm.run(case.ok);
        assert_eq!(
            out.code, 0,
            "[{}] success/plain: {}{}",
            case.verb, out.stdout, out.stderr
        );

        // --json: same leg on a fresh tree, stdout is one document.
        let tm = Tm::new();
        run_setup(&tm, case.setup_ok);
        let mut args = vec!["--json"];
        args.extend_from_slice(case.ok);
        let out = tm.run(&args);
        assert_eq!(
            out.code, 0,
            "[{}] success/json: {}{}",
            case.verb, out.stdout, out.stderr
        );
        assert!(
            !out.stdout.trim().is_empty(),
            "[{}] success/json printed nothing",
            case.verb
        );
        let doc: Value = serde_json::from_str(&out.stdout).unwrap_or_else(|e| {
            panic!(
                "[{}] success/json stdout is not JSON ({e}): {:?}",
                case.verb, out.stdout
            )
        });
        assert!(doc.is_object(), "[{}] success doc: {doc}", case.verb);
    }
}

#[test]
fn every_verb_fails_plain_and_as_json() {
    for case in CASES {
        let fixture = |setup: &[&[&str]]| {
            let tm = match case.err_where {
                ErrWhere::Fixture => Tm::new(),
                ErrWhere::EmptyDir => Tm::empty(),
            };
            run_setup(&tm, setup);
            tm
        };

        // Plain: the human line, on stderr, nothing on stdout.
        let tm = fixture(case.setup_err);
        let out = tm.run(case.err);
        assert_eq!(
            out.code, case.err_code,
            "[{}] error/plain: {}{}",
            case.verb, out.stdout, out.stderr
        );
        assert_eq!(out.stdout, "", "[{}] error/plain wrote stdout", case.verb);
        assert!(
            out.stderr.starts_with("tm: "),
            "[{}] error/plain is not the `tm: …` line: {:?}",
            case.verb, out.stderr
        );

        // --json: the same failure is a document on stderr (G3's assertion).
        let tm = fixture(case.setup_err);
        let mut args = vec!["--json"];
        args.extend_from_slice(case.err);
        let out = tm.run(&args);
        assert_eq!(
            out.code, case.err_code,
            "[{}] error/json: {}{}",
            case.verb, out.stdout, out.stderr
        );
        assert_eq!(out.stdout, "", "[{}] error/json wrote stdout", case.verb);
        let doc = err_doc(case.verb, &out.stderr);
        assert_eq!(doc["ok"], Value::Bool(false), "[{}] {doc}", case.verb);
        assert!(
            doc["kind"].is_string(),
            "[{}] error doc has no `kind`: {doc}",
            case.verb
        );
        assert!(
            doc["message"].is_string(),
            "[{}] error doc has no `message`: {doc}",
            case.verb
        );
        assert_eq!(
            doc["exit_code"],
            Value::from(case.err_code),
            "[{}] {doc}",
            case.verb
        );
    }
}

/// `tm init`, all four legs — outside the table because it runs *without*
/// a plan directory, and its error is "directory not empty".
#[test]
fn init_all_four_legs() {
    // success/plain
    let tm = Tm::empty();
    let dir = tm.plan.to_str().expect("utf-8 path");
    let out = tm.run(&["init", dir]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);

    // error/plain: the same directory again, no --force.
    let out = tm.run(&["init", dir]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.starts_with("tm: "), "{:?}", out.stderr);

    // success/json, on a fresh directory.
    let tm = Tm::empty();
    let dir = tm.plan.to_str().expect("utf-8 path");
    let out = tm.run(&["--json", "init", dir]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let doc: Value = serde_json::from_str(&out.stdout).expect("init --json is a document");
    assert!(doc.is_object(), "{doc}");

    // error/json.
    let out = tm.run(&["--json", "init", dir]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc = err_doc("init", &out.stderr);
    assert_eq!(doc["ok"], Value::Bool(false), "{doc}");
    assert!(doc["kind"].is_string(), "{doc}");
    assert_eq!(doc["exit_code"], Value::from(1), "{doc}");
}

/// `tm check`, all four legs — outside the table because §13 gives a failed
/// check exit **2** and its problem document lands on **stdout**: the check
/// *ran*; what failed is the tree.
#[test]
fn check_all_four_legs() {
    let poison = |tm: &Tm| {
        // A dependency cycle is an error-severity problem (a duplicate id is
        // only a warning): `error[dep-cycle]`, exit 2 — probed, then pinned.
        let path = tm.plan.join("week/2026-W37.md");
        let mut text = std::fs::read_to_string(&path).expect("read week");
        text.push_str("- [ ] 2 1b Self loop after:^qq1 ^qq1\n");
        std::fs::write(&path, text).expect("write week");
    };

    // success/plain and success/json on the healthy fixture.
    let tm = Tm::new();
    let out = tm.run(&["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let out = tm.run(&["--json", "check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let doc: Value = serde_json::from_str(&out.stdout).expect("check --json is a document");
    assert_eq!(doc["exit_code"], Value::from(0), "{doc}");

    // error/plain: exit 2, the problem named on stdout.
    let tm = Tm::new();
    poison(&tm);
    let out = tm.run(&["check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("dep-cycle"), "{:?}", out.stdout);

    // error/json: exit 2 and the problems array in the stdout document.
    let out = tm.run(&["--json", "check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let doc: Value = serde_json::from_str(&out.stdout).expect("check --json is a document");
    assert_eq!(doc["exit_code"], Value::from(2), "{doc}");
    assert!(
        doc["problems"].as_array().is_some_and(|p| !p.is_empty()),
        "{doc}"
    );
}

/// The matrix's size, re-measured, so a silently shrinking table is loud:
/// §13 has 34 top-level verbs; `init` and `check` have their own
/// four-legged tests above, so the table carries the other 32 — and `tui`
/// is the one row without a headless success leg.
#[test]
fn the_table_covers_every_section_13_verb() {
    assert_eq!(CASES.len(), 32, "the table lost a verb");
    let with_success = CASES.iter().filter(|c| !c.ok.is_empty()).count();
    assert_eq!(with_success, 31, "only tui may lack a success leg");
    let named: Vec<&str> = CASES.iter().map(|c| c.verb).collect();
    for verb in ["init", "check"] {
        assert!(!named.contains(&verb), "{verb} belongs to its own test");
    }
}

/// An exact `{num, den}` pair (the owner's D15): digit strings (D17).
fn exact_pair(v: &Value) -> (u128, u128) {
    let part = |k: &str| v[k].as_str().and_then(|s| s.parse::<u128>().ok()).unwrap_or_else(|| panic!("{k} in {v}"));
    (part("num"), part("den").max(1))
}

/// **Every integer of capacity on `--json` is the floor of the exact value
/// beside it** (the owner's D15; stage 5 D10 L8). `tm plan --json`'s
/// priorities carry `avail_min`, `allocation_min` and `shortfall_min` with
/// `…_exact` pairs; each integer is the floor of its own pair, so for a HOT
/// answer `need_min − allocation_min` may exceed `shortfall_min` by one (the
/// design's Q4 names the pair `avail − allocation`; documented on `Prio`),
/// while the exact values agree: the exact shortfall is exactly `need −
/// allocation`. `tm plan --week --json` is pinned in `cli_plan.rs`.
#[test]
fn capacity_integers_are_floors_beside_their_exact_values() {
    let tm = Tm::new();
    run_setup(&tm, &[&["arrive", "lounge"]]);
    let out = tm.run(&["--json", "plan"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let json = out.json();
    let prios = json["priorities"].as_array().expect("priorities");
    assert!(!prios.is_empty());
    let mut passed = 0;
    for p in prios {
        let mut ex = Vec::new();
        for key in ["avail_min", "allocation_min", "shortfall_min"] {
            let (n, d) = exact_pair(&p[format!("{key}_exact")]);
            assert_eq!(p[key].as_u64(), Some((n / d) as u64), "{key} in {p}");
            ex.push((n, d));
        }
        let [(ln, ld), (sn, sd)] = [ex[1], ex[2]];
        if sn > 0 {
            let need = u128::from(p["need_min"].as_u64().expect("need"));
            assert_eq!(sn * ld, need * sd * ld - ln * sd, "the exact shortfall is need − allocation: {p}");
            let gap = need - ln / ld - sn / sd;
            assert!(gap <= 1, "the floors differ by at most one: {p}");
        }
        passed += usize::from(p["until"].is_string());
    }
    assert!(passed > 0, "no candidate went through a pass: {json}");
}
