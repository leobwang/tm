//! **`tm stop` and `tm done --partial` on a line that carries a tab END THE
//! BLOCK and say the estimate was not written; `tm extend` keeps refusing** —
//! the campaign's D66 call on README gap 3047 (stage 6 W-37 track T).
//!
//! D62 routes the three estimate writers through the kernel's `est` op, and
//! every edit op refuses a line carrying a tab (`tabbedLine`, gap 32). Until
//! W-37 that refusal failed `tm stop` whole: nothing written and the block
//! still RUNNING — a stop that could not stop. The estimate is the secondary
//! write; the stop is the verb.

mod cli_common;

use cli_common::Tm;

const WEEK: &str = "week/2026-W37.md";

/// `plan-basic` with a tab inside `^t4`'s title, `^t4` started at 09:00.
fn tabbed_and_running() -> Tm {
    let tm = Tm::new();
    let path = tm.plan.join(WEEK);
    let text = std::fs::read_to_string(&path).expect("week file");
    let tabbed = text.replacen("Claude Code drafts tests", "Claude\tCode drafts tests", 1);
    assert_ne!(tabbed, text, "the fixture holds ^t4's title");
    std::fs::write(&path, tabbed).expect("write");
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

/// `^t4`'s line as it stands.
fn t4(tm: &Tm) -> String {
    tm.read(WEEK).lines().find(|l| l.ends_with("^t4")).expect("^t4's line").to_string()
}

#[test]
fn tm_stop_on_a_tabbed_line_ends_the_block_and_says_the_estimate_was_not_written() {
    let tm = tabbed_and_running();
    let before = t4(&tm);
    let out = tm.run_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert_eq!(out.code, 0, "the stop stops: {}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("^t4's estimate was not written"), "it says so: {:?}", out.stderr);
    let after = t4(&tm);
    assert!(after.starts_with("- [ ] 3 1b Claude\tCode"), "the box moved, the estimate stood: {after:?} (was {before:?})");
    assert!(!after.contains("est:"), "no estimate was written: {after:?}");
    assert_eq!(tm.last_ev("stop")["id"], "t4", "the stop is logged");
    let now = tm.json_at("2026-09-07T09:21:00-05:00", &["now"]);
    assert!(now["active"].is_null(), "nothing is running: {now}");
}

#[test]
fn tm_done_partial_on_a_tabbed_line_ends_the_block_and_says_so_in_json() {
    let tm = tabbed_and_running();
    let out = tm.json_at("2026-09-07T09:25:00-05:00", &["done", "--partial"]);
    assert_eq!(out["partial"], true, "{out}");
    assert!(
        out["estimate_not_written"].as_str().is_some_and(|w| w.contains("carries a tab")),
        "the reason is carried: {out}"
    );
    let after = t4(&tm);
    assert!(after.starts_with("- [ ] 3 1b Claude\tCode"), "{after:?}");
    let now = tm.json_at("2026-09-07T09:26:00-05:00", &["now"]);
    assert!(now["active"].is_null(), "nothing is running: {now}");
}

#[test]
fn tm_extend_on_a_tabbed_line_keeps_refusing_and_writes_nothing() {
    let tm = tabbed_and_running();
    let before = tm.read(WEEK);
    let log_before = tm.log().len();
    let out = tm.run_at("2026-09-07T09:10:00-05:00", &["extend", "1b"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(format!("{}{}", out.stdout, out.stderr).contains("tabbedLine"), "{}", out.stderr);
    assert_eq!(tm.read(WEEK), before, "nothing written");
    assert_eq!(tm.log().len(), log_before, "nothing logged");
}

#[test]
fn a_stop_on_a_plain_line_says_nothing_new() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let out = tm.json_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert!(out.get("estimate_not_written").is_none(), "{out}");
    assert!(t4(&tm).contains(" 40m "), "the estimate was written as D62 writes it: {}", t4(&tm));
}
