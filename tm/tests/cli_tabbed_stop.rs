//! **`tm stop`, `tm done --partial` and `tm extend` on a line that carries a tab write the
//! estimate as on any other line** — the owner's D83 (stage 6 W-42 track G, README gap 32
//! closed), restating what the campaign's D66 call on README gap 3047 (W-37 track T) held here.
//!
//! D62 routes the three estimate writers through the kernel's `est` op.  Until W-42 every edit op
//! refused a line carrying a tab by name, because a tab was a word character to the kernel and a
//! separator to the host, so an edit could land on a token the host never read; D66 then made
//! `tm stop` and `tm done --partial` END THE BLOCK anyway and say the estimate was not written,
//! and kept `tm extend` refusing.  D83 made a tab the kernel's separator, the refusal's reason went
//! with it, and the refusal is lifted: on a tabbed line the three verbs do what they do on any line
//! — the leading estimate, the slot, rewritten in place with the value as the verb spells it
//! (P54) — and the tab between the title words is kept.  The D66 sentence ("the estimate was not
//! written") can no longer be printed; `tm/src/cli/day.rs`' branch that prints it is dead, owed
//! to the step that holds that file (README gap 4165).

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
fn tm_stop_on_a_tabbed_line_writes_the_estimate_as_on_any_line() {
    let tm = tabbed_and_running();
    let out = tm.run_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert_eq!(out.code, 0, "the stop stops: {}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout.trim(), "stopped ^t4 after 20m · 40m left", "{}", out.stderr);
    assert!(!out.stderr.contains("was not written"), "D66's sentence is gone: {:?}", out.stderr);
    assert_eq!(t4(&tm), "- [ ] 3 40m Claude\tCode drafts tests     @m2 ^t4", "the slot rewritten, the tab kept");
    assert_eq!(tm.last_ev("stop")["id"], "t4", "the stop is logged");
    let now = tm.json_at("2026-09-07T09:21:00-05:00", &["now"]);
    assert!(now["active"].is_null(), "nothing is running: {now}");
}

#[test]
fn tm_done_partial_on_a_tabbed_line_writes_the_estimate_and_says_nothing_new() {
    let tm = tabbed_and_running();
    let out = tm.json_at("2026-09-07T09:25:00-05:00", &["done", "--partial"]);
    assert_eq!((&out["partial"], &out["remaining_min"]), (&serde_json::json!(true), &serde_json::json!(35)), "{out}");
    assert!(out.get("estimate_not_written").is_none(), "D66's field is gone: {out}");
    assert_eq!(out["title"], "Claude\tCode drafts tests", "the host's title, the tab kept: {out}");
    assert_eq!(t4(&tm), "- [ ] 3 35m Claude\tCode drafts tests     @m2 ^t4", "the slot rewritten");
    let now = tm.json_at("2026-09-07T09:26:00-05:00", &["now"]);
    assert!(now["active"].is_null(), "nothing is running: {now}");
}

#[test]
fn tm_extend_on_a_tabbed_line_extends_it() {
    let tm = tabbed_and_running();
    let out = tm.run_at("2026-09-07T09:10:00-05:00", &["extend", "1b"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout.trim(), "+60m on ^t4 · now 120m", "{}", out.stderr);
    assert_eq!(t4(&tm), "- [>] 3 2b Claude\tCode drafts tests     @m2 ^t4", "the slot as the verb spells it");
    assert_eq!(tm.last_ev("extend")["by_min"], 60, "the extension is logged");
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
