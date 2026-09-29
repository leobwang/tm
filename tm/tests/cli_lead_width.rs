//! **One grammar for the leading-estimate slot** (stage 6 W-37 track T, README
//! gap 3140, parity P57).
//!
//! The kernel reads the slot by SHAPE (`Field.estSlot`: `Nb|Nm|Nh|NhMm` over
//! `Nat` numerals); the host added a magnitude (`u32` minutes at a one-minute
//! block). So `- [ ] 2 9999999999999m Insurance claim for the bike ^a1` was an
//! ESTIMATE to the kernel and a TITLE WORD to the host: `tm check` said nothing,
//! `tm start` printed the word in the title, and the first `tm extend` had the
//! kernel rewrite the word as the slot — the title lost it. The host now reads
//! the slot by the kernel's shape (`tm_core::grammar::is_est_slot`), and a value
//! it cannot hold is a `bad-value` error, the way a keyed token's is.
//!
//! The comparison is DIFFERENTIAL: the host's reading is `tm_core`'s parser and
//! `tm`'s title; the kernel's is what its `est` op rewrites (the kernel writes
//! the slot in place when it reads the word as the slot, and appends an `est:`
//! token beside the title when it does not).

mod cli_common;

use cli_common::Tm;
use tm_core::grammar::{ItemLine, TokenKind};

const BOUND: &str = "4294967295m";
const PAST: &str = "4294967296m";

/// `plan-basic` with `^a1`'s leading estimate replaced by `lead`.
fn with_lead(lead: &str) -> Tm {
    let tm = Tm::new();
    let path = tm.plan.join("backlog.md");
    let text = std::fs::read_to_string(&path).expect("backlog");
    let edited = text.replacen(
        "- [ ] 2 30m Insurance claim for the bike  ^a1",
        &format!("- [ ] 2 {lead} Insurance claim for the bike  ^a1"),
        1,
    );
    assert_ne!(edited, text, "the fixture holds ^a1's line");
    std::fs::write(&path, edited).expect("write");
    tm
}

/// The host's reading: the title segment and the leading estimate's text.
fn host_reading(line: &str) -> (String, Option<String>) {
    let l = ItemLine::parse(line).expect("an item line");
    let text_of = |k: TokenKind| l.tokens.iter().find(|t| t.kind == k).map(|t| t.text.clone());
    (text_of(TokenKind::Title).unwrap_or_default(), text_of(TokenKind::Est))
}

/// The kernel's reading, through its `est` op: `tm edit ^a1 est=45m` rewrites
/// the slot in place when the kernel reads `lead` as the slot.
fn kernel_rewrite(lead: &str) -> String {
    let tm = with_lead(lead);
    tm.ok(&["edit", "^a1", "est=45m"]);
    tm.line("backlog.md", "a1")
}

/// **At the bound and past it, the two readers read ONE slot and one title.**
#[test]
fn the_host_and_the_kernel_read_the_slot_alike_at_and_past_the_width() {
    for lead in [BOUND, PAST, "9999999999999m", "71582789h", "4294967296b", "1h4294967296m"] {
        let line = format!("- [ ] 2 {lead} Insurance claim for the bike  ^a1");
        let (title, est) = host_reading(&line);
        assert_eq!(title, "Insurance claim for the bike", "the host's title for {lead}");
        assert_eq!(est.as_deref(), Some(lead), "the host reads {lead} as the slot");
        let rewritten = kernel_rewrite(lead);
        assert_eq!(
            rewritten, "- [ ] 2 45m Insurance claim for the bike  ^a1",
            "the kernel read {lead} as the slot and rewrote it in place"
        );
    }
}

/// **A word that is not duration-shaped stays a title word, to both.**
#[test]
fn a_word_that_is_not_the_slots_shape_stays_in_the_title_for_both() {
    for lead in ["3d", "12hm", "5hh", "m30", "1h5"] {
        let line = format!("- [ ] 2 {lead} Insurance claim for the bike  ^a1");
        let (title, est) = host_reading(&line);
        assert_eq!(title, format!("{lead} Insurance claim for the bike"), "{lead}");
        assert!(est.is_none(), "{lead}");
        let rewritten = kernel_rewrite(lead);
        assert!(
            rewritten.contains(&format!("{lead} Insurance claim for the bike")),
            "the kernel kept {lead} in the title: {rewritten}"
        );
    }
}

/// **`tm check` names a slot it cannot hold; at the bound it says nothing.**
#[test]
fn tm_check_names_a_leading_estimate_past_the_width() {
    let past = with_lead(PAST);
    let out = past.run(&["check"]);
    assert_eq!(out.code, 2, "an error: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains(&format!("`{PAST}` (the leading estimate)")), "{}", out.stdout);
    let at = with_lead(BOUND);
    let out = at.run(&["check"]);
    assert!(!out.stdout.contains("(the leading estimate)"), "{}", out.stdout);
}

/// **`tm start` shows the title without the word, and `tm extend` and `tm stop`
/// lose no title word** — at the bound + 1 and at the drive's own word, which is
/// how gap 3140 was found.
#[test]
fn extend_and_stop_on_a_leading_estimate_past_the_width_lose_no_title_word() {
    for lead in [PAST, "9999999999999m"] {
        let tm = with_lead(lead);
        tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
        let started = tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^a1", "--energy", "4"]);
        assert!(started.stdout.contains("Insurance claim for the bike"), "{}", started.stdout);
        assert!(!started.stdout.contains(lead), "the word is the slot, not the title: {}", started.stdout);
        tm.ok_at("2026-09-07T09:05:00-05:00", &["extend", "1b"]);
        tm.ok_at("2026-09-07T09:20:00-05:00", &["stop"]);
        let line = tm.line("backlog.md", "a1");
        assert!(line.contains("Insurance claim for the bike"), "no title word lost at {lead}: {line}");
        let (title, _) = host_reading(&line);
        assert_eq!(title, "Insurance claim for the bike", "{lead}: {line}");
    }
}

/// **`tm check`'s swallowed-ci rule reads the slot by the same shape** (W-37
/// repair, README gap 3336). A number in the positional ci slot the tokenizer
/// could not eat (`7`) blocks the leading estimate behind it; the rule reported
/// that only when the word behind was an estimate by MAGNITUDE (`u32` minutes),
/// so `7 4294967296m` went unreported while `7 30m` was an error — the second
/// reader of "is this word the leading estimate" track T's P57 left behind.
#[test]
fn a_swallowed_ci_is_reported_whatever_the_estimate_behind_it_weighs() {
    for lead in ["30m", PAST] {
        let tm = Tm::new();
        let path = tm.plan.join("backlog.md");
        let text = std::fs::read_to_string(&path).expect("backlog");
        let edited = text.replacen(
            "- [ ] 2 30m Insurance claim for the bike  ^a1",
            &format!("- [ ] 7 {lead} Insurance claim for the bike  ^a1"),
            1,
        );
        assert_ne!(edited, text, "the fixture holds ^a1's line");
        std::fs::write(&path, edited).expect("write");
        let out = tm.run(&["--json", "check"]);
        assert!(
            out.stdout.contains("bad-ci") && out.stdout.contains(&format!("`7 {lead}`")),
            "`7 {lead}` is named as a swallowed ci: {}{}",
            out.stdout,
            out.stderr
        );
    }
}
