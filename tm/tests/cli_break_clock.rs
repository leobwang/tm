//! **A break running across local midnight began at the latest instant at or
//! before `now` with its clock** — the campaign's D81 call on README gap 3820,
//! parity P73, stage 6 W-41 track T.
//!
//! `.tm/state.json`'s `break.started` is a bare `HH:MM`, and the log holds no
//! line for a running break (its `break` entry is appended when it ends), so
//! the cache's clock is all there is. Fork 4748911 placed it on TODAY's date at
//! every site: after midnight a break begun at 23:50 began TONIGHT, so `tm
//! done` netted none of it out of the block (`actual_min: 70` where fifty were
//! worked), `tm break`'s end logged it tonight with `actual_min: 0`, and `tm
//! now` read the break as worked. One function reads it now
//! (`BreakState::started_at`), at every site: the worked minutes, `end_break`,
//! `since_break_min`, D61's walls request, the week cut's, `tm pause`'s, and the
//! TUI's timer and break-overrun prompt (`break_clock_timer.rs`).

mod cli_common;

use cli_common::Tm;

/// Gap 3820's world: `^t4` from Tuesday 23:00 and a break begun at 23:50.
fn on_a_break() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-08T23:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T23:50:00-05:00", &["break", "20m"]);
    tm
}

/// **`tm done` at 00:10 logs the fifty minutes worked and the break as the
/// evening's twenty** — `tm now` at 00:05 already read fifty.
#[test]
fn a_break_across_midnight_is_the_evenings() {
    let tm = on_a_break();
    let now = tm.json_at("2026-09-09T00:05:00-05:00", &["now"]);
    assert_eq!(now["active"]["elapsed_min"].as_u64(), Some(50), "the break is not worked: {now}");
    let out = tm.ok_at("2026-09-09T00:10:00-05:00", &["done"]);
    assert_eq!(out.stdout.trim(), "✓ ^t4 Claude Code drafts tests · 50m/60m");
    let log = tm.log();
    let brk = &log[log.len() - 2];
    assert_eq!(
        (brk["ev"].as_str(), brk["t"].as_str(), brk["actual_min"].as_u64()),
        (Some("break"), Some("2026-09-08T23:50:00-05:00"), Some(20)),
        "{brk}"
    );
    assert_eq!(tm.last()["actual_min"].as_u64(), Some(50), "{}", tm.last());
    let tue = tm.json_at("2026-09-09T00:11:00-05:00", &["review", "day", "--date", "2026-09-08"]);
    assert_eq!(tue["review"]["breaks"]["actual_min"].as_u64(), Some(20), "{tue}");
}

/// **`tm stop` and `tm break`'s own end read it the same way**: the stop nets
/// the break out (fifty worked, ten left), and a break ended by `tm break` at
/// 00:15 is logged as the evening's twenty-five.
#[test]
fn every_verb_that_ends_the_break_reads_one_start() {
    let tm = on_a_break();
    let out = tm.json_at("2026-09-09T00:10:00-05:00", &["stop"]);
    assert_eq!((out["worked_min"].as_u64(), out["remaining_min"].as_u64()), (Some(50), Some(10)), "{out}");

    let tm = on_a_break();
    let out = tm.json_at("2026-09-09T00:15:00-05:00", &["break"]);
    assert_eq!((out["action"].as_str(), out["actual_min"].as_u64()), (Some("ended"), Some(25)), "{out}");
    assert_eq!(tm.last()["t"], "2026-09-08T23:50:00-05:00", "{}", tm.last());
}

/// **D61's walls request reads the same start**: a call 00:00–00:30 begins
/// while the break that began at 23:50 has the timer already stopped, so no
/// meeting pause is written — where the break read as tonight's left the timer
/// running at midnight and the call was logged as pausing it.
#[test]
fn a_wall_inside_the_break_writes_no_pause() {
    let tm = on_a_break();
    let path = tm.plan.join("calendar/2026-W37.md");
    let mut text = std::fs::read_to_string(&path).expect("calendar");
    text.push_str("- [ ] 3 Late call          at:2026-09-09T00:00/00:30 ^g7\n");
    std::fs::write(&path, text).expect("write calendar");
    let out = tm.ok_at("2026-09-09T00:35:00-05:00", &["now"]);
    assert!(!out.stderr.contains("paused ^t4"), "{}", out.stderr);
    assert!(!tm.events().iter().any(|e| e == "pause"), "{:?}", tm.events());
}

/// Whether `text` holds `word` with no identifier character on either side
/// (`prefix` may start with a non-identifier character, `.break_`).
fn has_word(text: &str, word: &str) -> bool {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    text.match_indices(word).any(|(i, _)| {
        let before = text[..i].chars().next_back();
        let after = text[i + word.len()..].chars().next();
        (word.starts_with('.') || !before.is_some_and(ident)) && !after.is_some_and(ident)
    })
}

/// Every function of a source file, `(name, first line, body)`, at its `fn`
/// lines, with `//` comments dropped.
fn functions(text: &str) -> Vec<(String, usize, String)> {
    let lines: Vec<String> = text
        .lines()
        .map(|l| l.find("//").map_or(l, |i| &l[..i]).to_string())
        .collect();
    let starts: Vec<(usize, String)> = lines
        .iter()
        .enumerate()
        .filter_map(|(i, l)| {
            let t = l.trim_start();
            let rest = t.strip_prefix("pub(crate) fn ").or_else(|| t.strip_prefix("pub fn ")).or_else(|| t.strip_prefix("fn "))?;
            Some((i, rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect()))
        })
        .collect();
    starts
        .iter()
        .enumerate()
        .map(|(n, (i, name))| {
            let end = starts.get(n + 1).map_or(lines.len(), |(j, _)| *j);
            (name.clone(), i + 1, lines[*i..end].join("\n"))
        })
        .collect()
}

/// **The class, not a list** (README gap 3820's own body shapes): a function of
/// the host or of `tm-core` that touches a running break (`.break_`), reads a
/// `.started` and places a clock (`ctx.at(`, `self.local(`, `local_dt(`,
/// `clock_sec(`, the codec's `cache`) reads the break's start through
/// `BreakState::started_at` — or is the one named below. Driven: on `122e153`
/// this finds the nine sites P73 moved (eight in `tm/src`, and the planner
/// request's `state_json`, moved at W-41's land step, README gap 4001) and
/// `reconcile_state`.
#[test]
fn every_reader_of_a_running_breaks_start_reads_one_function() {
    let exempt = [
        // Reads only THAT a break runs (`break_.is_some()`); its `.started` and its
        // clock call are the running block's and the arrival's.
        ("tm/src/cli/ctx.rs", "reconcile_state"),
    ];
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut found = Vec::new();
    // And the HARNESS (the W-41 repair, README gap 4143): a reader that computes what the
    // KERNEL should answer (P45's rule, P67's transformation) reads the binary's start, so a
    // generated world that carries a break across midnight is asked the binary's question.
    let mut stack = vec![root.join("tm/src"), root.join("tm-core/src"), root.join("tm/tests")];
    while let Some(dir) = stack.pop() {
        for e in std::fs::read_dir(&dir).expect("a source directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().is_none_or(|x| x != "rs") {
                continue;
            }
            let rel = p.strip_prefix(&root).expect("inside").to_string_lossy().replace('\\', "/");
            let text = std::fs::read_to_string(&p).expect("a source file");
            for (name, line, body) in functions(&text) {
                let clock = [".at(", ".local(", "local_dt(", "clock_sec("].iter().any(|c| body.contains(c))
                    || has_word(&body, "cache");
                if has_word(&body, ".break_") && has_word(&body, ".started") && clock && !body.contains("started_at(") {
                    found.push((rel.clone(), name, line));
                }
            }
        }
    }
    found.sort();
    let names: Vec<(&str, &str)> = found.iter().map(|(f, n, _)| (f.as_str(), n.as_str())).collect();
    let mut want = exempt.to_vec();
    want.sort();
    assert_eq!(names, want, "a reader of a running break's start that is not `BreakState::started_at`: {found:?}");
}
