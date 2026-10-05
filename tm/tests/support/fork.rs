//! **The comparand that survives §12's deletion** (README gaps 137, 146, 147,
//! 149; design §14.6 item 4, §17).
//!
//! Fork point `4748911` is the last commit carrying the Rust `log::replay` this
//! kernel is a port of. Its answers are taken once through AGENTS §7.3's oracle
//! and frozen into `tm/tests/fixtures/`, and this module is the one place that
//! reads them back and compares.
//!
//! **Neither side of a comparison here is the in-tree reader.** One side is a
//! `tm_core::log::Replay` the *kernel* produced (`kernel_log::decode_facts`, the
//! function `Ctx::replay_with` calls at S); the other is bytes on disk. So §12's
//! deletion cannot turn any of it into a self-comparison — which is the whole
//! reason it exists, and why it is a shared `support/` module rather than
//! private to `kernel_replay_parity.rs`: `kernel_log_door.rs` needs the same
//! comparand for the same reason.
//!
//! Re-bless with, from the repository root:
//!
//! ```text
//! TM_ORACLE=$(kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh) \
//! TM_FORK_BLESS=1 cargo test --test kernel_replay_parity -- --ignored \
//!   the_frozen_fork_answers_are_reblessed_from_the_oracle
//! ```
//!
//! A re-bless is a decision about what the fork point says, never a way to make
//! a failure go away (AGENTS §7.2).
//!
//! **The comparison is only as fine as the parser under it** (W-12, README gap
//! 235). Both sides of every frozen comparison — the oracle's stdout at the
//! bless, the fixture at the read — are decoded by this workspace's
//! `serde_json`, and without its `float_roundtrip` feature serde's best-effort
//! decimal parser answers the *nearest-but-one* double for a literal that needs
//! all 17 significant digits: it read the fork's own
//! `"days.2026-08-29.load": 187.60000000000002` back as `187.6`, which is
//! exactly the double the kernel's `load_fifths / 5` produces. Eight genuine
//! parity **P21** sightings across the two fixtures were therefore counted as
//! agreement, and the bless had silently rounded the fork's answer into the
//! file. The feature is on in the root `Cargo.toml` and
//! [`the_frozen_comparand_is_read_at_full_precision`] (in
//! `kernel_replay_parity.rs`) fails if it is ever dropped. Nothing about the
//! *kernel's* own numeral parser changes: it ports serde **without**
//! `float_roundtrip`, because that is what fork point `4748911` runs (parity
//! P25, kernel/README.md's `finiteF64` row).

use std::collections::BTreeMap;
use std::sync::OnceLock;

use serde_json::Value;
use tm_core::log::Replay;

/// The frozen corpus answers (W-10, `3c0844c`): the seven `kernel/corpus` logs.
pub const FROZEN_FORK: &str = "fork-4748911-corpus-replay.jsonl";

/// The frozen class answers (W-11, gap 147 under **D21**): the generated classes
/// small enough to freeze **by value**.
///
/// D21 settles what goes in it — *one representative generated month*, not every
/// generated class, and **values, never a digest**. A digest over the fork-shaped
/// JSON would have to normalise parity **P21** out (some `days.<date>.load`
/// values legitimately differ between the kernel's exact fifths and the fork's
/// accumulated `f64`), and normalising P21 out hides the one thing P21 exists to
/// watch. Every sighting stays visible and counted — which, until W-12's
/// `float_roundtrip` (module docs above, README gap 235), the *parser* was
/// quietly undoing on five of this file's records and three of [`FROZEN_FORK`]'s.
///
/// §6.4's zone cases ride along: twelve tiny logs, 18,748 bytes for the lot, and
/// they are the day index's own instrument.
pub const FROZEN_CLASSES: &str = "fork-4748911-classes-replay.jsonl";

pub fn fixtures_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// The frozen answers by log name, read once. Each carries the fork's serialised
/// `Replay`, its all-time entry count, and the physical lines its reader refused.
pub fn frozen_fork_answers() -> &'static BTreeMap<String, Value> {
    static FROZEN: OnceLock<BTreeMap<String, Value>> = OnceLock::new();
    FROZEN.get_or_init(|| {
        let mut out = BTreeMap::new();
        for file in [FROZEN_FORK, FROZEN_CLASSES] {
            let path = fixtures_dir().join(file);
            let text = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("{}: {e} — re-bless it (see support/fork.rs)", path.display()));
            for l in text.lines().filter(|l| !l.trim().is_empty()) {
                let v: Value = serde_json::from_str(l).expect("a frozen fork answer is JSON");
                let name = v["name"].as_str().expect("a frozen fork answer names its log").to_string();
                assert!(out.insert(name.clone(), v).is_none(), "two frozen answers for `{name}`");
            }
        }
        out
    })
}

/// One line of a frozen fixture: the name, the fork's entry count, the lines its
/// reader refused, and its whole serialised `Replay`.
pub fn frozen_row(name: &str, a: &Value) -> String {
    let row = serde_json::json!({
        "name": name,
        "entries": a["entries"],
        "warningLines": a["warningLines"],
        "replay": a["replay"],
    });
    serde_json::to_string(&row).expect("a frozen answer serialises") + "\n"
}

/// The fork point's `Replay` keys this compares **whole**. The fork serialises
/// **20**; two are left out of this list, and neither is left uncompared:
///
/// * `events` — the fork keeps a list of every occurrence per name; the kernel
///   keeps only the latest per `(name, id?)` (design §8.4), so the *values*
///   have no common shape. The **key set** does, and it is what the binary
///   reads: `priority::collect_candidates` builds its `events` set from
///   `Replay::event_names()`. [`compare_event_names`] compares exactly that,
///   counted separately in [`ForkTally::event_names`]. *(Restored at stage 5's
///   close, README gap 225: this comment used to say "T5's `latest_named`
///   queries are what compare it", and that stopped being true the moment S
///   deleted the in-tree reader those queries were compared against — the
///   family went from compared to merely counted, with nothing saying so.)*
/// * `warnings` — free text on the fork's side, named constructors on the
///   kernel's: **parity P15**, compared by line and status instead.
///
/// **One record differs in shape, and it is a Rust rename, not a fact.** Phase
/// R's R9 (`100bd88`) turned `DayReplay.load` into `load_fifths` with a `load()`
/// accessor, so the fork writes `"load": 5.2` where this branch writes
/// `"load_fifths": 26`. [`as_fork_shaped`] maps the one back to the other —
/// `load_fifths / 5`, the exact fifths R9 claims, divided once — so the
/// comparison tests R9's claim rather than stepping around it. The two `f64`s
/// then differ wherever the fork's accumulated sum has drifted from the exact
/// value: **parity P21**, which design §17 states at exactly this site. Each
/// sighting is counted, and **both of its displays are checked to be equal
/// anyway**. A difference that reaches a display is a defect, not an exception,
/// and fails.
pub const FORK_REPLAY_KEYS: [&str; 18] = [
    "tz",
    "range",
    "days",
    "items",
    "instances",
    "energy",
    "durations",
    "interrupts",
    "demotions",
    "closes",
    "dropped_items",
    "done_items",
    "last_done",
    "done_dates",
    "longest_leak",
    "open_block",
    "open_interrupt",
    "unknown",
];

/// **Parity P21**, checked rather than waved through: this day's `load` differs
/// between the kernel's exact fifths and the fork's accumulated `f64` sum.
/// `Some(why)` only when the difference reaches a display — which is what R9
/// promised it never does ("recorded as P21 here, in Rust, so the switch changes
/// no display").
pub fn p21_display_is_unchanged(date: &str, fifths: u64, fork_load: f64, block_min: u32) -> Option<String> {
    let round1 = |x: f64| (x * 10.0).round() / 10.0;
    let round2 = |x: f64| (x * 100.0).round() / 100.0;
    let b = u128::from(block_min.max(1));
    // R9's exact route: `review.rs`'s `load_blocks_of_fifths`.
    let kernel_blocks = ((40 * u128::from(fifths) + b) / (2 * b)) as f64 / 100.0;
    let fork_blocks = round2(fork_load / f64::from(block_min.max(1)));
    let kernel_load = fifths as f64 / 5.0;
    if round1(kernel_load) != round1(fork_load) {
        return Some(format!(
            "days.{date}.load reaches the display: round1 kernel {} fork {}",
            round1(kernel_load),
            round1(fork_load)
        ));
    }
    if kernel_blocks != fork_blocks {
        return Some(format!("days.{date}.load_blocks differs: kernel {kernel_blocks} fork {fork_blocks}"));
    }
    None
}

/// The kernel-side value in the **fork's** record shape: `load_fifths` back to
/// the fork's `load`, exactly as R9's `DayReplay::load()` computes it. Nothing
/// else is touched, so any other difference is a real one.
pub fn as_fork_shaped(v: &mut Value) {
    match v {
        Value::Array(a) => a.iter_mut().for_each(as_fork_shaped),
        Value::Object(o) => {
            if let Some(fifths) = o.remove("load_fifths").and_then(|f| f.as_u64()) {
                let load = fifths as f64 / 5.0;
                o.insert("load".to_string(), serde_json::json!(load));
            }
            o.values_mut().for_each(as_fork_shaped);
        }
        _ => {}
    }
}

/// Every differing leaf, named by its path, so a finding says which field of
/// which day differs rather than printing two truncated records.
pub fn diff_paths(path: &str, k: &Value, f: &Value, out: &mut Vec<(String, String)>) {
    if k == f {
        return;
    }
    match (k, f) {
        (Value::Object(ko), Value::Object(fo)) => {
            for (key, fv) in fo {
                match ko.get(key) {
                    Some(kv) => diff_paths(&format!("{path}.{key}"), kv, fv, out),
                    None => out.push((
                        format!("{path}.{key}"),
                        format!("{path}.{key}: kernel has no such key, fork {fv}"),
                    )),
                }
            }
            for key in ko.keys().filter(|k| !fo.contains_key(*k)) {
                out.push((
                    format!("{path}.{key}"),
                    format!("{path}.{key}: fork has no such key, kernel {}", ko[key]),
                ));
            }
        }
        (Value::Array(ka), Value::Array(fa)) if ka.len() == fa.len() => {
            for (i, (kv, fv)) in ka.iter().zip(fa).enumerate() {
                diff_paths(&format!("{path}[{i}]"), kv, fv, out);
            }
        }
        _ => {
            let (ks, fs) = (k.to_string(), f.to_string());
            out.push((
                path.to_string(),
                format!("{path}: kernel {} fork {}", &ks[..ks.len().min(90)], &fs[..fs.len().min(90)]),
            ));
        }
    }
}

/// Scalar leaves of a JSON value: the denominator that says how much was
/// actually compared, rather than how many keys were looked at.
pub fn leaves(v: &Value) -> usize {
    match v {
        Value::Array(a) => a.iter().map(leaves).sum(),
        Value::Object(o) => o.values().map(leaves).sum(),
        _ => 1,
    }
}

/// What one fork comparison actually counted, so "no disagreement" is never
/// confused with "never ran" (AGENTS §7.3).
#[derive(Default)]
pub struct ForkTally {
    pub logs: usize,
    pub keys: usize,
    pub values: usize,
    pub entries: usize,
    pub warning_lines: usize,
    /// Parity **P21** sightings: a day whose `load` differs from the fork's in
    /// the last ulp. Counted, and each one's displays checked to be equal.
    pub p21: usize,
    /// `tm event` names compared between the fork's `events` map and the
    /// kernel's [`Replay::event_names`] (README gap 225). Counted apart from
    /// `keys`, because it is the one family whose *values* have no common shape.
    pub event_names: usize,
    /// Inputs that had no frozen answer, so the fork did not answer them at all.
    /// The number that must never be read as agreement.
    pub skipped: usize,
    /// Parity **P100** (the owner's D105): `break_start` lines the fork counted as
    /// unknown events and the kernel read as the running break's, carried onto the
    /// kernel's `unknown` by value ([`p100_starts`]).
    pub p100: usize,
}

impl ForkTally {
    pub fn add(&mut self, o: &ForkTally) {
        self.logs += o.logs;
        self.keys += o.keys;
        self.values += o.values;
        self.entries += o.entries;
        self.warning_lines += o.warning_lines;
        self.p21 += o.p21;
        self.event_names += o.event_names;
        self.skipped += o.skipped;
        self.p100 += o.p100;
    }

    /// One line saying what was compared and what was not.
    pub fn line(&self, what: &str) -> String {
        format!(
            "fork point 4748911 — {what}: {} inputs, {} Replay keys ({} of the fork's 20 each, \
             plus `events`' key set), {} scalar values, {} entry counts, {} refused-line lists, \
             {} event-name sets compared; parity P21 {} day records, every one displaying the \
             same load; parity P100 {} `break_start` lines carried onto `unknown`; {} inputs had no \
             frozen answer; 0 other exceptions",
            self.logs,
            self.keys,
            FORK_REPLAY_KEYS.len(),
            self.values,
            self.entries,
            self.warning_lines,
            self.event_names,
            self.p21,
            self.p100,
            self.skipped
        )
    }
}

/// **Parity P100, by value** (the owner's D105, README "Stage 6 — W-46 track K"): the
/// `break_start` lines of `kr`'s log that no `undo` cancelled — read off the kernel's own
/// rows, never off a count. Fork 4748911 has no such event: it reads each of these lines as
/// an unknown event and counts it in `unknown`, where the kernel reads it as the running
/// break's start and counts nothing. So the fork's `unknown` is the kernel's plus this.
///
/// The rows are the WHOLE log's only at `All` scope, which is the only scope this
/// comparison is asked of (T5's answers and the door's `All` reads).
pub fn p100_starts(kr: &Replay) -> u64 {
    kr.view().iter().filter(|r| r.tag == "break_start" && !r.cancelled).count() as u64
}

/// **Compare a `Replay` the kernel produced with fork point 4748911's own.**
///
/// `kr` must be the *kernel's* replay — `kernel_log::decode_facts`' output, or
/// `kernel_log::replay_scoped`'s `All` scope, which is the same function. The
/// fork's side is the frozen row. Key for key over [`FORK_REPLAY_KEYS`], plus the
/// all-time entry count and the physical lines each reader refused. Every
/// disagreement that is not a recorded design §17 exception comes back by name.
pub fn compare_replay_with_fork(
    name: &str,
    kr: &Replay,
    entries: u64,
    warnings: &[u64],
    fork_answer: &Value,
    t: &mut ForkTally,
) -> Vec<String> {
    let mut findings: Vec<String> = Vec::new();
    let kv_raw = serde_json::to_value(kr).expect("the kernel's replay serialises");
    let mut kv = kv_raw.clone();
    as_fork_shaped(&mut kv);
    // **Parity P100, carried by value** (the owner's D105): the kernel's `unknown` moved by
    // P100's rule — every surviving `break_start` is one more unknown event to the fork — and
    // then compared key for key like any other value, so a kernel that counted one, or
    // cancelled the wrong one, still fails at `unknown` by name.
    let p100 = p100_starts(kr);
    if p100 > 0 {
        let u = kv["unknown"].as_u64().expect("the kernel's unknown count");
        kv["unknown"] = serde_json::json!(u + p100);
        t.p100 += p100 as usize;
    }
    let fork = &fork_answer["replay"];
    t.logs += 1;

    for key in FORK_REPLAY_KEYS {
        let (k, f) = (&kv[key], &fork[key]);
        assert!(!f.is_null() || k.is_null(), "{name}: the frozen fork has no key `{key}`");
        t.keys += 1;
        t.values += leaves(f);
        if k == f {
            continue;
        }
        let mut paths = Vec::new();
        diff_paths(key, k, f, &mut paths);
        let mut real: Vec<String> = Vec::new();
        for (path, message) in paths {
            // `days.<date>.load` is parity P21: counted and checked, never skipped.
            if let Some(date) = path.strip_prefix("days.").and_then(|r| r.strip_suffix(".load")) {
                t.p21 += 1;
                let day = &fork["days"][date];
                let fifths = kv_raw["days"][date]["load_fifths"].as_u64().expect("the kernel's fifths");
                let fork_load = day["load"].as_f64().expect("the fork's load");
                let block_min = u32::try_from(day["block_min"].as_u64().expect("the day's block_min"))
                    .expect("a u32 (P17: the decoder at S refuses minutesOverflow by name)");
                if let Some(why) = p21_display_is_unchanged(date, fifths, fork_load, block_min) {
                    real.push(why);
                }
                continue;
            }
            real.push(message);
        }
        if real.is_empty() {
            continue;
        }
        let shown = real.len().min(6);
        findings.push(format!(
            "{name}: `{key}` differs at {} leaf/leaves\n      {}",
            real.len(),
            real[..shown].join("\n      ")
        ));
    }

    // The one family whose values have no common shape, compared by the part
    // that does: the set of `tm event` names (README gap 225).
    if let Some(why) = compare_event_names(name, kr, fork, t) {
        findings.push(why);
    }

    // The all-time entry count (design §8.4's `entryCount`, §11.4 step 5's
    // `tm log` total; gap 136).
    t.entries += 1;
    let fork_entries = fork_answer["entries"].as_u64().expect("a frozen entry count");
    if entries != fork_entries {
        findings.push(format!("{name}: entries differ — kernel {entries} fork {fork_entries}"));
    }

    // The physical lines each reader refused. Parity P15 makes the warning
    // *text* differ by design (named constructors against serde's free text) —
    // which line is refused must not.
    let fork_lines: Vec<u64> = fork_answer["warningLines"]
        .as_array()
        .expect("frozen warning lines")
        .iter()
        .map(|l| l.as_u64().expect("a refused line"))
        .collect();
    t.warning_lines += fork_lines.len();
    if warnings != fork_lines.as_slice() {
        findings.push(format!("{name}: the refused lines differ — kernel {warnings:?} fork {fork_lines:?}"));
    }
    findings
}

/// **The `events` family, compared by the part both sides agree on** (README
/// gap 225).
///
/// The fork's `events` is `BTreeMap<String, Vec<NamedEvent>>` — every
/// occurrence of every `tm event <name>`. This branch narrowed it at step X1 to
/// `named`, the latest record per `(name, id?)` (design §8.4), so the values
/// cannot be compared leaf for leaf and the key is not in
/// [`FORK_REPLAY_KEYS`]. **The names can be compared, and they are the half the
/// binary reads**: `priority::collect_candidates` builds a candidate's `events`
/// set from `Replay::event_names()`, which is `named`'s keys, and an
/// `on-event:` recurrence fires off that set.
///
/// Returns `None` when the two name sets are equal, and the difference by name
/// when they are not. `t.event_names` counts the names the fork offered, so a
/// log with no `tm event` in it adds 0 and can never read as agreement.
pub fn compare_event_names(name: &str, kr: &Replay, fork: &Value, t: &mut ForkTally) -> Option<String> {
    let fork_names: Vec<&str> = match fork["events"].as_object() {
        Some(o) => o.keys().map(String::as_str).collect(),
        // The fork always serialises the key; a missing one is a damaged fixture.
        None => {
            assert!(fork["events"].is_null(), "{name}: the frozen fork's `events` is not a map");
            Vec::new()
        }
    };
    t.event_names += fork_names.len();
    // Both sides are `BTreeMap` keys, so both are sorted and deduplicated.
    let kernel_names: Vec<&str> = kr.event_names().collect();
    if kernel_names == fork_names {
        return None;
    }
    Some(format!(
        "{name}: the `tm event` names differ — kernel {kernel_names:?} fork {fork_names:?}"
    ))
}

/// Panic unless `findings` is empty, quoting every one.
pub fn no_disagreement(findings: &[String]) {
    assert!(
        findings.is_empty(),
        "{} disagreements with fork point 4748911 (each must be on design \u{a7}17's list):\n  {}",
        findings.len(),
        findings.join("\n  ")
    );
}

/// What [`reader_scan`] found: the deletion region's size, the marked call sites
/// outside it, and every reference to §12's reader that escaped both.
pub struct ReaderScan {
    pub region_bytes: usize,
    pub markers: usize,
    pub escapes: Vec<String>,
    /// True once the region is gone — which is to say, after S.
    pub deleted: bool,
}

/// **Is §12's deletion mechanical in this file?** (README gaps 146, 149.)
///
/// Design §12's one-reader grep is the definition of "the reader". This runs
/// that alternation over a test file's own source and requires every hit to be
/// either inside its `BEGIN … END THE IN-TREE CROSS-CHECK` region or on a line
/// marked `// S: deleted with the reader`. So S's deletion is
/// `sed '/BEGIN THE IN-TREE/,/END THE IN-TREE/d'` plus those marked lines, and
/// nothing else has to be found by reading.
///
/// **Once the region is gone it keeps checking**: with no banners in the file,
/// *no* reference may remain anywhere. That is what makes this the instrument
/// for the deletion rather than a note about it — after S it is the assertion
/// that the comparand really did move.
///
/// Comment lines are skipped: a comment may name the reader freely, because it
/// compiles to nothing. The needles live here rather than in the scanned file,
/// so a file that greps itself cannot match its own test.
pub fn reader_scan(source: &str) -> ReaderScan {
    const BEGIN: &str = "// BEGIN THE IN-TREE CROSS-CHECK";
    const END: &str = "// END THE IN-TREE CROSS-CHECK";
    const MARKER: &str = "// S: deleted with the reader";
    // Design §12's alternation, verbatim — plus `in_tree`, which is this repo's
    // own bridge to it. **The bridge matters as much as the symbols.** A line
    // that binds `in_tree::reader(text)` to a name and twenty unmarked lines
    // that use that name are not a mechanical deletion, and the alternation
    // alone cannot see them: the convention is that every such binding is named
    // `in_tree_*`, so one needle catches the call and every use of its result.
    const NEEDLES: [&str; 13] = [
        "in_tree",
        "replay_of_text",
        "entries_of_text",
        "warning_lines_of_text",
        "Log::parse",
        "Log::new",
        "parse_bytes",
        "LogEntry::parse",
        "parse_timestamp",
        "undo_mask",
        "DayIndex",
        "iter_day",
        ".effective()",
    ];

    let (outside, region_bytes, deleted) = match (source.find(BEGIN), source.find(END)) {
        (Some(i), Some(j)) => {
            assert!(i < j, "the END banner precedes the BEGIN banner");
            let mut outside = source[..i].to_string();
            outside.push_str(&source[j..]);
            (outside, j - i, false)
        }
        (None, None) => (source.to_string(), 0, true),
        _ => panic!("one deletion banner without the other"),
    };

    let mut escapes = Vec::new();
    let mut markers = 0usize;
    for (i, line) in outside.lines().enumerate() {
        if line.trim_start().starts_with("//") {
            continue;
        }
        if line.contains(MARKER) {
            markers += 1;
            // A marked line is deleted **on its own**, so it has to be a whole
            // statement: its brackets must balance. A marker on the closing
            // line of a multi-line `assert!` would leave the opening lines
            // behind, and that is not a mechanical deletion.
            let stripped = line.split(MARKER).next().unwrap_or("");
            let mut depth = 0i32;
            for c in stripped.chars() {
                match c {
                    '(' | '{' | '[' => depth += 1,
                    ')' | '}' | ']' => depth -= 1,
                    _ => {}
                }
            }
            assert_eq!(depth, 0, "line {i}: marked for deletion and not a whole statement: {line}");
            continue;
        }
        for n in NEEDLES {
            if line.contains(n) {
                escapes.push(format!("line {i}: `{n}` in {}", line.trim()));
            }
        }
    }
    ReaderScan { region_bytes, markers, escapes, deleted }
}

// ---------------------------------------------------------------------------
// The fork-point oracle, out of the tree (AGENTS §7.3) — moved here from
// `kernel_replay_parity.rs` at the W-41 repair (README gap 4149).
// ---------------------------------------------------------------------------

/// **The oracle's own usage banner**, read from the binary itself.
///
/// Provenance is not freshness. W-11's audit followed the brief, verified that
/// the scratch tree's `.oracle-ref` and extracted sources were fork point
/// `4748911` — and the *binary* built from them was older than owner decision
/// **D23**, so it had no `parse-entry` mode: every call printed this banner and
/// exited 2, and the success assertion below reported `the fork oracle failed: `
/// with an **empty** message, because that oracle printed its banner on stdout.
/// So the mode is checked before it is used and named when it is missing, and
/// both streams are quoted when a call fails.
///
/// Neither the exit code (2, no subcommand) nor the stream matters here; only
/// the text does.
pub fn oracle_banner(bin: &std::path::Path) -> String {
    let out = std::process::Command::new(bin)
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap_or_else(|e| panic!("the fork oracle {}: {e}", bin.display()));
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// Refuse a stale oracle **by name**, before it is fed anything.
pub fn assert_oracle_mode(bin: &std::path::Path, mode: &str) {
    let banner = oracle_banner(bin);
    assert!(
        banner.contains(&format!("tm-oracle {mode}")),
        "the oracle at {} has no `{mode}` mode — it is STALE, whatever its `.oracle-ref` says. \
         Rebuild it: kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh. Its banner reads:\n{banner}",
        bin.display()
    );
}

/// Run one mode of the fork-point oracle over `texts`, one JSON string per line
/// in, one JSON object per line out.
pub fn fork_oracle(bin: &std::path::Path, args: &[&str], texts: &[String]) -> Vec<Value> {
    use std::io::Write as _;
    assert_oracle_mode(bin, args.first().expect("the oracle is run in a mode"));
    let mut child = std::process::Command::new(bin)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("the fork oracle {}: {e}", bin.display()));
    let mut input = String::new();
    for t in texts {
        input.push_str(&serde_json::to_string(t).expect("a JSON string"));
        input.push('\n');
    }
    // The input is larger than a pipe buffer and so is the oracle's answer, so
    // the write has to happen while this side is free to drain stdout — writing
    // it all first deadlocks: the child blocks writing its reply, we block
    // writing the request.
    let mut stdin = child.stdin.take().expect("stdin");
    let feeder = std::thread::spawn(move || stdin.write_all(input.as_bytes()).expect("write to the oracle"));
    let out = child.wait_with_output().expect("the oracle runs");
    feeder.join().expect("the feeding thread");
    assert!(
        out.status.success(),
        "the fork oracle {} {:?} failed (exit {:?})\n--- stderr ---\n{}\n--- stdout ---\n{}",
        bin.display(),
        args,
        out.status.code(),
        String::from_utf8_lossy(&out.stderr),
        String::from_utf8_lossy(&out.stdout)
    );
    String::from_utf8(out.stdout)
        .expect("the oracle's output is UTF-8")
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("the oracle prints JSON"))
        .collect()
}
