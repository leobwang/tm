//! **Fork 4748911's lookahead, day-0 slots, slot cut, §7 pass and §7.5 batches — BY VALUE**
//! (stage 6 W-46 track C; README gap 4752, restated as a CLASS by that step).
//!
//! # Why this module exists
//!
//! R3 swaps the binary's planner for the kernel's, and with fork `planner.rs` gone a CLASS of
//! tm-core functions has no shipped caller left: measured at W-46 by two instruments (the
//! switched `tm` built at opt-level 0, its `tm_core` symbols against HEAD's; and a by-name call
//! graph over the sources), 35 of them — `priority::compute`, `capacity::lookahead`,
//! `cut_slots`, `energize`, `batches` and the rest (README "W-46 track C" §1).  The switch
//! deletes them.  Until W-46 several COMPARISONS read them in-tree as "the fork": T13
//! (`kernel_lookahead_parity.rs`) held the kernel's lookahead and priorities to them, the TUI
//! queue harness and the §7 tests of shipped functions (`explain`, `deadline_health`,
//! `priorities_for_state`) took their input from `priority::compute`, and P64's precondition read
//! `priority::batches`.  Deleting the functions would turn each into a comparison with nothing.
//! So, before the change (D21) and in D72's shape, every one of them reads fork 4748911's OWN
//! answer from outside the tree: frozen by value in `tests/fixtures/`, re-blessed through
//! `tm-oracle capacity` — built from the extracted fork by `build-oracle.sh`, calling the fork's
//! own functions — and asked live under `TM_ORACLE`.
//!
//! # One call, three backends
//!
//! [`Store::ask`]`(req)` — `req` a JSON object with its `op` and the configuration as
//! `config.toml` TEXT (the fork's own reader of it; a double crosses as text, never as a JSON
//! number — the oracle's serde_json is the fork's, without `float_roundtrip`):
//!
//! * **a plain run** (no `TM_ORACLE`): the frozen file's answer.  The request is compared BY
//!   VALUE with the one the line was frozen from, and a request no line holds FAILS by name —
//!   so a harness that starts asking something new cannot pass on an answer nobody froze;
//! * **`TM_ORACLE` set**: the oracle answers, and its answer must EQUAL the frozen one (the
//!   file is the fork's answer today, README gap 196's freshness rule checked by the mode);
//! * **a RECORDING run** (`TM_ORACLE` and [`RECORD_VAR`] set): the oracle answers and the store
//!   appends each request's line to the file [`RECORD_VAR`] names.  Only [`fork_rebless`] starts one:
//!   the file's `#[ignore]`d bless, inert without `TM_ORACLE` and `TM_FORK_BLESS`, runs ITS OWN
//!   TEST BINARY again — every test in it, by no list — recording, and writes what the run asked
//!   over the frozen file.  That is the D21 family's re-bless (`fork_rebless_history.rs`'
//!   `is_d21`): no line records a departure, so there is nothing a committed version could
//!   license, and a re-bless is a decision, never a repair (AGENTS §7.2).
//!
//! # The file
//!
//! One JSON object a line, sorted by `key`: a configuration line `{"key":"config:<fnv>","config":
//! <toml>}` — every request names its configuration by that key, so a configuration many requests
//! share is written once — and an answer line `{"key":"<op>:<fnv>","op":..,"req":..,"answer":..}`,
//! `<fnv>` the harness's one FNV-1a-64 (`support/fnv.rs`) of the request's canonical text.  No line
//! carries a fork DAY, so `frozenhist::frozen_files` does not read it as a planner comparand.
//!
//! # What it cannot see, declared
//!
//! A request the harness never makes (the bless writes what the file's tests ask, and a line no
//! test asks any more leaves at the next bless, not before); and the oracle's own wire readers —
//! `cap_cand`, `cap_model` — which are checked only by the answers they produce: the first bless
//! held every answer equal to the in-tree function's at `16aaafc` (README "W-46 track C" §3).

#![allow(dead_code)]

#[path = "fnv.rs"]
mod fnv;

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::{Mutex, OnceLock};

use chrono::{DateTime, NaiveDate, Weekday};
use chrono_tz::Tz;
use serde_json::{json, Value};
use tm_core::capacity::{DayCapacity, Exact, Slot, SlotKind, Wall, WallsByDate};
use tm_core::config::Config;
use tm_core::energy::{Hhmm, Model, WeekdayMap};
use tm_core::model::Id;
use tm_core::priority::{Candidate, Prio, PrioClass};

/// `tm/tests/fixtures` — from either crate's tests (`tm`'s, and `tm-core`'s, which include this
/// module by path): every frozen fork answer lives there.
pub fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm/tests/fixtures")
}

// ---------------------------------------------------------------------------
// The oracle's pipe: `tm-oracle capacity`, one request line in, one answer line out
// ---------------------------------------------------------------------------

/// The mode this module asks the oracle in.
pub const MODE: &str = "capacity";

/// **Refuse an oracle without the `capacity` mode BY NAME**, before it is fed anything (README
/// gap 196: provenance is not freshness — an oracle built before W-46 has no such mode).
pub fn assert_capacity_mode(bin: &Path) {
    let out = Command::new(bin).stdin(Stdio::null()).output().unwrap_or_else(|e| panic!("the fork oracle {}: {e}", bin.display()));
    let banner = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert!(
        banner.contains(&format!("tm-oracle {MODE}")),
        "the oracle at {} has no `{MODE}` mode — it is STALE, whatever its `.oracle-ref` says. \
         Rebuild it: kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh. Its banner reads:\n{banner}",
        bin.display()
    );
}

struct Pipe {
    bin: PathBuf,
    io: Option<(Child, ChildStdin, BufReader<ChildStdout>)>,
}

impl Pipe {
    fn ask(&mut self, req: &Value) -> Result<Value, String> {
        if self.io.is_none() {
            let mut child = Command::new(&self.bin)
                .arg(MODE)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .map_err(|e| format!("the fork oracle {}: {e}", self.bin.display()))?;
            let stdin = child.stdin.take().expect("stdin");
            let stdout = BufReader::new(child.stdout.take().expect("stdout"));
            self.io = Some((child, stdin, stdout));
        }
        let (child, stdin, stdout) = self.io.as_mut().expect("spawned");
        let line = serde_json::to_string(req).map_err(|e| e.to_string())?;
        let sent = writeln!(stdin, "{line}").and_then(|()| stdin.flush());
        let mut answer = String::new();
        match sent.and_then(|()| stdout.read_line(&mut answer)) {
            Ok(n) if n > 0 => {}
            other => {
                let status = child.try_wait().ok().flatten();
                self.io = None;
                return Err(format!("the fork oracle stopped answering ({other:?}, exit {status:?})"));
            }
        }
        let v: Value = serde_json::from_str(&answer).map_err(|e| format!("the oracle's answer is not JSON: {e}: {answer}"))?;
        match v.get("error") {
            Some(e) => Err(format!("the fork oracle refused: {e}")),
            None => Ok(v),
        }
    }
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

/// Which backend a run asks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// The frozen file alone.
    Frozen,
    /// The oracle, held to the frozen file.
    Oracle,
    /// The oracle, each line appended to [`RECORD_VAR`]'s file for [`fork_rebless`].
    Record,
}

/// **The variable a recording run reads**: the file each request's line is appended to.  Set by
/// [`fork_rebless`] on the test binary it re-runs, never by hand.
pub const RECORD_VAR: &str = "TM_FORKCAP_RECORD";

/// **The frozen answers of one file, and the oracle when one is set.**
pub struct Store {
    name: &'static str,
    mode: Mode,
    configs: BTreeMap<String, String>,
    lines: BTreeMap<String, (Value, Value)>,
    pipe: Mutex<Option<Pipe>>,
    record: Mutex<Option<std::fs::File>>,
    asked: Mutex<BTreeMap<String, u64>>,
}

static STORE: OnceLock<Store> = OnceLock::new();

/// **This test binary's frozen file** — one per binary that includes this module, named for the
/// binary (`CARGO_CRATE_NAME`), so a bless rewrites exactly what its own binary asks.
pub const FROZEN: &str = concat!("fork-4748911-capacity-", env!("CARGO_CRATE_NAME"), ".jsonl");

/// **The store of this binary's [`FROZEN`] file** (under [`fixtures_dir`]), opened once per
/// process.  The mode is read off the environment: `TM_ORACLE` (the oracle binary) and
/// [`RECORD_VAR`].  A file that does not exist is an empty store (every plain ask then fails by
/// name until it is blessed).
pub fn store() -> &'static Store {
    STORE.get_or_init(|| Store::open(FROZEN))
}

impl Store {
    fn open(name: &'static str) -> Store {
        let oracle = std::env::var_os("TM_ORACLE").map(PathBuf::from);
        let record_to = std::env::var_os(RECORD_VAR).map(PathBuf::from);
        let mode = match (&oracle, &record_to) {
            (None, None) => Mode::Frozen,
            (None, Some(_)) => panic!("{RECORD_VAR} is set and TM_ORACLE is not: a recording run asks the oracle"),
            (Some(_), None) => Mode::Oracle,
            (Some(_), Some(_)) => Mode::Record,
        };
        let record = record_to.map(|p| {
            std::fs::OpenOptions::new().append(true).create(true).open(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
        });
        let pipe = oracle.map(|bin| {
            assert_capacity_mode(&bin);
            Pipe { bin, io: None }
        });
        let path = fixtures_dir().join(name);
        let text = std::fs::read_to_string(&path).unwrap_or_default();
        let (mut configs, mut lines) = (BTreeMap::new(), BTreeMap::new());
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let v: Value = serde_json::from_str(raw).unwrap_or_else(|e| panic!("{name}: a line that is not JSON ({e}): {raw:.120}"));
            let key = v["key"].as_str().unwrap_or_else(|| panic!("{name}: a line with no key: {raw:.120}")).to_string();
            if let Some(c) = v.get("config") {
                let toml = c.as_str().unwrap_or_else(|| panic!("{name}: {key}'s config is not text"));
                assert_eq!(config_key(toml), key, "{name}: a configuration line whose key is not its text's digest");
                configs.insert(key, toml.to_string());
            } else {
                let prev = lines.insert(key.clone(), (v["req"].clone(), v["answer"].clone()));
                assert!(prev.is_none(), "{name}: two lines carry the key {key}");
            }
        }
        Store {
            name,
            mode,
            configs,
            lines,
            pipe: Mutex::new(pipe),
            record: Mutex::new(record),
            asked: Mutex::new(BTreeMap::new()),
        }
    }

    /// The backend this run asks.
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Frozen answer lines and configuration lines.
    pub fn sizes(&self) -> (usize, usize) {
        (self.lines.len(), self.configs.len())
    }

    /// **Fork 4748911's answer to `req`** — by the backend [`Store::mode`] names (the module's doc).
    pub fn ask(&self, req: Value) -> Value {
        let op = req["op"].as_str().unwrap_or_else(|| panic!("a request with no op: {req}")).to_string();
        let toml = req["config"].as_str().unwrap_or_else(|| panic!("a {op} request with no config text")).to_string();
        let ckey = config_key(&toml);
        let mut canon = req.clone();
        canon["config"] = json!(ckey);
        let key = format!("{op}:{}", fnv::fnv1a64_hex(serde_json::to_string(&canon).expect("a request serialises").as_bytes()));
        *self.asked.lock().expect("census").entry(op.clone()).or_default() += 1;
        let frozen = || -> Result<&Value, String> {
            let held = self.configs.get(&ckey).ok_or_else(|| format!("{}: no frozen configuration {ckey}", self.name))?;
            if *held != toml {
                return Err(format!("{}: the frozen configuration {ckey} is not this request's text", self.name));
            }
            let (freq, answer) = self.lines.get(&key).ok_or_else(|| {
                format!("{}: no frozen fork answer for this {op} request ({key}) — the harness asks something the file was not blessed with; re-bless with TM_ORACLE and TM_FORK_BLESS (the file's bless test)", self.name)
            })?;
            if *freq != canon {
                return Err(format!("{}: {key}: the frozen request is not this one (a digest collision)", self.name));
            }
            Ok(answer)
        };
        match self.mode {
            Mode::Frozen => frozen().unwrap_or_else(|e| panic!("{e}")).clone(),
            Mode::Oracle | Mode::Record => {
                let live = {
                    let mut pipe = self.pipe.lock().expect("the oracle's pipe");
                    pipe.as_mut().expect("an oracle").ask(&req).unwrap_or_else(|e| panic!("{}: {op} ({key}): {e}", self.name))
                };
                if self.mode == Mode::Oracle {
                    let held = frozen().unwrap_or_else(|e| panic!("{e}"));
                    assert_eq!(*held, live, "{}: {key}: the frozen {op} answer is not fork 4748911's answer today", self.name);
                } else {
                    let mut text = serde_json::to_string(&json!({"key": ckey, "config": toml})).expect("a line serialises");
                    text.push('\n');
                    text.push_str(&serde_json::to_string(&json!({"key": key, "op": op, "req": canon, "answer": live})).expect("a line serialises"));
                    text.push('\n');
                    let mut rec = self.record.lock().expect("the recorder");
                    rec.as_mut().expect("a record file").write_all(text.as_bytes()).expect("append to the record");
                }
                live
            }
        }
    }

    /// **Fork 4748911's answer to a FRESH request** — asked of the oracle alone, held to no frozen
    /// line and recorded in none: what a `TM_ORACLE` arm over fresh draws asks (D72's other half),
    /// a census whose worlds no frozen file holds.  Without an oracle it FAILS by name: such an arm
    /// is inert without `TM_ORACLE` and must say so before it asks.
    pub fn ask_live(&self, req: Value) -> Value {
        let op = req["op"].as_str().unwrap_or_else(|| panic!("a request with no op: {req}")).to_string();
        *self.asked.lock().expect("census").entry(format!("{op} (live)")).or_default() += 1;
        let mut pipe = self.pipe.lock().expect("the oracle's pipe");
        pipe.as_mut()
            .unwrap_or_else(|| panic!("{}: a live {op} request with no oracle — set TM_ORACLE", self.name))
            .ask(&req)
            .unwrap_or_else(|e| panic!("{}: a live {op}: {e}", self.name))
    }

    /// One census line: the requests answered, by op, and the backend.
    pub fn census(&self) -> String {
        let asked = self.asked.lock().expect("census");
        let ops: Vec<String> = asked.iter().map(|(op, n)| format!("{op} {n}")).collect();
        format!(
            "{}: {:?}, {} frozen answer(s) over {} configuration(s); asked {}",
            self.name,
            self.mode,
            self.lines.len(),
            self.configs.len(),
            ops.join(", ")
        )
    }

    /// The file this store reads, under [`fixtures_dir`].
    pub fn path(&self) -> PathBuf {
        fixtures_dir().join(self.name)
    }
}

/// A configuration's key: `config:` and the FNV-1a-64 of its text.
pub fn config_key(toml: &str) -> String {
    format!("config:{}", fnv::fnv1a64_hex(toml.as_bytes()))
}

/// Whether this run asks the oracle (`TM_ORACLE` set) — the census arms read it.
pub fn oracle_set() -> bool {
    std::env::var_os("TM_ORACLE").is_some()
}

/// **A file's bless**, the part every bless shares — called by the bless only once it has seen
/// `TM_ORACLE` and `TM_FORK_BLESS` both set (the bless says so itself, where
/// `fork_rebless_history.rs` reads it): it runs THIS test binary again — every non-ignored test of
/// it, by no list, `TM_ORACLE` kept and `TM_FORK_BLESS` dropped — in a recording run
/// ([`RECORD_VAR`]), and returns what that run asked: the file's text (one line per key, sorted, a
/// key asked twice written once and required to carry one answer), its answer lines and its
/// configuration lines.  A child that fails FAILS the bless, which then writes nothing.  The caller
/// writes the text over the frozen file.
pub fn fork_rebless(name: &str) -> (String, usize, usize) {
    assert!(
        std::env::var_os("TM_ORACLE").is_some() && std::env::var_os("TM_FORK_BLESS").is_some(),
        "{name}: a bless runs only with TM_ORACLE and TM_FORK_BLESS set"
    );
    let exe = std::env::current_exe().expect("this test binary");
    let dir = std::env::temp_dir().join(format!("forkcap-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).expect("a record directory");
    let record = dir.join("record.jsonl");
    let _ = std::fs::remove_file(&record);
    let out = Command::new(&exe)
        .env(RECORD_VAR, &record)
        .env_remove("TM_FORK_BLESS")
        .output()
        .unwrap_or_else(|e| panic!("{}: {e}", exe.display()));
    assert!(
        out.status.success(),
        "{name}: the recording run of {} failed (exit {:?}) — nothing is written\n--- stdout ---\n{}\n--- stderr ---\n{}",
        exe.display(),
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let text = std::fs::read_to_string(&record).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    let mut lines: BTreeMap<String, Value> = BTreeMap::new();
    for raw in text.lines().filter(|l| !l.trim().is_empty()) {
        let v: Value = serde_json::from_str(raw).expect("a recorded line is JSON");
        let key = v["key"].as_str().expect("a recorded key").to_string();
        if let Some(prev) = lines.insert(key.clone(), v.clone()) {
            assert_eq!(prev, v, "{name}: {key} was asked twice and answered two ways");
        }
    }
    let mut out = String::new();
    for v in lines.values() {
        out.push_str(&serde_json::to_string(v).expect("a line serialises"));
        out.push('\n');
    }
    let configs = lines.keys().filter(|k| k.starts_with("config:")).count();
    (out, lines.len() - configs, configs)
}

/// The message an inert bless prints.
pub fn inert(name: &str) {
    eprintln!(
        "{name}: INERT — set TM_ORACLE to the fork-point oracle binary \
         (kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh prints its path) and \
         TM_FORK_BLESS=1 to rewrite tests/fixtures/{name}"
    );
}

// ---------------------------------------------------------------------------
// The wire: in-tree values out, the fork's answers in
// ---------------------------------------------------------------------------

/// **A configuration as the oracle reads it**: `config.toml`'s text, which fork `Config::parse`
/// reads — and which must read back as THIS configuration (a field `to_toml` could not carry would
/// otherwise be a different request to the fork, silently).
pub fn config_wire(cfg: &Config) -> String {
    let text = cfg.to_toml().expect("a configuration writes as TOML");
    let back = Config::parse(&text).unwrap_or_else(|e| panic!("the configuration's TOML does not read back: {e}\n{text}"));
    assert!(back == *cfg, "the configuration does not round-trip through its TOML:\n{text}");
    text
}

const WEEK: [(Weekday, &str); 7] = [
    (Weekday::Mon, "Mon"),
    (Weekday::Tue, "Tue"),
    (Weekday::Wed, "Wed"),
    (Weekday::Thu, "Thu"),
    (Weekday::Fri, "Fri"),
    (Weekday::Sat, "Sat"),
    (Weekday::Sun, "Sun"),
];

/// **A model as the oracle reads it**: its learned `energy` curves, `p_lounge` (each weight a
/// double's text) and `expected_arrival` — the three a capacity reads — and nothing else: a model
/// carrying any other learned value FAILS here rather than reaching the fork without it.
pub fn model_wire(m: &Model) -> Value {
    let mut back = Model { energy: m.energy.clone(), ..Model::default() };
    let (mut p, mut a) = (serde_json::Map::new(), serde_json::Map::new());
    let (mut pw, mut aw) = (WeekdayMap::new(), WeekdayMap::new());
    for (wd, k) in WEEK {
        if let Some(x) = m.p_lounge.get(wd) {
            p.insert(k.to_string(), json!(x.to_string()));
            pw.set(wd, *x);
        }
        if let Some(h) = m.expected_arrival.get(wd) {
            a.insert(k.to_string(), json!(h.0.format("%H:%M").to_string()));
            aw.set(wd, Hhmm(h.0));
        }
    }
    back.p_lounge = pw;
    back.expected_arrival = aw;
    assert!(back == *m, "a model with learned values beyond energy, p_lounge and expected_arrival — the capacity wire carries those three");
    json!({"energy": m.energy, "p_lounge": p, "expected_arrival": a})
}

/// An instant on the wire (RFC 3339, its offset, sub-seconds when there are any).
pub fn instant_wire(t: &DateTime<Tz>) -> Value {
    json!(t.to_rfc3339())
}

/// Walls on the wire: `[[start, end], …]`.
pub fn walls_wire(ws: &[Wall]) -> Value {
    Value::Array(ws.iter().map(|(a, b)| json!([a.to_rfc3339(), b.to_rfc3339()])).collect())
}

/// Each date's walls: `{date: [[start, end], …]}`.
pub fn walls_by_date_wire(w: &WallsByDate) -> Value {
    Value::Object(w.iter().map(|(d, ws)| (d.to_string(), walls_wire(ws))).collect())
}

/// Slots on the wire: `[[start, end, energy, "block"|"short"], …]` — the oracle's `cap_slot_json`.
pub fn slots_wire(ss: &[Slot]) -> Value {
    Value::Array(
        ss.iter()
            .map(|s| {
                let kind = match s.kind {
                    SlotKind::Block => "block",
                    SlotKind::ShortBlock => "short",
                };
                json!([s.start.to_rfc3339(), s.end.to_rfc3339(), s.energy, kind])
            })
            .collect(),
    )
}

fn at(v: &Value, tz: Tz, what: &str) -> DateTime<Tz> {
    let t = v.as_str().unwrap_or_else(|| panic!("{what} is {v}, not an instant"));
    DateTime::parse_from_rfc3339(t).unwrap_or_else(|e| panic!("{what} {t:?}: {e}")).with_timezone(&tz)
}

/// The fork's slots, read back into the in-tree type (its four fields).
pub fn slots_of(v: &Value, tz: Tz) -> Vec<Slot> {
    v.as_array()
        .unwrap_or_else(|| panic!("slots {v}"))
        .iter()
        .map(|s| Slot {
            start: at(&s[0], tz, "a slot's start"),
            end: at(&s[1], tz, "a slot's end"),
            energy: s[2].as_u64().and_then(|e| u8::try_from(e).ok()).unwrap_or_else(|| panic!("a slot's energy {}", s[2])),
            kind: match s[3].as_str() {
                Some("block") => SlotKind::Block,
                Some("short") => SlotKind::ShortBlock,
                other => panic!("a slot's kind {other:?}"),
            },
        })
        .collect()
}

/// Days of capacity on the wire: `[[date, [m0 .. m5]], …]`.
pub fn caps_wire(caps: &[DayCapacity]) -> Value {
    Value::Array(caps.iter().map(|d| json!([d.date.to_string(), d.minutes_at_level])).collect())
}

/// The fork's days of capacity, read back into the in-tree type (its two fields).
pub fn caps_of(v: &Value) -> Vec<DayCapacity> {
    v.as_array()
        .unwrap_or_else(|| panic!("days {v}"))
        .iter()
        .map(|d| DayCapacity {
            date: NaiveDate::parse_from_str(d[0].as_str().expect("a day's date"), "%Y-%m-%d").expect("a date"),
            minutes_at_level: serde_json::from_value(d[1].clone()).expect("six levels"),
        })
        .collect()
}

/// A day of minutes: `[m0 .. m5]`.
pub fn levels_of(v: &Value) -> [u32; 6] {
    serde_json::from_value(v.clone()).unwrap_or_else(|e| panic!("six levels {v}: {e}"))
}

/// **A candidate on the wire**: the in-tree struct's own `Serialize` output (fork 4748911's
/// `Candidate` has the same thirty fields, field for field), its `multiplier` as the double's text.
pub fn cand_wire(c: &Candidate) -> Value {
    let mut v = serde_json::to_value(c).expect("a candidate serialises");
    v["multiplier"] = json!(c.multiplier.to_string());
    v
}

/// Candidates on the wire, in order.
pub fn cands_wire(cs: &[&Candidate]) -> Value {
    Value::Array(cs.iter().map(|c| cand_wire(c)).collect())
}

/// `yesterday`'s stored priorities on the wire.
pub fn yesterday_wire(y: &BTreeMap<Id, u8>) -> Value {
    Value::Object(y.iter().map(|(id, p)| (id.as_str().to_string(), json!(p))).collect())
}

/// One §7.2 line of the in-tree enum, by the name serde gives it (`rename_all = "lowercase"`).
pub fn class_of(name: &str) -> PrioClass {
    let all = [
        PrioClass::Wall,
        PrioClass::Hot,
        PrioClass::Impossible,
        PrioClass::Overdue,
        PrioClass::Mandatory,
        PrioClass::HotFlag,
        PrioClass::Dated,
        PrioClass::Floor,
        PrioClass::Rank,
        PrioClass::Optional,
    ];
    all.into_iter()
        .find(|c| serde_json::to_value(c).ok().as_ref().and_then(Value::as_str) == Some(name))
        .unwrap_or_else(|| panic!("a grant's class {name:?}"))
}

/// **The fork's grants, read back into the in-tree `Prio`** — its fourteen shared fields by value,
/// and the three exact ones the in-tree pass adds as the whole minutes of their integer fields
/// (`priority.rs`' compute at `16aaafc`: `Exact::of_minutes` of `avail_min`, `allocation_min` and
/// `shortfall_min`, which is `Exact::new(m, 1)`).  The graft's `shortfall_positive`
/// (`plan-seam.patch`) carries a KERNEL grant's sub-minute shortfall into the fork and is `false` on
/// every grant the fork computes; it is checked so and read no further.
pub fn prios_of(v: &Value) -> Vec<Prio> {
    v.as_array()
        .unwrap_or_else(|| panic!("grants {v}"))
        .iter()
        .map(|g| {
            let small = |k: &str| g[k].as_u64().and_then(|n| u8::try_from(n).ok()).unwrap_or_else(|| panic!("a grant's `{k}`: {}", g[k]));
            let minutes = |k: &str| g[k].as_u64().and_then(|n| u32::try_from(n).ok()).unwrap_or_else(|| panic!("a grant's `{k}`: {}", g[k]));
            let shortfall = minutes("shortfall_min");
            assert_eq!(g["shortfall_positive"].as_bool(), Some(false), "the graft is `false` on every grant the fork computes (plan-seam.patch): {g}");
            Prio {
                id: Id::new(g["id"].as_str().expect("a grant's id")),
                p: small("p"),
                class: class_of(g["class"].as_str().expect("a grant's class")),
                k: small("k"),
                u: g["u"].as_str().map(|t| t.parse::<f64>().unwrap_or_else(|e| panic!("a grant's `u` {t:?}: {e}"))),
                bin: (!g["bin"].is_null()).then(|| small("bin")),
                need_min: minutes("need_min"),
                avail_min: minutes("avail_min"),
                avail_min_exact: Exact::new(u128::from(minutes("avail_min")), 1),
                allocation_min: minutes("allocation_min"),
                allocation_min_exact: Exact::new(u128::from(minutes("allocation_min")), 1),
                shortfall_min: shortfall,
                shortfall_min_exact: Exact::new(u128::from(shortfall), 1),
                until: g["until"].as_str().map(|d| NaiveDate::parse_from_str(d, "%Y-%m-%d").expect("a grant's until")),
                hysteresis_applied: g["hysteresis_applied"].as_bool().expect("a grant's hysteresis_applied"),
                raw_p: small("raw_p"),
            }
        })
        .collect()
}

/// The fork's reading of each grant's pass — `priority::utilization(need_min, avail_min)` and
/// `priority::bin_of` over the configured ladder, both the fork's own: `(u, bin)` per grant.
pub fn pass_of(v: &Value) -> Vec<(f64, Option<u8>)> {
    v.as_array()
        .unwrap_or_else(|| panic!("pass {v}"))
        .iter()
        .map(|p| {
            let u = p[0].as_str().expect("u as text").parse::<f64>().expect("a double");
            (u, p[1].as_u64().map(|b| u8::try_from(b).expect("a bin")))
        })
        .collect()
}

/// **One of fork `priority::batches`' groups**, field by field (fork 4748911's `Batch`): its
/// members in key order, the shared min-energy, Σ planned and Σ remaining minutes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForkBatch {
    pub ids: Vec<Id>,
    pub ci: u8,
    pub total_min: u32,
    pub total_remaining_min: u32,
}

impl ForkBatch {
    /// More than one member (fork `Batch::is_batch`'s reading of `ids`).
    pub fn is_batch(&self) -> bool {
        self.ids.len() > 1
    }
}

/// The fork's batches, in order.
pub fn batches_of(v: &Value) -> Vec<ForkBatch> {
    v.as_array()
        .unwrap_or_else(|| panic!("batches {v}"))
        .iter()
        .map(|b| ForkBatch {
            ids: b["ids"].as_array().expect("a batch's ids").iter().map(|i| Id::new(i.as_str().expect("an id"))).collect(),
            ci: b["ci"].as_u64().and_then(|c| u8::try_from(c).ok()).expect("a batch's ci"),
            total_min: b["total_min"].as_u64().and_then(|m| u32::try_from(m).ok()).expect("a batch's total_min"),
            total_remaining_min: b["total_remaining_min"].as_u64().and_then(|m| u32::try_from(m).ok()).expect("a batch's total_remaining_min"),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The requests
// ---------------------------------------------------------------------------

/// **Day 0's slots, the fork's** — fork `cut_slots(from, end, walls)` energised by
/// `EnergyCtx::new(model, cfg, posterior, wake, loc).with_slept(slept).with_blocks_done(blocks_done)
/// .with_allow_home(allow_home)` (the posterior `Posterior::from_reports` of `reports`), and fork
/// `DayCapacity::from_slots(date, slots)`: `(slots, day 0's minutes)`.
#[allow(clippy::too_many_arguments)]
pub fn today(
    store: &Store,
    cfg: &Config,
    model: &Model,
    window: (DateTime<Tz>, DateTime<Tz>),
    walls: &[Wall],
    reports: &[(DateTime<Tz>, u8, u8)],
    wake: DateTime<Tz>,
    loc: &str,
    slept: Option<u32>,
    blocks_done: u32,
    allow_home: bool,
    date: NaiveDate,
) -> (Vec<Slot>, [u32; 6]) {
    let req = json!({
        "op": "today", "config": config_wire(cfg), "model": model_wire(model),
        "from": instant_wire(&window.0), "end": instant_wire(&window.1), "walls": walls_wire(walls),
        "reports": reports.iter().map(|(t, p, r)| json!([t.to_rfc3339(), p, r])).collect::<Vec<_>>(),
        "wake": instant_wire(&wake), "loc": loc, "slept": slept, "blocks_done": blocks_done,
        "allow_home": allow_home, "date": date.to_string(),
    });
    let a = store.ask(req);
    (slots_of(&a["slots"], cfg.tz), levels_of(&a["day0"]))
}

/// **Fork `capacity::lookahead(walls, cfg, model, today_slots, from, days, wake)`**.
pub fn lookahead(
    store: &Store,
    walls: &WallsByDate,
    cfg: &Config,
    model: &Model,
    today_slots: &[Slot],
    from: NaiveDate,
    days: u32,
    wake: chrono::NaiveTime,
) -> Vec<DayCapacity> {
    let req = json!({
        "op": "lookahead", "config": config_wire(cfg), "model": model_wire(model),
        "walls": walls_by_date_wire(walls), "slots": slots_wire(today_slots),
        "from": from.to_string(), "days": days, "wake": wake.format("%H:%M:%S%.f").to_string(),
    });
    caps_of(&store.ask(req)["days"])
}

/// **Fork `cut_slots(from, end, walls)`, as the fork answers it**: its slots (energy 0), its
/// breaks, and `Cut::slot_minutes` and `Cut::break_minutes`.
#[derive(Clone, Debug, PartialEq)]
pub struct ForkCut {
    pub slots: Vec<Slot>,
    pub breaks: Vec<Wall>,
    pub slot_minutes: u32,
    pub break_minutes: u32,
}

/// **Fork `cut_slots(from, end, walls)`** ([`ForkCut`]).
pub fn cut(store: &Store, cfg: &Config, from: DateTime<Tz>, end: DateTime<Tz>, walls: &[Wall]) -> ForkCut {
    let req = json!({
        "op": "cut", "config": config_wire(cfg), "from": instant_wire(&from), "end": instant_wire(&end), "walls": walls_wire(walls),
    });
    let a = store.ask(req);
    let minutes = |k: &str| a[k].as_u64().and_then(|m| u32::try_from(m).ok()).unwrap_or_else(|| panic!("a cut's {k}"));
    ForkCut {
        slots: slots_of(&a["slots"], cfg.tz),
        breaks: a["breaks"].as_array().expect("a cut's breaks").iter().map(|b| (at(&b[0], cfg.tz, "a break"), at(&b[1], cfg.tz, "a break"))).collect(),
        slot_minutes: minutes("slot_minutes"),
        break_minutes: minutes("break_minutes"),
    }
}

/// **Fork `priority::compute(cands, caps, yesterday, cfg, today)`**, and each grant's pass as the
/// fork reads it ([`pass_of`]).
pub fn rank(
    store: &Store,
    cands: &[Candidate],
    caps: &[DayCapacity],
    yesterday: &BTreeMap<Id, u8>,
    cfg: &Config,
    today: NaiveDate,
) -> (Vec<Prio>, Vec<(f64, Option<u8>)>) {
    let refs: Vec<&Candidate> = cands.iter().collect();
    let req = json!({
        "op": "rank", "config": config_wire(cfg), "cands": cands_wire(&refs), "caps": caps_wire(caps),
        "yesterday": yesterday_wire(yesterday), "today": today.to_string(),
    });
    let a = store.ask(req);
    let prios = prios_of(&a["prios"]);
    assert_eq!(prios.len(), cands.len(), "one fork grant per candidate");
    (prios, pass_of(&a["pass"]))
}

/// **Fork `priority::batches(ranked, cfg)`** ([`ForkBatch`]).
pub fn batches(store: &Store, ranked: &[&Candidate], cfg: &Config) -> Vec<ForkBatch> {
    let req = json!({"op": "batches", "config": config_wire(cfg), "ranked": cands_wire(ranked)});
    batches_of(&store.ask(req)["batches"])
}

/// [`batches`] over a FRESH ranking, asked of the oracle alone ([`Store::ask_live`]).
pub fn batches_live(store: &Store, ranked: &[&Candidate], cfg: &Config) -> Vec<ForkBatch> {
    let req = json!({"op": "batches", "config": config_wire(cfg), "ranked": cands_wire(ranked)});
    batches_of(&store.ask_live(req)["batches"])
}

/// **A candidate's cap and floor readings, the fork's** — fork `Candidate::cap_left_min()` and
/// `Candidate::floor_need_min(cfg)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForkCand {
    pub cap_left_min: Option<u32>,
    pub floor_need_min: Option<u32>,
}

/// **Fork `Candidate::cap_left_min` and `Candidate::floor_need_min`** over each candidate.
pub fn cand_facts(store: &Store, cands: &[&Candidate], cfg: &Config) -> Vec<ForkCand> {
    let req = json!({"op": "cand", "config": config_wire(cfg), "cands": cands_wire(cands)});
    let a = store.ask(req);
    let opt = |v: &Value, k: &str| -> Option<u32> { (!v[k].is_null()).then(|| v[k].as_u64().and_then(|m| u32::try_from(m).ok()).unwrap_or_else(|| panic!("a candidate's {k}"))) };
    a["cands"]
        .as_array()
        .expect("the candidates' facts")
        .iter()
        .map(|v| ForkCand { cap_left_min: opt(v, "cap_left_min"), floor_need_min: opt(v, "floor_need_min") })
        .collect()
}

/// A grant on the wire as the oracle's `prio_of` reads it (fork 4748911's `Prio` and the
/// graft's `shortfall_positive`, `false` on every grant the fork computes).
pub fn prio_wire(p: &Prio) -> Value {
    let class = serde_json::to_value(p.class).expect("a class serialises");
    json!({
        "id": p.id.as_str(), "p": p.p, "class": class, "k": p.k, "u": p.u.map(|u| u.to_string()), "bin": p.bin,
        "need_min": p.need_min, "avail_min": p.avail_min, "allocation_min": p.allocation_min,
        "shortfall_min": p.shortfall_min, "shortfall_positive": false,
        "until": p.until.map(|d| d.to_string()), "hysteresis_applied": p.hysteresis_applied, "raw_p": p.raw_p,
    })
}

/// **Fork `capacity::wall_minutes(from, to, walls)`** — §8.1's Σ minutes of the (clipped,
/// merged) walls inside `[from, to)`.
pub fn wall_minutes(store: &Store, cfg: &Config, from: DateTime<Tz>, to: DateTime<Tz>, walls: &[Wall]) -> i64 {
    let req = json!({"op": "wall_minutes", "config": config_wire(cfg), "from": instant_wire(&from), "to": instant_wire(&to), "walls": walls_wire(walls)});
    store.ask(req)["minutes"].as_i64().expect("the wall minutes")
}

/// **Fork `priority::sort_key(prio, cand)`** — `(p, root line order, own line order)`.
pub fn sort_key(store: &Store, prio: &Prio, cand: &Candidate, cfg: &Config) -> (u8, (usize, usize), (usize, usize)) {
    let req = json!({"op": "sort_key", "config": config_wire(cfg), "cand": cand_wire(cand), "prio": prio_wire(prio)});
    let k = &store.ask(req)["key"];
    let pair = |v: &Value| (v[0].as_u64().expect("an order") as usize, v[1].as_u64().expect("an order") as usize);
    (k[0].as_u64().and_then(|p| u8::try_from(p).ok()).expect("a key's p"), pair(&k[1]), pair(&k[2]))
}

/// **Re-bless this binary's frozen fork answers** ([`FROZEN`]) from the oracle: the binary is run
/// again — every test of it, by no list — the store recording each request and fork 4748911's
/// answer ([`fork_rebless`]), and what that run asked is written over the file.  `#[ignore]`d and inert
/// without **both** `TM_ORACLE` and `TM_FORK_BLESS`: it rewrites a committed fixture, which is a
/// decision and never a repair (AGENTS §7.2).  Every binary that includes this module carries it;
/// re-bless one with, from the repository root:
///
/// ```text
/// TM_ORACLE=$(kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh) TM_FORK_BLESS=1 \
///   cargo test --test <binary> -- --ignored the_frozen_fork_capacity_answers_are_reblessed_from_the_oracle
/// ```
#[test]
#[ignore]
fn the_frozen_fork_capacity_answers_are_reblessed_from_the_oracle() {
    if std::env::var_os("TM_ORACLE").is_none() || std::env::var_os("TM_FORK_BLESS").is_none() {
        return inert(FROZEN);
    }
    let (text, answers, configs) = fork_rebless(FROZEN);
    assert!(answers > 0 && configs > 0, "{FROZEN}: the recording run asked the fork nothing");
    std::fs::write(fixtures_dir().join(FROZEN), text).expect("write the frozen fork answers");
    println!("{FROZEN}: {answers} answer line(s) over {configs} configuration(s) written");
}
