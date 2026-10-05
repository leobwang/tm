//! **A frozen comparand's COMMITTED history — what every bless holds its lines against**
//! (stage 6 W-42 track C; README gaps 4139, 4151 and 4280).
//!
//! # The finding
//!
//! Every bless of a frozen fork comparand held each line it was about to write against the
//! line the file already held — and it read "the file already held" off the WORKING COPY. So
//! the working copy decided what was a re-bless (held to the owner's D64) and what was a fresh
//! freeze (held to nothing): delete the file, or one line of it, and every recomputed line is
//! "added". W-41's land step did exactly that to the TUI file — it froze it FRESH, the fixture
//! absent, over a line a track had committed with other answers (README gaps 4123 and 4139) —
//! and the working copy can be bent the same way by anything that writes it: a hand edit, an
//! earlier bless in the same session, a clean checkout of another branch.
//!
//! # The rule this module is the one definition of
//!
//! A bless takes the lines it HOLDS from the file's committed history: the file at the base
//! `kernel/ratchet.py` names and at every commit after it on HEAD's FIRST-PARENT line, oldest
//! first — the walk `ratchet.py` holds the exemption files to (README gap 4132), read from that
//! file so the base has one home. For every key a bless writes, the line it is held against is
//! the LATEST committed version of that key — HEAD's where HEAD holds it, else the last commit
//! since the base that did — so deleting a file or a line, in the working copy or in a commit,
//! cannot turn a re-bless into a fresh freeze. A key no committed version holds is new. And a
//! bless that refuses "a frozen line it no longer writes" asks that of the keys at HEAD
//! ([`Held::head`]): a line a COMMIT removed was reviewed in that commit's diff.
//!
//! **And a merge in progress** ([`merge_heads`], README gap 4286): a key no first-parent version
//! holds is held against the line the commit being merged holds — the window W-41's land froze the
//! TUI file fresh in (gaps 4123 and 4139), which the first-parent walk alone does not reach.
//!
//! **UNCHECKED fails, as `ratchet.py`'s does**: a history git cannot read — a `git archive`
//! copy, a shallow clone without the base, a base that is not an ancestor of HEAD — or a
//! committed version that does not parse is an `Err`, and the bless FAILS and writes nothing
//! rather than holding its lines against nothing.
//!
//! # What it cannot see, declared
//!
//! A commit before the base (the owner moves it, in `ratchet.py`, by D88's rule). A track's own
//! commit off the first-parent line once its merge is committed (it is judged by the merge that
//! brings it — `ratchet.py`'s blind spot, the same walk) — and, during a merge, a key BOTH sides
//! hold differently is held against the first-parent side only. And what a bless does with its
//! INPUT: a bless whose worlds come
//! from the file (the classes' re-bless, the grid's `p63` mode, the classes' re-draw) still
//! reads them from the working copy, where a pending re-draw lives; what this module decides is
//! what each written line is HELD AGAINST, never where its world came from.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// `kernel/ratchet.py`, whose `BASE` is the base of the walk.
pub fn ratchet_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/ratchet.py")
}

/// **The base of the walk**: `kernel/ratchet.py`'s `BASE = "<sha>"`, read from that file (one
/// home: the owner moves it there and every walk moves with it). A file that does not name a
/// forty-digit hex sha is an `Err`.
pub fn base() -> Result<String, String> {
    let path = ratchet_path();
    let text = std::fs::read_to_string(&path).map_err(|e| format!("UNCHECKED: {}: {e}", path.display()))?;
    base_of(&text).ok_or_else(|| format!("UNCHECKED: {} names no `BASE = \"<sha>\"`", path.display()))
}

/// [`base`] over a file's text: the first column-zero `BASE = "<40 hex digits>"`.
pub fn base_of(text: &str) -> Option<String> {
    text.lines().find_map(|l| {
        let sha = l.strip_prefix("BASE = \"")?.strip_suffix('"')?;
        (sha.len() == 40 && sha.bytes().all(|c| c.is_ascii_hexdigit())).then(|| sha.to_string())
    })
}

/// `git -C dir args…`'s stdout, `None` when git cannot say (it is not there, or it exits non-zero).
fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git").arg("-C").arg(dir).args(args).output().ok()?;
    out.status.success().then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

/// **The file's text at `rev`**: `Some("")` when that commit does not hold it, `None` when git
/// cannot say — `ratchet.py`'s `show`, the same two git calls.
pub fn show(path: &Path, rev: &str) -> Option<String> {
    let dir = path.parent()?;
    let name = path.file_name()?.to_str()?;
    let listed = git(dir, &["ls-tree", rev, "--", name])?;
    if listed.trim().is_empty() {
        return Some(String::new());
    }
    git(dir, &["show", &format!("{rev}:./{name}")])
}

/// One committed line: the commit whose file last held its key, its bytes, and its value.
#[derive(Clone, Debug, PartialEq)]
pub struct Committed {
    pub sha: String,
    pub raw: String,
    pub line: Value,
}

/// **What a bless holds**, read off the file's committed history.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Held {
    /// Every key any committed version since the base holds, with its LATEST committed line.
    pub ever: BTreeMap<String, Committed>,
    /// The keys the file at HEAD holds, in its order.
    pub head: Vec<String>,
    /// The distinct versions read, oldest first: the commit and its number of lines.
    pub versions: Vec<(String, usize)>,
}

impl Held {
    /// The committed line `key` is held against, if any commit since the base held it.
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.ever.get(key).map(|c| &c.line)
    }

    /// The keys a committed version held that HEAD does not — what deleting a line would have
    /// turned into a fresh freeze before this module.
    pub fn only_in_history(&self) -> Vec<&str> {
        self.ever.keys().filter(|k| !self.head.contains(k)).map(String::as_str).collect()
    }

    /// One census line for a bless's report.
    pub fn census(&self, what: &str) -> String {
        format!(
            "{what}: held against {} committed line(s) from {} version(s) since the base ({} at HEAD, {} only in history: {:?})",
            self.ever.len(),
            self.versions.len(),
            self.head.len(),
            self.ever.len() - self.head.iter().filter(|k| self.ever.contains_key(*k)).count(),
            self.only_in_history()
        )
    }
}

/// **The lines a bless of `path` holds**, keyed by `key` — over the base [`base`] reads.
pub fn held(path: &Path, key: impl Fn(&Value) -> Option<String>) -> Result<Held, String> {
    held_since(path, &base()?, key)
}

/// [`held`] over an explicit base (a test's own repository).
pub fn held_since(path: &Path, base: &str, key: impl Fn(&Value) -> Option<String>) -> Result<Held, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why} — a bless that cannot read the committed history writes nothing", path.display());
    git(dir, &["merge-base", "--is-ancestor", base, "HEAD"])
        .ok_or_else(|| unchecked(&format!("the base {base} is not an ancestor of HEAD, or git cannot say (a `git archive` copy, a shallow clone)")))?;
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let mut out = Held::default();
    let mut last: Option<String> = None;
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?;
        let mut keys = Vec::new();
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("its line at {rev} is not JSON ({e}): {raw:.80}")))?;
            let k = key(&line).ok_or_else(|| unchecked(&format!("a line at {rev} has no key: {raw:.80}")))?;
            if keys.contains(&k) {
                return Err(unchecked(&format!("two lines at {rev} carry the key {k}")));
            }
            keys.push(k.clone());
            out.ever.insert(k, Committed { sha: rev.clone(), raw: raw.to_string(), line });
        }
        if last.as_deref() != Some(text.as_str()) {
            out.versions.push((rev.clone(), keys.len()));
        }
        out.head = keys;
        last = Some(text);
    }
    // **A merge in progress** (README gap 4286): the branch being merged has committed lines the
    // first-parent walk does not reach, and resolving the merge is when a land re-blesses — W-41's
    // land froze the TUI file FRESH there, over a line track H had committed (gaps 4123, 4139). So
    // a key no first-parent version holds is held against the incoming commit's line.
    for rev in merge_heads(dir) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at the merge head {rev}")))?;
        let mut keys = Vec::new();
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("its line at {rev} is not JSON ({e}): {raw:.80}")))?;
            let k = key(&line).ok_or_else(|| unchecked(&format!("a line at {rev} has no key: {raw:.80}")))?;
            if keys.contains(&k) {
                return Err(unchecked(&format!("two lines at {rev} carry the key {k}")));
            }
            keys.push(k.clone());
            out.ever.entry(k).or_insert(Committed { sha: rev.clone(), raw: raw.to_string(), line });
        }
        out.versions.push((rev, keys.len()));
    }
    Ok(out)
}

/// **What a bless of a WHOLE-FILE comparand holds** (W-45 track C, README gap 4680): a committed
/// snapshot — `emit_planner.rs`' renderings of the fork's fixture days, which a surviving test reads
/// as the fork's frozen answer — is held as [`held`] holds a line: its latest committed text since
/// the base on HEAD's first-parent line (HEAD's where HEAD holds it), else the text the commit being
/// merged holds; `Ok(None)` when no committed version holds the file. The working copy is never
/// what is held, and a history git cannot read is UNCHECKED, an `Err`.
pub fn held_text(path: &Path) -> Result<Option<(String, String)>, String> {
    held_text_since(path, &base()?)
}

/// [`held_text`] over an explicit base (a test's own repository).
pub fn held_text_since(path: &Path, base: &str) -> Result<Option<(String, String)>, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why} — a bless that cannot read the committed history writes nothing", path.display());
    git(dir, &["merge-base", "--is-ancestor", base, "HEAD"])
        .ok_or_else(|| unchecked(&format!("the base {base} is not an ancestor of HEAD, or git cannot say (a `git archive` copy, a shallow clone)")))?;
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let mut latest: Option<(String, String)> = None;
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?;
        if !text.is_empty() {
            latest = Some((rev, text));
        }
    }
    if latest.is_none() {
        for rev in merge_heads(dir) {
            let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at the merge head {rev}")))?;
            if !text.is_empty() {
                latest = Some((rev, text));
            }
        }
    }
    Ok(latest)
}

/// **Every committed version of the file since the base, oldest first, then the working copy**
/// (the W-42 repair, README gap 4341): `(sha, {key: line})` per first-parent commit — the walk
/// [`held_since`] reads — and `("WORKTREE", …)` last, read off the disk. What a PLAIN run holds the
/// history to, with no fork planner: R3 deleted eight of the eleven blesses that ask the gate, so
/// after it a frozen line can change only by hand, and this is what still sees the change.
pub fn versions(path: &Path, key: impl Fn(&Value) -> Option<String>) -> Result<Vec<(String, BTreeMap<String, Value>)>, String> {
    versions_since(path, &base()?, key)
}

/// [`versions`] over an explicit base (a test's own repository).
pub fn versions_since(path: &Path, base: &str, key: impl Fn(&Value) -> Option<String>) -> Result<Vec<(String, BTreeMap<String, Value>)>, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why}", path.display());
    git(dir, &["merge-base", "--is-ancestor", base, "HEAD"])
        .ok_or_else(|| unchecked(&format!("the base {base} is not an ancestor of HEAD, or git cannot say")))?;
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let parse = |rev: &str, text: &str| -> Result<BTreeMap<String, Value>, String> {
        let mut out = BTreeMap::new();
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("its line at {rev} is not JSON ({e}): {raw:.80}")))?;
            let k = key(&line).ok_or_else(|| unchecked(&format!("a line at {rev} has no key: {raw:.80}")))?;
            if out.insert(k.clone(), line).is_some() {
                return Err(unchecked(&format!("two lines at {rev} carry the key {k}")));
            }
        }
        Ok(out)
    };
    let mut out = Vec::new();
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?;
        out.push((rev.clone(), parse(&rev, &text)?));
    }
    let text = std::fs::read_to_string(path).unwrap_or_default();
    out.push(("WORKTREE".to_string(), parse("WORKTREE", &text)?));
    Ok(out)
}

/// **The answer a frozen line holds for the SHIPPED fork**, whatever its file: a comparand line's
/// `shipped` day where the comparand departs, its `day`'s day otherwise (`forkclass::shipped_of`,
/// the gate's own reading); a grid line's `fork`; a fixture day's `day` and `hash`, which ARE the
/// shipped fork's answer (those files carry no comparand).
pub fn shipped_answer(line: &Value) -> Value {
    if line.get("shipped").is_some() {
        if line["shipped"].is_null() { line["day"]["day"].clone() } else { line["shipped"]["day"].clone() }
    } else if line.get("fork").is_some() {
        line["fork"].clone()
    } else {
        serde_json::json!([line["day"], line["hash"]])
    }
}

/// **A line's answers**, by a property of the key and never a list of files: the comparand's and
/// the fork's days (`day`, `shipped`, `whatif`, `hash`, `fork`), every key named by a parity
/// number (`p45` .. `p69`, `p63`: a departure's own answer), and every object the line carries a
/// parity flag in (`d57`, `d60`: `forkclass::flag_homes`' rule). Everything else is the line's
/// WORLD and PROVENANCE.
pub fn is_answer(line: &Value, k: &str) -> bool {
    let numbered = |s: &str| s.strip_prefix('p').is_some_and(|d| !d.is_empty() && d.bytes().all(|c| c.is_ascii_digit()));
    matches!(k, "day" | "shipped" | "whatif" | "hash" | "fork")
        || numbered(k)
        || line[k].as_object().is_some_and(|o| o.iter().any(|(f, v)| numbered(f) && v.is_boolean()))
}

/// **A D64(b) re-draw between two versions of one line**: the newer carries a `d64b` the older
/// does not, its reason dated and naming D64(b) (`forkclass::is_d64b_reason`'s rule).
pub fn redrawn(old: &Value, new: &Value) -> bool {
    let why = new["d64b"]["why"].as_str().or_else(|| new["d64b"].as_str()).unwrap_or_default();
    new["d64b"] != old["d64b"] && why.starts_with("20") && why.contains("D64(b)")
}

/// **The commits a merge in progress is merging** — `MERGE_HEAD`'s lines (an octopus names
/// several), empty when no merge is in progress.
pub fn merge_heads(dir: &Path) -> Vec<String> {
    let Some(file) = git(dir, &["rev-parse", "--git-path", "MERGE_HEAD"]) else { return Vec::new() };
    let file = dir.join(file.trim());
    std::fs::read_to_string(file).map(|t| t.split_whitespace().map(str::to_string).collect()).unwrap_or_default()
}

/// **A frozen class line's key** (`fork-4748911-planner-classes.jsonl`, whose lines carry no name):
/// its class, its secondary floor and its derivation — together they name one line of the file (a
/// re-draw keeps all three; the world is the line's VALUE). One definition, for the classes'
/// re-bless, their re-draw and the reader's own test.
pub fn class_key(l: &Value) -> Option<String> {
    Some(format!("{} | {} | {}", l["class"].as_str()?, l["secondary"], l["derived"]))
}

/// **A line's key, read as a bless reads it**: the string at `field`, or a number's digits.
pub fn key_of(field: &'static str) -> impl Fn(&Value) -> Option<String> {
    move |v: &Value| match &v[field] {
        Value::String(s) => Some(s.clone()),
        Value::Number(n) => Some(n.to_string()),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Every frozen file, by a property; and a line that moves to a new KEY (W-43 track C)
// ---------------------------------------------------------------------------

/// A line's key reader, as a bless and the history gates hold its file by.
pub type KeyFn = Box<dyn Fn(&Value) -> Option<String>>;

/// `tm/tests/fixtures`.
pub fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// **Does a line carry a fork DAY** — a frozen planner or grid answer: a comparand's `shipped`, a
/// grid's `fork`, or a fixture day's `day` beside its `hash` ([`shipped_answer`]'s three shapes)?
pub fn carries_a_fork_day(line: &Value) -> bool {
    line.get("shipped").is_some() || line.get("fork").is_some() || (line.get("day").is_some() && line.get("hash").is_some())
}

/// **Every frozen fork comparand file, and the key its lines are held by — by a PROPERTY of the
/// file, never a list** (W-43 track C, README gap 4461; the campaign's lesson 2). Until W-43 the
/// history gates named ten files by hand, so a comparand frozen after them (W-43's separator days)
/// would have been held by no plain run. A file of [`fixtures_dir`] named `fork-4748911-*.jsonl`
/// whose every line [`carries_a_fork_day`] is one; its key is the lines' `name` where every line
/// carries one, else [`class_key`] where every line carries a `class` (the classes file, whose lines
/// carry no name). The D21 family — the replay and log-line fixtures `TM_FORK_BLESS` rewrites from
/// the oracle, whose lines carry a `replay` or a verdict and no fork day — is not one, by the same
/// property (README gap 4285). A file that is one and has neither key FAILS: an `Err`, never skipped.
pub fn frozen_files() -> Result<Vec<(String, KeyFn)>, String> {
    let dir = fixtures_dir();
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(|e| e.ok().and_then(|e| e.file_name().into_string().ok()))
        .filter(|n| n.starts_with("fork-4748911-") && n.ends_with(".jsonl"))
        .collect();
    names.sort();
    let mut out: Vec<(String, KeyFn)> = Vec::new();
    for name in names {
        let text = std::fs::read_to_string(dir.join(&name)).map_err(|e| format!("{name}: {e}"))?;
        let lines: Vec<Value> = text
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| serde_json::from_str(l).map_err(|e| format!("{name}: a line that is not JSON ({e})")))
            .collect::<Result<_, _>>()?;
        if lines.is_empty() || !lines.iter().all(carries_a_fork_day) {
            continue;
        }
        let key: KeyFn = if lines.iter().all(|l| l["name"].is_string()) {
            Box::new(key_of("name"))
        } else if lines.iter().all(|l| l["class"].is_string()) {
            Box::new(class_key)
        } else {
            return Err(format!("{name}: a frozen fork comparand whose lines carry neither a `name` nor a `class` to be held by"));
        };
        out.push((name, key));
    }
    Ok(out)
}

/// **The parity numbers a line carries a flag of, and of those the ones SET** — every `p<n>`
/// with a boolean value in an object the line carries beside its world and its days
/// (`forkclass::flag_homes`' reading, which the re-bless gate reads; [`is_answer`] reads the
/// same objects as answers).
pub fn flags(line: &Value) -> (BTreeSet<u32>, BTreeSet<u32>) {
    let (mut all, mut set) = (BTreeSet::new(), BTreeSet::new());
    for (k, v) in line.as_object().into_iter().flatten() {
        if matches!(k.as_str(), "world" | "day" | "shipped" | "whatif") {
            continue;
        }
        for (f, b) in v.as_object().into_iter().flatten() {
            let n = f.strip_prefix('p').filter(|d| !d.is_empty() && d.bytes().all(|c| c.is_ascii_digit())).and_then(|d| d.parse::<u32>().ok());
            if let (Some(n), Some(b)) = (n, b.as_bool()) {
                all.insert(n);
                if b {
                    set.insert(n);
                }
            }
        }
    }
    (all, set)
}

/// **The fields a file's key is made of** — what may move when a line moves to a new key: a
/// `name`-keyed file's `name`; the classes file's class, secondary floor and derivation
/// ([`class_key`]).
pub fn key_fields(line: &Value) -> &'static [&'static str] {
    if line["name"].is_string() {
        &["name"]
    } else {
        &["class", "secondary", "derived"]
    }
}

/// **The lines that left between two versions, paired with the line that holds each one's WORLD
/// in the newer** (W-43 track C, README gap 4320's key-change half): a frozen line's key is a
/// label — the classes file's is its class, which is a FUNCTION of the world through the kernel's
/// reading (`forkclass::class_of`), so a registered number that moves the kernel's reading moves
/// the key (the owner's D87 re-filed two `worked` lines) — and until W-43 a key that left and a key
/// that arrived were two lines to every gate: the old one judged by nothing, the new one a fresh
/// freeze. `(paired, unpaired)`: `paired` is `(old key, new key)` where exactly one ARRIVED line
/// carries the departed line's world byte for byte; `unpaired` is every departed key no arrived
/// line, or more than one, holds the world of, with why — each a finding for the caller to judge
/// ([`left_with_a_redrawn_parent`] says which the owner's D64(b) lets go).
pub fn refiles(old: &BTreeMap<String, Value>, new: &BTreeMap<String, Value>) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let arrived: Vec<&String> = new.keys().filter(|k| !old.contains_key(*k)).collect();
    let (mut paired, mut unpaired) = (Vec::new(), Vec::new());
    for (k, line) in old.iter().filter(|(k, _)| !new.contains_key(*k)) {
        let world = line.get("world").map(|w| serde_json::to_string(w).expect("a value serialises"));
        let twins: Vec<&&String> = arrived
            .iter()
            .filter(|a| world.is_some() && new[a.as_str()].get("world").map(|w| serde_json::to_string(w).expect("a value serialises")) == world)
            .collect();
        match twins.as_slice() {
            [one] => paired.push((k.clone(), (**one).clone())),
            [] => unpaired.push((k.clone(), format!("`{k}` left the file and no line that arrived holds its world"))),
            many => unpaired.push((k.clone(), format!("`{k}` left the file and {} lines that arrived hold its world", many.len()))),
        }
    }
    (paired, unpaired)
}

/// **A derived line that left with its parent re-drawn** — the one deletion a history gate lets
/// through: the classes' re-draw (the owner's D64(b)) drops a derived line its re-drawn parent's rule
/// no longer derives. `k` names a line of `old` carrying a `derived`, and its parent — the primary
/// line of the same `seed` and `draw` — carries a new D64(b) reason in `new` ([`redrawn`]).
pub fn left_with_a_redrawn_parent(k: &str, old: &BTreeMap<String, Value>, new: &BTreeMap<String, Value>) -> bool {
    let Some(line) = old.get(k).filter(|l| !l["derived"].is_null()) else { return false };
    let parent = |m: &BTreeMap<String, Value>| {
        m.values().find(|p| p["secondary"].is_null() && p["derived"].is_null() && p["seed"] == line["seed"] && p["draw"] == line["draw"]).cloned()
    };
    matches!((parent(old), parent(new)), (Some(a), Some(b)) if redrawn(&a, &b))
}

/// **May a line move from `old` to `new`, a new key?** (W-43 track C, README gap 4320.) Held as an
/// in-place line is held ([`shipped_answer`] byte for byte; every key of the world and the
/// provenance byte for byte) but for the fields its key is made of ([`key_fields`]) — and those may
/// move only when `new` carries a SET parity flag of a number `old` carries no flag of at all: the
/// number whose rule moved the kernel's reading, and with it the key (D64(a)'s licence, read off the
/// line as the re-bless gate reads it; the number's registration is `planner_classes.rs`'
/// `every_parity_flag_names_a_registered_number`'s, on every run). `Ok` names the licensing
/// numbers (empty when no key field moved); `Err` says what moved that may not.
pub fn refiled_allows(old: &Value, new: &Value) -> Result<Vec<u32>, String> {
    if shipped_answer(old) != shipped_answer(new) {
        return Err("it moved the SHIPPED fork's answer".to_string());
    }
    let fields = key_fields(old);
    let keys: BTreeSet<&String> = old.as_object().into_iter().flatten().chain(new.as_object().into_iter().flatten()).map(|(k, _)| k).collect();
    let mut key_moved = false;
    for k in keys {
        if is_answer(old, k) || is_answer(new, k) || old[k.as_str()] == new[k.as_str()] {
            continue;
        }
        if fields.contains(&k.as_str()) {
            key_moved = true;
            continue;
        }
        return Err(format!("it moved `{k}`, which is its world or provenance"));
    }
    if !key_moved {
        return Ok(Vec::new());
    }
    let (old_all, _) = flags(old);
    let licence: Vec<u32> = flags(new).1.into_iter().filter(|n| !old_all.contains(n)).collect();
    if licence.is_empty() {
        return Err(format!(
            "its key moved ({}) and it carries no newly set parity flag — a key moves only with the number whose rule moved it",
            fields.join(", ")
        ));
    }
    Ok(licence)
}
