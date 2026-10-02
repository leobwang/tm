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

use std::collections::BTreeMap;
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
