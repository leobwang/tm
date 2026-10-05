//! **Every bless holds its lines against the COMMITTED history, and the history reader bites**
//! (stage 6 W-42 track C; README gaps 4151, 4280 and 4284).
//!
//! `support/frozenhist.rs` is the one definition of what a bless of a frozen fork comparand holds
//! each line it writes against: the line's latest version at HEAD or at any first-parent commit
//! since `kernel/ratchet.py`'s base — never the working copy, so deleting a file or a line cannot
//! turn a re-bless into a fresh freeze (README gaps 4139 and 4151). This file holds three things:
//!
//! * **the reader, both ways** (AGENTS §5.8), on a repository each test builds for itself: a line
//!   a commit deleted is still held, at its latest committed version; a world git cannot read is
//!   UNCHECKED and an `Err`, never an empty history;
//! * **the reader on the real tree**: every frozen comparand file reads its committed history, and
//!   the base is `ratchet.py`'s;
//! * **the rule as a CLASS** (lesson 2): every bless of a fork comparand in `tm/tests` — a
//!   `#[test]` function that writes a file, reads a `TM_…BLESS…` or `TM_PLANNER_DRAW` variable and
//!   names the fork — calls `frozenhist::held` (or, for a whole-file comparand, `frozenhist::held_text`).
//!   The one family outside it is named by its property, not listed by name: the D21 differential
//!   fixtures `TM_FORK_BLESS` rewrites from the oracle hold no line (each run writes the oracle's
//!   answer over committed inputs, and no line records a departure a gate could license), README gap
//!   4285. A pin of the binary's OWN bytes (`tm log`'s, `TM_LOG_BLESS`) names no fork and is a
//!   snapshot, which is never re-blessed: not a bless here.
//! * **and since W-45 track C (README gap 4680) the rule that keeps every comparand re-blessable
//!   after R3, as a CLASS too**: no bless sits inside a `BEGIN THE FORK PLANNER` region (R3 deleted
//!   the region, and a bless there makes its file final — README gap 4463 found six), every frozen
//!   comparand file `frozenhist::frozen_files` finds is named by a bless outside every region, and
//!   every test file that reads a committed snapshot as a frozen answer holds such a bless. Until
//!   W-45 this file asked for twelve blesses BY NAME, seven of them inside regions, so it went red
//!   the moment R3 deleted them (W-44's simulation): a LIST where the rule is a CLASS.

#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

use std::path::Path;
use std::process::Command;

use serde_json::json;

/// `git` in `dir`, with an identity and no signing, so a test's own repository commits anywhere.
fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["-c", "user.name=w42c", "-c", "user.email=w42c@example.invalid", "-c", "commit.gpgsign=false"])
        .args(args)
        .output()
        .expect("git runs");
    assert!(out.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// A repository with `frozen.jsonl` committed as each of `versions` in turn (`None`: deleted),
/// the first commit the base. The directory, the file's path and every commit, oldest first.
fn repo(versions: &[Option<&[serde_json::Value]>]) -> (tempfile::TempDir, std::path::PathBuf, Vec<String>) {
    let dir = tempfile::TempDir::new().expect("a temp dir");
    git(dir.path(), &["init", "-q"]);
    let path = dir.path().join("frozen.jsonl");
    let mut shas = Vec::new();
    for (i, v) in versions.iter().enumerate() {
        match v {
            Some(lines) => {
                let text: String = lines.iter().map(|l| format!("{l}\n")).collect();
                std::fs::write(&path, text).expect("write");
                git(dir.path(), &["add", "frozen.jsonl"]);
            }
            None => {
                git(dir.path(), &["rm", "-q", "frozen.jsonl"]);
            }
        }
        git(dir.path(), &["commit", "-q", "--allow-empty", "-m", &format!("version {i}")]);
        shas.push(git(dir.path(), &["rev-parse", "HEAD"]));
    }
    (dir, path, shas)
}

/// **A line a commit deleted is still held, at its latest committed version** — and the file a
/// later commit deleted outright is held whole: the two ways a re-bless used to become a fresh
/// freeze (README gaps 4139, 4151).
#[test]
fn a_line_a_commit_deleted_is_still_held_at_its_latest_version() {
    let a1 = json!({"name": "a", "v": 1});
    let a2 = json!({"name": "a", "v": 2});
    let b1 = json!({"name": "b", "v": 1});
    let (_dir, path, shas) = repo(&[Some(&[a1.clone(), b1.clone()]), Some(&[a2.clone()]), None]);
    let held = frozenhist::held_since(&path, &shas[0], frozenhist::key_of("name")).expect("the history reads");
    assert!(held.head.is_empty(), "HEAD holds no file");
    assert_eq!(held.get("a"), Some(&a2), "a is held at its LATEST committed version");
    assert_eq!(held.ever["a"].sha, shas[1], "…which the second commit holds");
    assert_eq!(held.get("b"), Some(&b1), "b, deleted by the second commit, is still held");
    assert_eq!(held.only_in_history(), vec!["a", "b"]);
    assert!(held.census("frozen.jsonl").contains("held against 2 committed line(s) from 3 version(s)") && held.census("x").contains("0 at HEAD, 2 only in history"), "{}", held.census("frozen.jsonl"));
    assert_eq!(held.versions.iter().map(|(s, n)| (s.as_str(), *n)).collect::<Vec<_>>(), vec![(shas[0].as_str(), 2), (shas[1].as_str(), 1), (shas[2].as_str(), 0)]);
    // And a working copy that brings the file back with one line changed is not what is held.
    std::fs::write(&path, format!("{}\n", json!({"name": "a", "v": 99}))).expect("write");
    let again = frozenhist::held_since(&path, &shas[0], frozenhist::key_of("name")).expect("the history reads");
    assert_eq!(again.get("a"), Some(&a2), "the working copy is never what a bless holds");
}

/// **During a merge, a line the incoming commit holds is held** (README gap 4286) — the window W-41's
/// land froze the TUI file fresh in: the first-parent side holds no file, the branch being merged
/// does, and the working copy's file is gone. The incoming line is what a bless is held to.
#[test]
fn a_line_the_merge_brings_is_held_while_the_merge_is_in_progress() {
    let dir = tempfile::TempDir::new().expect("a temp dir");
    let d = dir.path();
    git(d, &["init", "-q", "-b", "line"]);
    git(d, &["commit", "-q", "--allow-empty", "-m", "base"]);
    let base = git(d, &["rev-parse", "HEAD"]);
    git(d, &["checkout", "-q", "-b", "track"]);
    let path = d.join("frozen.jsonl");
    let h = json!({"name": "tui AfterMidnight(1, 0)", "p55": {"p55": true}});
    std::fs::write(&path, format!("{h}\n")).expect("write");
    git(d, &["add", "frozen.jsonl"]);
    git(d, &["commit", "-q", "-m", "the track's line"]);
    let track = git(d, &["rev-parse", "HEAD"]);
    git(d, &["checkout", "-q", "line"]);
    git(d, &["commit", "-q", "--allow-empty", "-m", "the line moves on"]);
    let before = frozenhist::held_since(&path, &base, frozenhist::key_of("name")).expect("the history reads");
    assert!(before.ever.is_empty() && frozenhist::merge_heads(d).is_empty(), "no merge, no file on the line");
    git(d, &["merge", "-q", "--no-commit", "--no-ff", "track"]);
    assert_eq!(frozenhist::merge_heads(d), vec![track.clone()]);
    std::fs::remove_file(&path).expect("the working copy's file deleted, as W-41's land did");
    let during = frozenhist::held_since(&path, &base, frozenhist::key_of("name")).expect("the history reads");
    assert_eq!(during.get("tui AfterMidnight(1, 0)"), Some(&h), "the incoming line is not held");
    assert_eq!(during.ever["tui AfterMidnight(1, 0)"].sha, track);
    assert!(during.head.is_empty(), "HEAD — the first parent — holds no file");
}

/// **What git cannot read is UNCHECKED, and an `Err` — never an empty history** (AGENTS §5.8, the
/// other direction): a directory outside any repository; a base that is not an ancestor of HEAD; a
/// committed version that holds two lines of one key, or a line with none.
#[test]
fn what_git_cannot_read_is_unchecked() {
    let bare = tempfile::TempDir::new().expect("a temp dir");
    let outside = bare.path().join("frozen.jsonl");
    std::fs::write(&outside, "{\"name\":\"a\"}\n").expect("write");
    let e = frozenhist::held_since(&outside, "17a13c234547a409a352d1ac15d2d62d2110f01c", frozenhist::key_of("name")).expect_err("no repository");
    assert!(e.starts_with("UNCHECKED"), "{e}");
    let a = json!({"name": "a"});
    let (_dir, path, shas) = repo(&[Some(&[a.clone()])]);
    let e = frozenhist::held_since(&path, &"0".repeat(40), frozenhist::key_of("name")).expect_err("a base that is no ancestor");
    assert!(e.starts_with("UNCHECKED") && e.contains("not an ancestor"), "{e}");
    let (_dir2, path2, shas2) = repo(&[Some(&[a.clone(), a.clone()])]);
    let e = frozenhist::held_since(&path2, &shas2[0], frozenhist::key_of("name")).expect_err("two lines of one key");
    assert!(e.contains("two lines") && e.contains(&shas2[0]), "{e}");
    let (_dir3, path3, shas3) = repo(&[Some(&[json!({"other": 1})])]);
    let e = frozenhist::held_since(&path3, &shas3[0], frozenhist::key_of("name")).expect_err("a line with no key");
    assert!(e.contains("no key"), "{e}");
    assert!(frozenhist::held_since(&path, &shas[0], frozenhist::key_of("name")).is_ok(), "the well-formed history reads");
}

/// **The base is `kernel/ratchet.py`'s, read from that file** — one home (the owner's D88 moved it
/// there, to `17a13c2`), and `base_of` takes exactly a column-zero forty-digit sha.
#[test]
fn the_base_is_the_ratchets() {
    let text = std::fs::read_to_string(frozenhist::ratchet_path()).expect("kernel/ratchet.py");
    let base = frozenhist::base().expect("the base reads");
    assert!(text.contains(&format!("BASE = \"{base}\"")), "{base}");
    assert!(base.starts_with("17a13c2"), "D88's base: {base}");
    assert_eq!(frozenhist::base_of("BASE = \"abc\"\n"), None, "a short sha is not a base");
    assert_eq!(frozenhist::base_of("    BASE = \"17a13c234547a409a352d1ac15d2d62d2110f01c\"\n"), None, "an indented one is not the module's");
}

/// **Every frozen planner and grid comparand reads its committed history on this tree** — the
/// reader every bless calls, over each file and its bless's key: the base is an ancestor of HEAD,
/// every committed version parses, and HEAD holds at least one line. Printed: the census.
#[test]
fn every_frozen_comparand_reads_its_committed_history() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    // **Every frozen file, by a property** (W-43 track C, README gap 4461): until W-43 this named
    // ten files by hand, so a comparand frozen after them was held by nothing here.
    let files = frozenhist::frozen_files().unwrap_or_else(|e| panic!("{e}"));
    assert!(files.len() >= 11, "the property finds {} frozen comparand files", files.len());
    for (name, key) in files {
        let held = frozenhist::held(&fixtures.join(&name), key).unwrap_or_else(|e| panic!("{e}"));
        // A file no committed version holds yet is one the working copy introduces (the commit that
        // carries it gives it a history); one HEAD dropped while a committed version held lines is not.
        assert!(!held.head.is_empty() || held.ever.is_empty(), "{name}: HEAD holds no line and a committed version did");
        println!("{}", held.census(&name));
    }
}

/// **Every committed frozen line kept its world and the shipped fork's answer, in a PLAIN run**
/// (the W-42 repair, README gap 4341; W-42's reuse critic). Every bless holds its lines against
/// the committed history (`frozenhist::held`) — but only INSIDE a bless, and R3 deleted eight of
/// the eleven blesses with the fork regions they live in (planner-classes, -batch, -driven,
/// -basic-days, the classes' re-draw, -days, -conference, -p56). After it a frozen line can change
/// only by hand, and nothing in `cargo test` compared a committed line with its history: this test
/// asserted the history READ and printed its census.
///
/// It holds, with no fork planner, the two halves of the owner's D64 that need none, over every
/// first-parent commit since `ratchet.py`'s base and the working copy: for every key two
/// consecutive versions both hold, (1) **the shipped fork's answer** (`frozenhist::shipped_answer`)
/// and (2) **every key of the world and the provenance** (all but `frozenhist::is_answer`'s) are
/// byte-identical — unless the newer version is a D64(b) re-draw (`frozenhist::redrawn`), whose
/// world moved and whose fork was asked again. So a hand-moved world, class, test list or shipped
/// day fails a plain run on the commit that moved it. And since W-43 track C (README gap 4320) a
/// key that LEAVES the file is judged too: paired with the arrived line that holds its world
/// (`frozenhist::refiles`), it is held as one line moving, its key's own fields licensed only by a
/// newly set parity flag (`frozenhist::refiled_allows`); a key that leaves with no such twin is a
/// finding. WHAT IT CANNOT SEE, declared: a comparand answer moved with the shipped day held (that
/// is D64(a)/(c)'s to license, and only a bless knows its reason), and a line deleted with its world
/// re-used by another line in the same commit (the pair is then judged as a re-file).
#[test]
fn every_committed_frozen_line_kept_its_world_and_the_shipped_answer() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    // **Every frozen file, by a property** (W-43 track C, README gap 4461): until W-43 this named
    // ten files by hand, so a comparand frozen after them was held by nothing here.
    let files = frozenhist::frozen_files().unwrap_or_else(|e| panic!("{e}"));
    assert!(files.len() >= 11, "the property finds {} frozen comparand files", files.len());
    // **From the commit that brought this check in, never before it** — a property of the
    // history, not a sha written here: the first first-parent commit since the base whose
    // `tm/tests/fork_rebless_history.rs` holds this function (`HEAD` until that commit exists, so
    // the working copy is held against HEAD).  A check cannot judge the commits before it: the
    // W-41 land re-derived the week grid's worlds and steps under no reason a plain run can read
    // (`17a13c2..69de2de`, 42 changes), and they are counted, never judged.
    let me = "fn every_committed_frozen_line_kept_its_world_and_the_shipped_answer";
    let this = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fork_rebless_history.rs");
    let holds_me = |rev: &str| frozenhist::show(&this, rev).is_some_and(|t| t.contains(me));
    let mut pairs = 0usize;
    let mut before = 0usize;
    let mut moved = Vec::new();
    let mut refiled = 0usize;
    for (name, key) in files {
        let versions = frozenhist::versions(&fixtures.join(&name), key).unwrap_or_else(|e| panic!("{e}"));
        let commits = versions.len() - 1;
        let from = (0..commits).find(|i| holds_me(&versions[*i].0)).unwrap_or(commits - 1);
        for (i, w) in versions.windows(2).enumerate() {
            let ((was, old), (now, new)) = (&w[0], &w[1]);
            let judged = i >= from;
            // **A line that moved to a new KEY is held as one line** (W-43 track C, README gap 4320):
            // paired with the arrived line that holds its world, it is held as an in-place line is,
            // but for the fields its key is made of, which move only under a newly set parity flag
            // (`frozenhist::refiled_allows`); a line that left with no such twin is a finding.
            let tag2 = |what: String| format!("{name}: {what} between {} and {}", &was[..was.len().min(9)], &now[..now.len().min(9)]);
            let (paired, unpaired) = frozenhist::refiles(old, new);
            let mut found: Vec<String> =
                unpaired.into_iter().filter(|(k, _)| !frozenhist::left_with_a_redrawn_parent(k, old, new)).map(|(_, why)| tag2(why)).collect();
            for (k, k2) in &paired {
                pairs += 1;
                refiled += 1;
                if let Err(e) = frozenhist::refiled_allows(&old[k], &new[k2]) {
                    found.push(tag2(format!("`{k}` moved to `{k2}`: {e}")));
                }
            }
            if judged {
                moved.extend(found);
            } else {
                before += found.len();
            }
            for (k, a) in old {
                let Some(b) = new.get(k) else { continue };
                pairs += 1;
                if frozenhist::redrawn(a, b) {
                    continue;
                }
                let tag = |what: &str| format!("{name}: `{k}` {what} between {} and {}", &was[..was.len().min(9)], &now[..now.len().min(9)]);
                let mut found = Vec::new();
                if frozenhist::shipped_answer(a) != frozenhist::shipped_answer(b) {
                    found.push(tag("moved the SHIPPED fork's answer"));
                }
                let keys: std::collections::BTreeSet<&String> =
                    a.as_object().into_iter().flatten().chain(b.as_object().into_iter().flatten()).map(|(k, _)| k).collect();
                for f in keys {
                    if !frozenhist::is_answer(a, f) && !frozenhist::is_answer(b, f) && a[f.as_str()] != b[f.as_str()] {
                        found.push(tag(&format!("moved `{f}`, which is its world or provenance")));
                    }
                }
                if judged {
                    moved.extend(found);
                } else {
                    before += found.len();
                }
            }
        }
    }
    assert!(pairs > 0, "no line was held by two versions — the history compared nothing");
    assert!(moved.is_empty(), "{} change(s) no clause of D64 that needs no fork licenses:\n{}", moved.len(), moved.join("\n"));
    println!(
        "held {pairs} line-version pair(s) across every frozen file's history and the working copy ({refiled} of them a \
         line moved to a new key); {before} change(s) before this check landed, counted and not judged"
    );
}

/// **The plain history check bites** (AGENTS §5.8): over a synthetic repository, a line whose
/// `class` moved, whose shipped day moved, or whose world moved without a re-draw's reason is
/// caught by the same three readers; a comparand answer moving, an introduced `p<n>` answer and a
/// D64(b) re-draw are not.
#[test]
fn the_plain_history_check_bites_and_does_not_over_bite() {
    let line = json!({"name": "a", "class": "c", "tests": ["t"], "world": {"now": 1}, "day": {"day": "d", "hash": "h"},
                      "shipped": null, "d57": {"p46": false}, "whatif": null});
    assert_eq!(frozenhist::shipped_answer(&line), json!("d"));
    for k in ["day", "shipped", "whatif", "d57", "p69"] {
        assert!(frozenhist::is_answer(&line, k) || k == "p69", "{k}");
    }
    assert!(frozenhist::is_answer(&json!({}), "p69"), "a key named by a parity number is an answer");
    for k in ["name", "class", "tests", "world"] {
        assert!(!frozenhist::is_answer(&line, k), "{k} is provenance");
    }
    let mut class = line.clone();
    class["class"] = json!("planted/class");
    assert!(!frozenhist::is_answer(&class, "class") && class["class"] != line["class"], "a moved class is caught");
    let mut ship = line.clone();
    ship["day"]["day"] = json!("bent");
    assert_ne!(frozenhist::shipped_answer(&ship), frozenhist::shipped_answer(&line), "a bent shipped day is caught");
    let mut departs = ship.clone();
    departs["shipped"] = json!({"day": "d"});
    assert_eq!(frozenhist::shipped_answer(&departs), frozenhist::shipped_answer(&line), "a comparand departing with the shipped day kept passes");
    let mut redraw = line.clone();
    redraw["world"] = json!({"now": 2});
    assert!(!frozenhist::redrawn(&line, &redraw), "a moved world with no reason is no re-draw");
    redraw["d64b"] = json!("2026-10-03 D64(b): a world the binary cannot hold");
    assert!(frozenhist::redrawn(&line, &redraw), "a dated D64(b) reason is a re-draw");
    let grid = json!({"name": "g", "fork": {"heat": [1]}, "p63": [], "world": 1});
    assert_eq!(frozenhist::shipped_answer(&grid), json!({"heat": [1]}));
    let days = json!({"name": "d", "day": {"date": "x"}, "hash": "h", "now": 1});
    assert_eq!(frozenhist::shipped_answer(&days), json!([{"date": "x"}, "h"]));
}

/// One `#[test]` function of a test file: its name and its code, comments stripped. Its braces
/// are counted on the code with every string literal blanked ([`blank_literals`], over the whole
/// file, so a literal continued across lines is still one literal).
fn test_fns(text: &str) -> Vec<(String, String)> {
    if text.is_empty() {
        return Vec::new();
    }
    let lines: Vec<String> = srcwalk::code_lines(text).into_iter().map(|(_, c)| c).collect();
    let blank: Vec<String> = blank_literals(&lines.join("\n")).split('\n').map(str::to_string).collect();
    assert_eq!(blank.len(), lines.len(), "blanking keeps the lines");
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if blank[i].trim() != "#[test]" {
            i += 1;
            continue;
        }
        let Some(f) = (i..lines.len()).find(|j| blank[*j].contains("fn ")) else { break };
        let name = blank[f].split("fn ").nth(1).and_then(|r| r.split('(').next()).unwrap_or_default().trim().to_string();
        let (mut depth, mut opened, mut end) = (0i64, false, f);
        for (j, l) in blank.iter().enumerate().skip(f) {
            depth += l.matches('{').count() as i64 - l.matches('}').count() as i64;
            opened |= l.contains('{');
            if opened && depth <= 0 {
                end = j;
                break;
            }
        }
        out.push((name, lines[f..=end].join("\n")));
        i = end + 1;
    }
    out
}

/// **A bless of a FORK comparand, by its shape**: it writes a file, it reads a variable whose name
/// is a bless's — `TM_` and `BLESS` in one literal, or the class lines' re-draw, `TM_PLANNER_DRAW` —
/// and what it writes is the fork's: its code names a fork-side helper (an identifier that begins
/// `fork` and continues as a name or a path, `forkclass::`, `forkplan::`, or fork_conference_day as the
/// conference file's region declared it until R3…).
/// A bless of the binary's OWN bytes — `cli_switch_acceptance`'s `tm log` pin, `TM_LOG_BLESS` — is
/// a snapshot, which is never re-blessed against a committed answer, and names no fork.
fn is_bless(body: &str) -> bool {
    let code = blank_literals(body);
    let reads = body.split('"').skip(1).step_by(2).any(|lit| (lit.starts_with("TM_") && lit.contains("BLESS")) || lit == "TM_PLANNER_DRAW");
    code.contains("fs::write(") && reads && names_the_fork(&code)
}

/// Does the code — string literals blanked — call the history reader: `frozenhist::held` for a
/// file of lines, or `frozenhist::held_text` for a whole-file comparand (W-45 track C, README gap
/// 4680: `emit_planner.rs`' renderings)?
fn holds_history(body: &str) -> bool {
    let code = blank_literals(body);
    code.contains("frozenhist::held(") || code.contains("frozenhist::held_text(")
}

/// **A test file's text, split at its fork region**: `(outside, region)` — the text before the
/// line-start `// BEGIN THE FORK PLANNER` banner and after the line-start `// END THE FORK PLANNER`
/// banner, and the text between them (`""` where the file holds no region). One banner without the
/// other is the region guard's to refuse (`forkday::fork_scan`); here it reads as no region.
fn split_at_region(text: &str) -> (String, String) {
    let at = |needle: &str| text.match_indices(needle).map(|(i, _)| i).find(|&i| i == 0 || text.as_bytes()[i - 1] == b'\n');
    match (at("// BEGIN THE FORK PLANNER"), at("// END THE FORK PLANNER")) {
        (Some(i), Some(j)) if i < j => (format!("{}{}", &text[..i], &text[j..]), text[i..j].to_string()),
        _ => (text.to_string(), String::new()),
    }
}

/// **The `const`s that name a frozen comparand file in code**: every `const NAME: &str =
/// "fork-4748911-…"` the test tree declares, as `(declaring file, module, NAME, value)` — a bless names
/// the file by its literal name, by its module-qualified name, or by the bare name in the file that declares it
/// ([`names_file`]).
fn file_consts(files: &[(String, String)]) -> Vec<(String, String, String, String)> {
    let mut out = Vec::new();
    for (label, text) in files {
        let path = std::path::Path::new(label);
        let stem = path.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
        let module = if stem == "mod" {
            path.parent().and_then(|d| d.file_name()).map(|d| d.to_string_lossy().to_string()).unwrap_or_default()
        } else {
            stem
        };
        for line in text.lines() {
            let l = line.trim_start();
            let l = l.strip_prefix("pub ").unwrap_or(l);
            let Some(rest) = l.strip_prefix("const ") else { continue };
            let Some((name, value)) = rest.split_once(": &str = \"") else { continue };
            let Some(value) = value.strip_suffix("\";") else { continue };
            if value.starts_with("fork-4748911-") {
                out.push((label.clone(), module.clone(), name.trim().to_string(), value.to_string()));
            }
        }
    }
    out
}

/// Does the bless `body`, in the file `label`, name the frozen file `file`?
fn names_file(body: &str, label: &str, file: &str, consts: &[(String, String, String, String)]) -> bool {
    let code = blank_literals(body);
    body.contains(file)
        || consts.iter().any(|(declared_in, module, name, value)| {
            value == file && (is_word_in(&code, &format!("{module}::{name}")) || (declared_in == label && is_word_in(&code, name)))
        })
}

/// Whether `word` occurs in `code` as a whole identifier.
fn is_word_in(code: &str, word: &str) -> bool {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    code.match_indices(word).any(|(i, _)| {
        !code[..i].chars().next_back().is_some_and(|c| ident(c) || c == ':') && !code[i + word.len()..].chars().next().is_some_and(ident)
    })
}

/// The code with every string literal's contents blanked (its quotes kept), so a call spelled
/// inside a literal — a test's own example source — is not read as a call.
fn blank_literals(code: &str) -> String {
    let cs: Vec<char> = code.chars().collect();
    let (mut out, mut in_str, mut escaped) = (String::new(), false, false);
    for (i, &c) in cs.iter().enumerate() {
        let char_literal = !in_str && c == '"' && i > 0 && cs[i - 1] == '\'' && cs.get(i + 1) == Some(&'\'');
        if in_str && escaped {
            escaped = false;
            out.push(if c == '\n' { c } else { ' ' });
        } else if in_str && c == '\\' {
            escaped = true;
            out.push(' ');
        } else if c == '"' && !char_literal {
            in_str = !in_str;
            out.push(c);
        } else {
            out.push(if in_str && c != '\n' { ' ' } else { c });
        }
    }
    out
}

/// Does the code name a fork-side helper — `fork` at the start of an identifier, followed by a name
/// character or a path separator?
fn names_the_fork(body: &str) -> bool {
    body.match_indices("fork").any(|(i, _)| {
        let before = body[..i].chars().next_back();
        let after = &body[i + 4..];
        !before.is_some_and(|c| c.is_alphanumeric() || c == '_') && (after.starts_with("::") || after.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
    })
}

/// **The D21 family, by its property**: a bless whose only bless variable is `TM_FORK_BLESS`
/// rewrites the replay and log-line fixtures from the oracle over committed inputs — it holds no
/// line and none records a departure, so there is nothing a committed version could be held to
/// (README gap 4285 records it, and what it would take to hold them).
fn is_d21(body: &str) -> bool {
    let vars: Vec<&str> = body.split('"').skip(1).step_by(2).filter(|lit| lit.starts_with("TM_") && lit.contains("BLESS")).collect();
    !vars.is_empty() && vars.iter().all(|v| *v == "TM_FORK_BLESS")
}

/// **Every bless of a frozen fork comparand holds its lines against the committed history, sits
/// outside every fork region, and every frozen comparand has one** — README gap 4151 as a CLASS
/// (lesson 2), and since W-45 track C (README gap 4680) the rule that no comparand is final at R3:
///
/// 1. every bless-shaped `#[test]` in `tm/tests` calls the history reader (`frozenhist::held`, or
///    `frozenhist::held_text` for a whole file), but the D21 family named by its property;
/// 2. **no bless sits inside a `BEGIN THE FORK PLANNER` region** — R3 deleted the region, so a bless
///    there makes its file final (README gap 4463's six, and the class worlds' re-draw);
/// 3. **every frozen comparand file** (`frozenhist::frozen_files`, a property of the fixtures
///    directory) **is named by a bless outside every region** — by its name, or by a `const` whose
///    value it is (`file_consts`) — **and every test file that reads a committed snapshot as a frozen
///    answer** (its code spells `tests/snapshots/`) **holds a bless outside its region**.
///
/// So the gate is green while the fork's regions stand and once R3 has deleted them, and the switch
/// has nothing in it to rewrite. Until W-45 clause 3 was a list of twelve names, seven of them inside
/// regions, and the gate went red at R3's simulated deletion (W-44 track C §6). The census is printed.
#[test]
fn every_bless_holds_its_lines_against_the_committed_history() {
    let tests: Vec<(String, String)> = srcwalk::every_rust_file().into_iter().filter(|(label, _)| label.starts_with("tm/tests/")).collect();
    let consts = file_consts(&tests);
    let mut found: Vec<(String, String)> = Vec::new();
    let mut d21 = Vec::new();
    let mut bad = Vec::new();
    for (label, text) in &tests {
        let (outside, region) = split_at_region(text);
        for (name, body) in test_fns(&region) {
            if is_bless(&body) {
                bad.push(format!("{label}::{name} sits inside a fork region: R3 deleted the regions, and its file is final after R3 (README gap 4680)"));
            }
        }
        for (name, body) in test_fns(&outside) {
            if !is_bless(&body) {
                continue;
            }
            if is_d21(&body) {
                d21.push(format!("{label}::{name}"));
            } else if holds_history(&body) {
                found.push((format!("{label}::{name}"), body));
            } else {
                bad.push(format!("{label}::{name} holds its lines against the working copy, or against nothing (README gap 4151)"));
            }
        }
        // A committed snapshot read as a frozen answer (`emit_planner.rs`' renderings): its file holds a
        // bless. The path is spelled in pieces here so this file's own code does not read as a reader.
        let snapshots = ["tests/", "snapshots/"].concat();
        if srcwalk::code_lines(&outside).iter().any(|(_, c)| c.contains(&snapshots)) {
            let here: Vec<&String> = found.iter().filter(|(n, _)| n.starts_with(&format!("{label}::"))).map(|(n, _)| n).collect();
            if here.is_empty() {
                bad.push(format!("{label} reads a committed snapshot as a frozen answer and holds no bless outside its region (README gap 4680)"));
            }
        }
    }
    let files = frozenhist::frozen_files().unwrap_or_else(|e| panic!("{e}"));
    for (file, _) in &files {
        let by: Vec<&String> = found.iter().filter(|(n, body)| names_file(body, n.split("::").next().unwrap_or_default(), file, &consts)).map(|(n, _)| n).collect();
        if by.is_empty() {
            bad.push(format!("{file}: no bless outside a fork region names it, so R3 would leave it final (README gap 4680)"));
        }
        println!("{file}: blessed by {by:?}");
    }
    println!("blesses holding the committed history ({}):\n  {}", found.len(), found.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join("\n  "));
    println!("the D21 family, holding no line ({}):\n  {}", d21.len(), d21.join("\n  "));
    assert!(bad.is_empty(), "{} bless finding(s):\n  {}", bad.len(), bad.join("\n  "));
    assert!(files.len() >= 11 && found.len() >= files.len(), "{} bless(es) found for {} frozen file(s) — the walk is not reading what it claims", found.len(), files.len());
    assert!(d21.len() >= 2, "the D21 family was not found: {d21:?}");
}

/// **Clause 2 and 3 of the gate bite, and do not over-bite** (AGENTS §5.8; W-45 track C, README gap
/// 4680): a bless inside a region is seen there and nowhere else; a file split at its banners keeps
/// both sides; a frozen file named by a `const` in another module, by the bare `const` in its own
/// file, or by its literal name is named, and one named by none — or by a same-named `const` of
/// another value — is not.
#[test]
fn the_region_and_naming_clauses_bite() {
    let b = ["// BEGIN THE FORK", " PLANNER\n"].concat();
    let e = ["// END THE FORK", " PLANNER\n"].concat();
    let bless = "#[test]\nfn x() {\n    if std::env::var_os(\"TM_X_BLESS\").is_none() { return; }\n    let held = frozenhist::held(&p, k); let day = forkplan::plan();\n    std::fs::write(p, out).expect(\"w\");\n}\n";
    let text = format!("fn a() {{}}\n{b}{bless}{e}fn z() {{}}\n");
    let (outside, region) = split_at_region(&text);
    assert!(test_fns(&region).iter().any(|(n, body)| n == "x" && is_bless(body)), "a bless inside the region was not seen there");
    assert!(test_fns(&outside).is_empty() && outside.contains("fn a()") && outside.contains("fn z()"), "the split lost a side: {outside:?}");
    let (whole, none) = split_at_region(bless);
    assert!(none.is_empty() && whole == bless, "a file with no region is all outside");
    let tests = vec![
        ("tm/tests/support/forkx.rs".to_string(), "pub const FROZEN_X: &str = \"fork-4748911-planner-x.jsonl\";\n".to_string()),
        ("tm/tests/other.rs".to_string(), "const FROZEN_X: &str = \"fork-4748911-planner-y.jsonl\";\nconst FROZEN_Z: &str = \"fork-4748911-planner-z.jsonl\";\n".to_string()),
    ];
    let consts = file_consts(&tests);
    let file = "fork-4748911-planner-x.jsonl";
    assert!(names_file("eprintln!(\"{}\", forkx::FROZEN_X);", "tm/tests/a.rs", file, &consts), "a `module::NAME` spelling was not read");
    assert!(names_file("let p = \"fork-4748911-planner-x.jsonl\";", "tm/tests/a.rs", file, &consts), "the literal name was not read");
    assert!(names_file("w(FROZEN_Z)", "tm/tests/other.rs", "fork-4748911-planner-z.jsonl", &consts), "a bare `NAME` in its own file was not read");
    assert!(!names_file("w(FROZEN_X)", "tm/tests/other.rs", file, &consts), "another value's same-named `const` named the file");
    assert!(!names_file("w(FROZEN_Z)", "tm/tests/a.rs", "fork-4748911-planner-z.jsonl", &consts), "a bare `NAME` outside its file named the file");
    assert!(!names_file("let x = forkx::FROZEN_XY;", "tm/tests/a.rs", file, &consts), "a longer name was read as the `const`");
    assert!(holds_history("let h = frozenhist::held_text(&p);") && !holds_history("let h = \"frozenhist::held_text(\";"), "the whole-file reader is not read as a history reader, or a literal is");
}

/// **The class test bites** (AGENTS §5.8): a bless-shaped function that reads its held lines off the
/// working copy is a bless the rule refuses; one that calls the reader is not; one that writes no
/// file, or reads no bless variable, is no bless; and the D21 family is told apart by its variable.
#[test]
fn the_class_test_tells_a_bless_by_its_shape() {
    let working_copy = "#[test]\nfn x() {\n    if std::env::var_os(\"TM_X_BLESS\").is_none() { return; }\n    let held = read(); let day = forkplan::plan();\n    std::fs::write(p, out).expect(\"w\");\n}\n";
    let fns = test_fns(working_copy);
    assert_eq!(fns.len(), 1);
    assert!(is_bless(&fns[0].1) && !holds_history(&fns[0].1) && !is_d21(&fns[0].1), "a working-copy bless was not caught");
    let history = working_copy.replace("let held = read();", "let held = frozenhist::held(&p, k);");
    assert!(holds_history(&test_fns(&history)[0].1));
    assert_eq!(blank_literals("a(\"x\\\"y\", '\"', \"z\")"), "a(\"    \", '\"', \" \")", "an escaped quote or a quote char ended a literal");
    assert_eq!(blank_literals("f(\"a \\\n b\")\n}").lines().count(), 3, "a literal continued across a line lost the line");
    let spelled = working_copy.replace("let held = read();", "let held = \"frozenhist::held(\";");
    assert!(is_bless(&test_fns(&spelled)[0].1) && !holds_history(&test_fns(&spelled)[0].1), "a call spelled inside a literal passed as a call");
    let no_write = working_copy.replace("std::fs::write(p, out)", "drop(out)");
    assert!(!is_bless(&test_fns(&no_write)[0].1), "a function that writes nothing is no bless");
    let no_var = working_copy.replace("TM_X_BLESS", "TM_X");
    assert!(!is_bless(&test_fns(&no_var)[0].1), "a function that reads no bless variable is no bless");
    let own_bytes = working_copy.replace("let day = forkplan::plan();", "let day = measured();");
    assert!(!is_bless(&test_fns(&own_bytes)[0].1), "a pin of the binary's own bytes, naming no fork, is no fork bless");
    assert!(!names_the_fork("let s = \"the fork plans\"; let x = unfork::y();"), "prose, or a name that only contains it, names no fork");
    let d21 = working_copy.replace("TM_X_BLESS", "TM_FORK_BLESS");
    assert!(is_bless(&test_fns(&d21)[0].1) && is_d21(&test_fns(&d21)[0].1), "the D21 family is not told apart");
    let both = d21.replace("let held = read();", "let b = std::env::var(\"TM_Y_BLESS\");");
    assert!(!is_d21(&test_fns(&both)[0].1), "a bless reading another bless variable beside TM_FORK_BLESS passed as D21");
    let braces = working_copy.replace("let held = read();", "let held = \"}\"; let n = json!({\"a\": {}});");
    assert_eq!(test_fns(&braces)[0].1.lines().count(), working_copy.lines().count() - 1, "a brace inside a literal ended the body");
}
