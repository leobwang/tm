//! **A frozen line that moves to a new KEY is held as one line** — stage 6 W-43 track C (README
//! gap 4320's key-change half; gap 4461, the frozen files read by a property).
//!
//! A frozen comparand's key is a label: the classes file's is its class, which is a FUNCTION of the
//! world through the kernel's reading (`forkclass::class_of`), so a registered number that moves the
//! kernel's reading moves the key — the owner's D87 (parity P81) re-filed two `worked` lines,
//! `overtime/home` → `running/home` and `overtime/travel` → `running/travel`, at the W-42 land. Until
//! W-43 every gate read a key that left and a key that arrived as two lines: the old one judged by
//! nothing, the new one a fresh freeze — so a line could be re-keyed by hand with its world, its
//! provenance or its shipped day bent, and no gate would say so.
//!
//! `support/frozenhist.rs` holds the rule, once: [`frozenhist::refiles`] pairs a key that left with
//! the one arrived line that holds its WORLD byte for byte, and [`frozenhist::refiled_allows`] holds
//! the pair as an in-place line is held — the shipped fork's answer and every key of the world and
//! the provenance byte for byte — but for the fields the key is made of, which move only under a
//! newly SET parity flag (the number whose rule moved the reading; the re-bless checks it is
//! registered). The plain run (`fork_rebless_history.rs`' history test, over every frozen file
//! `frozenhist::frozen_files` finds) and the classes' re-bless (`planner_classes.rs`) both ask it.
//! This file is the rule's bite, both ways (AGENTS §5.8), over values and over a repository built
//! here, and the census of the one re-file the tree's history holds.

#[allow(dead_code)]
#[path = "support/frozenhist.rs"]
mod frozenhist;

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

use serde_json::{json, Value};

/// A `worked` class line before the owner's D87 re-filed it.
fn before() -> Value {
    json!({
        "class": "overtime/home", "secondary": "worked", "arm": "w36", "case": "c", "seed": "s", "draw": 1402,
        "derived": {"from": "overtime/home", "now": "2026-09-07T10:00:00-05:00"},
        "world": {"docs": [["week/a.md", "- [ ] 1b x ^zac"]], "log": "", "now": "2026-09-07T10:00:00-05:00"},
        "day": {"hash": "h", "day": {"segments": [1]}},
        "shipped": {"hash": "s", "day": {"segments": [2]}},
        "d57": {"p46": false, "p47": false}, "d60": {"p51": false}, "whatif": null, "p55": {"p55": true},
    })
}

/// The same line under the kernel's new class — re-filed, its world and its answers kept.
fn refiled() -> Value {
    let mut l = before();
    l["class"] = json!("running/home");
    l
}

/// …carrying the flag of the number whose rule moved the reading (P81's answer, as W-43 froze it).
fn licensed() -> Value {
    let mut l = refiled();
    l["p81"] = json!({"p81": true, "hash": "p", "day": {"segments": [3]}});
    l
}

/// **The rule, both ways, over values**: a re-filed line with no newly set flag is refused; with
/// one it is allowed and the number named; a re-file that also moves the shipped day, the world or
/// the provenance is refused whatever it carries; a flag the old line already carried — even unset
/// — licenses nothing, nor does one the new line carries unset; and a `name`-keyed line is held the
/// same way.
#[test]
fn a_line_moved_to_a_new_key_is_held_as_one_line() {
    let old = before();
    assert_eq!(frozenhist::refiled_allows(&old, &old), Ok(Vec::new()), "an unchanged line");
    let e = frozenhist::refiled_allows(&old, &refiled()).expect_err("a class moved by hand, no flag");
    assert!(e.contains("carries no newly set parity flag"), "{e}");
    assert_eq!(frozenhist::refiled_allows(&old, &licensed()), Ok(vec![81]), "a class moved under P81's newly set flag");
    let mut bent = licensed();
    bent["shipped"]["day"] = json!({"segments": [9]});
    assert!(frozenhist::refiled_allows(&old, &bent).is_err_and(|e| e.contains("SHIPPED")), "a re-file that bent the shipped day passed");
    let mut moved = licensed();
    moved["world"]["log"] = json!("{\"ev\":\"start\"}\n");
    assert!(frozenhist::refiled_allows(&old, &moved).is_err_and(|e| e.contains("`world`")), "a re-file that moved the world passed");
    let mut prov = licensed();
    prov["arm"] = json!("w35");
    assert!(frozenhist::refiled_allows(&old, &prov).is_err_and(|e| e.contains("`arm`")), "a re-file that moved the provenance passed");
    let mut held = old.clone();
    held["p81"] = json!({"p81": false});
    let e = frozenhist::refiled_allows(&held, &licensed()).expect_err("a flag the old line carried, unset");
    assert!(e.contains("no newly set parity flag"), "{e}");
    // A flag the NEW line carries UNSET licenses nothing either: the number did not move the reading.
    let mut unset = refiled();
    unset["p81"] = json!({"p81": false, "hash": "p", "day": {"segments": [3]}});
    let e = frozenhist::refiled_allows(&old, &unset).expect_err("a new flag, unset");
    assert!(e.contains("no newly set parity flag"), "a newly carried UNSET flag licensed a re-file: {e}");
    // The comparand's own answers may move beside the key (that is D64's, which a bless asks).
    let mut answers = licensed();
    answers["day"] = json!({"hash": "h2", "day": {"segments": [4]}});
    assert_eq!(frozenhist::refiled_allows(&old, &answers), Ok(vec![81]));
    // A `name`-keyed file: the name is the key's one field.
    let a = json!({"name": "tui At(12, 51)", "class": "idle/lounge", "world": {"now": 1}, "shipped": null, "day": {"day": 1}});
    let mut b = a.clone();
    b["name"] = json!("tui At(12, 52)");
    assert!(frozenhist::refiled_allows(&a, &b).is_err_and(|e| e.contains("(name)")), "a renamed line passed");
    b["p77"] = json!({"p77": true});
    assert_eq!(frozenhist::refiled_allows(&a, &b), Ok(vec![77]));
    let mut c = b.clone();
    c["class"] = json!("running/lounge");
    assert!(frozenhist::refiled_allows(&a, &c).is_err_and(|e| e.contains("`class`")), "a name-keyed line's class is its provenance");
}

/// **The pairing, both ways**: a key that left is paired with the one arrived line holding its world;
/// none, or two, leave it unpaired with why; and a derived line whose parent is re-drawn under
/// D64(b) in the newer version is the one departure a gate lets go.
#[test]
fn a_key_that_left_is_paired_by_its_world() {
    let map = |ls: &[Value]| -> BTreeMap<String, Value> { ls.iter().map(|l| (frozenhist::class_key(l).expect("a key"), l.clone())).collect() };
    let (paired, unpaired) = frozenhist::refiles(&map(&[before()]), &map(&[licensed()]));
    assert_eq!(paired.len(), 1, "{paired:?}");
    assert!(paired[0].0.starts_with("overtime/home") && paired[0].1.starts_with("running/home"));
    assert!(unpaired.is_empty());
    let (paired, unpaired) = frozenhist::refiles(&map(&[before()]), &map(&[]));
    assert!(paired.is_empty() && unpaired.len() == 1 && unpaired[0].1.contains("no line that arrived holds its world"), "{unpaired:?}");
    let mut twin = licensed();
    twin["class"] = json!("running/lounge");
    let (paired, unpaired) = frozenhist::refiles(&map(&[before()]), &map(&[licensed(), twin]));
    assert!(paired.is_empty() && unpaired[0].1.contains("2 lines that arrived hold its world"), "{unpaired:?}");
    // A derived line dropped with its parent re-drawn.
    let parent = json!({"class": "overtime/home", "secondary": null, "derived": null, "seed": "s", "draw": 1402, "world": {"now": 0}});
    let mut redrawn = parent.clone();
    redrawn["world"] = json!({"now": 1});
    redrawn["d64b"] = json!({"why": "2026-10-03 D64(b): a world the binary cannot hold"});
    let old = map(&[parent.clone(), before()]);
    let k = frozenhist::class_key(&before()).expect("a key");
    assert!(frozenhist::left_with_a_redrawn_parent(&k, &old, &map(&[redrawn])), "a derived line dropped with its re-drawn parent was held");
    assert!(!frozenhist::left_with_a_redrawn_parent(&k, &old, &map(&[parent])), "a derived line dropped with its parent unchanged passed");
}

/// `git` in `dir`, with an identity and no signing.
fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["-c", "user.name=w43c", "-c", "user.email=w43c@example.invalid", "-c", "commit.gpgsign=false"])
        .args(args)
        .output()
        .expect("git runs");
    assert!(out.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// **The rule over a repository's history** — the plain run's walk (`frozenhist::versions_since`)
/// over three commits: the line, the line re-filed by hand with no flag (refused), and the line
/// carrying the flag (the re-file from the first version, licensed).
#[test]
fn a_hand_refiled_line_is_refused_and_a_licensed_one_passes_over_history() {
    let dir = tempfile::TempDir::new().expect("a temp dir");
    let d = dir.path();
    git(d, &["init", "-q"]);
    let path = d.join("frozen.jsonl");
    let mut shas = Vec::new();
    for v in [before(), refiled(), licensed()] {
        std::fs::write(&path, format!("{v}\n")).expect("write");
        git(d, &["add", "frozen.jsonl"]);
        git(d, &["commit", "-q", "-m", "a version"]);
        shas.push(git(d, &["rev-parse", "HEAD"]));
    }
    let versions = frozenhist::versions_since(&path, &shas[0], frozenhist::class_key).expect("the history reads");
    assert_eq!(versions.len(), 4, "three commits and the working copy");
    let judge = |old: &BTreeMap<String, Value>, new: &BTreeMap<String, Value>| -> Vec<String> {
        let (paired, unpaired) = frozenhist::refiles(old, new);
        let mut out: Vec<String> = unpaired.into_iter().map(|(_, why)| why).collect();
        for (k, k2) in paired {
            if let Err(e) = frozenhist::refiled_allows(&old[&k], &new[&k2]) {
                out.push(format!("`{k}` → `{k2}`: {e}"));
            }
        }
        out
    };
    let by_hand = judge(&versions[0].1, &versions[1].1);
    assert!(by_hand.len() == 1 && by_hand[0].contains("no newly set parity flag"), "the hand re-file was not refused: {by_hand:?}");
    assert!(judge(&versions[0].1, &versions[2].1).is_empty(), "a re-file carrying its number's flag was refused");
    assert!(judge(&versions[2].1, &versions[3].1).is_empty(), "the working copy, unchanged, was judged");
}

/// **Every frozen fork comparand file is found by its property** (README gap 4461): a
/// `fork-4748911-*.jsonl` whose every line carries a fork day — the twelve planner and grid
/// comparands, W-43's separator days and the W-43 repair's P85 days among them — and none of the D21 family, whose lines carry a
/// replay or a verdict; each held by `name`, but the classes file by its class key.
#[test]
fn every_frozen_comparand_file_is_found_by_its_property() {
    let files = frozenhist::frozen_files().unwrap_or_else(|e| panic!("{e}"));
    let names: Vec<&str> = files.iter().map(|(n, _)| n.as_str()).collect();
    println!("frozen comparand files by their property: {names:?}");
    for want in ["fork-4748911-planner-classes.jsonl", "fork-4748911-planner-separators.jsonl", "fork-4748911-week-grid.jsonl", "fork-4748911-planner-tui.jsonl", "fork-4748911-planner-p85.jsonl"] {
        assert!(names.contains(&want), "{want} is not found by the property");
    }
    for d21 in ["fork-4748911-classes-replay.jsonl", "fork-4748911-corpus-replay.jsonl", "fork-4748911-log-lines.jsonl"] {
        assert!(!names.contains(&d21), "{d21}, a D21 fixture, was taken for a planner comparand");
    }
    // Twelve since the W-43 repair: P85's planner days (README gap 4367) joined the eleven.
    assert_eq!(names.len(), 12, "the property finds {} files: {names:?}", names.len());
    let classes = &files.iter().find(|(n, _)| n == "fork-4748911-planner-classes.jsonl").expect("the classes file").1;
    assert!(classes(&before()).is_some_and(|k| k.starts_with("overtime/home | ")), "the classes file is not held by its class key");
    assert!(!frozenhist::carries_a_fork_day(&json!({"name": "x", "replay": {}})), "a replay line carries a fork day");
}

/// **The tree's one re-file, accounted for** (README gap 4320): every key the classes file's
/// committed history holds that the working copy does not is paired by its world with a line the
/// working copy holds, and that line carries the flag that licenses it — on this tree, W-42's two
/// `worked` lines and P81's flag, which W-43 froze on them.
#[test]
fn the_classes_files_refiled_lines_carry_their_licence() {
    let path = frozenhist::fixtures_dir().join("fork-4748911-planner-classes.jsonl");
    let held = frozenhist::held(&path, frozenhist::class_key).unwrap_or_else(|e| panic!("{e}"));
    let text = std::fs::read_to_string(&path).expect("the classes file");
    let now: BTreeMap<String, Value> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str::<Value>(l).expect("JSON"))
        .map(|v| (frozenhist::class_key(&v).expect("a key"), v))
        .collect();
    let gone: BTreeMap<String, Value> = held.ever.iter().filter(|(k, _)| !now.contains_key(*k)).map(|(k, c)| (k.clone(), c.line.clone())).collect();
    let (paired, unpaired) = frozenhist::refiles(&gone, &now);
    assert!(unpaired.is_empty(), "a committed classes line left with no line holding its world: {unpaired:?}");
    for (k, k2) in &paired {
        let licence = frozenhist::refiled_allows(&gone[k], &now[k2]).unwrap_or_else(|e| panic!("`{k}` → `{k2}`: {e}"));
        println!("`{k}` → `{k2}`: licensed by {licence:?}");
        assert!(licence.contains(&81), "`{k}` → `{k2}` is licensed by {licence:?}, not P81's");
    }
    assert_eq!(paired.len(), 2, "the classes file's history holds {} re-filed line(s): {paired:?}", paired.len());
}
