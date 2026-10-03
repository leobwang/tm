//! CLI conformance: `--help` versus the runtime (AGENTS.md §8.1 scope item
//! 7; the third row of PLAN-lean-kernel.md §4's integration-bug table —
//! G2's flag clash and G4's `tm close day --help` advertising a `--drop`
//! the runtime rejected).
//!
//! Everything here drives the **built binary** (`CARGO_BIN_EXE_tm`), never
//! the clap tree: the tree is what *should* be; the binary is what ships.
//! The walk discovers the subcommands from the top-level help, recurses
//! into every one of them (`tm close`'s periods, `tm routine`'s verbs),
//! extracts every advertised long flag from each `Options:` section, and
//! then asserts the runtime **accepts** the flag: `tm <verb…> --<flag>
//! [<dummy>] --help` must not die with clap's `unexpected argument`. A
//! value-taking flag is fed a dummy value; an "invalid value" complaint is
//! acceptance (the flag was recognised), `unexpected argument` is the G4
//! defect.
//!
//! `--help` terminates every probe before it runs a verb, and `--dir` is
//! pinned to an empty temp directory anyway, so a probe that *did* slip
//! past parsing would refuse on "not a plan directory" rather than touch a
//! real tree.

use std::process::Command;

use tempfile::TempDir;

/// One advertised long flag: its name and whether the help shows a value.
#[derive(Debug, Clone, PartialEq)]
struct Flag {
    name: String,
    takes_value: bool,
}

/// What one subcommand's help page advertises.
#[derive(Debug)]
struct HelpPage {
    /// The subcommand path, e.g. `["close", "day"]`.
    path: Vec<String>,
    flags: Vec<Flag>,
}

/// Run the built binary; return (exit code, stdout, stderr).
fn tm(dir: &TempDir, args: &[&str]) -> (i32, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_tm"))
        .arg("--dir")
        .arg(dir.path())
        .args(args)
        .output()
        .expect("run tm");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// `tm <path…> --help`, asserted to succeed — a subcommand the help lists
/// but the binary refuses is itself a conformance failure.
fn help_of(dir: &TempDir, path: &[String]) -> String {
    let mut args: Vec<&str> = path.iter().map(String::as_str).collect();
    args.push("--help");
    let (code, stdout, stderr) = tm(dir, &args);
    assert_eq!(
        code, 0,
        "`tm {} --help` failed (advertised subcommand refused):\n{stderr}",
        path.join(" ")
    );
    stdout
}

/// Split a help page into its sections. clap 4 headers are a line of the
/// form `Word:` (or `Word words:`) at column 0 — `Usage: tm …` has text
/// after the colon and is not a section.
fn sections(help: &str) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    for line in help.lines() {
        let is_header = line.ends_with(':')
            && !line.starts_with(' ')
            && line.len() > 1
            && line[..line.len() - 1].chars().all(|c| c.is_alphanumeric() || c == ' ');
        if is_header {
            out.push((line[..line.len() - 1].to_string(), Vec::new()));
        } else if let Some((_, body)) = out.last_mut() {
            body.push(line.to_string());
        }
    }
    out
}

/// The subcommand names a help page lists. Any section that is not
/// `Usage`/`Arguments`/`Options` lists subcommands (`Commands:`, and
/// `tm close`'s custom `Periods:` heading). clap's own `help` is skipped.
fn subcommands(help: &str) -> Vec<String> {
    let mut names = Vec::new();
    for (header, body) in sections(help) {
        if matches!(header.as_str(), "Usage" | "Arguments" | "Options") {
            continue;
        }
        for line in body {
            // `  name  description` — two spaces, the name, whitespace.
            let Some(rest) = line.strip_prefix("  ") else { continue };
            if rest.starts_with(' ') {
                continue; // continuation line
            }
            let name = rest.split_whitespace().next().unwrap_or("");
            if !name.is_empty() && name != "help" {
                names.push(name.to_string());
            }
        }
    }
    names
}

/// The long flags an `Options:` section advertises.
fn flags(help: &str) -> Vec<Flag> {
    let mut out = Vec::new();
    for (header, body) in sections(help) {
        if header != "Options" {
            continue;
        }
        for line in body {
            let Some(ix) = line.find("--") else { continue };
            // Only the flag column (leading `  -h, --help` / `      --json`),
            // not a `--flag` mentioned inside a description.
            if !line[..ix].chars().all(|c| c == ' ' || c == ',' || c == '-'
                || c.is_alphanumeric())
            {
                continue;
            }
            let rest = &line[ix + 2..];
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '-')
                .collect();
            if name.is_empty() {
                continue;
            }
            let takes_value = rest[name.len()..].starts_with(" <");
            out.push(Flag { name, takes_value });
        }
    }
    out
}

/// Walk the whole verb tree from the top-level help, against the binary.
fn walk(dir: &TempDir) -> Vec<HelpPage> {
    let mut pages = Vec::new();
    let mut queue: Vec<Vec<String>> = vec![Vec::new()];
    while let Some(path) = queue.pop() {
        let help = help_of(dir, &path);
        for sub in subcommands(&help) {
            let mut next = path.clone();
            next.push(sub);
            queue.push(next);
        }
        if !path.is_empty() {
            pages.push(HelpPage {
                path,
                flags: flags(&help),
            });
        }
    }
    pages
}

#[test]
fn every_advertised_flag_is_accepted_by_the_runtime() {
    let dir = TempDir::new().expect("temp dir");
    let pages = walk(&dir);

    // §13 has 34 top-level verbs; `close` adds three periods and `routine`
    // one verb — 38 pages, re-measured. A collapse here means the walk (or
    // the help) broke.
    assert!(
        pages.len() >= 38,
        "expected the full §13 verb tree, walked only {}: {:?}",
        pages.len(),
        pages.iter().map(|p| p.path.join(" ")).collect::<Vec<_>>()
    );

    let mut probes = 0usize;
    for page in &pages {
        // Every subcommand advertises the globals — G2's class dies here.
        for global in ["json", "dir"] {
            assert!(
                page.flags.iter().any(|f| f.name == global),
                "`tm {}` does not advertise --{global}",
                page.path.join(" ")
            );
        }
        for flag in &page.flags {
            if flag.name == "help" || flag.name == "version" {
                continue; // clap's own; they *are* the probe's terminator.
            }
            let long = format!("--{}", flag.name);
            let mut args: Vec<&str> = page.path.iter().map(String::as_str).collect();
            args.push(&long);
            if flag.takes_value {
                args.push("x"); // a dummy; "invalid value" is still acceptance
            }
            args.push("--help");
            let (_, _, stderr) = tm(&dir, &args);
            let rejected = format!("unexpected argument '{long}'");
            assert!(
                !stderr.contains(&rejected),
                "`tm {} --help` advertises {long}, but the runtime rejects it \
                 (G4's class):\n{stderr}",
                page.path.join(" ")
            );
            probes += 1;
        }
    }
    // Re-measured floor: 44 pages × (2 globals + own flags) — a parser that
    // silently extracts nothing would pass every assert above.
    assert!(
        probes >= 100,
        "only {probes} flag probes ran — the help parser lost the Options sections"
    );
}

#[test]
fn the_help_parser_reads_clap_output() {
    // Anchors for the extraction itself, against the real binary: a flag
    // with a value, a flag without, a custom subcommand heading.
    let dir = TempDir::new().expect("temp dir");

    let plan = help_of(&dir, &["plan".to_string()]);
    let fs = flags(&plan);
    assert!(fs.contains(&Flag { name: "week".into(), takes_value: false }), "{fs:?}");
    assert!(fs.contains(&Flag { name: "explain".into(), takes_value: true }), "{fs:?}");
    assert!(fs.contains(&Flag { name: "json".into(), takes_value: false }), "{fs:?}");

    let close = help_of(&dir, &["close".to_string()]);
    assert_eq!(subcommands(&close), ["day", "week", "month"], "the Periods heading");

    let top = help_of(&dir, &[]);
    let subs = subcommands(&top);
    assert!(subs.iter().any(|s| s == "init"), "{subs:?}");
    assert!(subs.iter().any(|s| s == "tui"), "{subs:?}");
    assert!(!subs.iter().any(|s| s == "help"), "clap's help is not a verb");
}

/// **§13's synopsis, `--help` and the runtime agree on W-41's flags**: D79's
/// `--at HH:MM` on `tm stop` and `tm done`, and `tm break --where`'s four places
/// (D81, README gap 3903). The spec writes them, each help page advertises
/// them with a value, and the walk above has the runtime take them.
#[test]
fn section_13_and_the_help_agree_on_the_end_time_and_the_places() {
    let dir = TempDir::new().expect("temp dir");
    for verb in ["stop", "done"] {
        let fs = flags(&help_of(&dir, &[verb.to_string()]));
        assert!(fs.contains(&Flag { name: "at".into(), takes_value: true }), "`tm {verb}`: {fs:?}");
    }
    let fs = flags(&help_of(&dir, &["break".to_string()]));
    assert!(fs.contains(&Flag { name: "where".into(), takes_value: true }), "{fs:?}");
    let spec = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-spec-v1.md"),
    )
    .expect("the spec");
    let section = spec.split("## 13. CLI").nth(1).and_then(|s| s.split("\n## 14.").next()).expect("§13");
    for synopsis in ["tm done [--partial] [--at HH:MM]", "tm stop [--at HH:MM]", "tm break [20m] [--where walk|seat|bed|phone]"] {
        assert!(section.contains(synopsis), "§13 does not write {synopsis:?}");
    }
}

/// **§13, `--help` and the runtime agree on `tm energy --at`'s rule** — the
/// owner's D86 (W-42 track H, README gap 4135, parity P82): the spec writes
/// the twelve-hour rule beside D79's, `tm energy --help` says it on the flag
/// (with the `HH:MM` value D79's flags show), and `tm stop`/`tm done` still say
/// theirs — two rules, each said where its flag is.
#[test]
fn section_13_and_the_help_agree_on_energys_twelve_hour_rule() {
    let dir = TempDir::new().expect("temp dir");
    let energy = help_of(&dir, &["energy".to_string()]);
    let fs = flags(&energy);
    assert!(fs.contains(&Flag { name: "at".into(), takes_value: true }), "{fs:?}");
    assert!(energy.contains("--at <HH:MM>"), "{energy}");
    let flat = energy.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("more than 12 hours after now, then yesterday's"), "{flat}");
    for verb in ["stop", "done"] {
        let help = help_of(&dir, &[verb.to_string()]).split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(help.contains("the latest such time at or before now"), "`tm {verb}` keeps D79's: {help}");
        assert!(!help.contains("12 hours"), "`tm {verb}` does not take energy's rule: {help}");
    }
    let spec = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-spec-v1.md"),
    )
    .expect("the spec");
    let section = spec.split("## 13. CLI").nth(1).and_then(|s| s.split("\n## 14.").next()).expect("§13");
    assert!(section.contains("tm energy 0-5 [--at HH:MM]"), "§13's synopsis");
    assert!(
        section.contains("`tm energy 0-5 --at HH:MM` reports energy at today's HH:MM, unless that is more than 12 hours after now"),
        "§13 says D86's rule"
    );
}

/// **Every `--at` the help pages advertise is read by the ONE parser** — D86's
/// "one parser for both flags" (W-42 track H), as a property over the walked
/// verb tree rather than a list of verbs: on a tree with a block running, each
/// such verb refuses each malformed clock with the one parser's sentence
/// (`tm_core::model::parse_time`), exit 1, and writes nothing. A verb that
/// gains an `--at` joins the walk by itself; the set is asserted so a new one is
/// seen, and its required positionals are filled from its own `Usage:` line.
#[test]
fn every_at_flag_is_read_by_the_one_parser() {
    use std::collections::BTreeMap;
    use std::path::Path;

    fn copy(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).expect("dir");
        for e in std::fs::read_dir(from).expect("read") {
            let e = e.expect("entry");
            let target = to.join(e.file_name());
            if e.file_type().expect("type").is_dir() {
                copy(&e.path(), &target);
            } else {
                std::fs::copy(e.path(), &target).expect("copy");
            }
        }
    }
    fn files(root: &Path, dir: &Path, out: &mut BTreeMap<String, Vec<u8>>) {
        for e in std::fs::read_dir(dir).expect("read") {
            let p = e.expect("entry").path();
            if p.is_dir() {
                files(root, &p, out);
            } else {
                out.insert(p.strip_prefix(root).expect("inside").display().to_string(), std::fs::read(&p).expect("bytes"));
            }
        }
    }
    let now = "2026-09-07T09:00:00-05:00";
    let run = |plan: &Path, args: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_tm"))
            .arg("--dir")
            .arg(plan)
            .arg("--now")
            .arg(now)
            .args(args)
            .output()
            .expect("run tm");
        (out.status.code().unwrap_or(-1), String::from_utf8_lossy(&out.stderr).into_owned())
    };

    let dir = TempDir::new().expect("temp dir");
    let mut at_pages: Vec<(Vec<String>, Vec<String>)> = Vec::new();
    for page in walk(&dir) {
        if page.flags.iter().any(|f| f.name == "at" && f.takes_value) {
            let usage = help_of(&dir, &page.path);
            let usage = usage.lines().find(|l| l.starts_with("Usage:")).unwrap_or_default().to_string();
            let positionals: Vec<String> = usage
                .split_whitespace()
                .filter(|w| w.starts_with('<') && w.ends_with('>'))
                .map(|_| "3".to_string())
                .collect();
            at_pages.push((page.path.clone(), positionals));
        }
    }
    let verbs: Vec<String> = at_pages.iter().map(|(p, _)| p.join(" ")).collect();
    let mut sorted = verbs.clone();
    sorted.sort();
    assert_eq!(sorted, ["arrive", "done", "energy", "stop"], "the verbs that take `--at`");

    let tree = TempDir::new().expect("temp dir");
    let plan = tree.path().join("plan");
    copy(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-core/tests/fixtures/plan-basic"), &plan);
    assert_eq!(run(&plan, &["wake", "07:00"]).0, 0);
    assert_eq!(run(&plan, &["start", "^t4", "--energy", "4"]).0, 0, "a block runs, so `stop`/`done` reach their `--at`");
    let mut refused = 0;
    for bad in ["7:5", "24:00", "07:60", "07:05:00", "0705", ""] {
        for (path, positionals) in &at_pages {
            let mut before = BTreeMap::new();
            files(&plan, &plan, &mut before);
            let mut args: Vec<&str> = path.iter().map(String::as_str).collect();
            args.extend(positionals.iter().map(String::as_str));
            args.extend(["--at", bad]);
            let (code, stderr) = run(&plan, &args);
            assert_eq!(code, 1, "`tm {}`: {stderr}", args.join(" "));
            assert_eq!(stderr.trim(), format!("tm: invalid time: {bad:?}"), "`tm {}` reads the clock by the one parser", args.join(" "));
            let mut after = BTreeMap::new();
            files(&plan, &plan, &mut after);
            assert!(before == after, "`tm {}` wrote on a refused clock", args.join(" "));
            refused += 1;
        }
    }
    assert_eq!(refused, 6 * 4);
}

/// **§13, `--help` and the runtime agree on `tm interrupt`'s rule** — the owner's D90 (W-43 track
/// H, README gap 4340, parity P86): the spec says a running break ends first, `tm interrupt
/// --help` says it, and the runtime does it (`cli_interrupt_break.rs`, the day of gap 4340 on every
/// surface that reads a block's minutes).
#[test]
fn section_13_and_the_help_agree_that_tm_interrupt_ends_a_running_break_first() {
    let dir = TempDir::new().expect("temp dir");
    let help = help_of(&dir, &["interrupt".to_string()]).split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(help.contains("A running break ends first, logged as `tm break` logs its end"), "{help}");
    let spec = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tm-spec-v1.md"),
    )
    .expect("the spec");
    let section = spec.split("## 13. CLI").nth(1).and_then(|s| s.split("\n## 14.").next()).expect("§13");
    assert!(
        section.contains("`tm interrupt` while a break is running ends the break first"),
        "§13 says D90's rule"
    );
}
