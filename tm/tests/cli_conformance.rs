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
