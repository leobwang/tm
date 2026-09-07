//! What `tm init` generates: the plan skeleton of tm-spec-v1.md §2 and the
//! Claude Code integration of §14.
//!
//! # API overview
//!
//! The content lives in `tm/templates/` and is embedded with `include_str!`,
//! so the binary carries the whole skeleton and `tm init` needs no data files:
//!
//! * [`CLAUDE_MD`] — §14's rules for Claude Code, verbatim (6 lines).
//! * [`SKILLS`] — one `(name, SKILL.md)` pair per row of §14's skill table:
//!   `plan-week`, `plan-month`, `triage`, `capture`, `replan`, `review-day`,
//!   `review-week`, `explain`. Each has YAML front matter (`name`,
//!   `description` = when to use it) and the `tm … --json` commands it runs.
//! * [`SETTINGS_JSON`] — `.claude/settings.json`: the §14 `PostToolUse` hook
//!   on `Edit|MultiEdit|Write` that runs `tm check`, plus a `deny` rule for
//!   `.tm/**` (§14: Claude never touches the runtime state). A hook matcher
//!   matches tool *names*, not paths; the scoping to `plan/` comes from where
//!   the file lives — §2 puts `.claude/` inside the plan tree, so the project
//!   directory is the plan tree and the bare `tm check` resolves it from the
//!   working directory.
//! * [`PRE_COMMIT`] — `.githooks/pre-commit`, the same check as a git hook
//!   (§1.3). `tm init` never rewrites the user's git config; it prints
//!   [`hook_hint`] instead.
//! * [`GITIGNORE`] — the `.tm/state.json` line and the CLI's other caches.
//!
//! Two entry points:
//!
//! * [`files`]`(&`[`Options`]`)` — the whole tree as [`InitFile`] values
//!   (relative path, text, [`Mode`]), pure and testable; [`DIRS`] lists the
//!   directories that carry no file of their own (`calendar/`, `.tm/`).
//! * [`write`]`(root, &`[`Options`]`)` — creates them, returning [`Written`]
//!   (what was created, what was left alone). It refuses a non-empty
//!   directory unless [`Options::force`], and never rewrites an existing
//!   `.gitignore` — it appends the tm block only when it is missing.
//!
//! [`Options::example`] swaps the guidance files for §4.3's populated tree
//! (the `plan-basic` fixture, byte for byte), so a new user can run `tm plan`
//! immediately. Either way the result passes `tm check` (§17 M9).

use std::fs;
use std::io;
use std::path::Path;

use chrono::NaiveDate;
use thiserror::Error;
use tm_core::config::Config;
use tm_core::model::{Horizon, IsoWeek, YearMonth};
use tm_core::store;

/// §14's `plan/CLAUDE.md`, verbatim.
pub const CLAUDE_MD: &str = include_str!("../../templates/CLAUDE.md");

/// `.claude/settings.json`: the §14 `PostToolUse` hook running `tm check`.
pub const SETTINGS_JSON: &str = include_str!("../../templates/settings.json");

/// `.githooks/pre-commit`: `tm check` before every commit (§1.3).
pub const PRE_COMMIT: &str = include_str!("../../templates/pre-commit");

/// The `.gitignore` block for the runtime state (§10.2).
pub const GITIGNORE: &str = include_str!("../../templates/gitignore");

/// The path whose presence means the [`GITIGNORE`] block is already there.
const GITIGNORE_MARKER: &str = ".tm/state.json";

/// §14's skills, as `(name, SKILL.md text)`, in table order.
pub const SKILLS: &[(&str, &str)] = &[
    (
        "plan-week",
        include_str!("../../templates/skills/plan-week.md"),
    ),
    (
        "plan-month",
        include_str!("../../templates/skills/plan-month.md"),
    ),
    ("triage", include_str!("../../templates/skills/triage.md")),
    ("capture", include_str!("../../templates/skills/capture.md")),
    ("replan", include_str!("../../templates/skills/replan.md")),
    (
        "review-day",
        include_str!("../../templates/skills/review-day.md"),
    ),
    (
        "review-week",
        include_str!("../../templates/skills/review-week.md"),
    ),
    ("explain", include_str!("../../templates/skills/explain.md")),
];

/// The guidance an empty tree carries: `(relative path, text)`.
const STARTER: &[(&str, &str)] = &[
    ("inbox.md", include_str!("../../templates/starter/inbox.md")),
    (
        "backlog.md",
        include_str!("../../templates/starter/backlog.md"),
    ),
    (
        "routines.md",
        include_str!("../../templates/starter/routines.md"),
    ),
    (
        "optional.md",
        include_str!("../../templates/starter/optional.md"),
    ),
];

/// The body of a fresh `month/<YYYY-MM>.md`, after its front matter.
const MONTH_BODY: &str = include_str!("../../templates/starter/month-body.md");

/// The body of a fresh `week/<YYYY-Www>.md`, after its front matter.
const WEEK_BODY: &str = include_str!("../../templates/starter/week-body.md");

/// `--example`: §4.3's tree, `(relative path, text)`. The dates are the
/// spec's (Monday 2026-09-07, week 2026-W37), so the example reads exactly
/// like §4.3 and like the `plan-basic` fixture.
const EXAMPLE: &[(&str, &str)] = &[
    ("inbox.md", include_str!("../../templates/example/inbox.md")),
    (
        "backlog.md",
        include_str!("../../templates/example/backlog.md"),
    ),
    (
        "routines.md",
        include_str!("../../templates/example/routines.md"),
    ),
    (
        "optional.md",
        include_str!("../../templates/example/optional.md"),
    ),
    (
        "month/2026-09.md",
        include_str!("../../templates/example/month.md"),
    ),
    (
        "week/2026-W37.md",
        include_str!("../../templates/example/week.md"),
    ),
    (
        "calendar/2026-W37.md",
        include_str!("../../templates/example/calendar.md"),
    ),
    (
        "day/2026-09-07.md",
        include_str!("../../templates/example/day.md"),
    ),
];

/// Directories §2 wants that no generated file creates on its own.
pub const DIRS: &[&str] = &["calendar", ".tm"];

/// Where the git hook lives, relative to the plan root (§1.3).
pub const HOOKS_DIR: &str = ".githooks";

/// What `tm init` should generate.
#[derive(Debug, Clone)]
pub struct Options {
    /// Today, for `month/<YYYY-MM>.md` and `week/<YYYY-Www>.md` (injected,
    /// never read from a clock in here).
    pub today: NaiveDate,
    /// Write §4.3's populated tree instead of the guidance files.
    pub example: bool,
    /// Overwrite an existing tree (without it, a non-empty directory is
    /// [`InitError::NotEmpty`]).
    pub force: bool,
}

impl Options {
    /// The default options for `today`: guidance files, no overwriting.
    pub fn new(today: NaiveDate) -> Options {
        Options {
            today,
            example: false,
            force: false,
        }
    }
}

/// How one generated file is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// tm owns the file: written as generated (existing content is replaced
    /// only under `--force`, which is the only way to reach an existing tree).
    Managed,
    /// [`Mode::Managed`], plus the executable bit on unix (the git hook).
    Executable,
    /// The user owns the file: created when absent, otherwise extended with
    /// the missing block, never rewritten — `.gitignore` may hold their own
    /// entries.
    Merge,
}

/// One file `tm init` generates.
#[derive(Debug, Clone)]
pub struct InitFile {
    /// Path relative to the plan root, `/`-separated.
    pub path: String,
    /// The whole file.
    pub text: String,
    /// How to write it.
    pub mode: Mode,
}

impl InitFile {
    /// A file tm owns.
    fn managed(path: impl Into<String>, text: impl Into<String>) -> InitFile {
        InitFile {
            path: path.into(),
            text: text.into(),
            mode: Mode::Managed,
        }
    }
}

/// What [`write`] did.
#[derive(Debug, Clone, Default)]
pub struct Written {
    /// Files created (or, for `.gitignore`, extended), in generation order.
    pub created: Vec<String>,
    /// [`Mode::Merge`] files that already carried tm's block and were left
    /// exactly as they were. Nothing else can land here: `tm init` refuses a
    /// non-empty directory rather than half-writing it, and `--force`
    /// rewrites every file it owns.
    pub unchanged: Vec<String>,
}

/// Everything `tm init` can fail with.
#[derive(Debug, Error)]
pub enum InitError {
    /// The target directory already holds something and `--force` was not
    /// given.
    #[error("{dir} is not empty — refusing to overwrite it (use --force)")]
    NotEmpty {
        /// The directory.
        dir: String,
    },
    /// Creating a directory or writing a file failed.
    #[error("{path}: {source}")]
    Io {
        /// The path being written.
        path: String,
        /// The underlying error.
        source: io::Error,
    },
}

impl InitError {
    /// An [`InitError::Io`] for `path`.
    fn io(path: impl Into<String>, source: io::Error) -> InitError {
        InitError::Io {
            path: path.into(),
            source,
        }
    }
}

/// The one-line instruction `tm init` prints instead of rewriting the user's
/// git config (§1.3, §14).
pub fn hook_hint(root: &Path) -> String {
    format!(
        "git config core.hooksPath {}",
        root.join(HOOKS_DIR).display()
    )
}

/// One `SKILL.md`'s path and text.
fn skill_file(name: &str, text: &str) -> InitFile {
    InitFile::managed(format!(".claude/skills/{name}/SKILL.md"), text)
}

/// Every file `tm init` writes, in the order it writes them.
///
/// Pure: the only inputs are [`Options::today`] and the two flags, so the
/// whole tree can be snapshotted without touching the filesystem.
pub fn files(opts: &Options) -> Vec<InitFile> {
    let mut out = Vec::new();

    // §16: the complete config, with `ics_urls = []` and the example URL as a
    // comment (§15). It parses to `Config::default()`.
    out.push(InitFile::managed(
        store::CONFIG_PATH,
        Config::default_toml(),
    ));

    // §14: the rules, the skills and the two hooks.
    out.push(InitFile::managed("CLAUDE.md", CLAUDE_MD));
    out.push(InitFile::managed(".claude/settings.json", SETTINGS_JSON));
    for (name, text) in SKILLS {
        out.push(skill_file(name, text));
    }
    out.push(InitFile {
        path: format!("{HOOKS_DIR}/pre-commit"),
        text: PRE_COMMIT.to_string(),
        mode: Mode::Executable,
    });
    out.push(InitFile {
        path: ".gitignore".to_string(),
        text: GITIGNORE.to_string(),
        mode: Mode::Merge,
    });

    // §2: the files themselves.
    if opts.example {
        for (path, text) in EXAMPLE {
            out.push(InitFile::managed(*path, *text));
        }
    } else {
        for (path, text) in STARTER {
            out.push(InitFile::managed(*path, *text));
        }
        let month = Horizon::Month(YearMonth::from_date(opts.today));
        let week = Horizon::Week(IsoWeek::from_date(opts.today));
        out.push(InitFile::managed(
            month.path(),
            format!("{}{MONTH_BODY}", store::initial_text(&month)),
        ));
        out.push(InitFile::managed(
            week.path(),
            format!("{}{WEEK_BODY}", store::initial_text(&week)),
        ));
    }
    out
}

/// True when `dir` exists and holds at least one entry.
fn is_non_empty(dir: &Path) -> bool {
    fs::read_dir(dir)
        .map(|mut entries| entries.next().is_some())
        .unwrap_or(false)
}

/// Give the file the executable bit (unix only; a no-op elsewhere).
#[cfg(unix)]
fn make_executable(path: &Path) -> Result<(), InitError> {
    use std::os::unix::fs::PermissionsExt;
    let mut perms = fs::metadata(path)
        .map_err(|e| InitError::io(path.display().to_string(), e))?
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).map_err(|e| InitError::io(path.display().to_string(), e))
}

/// Give the file the executable bit (unix only; a no-op elsewhere).
#[cfg(not(unix))]
fn make_executable(_path: &Path) -> Result<(), InitError> {
    Ok(())
}

/// The text a `.gitignore` should end up with: the existing one plus the tm
/// block, or `None` when it already has it.
fn merged_gitignore(existing: &str, block: &str) -> Option<String> {
    if existing.lines().any(|l| l.trim() == GITIGNORE_MARKER) {
        return None;
    }
    let mut out = String::from(existing);
    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(block);
    Some(out)
}

/// Create the tree under `root` (§2, §14, §17 M9).
///
/// Refuses a directory that already holds something unless
/// [`Options::force`]; creates `root` and [`DIRS`] otherwise. Returns what
/// was written — `.gitignore` appears in [`Written::created`] only when it
/// was actually created or extended, and in [`Written::unchanged`] when it
/// already carried the tm block.
pub fn write(root: &Path, opts: &Options) -> Result<Written, InitError> {
    if !opts.force && is_non_empty(root) {
        return Err(InitError::NotEmpty {
            dir: root.display().to_string(),
        });
    }
    fs::create_dir_all(root).map_err(|e| InitError::io(root.display().to_string(), e))?;
    for dir in DIRS {
        let path = root.join(dir);
        fs::create_dir_all(&path).map_err(|e| InitError::io(path.display().to_string(), e))?;
    }

    let mut written = Written::default();
    for file in files(opts) {
        let path = root.join(&file.path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| InitError::io(parent.display().to_string(), e))?;
        }
        let text = match file.mode {
            Mode::Merge if path.exists() => {
                let existing = fs::read_to_string(&path)
                    .map_err(|e| InitError::io(path.display().to_string(), e))?;
                match merged_gitignore(&existing, &file.text) {
                    Some(text) => text,
                    None => {
                        written.unchanged.push(file.path.clone());
                        continue;
                    }
                }
            }
            _ => file.text.clone(),
        };
        fs::write(&path, &text).map_err(|e| InitError::io(path.display().to_string(), e))?;
        if file.mode == Mode::Executable {
            make_executable(&path)?;
        }
        written.created.push(file.path.clone());
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn opts() -> Options {
        Options::new(NaiveDate::from_ymd_opt(2026, 9, 7).expect("date"))
    }

    #[test]
    fn the_generated_config_is_the_default_one() {
        let files = files(&opts());
        let cfg = &files[0];
        assert_eq!(cfg.path, "config.toml");
        assert_eq!(Config::parse(&cfg.text).expect("parse"), Config::default());
        assert!(cfg.text.contains("ics_urls       = []"));
    }

    #[test]
    fn every_skill_has_front_matter_and_is_short() {
        for (name, text) in SKILLS {
            let mut lines = text.lines();
            assert_eq!(lines.next(), Some("---"), "{name}");
            let front: Vec<&str> = lines.by_ref().take_while(|l| *l != "---").collect();
            assert!(
                front.iter().any(|l| *l == format!("name: {name}")),
                "{name} front matter: {front:?}"
            );
            let description = front
                .iter()
                .find_map(|l| l.strip_prefix("description: "))
                .unwrap_or_else(|| panic!("{name} has no description"));
            // The front matter is one plain YAML scalar per key: no `: ` and
            // no ` #`, either of which would truncate it.
            assert!(!description.contains(": "), "{name}: {description}");
            assert!(!description.contains(" #"), "{name}: {description}");
            assert!(front.len() == 2, "{name} front matter: {front:?}");
            assert!(text.lines().count() < 60, "{name} is too long");
            assert!(text.contains("tm "), "{name} runs no tm command");
        }
    }

    #[test]
    fn the_month_and_week_files_keep_their_front_matter_first() {
        let files = files(&opts());
        let month = files
            .iter()
            .find(|f| f.path == "month/2026-09.md")
            .expect("month");
        assert!(month.text.starts_with("---\nmonth: 2026-09\n---\n"));
        let week = files
            .iter()
            .find(|f| f.path == "week/2026-W37.md")
            .expect("week");
        assert!(week.text.starts_with("---\nweek: 2026-W37\n"));
        assert!(week.text.contains("window: 2026-09-07..2026-09-13"));
    }

    #[test]
    fn the_gitignore_is_merged_not_rewritten() {
        assert_eq!(merged_gitignore(GITIGNORE, GITIGNORE), None);
        let merged = merged_gitignore("target/", GITIGNORE).expect("merged");
        assert!(merged.starts_with("target/\n\n"));
        assert!(merged.ends_with(GITIGNORE));
        assert_eq!(merged_gitignore("", GITIGNORE).as_deref(), Some(GITIGNORE));
    }
}
