//! The human-owned halves of `day/<date>.md` (tm-spec-v1.md §4.3): the
//! runtime front matter and the append-only `## Log`.
//!
//! # API overview
//!
//! §4.3 draws a day file with six front-matter keys (`date`, `wake`, `slept`,
//! `loc`, `window`, `budget`) and three sections (`# Pinned`, `## Log`,
//! `## Notes`); §1.2 gives `emit.rs` only the generated section and the SVG,
//! and §14's generated `CLAUDE.md` forbids Claude Code from touching
//! `## Log` — so the CLI is the only writer of either.
//!
//! * [`ensure`] — create the day file with the whole §4.3 skeleton when it
//!   does not exist yet (the store's own `initial_text` stops at the
//!   `![day]` line).
//! * [`note`] — append one `HH:MM …` line to `## Log`. Every clock verb of
//!   §9 writes exactly one.
//! * [`front`] — set runtime front-matter keys, in the §4.3 order, keeping
//!   every other key and the rest of the file byte for byte.
//!
//! All three go through [`tm_core::store::Store::modify_file`], so a
//! concurrent save by one of the other two writers (§1.3) is merged rather
//! than clobbered.

use chrono::{NaiveDate, NaiveTime};
use tm_core::grammar::ParsedFile;
use tm_core::model::Horizon;
use tm_core::store::{edit, Store};

use super::ctx::Ctx;
use super::out::CliError;

/// The path of a day file.
pub fn path(date: NaiveDate) -> String {
    Horizon::Day(date).path()
}

/// The §4.3 skeleton of a day file that does not exist yet. Returns the path.
pub fn ensure(ctx: &Ctx, date: NaiveDate) -> Result<String, CliError> {
    let rel = path(date);
    let initial = format!(
        "---\ndate: {date}\n---\n![day]({date}.svg)\n\n# Pinned\n\n## Log\n\n## Notes\n"
    );
    ctx.store.ensure_file(&rel, &initial)?;
    Ok(rel)
}

/// Append one line to the day file's append-only `## Log` (§4.3). The
/// section — and the file — are created when they are missing.
pub fn note(ctx: &Ctx, date: NaiveDate, at: NaiveTime, text: &str) -> Result<(), CliError> {
    let rel = ensure(ctx, date)?;
    ctx.store.append_to_section(&rel, "## Log", &journal_line(at, text))?;
    Ok(())
}

/// The `## Log` line [`note`] writes: `HH:MM <text>`.
fn journal_line(at: NaiveTime, text: &str) -> String {
    format!("{} {}", at.format("%H:%M"), text.trim())
}

/// [`note`], written by **housekeeping** rather than by the user's command —
/// D61's meeting pause, which runs before any undo recorder — and therefore
/// rebased UNDER the undo stack, so a later `tm undo` neither trips over the
/// line nor drops it (`undo::rebase_underneath`, README gap 3330). `active` is
/// the running block and the timer state the same write left it in.
pub fn note_underneath(
    ctx: &Ctx,
    date: NaiveDate,
    at: NaiveTime,
    text: &str,
    active: Option<(&tm_core::model::Id, bool)>,
) -> Result<(), CliError> {
    let rel = path(date);
    let was = if ctx.store.exists(&rel) { Some(ctx.store.read_text(&rel)?) } else { None };
    note(ctx, date, at, text)?;
    let now = ctx.store.read_text(&rel)?;
    let line = journal_line(at, text);
    let cfg = ctx.store.read_config()?;
    let edit = |t: &str| {
        edit::append_to_section(&tm_core::grammar::parse_file(&rel, t, &cfg), "## Log", &line)
    };
    super::undo::rebase_underneath(ctx, &rel, was.as_deref(), &now, &edit, active)
}

/// Set runtime front-matter keys of the day file (§4.3's `wake`, `slept`,
/// `loc`, `window`, `budget`). A key already present is rewritten in place;
/// a new one is appended at the end of the front matter, which — because
/// §4.3's own order is the order the day is lived in — reproduces the spec's
/// layout on a file the CLI created.
pub fn front(ctx: &Ctx, date: NaiveDate, entries: &[(&str, String)]) -> Result<(), CliError> {
    if entries.is_empty() {
        return Ok(());
    }
    let rel = ensure(ctx, date)?;
    ctx.store
        .modify_file(&rel, &mut |parsed: &ParsedFile| Ok(set_front(parsed, entries)))?;
    Ok(())
}

/// The file text with `entries` applied to its front matter, or `None` when
/// nothing changed (or the file has no front matter to change).
fn set_front(parsed: &ParsedFile, entries: &[(&str, String)]) -> Option<String> {
    let len = edit::front_matter_len(parsed);
    if len < 2 {
        return None;
    }
    let text = parsed.to_text();
    let ends_with_newline = text.ends_with('\n');
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut changed = false;
    // The front matter runs from line 1 up to `end`, the closing `---`.
    // Appending moves that delimiter down, so new keys keep the order they
    // were given in — which is §4.3's.
    let mut end = len - 1;
    for (key, value) in entries {
        let want = format!("{key}: {value}");
        match (1..end).find(|i| is_key(&lines[*i], key)) {
            Some(i) if lines[i] == want => {}
            Some(i) => {
                lines[i] = want;
                changed = true;
            }
            None => {
                lines.insert(end, want);
                end += 1;
                changed = true;
            }
        }
    }
    if !changed {
        return None;
    }
    let mut out = lines.join("\n");
    if ends_with_newline {
        out.push('\n');
    }
    Some(out)
}

/// True when a front-matter line carries `key`.
fn is_key(line: &str, key: &str) -> bool {
    line.split_once(':')
        .is_some_and(|(k, _)| k.trim() == key)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tm_core::config::Config;
    use tm_core::grammar::parse_file;

    fn parsed(text: &str) -> ParsedFile {
        parse_file("day/2026-09-07.md", text, &Config::default())
    }

    #[test]
    fn a_new_key_lands_at_the_end_of_the_front_matter() {
        let p = parsed("---\ndate: 2026-09-07\n---\n![day](x.svg)\n");
        let out = set_front(&p, &[("wake", "06:05".into())]).expect("changed");
        assert_eq!(out, "---\ndate: 2026-09-07\nwake: 06:05\n---\n![day](x.svg)\n");
    }

    #[test]
    fn several_new_keys_keep_the_order_they_were_given() {
        let p = parsed("---\ndate: 2026-09-07\n---\nbody\n");
        let out = set_front(
            &p,
            &[
                ("loc", "home".into()),
                ("window", "08:30..16:30".into()),
                ("budget", "6".into()),
            ],
        )
        .expect("changed");
        assert_eq!(
            out,
            "---\ndate: 2026-09-07\nloc: home\nwindow: 08:30..16:30\nbudget: 6\n---\nbody\n"
        );
    }

    #[test]
    fn an_existing_key_is_rewritten_in_place() {
        let p = parsed("---\ndate: 2026-09-07\nwake: 06:05\nloc: lounge\n---\nbody\n");
        let out = set_front(&p, &[("wake", "08:15".into())]).expect("changed");
        assert!(out.contains("wake: 08:15"));
        assert!(out.contains("loc: lounge"));
        assert!(!out.contains("06:05"));
    }

    #[test]
    fn writing_the_same_value_changes_nothing() {
        let p = parsed("---\ndate: 2026-09-07\nwake: 06:05\n---\n");
        assert!(set_front(&p, &[("wake", "06:05".into())]).is_none());
    }

    #[test]
    fn a_file_without_front_matter_is_left_alone() {
        let p = parsed("# Pinned\n");
        assert!(set_front(&p, &[("wake", "06:05".into())]).is_none());
    }
}
