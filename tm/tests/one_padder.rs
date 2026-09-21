//! **D43's guard: one table decides every column.**
//!
//! README gap **1007** has owed this test since it was opened — P8's row says
//! "`emit::render_row` the only padder" and "the grep guard" — and gap **1089**
//! named what the guard would have to kill: `tm/src/tui/queue.rs` had its own
//! `width`, `truncate` and `pad`, measuring with ratatui's `unicode-width`
//! where `tm-core/src/emit.rs` measures with its own East-Asian table. One
//! concept, two implementations, two different answers (AGENTS §5.3).
//!
//! The three byte-equality assertions D30 Q5 asks for do **not** keep G1 dead
//! on their own: a future private stand-in renderer reintroduces it and those
//! assertions still pass, because they compare two surfaces that both call the
//! new one. This does, and it is the shape design §8.3's last line asks for.
//!
//! **What it cannot see.** It reads the two `src` trees as text, so a padder
//! written in a `tests/`, `examples/` or `build.rs` file is invisible, and so
//! is one that reaches a width through a dependency this file does not name
//! (ratatui's `Span::width`, `unicode-width` and `wcwidth` are named; a new
//! crate would not be). It also cannot see a padder that measures correctly
//! and lays out wrongly — it is about *one measurement*, not about layout.

use std::fs;
use std::path::{Path, PathBuf};

/// The one file allowed to hold a width table, a truncation or a pad.
const HOME: &str = "tm-core/src/emit.rs";

/// The names the home file is allowed to declare, and nobody else may.
const RESERVED: &[&str] =
    &["char_width", "display_width", "width", "pad", "truncate", "pad_to", "clip"];

/// Ways of asking "how many terminal columns is this string?" that are not
/// [`HOME`]'s own table. `.width()` is ratatui's `Span`/`Line`/`Text` method
/// (a `Rect`'s width is a field and has no parentheses); `0x1100` is the first
/// entry of every hand-rolled East-Asian range table there has ever been, and
/// catches the one shape the name list cannot — a second table under a name
/// nobody thought to reserve.
const MEASUREMENTS: &[&str] =
    &[".width()", "unicode_width", "UnicodeWidthStr", "wcwidth", "0x1100"];

/// Every `.rs` file of the two crates the binary is built from.
fn sources() -> Vec<(String, String)> {
    fn walk(label: &str, root: &Path, dir: &Path, acc: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(dir).expect("read_dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(label, root, &path, acc);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(root).expect("under src").display().to_string();
                acc.push((
                    format!("{label}/{rel}"),
                    fs::read_to_string(&path).expect("read source"),
                ));
            }
        }
    }
    let tm = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace = tm.parent().expect("workspace root").to_path_buf();
    let mut acc = Vec::new();
    for (label, dir) in [
        ("tm/src", tm.join("src")),
        ("tm-core/src", workspace.join("tm-core").join("src")),
    ] {
        walk(label, &dir, &dir, &mut acc);
    }
    acc.sort();
    assert!(acc.len() > 20, "the walk found {} files; it is not reading the tree", acc.len());
    acc
}

/// The function names a file declares, at any indentation.
fn declared_fns(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|l| {
            let t = l.trim_start();
            let rest = t
                .strip_prefix("pub(crate) fn ")
                .or_else(|| t.strip_prefix("pub fn "))
                .or_else(|| t.strip_prefix("fn "))?;
            Some(
                rest.chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect::<String>(),
            )
        })
        .collect()
}

/// Lines that are code rather than prose: `//` comments name the functions
/// that were deleted, and a guard that could not tell a comment from a call
/// would fail on its own explanation of itself.
fn code_lines(text: &str) -> impl Iterator<Item = (usize, &str)> {
    text.lines()
        .enumerate()
        .map(|(i, l)| (i + 1, l))
        .filter(|(_, l)| {
            let t = l.trim_start();
            !(t.starts_with("//") || t.starts_with("/*") || t.starts_with('*'))
        })
}

/// **One measurement.** Nothing outside [`HOME`] asks a string how wide it is.
#[test]
fn exactly_one_thing_measures_a_terminal_column() {
    let mut hits = Vec::new();
    for (name, text) in sources() {
        if name == HOME {
            continue;
        }
        for (n, line) in code_lines(&text) {
            for probe in MEASUREMENTS {
                if line.contains(probe) {
                    hits.push(format!("{name}:{n}: {probe} in `{}`", line.trim()));
                }
            }
        }
    }
    assert!(
        hits.is_empty(),
        "a second measurement of terminal width (D43: there is one, and it is \
         `{HOME}`'s `char_width`):\n  {}",
        hits.join("\n  ")
    );
}

/// **One padder.** Nothing outside [`HOME`] declares a pad, a truncation, a
/// fit or a width — under those names or any of them.
#[test]
fn exactly_one_thing_pads_a_cell() {
    let mut strays = Vec::new();
    let mut at_home: Vec<String> = Vec::new();
    for (name, text) in sources() {
        for f in declared_fns(&text) {
            if !RESERVED.contains(&f.as_str()) {
                continue;
            }
            if name == HOME {
                at_home.push(f);
            } else {
                strays.push(format!("{name}: fn {f}"));
            }
        }
    }
    assert!(
        strays.is_empty(),
        "a second padder (D43, README gap 1089 — this is what the guard is for):\n  {}",
        strays.join("\n  ")
    );
    at_home.sort();
    assert_eq!(
        at_home,
        vec!["char_width", "clip", "display_width", "pad", "pad_to", "truncate"],
        "{HOME} no longer declares exactly the five the guard is written about"
    );
}

/// **The home file still holds the table**, so the guard cannot pass by the
/// padder having been deleted rather than unified.
#[test]
fn the_one_table_is_still_there() {
    let (_, emit) = sources()
        .into_iter()
        .find(|(n, _)| n == HOME)
        .expect("tm-core/src/emit.rs");
    assert!(emit.contains("WIDE_RANGES"), "the East-Asian table is gone");
    assert!(emit.contains("ZERO_RANGES"), "the zero-width table is gone");
}

/// **The screens that lost their padder call this one.** Without this the
/// guard would pass on a TUI that stopped padding at all.
#[test]
fn every_screen_pads_through_emit() {
    let want = [
        "tm/src/tui/queue.rs",
        "tm/src/tui/necessities.rs",
        "tm/src/tui/inbox.rs",
        "tm/src/tui/today.rs",
    ];
    let files = sources();
    for name in want {
        let (_, text) = files
            .iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("{name} is not in the walk"));
        assert!(
            text.contains("emit::clip(") || text.contains("emit::pad_to("),
            "{name} draws columns and asks nothing to fit them"
        );
    }
}

/// **What D43 actually cost, measured rather than predicted.**
///
/// D43 accepted that "columns containing CJK or emoji may shift by a cell".
/// Measured over all 1,112,064 code points, **CJK does not shift**: `emit`'s
/// table and ratatui's `unicode-width` agree on every Han, Kana and Hangul
/// character in the BMP, and on `⏰`, `🌙` and `·` — the glyphs this repository
/// actually prints. Where they part is elsewhere, and it is **both
/// directions**, which is the half the prediction did not have:
///
/// * **8,099 code points `emit` calls one column and ratatui calls two** —
///   Tangut (U+17000..U+187F7), Tangut Components, Nushu and the Kana
///   supplements, which `WIDE_RANGES` does not carry. A row holding one is
///   measured a column narrow per character and is cut a column **late**.
/// * **6,053 that `emit` calls one and ratatui calls zero** — combining marks
///   outside U+0300..U+036F (Arabic and Hebrew points, Indic matras) and the
///   bidi controls, which `ZERO_RANGES` does not carry. Cut **early**.
/// * **1,163 the other way**, mostly unassigned CJK radical positions.
/// * Above one code point, a skin-toned or ZWJ emoji is two columns to ratatui
///   and four or six to `emit` (`👍🏽`, `👨‍👩‍👧`).
///
/// The owner declined unifying on ratatui because the day file's bytes are
/// this table's, so the corpus round trip and the frozen-fork comparand would
/// both have moved. This test is what that decision costs, in numbers.
#[test]
fn the_accepted_divergence_is_measured_and_not_predicted() {
    use ratatui::text::Span;
    use tm_core::emit;
    for s in ["abc", "読書", "日本語のタイトル", "한국어", "⏰", "🌙", "café", "naïve", "·", "…"] {
        assert_eq!(
            emit::display_width(s),
            Span::raw(s.to_string()).width(),
            "the two tables were supposed to agree on {s:?}"
        );
    }
    let (mut narrow, mut zero, mut other) = (0usize, 0usize, 0usize);
    for cp in 0u32..0x11_0000 {
        let Some(c) = char::from_u32(cp) else { continue };
        let s = c.to_string();
        match (emit::display_width(&s), Span::raw(s).width()) {
            (a, b) if a == b => {}
            (1, 2) => narrow += 1,
            (1, 0) => zero += 1,
            _ => other += 1,
        }
    }
    // Bands, not equalities: a `unicode-width` bump moves these and should be
    // visible, but a one-code-point revision is not a regression.
    assert!((7_500..8_700).contains(&narrow), "{narrow} under-counted (measured 8,099)");
    assert!((5_700..6_400).contains(&zero), "{zero} zero-width missed (measured 6,053)");
    assert!((1_000..1_400).contains(&other), "{other} the other way (measured 1,163)");
    assert_eq!(emit::display_width("👍🏽"), 4);
    assert_eq!(Span::raw("👍🏽".to_string()).width(), 2);
}

/// **The runtime half.** The guard is a grep; this is the measurement it is
/// protecting, so a table quietly replaced by one that counts characters fails
/// here rather than in a screenshot.
#[test]
fn the_one_table_is_the_east_asian_one() {
    use tm_core::emit;
    assert_eq!(emit::display_width("読書"), 4, "a CJK title is two columns a character");
    assert_eq!(emit::display_width("⏰"), 2, "U+23F0");
    assert_eq!(emit::display_width("abc"), 3);
    // `pad_to` is exactly what `tui/queue.rs::pad` was: cut, then left-align.
    assert_eq!(emit::pad_to("abc", 6), "abc   ");
    assert_eq!(emit::display_width(&emit::pad_to("読書読書", 5)), 5);
    assert_eq!(emit::pad_to("", 3), "   ");
    assert_eq!(emit::pad_to("abcdef", 4), "abc…");
    // `clip` is the viewport cut and keeps the padding in front of the `…`,
    // which is the one thing it does differently from `truncate`.
    assert_eq!(emit::clip("ab   cdef", 5), "ab  …");
    assert_eq!(emit::truncate("ab   cdef", 5), "ab…");
}
