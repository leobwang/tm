//! **D30 Q5 (a)'s acceptance: one row renderer, and every surface's rows are
//! its output.** This is what design §8.3 asks for by name and what §8.4 means
//! by PLAN §4's **G1** — "the kernel owns the generated blocks; there is exactly
//! one implementation of the day-section text" — being dead. §8.4 calls G1 an
//! **architecture row, not a proof row**, so this is a Rust test and the Lean
//! compiler gets no credit for it.
//!
//! **What was alive until W-23.** `emit::render_row` wrote the day file's grid
//! and the TUI's Timeline; `emit::render_now_with` was a *second* renderer with
//! its own format string (`▶ title  @O1  ci4  p5  2b`, two spaces, no columns,
//! no truncation); and `tm/src/tui/today.rs::seg_title` was a *third*, of the
//! title cell alone, saying `break`, `rest`, `interruption` and `batch (3)`
//! where `emit::title_cell` says `break 20m`, `rest 20m`, the wall's item and
//! `batch: … (3)`. Three implementations agreeing by hand is the defect G1
//! names. README gaps **1104** and **1109** owed this file.
//!
//! **Position, never value** (README gap **1197**). Two items with one title
//! give rows that differ only in the time column, and nothing forbids two
//! segments starting at the same instant, so two rows of a day can be
//! byte-identical — [`byte_identical_rows_are_constructible_so_position_decides`]
//! builds the pair rather than arguing about it. Every mapping between a row and
//! a segment in this repository is therefore an index, and the one place that
//! re-derived it from the text (the TUI, looking for `───` at a fixed offset)
//! was deleted at W-23.
//!
//! # What each test can see, and what it cannot
//!
//! * [`the_day_file_the_json_and_tm_now_print_one_row_list`] drives the real
//!   binary, so it sees the whole stack. It cannot see a surface it does not
//!   run: `tm tui` needs a tty (README gap **182**).
//! * [`the_tui_timeline_is_the_day_files_lines`] stands in for that surface at
//!   the library level. It is close to tautological *by construction* — both
//!   sides call `emit::day_lines` — and that is what single ownership means; what
//!   it actually guards is the **wiring**, which is the thing that regresses.
//! * [`exactly_one_function_composes_a_plan_row`] is the grep §8.3's last line
//!   asks for. Without it the three byte-equality assertions do not keep G1
//!   dead: a future private stand-in renderer reintroduces it and they all still
//!   pass, because they compare surfaces that both call the new one.
//!
//! # The guard was driven RED on its own class before it was kept
//!
//! W-22 shipped a brand-new guard that reported green on two instances of the
//! class it was written for, so five stand-in renderers were planted here and
//! the result of each is recorded rather than assumed:
//!
//! | plant | caught by |
//! |---|---|
//! | `fn day_line_for` in `cli/render.rs` calling `title_cell` **and** `mark_of` | [`exactly_one_function_composes_a_plan_row`] |
//! | `fn seg_title` restored verbatim in `tui/today.rs` | [`no_second_set_of_row_words`] **and** [`the_one_renderer_is_still_there`] |
//! | `let t = emit::title_cell;` aliased **inside** the function | [`exactly_one_function_composes_a_plan_row`] |
//! | `use emit::{title_cell as tc, mark_of as mo}` at file scope | [`exactly_one_function_composes_a_plan_row`], in the `<file>` bucket |
//! | `fn compact_row` naming **one** cell and writing the rest with `format!` | **NOTHING. It walked through, and it is the declared hole** |
//!
//! The last one is not fixable by tightening this needle: `tui/today.rs`'s
//! legitimate `next 11:20 lunch 30m · …` line has exactly that shape, so "one
//! cell plus a format string" cannot be the rule. What stops the hole widening
//! is `one_padder.rs`: a stand-in that lays out *columns* has to measure and
//! pad, and nothing outside `emit.rs` may.
//!
//! # The walk this file reads with was a SECOND COPY, and it had diverged
//!
//! `sources` and `code_lines` lived here and in `one_padder.rs` — one walk
//! written twice, inside the two guards that exist to enforce AGENTS §5.3 —
//! and the copies were **not equivalent**: this one never got README gap
//! 1201's char-literal rule, so a `&'static str` opened a quote that never
//! closed and the `//` comment behind it was scanned as code. DRIVEN at the
//! W-24 repair step: one line appended to `tm/src/cli/day.rs` put
//! [`no_second_set_of_row_words`] RED on a comment while `one_padder` stayed
//! green. Both now import `tests/support/srcwalk.rs`, whose header carries the
//! transcript and the blind-spot sentence this file used to carry alone
//! (README gap **1419**).

mod cli_common;
#[path = "support/srcwalk.rs"]
mod srcwalk;
mod tui_common;

use cli_common::Tm;
use srcwalk::{code_lines, sources};

// ---------------------------------------------------------------------------
// The four surfaces
// ---------------------------------------------------------------------------

/// A line of `tm now` that is a **row**: §4.3's row opens with `HH:MM`.
///
/// `tm now`'s own chrome cannot be mistaken for one — `nothing running`, the
/// `▶ id title · started …` active line, `next`, the two-space-indented
/// `HH:MM–HH:MM · elapsed …` annotation and the trailing `N/M blocks` (which
/// starts with a digit but is not a clock).
fn is_row(line: &str) -> bool {
    let b = line.as_bytes();
    b.len() >= 5
        && b[0].is_ascii_digit()
        && b[1].is_ascii_digit()
        && b[2] == b':'
        && b[3].is_ascii_digit()
        && b[4].is_ascii_digit()
}

/// The `<!-- tm:plan … -->` block of a day file, line by line.
fn plan_block(day: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut inside = false;
    for line in day.lines() {
        if line.starts_with("<!-- tm:plan start") {
            inside = true;
            continue;
        }
        if line.starts_with("<!-- tm:plan end") {
            inside = false;
            continue;
        }
        if inside {
            out.push(line.to_string());
        }
    }
    assert!(!out.is_empty(), "the day file has no plan block:\n{day}");
    out
}

/// **D30 Q5 (a), on the shipped binary.** The day file, `tm plan --json` and
/// `tm now` print one row list.
///
/// Three assertions, in the order §8.3 states them, all **indexed by
/// position**:
///
/// 1. every `segments[i].text` is the day file's line for segment `i`, byte for
///    byte, with the `─── window ends` divider as the only line the file has and
///    the JSON has not;
/// 2. every row `tm now` prints is one of those, at its own position;
/// 3. `tm now`'s rows are a **contiguous** run of them.
#[test]
fn the_day_file_the_json_and_tm_now_print_one_row_list() {
    let now = "2026-09-07T10:42:00-05:00";
    let tm = Tm::new();
    tm.ok_at(now, &["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at(now, &["arrive", "lounge"]);
    tm.ok_at(now, &["plan"]);

    let json = tm.json_at(now, &["plan"]);
    let texts: Vec<String> = json["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .map(|s| s["text"].as_str().expect("segments[].text").to_string())
        .collect();
    assert!(texts.len() > 5, "a day worth comparing: {}", texts.len());

    // (1) The file is the JSON's rows with the divider spliced in.
    let file = plan_block(&tm.read("day/2026-09-07.md"));
    let mut j = 0usize;
    let mut dividers = 0usize;
    for line in &file {
        if j < texts.len() && *line == texts[j] {
            j += 1;
        } else {
            assert!(
                line.contains("window ends"),
                "the day file holds a line `tm plan --json` does not, and it is \
                 not the divider:\n  file: {line:?}\n  json[{j}]: {:?}",
                texts.get(j)
            );
            dividers += 1;
        }
    }
    assert_eq!(j, texts.len(), "the file dropped a row the JSON has");
    assert!(dividers <= 1, "{dividers} divider rows in one day");
    assert_eq!(file.len(), texts.len() + dividers);

    // (2) and (3) `tm now` selects from that list, contiguously.
    let out = tm.ok_at(now, &["now"]).stdout;
    let printed: Vec<&str> = out.lines().filter(|l| is_row(l)).collect();
    assert!(
        (1..=4).contains(&printed.len()),
        "§13 is the current block and the next three, got {}:\n{out}",
        printed.len()
    );
    let starts: Vec<usize> = (0..=texts.len().saturating_sub(printed.len()))
        .filter(|k| texts[*k..*k + printed.len()] == printed[..])
        .collect();
    assert_eq!(
        starts.len(),
        1,
        "`tm now`'s rows are not a contiguous run of the day's rows, or the run \
         has more than one witness (README gap 1197 — then the position is the \
         answer and the text cannot supply it):\n  now: {printed:#?}\n  day: \
         {texts:#?}"
    );

    // And none of `tm now`'s chrome is a row, so (2) is not vacuous.
    assert!(out.contains("nothing running"), "{out}");
    assert!(
        out.lines().any(|l| l.starts_with("  ") && l.contains("elapsed")),
        "the elapsed annotation is indented and is not a row:\n{out}"
    );
    assert!(out.lines().any(|l| l == "next"), "{out}");
}

/// **`tm now` and `tm now --json` select the same rows.**
///
/// They did not until W-23. "The current block and the next three" (§13) had
/// **three** implementations in the tree and no two agreed:
///
/// | | current | next three |
/// |---|---|---|
/// | `emit::render_now_with` | `flags.current` **and** `start ≤ now < end`, else the first unfinished row over `now` | `start ≥ now`, the current one excluded |
/// | `cli/planning.rs::now` (the JSON) | the first row over `now`, marked or not, done or not | `start > now`, **Sleep hidden** |
/// | `tui/today.rs::current_segment` | `flags.current` **anywhere in the day** — no time guard at all | `start > now`, **Sleep hidden** |
///
/// The third was a defect and not a difference: a `▶` the planner left on a
/// block that has since ended kept the Now pane on it, elapsed bar and all. The
/// TUI fixture at 12:51 showed `Exercises 5.3–5.5`, which ran 09:32–12:50, with
/// `elapsed 3h19m`; it now shows the meeting that actually contains 12:51.
///
/// **The head moved and the line under it did NOT, which was a second defect**
/// (README gap **1315**, the W-23 repair step). `App::active_elapsed_min` is a
/// fact about `state.active` — the running *item* — so the pane shipped
/// `ci3 Meeting w/ host` over `elapsed 3h19m ▐███████████████▌`: the previous
/// block's run, drawn full against a 1h meeting, while the overtime prompt in
/// the same snapshot correctly said `Exercises 5.3–5.5 … elapsed 3h19m`. The
/// elapsed is now the head's own segment's unless the head IS the running
/// block, and the snapshot reads `elapsed 1m ▐░░░░░░░░░░░░░░░▌`.
///
/// The rule that survives is `emit::now_window`'s, and **hiding a kind is what
/// decided it**: D30 Q5 (a) asks for `tm now`'s rows to be a *contiguous*
/// sub-list of the file's, and a `next` that skips Sleep cannot be one.
#[test]
fn tm_now_and_tm_now_json_select_the_same_rows() {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T10:42:00-05:00", &["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T10:42:00-05:00", &["arrive", "lounge"]);

    // **21:40 is the instant that made this test worth writing.** Only sleep is
    // left of the day, and the JSON's `next` hid Sleep, so it answered `[]`
    // where the text printed the row. At 10:42 the three rules happen to agree
    // and the test would have been green on the tree that had the defect —
    // which is the failure mode this campaign keeps finding, so both instants
    // are here and the late one is the one that bites.
    for (now, want_rows) in [("2026-09-07T10:42:00-05:00", 4), ("2026-09-07T21:40:00-05:00", 1)] {
        let json = tm.json_at(now, &["now"]);
        let mut want: Vec<String> = Vec::new();
        if let Some(c) = json["current"].as_object() {
            want.push(c["text"].as_str().expect("current.text").to_string());
        }
        for n in json["next"].as_array().expect("next") {
            want.push(n["text"].as_str().expect("next[].text").to_string());
        }
        assert_eq!(want.len(), want_rows, "§13, at {now}: {want:#?}");

        let out = tm.ok_at(now, &["now"]).stdout;
        let printed: Vec<String> =
            out.lines().filter(|l| is_row(l)).map(String::from).collect();
        assert_eq!(printed, want, "the two `tm now`s chose different rows at {now}");
    }
}

/// **The TUI's Timeline is the day file's lines**, at the same [`Layout`].
///
/// `App::timeline_rows` and `emit::render_plan_section_with` both go through
/// `emit::day_lines`, so this is a **wiring** check rather than an independent
/// measurement — that is what "one renderer" buys, and it is stated here rather
/// than left to be discovered. What it catches is the TUI growing its own path
/// back, which is exactly how G1 was born.
///
/// `tm tui` itself is not driven: it exits when stdout is not a tty (README gap
/// **182**).
///
/// [`Layout`]: tm_core::emit::Layout
#[test]
fn the_tui_timeline_is_the_day_files_lines() {
    let app = tui_common::app();
    let w = tm_core::emit::DEFAULT_TITLE_W;
    let rows = app.timeline_rows(w);
    let (_, body) = tm_core::emit::render_plan_section_with(
        &app.plan,
        &app.tree,
        &app.cfg,
        app.now,
        &tm_core::emit::Layout::new(w),
    );
    let file: Vec<&str> = body.lines().collect();
    assert_eq!(rows.len(), file.len(), "the pane and the file differ in length");
    for (i, (row, line)) in rows.iter().zip(&file).enumerate() {
        assert_eq!(&row.text, line, "row {i} is not the file's line");
    }
    // And the provenance is an index into `segments`, in order, with the
    // divider the only line that has none.
    let mut want = 0usize;
    for row in &rows {
        match row.segment {
            Some(i) => {
                assert_eq!(i, want, "the rows are not in segment order");
                want += 1;
            }
            None => assert!(row.text.contains("window ends"), "{}", row.text),
        }
    }
    assert_eq!(want, app.plan.segments.len(), "a segment drew no row");
}

/// **README gap 1197, constructed rather than argued.**
///
/// The gap says two items with one title "produce day rows that differ only in
/// their start time". They can differ in nothing at all: two segments may start
/// at the same instant, and then the two rows are byte-identical and a sub-list
/// found *by value* has more than one witness. `emit::now_window` answers
/// **positions** for exactly this reason.
#[test]
fn byte_identical_rows_are_constructible_so_position_decides() {
    use tm_core::emit;
    use tm_core::planner::{DayPlan, SegKind};

    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let plan = tui_common::day_plan(&cfg);
    let twin = plan
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Routine) && s.item.is_some())
        .expect("a routine row to clone")
        .clone();

    let mut day = DayPlan::empty(plan.date, plan.window, plan.budget_blocks);
    day.segments = vec![twin.clone(), twin];

    let rows = emit::plan_rows(&day, &tree, &cfg, &emit::Layout::default());
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0], rows[1], "the two rows were supposed to be identical");

    // A by-value sub-list search has two witnesses here; a position has one.
    let by_value: Vec<usize> = rows
        .iter()
        .enumerate()
        .filter(|(_, r)| **r == rows[0])
        .map(|(i, _)| i)
        .collect();
    assert_eq!(by_value, vec![0, 1], "the ambiguity is the point");

    let (current, next) = emit::now_window(&day, day.segments[0].start);
    assert_eq!(current, Some(0), "the FIRST of the two is the one running");
    assert_eq!(next, vec![1], "and the twin is the next one, by position");
    // The whole point: the two answers are 0 and 1 and the two texts are equal,
    // so a caller that matched `tm now`'s output back to a segment by looking
    // for the row it says would land on 0 for both.
    assert_eq!(rows[current.expect("a current row")], rows[next[0]]);
    // And `day_lines` hands each row its own index, equal text or not.
    let lines = emit::day_lines(&day, &tree, &cfg, &emit::Layout::default());
    let segs: Vec<Option<usize>> = lines.iter().map(|l| l.segment).collect();
    assert!(
        segs.windows(2).all(|w| w[0] != w[1]),
        "two lines claim one segment: {segs:?}"
    );
}

// ---------------------------------------------------------------------------
// The grep guard (design §8.3's last line)
// ---------------------------------------------------------------------------

/// The one file allowed to compose a §4.3 row.
const HOME: &str = "tm-core/src/emit.rs";

/// The cell producers of §4.3's row. A function that names **two or more** of
/// them is composing a row out of cells, and there is exactly one of those.
///
/// One is fine and deliberate: `tm/src/tui/today.rs`'s Now pane takes
/// `emit::title_cell` (that is what killed seg_title) and
/// `tm/src/cli/render.rs::rows` takes `emit::mark_of` for the JSON's `mark`
/// field. Neither is laying out a row.
const CELLS: &[&str] = &[
    "title_cell",
    "est_cell",
    "parent_cell",
    "note_cell",
    "mark_of",
    "glyph_of",
    "batch_names",
    "fit_batch",
    "underused_note",
    "hot_note",
];

/// `(function name, first line, its code lines)` for each `fn` in a file.
///
/// A crude splitter, declared as such: it starts a bucket at every `fn`
/// declaration and runs it to the next one, so a nested `fn` closes its parent
/// early and a closure inside a function belongs to that function. What it
/// cannot see at all is a function assembled by a macro. Everything before the
/// first `fn` is the file's own scope, under the name `<file>`.
fn functions(text: &str) -> Vec<(String, usize, Vec<String>)> {
    let mut out: Vec<(String, usize, Vec<String>)> = vec![("<file>".to_string(), 1, Vec::new())];
    for (n, code) in code_lines(text) {
        let t = code.trim_start();
        let name = t
            .strip_prefix("pub(crate) fn ")
            .or_else(|| t.strip_prefix("pub fn "))
            .or_else(|| t.strip_prefix("fn "))
            .map(|rest| {
                rest.chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect::<String>()
            });
        if let Some(name) = name {
            out.push((name, n, Vec::new()));
        }
        out.last_mut().expect("a bucket").2.push(code);
    }
    out
}

/// **One row renderer.** Nothing outside [`HOME`] names two or more of the
/// row's cells in one function.
///
/// This is the shape, not a vocabulary: a stand-in renderer under any name is
/// caught, because it has to *have* the cells. It is the second half of
/// `one_padder.rs`'s guard — that one says nothing outside `emit.rs` measures or
/// pads a column, this one says nothing outside it puts cells side by side — and
/// together they are what keeps G1 dead.
///
/// **What it cannot see**, measured rather than assumed:
///
/// * a renderer that names **one** cell and writes the rest with `format!`.
///   `tm/src/tui/today.rs`'s `next 11:20 lunch 30m · …` line is exactly that
///   shape and is legitimate, so the needle cannot be "one"; a hostile version
///   of it is invisible here and is caught, if at all, by
///   [`no_second_set_of_row_words`].
/// * a renderer in `tests/`, `examples/` or `build.rs` (the walk is two `src`
///   trees), or one assembled by a macro (the splitter reads text).
/// * a renderer that reaches the cells through a re-export under another name.
#[test]
fn exactly_one_function_composes_a_plan_row() {
    let mut hits = Vec::new();
    for (name, text) in sources() {
        if name == HOME {
            continue;
        }
        for (f, line, body) in functions(&text) {
            let used: Vec<&str> = CELLS
                .iter()
                .copied()
                .filter(|c| body.iter().any(|l| l.contains(c)))
                .collect();
            if used.len() >= 2 {
                hits.push(format!("{name}:{line}: fn {f} composes {}", used.join(" + ")));
            }
        }
    }
    assert!(
        hits.is_empty(),
        "a second row renderer (PLAN §4 G1, D30 Q5 (a): there is one, and it is \
         `{HOME}`'s `render_row`):\n  {}",
        hits.join("\n  ")
    );
}

/// The **row's own words** paired with the kind they are written for: a `match`
/// on `SegKind` that answers text. `emit::title_cell` is the one that may.
///
/// This is a **vocabulary** and a vocabulary is one rename away from useless
/// (README gap **1193** is the lesson). It is here because the shape needle
/// above cannot see a second renderer of a *single* cell, which is exactly what
/// seg_title was: ten `SegKind` arms and not one call into `emit`.
const KIND_WORDS: &str = "SegKind::";

/// The `SegKind`-arms-with-text outside [`HOME`] that are **not** display cells
/// — exact lines, each adjudicated, and every entry must still be found or this
/// test fails (check 8's "0 allow entries unused" rule).
const WORD_ALLOW: &[(&str, &str)] = &[
    ("tm-core/src/planner.rs", r#"SegKind::Block => "block","#),
    ("tm-core/src/planner.rs", r#"SegKind::Batch(_) => "batch","#),
    ("tm-core/src/planner.rs", r#"SegKind::Break => "break","#),
    ("tm-core/src/planner.rs", r#"SegKind::Routine => "routine","#),
    ("tm-core/src/planner.rs", r#"SegKind::Wall => "wall","#),
    ("tm-core/src/planner.rs", r#"SegKind::Rest => "rest","#),
    ("tm-core/src/planner.rs", r#"SegKind::Optional => "optional","#),
    ("tm-core/src/planner.rs", r#"SegKind::WindDown => "wind-down","#),
    ("tm-core/src/planner.rs", r#"SegKind::Sleep => "sleep","#),
    ("tm-core/src/planner.rs", r#"SegKind::Lost => "lost","#),
];

/// **One title renderer.** Nothing outside [`HOME`] turns a `SegKind` into
/// words, except `planner::kind_label`'s ten — the **wire** word the `--json`
/// `kind` field and `.tm/last_plan.json` use, which is not a cell and is not
/// padded, truncated or printed in a column.
///
/// `tm/src/cli/render.rs::kind_name` held a byte-for-byte copy of those ten arms
/// until W-23 (AGENTS §5.3: two definitions of one concept is the bug); it was
/// deleted and its two callers take `planner::kind_label`. Finding it is what
/// this needle was measured on.
#[test]
fn no_second_set_of_row_words() {
    let mut hits: Vec<(String, String, usize)> = Vec::new();
    for (name, text) in sources() {
        if name == HOME {
            continue;
        }
        for (n, line) in code_lines(&text) {
            if line.contains(KIND_WORDS) && line.contains('"') {
                hits.push((name.clone(), line.trim().to_string(), n));
            }
        }
    }
    let mut strays = Vec::new();
    let mut used = vec![0usize; WORD_ALLOW.len()];
    for (file, code, n) in &hits {
        match WORD_ALLOW
            .iter()
            .position(|(f, c)| *f == file.as_str() && *c == code.as_str())
        {
            Some(i) => used[i] += 1,
            None => strays.push(format!("{file}:{n}: {code}")),
        }
    }
    assert!(
        strays.is_empty(),
        "a second renderer of the title cell (G1 — `{HOME}`'s `title_cell` is \
         the one; if this is a wire word and not a cell, adjudicate it into \
         WORD_ALLOW by its exact line):\n  {}",
        strays.join("\n  ")
    );
    let unused: Vec<&str> = WORD_ALLOW
        .iter()
        .zip(&used)
        .filter(|(_, n)| **n == 0)
        .map(|((_, c), _)| *c)
        .collect();
    assert!(
        unused.is_empty(),
        "WORD_ALLOW entries nobody needs any more — delete them rather than \
         leave a free exemption open:\n  {}",
        unused.join("\n  ")
    );
}

/// The file allowed to build an `HH:MM` by hand: the row's **time** cell is one
/// of the nine, and `planner::fmt_clock`'s own doc comment calls it "one §4.3
/// timeline row's leading `HH:MM`". `Emit.lean`'s header names it as the Rust
/// half of the kernel's one clock, beside `Field.renderClock`.
const CLOCK_HOME: &str = "tm-core/src/planner.rs";

/// **One clock, hand-rolled.** Nothing but [`CLOCK_HOME`] writes
/// `format!("{:02}:{:02}", …)`.
///
/// **Eight functions in this repository rendered `HH:MM`** until W-23, found by
/// body shape rather than by name — five taking a `DateTime<Tz>`
/// (`planner::fmt_clock`, and copies in `emit.rs`, `cli/render.rs`,
/// `cli/planning.rs` and `cli/day.rs`, all four called `hhmm`) and three taking a
/// `NaiveTime` (`model::fmt_time`, a byte-for-byte copy in `cli/out.rs`, and
/// `cli/kernel_capacity.rs`'s own `hhmm`). All eight produced identical bytes,
/// which is what made them invisible: nothing could ever fail.
///
/// Six are gone. `fmt_clock` and `model::fmt_time` are the two that survive —
/// two because the input types are two, and neither can be written in terms of
/// the other without a zone.
///
/// **What this needle cannot see**, measured rather than assumed:
/// `.format("%H:%M")` is the same cell spelled with chrono's formatter and there
/// are **15** of those, in `tui/today.rs`, `tui/daybar.rs`, `cli/dayfile.rs`,
/// `cli/ctx.rs`, `planner.rs`, `check.rs`, `review.rs`, `model.rs` and
/// `config.rs`. They are not all this cell — a day-bar cursor label and a review
/// window line are not §4.3 rows — so unifying them is a judgement this step did
/// not take. README gap **1214**.
#[test]
fn exactly_one_function_renders_a_clock_by_hand() {
    let mut hits = Vec::new();
    for (name, text) in sources() {
        if name == CLOCK_HOME {
            continue;
        }
        for (n, line) in code_lines(&text) {
            // `{:02}:{:02}:{:02}` is a UTC **offset** (`cli/tz_table.rs`'s
            // `fmt_offset`, `±HH:MM:SS`), a different arity and a different
            // concept — excluded by shape, not by an allow-list entry.
            if line.contains(r#"{:02}:{:02}"#) && !line.contains(r#"{:02}:{:02}:{:02}"#) {
                hits.push(format!("{name}:{n}: {}", line.trim()));
            }
        }
    }
    assert!(
        hits.is_empty(),
        "a second hand-rolled clock (AGENTS §5.3 — there is one, and it is          `{CLOCK_HOME}`'s `fmt_clock`):\n  {}",
        hits.join("\n  ")
    );
    // And the home file still has it, so this cannot pass by deletion.
    let (_, planner) = sources()
        .into_iter()
        .find(|(n, _)| n == CLOCK_HOME)
        .expect("tm-core/src/planner.rs");
    assert!(planner.contains("pub fn fmt_clock("), "the one clock is gone");
}

/// **The home file still holds the renderer**, so neither grep can pass by the
/// renderer having been deleted rather than unified — `one_padder.rs`'s
/// `the_one_table_is_still_there`, for rows.
#[test]
fn the_one_renderer_is_still_there() {
    let files = sources();
    let (_, emit) = files
        .iter()
        .find(|(n, _)| n == HOME)
        .expect("tm-core/src/emit.rs");
    assert!(emit.contains("fn render_row("), "the row renderer is gone");
    assert!(emit.contains("pub fn plan_rows("), "the row list is gone");
    assert!(emit.contains("pub fn day_lines("), "the day's lines are gone");
    // And the two surfaces that used to render take the list instead.
    for (needle, why) in [
        ("plan_rows(plan, tree, cfg, &Layout::default())", "`tm now` selects"),
        ("let rows = plan_rows(plan, tree, cfg, layout);", "`day_lines` maps"),
    ] {
        assert!(emit.contains(needle), "{why}: `{needle}` is gone");
    }
    let (_, today) = files
        .iter()
        .find(|(n, _)| n == "tm/src/tui/today.rs")
        .expect("tm/src/tui/today.rs");
    assert!(
        today.contains("emit::title_cell("),
        "the TUI stopped taking the one title cell"
    );
    assert!(
        !today.contains("fn seg_title"),
        "the second title renderer came back"
    );
}
