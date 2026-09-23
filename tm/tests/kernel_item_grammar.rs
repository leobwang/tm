//! **The item-grammar proptest, aimed at the KERNEL** (stage 6 design
//! `kernel/design/stage6/stage6-planner-design.md` §7.3 and §14.4 row **R2**;
//! stage 6 **W-25**).
//!
//! `tm-core/tests/grammar_proptest.rs` has drawn random item lines since the
//! fork point and asked whether **the fork's two readers** — `parse_line` and
//! `ItemLine` — agree with each other. It never touched the kernel. §14.4's R2
//! says the proptest is aimed **through the FFI**, so this file draws the *same*
//! lines from the *same* generator (`tm-core/tests/grammar_common/mod.rs` — one
//! definition, AGENTS §5.3) and asks a different question: **does `Line.lean`
//! read the line the way the fork reads it?**
//!
//! # How the kernel is asked
//!
//! Every arm sends the line to `tm_kernel_ffi::call` inside one document and
//! reads `ok.docs[0].lines`, which is the kernel's **own re-render of its own
//! parse** (`Boundary.runPlan`, `runPlan_renders_the_input`). The Rust never
//! tells the kernel where a token is, what the title is or which slot an
//! estimate lives in; the request is the line's bytes.
//!
//! A boxed line is sent in `week/2026-W37.md` under `# Tasks`; a **boxless**
//! line is sent in `inbox.md`, which is §4.1's third box-less file. The fork's
//! own proptest uses `routines.md` for its box-less lines, and this file does
//! **not**: §4.3's routines shape (`win:`/`every:`/`after-done:`) is checked by
//! the kernel's `Plan.shapeWfFor` and by nothing in `parse_line`, so nearly
//! every drawn line would come back `itemCheck: fileKindShape` and the box-less
//! half would be a check no input can pass (AGENTS §9.2's named shape).
//! `inbox.md` carries no shape rule, and **both** readers are given that same
//! path, so it is one file with two readers and not two files.
//!
//! # The arms
//!
//! * [`the_kernel_round_trips_every_line_the_fork_round_trips`] — the fork's
//!   `parse_serialize_is_byte_identical` with a third reader in it.
//! * [`the_two_readers_agree_on_which_lines_are_items`] — **cheats 122 and 123,
//!   pinned by machine for the first time.** The kernel reads `-  [ ] A ^a1`
//!   (two spaces) and `- <TAB>[ ] …` as **prose**; the fork reads them as items.
//!   This arm asserts the divergence is *exactly* that class and nothing wider.
//! * [`the_two_editors_write_the_same_drop`] — the kernel's `drop` op against
//!   `ItemLine::set_state(State::Dropped)`, the fork's own editor for the verb
//!   (`tm-core/src/horizon.rs:1285`), byte for byte — and, on a box-less line,
//!   the D31/K3a refusal where the fork would have written a box.
//! * [`the_two_editors_write_the_same_keyed_edit`] — the kernel's `edit` op
//!   against `ItemLine::set_token`, over the keys `tm edit` wires to the kernel.
//! * [`no_line_faults_the_kernel`] — free-form bytes: the kernel answers, and
//!   an `ok` answer is byte-identical to the input.
//!
//! # What it cannot see
//!
//! * **One line, one document.** The loader's cross-line work — collisions,
//!   ranks, sections — is `check_fix_ids.rs`' and `cli_check_log.rs`' ground,
//!   not this file's. It is why `danglingDep` and `danglingParent` are declared
//!   rather than compared: in a one-line document every `after:` and `@parent`
//!   dangles, and the fork's `parse_line` resolves neither.
//! * **A refusal is compared by CLASS, never by message.** Where the kernel
//!   refuses and the fork does not, this file records which class and why; it
//!   does not assert a matching fork diagnostic, because on most of these
//!   classes the fork produces none — which is the kernel's point (§5.7).
//! * **[`kernel_reads_as_item`] is a RESTATEMENT of `Line.parseBody` in Rust**,
//!   and AGENTS §5.3 is right that a second statement of one rule is a hazard.
//!   It is kept because the alternative is no assertion at all about the cheats'
//!   boundary, and it is pinned in both directions on every draw: a kernel that
//!   widens *or* narrows what it reads as an item fails this file immediately.
//! * **Tabs are out of the item-ness arm's reach** (gap 32's `tabbedLine` guard
//!   and cheat 122 between them), and the arm says so where it assumes them
//!   away. Every other arm still draws them.
//! * **No binary is driven**, so nothing here sees the CLI's own choice between
//!   its kernel path and its Rust path for a verb — README gap **1430** is about
//!   exactly that and was found from this file's evidence, not by this file.

/// The generator module, shared with `tm-core/tests/grammar_proptest.rs`. Not
/// every strategy in it is drawn here — the fork test's `ctx_for` and
/// `without_src` are its own — and that is the point of sharing rather than
/// copying: the file is one, the readers are two.
#[allow(dead_code)]
#[path = "../../tm-core/tests/grammar_common/mod.rs"]
mod grammar_common;

use std::collections::BTreeMap;
use std::sync::Mutex;

use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::grammar::{parse_line, ItemLine, ParseCtx};
use tm_core::model::{Id, State};

use grammar_common::line;

/// The week file a **boxed** line is sent in, with the region
/// `kernel_bridge::region_of` gives it (gap 10's host half), and the heading
/// §4.3 puts week items under. Hard-coded rather than computed: `region_of`
/// lives in the binary crate behind `Horizon`, and three test files already pin
/// this exact pair.
const WEEK: (&str, u64, u64) = ("week/2026-W37.md", 1, 105_695);

/// The file a **box-less** line is sent in (see the module header).
const INBOX: &str = "inbox.md";

/// The id appended to a line that carries none, by the fork's own
/// `ItemLine::append_id` — the fork proptest's `append_id_sets_id` uses the same
/// editor. A boxed line with no `^id` is refused `noId` by the kernel (README:
/// "no `^id` on a **bare** line → the title key"), so without this the editing
/// arms would be about whichever draws happened to carry an id token.
const APPENDED: &str = "q9x2";

/// **Every refusal these arms are allowed to see, with the reason it is not a
/// bug.** A refusal outside this list fails the arm that saw it.
const DECLARED_REFUSALS: &[(&str, &str)] = &[
    (
        "manyIds",
        "Two `^id`s on one line: `Line.PErr.manyIds`. The fork's `ItemLine` \
         keeps both. This is the corpus's own long-standing divergence — the \
         eight `plan-conflicts` files are refused for it — and it is a REFUSAL, \
         not a wrong answer.",
    ),
    (
        "noId",
        "A boxed line with no `^id`. The title key is the box-less line's key, \
         not the boxed line's, so the kernel refuses rather than invent one \
         (§5.6). The fork keys every line on `Id(title)`.",
    ),
    (
        "danglingDep",
        "`after:^zz9` names an id no line in this ONE-LINE document carries. \
         The fork's `parse_line` does not resolve deps at all: resolution is the \
         tree's, and this document is the tree here.",
    ),
    (
        "danglingParent",
        "`@m1` names a parent no line in this one-line document carries. Same \
         reason as `danglingDep`.",
    ),
    (
        "parentCycle",
        "`- a ^o @o` — the line is its own parent. The kernel's tree check names \
         it; the fork's `parse_line` resolves no parents at all. The same \
         one-line-document family as `danglingParent`, found at 50,000 cases and \
         not before.",
    ),
    (
        "depCycle",
        "`- [ ] A ^s after:^s` — the line depends on itself. Same family, same \
         draw depth.",
    ),
    (
        "badState",
        "A box whose glyph is not one of `Glyph.ofChar?`'s six. Only \
         `no_line_faults_the_kernel` draws these; the generator's `state()` \
         draws the six.",
    ),
    (
        "noSuchId",
        "The command's id is not a live key. On a generated line this means the \
         kernel read the line as PROSE where the fork read an item — cheats 122 \
         and 123 — and `the_two_readers_agree_on_which_lines_are_items` is the \
         arm that pins that class exactly rather than tolerating it.",
    ),
    (
        "badHorizon",
        "`drop` would put a `[~]` box on a BOX-LESS line. `Plan.boxWf` (D31, \
         K3a) refuses the post-state: a box-less line's bytes carry no box, so \
         `serializeItem` would write the line back unchanged and the status \
         would vanish on the next read. The fork's `ItemLine::set_state` writes \
         the box in. `the_two_editors_write_the_same_drop` asserts this refusal \
         rather than skipping it.",
    ),
    (
        "tabbedLine",
        "**Gap 32's guard**: `Cmd.editE`/`unsetE` refuse a line carrying a tab \
         anywhere in its raw bytes, whatever the key and value \
         (`editE_refuses_a_tabbed_line`). The fork's `set_token` writes into it. \
         The guard fires BEFORE item-ness is reached, so a tabbed line teaches \
         `the_two_readers_agree_on_which_lines_are_items` nothing and that is \
         why the arm ends on a declared refusal rather than concluding.",
    ),
    (
        "fileKindShape",
        "§4.3's per-file shape rule (`Plan.shapeWfFor`). Reachable only from \
         `zz_the_declared_refusals_are_all_reachable`'s `routines.md` probe; the \
         arms use `inbox.md`, which carries no shape rule (module header).",
    ),
];

/// One kernel answer: the document's lines, or the refusal's class name.
#[derive(Debug, Clone, PartialEq)]
enum Kernel {
    Lines(Vec<String>),
    Refused(String),
}

/// Every refusal any arm has seen, with how many times — read by
/// [`zz_the_declared_refusals_are_all_reachable`]. A proptest case body returns
/// only a verdict, so the census is a side channel.
static SEEN: Mutex<Option<BTreeMap<String, u64>>> = Mutex::new(None);

fn note_refusal(what: &str) {
    let mut g = SEEN.lock().expect("census");
    *g.get_or_insert_with(BTreeMap::new).entry(what.to_string()).or_insert(0) += 1;
}

/// **The DENOMINATOR: per arm, how many cases actually compared bytes.**
///
/// `[drawn, addressable, compared]`. Three of the arms open with
///
/// ```ignore
/// let Some((addressed, id)) = addressable(&text) else { return Ok(()) };
/// ```
///
/// which is a silent **pass** and not a `prop_assume!`, so it is charged to
/// neither `max_global_rejects` nor any count; and every arm's
/// `Kernel::Refused(name) => prop_assert!(declared(&name))` branch passes
/// without comparing a byte. "Every cell agreed" is a sentence a fuzz comparing
/// NOTHING also produces — AGENTS §9.2's "a check no input can fail" — and the
/// refusal census below is per **class**, not per arm, so it could not answer
/// how many cases of any one arm reached a comparison. The sibling file
/// `tm/tests/planner_invariants.rs` grew the same floor for the same reason.
///
/// It is read **inside the arm that fills it**, on every case, and not by a
/// separate `#[test]`: a separate test would race the arms in cargo's default
/// parallel run and pass by seeing nothing, which is the very defect it exists
/// to catch.
static COMPARED: Mutex<Option<BTreeMap<&'static str, [u64; 3]>>> = Mutex::new(None);

/// Record one case of `arm`, and return that arm's running totals.
///
/// `reached` is how far the case got: 0 drawn only, 1 addressable, 2 compared.
fn note_case(arm: &'static str, reached: usize) -> [u64; 3] {
    let mut g = COMPARED.lock().expect("census");
    let row = g.get_or_insert_with(BTreeMap::new).entry(arm).or_insert([0; 3]);
    for slot in row.iter_mut().take(reached + 1) {
        *slot += 1;
    }
    *row
}

/// **The floor, asserted inside the arm.** Once an arm has drawn `FLOOR_AFTER`
/// cases it must have compared at least `FLOOR_NUM/FLOOR_DEN` of them.
///
/// The rate is not a guess: the generator puts `""`, `" "` or `"\t"` between the
/// bullet and the box with equal weight, so two draws in three are cheat
/// 122/123's class and the editing arms assume them away. MEASURED at
/// `TM_PROPTEST_CASES=4096`, `--test-threads=1 --nocapture`, from the census
/// this file prints — `[drawn, addressable, compared]`:
///
/// ```text
/// the_two_editors_write_the_same_drop            [8176, 4104, 1561]   19.1%
/// the_two_editors_write_the_same_keyed_edit      [8344, 4104, 2064]   24.7%
/// the_two_readers_agree_on_which_lines_are_items [9924, 4104, 3656]   36.8%
/// ```
///
/// `drawn` exceeds `cases` because a rejected case is re-drawn. One in ten is
/// the floor — about half the lowest measured rate: loose enough that a
/// generator reweighting does not turn this into a flake, tight enough that an
/// arm which has stopped comparing fails. §5.11: re-measure, do not quote.
const FLOOR_AFTER: u64 = 64;
const FLOOR_NUM: u64 = 1;
const FLOOR_DEN: u64 = 10;

fn floor_holds(row: [u64; 3]) -> bool {
    let [drawn, _, compared] = row;
    drawn < FLOOR_AFTER || compared * FLOOR_DEN >= drawn * FLOOR_NUM
}

/// **The refusal, flattened to the name the kernel chose.**
///
/// `{"err":{"itemCheck":"danglingDep"}}` is `danglingDep`;
/// `{"err":{"kernel":"noSuchId"}}` is `noSuchId`;
/// `{"err":{"badLine":{…,"why":"Tm.PErr.badState '@'"}}}` is `badState`.
/// Anything else keeps its whole shape, so an unnamed refusal can never be
/// mistaken for a named one.
fn refusal_name(err: &Value) -> String {
    for key in ["itemCheck", "kernel"] {
        if let Some(s) = err.get(key).and_then(Value::as_str) {
            return s.to_string();
        }
    }
    if let Some(why) = err.get("badLine").and_then(|b| b.get("why")).and_then(Value::as_str) {
        let name = why.strip_prefix("Tm.PErr.").unwrap_or(why);
        // `badState '@'` carries the offending char; the class is the word.
        return name.split(' ').next().unwrap_or(name).to_string();
    }
    if let Some(s) = err.as_str() {
        return s.to_string();
    }
    err.to_string()
}

/// **One kernel call**: the line, in the file its box decides, with the commands
/// given. A boxed line gets `# Tasks` above it and nothing else, so the only
/// item in the document is the line under test.
fn kernel(text: &str, cmds: Value) -> Kernel {
    let doc = if fork_boxed(text) {
        json!({"path": WEEK.0, "grain": WEEK.1, "ix": WEEK.2, "lines": ["# Tasks", text]})
    } else {
        json!({"path": INBOX, "lines": [text]})
    };
    let req = json!({"docs": [doc], "cmds": cmds});
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("the kernel answered nothing at all");
    let resp: Value =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("not JSON ({e}): {raw}"));
    if let Some(err) = resp.get("err") {
        let name = refusal_name(err);
        note_refusal(&name);
        return Kernel::Refused(name);
    }
    let lines: Vec<String> = resp["ok"]["docs"][0]["lines"]
        .as_array()
        .unwrap_or_else(|| panic!("no lines in {raw}"))
        .iter()
        .map(|l| l.as_str().expect("a line is a string").to_string())
        .collect();
    Kernel::Lines(lines)
}

/// The line the kernel answered with, whichever file it went to.
fn answered<'a>(text: &str, ls: &'a [String]) -> &'a str {
    if fork_boxed(text) {
        &ls[1]
    } else {
        &ls[0]
    }
}

/// The `ParseCtx` for the file [`kernel`] sent the line to — the **same** file,
/// so the two readers are reading one document (module header).
fn ctx_of(text: &str) -> ParseCtx<'static> {
    ParseCtx::new(if fork_boxed(text) { WEEK.0 } else { INBOX }, 60)
}

/// Does the **fork** read a state box on this line? `ItemLine`'s bullet token is
/// the box when there is one, and `grammar.rs`'s `state_at` skips whitespace to
/// find it — which is the half of cheat 123 that makes the two readers differ.
fn fork_boxed(text: &str) -> bool {
    let rest = text.trim_start().strip_prefix('-').unwrap_or("").trim_start();
    let b: Vec<char> = rest.chars().take(3).collect();
    b.len() == 3 && b[0] == '[' && b[2] == ']'
}

/// Is this refusal one of the declared ones?
fn declared(name: &str) -> bool {
    DECLARED_REFUSALS.iter().any(|(n, _)| *n == name)
}

/// **`Line.parseBody`'s item-ness rule, restated over the line's bytes** — the
/// exact boundary cheats **122** and **123** record, and the thing
/// [`the_two_readers_agree_on_which_lines_are_items`] pins.
///
/// `Line.parseItem` splits the indent with `Text.isSp`, **which is a space and
/// not a tab** (cheat 122), then `parseBody` matches the literal `'-' :: ' '`;
/// a `'['` immediately after takes the boxed arm through `boxAt` (`[`, a glyph,
/// `]`), and anything else takes the bare arm, which `Field.tokBare` refuses if
/// any word carries a `'['` (cheat 123's W-15/K3a half) and `bareOk` refuses if
/// no word is left at all.
///
/// Stated in the header as a restatement, with what that costs.
fn kernel_reads_as_item(text: &str) -> bool {
    let body: String = text.chars().skip_while(|c| *c == ' ').collect();
    let Some(rest) = body.strip_prefix("- ") else { return false };
    let head: Vec<char> = rest.chars().take(3).collect();
    if head.first() == Some(&'[') {
        // The boxed arm: `boxAt` wants `[`, a char, `]`, and a glyph the kernel
        // knows. A `[` that is not a box falls through to the bare arm, which
        // `tokBare` then refuses for carrying the `[`.
        return head.len() == 3
            && head[2] == ']'
            && matches!(head[1], ' ' | '>' | 'x' | '-' | '~' | '?');
    }
    rest.chars().any(|c| c != ' ') && !rest.contains('[')
}

/// **The fork's answer with the budget key spelled the way the kernel spells
/// it** — the FIRST budget token renamed from `cap:` to `max:`, and nothing
/// else touched.
///
/// `cap` and `max` are one `Field.Key` to both readers: the fork's
/// `set_token("max", …)` updates an existing `cap:` token **in place, keeping
/// its spelling**, and the kernel's `setMax` rewrites the key as well
/// (`Line.set_max_writes_max`: *"`cap:` normalises to `max:` on write, so the
/// alias cannot become a second place a budget lives"*). So the two answers
/// differ in that one key name and in nothing else, and this rename is what
/// lets the rest of the line still be compared **byte for byte**.
///
/// **It renames one token, not every `cap:` on the line, and that is two seeds'
/// doing.** The first form renamed all of them and a 5,000-case draw found
/// `- [ ]    a max:1m/d    cap:1m/d`: both readers write into the FIRST budget
/// token and leave the second alone, so the sweeping rename invented a
/// difference the kernel had not made. The second form renamed "the token whose
/// text moved" and a 20,000-case draw found `- a loc:lounge cap:3h/d` edited
/// with `cap=3h/d`, where no text moves and the kernel rewrites the key anyway.
/// Both were **this test asserting something untrue** — neither a kernel bug nor
/// a fork quirk — and both seeds are pinned in
/// `kernel_item_grammar.proptest-regressions` under **D46**, so the cases run
/// every time rather than when a draw finds them again.
///
/// It walks `ItemLine`'s own token vector rather than replacing a substring, so
/// a title word that happens to read `cap:` is untouched.
fn canonical_budget_key(after: &ItemLine) -> String {
    // **The budget token the kernel rewrote: the FIRST one.** Not "the token
    // whose text moved" — a 20,000-case draw found `- a loc:lounge cap:3h/d`
    // edited with `cap=3h/d`, where the value does not move and nothing differs,
    // and the kernel still rewrites the key. And not "every budget token" — the
    // 5,000-case seed above is a line carrying two, of which both readers touch
    // only the first.
    let wrote = after
        .tokens
        .iter()
        .position(|t| t.text.starts_with("max:") || t.text.starts_with("cap:"));
    let mut out = String::new();
    for (k, t) in after.tokens.iter().enumerate() {
        out.push_str(&t.lead);
        match t.text.strip_prefix("cap:").filter(|_| Some(k) == wrote) {
            Some(rest) => {
                out.push_str("max:");
                out.push_str(rest);
            }
            None => out.push_str(&t.text),
        }
    }
    out.push_str(&after.trailing);
    out
}

/// **The line made addressable by the FORK's own editor**, with the id every
/// command below uses: the `^id` it carries, or [`APPENDED`] put on by
/// `ItemLine::append_id`. `None` when the fork cannot tokenise the line at all.
fn addressable(text: &str) -> Option<(String, String)> {
    let item = parse_line(text, &ctx_of(text)).ok()?;
    if item.has_id() {
        return Some((text.to_string(), item.id.to_string()));
    }
    let mut line = ItemLine::parse(text).ok()?;
    line.append_id(&Id::new(APPENDED));
    Some((line.to_string(), APPENDED.to_string()))
}

/// How many cases each arm draws. `TM_PROPTEST_CASES` raises it: D46's point is
/// that one run of a randomised test is a weak claim, and W-25's README block
/// records the counts this file was run at.
fn config() -> ProptestConfig {
    let cases =
        std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(256);
    // The generator puts `""`, `" "` or `"\t"` between the bullet and the box
    // with equal weight, so **two draws in three are cheat 122/123's class** and
    // the two editing arms assume them away (the item-ness arm is where they are
    // asserted). proptest's default ceiling of 1,024 global rejects would stop
    // the run long before `cases` were met, so it is raised in proportion.
    ProptestConfig { cases, max_global_rejects: cases * 8, ..ProptestConfig::default() }
}

proptest! {
    #![proptest_config(config())]

    /// **The fork's `parse_serialize_is_byte_identical`, with a third reader.**
    ///
    /// Both fork readers must return the input unchanged (that half is the
    /// existing test's, restated so a failure names which reader moved), and the
    /// kernel must then return the same bytes or refuse by a declared name.
    #[test]
    fn the_kernel_round_trips_every_line_the_fork_round_trips((text, _stateful) in line()) {
        let item = parse_line(&text, &ctx_of(&text)).expect("the fork parses");
        prop_assert_eq!(item.line_text(), text.clone(), "the fork's parse_line moved a byte");
        let tokens = ItemLine::parse(&text).expect("the fork tokenises");
        prop_assert_eq!(tokens.to_string(), text.clone(), "the fork's ItemLine moved a byte");

        match kernel(&text, json!([])) {
            Kernel::Lines(ls) => prop_assert_eq!(
                answered(&text, &ls), &text,
                "the kernel re-rendered the line differently"
            ),
            Kernel::Refused(name) => prop_assert!(
                declared(&name),
                "the kernel refused {:?} with an UNDECLARED name {:?}", text, name
            ),
        }
    }

    /// **Cheats 122 and 123, pinned by machine.**
    ///
    /// The fork reads an item wherever `ItemLine::parse` succeeds; the kernel
    /// reads one only where [`kernel_reads_as_item`] holds. The difference is
    /// invisible in the round trip — a line the kernel calls prose comes back
    /// byte for byte — so it is asked with a keyed `edit`, which touches no
    /// state and therefore separates "not an item" from every other refusal:
    /// **`noSuchId` iff the kernel read prose.**
    ///
    /// This is the biconditional, so a kernel that starts reading MORE lines as
    /// items fails it as loudly as one that reads fewer.
    #[test]
    fn the_two_readers_agree_on_which_lines_are_items((text, _stateful) in line()) {
        const ARM: &str = "the_two_readers_agree_on_which_lines_are_items";
        let Some((addressed, id)) = addressable(&text) else {
            note_case(ARM, 0);
            return Ok(());
        };
        // **A tab hides the answer, in two ways at once, and both are recorded.**
        // Gap 32's `Cmd.editE` guard refuses a tabbed line by name before
        // item-ness is ever reached; and cheat 122 — the kernel's separator is a
        // space, so `- a ^q9x2<TAB>` tokenises as the single word `^q9x2<TAB>`,
        // which is not an id word — makes the KEY tab-dependent as well, so
        // `noSuchId` there means "a different key", not "prose". The round-trip
        // arm above still reads every tabbed line; this one cannot.
        if addressed.contains('\t') {
            note_case(ARM, 0);
        }
        prop_assume!(!addressed.contains('\t'));
        // Appending the id cannot change item-ness, and this says so rather
        // than assuming it.
        prop_assert_eq!(
            kernel_reads_as_item(&addressed), kernel_reads_as_item(&text),
            "append_id changed item-ness: {:?} -> {:?}", text, addressed
        );
        let (key, value, _) = WIRED_EDITS[0];
        let cmds = json!([{"op": "edit", "id": id, "key": key, "value": value}]);
        // `reached` is the DENOMINATOR (see `COMPARED`): 2 means the kernel's
        // answer was adjudicated against `kernel_reads_as_item`, which is the
        // only branch that says anything. The third branch checks a name.
        let mut reached = 1;
        match kernel(&addressed, cmds) {
            Kernel::Lines(_) => {
                reached = 2;
                prop_assert!(
                    kernel_reads_as_item(&addressed),
                    "the kernel edited {:?}, which this file says it reads as prose", addressed
                );
            }
            Kernel::Refused(name) if name == "noSuchId" => {
                reached = 2;
                prop_assert!(
                    !kernel_reads_as_item(&addressed),
                    "the kernel says noSuchId on {:?}, which this file says it reads as an item",
                    addressed
                );
            }
            Kernel::Refused(name) => prop_assert!(
                declared(&name),
                "UNDECLARED refusal {:?} on {:?}", name, addressed
            ),
        }
        let row = note_case(ARM, reached);
        prop_assert!(floor_holds(row), "{ARM} compared {row:?} — [drawn, addressable, compared]");
    }

    /// **`tm drop`'s two halves write the same bytes** — the kernel's `drop` op
    /// against the fork's own editor for the verb.
    ///
    /// On a **box-less** line the fork writes a `[~]` box in and the kernel
    /// refuses `badHorizon` (D31/K3a); that branch is asserted, not skipped.
    #[test]
    fn the_two_editors_write_the_same_drop((text, _stateful) in line()) {
        const ARM: &str = "the_two_editors_write_the_same_drop";
        let Some((addressed, id)) = addressable(&text) else {
            note_case(ARM, 0);
            return Ok(());
        };
        if !kernel_reads_as_item(&addressed) {
            note_case(ARM, 0);
        }
        prop_assume!(kernel_reads_as_item(&addressed));
        let mut fork = ItemLine::parse(&addressed).expect("the fork tokenises");
        let forked = fork.set_state(State::Dropped).ok().map(|()| fork.to_string());
        // `reached` is the DENOMINATOR (see `COMPARED`): 2 is the branch that
        // compares BYTES. The refusal branches check a class and a box.
        let mut reached = 1;
        match (kernel(&addressed, json!([{"op": "drop", "id": id}])), forked) {
            (Kernel::Lines(ls), Some(want)) => {
                reached = 2;
                prop_assert!(
                    fork_boxed(&addressed),
                    "the kernel dropped the BOX-LESS line {:?}; D31/K3a says it refuses", addressed
                );
                prop_assert_eq!(
                    answered(&addressed, &ls), &want,
                    "the two editors disagree on the drop of {:?}", addressed
                );
            }
            (Kernel::Lines(ls), None) => prop_assert!(
                false, "the fork refused to drop {:?}; the kernel wrote {:?}",
                addressed, answered(&addressed, &ls)
            ),
            (Kernel::Refused(name), forked) => {
                if name == "badHorizon" {
                    prop_assert!(
                        !fork_boxed(&addressed),
                        "badHorizon on the BOXED line {:?}", addressed
                    );
                    // The fork either writes the box in — the divergence D31 and
                    // K3a record — or refuses for its OWN reason, an ambiguous
                    // first title word. Both are recorded; the second is the two
                    // readers agreeing, and neither is a kernel bug.
                    if let Some(w) = forked {
                        prop_assert!(
                            fork_boxed(&w),
                            "the fork's drop of the box-less {:?} wrote {:?}, which carries no box",
                            addressed, w
                        );
                    }
                } else {
                    prop_assert!(
                        declared(&name),
                        "UNDECLARED refusal {:?} dropping {:?}", name, addressed
                    );
                }
            }
        }
        let row = note_case(ARM, reached);
        prop_assert!(floor_holds(row), "{ARM} compared {row:?} — [drawn, addressable, compared]");
    }

    /// **The keyed edit's two halves write the same bytes**, over the keys
    /// `tm edit` sends to the kernel today (`items.rs`'s `KERNEL_EDIT_KEYS`).
    ///
    /// `est` is **not** among them and the omission is recorded, not silent.
    /// `tm edit ^id est=2b` writes `est:120m` when the whole edit is wired and
    /// the **leading** estimate `2b` when any pair in it is not — two different
    /// fields, one of which §4.1 calls the remaining estimate and the other the
    /// history §11 calibrates against. README gap **1430**, driven on the
    /// shipped binary, found from this file and NOT fixed here. `ci` is excluded
    /// for the reason `kernel_edit_cmds` excludes it: on a line whose ci is the
    /// positional digit the kernel's write would populate both slots.
    #[test]
    fn the_two_editors_write_the_same_keyed_edit(
        (text, _stateful) in line(),
        which in 0usize..WIRED_EDITS.len(),
    ) {
        const ARM: &str = "the_two_editors_write_the_same_keyed_edit";
        let Some((addressed, id)) = addressable(&text) else {
            note_case(ARM, 0);
            return Ok(());
        };
        if !kernel_reads_as_item(&addressed) {
            note_case(ARM, 0);
        }
        prop_assume!(kernel_reads_as_item(&addressed));
        let (key, value, fork_key) = WIRED_EDITS[which];
        let mut fork = ItemLine::parse(&addressed).expect("the fork tokenises");
        fork.set_token(fork_key, value);
        let want =
            if fork_key == "max" { canonical_budget_key(&fork) } else { fork.to_string() };
        let cmds = json!([{"op": "edit", "id": id, "key": key, "value": value}]);
        // `reached` is the DENOMINATOR (see `COMPARED`): 2 is the branch that
        // compares BYTES; the refusal branch checks a class.
        let mut reached = 1;
        match kernel(&addressed, cmds) {
            Kernel::Lines(ls) => {
                reached = 2;
                prop_assert_eq!(
                    answered(&addressed, &ls), &want,
                    "the two editors disagree on {}={} in {:?}", key, value, addressed
                );
            }
            Kernel::Refused(name) => prop_assert!(
                declared(&name),
                "UNDECLARED refusal {:?} on {}={} in {:?}", name, key, value, addressed
            ),
        }
        let row = note_case(ARM, reached);
        prop_assert!(floor_holds(row), "{ARM} compared {row:?} — [drawn, addressable, compared]");
    }

    /// **The `arbitrary_lines_never_panic` arm, aimed at the kernel.**
    ///
    /// Free-form bytes after the bullet, in both files. The kernel must answer —
    /// `ok` or a refusal object, never a fault — and an `ok` answer must carry
    /// the input's bytes.
    #[test]
    fn no_line_faults_the_kernel(tail in "[^\\r\\n]{0,40}") {
        let text = format!("-{tail}");
        match kernel(&text, json!([])) {
            Kernel::Lines(ls) => prop_assert_eq!(
                answered(&text, &ls), &text,
                "the kernel re-rendered {:?} differently", text
            ),
            // Free-form bytes reach refusals no generated line does; the claim
            // here is that the kernel ANSWERS. The declared list is enforced by
            // the arms above, over the generator's own lines.
            Kernel::Refused(_) => {}
        }
    }
}

/// The `k=v` pairs `tm edit` wires to the kernel: `(the key on the wire, the
/// value, **the key the fork's `set_token` must be given for the two to write
/// the same bytes**)`.
///
/// The third column is one entry wide and it is a finding, not a fudge. `cap`
/// and `max` are one `Field.Key` to the kernel, whose name is `max`, and
/// `Line.set_max_writes_max` says so on purpose — *"`cap:` normalises to `max:`
/// on write, so the alias cannot become a second place a budget lives"*. The
/// fork's `set_token("cap", …)` writes `cap:` and lets the alias become exactly
/// that second place. So the kernel is **stricter**, the divergence is a
/// theorem rather than an accident, and this column pins it: a kernel that
/// stopped normalising would fail here.
///
/// `WIRED_EDITS[0]` is also [`the_two_readers_agree_on_which_lines_are_items`]'s
/// probe, so it must be a key every drawn line can take.
const WIRED_EDITS: &[(&str, &str, &str)] = &[
    ("dur", "45m", "dur"),
    ("buffer", "10m", "buffer"),
    ("on-miss", "persist", "on-miss"),
    ("after-done", "2d", "after-done"),
    ("min", "1h/w", "min"),
    ("max", "4h/w", "max"),
    ("cap", "3h/d", "max"),
];

/// **Every declared refusal still fires, and nothing the arms saw is
/// undeclared.**
///
/// The first half is deliberate probes, so the census does not depend on a seed:
/// a declared class that has stopped being reachable is a change worth knowing
/// about, and AGENTS §9.2's "a check no input can fail" is the shape it would
/// otherwise decay into. The second half reports the arms' own census.
#[test]
fn zz_the_declared_refusals_are_all_reachable() {
    let probes: &[(&str, &str, Value)] = &[
        ("- [ ] two ids ^a1 ^a2", "manyIds", json!([])),
        ("- [ ] no id at all", "noId", json!([])),
        ("- [ ] a after:^zz9 ^t1", "danglingDep", json!([])),
        ("- [ ] a @m1 ^t1", "danglingParent", json!([])),
        ("- [@] a ^t1", "badState", json!([])),
        ("- [ ] a ^t1", "noSuchId", json!([{"op": "drop", "id": "nope"}])),
        ("- a b ^q1", "badHorizon", json!([{"op": "drop", "id": "q1"}])),
    ];
    let mut missing = Vec::new();
    for (text, want, cmds) in probes {
        match kernel(text, cmds.clone()) {
            Kernel::Refused(name) if name == *want => {}
            other => missing.push(format!("{text:?} wanted {want}, got {other:?}")),
        }
    }
    // `fileKindShape` is the one class the arms never route to: it needs
    // `routines.md`, which the module header says they deliberately avoid.
    let req = json!({"docs": [{"path": "routines.md", "lines": ["- a b ^q1"]}], "cmds": []});
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let got = resp.get("err").map(refusal_name).unwrap_or_else(|| "ok".to_string());
    if got != "fileKindShape" {
        missing.push(format!("routines.md shape probe wanted fileKindShape, got {got:?}"));
    }
    assert!(missing.is_empty(), "declared refusals that no longer fire: {missing:#?}");

    let seen = SEEN.lock().expect("census").clone().unwrap_or_default();
    let undeclared: Vec<_> = seen.keys().filter(|k| !declared(k)).collect();
    assert!(undeclared.is_empty(), "refusals nothing declared: {undeclared:?} (census {seen:?})");
    eprintln!("kernel_item_grammar refusal census: {seen:?}");

    // **THE DENOMINATOR, printed.** The floor above is asserted inside each arm
    // on every case and is what actually guards the claim; this print is so the
    // number can be RE-DERIVED from the committed tree rather than quoted from a
    // temporary `eprintln!` nobody kept. It needs `--test-threads=1` (so this
    // [`zz_the_declared_refusals_are_all_reachable`] runs last) and `--nocapture`,
    // the same two flags the refusal
    // census above needs, and under cargo's default parallel run it reports
    // whatever had accumulated when it ran — which is why it PRINTS and does not
    // assert.
    let compared = COMPARED.lock().expect("census").clone().unwrap_or_default();
    eprintln!("kernel_item_grammar comparison census [drawn, addressable, compared]: {compared:?}");
}
