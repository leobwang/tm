# tm — spec v1.0 (Rust)

**2026-09-07 · frontends: Markdown in VS Code + ratatui TUI · backend: Rust · agent: Claude Code**

This document is the implementation contract. Sections 1–4 fix the architecture and the data (types, grammar, files). Sections 5–8 fix the semantics (recurrence, hierarchy and horizons, priority, planner, energy). Sections 9–13 fix the behaviour (dynamic adjustment, logs, monitors, TUI, CLI). Sections 14–17 cover Claude Code, calendar, configuration, and the build plan with tests. The cheatsheet at the end is the one-page reference.

Where this spec and `tm-spec.md` (v0.1) disagree, this one wins. The main changes from v0.1: one entity type with orthogonal fields instead of kind-by-file; explicit priority with deadline pressure; 0–5 min-energy; recurrence unified across calendar, completion, and event triggers; allocations computed, never stored; day bar and monitors; Rust.

---

## 0. Principles

1. **Markdown is the database.** Every human-authored fact is a line in a `.md` file under `plan/`. Rank within a priority class is line order. VS Code is the admin UI.
2. **Schedules and allocations are derived, never stored.** `plan(state, now)` is a pure function. "How many blocks of X in week W" is computed from estimates, capacity, and pressure; no subtask is ever generated to hold an allocation.
3. **One entity, orthogonal fields.** A goal, a milestone, a pset, a flight, a shower, a TV episode are all `Item`s that differ in field values, not in type. The planner reads fields; it never asks "what kind is this."
4. **Importance from the goal, urgency from the deadline, urgency capped by importance — except when a deadline becomes infeasible.**
5. **Energy is matched, not assumed.** Every item has a min-energy `ci` 0–5; every slot has a predicted energy 0–5 from a prior curve corrected by your reports and learned over time.
6. **Demotion, not deletion.** Unfinished work moves to the enclosing horizon with its remaining estimate and a stamp, and re-competes.
7. **Zero-effort adjustment.** Every disruption is one keystroke that changes one fact, followed by a replan from `now`. Nothing is ever dragged.

---

## 1. Architecture

```
                     ┌──────────────── frontends ─────────────────┐
                     │ VS Code (edit .md) │ tm tui │ Claude Code   │
                     └──────────┬─────────┴───┬────┴──────┬───────┘
                                │ files       │ in-proc   │ `tm … --json`
                     ┌──────────▼─────────────▼───────────▼───────┐
                     │ tm-core (lib)                                │
                     │ parse · model · recur · hierarchy · priority │
                     │ planner · energy · log · review · ics        │
                     └──────────┬─────────────┬───────────┬───────┘
                                │             │           │
                          plan/**/*.md   .tm/log.jsonl   Google Calendar (ICS)
                                         .tm/model.json
                                         .tm/state.json
```

### 1.1 Crates (Cargo workspace)

| Crate | Kind | Contents |
|---|---|---|
| `tm-core` | lib | everything with semantics; no I/O beyond `std::fs` behind a `Store` trait; no terminal code |
| `tm` | bin | CLI (`clap`) and the TUI (`ratatui` + `crossterm`) as the `tm tui` subcommand; one binary |

Dependencies (pin in `Cargo.toml`; all mature): `chrono` + `chrono-tz` (time), `serde` + `serde_json` + `toml` (config/log/model), `clap` (CLI), `ratatui` + `crossterm` (TUI, mouse capture for hover), `notify` (file watcher), `ical` (ICS parsing), `thiserror` + `anyhow` (errors), `insta` (snapshot tests), `proptest` (round-trip and invariant tests), `ureq` (ICS fetch, blocking), `nanoid` or custom (ids).

### 1.2 Module map (`tm-core/src`)

```
model.rs      Item, enums, Id, Dur, Horizon                      (§3)
grammar.rs    tokenizer + parser + serializer, byte-faithful     (§4)
store.rs      Store trait; FsStore: read tree, write line by id, generated sections, mtime guard
recur.rs      instances of recurring items over a date range     (§5)
tree.rs       parent/child index, root lookup, rollups, effective shape/due, series heads, deps
horizon.rs    horizon lifecycle: close day/week/month, demote, readopt, move
priority.rs   root priority, EDF pass, utilization bins, hysteresis (§7)
capacity.rs   week lookahead: expected slots per day by energy level
energy.rs     prior curve, today's posterior, learned model, duration multipliers (§8.5)
planner.rs    plan(state, now) -> DayPlan                        (§8)
emit.rs       DayPlan -> generated markdown section + SVG day bar
log.rs        append-only JSONL events; replay to derive block/instance state (§10)
review.rs     day/week/month reviews and monitors               (§11)
ics.rs        ICS -> calendar/*.md
check.rs      tree validation (ids, parents, cycles, fields, files)
```

### 1.3 Three writers, one file set

You, the TUI, and Claude Code all write `plan/`. Rules:

- Every item has a stable id (`^k7q2`). Writers address items by id, never by line number.
- `Store::write_line(id, new_text)` re-reads the file, finds the line by id, replaces exactly that line, checks mtime unchanged since read, writes atomically (temp + rename). On mtime mismatch: re-read and retry once; then return `Conflict` with both texts.
- Generated sections are replaced whole between `<!-- tm:… start -->` / `<!-- tm:… end -->` markers. Text outside markers is never touched.
- `tm check` validates the tree; runs as a git pre-commit hook and a Claude Code post-edit hook.

---

## 2. Repository layout

```
plan/
├── config.toml                # §15
├── CLAUDE.md                  # §13
├── inbox.md                   # capture, untriaged (bare lines)
├── backlog.md                 # horizon = none: finite undated items, far-out dated items, series
├── routines.md                # open recurring windows: sleep, meals, workout, laundry …
├── optional.md                # never displaces; rest slots only; capped
├── month/2026-09.md           # horizon = month
├── week/2026-W37.md           # horizon = week
├── day/2026-09-07.md          # generated timeline + pinned + log + notes
├── day/2026-09-07.svg         # generated day bar
├── calendar/2026-W37.md       # synced intervals (generated; `manual` lines preserved)
├── .claude/skills/…           # §13
└── .tm/
    ├── log.jsonl              # append-only observations
    ├── model.json             # learned energy curve, duration multipliers, lounge rate
    └── state.json             # runtime: current block, timers, wake, location, last plan hash
```

**Horizon is the file.** An item's horizon is where its line lives: `month/`, `week/`, `day/` (pinned section), or `backlog.md` (none). Moving an item between horizons is moving its line (`tm move`, or cut/paste in VS Code). `routines.md`, `optional.md`, and `calendar/` are horizon-less files with one convention each (§4.3).

---

## 3. Data model

### 3.1 The entity

```rust
pub struct Item {
    pub id: Id,                          // alphanumeric, stored as ^id; new ids are digits (the kernel's freshId); assigned on first parse
    pub title: String,
    pub state: State,                    // [ ] [>] [x] [-] [~] [?]
    pub ci: u8,                          // min-energy 0..=5; default: parent's, else 3
    pub est: Option<Dur>,                // remaining estimate (est: field overrides the leading estimate)
    pub est_original: Option<Dur>,       // the leading estimate as written
    pub priority: Option<u8>,            // explicit !k, 1..=4; normally only on roots
    pub parent: Option<Ref>,             // @id or @label
    pub horizon: Horizon,                // derived from file path
    pub scope: Scope,                    // Finite (default) | Open (`open` flag)
    pub shape: Shape,                    // None | Point | Interval | Window
    pub recur: Recur,                    // None | Calendar | AfterDone | OnEvent
    pub on_miss: OnMiss,                 // Expire | Persist | Next  (default depends on shape, §5.3)
    pub budget: Budget,                  // floor (min:) and/or cap (max:) per period
    pub splittable: bool,                // default true; `atomic` flag sets false
    pub after: Vec<Dep>,                 // dependencies: ^id or event:name
    pub loc: Loc,                        // any | lounge | home | out | <name>
    pub tags: Vec<String>,
    pub series: Option<(String, u32)>,   // from `## series:<name>` section; index = position
    pub stamps: Stamps,                  // demoted: [W36,W37], waiting_since, readopted
    pub extra: Vec<(String, String)>,    // unknown key:value tokens, preserved verbatim
    pub src: SourceLoc,                  // file, line number, raw tokens (for byte-faithful rewrite)
}

pub enum State { Todo, Active, Done, Demoted, Dropped, Waiting }
pub enum Scope { Finite, Open }
pub enum Shape {
    None,
    Point    { due: DateTime },
    Interval { start: DateTime, end: DateTime },
    Window   { range: WindowRange, dur: Dur },
}
pub enum WindowRange { Daily { from: Time, to: Time }, Absolute { from: DateTime, to: DateTime } }
pub enum Recur {
    None,
    Calendar(Rule),                             // every:
    AfterDone { offset: Dur, window: Option<Dur> },  // after-done:2d~1d
    OnEvent  { name: String, timeout: Option<Dur> }, // on-event:reply/7d
}
pub enum Rule { Daily, Weekdays, Weekly(Vec<Weekday>), EveryNDays(u32), EveryNWeeks(u32, Weekday), Monthly(u8) }
pub enum OnMiss { Expire, Persist, Next }
pub struct Budget { pub floor: Option<Rate>, pub cap: Option<Rate> }
pub struct Rate { pub amount: Dur, pub per: Period }     // Period: Day | Week | Month
pub enum Dep { Item(Id), Event(String) }
pub enum Loc { Any, Lounge, Home, Out, Named(String) }
pub enum Horizon { Backlog, Month(YearMonth), Week(IsoWeek), Day(NaiveDate), Routine, Optional, Calendar(IsoWeek), Inbox }
pub struct Dur(pub u32);   // minutes; `b` unit converts via config.block_min; unit remembered for serialization
```

Everything the user described maps onto these fields:

| Your example | scope | shape | recur | on_miss | other |
|---|---|---|---|---|---|
| exam | finite | interval | none | persist | `prep:` children (§6.4) |
| exam review | finite | point (due = exam start, derived) | none | persist | child of the exam |
| assignment deadline | finite | point | none | persist | `splittable`, maybe `max:2b/d` |
| flight | finite | interval | none | persist | `buffer:2h travel-day` (calendar file) |
| self-paced reading | finite | none | none | — | in backlog or a series |
| read cell-bio 1→2→3 | finite | none | none | — | `## series:cell-bio` section |
| message someone, await reply | finite | none | on-event(reply, 7d) | — | `[?]` while waiting |
| shower every 2–3 days | open | window | after-done(2d~1d) | expire | routines |
| lunch | open | window(11:30–13:30, 30m) | calendar(daily) | expire | routines |
| Lean practice ≥ 6b/week | open | none | none | — | `min:6b/w` |
| TV episode | open | none | none | — | optional file, `max:4h/w` |

### 3.2 Derived (never stored)

- `effective_shape(item)`: an item with `shape = None` whose parent is an `Interval` is treated as `Point { due: parent.start }` (prep work). Otherwise as written.
- `root(item)`, `root_priority(item)`: walk `parent` to the top; explicit `!k` there, else `config.default_priority`.
- `remaining(item)`: `est` if set, else `est_original`, else Σ `remaining(children)`.
- `progress(item)`: Σ logged block minutes for the item and descendants ÷ (`est_original` or Σ children).
- `instances(item, range)`: occurrences of a recurring item in a date range (§5).
- `series_head(name)`: first item in the series section with state ≠ Done/Dropped.
- `priority(item, ctx)`: §7. `allocation(item, horizon)`: §7.2 — a number, never a line.

---

## 4. Grammar and files

### 4.1 Item line

```
- [ ] 4 2b Exercises 5.3–5.5  @m1 #lean due:2026-09-11T23:59 max:2b/d est:1b ^t3
  │   │ │  │                   └──────────── tokens, any order ────────────────┘
  │   │ │  └ title: text up to the first token that starts with @ # ! ^ or matches key:value
  │   │ └ leading estimate: Nb | Nm | Nh     (optional; must directly follow ci)
  │   └ ci 0–5                                (optional; must directly follow state)
  └ state
```

EBNF (whitespace-separated tokens after the state):

```
line      = "- " state SP [ci SP] [est SP] title { SP token } ;
state     = "[ ]" | "[>]" | "[x]" | "[-]" | "[~]" | "[?]" ;          (* todo active done demoted dropped waiting *)
ci        = "0".."5" ;
est       = digits ("b" | "m" | "h") ;
token     = "@" ref | "#" tag | "!" ("1".."4") | "^" id | key ":" value | flag ;
key       = "due" | "at" | "win" | "dur" | "pref" | "every" | "after-done" | "on-event" | "on-miss"
          | "min" | "max" | "after" | "loc" | "buffer" | "est" | "demoted" | "waiting" | "cap" ;
flag      = "open" | "atomic" | "manual" | "travel-day" | "hot" ;
```

Value formats:

| key | value | meaning |
|---|---|---|
| `due:` | `2026-09-11` or `2026-09-11T23:59` | shape = Point |
| `at:` | `2026-09-07T12:50/13:50` or `…T08:15/2026-09-12T10:40` | shape = Interval |
| `win:` + `dur:` | `win:11:30-13:30 dur:30m` (daily) or `win:2026-09-07T14:00/17:00 dur:1h` | shape = Window |
| `pref:` | `wake+10m` or `12:00` | preferred anchor inside a window |
| `every:` | `day` `weekday` `Mon,Wed,Fri` `2w:Sun` `3d` `month:15` | recur = Calendar |
| `after-done:` | `2d` or `2d~1d` (offset ~ validity window) | recur = AfterDone |
| `on-event:` | `reply` or `reply/7d` (name / timeout) | recur = OnEvent |
| `on-miss:` | `expire` `persist` `next` | override the default (§5.3) |
| `min:` `max:` | `6b/w` `2b/d` `4h/w` | budget floor / cap per day, week, month |
| `after:` | `^k7q2,^m2` or `event:visa` | dependencies |
| `loc:` | `lounge` `home` `out` `zoom` … | location constraint |
| `est:` | `1b` | remaining estimate (tool-written after partial work) |
| `demoted:` | `W36,W37` | tool-written stamps |
| `waiting:` | `2026-09-05` | tool-written; set with state `[?]` |
| `buffer:` | `2h` | intervals only: blocked time before start |

In `routines.md` and `optional.md` the state is omitted (instances live in the log); the parser treats a missing state there as `[ ]`. Parsing rules: tokens the parser cannot classify stay in the title; unknown `key:` is preserved in `extra` and reported by `tm check`; lines not beginning with `- ` are prose/headings/comments and are kept verbatim. Ids are global across the tree; a missing `^id` is appended to the line in place on first parse; ids are never renumbered.

Serialization is byte-faithful: the parser keeps the original token list; an edit replaces or inserts the specific token; everything else is written back unchanged (including the original estimate unit).

### 4.2 Sections

- `# Heading` lines partition a file. The parser records the section for each item. Three section names have meaning: `# Demoted` (in month files, §6.3), `# Pinned` (in day files, §6.2), and `## series:<name>` (§5.4). Any other heading is organisational.
- Line order within a section = rank for tie-breaking (§7.4).

### 4.3 Files

**`month/2026-09.md`** — roots carry explicit priority.

```markdown
---
month: 2026-09
---
# Outcomes
- [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1
- [ ] 4 !1 Soundcode: end-to-end demo runs             ^O2
- [ ] 2 !3 Winter course selection + admin done        ^O3

# Demoted
- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2
```

**`week/2026-W37.md`**

```markdown
---
week: 2026-W37
window: 2026-09-07..2026-09-13
budget: 25
planned: 20
---
# Milestones
- [ ] 5 6b Finish ch.5 exercises        @O1 ^m1
- [ ] 4 6b Rollback path passes tests   @O2 ^m2
- [ ] 5 3b Read ch.6                    @O1 ^m3
- [ ] 2 2b Pick winter courses          @O3 ^m4
- [ ] 4 6b CS 234 pset 2                @O3 due:2026-09-11T23:59 max:2b/d ^d1
- [ ] 5 2h Midterm                      @O3 at:2026-10-20T10:00/12:00 loc:JCL ^x1
- [ ] 5 8b Midterm review               @x1 ^x2

# Tasks
- [ ] 5 1b Read ch.6 §1–2               @m3 ^t1
- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3
- [ ] 3 1b Claude Code drafts tests     @m2 ^t4
- [ ] 3 1b Review the drafts            @m2 after:^t4 ^t5
```

`^d1` is a dated milestone (Point). `^x1` is an interval with a prep child `^x2` whose due is derived as `2026-10-20T10:00`. Depth is arbitrary; sections are organisational.

**`backlog.md`** — horizon none.

```markdown
# Untied
- [ ] 2 30m Insurance claim for the bike  ^a1
- [ ] 1 Pick up package  win:2026-09-07T09:00/21:00 dur:20m ^a3
- [?] 2 15m Ask Prof. Lee about the reading group  on-event:reply/7d waiting:2026-09-05 ^a4

# Dated, far out
- [ ] 5 10b Workshop paper draft  @O2 due:2026-11-20 #soundcode ^d2

## series:cell-bio
- [x] 4 4b Cell Biology vol. 1 ^c1
- [ ] 4 4b Cell Biology vol. 2 ^c2
- [ ] 4 4b Cell Biology vol. 3 ^c3
```

**`routines.md`** — every line is `open`, has a window or `after-done`, and `ci` defaults to 1. No checkbox: instances are tracked in the log, not in the file.

```markdown
- sleep      win:22:00-08:00 dur:8h30m every:day ci:0
- breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m
- lunch      win:11:30-13:30 dur:30m  every:day
- dinner     win:17:30-19:30 dur:30m  every:day
- workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri
- shower     win:07:00-23:00 dur:20m  after-done:2d~1d
- laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist
- groceries  win:10:00-20:00 dur:45m  every:week loc:out
```

**`optional.md`** — `open`, `ci:0`, priority 5, rest slots only.

```markdown
- Severance S3E4  dur:1h
- Factorio        dur:2h max:4h/w
```

**`calendar/2026-W37.md`** — generated intervals; only `manual` lines survive a sync.

```markdown
- [ ] 3 Meeting w/ host      at:2026-09-07T12:50/13:50 loc:zoom ^g1
- [ ] 2 CS 234 lecture       at:2026-09-09T15:00/16:20 loc:JCL ^g2
- [ ] 1 ✈ ORD→SFO UA 1234    at:2026-09-12T08:15/10:40 buffer:2h travel-day ^g3
- [ ] 1 Dinner w/ Kun        at:2026-09-10T19:00/20:00 manual ^g4
```

**`day/2026-09-07.md`** — one generated section, one human section, one append-only section.

```markdown
---
date: 2026-09-07
wake: 06:05
slept: 8h10m
loc: lounge
window: 07:00..16:00
budget: 6
---
![day](2026-09-07.svg)
<!-- tm:plan start 10:42 -->
07:00  5 p1 ✓ Read ch.6 §1–2               @m3  1b  (67m)
08:00  5 p1 ✓ Read ch.6 §3                 @m3  1b  (58m)
09:00  ·     ✓ break 20m                        (24m)
09:20  4 p1 ▶ Exercises 5.3–5.5            @m1  2b×1.6
11:20  ·       lunch 30m
11:50  4↓p3    Claude Code drafts tests    @m2  1b     ↓ slot 4, item 3
12:50  ⏰      Meeting w/ host              1h
13:50  ·       break 20m
14:10  3 p3    Review the drafts           @m2  1b
15:10  ───     window ends 16:00
15:10  1 p0 ⚠  Pick up package             20m    due today
17:30  ·       dinner 30m
18:00  ○       Severance S3E4              1h
21:30  🌙      wind-down · bed 22:00
<!-- tm:plan end -->

# Pinned
- [ ] 2 20m Call the bank about the card  ^p1

## Log
06:05 wake slept=8h10m
07:02 start ^t1 pred=5 rep=5
08:09 done ^t1 67m/60m went=1
09:32 start ^t3 pred=5 rep=4 replan
12:10 interrupt ^t4 … 13:05 resume lost=55m dropped=^t5

## Notes
```

Timeline row: `HH:MM  ci  pN  mark  title  @parent  est  (actual)  note`. Marks: `✓` done · `▶` current · `↓` slot under-used (gap ≥ 2) · `⚠` HOT (p0) · `⏰` interval · `○` optional · `·` routine/break · `🌙` wind-down. `# Pinned` is yours: items you want today regardless of rank (horizon = day). `## Log` is append-only. `## Notes` is free text.

---

## 5. Recurrence, instances, waiting, series

### 5.1 Instances

A recurring item never changes its line. Occurrences are computed:

```rust
pub struct Instance { pub item: Id, pub key: InstanceKey, pub due: Option<DateTime>,
                      pub window: Option<(DateTime, DateTime)>, pub status: InstanceStatus }
pub enum InstanceKey { Date(NaiveDate), Nth(u32) }      // calendar → date; after-done/on-event → ordinal
pub enum InstanceStatus { Pending, Done, Missed, Expired, Skipped }
pub fn instances(item: &Item, range: DateRange, log: &Log) -> Vec<Instance>
```

- **Calendar:** expand `Rule` over the range; window = the daily window on that date (or the absolute window); status from the log (`done inst=2026-09-07`, `skip inst=…`).
- **AfterDone:** next instance due = last `done` + `offset`; valid until due + `window` (if given); before the first completion, due = today. Exactly one pending instance exists at a time.
- **OnEvent:** on `done`, the item's state becomes `[?]` with `waiting:<date>`. `tm event <name> [^id]` or `timeout` elapsed → state `[ ]`, `est` reset to `est_original`, and a new instance is pending. Waiting items are listed in the TUI's Necessities screen; they never take slots.

### 5.2 Windows and mandatory placement

A Window instance is placed by the planner inside its range at the lowest-value position (§8.2 step 3). It becomes **mandatory** — placed before any task — when its window closes today and `on_miss ≠ expire`, or when `on_miss = expire` and it is the last chance today (a shower on day 3 of its 2d~1d window).

### 5.3 `on_miss` defaults and effects

| shape / recur | default | on miss |
|---|---|---|
| Interval | persist | stays with state `[ ]` and an `overdue` badge until you re-date (`at:`) or drop; priority 0 while overdue |
| Point | persist | same, priority 0 (§7) |
| Window, calendar recur | expire | instance marked Expired; nothing carried |
| Window, after-done | expire | Expired; next instance is due immediately (offset from last *completion*, not from the miss) |
| `on-miss:next` | — | instance Skipped; next occurrence unchanged |
| `on-miss:persist` on a routine (laundry) | — | instance stays Pending into the next day; mandatory; counts as overdue |

### 5.4 Series

`## series:<name>` sections hold ordered items. Only the **head** (first item not Done/Dropped) is active; the rest are invisible to the planner. Completing the head activates the next line; the head inherits nothing from the previous item except the section's implied `after:`. Adding a volume = adding a line at the end. A series is the only place where "finishing one produces the next" is expressed; it is data, not generation.

### 5.5 Dependencies

`after:^id` items are ineligible until the referenced item is Done. `after:event:<name>` items are ineligible until `tm event <name>` is logged. Cycles are a `tm check` error. Dependencies do not affect priority, only eligibility, so a blocked high-priority item shows in diagnostics as *blocked by ^id* rather than silently vanishing.

---

## 6. Hierarchy and horizons

### 6.1 Two independent relations

- **Hierarchy** = `parent`. Any depth. Used for: root priority, `ci` default, tag inheritance, rollups, prep-due derivation.
- **Horizon** = file location. Used for: which planning conversation the item belongs to, budgets, lifecycle. A week item may be a child of a month item, of a backlog item, or of nothing. A day-pinned item may be a child of anything.

There is no rule "child must be one horizon below parent." The `/plan-week` skill *suggests* pulling children of month outcomes into the week; it never requires it.

### 6.2 Which items the day planner sees

Candidates for today = all items in `week/<this week>` + `day/<today>#Pinned` + `backlog.md` + series heads + instances of `routines.md` and `calendar/` due today + `optional.md`, filtered by state ∈ {Todo, Active}, eligibility (deps, waiting, `loc`), and `max:` caps. Month items are **not** candidates (they are outcomes, not work); an item in `month/` that has an estimate and no children is a `tm check` warning ("outcome with estimate — did you mean a milestone?").

### 6.3 Lifecycle (`horizon.rs`)

`tm close <day|week|month>` runs automatically on the first command after the period ends (idempotent; recorded in `state.json`).

| Close | For each unfinished item in that horizon | Result |
|---|---|---|
| **day** | `[>]` → `[ ]`, `est:` = remaining. Pinned items → moved to `week/<current>` with `demoted:D07`. | nothing else moves; the day file gets its review section |
| **week** | `[ ]`/`[>]` → `[-]` in the week file; the line is **copied** to `month/<current>#Demoted` with `est:` = remaining and `demoted:W37` appended. Unfinished children are dropped from the week file (their remaining is folded into the parent's `est:`). Dated items past due with `persist` → moved to `backlog.md#Overdue` instead. | the week file becomes an archive |
| **month** | unfinished outcomes and everything in `# Demoted` → listed; `tm close month` moves them to the next month file (outcomes keep `!k`; demoted items keep stamps) unless you `--drop ^id`. | `/plan-month` proposes cuts for anything with ≥ 2 stamps |

`tm readopt ^id [--to week]` moves a demoted line into the current week (`[-]` → `[ ]`, stamp kept). `tm move ^id <backlog|month|week|day>` moves any line between horizon files. Recurring items and calendar intervals are never demoted — their instances expire or persist per §5.3.

### 6.4 Rollups (`tree.rs`)

- `remaining(item)`: `est` if set, else `est_original`, else Σ over children.
- `done_minutes(item)`: Σ log block minutes of the item and all descendants, from `log.rs` replay.
- `progress(item)` = `done_minutes / (est_original || Σ children est_original)`.
- Children of an Interval with no shape → `Point { due: parent.start }` (prep). Their remaining sums into the parent's prep need, which is what the pressure in §7 uses.

---

## 7. Priority (`priority.rs`)

Priority `p` is an integer, **0 = highest**, computed at plan time for every candidate. It orders candidates; it does not place them (the energy filter in §8 does).

### 7.1 Definitions

- `k` = `root_priority(item)` ∈ 1..=4 (explicit `!k` on the root; default `config.default_priority = 3`).
- `need(item)` = `remaining(item) × config.safety` (default 1.3).
- `capacity(item, until)` = Σ over days from now to `until` of expected slot-minutes with `slot_energy ≥ item.ci`, from `capacity.rs` (§8.4), **net of reservations made by earlier deadlines in the EDF pass**.
- `u(item)` = `need / capacity` (capacity 0 → `u = ∞`).
- `bin(u)`: `u ≥ 1 → HOT`; `0.5 ≤ u < 1 → +0`; `0.25 ≤ u < 0.5 → +1`; `0.1 ≤ u < 0.25 → +2`; `u < 0.1 → +3`. Bin edges are `config.priority_bins`.

### 7.2 The rule

```
walls    : Interval instances (calendar, exams, meetings) are not on the scale; they are placed first (§8.2 step 2)
p = 0    : HOT (u ≥ 1) · overdue with on_miss = persist · mandatory window instance (§5.2) · `hot` flag
p = k + bin(u)         : Finite with a due (own or derived) — after the EDF pass
p = k + bin(u_floor)   : Open with a floor:  need = floor − done_this_period, capacity = rest of the period
p = k + 2              : Finite, no due, no floor (pure rank)
p = 5                  : optional.md items (never compete; rest slots only)
clamp p to 0..=7
```

`allocation(item, period)` — the number v0.1 called "reserved blocks" — is `min(need, capacity)` from the EDF pass. It is shown in the Queue screen ("fits: 6b of 6b") and never written to a file.

### 7.3 EDF pass (feasibility with competition)

```
dated = candidates with an effective due, sorted by due ascending
cap   = per-day map: minutes of expected capacity at each energy level (from lookahead)
for item in dated:
    avail = Σ_{day ≤ due(item)} cap[day][level ≥ item.ci]        # what is left after earlier deadlines
    reserve = min(need(item), avail)
    subtract reserve from cap, earliest days first, highest matching levels first
    u(item) = need(item) / avail            # avail before this item's own reservation; 0 → ∞
    if u ≥ 1: mark IMPOSSIBLE if need > avail else HOT
```

IMPOSSIBLE items are still scheduled with everything available; the banner in the TUI and `tm plan` output names the item and the shortfall (`needs 8b, 5b available by Fri`). The two exits are editing `est:` or `due:`.

### 7.4 Sort key and hysteresis

Candidates are sorted by `(p, root_line_order, own_line_order)`. Line order is your rank within a priority class; this is the affordance cut/paste in VS Code gives you.

Hysteresis: `p` may improve (decrease) by at most one bin per day relative to yesterday's stored `p` (in `state.json`) unless the new value is 0. It may worsen freely. This stops the day-to-day reshuffling that pure utilization would cause.

### 7.5 Batching

Candidates with `remaining ≤ config.batch_max_min` (default 20m) and equal `ci` are grouped: the planner fills one block with several of them in key order, shown as one row `batch: package · insurance · bank (3)`. Without this, the `+3` bin never gets a slot.

---

## 8. Planner (`planner.rs`)

```rust
pub struct PlanInput<'a> { pub tree: &'a Tree, pub log: &'a Log, pub cfg: &'a Config,
                           pub model: &'a Model, pub runtime: &'a Runtime, pub now: DateTime }
pub fn plan(input: &PlanInput) -> DayPlan;          // pure; no I/O
pub struct DayPlan { pub date: NaiveDate, pub window: (DateTime, DateTime), pub budget_blocks: u32,
                     pub segments: Vec<Segment>, pub diagnostics: Diagnostics, pub priorities: Vec<(Id, Prio)> }
pub struct Segment { pub start: DateTime, pub end: DateTime, pub kind: SegKind, pub energy: Option<u8>,
                     pub item: Option<Id>, pub instance: Option<InstanceKey>, pub flags: SegFlags }
pub enum SegKind { Block, Batch(Vec<Id>), Break, Routine, Wall, Rest, Optional, WindDown, Sleep, Lost }
```

### 8.1 Window and budget

```
arrival  = runtime.arrival (set by `tm arrive`), else now
end      = min(arrival + window_hours, window_cap) + Σ duration(walls inside [arrival, end])
budget   = floor(window_hours × 60 / block_min × budget_ratio)        # 8h → 6 blocks
remaining_budget = budget − blocks_done_today (from log)
```

Window and budget are computed once at `tm arrive` and stored in `state.json`; a replan reads them. A late start gets a later end and the same budget formula, so the day is proportional, never cancelled.

### 8.2 Steps

```
1 WALLS      place Interval instances due today (+ buffer:, travel-day zeroing). Overlapping walls → diagnostics.conflicts; the planner
             does not resolve them and places nothing in the overlap.
2 ROUTINES   for each Window instance due today (calendar or after-done):
               mandatory (§5.2) → place now, earliest feasible position in its window
               pref: given → at the anchor if free
               otherwise → deferred to step 6 (placed in the lowest-energy free position inside its window)
             sleep and wind-down define the hard end of the day: no Block with ci ≥ 4 after wind-down.
3 SLOTS      cut free time in [now, end] into blocks of block_min; a break of break_min after every break_after_blocks blocks;
             the last block may be short (≥ 30m) or dropped.
             each slot gets energy = energy::predict(model, features(slot)) then posterior correction (§8.5), then
             min(energy, home_max_ci) if runtime.loc == Home (unless --allow-home).
4 PRIORITY   priorities = priority::compute(candidates, capacity_lookahead, log, cfg)      (§7)
5 ASSIGN     sorted = candidates sorted by key; cursor over sorted
             for slot in slots, while blocks_assigned < remaining_budget:
                 pick the first eligible candidate:
                     state ∈ {Todo, Active}; deps satisfied; not Waiting; loc compatible;
                     ci ≤ slot.energy; cap (max:) not exhausted for the period;
                     if !splittable: contiguous free slots ≥ remaining exist before the next wall, else skip
                 none → slot becomes REST
                 gap = slot.energy − item.ci; gap ≥ 2 → flag ↓ and count in diagnostics.underused
                 Active item keeps its current slot regardless of key (no preemption mid-block).
                 batching (§7.5) fills a slot with several small items.
6 ROUTINES'  place deferred Window instances into the lowest-energy free position in their windows (REST first, then the
             lowest-energy block, displacing it — that block's item returns to the candidate pool for a later slot).
7 REST       leftover slots after the budget → Rest; optionals (p = 5) fill Rest and the evening before wind-down, within max:.
8 EMIT       DayPlan with diagnostics: underused, a_capacity_lost (slots with energy ≥ 4 left Rest while ci-5 items exist but
             were ineligible), hot, impossible, conflicts, blocked (by dep), deferred (ci-5 items that lost their slot to a
             posterior downgrade), waiting.
```

### 8.3 Invariants (property tests)

- **Purity/stability:** same input → identical `DayPlan`; a replan changes no segment with `end ≤ now`.
- **No overbooking:** Σ Block minutes ≤ remaining_budget × block_min; no segment overlaps a Wall; no ci ≥ 4 Block after wind-down.
- **Monotone rank:** for two candidates with equal `p` and equal `ci`, the one with the lower line order is never left unassigned while the other is assigned.
- **Energy filter:** every Block has `item.ci ≤ slot.energy`.
- **Tail-drop:** removing minutes from the day (interrupt, overrun, downgrade) never changes the set of assigned items except by removing a suffix in key order (Active item excepted).
- **HOT before queue; impossible never dropped; walls never moved.**

### 8.4 Capacity lookahead (`capacity.rs`)

```rust
pub fn lookahead(tree, log, cfg, model, runtime, from: NaiveDate, days: u32) -> Vec<DayCapacity>
pub struct DayCapacity { pub date: NaiveDate, pub minutes_at_level: [u32; 6] }   // index = energy 0..=5
```

For today: the actual remaining slots from §8.2 step 3. For future days: expected arrival = `model.expected_arrival(weekday)` (learned; default config), expected location by `P(lounge | weekday)`, walls from `calendar/`, the prior curve, and budget_ratio. `tm plan --week` renders this as the week grid; `priority.rs` consumes it for the EDF pass.

**Exact capacity (kernel stage 5, owner decisions D10, D15, D17).** Since the kernel computes the lookahead, a future day is the exact mixture `p · lounge day + (1 − p) · home day` with `p = P(lounge | weekday)`, held in units over `capDen = 10^18`; `p_lounge` (in `model.json` or `config.toml`) must be a decimal in `[0, 1]` of at most 18 places **as written**, or every verb that computes capacity or priority fails naming the file and key. Capacity minutes in `--json` are **floors**, each beside its exact value as `{"num": "<digits>", "den": "<digits>"}` in lowest terms:
- `tm plan --week --json`: `days[].minutes_at_level` (each the floor of its entry in `minutes_at_level_exact`) and `days[].total` (the floor of the exact day total `total_exact`, **not** the sum of the six floors, so up to five more);
- `tm plan --json` and `--explain`: `priorities[].avail_min`, `allocation_min` and `shortfall_min`, each the floor of `avail_min_exact`, `allocation_min_exact` and `shortfall_min_exact`. Because each integer is its own floor, `need_min − allocation_min` may exceed `shortfall_min` by one; the exact values agree.

### 8.5 Energy (`energy.rs`)

**Scale:** 0–5 for both items (`ci`) and slots. Report keys `0`–`5`.

**Prior:** `config.energy.prior.<loc>` — a step function of hours-since-wake (`hsw`), e.g. lounge `0–1h: 4, 1–5h: 5, 5–8h: 4, 8–10h: 3, 10h+: 2`; home one level lower; `sleep_debt.shift` subtracted when `slept < under_hours`.

**Today's posterior:** each report at time `t` gives `δ = rep − pred(t)`. Correction to a later slot at `t'`: `δ · w(t'−t)`, `w = 1` for 3h, linearly to 0 at 6h. Non-zero `δ` triggers a replan.

**Learned model (`model.json`), v1 — bucketed shrinkage means:**

```
bucket b = (loc, floor(hsw))
energy[b] = round( (n0 · prior[b] + Σ_i w_i · rep_i) / (n0 + Σ_i w_i) ),   w_i = exp(−age_days_i / decay_days),   n0 = prior_weight
sleep_debt_shift = shrunken mean of (rep − energy[b]) over observations with slept < under_hours
duration[(ci, tag)] = shrunken mean of actual/est, prior 1.0, n0 = duration_prior_weight
p_lounge[weekday], expected_arrival[weekday] = shrunken means from `arrive` events
```

Observations with `went = 3` (collapsed) count double; `went = 2` count 1.5. `tm model --fit` rewrites `model.json` (human-readable; hand edits become the new prior). **v2** (after ~60 days): ordinal regression on `(hsw, hod, loc, slept, dow, blocks_done, since_break)`; promoted only if held-out MAE improves (`tm model --compare`).

```json
{ "energy": { "lounge": [4,5,5,5,5,4,4,4,3,3,2,2], "home": [3,4,4,4,3,3,3,2,2,2,2,2] },
  "sleep_debt_shift": 0.8,
  "duration": { "lean": 1.6, "soundcode": 1.1, "_default": 1.3 },
  "p_lounge": { "Mon": 0.9, "Tue": 0.9, "Wed": 0.8, "Thu": 0.9, "Fri": 0.7, "Sat": 0.5, "Sun": 0.4 },
  "expected_arrival": { "Mon": "07:10", "Sat": "10:30" },
  "fitted": "2026-09-14", "n_obs": 61 }
```

The planner schedules with `est × duration[(ci, tag)]` (first matching tag, else `_default`) and displays both (`2b×1.6`).

---

## 9. Dynamic adjustment

One keystroke changes one fact; `plan()` reruns from `now`. Because assignment is a rank-ordered fill of remaining slots, any loss of time drops a suffix of the candidate list — and those items are still in their files, untouched.

| Event | Key | Fact | Replan effect |
|---|---|---|---|
| Block finished | `d` | `done` logged; item `[x]` (or `est:` = remaining if `d` on a partial with `--partial`) | next candidate starts now |
| Timer passes `est × r` | overtime prompt | `x` extend (`est:` += 1b) · `s` stop (`[ ]`, `est:` remaining) · `d` done | `x`: tail drops one item · `s`: remainder re-competes |
| Interruption | `i` … `r` | ad-hoc Wall from t_i to t_r; Active block paused | segments after t_r shift; tail drops; log `lost=` |
| Energy report | `0`–`5` | posterior δ | slots re-energised; ci-5 items may be deferred (diagnostics) |
| Break overran | timer | actual logged | next block starts now; tail drops |
| Late wake / arrival | `tm wake`, `tm arrive` | window, budget | proportional day |
| Location change | `l` | `runtime.loc` | `home_max_ci` applied |
| Calendar sync adds a wall | `R` / auto | new Interval | flow around; window extends |
| Deadline or estimate edited | VS Code | need, u | may become HOT; hysteresis does not apply to 0 |
| Routine skipped | `k` | instance Skipped / deferred | mandatory if last chance |
| Event arrives | `tm event reply` | Waiting → Todo | item becomes a candidate |
| Idle (nothing running ≥ `idle_min`) | idle prompt | `w` start next block · `b` break · `t` routine · `i` interrupt · `l` leak (logged as Lost) | — |

### 9.1 Overtime prompt

```
┌ Overtime ───────────────────────────────────────────────────┐
│ Exercises 5.3–5.5     est 2b ×1.6 = 3h12m · elapsed 3h19m    │
│   x  extend +1 block      → drops: Review the drafts (p3)     │
│   s  stop, demote rest    → 0.5b stays in week queue          │
│   d  done                                                     │
│   any other key: ask again in 15m                             │
└───────────────────────────────────────────────────────────────┘
```

The prompt computes the consequence by running `plan()` with each option and diffing. Fires at `est × r`, then every `overtime_reprompt_min`.

### 9.2 Idle prompt

After `idle_min` (default 12) with no Block, Break, Routine, or Wall running:

```
┌ Nothing is running (14m) ───────────────────────────────────┐
│  w  work (starts next block)   b  break   t  routine        │
│  i  interruption               l  leak (log it, no judgment) │
└─────────────────────────────────────────────────────────────┘
```

Whatever you press, the elapsed gap is attributed (`leak` → `Lost`). This is what keeps the leak ledger (§11) honest.

---

## 10. Logs and runtime state

### 10.1 `.tm/log.jsonl` — one JSON object per line, append-only

```json
{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":490}
{"t":"…T07:00","ev":"arrive","loc":"lounge","window":["07:00","15:00"],"budget":6}
{"t":"…T07:02","ev":"start","id":"t1","pred":5,"rep":5,"hsw":0.95,"slept_min":490,"loc":"lounge","blocks_done":0,"since_break_min":0}
{"t":"…T08:09","ev":"done","id":"t1","est_min":60,"actual_min":67,"went":1,"tags":["lean"],"ci":5}
{"t":"…T09:08","ev":"break","planned_min":20,"actual_min":24,"where":"walk"}
{"t":"…T09:32","ev":"energy","pred":5,"rep":4,"hsw":3.45,"loc":"lounge"}
{"t":"…T12:10","ev":"interrupt","id":"t4"}   {"t":"…T13:05","ev":"resume","lost_min":55,"dropped":["t5"]}
{"t":"…T15:40","ev":"idle","attributed":"leak","min":14}
{"t":"…T16:10","ev":"routine","item":"package","inst":"2026-09-07","status":"done","actual_min":18}
{"t":"…T21:30","ev":"plan","hash":"a91f…","replans_today":4,"drift_min":75}
{"t":"…","ev":"event","name":"reply","id":"a4"}
{"t":"…","ev":"demote","id":"m2","from":"2026-W37","to":"2026-09","est_min":180}
{"t":"…","ev":"undo","of":"done","id":"t4"}
```

`log::replay(range)` derives: blocks done per item and per day, instance statuses, energy observations, durations, breaks, lost minutes, leak minutes. Nothing in the log is ever edited; `tm undo` appends a compensating event.

### 10.2 `.tm/state.json` (runtime, not committed)

```json
{"date":"2026-09-07","wake":"06:05","arrival":"07:00","loc":"lounge","window":["07:00","16:00"],"budget":6,
 "active":{"id":"t3","started":"09:32","est_min":192,"paused":false},
 "break":null,"interrupt":null,
 "last_plan_hash":"a91f…","priorities_yesterday":{"d1":1,"m2":3},
 "closed":{"day":"2026-09-06","week":"2026-W36","month":"2026-08"}}
```

---

## 11. Monitors (`review.rs`)

All computed from the log and the tree; none stored. **Status line (always visible):** blocks done / budget · leak minutes · adherence %.

| Monitor | Definition | Surface |
|---|---|---|
| Blocks / load | blocks done; load = Σ block_min × ci / 5 | status line; day review |
| Leak ledger | minutes attributed `leak` + unattributed gaps > idle_min; longest single leak | status line; day review |
| Adherence | % of planned Blocks started within ±10m of plan; % completed | status line |
| Start latency | wake → arrive; arrive → first `start` | day review; week trend |
| Lounge rate | `P(lounge | wake hour)`, streak | week review |
| Replans and drift | count of `plan` events today; Σ minutes segments moved | Diagnostics pane |
| Break integrity | planned vs actual per break; share > 2×; histogram by `where` | day review; week histogram |
| Rest debt | planned breaks skipped or cut, cumulative today | warning in status line when > 40m |
| Energy mix | minutes at each ci; share of budget with ci ≥ 4; `↓` count | day bar legend; week stacked bars |
| Energy calibration | MAE(pred, rep) overall and by hour; bias sign | Energy pane; `tm model --compare` |
| Estimate calibration | actual/est per tag, trend | Queue "fits"; week review |
| Plan honesty | planned blocks / realistic budget (day, week) | warning at `tm plan` when > 1.1 |
| Sleep panel | slept, onset (from `wake --onset`), next-day blocks alongside; display only | week review |
| Deadline health | min slack; #HOT; #IMPOSSIBLE; #overdue | Week pane header |
| Demotion churn | items with ≥ 2 stamps; carry-over blocks week over week | month review |
| Optional quota | optional minutes vs `max:`; optionals outside Rest | day bar (dotted segments) |
| Waiting | items in `[?]` with days waiting and timeout | Necessities screen |
| Week heat grid | 7 day bars side by side | week review |

---

## 12. TUI (`tm tui`, ratatui)

ratatui + crossterm with `EnableMouseCapture` (hover and click on the day bar). Screens `1`–`5`; `?` help; `:` command line accepting any CLI verb; `e` opens the selected item in VS Code at its line (`code -g file:line`). A `notify` watcher on `plan/` triggers re-parse and re-render. Layout ≥ 110 columns as drawn; below that, panes stack (Now on top, Timeline below, Week folded into the status line).

### 12.1 Screen 1 — Today

```
 tm · Mon 2026-09-07 · 10:42 · lounge · wake 06:05 (8h10m) · pred 4 rep 4 ·  ● 3/6 · leak 14m · adherence 83% · window → 16:00 · lost 0
 ████▓▓▓░░▒▒▒▒▒▒▒▓▓▓▓▓▓▓░░▒▒▒▒▒▒▒▒▒▒▓▓▓▓░░▒▒▒▒▓▓▓▓░░░░░░░░░░░░████████████   ▲ 10:42   (hover: item · dur · ci · p)
 ████▓▓▓░░▒▒▒▒▒▒▒▒▒▒▓▓▓▓░░▒▒▒▒▒▒▒▒▒▒▒▒▒▒▒░░▒▒▒▒▒▒▒░░░░░░░░░░░░████████████   plan @07:00
┌─ Timeline ─────────────────────────┐┌─ Now ─────────────────────────────────────────┐┌─ Week W37 · 8/20 ─────────────────┐
│ 07:00 5 ✓ Read ch.6 §1–2       67m ││ ci4 p1  Exercises 5.3–5.5          @m1 #lean   ││ ▶ m1 Finish ch.5 exercises ▓▓▓░░░ 3/6│
│ 08:00 5 ✓ Read ch.6 §3         58m ││ elapsed 1h22m ▐████████░░░░░░░▌ est 2b ×1.6    ││   m2 Rollback tests        ░░░░░░ 0/6│
│ 09:00 · ✓ break 20m            24m ││ next 11:20 lunch · 11:50 CC drafts (4↓3)       ││ ✓ m3 Read ch.6            ▓▓▓    3/3│
│ 09:20 4 ▶ Exercises 5.3–5.5    2b  ││                                                ││ ! d1 CS 234 pset 2  p1  u=0.6  fits  │
│ 11:20 ·   lunch 30m                ││ d done  x extend  s stop  b break  i interrupt ││──── HOT / overdue ───────────────────│
│ 11:50 4↓  CC drafts rollback tests ││ 0-5 energy  l location  k skip  n note        ││ ⚠ a3 Pick up package   due today     │
│ 12:50 ⏰  Meeting w/ host      1h  │└────────────────────────────────────────────────┘│──── Waiting ─────────────────────────│
│ 13:50 ·   break 20m                │┌─ Energy today ─────────────────────────────────┐│ ? a4 Prof. Lee reply   2d / 7d       │
│ 14:10 3   Review the drafts    1b  ││ pred 5 5 5 4 4 4 4 3 3 2 2                     ││──── Diagnostics ─────────────────────│
│ 15:10 ─── window ends 16:00 ────── ││ rep  5 5 · 4 · · · · · · ·   (· = not asked)   ││ 1 underused (4→3) · 0 ci-5 lost      │
│ 15:10 1 ⚠ pick up package      20m ││      07 08 09 10 11 12 13 14 15 16 17          ││ replans 4 · drift 75m · rest debt 0  │
│ 17:30 ·   dinner 30m               │└────────────────────────────────────────────────┘│ t5 blocked by t4                      │
│ 18:00 ○   Severance S3E4       1h  │                                                  │                                       │
│ 21:30 🌙  wind-down · bed 22:00    │                                                  │                                       │
└────────────────────────────────────┘                                                  └───────────────────────────────────────┘
 :                                                                        j/k move · Enter open · e edit · r replan · R sync · ? help
```

**Day bar widget** (`daybar.rs`): one row per 24h from wake to wake, `cols = width`, each cell = 24h/cols. Left of the cursor renders the log (actual); right renders the current plan; a second row renders the plan as it stood at arrival (ghost). Cell colour = project hue (hash of root id, from a 12-colour palette); brightness = `ci` (0 black … 5 full); routines grey; breaks light grey; Lost/leak hatched orange; interruptions hatched red; optionals dotted; walls solid dark. Mouse move over a cell shows a tooltip: `title · duration · ci · p · @root`; click selects the item. The same renderer writes `day/<date>.svg` with `<title>` per segment (VS Code preview shows them on hover).

### 12.2 Screen 2 — Queue

```
┌─ Month 2026-09 ─────────────┐┌─ Week W37 · planned 20 / budget 25 ─────────────────┐┌─ Tasks @m2 ───────────────────────┐
│ !1 O1 Lean ch.8        ▓▓░  ││ p1 5 6b m1 Finish ch.5 exercises  @O1  ▓▓▓░░░       ││ p3 3 1b CC drafts rollback tests   │
│ !1 O2 Soundcode demo   ░░░  ││ p1 4 6b d1 CS 234 pset 2  due Fri  u=0.6  fits 6/6  ││ p3 3 1b Review the drafts  ⛔ after t4│
│ !3 O3 Courses + admin  ░░░  ││ p3 4 6b m2 Rollback tests         @O2  ░░░░░░       ││ p3 4 2b Fix rollback edge cases    │
│                             ││ p1 5 3b m3 Read ch.6              @O1  ✓            ││                                    │
│ Demoted (1)                 ││ p5 2 2b m4 Pick winter courses    @O3  ░░           ││ fits this week: 6b of 6b           │
│ · m9 Rollback edges  W36    ││ p3 5 8b x2 Midterm review  due Oct 20  u=0.15       ││                                    │
└─────────────────────────────┘└─────────────────────────────────────────────────────┘└────────────────────────────────────┘
 h/l pane · j/k · J/K reorder (rewrites line order) · Enter drill · a add · c ci · E estimate · P priority (roots) · D demote · A readopt · x drop · e edit
```

`J`/`K` rewrite line order in the file. `P` on a root sets `!k`. The `u` and `fits` columns come from the EDF pass and change daily; `p` moves at most one bin per day (hysteresis) so the list is stable enough to read.

### 12.3 Screen 3 — Necessities

Left: this week's walls and routine windows on a 7-column hour grid, conflicts in red. Right: dated items sorted by `u` with `need / capacity / u / p`, IMPOSSIBLE first with the shortfall; then Waiting items with days waiting and timeout; then overdue-persist items. Keys: `E` estimate, `e` edit, `t` mark event arrived, `k` skip instance.

### 12.4 Screen 4 — Review

```
 Day 2026-09-07 · lounge · 5/6 blocks · load 18.4 · window 07:00–16:00 · lost 55m (call) · leak 14m · adherence 83%
 done      t1 t2 t3 t4          demoted  t5 (0.5b → week)         underused 1        replans 4 · drift 75m
 energy    pred 5 5 5 4 4 4 4 3 3   rep 5 5 4 4 4 3 3 3 ·          MAE 0.4   bias −0.3 after 13:00
 estimates lean ×1.6 (n=9)   soundcode ×1.1 (n=4)   admin ×0.8 (n=6)
 breaks    planned 20m ×3 · actual 24 (walk) 31 (seat) 20 (walk) · rest debt 0
 sleep     8h10m · onset 25m
 tomorrow  first candidate t5 (after t4) · d1 p1 u=0.6 · a3 done
                                                             w write to day file · c ask Claude Code for prose
```

Week review adds milestones hit/demoted, blocks per day bars, the week heat grid, lounge rate, calibration trends, prior vs learned curve overlay, plan honesty. Month review adds outcomes, demotion churn, and a proposed cut list.

### 12.5 Screen 5 — Inbox and capture

```
┌─ Capture ───────────────────────────────────────────────────────────────┐
│ > pset2 fri 6b ci4 max 2b/d                                             │
│   parsed  - [ ] 4 6b pset2  due:2026-09-11T23:59 max:2b/d  → week/2026-W37.md #Milestones │
│   Enter save · Tab change file · Esc cancel                             │
└─────────────────────────────────────────────────────────────────────────┘
 Inbox (4)   t triage line · C Claude Code triages all · x drop
```

### 12.6 Keymap

| Scope | Key | Action |
|---|---|---|
| global | `1`–`5` `?` `:` `q` | screens · help · command line · quit |
| global | `e` `r` `R` | edit in VS Code · replan · sync calendar + replan |
| today | `d` `x` `s` | done · extend 1b · stop and demote remainder |
| today | `b` (+ `w`/`s`/`b`/`p`) | break (where: walk / seat / bed / phone) |
| today | `i` / `r` | interrupt / resume |
| today | `0`–`5` | energy report now |
| today | `l` `k` `n` `Space` | location · skip routine · note · pause timer |
| queue | `h` `l` `j` `k` `J` `K` `Enter` | navigate · reorder · drill |
| queue | `a` `c` `E` `P` `D` `A` `x` | add · ci · estimate · priority · demote · readopt · drop |
| necessities | `E` `t` `k` `e` | estimate · event arrived · skip · edit |

---

## 13. CLI (`tm`)

Every verb accepts `--json`; exit codes: 0 ok, 1 error, 2 validation problems (`check`), 3 conflict (write race).

```
tm init [dir]                                skeleton: config, CLAUDE.md, skills, hooks, empty files
tm wake [HH:MM] [--slept 8h10m] [--onset 25m]
tm arrive [lounge|home|<name>]               sets location; sync calendar; window + budget; plan
tm plan [--week] [--allow-home] [--diff] [--explain ^id]
tm now                                       current block + next 3 segments
tm start ^id | tm done [--partial] [--at HH:MM] | tm extend [1b] | tm stop [--at HH:MM]
tm break [20m] [--where walk|seat|bed|phone]
tm interrupt | tm resume | tm pause | tm energy 0-5 [--at HH:MM] | tm idle <w|b|t|i|l>
tm add "<line>" [--to <file>] [--section <name>]
tm edit ^id [ci=4] [est=2b] [due=…] [title="…"] [p=2] [--set key=value] [--unset key]
tm move ^id <backlog|month|week|day>         moves the line between horizon files
tm rank ^id <n> | tm demote ^id | tm readopt ^id | tm drop ^id | tm done ^id (retro, no timing)
tm event <name> [^id]                        resolves on-event / after:event dependencies
tm skip <routine> | tm routine done <name> [--min 18]
tm close <day|week|month> [--drop ^id …]     lifecycle (§6.3); auto-run when overdue
tm sync-cal
tm review <day|week|month> [--write] [--date …]
tm model --fit | --show | --compare
tm log --tail 20 | --since 7d | --item ^id
tm undo                                      compensating event for the last state change
tm triage [--json]                           inbox lines with parse previews
tm check [--fix-ids]                         validate; --fix-ids appends missing ids
tm tui
```

`tm plan --explain ^id` prints why an item is where it is: `p = k(3) + bin(u=0.31 → +1) = 4; slot 11:50 energy 4, ci 3, gap 1; deps ok; cap 2b/d: 1b used`.

`tm stop --at HH:MM` and `tm done --at HH:MM` end the running block when it ended — the latest such time at or before now, so `--at 23:40` typed in the morning is last night — and log that instant; the minutes are worked up to it. An end before the block's start, or before a pause, interruption or running break the log or `state.json` already holds after it, is refused by name, and so is `--at` on a retro `tm done ^id`. `tm energy 0-5 --at HH:MM` reports energy at today's HH:MM, unless that is more than 12 hours after now (elapsed time, so a DST change moves the edge by its hour), when it is yesterday's — `--at 23:40` typed at 00:40 is last night, `--at 10:30` at 09:00 is today — and the report's hours since wake and night slept are that day's. `tm wake` is refused while a block, an interruption or a break is still running; `tm break --where` takes one of the four places of §12.6.

`tm interrupt` while a break is running ends the break first — its `break` line logged as `tm break` logs its end, at the interruption's instant — and then begins the interruption, as `tm start` ends a running break before its block starts; no clock-stopping mark is logged inside a running break.

---

## 14. Claude Code integration

Claude Code is the language-level frontend: capture in natural language, the Sunday planning conversation, triage, review prose. It acts through the CLI (`--json`) and by editing human sections of `.md` files. It never edits generated sections, never marks blocks done, never touches `.tm/`.

**`plan/CLAUDE.md`** (generated by `tm init`, keep under ~100 lines):

```markdown
# tm — rules for Claude Code
Files: month/ week/ day/ backlog.md routines.md optional.md calendar/ inbox.md. Horizon = file. Rank = line order.
Grammar: `- [ ] <ci 0-5> <est> Title @parent #tag key:value ^id`. Fields: due at win dur pref every after-done on-event on-miss min max after loc est. Flags: open atomic manual travel-day hot.
Always: add items with `tm add "..."` (or write the grammar exactly, then run `tm check`). Read `tm plan --json` before reasoning about today. Use `tm model --show` multipliers when estimating.
Never: edit between `<!-- tm:plan start/end -->`; edit `## Log`; mark blocks done; change an existing item's ci, est, or priority unless asked; reorder `month/` outcomes without confirmation; touch `.tm/`.
Demote, never delete. Explain the diff after `tm plan --diff`.
```

**Skills** in `.claude/skills/<name>/SKILL.md` (project-level; `.claude/commands/<name>.md` also still works — see https://docs.claude.com/en/docs/claude-code/overview):

| Skill | Behaviour |
|---|---|
| `/plan-week` | reads `month/` (outcomes, `# Demoted`), `backlog.md` dated items, `calendar/`, `tm plan --week --json`, `tm review week --json`; proposes 3–5 milestones with calibrated estimates, demoted items pre-selected, carry-over and plan-honesty shown; writes `week/<next>.md` **only after confirmation** |
| `/plan-month` | reads last month's review; proposes outcomes with `!k`, cuts for anything with ≥ 2 stamps; writes after confirmation |
| `/triage` | `tm triage --json` → assigns ci, estimate, parent, file; `tm add`; asks when ambiguous |
| `/capture <text>` | natural language → grammar → `tm add`; "pset 2 is due Friday night, six blocks, two a day max" → `- [ ] 4 6b pset 2 due:…T23:59 max:2b/d` |
| `/replan` | `tm plan --diff`; two sentences on what moved and why |
| `/review-day`, `/review-week` | `tm review … --json` → prose into `## Notes`; flags repeated demotions, estimate drift, leak trend |
| `/explain ^id` | `tm plan --explain ^id` in plain language |

**Hooks** (generated by `tm init` into `.claude/settings.json`): a `PostToolUse` hook on Edit/Write under `plan/` running `tm check`; a git pre-commit hook running `tm check`.

---

## 15. Calendar sync (`ics.rs`)

- `config.calendar.ics_urls`: Google Calendar private ICS addresses. `tm sync-cal` fetches (`ureq`), parses (`ical`), keeps events in `[this week − 1, this week + 1]`, writes `calendar/YYYY-Www.md` as Interval items with stable ids derived from the ICS `UID` (so re-syncs don't change ids). Lines tagged `manual` are preserved verbatim.
- Flights: events matching `config.calendar.flight_regex` (default `\b[A-Z]{2}\s?\d{2,4}\b` plus `✈`) get `buffer:2h travel-day`.
- Runs on `tm arrive` when `sync_on_arrive = true`, and on `R`. No write-back in v1.

---

## 16. Configuration (`config.toml`, complete)

```toml
[day]
block_min             = 60
break_after_blocks    = 2
break_min             = 20
window_hours          = 8
window_cap            = "19:00"
budget_ratio          = 0.75
wind_down             = "21:30"
bed                   = "22:00"
overtime_reprompt_min = 15
idle_min              = 12
min_last_block_min    = 30

[week]
plan_ratio = 0.8                 # warn if planned > 0.8 × budget

[priority]
default_priority = 3             # k for roots without !k and for untied items
bins             = [0.5, 0.25, 0.1]
safety           = 1.3
hysteresis       = true
batch_max_min    = 20

[location]
home_max_ci = 3

[energy]
prior_weight          = 5
decay_days            = 30
duration_prior_weight = 5
posterior_full_hours  = 3
posterior_zero_hours  = 6
[energy.prior.lounge]            # by hours since wake
"0-1" = 4
"1-5" = 5
"5-8" = 4
"8-10" = 3
"10+" = 2
[energy.prior.home]
"0-1" = 3
"1-4" = 4
"4-8" = 3
"8+" = 2
[energy.sleep_debt]
under_hours = 7.0
shift       = 1

[expected]                       # used by the lookahead until learned
arrival = { Mon = "07:00", Tue = "07:00", Wed = "07:00", Thu = "07:00", Fri = "07:00", Sat = "10:00", Sun = "10:00" }
p_lounge = { Mon = 0.9, Tue = 0.9, Wed = 0.9, Thu = 0.9, Fri = 0.8, Sat = 0.5, Sun = 0.4 }

[calendar]
ics_urls       = ["https://calendar.google.com/calendar/ical/…/basic.ics"]
sync_on_arrive = true
flight_regex   = "\\b[A-Z]{2} ?\\d{2,4}\\b"

[tui]
palette   = ["#e6194b","#3cb44b","#4363d8","#f58231","#911eb4","#42d4f4","#f032e6","#bfef45","#fabed4","#469990","#dcbeff","#9A6324"]
min_width = 110
editor    = "code -g {file}:{line}"
```

---

## 17. Implementation plan

Estimates in the app's own units. Each milestone has a definition of done that Claude Code can verify by running the listed tests.

| # | Milestone | Est. | Definition of done |
|---|---|---|---|
| M1 | `grammar.rs`, `model.rs`, `store.rs`, `check.rs` | 5b | `proptest` round-trip: parse→serialize is byte-identical for every fixture and for generated lines; `tm check` catches dangling parents, cycles, duplicate ids, bad values; `write_line` survives a concurrent edit test (mtime race → retry → conflict) |
| M2 | `tree.rs`, `recur.rs`, `horizon.rs` | 4b | rollups, effective due for prep children, instances for all four recur kinds over a range with log replay, series heads, deps; `tm close week` snapshot tests on fixtures |
| M3 | `capacity.rs`, `priority.rs` | 4b | EDF pass unit tests: two feasible deadlines that are jointly infeasible are flagged; bins; hysteresis; explicit `!k` inheritance; `tm plan --explain` output snapshot |
| M4 | `energy.rs` (prior + posterior), `planner.rs`, `emit.rs` | 7b | all §8.3 invariants as property tests; snapshot of the generated day section and SVG for three fixture days (early start, late start with a wall, home day) |
| M5 | CLI verbs + `log.rs` + `state.json` | 4b | every verb in §13 has an integration test against a temp `plan/` dir; `tm undo` compensates each state change; `--json` schemas snapshot-tested |
| M6 | TUI: Today (timeline, Now, energy pane, day bar with hover), overtime and idle prompts | 7b | manual acceptance in VS Code terminal on macOS and Linux; `ratatui` `TestBackend` snapshots of each pane at 120 and 90 columns |
| M7 | TUI: Queue, Necessities, Inbox/capture | 5b | J/K reorder rewrites files byte-faithfully; capture preview matches `tm add` |
| M8 | `review.rs` monitors + Review screen + `model --fit` v1 | 5b | monitors computed from a synthetic 14-day log fixture match hand-computed values; `model.json` round-trips |
| M9 | `ics.rs` sync, `tm init`, CLAUDE.md + skills + hooks | 3b | sync against a fixture `.ics` preserves `manual` lines and stable ids; `tm init` produces a tree that passes `tm check` |
| M10 | model v2, ActivityWatch ingestion, notifications | later | after ~60 days of log |

≈ 44 blocks. Start living in it after M6.

### 17.1 Fixtures (`tm-core/tests/fixtures/`)

`plan-basic/` (the examples in §4.3, three weeks of history in `log.jsonl`), `plan-conflicts/` (overlapping walls, impossible deadline, cycle), `plan-recur/` (every kind of recurrence with partial completion history), `plan-home-day/`, `plan-travel-day/`, `sample.ics`.

### 17.2 Implementation notes for Claude Code

- **Parsing:** hand-written tokenizer (split on whitespace outside the title; the title ends at the first token that starts with `@ # ! ^` or matches `[a-z-]+:`). Keep `Vec<Token>` on the item for byte-faithful rewriting; do not regenerate lines from the struct. Use `winnow` only if the hand-written version exceeds ~300 lines.
- **Time:** `chrono` with a fixed local timezone from config (`tz = "America/Chicago"`); store timestamps in the log with offsets; never use naive datetimes across a DST boundary in the planner (work in `DateTime<Tz>`, convert at the edges).
- **Ids:** new ids are decimal numerals generated by the kernel's proved `freshId` (the first numeral from a seed upward that no id in the tree claims, so uniqueness against the whole tree is a theorem); ids already in real files are alphanumeric and remain valid — the earlier 4-character `[a-z0-9]` ids and §4.3's `^O1` alike; assign on first parse by appending ` ^id` to the line (this is the one write `parse` is allowed to trigger, behind `--fix-ids` or the TUI's first load).
- **Purity:** `plan()` takes references and returns an owned `DayPlan`; all randomness and clocks are injected. The TUI calls `plan()` on every event; it is fast enough (microseconds) that caching is unnecessary.
- **Errors:** `thiserror` enums in core (`ParseError`, `StoreError::Conflict`, `CheckProblem`), `anyhow` in the binary. `Conflict` must carry both versions so the TUI can show a diff.
- **Tests first for §8.3 invariants**: generate random trees with `proptest` (≤ 40 items, random ci/est/due/deps), random logs, and assert the invariants; they are the specification.
- **SVG:** write by hand (a few `<rect>` and `<title>` elements per segment); no crate needed.
- **Watching:** `notify` debounce 200 ms; on change, re-parse the changed file only, then replan.
- **Mouse:** `crossterm::event::EnableMouseCapture`; handle `MouseEventKind::Moved` for the day-bar tooltip and `Down(Left)` for selection; everything else stays keyboard-only.

### 17.3 Decisions made (change in config) and open questions

Decided: block 60m, break 20m/2 blocks; window arrival + 8h capped 19:00; budget 6; home cap ci 3; priority bins 0.5/0.25/0.1 with safety 1.3; default priority 3; hysteresis on; batching at 20m; `on_miss` defaults per §5.3; Rust + ratatui.

Open: (1) should a HOT item be allowed to take a ci-5 slot when its own ci is 4 (current: yes — deadline beats slot efficiency); (2) should optionals be time-boxed with the overtime prompt (current: yes); (3) should `min:` floors on open items count toward the day budget (current: yes, they are blocks like any other).

---

## Cheatsheet

**Files** · `month/` (outcomes, `!k`, `# Demoted`) · `week/` (milestones, tasks, dated items) · `day/` (generated plan, `# Pinned`, `## Log`, `## Notes`, `.svg`) · `backlog.md` (untied, far-out dated, `## series:`) · `routines.md` · `optional.md` · `calendar/` · `.tm/{log.jsonl,model.json,state.json}` — horizon = file, rank = line order

**Line** · `- [ ] <ci> <est> Title @parent #tag key:value ^id` · states `[ ] [>] [x] [-] [~] [?]` · est `Nb|Nm|Nh` · `!k` on roots · fields `due at win dur pref every after-done on-event on-miss min max after loc buffer est` · flags `open atomic manual travel-day hot`

**Fields, one entity** · scope finite/open · shape none/point/interval/window · recur none/calendar/after-done/on-event · on_miss expire/persist/next · budget min/max per d/w/m · ci 0–5 · splittable · after · loc · prep = child of an interval (due = its start)

**Derived, never stored** · effective due · root priority · remaining · progress · instances · series head · allocation · the whole day plan

**Priority** (0 = highest) · walls off-scale · `p=0` HOT (u ≥ 1) / overdue-persist / mandatory window / `hot` · `p = k + bin(u)` dated or floored, `u = need/capacity` after the EDF pass, bins 0.5/0.25/0.1 → +0/+1/+2/+3 · `p = k+2` finite undated · `p=5` optional · sort `(p, root line, own line)` · ≤ 1 bin better per day (hysteresis) · batch items ≤ 20m

**Energy** · ci and slot both 0–5 · assign `ci ≤ slot`, prefer small gap, `↓` at gap ≥ 2, never over · home cap 3 · prior by hours-since-wake × loc · report `0–5` at block start, `1/2/3` at end · learned: `energy[b] = (n0·prior + Σ w r)/(n0 + Σ w)`, `w = e^{−age/30d}`, `n0 = 5` · duration `r = actual/est` per (ci, tag) · plan with `est × r`

**Planner** · walls → routines (mandatory first) → slots + energy → priorities → assign by key with filters (deps, waiting, loc, ci, cap, atomic) → deferred routines → rest + optionals → emit · invariants: pure, no overbooking, monotone rank, energy filter, tail-drop only

**Lifecycle** · day close: `[>]`→`[ ]` + `est:`; pinned → week · week close: `[-]` + copy to month `# Demoted` (`est:`, `demoted:W37`); overdue-persist → backlog `# Overdue` · month close: carry or `--drop` · `readopt` / `move` between horizon files · ≥ 2 stamps ⇒ cut or re-scope

**Recurrence** · calendar `every:` · completion `after-done:2d~1d` · event `on-event:reply/7d` (`[?]` while waiting) · series section = one active head · deps `after:` gate eligibility, not priority

**Keys (Today)** · `d x s` · `b`+where · `i r` · `0–5` · `l k n Space` · `e r R` · idle prompt `w b t i l`

**CLI** · `wake → arrive → plan → start/done/extend/stop` · `add edit move rank demote readopt drop event skip close` · `review day|week|month` · `model --fit` · `check` · every verb `--json`

**Status line** · blocks done/budget · leak min · adherence % · window → · lost

**Build** · M1 grammar/store → M2 tree/recur/horizon → M3 capacity/priority → M4 energy/planner/emit → M5 CLI/log → M6 Today TUI (start using) → M7 Queue/Necessities/Inbox → M8 monitors/model → M9 ICS/init/Claude Code · ≈ 44 blocks
