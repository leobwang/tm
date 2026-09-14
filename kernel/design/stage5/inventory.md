# Stage 5 fact base: the log, its replay, its consumers, its size, and D10's inputs

Facts only; no design. Every claim cites a file and a function or type **name**
(AGENTS §5.11: names, not line numbers). Paths are relative to the repo root
`/home/leobwang/code/projects/tm` (the docs call it `/Users/psixyzt/code/planner`).
The oracle is the fork-point Rust in `tm-core/`. Anything this pass measured says
how it was measured. Anything estimated is marked **ESTIMATE**. Anything that looks
like an owner question is marked **FLAG** and is not decided here.

Read at branch `rebuild-on-lean`, HEAD `c2cf4dc`, with `kernel/TmKernel/TmKernel/Tree.lean`
untracked. Another workflow is building stage 5 in that tree, so kernel line counts may move.

---

## 0. Where the log lives and how the Rust reads it

| fact | where |
|---|---|
| File: `.tm/log.jsonl`, one JSON object per line, append-only; `tm undo` appends and never edits | spec §10.1; `tm-core/src/store.rs` `LOG_PATH` |
| **The CLI reads the whole file on every `Ctx` load:** `read_log` returns `Log::parse(&store.read_text(LOG_PATH)?)` | `tm/src/cli/ctx.rs` `read_log` |
| **The CLI replays the whole log on every `Ctx` load and reload:** `log.replay(None, cfg.tz)`, where `None` is the full range | `tm/src/cli/ctx.rs` `Ctx::load_with`, `Ctx::reload` |
| The TUI gets its replay from the same `Ctx` (`replay: ctx.replay.clone()`) and replaces it on reload | `tm/src/tui/mod.rs`; `tm/src/tui/app.rs` (`self.replay = data.replay`) |
| `FsStore::read_text` is `fs::read_to_string`. **Invalid UTF-8 anywhere in the file fails the whole read** with an I/O error before `Log::parse` runs. The per-line UTF-8 tolerance lives only in `Log::parse_bytes`/`Log::read`, which the CLI does not call | `tm-core/src/store.rs` `FsStore::read_text`; `tm-core/src/log.rs` `Log::parse_bytes` |
| Appends from the CLI go through `FsStore::append_text` (plain `O_APPEND` `write_all`). **It does not add a newline after a torn last line.** Only `Log::append_all` does that, and no CLI path calls it | `tm-core/src/store.rs` `FsStore::append_text`; `tm/src/cli/ctx.rs` `Ctx::append_entry`; `tm-core/src/horizon.rs` `Ctx::log`; `tm-core/src/log.rs` `Log::append_all` |
| Defect **G9** in the plan: "`Log::read` on invalid UTF-8; `append_all` on a torn last line; `FsStore::abs` accepting an escaping path", verdict **M**, "Rust; I/O stays in Rust" | `PLAN-lean-kernel.md` §4 defect table |
| The undo stack reads the raw text twice. `log_len` counts non-blank lines (`t.lines().filter(non-blank)`). `new_events` runs `Log::parse(text).entries.skip(from)`. **A malformed line counts in `log_len` but is not an entry**, so the two counts can disagree | `tm/src/cli/undo.rs` `log_len`, `new_events` |
| Timestamps written by the CLI: `ctx.now = g.now.unwrap_or_else(Local::now().fixed_offset())`. **The offset in each `t` is the machine's local offset (or `--now`'s), not `cfg.tz`'s** | `tm/src/cli/ctx.rs` `Ctx::load_with` |

### 0.1 Line tolerance (`Log::parse_bytes`)

1. Split the bytes on `\n` and number lines from 1 (`LogWarning.line`).
2. A line that is not UTF-8 becomes a `LogWarning` whose `text` is `from_utf8_lossy` and whose `error` is `"invalid UTF-8: …"`.
3. A trailing `\r` is trimmed. A blank line (after `trim`) is skipped silently.
4. `LogEntry::parse` (serde) failure becomes a `LogWarning {line, text, error}`. Parsing continues.
5. A **torn last line** (no newline, truncated JSON) is just a malformed line and becomes a warning. A torn line that happens to be valid JSON is accepted.
6. What makes a line a warning, per `tests/fixtures/logs/malformed.jsonl` (11 lines; this corpus has 1 good `wake`, 1 good `note`, 1 unknown event, and the rest warnings or blank):
   - not JSON;
   - a known `ev` with a missing required field (`wake` without `slept_min`);
   - no `t`;
   - a known `ev` with a wrongly typed field (`est_min:"sixty"`); the error names the field through `Known::field_error`;
   - an unparseable `t`;
   - a top-level array;
   - `ev` not a string (`"ev":7` gives "`ev` must be a string");
   - a blank line, which is skipped rather than warned.
7. `{"ev":"mood","level":3}` is **not** a warning. It becomes `Event::Unknown`.

`Log::read` treats a missing file as an empty log; any other I/O error is `LogError::Read`.

### 0.2 Deserialisation rules (`Event`'s hand-written `Deserialize`)

- `ev` is read first. If it is in `EVENT_NAMES`, the payload is decoded **strictly** through the private `Known` enum. A bad payload is an error, never `Unknown`.
- Any other `ev` string becomes `Event::Unknown { ev, rest: Map }`. `rest` holds every other key (sorted on re-serialisation). `LogEntry`'s `t` is taken out by `#[serde(flatten)]` first.
- **Unknown extra keys on a known event are ignored.** There is no `deny_unknown_fields`, and they are dropped on re-serialisation.
- `Option<_>` fields accept `null` as `None`. Fields with `#[serde(default)]` may be absent.
- Integer types are serde's. `u8` fields (`pred`, `rep`, `went`, `ci`) accept 0..=255 and **no range check to 0..5 exists in log.rs**. The only clamp is `ci.min(5)` inside `Machine::credit`. `u32` fields accept 0..=4294967295. `hsw` is `f64`.
- `t`: `parse_timestamp` accepts RFC 3339 (`DateTime::parse_from_rfc3339`: seconds, optional fractional seconds, `Z` or `±HH:MM`). As a fallback it accepts `%Y-%m-%dT%H:%M%:z` with no seconds. `fmt_timestamp` writes whole seconds with the offset (`2026-09-07T06:05:00-05:00`). Instants compare **by absolute time**, whatever the offset (`hsw_matches_spec` compares `+01:00` against `-05:00`).

---

## 1. Every event kind

The source is `tm-core/src/log.rs` `define_events!`, which defines `Event`, the private `Known`, and `EVENT_NAMES` (25 known tags, in spec §10.1 order). Spec §10.1 shows 13 example lines covering 14 kinds (`wake arrive start done break energy interrupt resume idle routine plan event demote undo`). The other 11 exist only in the Rust.

Every line also carries `t` (the instant) and `ev` (the tag). "opt" means `Option`; "def" means `#[serde(default)]` (absent is 0, `[]` or `false`).

| `ev` | fields (type, optionality) | primary id (`Event::primary_id`) | state change (`is_state_change`) | replay facts it feeds (`Machine::step`) |
|---|---|---|---|---|
| `wake` | `slept_min: u32`; `onset_min: opt u32` | — | yes | `DayIndex` wakes; `slept_by_day`; `DayReplay.{wake, slept_min, onset_min}` |
| `arrive` | `loc: String`; `window: [String; 2]` (`HH:MM`, not validated in log.rs); `budget: u32` | — | yes | `DayReplay.{arrival, loc, window, budget}` (first only); `loc_changes` (every one); `energy::arrivals_from_replay` |
| `start` | `id: String`; `pred: u8`; `rep: opt u8`; `hsw: f64` def; `slept_min: u32` def; `loc: String`; `blocks_done: u32` def; `since_break_min: u32` def | `id` | yes | cuts any open block; `EnergyObs` when `rep` is set; `DayReplay.{first_start, starts}`; opens a block. `blocks_done` and `since_break_min` are **not read by replay** |
| `done` | `id: String`; `est_min: u32`; `actual_min: u32`; `went: opt u8`; `tags: Vec<String>` def; `ci: u8`; `partial: bool` def | `id` | yes | closes a matching block; credits minutes with ci; `blocks`/`blocks_done`/`DurationObs` when `actual_min > 0`; sets `went` on the start's `EnergyObs`; done sets unless `partial` |
| `extend` | `id: String`; `by_min: u32` | `id` | yes | `ItemReplay.extended_min` |
| `stop` | `id: String`; `remaining_min: u32` | `id` | yes | cuts the block if the ids match; `ItemReplay.stops`. `remaining_min` is **not read by replay** |
| `break` | `planned_min: u32`; `actual_min: opt u32`; `where: opt String` | — | yes | `BreakRecord`; `Break` segment `[t, t + actual_or_planned]` |
| `energy` | `pred: u8`; `rep: u8`; `hsw: f64` def; `loc: String` | — | yes | `EnergyObs` (`from_start = false`; `slept_min` from `slept_by_day`) |
| `interrupt` | `id: opt String` | `id` if set | yes | closes the running sub-segment and the pause; opens the interruption |
| `resume` | `lost_min: u32`; `dropped: Vec<String>` def | — | yes | `Interruption`; `Interrupt` segment; `DayReplay.{lost_min, dropped}`; restarts the block clock |
| `pause` | `id: String` | `id` | yes | block paused; `Pause` segment |
| `unpause` | `id: String` | `id` | yes | block resumed |
| `idle` | `attributed: String` (`leak`, `work`, `break`, `routine`, `interrupt`, not validated); `min: u32` | — | yes | `IdleRecord`; `Idle` segment `[t − min, t]`; leak stats when `attributed == "leak"` |
| `routine` | `item: String`; `inst: String` (a date or `#N`); `status: String`; `actual_min: opt u32` | `item` | yes | `instances[item][inst]`; on `done`, the done sets and a `Routine` segment and `routine_min` |
| `skip` | `item: String`; `inst: String` | `item` | yes | `instances[item][inst] = Skipped` |
| `plan` | `hash: String`; `replans_today: u32`; `drift_min: u32` | — | **no** | `DayReplay.{plans, replans_today, drift_min, last_plan_hash}` |
| `event` (variant `Named`) | `name: String`; `id: opt String` | `id` if set | yes | `events[name]` gets a `NamedEvent` |
| `demote` | `id: String`; `from: String`; `to: String`; `est_min: u32` | `id` | yes | `demotions[id]` gets a `Demotion` with `stamp_from_key(from)` |
| `readopt` | `id: String` | `id` | yes | nothing |
| `move` | `id: String`; `from: String`; `to: String` | `id` | yes | nothing |
| `drop` | `id: String` | `id` | yes | `dropped_items` |
| `edit` | `id: String`; `field: String`; `from: String`; `to: String` | `id` | yes | nothing |
| `note` | `text: String` | — | **no** | nothing |
| `loc` | `loc: String` | — | yes | `DayReplay.loc_changes` |
| `close` | `period: String` (`day`, `week`, `month`); `key: String` | — | yes | `closes` |
| `undo` | `of: String`; `id: opt String` | `id` if set | **no** | removed by `undo_mask` before replay |
| any other tag (`Unknown`) | `rest: Map<String, Value>`, which can hold anything | `rest["id"]` when it is a string | **no** | `Replay.unknown += 1` |

Facts about types that matter for a kernel reader:

- **The only non-integer JSON numbers in known events are `start.hsw` and `energy.hsw` (`f64`).** They are written through `hours_since_wake`, which rounds to 0.01, but serde accepts any double. **`hsw` can be negative**: `hours_since_wake` is negative when `t` precedes the wake (`hsw_matches_spec` asserts `-0.5`).
- **UTC offsets such as `-05:00` are inside the `t` string, not JSON numbers.**
- `Unknown` payloads may hold any JSON: negative numbers, floats, exponents, nesting.
- `serde_json` writes non-ASCII as raw UTF-8 and never writes a `\uD83D`-style surrogate escape. A hand-appended line could contain one.

---

## 2. Every derived fact

### 2.1 The pipeline (`tm-core/src/log.rs` `replay`, `replay_refs`)

1. `undo_mask(entries)` runs over the **raw entries in file order**, before any range or day logic.
2. The survivors are the entries whose `cancelled[i]` is false, still in file order.
3. `DayIndex::new(tz, surviving wake instants)`.
4. `slept_by_day`: for each surviving `wake` in file order, `entry(days.day_of(t)).or_insert(slept_min)`. The first in file order wins.
5. `Machine::step` runs over **every** survivor. The range gates only what is recorded; the state machine always runs (`replay_credits_cut_blocks` asserts `open_block` is set even when the range keeps nothing).
6. `Machine::finish` sets `open_block` and `open_interrupt`, and sorts each day's `segments` by `start` (a stable sort).

`Log::effective`, `Log::iter_day`, `Log::iter_range` and `Log::iter_item` apply the same mask. `Log::day_index(tz)` builds the same `DayIndex` from surviving wakes.

### 2.2 `UndoMask` (`undo_mask`, `UndoMask`, `Log::undo_target`, `Log::compensating_undo`)

- The scan runs over `i` in file order. For each `undo{of, id?}` at `i`:
  - `cancelled[i] = true`. **The undo entry itself is always cancelled.**
  - The target is the **greatest `j < i`** such that `!cancelled[j]`, entry `j` is not an `undo`, `ev.name() == of`, and, when `id` is given, `ev.primary_id() == Some(id)`.
  - If a target exists, `cancelled[j] = true`. Otherwise `i` goes into `dangling`.
- `of` is compared to the tag string, so it can name **any** kind, including `plan`, `note`, an unknown tag such as `mood`, or a verb name that is no event at all (`rank`). **`is_state_change` does not restrict the mask.** It restricts only `undo_target` and `compensating_undo`, which choose what `tm undo` should cancel next.
- **Undoing an undo:** an `undo{of:"undo"}` can never match, because undos are excluded as targets. It is always dangling and cancels only itself. There is **no redo**, and a cancelled event cannot be revived.
- Two undos of one kind cancel the two most recent survivors in turn; a third with nothing left dangles. The test `undo_mask_pairs_and_dangling` gives `cancelled = [T,T,T,T,T,F,T]`, `dangling = [4,6]`, `pairs() == 2`.
- The mask ignores time and day: an undo cancels across day boundaries and range edges.
- `UndoMask::pairs() = (count(cancelled) − dangling.len()) / 2`.
- What the CLI appends (`tm/src/cli/undo.rs` `undo`): for the popped `UndoEntry`, one `undo{of: e.ev, id: e.id}` per recorded event **most recent first**; or, when the command logged nothing (e.g. `tm rank`), one `undo{of: verb, id: None}`, which matches nothing unless an event of that tag exists (`rank` never does). It restores file bytes and `state.json` itself; the log's undos only shape future replays.
- Kernel fact: `move_has_no_inverse_command` (`kernel/TmKernel/TmKernel/Boundary.lean`, L22 refuted) states `¬ ∃ inv : ReqCmd → ReqCmd, ∀ p q i n, applyCmd (.move i n) p = .ok q → applyCmd (inv (.move i n)) q = .ok p`. Its docstring concludes "`tm undo` must replay the log, never apply an inverse command". `Report.lean` widens it on the wire to the closes. The plan's wording is in `PLAN-lean-kernel.md` §4 L4, and AGENTS §10.5 q4 cites it.

### 2.3 `DayIndex`: wake-based day attribution (`DayIndex`, `hours_since_wake`, `local_midnight`)

- Built from the surviving `wake` instants, **sorted by instant**, then `dedup_by` on calendar date **in `tz`**. That keeps the **earliest wake per calendar date**, so a day is never longer than 24 h.
- `day_of(t)`: `w = last_wake_before(t)`, the last wake `≤ t` (`partition_point`). If `w` exists and `t − w < 24 h` (strict), the day is `calendar_date(w)` in `tz`. Otherwise it is `calendar_date(t)` in `tz`.
- `tz` is `chrono_tz::Tz` (an IANA named zone, `config.rs` `Config.tz`, default `America/Chicago`). **The entry's own fixed offset only fixes the instant.** Every calendar date is computed by converting the instant into `cfg.tz` (`t.with_timezone(&tz).date_naive()`). The test `day_index_wake_to_wake` asserts "UTC-written entries are attributed in the configured zone": `2026-09-08T03:00:00+00:00` falls on 2026-09-07 in Chicago.
- The same test pins the attribution cases:
  - after midnight, before the next wake: the previous day;
  - a stale wake (24 h or more earlier): its own calendar date;
  - no wake that date: the calendar date;
  - before the first wake: the calendar date.
- `bounds(date)` gives `[start, end)`, exactly the instants whose `day_of` is `date`. Candidates are local midnights (`local_midnight`, which takes the first valid instant within 4 h after a DST-gap midnight) plus every wake within ±1 day and `wake + 24 h`.
- `wake_of(date)` is the first kept wake on that calendar date.
- `hours_since_wake(t, wake)` is `round(secs / 36) / 100` in `f64`, so 0.01 h resolution. It is signed.
- **Two "first wake" rules coexist.** `DayIndex` keeps the earliest wake **by instant** per date. `DayReplay.wake` and `slept_by_day` take the first wake **in file order** attributed to that day (`if d.wake.is_none()`). They differ only if wakes were appended out of time order.

### 2.4 The block state machine (`Machine`, `Block`, `Cut`)

State:
- `block: Option<Block { id, started, since: Option<instant>, paused, paused_at, worked_min, obs: Option<index into energy> }>`
- `last_cut: Option<Cut { id, t, min }>`
- `interrupt: Option<(t, Option<id>)>`

Helpers:
- `close_sub(t)`: if a block is running (`since` is set), add `num_minutes(t − since)` (**whole minutes, truncated per sub-segment**) to `worked_min`, emit a `Block` segment if `t > since`, and set `since = None`.
- `close_pause(t)`: take `paused_at` and emit a `Pause` segment if `t > p`. It does **not** clear `paused`.
- `credit(id, t, min, ci)`: the day is `day_of(t)` **of the closing event**, so a block spanning a day boundary is credited wholly to the day it ends. Nothing happens out of range. It adds `ItemReplay.minutes`, `minutes_by_day[day]` (the key is inserted even when `min == 0`) and `DayReplay.block_min`. With `ci = Some`, it clamps `min(5)`, adds `minutes_by_ci[ci]`, and does `load += min × ci / 5` **as `f64`**. With `ci = None` and `min > 0`, it adds `ci_unknown[id]`. The invariant `Σ minutes_by_ci + ci_unknown_min() == block_min` holds.
- `cut(t)`: `close_sub`, `close_pause`, take the block, `credit(id, t, worked_min, None)`, and set `last_cut = Cut{id, t, worked_min}`.
- `uncredit_cut(cut)`: saturating subtraction of `cut.min` from the same maps. It removes `minutes_by_day[day]` and `ci_unknown[id]` when they reach 0.

Per event (all saturating on `u32`):

| event | exact effect |
|---|---|
| `start{id, pred, rep, hsw, slept_min, loc}` | `cut(t)` on **any** open block, including one with the same id. If in range and `rep` is set, push `EnergyObs{t, day, pred, rep, hsw, loc, slept_min: Some(start.slept_min), went: None, id: Some, from_start: true}` and remember its index. If in range, set `first_start` if unset and push `StartRecord{t, id, pred, rep}`. The new block has `since = t` unless an interruption is open (then `None`). Then `last_cut = None`, so **a block cut by the next `start` can never be replaced by a later `done`** |
| `pause{id}` | only if the open block has this id and is not paused: `close_sub(t)`, `paused = true`, `paused_at = t` |
| `unpause{id}` | only if the open block has this id and is paused: `close_pause(t)`, `paused = false`, and `since = t` if no interruption is open. A stray unpause is a no-op |
| `interrupt{id?}` | `close_sub(t)` and `close_pause(t)` always. If no interruption is open, open one as `(t, id.or(open block id))`. A second `interrupt` while one is open is otherwise ignored |
| `resume{lost_min, dropped}` | Take the open interruption `(s, id)`, if any. If `s` exists, emit an `Interrupt` segment `[s, t]`. The record day is `day_of(s)`, or `day_of(t)` without an interrupt. If in range, push `Interruption{start: Option, end: Some(t), day, id, lost_min, dropped}`, add `lost_min` to that day and extend its `dropped`. For an open block: if paused, `paused_at.get_or_insert(t)`; else if `since` is `None`, `since = t` |
| `done{id, est_min, actual_min, went, tags, ci, partial}` | `matched` means the open block has this id. **If matched:** `close_sub`, `close_pause`, and take the block; **its clock-worked minutes are discarded**, because `actual_min` is authoritative. If `went` is set, write it onto the block's `EnergyObs`. Set `last_cut = None`. **Else if** `actual_min > 0`, no block is open, and `last_cut.id == id`: `uncredit_cut` (the stop then done replacement). Then always `credit(id, t, actual_min, Some(ci))`. If in range and `actual_min > 0`: `ItemReplay.blocks += 1`, `DayReplay.blocks_done += 1`, push `DurationObs{t, day, id, ci, tags, est_min, actual_min, went, partial}` (partials included). If `partial`, push `partial_done_at`. Otherwise push `done_at`, push `DayReplay.done`, and call `mark_done(id, t, day)`. A `done` for id X while a different block Y is open leaves Y open |
| `stop{id}` | only if the open block has this id: `cut(t)` and, if in range, `stops += 1`. A stop for another id is ignored entirely |
| `extend{id, by_min}` | if in range: `extended_min += by_min` |
| `break{planned_min, actual_min, where}` | segment `[t, t + actual.unwrap_or(planned)]` on `day_of(t)`; `BreakRecord{t, day, planned_min, actual_min, where}` |
| `energy{pred, rep, hsw, loc}` | if in range: `EnergyObs{…, slept_min: slept_by_day.get(day), went: None, id: None, from_start: false}`. It uses the day index, so a `wake` appended after it still counts |
| `idle{attributed, min}` | `start = t − min`, `seg_day = day_of(start)`; an `Idle` segment and an `IdleRecord{t, day: seg_day, attributed, min}`. If `leak`: `leak_min += min`, `longest_leak = max`, and the global `longest_leak` is replaced only when `min >` the current one (the first maximum wins) |
| `routine{item, inst, status, actual_min}` | `parse_instance_status`: `done`, `pending`, `missed`, `expired`, `skipped` or `skip`. Anything else pushes a warning string to `Replay.warnings` and is treated as `Pending`. If in range (day of `t`): `instances[item][inst] = InstanceRecord{t, status, raw_status, actual_min}` (**BTreeMap insert, so the last in file order wins**). If `Done`: `date = parse_date(inst)`, or `day` if `inst` is not a date, then `mark_done(item, t, date)`; if `actual_min` is set, a `Routine` segment `[t − min, t]` and `routine_min += min` (on `day_of(t)`) |
| `skip{item, inst}` | if in range: `instances[item][inst] = {t, Skipped, "skipped", None}` |
| `plan` | `plans += 1`; `replans_today = max`; `drift_min += drift_min`; `last_plan_hash = hash` |
| `event{name, id}` | if in range: `events[name]` gets `NamedEvent{t, name, id}` |
| `demote{id, from, to, est_min}` | if in range: `demotions[id]` gets `Demotion{t, id, from, to, est_min, stamp: stamp_from_key(from)}`. `stamp_from_key`: `IsoWeek::parse` gives `Stamp::Week(w)`; `parse_date` gives `Stamp::Day(day_of_month)`; anything else gives `None` (a month key) |
| `drop{id}` | if in range: `dropped_items.insert(id)` |
| `close{period, key}` | if in range: `closes` gets `CloseRecord{t, period, key}` |
| `wake{slept_min, onset_min}` | on `day_of(t)`: if `wake` is unset, set `wake`, `slept_min` and `onset_min` |
| `arrive{loc, window, budget}` | the first sets `arrival`, `loc`, `window` and `budget`; every one pushes `loc_changes (t, loc)` |
| `loc{loc}` | `loc_changes` gets `(t, loc)` |
| `readopt`, `move`, `edit`, `note` | nothing |
| `undo` | nothing (the mask removed them) |
| `Unknown` | if in range: `unknown += 1` |

`mark_done(id, t, date)`: gated on `in_range(day_of(t))`.
- `done_items.insert(id)`.
- `last_done[id] = max(existing, t)` **by timestamp, not file position** (the comment: "an appended retro `done` must not make an older completion look like the last one").
- `done_dates[id].insert(date)`.
- **Nothing ever removes from `done_items`, `last_done` or `done_dates`** except an undo cancelling the event. A `routine done` followed by `routine pending` for the same instance leaves the instance `Pending` but the item still in `done_items` with the date in `done_dates`.

**Partial and non-partial `done` compared.** Both credit minutes. Both count a block and a `DurationObs` when `actual_min > 0`. Only a non-partial one pushes `DayReplay.done`, `ItemReplay.done_at` and the done sets. A retro `tm done ^id` has `actual_min: 0`: it credits 0 minutes (the `minutes_by_day` key is still inserted), counts no block and no `DurationObs`, but a non-partial one still marks the item done.

**The latest-record rule for instances.** `instances[item][inst]` holds the last `routine` or `skip` **in file order** (map overwrite). `last_done` holds the latest **by timestamp**. These two rules differ.

### 2.5 The output types (`Replay` and friends)

- `Replay { tz, range, days: BTreeMap<Date, DayReplay>, items: BTreeMap<String, ItemReplay>, instances: BTreeMap<item, BTreeMap<inst, InstanceRecord>>, energy: Vec<EnergyObs>, durations: Vec<DurationObs>, interrupts: Vec<Interruption>, events: BTreeMap<name, Vec<NamedEvent>>, demotions: BTreeMap<id, Vec<Demotion>>, closes: Vec<CloseRecord>, dropped_items: BTreeSet, done_items: BTreeSet, last_done: BTreeMap<id, instant>, done_dates: BTreeMap<id, BTreeSet<Date>>, longest_leak: Option<LeakRecord>, open_block: Option<OpenBlock>, open_interrupt: Option<Interruption>, unknown: u32, warnings: Vec<String> }`. It is `Serialize`/`Deserialize` for `--json`.
- `DayReplay { date, wake, slept_min, onset_min, arrival, loc, window: Option<[String;2]>, budget, loc_changes: Vec<(instant, String)>, first_start, starts: Vec<StartRecord{t,id,pred,rep}>, block_min, blocks_done, load: f64, minutes_by_ci: [u32;6], ci_unknown: BTreeMap<id,u32>, done: Vec<id>, lost_min, dropped: Vec<id>, leak_min, longest_leak, idle: Vec<IdleRecord{t,day,attributed,min}>, breaks: Vec<BreakRecord{t,day,planned_min,actual_min,where}>, routine_min, plans, replans_today, drift_min, last_plan_hash, segments: Vec<LogSegment{start,end,kind}> }`.
  - Methods: `wake_to_arrive_min`, `arrive_to_start_min` (both `i64`), `break_min` (actual or planned), `high_ci_min` (ci 4 plus 5), `ci_unknown_min`, `gaps(min_min)` (spans with `end > start`, sorted, merged by a running max end; a gap of `≥ min_min` whole minutes between the first span's end and later spans), `gap_min`.
- `SegmentKind = Block{id} | Pause{id} | Interrupt{id?} | Break{where?} | Routine{item, inst} | Idle{attributed}`. `LogSegment::minutes` is truncated and floored at 0.
- `ItemReplay { id, minutes, blocks, minutes_by_day: BTreeMap<Date,u32>, done_at: Vec<instant>, partial_done_at, stops, extended_min }`.
- `InstanceRecord { t, status: InstanceStatus, raw_status: String, actual_min: Option<u32> }`, where `InstanceStatus = Pending | Done | Missed | Expired | Skipped` (`tm-core/src/model.rs`).
- `EnergyObs { t, day, pred: u8, rep: u8, hsw: f64, loc, slept_min: Option<u32>, went: Option<u8>, id: Option, from_start }`. `delta()` returns `i32`. `weight()` returns `f64`: `went` 3 gives 2.0, 2 gives 1.5, anything else 1.0.
- `DurationObs { t, day, id, ci: u8, tags, est_min, actual_min, went, partial }`. `ratio()` returns `Option<f64>`, `None` when `est_min == 0`.
- `Interruption { start: Option, end: Option, day, id, lost_min, dropped }`. `NamedEvent { t, name, id }`. `Demotion { t, id, from, to, est_min, stamp: Option<Stamp> }`, where `Stamp = Week(u32) | Day(u32)`. `CloseRecord { t, period, key }`. `LeakRecord { t, day, min }`.
- `OpenBlock { id, started, worked_min, since: Option, paused }`. `worked_min_at(now) = worked_min + max(0, num_minutes(now − since))`.
- Accessors: `day`, `block_minutes`, `block_minutes_on(id, date)`, `blocks_done(date)`, `block_minutes_on_day`, `leak_min`, `lost_min`, `is_done`, `last_done`, `done_dates` (ascending `Vec`), `instance`, `instance_status` (`Pending` if absent), `instances_of` (sorted by inst string), `events_named`, `events_for(id)` (sorted by `t`), `breaks`, `interrupts_on`, `event_occurred(name, since?, id?)`, `stamps(id)`, `energy_on(date)`, `durations_on(date)`, `total_block_min`, `done_minutes_map() -> HashMap<Id,u32>` (feeds `tree::done_minutes`, §6.4).

**Every non-integer in the replay output:**
- `DayReplay.load` (`f64`, a sum of `min×ci/5`);
- `EnergyObs.hsw` (copied from the event);
- `EnergyObs::weight`;
- `DurationObs::ratio`.

Everything else is integers, strings, dates and instants.

---

## 3. Every consumer, and exactly what each reads

The Rust call sites were found by `grep` for `replay`, `Log::`, `effective`, `day_index`, `iter_day`, `iter_item` and `undo_target` over `tm-core/src` and `tm/src`.

| consumer (file :: function) | replay / log facts read |
|---|---|
| `tm/src/cli/ctx.rs` :: `Ctx::load_with`, `Ctx::reload` | builds `log` and `replay(None, cfg.tz)`, the **whole log, every load** |
| ctx.rs :: `Ctx::wake_time` | `day(today).wake` (time-of-day in `cfg.tz`); feeds `Model::wake_or_expected` |
| ctx.rs :: `Ctx::slept_min` | `day(today).slept_min` |
| ctx.rs :: `Ctx::today_slots` | `energy_on(today)` into `Posterior::from_observations` (`t`, `pred`, `rep`); `blocks_done(today)` |
| ctx.rs :: `Ctx::priorities` | `collect_candidates(replay)`; `capacity::lookahead` |
| ctx.rs :: `Ctx::plans_today` | `day(today).plans` |
| ctx.rs :: `Ctx::resolve_timeouts` | `recur::waiting_state`, which reads `events_named` |
| ctx.rs :: `Ctx::hz` | passes the replay to `horizon::Ctx::with_replay` |
| `tm-core/src/horizon.rs` :: `close_day`, `day_remaining` | `block_minutes_on(key, date)`, subtracted only from a line with no `est:` |
| `tm-core/src/priority.rs` :: `collect_candidates` | `done_items` (for deps); `events.keys()` (names only); `recur::today_instances` |
| priority.rs :: `build_candidate`, `done_this_period` | `block_minutes_on(id, day)` for `id` and its descendants over each day of the period; `instances_of(id)` where `status == Done` with `actual_min`, dated by the `inst` date else `rec.t` in `replay.tz` |
| `tm-core/src/recur.rs` :: `calendar_instances` | `done_dates(key).first()` is the `every:Nd` anchor (else `PHASE_EPOCH`); `status_of`, which calls `logged_status`, which calls `instance(key, k)` (non-`Pending`) |
| recur.rs :: `after_done_state` | `last_done(key)` (instant, into `cfg.tz`); `completion_count` (`instances_of` `Nth` `Done` count vs `done_dates.len()`); `next_ordinal` (max `Nth` among non-`Pending` instances vs `done_dates.len()`, plus 1) |
| recur.rs :: `after_done_instances`, `on_event_instances`, `logged_instances` | `instances_of` (key and status; dated by the `Date` key or `rec.t` in `cfg.tz`); `next_ordinal`; `logged_status` |
| recur.rs :: `one_off_instances` | `status_of`; `is_done(key)` |
| recur.rs :: `waiting_state`, `arrival_of` | `events_named(name)` where `id` is none or the key and the date of `t` in `cfg.tz` is at least `waiting_since`; the max `t` |
| `tm-core/src/planner.rs` :: `PlanInput` (holds `log` and `replay`), `Planner::new` | `day(date).{wake, arrival, loc, slept_min}`; `energy_on(date)` into the posterior; `blocks_done(date)`; `blocks_since_last_break(day)` (`breaks[].t`, `starts[].t`) |
| planner.rs :: the run's step 4 | `collect_candidates`; `capacity::lookahead` |
| planner.rs :: `active_run`, `open_block_segment` | `open_block.{id, since, worked_min_at}` |
| planner.rs :: `past_segments` | `day(date).segments` (every kind) |
| planner.rs :: diagnostics | `day(date).breaks` (`planned_min`, `actual_or_planned`) for rest debt |
| `tm-core/src/review.rs` :: `status_line` | `days.keys().last` (when no `runtime.date`); `day.{blocks_done, budget, leak_min, idle, segments (gaps), starts (adherence), window, lost_min, breaks, load}` |
| review.rs :: `waiting` | `recur::waiting_state` |
| review.rs :: `day_review` | `day(date)`: `budget`, `minutes_by_ci` and `ci_unknown` (through `mix_and_load` with the tree), `block_min`, `window`, `lost_min`, leak and gaps, adherence (`starts`), `wake_to_arrive`, `arrive_to_start`, `plans`, `drift_min`, `breaks`, `slept_min`, `onset_min`, `loc`; `energy` filtered by `day`; `demotions` whose `t` date in `tz` is `date` (`id`, `est_min`, `to`); `durations` (through `estimate_calibration`) |
| review.rs :: `week_review` | the week's `day(d)` (`blocks_done`, `block_min`, `budget`, `breaks`, mix); `energy` by day; `is_done`; `demotions` (`from == week key`, `from == prev week`, `est_min`); `lounge_rate` (every day's `loc` and `wake.hour()`); `durations` |
| review.rs :: `month_review` | `done_minutes_map` into `tree.progress`; `is_done`; `demotions` whose `t` date in `tz` is in the month, with `Stamp::Week`, `from`, `est_min` |
| `tm-core/src/energy.rs` :: `fit_replay` | `replay.energy` (`EnergyObs`: `day`, `rep`, `hsw`, `loc`, `slept_min`, `went`); `replay.durations` (tags, est/actual, `went`, `day`); `arrivals_from_replay` (`days[].{date, arrival (time in cfg.tz), loc}`) |
| energy.rs :: `compare`, `calibration`, `estimate_calibration` | `EnergyObs` `pred`/`rep`/`t`; `DurationObs` |
| `tm/src/cli/lifecycle.rs` :: `model` | `fit_replay`; `compare(…, replay.energy)` |
| lifecycle.rs :: `day_extras` | `is_done` |
| lifecycle.rs :: review verbs | pass the replay to the three reviews |
| lifecycle.rs :: `log` | **raw entries**: `ctx.log.entries`; `iter_item(key)` (mask plus `primary_id`); `day_index(tz).day_of` for `--since` |
| `tm/src/cli/day.rs` :: `since_break_min` | **raw** `log.iter_day(today, tz)`: `Break.{t, actual_min}`, the first `Start.t` |
| day.rs :: `idle_min_since` | **raw** `iter_day`: `Pause`, `Interrupt`, `Unpause`, `Resume`, `Break{actual_min}` |
| day.rs :: `idle` | **raw** `log.effective().last().t` |
| day.rs :: other verbs | `replay.blocks_done(today)` (`EnergyCtx`, status) |
| `tm/src/cli/planning.rs` :: `build`, `plan`, `week` | the replay into `PlanInput`; `blocks_done(today)`; `capacity::lookahead` |
| `tm/src/cli/items.rs` :: the routine verbs | `recur::today_instances` |
| `tm/src/cli/undo.rs` :: `log_len`, `new_events`, `undo` | raw text: line count; `Log::parse` event `name` and `primary_id`. **No replay** |
| `tm/src/tui/app.rs` :: `bare`, `status_head`, `week_pane`, `week_blocks_done`, `active_elapsed_min`, the review screen | `energy_on(today)`, `status_line`, `day(today)` (`slept_min`), `blocks_done`, `done_minutes_map`, `waiting_state`, `open_block`, the three reviews, `PlanInput` |
| app.rs :: `idle_since` | **raw** `log.iter_day(today, tz)` max `t` |
| `tm/src/tui/queue.rs` :: `View::new` | `replay.done_minutes_map()` |
| `tm/src/tui/necessities.rs` | `recur::week_instances`; `waiting_state` |
| `tm-core/src/tree.rs` :: `done_minutes` | takes the `HashMap<Id,u32>` from `done_minutes_map` |

**Replay facts nobody outside log.rs reads (by grep):**
- `ItemReplay.{stops, extended_min, done_at, partial_done_at}`;
- `Replay.{closes, dropped_items, interrupts (except through the day's lost/dropped), open_interrupt, unknown, warnings, longest_leak}`;
- `DayReplay.{replans_today, last_plan_hash, loc_changes, dropped}`.

Some of these may be reachable through `--json` serialisation of `Replay`. That was not checked.

**Raw-entry consumers**, which bypass `Replay` but still apply the undo mask and `DayIndex`: `day.rs` `since_break_min`, `idle_min_since`, `idle`; `app.rs` `idle_since`; `lifecycle.rs` `log`; `undo.rs`, which applies no mask.

---

## 4. Size and growth

### 4.1 The corpus's own rates (`tm-core/tests/fixtures/logs`, identical under `kernel/corpus/logs`)

| file | lines | bytes | days | lines/day |
|---|---:|---:|---:|---:|
| `review-14d.jsonl` | 179 | 20,336 | 14 | 12.8 |
| `energy-14d.jsonl` | 155 | 18,134 | 14 | 11.1 |
| `three-days.jsonl` | 74 | 6,983 | 3 | 24.7 |
| `malformed.jsonl` | 11 | 483 | — | — |

`review-14d` by kind: start 45, done 45, break 22, plan 16, wake 14, arrive 13, routine 7, energy 6, demote 4, idle 2, interrupt 2, resume 2, skip 1. It averages about 114 bytes per line.

### 4.2 The synthetic logs (this pass)

The generator is `design/genlog.py`, using the spec §10.1 and `define_events!` shapes. Every kind is exercised, including `undo`, `pause`, `stop`, `extend`, `close`, `demote` and `edit`. The seed is fixed. There are two rates: `genlog.py` at about 40 events a day, and `genlog80.py` at about 61 a day, which adds replans. Ids are short digit strings (D2). Output is compact JSON.

| age | ~40/day: events | bytes | ~61/day: events | bytes |
|---|---:|---:|---:|---:|
| 1 month (30 d) | 1,191 | 123,939 (0.12 MiB) | 1,845 | 191,478 (0.18 MiB) |
| 6 months (182 d) | 7,422 | 772,210 (0.74 MiB) | 11,172 | 1,165,920 (1.11 MiB) |
| 1 year (365 d) | 14,941 | 1,555,376 (1.48 MiB) | 22,055 | 2,293,587 (2.19 MiB) |
| 3 years (1,095 d) | 45,172 | 4,702,828 (4.48 MiB) | 65,771 | 6,857,648 (6.54 MiB) |

- Mean event size is **104 bytes** at both rates, and bytes grow linearly.
- Sending the log as one JSON array of objects costs about the same bytes. As an array of escaped line strings it costs about 20% more (1 y at 40/day: 1,865,117 bytes).
- For 80/day, scale the 40/day row by 2: 1 y is about 29,900 events and 3.0 MiB.
- The 1-month mix at 40/day: plan 306, start 163, done 143, break 77, routine 69, energy 54, idle 42, demote 42, pause/unpause 36 each, close 34, wake 30, arrive 30, interrupt/resume 30 each, stop 20, skip 13, extend 8, edit 6, drop 6, note 5, undo 4, move 4, event 3.
- **Observations flowing back** (energy obs plus timed `done`) at 40/day: 217 + 143 = 360 per 30 days, about **12 a day**.

### 4.3 Rust's cost today (measured this pass)

- **Binary:** a copy of `target/debug/tm` (debug profile, built 2026-09-13 20:58, the stage-4 final-repair binary; its `log.rs` is the fork-point one), run from scratch.
- **Tree:** `tm init --example` with the synthetic log in `.tm/log.jsonl`.
- **Timing:** best of 3, wall clock, `--now 2026-09-14T09:00:00-05:00`.
- **Verbs:** `tm log --tail 1` builds a `Ctx` without housekeeping, which parses and replays the whole log. `tm now` adds housekeeping and the kernel's automatic close.

| log | `log --tail 1` | `now` |
|---|---:|---:|
| empty log | 2.2–2.5 ms | 2.8 ms |
| 1 mo @40 / @61 | 3.9 / 4.3 ms | 4.3 / 4.9 ms |
| 6 mo @40 / @61 | 12.8 / 16.3 ms | 13.5 / 16.8 ms |
| 1 y @40 / @61 | 25.2 / 30.1 ms | 23.6 / 29.9 ms |
| 3 y @40 / @61 | 69.1 / 89.8 ms | 66.0 / 85.3 ms |

In a debug build, Rust's whole-log `Log::parse` plus `replay` costs about **15 ms per MiB of log**. It does not fail at any of these sizes.

### 4.4 The kernel's bounds that apply

- **Gap 44** (`kernel/README.md`, "Gap 44 — `jparse`'s and `jemit`'s per-element recursion has no runtime twin"). `jarr`/`jtail`, `jobj`/`jotail` and `jemitTail`/`jemitOTail` recurse **once per array element or object pair, not in tail position**. Measured through `examples/oneshot`: **21,500 one-line strings in one array read; 22,000 abort on a 2 MiB stack** (`gdb`: `jtail` frames). **80,000 read and 90,000 abort on 8 MiB.** The failure is a loud stack-overflow abort, never a wrong answer. `splitDoc` (a document's lines) has the same bands.
- **Which stack is in use.** README gap 44 names "tm's 8 MiB main thread" for the CLI. `kernel/tm-kernel-ffi` tests call in-process on test threads; libtest's default thread stack is 2 MiB, which is a Rust default, not verified in this repo.
- **The measured band covers arrays of strings**, not arrays of objects. Per event, an object adds only its own pair recursion (≤ 11 pairs, depth reset per object). The dominant depth is the top-level array length. **ESTIMATE:** arrays of objects overflow in the same element band, give or take the per-frame size.
- **Log age at which one whole-log JSON array crosses the bands:**

| rate (events/day) | 21,500 (2 MiB) | 80,000 (8 MiB) |
|---|---:|---:|
| 12.8 (`review-14d`) | 1,680 d ≈ 4.6 y | 6,250 d ≈ 17 y |
| 24.7 (`three-days`) | 870 d ≈ 2.4 y | 3,239 d ≈ 8.9 y |
| 40.9 (synthetic) | **526 d ≈ 17 months** | 1,956 d ≈ 5.4 y |
| 61 (synthetic, replan-heavy) | **352 d ≈ 11.5 months** | 1,311 d ≈ 3.6 y |
| 80 | **269 d ≈ 9 months** | 1,000 d ≈ 2.7 y |

- **An observation list emitted back** (a `jemitTail` array) at about 12 a day crosses 21,500 at about 1,790 d (4.9 y) and 80,000 at about 18 y.
- **Kernel JSON parse cost per byte is not in the committed measurements.** The only in-process whole-call numbers (README "Stage 4 hardening, 2026-09-13: the checker renders a plan once", "Against the TUI budget") are 500 items and 9 files: read 3.45 ms, drop 3.86 ms; "2,926 lines 16–19 ms a call". They include `loadPlan` and do not record request bytes. `oneshot` read and wrote 1,000,000-character strings on 2 MiB (README, the character twins `junescapeTR`, `jscanTR`) without a recorded time.
  - `call` works on `input.toList` (`the_response_call_emits_parses_back : jparse (call input).toList = .ok (respond input.toList)`), so the whole request is materialised as a `List Char`: 1.56 M cells at 1 y and 40/day, 6.86 M at 3 y and 61/day. **ESTIMATE**, not measured: tens of bytes per boxed cons cell, so roughly 50–200 MB transient at 3 y.
  - **FLAG (a measurement, not a decision):** a designer must measure `jparse` throughput on a log-shaped request before quoting any latency (AGENTS §5.11).
- **The latency budgets that bind** (`tm/tests/cli_latency.rs` `a_verb_on_a_tree_with_months_of_history_takes_well_under_a_second`):
  - First verb, which lands the unswept close: bound **5 s**, measured 0.59–0.65 s.
  - A later verb on the swept tree, one kernel call: bound **1 s**, measured 0.05–0.062 s.
  - The test's tree has **no `.tm/log.jsonl` history**: 226 files and 2,959 lines, and it generates no log. A log therefore adds cost this test does not yet exercise.
  - The TUI budget is 5 ms per call at 500 items (AGENTS §9.1), and it is stage 6's gate.
- **Growth law, from `ctx.rs`:** replay cost is proportional to the whole log on **every** command and every TUI reload, because `Ctx::load_with` and `Ctx::reload` always pass `None`. `replay`'s `range` argument exists but no CLI caller uses it.

---

## 5. Kernel prerequisites: what exists and what is missing

| need | exists | missing |
|---|---|---|
| Civil date | `Cal.lean`: `Day := Nat` (days since 0001-01-01, a Monday), `Date`, `ValidDate`, `toDay`/`ofDay` with `toDay_ofDay` and `ofDay_toDay`, `isLeap`, `monthLen`, `weekdayOf`, ISO week, `monthOfIsoWeek`, `unixEpoch := toDay ⟨1970,1,1⟩` | the `Day` abbreviation inside `=`/`≤` defeats `omega` (Cal.lean header), so day-valued results are typed `Nat` |
| Time of day | `Line.lean`: `Clock := Fin 1440`, `mkClock?`, `parseClock` (strict `HH:MM`, rejects `9:05`, `25:00`, `11:60`), `renderClock`, `parse_render_clock`; `DT {day, time}` with `DT.abs = day*1440 + time`; `Moment = date d \| dateTime d t` with `parseMoment`/`renderMoment` | clock arithmetic in `Cal.lean` (AGENTS §8.3 trap); **seconds** (the log writes `HH:MM:SS`); fractional seconds (RFC 3339 allows them and `parse_timestamp` accepts them) |
| Offset / zone | nothing | a `±HH:MM` offset parser; an instant type (UTC minutes or seconds); **any timezone rule**: `DayIndex` converts each instant into the IANA zone `cfg.tz` (DST), and the kernel has no tzdb (README "What this does not cover" item 10: "days only: no time of day, no time zone … the tree's `tz` [has] nowhere to live") |
| Wire `now` | `Boundary.lean`'s request clock reader takes `"now":"YYYY-MM-DD"` (a date only; `badNow` on `2026-02-30` or `2026-9-12`) plus `blockMin` | a time of day and an offset in `now` |
| JSON numbers | `Json.lean`: `inductive JVal \| null \| bool \| num (n : Nat) \| str (s : List Char) \| arr \| obj`; `jparse`/`jemit` with `jparse_jemit` and `jparse_never_runs_out` | **negatives and decimals are refused at parse:** `jparse_refuses_what_the_fragment_has_no_type_for` (`-3` gives `notAValue '-'`, `1.5` gives `trailingGarbage '.'`, `1e3` gives `trailingGarbage 'e'`). The log has `hsw` (`0.95`, possibly `-0.5`), and `Unknown` events may carry any number. A surrogate-pair escape is refused (`badEscape surrogateEscape`, gap 42). AGENTS §8.3's "Config decimals" trap: the `Lean.JsonNumber` route is gone; the remaining routes are Rust sending num/den `Nat` pairs, or widening `JVal` **visibly** with the round trip extended |
| Exact rationals | `Arith.lean` (namespace `Tm.Arith`): `Q {num den : Nat}` **unnormalised**, where `⟨n,0⟩` is ∞; `Q.ok`, `Q.defined`, `Pos` (a subtype with `den > 0`), `mkPos`, `ofPair? (n d : Nat) : Option Pos`, `ofNat`, `Q.mul`, `Q.div`, `Q.le`/`Q.lt`/`Q.equiv` by cross-multiplication (reflexive, transitive, total, congruent under `n/d ≈ kn/kd`); `util need avail`, `utilGe`, `utilScaledGe (s : Pos) rem avail e`, `isHot`, `isImpossible`, `defaultBins`, `binsWf`, `descending`, `rungs`, `binOf`, `ladderIx`; rounding `floorQ`/`ceilQ`/`halfUpQ` (each `_mono`, `_withinOne`); `scale`, `safety = 13/10`, `budgetRatio = 3/4`, `planRatio = 4/5`, `needMin` (R1 ceiling), `budgetBlocks` (R2 floor), `overRatio`, `plannedMin` (R4 half-up), `ramp`/`defaultRamp`, `posteriorNum : Int`, `energyAfter` (R5 half-up then clamp to `Fin 6`). Header table **R7: "open … Nothing rounds here yet; the pair is carried exact"**. `Rat` is deliberately unused. `Q.add` was **not found** by the declaration grep (`^def`) | **no `Q.add` or sum**: a weighted mixture `p·a + (1−p)·b` needs addition of pairs. `util`, `utilGe` and `utilScaledGe` take `avail : Nat`, not a `Q`. **No consumer imports `Arith`** (AGENTS §8.3 scope item 5) |
| A log in the plan | `Plan.lean` `structure PlanCore where docs : List Doc; store : Store`, with **no log field** (AGENTS §8.3 "The log has nowhere to live") | a log event type. Note: `Goals.lean`'s header still says "`PlanCore.log` is `List String`, JSONL held verbatim"; `Plan.lean` has no such field, so **that header sentence is stale** |
| Undo | `move_has_no_inverse_command` (L22 refuted, `Boundary.lean`) and its close widening (`Report.lean`); plan L4 | any undo or mask definition |
| Recurrence denotation | `Field.Recur` syntax (`Line.lean`); `Goals.lean` header: D1/D2 "not stateable until a parsed `LogEvent` exists"; D2's `every:Nd` epoch is a spec gap (`Rule.everyNDays` has no anchor; the Rust uses `done_dates.first()` or `PHASE_EPOCH`, `recur.rs` `calendar_instances`) | `LogEvent`, `Occurrence` |
| Stage 5 goals that touch this | `Goals.lean` `# STAGE 5`: provisional `DayCapacity {day : Day, minutesAt : Fin 6 → Nat}`, `Deadline {need : Nat, ci : Fin 6, due : Day}`, `edf`, and goals `edf_keeps_the_days`, `edf_only_spends_capacity`, `edf_reserves_only_before_the_deadline` | `minutesAt` is **`Nat`-valued**, so it cannot hold D10's exact fractional minutes as declared. Goals says the stage "is free to widen" provisional signatures |
| Checks and budgets | AGENTS §5.10: `decide` has a budget; `digitsOf`'s structural fuel trick; `jparse` fuel `2·length+2`. §5.10a: witnesses stay small `List Char` literals; a realistic-size input is an instance of a round-trip theorem, never an evaluation; cap memory | — |

---

## 6. D10 facts: the capacity lookahead's inputs

### 6.1 The fork-point `capacity::lookahead` (`tm-core/src/capacity.rs`)

- **Actual signature:** `lookahead(walls_by_date: &WallsByDate, cfg, model: &Model, today_slots: &[Slot], from: NaiveDate, days: u32, wake_default: NaiveTime) -> Vec<DayCapacity>`. **It differs from spec §8.4's** `lookahead(tree, log, cfg, model, runtime, from, days)`: there is no log or runtime, and slots and walls are precomputed.
- `DayCapacity { date, minutes_at_level: [u32; 6] }`, with `from_slots`, `total`, `at_least(min_ci)`.
- **Day 0 (`from`)** is `DayCapacity::from_slots(date, today_slots)`, exactly as handed in. No mixture, no budget limit.
- **Each future day `i ≥ 1`**, with `wd = date.weekday()`:
  1. `arrival = local_dt(tz, date, model.expected_arrival_on(wd, cfg))`. `Model::expected_arrival_on` returns the learned `expected_arrival[wd]`, else `cfg.expected.arrival[wd]` (a `NaiveTime`).
  2. `wake = local_dt(tz, date, wake_default)`. Callers pass `Ctx::wake_time()`, which is **today's** logged wake time-of-day else `model.wake_or_expected(…, today.weekday())`, so every future day reuses today's wake clock (`ctx.rs` `Ctx::priorities`, `planning.rs` `week`); `planner.rs` passes `self.wake.time()`.
  3. **`loc = Lounge if model.p_lounge_on(wd, cfg) >= 0.5 else Home`.** `Model::p_lounge_on` returns the learned `p_lounge[wd]` (`f64`), else `cfg.expected.p_lounge[wd]` (`f64`). **This is the threshold D10 replaces.**
  4. `walls = walls_by_date[date]`, or empty. `Ctx::walls_by_date(days)` calls `Ctx::walls_on(date)` for each date: every not-closed item whose `tree.effective_shape` is `Shape::Interval{start, end}`, with `start − buffer`, covering the date, as `DateTime<Tz>` through `Ctx::instant`/`local_dt`, sorted. **These are Interval items from the whole tree**, the `calendar/` files among them.
  5. `(end, budget) = window_and_budget(arrival, walls, cfg)`, spec §8.1:
     - `window_min = round(window_hours×60)` (`f64`);
     - `cap = local_dt(tz, date, cfg.day.window_cap)`;
     - `base_end = clamp(arrival + window_min, ≤ cap, ≥ arrival)`;
     - walk the walls clipped to start at the arrival, merged and sorted; each wall `[a, b)` with `a < end` adds `b − a` (the least fixed point, per the doc comment);
     - `budget = budget_blocks(cfg) = floor(window_hours×60 / block_min × budget_ratio)` (`f64`), which is independent of the day's actual window.
  6. `cut = cut_slots(arrival, end, walls, cfg)` (spec §8.2 step 3): `block_min` blocks, a `break_min` break after every `break_after_blocks`, a short last block of at least `min_last_block_min` or dropped, applied at the end of **every** free stretch.
  7. `ctx = EnergyCtx::new(model, cfg, &Posterior::none(cfg), wake, loc)`: `slept_min: None`, `blocks_done: 0`, `allow_home: false`.
  8. `slots = energize(&cut.slots, &ctx)`. Each slot gets `energy_at(start, blocks_done, since_break)` = `cap_for_location(posterior.correct(t, predict(model, cfg, Features::at(t, wake, loc).with_slept(None).with_progress(..))))`.
     - `predict` = `(base − shift).clamp(0, 5)`. `base` = `model.energy_at(curve_key(loc), hsw)`, which is `energy[curve][bucket(hsw)]` with `bucket = floor(hsw)` clamped to `0..HSW_BUCKETS−1` (`HSW_BUCKETS = 12`), else `prior_level(cfg, curve, hsw)`. `shift` = `round(model.sleep_shift(cfg))` only when `under_slept`, which is never here because `slept` is `None`.
     - `Posterior::none` gives no correction.
     - **`cap_for_location` = `min(energy, cfg.location.home_max_ci)` when `loc == Home`** (and not `allow_home`).
     - **The location-dependent pieces are exactly `curve_key(loc)` and the home cap.** `window_and_budget` and `cut_slots` do not read `loc`.
  9. `limit_to_budget(slots, budget, cfg.block_min())`: order slots by energy descending, then start ascending; take `min(slot minutes, left)` until `budget × block_min` minutes are used; sum into `minutes_at_level[level]`. **This selection depends on the energies, and so on `loc`.**
- **Consumers of the capacities:**
  - `priority::compute(cands, caps, priorities_yesterday, cfg, date)`, the EDF pass, which uses `capacity::available_until(caps, due, min_ci)` (`Σ at_least` over days `≤ due`, `u32`), `capacity::reserve(caps, minutes, min_ci)` (earliest day first, highest level first, integer subtraction) and `capacity::upto`;
  - `priority::lookahead_days(cands, today)`, which sizes `days` (at least 7, through the furthest effective due or `min:` floor period end);
  - `capacity::week_grid`, and `planning.rs` `week`'s `WeekOut.days[].minutes_at_level` (`--json`);
  - `planner.rs` step 4;
  - `ctx.rs` `Ctx::priorities`;
  - the TUI queue `View`.

### 6.2 Where each piece belongs in the staged plan

| piece | spec | stage (AGENTS §8.3/§8.4, `Goals.lean`) |
|---|---|---|
| `lookahead`, `DayCapacity`, the EDF `edf`/`reserve`/`available_until` | §8.4, §7.3 | **stage 5** (§8.3 scope items 3 and 4; `Goals.lean` STAGE 5 `DayCapacity`, `Deadline`, `edf` plus three goals) |
| `window_and_budget` | §8.1 | **stage 6** in the goal list: `Goals.lean` STAGE 6 "E7 — §8.1's window, which is a fixed point and was solved by iterating", provisional `wallsInside`, `windowEnd`, goals `the_window_end_solves_the_equation` (E7a) and `the_window_end_is_the_least_solution` (E7b). R2 `budgetBlocks` exists in `Arith`; R3 "eliminated: the window enters the kernel as minutes" |
| `cut_slots`, `energize`, `limit_to_budget`, `predict`, `cap_for_location` | §8.2 step 3, §8.5 | **stage 6** planner pieces (`Goals.lean` STAGE 6 `PlanReq`/`dayPlan`/`Seg` and the `plan_*` invariants). R5 `energyAfter` and R6 (short block, a comparison) exist in `Arith` |
| the model fit (`p_lounge`, `expected_arrival`, curves, `duration`, `sleep_debt_shift`) | §8.5 | **stays Rust** (AGENTS §4 "The statistical layer stays in Rust"; PLAN §3.6: "The kernel consumes a fitted model as data; it never fits one … typed on entry as exact rationals") |

**FLAG (a sequencing fact, not decided here).** Stage 5's capacity under D10 needs, for each future day and each of the two locations, the output of §8.1, §8.2 step 3 and §8.5's `predict`. Those are listed as stage-6 pieces with stage-6 goals (E7a/E7b, the `plan_*` invariants). Either stage 5 builds them early, or it receives per-location per-level minutes from somewhere. The owner's D10 does not say which.

### 6.3 `model.json` (spec §8.5; `tm-core/src/energy.rs` `Model`; `kernel/corpus/model.json`)

| key | Rust type | JSON form | notes |
|---|---|---|---|
| `energy` | `BTreeMap<String, Vec<u8>>` | `{"lounge":[4,5,…12 entries], "home":[…]}` | integers 0–5 by convention; `u8` accepts 0–255 |
| `sleep_debt_shift` | `Option<f64>` | `0.8` | used as `round(shift)` in `predict` |
| `duration` | `BTreeMap<String, f64>` | `{"lean":1.6, "_default":1.3}` | fit writes `round2` |
| `p_lounge` | `WeekdayMap<f64>` | `{"Mon":0.9,…}` (keys may be absent) | fit writes `round2(shrunken_mean)`; hand-editable to any decimal (`#[serde(default)]`, §8.5 "hand edits become the new prior") |
| `expected_arrival` | `WeekdayMap<Hhmm>` | `{"Mon":"07:10"}` | strings |
| `fitted` | `Option<NaiveDate>` | `"2026-09-14"` | |
| `n_obs` | `u32` | `61` | |

`Model::to_json` uses `serde_json` with a `CompactArrays` formatter.

**`f64` in config** (`tm-core/src/config.rs`): `day.window_hours`, `day.budget_ratio`, `week.plan_ratio`, `priority.bins: Vec<f64>`, `priority.safety`, `energy.sleep_debt.under_hours`, `energy.sleep_debt.shift`, `energy.prior_weight`, `energy.decay_days`, `energy.duration_prior_weight`, `energy.posterior_full_hours`, `energy.posterior_zero_hours`, `expected.p_lounge: PerWeekday<f64>`, and the prior-curve range keys (`from: f64`, `to: Option<f64>`). Spec §16 ships `p_lounge = {Mon 0.9 … Fri 0.8, Sat 0.5, Sun 0.4}`. The corpus model has `Wed 0.8`, `Fri 0.7`.

### 6.4 The dyadic fact

- Every finite IEEE-754 binary64 value is exactly `m · 2^e` with integer `|m| < 2^53` and `−1074 ≤ e ≤ 971`, so it is an exact dyadic rational `m·2^e` (or `m / 2^(−e)`). A finite `f64` `p` in `[0, 1]` therefore gives an exact pair with `den` a power of two (up to `2^1074`), and `1 − p` has the same denominator.
- **The value in the file and the value Rust computes with are two different rationals.** `serde_json` reads the decimal text `0.9` to the **nearest** double, which is 0.90000000000000002220446049250313080847263336181640625, not 9/10. It writes back the shortest decimal that round-trips, `0.9`. So "the exact dyadic of Rust's `f64`" and "the exact decimal in `model.json`" differ.
- The fork-point threshold `p >= 0.5` gives the same answer under both readings for every value the fit writes (`round2`), because 0.5 is exactly representable.
- **FLAG:** which of the two rationals D10's mixture weight is (the decimal text or the double) is not stated in D10.

---

## 7. Open items this inventory surfaced

These are facts that look like decisions. None is decided here.

1. **FLAG (G9 versus D9).** The CLI's log read fails the whole command on invalid UTF-8 (`read_to_string`). Its appends never repair a torn last line (`FsStore::append_text`). The UTF-8 and torn-line tolerance exists only in the uncalled `Log::read`/`Log::append_all`. D9 moves the replay into the kernel. Whether the kernel's reader is the tolerance authority (per-line warnings), or Rust still splits lines and handles UTF-8, is not stated.
2. **FLAG (the timezone source).** Day attribution uses the IANA zone `cfg.tz`, not each event's fixed offset, and the offsets are the writer's local zone (`Local::now()`). The kernel has no tzdb. D9 says the kernel derives day attribution, but how it gets UTC offsets for `cfg.tz` across DST is open.
3. **FLAG (two "first wake" rules; file order versus timestamp).** `DayIndex` takes the earliest by instant; `DayReplay.wake` and `slept_by_day` take the first in file order. Instance records take the last in file order; `last_done` takes the latest by timestamp. A faithful port reproduces all four. A "one definition" port (AGENTS §5.3) changes behaviour on out-of-order appends.
4. **FLAG (seconds and truncation).** Minutes are `num_minutes` truncated **per sub-segment** (`close_sub`), so a block paused many times loses up to a minute per sub-segment. This is a rounding site not in `Arith`'s R1–R7 table.
5. **FLAG (`hsw` as data).** `hsw` is the only fractional number in the known events, and it can be negative. It is written rounded to 0.01 and could be recomputed from `t` and the day's wake (which is how `hours_since_wake` produced it). Whether the kernel reads the logged `hsw` or recomputes it is open. The observations handed back to Rust carry it.
6. **FLAG (`load`).** `DayReplay.load` is an `f64` sum of `min×ci/5`, and the reviews round it (`round1`). As an exact pair its denominator is 5.
7. **Stale sentence.** `Goals.lean`'s header says `PlanCore.log` is `List String`; `Plan.lean` `PlanCore` has no log field.
8. **Spec and Rust drift.** Spec §8.4's `lookahead` signature (`tree, log, cfg, model, runtime, …`) is not the fork-point's.
