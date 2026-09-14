# Completeness critique of `stage5-D9-D10-design.md`

Read in full against `inventory.md`, the three input designs where a claim needed checking, and fork-point
Rust `4748911` (read-only `git show`/`git grep`). Nothing in the repo was touched. Each item gives its
severity, the section it is about, what is missing or wrong, the evidence, and the smallest fix I can see.
"Fork" means `4748911`.

Severity counts: **3 blocker, 17 major, 12 minor.**

---

## Blockers

### 1. blocker: §9.4 (fold point and ledger day), §9.1, §9.6. The window is anchored to the log's latest day, not to `now`

- **What is wrong.** §9.4 (i) sets `F = (max day touched by any survivor of b) − keepDays`. `L'` and
  `H'` follow from `F`. §9.1 then asserts "`L ≤ today`, so every period containing today starts at or
  after `H`", but nothing enforces it. The request's `now` never enters `resume`.
- **Where it came from.** LAT's rule (design-latency.md §8.4 (i)) was `F' = dayOf at − 1`, bounded by the
  request instant. The synthesis dropped the `at` bound.
- **Failure 1: a line dated in the future.** Causes include a synced device with a wrong clock, a
  `--now 2027-…` typo, or a hand-appended line.
  - `F` jumps ahead, and `L'`/`H'` follow. Today's window facts (`itemDay`, `doneDate`, date-keyed `inst`)
    are compacted below `H'`, and they are in no bundle (item 3).
  - `done_this_period`, `close_day`/`day_remaining`, `recur` and `today_slots` then read zeros. The
    priorities and the Markdown are wrong, with no refusal.
- **Failure 2: when the future line stays unfolded.** Condition (iii) forbids folding past it once a later
  wake exists. The line then pins `c'` forever, and the tail grows by about 40–60 lines a day with no
  notice. The stall notice in §9.4 covers only blocks, `stop` and interruptions. That is unbounded latency
  growth, which is exactly what `cli_latency.rs` guards.
- **Failure 3: `--now` in the past** (tests, and the user). The `today` Rust asks about sits below `H`.
- **Fix.**
  - Make `at` (the request instant, or at least `now`'s date) a required field of `reseal`.
  - Define `F = min (dayOf at − keepDays) (max survivor day − keepDays)`.
  - Add a guard or refusal `nowBelowLedger` when `now`'s date `< H`, so the host runs a genesis that never
    reseals past `now`.
  - Give a line with `t > at + slack` a named rule. It must not advance `F` and must not pin `c'`: it is
    excluded from (iii) or folded as an open-day line.
  - Add a law: after any accepted reseal, `H' ≤ dayOf at`.
  - Whether a future-dated line is also warned about is an owner question (Q-a below).

### 2. blocker: §8.4 (the `minutes_by_day` row, "lives in W"), §9.1, §14.3 R-audit. Readers of old dates are already known, and the table puts them on compacted data

- **`horizon::auto_close`.** It runs from `Ctx::load` housekeeping (fork `ctx.rs`, `auto_close(&store,
  &mut state, today, now, Some(&replay))`). It walks `pending_closes`, which catches up from
  `state.closed.day`, and that can be weeks or months back. For each day it calls `close_day(cx, day)`,
  then `day_remaining`, then `replay.block_minutes_on(key, date)`.
- **`tm close day <date>`.** `lifecycle.rs` `horizon::close_day(&ctx.hz(), date)` takes any date.
- **What goes wrong.** For `date < H` both read 0 minutes. A line with no `est:` then keeps minutes that
  were already worked, and the wrong remaining estimate is written into the Markdown. This is a durable
  wrong answer, not a slow one.
- **Why the audit comes too late.** The design defers this to R-audit ("if a consumer needs more history
  … moves to the fuller form"). But W1 freezes the `Ckpt` shape and the law signatures (§15) around W's
  `d ≥ H`, and the audit runs only after the formats are designed.
- **Fix.**
  - Decide now. Either every sealed `Bundle` carries that day's `itemDay` minutes, and `close_day` for
    `d < L` reads bundles (a kernel decision reading Rust-stored data, which contradicts D9-13's "kernel
    decisions never read bundles", so this needs a stated exception), or old-date closes refuse by name
    (a behaviour change, so an owner question).
  - Also check `lounge_rate` (item 4) and every `instances_of`/`done_dates` reader before W1.

### 3. blocker: §9.5 laws 1–2, §15 W1 block. The laws cannot say what §9 claims about the W facts, and the hot path has no answer law

- **Problem 1: the partition law.** `seal_partition_is_the_replay` equates `merge (bundlesBelow z L es)
  (answer (ckptOf z L es []))` with `Replay.view (replay z es)`. The right side does not depend on `L`.
  The W facts below `H` (`itemDay`, `doneDate`, date-keyed instances) are in **neither** the bundles
  (`Bundle` = `DayFacts`, `obs`, `demotions`, `headers`) **nor** the answer. That leaves two readings:
  - `view` contains them, and the law is false;
  - `view` omits them entirely, and the law says nothing about the facts `done_this_period`, `recur` and
    `close_day` read.

  The second is exactly AGENTS §5.2 ("the law compiles and means less") and the design's own risk K5.
- **Problem 2: the reseal answer.** `resume_is_replay` is stated only for `policy = none`, and
  `reseal_is_seal` describes `k'` and `bs` but not `v`. The shipped hot path sends `reseal` whenever the
  tail exceeds 512 lines, or today − `L` > 2, so the answer a verb actually uses has no law.
- **Problem 3: `L` is unconstrained.** `ckptOf z L a r` takes any `L`. A checkpoint whose `L` is past a
  day the machine can still write is not a checkpoint `resume` ever builds, so the laws either need a
  `hL : L ≤ sealBound z a r` hypothesis or become false or vacuous.
- **Fix.**
  - State the W family as a query-indexed law: `∀ q, H ≤ q → (answer …).itemDay i q = (replay z
    es).itemDay i q`, with the same shape for `doneDate` and date-keyed instances. Pair it with item 1's
    `H ≤ dayOf at`.
  - Add `resume_with_reseal_answers_the_replay`.
  - Add the `L` well-formedness hypothesis.
  - Cheat 97 should be joined by a cheat that compacts one day too far (`H + 1`) and must fail.

---

## Major

### 4. major: §11.1, §11.3, §14.6 S versus §14.7 F1, §18.5. Old-day facts do not reach tm-core consumers at the switch, and `lounge_rate` reads every day

- **`tm model --fit` between S and F1.** `fit_replay(&Replay)` runs on the decoded `Replay`. If
  `decode_facts` is lazy about bundles (§11.1 "loads month files lazily"), then at S the fit sees only
  open-day observations until F1 lands. That is a silent regression across at least one commit. If it is
  eager, every verb decodes about 4 MiB at 3 years, and §18's hot-call budget is wrong.
- **tm-core cannot reach the bundles.** `review.rs`, `recur.rs`, `priority.rs` and `energy.rs` take
  `&Replay` in **tm-core**. They cannot call `Ctx::sealed()`, which lives in the **tm** crate.
- **`lounge_rate` is all-time.** Fork `review.rs` `lounge_rate` iterates `replay.days.values()`, every day
  ever. So `review week` needs **all** month files, not the "1–2 month files" in §18.5.
- **Fix.**
  - Move F1 into S, or have S eager-merge observations only for `model`.
  - Specify in R13 the tm-core abstraction (a `DaySource` trait, or a merged `Replay` built per verb
    family), with signature changes listed per function.
  - Correct §18.5 for `review week`.

### 5. major: §12 (the `tui/queue.rs` row only), §14.8 L8, Q4. Rust still runs its own reserve over `DayCapacity`

- **The Rust reserve loops.**
  - Fork `planner.rs`, around the week-allocation loop, does `let take = left.min(day.at_least(c.ci));
    capacity::reserve(std::slice::from_mut(day), take, c.ci)` over the lookahead.
  - `tui/queue.rs` does `capacity::reserve`.
  - `planning.rs` `week` emits `minutes_at_level`.
- **Why that is a problem.** After D10 these receive either floors (a silent rounding that D10 forbids, and
  a second reserve deciding placement, the AGENTS §5.3 bug) or `u64` units (listed only for the queue).
- **What is left unsaid.** Q4(a) "integer fields as documented floors" does not say whether `total` is the
  floor of the sum or the sum of the floors.
- **Fix.** Add a table of every `DayCapacity` consumer, from inv §6.1 plus `planner.rs`'s reserve loop.
  For each, give exact units, a display floor, or "moves into the kernel in L8". A floor may only ever
  display.

### 6. major: §13.4 `Input.wakeClock : Clock`, §17 P23, LOOK §4.3. Today's wake seconds are rounded away, so the twin cannot be exact

- **The fork's input has seconds.** `Ctx::wake_time` returns `d.wake.with_timezone(&tz).time()`, which
  includes seconds (a bare `tm wake` logs `now`). Fork `Features::at` calls `hours_since_wake`, which
  rounds to 0.01 h, and `bucket` then floors.
- **Where the proof stops.** LOOK's "buckets agree always" argument covers whole minutes only.
- **A counterexample.**
  - Wake 06:05:40 and slot 07:05:00 give 59 min 20 s = 0.9889 h. That rounds to 0.99, which is bucket 0.
  - `Clock` 06:05 gives 60 min, which is bucket 1.
- **The consequences.** The kernel truncates, which is a rounding site with no R-number. The prediction
  differs, and T13's "twin equals fork × `capDen` modulo P23–P25" fails.
- **Fix.** Carry the wake as a `Cal.Instant` (B1 exists) and port `round(secs/36)/100` exactly as a named
  rounding site, or record a new parity entry and a rounding-table row. `state.wake` has the same
  question.

### 7. major: §9.8 (files, write order, concurrency), §11.1. Mixed snapshots and non-atomic replacement of `sealed/`

- **Two snapshots can mix.**
  - A process reads `ckpt.json` at `L = 10` and later lazily loads month files that a concurrent reseal
    (by the TUI or the CLI) has rewritten to cover `[10, 12)`.
  - Days 10–11 then exist in both the bundles and the open days.
  - "Disjoint by day key" (law 1) is a property of one snapshot, not of two.
- **Genesis replacement is not atomic.**
  - "Rename a temporary directory over `sealed/`" fails on POSIX when the target is non-empty.
  - Any two-step replacement leaves a window in which `sealed/` is missing, and a concurrent reader
    silently sees no history (empty old reviews, a fit on nothing).
- **The month-file rule contradicts itself.** "Replace every day of `[L, L')` in the months it spans; never
  merges" is impossible when a month already holds days below `L` from an earlier reseal: Rust must
  read-modify-write.
- **Fix.**
  - Filter bundles to `day < ckpt.ledgerDay` of the checkpoint actually in hand.
  - Stamp month files with a generation that `ckpt.json` names.
  - Specify generation directories (`sealed.<gen>/`, with `ckpt.json` pointing at one) instead of
    renaming over a directory.

### 8. major: §9.4 condition (i), §9.8 prefix digest, R10. A torn last line can be folded, and the digest cannot see it completed

- **What happens.**
  - A warning line has no survivor, so no condition stops the fold at it. If the last physical line is
    torn (a crash, a sync client mid-flush, a non-atomic `O_APPEND` on a network file system) and every
    earlier line is old, `c'` can include it.
  - `prefixBytes` then ends mid-line.
  - When the writer finishes the line, the bytes before `prefixBytes` are unchanged, so the FNV matches.
    The checkpoint keeps "line c is `notJson`" while the file holds a valid event.
- **Fix.**
  - Rust sends whether the last segment ended in `\n`.
  - The kernel never folds an unterminated segment, and `prefixBytes` always ends at a newline.
  - Add this to T10's mutation set ("extend the torn last line").

### 9. major: §9.3 G3, §8.2 `Effect.key`, §11.3–11.4. Retro lines that touch no day key slip past G3 and are lost at the next fold

- **Retro energy observations.**
  - G3 refuses only `Key.day d < L` and `itemDay`/`doneDate`/`instDate < H`. §8.2's `Key` has no
    observation key, and `Effect.obs` is not given a key.
  - A hand-appended or retro `energy` line dated ten days back yields an `EnergyObs` whose `day < L`.
  - It is admitted into `openObs`, which `Ckpt.wf` says holds only days `≥ L`. It is either dropped at the
    next reseal (the day is not in `[L, L')`, so no bundle gets it) or it breaks `wf`.
- **Retro no-effect lines.** `note`, `move`, `readopt`, `edit`, `undo` and `unknown` lines dated before
  `L` produce a header whose day is already sealed. The header is never written to any bundle, so
  `tm log --since/--item` loses the line after it folds, and `entryCount` stops matching the headers
  shown.
- **Fix.**
  - Give every effect that carries a day, and every header, a day key (`Key.day o.day`), so G3 refuses
    and a genesis puts the line in the right bundle.
  - Or specify that headers and observations below `L` are appended to their day's bundle at the reseal.
  - Add `every_dated_output_names_its_day_key`.

### 10. major: §14.1 A1, §9.7, §10.4, §18.4. Gap 44 is closed only for JSON, and the call bounds are memory-unsafe on this machine

- **Only three functions get twins.** A1 gives accumulating twins to `jparse`/`jemit`/`splitDoc`. Every
  other function over lines, entries, ids or days must also be tail-recursive or bounded:
  - `readLine` mapped over `lines`;
  - `survivors` and `survivorsFast`;
  - `keptWakes`;
  - the header and bundle emitters;
  - `readCkpt`'s list decoders;
  - association-list updates in `applyEffects`;
  - `List.range (stop − arrival)` in `wallOverlap`;
  - `lookahead` over 1,095 or more days.
- **T0 misses them.** T0 checks only a raw 200,000-element array read.
- **The line cap is too high for the memory.** `maxLinesPerCall = 2^20` at about 104 B a line and the
  MEASURED 63 MiB RSS per MiB of request is about 6.3 GB of RSS for one call. The §9.7 back-up "resends
  from that checkpoint through the end of the refusing chunk, in one call", so it can reach the whole log:
  - 520 MiB at 3 years;
  - 1.7 GB at 10 years;
  - with the TUI and the CLI both running genesis, doubled.

  This machine has no swap, and an uncapped process has already OOM-killed the owner's terminal.
- **Fix.**
  - Add an end-to-end T0: a `log` request with at least 200,000 lines through `resume`, facts and bundle
    emission on a 2 MiB thread, and `lookahead` with `days = 5,000`.
  - State the rule "every recursion over wire-sized lists has a TR twin".
  - Derive `maxLinesPerCall` from a stated memory budget, for example 65,536 lines ≈ 400 MiB.
  - Make back-up itself chunked. Law 8 already permits any partition, so resend from the popped checkpoint
    in `CHUNK`-sized calls.

### 11. major: §6.1, §14.2 T4, §14.4 T5. The time-zone edge cases the owner named are not in any test

- **T4 almost never lands on a transition.** It samples 10,000 random instants over 130 years. It must
  also test every table transition at −1 s, 0 and +1 s from 1970 to 2100, in every zone.
- **The probe can miss transitions.**
  - It records a transition only "where two daily samples differ". A→B→A inside one UTC day (sub-daily
    reverts) is invisible, and T4 as described cannot find what the probe missed.
  - Fix: probe hourly for any zone whose tzdb has sub-day spans, or compare the table against
    `chrono_tz`'s behaviour at the hourly boundaries of a whole year per zone.
- **T5's 256 generated sequences name only "out-of-order wakes, retro break/idle, a silent-verb undo".**
  They must also include:
  - a wake at 01:30 on the fall-back day, with the ambiguous local hour used twice;
  - a wake after midnight whose previous wake is under 24 h old;
  - events 23–25 real hours after a wake across both DST transitions;
  - a date where consecutive dedup differs from earliest-per-date (the §6.2 porting trap), which needs a
    DST fold at midnight in a zone that has one;
  - one day with mixed written offsets (`-05:00` then `+02:00`, a travelling machine);
  - `cfg.tz` different from the writer's `Local`.
- **The example request contradicts the span.** §10.1 starts at 1883 with base `-05:50:36`, but the
  table's span is [1900, 2200). Chicago's base at 1900 is `-06:00`.

### 12. major: §7.3 the undo law. It assumes the command's events are the last lines, which housekeeping breaks

- **Non-recorded appends.** Fork `Ctx::load` runs `horizon::auto_close` (it appends `close` events) as
  housekeeping **before** any verb's `Recorder::start`. `tm now`, `tm plan` and the TUI append without an
  `UndoEntry`, and the undo stack spans up to 50 commands.
- **The resulting shape.** `tm undo` of command X, taken after a later verb whose housekeeping
  auto-closed, appends `undosFor E` after `L ++ E ++ M`, where M holds closes X did not write.
- **The wrong cancellation.** If E contains a `close` (X = `tm close week`), `undo{of:"close", id:null}`
  cancels **M's** automatic close, not E's. The law `L ++ E ++ undosFor E` never sees M, and Q6(d)
  describes only silent verbs.
- **Fix.**
  - Generalize to `L ++ E ++ M ++ undosFor E ≃ L ++ M` under "no event of M matches any `(tag, primaryId)`
    of E".
  - Add the refutation witness with an interleaved automatic close.
  - Add a Q6(f) row: `close` events have no id, so this is a live defect, not a theoretical one.
  - Add a T5 case.

### 13. major: §16 cheat 97, §15 W instances, §5.5, §13.4 L5 loaded-plan witness. Decide-witness memory is asserted, not designed

- **What the cheats need.** Cheat 97 ("a view without `lastDone` still satisfies the partition law on the
  witness log") and "`resume_is_replay`'s instances" run over a 25-kind witness log, one stall, one undo,
  one retro wake and one compaction. They require kernel evaluation of `mergeSort`, `eraseP`, the effects
  fold, `resume` and, for the disk-shaped law, `emitCkpt`, then `jemit`, `jparse` and `readCkpt` of a
  checkpoint thousands of characters long.
- **Why that is the wrong shape.** AGENTS §5.10a and the memory lesson say a realistic-size input is an
  instance of a round-trip theorem, never an evaluation.
- **Other heavy evaluations.**
  - `the_malformed_corpus_reads_as_the_fork_point_did` pushes `jparse`, `parseStamp` and a `White_Space`
    table through `decide` per line.
  - L5's Wednesday-wall witness runs `loadPlan`, `wallsOn`, E7, the cut and the energy in `Boundary.lean`.
- **Fix.**
  - State that the instances go through `readCkpt_emitCkpt` and `jparse_jemit` as rewrites, never
    evaluated.
  - Bound each witness: at most 8 entries per witness, at most 2 zone transitions, per-cheat minimal logs
    (cheat 97 needs 2 `done` entries, not 25 kinds).
  - Name the fallback when a probe exceeds 8 GB: split into per-arm lemmas, and never `native_decide`.
  - Give K6 a concrete budget per step.

### 14. major: §10.4 R10 table. Many wire values have no stated bound

- **The client-supplied checkpoint.** `readCkpt` has no stated bounds on:
  - the lengths of `items`, `window`, `named`, `instOther`, `openDays` and `openObs`;
  - string lengths inside it;
  - unknown-tag string length in `TagSet`.
- **Bundles.** `Bundle` sizes are unbounded.
- **Numbers on the request.** `from`, `maxLine` and `headersFrom` are unbounded `Nat`s.
- **The decimal exponent.** `JDec.exp` is a `Nat` **value**. `1e99999999999` is 13 characters, but
  `finiteF64` compares `m · 10^e`. "Exponent work is capped by the line bound" is false, because the digit
  count is capped and the value is not. Short-circuit on digit counts first and cap the exponent value.
- **The capacity section.**
  - `breakMin`, `blockMin`, `minLastBlockMin`, `windowCap` and `homeMaxCi` have no ranges.
  - Energy curves should be exactly 12 entries, and the prior-range count needs a bound.
  - `Input.days` is unbounded; a `due:` in 9999 means millions of days.
- **The response.** "Numerals the kernel emits are all below 2^53" is false for grants. `avail` over
  6,250 days × 1,440 × 10^6 passes 2^53 at about 17 years (a `due:` in 2043). The `lcm` fallback of D10-2
  breaks it immediately.
- **Fix.** Complete the table, and prove an `emitted_numerals_are_below_2^53` law or bound `days`.

### 15. major: §5.4, §11.4, §17 P17/P21. `tm log --json` changes for unknown events, and unknown payload numbers break warning parity

- **Byte identity is only proved for writer output.** T2 covers writer-produced events only. Fork `tm log`
  prints `Unknown.rest` re-serialised through `serde_json::Value`:
  - `1.50` becomes `1.5`;
  - `1e3` becomes `1000.0`;
  - `-0` becomes `-0.0`;
  - integers above `u64` become floats.

  The kernel renders lexically.
- **Warning parity breaks.** Serde turns `{"ev":"mood","x":1e400}` into a **warning** ("number out of
  range"). The kernel applies `finiteF64` only to `hsw`, so it reads an **entry**, and `unknown` counts
  differ.
- **Fix.**
  - Apply the finiteness check to every numeral in unknown payloads.
  - Either port serde's number normalisation in `renderLine` for `unknown`, or add a behaviour row and a
    parity entry for hand-appended unknown lines.

### 16. major: §3.3 row 1, §14.3 R11, §4. Narrowing "every replay fact" is taken as a reading, not asked

- **Why it is not a reading.** D9 as the owner wrote it: "THE LEAN KERNEL REPLAYS THE LOG, ALL OF IT …
  derives every replay fact". R11 **deletes** the unobserved facts from Rust **before** the port. After S
  no Rust replay exists to re-derive them, so restoring them later means a kernel port plus bundle
  migration.
- **The fix.** It is flagged in §3.3 but absent from §4 ("All of them are in §4"). It must be an owner
  question with its cost (≈ 300 definition lines plus bundle growth).

### 17. major: §13.6, §17 P24, §4 "Not owner questions". Refusing weights with more than 6 decimals is a user-visible behaviour change

- **The behaviour today.** `model.json` is documented as hand-editable (spec §8.5 "hand edits become the
  new prior"), and the fork accepts any `f64`.
- **The behaviour under the design.**
  - `p_lounge: 0.3333333` (7 places) makes every priority- and plan-computing verb fail by name.
  - The design does not say whether the host fails the verb, ignores the model, or falls back to the
    config.
- **The alternative already exists.** The `lcm` fallback is designed (D10-2), and it avoids the refusal at
  the cost of item 14's 2^53 bound.
- **Fix.** This is an owner question, not a settled row. Also specify the host's reaction to the refusal.

### 18. major: §17 P10, §14.6 T9. A corrupt log line goes from a loud failure to silence

- **What changes.** Fork: invalid UTF-8 fails the whole command. The design turns it into a per-line
  warning.
- **Nothing shows it.** No CLI surface prints log warnings (grep: no reader of `Log.warnings` or
  `Replay.warnings` outside `log.rs`). Folded warnings collapse to `warnCount`.
- **The user never learns of it.** A corrupt or hand-mangled line is now invisible forever, and T9 asserts
  only that "the verb runs".
- **Fix.**
  - `tm check` (or `tm log`) names the log's warning lines. That needs warning headers in the sealed
    bundles.
  - Add a behaviour row saying where warnings appear. This touches G9's verdict M, so confirm it with the
    owner.

### 19. major: §9.6, §9.4 stalls, §18.2. Stalls and old undo targets turn the hot path into a replay without a notice

- **A stall makes every call reseal.** The host triggers a reseal whenever today − `ledgerDay` > 2. With a
  stall (an open block, a `stop` without `start`, an open interruption, item 1's future line) `L` cannot
  advance. Every call, including each TUI reload at 200 ms debounce, emits a checkpoint and rewrites
  `ckpt.json`, adding 3–10 ms and a write.
- **Old undo targets pin the tail.** A G1 crossing (a 30-day-old target, or a silent-verb `close` undo)
  goes to genesis. Condition (iv) then pins `c'` before the target until the undo itself folds, 2 days
  later. The tail is about 30 days (≈ 1,800 lines), beyond §18.2's "high" 850-line case and W5's 60 ms
  gate.
- **Fix.**
  - Add a no-progress back-off: skip the reseal when the last reseal did not advance `L`.
  - Add both cases to W5 and T11.

### 20. major: §12, §6.4, Q6. A second "which day is it" definition survives, and a second stamp reader may too

- **The calendar-day gap.** Fork `Ctx::load_with`: `today = now_tz.date_naive()`, a calendar date. The
  kernel's `dayOf` is wake-attributed. At 00:30 before a new wake:
  - `replay.day(today)` reads an empty day;
  - `wake_time` falls back to the expected wake;
  - `blocks_done(today)` is 0;
  - tonight's blocks sit on yesterday.

  This is the fork's behaviour, but after D9 it is two definitions of one concept across the FFI
  (AGENTS §5.3). It is not a Q6 row.
- **A possible second stamp reader.** §11.4's human `tm log` "formats `t` … from that `Value`". If that
  calls `parse_timestamp` (kept "unless `--now` uses it"), Rust keeps a second reader of `t`.
- **Fix.**
  - Add Q6(g) for today's day definition.
  - Have the kernel emit the display fields (local date and time in `cfg.tz`) for rendered lines, and
    delete `parse_timestamp` at S, or restrict it to `--now` by name in the one-reader grep.

---

## Minor

### 21. minor: §14.4 C3–C5 arm lists. `extend` is in no step

`extend` has no `effects` arm listed in C3, C4 or C5. Its only fact, `extended_min`, is deleted by R11, so
the arm is a no-op. It still needs a named arm and a witness, or `every_known_event_has_an_arm` fails
silently.

### 22. minor: §8.2 witnesses. Partial `done` is not pinned

There is no witness that a partial `done`:
- credits minutes and pushes a `DurationObs`;
- does **not** mark done;
- after a `stop`, still runs `uncredit_cut` (the fork's `uncredit_cut` ignores `partial`).

Add `a_partial_done_credits_but_does_not_complete` and `a_partial_done_after_stop_replaces_the_cut`.

### 23. minor: §8.4 `events[name]`. Compacting to the latest instant needs a check of every accessor

The accessor list in inv §2.5 includes `events_for(id)` (sorted by `t`) and `stamps(id)`. If any reader
wants the list and not the maximum, compacting to "latest per (name, id?)" is wrong. R-audit must list
these explicitly, not by family.

### 24. minor: §8.4 seam facts. `lastT` and `lastEffective` are underspecified

- Fork `app.rs` `idle_since` takes the **max** `t` over `iter_day(today)`, which includes `plan`, `note` and
  `unknown`.
- Fork `day::idle` takes the **last in file order** of `effective()`.
- State which order each field uses and which kinds count, with a witness where they differ.

### 25. minor: §9.2 `wakes` and §9.3. The no-wake case is not written out

When no wake exists below `L − 1` (a user who never logs `wake`), `wakes.head` does not exist, and the
"G3 refuses anyway" argument (`dayOf_before_the_stored_wakes_is_sealed`) needs its `wakes = []` case
written out: `dayOf` is `localDate t`, guarded by `Key.day`.

### 26. minor: §9.8. Every tm upgrade, and every read-only plan directory, pays genesis

- `TM_KERNEL_ID` changes on every kernel build, so each release's first verb pays 1–4 s.
- An unwritable `.tm/cache/` (a read-only synced viewer, a permission error) makes **every** verb run
  genesis.
- Needed: an in-memory fallback with a named notice, and an owner-visible note of the per-upgrade pause.

### 27. minor: §9.6 `maxLine`. Old undo stacks and restored state are not covered

- An undo stack written before R6 has no `log_line`; say it is treated as `none`.
- `tm undo` restores `state.json` bytes; say whether the undo stack lives there, and that a restored stack
  can only lower `maxLine` (a performance effect, not a correctness one).

### 28. minor: §11.4 `tm log` render path. The digest check must come first

- Rust reads raw bytes "by line number" from sealed headers. That is valid only after the prefix digest
  has been checked in the same process.
- State the ordering (digest, then header selection, then byte read, then render), so a hand edit between
  two calls cannot render a different line under an old header.

### 29. minor: §5.2 `Instant.wf`, leap seconds. Leap-second durations are untested

- `ns ≥ 10^9` is accepted on second 59.
- `minutesBetween` subtracts nanos linearly, while chrono's `signed_duration_since` has its own
  leap-second rule.
- T3 pins parsing only. Add one T5 case with a `:60` stamp inside a block.

### 30. minor: Q4. Floors are not pinned per field

Q4(a) "floors" should say per field whether `total` is `floor(Σ)` or `Σ floor`. `allocation_min` and
`shortfall_min` floors can disagree with `avail_min − …`, so pin one rule.

### 31. minor: §14.3 R8's grep. The pattern misses callers

It does not include `horizon.rs`'s `Replay` constructors or `tests/`. Before R12, 17 tm-core test files
and 3 tm test support modules (`tui_common`, `tui_queue_common`, `tui_today_prompts`) call `Log::`/`replay`
directly. Fork grep lists `tm/tests/tui_common/mod.rs`, `tui_queue_common/mod.rs` and
`tui_today_prompts.rs`, which are **tm** tests, not tm-core. So "move to `tm/tests` at S" is not the whole
set. Recount the 17 files and 27 sites by crate.

### 32. minor: §14.9 and §0. The cost headlines do not match

- §0 says "21,000 proof lines" while §4/§14.9 say 21,400.
- §4's D10 row has 3,500 proof lines while §14.9's has 3,450.
- Harmonise the figures, because Q1 quotes them to the owner.

---

## Checked and found adequate

These need no change:

- **All 25 kinds plus `unknown`** have grammar rows (§5.4).
- **Every inventory §3 consumer** has a row in §8.4 or §12, except as noted in items 2, 4, 5 and 23.
- **The undo cases:**
  - undo of an undo (C1 `an_undo_of_an_undo_cancels_nothing`);
  - an undo with no target (dangling, C1);
  - the mask ignoring `isStateChange`.
- **Torn and malformed lines** in the grammar (§5.5).
- **The one-reader invariant across commits (§14):**
  - before S the kernel reader is test-only (D9-1);
  - Phase R narrows Rust to one chokepoint;
  - S is atomic.

  The exceptions are item 4 (the S/F1 gap) and item 20 (a possible stamp reader).
- **D10's arithmetic** does not round inside the mixture or the EDF.
  - `decimal_pair` from the shortest `Display` text is exact for `round2` values.
  - The threshold twin `2w ≥ capDen` equals the fork's `p ≥ 0.5` exactly.
  - The rounding D10 does not cover is outside the mixture: item 6 (the wake's seconds), item 5 (Rust
    floors in `planner.rs`) and item 17 (refusal instead of the `lcm` fallback).
