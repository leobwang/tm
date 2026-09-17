# Stage 6, the planner: the one plan

A read-only design pass, written 2026-09-16 (campaign run **W-13**, track A). **Nothing in the
repo was edited, built or committed by the reading half of this pass**; the only file it adds is
this one, plus its `kernel/README.md` block.

**What it was read against.** Branch `rebuild-on-lean` at `0585e72`. Stage 5 is **closed**
(`c627148`; AGENTS §8.3), the kernel is the shipped binary's only reader (`2b26be3`) and only
writer (`47a0443`) of `.tm/log.jsonl`, W-12's audit repair has landed (`a7f07fc`), and D24/D25 are
recorded (`0585e72`). Every name taken from the tree below was re-read in the committed tree, and
every number was re-measured at this commit (§0.3).

**What it is.** The thing a future agent is handed: a numbered step plan with dependencies, the
reuse table that keeps AGENTS §5.3 true, the settled shapes of `Planner.lean`'s vocabulary, the
one proof pattern that dominates the stage, an honest price for the two relational laws, the
architecture row that kills G1, and — §4 — the questions only the owner can settle.

**How to read it.**
- Rust is cited by function name and file. The oracle is fork point **4748911** (D21), frozen in
  `tm/tests/fixtures/fork-4748911-*.jsonl`.
- **MEASURED** means a figure this pass actually ran; the text says how.
- **ESTIMATE** means a derived figure; the text says what it was derived from.
- **OWNER** marks a genuinely new human decision. All of them are in §4.
- **FINDING** marks something this pass discovered that contradicts a document in the repo. Each
  one has a gap number in §20 and is repeated in the README block.
- Everything else is a decision taken inside D5, D9, D10, D16, D19, D24, D25, the hard rules and
  AGENTS §4, with its reason beside it (§3).

---

## 0. The plan on one page

1. **The seam comes first, and it is the whole stage's opening move, not only L9's.** D24 puts
   L9's day 0 inside the kernel by exposing the `log` section's `Seal.Run` to the `capacity`
   section (gap 210). **FINDING (gap 255): the planner needs the same seam for a second and
   larger reason.** The fork's `plan()` returns *the whole day, past and future*, and its past
   half is `Planner::past_segments()` — the day's segments replayed from the log
   (`tm-core/src/planner.rs:2034`). A kernel `dayPlan` that cannot reach the replay cannot
   produce the past half at all, so it cannot produce the day file's rows, so §8.4 item 3 — the
   architecture row that kills G1 — cannot land either. Three steps were said to pay for the seam
   once (D24); it is four, and the fourth is the stage itself.
2. **Nothing stage 5 built is built again.** §1 is a table of eighteen names with the step that
   consumes each. A second copy of any of them is a defect under AGENTS §5.3, and the reason the
   table is written out by name is that `dayPlan` is the first kernel function whose natural
   shape is "compute a window, cut it, energise it, rank the candidates" — every one of which
   already exists.
3. **The eleven single-run goals are one checker and one lift, and the lift is where the stage's
   proof budget goes.** §8.4 calls them "cheap — a checker plus a `lift`". The checkers are
   cheap. `dayPlan_ok`, the theorem that the produced plan passes them, is a fold induction
   carrying eleven invariants through eight steps, and it is the largest single proof in the
   stage. §6 writes the pattern once; **OWNER Q3** asks whether it is proved (a theorem for every
   input) or gated (a named refusal when a produced plan fails), because "decidable-checked on
   every plan the corpus produces" and `∀ r, …` are **not the same claim** and `Goals.lean` states
   the second.
4. **FINDING (gap 251): at least five of the thirteen stage-6 goals are FALSE AS WRITTEN against
   the fork, and `tm/tests/planner_invariants.rs`'s own header already says which.** The running
   block is excepted from overbooking and from the energy filter; the running block and the
   running interruption *grow* across a replan, so they break stability as written; and every
   comparison between two candidates has to be restricted to the candidates its rule is written
   about, because §8.2 step 5 skips a `loc:`-constrained, `atomic` or `max:`-capped item for
   reasons no §8.3 invariant is about. Under AGENTS §3.1 item 3 these are refuted, renamed and
   restated — the shape stage 5 used for E7 — never weakened silently. §6.3 names each one, its
   witness, and the restated form.
5. **L24 and L25 are proved (D5), and D5 is what makes them affordable to state correctly.** Both
   are relational. §7 prices them at ≈ 3,000 proof lines and 15–23 agent-days together and says
   exactly what each induction needs. The Active-item exception is not a footnote: it is the
   reason `plan_tail_drop` as written is false.
6. **`Emit.lean` owns what the day section *says*; one Rust function owns how wide it is.** G1's
   verdict is `A` — "the kernel owns the generated blocks; there is exactly one implementation of
   the day-section text" — and G6's verdict is `M` — "`pad`/`truncate` counted characters, so `⏰`
   broke every column; Rust unit tests; stays in the TUI". §8 reconciles them: the kernel emits
   the cells and their order, one Rust padder turns cells into columns, and **OWNER Q5** settles
   what "byte-identical across four surfaces" can mean when `tm now` prints four rows and the day
   file prints the day.
7. **§9's dynamic adjustment splits cleanly.** The *facts* (the running block, the interrupt wall,
   the posterior, the window) are `dayPlan` inputs and are stage 6's; the *prompts and timers* are
   TUI and stay Rust; §9.1's "→ drops: …" consequence is `dayPlan` run twice and diffed, which is
   the kernel's the moment `dayPlan` is, and it closes gap 114. §11 is the row-by-row table.
8. **The price is large, and this document states it.** ESTIMATE (§14.7): ≈ **5,360** Lean
   definition lines, ≈ **21,350** Lean proof lines, Rust **+950 / −5,400**, ≈ **121–167
   agent-days**, at a proof : definition ratio of ≈ **3.98 : 1** — between the D9/D10 tranche's
   3.61 : 1 and stage 4's 4.80 : 1, because a third of the stage is proof with almost no
   definition behind it. **FINDING (gap 250): AGENTS §8.4 prices this stage at "3–4 wk".** That
   figure predates stage 5, and it is the same unit the plan used to price the whole of stage 5
   ("3–4 weeks") — which landed **6,534 definition and 23,611 proof lines** across twelve campaign
   runs. By lines, which is what this document says to compare, **stage 6 is 82% of stage 5's
   definitions and 90% of its proofs** — not a fifth of it; and the estimating method here is the
   one that priced D9+D10 at 6,550 / 23,300 against an actual 6,534 / 23,611. **OWNER Q1** asks to
   confirm or narrow.

### 0.1 The eight steps, and where each one already lives

| §8.2 step | who owns it today | stage 6's work | build step |
|---|---|---|---|
| 1 WALLS | `Look.wallIndex`/`wallsOn` index them; `planner.rs` places them | place them as segments; `buffer:`; travel-day zeroing; conflicts; the interrupt wall | **P1** |
| 2 ROUTINES | `recur.rs` + `planner.rs` | mandatory placement, `pref:` anchors, deferral, sleep/wind-down | **P2** |
| 3 SLOTS | **`Look.freeIntervals`, `cutSlots`, `energize`, `capForLocation`, `limitSlots`** | today's posterior (`Arith.energyAfter`), the Active reservation, `--allow-home` | **P3** |
| 4 PRIORITY | **`Look.prioritiesWithFloors`, `Priority.finalPrio`** | candidate *collection* inside the kernel (gap 113) | **P4** |
| 5 ASSIGN | `planner.rs` | the greedy fold: cursor, batching, atomic runs, `max:`, deps, `loc:` | **P5** |
| 6 ROUTINES' | `planner.rs` | lowest-energy placement, displacement, the un-placed note | **P6** |
| 7 REST | `planner.rs` | Rest past the budget, optionals within `max:` | **P7** |
| 8 EMIT | `emit.rs`, `cli/render.rs`, `tui/today.rs` | `Emit.lean`: rows, diagnostics, the review block | **P8** |

### 0.2 Reading order for the agent who is handed this

§14.0 (rules before any step) → §1 (what must not be rebuilt) → §5 (the vocabulary) → §6 (the one
pattern) → the step's own row in §14 → §15 (its goals' signatures) → §20 (the gap format).

### 0.3 Numbers re-measured for this pass, at `0585e72`

Every command capped with `systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0
--quiet`, per AGENTS §3.

| measurement | value | comparand |
|---|---|---|
| `check.sh`, built tree | **7/7 ok**, **3.142 s** | 3.04 / 3.04 / 3.07 s at stage 5's close — **+2.4%**, inside the 10%-per-step rule |
| axiom audit | **3,946 theorems** | unchanged since `c627148` |
| corpus | **29/37 files, 4/5 whole plans** | unchanged |
| burn-down | **13**, every one stage 6's | unchanged |
| `cargo test --workspace` | **1,311 passed / 0 failed / 9 ignored across 78** result lines, exit 0 | 1,311 / 78, the brief's comparand; 1,309 at `c627148`, +2 from W-12's repair (the precision tripwire and the tree-refusal regression test) |
| `tm/tests/planner_invariants.rs` | **882 lines, 256 cases**, in the workspace suite | §8.4 cites `tm-core/tests/…` — **stale path, gap 253** |
| the Rust this stage retires | `planner.rs` **2,700** (2,673 code), `emit.rs` **1,840**, `priority.rs` **1,499**, `capacity.rs` **1,012** (948 code), `cli/render.rs` **117**, `review.rs` **2,249** (2,156 code) | `wc -l`, `#[cfg(test)]` split |
| the Lean this stage reuses | `Lookahead.lean` **4,752**, `Capacity.lean` **1,419**, `Priority.lean` **817**, `Arith.lean` **1,080** | `wc -l` |

---

## 1. What is already built, and must be REUSED rather than rewritten (AGENTS §5.3)

**The rule.** Two definitions of one concept is the bug this rebuild is named after. Every name in
this table exists, is proved, and is the kernel's single reader of its concept. **A second copy of
any of them is a defect, and a step that writes one has not landed** — it has reopened the class
the kernel exists to remove. A step that finds one of these *almost* right widens the existing
definition and re-proves its laws (D5); it does not fork it.

### 1.1 The window and the budget (D12, stage 5 step L2) — `Lookahead.lean`

| name | what it is | consumed by |
|---|---|---|
| `Look.windowEnd (arrival windowMin windowCap) (walls)` | §8.1's end: the base clamped to the cap, extended by the overlap of the walls inside it. Has a `@[csimp]` twin `windowEndFast` | **P1**, and `PlanReq`'s window when the host sends none |
| `Look.windowBase`, `Look.wallOverlap`, `Look.clipWalls`, `Look.mergeSorted` | the parts `windowEnd` is built from, each with its law | **P1** only, and only through `windowEnd` |
| `Look.windowOn (z d arrival windowCap windowMin walls)` | the window of a *dated* day in a zone, in absolute seconds | **P1**, **P3** |
| `Look.budgetOf (windowHours blockMin budgetRatio)` | §8.1's `floor(window_hours × 60 / block_min × budget_ratio)` | **P0** (`PlanReq`), **P3** |
| `Look.windowMinOf` | window hours → minutes, half-up (site R3) | **P1** |
| `Look.wallIndex (z bm p)`, `Look.wallsOn (ix d)` | the plan's intervals indexed once by day, with `buffer:` shifted back (`shiftBack`) | **P1** |
| `Look.WallIx` | one indexed wall | **P1**, **P5** (the atomic-run test) |

**E7 is stage 5's and is proved** (`the_window_end_solves_the_equation`,
`the_window_end_is_the_least_solution`, restated to the fork's overlap semantics and refuted as
stage 6 wrote them). Stage 6 **never restates E7** and never computes a window a second way.

### 1.2 The slot cut (D12, stage 5 step L3) — `Lookahead.lean`

| name | what it is | consumed by |
|---|---|---|
| `Look.freeIntervals (lo hi walls)` | §8.2 step 3's free time between walls | **P3** |
| `Look.cutSlots (cfg lo hi walls rests sinceBreak)` | the slot list plus the breaks, with `break_after_blocks`, the short last block and the rest-satisfies-a-break rule | **P3** |
| `Look.Slot {start, stop, kind}`, `Look.SlotKind`, `Look.Slot.minutes` | one slot, in **absolute seconds** | **P0** (`Seg` is built on this — §5.1), **P3**, **P5** |
| `Look.Cut {slots, breaks}`, `Cut.slotMinutes`, `Cut.breakMinutes` | the cut's result | **P3**, **P7** |
| `Look.CutCfg {blockMin, breakMin, breakAfter, minLastBlockMin}`, `CutCfg.minLast`, `mkDayCfg?` | the cut's configuration with its smart constructor and bounds | **P0** (`PlanReq` contains it, never copies it) |

### 1.3 Slot energy and the budget limit (D12, stage 5 step L4) — `Lookahead.lean`, `Arith.lean`

| name | what it is | consumed by |
|---|---|---|
| `Look.hsw100 (s)`, `Look.hswAt (wake t)` | hours since wake in exact hundredths, from **seconds** (site R11) | **P3** |
| `Look.bucket (h)` | the fork's floor-and-clamp to `0..11` | **P3** |
| `Look.predictAt (curves curve h)` | the prior step function and the learned curve, as data | **P3** |
| `Look.capForLocation (homeMax allowHome loc e)` | `min(energy, home_max_ci)` at home unless `--allow-home` | **P3** |
| `Look.energize (curves homeMax loc wake slots)` | each slot's level | **P3** |
| `Look.limitSlots (budgetMin slots)`, `Look.limitHist` | §8.4's budget limit, highest level first | **P3**, and **P7**'s Rest cut |
| `Look.Curves`, `Look.Step`, `mkStep?`, `Curves.wf`, `Look.Loc` | the fitted model as data, bounded and refused by name | **P0**'s wire |
| `Arith.ramp`, `Arith.defaultRamp` | §8.5's `w = 1` for 3 h, linearly to 0 at 6 h, with `ramp_antitone` | **P3** |
| `Arith.posteriorNum`, `Arith.energyAfter` | §8.5's posterior correction, half-up then clamped (site R5), with `posterior_can_go_negative` | **P3** |

**`Arith.energyAfter` is the *only* posterior.** Today's slot energy is `energize` composed with
`energyAfter`, in that order — **not** a second prediction path. Stage 5's cheat 118 already names
the wrong order ("the posterior applied after the cap") and is owed to L9.

### 1.4 The EDF pass and the priority rule (stage 5 step 3 and L8) — `Capacity.lean`, `Priority.lean`

| name | what it is | consumed by |
|---|---|---|
| `Cap.DayCapacity`, `minutesAt`, `Den`, `denOf?` | a day's minutes at each level over one denominator | **P4** |
| `Cap.Deadline`, `Deadline.ofRemaining`, `sortDue` | §7.3's dated candidates in due order | **P4** |
| `Cap.edf (den caps ds)`, `edfGrants`, `Grant`, `grantOf` | the EDF pass, its reservations and its grants | **P4** |
| `Grant.availQ`, `reservedQ`, `shortfallQ`, `Grant.hot`, `Grant.impossible` | §7.3's four numbers, exact | **P4**, **P8**'s banner, `edfNumbers` (§5.5) |
| `Cap.availUntil`, `reserveRest`, `reserveOut` | what a deadline may take and what it leaves | **P4**, and **gap 94**'s two Rust reserves when they die in **R3** |
| `Cap.Lookahead`, `lookaheadOf?`, `daysAscending` | the lookahead with its smart constructor | **P4** |
| `Look.lookahead (I)`, `Look.Input`, `mkInput?`, `Look.dayOf` | D10's exact mixture, days 1..n | **P4**; day 0 becomes the kernel's in **K2** |
| `Prio.binOfQ`, `binOfScaledQ`, `binOfScaledQ_congr` | §7.1's bin at an exact availability | **P4** |
| `Prio.prio (k b)`, `rootK`, `defaultPrioOf?`, `Prio.Bins`, `binsOf?` | §7.2's `p = k + bin(u)`, clamped to `0..7` | **P4** |
| `Prio.hysteresis`, `applyHysteresis`, `yesterdayOf?`, `hysteresisDays` | §7.4's one-bin-a-day rule, with its settling theorems | **P4**; `priorities_yesterday` crosses in **P0**'s wire |
| `Prio.RuleIn`, `rowOf`, `rowTable`, `rawPrio`, `finalPrio` | §7.2's whole row table | **P4** |
| `Look.Cand`, `Cand.enters`, `servedOrder`, `prioritiesWithFloors`, `CandOut` | the candidate, its EDF entry and its answer | **P4**; its *facts* become the kernel's in **K4** |

### 1.5 Everything else the planner needs and already has

| name | module | consumed by |
|---|---|---|
| `Plan.effectiveCi`, `effectiveCi_explicit` | `Plan.lean` | **P5**'s energy filter, and five goals |
| `Plan.rootPrio`, `Prio.rootK` | `Plan.lean`, `Priority.lean` | **P4** |
| `Plan.WfPlan`, `PlanCore`, `planWf`, `mapAt` | `Plan.lean` | `PlanReq.plan` |
| `Replay.Segment`, `Replay.DayAcc.segments`, `sortSegs` (+ its `mergeSort` twin) | `Replay.lean` | **P1**'s past half, through the seam |
| `Seal.OpenDay`, `Seal.DayRecord`, `Seal.Run` | `Seal.lean` | the seam **K1**, then **P1** |
| `Cal.Instant`, `Cal.instantOf`, `Cal.secondsBetween`, `Cal.Tz`, `Cal.weekdayOf` | `Cal.lean` | every instant in `Seg` |
| `Json.JVal`, `jparse`, `jemit`, `jget` | `Json.lean` | **P0**'s wire, **P8**'s `--json` |
| `Field.Clock`, `Field.DT`, `Field.Flag.hot`, `Shape.interval` | `Line.lean` | **P1**, `plan_never_moves_a_wall` |

**One name is deliberately *not* in this table.** `Look.twin` (the threshold reading of
`p_lounge`) exists only to state that D10's mixture disagrees with the fork; nothing in stage 6
calls it.

---

## 2. What is NOT built: the fork's planner, measured

The eight steps are 2,673 lines of Rust behaviour in `tm-core/src/planner.rs`, and its module
header is the only complete statement anywhere of what the planner does where the spec leaves a
choice open. **It is a specification and must be read before P1** — ten numbered choices, each of
which is either ported, or deviated from with a parity entry and a behaviour row, and there is no
third option.

The ten choices, with the build step that owns each:

| # | the fork's choice | step |
|---|---|---|
| 1 | walls placed exactly where written; `buffer:` is its own `Wall` segment; a travel-day wall **zeroes the remaining budget**; overlaps are blocked on both sides; an open `state.interrupt` is an ad-hoc wall that does **not** extend the window | **P1** |
| 2 | routines: mandatory to the earliest feasible position at or after `now`; a `pref:` anchor when still ahead and free; the rest deferred; a carried instance whose window closed may go anywhere; **the `loc:` filter is not applied to routines** | **P2** |
| 3 | `wind_down`/`bed` are segments, the `sleep` instance is consumed by them, and **everything from `wind_down` to midnight is blocked for cutting** — strictly stronger than §8.2's "no `ci ≥ 4` after wind-down" | **P2** |
| 4 | slots: `cut_slots_around` with the placed routines as *rests*, continuing the break counter from the log | **P3** |
| 5 | assignment: `batches` over `sorted_candidates`; a group keeps consecutive slots until its planned minutes are covered; **a batch is split before the filter wherever its members disagree about `loc:` or `atomic`**, and the split parts are re-sorted into §7.4's key order | **P5** |
| 5b | **the running block is reserved, not assigned** — like a wall, from `now` to the end of the block it is in, before routines and before the cut; it carries no slot energy; its block counts as one against the budget however long it runs | **P3**, **P5** |
| 6 | deferred routines take the **lowest predicted energy** free position (ties: earliest); a mandatory one may reach into the wind-down and then displace the lowest-energy assigned block; an instance with no position is named in `diagnostics.notes` | **P6** |
| 7 | Rest past the budget; optionals fill Rest and the evening before wind-down, within `max:` | **P7** |
| 8 | plan honesty = planned minutes ÷ (remaining budget × block_min), counting an unfinishable started item in full; rest debt = planned break minutes the log shows skipped or cut | **P8** |
| 9 | `a_capacity_lost` = Rest minutes at energy ≥ 4 on a day with a `ci = 5` candidate none could take; `deferred` = candidates a *posterior downgrade* cost a slot | **P8** |
| 10 | **§4.3's day file is an illustration, not a fixture**; the differences are enumerated in `tests/planner_fixtures.rs` | **P8** |

Choice 5b is the single most consequential one for the proofs, and §6.3 is about it.

---

## 3. Decisions taken inside this design, with reasons

Each is a decision the existing rules already force; none is new. They are listed so a reviewer
can object to one without re-reading the tree.

### 3.1 Architecture

1. **The seam (K1) is the stage's first commit**, before any planner step, because both L9 (D24)
   and the planner's past half (gap 255) need it and neither can be written around it. *Reason:*
   D24, plus `planner.rs:2034`.
2. **`Seg` is built on `Look.Slot`'s representation — absolute seconds — not on minutes since
   midnight.** *Reason:* AGENTS §5.3. Minutes-since-midnight would be a second representation of
   an instant beside `Cal.Instant` and `Look.Slot`, and `plan_never_moves_a_wall`'s own doc
   comment already records the defect it causes ("says nothing about a wall that crosses
   midnight"). Restating the goal over absolute seconds *removes* the caveat rather than
   inheriting it. **Gap 256.**
3. **A goal false against the fork is refuted, renamed and restated, never weakened.** *Reason:*
   AGENTS §3.1 item 3 and the E7 precedent (`Look.the_window_end_is_not_the_least_solution_as_stage_6_wrote_it`).
   §6.3's five restatements each ship with their refutation in the same commit.
4. **The kernel emits row *cells*; one Rust function pads them.** *Reason:* G1's verdict is `A`
   (the kernel owns the generated blocks) and G6's is `M` (`pad`/`truncate` stay in the TUI). The
   reconciliation that satisfies both is single ownership of *what the bytes say*, with the
   East-Asian width table where the terminal is. Subject to **OWNER Q5**.
5. **`DayPlan.hash` is the kernel's.** *Reason:* it decides whether a `plan` event is written
   (§10.1) and whether `state.last_plan_hash` changes; two implementations of it is §5.3's bug
   with a log write behind it. FNV-1a-64 over `UInt64` needs no `Float` and stage 5's step A3
   already measured the algorithm in this repo.
6. **`Planner.lean` and `Emit.lean` are two modules, not one**, and each gets its
   `import TmKernel.<Mod>` line in `kernel/TmKernel/TmKernel.lean` **in the commit that creates
   it** (§2.3). *Reason:* AGENTS §9.2's disguised-gap list — "a new module that is never imported
   ... looks built, and check 1 agrees" — and §8.4 says it of `Emit.lean` explicitly.
7. **The planner never reads the log; it reads the run.** *Reason:* D9's one reader. `PlanReq`
   carries the replay facts it needs as a decoded value produced by the seam, not a line list.

### 3.2 Proof

8. **The eleven single-run goals share one checker battery and one lift** (§6). *Reason:* §8.4
   ("a checker plus a `lift`, which is the shape to aim for everywhere in this stage"), and
   because they share their hypotheses: every one of them needs the same eligibility restriction
   (§6.3), and writing it eleven times is eleven places for it to drift.
9. **A gate that a proved lift makes unreachable is not shipped.** *Reason:* AGENTS §9.2 names
   "a check no input can fail" as a disguised gap. So Q3's options (a) and (c) are exclusive and
   the design says so rather than shipping both and calling it defence in depth.
10. **L24 and L25 are proved** (D5), and the D5 override is what makes it affordable to state
    them *correctly* — a statement with the Active exception in it is harder than the one in
    `Goals.lean` today, and under the old brake the cheap wrong one would have looked attractive.
11. **Every bounded value crossing the wire gets a smart constructor and a rejection theorem, and
    every setter gets `view ∘ set = id`** (R10, AGENTS §4). §10.4 is the table; `Segment`'s eleven
    variants and `Diagnostics`' nine families are ~8 lines each and forgetting **one** reopens
    the hole (§8.4's named trap).
12. **Every recursion over a list the wire can make large has a `foldl` form or a `@[csimp]`
    twin** (D9-21), listed per step in the README block. The assign fold, the segment list, the
    nine diagnostic lists and the row list all qualify.

### 3.3 Readings of the owner's and the documents' own words taken here (flagged; object and they change)

- §8.4's "**§12 for the emitted text**" is read as **tm-spec-v1.md §12.1** (the Today screen's
  timeline and day bar) together with **§4.3** (the day file's `<!-- tm:plan -->` block), because
  §12 as a whole is the TUI and the day file's grid is §4.3's. If "§12" meant something else,
  P8's acceptance changes.
- §8.4's "**the review block**" is read as §4.3's `<!-- tm:review -->` block, whose placeholder is
  `horizon::REVIEW_PLACEHOLDER = "review pending"` — which is what makes PLAN §4's **F3** land
  here (§3.4).
- "**D1–D14 decidable-checked on every plan the corpus produces**" is read as a *corpus-wide
  check*, which is a weaker claim than `Goals.lean`'s `∀ r`. The design keeps both and asks
  **OWNER Q3** which one the stage is accountable to.

### 3.4 FINDING (gap 252): "F3" names two different things, and §8.4 cites both

- **PLAN-lean-kernel.md §4, line 823:** `F3 | close day replaced a written review with "review
  pending" | P | needs generated-block ownership — arrives at stage 6, M until then`. A **defect**.
- **`kernel/design/stage5/stage5-D9-D10-design.md` §14.7:** `F3 | priority rule inputs
  (RuleIn.overdue, mandatory, pass; done_this_period from W's window); horizon::close_day /
  day_remaining's block_minutes_on moves into the kernel with the close tranche`. A **build step**.

AGENTS §8.4 cites the design's F3 in its inherited list ("**F3** (the priority rule inputs, and
`block_minutes_on` ...)") and PLAN's F3 in its named traps ("**F3 finally lands here**: `close
day` replacing a written review with `review pending`"). Both are true; they are different work.
This document calls them **F3-rule** (build step **K4**) and **F3-review** (build step **P8**),
and never "F3" alone.

---

## 4. Genuinely new owner questions

Eight questions. Each has a recommended default so the build is not blocked, but taking a default
is still the owner's call. **"Blocks"** names the first step that must not start without an answer
(or an explicit "take the default").

### Q1: The price. Confirm it, or narrow the scope.

**The situation.** AGENTS §8.4 prices stage 6 at **"3–4 wk"**. This design's ESTIMATE (§14.7) is
≈ **5,360 definition** and ≈ **21,350 proof** lines and ≈ **121–167 agent-days**. The gap is not
an opinion: the same estimating method priced D9+D10 at 6,550 / 23,300 and the tranche landed at
**6,534 / 23,611** — within 0.3% on definitions and 1.3% on proofs (AGENTS §4, D5's row). "3–4 wk"
is also the unit the plan used for the whole of stage 5, which landed 6,534 / 23,611 over twelve
campaign runs; by lines, stage 6 is **82% of its definitions and 90% of its proofs**. The §8.4
figure predates stage 5 and
counts only the port of `planner.rs`'s definitions, the way the "1,500 lines of `log.rs`" figure
did for D9.

What the extra buys, in the same shape D9's Q1 used:
- the proofs D5 requires, since L24 and L25 cannot be downgraded;
- the seam (K1), which §14.8's L9 row does not include because gap 210 was found two days after
  that row was written;
- the candidate collection (K4/P4), without which the planner has two readers of `remaining`,
  `ci` and `due`;
- `Emit.lean` and the architecture row that kills G1;
- five restatements with their refutations (§6.3).

**The options.**
- **(a) Confirm, and run two tracks in parallel.** Track **K** (seam, L9, F2, F3-rule) on a
  worktree; track **P** (the planner and its goals) on `rebuild-on-lean`. They collide only in
  `Boundary.lean` (the wire) and the three append-only files, and P1–P7 do not need the wire.
  This is D11's shape, which worked.
- **(b) Confirm, one track, K before P.** Simpler ledger, no merge, ≈ 15% longer in calendar
  terms by stage 5's own experience.
- **(c) Narrow.** The levers, each costed, none of which touches the substance:
  - Q3's option (c) — the gate instead of the proved lift: **−4,500 proof lines, −22 to −30
    agent-days**,
    and the eleven goals become "the produced plan passed" rather than "every plan does";
  - leave `week_plan` (`tm plan --week`'s allocation) in Rust as a recorded gap: **−700 lines,
    −5 days**, and gap 94's two reserves stay;
  - leave `explain` and `diff` in Rust: **−400 lines, −3 days**;
  - defer **P6** (deferred routines) by shipping them as "placed at the earliest free position"
    with a behaviour row: **−1,700 lines, −7 days**, and a day can quietly lose lunch, which
    choice 6 exists to prevent.

  L24, L25 and the five restatements cannot be narrowed under D5 and §3.1.

**Recommendation:** **(a)**, with (c)'s first lever held in reserve and pulled only if Q3 is
answered (c). **Blocks:** scheduling only.

### Q2: Does the kernel collect the candidates, or does the host keep sending them?

**The situation.** Since stage 5 D10 L8 the capacity request carries a candidate list whose facts
are the **host's** (`Look.Cand`'s twelve fields; README gap 113). §8.2 step 4 and §6.2 make the
candidate list a function of the tree, the recurrence rules and the replay — all three of which
are now the kernel's. Every one of `remaining`, `ci`, `due`, `overdue`, `mandatory`, `hot`,
`window`, `wall`, `optional` therefore has **two** readers today.

**The options.**
- **(a) The kernel collects.** `Cand` becomes derived from the `PlanCore` the request already
  loads plus the run the seam exposes. Kills gaps **113**, **114** and **116**; kills the
  two-reader class on nine fields; makes §7.4's hysteresis read `priorities_yesterday` from the
  state section rather than from a field the host computed. Costs **K3** (F2, the recurrence
  family) and **K4** (F3-rule) *before* P4, and a larger request. ESTIMATE +650 definition,
  +1,700 proof, −500 Rust, 11–15 agent-days, most of which is F2/F3-rule and is owed anyway.
- **(b) The host keeps sending them.** Cheaper now. The planner then has two readers of nine
  facts, §5.3's exception list grows by nine, and gaps 114 and 116 can never close: a what-if or
  a minute tick cannot re-derive what it did not compute.

**Recommendation:** **(a)**. This is the one place in stage 6 where the cheap option contradicts
the decision the rebuild is named after. **Blocks:** P4 (and K3/K4's ordering).

### Q3: Are the eleven single-run laws PROVED, or CHECKED-AND-REFUSED?

**The situation, and it is the stage's largest single decision.** `Goals.lean` states the eleven as
`∀ (r : PlanReq), …` — a theorem about *every* request. §8.4's acceptance says "D1–D14
decidable-checked on **every plan the corpus produces**" — a check about *some* plans. These are
different claims and only one of them is in the burn-down.

The checker battery (§6) is cheap either way: eleven `Bool` functions and eleven reflection
lemmas, ≈ 900 definition and ≈ 1,800 proof lines. What differs is the lift.

**The options.**
- **(a) Prove `dayPlan_ok : ∀ r, planOk r (dayPlan r) = true`.** A fold induction carrying eleven
  invariants through eight steps. The eleven goals then discharge in one line each and leave the
  burn-down honestly. ESTIMATE **≈ 4,500 proof lines, 22–30 agent-days** — about a quarter of the
  stage.
- **(b) Ship the battery as a runtime gate with a silent fallback** (a failing plan becomes an
  all-Rest day). Free. **Rejected outright, not offered:** it is a silent wrong answer, which is
  the failure class AGENTS §4 says the kernel exists to remove.
- **(c) Ship the battery as a runtime gate with a NAMED REFUSAL.** `dayPlan? : PlanReq → Except
  PlanRefusal DayPlan`, and the law is `dayPlan? r = .ok d → planOk r d`, which is `by simp`. The
  eleven goals are restated in that conditional form and discharged almost free. **Cost:** the
  kernel can refuse to plan a day — a real, user-visible behaviour change needing its row; and
  the eleven laws stop saying the planner is correct and start saying it is checked. Under
  §3.2 item 9 this and (a) are exclusive: a gate behind a proved lift is a check no input can
  fail.

**Recommendation:** **(a)**, and it is what D5's spirit asks for — but this is exactly the trade
D5 was issued about, so it is the owner's. If the answer is (c), say so *before* P0, because the
vocabulary changes (`dayPlan` becomes `dayPlan?`) and eleven goal statements change with it.
**Blocks:** P0.

### Q4: `plan_tail_drop`'s Active exception — restate it, or restrict it?

**The situation.** §8.3 writes tail-drop as "never changes the set of assigned items except by
removing a suffix in key order **(Active item excepted)**". `Goals.lean`'s `plan_tail_drop` has
**no** Active exception: it says `∃ n, assignedOf (dayPlan r') = (assignedOf (dayPlan r)).take n`.
Against the fork that is **false**: §8.2 choice 5b reserves the running block *before* the budget
is consulted, so shrinking the budget can drop items that rank *ahead* of the Active item while
the Active item stays — and the result is not a prefix.
`tm/tests/planner_invariants.rs`'s header says the same thing in its own words.

**The options.**
- **(a) Restate over the list with the Active item erased.**
  `∃ n, (assignedOf (dayPlan r')).erase a = ((assignedOf (dayPlan r)).erase a).take n`, with `a`
  the Active id when there is one. Ships with `plan_tail_drop_as_stage_6_wrote_it_is_refuted` and
  a witness. This is what §8.3 actually says.
- **(b) Restrict the theorem to requests with no Active block** (`r.active = none`). Cheaper,
  and it is §5.2's failure mode: a precondition that excludes the interesting case, so the
  conclusion never fires where the bug lives. A running block is the normal state of a working
  day.

**Recommendation:** **(a)**. **Blocks:** G2.

### Q5: What does "the day section byte-identical across four surfaces" mean?

**The situation.** §8.4's third acceptance item is a Rust test: "the day section byte-identical
across the file, `tm now`, `tm tui` and `tm plan --json`". Those four do not print the same thing
and never have. `emit::render_plan_section` writes the day file's whole grid and the TUI's
Timeline pane (`tui/app.rs:845`); **`emit::render_now_with` is a separate renderer** that prints
the current block and the next three with its own format string (`emit.rs:1512`); and
`tm plan --json` emits `Row` records, not text.

**The options.**
- **(a) "One row renderer, and every surface's rows are its output."** The test asserts that each
  row `tm now` prints, each row the TUI draws, and each `rows[].text` in `--json` is **byte-equal
  to that row as the day file wrote it**, and that `tm now`'s row set is a contiguous sub-list of
  the file's. `render_now_with` stops formatting and starts selecting. No user-visible change.
- **(b) The literal reading:** all four print the same bytes. `tm now` then prints the whole day,
  which is a behaviour change to a verb whose whole point is brevity, and the TUI pane and the
  file differ in width by construction (`Layout::new(w)`), so the literal reading is not even
  satisfiable without dropping the width parameter.

**Recommendation:** **(a)**, and record the reading in the README so the acceptance is not read
literally later and declared unmet. **Blocks:** P8's acceptance wording; R1.

### Q6: Does the kernel emit padded text, or cells?

**The situation.** G1 (verdict `A`) says "the kernel owns the generated blocks; there is exactly
one implementation of the day-section text". G6 (verdict `M`) says `pad`/`truncate` counted
characters so `⏰` broke every column, and that the fix "stays in the TUI". The day file's grid is
padded to a `Layout`, and padding needs `emit::char_width`'s East-Asian ranges (`emit.rs:288-343`).

**The options.**
- **(a) The kernel emits cells; one Rust function pads.** `Emit.lean` produces
  `Row {time, ci, p, mark, title, parent, est, actual, note}` as `List Char` cells in a fixed
  order; `emit::render_row` becomes the only thing that pads, and G6's width table stays where the
  terminal is. G1 dies by *single ownership of what the bytes say*, which is what §8.4 means by
  calling it an architecture row and not a proof row.
- **(b) The kernel emits the padded bytes.** G1 dies by kernel ownership outright and the
  one-renderer test becomes trivial. **Cost:** `char_width`'s range table (≈ 120 lines of
  ranges) is ported into Lean with no theorem worth proving about it, and the kernel acquires a
  Unicode table it must track. `Id := List Char` exists precisely to keep the proofs off UTF-8
  (AGENTS §4).
- **(c) (a), plus the kernel emits the *widths* it computed** so Rust only places them. Half of
  (b)'s cost for none of its benefit.

**Recommendation:** **(a)**. **Blocks:** P8.

### Q7: Which rows of §9 are stage 6's?

**The situation.** §8.4 names §9 (dynamic adjustment: the running block, overtime, interrupts) in
its spec sections. §9's table has thirteen rows and they are not one kind of thing: some are facts
`dayPlan` must read, one is a *consequence computation* (§9.1's "→ drops: …" runs `plan()` twice
and diffs), and two are prompt UI with timers.

**The options.**
- **(a) All of §9 in stage 6**, prompts included. The prompts are ratatui and crossterm; the
  kernel has no business in them.
- **(b) The facts and the consequence are stage 6's; the prompt UI and its timers stay Rust.**
  §11's table assigns every row. This closes gap **114** (the what-if ranks by the pre-what-if
  priorities) because the consequence replan becomes a second `dayPlan` call, and it leaves gap
  **116** (the TUI's minute replan) to Q8.
- **(c) Defer §9 to stage 7.** Then the running block and the interrupt wall are not `dayPlan`
  inputs, and §8.3's own invariants cannot be stated about the days they describe.

**Recommendation:** **(b)**. **Blocks:** P0's `PlanReq`.

### Q8: What happens if the 5 ms TUI stop condition fires?

**The situation.** AGENTS §9.1's third trigger: "a kernel call in the TUI exceeds **5 ms at 500
items**" → try the session handle, and if that is not enough, "the runtime kernel is the wrong
shape for the TUI". The measurement behind the 5 ms budget is 0.8 ms for a 500-item replan against
a 16.7 ms frame — **taken at the FFI spike, not against this kernel**, and stage 6 is the stage
that adds a kernel call to every replan. **FINDING (gap 257): nothing in the tree measures it.**
`cli_latency.rs`'s seven T11 rows measure CLI verbs; none is a TUI replan, and three of the seven
are too noisy across sessions to read as single numbers anyway (gap 240).

**The options.**
- **(a) Measure at P5 and decide then**, with the fallback **pre-authorised**: the TUI replans on
  reload rather than on a tick, gaps 114/116 stay open as a recorded deliberate narrowing, and no
  step is ever blocked waiting for this answer.
- **(b) Build the fast path up front** — "a fast implementation behind the same interface with the
  proofs on the interface", §8.4's own recorded answer for `planWf`'s quadratic `mapAt`.
  ≈ 10 agent-days spent before there is evidence it is needed.
- **(c) The session handle** (`lean_mark_mt` + a mutex, UI thread only). Against AGENTS §4's
  settled "nothing but `String` crosses the FFI; the C shim is permanent", so it is a
  plan-tier change, not an agent's.

**Recommendation:** **(a)**, and add the missing instrument — a T-row for a 500-item replan
through the FFI — as part of **P5**, so the trigger has a number before it can fire. **Blocks:**
nothing; gates R3.

---

## 5. `Planner.lean`'s vocabulary, settled

Today's `Goals.lean` declares `SegKind`, `Seg`, `DayPlan`, `PlanReq` and `dayPlan` as
**provisional**, with three honest caveats in their doc comments. This section settles them. Every
change from the provisional form is justified by a rule, not a preference.

### 5.1 `Seg` — on `Look.Slot`'s representation

```lean
/-- §8's `Segment`, on stage 5's instant representation.  `start`/`stop` are
absolute seconds (`Cal.Instant.sec`), exactly `Look.Slot`'s UTC seconds `[start, stop)`,
so a wall that crosses midnight is representable and `plan_never_moves_a_wall` needs no caveat. -/
structure Seg where
  start    : Nat
  stop     : Nat
  kind     : SegKind
  energy   : Option (Fin 6)
  item     : Option Id
  inst     : Option (List Char × List Char)   -- the (item, inst) pair `Replay.Facts.instances`
  flags    : SegFlags                         -- is keyed by; there is no `InstKey` type today
deriving DecidableEq, Repr
```

**Changed from provisional:** `startMin`/`endMin : Nat` (minutes since midnight) → `start`/`stop`
in absolute seconds (§3.1 item 2, **gap 256**); `inst` and `flags` restored, because §8.2
step 6 reports an unplaced instance by key and §9 marks the running block `open` — both of which
are rows of the day section, and P8 cannot emit what `Seg` does not carry.

**Bounded, so R10 applies:**

```lean
def Seg.wf (s : Seg) : Bool := decide (s.start ≤ s.stop) && decide (s.stop ≤ maxPlanSec)
abbrev WfSeg := { s : Seg // Seg.wf s = true }
def mkSeg? (…) : Except SegErr WfSeg          -- the smart constructor
theorem mkSeg?_refuses_an_inverted_segment …  -- rejection theorem
theorem mkSeg?_refuses_past_the_horizon …
```

`SegFlags` is a plain record of `Bool`s (`current`, `done`, `open`, `underused`, `hot`) —
§5.1's rule: a `Bool` predicate on a plain record plus a `Subtype`, never a dependent proof field.

### 5.2 `SegKind` — eleven variants, bounded

The provisional form has ten constructors; §8's `SegKind` has eleven counting `Batch`'s payload
distinctly, and §8.4's named trap prices them at "~8 lines per type, and forgetting it on **one**
type silently reopens the hole".

```lean
inductive SegKind
  | block | batch (ids : BatchIds) | brk | routine | wall | rest
  | optional | windDown | sleep | lost | ghost
deriving DecidableEq, Repr
```

`BatchIds` is bounded (`maxBatch = 16`, the most §7.5 can gather under `batch_max_min`), with
`mkBatch?` and `mkBatch?_refuses_too_many_members`. `ghost` is the arrival plan's row (§12.1's
ghost row, `.tm/arrival_plan.json`), which the day bar draws and the provisional form has no name
for.

### 5.3 `DayPlan` — the whole day, past and future

```lean
structure DayPlan where
  day          : Day
  window       : Nat × Nat          -- absolute seconds, from Look.windowOn
  blockMin     : Nat
  budgetBlocks : Nat
  segments     : List WfSeg
  diagnostics  : Diagnostics
  priorities   : List (Id × Fin 8)
  planHash     : UInt64
deriving Repr
```

**Changed from provisional:** `windowStart`/`windowEnd : Nat` → the pair in absolute seconds;
`diagnostics`, `priorities` and `planHash` restored. The provisional comment's reason for dropping
the first two — "both are reports, and no §8.3 invariant is about them" — is right about §8.3 and
wrong about the stage: `diagnostics` is §8.2 **step 8**, which is one of the eight steps this
stage owns, and `planHash` decides whether a log line is written (§3.1 item 5).

`Diagnostics` is nine bounded lists plus §9's `dropped_tail` and §11's two ratios as
numerator/denominator pairs (§11 "only as integer numerator/denominator pairs" — `plan_honesty`
and `rest_debt_min` never divide in the kernel):

```lean
structure Diagnostics where
  underused      : IdList            -- each of the nine is bounded and has its
  aCapacityLost  : Nat               -- own smart constructor (R10)
  hot            : IdList
  impossible     : List (Id × Nat)   -- id and shortfall, exact
  conflicts      : List (Id × Id)
  blocked        : IdList
  deferred       : IdList
  waiting        : List (Id × Nat)
  notes          : List Note
  droppedTail    : IdList
  planHonesty    : Nat × Nat         -- §11: numerator, denominator; Rust divides
  restDebtMin    : Nat
```

**Setters and `view ∘ set = id`.** `DayPlan` is produced, not edited, so it has no public setters
and owes no such law. The obligation lands where a value is genuinely updated: `Diagnostics`'
accumulation during the fold (`Diagnostics.withNote`, `withUnderused`, …) and `Seg.withEnergy`,
each of which gets `Diagnostics.notes_withNote`, `Seg.energy_withEnergy` and friends in the shape
AGENTS §4 requires. The bounded-list setters (`IdList.cons?`) return `Option` and get their
rejection theorem beside their view law.

### 5.4 `PlanReq` — what §9 and the seam make necessary

```lean
structure PlanReq where
  plan     : WfPlan
  run      : Seal.Run          -- the seam (K1): today's replay, not the log
  now      : Cal.Instant
  tz       : Cal.Tz
  day      : Look.DayCfg       -- contains CutCfg; never a second copy
  curves   : Look.Curves
  homeMax  : Nat
  allowHome : Bool
  loc      : Look.Loc
  state    : RuntimeIn         -- §9 / §10.2, decoded — see §9
  caps     : Cap.Lookahead     -- the kernel's own lookahead, day 0 included after K2
  overrides : Option PlanOverrides
```

**Changed from provisional:** `now : Day` → `Cal.Instant` (a planner without a time of day cannot
place a slot); `windowStart`/`windowEnd`/`blockMin`/`budgetBlocks` are **removed as fields** and
computed from `day` and `state` by `Look.windowOn` and `Look.budgetOf` — carrying them as fields
would be a second copy of the window (§5.3). The provisional comment's claim that "widening this
record does not disturb any of them" is what makes the widening safe, and it holds: every one of
the thirteen goals reads only the output.

### 5.5 `dayPlan` and `edfNumbers`

```lean
def dayPlan (r : PlanReq) : DayPlan          -- (a) under Q3
def dayPlan? (r : PlanReq) : Except PlanRefusal DayPlan   -- (c) under Q3
```

`edfNumbers (r : PlanReq) (i : Id) : Nat × Nat` stops being provisional and becomes
`(g.deadline.need, g.avail)` from `Cap.grantOf` over `r.caps` — a projection of stage 5's grant,
with `Grant.impossible` already proved. It is the one provisional `def` in `Goals.lean` whose real
definition exists today; **P4 deletes it from `Goals.lean` on the day P4 lands**, and the
burn-down does not count `def`s, so nothing in check 7 moves. Say so in P4's block, because a
reader comparing goal counts will otherwise look for a discharge that did not happen.

---

## 6. L26's eleven single-run goals: one checker, one lift

This is the stage's dominant pattern, and §8.4 says so. Getting it right once is most of the
stage.

### 6.1 The shape

```lean
/-- One decidable check over a produced plan, with the name its refusal carries. -/
structure Check where
  name : CheckName
  run  : PlanReq → DayPlan → Bool

/-- The eleven of §8.3, in one place. -/
def checks : List Check :=
  [ ⟨.overbook,      noOverbook⟩,     ⟨.oneBlock,     oneBlockAtATime⟩
  , ⟨.energyFilter,  energyFilterOk⟩, ⟨.overWall,     noBlockOverAWall⟩
  , ⟨.overBreak,     noBlockOverABreak⟩, ⟨.windDown,   noDemandingAfterWindDown⟩
  , ⟨.wallMoved,     wallsUnmoved⟩,   ⟨.rank,         monotoneInRank⟩
  , ⟨.hot,           hotBeforeQueue⟩, ⟨.impossible,   impossibleKept⟩
  , ⟨.batch,         batchDoesNotReachPast⟩ ]

def planOk (r : PlanReq) (d : DayPlan) : Bool := checks.all (fun c => c.run r d)

/-- **THE LIFT** — the stage's largest single proof (OWNER Q3 (a)). -/
theorem dayPlan_ok (r : PlanReq) : planOk r (dayPlan r) = true
```

Each of the eleven goals is then three things:

1. **the checker** — a `Bool` function over `(r, d)`, 10–25 lines, total, decidable by
   construction;
2. **the reflection lemma** — `checkerX r d = true ↔ <the Prop the goal states>`, 20–60 lines,
   proved once by `List.all_eq_true`, `decide_eq_true_eq` and the list lemmas core already has;
3. **the discharge** — one line:

```lean
theorem plan_does_not_overbook (r : PlanReq) : … :=
  (noOverbook_iff r _).mp (checks_all (dayPlan_ok r) ⟨.overbook, noOverbook⟩ (by decide))
```

`checks_all : planOk r d = true → ∀ c ∈ checks, c.run r d = true` is proved once, by
`List.all_eq_true`; the `by decide` is the membership, which is a literal list.

**Why a battery and not eleven separate lifts.** The eleven share their hypotheses (§6.3). One
battery means the eligibility restriction is written once, the fold induction carries one
conjunction, and adding a twelfth check later is one list entry plus one invariant — not a twelfth
copy of the induction.

### 6.2 What `dayPlan_ok` costs, honestly

The induction is over the assign fold (§8.2 step 5), with the other seven steps as pre- and
post-conditions on its input and output. Eleven invariants, eight steps, and three of the
invariants (rank, hot, batch) are *relations between two candidates* rather than properties of one
segment, so they need the sorted order of the candidate list as a hypothesis carried through.

ESTIMATE: **≈ 4,500 proof lines, 22–30 agent-days**, roughly a quarter of the stage. This is the
figure Q3 asks the owner to accept or trade. It is not the eleven checkers that are expensive;
§8.4's "cheap" is right about them and silent about this.

### 6.3 FINDING (gap 251): five of the eleven are FALSE AS WRITTEN, and the proptest says so

`tm/tests/planner_invariants.rs`'s header (lines 16–39) states the exceptions that
`Goals.lean` does not have. Under AGENTS §3.1 item 3 each is **refuted, renamed and restated**,
in the step that owns it, with the refutation committed beside the restatement — exactly the shape
stage 5 used for E7.

| goal | why it is false against the fork | restated as | owner |
|---|---|---|---|
| `plan_does_not_overbook` | §8.2 choice 5b: "the running block excepted — §9 gives it its minutes whatever the budget says". A day whose Active block runs long has Σ block minutes > budget × block_min | Σ over blocks **that are not the Active reservation** | **P5** |
| `plan_respects_the_energy_filter` | the Active block "takes no slot at all" and carries no slot energy. **Survives as written** because `he : s.energy = some lvl` never fires for it — but only by accident, and the restatement makes the reason a hypothesis rather than luck | unchanged in force; a `hactive : s.item ≠ r.state.activeId` hypothesis added so the statement says what it means (§5.2) | **P5** |
| `plan_is_stable_across_a_replan` | the running block and the running interruption **grow** rather than move (`SegFlags::open`), so a segment with `end ≤ now` in run 1 is present but **not equal** in run 2 | over segments that are `end ≤ now` **and not `open`**; open segments get their own law — they only ever extend | **G3** |
| `plan_is_monotone_in_rank` | §8.2 step 5 skips a `loc:`-constrained, `atomic` or `max:`-capped item "for reasons the invariant is not about" | the two candidates are additionally **comparable**: same `loc:` eligibility, neither `atomic`-blocked, neither `max:`-exhausted | **P5** |
| `plan_puts_hot_before_the_queue` | same reason, plus a dep-blocked or `Waiting` hot item is not assigned at all | the hot item is additionally **eligible** at some slot of the day | **P5** |
| `plan_never_drops_an_impossible_item` | §7.3's "still scheduled with everything available" is about capacity, not eligibility: an impossible item that is dep-blocked is not assigned | same eligibility hypothesis | **P5** |
| `plan_never_batches_past_an_equal_ci_candidate` | a batch is **split** before the filter wherever members disagree about `loc:` or `atomic`, and the split parts are re-sorted | the skipped candidate is additionally in the same split group | **P5** |

That is seven statements touched, five of them false as written and two sharpened. **The
eligibility predicate is the same in five rows**, which is the argument for the shared battery:

```lean
/-- §8.2 step 5's filter, as one predicate — the thing five of §8.3's
comparisons have to be restricted to, and the thing the fork's proptest
restricts to in prose. -/
def eligibleAt (r : PlanReq) (d : DayPlan) (s : Seg) (i : Id) : Bool
```

Writing it once, in `Planner.lean`, is the difference between five consistent restatements and
five slightly different ones.

### 6.4 The order the eleven become provable

A goal is provable when the step that establishes its invariant has landed, not before.

| after | provable |
|---|---|
| **P1** | `plan_places_no_block_over_a_wall`, `plan_never_moves_a_wall` |
| **P2** | `plan_places_no_demanding_block_after_wind_down` |
| **P3** | `plan_places_no_block_over_a_break`, `plan_reserves_one_block_at_a_time` |
| **P5** | `plan_does_not_overbook`, `plan_respects_the_energy_filter`, `plan_is_monotone_in_rank`, `plan_puts_hot_before_the_queue`, `plan_never_drops_an_impossible_item`, `plan_never_batches_past_an_equal_ci_candidate` |

Six of the eleven land in one step, which is why **P5** and **G1** are the stage's two largest
rows and why G1 may be split across commits along §6.4's own boundary if it will not fit.

---

## 7. L24 and L25 — the two relational laws, priced

**D5 governs, and D5 supersedes §8.4's older prose.** AGENTS §8.4 still carries the recommendation
to "leave the two relational ones to the proptest" and says the stage may end at 2 goals rather
than 0. **D5, the owner's later word, overrides it**: relational laws keep being proved, L24 and
L25 included, and a two-run theorem a change breaks is re-proved in that step, never downgraded to
a property test and never deleted. This section prices them on that basis.

### 7.1 L24 — `plan_tail_drop`

**What it says.** Removing minutes from the day never changes the set of assigned items except by
removing a suffix in key order, the Active item excepted (**OWNER Q4**).

**What it needs.**
1. The assign fold as an explicit `foldl` over `(slots, cursor, budgetLeft, acc)`, with a
   `Monotone` lemma: a smaller `budgetLeft` at the same cursor yields an `acc` that is a prefix of
   the larger one's.
2. **The cursor lemma**: the candidate order does not depend on the budget. This is where
   §7.3's EDF pass enters — `avail` is computed from `caps`, not from the budget — and stage 5's
   `edf_commutes_with_scaling` and `binOfScaledQ_congr` do the arithmetic half already.
3. **The Active erasure** (Q4 (a)): the reservation is made before the fold and is independent of
   `budgetBlocks`, so erasing it from both sides restores the prefix property. One lemma.
4. The refutation `plan_tail_drop_as_stage_6_wrote_it_is_refuted` with an 8-`Entry` witness — a
   running block plus two candidates, one ranking ahead of it — probed at `MemoryMax=8G timeout
   120` per §14.0 item 4.

**ESTIMATE:** 120 definition / **1,600 proof** lines, 8–12 agent-days. `inventory` budgeted
tail-drop alone at "plausibly a week"; that was for the statement without the Active exception.

### 7.2 L25 — `plan_is_stable_across_a_replan`

**What it says.** A replan changes no segment with `end ≤ now`.

**What it needs, and why it is cheaper than it looks.** The fork's past half is **not planned**: it
is `Planner::past_segments()`, the day's segments replayed from the log
(`tm-core/src/planner.rs:2034`). So the law splits:

1. **The past half is a function of the run alone.** `pastSegs r` reads `r.run` and `r.now` and
   nothing else; two requests with the same run and `now' ≥ now` agree on `pastSegs` up to `now`.
   This is an equality of two `filterMap`s over the same list — cheap, ≈ 300 proof lines.
2. **The fold starts at `max now (window start)`.** Nothing the fold produces has `stop ≤ now`.
   One lemma over `Look.cutSlots`' lower bound, ≈ 200 lines.
3. **The `open` exception** (§6.3): the running block and the running interruption end at `now` by
   construction and therefore *grow* as `now` advances. They are the segments that are in the past
   half and still change, and the restated law excludes them and gives them their own monotone
   law (`an_open_segment_only_extends`), ≈ 400 lines.
4. Refutation of the as-written form: a running block, two instants. ≈ 100 lines.

**ESTIMATE:** 120 definition / **1,400 proof** lines, 7–11 agent-days.

**Together: ≈ 3,000 proof lines and 15–23 agent-days** — about 15% of the stage's proof budget for
two of its thirteen goals. That is the honest price, and it is the price of the laws that caught
stage 4's defects.

### 7.3 The proptest is aimed through the FFI, not rewritten

§8.4's named trap says so and the plan's acceptance says so: `tm/tests/planner_invariants.rs`
(882 lines, 256 cases, **`tm/tests/`, not `tm-core/tests/` — gap 253**) keeps its generators and
its explicit tail-drop and stability sections, and its `plan()` call becomes a kernel call through
the FFI. The same pattern applies to `tm-core/tests/grammar_proptest.rs` (395 lines). Under D5 the
proptest is **not** a substitute for L24/L25; it is the instrument that catches what the theorems
do not quantify over — the generators build running blocks, interruptions and late days, and the
theorems are about one fold.

---

## 8. `Emit.lean` and single ownership: which renderer dies

### 8.1 What G1 is, and what kills it

PLAN §4, G1, verdict **A**: "`tm plan` wrote the day section with a private stand-in renderer in
`cli/render.rs`, so the file, `tm now` and `tm tui` printed three different texts" → "the kernel
owns the generated blocks; there is exactly one implementation of the day-section text.
Structural, but architectural." §8.4 repeats it: an **architecture** row, not a proof row. **Do not
credit the Lean compiler for it.**

### 8.2 The renderers today, and what happens to each

| renderer | file | fate |
|---|---|---|
| `emit::render_plan_section` / `_with` / `render_segment_row` / `render_row` | `tm-core/src/emit.rs:662-816` | **the survivor's padding half.** Its cell *content* moves to `Emit.lean`; `render_row` keeps `pad`/`truncate`/`display_width` (G6) and becomes the one padder (**Q6 (a)**) |
| `emit::render_now_with` | `emit.rs:1512-1613` | **DIES.** It is a second renderer with its own format string. It becomes a **selection** over the one row list: the current row and the next three (**Q5 (a)**) |
| `cli/render.rs::timeline` / `rows` / `kind_name` | `tm/src/cli/render.rs` (117 lines) | `kind_name` dies — the kernel's `SegKind` name is the wire word. The rest already delegates and stays as the thin CLI adapter |
| `tui/today.rs::seg_title` | `tm/src/tui/today.rs:299` | **DIES.** A second title renderer beside `emit::title_cell` |
| `emit::render_diagnostics` / `render_banners` | `emit.rs:1614-1719` | content moves to `Emit.lean` (§8.2 step 8's list is the kernel's); the Rust keeps the line assembly |
| `emit::daybar_cells` / `render_svg` | `emit.rs:1092-1506` | **STAYS Rust.** The day bar is pixels, G7 is its property test, and no §8.3 invariant is about it |
| `review::render_day` / `render_week` / `render_month` | `tm-core/src/review.rs:1147+` | the **review block**'s content moves in **P8** (F3-review); the §11 monitors' ratios cross as numerator/denominator pairs and Rust divides |

### 8.3 The one-renderer Rust test

`tm/tests/one_renderer.rs` — a **Rust** test, as §8.4's acceptance says, not a Lean theorem.

```
build one fixture day (the §4.3 illustration plus a running block and one batch)
assert: for every row r the day file's <!-- tm:plan --> block contains,
   - `tm plan --json`'s rows[i].text == r                         (byte-equal)
   - the TUI's App row i == r                                     (byte-equal, same Layout)
   - if r is in `tm now`'s window, `tm now`'s line for it == r    (byte-equal)
assert: `tm now`'s rows are a contiguous sub-list of the file's rows
assert: exactly one function in the workspace formats a plan row  (a grep guard, like §12's)
```

The last line is the part that keeps G1 dead: a grep guard in the test, in the shape §12's
one-reader grep already uses (41 hits after the switch, down from 125). Without it, a future
private stand-in renderer reintroduces G1 and three byte-equality assertions still pass, because
they compare the two surfaces that both call the new one.

### 8.4 F3-review

PLAN §4's F3: `close day` replaced a written review with `review pending`
(`horizon::REVIEW_PLACEHOLDER`). It lands in **P8** because it needs generated-block ownership:
once `Emit.lean` owns the `<!-- tm:review -->` block's content, `close day` can tell a written
review from the placeholder it wrote, which it cannot do while two things write the block. Its
acceptance is a behaviour row plus a `cli_close_kernel.rs` leg: a day file with a hand-written
review survives `tm close day`.

---

## 9. The Rust runtime state stage 6 depends on, and how it crosses

§8.4: "**Depends on.** All of stage 5 and stage 4, plus runtime state that lives in Rust:
`active`, `window`, `budget`, `break`, `interrupt`, `last_plan_hash`."

`RuntimeState` is `tm-core/src/store.rs:1993`. It crosses in a new `state` section of the request,
decoded by a smart constructor, under R10 and D9-21.

| field | Rust type | wire | bound, constructor, rejection theorem |
|---|---|---|---|
| `date` | `Option<NaiveDate>` | day number | `Cal`'s day bound; `mkStateDay?`, `refuses_a_day_past_9999` |
| `wake` | `Option<NaiveTime>` | `Look.WakeClock` | **reuse** `WakeClock.wf`, `badWake` — already exists |
| `arrival` | `Option<NaiveTime>` | `Field.Clock` | **reuse** `Field.Clock`'s bound |
| `loc` | `Option<String>` | `Look.Loc` | **reuse** `Loc.curve`; an unknown location is refused by name |
| `window` | `Option<(NaiveTime, NaiveTime)>` | two `Field.Clock` | `mkWindow?`, `refuses_an_inverted_window` |
| `budget` | `Option<u32>` | `Nat` | `maxBudget = 96`; `mkBudget?`, `refuses_an_impossible_budget` |
| `active` | `Option<ActiveBlock>` | `{id, started, estMin, paused}` | `mkActive?`; `refuses_an_estimate_past_the_day`, `refuses_a_start_after_now` |
| `break` | `Option<BreakState>` | `{started, plannedMin, where}` | `mkBreak?`, `refuses_a_negative_break` |
| `interrupt` | `Option<InterruptState>` | `{started, id}` | `mkInterrupt?`, `refuses_a_start_after_now` |
| `last_plan_hash` | `Option<String>` | 16 hex chars | `mkHash?`, `refuses_a_short_digest`; the kernel **computes** the comparand (§3.1 item 5) |
| `priorities_yesterday` | `BTreeMap<Id, u8>` | `List (Id × Nat)` | ≤ 1,024 entries (the candidate bound); **reuse** `Prio.yesterdayOf?` (`Fin 8`) and its two theorems |
| `closed` | `Closed` | three periods | already crosses for the close tranche; reused unchanged |

**D9-21.** `priorities_yesterday`'s decoder recurses over a wire-sized list and needs its `foldl`
form or `@[csimp]` twin, as `readCandList` already has. Nothing else in the table recurses.

**The `--allow-home` flag and `loc`** are the two inputs L9 is blocked on (README gap 93 item 3:
"`--allow-home` is honoured host-side only"), so **K2 and P0 want the same section** — another
reason the seam and the vocabulary are the stage's first two steps.

---

## 10. The wire

### 10.1 The request gains two sections

```
{ "tz": …, "now": …, "docs": […],            // as today
  "log": { … },                               // as today — and its Run now reaches the rest (K1)
  "capacity": { … },                          // "day0" DELETED by K2 — LANDED, stage 6 W-13 step L9
  "state": { … },                             // NEW (§9)
  "plan": { "blockMin": …, "day": {…}, "curves": {…}, "allowHome": …,
            "overrides": … } }                // NEW
```

### 10.2 The response gains the day plan

```
{ "run": {…}, "report": {…}, "log": {…}, "lookahead": {…},   // as today
  "plan": { "day": …, "window": [s, s], "budgetBlocks": …,
            "segments": [ … ], "diagnostics": { … },
            "priorities": [ … ], "hash": "…",
            "rows": [ { "time": …, "ci": …, "p": …, "mark": …, "title": …,
                        "parent": …, "est": …, "actual": …, "note": … } ] } }
```

`rows` is Q6 (a)'s cells. §8.4's "the `report` shape is inherited, not invented here" holds: the
`report` half is unchanged and `plan` is a new sibling, so nothing stage 4 settled is reopened.

### 10.3 Refusals

Every refusal is named (§5.7). The new families: `planRefusal.*` (`badState`, `badWindow`,
`badBudget`, `badActive`, `badBreak`, `badInterrupt`, `badHash`, `badOverride`, `tooManyCands`)
and — only under **Q3 (c)** — `planCheckFailed (name : CheckName)`.

### 10.4 R10's table for this stage

Every bounded value this stage adds, with its constructor and rejection theorem, is §5.1–§5.3 and
§9's tables taken together: **`Seg`, `BatchIds`, `SegFlags`, `DayPlan.budgetBlocks`, the nine
`Diagnostics` lists, `Note`, `CheckName`, and the twelve state fields** — 25 types, ≈ 200
definition lines and ≈ 500 proof lines of pure R10 obligation. The named trap is real: "forgetting
it on **one** type silently reopens the hole", so each step's README block lists the types it
added and the theorem name for each.

---

## 11. §9's dynamic-adjustment surface: what is stage 6's (OWNER Q7)

| §9 row | the fact | stage 6? | where |
|---|---|---|---|
| Block finished (`d`) | `done` logged | **yes** — a replay fact through the seam | K1, P1 |
| Timer passes `est × r` (overtime) | the **prompt** and its 15-minute re-prompt | **no** — ratatui UI | stays Rust |
| …its **consequence** ("→ drops: …") | `dayPlan` run twice and diffed | **yes** — closes gap **114** | P8 (`planDiff`) |
| Interruption (`i` … `r`) | an ad-hoc wall from `t_i` to `now`; does **not** extend the window | **yes** — a `PlanReq.state` input | P0, P1 |
| Energy report (`0`–`5`) | the posterior δ | **yes** — `Arith.energyAfter`, already built | P3 |
| Break overran | the actual length | **yes** — a replay fact | P3 |
| Late wake / arrival | window, budget | **yes** — `Look.windowOn`, `budgetOf`, already built | P0 |
| Location change (`l`) | `runtime.loc`, `home_max_ci` | **yes** — `Look.capForLocation`, already built | P3 |
| Calendar sync adds a wall | a new `Interval` | **yes** — `Look.wallIndex` re-indexes | P1 |
| Deadline or estimate edited | need, `u`, HOT | **yes** — the EDF pass, already built | P4 |
| Routine skipped (`k`) | instance Skipped / deferred | **yes** — recurrence, K3 (F2) | K3, P2, P6 |
| Event arrives | Waiting → Todo | **yes** — a candidate fact, K4 | K4, P4 |
| Idle prompt | the **prompt**; the attribution | prompt **no**, attribution **yes** (a replay fact) | stays Rust / K1 |
| The running block | reserved, not assigned (choice 5b) | **yes**, and it is why five goals are restated | P3, P5, §6.3 |

**Gap 116** (the TUI's minute replan ranks the last load's candidates) is **not** closed by this
table — it is closed by a kernel call per tick, which is **OWNER Q8**'s subject. Say so rather
than letting it look closed.

---

## 12. The seam, L9, F2 and F3-rule (D24, D25)

D24 and D25 fold four pieces of work into this stage. They are track **K** and they come first.

| step | what | why here |
|---|---|---|
| **K1** the seam | expose the `log` section's `Seal.Run` to the capacity path: a signature change through `logOp`, `logAnswerOf`, `logSectionWith`, `runCapZ`, with `readLogSection_is_zoneOf_then_logSectionWith`, `the_zone_is_read_once_and_feeds_both_sections` and `runCap_without_capacity_is_runWithLog` **re-proved over their new shapes, never weakened** (D5) | gap 210; L9, F2, F3-rule **and the planner's past half** (gap 255) all need it |
| **K2** L9 — **LANDED** (stage 6 W-13 step L9, gap 93 closed) | day 0 from the kernel's own replay: the `at` stamp with `nowDisagrees`, the state section (`date`, `window`, `budget`, `arrival`, `loc`, `allowHome`), site R10 (`Arith.roundAway`, **signed**) and **five** configured decimals through `written_pair`, not two; `day0` and `badDay0` deleted, and `Ctx::window`/`Ctx::today_slots` with them; `kernel_lookahead_parity.rs` **re-aimed** to compare against `Ctx::today_slots` exactly (92 day-0 comparisons, 0 disagreements) | gap 93; D24 |
| **K3** F2 | the recurrence family (`done_dates` first and count, `last_done`, instances, `latest_named`, `is_done`) read inside the kernel; each fact's last Rust reader goes with its tranche | design §14.7; needed by P2, P6 and Q2 (a) |
| **K4** F3-rule | `RuleIn.overdue`, `mandatory`, `pass`; `done_this_period` from W's window; `block_minutes_on` moves in with the close tranche, reading a sealed window record for an old date (D13) | design §14.7; needed by P4 and Q2 (a); closes gap **113** |

**FINDING (gap 255), repeated because it changes the ordering:** §14.8's L9 row prices L9 at
200 / 600 / −150 / 4–6, and that row was written on 2026-09-14, **two days before gap 210 was
found**. It therefore does not include the seam. K1 is priced separately below and the L9 figure
is carried unchanged.

---

## 13. Parity and the oracle

- **The instrument is anchored OUTSIDE the tree (D21).** T5 and the door suite compare against
  fork point **4748911** with frozen answers in `tm/tests/fixtures/fork-4748911-*.jsonl`;
  `fork_arm` runs unconditionally. **A failing comparison is never repaired by reintroducing an
  in-tree reader.**
- **The frozen comparand is read at full precision** (gap 235): the workspace pins serde_json with
  `float_roundtrip`, and `the_frozen_comparand_is_read_at_full_precision` fails **by name** if that
  is dropped. Stage 6 compares far more `f64`-derived numbers than stage 5 did — every slot energy
  on today's day — so this guard matters more here, not less.
- **Rebuild the oracle before trusting it** with
  `kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh` (16G, outside the repo) and **read its
  usage banner**: provenance is not freshness (AGENTS §7.3).
- **The next free parity number is P37**, and **gap 226** says the parity list has no single home
  and no check. Stage 6 will issue the largest parity tranche since stage 5. **Settle gap 226
  before the first entry**, or the same mistake that issued P32 twice happens at a larger scale.
- **Expected exceptions** (each to be recorded *before* the run that measures it, as L7 did):
  today's slot energies move from the fork's `f64` to the kernel's exact prediction (P21's family);
  the posterior is exact rather than rounded per report; `a_capacity_lost` and `deferred` follow
  the posterior; batch splitting around `loc:`/`atomic` re-sorts; and D10's mixture already
  disagrees with `capacity::lookahead` by owner decision.

---

## 14. The build plan

### 14.0 Before any step

1. **Numbers.** At `0585e72`: highest **gap 240**, highest **cheat 157**, highest **parity P36**
   (P37 free). This design takes gaps **250–257** (§20); **258 and 259 are free**. Gaps **241–244**
   were left unused inside W-12's repair range (that block's closing line) and **245–249** were
   never allocated — **do not reuse any of them without checking the README's newest block**. Before each commit, re-read the
   README's newest block; if a parallel track took numbers meanwhile, renumber **before**
   committing, never after (AGENTS §6.2, §6.4), and keep the label-to-number map in the block.
2. **Ranges, if two tracks run (Q1 (a)).** Track K and track P each get a range at the start and
   never take a number outside it. Two gap-number collisions happened in this campaign because
   parallel tracks shared one sequence.
3. **Memory.** Every `lake`, `lean`, `cargo`, `check.sh`, `tm` and oracle invocation is capped with
   `systemd-run --user --scope -p MemoryMax=40G -p MemorySwapMax=0 --quiet`. Benchmarks,
   generators and the oracle build use `MemoryMax=16G`. **The cap is never raised (D18).**
4. **The `decide` budget** (AGENTS §5.10a): every new `decide` or `rfl` witness is probed first in
   a scratch copy at `MemoryMax=8G timeout 120`; a witness holds at most 8 `Entry` values, at most
   2 zone transitions and literals of at most 90 characters; instants are `Nat` literals, never
   parsed text; a realistic input is **never** evaluated — it is an instance of a round-trip
   theorem used as a rewrite; a probe that exceeds the budget is split into per-arm lemmas;
   **never `native_decide`**. Per step: at most 20 new probed witnesses, and `check.sh`'s wall
   time may rise by at most **10%**, measured and recorded. **Baseline for this stage: 3.142 s**
   (§0.3).
5. **The recursion rule (D9-21).** Each step's README block lists every function it adds that
   recurses over a list the wire can make large, with its `foldl` form or `@[csimp]` twin.
6. **Every step commits green** (AGENTS §7.5): `check.sh` seven `ok`; `cargo test --workspace` 0
   failed with the count recorded and compared against **1,311 across 78**; the FFI suite; T5; the
   door suite; `cli_switch_acceptance`; `cli_latency`'s seven T11 rows — **three of which are
   noisy across sessions and must never be quoted as single numbers** (reseal 197.5–212.6 ms,
   3-day-old routine 121.6–136.8 ms, `review week` 248.1–253.3 ms; the **later verb** row spans
   146.66–147.01 ms and is the reliable baseline, gap 240); and `kernel_call_counts`. A step that
   adds a module adds its `import` line in `TmKernel.lean` **in the same commit** and the block
   says so.
7. **Rules for goals.** A goal enters `Goals.lean` in the step whose definitions let it elaborate.
   It leaves **only** when proved, with `#print axioms Tm.<name>` appended to `Check.lean` first
   (§3.2's burn-down protocol). **A goal is never deleted without its proof**, and a statement
   that is false is refuted and renamed, not quietly fixed (§6.3).
8. **Owner answers gate steps:** Q3 before P0; Q7 before P0; Q2 before P4 (and before K3/K4's
   ordering); Q4 before G2; Q5 and Q6 before P8; Q1 before scheduling; Q8 gates nothing but is
   answered before R3. **"Take the default" is an answer.**
9. **Read `tm-core/src/planner.rs`'s module header before P1** (§2). It is the only complete
   statement of the ten choices the spec leaves open, and a step that ports a choice without
   knowing it exists produces a parity failure it cannot explain.

**Cost columns** are ESTIMATE: Lean definition lines / Lean proof lines / Rust lines / agent-days.

### 14.1 Track K: the seam and what it unblocks

| step | depends on | files | goals (added → discharged) | acceptance | cost |
|---|---|---|---|---|---|
| **K1** the seam | — | `Boundary.lean` (`logOp`, `logAnswerOf`, `logSectionWith`, `runCapZ`, `logOpFast` and its `@[csimp]`), `Check.lean` | none added; **three laws re-proved over new shapes** | check.sh; `cargo test` unchanged; the three laws' names unchanged and their statements strengthened, not weakened; gap **210** closed | 120 / 450 / 0 / 2–3 |
| **K2** L9 (day 0) — **LANDED** | **K1**; ~~Q7~~ (it did **not** gate this step: day 0 reads `state.json`'s `date`/`window`/`budget`/`arrival`/`loc` and `--allow-home`, and **no** §9 row — `active`, `break`, `interrupt`, `last_plan_hash` never cross the wire) | `Lookahead.lean`, `Boundary.lean` (`at`, `state`, `posterior`, `sleep`), `Arith.lean` (site R10), `kernel_capacity.rs` (−`day0`, +the `log` section), `kernel_log.rs` (`capacity_log_section`), `kernel_bridge.rs` (`call_text`), `ctx.rs` (−`window`, −`today_slots`), and four test files | site R10's `roundAway_withinOne` / `roundAway_mono` | parity against `Ctx::today_slots` **exactly**, not P1, at 92 comparisons with 0 disagreements; `kernel_lookahead_parity.rs` **re-aimed**, not extended; cheat 118 taken as **cheat 158**; gap **93** closed | measured **+1,056/−78 Lean, +297/−69 Rust** against the estimate 200 / 600 / −150 / 4-6 |
| **K3** F2 recurrence | **K1** | `Replay.lean`, `Plan.lean`, a recurrence tranche | the recurrence family's laws | that tranche's parity; **a grep shows no Rust reader** of each moved fact | 350 / 900 / −250 / 6–8 |
| **K4** F3-rule | **K1**, K3; **Q2** | `Priority.lean`, `Seal.lean` (`block_minutes_on` from a sealed window record), `Boundary.lean` | `RuleIn`'s inputs derived, with their laws | the priority wiring's parity; gaps **79–80**, **113** closed | 300 / 800 / −200 / 5–7 |

### 14.2 Track P: the planner

| step | depends on | files | goals (added → discharged) | acceptance | cost |
|---|---|---|---|---|---|
| **P0** vocabulary | **Q3**, **Q7** | `Planner.lean` (**new**, + its import line), `Goals.lean` (the five provisional decls replaced) | the 25 R10 rejection theorems; the setter view laws | check.sh; every bounded type has its constructor **and** its rejection theorem, listed by name in the block; `Seg` is on `Look.Slot`'s seconds (gap **256** closed) | 450 / 900 / 0 / 5–7 |
| **P1** walls | P0, **K1** | `Planner.lean` | `plan_places_no_block_over_a_wall`, `plan_never_moves_a_wall` → discharged (burn-down 13 → 11) | choice 1 ported: `buffer:`, travel-day zeroing, pairwise conflicts, the interrupt wall; the **past half** from the run; cheats for "a wall placed where there was room" and "an overlap filled" | 300 / 900 / 0 / 5–6 |
| **P2** routines | P1, **K3** | `Planner.lean` | `plan_places_no_demanding_block_after_wind_down` → discharged (→ 10) | choices 2 and 3 ported; the `loc:` filter **not** applied to routines; the `sleep` instance consumed by wind-down; cheat "a routine placed outside its window" | 450 / 1,400 / 0 / 7–9 |
| **P3** slots | P2, **K2** | `Planner.lean` (**reusing** §1.2 and §1.3 entirely) | `plan_places_no_block_over_a_break`, `plan_reserves_one_block_at_a_time` → discharged (→ 8) | choices 4 and 5b; **a grep proving no second `cutSlots`, `energize` or `windowEnd`**; the Active reservation carries no slot energy | 250 / 700 / 0 / 4–5 |
| **P4** priority | P3, **K4**, **Q2** | `Planner.lean`, `Lookahead.lean` (candidate collection) | `edfNumbers` becomes real and leaves `Goals.lean` (no burn-down change — say so) | §7's pass is the kernel's end to end; gaps **113**, **114** closed; parity for the candidate facts | 350 / 900 / −300 / 5–7 |
| **P5** assign | P4 | `Planner.lean` | the six §6.4 goals **stated**; discharged in G1 | choice 5 ported incl. the batch split; `eligibleAt` written **once**; the 500-item replan measurement (Q8); the five refutations of §6.3 | 700 / 2,600 / 0 / 12–16 |
| **P6** deferred routines | P5 | `Planner.lean` | — | choice 6: lowest-energy placement, displacement, the un-placed note in `diagnostics.notes` | 400 / 1,300 / 0 / 6–8 |
| **P7** rest and optionals | P6 | `Planner.lean` | — | choice 7; optionals within `max:`; Rest past the budget | 200 / 600 / 0 / 3–4 |
| **P8** emit | P7; **Q5**, **Q6** | `Emit.lean` (**new**, + its import line), `Boundary.lean`, `emit.rs`, `review.rs`, `tui/today.rs` | — | choices 8, 9, 10; the review block; **F3-review**; §11's ratios as num/den pairs; `render_now_with` and `seg_title` **deleted**; the grep guard | 900 / 1,800 / +400 / −900 / 10–14 |

### 14.3 Track G: the goals

| step | depends on | what | cost |
|---|---|---|---|
| **G1** the lift | P5 (and §6.4's per-step boundary) | `dayPlan_ok` and the eleven discharges; burn-down 8 → 2 | 150 / 4,500 / 0 / 22–30 |
| **G2** L24 | G1; **Q4** | `plan_tail_drop` restated and proved, with its refutation; burn-down 2 → 1 | 120 / 1,600 / 0 / 8–12 |
| **G3** L25 | G1 | `plan_is_stable_across_a_replan` restated and proved, with its refutation and `an_open_segment_only_extends`; **burn-down 1 → 0** | 120 / 1,400 / 0 / 7–11 |

### 14.4 Track R: the Rust retirement

| step | depends on | what | cost |
|---|---|---|---|
| **R1** one renderer | P8 | `tm/tests/one_renderer.rs` with the grep guard; **G1 is dead** | 0 / 0 / +250 / −700 / 3–4 |
| **R2** the proptest through the FFI | P8, G2, G3 | `tm/tests/planner_invariants.rs` aimed at the kernel; `grammar_proptest.rs` likewise | 0 / 0 / +300 / −200 / 3–4 |
| **R3** `planner.rs` retires | R1, R2, **Q8** | `tm-core/src/planner.rs` deleted with its last caller; gap **94**'s two reserves die; gap **116** closes or is recorded as deliberate | 0 / 0 / −2,700 / 4–6 |

### 14.5 The dependency graph, in one line each

```
K1 ──┬─ K2 ─────────────────────────┐
     ├─ K3 ─── K4 ──┐               │
     └──────────────┼───────────────┼── P4 ── P5 ── P6 ── P7 ── P8 ── R1 ─┐
P0 ── P1 ── P2 ── P3 ┘              ┘                  │                  ├─ R3
                                     G1 ── G2, G3 ─────┴──────── R2 ──────┘
```

`P0` needs only Q3 and Q7, so **track P can start the day the owner answers**, in parallel with
K1. `P1` needs K1 (the past half) and `P3` needs K2 (day 0's posterior); everything else in P is
sequential.

### 14.6 What a step that will not fit does

Commit the green part, record the rest **by name** in AGENTS §9.2's four-part gap format, leave
the tree clean, and say so plainly. Five steps in this campaign refused honestly and the ledger
survived every one. A partial landing that hides is the only unrecoverable outcome. **P5, P8 and
G1 are the three rows most likely to need this**, and each has a natural internal boundary: P5 at
the batch split, P8 at the review block, G1 at §6.4's per-step goal groups.

### 14.7 Cost, in one table (ESTIMATE)

| tranche | Lean definitions | Lean proofs | Rust (net) | agent-days |
|---|---:|---:|---:|---:|
| K (seam, L9, F2, F3-rule) | 970 | 2,750 | −600 | 17–24 |
| P (the eight steps) | 4,000 | 11,100 | +400 / −1,200 | 57–76 |
| G (the thirteen goals) | 390 | 7,500 | — | 37–53 |
| R (the Rust retirement) | — | — | +550 / −3,600 | 10–14 |
| **stage 6 total** | **≈ 5,360** | **≈ 21,350** | **≈ +950 / −5,400** | **≈ 121–167** |

**What these numbers mean.**
- **The ratio is ≈ 3.98 : 1**, above the D9/D10 tranche's 3.61 : 1 and below stage 4's 4.80 : 1,
  because track G is nearly all proof with almost no definition behind it. Under D5 it informs and
  stops nothing.
- **Against the library.** The library is **78 modules and 73,557 lines** at 4.03 : 1. Stage 6 adds
  about **82%** of the D9/D10 tranche's definitions and about **90%** of its proofs.
- **Against §8.4's "3–4 wk"**: by lines this is 82% of stage 5's definitions and 90% of its
  proofs, and the plan called stage 5 "3–4 weeks" too. **OWNER Q1** asks about it.
- **Agent-days** follow the input designs' unit and the stage-4/5 steps landed several a day, so
  **compare lines, not calendar time**.
- **If Q3 is answered (c)**, subtract ≈ 4,500 proof lines and 22–30 agent-days from track G: the
  total becomes ≈ **5,360 / ≈ 16,850 / 91–145 agent-days**.

---

## 15. `Goals.lean` additions and restatements, as Lean signatures

**The rule.** A group enters `Goals.lean` under `# STAGE 6` in the step named in its heading,
because only then do its names elaborate. It leaves when proved and appended to `Check.lean`
(§3.2's burn-down protocol). The thirteen that are there today are **not re-added**; five are
**restated** (§6.3) and each restatement ships with its refutation in the same commit.

```lean
-- P0: the vocabulary's R10 obligations (in-step; the burn-down does not move)
theorem mkSeg?_refuses_an_inverted_segment (a b : Nat) (h : b < a) : …
theorem mkBatch?_refuses_too_many_members (ids : List Id) (h : maxBatch < ids.length) : …
theorem Diagnostics.notes_withNote (d : Diagnostics) (n : Note) : …   -- view ∘ set = id
-- …and 22 more, listed by name in P0's README block

-- P5: the eligibility predicate the five restatements share
def eligibleAt (r : PlanReq) (d : DayPlan) (s : Seg) (i : Id) : Bool

-- P5: the five refutations (each with an ≤ 8-Entry witness, probed at 8G)
theorem plan_does_not_overbook_as_stage_6_wrote_it_is_refuted : …
theorem plan_is_monotone_in_rank_as_stage_6_wrote_it_is_refuted : …
theorem plan_puts_hot_before_the_queue_as_stage_6_wrote_it_is_refuted : …
theorem plan_never_drops_an_impossible_item_as_stage_6_wrote_it_is_refuted : …
theorem plan_never_batches_past_an_equal_ci_candidate_as_stage_6_wrote_it_is_refuted : …

-- G1: the battery and the lift
def planOk (r : PlanReq) (d : DayPlan) : Bool
theorem checks_all (r : PlanReq) (d : DayPlan) (h : planOk r d = true) : …
theorem dayPlan_ok (r : PlanReq) : planOk r (dayPlan r) = true

-- G3: the open-segment law L25's restatement needs
theorem an_open_segment_only_extends (r r' : PlanReq) (s s' : Seg) : …
theorem plan_is_stable_across_a_replan_as_stage_6_wrote_it_is_refuted : …

-- G2
theorem plan_tail_drop_as_stage_6_wrote_it_is_refuted : …
```

---

## 16. `Negative.lean` cheats (append at the end; labels renumbered at commit, §6.2)

Highest today: **157**. This stage's, by step — each must fail at a line of its own, and a block
that quietly starts compiling is a disguised gap (§9.2):

| step | cheat |
|---|---|
| K1 | the capacity section reads a run from a *different* request |
| K2 | day 0's posterior applied **after** the home cap (stage 5's owed cheat 118) |
| P0 | a `Seg` with `stop < start` accepted; a batch of 17 |
| P1 | a wall placed where there was room; an overlap filled |
| P2 | a routine placed outside its window; a `ci = 5` block after wind-down |
| P3 | a block placed on a break; a slot cut past the window end; the Active block given a slot energy |
| P4 | a candidate's bin read before the EDF pass (the shape of cheat 141) |
| P5 | a batch reaching past an equal-`ci` candidate; an item assigned above its `ci`; the budget exceeded by a **non-Active** block |
| P6 | a deferred routine taking a higher-energy slot than a free lower one |
| P7 | an optional placed outside Rest and the evening |
| P8 | a second row renderer; a `plan_honesty` that divides in the kernel |

---

## 17. The stage-6 parity exception list

Entries start at **P37** (gap 226 — settle its home first, §13). Each is recorded **before** the
run that measures it, as L7 did, so a disagreement cannot be discovered and named in the same
breath.

---

## 18. Latency budget math

- **The base.** A later verb at three years is **146.9 ms** — the one T11 row that holds still
  (five capped runs across two sessions: 146.66, 146.85, 146.87, 146.95, 147.01 ms; spread 0.2%).
  Three rows do **not** hold still and must never be quoted as single numbers (gap 240).
- **What this stage adds per call.** One `dayPlan` over ≤ 1,024 candidates and ≤ 96 slots, plus
  `Emit`'s rows. The EDF pass and the lookahead are already in the measured 146.9 ms.
- **The TUI.** §9.1's 5 ms at 500 items. **Nothing measures it (gap 257)**; P5 adds the
  instrument, and Q8 decides what happens if it fires.
- **The levers stay unstarted** (D25): gaps **121, 122, 123, 126, 127, 143**. Genesis is the only
  cost that grows with log length (first verb ≈ 2.18 s against a 5 s bound), so they buy headroom
  rather than fix a defect. **A step that spends one says so in its block.**

---

## 19. Risks

1. **`dayPlan_ok` does not close** (§6.2). *Mitigation:* §6.4's per-step boundary lets G1 land in
   groups; Q3 (c) is the pre-priced fallback and is a plan-tier decision, not an agent's.
2. **P5 is too large for one session.** It is the biggest row in the table. *Mitigation:* §14.6's
   named boundary at the batch split, and D19's pattern — land everything separable first.
3. **The five restatements are contested.** A reviewer may read §8.3's prose as normative and this
   design's restatements as weakening. *Mitigation:* each ships with its refutation, which is a
   compiled proof that the prose's literal form is false of the fork — not an argument.
4. **The seam's three laws cannot be re-proved over the new shapes.** *Mitigation:* K1 is its own
   commit and refuses cleanly if they cannot; D5 forbids weakening them, so the refusal is the
   correct outcome and is cheap at that point.
5. **Parity noise swamps the signal.** Stage 6 compares every slot energy on today's day, where
   the fork uses `f64`. *Mitigation:* gap 235's full-precision guard, and P21's family recorded
   before the run.
6. **Two tracks collide in `Boundary.lean`.** *Mitigation:* D11's shape — separate worktrees,
   append-only shared files under each step's banner, and §14.0 item 2's ranges.
7. **The §5.13 human drives are still owed** for stages 3, 4 and 5, and **an agent cannot perform
   them** (gap 182). Stage 6 adds a fourth. *Mitigation:* none available to an agent; it is named
   here so the owner sees the debt compounding.

---

## 20. Gaps and behaviour rows to record

This pass takes gaps **250–257**; **258 and 259 are free**. Each is written in AGENTS §9.2's
four-part form in the README block.

| gap | what is not done | which stage clears it |
|---|---|---|
| **250** | §8.4 prices stage 6 at "3–4 wk" against this design's ≈ 5,360 / ≈ 21,350 lines and 121–167 agent-days — 82% of stage 5's definitions and 90% of its proofs, and the plan called stage 5 "3–4 weeks" too | the owner's answer to Q1; then AGENTS §10.2 |
| **251** | five of the thirteen stage-6 goals are false as written against the fork, and two more are true only by accident | P5, G2, G3 (§6.3) |
| **252** | "F3" names a PLAN §4 **defect** and a design §14.7 **build step**, and AGENTS §8.4 cites both without distinguishing them | this document (F3-rule / F3-review); AGENTS §8.4 when the owner confirms |
| **253** | §8.4 cites `tm-core/tests/planner_invariants.rs`; the file is `tm/tests/planner_invariants.rs` (882 lines, 256 cases, in the workspace suite) | AGENTS §8.4's citation |
| **254** | "the day section byte-identical across the file, `tm now`, `tm tui` and `tm plan --json`" is not satisfiable literally | Q5; then P8/R1 |
| **255** | the seam (gap 210) blocks the **planner**, not only L9: the fork's `plan()` returns the past half from the replay | K1 |
| **256** | `Goals.lean`'s `Seg` uses minutes since midnight while `Look.Slot` uses absolute seconds — two representations of an instant | P0 |
| **257** | nothing in the tree measures a TUI replan through the FFI, so §9.1's 5 ms trigger has no instrument | P5 (the instrument), Q8 (the decision) |

**Behaviour rows this stage will owe** (recorded next to the rule each replaces, with a theorem
separating them — never taken silently):

| input | before | after | why |
|---|---|---|---|
| `tm plan` on a day with a running block | the Rust planner's placement | the kernel's | P5 |
| `tm now` | `render_now_with`'s own text | the day file's rows, selected | Q5 (a), P8 |
| `close day` on a file with a hand-written review | replaced with `review pending` | left alone | F3-review, P8 |
| a capacity verb with `--allow-home` | honoured host-side only | honoured in the kernel | K2 |
| a day whose plan fails a §8.3 check | — | **only under Q3 (c)**: a named refusal | Q3 |

---

## 21. Reserved for a completeness critique of this document

Stage 5's design was revised the same day against `design/critique.md` (3 blockers, 17 major, 12
minor) and §21 recorded where each item landed. If this document is critiqued before it is built,
its responses go here.

---

## 22. Owner answers

*(empty — to be filled in when the owner answers §4's eight questions, in the shape of the stage-5
design's §22: one row per question with the decision number it becomes, and a §22.1 listing the
consequences for §14's step plan. §4's recommendations are what an agent takes only if the owner
says "take the default".)*

| question | answer | decision | differs from §4's recommendation? |
|---|---|---|---|
| Q1 price | | | |
| Q2 candidate collection | | | |
| Q3 proved lift or named gate | | | |
| Q4 tail-drop's Active exception | | | |
| Q5 what "byte-identical" means | | | |
| Q6 padded text or cells | | | |
| Q7 §9's rows | | | |
| Q8 the 5 ms trigger | | | |
