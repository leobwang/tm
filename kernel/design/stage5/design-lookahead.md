# Stage 5 design: D10's capacity lookahead as an exact mixture

Read-only design pass, 2026-09-14, over `rebuild-on-lean` at `c2cf4dc` plus the uncommitted
stage-5 step 1 work (`Tree.lean`, README "Stage 5 step 1"). Facts come from
`design/inventory.md` §6 and from reading the fork-point Rust. Functions are cited by name.
Nothing in the repo was built or run. The only thing executed was a throwaway Python model
(`design/lookahead-proto/proto.py`), used to check five claims before relying on them. Each
is marked **[checked in proto]** where it is used.

Owner questions that are genuinely new are marked **OWNER-Qn** and collected in §10. Every
other choice here is a design choice the build agent can take, with its reason.

---

## 0. The answer in one screen

1. **Units.** Capacity is carried in units of `1 / capDen` minute, with **one fixed
   denominator for the whole request: `capDen = 10^6`**. It is not stored per day or per
   level. A day's capacity is `unitsAt : Fin 6 → Nat`. The EDF pass is then plain `Nat`
   `+`, `-` and `min`. A need of `n` minutes reserves `n · capDen` units.
2. **Weights.** A lounge weight is `w : Nat` with `w ≤ capDen`, meaning `p = w / capDen`.
   Rust sends `p_lounge` as a decimal `num/den` pair (the step-1 config route). The kernel
   accepts it only if `den ∣ 10^6`, so the scaling is exact. Anything it cannot represent
   exactly is **refused by name, never rounded**. This rests on OWNER-Q1: the decimal text or
   the double?
3. **The mixture.** For a future day, with pure-location minute histograms `L`, `H : Fin 6 → Nat`:
   `unitsAt l = w · L l + (capDen − w) · H l`. Three things are proved: the value lies
   between `capDen · min` and `capDen · max`; it equals `capDen · H` at `w = 0` and
   `capDen · L` at `w = capDen`; and it denotes `p·L + (1−p)·H` exactly for the decoded `p`.
4. **Mix after the budget, never before.** `L` and `H` are each already cut to the day's
   budget. Mixing first and cutting afterwards gives a different, wrong answer
   **[checked in proto]**, and a refutation theorem pins that down.
5. **Utilisation needs no new comparator.** `u ≥ e` at `avail` units is
   `Arith.utilGe (need · capDen) avail e`. `binOf`, `isHot` and `isImpossible` are reused
   unchanged. One anchor theorem says `util (need·capDen) a` *is* `need / (a/capDen)`.
6. **Where the histograms come from.** Nothing location-dependent in the fork is
   statistical, so the kernel computes `L` and `H` itself. That means pulling forward from
   stage 6: §8.1's `windowEnd` (E7a/E7b, restated, §4), §8.2 step 3's `cutSlots`, a
   future-day `predict` with the home cap, and the budget limit. The budget limit is
   simplified to a per-level greedy, proved equal to the fork's per-slot sort. Rust keeps
   only the fitted numbers as data. The cheaper interim is to have Rust send `L` and `H`
   (§3.4); that is OWNER-Q2.
7. **Parity.** Entry P1 is made checkable by a **threshold twin**: the kernel lookahead run
   with every weight forced to `0` or `capDen` by `2w ≥ capDen` must equal fork
   `capacity::lookahead × capDen` **exactly**. The real run is checked only against the
   twin's bounds. New entries P7–P10 go on the list before the harness runs (§7).
8. **Cost.** 5–8 agent-weeks for everything including day 0 and wiring. About 2 of those
   weeks are stage-6 work paid early (E7, the slot cut), so stage 6 shrinks by the same
   amount (§9).

---

## 1. What the fork does, reduced to the parts D10 touches

`capacity::lookahead(walls_by_date, cfg, model, today_slots, from, days, wake_default)` works
as follows (inventory §6.1, read again here):

- **Day 0** is `DayCapacity::from_slots(today_slots)`, taken as handed in. The location is
  known and there is no mixture. **D10 does not apply to day 0.**
- **Each later day** runs these steps:
  1. `arrival = local_dt(date, model.expected_arrival_on(wd))`
  2. `wake = local_dt(date, wake_default)`, where `wake_default` is *today's* wake clock
  3. `loc = Lounge iff p_lounge_on(wd) ≥ 0.5`
  4. `walls = walls_by_date[date]`
  5. `(end, budget) = window_and_budget(arrival, walls)`
  6. `cut = cut_slots(arrival, end, walls)`
  7. `energize` with `Posterior::none`, `slept = None` and `allow_home = false`
  8. `limit_to_budget(slots, budget, block_min)`

**Which pieces read `loc`.** The only ones are `curve_key(loc)` inside `energy::predict` and
`EnergyCtx::cap_for_location` (`min(e, home_max_ci)` at home). `window_and_budget`,
`cut_slots` and `walls_on` do not read `loc`. So for each future day there is **one window,
one cut, two energize passes and two budget limits**. That shape is what the design exploits.

**Future-day `predict` has no hidden inputs.**
- `Features::under_slept` is `slept_min.is_some_and(…)`, which is false for `None`, so the
  sleep shift is 0.
- `Posterior::none` has no reports, so `correct` returns `round(pred + 0)`, which is `pred`.
- The `blocks_done` and `since_break_min` features are v2-only and `predict` does not read
  them.

So a future slot's energy is:

`cap_loc( min 5 ( curve_loc(hsw(slot.start − wake)) ) )`

- `curve_loc` is `model.energy[curve][bucket]` if present, else `prior_level(cfg, curve, hsw)`.
- `bucket = floor(hsw)` clamped to `0..11`. A negative `hsw` saturates to bucket 0.

**The budget limit.** `limit_to_budget` sorts slots by `(energy desc, start asc)` and takes
`min(slot minutes, left)`. The result is summed per level, and the sum depends only on the
per-level totals. That is, `limit_slots(slots, B) == limit_hist(hist(slots), B)`, where
`limit_hist` takes `min(h[l], left)` from level 5 down **[checked in proto: 20,000 random
cases]**. The kernel therefore needs no sort.

**The EDF pass.** `priority::compute` works on a copy of the capacities. For each dated
candidate in due order it does `avail = available_until(work, due, ci)`,
`take = min(need, avail)` and `reserve(work[..upto(due)], take, ci)`, and computes
`u = utilization(need, avail)`. `floor_pass` reads `available_until` on the same `work`.

Consumers outside the pass:
- `planning::week` (`WeekOut.days[].minutes_at_level`, `week_grid`)
- `planner::week_from_run` (`capacity_min = total()`)
- the TUI queue, `queue.rs`, which does **its own second `capacity::reserve`** up to the week's end

---

## 2. Representation

### 2.1 Choice: one fixed denominator, `capDen = 10^6`

| option | cost | verdict |
|---|---|---|
| a `Q` per day **per level** | the same `p` is repeated across six levels; `available_until` sums across days with different denominators, so it cross-multiplies and the pairs grow with every reservation (README step 1's cost (ii)) | rejected |
| a `Q` per **day** (one denominator per day) | still cross-day sums with mixed denominators; a normalisation needs its own proof | rejected |
| one denominator per request, `D = lcm` of the ≤ 7 weekday denominators | exact for any decimal; `Nat.lcm`, `Nat.dvd_lcm_left` and `Nat.dvd_lcm_right` are in core v4.33.1 (`Init/Data/Nat/Lcm.lean`); but `D` has no stated width (seven 18-digit denominators give up to 10^126), so the host cannot hold units in `u64` and R10 has no bound to state | the fallback if OWNER-Q1 rejects the precision bound |
| **one fixed `capDen = 10^6`**, weights restricted to `den ∣ 10^6` (at most 6 decimal places) | no lcm; every unit count ≤ `1440 · 10^6 · days`, which fits `u64` for any calendar lookahead; the EDF pass is `Nat` add, subtract and min; comparisons reuse `Arith` unchanged | **chosen** |

What D10 requires, and how this meets it:
- **"Exact numerator/denominator pairs through the EDF pass."** Every day and level
  numerator shares the one denominator `capDen`. A pair is `⟨unitsAt l, capDen⟩`.
- **"Nothing rounded."** A weight the scaling cannot represent is refused, not approximated.

Why 10^6:
- The fit writes `round2`, whose denominators are 100, 50, 25, 20, 10, 5, 4 or 2. All of
  them divide 10^6.
- Hand edits with more than 6 decimals are the only thing refused.

What happens under the other answer to OWNER-Q1:
- Every finite double in `[0,1]` is a multiple of `2^-1074`, so `capDen = 2^1074` would be
  equally exact.
- Units would then be ~330-digit bignums, the host could no longer hold them, and the queue's
  second reserve (§6.3) would have to move into the kernel first.

### 2.2 Types (new module `TmKernel/Capacity.lean`, imports `Arith`, `Plan`, `State`)

```lean
namespace Tm.Cap

/-- Units per minute of capacity.  The one denominator of every capacity pair. -/
def capDen : Nat := 1000000

/-- R10: `p_lounge` scaled to `capDen`.  Built only by `mkWeight?`. -/
abbrev Weight := { w : Nat // w ≤ capDen }

/-- The decoder.  `n / d` must be a probability whose scaling to `capDen` is exact. -/
def mkWeight? (n d : Nat) : Except String Weight :=
  match Arith.ofPair? n d with
  | none => .error "badWeight"                       -- zero denominator
  | some _ =>
    if hnd : n ≤ d then
      if hdiv : capDen % d = 0 then .ok ⟨n * (capDen / d), (proof)⟩
      else .error "weightPrecision"                   -- more than 6 decimals
    else .error "weightAboveOne"

/-- Whole minutes per energy level, one location, one day (a fork `[u32; 6]`). -/
abbrev Hist := Fin 6 → Nat

/-- A day of expected capacity, in units (`unitsAt l / capDen` minutes). -/
structure DayCap where
  day     : Nat            -- a `Cal` day; typed `Nat` because of the omega trap (AGENTS §8.3)
  unitsAt : Fin 6 → Nat

def mix (w : Weight) (lounge home : Hist) : Fin 6 → Nat :=
  fun l => w.val * lounge l + (capDen - w.val) * home l

def ofHist (d : Nat) (h : Hist) : DayCap := ⟨d, fun l => capDen * h l⟩   -- day 0, pure
```

The three numbers crossing the wire, and their stated widths (R10):
- **Weights** are pairs of JSON `Nat` with `d ≤ 10^6` implied by `d ∣ 10^6`.
- **Minutes** are whole minutes, each bounded by the day's window (≤ `2 · 1440 + walls`).
- **Output units** are `Nat` numerals ≤ `1440 · 10^6 · days`.

`JVal` is not widened.

### 2.3 The three mixture theorems, and one that anchors the meaning

`w ≤ capDen` is the subtype's property throughout.

```lean
theorem mix_between_the_locations (w : Weight) (L H : Hist) (l : Fin 6) :
    capDen * min (L l) (H l) ≤ mix w L H l ∧ mix w L H l ≤ capDen * max (L l) (H l)

theorem mix_at_zero_is_home (L H : Hist) (l : Fin 6) :
    mix ⟨0, Nat.zero_le _⟩ L H l = capDen * H l

theorem mix_at_one_is_lounge (L H : Hist) (l : Fin 6) :
    mix ⟨capDen, Nat.le_refl _⟩ L H l = capDen * L l

/-- §5.2: the units denote `p·L + (1−p)·H` for the `p` that was decoded, not some other weight. -/
theorem mix_denotes_the_weighted_sum {n d : Nat} {w : Weight} (h : mkWeight? n d = .ok w)
    (L H : Hist) (l : Fin 6) :
    mix w L H l * d = capDen * (n * L l + (d - n) * H l)
```

**How the proofs go.**
- **Bounds.** Split on `L l ≤ H l`. Write `w·L + (D−w)·H` with `D − w + w = D` (omega on
  `w ≤ D`). Then each side is a `Nat.mul_le_mul` step. There is no division anywhere.
  Around 40 lines.
- **Endpoints.** `simp [mix]`.
- **Meaning.** `capDen = d · k` with `k = capDen / d` (`Nat.div_mul_cancel` on the `hdiv`
  branch). Unfold, then `Nat.mul_sub`/`Nat.sub_mul` distribution with `n ≤ d`. Around 60 lines.

The same bounds lift to `atLeast` sums (`Σ_{l ≥ ci}`) by induction over the level list:
`mix_atLeast_between_the_locations`. That is what the EDF pass actually reads.

### 2.4 The mixture is taken after the budget

D10 says "*expected* minutes at each energy level". The expectation over the location of the
capacity the day would have is `p · limit(L) + (1−p) · limit(H)`. Limiting the mixed
histogram instead is a different number:

**[checked in proto]** Take budget 60 min, `L = {5:60, 4:60}`, `H = {3:120}` and `p = 1/2`.
- After: `{5:30, 3:30}`.
- Before: `{5:30, 4:30}`.

```lean
theorem mixing_before_the_budget_is_not_the_expectation :
    ∃ (w : Weight) (B : Nat) (L H : Hist) (l : Fin 6),
      mix w (limitHist B L) (limitHist B H) l ≠ limitHist (B * capDen) (mix w L H) l
```

The witness is the one above, with `w = 500000`. `decide` sees six `Fin` values and small
numbers. Probe it under the 8 GB cap as AGENTS §5.10a says. It is also the Negative.lean
cheat "mix before limit".

This is D10's wording read literally, not a new decision. The refutation sits beside it so
the other reading cannot come back unnoticed.

---

## 3. Where each input comes from once D9 lands

### 3.1 Inputs table

| input | source after D9 | crosses the wire as | kernel type and decoder | named refusals |
|---|---|---|---|---|
| `p_lounge` per weekday | `model.json` `p_lounge` (a partial `WeekdayMap<f64>`, fitted `round2(shrunken_mean)` by Rust's statistics) **and** `config.expected.p_lounge` (a full `PerWeekday<f64>`) | `"pLounge":{"model":{"Mon":{"num":9,"den":10},…},"config":{…all 7…}}`, both from Rust's `decimal_pair` (§3.2) | `Weekday → Weight`. **The kernel applies `Model::p_lounge_on`'s fallback** (model, else config), so the rule has one proved definition and Rust sends raw data | `badWeight`, `weightAboveOne`, `weightPrecision`, `pLoungeMissingWeekday` (config short of a day) |
| expected arrival per weekday | `model.json` `expected_arrival` (a partial map of `"HH:MM"`) and `config.expected.arrival` (a full map) | strings, as in the files | `Weekday → Clock` via `Line.parseClock` (strict `HH:MM`); fallback in the kernel (`Model::expected_arrival_on`) | `badArrival` |
| energy curves, learned | `model.json` `energy`: `{curve: [u8…]}`, any length | `"energy":{"lounge":[4,5,…],"home":[…]}` | `List (List Char × List Nat)`, each level `< 256` (a stated width) | `badLevel` (≥ 256). No length refusal: a short vector falls through to the prior, as `Model::energy_at`'s `.get(bucket)` does |
| energy curves, prior | `config.energy.prior`: `BTreeMap<String, StepFn>`, whose range keys are `f64` hours | `"prior":{"lounge":[{"from":{"num":0,"den":1},"to":{"num":1,"den":1},"level":4},…],…}`, steps in the `StepFn` vector's order | a list of steps with from/to as `Arith.Pos` hours, converted to minutes by cross-multiplication when compared, never divided; `level < 256` | `badStep`: a negative key, which the fork's `parse_key` can produce from `"-1+"`; parity entry P9 |
| `home_max_ci` | config `u8` | `Nat` | `Nat`, applied as `min`, which is what the fork does | `badLevel` if ≥ 256 |
| `block_min`, `break_min`, `break_after_blocks`, `min_last_block_min` | config `u32` | `Nat` | `Nat < 2^32`; `block_min > 0` reuses stage 3's `BlockMin` subtype | the existing `badBlockMin`, plus `badDayConfig` |
| window | config `window_hours: f64`, `window_cap: NaiveTime`, `budget_ratio: f64` | `windowHours` pair, `windowCap` `"HH:MM"`, `budgetRatio` pair | `Arith.Pos`; `windowMin = Arith.halfUpQ (60 · windowHours)` (R3 reopened as a kernel-owned half-up site, §4.3); `budget = floor(60 · wh / block_min · br)` as one exact `floorQ`, which equals the fork's `budget_blocks` | `badWindow` (zero denominator) |
| walls | **the tree**, already loaded: fork `Ctx::walls_on` is every item not in `Done`/`Dropped` whose `effective_shape` is `Interval{start,end}`, with `start − buffer`, covering the date | nothing: the kernel derives them | `wallsOn p day : List (Nat × Nat)` in `DT.abs` minutes, from `Plan.effectiveShape`, `Core.buffer` (`Field.viewBuffer`) and `.settled` status | — |
| future-day wake clock | fork: `Ctx::wake_time` is `state.wake`, else today's replayed `wake` time, else `model.wake_or_expected(today's weekday)` | `state.json` `wake` already crosses with the state; the replayed wake is **D9's replay output** | a `Clock`, chosen by the kernel with `wake_or_expected`'s order | — |
| `days` | fork `priority::lookahead_days(cands, today)`, at least 7, through the furthest effective due or floor period end | nothing: derived by the **priority tranche's** candidates | `Nat` | — |
| `today` | `now` (`Boundary.lean` `ReqClock`) | existing | `Nat` day | existing `badNow` |
| day 0's histogram | fork `Ctx::today_slots`: the stored window or formula, cut from `max(start, now)`, energised with **today's posterior** (the replay's `energy_on(today)`), `slept_min`, `blocks_done` and `allow_home` | **interim:** a `Hist` argument, §5.3. **Final:** derived (step L10) | `Hist` | `badHist` (a level ≥ 2^32) |

Nothing on this list is log-derived except the wake and day 0. Both arrive through D9's
replay, so they are plain arguments of the kernel functions that read them. README step 1
type (c) applies unchanged.

### 3.2 The one Rust encoder: `decimal_pair`

It goes in `tm/src/cli/kernel_bridge.rs` beside the step-1 config pairs. It must be **the
only** way a `f64` reaches the kernel for capacity: safety, bins and ratios share it.

```rust
/// A finite f64 as the exact decimal Rust prints for it (the shortest text that reads back
/// to the same double), as numerator/denominator.  Refuses what has no short exact decimal.
fn decimal_pair(x: f64, max_places: u32) -> Result<(u64, u64), CapErr> {
    if !x.is_finite() || x < 0.0 { return Err(CapErr::NotANonNegativeDecimal) }
    let s = format!("{x}");          // Display for f64: shortest round-trip, never an exponent
    let (int, frac) = s.split_once('.').unwrap_or((&s, ""));
    if frac.len() as u32 > max_places { return Err(CapErr::Precision) }
    let den = 10u64.pow(frac.len() as u32);
    let num: u64 = format!("{int}{frac}").parse().map_err(|_| CapErr::Range)?;
    Ok((num, den))
}
```

Tests owed:
- A proptest that `num as f64 / den as f64 == x` for every `round2` value in `[0,1]`.
- `0.9 → (9, 10)`.
- `0.5 → (5, 10)`. It is not reduced, and that is fine: `10 ∣ 10^6`.
- `NaN`, `-0.1` and `1e-7` are refused.

**Placement of the refusal.** The kernel refuses `weightAboveOne` and `weightPrecision`
itself (R10, a rejection theorem each). Rust should also check at `Model`/`Config` load, so
`tm model` names the file and key. The two checks are one rule, and the kernel's is the
authority.

### 3.3 Why the fallbacks move into the kernel

`Model::p_lounge_on` and `Model::expected_arrival_on` are one-line fallbacks, model then
config. If Rust applied them, the kernel would receive a summary of two readings. AGENTS §5.6
says "the loader never picks between two readings". The fallback is a stated rule, not a
reading conflict, but it costs about 10 kernel lines and removes a host-side decision. So it
goes in the kernel.

### 3.4 The alternative that was not chosen: Rust sends `L` and `H`

Rust could run fork `capacity::lookahead` twice per day with `loc` forced and send two `[u32;6]`
per future day. The kernel would then do only the mixture and EDF.

| | pull forward (chosen) | Rust sends `L`/`H` |
|---|---|---|
| kernel work this tranche | window, cut, predict, limit (§4, steps L3–L6) | mixture and EDF only |
| a second reader | none | **walls are read by Rust's parser**, which is comment-blind where the kernel is not (README gap 45); arrival and curve fallbacks are Rust decisions |
| is it a Rust summary format? | no | yes, against README step 1 type (c)'s rule |
| stage 6 | E7 and `cut_slots` already exist; `dayPlan` reuses `cutSlots` and `predict` | pays E7 and the cut in full |
| agent time | about 2 more weeks now, about 2 fewer in stage 6 | about 2 weeks less in stage 5 |

This is a scope move between stages with a real schedule effect, so it is **OWNER-Q2**. The
design recommends pulling forward. The steps in §8 are ordered so the `L`/`H`-from-Rust
interim can be dropped in at L6 if the owner chooses it.

---

## 4. What is pulled forward from stage 6, and how it is restated

### 4.1 E7: the window. `Goals.lean`'s statement disagrees with the fork and is refuted as written

`Goals.lean` STAGE 6 declares:
- `wallsInside arrival stop walls`: the sum of `w.2 − w.1` over walls with
  `arrival ≤ w.1 ∧ w.2 ≤ stop`, i.e. walls **wholly inside**, **unmerged**.
- `E7a`/`E7b` over `min (arrival + windowMin) windowCap + wallsInside …`.

Fork `window_and_budget` differs in three ways:
1. It **clips** each wall to start at the arrival (`walls_after`).
2. It **merges** overlapping walls.
3. A wall that has started before the current end adds its **whole remaining duration**. Its
   doc comment proves this is the least solution of `e' = e + (min(b, e') − a)`, which is
   **overlap** semantics.

It also clamps the base end: `base_end = … .max(arrival)`.

The two semantics have different least solutions. Take arrival 07:00 (420), an 8 h window
(480), cap 19:00 (1140) and one wall 14:50–15:50 `(890, 950)`:
- **Fork:** base 900, and `890 < 900` so the end is **960**.
- **Wholly-inside semantics:** `m = 900` solves `900 = 900 + wallsInside 420 900 [(890,950)]`,
  because the wall ends after 900 and counts 0. So the least solution is **900**.

A meeting that straddles the end of the window would not extend it. The fork's reading is the
sensible one, and the parity oracle is the fork (AGENTS §8.3 acceptance).

**The restatement**, following stage 5 step 1's pattern (refuted as written, the law that
holds beside it):

```lean
/-- The minutes of `[arrival, stop)` covered by at least one wall: the measure of the
union, counted minute by minute.  A *specification*, evaluated only on small witnesses. -/
def wallOverlap (arrival stop : Nat) (walls : List (Nat × Nat)) : Nat :=
  ((List.range (stop - arrival)).map (· + arrival)).countP
    (fun t => walls.any (fun w => decide (w.1 ≤ t ∧ t < w.2)))

def windowBase (arrival windowMin windowCap : Nat) : Nat :=
  max arrival (min (arrival + windowMin) windowCap)

/-- The fork's walk: clip to the arrival, sort, merge, then extend while a wall starts
before the current end.  Structural on the merged list. -/
def windowEnd (arrival windowMin windowCap : Nat) (walls : List (Nat × Nat)) : Nat

theorem the_window_end_solves_the_equation (a wm wc : Nat) (ws : List (Nat × Nat)) :
    windowEnd a wm wc ws = windowBase a wm wc + wallOverlap a (windowEnd a wm wc ws) ws

theorem the_window_end_is_the_least_solution (a wm wc m : Nat) (ws : List (Nat × Nat))
    (hm : m = windowBase a wm wc + wallOverlap a m ws) :
    windowEnd a wm wc ws ≤ m

/-- E7 as `Goals.lean` wrote it has a smaller solution than the window §8.1 means. -/
theorem the_window_end_is_not_the_least_solution_over_walls_wholly_inside :
    420 + 480 = 900 ∧ 900 = min (420 + 480) 1140 + wallsInside 420 900 [(890, 950)] ∧
    windowEnd 420 480 1140 [(890, 950)] = 960
```

**Proof shape for E7b.** `g(m) = m − wallOverlap a m ws` is non-decreasing, because one more
minute adds at most one covered minute. The walk stops at the first merged wall starting at or
after the end, and the `a ≥ end` test is strict-left. So every `m < windowEnd` has
`g(m) < windowBase`.

Two lemmas carry the proof:
- `wallOverlap_succ`: `wallOverlap a (m+1) ws = wallOverlap a m ws + [m covered]`.
- `wallOverlap_merge`: overlap is invariant under the walk's clip, sort and merge.

**The base clamp.** `Goals.lean`'s `min` without `max arrival` is also refuted, by an arrival
after the cap: 20:00 against 19:00. That is one more witness in the same theorem group.

**Cost:** 400–700 proof lines, 3–5 agent-days. The minute-count specification is chosen
because it cannot be misread (§5.2). If its induction is too slow to write, the fallback is a
merged-interval specification with a `wallOverlap_eq_merged` bridge. Record whichever is
chosen.

### 4.2 The slot cut

The kernel port of `capacity::cut_slots_around(from, end, walls, rests, cfg, blocks_since_break)`,
all in `DT.abs` minutes.

**Pull forward the general function**, rests and since-break included. Future days call it with
`rests = []` and `sinceBreak = 0`. Stage 6's `dayPlan` calls it with the placed routines. That
keeps one definition (§5.3). The rest handling is 5 lines (`restful_end`).

- `freeIntervals from to walls` works over the clipped, merged walls (`normalize_walls`).
- `cutStretch` is the fork's `while t < stop` loop. It runs on **structural fuel
  `stop − start + 1`**: every iteration advances `t` by `block_min ≥ 1`, or by
  `break_min ≥ 1` when breaks are on, or ends the loop. This is `remainingAux`'s pattern.
- `cutStretch_fuel_is_enough` proves that more fuel gives the same answer, so the fuel is
  never the answer.
- `Slot := {start : Nat, len : Nat, kind : Block | Short}`.
- The fork's `min_last = min(min_last_block_min, block_min).max(1)` and
  `breaks_on = break_after_blocks > 0 ∧ break_min > 0` are transcribed exactly.
- R6 stays a comparison.

**Theorems owed now** (stage 6's `plan_*` invariants will lean on them, so they are not wasted):
- `cutSlots_inside_the_window`: every slot satisfies `from ≤ start` and `start + len ≤ end`.
- `cutSlots_avoid_the_walls`: no slot minute is inside a wall.
- `cutSlots_short_block_is_at_least_min_last`.
- `cutSlots_fuel_is_enough`.

**Cost:** 120 definition lines and 300–450 proof lines, 3–5 days.

**Recorded quirk, reproduced and not fixed (a new README gap).** A multi-day wall clips only
at the arrival and has no upper bound (`walls_after`). Take a conference
`[Mon 09:00, Wed 17:00)` and Tuesday arriving at 07:00:
- The walk ends Tuesday's window at Thursday 01:00.
- `cut_slots` then finds Wednesday 17:00 to Thursday 01:00 free and gives it to **Tuesday's**
  capacity.

That evening is counted twice, once for Tuesday and once as Wednesday's own. The kernel copies
this, because parity needs it. It goes to the owner as non-blocking OWNER-Q4.

### 4.3 Future-day `predict`, the home cap and the budget limit

```lean
structure Step where
  fromH : Arith.Pos
  toH   : Option Arith.Pos
  level : Nat

/-- `StepFn::at` over whole minutes since wake (`Int`, may be negative).  `m ≥ 60·k`
is decided by cross-multiplication: `m·den ≥ 60·num`. -/
def stepAt (steps : List Step) (m : Int) : Nat

/-- `Config::prior_energy` then `energy::prior_level`: named curve, else "lounge", else the
least key by `List Char` order (= `BTreeMap`'s byte order for valid UTF-8), else 3. -/
def priorLevel (prior : List (List Char × List Step)) (curve : List Char) (m : Int) : Nat

/-- `Model::energy_at` with `energy::bucket`: `floor(m/60)` clamped to `0..11`, negative to 0. -/
def learnedLevel (energy : List (List Char × List Nat)) (curve : List Char) (m : Int) : Option Nat

inductive Loc | lounge | home

def futureEnergy (c : Curves) (homeMax : Nat) (loc : Loc) (wake start : Nat) : Fin 6 :=
  let m : Int := start - wake       -- as `Int`
  let curve := match loc with | .lounge => "lounge".toList | .home => "home".toList
  let base := min 5 ((learnedLevel c.energy curve m).getD (priorLevel c.prior curve m))
  let capped := match loc with | .lounge => base | .home => min base homeMax
  ⟨min capped 5, by omega⟩

def histOf (slots : List Slot) (energy : Nat → Fin 6) : Hist
def limitHist (budgetMin : Nat) (h : Hist) : Hist        -- level 5 down, `min (h l) left`
```

**Why whole minutes and not `hsw` in hundredths.** The fork's `hours_since_wake` rounds
seconds to 0.01 h before `bucket` and `StepFn::at` compare.
- **Bucket:** `round(m·5/3)/100 ≥ n ⇔ m ≥ 60n` for whole minutes `m`, so buckets agree always.
- **Range keys:** they differ only for a key that is not a whole number of minutes.
  **[checked in proto]** Over every key in hundredths of an hour from 0 to 24 h against every
  whole minute 0–1440, the differing keys are exactly those `c/100` with `c ≡ 2 (mod 5)`, such
  as 0.02 h = 1.2 min.
  - No whole-hour, half-hour or quarter-hour key differs.
  - Every shipped key (`0-1`, `1-5`, `5-8`, `8-10`, `10+`, `0-1`, `1-4`, `4-8`, `8+`) agrees.

The kernel compares exactly. That is parity entry P8.

**The budget limit, proved equal to the fork's sort:**

```lean
/-- The fork's `limit_to_budget`: slots ordered by energy descending (start ascending),
each taking `min len left`, summed per level. -/
def limitSlots (budgetMin : Nat) (slots : List (Nat × Slot)) : Hist   -- via `List.mergeSort`

theorem limitSlots_is_limitHist (budgetMin : Nat) (slots : List (Nat × Slot)) :
    limitSlots budgetMin slots = limitHist budgetMin (histOf' slots)
```

**Proof.**
- Within one level, `Σ min(len_i, left_i)` along the list equals `min(Σ len_i, left)` (an
  induction).
- Across levels, the sort puts every level-5 slot before every level-4 slot. Use
  `List.sorted_mergeSort` and `List.mergeSort_perm` from core.

The start-ascending tie-break is invisible to the sum. Core's `mergeSort` lemma names should
be checked with `#check` in a scratch file before planning around them. If they are missing,
state the theorem over an explicitly bucketed fold, which needs no sort.

**Cost:** 150–250 lines.

**R3 is reopened, as a kernel-owned site.** `Arith.lean`'s table says R3 is "eliminated: the
window enters the kernel as minutes". That only moves the fork's `(window_hours × 60).round()`
into Rust. With `windowHours` sent as a pair, the kernel owns it:
`windowMin = halfUpQ (scale 60 windowHours)`.
- For non-negative inputs this is exactly `f64::round` (half away from zero).
- `budget` uses the exact `wh` pair, so R2's floor sees `439.8`, not `440`, as the fork does.

Update the R3 row in `Arith.lean`'s header in the same step. This is a table correction, not
an owner decision.

---

## 5. The lookahead and the EDF pass over units

### 5.1 The lookahead

```lean
structure LookInput where
  today      : Nat
  days       : Nat
  day0       : Hist                    -- interim argument (§5.3)
  weight     : Weekday → Weight        -- after the model→config fallback
  arrival    : Weekday → Clock
  wakeClock  : Clock                   -- today's; every future day reuses it (fork behaviour)
  curves     : Curves
  dayCfg     : DayCfg                  -- block/break/min_last/window/cap/budget, all decoded
  walls      : Nat → List (Nat × Nat)  -- `wallsOn p`, indexed once (§6.4)

/-- One future day at one location: window, cut, energise, limit. -/
def pureDay (I : LookInput) (loc : Loc) (d : Nat) : Hist

def lookahead (I : LookInput) : List DayCap :=
  (List.range I.days).map fun i =>
    let d := I.today + i
    if i = 0 then ofHist d I.day0
    else ⟨d, mix (I.weight (weekdayOf d)) (pureDay I .lounge d) (pureDay I .home d)⟩

theorem lookahead_keeps_the_days (I : LookInput) : (lookahead I).length = I.days

/-- The parity anchor: with every weight certain, the kernel is the pure location. -/
theorem lookahead_at_a_certain_weight_is_the_pure_location (I : LookInput) (i : Nat)
    (hi : 0 < i) (hlt : i < I.days) (l : Fin 6) (loc : Loc)
    (hw : I.weight (weekdayOf (I.today + i)) = (match loc with | .lounge => ⟨capDen, _⟩ | .home => ⟨0, _⟩)) :
    ((lookahead I)[i]?).map (·.unitsAt l) = some (capDen * pureDay I loc (I.today + i) l)

theorem lookahead_between_the_locations (I : LookInput) (i : Nat) (c : DayCap) (l : Fin 6)
    (h : (lookahead I)[i]? = some c) (hi : 0 < i) :
    capDen * min (pureDay I .lounge c.day l) (pureDay I .home c.day l) ≤ c.unitsAt l ∧
    c.unitsAt l ≤ capDen * max (pureDay I .lounge c.day l) (pureDay I .home c.day l)
```

**Weekday of a day.** `Cal.weekdayOf` exists. `Weekday` is whatever `Cal` names; map it to the
wire's `"Mon"…"Sun"` keys with one table and its round-trip theorem.

### 5.2 EDF without division: the `Goals.lean` restatement

`Goals.lean` STAGE 5's provisional `DayCapacity {day, minutesAt : Fin 6 → Nat}` is **replaced**
by `DayCap {day, unitsAt}`. README step 1 owes this, as type (a).

Deadlines stay in whole minutes. R1's `needMin` ceiling happens upstream, in the priority
tranche.

```lean
structure Deadline where
  need : Nat      -- minutes (after R1)
  ci   : Fin 6
  due  : Nat

def atLeast (c : DayCap) (ci : Fin 6) : Nat := ((List.finRange 6).filter (ci ≤ ·)).foldl (· + c.unitsAt ·) 0
def availUntil (cs : List DayCap) (due : Nat) (ci : Fin 6) : Nat
/-- `capacity::reserve` over `cs[..upto due]`: earliest day first, highest level first. -/
def reserve (cs : List DayCap) (due : Nat) (units : Nat) (ci : Fin 6) : List DayCap × Nat
/-- `priority::compute`'s EDF loop: due ascending (stable), take `min (need·capDen) avail`. -/
def edf (cs : List DayCap) (ds : List Deadline) : List DayCap
```

**The three goals carry over with the same quantifiers**, `minutesAt ↦ unitsAt`. This is a
retyping, not a weakening: `unitsAt / capDen` is the exact rational minute count D10 names, and
`≤`/`=` on numerators over one shared denominator is `≤`/`=` on the rationals
(`Arith.Q.le` on `⟨x, capDen⟩`, `⟨y, capDen⟩` unfolds to `x·capDen ≤ y·capDen`). State this in
the README next to the goal edit, and delete the provisional definitions:

```lean
theorem edf_keeps_the_days (cs : List DayCap) (ds : List Deadline) :
    (edf cs ds).length = cs.length
theorem edf_only_spends_capacity (cs : List DayCap) (ds : List Deadline) (n : Nat)
    (c c' : DayCap) (l : Fin 6) (h : cs[n]? = some c) (h' : (edf cs ds)[n]? = some c') :
    c'.unitsAt l ≤ c.unitsAt l
theorem edf_reserves_only_before_the_deadline (cs : List DayCap) (ds : List Deadline) (n : Nat)
    (c c' : DayCap) (l : Fin 6) (h : cs[n]? = some c) (h' : (edf cs ds)[n]? = some c')
    (hafter : ∀ d ∈ ds, d.due < c.day) :
    c'.unitsAt l = c.unitsAt l
```

**New goals, stated with this tranche:**

```lean
/-- `reserve` takes exactly what was asked, or everything that was there. -/
theorem reserve_takes_the_need_or_the_pool (cs : List DayCap) (due units : Nat) (ci : Fin 6) :
    (reserve cs due units ci).2 = min units (availUntil cs due ci)

/-- `reserve` keeps the pool's books: what was taken left the pool. -/
theorem reserve_conserves (cs : List DayCap) (due units : Nat) (ci : Fin 6) :
    availUntil (reserve cs due units ci).1 due ci + (reserve cs due units ci).2 = availUntil cs due ci

/-- §7.1's `u`, anchored: the units test *is* the rational `need / (avail / capDen)`. -/
theorem util_over_units_is_need_over_rational_minutes (need a : Nat) :
    Arith.util (need * capDen) a = Arith.Q.div (Arith.ofNat need) ⟨a, capDen⟩ ∨
    Arith.Q.equiv (Arith.util (need * capDen) a) (Arith.Q.div (Arith.ofNat need) ⟨a, capDen⟩) = true

/-- D5 two-run law: the choice of `capDen` is not observable in any bin.  Scaling every
unit and the per-minute factor by `k > 0` scales the pass and leaves every bin unchanged. -/
theorem edf_commutes_with_scaling (k : Nat) (hk : 0 < k) (cs : List DayCap) (ds : List Deadline) :
    edfAt (k * capDen) (cs.map (scaleDay k)) ds = (edfAt capDen cs ds).map (scaleDay k)
theorem binOf_is_scale_invariant (bins : List Arith.Q) (k n a : Nat) (hk : 0 < k) :
    Arith.binOf bins (k * n) (k * a) = Arith.binOf bins n a
```

**Notes on these goals.**
- `edfAt D` is `edf` with the per-minute factor as a parameter. `edf := edfAt capDen`, so the
  scaling law is a real two-run theorem, not a tautology about a constant.
  **[checked in proto: 3,000 random passes]**
- `binOf_is_scale_invariant` follows from `Arith.Q.le_scale_left`/`le_congr` through
  `utilGe_eq_le`. It is the law that makes the fallback denominator (lcm, or `2^1074` under
  OWNER-Q1's other answer) a drop-in change.
- Gap 25 (P2) is unchanged. `utilGe (0·capDen) 0 e = utilGe 0 0 e` is HOT.
- `isImpossible (need·capDen) avail` means `avail < need·capDen`, which means the rational
  availability is below the need. Exact.

**Shortfall and allocation are pairs.** The fork's `shortfall_min = need − avail : u32` becomes
`(need·capDen − avail) / capDen`. The kernel emits `{num, den}`, as D3's report does. How the
host renders it is §6.2 and OWNER-Q3.

### 5.3 Day 0: interim argument, then derived

Day 0 is `ofHist today day0`, **pure, no mixture** (the location is known). The fork builds it
in `Ctx::today_slots` from:
- the stored window or the window formula;
- `now`;
- today's walls;
- **the replay's `energy_on(today)` posterior, `slept_min` and `blocks_done`**;
- `allow_home`.

Under D9 the replay inputs are the kernel's own. So:

- **Interim (L1–L9):** `day0 : Hist` is a plain argument. Until D9's replay is wired, the host
  fills it from fork `Ctx::today_slots` → `DayCapacity::from_slots`. Record it as a named gap:
  "day 0 of the lookahead is the host's histogram".
  - This is the one place the tranche takes a host-computed summary.
  - It is bounded: one `[u32; 6]`, not a format.
  - It must be gone before D9's cut-over removes Rust's `replay`.
- **Final (L10, after D9's replay lands):** `day0 := histOf (cutSlots …today…) (energyToday …)`,
  reusing `cutSlots` and `futureEnergy`'s curve lookup, plus three things:
  - the posterior correction, which **R5 `Arith.energyAfter` already is**, with `Arith.ramp`
    over minutes from `posterior_full_hours`/`posterior_zero_hours` pairs;
  - the sleep shift `round(model.sleep_shift)`, a **new rounding site R8** (half away from zero
    on a signed value; a hand-edited negative shift is legal), with
    `under_slept ⇔ slept_min · den < 60 · num`;
  - the `allow_home` flag.

  Parity: `Ctx::today_slots` exactly, since day 0 is not P1.

---

## 6. Wire, host and latency

### 6.1 Request section (Nat numerals only)

```json
"capacity": {
  "pLounge":  {"model": {"Mon": {"num": 9, "den": 10}}, "config": {"Mon": {"num": 9, "den": 10}, "…": "all 7"}},
  "arrival":  {"model": {"Mon": "07:10"}, "config": {"Mon": "07:00", "…": "all 7"}},
  "energy":   {"lounge": [4,5,5,5,5,4,4,4,3,3,2,2], "home": [3,4,4,4,3,3,3,2,2,2,2,2]},
  "prior":    {"lounge": [{"from": {"num":0,"den":1}, "to": {"num":1,"den":1}, "level": 4}], "home": []},
  "homeMaxCi": 3,
  "day": {"breakMin": 20, "breakAfterBlocks": 2, "minLastBlockMin": 30,
          "windowHours": {"num": 8, "den": 1}, "windowCap": "19:00", "budgetRatio": {"num": 75, "den": 100}},
  "day0": [0, 0, 60, 120, 60, 0]
}
```

- `blockMin`, `now` and the state's `wake` are already on the wire (stage 3–4) and are not
  repeated.
- Each array is at most 12 elements and each map at most 7 keys, so gap 44 is irrelevant.
- The config pairs share step 1's route and `decimal_pair`.
- **Coordinate with the D9 and priority designs:** if they add one `"config"`/`"model"`
  section, these keys live there, not in a `capacity` island. The key names here are
  placeholders for that merge.

### 6.2 Response and display

- **Emit the first `min(days, 7)` days only.**
  `"lookahead": {"den": 1000000, "days": [{"day": "2026-09-15", "unitsAt": [..6..]}, …]}`.
  - Every host consumer of whole-day capacities reads at most a week: `planning::week` (7),
    `planner::week_from_run` (`min(7)`), the TUI queue (`upto(week_end)`).
  - The EDF pass reads the long horizon *inside* the kernel, so no response array is ever
    anywhere near gap 44's band.
- **Priorities** carry `avail`, `allocation` and `shortfall` as `{num, den}` pairs.
- **Display is the host's.** `week_grid` shows `floor(units / den)` minutes. This matches
  `Arith.lean`'s rule that display quotients are the host's to divide. It is not a
  decision-path rounding.
- **`--json` compatibility** of `WeekOut.days[].minutes_at_level: [u32;6]`, `Prio.avail_min`
  and similar is **OWNER-Q3**. The recommendation: keep the integer fields as documented floors
  and add `*_exact: {num, den}` beside them.

### 6.3 The host's second reserve

`tui/queue.rs` recomputes "fits this week" with its own `capacity::reserve` over the
capacities. After wiring, that runs in `u64` units, which is exact because `capDen = 10^6`
keeps a week well under `2^64`. It remains a **second implementation of `reserve`**, an AGENTS
§5.3 hazard.

Record it as a gap with the TUI (stage 6's surface). The proper fix is for the kernel to emit
the per-row fit, reusing `reserve`.

### 6.4 Latency

The lookahead reads **no log**; under D9 only the wake and day 0 come from the replay. Its
cost is `days × (walls of the day + ~12 slots × 2 locations)`.

- Fork `Ctx::walls_by_date` rescans the tree per date: O(days × items).
- The kernel should **index once**: collect every unsettled interval item's
  `(start − buffer, end)` in one pass, then filter that short list per day.
- `days` is set by the furthest due date. A candidate due three years out means 1,095
  simulated days, and the fork pays the same.

**Owed measurement, before quoting any number (AGENTS §5.11):**
- `cli_latency.rs`'s history tree plus one `due:` three years out, through the shipped binary.
- `LATER_VERB` (1 s) must hold.

**If the measurement says so, an exact acceleration exists.** Wall-free future days depend only
on the weekday. `pureDay` can be memoised per weekday, with a `@[csimp]` twin proved equal,
which is `parentRef_eq_parentRefFast`'s pattern. No bound or cap on `days` is proposed: capping
it would change `u` for far-dated items, and that would be an owner question nobody needs yet.

---

## 7. Parity: the exception entries and the harness

### 7.1 The threshold twin: how P1 becomes checkable

A raw comparison of the kernel's mixture with fork `lookahead` differs on every future day with
`0 < p < 1` and `L ≠ H`. That tells nothing about whether window, cut, predict and limit were
ported right. So the harness runs **two kernel lookaheads** per fixture:

1. **Twin.** Replace every decoded weight by `if 2·w ≥ capDen then capDen else 0`, mirroring
   `p_lounge_on(wd) ≥ 0.5`. Require
   `twin.unitsAt = capDen × fork_lookahead.minutes_at_level`, **day by day and level by level,
   with no exceptions** beyond P7–P9. Priorities computed on the twin must equal fork
   `priority::compute`, modulo P2 and P3.
   - By `lookahead_at_a_certain_weight_is_the_pure_location`, the twin *is* the kernel's pure
     location, so this checks the whole pulled-forward pipeline against the oracle.
   - **Caveat to check before relying on it.** A `round2` weight decoded as a decimal compares
     `2w ≥ capDen` exactly, while the fork compares the double `≥ 0.5`. They agree, because
     0.5 is exactly representable (inventory §6.4).
2. **Real run.** Require `lookahead_between_the_locations` numerically against the twin's own
   `pureDay` histograms, which the kernel emits under a harness-only flag or a test export. Also
   require that day 0 is identical to the twin's.

### 7.2 Entries for README "The stage-5 parity exception list", recorded before the harness runs

| # | site | the kernel | the fork point | authority |
|---|---|---|---|---|
| P1 (refined) | future-day capacity, **and everything downstream of it**: each dated candidate's `avail`, `allocation`, `shortfall`, `u`, bin, `p`, HOT/IMPOSSIBLE class, and `floor_pass`'s availability | `w·L + (capDen−w)·H` in units, mixed **after** each location's budget limit; downstream reads units | `capacity::lookahead`: `L` iff `p ≥ 0.5`; `u32` minutes; `f64` `u` | D10. Checked through the twin (§7.1); the real run is checked by bounds only |
| P7 | a window or wall spanning a DST transition in `cfg.tz`, or starting in a spring-forward gap | civil minutes (`DT.abs`): 02:00–03:00 is 60 min on every day | instants via `capacity::local_dt`: 0 or 120 real minutes; a gap time moves to the first valid instant | the kernel has no zone (README gap 10). Revisit if D9's zone design lands a UTC-offset table the lookahead can read |
| P8 | a prior-curve range key that is not a whole number of minutes (e.g. `0.02` h) | exact comparison of whole minutes since wake against `num/den` hours | `hours_since_wake` rounds to 0.01 h before `StepFn::at` | §4.3; no shipped key is affected [checked in proto] |
| P9 | a weight or config decimal outside the exact domain: `p ∉ [0,1]`, `NaN`, more than 6 decimals; a negative range key; a level ≥ 256 | refused by name (`weightAboveOne`, `weightPrecision`, `badStep`, `badLevel`) | accepted: `p = 1.2` gives lounge, `NaN` gives home, `-0.1` gives home | R10; OWNER-Q1 covers the precision bound |
| P10 | `window_hours · 60` not whole (e.g. `7.33` h) | `halfUpQ` on the exact pair for the window; exact pair for the budget | `f64::round` for the window; `f64` floor for the budget | R3 reopened (§4.3). Differs only where the double product lands on the other side of a `.5`, or of an integer for the budget; record it even if the corpus never hits it |

- **P2, P3 and P6 stand** as README step 1 lists them.
- **P11 is not an exception, it is a gap:** the multi-day wall quirk (§4.2) is reproduced
  exactly.

---

## 8. Step plan

Each step ends the way AGENTS §6 requires:
- **Tests:** check.sh 7/7, cargo test acceptance.
- **Records:** a README block, the gap list, `Check.lean` appended under the stage-5 banner,
  and `Negative.lean` appended at the end.
- **Imports:** `TmKernel.lean` gains `import TmKernel.Capacity` **once, at L1, after
  `TmKernel.Tree`**. Count the imports at the end, per AGENTS §8.3.
- **Proof work:** under D5 every restated goal is proved in the step that states it or the step
  is not done. Every `decide` witness is probed first under an 8 GB cap with `timeout 120`.

**Dependencies.**
- L1–L8 depend on nothing unbuilt.
- L9 needs the priority tranche's candidates and `lookahead_days`.
- L10 needs D9's replay (today's wake, energy observations, `slept_min`, `blocks_done`) and a
  `now` with time of day.
- L3 and L4 can run in parallel worktrees with L2, with care over `Check.lean` (AGENTS §6.3:
  serialise the `Check.lean` edits).

| step | builds | theorems | Negative cheats | est. agent-days |
|---|---|---|---|---|
| **L1** Capacity types and the mixture | `Capacity.lean`: `capDen`, `Weight`, `mkWeight?`, `Hist`, `DayCap`, `mix`, `ofHist`; `Goals.lean`: delete the provisional `DayCapacity`, `Deadline` and `edf`, add the restated signatures (§5.2) as `sorry` goals with a README note "retyped, not weakened" | `mix_between_the_locations`, `mix_at_zero_is_home`, `mix_at_one_is_lounge`, `mix_denotes_the_weighted_sum`, `mix_atLeast_between_the_locations`, `mkWeight?` rejection theorems (`_zero_den`, `_above_one`, `_precision`) and acceptance `mkWeight?_round2` (`9/10 ↦ 900000`) | swap `w` and `capDen − w`; accept `n > d` | 1–2 |
| **L2** EDF over units | `atLeast`, `availUntil`, `reserve`, `edfAt`, `edf` (due-stable order as `priority::compute`: due, then `own_order`, then input index; the order key is an argument) | the three restated EDF goals; `reserve_takes_the_need_or_the_pool`; `reserve_conserves`; `util_over_units_is_need_over_rational_minutes`; `edf_commutes_with_scaling`; `binOf_is_scale_invariant`; the fork's unit test `reserve_takes_the_best_levels_earliest` ×`capDen` as a `decide` witness | reserve lowest level first; reserve past `due` | 3–4 |
| **L3** E7, the window | `wallOverlap` (spec), `windowBase`, `windowEnd` (walk); `Goals.lean` E7a/E7b moved from STAGE 6 to STAGE 5 and restated | E7a, E7b, `the_window_end_is_not_the_least_solution_over_walls_wholly_inside`, the base-clamp refutation; the fork tests `budget_of_an_eight_hour_window` (15:00), `walls_extend_the_window` (16:00) and `the_cap_bounds_the_window` (19:00) as witnesses | wholly-inside walls; no merge | 3–5 |
| **L4** the cut | `freeIntervals`, `cutStretch` (fuel), `cutSlots` (general: rests, since-break) | `cutSlots_fuel_is_enough`, `_inside_the_window`, `_avoid_the_walls`, `_short_block_is_at_least_min_last`; the capacity.rs doc comment's §4.3 cut (07:00, 08:00, break 09:00, 09:20, 10:20, break 11:20, 11:40, wall, 13:50, break 14:50, 15:10–16:00 short) as a witness | end a stretch on a break; drop the short block | 3–5 |
| **L5** energy and limit | `Step`, `stepAt`, `priorLevel`, `learnedLevel`, `futureEnergy`, `histOf`, `limitHist`, `limitSlots` | `limitSlots_is_limitHist`; `futureEnergy_home_is_capped`; `stepAt` agreement with `prior_energy_lookup`'s 12 fork assertions (`decide`); `predict_falls_back_to_the_prior`'s 4 | skip the home cap; bucket without the clamp | 2–4 |
| **L6** the lookahead | `wallsOn` (indexed once), `pureDay`, `lookahead`, `LookInput` | `lookahead_keeps_the_days`, `lookahead_at_a_certain_weight_is_the_pure_location`, `lookahead_between_the_locations`, `mixing_before_the_budget_is_not_the_expectation`; **on a loaded plan** (`Boundary.lean`): a calendar wall 12:50–13:50 on a Wednesday in a tree gives Wednesday's window end 16:00 and a mixed capacity whose twin equals the fork value written out by hand | mix before limit | 2–3 |
| **L7** boundary | the `capacity` request section decoder; model→config fallbacks; the response's first 7 days; priority pairs | one rejection theorem per named refusal (R10); `the_capacity_section_reads_the_corpus_model` (a small, hand-shrunk `model.json` as a `List Char` literal, per AGENTS §5.10a) | accept `p = 1.2`; accept a zero denominator | 3–4 |
| **L8** parity | extend the fork-point oracle scaffolding (AGENTS §7.3) with the threshold twin (§7.1); fixtures: `kernel/corpus/plan-*` configs × `kernel/corpus/model.json` × `design`'s synthetic trees; a generated set of wall layouts, including multi-day and DST-crossing | — (a measurement); record P1 (refined), P7–P10 **before** the run | — | 2–3 |
| **L9** wiring (**jointly with the priority tranche**) | `Ctx::priorities`, `planning::week` and planner step 4 read the kernel lookahead and priorities; `decimal_pair`; host display floors; queue reserve in `u64` units (gap); `day0` from `Ctx::today_slots` (gap) | Rust: `decimal_pair` proptest; `cli_plan.rs`/`cli_json_matrix.rs` snapshots updated per OWNER-Q3; **latency probe** with a 3-year due (§6.4) | — | 3–5 |
| **L10** day 0 in the kernel (**after D9's replay is wired**) | today's window (state or formula), cut from `now`, posterior via `Arith.energyAfter`/`ramp`, R8 sleep shift, `allow_home`; the `day0` argument deleted | parity against `Ctx::today_slots` (not P1); R8 `_withinOne`/`_mono` in `Arith`'s vocabulary | apply the posterior after the cap | 4–6 |

**Recommended merge points:**
- L1+L2 together: the EDF goals are live and restated.
- L3–L5: stage-6 pieces pulled forward. Update AGENTS §8.3/§8.4 to move E7 into stage 5's goal
  list.
- L6+L7+L8.
- L9 with priority.
- L10 with or after D9's cut-over.

---

## 9. Cost, honestly

| part | Lean definition lines | Lean proof lines (ESTIMATE, at stage 4's 4.8 : 1) | Rust lines | agent-days |
|---|---:|---:|---:|---:|
| L1–L2 mixture and EDF | 150–200 | 700–1,000 | — | 4–6 |
| L3–L5 pulled-forward window, cut, energy, limit | 300–400 | 1,000–1,700 | — | 8–14 |
| L6–L7 lookahead and boundary | 250–350 | 600–1,000 | — | 5–7 |
| L8 parity | — | — | 200–300 (harness) | 2–3 |
| L9 wiring | 40–80 (response) | 100–200 | 300–500 | 3–5 |
| L10 day 0 | 150–200 | 400–700 | −150 (`today_slots` retired) | 4–6 |
| **total** | **~900–1,200** | **~2,800–4,600** | **~350–650 net** | **26–41 ≈ 5–8 weeks** |

**Against the plan.**
- Plan §5 priced all of stage 5 at 3–4 weeks. This tranche alone is 5–8.
- About 2 of those weeks (L3–L5) are stage 6's §8.1/§8.2 pieces moved earlier, and stage 6's
  estimate should drop by the same amount.
- About 1 week (L10) is day 0, which exists only because D9 takes the replay away from Rust.
- The part that is new because of D10 itself (L1, L2's exactness goals, the twin and P1) is
  about 1.5 weeks.

**Risks, in order:**
1. E7b's proof over the minute-count specification. Fallback: a merged-interval specification
   with a bridge lemma; record which.
2. `limitSlots_is_limitHist` depends on core `mergeSort` lemma names. Fallback: a bucketed-fold
   statement.
3. The latency of a long horizon (§6.4). Fallback: the per-weekday memo with a `@[csimp]` twin.
4. `decide` memory on loaded-plan witnesses. The step-1 probes of 1.5–10 s at 0.9–2.4 GB say
   to keep one witness per theorem.

---

## 10. Owner questions (new; none decided here)

**OWNER-Q1: which rational is the lounge weight, and may unrepresentable weights be refused?**
The inventory's §6.4 FLAG. `model.json` says `0.9`, and Rust computes with the nearest double,
`0.90000000000000002220…`. D10 fixes the formula, not which of the two `p` it is.

Recommended: the **decimal text**, i.e. the shortest round-trip decimal Rust prints, with at
most 6 decimal places, and a named refusal beyond that. Its advantages:
- It is what the fit meant (`round2`).
- It is what a person edits.
- It allows the fixed `capDen = 10^6`, so host units fit `u64` and the queue's reserve stays
  exact.

The alternative is the exact double: `capDen = 2^1074`, ~330-digit units, and the queue reserve
must move into the kernel first. A second alternative keeps decimals but has no precision
bound: a per-request lcm denominator, no stated width, and bignum units on the host.

What differs: nothing for any `round2` value's decisions except on exact ties in the EDF, and
the refusal of hand edits with more than 6 decimals, or `p ∉ [0,1]` (P9).

**OWNER-Q2: pull §8.1's window, §8.2's slot cut and the future-day energy forward into stage 5,
or have Rust send per-location histograms for now?**
- Recommended: pull forward (§3.4). It keeps one reader of walls and curves (§5.3) and pays
  stage-6 work early (5–8 weeks for this tranche).
- The interim saves about 2 weeks in stage 5 at the price of a Rust summary format and Rust
  reading walls through a parser that disagrees with the kernel's about comments (gap 45).
- Either way D10's mixture and the EDF pass are the kernel's.

**OWNER-Q3: the `--json` contract for capacities that are no longer whole minutes.**
Affected fields:
- `tm plan --week --json` `days[].minutes_at_level: [u32;6]` and `total`
- `Prio.avail_min`, `allocation_min` and `shortfall_min`, in priorities output and the TUI

Recommended: keep the integer fields as documented floors of the exact value (display only) and
add `…_exact: {num, den}` beside them. The alternatives are a breaking schema change to pairs,
or integers only with the exact value hidden.

**OWNER-Q4 (not blocking): a multi-day wall gives a day capacity on later days.**
Fork `window_and_budget` clips walls only at the arrival (`walls_after`). A wall from Monday
09:00 to Wednesday 17:00 extends Tuesday's window past Wednesday evening, and Tuesday then
counts Wednesday 17:00 to Thursday 01:00 as its own free time, which Wednesday also counts. The
kernel reproduces it for parity (§4.2). Should a later step bound the window to the day, as a
recorded behaviour change and a new parity entry?

Not owner questions, and taken here with reasons:
- mix after the budget (D10's "expected", §2.4)
- restating E7 to overlap semantics (the oracle's reading, refuted-as-written pattern, §4.1)
- R3 reopened as kernel half-up (§4.3)
- the kernel owning the model→config fallbacks (§3.3)
- emitting 7 days (§6.2)
