import TmKernel.PlanFold
/-!
# Three stability laws of the planner's day (stage 6, run W-40, track P)

**Theorems only.**  Every definition this module reasons about is `Planner.lean`'s or `Lookahead.lean`'s,
and it adds none, so nothing here is compiled into the archive and nothing here can be a second reading of
a fact the planner reads once (AGENTS §5.3).  It imports `PlanFold`, not `PlanCheck`: the checker battery
stays a module no library code imports (check 12's `CLASS proof PlanCheck`), and the one law here that
reads it — the wind-down law's union with W-39's form — is stated in `PlannerWit`, which may.

1. **The day does not change at the instant a break ends** (the owner's D77, README gaps 3480, 3666, 3784;
   parity **P67**).  Since W-40 a RUNNING break resets the cut's break counter as the same break does once
   `tm break` has logged it (`Planner.PlanReq.sinceBreak` reads its start as a break), and it is no longer a
   rest of the cut (`Planner.PlanReq.restsToday`).  `the_running_break_and_its_logged_twin_count_alike`
   says the counter reads the two alike, at any length and wherever the break ends;
   `the_cut_does_not_change_when_an_overrun_break_is_logged` lifts it to §8.2 step 3's cut, and §4's
   `the_day_from_now_does_not_change_when_an_overrun_break_is_logged` to every row of the day from `now`,
   on the class of states where nothing else differs and a block the break paused stays paused.

2. **§8.3's wind-down law, without E8's seam** (README gaps 2326, 3544, 3713 and 3782).
   `the_window_ends_by_the_night` is README gap 2326's bound for the kernel's planner window — a planned
   window since the W-39 repair clipped its walls (`Look.wallsClippedOn`), a stored one since W-40 ended it
   24 hours after its end clock as the fork does (`Planner.PlanReq.window`, README gap 3782) — on every
   request whose `[day]` the decoder accepts, whose arrival is not past the day's end and whose stored end
   clock reads inside the day; and
   `no_block_row_starts_at_or_after_a_wind_down_row_when_the_window_ends_by_the_night` says that wherever
   the window ends by the night's end, no Block row of the day starts at or after a WindDown row at all —
   so `Goals.plan_places_no_demanding_block_after_wind_down` holds there whatever the wire calls the item's
   `ci`.  What it does NOT reach is said in `Goals.lean` and README gap 3780.

3. **L25 over a record that EXTENDS the earlier one** (the owner's D77, README gap 3714).
   `PlanFold.plan_is_stable_across_a_replan` pinned today's record (`r'.todayRecord = r.todayRecord`), so a
   replan after any logged verb was outside it.  `plan_is_stable_across_a_replan_after_a_logged_verb`
   takes a later record that holds every segment and every closed id of the earlier one — what a `stop` or a
   `done` appended after `now` leaves on the replays `PlannerWit`'s W-40 block computes (that every verb but
   `undo` does is not proved of the replay, README gap 3781) — and concludes that every row of the
   earlier day that ended before `now` and is not open is a row of the later day **up to its `done` flag,
   which can only rise**: fork `past_segments` marks a replayed Block done when the log closed the item
   today, so `tm done` after `now` raises it on an earlier block of the same item, and the exact law is
   refuted at a computed pair (`PlannerWit`'s W-40 block).  The W-39 form is the corollary
   `plan_is_stable_across_a_replan_of_the_same_record`.
-/

namespace Tm
namespace PlanStable

open Planner

/-! ############################################################################
## 1. The running break and its logged twin (D77, README gaps 3480 and 3666)
############################################################################ -/

/-- **Walls that end by `lo` are clipped away** — `Look.clipTo` drops them, wherever they sit in the list. -/
theorem clipTo_drops_walls_ending_by (lo hi : Nat) (A L B : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ lo) : Look.clipTo lo hi (A ++ L ++ B) = Look.clipTo lo hi (A ++ B) := by
  unfold Look.clipTo
  simp only [List.map_append, List.filter_append]
  have hnil : (L.map fun w => (max w.1 lo, min w.2 hi)).filter (fun w => decide (w.1 < w.2)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    have := hL w hw
    simp only [decide_eq_true_eq]
    omega
  rw [hnil, List.append_nil]

/-- **So the free stretches of `[lo, hi)` do not see them** — `Look.freeIntervals` reads its walls only
through the clip. -/
theorem freeIntervals_drop_walls_ending_by (lo hi : Nat) (A L B : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ lo) :
    Look.freeIntervals lo hi (A ++ L ++ B) = Look.freeIntervals lo hi (A ++ B) := by
  unfold Look.freeIntervals Look.freeChain
  rw [clipTo_drops_walls_ending_by lo hi A L B hL]

/-- **Nor does the overlap test of a span that starts after them** (step 2's anchored placement). -/
theorem overlapsAny_drops_walls_ending_by (lo hi : Nat) (A L : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ lo) : overlapsAny lo hi (A ++ L) = overlapsAny lo hi A := by
  unfold overlapsAny
  rw [List.any_append]
  have : L.any (fun w => decide (lo < w.2 ∧ w.1 < hi)) = false := by
    rw [List.any_eq_false]
    intro w hw
    have := hL w hw
    simp only [decide_eq_true_eq]
    omega
  rw [this, Bool.or_false]

/-- **Nor does the earliest-free search from `lo`** (step 2's mandatory placement). -/
theorem earliestFree_drops_walls_ending_by (lo hi d : Nat) (A L : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ lo) : earliestFree lo hi d (A ++ L) = earliestFree lo hi d A := by
  unfold earliestFree
  have := freeIntervals_drop_walls_ending_by lo hi A L [] hL
  simp only [List.append_nil] at this
  rw [this]

/-- **Nor does §8.2 step 3's cut over `[lo, hi)`** — its walls reach it only through the free stretches,
and its rests are not touched. -/
theorem cutSlots_drop_walls_ending_by (c : Look.CutCfg) (lo hi : Nat) (S L R : List (Nat × Nat)) (k : Nat)
    (hL : hi ≤ lo ∨ ∀ w ∈ L, w.2 ≤ lo) :
    Look.cutSlots c lo hi (S ++ L) R k = Look.cutSlots c lo hi S R k := by
  unfold Look.cutSlots
  split
  · rfl
  · rcases hL with hhl | hL
    · have h1 : Look.freeIntervals lo hi (S ++ L ++ R) = [] := by unfold Look.freeIntervals; rw [if_pos hhl]
      have h2 : Look.freeIntervals lo hi (S ++ R) = [] := by unfold Look.freeIntervals; rw [if_pos hhl]
      simp only [h1, h2]
    · rw [freeIntervals_drop_walls_ending_by lo hi S L R hL]

/-- **The cut's break counter, as a normal form**: today's `start`s after the latest of today's break instants — the
`break`s the record holds and, since W-40, the running break's start (`Planner.PlanReq.sinceBreak`) — counted; none
when today has no record. -/
theorem sinceBreak_is_the_starts_after_the_last_break (r : PlanReq) :
    r.sinceBreak = (((r.todayRecord.map (·.starts)).getD []).filter (fun s =>
      match (if (((r.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) ++
              (r.state.brk.bind (·.started)).toList.map (·.sec)).isEmpty then none
            else some ((((r.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) ++
              (r.state.brk.bind (·.started)).toList.map (·.sec)).foldl max 0)) with
      | none => true
      | some t => decide (t < s.t.1.sec))).length := by
  unfold PlanReq.sinceBreak
  cases r.todayRecord with
  | none => rfl
  | some d => rfl

/-- **D77: the running break and its logged twin count alike** (README gaps 3480 and 3666; P67).  A request
whose state holds a break running since `t`, and a request whose state holds none and whose record holds that
break among the ones the log closed today — at the break's start, as `tm break`'s line stamps it — with the
same starts: the cut's break counter is the same in both, **whatever the break's length and wherever it
ends**.  Until W-40 the two disagreed exactly when the break was shorter than `break_min` or ended under a
wall (the running one was a rest, `Look.restfulEnd`); `PlannerWit`'s W-40 block computes such a day. -/
theorem the_running_break_and_its_logged_twin_count_alike (r r' : PlanReq) (t : Nat)
    (hrun : (r.state.brk.bind (·.started)).map (·.sec) = some t)
    (hrun' : r'.state.brk.bind (·.started) = none)
    (hstarts : (r'.todayRecord.map (·.starts)).getD [] = (r.todayRecord.map (·.starts)).getD [])
    (hlogged : ((r'.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) =
      ((r.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) ++ [t]) :
    r'.sinceBreak = r.sinceBreak := by
  have hr : (r.state.brk.bind (·.started)).toList.map (·.sec) = [t] := by
    cases h : r.state.brk.bind (·.started) with
    | none => rw [h] at hrun; exact absurd hrun (by simp)
    | some x => rw [h] at hrun; simp only [Option.map_some, Option.some.injEq] at hrun; simp [hrun]
  have hr' : (r'.state.brk.bind (·.started)).toList.map (·.sec) = [] := by rw [hrun']; rfl
  rw [sinceBreak_is_the_starts_after_the_last_break r', sinceBreak_is_the_starts_after_the_last_break r,
    hr, hr', hlogged, hstarts, List.append_nil]

/-- **An overrun running break blocks nothing from `now`**: its row ends at `now`. -/
theorem an_overrun_break_ends_at_now (r : PlanReq) (b : BreakState) (t : Cal.Instant)
    (hbrk : r.state.brk = some b) (hst : b.started = some t)
    (hover : t.sec + 60 * b.plannedMin ≤ r.now.sec) :
    ∀ w ∈ (breakRows r).map (fun s => (s.start, s.stop)), w.2 ≤ r.now.sec := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hw
  unfold breakRows at hs
  rw [hbrk] at hs
  simp only [Option.bind_some, hst, Option.map_some] at hs
  split at hs
  · cases hs
  · simp only [List.mem_singleton] at hs
    subst hs
    show max (min (t.sec + 60 * b.plannedMin) r.dayEnd) r.now.sec ≤ r.now.sec
    omega

/-- **A block the break paused stays paused, so nothing is reserved** — on either side of the break's end. -/
theorem nothing_is_reserved_while_the_block_is_paused (r : PlanReq)
    (hpaused : ∀ a, r.state.active = some a → a.paused = true) : r.activeRun = none := by
  unfold PlanReq.activeRun
  cases ha : r.state.active with
  | none => rfl
  | some a => simp only [hpaused a ha, if_true]

/-- **One placement step, with walls ending by `now` appended to the blocked list**: the same placement,
and the same walls still appended — every search of step 2 starts at or after `now`. -/
theorem placeStep_drops_walls_ending_by_now (r : PlanReq) (P : List Placed) (X L : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ r.now.sec) (q : Placed) :
    placeStep r (P, X ++ L) q = ((placeStep r (P, X) q).1, (placeStep r (P, X) q).2 ++ L) := by
  have hlo : ∀ w ∈ L, w.2 ≤ max q.span.1 r.now.sec := fun w hw => by have := hL w hw; omega
  unfold placeStep
  simp only
  rw [show r.night :: (X ++ L) = (r.night :: X) ++ L from rfl,
    earliestFree_drops_walls_ending_by _ _ _ _ _ hlo, earliestFree_drops_walls_ending_by _ _ _ _ _ hlo]
  split
  · split
    · rfl
    · split <;> rfl
  · split
    · rename_i a _
      by_cases hc : max q.span.1 r.now.sec ≤ a ∧ a + 60 * q.inst.durMin ≤ q.span.2
      · have hla : ∀ w ∈ L, w.2 ≤ a := fun w hw => by have := hlo w hw; omega
        rw [overlapsAny_drops_walls_ending_by a _ _ L hla]
        split <;> rfl
      · rw [if_neg (by intro h; exact hc ⟨h.1, h.2.1⟩), if_neg (by intro h; exact hc ⟨h.1, h.2.1⟩)]
    · rfl

/-- **The placement fold, likewise** — by induction over the instances. -/
theorem foldl_placeStep_drops_walls_ending_by_now (r : PlanReq) (L : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ r.now.sec) :
    ∀ (qs : List Placed) (P : List Placed) (X : List (Nat × Nat)),
      qs.foldl (placeStep r) (P, X ++ L) =
        ((qs.foldl (placeStep r) (P, X)).1, (qs.foldl (placeStep r) (P, X)).2 ++ L)
  | [], _, _ => rfl
  | q :: qs, P, X => by
    simp only [List.foldl_cons]
    rw [placeStep_drops_walls_ending_by_now r P X L hL q]
    exact foldl_placeStep_drops_walls_ending_by_now r L hL qs _ _

/-- **D77 lifted to §8.2 step 3's whole cut — the day does not change at the instant an overrun break
ends** (README gaps 3480 and 3666; P67).  `r` holds a break running since `t` that has run its planned
length by `now`; its twin is `r` with that break taken out of the state and `run'` in place of the replay —
the same day after `tm break` has ended it at `now` and appended its line, which adds to today's record the
break at its start, and no `start` and no `arrive`.  The two cut the same slots and the same breaks from
`now`: the running break's row ends at `now`, so it blocks nothing the cut can reach
(`an_overrun_break_ends_at_now`), and its counter reads the two alike
(`the_running_break_and_its_logged_twin_count_alike`).

**The class, and why it is the one asked for.**  Nothing differs but the break — so a block the break paused
stays paused (`hpaused`): `tm break` ending a break also UN-PAUSES the block it paused (`day::end_break`),
and the reservation that then appears from `now` is the block resuming, a second change the day should show.
A break ended BEFORE its planned length frees the rest of that length, and the day rightly changes there too;
on that class the counter half still holds (`the_running_break_and_its_logged_twin_count_alike` asks no
length). -/
theorem the_cut_does_not_change_when_an_overrun_break_is_logged (r : PlanReq) (run' : Seal.Run)
    (b : BreakState) (t : Cal.Instant)
    (hbrk : r.state.brk = some b) (hst : b.started = some t)
    (hover : t.sec + 60 * b.plannedMin ≤ r.now.sec)
    (hpaused : ∀ a, r.state.active = some a → a.paused = true)
    (hstarts : (({ r with run := run' } : PlanReq).todayRecord.map (·.starts)).getD [] =
      (r.todayRecord.map (·.starts)).getD [])
    (hlogged : ((({ r with run := run' } : PlanReq).todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) =
      ((r.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) ++ [t.sec])
    (harr : ({ r with run := run' } : PlanReq).todayRecord.bind (·.arrival) =
      r.todayRecord.bind (·.arrival)) :
    ({ r with state := { r.state with brk := none }, run := run' } : PlanReq).todayCut = r.todayCut := by
  generalize hr' : ({ r with state := { r.state with brk := none }, run := run' } : PlanReq) = r'
  have hrec : r'.todayRecord = ({ r with run := run' } : PlanReq).todayRecord := by subst hr'; rfl
  have hlook : r'.look = r.look := by subst hr'; rfl
  have hL := an_overrun_break_ends_at_now r b t hbrk hst hover
  have hbr' : breakRows r' = [] := by subst hr'; rfl
  have hres : r.activeRun = none := nothing_is_reserved_while_the_block_is_paused r hpaused
  have hres' : r'.activeRun = none := nothing_is_reserved_while_the_block_is_paused r' (by subst hr'; exact hpaused)
  have hwalls : wallsToday r' = wallsToday r := by subst hr'; rfl
  have hint : interruptRows r' = interruptRows r := by subst hr'; rfl
  have hbb : r.blockedBeforeRoutines =
      r'.blockedBeforeRoutines ++ (breakRows r).map (fun s => (s.start, s.stop)) := by
    unfold PlanReq.blockedBeforeRoutines PlanReq.reservedSpan blockedByWalls
    rw [hres, hres', hbr', hwalls, hint]
    simp only [List.map_append, List.append_nil, List.map_nil, List.append_assoc]
  have hps : placeStep r' = placeStep r := by subst hr'; rfl
  have hinst : sortRoutines (splitSleep r' r'.routineInstances).2 = sortRoutines (splitSleep r r.routineInstances).2 := by
    have hri : r'.routineInstances = r.routineInstances := by subst hr'; rfl
    have hsl : PlanReq.isSleepInstance r' = PlanReq.isSleepInstance r := by subst hr'; rfl
    rw [hri, splitSleep_congr hsl]
  have hfold : r.placementFold = (r'.placementFold.1, r'.placementFold.2 ++ (breakRows r).map (fun s => (s.start, s.stop))) := by
    unfold PlanReq.placementFold
    rw [hbb, hps, hinst]
    exact foldl_placeStep_drops_walls_ending_by_now r _ hL _ [] _
  have hwin : r'.window = r.window := by
    have hla : r'.loggedArrival = r.loggedArrival := by
      unfold PlanReq.loggedArrival; rw [hrec, harr]
    unfold PlanReq.window
    rw [hla, hlook]
  have hsince : r'.sinceBreak = r.sinceBreak := by
    refine the_running_break_and_its_logged_twin_count_alike r r' t.sec ?_ ?_ (by rw [hrec]; exact hstarts)
      (by rw [hrec]; exact hlogged)
    · rw [hbrk]; simp [hst]
    · rw [← hr']; rfl
  have hrests : r'.restsToday = r.restsToday := by
    unfold PlanReq.restsToday PlanReq.placedRoutines; rw [hfold]
  have hnight : r'.night = r.night := by subst hr'; rfl
  have hsb : r.slotBlocked = r'.slotBlocked ++ (breakRows r).map (fun s => (s.start, s.stop)) := by
    unfold PlanReq.slotBlocked; rw [hfold, hnight]; rfl
  have hcf : r'.cutFrom = r.cutFrom := by
    unfold PlanReq.cutFrom; rw [hwin]; rw [← hr']; rfl
  unfold PlanReq.todayCut
  rw [hsb, hcf, hwin, hrests, hsince, hlook]
  symm
  apply cutSlots_drop_walls_ending_by
  by_cases hc : r.window.2 ≤ max r.now.sec r.window.1
  · left; unfold PlanReq.cutFrom; omega
  · right; intro w hw; have := hL w hw; unfold PlanReq.cutFrom; omega

/-! ############################################################################
## 2. The night — README gaps 2326, 3544 and 3713
############################################################################ -/

/-- **A predicate that holds only below `hi` holds at most `min x hi − a` times in `[a, x)`.** -/
theorem countIn_le_below (P : Nat → Bool) (a hi : Nat) (hP : ∀ t, P t = true → t < hi) :
    ∀ x, Look.countIn P a x ≤ min x hi - a
  | 0 => by simp [Look.countIn]
  | x + 1 => by
    by_cases hax : a ≤ x
    · rw [Look.countIn_succ P hax]
      have ih := countIn_le_below P a hi hP x
      cases hp : P x
      · simp only [Bool.false_eq_true, if_false, Nat.add_zero]; omega
      · have := hP x hp; simp only [if_true]; omega
    · rw [Look.countIn_of_le P (by omega)]; omega

/-- **§8.1's window end, bounded by its walls' end** (README gap 2326's arithmetic): from an arrival at or
before `hi`, over walls that all end by `hi`, the window runs at most `wm` past `hi` — the base adds at most
`wm` to the arrival, and the walls at most the part of `[arrival, hi)` they cover.  Through E7b's least
solution (`Look.windowEnd_le_of_prefixpoint`), not through the walk. -/
theorem windowEnd_le_of_walls_end_by (a wm wc hi : Nat) (ws : List (Nat × Nat)) (ha : a ≤ hi)
    (hws : ∀ w ∈ ws, w.2 ≤ hi) : Look.windowEnd a wm wc ws ≤ hi + wm := by
  apply Look.windowEnd_le_of_prefixpoint
  have hb : Look.windowBase a wm wc ≤ a + wm := by unfold Look.windowBase; omega
  have ho : Look.wallOverlap a (hi + wm) ws ≤ hi - a := by
    rw [Look.wallOverlap_eq_countIn]
    refine Nat.le_trans (countIn_le_below _ a hi ?_ (hi + wm)) (by omega)
    intro t ht
    obtain ⟨w, hw, -, h2⟩ := Look.covered_eq_true.1 ht
    have := hws w hw
    omega
  omega

/-- **README gap 2326's bound, for the kernel's planner window** — closed since the W-39 repair clipped the
window's walls to the day (`Look.wallsClippedOn`, README gap 3556).  When no window is stored for the day,
the arrival is inside it, and the `[day]` is one the decoder accepts (`Look.DayCfg.wf`: a window of at most
24 hours), §8.1's window ends by the end of the night §8.2 step 3 flows around (`Planner.PlanReq.night`) —
the clipped walls end by midnight (`Planner.PlanReq.the_windows_walls_end_by_the_days_end`), and the base is
at most a day past the arrival.  A stored window is `the_stored_window_ends_by_the_night`'s. -/
theorem the_window_ends_by_the_night_without_a_stored_window (r : PlanReq)
    (hnone : r.look.today0.planWindow r.look.today = none)
    (harr : r.look.today0.planArrivalSec r.look.today r.look.tz r.loggedArrival ≤ r.dayEnd)
    (hday : r.look.day.wf = true) : r.window.2 ≤ r.dayEnd + 86400 := by
  have hwm := Look.DayCfg.wf_window_le_a_day hday
  unfold PlanReq.window
  rw [hnone]
  simp only [Look.windowFrom]
  refine Nat.le_trans (windowEnd_le_of_walls_end_by _ _ _ r.dayEnd _ harr ?_) (by omega)
  intro w hw
  exact Look.wallsClippedOn_ends_by _ _ _ _ w hw

/-- **And a STORED window ends by the night's end** whenever its end clock, read on the planned day, is an instant
of that day — true of every zone the host's table probes.  Since W-40 a stored window that crosses midnight
ends 24 hours after that instant, as fork `Planner::window_and_budget` adds `Duration::days(1)` (README gap
3782).  Until W-40 it ended at the NEXT day's clock, and on the night before a 25-hour day that is an hour
later — past `day_end + 24 h`, where the night §8.2 step 3 flows around ends, so the kernel cut a slot the
fork never had (`PlannerWit.the_window_crossing_midnight_ends_on_the_next_days_clock_is_refuted`). -/
theorem the_stored_window_ends_by_the_night (r : PlanReq) (w : Field.Clock × Field.Clock)
    (hs : r.look.today0.planWindow r.look.today = some w)
    (he : (Cal.instantOf r.look.tz r.look.today w.2).sec ≤ r.dayEnd) : r.window.2 ≤ r.dayEnd + 86400 := by
  unfold PlanReq.window
  rw [hs]
  simp only
  split <;> omega

/-- **README gap 2326's bound, whole**: on a `[day]` the decoder accepts, with the planner's arrival and every
stored end clock inside the planned day, §8.1's window ends by the end of the night.  `harr` is not a fact about the
zone: an `arrive` logged after midnight with no wake between is the day's arrival, and on the eve of a 25-hour day
the window then runs past the night on a request the decoder accepts
(`PlannerWit.the_window_bound_needs_the_arrival_inside_the_day`; README gap 3790). -/
theorem the_window_ends_by_the_night (r : PlanReq) (hday : r.look.day.wf = true)
    (harr : r.look.today0.planArrivalSec r.look.today r.look.tz r.loggedArrival ≤ r.dayEnd)
    (hend : ∀ w, r.look.today0.planWindow r.look.today = some w →
      (Cal.instantOf r.look.tz r.look.today w.2).sec ≤ r.dayEnd) : r.window.2 ≤ r.dayEnd + 86400 := by
  cases hs : r.look.today0.planWindow r.look.today with
  | none => exact the_window_ends_by_the_night_without_a_stored_window r hs harr hday
  | some w => exact the_stored_window_ends_by_the_night r w hs (hend w hs)

/-- **Where the window ends by the night's end, no Block row of the day starts at or after a WindDown
row** — not the reservation (it starts at `now`, before the wind-down), not a replayed row (it ends at
`now`), and not a row of §8.2 step 5 (its slot lies in the window and outside the night, which begins at
the wind-down).  `hwdcal` keeps the wind-down inside the calendar, where the rows' clock
(`Planner.clampSec`) does not merge it with a later instant; `PlannerWit`'s W-40 block computes a day
whose wind-down is past the calendar's last second and whose reservation the clock puts ON it. -/
theorem no_block_row_starts_at_or_after_a_wind_down_row_when_the_window_ends_by_the_night (r : PlanReq)
    (hwdcal : r.windDownSec < LogStamp.yearEnd) (hwin : r.window.2 ≤ r.dayEnd + 86400)
    (b w : WfSeg) (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown) :
    b.val.start < w.val.start := by
  obtain ⟨hnw, hws⟩ := a_wind_down_row_of_the_day r w (dayPlan_segments r ▸ hw) hwk
  rw [hws, clampSec_id _ hwdcal]
  rcases a_block_row_is_replayed_reserved_or_assigned r b (dayPlan_segments r ▸ hb) hbk with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨-, h2, h3⟩ := replayedRows_end_at_now r t ht
    show clampSec t.start < r.windDownSec
    unfold clampSec; omega
  · have hst : t.start = r.now.sec := (r.activeRow_is_an_energyless_block t ht).2.2.2.2
    show clampSec t.start < r.windDownSec
    rw [hst]; unfold clampSec; omega
  · obtain ⟨e, s, hs, hst, -, -⟩ := r.an_assigned_row_is_a_slot_of_the_day t ht
    have hsl := r.energised_slot_is_a_slot hs
    obtain ⟨-, h2, h3⟩ := r.a_slot_is_inside_the_window s hsl
    have hev := r.no_slot_reaches_the_evening s hsl (Nat.le_refl s.start) h2
    show clampSec t.start < r.windDownSec
    rw [hst]
    by_cases hc : clampSec s.start < r.windDownSec
    · exact hc
    · exfalso
      apply hev
      unfold clampSec at hc
      unfold PlanReq.night
      simp only
      omega

/-- **§8.3's "no `ci ≥ 4` Block after wind-down", over the whole day, WITHOUT E8's seam** — wherever the
window ends by the night's end, whatever the wire calls the item's `ci` (README gap 3713).  The goal as
written asks it with no hypothesis at all, and is false at a wind-down past the calendar (`hwdcal`'s
witness, `PlannerWit`'s W-40 block). -/
theorem plan_places_no_demanding_block_after_wind_down_when_the_window_ends_by_the_night (r : PlanReq)
    (hwdcal : r.windDownSec < LogStamp.yearEnd) (hwin : r.window.2 ≤ r.dayEnd + 86400)
    (b w : WfSeg) (i : Id)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown)
    (hi : b.val.item = some i) (hafter : w.val.start ≤ b.val.start) :
    (effectiveCi r.plan.val i).val < 4 :=
  absurd hafter (Nat.not_le.2
    (no_block_row_starts_at_or_after_a_wind_down_row_when_the_window_ends_by_the_night r hwdcal hwin b w hb hw
      hbk hwk))

/-- **And on every request whose window is planned rather than stored** — the arrival inside the day, the
`[day]` the decoder accepts and the wind-down inside the calendar: the law with no word about the wire. -/
theorem plan_places_no_demanding_block_after_wind_down_on_a_planned_window (r : PlanReq)
    (hwdcal : r.windDownSec < LogStamp.yearEnd)
    (hnone : r.look.today0.planWindow r.look.today = none)
    (harr : r.look.today0.planArrivalSec r.look.today r.look.tz r.loggedArrival ≤ r.dayEnd)
    (hday : r.look.day.wf = true)
    (b w : WfSeg) (i : Id)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown)
    (hi : b.val.item = some i) (hafter : w.val.start ≤ b.val.start) :
    (effectiveCi r.plan.val i).val < 4 :=
  plan_places_no_demanding_block_after_wind_down_when_the_window_ends_by_the_night r hwdcal
    (the_window_ends_by_the_night_without_a_stored_window r hnone harr hday) b w i hb hw hbk hwk hi hafter

/-- **And on every request whose arrival and stored end clock read inside the planned day**: a `[day]` the decoder
accepts and the wind-down inside the calendar — the goal's conclusion with no word about the wire.  What
`Goals.plan_places_no_demanding_block_after_wind_down` asks beyond this is the calendar's last second (`PlannerWit`'s
W-40 block: the clamp the fork does not have), and a window past the night — a `[day]` window over 24 hours, which the
decoder refuses, or an arrival past the day's end (`PlannerWit.the_eves_window_runs_past_the_night`) — together with a
wire `ci` below the plan's (README gap 3780). -/
theorem plan_places_no_demanding_block_after_wind_down_inside_the_day (r : PlanReq)
    (hwdcal : r.windDownSec < LogStamp.yearEnd) (hday : r.look.day.wf = true)
    (harr : r.look.today0.planArrivalSec r.look.today r.look.tz r.loggedArrival ≤ r.dayEnd)
    (hend : ∀ w, r.look.today0.planWindow r.look.today = some w →
      (Cal.instantOf r.look.tz r.look.today w.2).sec ≤ r.dayEnd)
    (b w : WfSeg) (i : Id)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown)
    (hi : b.val.item = some i) (hafter : w.val.start ≤ b.val.start) :
    (effectiveCi r.plan.val i).val < 4 :=
  plan_places_no_demanding_block_after_wind_down_when_the_window_ends_by_the_night r hwdcal
    (the_window_ends_by_the_night r hday harr hend) b w i hb hw hbk hwk hi hafter

/-! ############################################################################
## 3. L25 over a record that extends the earlier one — README gap 3714
############################################################################ -/

/-- **A replayed row that ended before `now` is replayed again by a later replan whose record still holds
its segment** — the same clip, by the same walls (`PlanFold.clipCut_keeps_an_early_piece`), off the later
record; only the row's `done` flag reads the record, and it reads the later one. -/
theorem a_past_row_is_replayed_from_an_extending_record (r r' : PlanReq) (d d' : Replay.DayAcc)
    (hd' : r'.todayRecord = some d') (hday : r'.dayStart = r.dayStart)
    (hwalls : wallsToday r' = wallsToday r) (hlater : r.now.sec ≤ r'.now.sec)
    (g : Replay.Segment) (hg : g ∈ d'.segments) (q : Nat × Nat) (hq : q ∈ pastSpans r g)
    (hend : q.2 < r.now.sec) : pastRowOf d' g q ∈ pastRows r' := by
  refine mem_pastRows.2 ⟨d', hd', g, hg, q, ?_, rfl⟩
  have hws : wallSpans r' = wallSpans r := by unfold wallSpans; rw [hwalls]
  unfold pastSpans at hq ⊢
  rw [hday, hws]
  by_cases hgs : g.stop.1.sec ≤ r.now.sec
  · rw [Nat.min_eq_left hgs] at hq
    rw [Nat.min_eq_left (by omega : g.stop.1.sec ≤ r'.now.sec)]
    exact hq
  · rw [Nat.min_eq_right (by omega : r.now.sec ≤ g.stop.1.sec)] at hq
    exact PlanFold.clipCut_keeps_an_early_piece
      (by omega : r.now.sec ≤ min g.stop.1.sec r'.now.sec) hq hend

/-- **The two rows of one replayed span, off two records, differ in their `done` flag and nothing else.** -/
theorem pastRowOf_reads_the_record_only_for_done (d d' : Replay.DayAcc) (g : Replay.Segment) (q : Nat × Nat) :
    { pastRowOf d' g q with flags := { (pastRowOf d' g q).flags with done := (pastRowOf d g q).flags.done } }
      = pastRowOf d g q := rfl

/-- **What a replan after a logged verb keeps, case by case**: a row of the earlier day that ended before
`now` and is not open is either a row of the later day as it stands, or a replayed row whose span the later
record still holds, replayed there off the later record. -/
theorem a_closed_row_ended_before_now_is_kept (r r' : PlanReq)
    (hext : ∀ d, r.todayRecord = some d → ∃ d', r'.todayRecord = some d' ∧
      (∀ g ∈ d.segments, g ∈ d'.segments) ∧ (∀ i ∈ d.done, i ∈ d'.done))
    (hday : r'.dayStart = r.dayStart) (hwalls : wallsToday r' = wallsToday r)
    (htravel : ∀ i, r'.isTravelDay i = r.isTravelDay i)
    (hlater : r.now.sec ≤ r'.now.sec) (hcal : r.now.sec < LogStamp.yearEnd)
    (s : WfSeg) (hs : s ∈ (dayPlan r).segments) (hend : s.val.stop < r.now.sec)
    (hopen : s.val.flags.isOpen = false) :
    s ∈ (dayPlan r').segments ∨
      ∃ d d' g q, r.todayRecord = some d ∧ r'.todayRecord = some d' ∧ (∀ i ∈ d.done, i ∈ d'.done) ∧
        s = segOf (pastRowOf d g q) ∧ segOf (pastRowOf d' g q) ∈ (dayPlan r').segments := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows (dayPlan_segments r ▸ hs)
  have hstop : (Planner.segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
  have hlate : ∀ u : Nat, r.now.sec ≤ u → r.now.sec ≤ max (clampSec u) (clampSec t.stop) := by
    intro u hu; unfold clampSec; omega
  have hmem : t ∈ stepOneSegs r ∨
      t ∈ dayRoutineSegs r ++ reservationSegs r ++ r.assignedRows ++ r.keptBreakRows ++
        r.optionalRows ++ r.restRows := by
    simp only [List.mem_append] at ht ⊢
    rcases ht with ((((((ht | ht) | ht) | ht) | ht) | ht) | ht)
    · exact Or.inl ht
    all_goals simp_all
  rcases hmem with ht | ht
  · unfold stepOneSegs at ht
    simp only [List.mem_append] at ht
    rcases ht with ((ht | ht) | ht) | ht
    · rcases mem_replayedRows.1 ht with hp | ho
      · right
        obtain ⟨d, hd, g, hg, q, hq, rfl⟩ := mem_pastRows.1 hp
        obtain ⟨d', hd', hseg, hdone⟩ := hext d hd
        have htend : q.2 < r.now.sec := by
          have := (pastRows_end_at_now r _ hp).2.2
          rw [hstop] at hend
          unfold clampSec at hend
          simp only [pastRowOf] at this hend ⊢
          omega
        have hp' := a_past_row_is_replayed_from_an_extending_record r r' d d' hd' hday hwalls hlater g
          (hseg g hg) q hq htend
        refine ⟨d, d', g, q, hd, hd', hdone, rfl, ?_⟩
        rw [dayPlan_segments]
        exact mem_dayRows_of_mem (by simp [stepOneSegs, replayedRows, hp'])
      · exfalso
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfl, -⟩ := mem_openBlockRows ho
        have : (Planner.segOf t).val.flags = t.flags := rfl
        rw [this, hfl] at hopen
        exact absurd hopen (by simp)
    · exfalso
      have := (interruptRows_are_open_lost_time r t ht).2.2
      rw [hstop] at hend
      unfold clampSec at hend
      omega
    · exfalso
      have := (breakRows_are_running_breaks r t ht).2.1
      rw [hstop] at hend
      unfold clampSec at hend
      omega
    · left
      have hw' : t ∈ (wallsToday r').flatMap (fun x => wallRows (r'.isTravelDay x.id) x) := by
        rw [hwalls]
        obtain ⟨x, hx, htx⟩ := List.mem_flatMap.1 ht
        exact List.mem_flatMap.2 ⟨x, hx, by rw [htravel]; exact htx⟩
      rw [dayPlan_segments]
      exact mem_dayRows_of_mem (by simp [stepOneSegs, hw'])
  · exfalso
    have := PlanFold.a_planned_row_starts_at_or_after_now r t ht
    rw [hstop] at hend
    have := hlate t.start this
    omega

/-- **L25 — §8.3's stability — over a replan after a LOGGED VERB** (the owner's D77, README gap 3714; D5).
Two requests of one day — the same day start, walls and travel days — the second planned later and off a
record that EXTENDS the first's: it holds every segment of the earlier record and every id the earlier
record closed — what a `tm done` appended after `now` leaves on the replays `PlannerWit`'s W-40 block computes
from the log's own lines (that every logged verb but `undo` does is a claim about the replay machine this
module does not prove, README gap 3781).  Then every row of the earlier day
that ended before `now` and is not open is a row of the later day **up to its `done` flag, which can only
rise**.

**Why the flag.**  Fork `past_segments` marks a replayed Block done "when the log closed the item today", so a
`tm done` logged after `now` raises it on an EARLIER block of the same item, and the exact law over an
extending record is refuted at a computed pair (`PlannerWit`'s W-40 block) — shipped behaviour, the fork's
own rule.  Where the later record closes no id the earlier did not, the row is exact
(`plan_is_stable_across_a_replan_after_a_verb_that_closes_nothing`), and the W-39 form, which pinned the
record, is its corollary (`plan_is_stable_across_a_replan_of_the_same_record`).

**What an extension excludes, and why it is not the interesting case.**  An `undo` line after `now` takes a
segment back — the user taking back a verb, which SHOULD move the past
(`PlannerWit.an_undo_after_now_is_not_an_extension` computes it); so a law over a log that merely grows after
`now` is false, and the extension is the hypothesis that the growth took nothing back. -/
theorem plan_is_stable_across_a_replan_after_a_logged_verb (r r' : PlanReq)
    (hext : ∀ d, r.todayRecord = some d → ∃ d', r'.todayRecord = some d' ∧
      (∀ g ∈ d.segments, g ∈ d'.segments) ∧ (∀ i ∈ d.done, i ∈ d'.done))
    (hday : r'.dayStart = r.dayStart) (hwalls : wallsToday r' = wallsToday r)
    (htravel : ∀ i, r'.isTravelDay i = r.isTravelDay i)
    (hlater : r.now.sec ≤ r'.now.sec) (hcal : r.now.sec < LogStamp.yearEnd)
    (s : WfSeg) (hs : s ∈ (dayPlan r).segments) (hend : s.val.stop < r.now.sec)
    (hopen : s.val.flags.isOpen = false) :
    ∃ s' ∈ (dayPlan r').segments,
      { s'.val with flags := { s'.val.flags with done := s.val.flags.done } } = s.val ∧
      (s.val.flags.done = true → s'.val.flags.done = true) := by
  rcases a_closed_row_ended_before_now_is_kept r r' hext hday hwalls htravel hlater hcal s hs hend hopen with
    hs' | ⟨d, d', g, q, -, -, hdone, rfl, hs'⟩
  · exact ⟨s, hs', rfl, id⟩
  · refine ⟨segOf (pastRowOf d' g q), hs', rfl, ?_⟩
    show (pastRowOf d g q).flags.done = true → (pastRowOf d' g q).flags.done = true
    simp only [pastRowOf, Bool.or_eq_true]
    rintro (h | h)
    · exact Or.inl h
    · right
      cases hi : (pastKind g.kind).2.1 with
      | none => simp [hi] at h
      | some i =>
        simp only [hi, Option.map_some, Option.getD_some, decide_eq_true_eq] at h ⊢
        exact hdone i h

/-- **And exactly, where the later record closes no id the earlier did not** — no `done` of a new item after
`now`. -/
theorem plan_is_stable_across_a_replan_after_a_verb_that_closes_nothing (r r' : PlanReq)
    (hext : ∀ d, r.todayRecord = some d → ∃ d', r'.todayRecord = some d' ∧
      (∀ g ∈ d.segments, g ∈ d'.segments) ∧ (∀ i ∈ d.done, i ∈ d'.done))
    (hnew : ∀ d d', r.todayRecord = some d → r'.todayRecord = some d' → ∀ i ∈ d'.done, i ∈ d.done)
    (hday : r'.dayStart = r.dayStart) (hwalls : wallsToday r' = wallsToday r)
    (htravel : ∀ i, r'.isTravelDay i = r.isTravelDay i)
    (hlater : r.now.sec ≤ r'.now.sec) (hcal : r.now.sec < LogStamp.yearEnd)
    (s : WfSeg) (hs : s ∈ (dayPlan r).segments) (hend : s.val.stop < r.now.sec)
    (hopen : s.val.flags.isOpen = false) : s ∈ (dayPlan r').segments := by
  rcases a_closed_row_ended_before_now_is_kept r r' hext hday hwalls htravel hlater hcal s hs hend hopen with
    hs' | ⟨d, d', g, q, hd, hd', hdone, rfl, hs'⟩
  · exact hs'
  · have hsame : pastRowOf d' g q = pastRowOf d g q := by
      have hdd : ∀ i, decide (i ∈ d'.done) = decide (i ∈ d.done) := fun i => by
        by_cases h : i ∈ d.done
        · rw [decide_eq_true h, decide_eq_true (hdone i h)]
        · rw [decide_eq_false h, decide_eq_false (fun h' => h (hnew d d' hd hd' i h'))]
      simp only [pastRowOf, hdd]
    rw [← hsame]
    exact hs'

/-- **The W-39 form — the same record — is a corollary** (`PlanFold.plan_is_stable_across_a_replan`'s
statement, re-derived here from the law over an extension; D77: "the W-39 form that pins the record stays as
a corollary, not as the law"). -/
theorem plan_is_stable_across_a_replan_of_the_same_record (r r' : PlanReq)
    (htr : r'.todayRecord = r.todayRecord) (hday : r'.dayStart = r.dayStart)
    (hwalls : wallsToday r' = wallsToday r) (htravel : ∀ i, r'.isTravelDay i = r.isTravelDay i)
    (hlater : r.now.sec ≤ r'.now.sec) (hcal : r.now.sec < LogStamp.yearEnd)
    (s : WfSeg) (hs : s ∈ (dayPlan r).segments) (hend : s.val.stop < r.now.sec)
    (hopen : s.val.flags.isOpen = false) : s ∈ (dayPlan r').segments :=
  plan_is_stable_across_a_replan_after_a_verb_that_closes_nothing r r'
    (fun d hd => ⟨d, htr.trans hd, fun _ h => h, fun _ h => h⟩)
    (fun d d' hd hd' i hi => by rw [htr, hd] at hd'; cases hd'; exact hi)
    hday hwalls htravel hlater hcal s hs hend hopen

/-! ############################################################################
## 4. D77 over the whole day from `now` — README gaps 3480, 3666 and 3784
############################################################################

The cut is where the two readings of a running break met; every later step of the day is built from the cut,
the placed routines, the blocked spans, the budget and the request's own unchanged fields.  So the day from
`now` is the same for the running break and its logged twin once each of those is shown the same — the one
blocked span that differs is the break's own, which ends by `now`, and every search of steps 2, 6 and the
optionals starts at or after `now`. -/

/-- **`lowestFree` from `lo` does not see spans that end by `lo`** — step 6's search, like step 2's. -/
theorem lowestFree_drops_walls_ending_by (r : PlanReq) (lo hi d : Nat) (A L B : List (Nat × Nat))
    (hL : ∀ w ∈ L, w.2 ≤ lo) : r.lowestFree (A ++ L ++ B) lo hi d = r.lowestFree (A ++ B) lo hi d := by
  unfold PlanReq.lowestFree
  rw [freeIntervals_drop_walls_ending_by lo hi A L B hL]

/-- **What logging an overrun break leaves of the day before step 4**, on the class of states where a block the
break paused stays paused: the twin — `r` with the break taken out of the state and `run'` in place of the replay —
has the same cut, the same placed routines and the same blocked spans but the break's own (which ends by
`now`), no reservation either side, and the same budget. -/
theorem the_logged_twins_inputs (r : PlanReq) (run' : Seal.Run) (b : BreakState) (t : Cal.Instant)
    (hbrk : r.state.brk = some b) (hst : b.started = some t)
    (hover : t.sec + 60 * b.plannedMin ≤ r.now.sec)
    (hpaused : ∀ a, r.state.active = some a → a.paused = true)
    (hstarts : (({ r with run := run' } : PlanReq).todayRecord.map (·.starts)).getD [] =
      (r.todayRecord.map (·.starts)).getD [])
    (hlogged : ((({ r with run := run' } : PlanReq).todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) =
      ((r.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) ++ [t.sec])
    (harr : ({ r with run := run' } : PlanReq).todayRecord.bind (·.arrival) =
      r.todayRecord.bind (·.arrival))
    (hbd : ({ r with run := run' } : PlanReq).blocksDone = r.blocksDone) :
    let r' : PlanReq := { r with state := { r.state with brk := none }, run := run' }
    r'.todayCut = r.todayCut ∧ r'.activeRun = none ∧ r.activeRun = none ∧
    r.placementFold = (r'.placementFold.1, r'.placementFold.2 ++ (breakRows r).map (fun s => (s.start, s.stop))) ∧
    (∀ w ∈ (breakRows r).map (fun s => (s.start, s.stop)), w.2 ≤ r.now.sec) ∧
    remainingBudget r' = remainingBudget r := by
  intro r'
  have hres : r.activeRun = none := nothing_is_reserved_while_the_block_is_paused r hpaused
  have hres' : r'.activeRun = none := nothing_is_reserved_while_the_block_is_paused r' hpaused
  refine ⟨the_cut_does_not_change_when_an_overrun_break_is_logged r run' b t hbrk hst hover
    hpaused hstarts hlogged harr, hres', hres, ?_,
    an_overrun_break_ends_at_now r b t hbrk hst hover, ?_⟩
  · have hL := an_overrun_break_ends_at_now r b t hbrk hst hover
    have hbr' : breakRows r' = [] := rfl
    have hwalls : wallsToday r' = wallsToday r := rfl
    have hint : interruptRows r' = interruptRows r := rfl
    have hbb : r.blockedBeforeRoutines =
        r'.blockedBeforeRoutines ++ (breakRows r).map (fun s => (s.start, s.stop)) := by
      unfold PlanReq.blockedBeforeRoutines PlanReq.reservedSpan blockedByWalls
      rw [hres, hres', hbr', hwalls, hint]
      simp only [List.map_append, List.append_nil, List.append_assoc]
    have hps : placeStep r' = placeStep r := rfl
    have hinst : sortRoutines (splitSleep r' r'.routineInstances).2 =
        sortRoutines (splitSleep r r.routineInstances).2 := by
      have hri : r'.routineInstances = r.routineInstances := rfl
      have hsl : PlanReq.isSleepInstance r' = PlanReq.isSleepInstance r := rfl
      rw [hri, splitSleep_congr hsl]
    unfold PlanReq.placementFold
    rw [hbb, hps, hinst]
    exact foldl_placeStep_drops_walls_ending_by_now r _ hL _ [] _
  · unfold remainingBudget
    have : travelDay r' = travelDay r := rfl
    rw [this]
    split
    · rfl
    · have hbb : r'.budgetBlocks = r.budgetBlocks := rfl
      rw [hbb]
      exact congrArg (r.budgetBlocks - ·) hbd

/-- **Step 5 and step 6 on the twin are step 5 and step 6 on `r`**: given the inputs
`the_logged_twins_inputs` names — the cut, no reservation, the placement with the break's span
appended, and the budget — the assignment fold, step 6's walk and so the final assignment and the
final routine instances are the same. -/
theorem the_logged_twins_folds (r r' : PlanReq) (L : List (Nat × Nat))
    (hlook : r'.look = r.look)
    (hcut : r'.todayCut = r.todayCut) (hres' : r'.activeRun = none) (hres : r.activeRun = none)
    (hpf : r.placementFold = (r'.placementFold.1, r'.placementFold.2 ++ L))
    (hL : ∀ w ∈ L, w.2 ≤ r.now.sec) (hbud : remainingBudget r' = remainingBudget r)
    (hgfs : r'.groupFitsSlot = r.groupFitsSlot) (hdb : r'.dayBatches = r.dayBatches)
    (hnow : r'.now = r.now) (hnight : r'.night = r.night) (hlf : r'.lowestFree = r.lowestFree) :
    r'.assignFold = r.assignFold ∧ r'.deferFold = r.deferFold ∧ r'.energisedSlots = r.energisedSlots ∧
      r'.keptBreaks = r.keptBreaks ∧ r'.assignedSpans = r.assignedSpans := by
  have hsl : r'.todaySlots = r.todaySlots := by unfold PlanReq.todaySlots; rw [hcut]
  have hbr : r'.todayBreaks = r.todayBreaks := by unfold PlanReq.todayBreaks; rw [hcut]
  have hes : r'.energisedSlots = r.energisedSlots := by
    unfold PlanReq.energisedSlots; rw [hsl, hlook]
  have hsg : r'.startGroups = r.startGroups := by
    unfold PlanReq.startGroups PlanReq.buildGroups PlanReq.rawGroups
    rw [hres, hres', hdb]
  have hseed : r'.activeSeed = r.activeSeed := by unfold PlanReq.activeSeed; rw [hres, hres']
  have hstart : r'.assignStart = r.assignStart := by
    unfold PlanReq.assignStart; rw [hsl, hsg, hseed]
  have hstep : r'.assignStep = r.assignStep := by
    funext slots breaks budget a x
    unfold PlanReq.assignStep; rw [hgfs]
  have hfold : r'.assignFold = r.assignFold := by
    unfold PlanReq.assignFold; rw [hes, hstep, hsl, hbr, hbud, hstart]
  have hpr : r'.placedRoutines = r.placedRoutines := by
    unfold PlanReq.placedRoutines; rw [hpf]
  have hspans : r'.assignedSpans = r.assignedSpans := by
    funext a; unfold PlanReq.assignedSpans; rw [hsl]
  have hkb : r'.keptBreaks = r.keptBreaks := by
    funext a; unfold PlanReq.keptBreaks; rw [hbr, hsl]
  have hkbt : r'.keptBreaksToday = r.keptBreaksToday := by
    unfold PlanReq.keptBreaksToday; rw [hkb, hfold]
  have hvs : r'.victimSlot = r.victimSlot := by
    funext a lo hi d; unfold PlanReq.victimSlot; rw [hes]
  have hrpw : r'.rePlaceWalk = r.rePlaceWalk := by
    funext budget a l
    induction l generalizing a with
    | nil => rfl
    | cons x rest ih =>
      unfold PlanReq.rePlaceWalk
      rw [hstep, hsl, hbr]
      simp only [ih]
  have hdi : r'.displaceInto = r.displaceInto := by
    funext budget a q vi s; unfold PlanReq.displaceInto; rw [hrpw, hes]
  have hocc : ∀ (qs : List Placed) (a : Assign) (X : List (Nat × Nat)) (lo hi d : Nat), r.now.sec ≤ lo →
      r.lowestFree (r.occupiedNow qs a ++ X) lo hi d = r'.lowestFree (r'.occupiedNow qs a ++ X) lo hi d := by
    intro qs a X lo hi d hlo
    rw [hlf]
    unfold PlanReq.occupiedNow
    rw [hpf, hspans]
    simp only [List.append_assoc]
    have := lowestFree_drops_walls_ending_by r lo hi d r'.placementFold.2 L
      (qs.filterMap (·.placedAt) ++ (r.assignedSpans a ++ X)) (fun w hw => by have := hL w hw; omega)
    simpa only [List.append_assoc] using this
  have hdo : ∀ budget qs a q, r'.deferOne budget qs a q = r.deferOne budget qs a q := by
    intro budget qs a q
    have hlo : r.now.sec ≤ max q.span.1 r.now.sec := Nat.le_max_right _ _
    unfold PlanReq.deferOne
    simp only [List.append_assoc]
    rw [hnow, hkbt, hnight, hvs, hes, hdi, ← hocc qs a _ _ _ _ hlo, ← hocc qs a _ _ _ _ hlo]
  have hdw : ∀ budget pre a qs, r'.deferWalk budget pre a qs = r.deferWalk budget pre a qs := by
    intro budget pre a qs
    induction qs generalizing pre a with
    | nil => rfl
    | cons q post ih =>
      unfold PlanReq.deferWalk
      rw [hdo]
      exact ih _ _
  refine ⟨hfold, ?_, hes, hkb, hspans⟩
  unfold PlanReq.deferFold
  rw [hbud, hfold, hpr, hdw]

/-- **No row of the log's past starts at or after `now`** — every replayed row ends by `now` and is not empty, and
the rows' clock only lowers a start. -/
theorem replayedRows_from_now (r : PlanReq) :
    (replayedRows r).filter (fun t => decide (r.now.sec ≤ clampSec t.start)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro t ht
  obtain ⟨-, h2, h3⟩ := replayedRows_end_at_now r t ht
  intro h
  rw [decide_eq_true_eq] at h
  unfold clampSec at h
  omega

/-- **Nor does an overrun running break's row** — it runs from where the break began to `now`. -/
theorem breakRows_from_now (r : PlanReq) (b : BreakState) (t : Cal.Instant)
    (hbrk : r.state.brk = some b) (hst : b.started = some t)
    (hover : t.sec + 60 * b.plannedMin ≤ r.now.sec) :
    (breakRows r).filter (fun t => decide (r.now.sec ≤ clampSec t.start)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro s hs
  unfold breakRows at hs
  rw [hbrk] at hs
  simp only [Option.bind_some, hst, Option.map_some] at hs
  split at hs
  · cases hs
  · rename_i hne
    simp only [List.mem_singleton] at hs
    subst hs
    intro h
    rw [decide_eq_true_eq] at h
    unfold clampSec at h
    simp only at h hne
    omega

/-- **§8.2 from `now`, on a twin whose inputs before step 4 are `r`'s** — the rows of the day that start at or
after `now` are the same, in the same order: the log's past and a running break end by `now`, the walls and the
interruption are the state's, and every row of steps 2 and 5-7 is built from the folds
`the_logged_twins_folds` shows equal. -/
theorem the_day_from_now_of_the_twins_inputs (r r' : PlanReq) (L : List (Nat × Nat))
    (hlook : r'.look = r.look)
    (hcut : r'.todayCut = r.todayCut) (hres' : r'.activeRun = none) (hres : r.activeRun = none)
    (hpf : r.placementFold = (r'.placementFold.1, r'.placementFold.2 ++ L))
    (hL : ∀ w ∈ L, w.2 ≤ r.now.sec) (hbud : remainingBudget r' = remainingBudget r)
    (hgfs : r'.groupFitsSlot = r.groupFitsSlot) (hdb : r'.dayBatches = r.dayBatches)
    (hnow : r'.now = r.now) (hnight : r'.night = r.night) (hlf : r'.lowestFree = r.lowestFree)
    (hstep1 : (stepOneOrder r').filter (fun t => decide (r.now.sec ≤ clampSec t.start)) =
      (stepOneOrder r).filter (fun t => decide (r.now.sec ≤ clampSec t.start)))
    (hrow : r'.routineRow = r.routineRow) (heve : r'.eveningRows = r.eveningRows)
    (hoc : r'.optionalCands = r.optionalCands) (hds : r'.dayStart = r.dayStart)
    (hwd : r'.windDownSec = r.windDownSec) :
    ((dayPlan r').segments.filter (fun s => decide (r.now.sec ≤ s.val.start))) =
      ((dayPlan r).segments.filter (fun s => decide (r.now.sec ≤ s.val.start))) := by
  obtain ⟨-, hdf, hes, hkb, hspans⟩ :=
    the_logged_twins_folds r r' L hlook hcut hres' hres hpf hL hbud hgfs hdb hnow hnight hlf
  have hfr : r'.finalRoutines = r.finalRoutines := by unfold PlanReq.finalRoutines; rw [hdf]
  have hfa : r'.finalAssign = r.finalAssign := by unfold PlanReq.finalAssign; rw [hdf]
  have hrs : reservationSegs r' = reservationSegs r := by
    unfold reservationSegs PlanReq.activeRow; rw [hres, hres']
  have hrt : dayRoutineSegs r' = dayRoutineSegs r := by
    unfold dayRoutineSegs routineRows; rw [hfr, hrow, heve]
  have har : r'.assignedRows = r.assignedRows := by
    unfold PlanReq.assignedRows; rw [hes, hfa]
  have hek : r'.emitKeptBreaks = r.emitKeptBreaks := by
    unfold PlanReq.emitKeptBreaks; rw [hkb, hfa, hfr]
  have hkr : r'.keptBreakRows = r.keptBreakRows := by
    unfold PlanReq.keptBreakRows; rw [hek]
  have hofree : r'.optionalFree = r.optionalFree := by
    unfold PlanReq.optionalFree PlanReq.optionalOccupied PlanReq.occupiedNow
    rw [hpf, hfr, hfa, hspans, hek, hnow, hds, hwd]
    simp only [List.append_assoc]
    have := freeIntervals_drop_walls_ending_by (max r.now.sec r.dayStart) r.windDownSec r'.placementFold.2 L
      (List.filterMap (·.placedAt) r.finalRoutines ++ (r.assignedSpans r.finalAssign ++ r.emitKeptBreaks))
      (fun w hw => by have := hL w hw; omega)
    simpa only [List.append_assoc] using this.symm
  have hof : r'.optionalFold = r.optionalFold := by
    unfold PlanReq.optionalFold; rw [hoc, hofree]
  have hor : r'.optionalRows = r.optionalRows := by unfold PlanReq.optionalRows; rw [hof]
  have hrst : r'.restRows = r.restRows := by
    unfold PlanReq.restRows PlanReq.restTaken PlanReq.optionalSpans; rw [hes, hfa, hof, hfr]
  rw [dayPlan_segments, dayPlan_segments]
  unfold dayRows
  rw [sortRows_filter, sortRows_filter, List.filter_map, List.filter_map]
  simp only [List.filter_append]
  have hq : ((fun s : WfSeg => decide (r.now.sec ≤ s.val.start)) ∘ Planner.segOf) =
      (fun (t : Seg) => decide (r.now.sec ≤ clampSec t.start)) := rfl
  rw [hq, hstep1, hrt, hrs, har, hkr, hor, hrst]

/-- **Step 1's rows from `now` are the same for the overrun break and its logged twin** — the log's past and the
running break end by `now` on both sides, and the walls and the interruption are the state's own. -/
theorem stepOneOrder_from_now_of_the_logged_twin (r : PlanReq) (run' : Seal.Run) (b : BreakState) (t : Cal.Instant)
    (hbrk : r.state.brk = some b) (hst : b.started = some t)
    (hover : t.sec + 60 * b.plannedMin ≤ r.now.sec) :
    (stepOneOrder ({ r with state := { r.state with brk := none }, run := run' } : PlanReq)).filter
        (fun t => decide (r.now.sec ≤ clampSec t.start)) =
      (stepOneOrder r).filter (fun t => decide (r.now.sec ≤ clampSec t.start)) := by
  have hrep' : (replayedRows ({ r with state := { r.state with brk := none }, run := run' } : PlanReq)).filter
      (fun t => decide (r.now.sec ≤ clampSec t.start)) = [] :=
    replayedRows_from_now ({ r with state := { r.state with brk := none }, run := run' } : PlanReq)
  have hrep := replayedRows_from_now r
  have hbr := breakRows_from_now r b t hbrk hst hover
  have hbr' : breakRows ({ r with state := { r.state with brk := none }, run := run' } : PlanReq) = [] := rfl
  have hint : interruptRows ({ r with state := { r.state with brk := none }, run := run' } : PlanReq) =
      interruptRows r := rfl
  have hwalls : wallsToday ({ r with state := { r.state with brk := none }, run := run' } : PlanReq) =
      wallsToday r := rfl
  have htr : ({ r with state := { r.state with brk := none }, run := run' } : PlanReq).isTravelDay = r.isTravelDay := rfl
  have htoday : ({ r with state := { r.state with brk := none }, run := run' } : PlanReq).today = r.today := rfl
  unfold stepOneOrder stepOneSegs
  rw [hint]
  split <;> simp only [List.filter_append, hrep', hrep, hbr, hbr', hwalls, htr, htoday, List.filter_nil,
    List.nil_append]

/-- **D77, the whole day from `now`** (the owner's D77, README gaps 3480, 3666 and 3784; P67).  `r` holds a break
running since `t` that has run its planned length by `now`, and no block is running; its twin is `r` with the break
taken out of the state and `run'` in place of the replay — the same day after `tm break` has ended it at `now`,
appending its line, which adds the break at its start to today's record and no `start`, no `arrive` and no
finished block.  **Every row of the two days that starts at or after `now` is the same, in the same order** — the
cut (`the_cut_does_not_change_when_an_overrun_break_is_logged`), step 5's assignment, step 6's walk, the kept
breaks, the optionals, the rest and the evening.  The rows before `now` differ, and should: the break's own row is
open while it runs and a closed past row once logged.

**The class, and why it is the one asked for.**  Nothing differs but the break, so a block the break paused stays
paused (`hpaused`; no block at all pays it) — the frozen P45 comparand's own model of the logged twin.  `tm break`
ending a break also UN-PAUSES the block it paused (`day::end_break`), and the reservation that then appears from
`now` is the block resuming, a second change the day should show.  A break ended BEFORE its planned length frees
the rest of that length; the counter half (`the_running_break_and_its_logged_twin_count_alike`) holds at any
length. -/
theorem the_day_from_now_does_not_change_when_an_overrun_break_is_logged (r : PlanReq) (run' : Seal.Run)
    (b : BreakState) (t : Cal.Instant)
    (hbrk : r.state.brk = some b) (hst : b.started = some t)
    (hover : t.sec + 60 * b.plannedMin ≤ r.now.sec)
    (hpaused : ∀ a, r.state.active = some a → a.paused = true)
    (hstarts : (({ r with run := run' } : PlanReq).todayRecord.map (·.starts)).getD [] =
      (r.todayRecord.map (·.starts)).getD [])
    (hlogged : ((({ r with run := run' } : PlanReq).todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) =
      ((r.todayRecord.map (·.breaks)).getD []).map (·.t.1.sec) ++ [t.sec])
    (harr : ({ r with run := run' } : PlanReq).todayRecord.bind (·.arrival) =
      r.todayRecord.bind (·.arrival))
    (hbd : ({ r with run := run' } : PlanReq).blocksDone = r.blocksDone) :
    ((dayPlan ({ r with state := { r.state with brk := none }, run := run' } : PlanReq)).segments.filter
        (fun s => decide (r.now.sec ≤ s.val.start))) =
      ((dayPlan r).segments.filter (fun s => decide (r.now.sec ≤ s.val.start))) := by
  obtain ⟨hcut, hres', hres, hpf, hL, hbud⟩ :=
    the_logged_twins_inputs r run' b t hbrk hst hover hpaused hstarts hlogged harr hbd
  have heve : ({ r with state := { r.state with brk := none }, run := run' } : PlanReq).eveningRows =
      r.eveningRows := by
    have hsl : PlanReq.isSleepInstance ({ r with state := { r.state with brk := none }, run := run' } : PlanReq) =
        PlanReq.isSleepInstance r := rfl
    have hri : ({ r with state := { r.state with brk := none }, run := run' } : PlanReq).routineInstances =
        r.routineInstances := rfl
    unfold PlanReq.eveningRows PlanReq.sleepSeg PlanReq.sleepInstance
    rw [hri, splitSleep_congr hsl]
    rfl
  exact the_day_from_now_of_the_twins_inputs r _ _ rfl hcut hres' hres hpf hL hbud rfl rfl rfl rfl rfl
    (stepOneOrder_from_now_of_the_logged_twin r run' b t hbrk hst hover) rfl heve rfl rfl rfl

end PlanStable
end Tm
