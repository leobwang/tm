import TmKernel.GridCut

/-!
# MidnightCut — a Pause past local midnight is cut by each calendar day's own walls (stage 6, W-40 track T)

**The call** — the campaign's D77 on README gap 3620, revisable by the owner.  W-39 made the week grid
draw a Pause over the kernel's cut, `GridCut.segSpans`, which is `Planner.pastSpans` at the day of the
Pause's record: the Pause clipped to that day's midnight and to `now`, and cut by that day's walls
clipped to that day.  A Pause of Tuesday's record that runs past midnight — a block run into a call
from 23:30 to 00:30, D61 pausing it over the call — therefore kept its half after midnight as `pause`
(parity P63 as issued), while Wednesday's own plan draws those thirty minutes as the call's Wall row.
One span, two readings (AGENTS §5.3), and the grid against D65's "the wall alone".  **Now each
calendar day's part of the clip is cut by that day's walls** (`GridCut.daySpans`,
`GridCut.dayCovered`): `segSpans` at every day the clip reaches, its `now` that day's next midnight
or `now`, whichever comes first, and `now` itself on the last day.

**What a partition needs, and the `Cal` lemma that gives it.**  The day parts
`[max start (midnight of d+i), min stop (its now))` cover the clip whatever the zone does
(`a_second_of_the_clip_is_in_a_days_part`), and they are DISJOINT, and inside the clip, exactly when
the midnights do not run backwards over the days concerned — which `Cal.instantOf` does not promise
for an arbitrary table: a table whose offsets jump by most of a day can put the earliest instant of
one day's midnight after the next day's.  `Cal.instantOf_midnights_rise` proves they rise strictly in
every zone whose offsets (its base and every transition's) lie within 21 hours of each other and of
UTC — every zone the tz database has over the host's sampled [1900, 2200) except the few that moved
across the date line (Apia, Fakaofo, Kwajalein, Kiritimati, Enderbury), each named here rather than
assumed away.  MEASURED at W-40 over chrono-tz 0.10.4, every zone sampled hourly over that range:
of its 597 names seven fail the hypotheses, and they are those five zones (Kwajalein twice, as a
link, and Enderbury twice, as Kanton); the widest span among the other 590 is eleven hours
(Antarctica/Casey).  The partition law is stated over rising midnights
(`the_grid_draws_every_second_of_the_clip_once_day_by_day`), and over such a zone with no hypothesis
on the midnights at all (`the_grid_cuts_every_second_once_in_a_zone_near_utc`).  21 hours is
`24 h − 180 min`: the latest instant `instantOf` can answer for a midnight in a spring-forward gap is
three hours on (`gapHit`'s 180 minutes).

**A Pause inside its day is cut exactly as before** (`the_cut_inside_its_day_is_unchanged`), so the
change is exactly the half past midnight, which `GridCut.the_call_past_midnight_is_its_days_wall` and
its Chicago twin run, beside P63's own cut of the same Pause (the theorem separating the two rules,
AGENTS §4's last row).  The partition laws are about the grid's units, whole seconds, as GridCut's are.

**No definition here.**  The condition on the table is written out in each statement rather than as a
`def`: a definition used only by proofs would be code the compiler emits and nothing calls, which
check 12 gates and its exemption file may only shrink (D51).
-/

namespace Tm
namespace Cal

/-! ## The midnights rise -/

/-- A span's offset is the base it began with or one of the transitions after it. -/
theorem spansFrom_off_mem : ∀ (L : List (Instant × Offset)) (lo : Option Nat) (off : Offset) (sp : Span),
    sp ∈ spansFrom lo off L → sp.off = off ∨ sp.off ∈ L.map Prod.snd
  | [], lo, off, sp, hm => by
      simp only [spansFrom, List.mem_singleton] at hm
      exact Or.inl (by rw [hm])
  | (i, o) :: rest, lo, off, sp, hm => by
      simp only [spansFrom, List.mem_cons] at hm
      rcases hm with h | h
      · exact Or.inl (by rw [h])
      · rcases spansFrom_off_mem rest (some i.sec) o sp h with h' | h'
        · exact Or.inr (by simp [h'])
        · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h')

/-- **A hit's second, east-positive**: the clock less its span's offset, exactly — `utcSecAt`, which
never saturates. -/
theorem Span.hit_sec (sp : Span) (l s : Nat) (h : sp.hit l = some s) :
    (s : Int) = (l : Int) - (if sp.off.west then -(sp.off.sec : Int) else (sp.off.sec : Int)) := by
  unfold Span.hit at h
  split at h
  · rename_i s' hu
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      unfold utcSecAt at hu
      cases hw : sp.off.west <;> simp only [hw, if_true, if_false, Bool.false_eq_true] at hu ⊢
      · split at hu
        · simp only [Option.some.injEq] at hu
          omega
        · simp at hu
      · simp only [Option.some.injEq] at hu
        omega
    · simp at h
  · simp at h

/-- **Every hit of a local clock is that clock less one of the table's offsets** — its base or a
transition's, east-positive. -/
theorem localHits_sec (z : Tz) (l s : Nat) (h : s ∈ localHits z l) :
    ∃ o ∈ z.val.base :: z.val.trans.map Prod.snd,
      (s : Int) = (l : Int) - (if o.west then -(o.sec : Int) else (o.sec : Int)) := by
  rw [localHits_eq, List.mem_filterMap] at h
  obtain ⟨sp, hsp, hhit⟩ := h
  refine ⟨sp.off, ?_, Span.hit_sec sp l s hhit⟩
  unfold TzTable.spans at hsp
  rcases spansFrom_off_mem z.val.trans none z.val.base sp hsp with h | h
  · rw [h]
    exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ h

/-- **`gapHit` answers a hit of a later clock**: `60·k` seconds on, `k` within its fuel. -/
theorem gapHit_some (z : Tz) (l : Nat) : ∀ (fuel m s : Nat), gapHit z l fuel m = some s →
    ∃ k, m ≤ k ∧ k < m + fuel ∧ s ∈ localHits z (l + 60 * k)
  | 0, m, s, h => by simp [gapHit] at h
  | fuel + 1, m, s, h => by
      unfold gapHit at h
      split at h
      · rename_i s' rest hh
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨m, Nat.le_refl _, by omega, by rw [hh]; exact List.mem_cons_self ..⟩
      · obtain ⟨k, hk1, hk2, hk3⟩ := gapHit_some z l fuel (m + 1) s h
        exact ⟨k, by omega, by omega, hk3⟩

/-- **`instantOf`'s three answers, east-positive**: a hit of its clock, or of a clock up to 180 minutes
later (a spring-forward gap), less one of the table's offsets — or the clock read as UTC. -/
theorem instantOf_sec (z : Tz) (d : Nat) (c : Fin 1440) :
    (∃ o ∈ z.val.base :: z.val.trans.map Prod.snd, ∃ k, k ≤ 180 ∧
        ((instantOf z d c).sec : Int) = ((d * 86400 + c.val * 60 + 60 * k : Nat) : Int) -
          (if o.west then -(o.sec : Int) else (o.sec : Int))) ∨
      (instantOf z d c).sec = d * 86400 + c.val * 60 := by
  unfold instantOf
  cases hh : localHits z (d * 86400 + c.val * 60) with
  | cons s rest =>
    left
    obtain ⟨o, ho, hs⟩ := localHits_sec z _ s (by rw [hh]; exact List.mem_cons_self ..)
    exact ⟨o, ho, 0, by omega, by simpa using hs⟩
  | nil =>
    cases hg : gapHit z (d * 86400 + c.val * 60) 180 1 with
    | some s =>
      left
      obtain ⟨k, hk1, hk2, hk3⟩ := gapHit_some z _ 180 1 s hg
      obtain ⟨o, ho, hs⟩ := localHits_sec z _ s hk3
      exact ⟨o, ho, k, by omega, by simpa using hs⟩
    | none => exact Or.inr rfl

/-- **A zone's local midnights rise, strictly** — when every two of its table's offsets (the base and
every transition's, east-positive) are less than 21 hours apart and none is 21 hours or more from UTC.
21 hours is a day less `gapHit`'s three: a midnight inside a spring-forward gap is answered up to
180 minutes on.  Every zone the tz database has over [1900, 2200) satisfies it except the few that
moved across the date line, whose tables span 24 hours or more (`a_date_line_table_is_not_near`) —
measured over chrono-tz 0.10.4's 597 names, the module header says which. -/
theorem instantOf_midnights_rise (z : Tz) (d : Nat)
    (hnear : ∀ a ∈ z.val.base :: z.val.trans.map Prod.snd, ∀ b ∈ z.val.base :: z.val.trans.map Prod.snd,
      (if b.west then -(b.sec : Int) else (b.sec : Int)) -
        (if a.west then -(a.sec : Int) else (a.sec : Int)) < 75600)
    (hsmall : ∀ a ∈ z.val.base :: z.val.trans.map Prod.snd,
      -75600 < (if a.west then -(a.sec : Int) else (a.sec : Int)) ∧
        (if a.west then -(a.sec : Int) else (a.sec : Int)) < 75600) :
    (instantOf z d 0).sec < (instantOf z (d + 1) 0).sec := by
  rcases instantOf_sec z d 0 with ⟨a, ha, k, hk, hp⟩ | hp <;>
    rcases instantOf_sec z (d + 1) 0 with ⟨b, hb, k', hk', hq⟩ | hq
  · have h1 := hnear a ha b hb
    generalize (if a.west then -(a.sec : Int) else (a.sec : Int)) = ea at *
    generalize (if b.west then -(b.sec : Int) else (b.sec : Int)) = eb at *
    simp only [Fin.val_zero] at hp hq
    omega
  · have h1 := hsmall a ha
    generalize (if a.west then -(a.sec : Int) else (a.sec : Int)) = ea at *
    simp only [Fin.val_zero] at hp hq
    omega
  · have h1 := hsmall b hb
    generalize (if b.west then -(b.sec : Int) else (b.sec : Int)) = eb at *
    simp only [Fin.val_zero] at hp hq
    omega
  · simp only [Fin.val_zero] at hp hq
    omega

/-- **The lemma's hypotheses hold of a real zone with transitions**: Chicago's 2026 table (CST, CDT,
CST), so its midnights rise on every day, the two transition days included. -/
theorem chicago_midnights_rise (d : Nat) :
    (instantOf chicago d 0).sec < (instantOf chicago (d + 1) 0).sec :=
  instantOf_midnights_rise chicago d (by decide) (by decide)

/-- **And they exclude what they name**: a table that moved across the date line, from eleven hours
west to thirteen east (Apia's 2011 move, by the day, not the second), is not near — its offsets are
24 hours apart, and the lemma says nothing of it. -/
theorem a_date_line_table_is_not_near :
    ¬ ((∀ a ∈ [(⟨true, 39600⟩ : Offset), ⟨false, 46800⟩], ∀ b ∈ [(⟨true, 39600⟩ : Offset), ⟨false, 46800⟩],
        (if b.west then -(b.sec : Int) else (b.sec : Int)) -
          (if a.west then -(a.sec : Int) else (a.sec : Int)) < 75600)) := by
  decide

end Cal

namespace GridCut

/-! ## The day parts -/

/-- **Kept, day by day**: a second is in `daySpans` exactly when it is in one day's `segSpans`. -/
theorem mem_daySpans_iff (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment)
    (u : Nat) :
    (∃ q ∈ daySpans z ix d now g, q.1 ≤ u ∧ u < q.2) ↔
      ∃ i, i < clipDays z d now g ∧
        ∃ q ∈ segSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g, q.1 ≤ u ∧ u < q.2 := by
  unfold daySpans
  constructor
  · rintro ⟨q, hq, hu⟩
    obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hq
    exact ⟨i, List.mem_range.1 hi, q, hq, hu⟩
  · rintro ⟨i, hi, q, hq, hu⟩
    exact ⟨q, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hq⟩, hu⟩

/-- **Covered, day by day**: a second is in `dayCovered` exactly when it is in one day's
`coveredSpans`. -/
theorem mem_dayCovered_iff (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment)
    (u : Nat) :
    (∃ q ∈ dayCovered z ix d now g, q.1 ≤ u ∧ u < q.2) ↔
      ∃ i, i < clipDays z d now g ∧
        ∃ q ∈ coveredSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g, q.1 ≤ u ∧ u < q.2 := by
  unfold dayCovered
  constructor
  · rintro ⟨q, hq, hu⟩
    obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hq
    exact ⟨i, List.mem_range.1 hi, q, hq, hu⟩
  · rintro ⟨i, hi, q, hq, hu⟩
    exact ⟨q, List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hq⟩, hu⟩

/-- At least one day: the record's own. -/
theorem one_le_clipDays (z : Cal.Tz) (d now : Nat) (g : Replay.Segment) : 1 ≤ clipDays z d now g := by
  unfold clipDays
  exact Nat.le_max_left _ _

/-- The last index at or below a bound whose value is at or below `u`, when the first is. -/
theorem last_at_or_below (f : Nat → Nat) (u : Nat) (h0 : f 0 ≤ u) :
    ∀ k, 0 < k → ∃ i, i < k ∧ f i ≤ u ∧ (i + 1 < k → u < f (i + 1))
  | 0, hk => absurd hk (by omega)
  | 1, _ => ⟨0, by omega, h0, fun h => absurd h (by omega)⟩
  | k + 2, _ => by
      obtain ⟨i, hi, hfi, hnext⟩ := last_at_or_below f u h0 (k + 1) (by omega)
      by_cases hk : f (k + 1) ≤ u
      · exact ⟨k + 1, by omega, hk, fun h => absurd h (by omega)⟩
      · refine ⟨i, by omega, hfi, fun h => ?_⟩
        by_cases h' : i + 1 < k + 1
        · exact hnext h'
        · have he : i + 1 = k + 1 := by omega
          rw [he]
          omega

/-- **Every second of the clip is in some day's part** — whatever the zone does: the last day whose
midnight is at or before it. -/
theorem a_second_of_the_clip_is_in_a_days_part (z : Cal.Tz) (d now : Nat) (g : Replay.Segment) (u : Nat)
    (hu : max g.start.1.sec (Cal.instantOf z d 0).sec ≤ u ∧ u < min g.stop.1.sec now) :
    ∃ i, i < clipDays z d now g ∧ max g.start.1.sec (Cal.instantOf z (d + i) 0).sec ≤ u ∧
      u < min g.stop.1.sec (dayNow z d now (clipDays z d now g) i) := by
  obtain ⟨i, hi, hfi, hnext⟩ := last_at_or_below (fun i => (Cal.instantOf z (d + i) 0).sec) u
    (by show (Cal.instantOf z (d + 0) 0).sec ≤ u; rw [Nat.add_zero]; omega)
    (clipDays z d now g) (one_le_clipDays z d now g)
  refine ⟨i, hi, by omega, ?_⟩
  unfold dayNow
  split
  · rename_i h
    have h2 := hnext h
    rw [show d + (i + 1) = d + i + 1 by omega] at h2
    omega
  · omega

/-- Rising midnights, consecutive day by consecutive day, rise over any two days in the range. -/
theorem midnights_rise_over (z : Cal.Tz) (d n : Nat)
    (hm : ∀ j, j + 1 < n → (Cal.instantOf z (d + j) 0).sec ≤ (Cal.instantOf z (d + j + 1) 0).sec) :
    ∀ a b, a ≤ b → b < n → (Cal.instantOf z (d + a) 0).sec ≤ (Cal.instantOf z (d + b) 0).sec
  | a, 0, hab, _ => by rw [show a = 0 by omega]; exact Nat.le_refl _
  | a, b + 1, hab, hb => by
      by_cases h : a = b + 1
      · rw [h]; exact Nat.le_refl _
      · have h1 := midnights_rise_over z d n hm a b (by omega) (by omega)
        have h2 := hm b (by omega)
        rw [show d + (b + 1) = d + b + 1 by omega]
        omega

/-- **On rising midnights a second is in at most one day's part.** -/
theorem a_second_is_in_one_days_part (z : Cal.Tz) (d now : Nat) (g : Replay.Segment) (u : Nat)
    (hm : ∀ j, j + 1 < clipDays z d now g →
      (Cal.instantOf z (d + j) 0).sec ≤ (Cal.instantOf z (d + j + 1) 0).sec)
    (i j : Nat) (hi : i < clipDays z d now g) (hj : j < clipDays z d now g)
    (hui : max g.start.1.sec (Cal.instantOf z (d + i) 0).sec ≤ u ∧
      u < min g.stop.1.sec (dayNow z d now (clipDays z d now g) i))
    (huj : max g.start.1.sec (Cal.instantOf z (d + j) 0).sec ≤ u ∧
      u < min g.stop.1.sec (dayNow z d now (clipDays z d now g) j)) : i = j := by
  have key : ∀ a b, a < b → b < clipDays z d now g →
      max g.start.1.sec (Cal.instantOf z (d + a) 0).sec ≤ u →
      u < min g.stop.1.sec (dayNow z d now (clipDays z d now g) a) →
      max g.start.1.sec (Cal.instantOf z (d + b) 0).sec ≤ u → False := by
    intro a b hab hb _ ha2 hb1
    have hmid := midnights_rise_over z d (clipDays z d now g) hm (a + 1) b (by omega) hb
    rw [show d + (a + 1) = d + a + 1 by omega] at hmid
    unfold dayNow at ha2
    rw [if_pos (by omega)] at ha2
    omega
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact (key i j h hj hui.1 hui.2 huj.1).elim
  · exact h
  · exact (key j i h hi huj.1 huj.2 hui.1).elim

/-- **On rising midnights a day's part is inside the clip.** -/
theorem a_days_part_is_inside_the_clip (z : Cal.Tz) (d now : Nat) (g : Replay.Segment) (u : Nat)
    (hm : ∀ j, j + 1 < clipDays z d now g →
      (Cal.instantOf z (d + j) 0).sec ≤ (Cal.instantOf z (d + j + 1) 0).sec)
    (i : Nat) (hi : i < clipDays z d now g)
    (hui : max g.start.1.sec (Cal.instantOf z (d + i) 0).sec ≤ u ∧
      u < min g.stop.1.sec (dayNow z d now (clipDays z d now g) i)) :
    max g.start.1.sec (Cal.instantOf z d 0).sec ≤ u ∧ u < min g.stop.1.sec now := by
  have h0 := midnights_rise_over z d (clipDays z d now g) hm 0 i (by omega) hi
  simp only [Nat.add_zero] at h0
  have hn : dayNow z d now (clipDays z d now g) i ≤ now := by
    unfold dayNow
    split <;> omega
  omega

/-! ## The grid's partition, day by day -/

/-- **Every second of a segment's clip is drawn once, by the walls of the day it falls on** (D77, README
gap 3620) — on rising midnights: kept or covered, never both; every piece holding it comes from one
calendar day's part; and nothing outside the clip is drawn. -/
theorem the_grid_draws_every_second_of_the_clip_once_day_by_day (z : Cal.Tz) (ix : List Look.WallIx)
    (d now : Nat) (g : Replay.Segment)
    (hm : ∀ j, j + 1 < clipDays z d now g →
      (Cal.instantOf z (d + j) 0).sec ≤ (Cal.instantOf z (d + j + 1) 0).sec) (u : Nat) :
    (((∃ q ∈ daySpans z ix d now g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ dayCovered z ix d now g, q.1 ≤ u ∧ u < q.2)) ↔
      (max g.start.1.sec (Cal.instantOf z d 0).sec ≤ u ∧ u < min g.stop.1.sec now)) ∧
    ¬ ((∃ q ∈ daySpans z ix d now g, q.1 ≤ u ∧ u < q.2) ∧
        (∃ q ∈ dayCovered z ix d now g, q.1 ≤ u ∧ u < q.2)) ∧
    (∀ i j, i < clipDays z d now g → j < clipDays z d now g →
      ((∃ q ∈ segSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ coveredSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g, q.1 ≤ u ∧ u < q.2)) →
      ((∃ q ∈ segSpans z ix (d + j) (dayNow z d now (clipDays z d now g) j) g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ coveredSpans z ix (d + j) (dayNow z d now (clipDays z d now g) j) g, q.1 ≤ u ∧ u < q.2)) →
      i = j) := by
  -- one day's own law: drawn ↔ in that day's part, never both
  have day := fun i => the_grid_draws_every_second_of_the_clip_once z ix (d + i)
    (dayNow z d now (clipDays z d now g) i) g u
  have one : ∀ i j, i < clipDays z d now g → j < clipDays z d now g →
      ((∃ q ∈ segSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ coveredSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g, q.1 ≤ u ∧ u < q.2)) →
      ((∃ q ∈ segSpans z ix (d + j) (dayNow z d now (clipDays z d now g) j) g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ coveredSpans z ix (d + j) (dayNow z d now (clipDays z d now g) j) g, q.1 ≤ u ∧ u < q.2)) →
      i = j := by
    intro i j hi hj hdi hdj
    exact a_second_is_in_one_days_part z d now g u hm i j hi hj ((day i).1.1 hdi) ((day j).1.1 hdj)
  refine ⟨⟨?_, ?_⟩, ?_, one⟩
  · rintro (h | h)
    · obtain ⟨i, hi, hq⟩ := (mem_daySpans_iff z ix d now g u).1 h
      exact a_days_part_is_inside_the_clip z d now g u hm i hi ((day i).1.1 (Or.inl hq))
    · obtain ⟨i, hi, hq⟩ := (mem_dayCovered_iff z ix d now g u).1 h
      exact a_days_part_is_inside_the_clip z d now g u hm i hi ((day i).1.1 (Or.inr hq))
  · intro hu
    obtain ⟨i, hi, hpart⟩ := a_second_of_the_clip_is_in_a_days_part z d now g u hu
    rcases (day i).1.2 hpart with hk | hc
    · exact Or.inl ((mem_daySpans_iff z ix d now g u).2 ⟨i, hi, hk⟩)
    · exact Or.inr ((mem_dayCovered_iff z ix d now g u).2 ⟨i, hi, hc⟩)
  · rintro ⟨hk, hc⟩
    obtain ⟨i, hi, hki⟩ := (mem_daySpans_iff z ix d now g u).1 hk
    obtain ⟨j, hj, hcj⟩ := (mem_dayCovered_iff z ix d now g u).1 hc
    have hij := one i j hi hj (Or.inl hki) (Or.inr hcj)
    subst hij
    exact (day i).2 ⟨hki, hcj⟩

/-- **A second is covered exactly when a wall of its own calendar day covers it** — the wall
`Planner.wallsOfDay` places for that day, clipped to it — for a Pause, and whatever the zone does. -/
theorem a_second_is_covered_iff_a_wall_of_its_own_day_covers_it (z : Cal.Tz) (ix : List Look.WallIx)
    (d now : Nat) (g : Replay.Segment) (i : Id) (hg : g.kind = .pause i) (u : Nat) :
    (∃ q ∈ dayCovered z ix d now g, q.1 ≤ u ∧ u < q.2) ↔
      ∃ j, j < clipDays z d now g ∧
        (max g.start.1.sec (Cal.instantOf z (d + j) 0).sec ≤ u ∧
          u < min g.stop.1.sec (dayNow z d now (clipDays z d now g) j)) ∧
        ∃ w ∈ Planner.wallsOfDay (Cal.instantOf z (d + j) 0).sec (Cal.instantOf z (d + j + 1) 0).sec
            (d + j) ix, w.lo ≤ u ∧ u < w.hi := by
  rw [mem_dayCovered_iff]
  constructor
  · rintro ⟨j, hj, hc⟩
    exact ⟨j, hj, (a_second_is_covered_iff_a_wall_of_the_day_covers_it z ix (d + j)
      (dayNow z d now (clipDays z d now g) j) g i hg u).1 hc⟩
  · rintro ⟨j, hj, hw⟩
    exact ⟨j, hj, (a_second_is_covered_iff_a_wall_of_the_day_covers_it z ix (d + j)
      (dayNow z d now (clipDays z d now g) j) g i hg u).2 hw⟩

/-- **In a zone near UTC the partition needs no hypothesis** — `Cal.instantOf_midnights_rise` gives the
rising midnights, so every second of the clip is drawn once, by its own day's walls. -/
theorem the_grid_cuts_every_second_once_in_a_zone_near_utc (z : Cal.Tz) (ix : List Look.WallIx)
    (d now : Nat) (g : Replay.Segment)
    (hnear : ∀ a ∈ z.val.base :: z.val.trans.map Prod.snd, ∀ b ∈ z.val.base :: z.val.trans.map Prod.snd,
      (if b.west then -(b.sec : Int) else (b.sec : Int)) -
        (if a.west then -(a.sec : Int) else (a.sec : Int)) < 75600)
    (hsmall : ∀ a ∈ z.val.base :: z.val.trans.map Prod.snd,
      -75600 < (if a.west then -(a.sec : Int) else (a.sec : Int)) ∧
        (if a.west then -(a.sec : Int) else (a.sec : Int)) < 75600) (u : Nat) :
    (((∃ q ∈ daySpans z ix d now g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ dayCovered z ix d now g, q.1 ≤ u ∧ u < q.2)) ↔
      (max g.start.1.sec (Cal.instantOf z d 0).sec ≤ u ∧ u < min g.stop.1.sec now)) ∧
    ¬ ((∃ q ∈ daySpans z ix d now g, q.1 ≤ u ∧ u < q.2) ∧
        (∃ q ∈ dayCovered z ix d now g, q.1 ≤ u ∧ u < q.2)) :=
  let h := the_grid_draws_every_second_of_the_clip_once_day_by_day z ix d now g
    (fun j _ => Nat.le_of_lt (Cal.instantOf_midnights_rise z (d + j) hnear hsmall)) u
  ⟨h.1, h.2.1⟩

/-- **A Pause inside its day is cut exactly as P63 cut it** — when the clip's last second falls on the
record's own day, the composition is that day's `segSpans` and `coveredSpans`, unchanged. -/
theorem the_cut_inside_its_day_is_unchanged (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat)
    (g : Replay.Segment) (h : Cal.localDate z ⟨min g.stop.1.sec now - 1, 0⟩ ≤ d) :
    daySpans z ix d now g = segSpans z ix d now g ∧ dayCovered z ix d now g = coveredSpans z ix d now g := by
  have hn : clipDays z d now g = 1 := by
    unfold clipDays
    omega
  unfold daySpans dayCovered
  rw [hn]
  simp [dayNow]

/-! ## The cut, run (AGENTS §5.2) -/

/-- **The same call in Chicago**, a zone with an offset and transitions (CDT, five hours west): `^g9` from
23:30 Tuesday 2026-09-08 to 00:30 Wednesday, local, and D61's Pause over exactly the call, read at 00:50.
P63's cut keeps the half after local midnight as the pause; the day-by-day cut covers the whole Pause,
Tuesday's half by Tuesday's part of the call and Wednesday's by Wednesday's (the drive's world, README
"Stage 6 — W-40, track T"). -/
theorem the_call_past_midnight_is_its_days_wall_in_chicago :
    segSpans Cal.chicago [⟨['g','9'], 739866, 739867, 63924525000, 63924525000, 63924528600⟩] 739866 63924529800
        ⟨(⟨63924525000, 0⟩, ⟨true, 18000⟩), (⟨63924528600, 0⟩, ⟨true, 18000⟩), .pause ['t','4']⟩
      = [(63924526800, 63924528600)] ∧
    daySpans Cal.chicago [⟨['g','9'], 739866, 739867, 63924525000, 63924525000, 63924528600⟩] 739866 63924529800
        ⟨(⟨63924525000, 0⟩, ⟨true, 18000⟩), (⟨63924528600, 0⟩, ⟨true, 18000⟩), .pause ['t','4']⟩ = [] ∧
    dayCovered Cal.chicago [⟨['g','9'], 739866, 739867, 63924525000, 63924525000, 63924528600⟩] 739866 63924529800
        ⟨(⟨63924525000, 0⟩, ⟨true, 18000⟩), (⟨63924528600, 0⟩, ⟨true, 18000⟩), .pause ['t','4']⟩
      = [(63924525000, 63924526800), (63924526800, 63924528600)] := by
  decide

/-- **The day-by-day cut, run where the call does not cover the whole Pause**: the same call, a Pause
from 23:20 Monday to 00:50 Tuesday at `now` 00:40 — Monday's part keeps 23:20–23:30 and covers
23:30–00:00, Tuesday's covers 00:00–00:30 and keeps 00:30 to `now`; a block over the same span is kept
whole on each day; and a Pause no wall touches is kept, day by day. -/
theorem the_day_by_day_cut_is_run :
    daySpans Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924424800
        ⟨(⟨63924420000, 0⟩, Cal.Offset.utc), (⟨63924425400, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924420000, 63924420600), (63924424200, 63924424800)] ∧
    dayCovered Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924424800
        ⟨(⟨63924420000, 0⟩, Cal.Offset.utc), (⟨63924425400, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924420600, 63924422400), (63924422400, 63924424200)] ∧
    daySpans Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924424800
        ⟨(⟨63924420000, 0⟩, Cal.Offset.utc), (⟨63924425400, 0⟩, Cal.Offset.utc), .block ['t','4']⟩
      = [(63924420000, 63924422400), (63924422400, 63924424800)] ∧
    dayCovered Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924424800
        ⟨(⟨63924420000, 0⟩, Cal.Offset.utc), (⟨63924425400, 0⟩, Cal.Offset.utc), .block ['t','4']⟩
      = [] ∧
    daySpans Replay.utcZone [] 739865 63924424800
        ⟨(⟨63924420000, 0⟩, Cal.Offset.utc), (⟨63924425400, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924420000, 63924422400), (63924422400, 63924424800)] := by
  decide

end GridCut
end Tm
