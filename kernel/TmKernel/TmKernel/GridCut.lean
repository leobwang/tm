import TmKernel.WallTimer
import TmKernel.Planner

/-!
# GridCut — the week grid cuts a pause with the planner's cut (stage 6, W-39 track T, README gaps 3432 and 3528)

**The defect.**  P56's cut — the part of a replayed `Pause` a wall of its day covers is the wall's, and the
rest stays the pause (the owner's D65, and the campaign's D69 call on README gap 3244) — was written twice:
in the day plan's past half, `Planner.pastSpans`, over the walls §8.2 step 1 places (`Planner.wallsOfDay`,
`Look.wallIxOn`'s selection); and in the host's week grid, `review::heat_of`'s own heat_pieces (deleted
here), over the host's own reader of the calendar (`Tree::walls_on`) and `capacity::free_intervals`.  Two definitions of one cut, and two
readers of the walls deciding one span's drawing (AGENTS §5.3).  Since the W-38 repair they were compared on
three days (`cli_week_grid`), never made one (README gap 3528, with gap 3432 its walls reader).

**Here they are one.**  `segSpans` is `Planner.pastSpans`' own composition — `Planner.clipCut` of the
segment's clip to `[local midnight, now]` by `Planner.wallsOfDay`'s walls, for a Pause — for a day the
planner is not planning, and `pastSpans_is_segSpans` says the planner's cut IS `segSpans` at the day it
plans, by `rfl`: change either and this module stops building.  It is not a third body of the cut or of
the wall selection: `clipCut` and `wallsOfDay` are called, not re-spelled.  The week grid asks for it
through the `emit` section's walls form (`Boundary.wallsEmit`) with a `week` key: `answer` is
`WallTimer.answer`, unchanged when the key is absent (`answer_without_a_week`), and with it the cut of
every Pause the replay's day records hold in that ISO week (`cutJson`) — what stays a pause
(`segSpans`) and what the grid draws as the wall (`coveredSpans`).  The host keeps no cut and no wall
reader of its own for the grid: its heat_pieces and the grid's `Tree::walls_on` read are deleted.

**The laws, in the units the grid counts** (whole seconds, as the planner's clip is).  `in_clipCut_iff`
says exactly which seconds `Planner.clipCut` keeps — those of the clip no span covers — from which the
grid's partition follows: every second of a segment's clip is drawn once, kept or covered and never both
(`the_grid_draws_every_second_of_the_clip_once`); a second is covered exactly when a wall of the day
covers it and the segment is a Pause (`a_second_is_covered_iff_a_wall_of_the_day_covers_it`); nothing
but a Pause is covered (`nothing_but_a_pause_is_covered`).  `the_cut_is_run`, `readWeek_is_run` and
`the_weeks_cut_is_answered` run them (AGENTS §5.2).

**What the move changes** — parity **P63**, README "Stage 6 — W-39, track T" — is exactly the planner's
clip: a Pause of day `d`'s record is cut by `d`'s walls clipped to `d` and clipped itself to
`[local midnight of d, now]`, where the host's cut took the segment whole and the walls unclipped.  The
two agree on every Pause that lies inside its own day before `now`; they part only across local midnight
(and past `now`), which the census in the README block measures.

**And since W-40 each calendar day's part is cut by that day's walls** — the campaign's D77 call on README
gap 3620, parity P63 restated.  The wire answers `daySpans` and `dayCovered`: `segSpans` and
`coveredSpans` at every day the clip reaches, each at that day's own `dayNow` (its next midnight or
`now`), so the half of a midnight-crossing meeting after midnight is the wall again — the next day's —
as the next day's plan draws it.  `segSpans` is unchanged and is still the planner's cut by `rfl`
(`pastSpans_is_segSpans`); a Pause inside its day is cut exactly as before
(`the_cut_inside_its_day_is_unchanged`), and the partition laws over the days, with the `Cal` lemma
that the midnights rise, are `MidnightCut.lean`'s.
-/

namespace Tm
namespace GridCut

/-! ## The cut, one definition -/

/-- **A replayed segment's spans on day `d` at `now`** — `Planner.pastSpans`' composition for a day it
is not planning: its clip to `[local midnight of d, now]`, and for a Pause, the walls of `d` as §8.2
step 1 places them (`Planner.wallsOfDay`) cut out of it (`Planner.clipCut`). -/
def segSpans (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment) : List (Nat × Nat) :=
  Planner.clipCut (max g.start.1.sec (Cal.instantOf z d 0).sec) (min g.stop.1.sec now)
    (match g.kind with
     | .pause _ => (Planner.wallsOfDay (Cal.instantOf z d 0).sec (Cal.instantOf z (d + 1) 0).sec d ix).map
         (fun w => (w.lo, w.hi))
     | _ => [])

/-- **The planner's cut is this one, at the day it plans** (README gaps 3432 and 3528): the week grid
and the day plan read one definition, and one selection of the walls. -/
theorem pastSpans_is_segSpans (r : Planner.PlanReq) (g : Replay.Segment) :
    Planner.pastSpans r g = segSpans r.tz r.look.walls r.today r.now.sec g := rfl

/-- **What a wall covers of a segment on day `d`**: its clip with the spans `segSpans` keeps cut out of
it — for a Pause, the stretches under a wall of the day, which the week grid draws as the wall (D65's
"the wall alone", the campaign's D69 call on README gap 3244); for any other kind, nothing
(`nothing_but_a_pause_is_covered`). -/
def coveredSpans (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment) : List (Nat × Nat) :=
  Planner.clipCut (max g.start.1.sec (Cal.instantOf z d 0).sec) (min g.stop.1.sec now) (segSpans z ix d now g)

/-! ## Which seconds a cut keeps -/

/-- **One span cut out of one piece keeps the piece's seconds the span does not cover.** -/
theorem in_cutOne_iff (s p : Nat × Nat) (u : Nat) :
    (∃ q ∈ Planner.cutOne s p, q.1 ≤ u ∧ u < q.2) ↔ (p.1 ≤ u ∧ u < p.2) ∧ ¬ (s.1 ≤ u ∧ u < s.2) := by
  unfold Planner.cutOne
  split
  · rename_i hs
    simp only [List.mem_singleton, exists_eq_left]
    exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
  · rename_i hs
    simp only [List.mem_append]
    constructor
    · rintro ⟨q, hq | hq, h1, h2⟩
      · split at hq
        · simp only [List.mem_singleton] at hq; subst hq; omega
        · simp at hq
      · split at hq
        · simp only [List.mem_singleton] at hq; subst hq; omega
        · simp at hq
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hu : u < s.1
      · refine ⟨(p.1, min p.2 s.1), Or.inl ?_, h1, by omega⟩
        rw [if_pos (by omega)]; exact List.mem_singleton_self _
      · refine ⟨(max p.1 s.2, p.2), Or.inr ?_, by omega, h2⟩
        rw [if_pos (by omega)]; exact List.mem_singleton_self _

/-- **Every span cut out of every piece keeps the pieces' seconds no span covers.** -/
theorem in_cutAll_iff (ss ps : List (Nat × Nat)) (u : Nat) :
    (∃ q ∈ Planner.cutAll ss ps, q.1 ≤ u ∧ u < q.2) ↔
      (∃ p ∈ ps, p.1 ≤ u ∧ u < p.2) ∧ ∀ s ∈ ss, ¬ (s.1 ≤ u ∧ u < s.2) := by
  induction ss generalizing ps with
  | nil => simp [Planner.cutAll]
  | cons s ss ih =>
    simp only [Planner.cutAll]
    rw [ih]
    constructor
    · rintro ⟨⟨q, hq, hu⟩, hall⟩
      obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
      have h := (in_cutOne_iff s p u).1 ⟨q, hq, hu⟩
      refine ⟨⟨p, hp, h.1⟩, fun s' hs' => ?_⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact h.2
      · exact hall s' hs'
    · rintro ⟨⟨p, hp, hu⟩, hall⟩
      obtain ⟨q, hq, hqu⟩ := (in_cutOne_iff s p u).2 ⟨hu, hall s (List.mem_cons_self ..)⟩
      exact ⟨⟨q, List.mem_flatMap.2 ⟨p, hp, hq⟩, hqu⟩, fun s' hs' => hall s' (List.mem_cons_of_mem _ hs')⟩

/-- **`Planner.clipCut` keeps exactly the seconds of the clip no span covers** — the law
`Planner.clipCut_within` and `Planner.clipCut_apart` state one direction of, in both. -/
theorem in_clipCut_iff (a b : Nat) (ss : List (Nat × Nat)) (u : Nat) :
    (∃ q ∈ Planner.clipCut a b ss, q.1 ≤ u ∧ u < q.2) ↔
      (a ≤ u ∧ u < b) ∧ ∀ s ∈ ss, ¬ (s.1 ≤ u ∧ u < s.2) := by
  unfold Planner.clipCut
  split
  · rename_i h
    constructor
    · rintro ⟨q, hq, _⟩; simp at hq
    · rintro ⟨⟨h1, h2⟩, _⟩; omega
  · rw [in_cutAll_iff]
    simp

/-! ## The grid's partition -/

/-- **Every second of a segment's clip is drawn once**: kept or covered, never both, and nothing
outside the clip. -/
theorem the_grid_draws_every_second_of_the_clip_once (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat)
    (g : Replay.Segment) (u : Nat) :
    (((∃ q ∈ segSpans z ix d now g, q.1 ≤ u ∧ u < q.2) ∨
        (∃ q ∈ coveredSpans z ix d now g, q.1 ≤ u ∧ u < q.2)) ↔
      (max g.start.1.sec (Cal.instantOf z d 0).sec ≤ u ∧ u < min g.stop.1.sec now)) ∧
    ¬ ((∃ q ∈ segSpans z ix d now g, q.1 ≤ u ∧ u < q.2) ∧
        (∃ q ∈ coveredSpans z ix d now g, q.1 ≤ u ∧ u < q.2)) := by
  have hc := in_clipCut_iff (max g.start.1.sec (Cal.instantOf z d 0).sec) (min g.stop.1.sec now)
    (segSpans z ix d now g) u
  unfold coveredSpans
  rw [hc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (⟨q, hq, hu⟩ | ⟨hu, _⟩)
    · exact (by unfold segSpans at hq; exact ((in_clipCut_iff _ _ _ u).1 ⟨q, hq, hu⟩).1)
    · exact hu
  · intro hu
    by_cases hk : ∃ q ∈ segSpans z ix d now g, q.1 ≤ u ∧ u < q.2
    · exact Or.inl hk
    · exact Or.inr ⟨hu, fun s hs hsu => hk ⟨s, hs, hsu⟩⟩
  · rintro ⟨⟨q, hq, hu⟩, _, hnot⟩
    exact hnot q hq hu

/-- **A second of a Pause's clip is covered exactly when a wall of the day covers it** — the wall
`Planner.wallsOfDay` places for the day, clipped to it. -/
theorem a_second_is_covered_iff_a_wall_of_the_day_covers_it (z : Cal.Tz) (ix : List Look.WallIx)
    (d now : Nat) (g : Replay.Segment) (i : Id) (hg : g.kind = .pause i) (u : Nat) :
    (∃ q ∈ coveredSpans z ix d now g, q.1 ≤ u ∧ u < q.2) ↔
      (max g.start.1.sec (Cal.instantOf z d 0).sec ≤ u ∧ u < min g.stop.1.sec now) ∧
      ∃ w ∈ Planner.wallsOfDay (Cal.instantOf z d 0).sec (Cal.instantOf z (d + 1) 0).sec d ix,
        w.lo ≤ u ∧ u < w.hi := by
  unfold coveredSpans
  rw [in_clipCut_iff]
  constructor
  · rintro ⟨hu, hk⟩
    refine ⟨hu, ?_⟩
    have hk' : ¬ ∃ q ∈ segSpans z ix d now g, q.1 ≤ u ∧ u < q.2 := fun ⟨q, hq, hqu⟩ => hk q hq hqu
    unfold segSpans at hk'
    rw [in_clipCut_iff, hg] at hk'
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk'
    exact Classical.byContradiction fun hn => hk' ⟨hu, fun w hw hwu => hn ⟨w, hw, hwu⟩⟩
  · rintro ⟨hu, w, hw, hwu⟩
    refine ⟨hu, fun q hq hqu => ?_⟩
    unfold segSpans at hq
    have := ((in_clipCut_iff _ _ _ u).1 ⟨q, hq, hqu⟩).2
    rw [hg] at this
    exact this (w.lo, w.hi) (List.mem_map.2 ⟨w, hw, rfl⟩) hwu

/-- **Nothing but a Pause is covered**: a Block, a Break, an interruption, a routine or an idle mark
is drawn over its whole clip, as the planner draws it. -/
theorem nothing_but_a_pause_is_covered (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat)
    (g : Replay.Segment) (hg : ∀ i, g.kind ≠ .pause i) : coveredSpans z ix d now g = [] := by
  have hs : segSpans z ix d now g =
      Planner.clipCut (max g.start.1.sec (Cal.instantOf z d 0).sec) (min g.stop.1.sec now) [] := by
    unfold segSpans
    cases hk : g.kind with
    | pause i => exact absurd hk (hg i)
    | _ => rfl
  unfold coveredSpans
  rw [hs, Planner.clipCut_nil]
  unfold Planner.clipCut
  split
  · rfl
  · rename_i h
    simp only [Planner.cutAll, List.flatMap_cons, List.flatMap_nil, List.append_nil, Planner.cutOne]
    split
    · omega
    · simp <;> omega

/-! ## Each calendar day's part, cut by its own walls (the campaign's D77 call on README gap 3620)

A Pause of day `d`'s record can run past `d`'s next local midnight — a block run into a call that
crosses midnight with it, D61 pausing it over the call — and `segSpans` cuts the whole of it by `d`'s
walls clipped to `d`, so the part after midnight was drawn `pause` (parity P63 as issued) while the
next day's plan draws the same minutes as that day's wall row.  One span, two readings (AGENTS §5.3),
and against D65's "the wall alone" as D69's call carried it to the grid.  **D77: each calendar day's
part of the clip is cut by that day's own walls** — `segSpans` itself, at each day `d + i` the clip
reaches, its `now` the next midnight or `now`, whichever is first, and `now` itself on the last day.
`clipCut` and `wallsOfDay` are still called, never re-spelled, and a Pause inside its day is cut
exactly as before (`the_cut_inside_its_day_is_unchanged`).  The partition laws, that theorem and the
`Cal` lemma they rest on are `MidnightCut.lean`'s. -/

/-- **The calendar days a segment's clip at `now` reaches from `d`**: through the local date of the
clip's last second, and never fewer than one — day `d` itself, whose part is `segSpans`' clip. -/
def clipDays (z : Cal.Tz) (d now : Nat) (g : Replay.Segment) : Nat :=
  max 1 (Cal.localDate z ⟨min g.stop.1.sec now - 1, 0⟩ + 1 - d)

/-- **Day `d + i`'s `now`, of `n` days**: the next local midnight, or `now` if it comes first — and
`now` itself on the last day, so no part of the clip past it is dropped. -/
def dayNow (z : Cal.Tz) (d now n i : Nat) : Nat :=
  if i + 1 < n then min now (Cal.instantOf z (d + i + 1) 0).sec else now

/-- **What stays a pause, day by day** (D77): each calendar day's part of the segment's clip with that
day's walls cut out — `segSpans` at day `d + i`, at its own `dayNow`. -/
def daySpans (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment) : List (Nat × Nat) :=
  (List.range (clipDays z d now g)).flatMap fun i =>
    segSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g

/-- **What a wall covers, day by day** (D77): `coveredSpans` at each day's part — the stretches under a
wall of the calendar day they fall on, which the grid draws as the wall. -/
def dayCovered (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment) : List (Nat × Nat) :=
  (List.range (clipDays z d now g)).flatMap fun i =>
    coveredSpans z ix (d + i) (dayNow z d now (clipDays z d now g) i) g

/-! ## The wire: the `emit` section's walls form, with a week -/

/-- **The walls form's refusals, with the week's**: `WallTimer.Refusal` unchanged, and one more. -/
inductive Refusal
  /-- one of the walls form's own (`WallTimer.Refusal`), unchanged -/
  | walls (r : WallTimer.Refusal)
  /-- `emit.walls.week` present and neither `null` nor a `YYYY-MM-DD` date the kernel's date grammar reads -/
  | badWeek
deriving DecidableEq, Repr

/-- `{"err":{"emit":{"walls":<name>}}}`, the walls form's own shape. -/
def Refusal.json : Refusal → JVal
  | .walls r => r.json
  | .badWeek => jone "err" (jone "emit" (jone "walls" (.str "badWeek".toList)))

/-- **`emit.walls.week`**: absent or `null` asks for no cut; a date read by the kernel's one date grammar
(`Field.parseDate`, the reader of the request's `now`) asks for the cut of that date's ISO week.  A walls
form that is not an object is `WallTimer.readReq`'s to refuse, and is refused before this is read. -/
def readWeek (v : JVal) : Except Refusal (Option Nat) :=
  match jget v "walls" with
  | .ok (some w@(.obj _)) =>
    match jget w "week" with
    | .ok none | .ok (some .null) => .ok none
    | .ok (some (.str s)) =>
      match Field.parseDate s with
      | some d => .ok (some d)
      | none => .error .badWeek
    | _ => .error .badWeek
  | _ => .ok none

/-- Whether a replayed segment is a Pause — the one kind the grid's cut draws in two styles. -/
def isPause (g : Replay.Segment) : Bool :=
  match g.kind with
  | .pause _ => true
  | _ => false

/-- A span `[lo, hi)`, on the wire, in the kernel's absolute seconds (from 0001-01-01). -/
def cutPieceJson (q : Nat × Nat) : JVal := .arr [.num q.1, .num q.2]

/-- **One Pause's cut, on the wire**: its own `[from, to)` in whole seconds — the key the host finds its
segment by — then what stays a pause and what a wall covers, each calendar day's part by that day's
walls (D77, README gap 3620: `daySpans` and `dayCovered`, where W-39 sent `segSpans` and
`coveredSpans` of the record's day alone). -/
def cutPauseJson (z : Cal.Tz) (ix : List Look.WallIx) (d now : Nat) (g : Replay.Segment) : JVal :=
  .obj [("from".toList, .num g.start.1.sec), ("to".toList, .num g.stop.1.sec),
    ("pause".toList, .arr ((daySpans z ix d now g).map cutPieceJson)),
    ("wall".toList, .arr ((dayCovered z ix d now g).map cutPieceJson))]

/-- **One day of the week, on the wire**: its date, and the cut of every Pause its record holds, in the
record's order. -/
def cutDayJson (z : Cal.Tz) (ix : List Look.WallIx) (now : Nat) (r : Seal.DayRecord) (a : Replay.DayAcc) :
    JVal :=
  .obj [("day".toList, .str (Field.renderDate r.day)),
    ("pauses".toList, .arr ((a.segments.filter isPause).map (cutPauseJson z ix r.day now)))]

/-- **The week's cut** (README gaps 3432 and 3528): every day record of the replay whose day is in `w`'s
ISO week — `Cal.weekOrdinal`, the week grain's own index — in the replay's order. -/
def cutJson (z : Cal.Tz) (ix : List Look.WallIx) (now w : Nat) (f : Seal.Answer) : JVal :=
  .arr (f.days.filterMap fun r =>
    if Cal.weekOrdinal r.day = Cal.weekOrdinal w then r.record.map (cutDayJson z ix now r) else none)

/-- The walls form's answer with the week's cut after it. -/
def withCut (a c : JVal) : JVal :=
  match a with
  | .obj kvs => .obj (kvs ++ [("cut".toList, c)])
  | x => x

/-- **The walls form, with a week** (README gaps 3432 and 3528): `WallTimer.answer` over the request's
replay, zone, walls and clock, refused by its own name; then, when `week` asks, the week's cut after it,
at `at` — the instant the walls form already reads. -/
def answer (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (cmds : Nat) (today : Option Nat) (bm : Option Nat) :
    Except Refusal JVal :=
  match WallTimer.answer v zo facts ixOf cmds today bm with
  | .error r => .error (.walls r)
  | .ok a =>
    match readWeek v, facts, zo, bm, WallTimer.readReq v with
    | .error r, _, _, _, _ => .error r
    | .ok (some w), some f, some z, some b, .ok q =>
      .ok (withCut a (cutJson z (ixOf z b) q.at_.1.val.sec w f))
    | _, _, _, _, _ => .ok a

/-! ## The wire's laws -/

/-- **Without a `week` the walls form is answered as before, byte for byte** — `WallTimer.answer`, its
refusals under their own names. -/
theorem answer_without_a_week (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (hw : readWeek v = .ok none) :
    answer v zo facts ixOf n d b =
      match WallTimer.answer v zo facts ixOf n d b with
      | .ok a => .ok a
      | .error r => .error (.walls r) := by
  unfold answer
  cases WallTimer.answer v zo facts ixOf n d b <;> simp [hw]

/-- **A walls answer came from a request that had them all**: the form read, the replay, the zone and
the block length. -/
theorem walls_answer_had_its_inputs (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (a : JVal)
    (h : WallTimer.answer v zo facts ixOf n d b = .ok a) :
    (∃ q, WallTimer.readReq v = .ok q) ∧ (∃ f, facts = some f) ∧ (∃ z, zo = some z) ∧
      (∃ bm, b = some bm) := by
  unfold WallTimer.answer at h
  cases hq : WallTimer.readReq v with
  | error e => simp [hq, bind, Except.bind] at h
  | ok q =>
    cases facts with
    | none => simp [hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some f =>
      cases zo with
      | none => simp [hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
      | some z =>
        cases d with
        | none => simp [hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
        | some dd =>
          cases b with
          | none => simp [hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
          | some bb => exact ⟨⟨q, rfl⟩, ⟨f, rfl⟩, ⟨z, rfl⟩, ⟨bb, rfl⟩⟩

/-- **A week asked is a week answered**: when the walls form answers, the `week` it reads puts that
week's cut after it — no request the walls form accepts drops it. -/
theorem a_week_asked_is_answered (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (a : JVal) (w : Nat)
    (h : WallTimer.answer v zo facts ixOf n d b = .ok a) (hw : readWeek v = .ok (some w)) :
    ∃ f z bm q, facts = some f ∧ zo = some z ∧ b = some bm ∧ WallTimer.readReq v = .ok q ∧
      answer v zo facts ixOf n d b = .ok (withCut a (cutJson z (ixOf z bm) q.at_.1.val.sec w f)) := by
  obtain ⟨⟨q, hq⟩, ⟨f, rfl⟩, ⟨z, rfl⟩, ⟨bm, rfl⟩⟩ := walls_answer_had_its_inputs v zo facts ixOf n d b a h
  exact ⟨f, z, bm, q, rfl, rfl, rfl, hq, by unfold answer; rw [h]; simp [hw, hq]⟩

/-- **A malformed `week` is refused by name**, after the walls form's own refusals. -/
theorem a_bad_week_is_refused_by_name (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (a : JVal)
    (h : WallTimer.answer v zo facts ixOf n d b = .ok a) (hw : readWeek v = .error .badWeek) :
    answer v zo facts ixOf n d b = .error .badWeek := by
  unfold answer; rw [h]; simp [hw]

/-- **Without a replay there is no answer** — `WallTimer.answer_refuses_without_the_replay`, carried:
the week's cut never reads a blank as a fact (D24). -/
theorem answer_refuses_without_the_replay (v : JVal) (zo : Option Cal.Tz)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (q : WallTimer.Req)
    (hq : WallTimer.readReq v = .ok q) :
    answer v zo none ixOf n d b = .error (.walls .logAbsent) := by
  unfold answer
  rw [WallTimer.answer_refuses_without_the_replay v zo ixOf n d b q hq]

/-- **The refusal spells itself** (§5.7), in the walls form's shape. -/
theorem the_week_refusal_is_the_err_emit_shape :
    jemit (Refusal.json .badWeek) = "{\"err\":{\"emit\":{\"walls\":\"badWeek\"}}}".toList ∧
    Refusal.json (.walls .logAbsent) = WallTimer.Refusal.json .logAbsent := by
  exact ⟨by decide, rfl⟩

/-! ## The cut and the wire, run (AGENTS §5.2: non-vacuity is a separate check from correctness)

Monday 2026-09-07 in UTC — day 739,865, local midnight at second 63,924,336,000 — with the calendar's
`^g1` meeting 12:50–13:50: the instants are written as literals, not through a helper, because a helper
is a definition the export does not reach (README gap 3333; D51). -/

/-- **The cut, run** (the three days `cli_week_grid` drives, and the edges the planner's clip draws): a
typed pause 12:40–14:00 straddling the meeting keeps 12:40–12:50 and 13:50–14:00 and the meeting's hour is
covered; a pause no wall touches (09:10–09:30) is kept whole and nothing covered; a block through the
meeting is kept whole — the cut is a Pause's alone; a pause begun before the day's midnight is clipped at
it; and a pause crossing into the next day under a wall that crosses with it keeps the part after
midnight, because the planner's walls are the day's, clipped to it (parity P63 as issued: this is the
planner's cut, and since the campaign's D77 call the grid's is `daySpans`, which covers that part by
the next day's walls — `the_call_past_midnight_is_its_days_wall`). -/
theorem the_cut_is_run :
    segSpans Replay.utcZone [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩] 739865 63924390000
        ⟨(⟨63924381600, 0⟩, Cal.Offset.utc), (⟨63924386400, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924381600, 63924382200), (63924385800, 63924386400)] ∧
    coveredSpans Replay.utcZone [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩] 739865 63924390000
        ⟨(⟨63924381600, 0⟩, Cal.Offset.utc), (⟨63924386400, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924382200, 63924385800)] ∧
    segSpans Replay.utcZone [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩] 739865 63924390000
        ⟨(⟨63924369000, 0⟩, Cal.Offset.utc), (⟨63924370200, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924369000, 63924370200)] ∧
    coveredSpans Replay.utcZone [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩] 739865 63924390000
        ⟨(⟨63924369000, 0⟩, Cal.Offset.utc), (⟨63924370200, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [] ∧
    segSpans Replay.utcZone [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩] 739865 63924390000
        ⟨(⟨63924379200, 0⟩, Cal.Offset.utc), (⟨63924386400, 0⟩, Cal.Offset.utc), .block ['t','4']⟩
      = [(63924379200, 63924386400)] ∧
    coveredSpans Replay.utcZone [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩] 739865 63924390000
        ⟨(⟨63924379200, 0⟩, Cal.Offset.utc), (⟨63924386400, 0⟩, Cal.Offset.utc), .block ['t','4']⟩
      = [] ∧
    segSpans Replay.utcZone [] 739865 63924390000
        ⟨(⟨63924335400, 0⟩, Cal.Offset.utc), (⟨63924336600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924336000, 63924336600)] ∧
    segSpans Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924500000
        ⟨(⟨63924421200, 0⟩, Cal.Offset.utc), (⟨63924423600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924422400, 63924423600)] ∧
    coveredSpans Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924500000
        ⟨(⟨63924421200, 0⟩, Cal.Offset.utc), (⟨63924423600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924421200, 63924422400)] := by
  decide

/-- **`week`, read** — absent or `null` asks for no cut, a date asks for its ISO week, and anything
else is refused by name: `2026-02-30`, a number, and a date in another spelling. -/
theorem readWeek_is_run :
    (match readWeek (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T15:00:00Z".toList)])]) with
      | .ok none => true | _ => false) = true ∧
    (match readWeek (.obj [("walls".toList, .obj [("week".toList, .null)])]) with
      | .ok none => true | _ => false) = true ∧
    (match readWeek (.obj [("walls".toList, .obj [("week".toList, .str "2026-09-07".toList)])]) with
      | .ok (some 739865) => true | _ => false) = true ∧
    (match readWeek (.obj [("walls".toList, .obj [("week".toList, .str "2026-02-30".toList)])]) with
      | .error .badWeek => true | _ => false) = true ∧
    (match readWeek (.obj [("walls".toList, .obj [("week".toList, .num 739865)])]) with
      | .error .badWeek => true | _ => false) = true ∧
    (match readWeek (.obj [("walls".toList, .obj [("week".toList, .str "2026-9-7".toList)])]) with
      | .error .badWeek => true | _ => false) = true := by
  decide

/-- **The call past midnight is its day's wall** (D77, README gap 3620), and the theorem that separates
the rule from the one it replaces (AGENTS §4's last row): Monday 2026-09-07 in UTC, a call `^g2` from
23:30 to 00:30 Tuesday, and a Pause of Monday's record from 23:40 to 00:20.  P63's cut (`segSpans`, the
record's day alone) keeps the twenty minutes after midnight as the pause; the day-by-day cut covers
them by Tuesday's part of the call, so the whole Pause is the wall — two pieces, one per day — and
nothing of it is kept.  The clip reaches two days. -/
theorem the_call_past_midnight_is_its_days_wall :
    segSpans Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924500000
        ⟨(⟨63924421200, 0⟩, Cal.Offset.utc), (⟨63924423600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924422400, 63924423600)] ∧
    clipDays Replay.utcZone 739865 63924500000
        ⟨(⟨63924421200, 0⟩, Cal.Offset.utc), (⟨63924423600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩ = 2 ∧
    daySpans Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924500000
        ⟨(⟨63924421200, 0⟩, Cal.Offset.utc), (⟨63924423600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩ = [] ∧
    dayCovered Replay.utcZone [⟨['g','2'], 739865, 739866, 63924420600, 63924420600, 63924424200⟩] 739865 63924500000
        ⟨(⟨63924421200, 0⟩, Cal.Offset.utc), (⟨63924423600, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩
      = [(63924421200, 63924422400), (63924422400, 63924423600)] := by
  decide

set_option maxRecDepth 8000 in
/-- **The week's cut, answered** (README gaps 3432 and 3528): a replay holding Monday's record — a
block, a typed pause no wall touches (09:10–09:30) and a pause straddling the meeting (12:40–14:00) — a
Tuesday record with no day accumulated, and the next Monday's record with a pause of its own; the walls
form asked at 15:00 for the week of 2026-09-07 answers no mark and no meeting, and then the cut of
Monday's two pauses, in the record's order, and nothing of the next week.  Without `week` it answers
the walls form alone. -/
theorem the_weeks_cut_is_answered :
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T15:00:00Z".toList),
          ("week".toList, .str "2026-09-07".toList)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [],
          [⟨739865, some { Replay.DayAcc.empty with segments :=
              [⟨(⟨63924366000, 0⟩, Cal.Offset.utc), (⟨63924369000, 0⟩, Cal.Offset.utc), .block ['t','4']⟩,
               ⟨(⟨63924369000, 0⟩, Cal.Offset.utc), (⟨63924370200, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩,
               ⟨(⟨63924381600, 0⟩, Cal.Offset.utc), (⟨63924386400, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩] },
             none, [], [], [], [], [], []⟩,
           ⟨739866, none, none, [], [], [], [], [], []⟩,
           ⟨739872, some { Replay.DayAcc.empty with segments :=
              [⟨(⟨63924974400, 0⟩, Cal.Offset.utc), (⟨63924975000, 0⟩, Cal.Offset.utc), .pause ['t','4']⟩] },
             none, [], [], [], [], [], []⟩],
          none, none, none, none, 0, 0, none, [], [], 0⟩)
        (fun _ _ => [⟨['g','1'], 739865, 739865, 63924382200, 63924382200, 63924385800⟩]) 0 (some 739865) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null),
          ("cut".toList, .arr [.obj [("day".toList, .str ['2','0','2','6','-','0','9','-','0','7']),
            ("pauses".toList, .arr [
              .obj [("from".toList, .num 63924369000), ("to".toList, .num 63924370200),
                ("pause".toList, .arr [.arr [.num 63924369000, .num 63924370200]]), ("wall".toList, .arr [])],
              .obj [("from".toList, .num 63924381600), ("to".toList, .num 63924386400),
                ("pause".toList, .arr [.arr [.num 63924381600, .num 63924382200], .arr [.num 63924385800, .num 63924386400]]),
                ("wall".toList, .arr [.arr [.num 63924382200, .num 63924385800]])]])]])]
      | .error _ => false) = true ∧
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T15:00:00Z".toList)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [], none, none, none, none, 0, 0, none, [], [], 0⟩)
        (fun _ _ => []) 0 (some 739865) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]
      | .error _ => false) = true ∧
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T15:00:00Z".toList),
          ("week".toList, .str "2026-13-01".toList)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [], none, none, none, none, 0, 0, none, [], [], 0⟩)
        (fun _ _ => []) 0 (some 739865) (some 60) with
      | .error .badWeek => true | _ => false) = true := by
  decide

end GridCut
end Tm
