import TmKernel.SealWire
import TmKernel.Lookahead

/-!
# WallTimer — the owner's D61, decided by the kernel (stage 6, W-37 track T, README gap 3139)

**D61** (2026-09-27, parity **P53**): a calendar wall that starts while a block runs STOPS THE
TIMER.  The log's own events are written — a `pause{id}` stamped at the wall's start and an
`unpause{id}` at its end — by the housekeeping of the first verb after the wall began (and after
it ended), so `tm now`'s worked minutes, `tm done`'s `actual_min` and the drawn history all net the
meeting out.  W-36 wrote that rule in Rust (`tm/src/cli/day.rs`, `stop_the_timer_at_walls`), over
the host's own reader of the calendar (`Ctx::walls_on`, fork `Ctx::walls_on`) — a SECOND reader of
the walls beside the kernel's `Look.wallsOn`, deciding one day (AGENTS §5.3), and a rule no Lean
statement named, so D40, checks 12 and 13 and the proofs could not see it (gap 3139).

**Here the kernel decides.**  `writes` is the rule, over the replay's own facts — the open block's
start and today's idle marks (`Seal.Answer`, D24's seam) — the day's walls as `Look.wallIxOn`
selects them from the plan the request loaded, joined as fork `merge_walls` joins them
(`Look.mergeSorted` over `Look.sortByStart`, REUSED), the running break `state.json` holds (the
one fact the log does not carry: a break is logged when it ends), and `now`.  The host asks with
the `emit` section's walls form (`Boundary.readEmitSection`), appends the lines the kernel renders
(`Log.emitLine`, D16's one writer), and no longer reads a wall to decide anything.

**The rule, as W-36 wrote it and as the host ran it, port for port** — fork
`tm_core::log::idle_spans` (`idleSpans`), and `day.rs`' timer_stopped_at (`stoppedAt`),
touched_after (`touchedAfter`) and last_timer_mark (`lastTimerMark`), deleted from the host here.  For each joined span
`[lo, hi)` in order: a span that began at or before the block's start, or after `now`, is not the
block's; if no pause is logged at `lo`, the wall writes one there unless the timer was already
stopped at `lo` (a pause, interruption or break covering it, the running break included) or a timer
mark was stamped after `lo` (the user has been deciding since); and once `hi` has passed, it writes
an `unpause` at `hi` if none is logged there and the wall's own pause is still the last word on the
timer.  Its laws are below, each named for the case it is about:
`a_wall_that_starts_while_a_block_runs_stops_its_timer`, and the four ways it writes nothing.
-/

namespace Tm
namespace WallTimer

/-- A mark's instant: its entry's stamp, the offset aside — chrono compares instants. -/
def markAt : Replay.IdleMark → Cal.Instant
  | .pause t | .interrupt t | .unpause t | .resume t | .brk t _ => t.1

/-- Whether a mark is a `break` (the one kind the host's last_timer_mark passed over). -/
def isBrk : Replay.IdleMark → Bool
  | .brk _ _ => true
  | _ => false

/-- Whether a mark is a pause stamped at `t`. -/
def pauseAt (t : Cal.Instant) : Replay.IdleMark → Bool
  | .pause a => a.1 == t
  | _ => false

/-- Whether a mark is an unpause stamped at `t`. -/
def unpauseAt (t : Cal.Instant) : Replay.IdleMark → Bool
  | .unpause a => a.1 == t
  | _ => false

/-- One mark of fork `idle_spans`' pairing: a pause before `started` was another block's; a pause or
interruption opens a span unless one is open; an unpause or resume closes the open one; a break
logged with its length is a span of its own; one logged without is none. -/
def spanStep (started : Cal.Instant) (st : Option Cal.Instant × List (Cal.Instant × Option Cal.Instant))
    (m : Replay.IdleMark) : Option Cal.Instant × List (Cal.Instant × Option Cal.Instant) :=
  match m with
  | .pause t => if t.1 < started then st else (st.1.or (some t.1), st.2)
  | .interrupt t => (st.1.or (some t.1), st.2)
  | .unpause t | .resume t =>
    match st.1 with
    | some a => (none, st.2 ++ [(a, some t.1)])
    | none => st
  | .brk t (some am) => (st.1, st.2 ++ [(t.1, some (Replay.addMinutes t.1 am))])
  | .brk _ none => st

/-- **Fork `idle_spans`** (`tm_core::log`): the spans the block begun at `started` was not worked,
`none` for an end still open — the open pause or interruption, then the running break. -/
def idleSpans (marks : List Replay.IdleMark) (started : Cal.Instant) (brk : Option Cal.Instant) :
    List (Cal.Instant × Option Cal.Instant) :=
  (marks.foldl (spanStep started) (none, [])).2 ++
    ((marks.foldl (spanStep started) (none, [])).1.map (fun a => (a, none))).toList ++
    (brk.map (fun s => (s, none))).toList

/-- **Was the timer stopped at `t`** (the host's timer_stopped_at, W-36): an idle span covers it. -/
def stoppedAt (marks : List Replay.IdleMark) (started t : Cal.Instant) (brk : Option Cal.Instant) : Bool :=
  (idleSpans marks started brk).any fun sp =>
    decide (sp.1 ≤ t) && (match sp.2 with | none => true | some b => decide (t < b))

/-- **Did anything touch the timer after `t`** (the host's touched_after): a mark stamped later. -/
def touchedAfter (marks : List Replay.IdleMark) (t : Cal.Instant) : Bool :=
  marks.any fun m => decide (t < markAt m)

/-- **The last mark that set the timer** (the host's last_timer_mark): the last that is not a break. -/
def lastTimerMark (marks : List Replay.IdleMark) : Option Replay.IdleMark :=
  (marks.filter fun m => !isBrk m).getLast?

/-- Whether the wall's pause at `lo` is still the last word on the timer. -/
def lastIsPauseAt (marks : List Replay.IdleMark) (lo : Cal.Instant) : Bool :=
  match lastTimerMark marks with
  | some m => pauseAt lo m
  | none => false

/-- The mark a written pause or unpause adds (its offset is the wire's business, not the rule's). -/
def markOf (pause : Bool) (t : Cal.Instant) : Replay.IdleMark :=
  if pause then .pause (t, Cal.Offset.utc) else .unpause (t, Cal.Offset.utc)

/-- The pause half of a span: the wall's pause at `lo` is written unless one is logged there. -/
def pauseIfNew (s : Nat × Nat) (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) :
    List Replay.IdleMark × List (Bool × Nat × Nat) :=
  if acc.1.any (pauseAt ⟨s.1, 0⟩) then acc
  else (acc.1 ++ [markOf true ⟨s.1, 0⟩], acc.2 ++ [(true, s)])

/-- The unpause half: once `hi` has passed, an unpause at `hi` is written if none is logged there and
the wall's pause is still the last word on the timer. -/
def unpauseIfDone (now : Cal.Instant) (s : Nat × Nat)
    (a1 : List Replay.IdleMark × List (Bool × Nat × Nat)) :
    List Replay.IdleMark × List (Bool × Nat × Nat) :=
  if (decide ((⟨s.2, 0⟩ : Cal.Instant) ≤ now) && !(a1.1.any (unpauseAt ⟨s.2, 0⟩)) &&
      lastIsPauseAt a1.1 ⟨s.1, 0⟩) = true
  then (a1.1 ++ [markOf false ⟨s.2, 0⟩], a1.2 ++ [(false, s)])
  else a1

/-- **One joined wall span `[lo, hi)`, in whole seconds**, against the marks so far: what it writes,
`(true, span)` for a pause at `lo` and `(false, span)` for an unpause at `hi`, and the marks with
what it wrote appended (the log grows in file order). -/
def step (started now : Cal.Instant) (brk : Option Cal.Instant)
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (s : Nat × Nat) :
    List Replay.IdleMark × List (Bool × Nat × Nat) :=
  if (⟨s.1, 0⟩ : Cal.Instant) ≤ started ∨ now < ⟨s.1, 0⟩ then acc
  else if (!(acc.1.any (pauseAt ⟨s.1, 0⟩)) &&
      (stoppedAt acc.1 started ⟨s.1, 0⟩ brk || touchedAfter acc.1 ⟨s.1, 0⟩)) = true then acc
  else unpauseIfDone now s (pauseIfNew s acc)

/-- **What the day's walls write** (D61, P53), in order: a pause at a span's start, an unpause at
its end, over the block begun at `started`, the log's marks of the day, the running break and
`now`. -/
def writes (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark)
    (spans : List (Nat × Nat)) : List (Bool × Nat × Nat) :=
  (spans.foldl (step started now brk) (marks, [])).2

/-! ## The laws — one span, the day as a user has it -/

theorem inst_le (a b : Nat) : (⟨a, 0⟩ : Cal.Instant) ≤ ⟨b, 0⟩ ↔ a ≤ b := by
  rw [Cal.Instant.le_iff]; simp only; omega

theorem inst_lt (a b : Nat) : (⟨a, 0⟩ : Cal.Instant) < ⟨b, 0⟩ ↔ a < b := by
  rw [Cal.Instant.lt_iff]; simp only; omega

theorem hasUnpause_none_of_untouched (marks : List Replay.IdleMark) (lo hi : Cal.Instant)
    (ht : touchedAfter marks lo = false) (hlt : lo < hi) : marks.any (unpauseAt hi) = false := by
  unfold touchedAfter at ht
  rw [List.any_eq_false] at ht ⊢
  intro m hm hu
  have := ht m hm
  cases m with
  | unpause a =>
    simp only [unpauseAt, beq_iff_eq] at hu
    simp only [markAt] at this
    exact this (decide_eq_true (by rw [hu]; exact hlt))
  | pause a => simp [unpauseAt] at hu
  | interrupt a => simp [unpauseAt] at hu
  | resume a => simp [unpauseAt] at hu
  | brk a b => simp [unpauseAt] at hu

theorem lastIsPauseAt_append (marks : List Replay.IdleMark) (lo : Cal.Instant) :
    lastIsPauseAt (marks ++ [markOf true lo]) lo = true := by
  simp [lastIsPauseAt, lastTimerMark, markOf, isBrk, pauseAt, List.filter_append]

/-- The span's two gates, when the block began before the wall and the wall has begun. -/
theorem step_of_running (started now : Cal.Instant) (brk : Option Cal.Instant)
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (s : Nat × Nat)
    (h1 : started < ⟨s.1, 0⟩) (h2 : (⟨s.1, 0⟩ : Cal.Instant) ≤ now) :
    step started now brk acc s =
      if (!(acc.1.any (pauseAt ⟨s.1, 0⟩)) &&
        (stoppedAt acc.1 started ⟨s.1, 0⟩ brk || touchedAfter acc.1 ⟨s.1, 0⟩)) = true then acc
      else unpauseIfDone now s (pauseIfNew s acc) := by
  have hn : ¬ ((⟨s.1, 0⟩ : Cal.Instant) ≤ started ∨ now < ⟨s.1, 0⟩) := by
    rintro (h | h)
    · exact absurd (Cal.Instant.lt_iff _ _ |>.1 h1) (by rw [Cal.Instant.le_iff] at h; omega)
    · exact absurd h ((Cal.Instant.not_lt _ _).2 h2)
  simp only [step, if_neg hn]

/-- **D61: a wall that starts while a block runs stops its timer at the wall's start** — and, once
the wall has ended, restarts it at its end.  The block began before the wall (`started < lo`), the
wall has begun (`lo ≤ now`), nothing is logged at `lo` yet, the log had the timer RUNNING at `lo`
and nothing has touched it since: the one span writes a pause at `lo`, and an unpause at `hi` when
`hi` has passed. -/
theorem a_wall_that_starts_while_a_block_runs_stops_its_timer (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h1 : started < ⟨lo, 0⟩) (h2 : (⟨lo, 0⟩ : Cal.Instant) ≤ now) (hlh : lo < hi)
    (hp : marks.any (pauseAt ⟨lo, 0⟩) = false) (hs : stoppedAt marks started ⟨lo, 0⟩ brk = false)
    (ht : touchedAfter marks ⟨lo, 0⟩ = false) :
    writes started now brk marks [(lo, hi)] =
      (true, lo, hi) :: (if (⟨hi, 0⟩ : Cal.Instant) ≤ now then [(false, lo, hi)] else []) := by
  have hu : (marks ++ [markOf true ⟨lo, 0⟩]).any (unpauseAt ⟨hi, 0⟩) = false := by
    rw [List.any_append, hasUnpause_none_of_untouched marks ⟨lo, 0⟩ ⟨hi, 0⟩ ht ((inst_lt _ _).2 hlh)]
    simp [markOf, unpauseAt]
  simp only [writes, List.foldl, step_of_running started now brk (marks, []) (lo, hi) h1 h2]
  simp only [hp, hs, ht, Bool.not_false, Bool.or_false, Bool.and_false, Bool.false_eq_true, if_false,
    pauseIfNew, unpauseIfDone, hu, lastIsPauseAt_append, Bool.not_false, Bool.and_true]
  by_cases hh : (⟨hi, 0⟩ : Cal.Instant) ≤ now
  · simp [hh]
  · simp [hh]

/-- **A block started inside a wall is not paused by it**: the wall did not start while it ran. -/
theorem a_block_started_inside_a_wall_is_not_paused_by_it (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h : (⟨lo, 0⟩ : Cal.Instant) ≤ started) : writes started now brk marks [(lo, hi)] = [] := by
  simp [writes, step, h]

/-- **A wall that has not begun writes nothing.** -/
theorem a_wall_that_has_not_begun_writes_nothing (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h : now < ⟨lo, 0⟩) : writes started now brk marks [(lo, hi)] = [] := by
  simp [writes, step, h]

/-- **A timer already stopped at the wall's start is not the wall's to stop** — a pause, an
interruption or a break (the running break included) covered `lo`. -/
theorem a_timer_already_stopped_at_the_wall_is_left_alone (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hp : marks.any (pauseAt ⟨lo, 0⟩) = false) (hs : stoppedAt marks started ⟨lo, 0⟩ brk = true) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp [writes, step, hp, hs]

/-- **A timer mark stamped after the wall's start stands**: the user has been deciding what the
timer did since, and the wall writes nothing under it. -/
theorem a_timer_mark_after_the_walls_start_stands (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hp : marks.any (pauseAt ⟨lo, 0⟩) = false) (ht : touchedAfter marks ⟨lo, 0⟩ = true) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp [writes, step, hp, ht]

/-- **The wall's end restarts the timer it stopped**: with the wall's pause logged (by an earlier
verb) and still the last word on the timer, a verb after the wall ended writes the unpause, once. -/
theorem the_walls_end_restarts_the_timer_it_stopped (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h1 : started < ⟨lo, 0⟩) (h2 : (⟨lo, 0⟩ : Cal.Instant) ≤ now) (h3 : (⟨hi, 0⟩ : Cal.Instant) ≤ now)
    (hp : marks.any (pauseAt ⟨lo, 0⟩) = true) (hu : marks.any (unpauseAt ⟨hi, 0⟩) = false)
    (hl : lastIsPauseAt marks ⟨lo, 0⟩ = true) :
    writes started now brk marks [(lo, hi)] = [(false, lo, hi)] := by
  simp only [writes, List.foldl, step_of_running started now brk (marks, []) (lo, hi) h1 h2]
  simp [hp, pauseIfNew, unpauseIfDone, h3, hu, hl]

/-- **A user who resumed during the meeting keeps their timer** (D61's correction for a skipped
meeting): the wall's pause is logged but no longer the last word on the timer, so its end writes
nothing. -/
theorem a_user_who_resumed_during_the_meeting_keeps_their_timer (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hp : marks.any (pauseAt ⟨lo, 0⟩) = true) (hl : lastIsPauseAt marks ⟨lo, 0⟩ = false) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp [writes, step, hp, pauseIfNew, unpauseIfDone, hl]

/-- What one span's step appends to the written list: the entries before it, then its own, each a
start or an end of `s` never ahead of `now`, and only when the block began before the wall. -/
theorem step_written (started now : Cal.Instant) (brk : Option Cal.Instant)
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (s : Nat × Nat) (x : Bool × Nat × Nat)
    (hx : x ∈ (step started now brk acc s).2) :
    x ∈ acc.2 ∨ (x.2 = s ∧ started < ⟨s.1, 0⟩ ∧ (⟨s.1, 0⟩ : Cal.Instant) ≤ now ∧
      (x.1 = false → (⟨s.2, 0⟩ : Cal.Instant) ≤ now)) := by
  by_cases hc : (⟨s.1, 0⟩ : Cal.Instant) ≤ started ∨ now < ⟨s.1, 0⟩
  · simp only [step, if_pos hc] at hx; exact Or.inl hx
  · have h1 : started < ⟨s.1, 0⟩ := by
      have := (not_or.1 hc).1
      rw [Cal.Instant.le_iff] at this; rw [Cal.Instant.lt_iff]; omega
    have h2 : (⟨s.1, 0⟩ : Cal.Instant) ≤ now := (Cal.Instant.not_lt _ _).1 (not_or.1 hc).2
    rw [step_of_running started now brk acc s h1 h2] at hx
    split at hx
    · exact Or.inl hx
    · unfold unpauseIfDone at hx
      split at hx
      · rename_i hq
        rcases List.mem_append.1 hx with hx | hx
        · unfold pauseIfNew at hx
          split at hx
          · exact Or.inl hx
          · rcases List.mem_append.1 hx with hx | hx
            · exact Or.inl hx
            · simp only [List.mem_singleton] at hx; subst hx
              exact Or.inr ⟨rfl, h1, h2, by simp⟩
        · simp only [List.mem_singleton] at hx; subst hx
          have h3 : (⟨s.2, 0⟩ : Cal.Instant) ≤ now := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
            exact hq.1.1
          exact Or.inr ⟨rfl, h1, h2, fun _ => h3⟩
      · unfold pauseIfNew at hx
        split at hx
        · exact Or.inl hx
        · rcases List.mem_append.1 hx with hx | hx
          · exact Or.inl hx
          · simp only [List.mem_singleton] at hx; subst hx
            exact Or.inr ⟨rfl, h1, h2, by simp⟩

/-- **Everything the walls write is a joined span's own start or end, and never ahead of `now`**
— over any number of spans. -/
theorem mem_writes (started now : Cal.Instant) (brk : Option Cal.Instant)
    (marks : List Replay.IdleMark) (spans : List (Nat × Nat)) (b : Bool) (lo hi : Nat)
    (h : (b, lo, hi) ∈ writes started now brk marks spans) :
    (lo, hi) ∈ spans ∧ started < ⟨lo, 0⟩ ∧ (⟨lo, 0⟩ : Cal.Instant) ≤ now ∧
      (b = false → (⟨hi, 0⟩ : Cal.Instant) ≤ now) := by
  unfold writes at h
  suffices H : ∀ (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (ss : List (Nat × Nat)),
      (∀ x ∈ acc.2, x.2 ∈ spans ∧ started < ⟨x.2.1, 0⟩ ∧ (⟨x.2.1, 0⟩ : Cal.Instant) ≤ now ∧
        (x.1 = false → (⟨x.2.2, 0⟩ : Cal.Instant) ≤ now)) →
      (∀ s ∈ ss, s ∈ spans) →
      ∀ x ∈ (ss.foldl (step started now brk) acc).2, x.2 ∈ spans ∧ started < ⟨x.2.1, 0⟩ ∧
        (⟨x.2.1, 0⟩ : Cal.Instant) ≤ now ∧ (x.1 = false → (⟨x.2.2, 0⟩ : Cal.Instant) ≤ now) by
    exact H (marks, []) spans (by simp) (fun s hs => hs) (b, lo, hi) h
  intro acc ss hacc hss
  induction ss generalizing acc with
  | nil => exact hacc
  | cons s ss ih =>
    apply ih _ _ (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs'))
    intro x hx
    rcases step_written started now brk acc s x hx with hx | ⟨he, h1, h2, h3⟩
    · exact hacc x hx
    · rw [he]; exact ⟨hss s (List.mem_cons_self ..), h1, h2, h3⟩

/-- The marks a written list adds to the log, in order. -/
def marksOf (w : List (Bool × Nat × Nat)) : List Replay.IdleMark :=
  w.map fun x => markOf x.1 (if x.1 then ⟨x.2.1, 0⟩ else ⟨x.2.2, 0⟩)

/-- **A second verb writes nothing more** (one wall, the day a user has — AGENTS §3.1 item 4, the
subdomain in the name): once the marks the rule wrote are in the log, the next verb's run of the
same rule writes nothing, which is D61's "written once".  A two-run law (owner D5). -/
theorem after_one_wall_a_second_verb_writes_nothing_more (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat) (hlh : lo < hi) :
    writes started now brk (marks ++ marksOf (writes started now brk marks [(lo, hi)])) [(lo, hi)]
      = [] := by
  by_cases hc : (⟨lo, 0⟩ : Cal.Instant) ≤ started ∨ now < ⟨lo, 0⟩
  · simp [writes, step, hc]
  · have h1 : started < ⟨lo, 0⟩ := by
      have := (not_or.1 hc).1
      rw [Cal.Instant.le_iff] at this; rw [Cal.Instant.lt_iff]; omega
    have h2 : (⟨lo, 0⟩ : Cal.Instant) ≤ now := (Cal.Instant.not_lt _ _).1 (not_or.1 hc).2
    cases hp : marks.any (pauseAt ⟨lo, 0⟩) with
    | true =>
      cases hq : (decide ((⟨hi, 0⟩ : Cal.Instant) ≤ now) && !(marks.any (unpauseAt ⟨hi, 0⟩)) &&
          lastIsPauseAt marks ⟨lo, 0⟩) with
      | true =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hq
        rw [the_walls_end_restarts_the_timer_it_stopped started now brk marks lo hi h1 h2 hq.1.1 hp
          hq.1.2 hq.2]
        simp only [writes, List.foldl, step_of_running started now brk _ (lo, hi) h1 h2]
        simp [marksOf, markOf, pauseIfNew, unpauseIfDone, hp, unpauseAt]
      | false =>
        have h0 : writes started now brk marks [(lo, hi)] = [] := by
          simp only [writes, List.foldl, step_of_running started now brk _ (lo, hi) h1 h2]
          simp [pauseIfNew, unpauseIfDone, hp, hq]
        rw [h0]
        simpa [marksOf] using h0
    | false =>
      cases hk : (stoppedAt marks started ⟨lo, 0⟩ brk || touchedAfter marks ⟨lo, 0⟩) with
      | true =>
        have h0 : writes started now brk marks [(lo, hi)] = [] := by
          simp only [writes, List.foldl, step_of_running started now brk _ (lo, hi) h1 h2]
          simp [hp, hk]
        rw [h0]
        simpa [marksOf] using h0
      | false =>
        have hs : stoppedAt marks started ⟨lo, 0⟩ brk = false := by
          simp only [Bool.or_eq_false_iff] at hk; exact hk.1
        have ht : touchedAfter marks ⟨lo, 0⟩ = false := by
          simp only [Bool.or_eq_false_iff] at hk; exact hk.2
        rw [a_wall_that_starts_while_a_block_runs_stops_its_timer started now brk marks lo hi h1 h2 hlh
          hp hs ht]
        simp only [writes, List.foldl, step_of_running started now brk _ (lo, hi) h1 h2]
        by_cases hh : (⟨hi, 0⟩ : Cal.Instant) ≤ now
        · simp [hh, marksOf, markOf, pauseIfNew, unpauseIfDone, pauseAt, unpauseAt]
        · simp [hh, marksOf, markOf, pauseIfNew, unpauseIfDone, pauseAt]

/-- **The meeting the running block is paused for** (the campaign's D66 call on gap 3048): the
first joined span `now` falls inside whose start's pause is the last word on the timer — what `tm
pause` names when it resumes the timer inside a meeting (the correction for a skipped one). -/
def pausedFor (now : Cal.Instant) (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id)) :
    Option ((Nat × Nat) × List Id) :=
  spans.find? fun x => lastIsPauseAt marks ⟨x.1.1, 0⟩ && decide ((⟨x.1.1, 0⟩ : Cal.Instant) ≤ now) &&
    decide (now < ⟨x.1.2, 0⟩)

/-- **What `pausedFor` names is a meeting the timer is paused for, now**: one of the spans, its
start's pause the last timer mark, and `now` inside it. -/
theorem pausedFor_is_a_meeting_the_timer_is_paused_for (now : Cal.Instant)
    (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id)) (x : (Nat × Nat) × List Id)
    (h : pausedFor now marks spans = some x) :
    x ∈ spans ∧ lastIsPauseAt marks ⟨x.1.1, 0⟩ = true ∧ (⟨x.1.1, 0⟩ : Cal.Instant) ≤ now ∧
      now < ⟨x.1.2, 0⟩ := by
  unfold pausedFor at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1.1, hp.1.2, hp.2⟩

/-! ## The wire: the `emit` section's walls form

The host asks `{"emit": {"walls": {"at": <stamp>, "break": <stamp> | null}}}` beside the request's
`docs`, `tz`, `log` (with facts), `now` and `blockMin`, and `Boundary.readEmitSection` answers
`ok.emit` with one entry per line to append, in order: `ev` (`pause`/`unpause`), the block's `id`,
`at` (the entry's stamp), `from`/`to` (the joined span), `walls` (the items it joins, for the
notice D65 prints) and `line` — the exact bytes, written by `Log.emitLine` (D16).  `at` and `break`
are read by B2's one stamp reader, `LogStamp.parseStamp`; `break` is the running break
`.tm/state.json` holds, the one input the log cannot give (a break is logged when it ends). -/

/-- **The walls form's refusals** (§10.3's shape): `{"err":{"emit":{"walls":<name>}}}`. -/
inductive Refusal
  /-- `emit.walls` absent or not an object -/
  | shape
  /-- `emit.walls.at` absent, repeated, or not a stamp B2's reader accepts -/
  | badAt
  /-- `emit.walls.break` present and neither `null` nor such a stamp -/
  | badBreak
  /-- no readable `tz`: a wall's instants are the zone's -/
  | tzAbsent
  /-- no `log` section that asked for facts: the open block and the marks are the replay's -/
  | logAbsent
  /-- no request `now`: the day the walls are selected for -/
  | nowAbsent
  /-- no request `blockMin`: a `buffer:` written in blocks -/
  | blockMinAbsent
  /-- commands beside the walls form: the walls are the documents as sent (gap 109's stance) -/
  | withCommands
  /-- a wall's instant, or the zone's offset at it, outside what the kernel holds (R10) -/
  | badInstant
  /-- the log's reader refuses a line the rule would write (named; not expected to fire) -/
  | refused
deriving DecidableEq, Repr, Inhabited

/-- Each refusal's wire name. -/
def Refusal.name : Refusal → String
  | .shape => "shape" | .badAt => "badAt" | .badBreak => "badBreak" | .tzAbsent => "tzAbsent"
  | .logAbsent => "logAbsent" | .nowAbsent => "nowAbsent" | .blockMinAbsent => "blockMinAbsent"
  | .withCommands => "withCommands" | .badInstant => "badInstant" | .refused => "refused"

/-- Keys in build order: `{"err":{"emit":{"walls":<name>}}}`. -/
def Refusal.json (r : Refusal) : JVal := jone "err" (jone "emit" (jone "walls" (.str r.name.toList)))

/-- The request's walls form, read. -/
structure Req where
  at_ : Cal.VInstant × Cal.VOffset
  brk : Option (Cal.VInstant × Cal.VOffset)

/-- A stamp through B2's one reader. -/
def readStamp : JVal → Option (Cal.VInstant × Cal.VOffset)
  | .str t => match LogStamp.parseStamp t with | .ok r => some r | .error _ => none
  | _ => none

/-- **`emit.walls`**: `at` required, `break` optional (`null` is none). -/
def readReq (v : JVal) : Except Refusal Req :=
  match jget v "walls" with
  | .ok (some w@(.obj _)) =>
    match jget w "at" with
    | .ok (some a) =>
      match readStamp a with
      | none => .error .badAt
      | some t =>
        match jget w "break" with
        | .ok none | .ok (some .null) => .ok ⟨t, none⟩
        | .ok (some b) =>
          match readStamp b with
          | some x => .ok ⟨t, some x⟩
          | none => .error .badBreak
        | .error _ => .error .badBreak
    | _ => .error .badAt
  | _ => .error .shape

/-- **Today's walls, joined as fork `merge_walls` joins them**, each with the items it joined:
`Look.wallIxOn`'s selection (the one the window, the cut and the wall rows read), `Look.clipWalls
0` (empty walls dropped), `Look.sortByStart`, `Look.mergeSorted` — reused, not re-spelled — and the
walls each joined span contains. -/
def spansOf (ix : List Look.WallIx) (d : Nat) : List ((Nat × Nat) × List Id) :=
  (Look.mergeSorted (Look.sortByStart (Look.clipWalls 0
      ((Look.wallIxOn ix d).map fun w => (w.lo, w.hi))))).map fun m =>
    (m, ((Look.wallIxOn ix d).filter fun w => decide (m.1 ≤ w.lo ∧ w.hi ≤ m.2 ∧ w.lo < w.hi)).map
      (·.id))

/-- An instant of whole seconds with the zone's offset at it, as a stamp is written. -/
def stampAt (z : Cal.Tz) (sec : Nat) : Option (Cal.VInstant × Cal.VOffset) :=
  match Cal.mkInstant? sec 0, Cal.mkOffset? (Cal.offsetAt z ⟨sec, 0⟩).west (Cal.offsetAt z ⟨sec, 0⟩).sec with
  | some i, some o => some (i, o)
  | _, _ => none

/-- **A joined span, on the wire**: `from`/`to` as stamps and the walls it joins. -/
def spanJson (z : Cal.Tz) (x : (Nat × Nat) × List Id) : Except Refusal JVal :=
  match stampAt z x.1.1, stampAt z x.1.2 with
  | some (a, ao), some (b, bo) => .ok (.obj [("from".toList, .str (LogStamp.renderStamp a ao)),
      ("to".toList, .str (LogStamp.renderStamp b bo)), ("walls".toList, .arr (x.2.map JVal.str))])
  | _, _ => .error .badInstant

/-- **One written mark, on the wire**: its line (D16's one writer) and what the host says of it. -/
def entryJson (z : Cal.Tz) (id : Id) (spans : List ((Nat × Nat) × List Id)) (w : Bool × Nat × Nat) :
    Except Refusal JVal :=
  match stampAt z (if w.1 then w.2.1 else w.2.2), stampAt z w.2.1, stampAt z w.2.2 with
  | some (i, o), some (a, ao), some (b, bo) =>
    match Log.emitLine i o (if w.1 then "pause".toList else "unpause".toList) [("id".toList, .str id)] with
    | .ok line => .ok (.obj [("ev".toList, .str (if w.1 then "pause".toList else "unpause".toList)),
        ("id".toList, .str id), ("at".toList, .str (LogStamp.renderStamp i o)),
        ("from".toList, .str (LogStamp.renderStamp a ao)), ("to".toList, .str (LogStamp.renderStamp b bo)),
        ("walls".toList, .arr ((((spans.find? fun x => x.1 == w.2).map (·.2)).getD []).map JVal.str)),
        ("line".toList, .str line)])
    | .error _ => .error .refused
  | _, _, _ => .error .badInstant

/-- **What the walls write, answered** (gap 3139): nothing while no block is open in the replay;
otherwise `writes` over the open block, its marks, the walls of the request's day, the running
break and `at`, each mark rendered.  The marks are day `d`'s and, stamped at or after the block's
start, the day before's: an entry is filed under the day of the last wake within 24 hours
(`Replay.dayOf`), so a mark stamped on `d` may sit in either (README gap 3245).  The walls are
the index argument's (`Boundary.wallsEmit` passes `Look.wallIndex`), a function for `answer_congr_ix`. -/
def answer (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (cmds : Nat) (today : Option Nat) (bm : Option Nat) :
    Except Refusal JVal := do
  let q ← readReq v
  let f ← match facts with | some f => pure f | none => throw .logAbsent
  let z ← match zo with | some z => pure z | none => throw .tzAbsent
  let d ← match today with | some d => pure d | none => throw .nowAbsent
  let b ← match bm with | some b => pure b | none => throw .blockMinAbsent
  if cmds ≠ 0 then throw .withCommands
  match f.openBlock with
  | none => pure (.obj [("marks".toList, .arr []), ("pausedFor".toList, .null)])
  | some ob =>
    let spans := spansOf (ixOf z b) d
    let dm := fun x => (((f.days.find? fun r => r.day == x).bind (·.seam)).map (·.idleMarks)).getD []
    let marks := (if 0 < d then (dm (d - 1)).filter (fun m => decide (ob.started.1 ≤ markAt m)) else []) ++ dm d
    let ws := writes ob.started.1 q.at_.1.val (q.brk.map (·.1.val)) marks (spans.map (·.1))
    let es ← ws.mapM (entryJson z ob.id spans)
    let pf ← match pausedFor q.at_.1.val (marks ++ marksOf ws) spans with
      | none => pure JVal.null
      | some x => spanJson z x
    pure (.obj [("marks".toList, .arr es), ("pausedFor".toList, pf)])

/-- **No open block, nothing to stop**: the answer is the empty list whatever the walls. -/
theorem answer_without_an_open_block (v : JVal) (z : Cal.Tz) (f : Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (d b : Nat) (q : Req) (hq : readReq v = .ok q)
    (hf : f.openBlock = none) :
    answer v (some z) (some f) ixOf 0 (some d) (some b) =
      .ok (.obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]) := by
  simp [answer, hq, hf, bind, Except.bind, pure, Except.pure]

/-- **The walls form refuses commands beside it**, by name. -/
theorem answer_refuses_commands (v : JVal) (z : Cal.Tz) (f : Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n d b : Nat) (q : Req) (hq : readReq v = .ok q)
    (hn : n ≠ 0) :
    answer v (some z) (some f) ixOf n (some d) (some b) = .error .withCommands := by
  simp [answer, hq, hn, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- **Without a replay there is no answer**: a walls request whose `log` section asked no facts is
refused `logAbsent`, never answered as if no block were open (D24's rule for a consumer handed no
replay). -/
theorem answer_refuses_without_the_replay (v : JVal) (zo : Option Cal.Tz)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (q : Req)
    (hq : readReq v = .ok q) :
    answer v zo none ixOf n d b = .error .logAbsent := by
  simp [answer, hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **The answer reads the wall index at the request's zone and block length and nowhere else.** -/
theorem answer_congr_ix (v : JVal) (z : Cal.Tz) (f : Option Seal.Answer)
    (ixOf ixOf' : Cal.Tz → Nat → List Look.WallIx) (n d b : Nat) (h : ixOf z b = ixOf' z b) :
    answer v (some z) f ixOf n (some d) (some b) = answer v (some z) f ixOf' n (some d) (some b) := by
  simp only [answer, pure_bind, h]

/-- **The refusals spell themselves** (§5.7). -/
theorem the_walls_refusals_spell_themselves :
    Refusal.name .shape = "shape" ∧ Refusal.name .badAt = "badAt" ∧
    Refusal.name .badBreak = "badBreak" ∧ Refusal.name .tzAbsent = "tzAbsent" ∧
    Refusal.name .logAbsent = "logAbsent" ∧ Refusal.name .nowAbsent = "nowAbsent" ∧
    Refusal.name .blockMinAbsent = "blockMinAbsent" ∧ Refusal.name .withCommands = "withCommands" ∧
    Refusal.name .badInstant = "badInstant" ∧ Refusal.name .refused = "refused" := by
  decide

/-! ## The rule, run (AGENTS §5.2: non-vacuity is a separate check from correctness)

A block begun at 500 s, one wall `[1000, 2000)`, and the log's marks of each case — every one of
`cli_wall_pause.rs`'s drives, at seconds a reader can check by eye. -/

/-- A whole-second instant. -/
def secAt (s : Nat) : Cal.Instant := ⟨s, 0⟩

/-- A mark's stamp at a whole second (the offset is the wire's). -/
def atSec (s : Nat) : Replay.At := (⟨s, 0⟩, Cal.Offset.utc)

/-- **The rule, run**: the pause and the unpause; the pause alone while the wall runs; nothing before
it or for a block started inside it; nothing over a timer already stopped (a pause at 900, the
running break, a break logged over 1000) and the wall's pause over a pause another block left
(400) or a stop that ended before the wall (900–950, an interruption 990–995, a break logged
without its length); nothing under a mark stamped after the wall's start; the end alone when the
pause is logged; nothing when the user resumed inside the meeting; and two walls in order. -/
theorem the_rule_is_run :
    writes (secAt 500) (secAt 2500) none [] [(1000, 2000)] = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (secAt 500) (secAt 1500) none [] [(1000, 2000)] = [(true, 1000, 2000)] ∧
    writes (secAt 500) (secAt 900) none [] [(1000, 2000)] = [] ∧
    writes (secAt 1500) (secAt 2500) none [] [(1000, 2000)] = [] ∧
    writes (secAt 500) (secAt 2500) none [.pause (atSec 900)] [(1000, 2000)] = [] ∧
    writes (secAt 500) (secAt 2500) (some (secAt 900)) [] [(1000, 2000)] = [] ∧
    writes (secAt 500) (secAt 2500) none [.brk (atSec 950) (some 1)] [(1000, 2000)] = [] ∧
    writes (secAt 500) (secAt 2500) none [.pause (atSec 400)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (secAt 500) (secAt 2500) none [.pause (atSec 900), .unpause (atSec 950)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (secAt 500) (secAt 2500) none [.interrupt (atSec 990), .resume (atSec 995)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (secAt 500) (secAt 2500) none [.brk (atSec 950) none] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (secAt 500) (secAt 2500) none [.unpause (atSec 1500)] [(1000, 2000)] = [] ∧
    writes (secAt 500) (secAt 2500) none [.pause (atSec 1000)] [(1000, 2000)] = [(false, 1000, 2000)] ∧
    writes (secAt 500) (secAt 2500) none [.pause (atSec 1000), .unpause (atSec 1200)] [(1000, 2000)]
      = [] ∧
    writes (secAt 500) (secAt 3500) none [] [(1000, 2000), (3000, 4000)]
      = [(true, 1000, 2000), (false, 1000, 2000), (true, 3000, 4000)] := by
  decide

/-- **The meeting named, run**: inside the meeting with its pause the last mark, it is named; after
the unpause, or once the user resumed inside it, it is not. -/
theorem pausedFor_is_run :
    pausedFor (secAt 1500) [.pause (atSec 1000)] [((1000, 2000), [['g','1']])]
      = some ((1000, 2000), [['g','1']]) ∧
    pausedFor (secAt 2500) [.pause (atSec 1000), .unpause (atSec 2000)] [((1000, 2000), [['g','1']])]
      = none ∧
    pausedFor (secAt 1500) [.pause (atSec 1000), .unpause (atSec 1200)] [((1000, 2000), [['g','1']])]
      = none := by
  decide

/-- **The walls joined, run**: two overlapping walls and one touching them are one span naming all
three; an empty wall is dropped; another day's wall is not today's; a separate wall is its own. -/
theorem spansOf_is_run :
    spansOf [⟨['g','1'], 7, 7, 1000, 1000, 2000⟩, ⟨['g','2'], 7, 7, 1500, 1500, 2500⟩,
      ⟨['g','3'], 7, 7, 3000, 3000, 3000⟩, ⟨['g','4'], 7, 7, 2500, 2500, 2600⟩,
      ⟨['g','5'], 8, 8, 1000, 1000, 2000⟩, ⟨['g','6'], 7, 7, 4000, 4000, 4500⟩] 7
      = [((1000, 2600), [['g','1'], ['g','2'], ['g','4']]), ((4000, 4500), [['g','6']])] := by
  decide

/-- **The walls form read, run**: a stamp is read by B2's one reader; `break` may be `null`; a
missing `at`, an `at` that is not a stamp, a `break` that is not one and a `walls` that is not an
object are refused by name. -/
theorem readReq_is_run :
    (match readReq (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) with
      | .ok q => q.at_.1.val == ⟨63924402000, 0⟩ && q.brk.isNone
      | .error _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .obj [])]) with
      | .error .badAt => true | _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .obj [("at".toList, .str "13:20".toList)])]) with
      | .error .badAt => true | _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .num 3)])]) with
      | .error .badBreak => true | _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .arr [])]) with
      | .error .shape => true | _ => false) = true := by
  decide

/-- **A refusal on the wire, in build order.** -/
theorem the_walls_refusal_is_the_err_emit_shape :
    jemit (Refusal.json .logAbsent) = "{\"err\":{\"emit\":{\"walls\":\"logAbsent\"}}}".toList := by
  decide

/-- **The day before's marks are read** (README gap 3245): a replay whose open block (`t4`, begun at
second 500) has its wall's pause and unpause filed under day 7 — a day with no wake of its own files
its entries under the day before's wake when that is within 24 hours (`Replay.dayOf`) — asked on
day 8 once the wall has ended, answers nothing more to write.  Day 8's record alone holds no mark,
and over no mark the rule writes both again (`the_rule_is_run`'s first case), which is what the
host's reading of day 8 alone did on every verb of such a day. -/
theorem the_day_befores_marks_are_read :
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [⟨7, none, some ⟨none, [.pause (atSec 1000), .unpause (atSec 2000)], none⟩,
          [], [], [], [], [], []⟩], some ⟨['t','4'], atSec 500, 0, none, false⟩, none, none, none, 0, 0, none,
          [], [], 0⟩)
        (fun _ _ => [⟨['g','1'], 8, 8, 1000, 1000, 2000⟩]) 0 (some 8) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]
      | .error _ => false) = true := by
  decide

/-- **A break is not a timer mark** (`lastTimerMark` passes over it, as the host's last_timer_mark
did): a break logged inside the meeting after the wall's pause leaves that pause the last word on
the timer, so the wall's end still writes the unpause. -/
theorem a_break_inside_the_meeting_leaves_the_pause_the_last_word :
    writes (secAt 500) (secAt 2500) none [.pause (atSec 1000), .brk (atSec 1200) (some 5)] [(1000, 2000)]
      = [(false, 1000, 2000)] := by
  decide

end WallTimer
end Tm
