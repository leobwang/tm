import TmKernel.SealIndex
/-!
# SealInStep — W2's in-step theorems (stage 5, D9, §14.5's W2 row)

The two edge cases of the stored wakes (§9.3, CRIT 25), the fence's day-index law, a spurious G1 refusal (§7.4), and
why the guards are there (a resume without them is not the replay).  The witnesses were probed in a scratch copy under
`MemoryMax=8G timeout 120` (§14.0 item 4): at most two entries, `utcZone`, instants as `Nat` literals, no text parsed.
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State survivors wakeInstants keptWakes sortWakes dayOf bE bDone utcZone)
open Log (Entry)

/-- **A tail instant before the head second is sealed** (§9.3's first edge case, CRIT 25, on W2's head second): its day
is below the ledger day on every index, so G3 refusing it without computing `dayOf` is exact. -/
theorem an_instant_before_the_stored_wakes_is_sealed (z : Cal.Tz) (L : Nat) (kw : List Cal.Instant)
    (q : Cal.Instant) (h : q.sec < headSec L) : dayOf z kw q < L :=
  dayOf_lt_of_head z L kw q h

theorem keptWakes_eq_nil (z : Cal.Tz) (ws : List Cal.Instant) : keptWakes z ws = [] ↔ ws = [] := by
  constructor
  · intro h
    cases hws : ws with
    | nil => rfl
    | cons w ws' =>
      exfalso
      have hm : w ∈ sortWakes (w :: ws') := (mem_sortWakes _ w).2 List.mem_cons_self
      rw [hws, keptWakes_eq] at h
      cases hs : sortWakes (w :: ws') with
      | nil => rw [hs] at hm; cases hm
      | cons y ys => rw [hs, dedupFrom_cons] at h; cases h
  · intro h; subst h; rfl

/-- **No folded wake, no stored wake, and the tail's index is the whole index** (§9.3's second edge case): the stored
wakes are empty exactly when no surviving wake was folded, and then the stored index is the tail's. -/
theorem dayOf_with_no_folded_wake_reads_the_tail (z : Cal.Tz) (L : Nat) (WA WB : List Cal.Instant) :
    (storedWakes L (keptWakes z WA) = [] ↔ WA = []) ∧
    (WA = [] → ∀ q, dayOf z (keptWakes z (storedWakes L (keptWakes z WA) ++ WB)) q
      = dayOf z (keptWakes z (WA ++ WB)) q) := by
  refine ⟨⟨fun h => (keptWakes_eq_nil z WA).1 (Classical.byContradiction (fun hne => storedWakes_ne_nil L _ hne h)),
    fun h => by subst h; rfl⟩, fun h q => by subst h; rfl⟩

/-- **The fence's day-index law, at three days** (§9.4's `dayOf_agrees_two_days_before`, restated): a surviving tail
wake after every folded instant not future, and more than three days before every future one, leaves the day of every
folded instant unchanged. -/
theorem dayOf_agrees_three_days_before (z : Cal.Tz) (P : Cal.Instant → Bool) (QA WA WB : List Cal.Instant)
    (hWA : ∀ w ∈ WA, w ∈ QA) (hns : ∀ q ∈ QA ++ WB, q.ns < 2000000000)
    (hsep : ∀ w ∈ WB, ∀ q ∈ QA, (P q = true → q < w) ∧ (P q = false → w.sec + 259200 < q.sec))
    (q : Cal.Instant) (hq : q ∈ QA) :
    dayOf z (keptWakes z (WA ++ WB)) q = dayOf z (keptWakes z WA) q :=
  dayOf_folded_agrees z P QA WA WB hWA hns hsep q hq

section Witnesses

set_option maxRecDepth 8000 in
/-- **A spurious G1 refusal exists** (§7.4): a folded `done a`, then `undo done b`.  G1 refuses the undo (a folded
survivor carries its tag, `done`), though the whole log's mask cancels nothing folded: the undo dangles.  The refusal
costs one pop, never a wrong fact. -/
theorem a_spurious_tag_refusal_exists :
    g1 (ckptOfEntries utcZone 739865 739865 1 [bE 1 63924368400 (bDone ['a'] 50 false)] [] [])
        (unsettled [] [bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['b']))]) = some (.undoReach 2 1) ∧
    survivors [bE 1 63924368400 (bDone ['a'] 50 false), bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['b']))]
      = [bE 1 63924368400 (bDone ['a'] 50 false)] := by
  decide

/-- **A resume without the guards**: the tail's survivors folded from the restored state, with no refusal (§15's
`resumeUnguarded`, over entries). -/
def resumeUnguarded (z : Cal.Tz) (K : Ckpt) (bs : List Entry) (ws : List (Nat × Log.LWarn)) : Seal.Answer :=
  let N := unsettled K.settled bs
  let sv := survivors N
  let kw := tailIndex z K sv
  let dy := dayOf z kw
  let sl := tailSlept z K kw sv
  let st := rebindState sl (sv.foldl (Replay.stepWith z dy sl) (restore K (K.items.length + K.openDays.length + bs.length)))
  resumedAnswer K st (storedHeaders K ++ tailHeaders dy K.settled bs) bs.length ws

set_option maxRecDepth 8000 in
/-- **A resume without the guards is not the replay** (§9.5 law 5's other side, cheat 152's control): after a folded
`done a`, the tail's `undo done a` finds nothing on the tail's stack, so the unguarded resume keeps `a` done while the
replay of both lines cancels it; G1 refuses that undo. -/
theorem resume_without_the_guards_is_not_replay :
    askAnswer (resumeUnguarded utcZone
        (ckptOfEntries utcZone 739865 739865 1 [bE 1 63924368400 (bDone ['a'] 50 false)] [] [])
        [bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] []) (.lastDone ['a'])
      ≠ askAnswer (answer (ckptOfEntries utcZone 739865 739865 2
        [bE 1 63924368400 (bDone ['a'] 50 false), bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] [] []))
        (.lastDone ['a']) ∧
    g1 (ckptOfEntries utcZone 739865 739865 1 [bE 1 63924368400 (bDone ['a'] 50 false)] [] [])
        (unsettled [] [bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))]) = some (.undoReach 2 1) := by
  decide

/-- One `done x` at 09:00 on 2026-08-29, the horizon of 2026-09-14. -/
def oneDoneOnTheHorizon : List Entry := [bE 1 63923590800 (bDone ['x'] 50 false)]

set_option maxRecDepth 8000 in
/-- **The window at the horizon reads the replay** (cheat 153's control): sealed on 2026-09-14, whose horizon is the
29th of August, the done date on the horizon itself is read from the answer's window. -/
theorem the_window_at_the_horizon_reads_the_replay :
    Cal.localDate utcZone ⟨63923590800, 0⟩ = 739856 ∧ horizonOf 739872 = 739856 ∧
    askMerged (dayRecordsOfEntries utcZone 0 739872 oneDoneOnTheHorizon)
        (windowRecordsOfEntries utcZone 0 (horizonOf 739872) oneDoneOnTheHorizon)
        (answer (ckptOfEntries utcZone 739872 739872 1 oneDoneOnTheHorizon [] [])) (.win 739856 (.done ['x']))
      = Replay.ask (Replay.replayDoc utcZone oneDoneOnTheHorizon) (.win 739856 (.done ['x'])) := by
  decide

/-- A zone of two transitions, a day's offset each way: `+23:00`, then `-23:00` from 18:00Z on 2026-09-07, then `+23:00`
again from 02:30Z on the 9th. -/
def flipZone : Cal.Tz :=
  ⟨⟨['f', 'l', 'i', 'p'], ⟨false, 82800⟩, [(⟨63924400800, 0⟩, ⟨true, 82800⟩), (⟨63924517800, 0⟩, ⟨false, 82800⟩)]⟩,
    by decide⟩

set_option maxRecDepth 8000 in
/-- **§9.4's two-day margin is false** under a zone table the kernel accepts (refuted; `dayOf_agrees_three_days_before`
is the law).  A tail wake at 01:00Z on the 7th (local date the 8th), a folded future wake at 02:00Z on the 9th, two days
and an hour later (local date the 8th again: the offset flipped), and a folded future instant at 03:00Z on the 9th
(local date the 10th: it flipped back).  The tail wake is more than two days before both folded instants, yet it takes
the folded wake's place in the index (one wake a local date), and the later instant's day moves from the 8th to the
10th. -/
theorem dayOf_agrees_two_days_before_is_false :
    ¬ (∀ (z : Cal.Tz) (P : Cal.Instant → Bool) (QA WA WB : List Cal.Instant), (∀ w ∈ WA, w ∈ QA) →
      (∀ q ∈ QA ++ WB, q.ns < 2000000000) →
      (∀ w ∈ WB, ∀ q ∈ QA, (P q = true → q < w) ∧ (P q = false → w.sec + 172800 < q.sec)) →
      ∀ q ∈ QA, dayOf z (keptWakes z (WA ++ WB)) q = dayOf z (keptWakes z WA) q) := by
  intro h
  have := h flipZone (fun _ => false) [⟨63924516000, 0⟩, ⟨63924519600, 0⟩] [⟨63924516000, 0⟩] [⟨63924339600, 0⟩]
    (by decide) (by decide) (by decide) ⟨63924519600, 0⟩ (by simp)
  revert this
  decide

end Witnesses

end Seal
end Tm
