import TmKernel.SealLaw2B
/-!
# SealLaw2C — law 2's state: an accepted resume's state agrees with the whole log's above the horizons (stage 5, D9, W2)

Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect HMap survivors wakeInstants keptWakes dayOf)
open Log (Entry)

theorem valueAt_day_get {x y : State} {d : Nat} (h : x.valueAt (.day d) = y.valueAt (.day d)) :
    x.days.get d = y.days.get d := by
  simp only [Replay.State.valueAt, Replay.Val.day.injEq, Replay.DayView.mk.injEq] at h
  exact h.1

theorem valueAt_doneDate_get {x y : State} {i : Log.Id} {d : Nat}
    (h : x.valueAt (.doneDate i d) = y.valueAt (.doneDate i d)) : x.doneDates.get (d, i) = y.doneDates.get (d, i) := by
  simp only [Replay.State.valueAt, Replay.Val.doneDate.injEq] at h
  exact h

/-- **The index facts of an accepted resume**: the mask splits at the cut, the whole log's index agrees with the folded
lines' at every folded instant and with the tail's at or after the head second, and every surviving tail wake is at or
after the head second. -/
theorem resume_index (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat)
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none) :
    survivors (As ++ (Rs ++ B')) = foldedSurvivors As Rs ++ sv ∧
    (∀ q ∈ As.flatMap entryInstants,
      dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) q = dayOf z (foldedIndex z As Rs) q) ∧
    (∀ q, headSec L ≤ q.sec →
      dayOf z (keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv)) q = dayOf z kw q) ∧
    (∀ w ∈ wakeInstants sv, headSec L ≤ w.sec) := by
  subst hK
  have hL := ckpt_ledgerDay' z T₀ L cut As Rs ws
  have hsurv := resume_survivors z T₀ L cut As Rs B' ws hd hg
  rw [← ckpt_settled z T₀ L cut As Rs ws, ← hsv] at hsurv
  obtain ⟨hsep, hhead⟩ := resume_sep z (dayOf z kw) sl (ckptOfEntries z T₀ L cut As Rs ws) (restore _ n) T₀
    (As.flatMap entryInstants) sv (ckpt_maxT z T₀ L cut As Rs ws) (ckpt_futureFloor z T₀ L cut As Rs ws) hsteps
  rw [hL] at hhead
  have hWA : ∀ w ∈ wakeInstants (foldedSurvivors As Rs), w ∈ As.flatMap entryInstants := by
    intro w hw
    obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
    exact List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, by simp [entryInstants]⟩
  have hns : ∀ q ∈ As.flatMap entryInstants ++ wakeInstants sv, q.ns < 2000000000 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨e, _, hqe⟩ := List.mem_flatMap.1 hq
      exact entryInstants_ns e q hqe
    · obtain ⟨e, _, _, rfl⟩ := mem_wakeInstants hq
      exact ns_lt_of_wf _ e.t.property
  refine ⟨hsurv, fun q hq => dayOf_folded_agrees z _ _ _ _ hWA hns hsep q hq, fun q hq => ?_, hhead⟩
  rw [hkw]
  unfold tailIndex
  rw [ckpt_wakes]
  exact dayOf_tail_agrees z L _ _ _ _ hWA hsep hhead q hq

/-- **Law 2's state** (§9.5's route): an accepted resume's state agrees with the whole log's above the horizons, and
below them the whole log's days and done dates are the folded lines', whose keys it keeps; the resumed fold writes
nothing below the horizons. -/
theorem resume_state_agrees (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (n : Nat) (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat) (hsl : sl = tailSlept z K kw sv)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none) :
    AgreeAbove L (horizonOf L) (rebindState sl (sv.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)))
        (foldedState z (As ++ (Rs ++ B')) []) ∧
    (∀ d, d < L → (foldedState z (As ++ (Rs ++ B')) []).days.get d = (foldedState z As Rs).days.get d) ∧
    (∀ d i, d < horizonOf L →
      (foldedState z (As ++ (Rs ++ B')) []).doneDates.get (d, i) = (foldedState z As Rs).doneDates.get (d, i)) ∧
    (∀ d, ((foldedState z As Rs).days.get d).isSome → ((foldedState z (As ++ (Rs ++ B')) []).days.get d).isSome) ∧
    (∀ i, ((foldedState z As Rs).items.get i).isSome → ((foldedState z (As ++ (Rs ++ B')) []).items.get i).isSome) ∧
    (∀ i, ((foldedState z As Rs).lastDone.get i).isSome →
      ((foldedState z (As ++ (Rs ++ B')) []).lastDone.get i).isSome) ∧
    (∀ i, ((foldedState z As Rs).dropped.get i).isSome → ((foldedState z (As ++ (Rs ++ B')) []).dropped.get i).isSome) ∧
    (∀ k, ((foldedState z As Rs).doneDates.get k).isSome →
      ((foldedState z (As ++ (Rs ++ B')) []).doneDates.get k).isSome) ∧
    (∀ d, d < L → (sv.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)).days.get d = none) ∧
    (∀ d i, d < horizonOf L → (sv.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)).doneDates.get (d, i) = none) := by
  obtain ⟨hsurv, hI1, hI2, hhead⟩ := resume_index z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps
  subst hK
  have hL := ckpt_ledgerDay' z T₀ L cut As Rs ws
  have hPS := pendingStart_restore z T₀ L cut As Rs ws n
  obtain ⟨KW, hKW⟩ : ∃ KW, KW = keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv) := ⟨_, rfl⟩
  rw [← hKW] at hI1 hI2
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = Replay.KMap.get (Replay.sleptByDay z KW (foldedSurvivors As Rs ++ sv)) := ⟨_, rfl⟩
  have hF : foldedState z (As ++ (Rs ++ B')) [] = sv.foldl (Replay.stepWith z (dayOf z KW) SL)
      ((foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL) (State.init (As ++ (Rs ++ B')).length)) := by
    rw [foldedState_nil, hsurv, wakeInstants_append, List.foldl_append, ← hKW, ← hSL]
  -- `slept_by_day` agrees at and above the ledger day
  have hslept : ∀ d, L ≤ d → sl d = SL d := by
    intro d hd
    rw [hsl, hSL]
    unfold tailSlept
    rw [ckpt_sleptByDay, get_storedSlept _ L d hd, sleptByDay_append, kmap_get_append]
    have e1 : Replay.sleptByDay z KW (foldedSurvivors As Rs)
        = Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs) :=
      sleptByDay_congr z KW (foldedIndex z As Rs) _ (fun e he _ =>
        hI1 e.t.val (List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, by simp [entryInstants]⟩))
    have e2 : Replay.sleptByDay z KW sv = Replay.sleptByDay z kw sv :=
      sleptByDay_congr z KW kw sv (fun e he hw =>
        hI2 e.t.val (hhead e.t.val (List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, hw⟩, rfl⟩)))
    rw [e1, e2]
  -- the folded part
  obtain ⟨G, hGdef⟩ : ∃ G, G = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL)
      (State.init (As ++ (Rs ++ B')).length) := ⟨_, rfl⟩
  rw [← hGdef] at hF
  have hq1 : ∀ q ∈ foldQueries z (dayOf z KW) SL (State.init (As ++ (Rs ++ B')).length) (foldedSurvivors As Rs),
      dayOf z KW q = dayOf z (foldedIndex z As Rs) q := by
    intro q hq
    rcases foldQueries_sub z _ _ _ _ q hq with h | h
    · simp [machineInstants, blockSince, blockPaused, State.init] at h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      exact hI1 q (List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, hqe⟩)
  obtain ⟨X, hXdef⟩ : ∃ X, X = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z (foldedIndex z As Rs))
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))))
      (State.init (As ++ (Rs ++ B')).length) := ⟨_, rfl⟩
  have hGX : G = rebindState SL X := by
    rw [hGdef, foldl_stepWith_congr z _ _ SL _ _ hq1, hXdef]
    have := foldl_rebind z (dayOf z (foldedIndex z As Rs)) SL
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))) (foldedSurvivors As Rs)
      (State.init (As ++ (Rs ++ B')).length) (pendingStart_init _)
    rwa [rebindState_init] at this
  have hXs : Replay.SameReadings X (foldedState z As Rs) := by
    rw [hXdef, foldedState_eq]; exact Replay.SameReadings.foldl z _ _ _ (Replay.sameReadings_init _ _)
  have hXa : AgreeAbove L (horizonOf L) X (foldedState z As Rs) := AgreeAbove.of_sameReadings hXs
  have hR := restore_agrees z T₀ L cut As Rs ws n
  have hG : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) := by
    rw [hGX]; exact AgreeAbove.rebind (hXa.trans hR.symm) SL SL (fun _ _ => rfl)
  -- the tail's checked fold is the fold on the whole index, on every prefix
  have hpre : ∀ pre post, sv = pre ++ post →
      pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n) := by
    intro pre post hs
    refine resume_fold_congr z (dayOf z kw) (dayOf z KW) sl _ _ pre
      (fun pre' e' post' h' => hsteps pre' e' (post' ++ post) (by rw [hs, h']; simp)) (fun q hq => ?_)
    exact (hI2 q (by rwa [hL] at hq)).symm
  have hY2 := foldl_rebind z (dayOf z KW) SL sl sv (restore (ckptOfEntries z T₀ L cut As Rs ws) n) hPS
  have hfull := hpre sv [] (by simp)
  have hAgree : AgreeAbove L (horizonOf L)
      (rebindState sl (sv.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)))
      (foldedState z (As ++ (Rs ++ B')) []) := by
    have h1 := AgreeAbove.rebind (AgreeAbove.refl L (horizonOf L)
      (sv.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n))) sl SL hslept
    refine h1.trans ?_
    rw [hF, hfull, ← hY2]
    exact (AgreeAbove.foldl z _ _ sv hG).symm
  -- the tail names no key below the horizons, on the whole index too
  have hkeys : ∀ pre e post, sv = pre ++ e :: post →
      ∀ x ∈ Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e,
        keyAtOrAbove L (horizonOf L) x.key = true := by
    intro pre e post hs x hx
    have hc := stepCheck_none z (dayOf z kw) sl _ _ e (hsteps pre e post hs)
    rw [hL] at hc
    obtain ⟨hhq, -, hck⟩ := hc
    have hm : (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine
        = (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)).machine := by
      rw [(AgreeAbove.foldl z _ _ pre hG).machine, foldl_rebind z (dayOf z KW) SL sl pre _ hPS, hpre pre (e :: post) hs]
      rfl
    rw [effectsWith_machine z _ _ _ _ e hm] at hx
    have hmem : x.key ∈ (Replay.effectsWith z (dayOf z KW) SL
        (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) e).map
          Replay.Effect.key := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [effectsWith_keys z (dayOf z KW) sl SL _ e (pendingStart_foldl z _ _ pre _ hPS),
      effectsWith_congr (dayOf z KW) (dayOf z kw) z sl _ e (fun q hq => hI2 q (hhq q hq))] at hmem
    obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hmem
    rw [← hyk]; exact hck y hy
  have hbelowF := foldl_below z (dayOf z KW) SL L (horizonOf L) sv G hkeys
  have hbelowR := foldl_below z (dayOf z kw) sl L (horizonOf L) sv (restore (ckptOfEntries z T₀ L cut As Rs ws) n)
    (fun pre e post hs x hx => by
      have := (stepCheck_none z (dayOf z kw) sl _ _ e (hsteps pre e post hs)).2.2 x hx
      rwa [hL] at this)
  have hkeep := foldl_keeps_keys z (dayOf z KW) SL sv G
  obtain ⟨hRbd, hRbl⟩ := restore_below z T₀ L cut As Rs ws n
  refine ⟨hAgree, fun d hd => ?_, fun d i hd => ?_, fun d h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_,
    fun k h => ?_, fun d hd => ?_, fun d i hd => ?_⟩
  · rw [hF, valueAt_day_get (hbelowF.1 d hd), hGX]; exact hXs.days d
  · rw [hF, valueAt_doneDate_get (hbelowF.2.2 i d hd), hGX]; exact hXs.doneDates (d, i)
  · rw [hF]; exact hkeep.1 d (by rw [hGX]; show (X.days.get d).isSome = true; rw [hXs.days d]; exact h)
  · rw [hF]; exact hkeep.2.1 i (by rw [hGX]; show (X.items.get i).isSome = true; rw [hXs.items i]; exact h)
  · rw [hF]; exact hkeep.2.2.1 i (by rw [hGX]; show (X.lastDone.get i).isSome = true; rw [hXs.lastDone i]; exact h)
  · rw [hF]; exact hkeep.2.2.2.1 i (by rw [hGX]; show (X.dropped.get i).isSome = true; rw [hXs.dropped i]; exact h)
  · rw [hF]; exact hkeep.2.2.2.2 k (by rw [hGX]; show (X.doneDates.get k).isSome = true; rw [hXs.doneDates k]; exact h)
  · rw [valueAt_day_get (hbelowR.1 d hd)]; exact hRbl d hd
  · rw [valueAt_doneDate_get (hbelowR.2.2 i d hd)]; exact hRbd d i hd

end Seal
end Tm
