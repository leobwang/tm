import TmKernel.SealResume
/-!
# SealReach — law 5's spec side: `reachFree` and `tagsClear` (stage 5, D9, W2)

Design §9.5 law 5.  `reachFree z T₀ L a b` is stated on the whole list `a ++ b`: its survivors, its day index, its
`slept_by_day` and its fold.  In three parts:
- every surviving wake of `b` is later than every instant of `a` that is not future at `T₀`, and more than the fence
  (`fenceSec`) before every future one;
- every entry of `b`, cancelled or not, is at or after the head second of `L` and on a day at or after `L`;
- every surviving entry of `b`, at its step of the whole log's fold, reads the index only at or after the head second
  and names only keys at or above the horizons (`tailStepsOk`).

§9.5's first part ("no undo of `b` cancels a line of `a` that a settled record does not already account for") is
implied by `tagsClear`, G1's conservative condition (§7.4) on the specification's tags (`tagReach`), with which
law 5 conjoins it.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect survivors wakeInstants keptWakes dayOf isWake)
open Log (Entry)

/-- **A fold's accumulated check**: every step's condition, read at the state before it. -/
def foldAll (step : State → Entry → State) (P : State → Entry → Bool) (l : List Entry) (st : State) : Bool :=
  (l.foldl (fun (acc : State × Bool) e => (step acc.1 e, acc.2 && P acc.1 e)) (st, true)).2

/-- **The whole log's surviving tail steps read the index at or after the head second and name keys at or above the
horizons.** -/
def tailStepsOk (z : Cal.Tz) (L : Nat) (Bs E : List Entry) : Bool :=
  foldAll (Replay.stepWith z (dayOf z (keptWakes z (wakeInstants (survivors E))))
      (Replay.KMap.get (Replay.sleptByDay z (keptWakes z (wakeInstants (survivors E))) (survivors E))))
    (fun st e => !Bs.contains e ||
      ((stepQueries st.machine e).all (fun q => decide (headSec L ≤ q.sec)) &&
       (Replay.effectsWith z (dayOf z (keptWakes z (wakeInstants (survivors E))))
          (Replay.KMap.get (Replay.sleptByDay z (keptWakes z (wakeInstants (survivors E))) (survivors E))) st e).all
         (fun x => keyAtOrAbove L (horizonOf L) x.key)))
    (survivors E) (State.init E.length)

/-- **Law 5's spec side of G2 and G3 on the whole list** (§9.5). -/
def reachFree (z : Cal.Tz) (T₀ L : Nat) (a b : List Log.Line) : Bool :=
  ((survivors (Log.lineEntries a ++ Log.lineEntries b)).filter
      (fun e => (Log.lineEntries b).contains e && isWake e)).all (fun w =>
    ((Log.lineEntries a).flatMap entryInstants).all (fun q =>
      if isFuture T₀ q then decide (w.t.val.sec + fenceSec < q.sec) else decide (q < w.t.val)))
  && (Log.lineEntries b).all (fun e => decide (headSec L ≤ e.t.val.sec) &&
      decide (L ≤ dayOf z (keptWakes z (wakeInstants (survivors (Log.lineEntries a ++ Log.lineEntries b)))) e.t.val))
  && tailStepsOk z L (Log.lineEntries b) (Log.lineEntries a ++ Log.lineEntries b)

/-- **G1 for one undo, on the specification's tags**: a folded survivor may carry its tag. -/
def tagReach (sv : List Entry) (u : Entry) : Bool :=
  match u.ev with
  | .undo of_ _ => (keptTags sv).any (fun p => p.1 == of_) ||
      (!Log.isKnownTag of_ && decide ((keptTags sv).length < (tagLines sv).length))
  | _ => false

/-- **G1's conservative tag condition** (§7.4): no undo of `b` that dangles there, its settled undos set aside, has a
tag a folded survivor of `a` may carry. -/
def tagsClear (_z : Cal.Tz) (_T₀ _L : Nat) (a r b : List Log.Line) : Bool :=
  !((Replay.danglingOf (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries b))).2.any
    (tagReach (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))))

theorem foldAll_iff (step : State → Entry → State) (P : State → Entry → Bool) :
    ∀ (l : List Entry) (st : State) (b : Bool),
      (l.foldl (fun (acc : State × Bool) e => (step acc.1 e, acc.2 && P acc.1 e)) (st, b)).2 = true ↔
        b = true ∧ ∀ pre e post, l = pre ++ e :: post → P (pre.foldl step st) e = true
  | [], st, b => by simp
  | e :: l, st, b => by
    rw [List.foldl_cons, foldAll_iff step P l (step st e) (b && P st e)]
    constructor
    · rintro ⟨hb, h⟩
      simp only [Bool.and_eq_true] at hb
      refine ⟨hb.1, fun pre e' post hs => ?_⟩
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact hb.2
      | cons x pre' =>
        simp only [List.cons_append, List.cons.injEq] at hs
        obtain ⟨rfl, hs'⟩ := hs
        exact h pre' e' post hs'
    · rintro ⟨hb, h⟩
      have h0 := h [] e l rfl
      simp only [List.foldl_nil] at h0
      refine ⟨by simp [hb, h0], fun pre e' post hs => ?_⟩
      exact h (e :: pre) e' post (by rw [hs]; rfl)

theorem foldAll_eq_true (step : State → Entry → State) (P : State → Entry → Bool) (l : List Entry) (st : State) :
    foldAll step P l st = true ↔ ∀ pre e post, l = pre ++ e :: post → P (pre.foldl step st) e = true := by
  unfold foldAll
  rw [foldAll_iff]
  simp

/-- **`tagsClear` is G1 accepting** the checkpoint of `a` knowing `r`, over `b`. -/
theorem tagsClear_iff (z : Cal.Tz) (T₀ L : Nat) (a r b : List Log.Line) :
    tagsClear z T₀ L a r b = true ↔
      g1 (ckptOf z T₀ L a r) (unsettled (ckptOf z T₀ L a r).settled (Log.lineEntries b)) = none := by
  have hset : (ckptOf z T₀ L a r).settled = settledOf (Log.lineEntries a) (Log.lineEntries r) := by
    simp only [ckptOf, ckptOfEntries]
  have htl : (ckptOf z T₀ L a r).tagLast = keptTags (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) := by
    simp only [ckptOf, ckptOfEntries]
  have hto : (ckptOf z T₀ L a r).tagOverflow = decide ((keptTags (foldedSurvivors (Log.lineEntries a)
      (Log.lineEntries r))).length < (tagLines (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))).length) := by
    simp only [ckptOf, ckptOfEntries]
  unfold tagsClear g1
  rw [hset, List.findSome?_eq_none_iff, Bool.not_eq_true', List.any_eq_false]
  generalize foldedSurvivors (Log.lineEntries a) (Log.lineEntries r) = SA at htl hto
  generalize (Replay.danglingOf (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r))
    (Log.lineEntries b))).2 = D
  have hone : ∀ u, reachOf (ckptOf z T₀ L a r) u = none ↔ ¬ tagReach SA u = true := by
    intro u
    unfold reachOf tagReach
    split
    · rename_i x of_ id hev
      simp only [hev]
      rw [htl, hto]
      cases hf : (keptTags SA).find? (fun p => p.1 == of_) with
      | some p =>
        have hp := List.find?_some hf
        have hany : (keptTags SA).any (fun p => p.1 == of_) = true :=
          List.any_eq_true.2 ⟨p, List.mem_of_find?_eq_some hf, hp⟩
        simp [hany]
      | none =>
        have hany : (keptTags SA).any (fun p => p.1 == of_) = false := by
          rw [List.any_eq_false]; intro x hx hx'; exact absurd hx' (List.find?_eq_none.1 hf x hx)
        dsimp only
        rw [hany, Bool.false_or]
        by_cases hc : (!Log.isKnownTag of_ && decide ((keptTags SA).length < (tagLines SA).length)) = true
        · rw [if_pos hc]; simp [hc]
        · rw [if_neg hc]; simp [hc]
    · simp
  constructor
  · intro h u hu
    exact (hone u).2 (h u (List.mem_reverse.1 hu))
  · intro h u hu
    exact (hone u).1 (h u (List.mem_reverse.2 hu))

end Seal
end Tm
