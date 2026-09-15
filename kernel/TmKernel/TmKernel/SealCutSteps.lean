import TmKernel.SealCutLows
import TmKernel.SealCutGroup
import TmKernel.SealLaw5A
/-!
# SealCutSteps — the unfolded steps after a reseal (stage 5, D9, W2: laws 6 and 7)

Every step of an accepted tail has, on the whole log's fold, the resumed fold's machine and writes its keys
(`resume_steps`).  A reseal's ledger day is at most the old one or every day an unfolded step names or reads, so an
accepted key or head second stays accepted at the new ledger day (`keyAtOrAbove_later`, `headSec_later`).  The effects
`sealable` collects are those of the unfolded survivors' steps (`mem_collect`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **Every step of an accepted tail, on the whole log's fold**: its machine and the keys its effects write are the
resumed fold's. -/
theorem resume_steps (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (n : Nat) (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none)
    (KW : List Cal.Instant) (hKW : KW = keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv))
    (SL : Nat → Option Nat) (G : State)
    (hG : G = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL) (State.init (As ++ (Rs ++ B')).length))
    (pre : List Entry) (e : Entry) (post : List Entry) (hs : sv = pre ++ e :: post) :
    (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine
        = (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)).machine ∧
    (Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e).map Effect.key
        = (Replay.effectsWith z (dayOf z kw) sl (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).map
            Effect.key := by
  obtain ⟨-, hI1, hI2, -⟩ := resume_index z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps
  rw [← hKW] at hI1 hI2
  subst hK
  have hKL := ckpt_ledgerDay' z T₀ L cut As Rs ws
  have hGa : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) := by
    rw [hG]; exact folded_part_agrees z T₀ L cut As Rs ws n _ KW SL hI1
  have hcongr : ∀ pre post, sv = pre ++ post →
      pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n) := by
    intro pre post hs
    refine resume_fold_congr z (dayOf z kw) (dayOf z KW) sl _ _ pre
      (fun pre' e' post' h' => hsteps pre' e' (post' ++ post) (by rw [hs, h']; simp)) (fun q hq => ?_)
    exact (hI2 q (by rwa [hKL] at hq)).symm
  obtain ⟨hmach, hkeys⟩ := steps_agree z T₀ L cut As Rs ws n sv KW (dayOf z kw) sl SL G hGa hI2 hcongr
  have hmm := hmach pre (e :: post) hs
  have hc := stepCheck_none z (dayOf z kw) sl _ _ e (hsteps pre e post hs)
  rw [hKL] at hc
  refine ⟨hmm.symm, (hkeys pre e post hs ?_).symm⟩
  rw [← hmm]; exact hc.1

/-- **An accepted key stays accepted at a later ledger day bounded by its date.** -/
theorem keyAtOrAbove_later (L L' : Nat) (k : Replay.Key) (hLL : L ≤ L') (hk : keyAtOrAbove L (horizonOf L) k = true)
    (hlow : ∀ dd, k.date? = some dd → L' ≤ Nat.max L dd) : keyAtOrAbove L' (horizonOf L') k = true := by
  have hwin : ∀ d, horizonOf L ≤ d → L' ≤ Nat.max L d → horizonOf L' ≤ d := by
    intro d hd hl
    have hm : Nat.max L d = max L d := rfl
    by_cases hLd : L ≤ d
    · have hH' := horizonOf_le L'
      omega
    · have hL' : L' = L := by omega
      rw [hL']; exact hd
  cases k with
  | day d =>
    have h1 := hlow d rfl
    have hm : Nat.max L d = max L d := rfl
    simp only [keyAtOrAbove, decide_eq_true_eq] at hk ⊢
    omega
  | itemDay i d =>
    simp only [keyAtOrAbove, decide_eq_true_eq] at hk ⊢; exact hwin d hk (hlow d rfl)
  | doneDate i d =>
    simp only [keyAtOrAbove, decide_eq_true_eq] at hk ⊢; exact hwin d hk (hlow d rfl)
  | instDate item inst d =>
    simp only [keyAtOrAbove, decide_eq_true_eq] at hk ⊢; exact hwin d hk (hlow d rfl)
  | item i => rfl
  | machine => rfl
  | global => rfl
  | instOther item inst => rfl
  | named name id => rfl

/-- **An accepted head second stays accepted at a later ledger day bounded by its day.** -/
theorem headSec_later (L L' sec : Nat) (hh : headSec L ≤ sec) (hlow : L' ≤ Nat.max L (sec / 86400 + 1)) :
    headSec L' ≤ sec := by
  unfold headSec at *
  by_cases h : L ≤ sec / 86400 + 1
  · have hmx : Nat.max L (sec / 86400 + 1) = sec / 86400 + 1 := Nat.max_eq_right h
    rw [hmx] at hlow
    exact Nat.le_trans (Nat.mul_le_mul_right 86400 (Nat.sub_le_of_le_add hlow)) (Nat.div_mul_le_self sec 86400)
  · have hmx : Nat.max L (sec / 86400 + 1) = L := Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le h))
    rw [hmx] at hlow
    exact Nat.le_trans (Nat.mul_le_mul_right 86400 (Nat.sub_le_sub_right hlow 1)) hh

/-- One step of `unfoldedEffects`' fold. -/
def collectStep (z : Cal.Tz) (kw : List Cal.Instant) (sl : List (Nat × Nat)) (acc : State × List (List Effect))
    (e : Entry) : State × List (List Effect) :=
  let fx := Replay.effects z kw sl acc.1 e
  (Replay.applyEffects acc.1 fx, fx :: acc.2)

theorem unfoldedEffects_eq (z : Cal.Tz) (es er : List Entry) :
    unfoldedEffects z es er =
      ((((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst).foldl
        (collectStep z (keptWakes z (wakeInstants (foldedSurvivors es er ++
            ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst)))
          (Replay.sleptByDay z (keptWakes z (wakeInstants (foldedSurvivors es er ++
            ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst)))
            (foldedSurvivors es er ++ ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map
              Prod.fst)))
        ((foldedSurvivors es er).foldl
          (Replay.step z (keptWakes z (wakeInstants (foldedSurvivors es er ++
            ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst)))
          (Replay.sleptByDay z (keptWakes z (wakeInstants (foldedSurvivors es er ++
            ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst)))
            (foldedSurvivors es er ++ ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map
              Prod.fst))) (State.init (es ++ er).length), [])).2.reverse.flatten := rfl

/-- **Every effect `sealable` collects is one of an unfolded survivor's step.** -/
theorem mem_collect (z : Cal.Tz) (kw : List Cal.Instant) (sl : List (Nat × Nat)) :
    ∀ (tv : List Entry) (st : State) (acc : List (List Effect)) (x : Effect),
      x ∈ (tv.foldl (collectStep z kw sl) (st, acc)).2.reverse.flatten →
        x ∈ acc.reverse.flatten ∨ ∃ pre e post, tv = pre ++ e :: post ∧
          x ∈ Replay.effects z kw sl (pre.foldl (Replay.step z kw sl) st) e
  | [], _, _, _, h => Or.inl h
  | e :: tv, st, acc, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_collect z kw sl tv _ _ x h with h' | ⟨pre, e', post, hs, hx⟩
    · simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.mem_append] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨[], e, tv, rfl, h'⟩
    · exact Or.inr ⟨e :: pre, e', post, by rw [hs]; rfl, hx⟩

/-- **The survivors of appended lists are the folded survivors then the unfolded ones.** -/
theorem survivors_split (es er : List Entry) :
    survivors (es ++ er) = foldedSurvivors es er
      ++ ((er.zipIdx es.length).filter (fun p => !Replay.cancelledAt (es ++ er) p.2)).map Prod.fst := by
  rw [Replay.survivors_are_the_uncancelled_entries, List.zipIdx_append, List.filter_append, List.map_append,
    Nat.zero_add]
  rfl

end Seal
end Tm
