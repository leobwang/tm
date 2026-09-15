import TmKernel.SealRun
/-!
# SealLaw2E — the policy, the `now` anchor, and the empty checkpoint's guards (stage 5, D9, W2)

Law 3 (`resume_answer_ignores_the_policy`), the anchor (`an_accepted_resume_covers_now`, from the month start and ISO
Monday being monotone), and law 8's pair (`resume_from_empty_never_refuses_by_guard`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State)
open Log (Entry)
open Cal (ys yearOfZ originShift cumBefore monthOfDoy isLeap dayOfDoy yearOfZ_bracket month_bracket doy_in_range
  yearOfZ_ge_one ys_one ys_succ_bounds cumBefore_mono monthOfDoy_mono)

theorem resume_ok_run {z : Cal.Tz} {T : Nat} {k : Ckpt} {b : List Log.Line} {term : Bool} {p : Option Policy}
    {x : Seal.Answer × Option Resealed} (h : resume z T k b term p = .ok x) :
    ∃ run, resumeRun z T k b = .ok run ∧ x = (run.answer, p.bind (fun q => resealOf z T k b term q run)) := by
  unfold resume at h
  cases hr : resumeRun z T k b with
  | error e => rw [hr] at h; simp at h
  | ok run =>
    rw [hr] at h
    simp only [Except.ok.injEq] at h
    exact ⟨run, rfl, h.symm⟩

/-- **Law 3**: the reseal's own answer is the same answer (CRIT 3). -/
theorem resume_answer_ignores_the_policy (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (term : Bool)
    (p : Seal.Policy) (v : Seal.Answer) (x : Option Seal.Resealed)
    (h : Seal.resume z T k b term (some p) = .ok (v, x)) :
    Seal.resume z T k b term none = .ok (v, none) := by
  obtain ⟨run, hrun, hx⟩ := resume_ok_run h
  simp only [Prod.mk.injEq] at hx
  unfold resume
  rw [hrun, hx.1]
  rfl

/-! ## The `now` anchor -/

theorem ys_mono {a b : Nat} (h : a ≤ b) : ys a ≤ ys b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · have h1 := ih (by omega)
      have h2 := (ys_succ_bounds b).1
      omega
    · rw [show a = b + 1 by omega]; exact Nat.le_refl _

theorem monthStart_eq (d : Nat) : Cal.monthStart d = ys (yearOfZ (d + originShift))
    + cumBefore (isLeap (yearOfZ (d + originShift))) (monthOfDoy (isLeap (yearOfZ (d + originShift)))
        (d + originShift - ys (yearOfZ (d + originShift)))) - originShift := by
  have hb := yearOfZ_bracket (d + originShift)
  have hm := month_bracket (isLeap (yearOfZ (d + originShift))) _ (doy_in_range (d + originShift))
  have hy := yearOfZ_ge_one (d + originShift) (by unfold originShift; omega)
  have hys := ys_mono hy
  rw [ys_one] at hys
  show d + 1 - dayOfDoy (isLeap (yearOfZ (d + originShift))) (d + originShift - ys (yearOfZ (d + originShift))) = _
  unfold dayOfDoy
  unfold originShift at *
  omega

theorem cumBefore_le_335 (l : Bool) {m : Nat} (hm : m ≤ 12) : cumBefore l m ≤ 335 := by
  have := cumBefore_mono l (show m < 14 by omega) (show 12 < 14 by omega) hm
  have h12 : cumBefore l 12 ≤ 335 := by cases l <;> decide
  omega

/-- **The first day of the month is monotone.** -/
theorem monthStart_mono {a b : Nat} (h : a ≤ b) : Cal.monthStart a ≤ Cal.monthStart b := by
  rw [monthStart_eq, monthStart_eq]
  have hzab : a + originShift ≤ b + originShift := by omega
  generalize a + originShift = za at hzab ⊢
  generalize b + originShift = zb at hzab ⊢
  have hba := yearOfZ_bracket za
  have hbb := yearOfZ_bracket zb
  have hma := month_bracket (isLeap (yearOfZ za)) _ (doy_in_range za)
  have hmb := month_bracket (isLeap (yearOfZ zb)) _ (doy_in_range zb)
  rcases Nat.lt_or_ge (yearOfZ za) (yearOfZ zb) with hy | hy
  · have h1 := ys_mono (show yearOfZ za + 1 ≤ yearOfZ zb by omega)
    have h2 := cumBefore_le_335 (isLeap (yearOfZ za)) hma.2.1
    have h3 := (ys_succ_bounds (yearOfZ za)).1
    omega
  · have hyy : yearOfZ za = yearOfZ zb := by
      rcases Nat.lt_or_ge (yearOfZ zb) (yearOfZ za) with hy' | hy'
      · have := ys_mono (show yearOfZ zb + 1 ≤ yearOfZ za by omega); omega
      · omega
    rw [hyy] at hma ⊢
    have hmono := monthOfDoy_mono (isLeap (yearOfZ zb))
      (show za - ys (yearOfZ zb) ≤ zb - ys (yearOfZ zb) by omega) (doy_in_range zb)
    have := cumBefore_mono (isLeap (yearOfZ zb))
      (show monthOfDoy (isLeap (yearOfZ zb)) (za - ys (yearOfZ zb)) < 14 by omega)
      (show monthOfDoy (isLeap (yearOfZ zb)) (zb - ys (yearOfZ zb)) < 14 by omega) hmono
    omega

/-- **The ISO Monday is monotone.** -/
theorem isoMonday_mono {a b : Nat} (h : a ≤ b) : Cal.isoMonday a ≤ Cal.isoMonday b :=
  Nat.mul_le_mul_left 7 (Nat.div_le_div_right h)

/-- **The `now` anchor** (§9.1): an accepted resume's today, week, month and auto-close dates are at or after the
horizon. -/
theorem an_accepted_resume_covers_now (z : Cal.Tz) (T : Nat) (k : Seal.Ckpt) (b : List Log.Line) (term : Bool)
    (p : Option Seal.Policy) (x : Seal.Answer × Option Seal.Resealed)
    (h : Seal.resume z T k b term p = .ok x) :
    k.ledgerDay ≤ T ∧ Seal.horizonOf k.ledgerDay ≤ Cal.monthStart T ∧
    Seal.horizonOf k.ledgerDay ≤ Cal.isoMonday T ∧ Seal.horizonOf k.ledgerDay ≤ T - 16 := by
  obtain ⟨run, hrun, -⟩ := resume_ok_run h
  obtain ⟨-, -, hT, -⟩ := resumeRun_ok z T k b run hrun
  refine ⟨hT, ?_, ?_, ?_⟩ <;> unfold horizonOf
  · exact Nat.le_trans (Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)) (monthStart_mono hT)
  · exact Nat.le_trans (Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)) (isoMonday_mono hT)
  · exact Nat.le_trans (Nat.min_le_right _ _) (by unfold autoCloseCatchup; omega)

/-! ## The empty checkpoint refuses no guard -/

theorem horizonOf_zero : horizonOf 0 = 0 := Nat.le_zero.1 (horizonOf_le 0)

theorem keyAtOrAbove_zero (k : Replay.Key) : keyAtOrAbove 0 0 k = true := by
  cases k <;> simp [keyAtOrAbove]

theorem g1_empty (z : Cal.Tz) (N : List Entry) : g1 (Ckpt.empty z) N = none := by
  unfold g1
  rw [List.findSome?_eq_none_iff]
  intro u _
  unfold reachOf
  split <;> simp [Ckpt.empty]

theorem stepCheck_empty (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (stepCheck z dy sl (Ckpt.empty z) st e).2 = none := by
  simp [stepCheck, Ckpt.empty, headSec, horizonOf_zero, keyAtOrAbove_zero]

theorem headerCheck_empty (z : Cal.Tz) (dy : Cal.Instant → Nat) (bs : List Entry) :
    headerCheck dy (Ckpt.empty z) bs = none := by
  unfold headerCheck
  rw [List.findSome?_eq_none_iff]
  intro e _
  simp [Ckpt.empty, headSec]

theorem tailFold_empty (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (sv : List Entry) :
    (tailFold z dy sl (Ckpt.empty z) st sv).2 = none := by
  unfold tailFold
  suffices h : ∀ (sv : List Entry) (acc : State × Option Refusal), acc.2 = none →
      (sv.foldl (tailFoldStep z dy sl (Ckpt.empty z)) acc).2 = none from h sv _ rfl
  intro sv
  induction sv with
  | nil => intro acc h; exact h
  | cons e sv ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    show (acc.2 <|> (stepCheck z dy sl (Ckpt.empty z) acc.1 e).2) = none
    rw [h, stepCheck_empty]
    rfl

/-- **Law 8's pair**: the empty checkpoint is never refused by a guard. -/
theorem resume_from_empty_never_refuses_by_guard (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (term : Bool)
    (p : Option Seal.Policy) (e : Seal.Refusal)
    (h : Seal.resume z T (Seal.Ckpt.empty z) ls term p = .error e) : e.isGuard = false := by
  have hr : resumeRun z T (Ckpt.empty z) ls = .error e := by
    unfold resume at h
    cases hr : resumeRun z T (Ckpt.empty z) ls with
    | error e' => rw [hr] at h; simp only [Except.error.injEq] at h; rw [h]
    | ok r => rw [hr] at h; simp at h
  unfold resumeRun at hr
  split at hr
  · rename_i hz; exact absurd rfl hz
  · split at hr
    · simp only [Except.error.injEq] at hr; rw [← hr]; rfl
    · split at hr
      · rename_i hT; exact absurd hT (Nat.not_lt_zero _)
      · dsimp only at hr
        rw [g1_empty] at hr
        dsimp only at hr
        split at hr
        · rename_i x hx
          rw [tailFold_empty, headerCheck_empty] at hx
          cases hx
        · cases hr

end Seal
end Tm
