import TmKernel.SealFoldPoint
import TmKernel.SealLaw2A
/-!
# SealLaw6Pair — a reseal never seals past `now` (stage 5, D9, W2: law 6's pair)

The new ledger day is the old one, or the least of bounds that include `F ≤ T − keepDays` (CRIT 1).  Specification
only (D9-21).
-/
namespace Tm
namespace Seal

open Log (Entry)

theorem foldl_min_le : ∀ (l : List Nat) (x : Nat), l.foldl Nat.min x ≤ x
  | [], _ => Nat.le_refl _
  | a :: l, x => Nat.le_trans (foldl_min_le l (Nat.min x a)) (Nat.min_le_left _ _)

theorem floorOf_le (T keep : Nat) (dy : Cal.Instant → Nat) (sv : List Entry) : floorOf T keep dy sv ≤ T - keep :=
  Nat.min_le_left _ _

theorem max_foldl_min_bound (L T keep F : Nat) (lows : List Nat) (hF : F ≤ T - keep) :
    Nat.max L (lows.foldl Nat.min F) = L ∨ Nat.max L (lows.foldl Nat.min F) + keep ≤ T := by
  have hm := Nat.le_trans (foldl_min_le lows F) hF
  generalize lows.foldl Nat.min F = m at hm ⊢
  rcases Nat.le_total m L with h | h
  · exact Or.inl (Nat.max_eq_left h)
  · by_cases hk : keep ≤ T
    · right
      have hmx : Nat.max L m = m := Nat.max_eq_right h
      rw [hmx]; omega
    · left; exact Nat.max_eq_left (by omega)

/-- **A reseal's ledger day stays, or is at least `keepDays` before `now`.** -/
theorem sealDayOf_bound (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j : Nat) :
    sealDayOf z T K p r j = K.ledgerDay ∨ sealDayOf z T K p r j + p.keepDays ≤ T := by
  unfold sealDayOf
  exact max_foldl_min_bound _ _ _ _ _ (floorOf_le _ _ _ _)

theorem le_sealDayOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j : Nat) :
    K.ledgerDay ≤ sealDayOf z T K p r j := by
  unfold sealDayOf
  exact Nat.le_max_left _ _

/-- **Law 6's pair**: a reseal never seals past `now` (CRIT 1). -/
theorem a_reseal_never_seals_past_now (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool)
    (p : Seal.Policy) (v : Seal.Answer) (s : Seal.Resealed)
    (_hc : Log.contiguousFrom 1 (a ++ b) = true) (_hr : r <+: b) (_hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term (some p) = .ok (v, some s)) :
    Seal.sealDay z T (Seal.ckptOf z T₀ L a r) b term p = L ∨
    Seal.sealDay z T (Seal.ckptOf z T₀ L a r) b term p + p.keepDays ≤ T := by
  obtain ⟨run, hrun, -, -⟩ := resume_some_reseal z T _ b term p v s h
  rw [sealDay_eq z T _ b term p run hrun]
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := ckpt_ledgerDay' z T₀ L _ _ _ _
  rcases sealDayOf_bound z T (ckptOf z T₀ L a r) p run (foldPointOf z T (ckptOf z T₀ L a r) b term p run) with h1 | h1
  · left; rw [h1, hKL]
  · right; exact h1

end Seal
end Tm
