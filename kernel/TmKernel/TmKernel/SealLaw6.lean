import TmKernel.SealLaw6Ckpt
import TmKernel.SealLaw6Seal
import TmKernel.SealTagsSelf
/-!
# SealLaw6 — laws 6 and 7: a reseal is a seal, and accepts its own suffix (stage 5, D9, W2)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.4 and §9.5.  Law 6 (`reseal_is_seal`): an emitted reseal's
checkpoint is the checkpoint of the lines up to its fold point knowing the rest, sealable at the new ledger day `L ≥ L`,
and its records are those lines' records of `[L, L')` and `[H, H')` (`rs_state_parts`, `rs_sealable_reachFree`).  Law 7
(`a_resealed_checkpoint_accepts_its_own_suffix`): by law 5 on the resealed checkpoint, since `L' ≤ T`, the suffix meets
the reach condition at `L'`, and a checkpoint's own suffix leaves no undo dangling (`tagsClear_self`).
Specification only (D9-21).
-/
namespace Tm
namespace Seal

/-- **Law 6, two-run** (§9.5, §15): a reseal is a seal, never behind its ledger day. -/
theorem reseal_is_seal (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Seal.Policy)
    (v : Seal.Answer) (s : Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term (some p) = .ok (v, some s)) :
    let k  := Seal.ckptOf z T₀ L a r
    let j  := Seal.foldPoint z T k b term p
    let L' := Seal.sealDay z T k b term p
    L ≤ L' ∧ Seal.sealable z T L' (a ++ b.take j) (b.drop j) = true ∧
    s.ckpt = Seal.ckptOf z T L' (a ++ b.take j) (b.drop j) ∧
    s.days = Seal.dayRecordsBetween z T L L' (a ++ b.take j) ∧
    s.window = Seal.windowRecordsBetween z T (Seal.horizonOf L) (Seal.horizonOf L') (a ++ b.take j) := by
  dsimp only
  obtain ⟨run, hrun, hseal, -⟩ := resume_some_reseal z T _ b term p v s h
  obtain ⟨hmig, hcut⟩ := resealOf_some z T _ b term p run s hseal
  obtain ⟨hsck, hsdays, hswin⟩ := resealOf_parts z T _ b term p run s hseal
  obtain ⟨hC, hD, hW⟩ := rs_state_parts z T₀ T L a r b term p run _ hc hr hrun hmig hcut
  obtain ⟨hS, -⟩ := rs_sealable_reachFree z T₀ T L a r b term p run _ hc hr hs hrun hmig hcut
  rw [foldPoint_eq z T _ b term p run hrun, sealDay_eq z T _ b term p run hrun, hsck, hsdays, hswin]
  exact ⟨le_sealDayOf z T (ckptOf z T₀ L a r) p run _, hS, hC, hD, hW⟩

/-- **Law 7, no loop** (§9.4, §15): a resealed checkpoint accepts its own unfolded suffix at every later day. -/
theorem a_resealed_checkpoint_accepts_its_own_suffix (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line)
    (term : Bool) (p : Seal.Policy) (v : Seal.Answer) (s : Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term (some p) = .ok (v, some s))
    (T' : Nat) (hT : T ≤ T') (term' : Bool) :
    (Seal.resume z T' s.ckpt (b.drop (Seal.foldPoint z T (Seal.ckptOf z T₀ L a r) b term p)) term' none).isOk = true := by
  obtain ⟨run, hrun, hseal, -⟩ := resume_some_reseal z T _ b term p v s h
  obtain ⟨hmig, hcut⟩ := resealOf_some z T _ b term p run s hseal
  obtain ⟨hsck, -, -⟩ := resealOf_parts z T _ b term p run s hseal
  obtain ⟨hC, -, -⟩ := rs_state_parts z T₀ T L a r b term p run _ hc hr hrun hmig hcut
  obtain ⟨hS, hRF⟩ := rs_sealable_reachFree z T₀ T L a r b term p run _ hc hr hs hrun hmig hcut
  have hLT : L ≤ T := (resumeRun_ok z T _ b run hrun).2.2.1
  have hbd := sealDayOf_bound z T (ckptOf z T₀ L a r) p run (foldPointOf z T (ckptOf z T₀ L a r) b term p run)
  have hjle := (cutOk_parts hcut).1
  rw [foldPoint_eq z T _ b term p run hrun, hsck, hC]
  generalize foldPointOf z T (ckptOf z T₀ L a r) b term p run = j at hS hRF hbd hjle ⊢
  generalize sealDayOf z T (ckptOf z T₀ L a r) p run j = L' at hS hRF hbd ⊢
  have hc' : Log.contiguousFrom 1 ((a ++ b.take j) ++ b.drop j) = true := by
    rw [List.append_assoc, List.take_append_drop]; exact hc
  rw [resume_ok_iff z T T' L' (a ++ b.take j) (b.drop j) (b.drop j) term' none hc' (List.prefix_refl _) hS,
    tagsClear_self z T L' (a ++ b.take j) (b.drop j) hc', hRF]
  have hLT' : L' ≤ T' := by
    rcases hbd with h1 | h1
    · have : (ckptOf z T₀ L a r).ledgerDay = L := rfl
      omega
    · omega
  simp [hLT']

end Seal
end Tm
