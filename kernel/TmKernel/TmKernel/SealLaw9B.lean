import TmKernel.SealLaw9A
import TmKernel.SealLaw2F
import TmKernel.SealLaw4
/-!
# SealLaw9B — one call of genesis (stage 5, D9, W2: law 9)

Law 9's invariant for a stack entry (`GenOk`): its checkpoint is the checkpoint of the lines up to its cut, sealable,
knowing the lines its call read, and its records are those lines' below its horizons.  One accepted call from such an
entry through a chunk end (`genesis_call`): its answer is the answer of the lines through that end (law 2), the entry's
records are theirs below its horizons (law 4), and a reseal pushes an entry meeting the invariant (laws 6 and 7, and
law 4 on the resealed checkpoint), whose extra records are at or above the answer's horizons (`ResultOk`).
Specification only (D9-21).
-/
namespace Tm
namespace Seal

/-- **A stack entry of genesis over lines `ls`** (law 9's invariant). -/
def GenOk (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (E : GenEntry) : Prop :=
  ∃ (T₀ L : Nat), E.ckpt = ckptOf z T₀ L (ls.take E.ckpt.cut) (genLines ls E.ckpt E.known) ∧
    sealable z T₀ L (ls.take E.ckpt.cut) (genLines ls E.ckpt E.known) = true ∧
    E.ckpt.cut ≤ E.known ∧ E.known ≤ ls.length ∧
    E.days = dayRecordsBetween z T 0 L (ls.take E.ckpt.cut) ∧
    E.window = windowRecordsBetween z T 0 (horizonOf L) (ls.take E.ckpt.cut)

/-- **A call's answer through line `e`, and its top entry's records** (law 9's invariant after a call). -/
def ResultOk (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (e : Nat) (E : GenEntry) (v : Seal.Answer) : Prop :=
  ∃ (T₀ L : Nat) (X : List DayRecord) (W : List WindowRecord), v = answer (ckptOf z T₀ L (ls.take e) []) ∧
    E.days = dayRecordsBetween z T 0 L (ls.take e) ++ X ∧ (∀ r ∈ X, L ≤ r.day) ∧
    E.window = windowRecordsBetween z T 0 (horizonOf L) (ls.take e) ++ W ∧ (∀ w ∈ W, horizonOf L ≤ w.day)

/-- The empty checkpoint is genesis' first entry. -/
theorem genOk_empty (z : Cal.Tz) (T : Nat) (ls : List Log.Line) : GenOk z T ls ⟨Ckpt.empty z, [], [], 0⟩ := by
  refine ⟨0, 0, ?_, ?_, Nat.le_refl 0, Nat.zero_le _, ?_, ?_⟩
  · show Ckpt.empty z = ckptOf z 0 0 (ls.take 0) ((ls.drop 0).take (0 - 0))
    simp only [List.take_zero]
    exact (the_checkpoint_of_nothing_is_the_empty_checkpoint z).symm
  · show sealable z 0 0 (ls.take 0) ((ls.drop 0).take (0 - 0)) = true
    simp only [List.take_zero]
    exact sealable_empty z
  · show [] = dayRecordsBetween z T 0 0 (ls.take 0)
    unfold dayRecordsBetween dayRecordsOfEntries daysIn
    simp
  · show [] = windowRecordsBetween z T 0 (horizonOf 0) (ls.take 0)
    rw [horizonOf_zero]
    unfold windowRecordsBetween windowRecordsOfEntries windowsIn
    simp

/-- **One accepted call of genesis.** -/
theorem genesis_call (z : Cal.Tz) (T : Nat) (ls : List Log.Line) (p : Policy) (hc : Log.contiguousFrom 1 ls = true)
    (E : GenEntry) (hE : GenOk z T ls E) (e : Nat) (hke : E.known ≤ e) (hel : e ≤ ls.length) (t : Bool)
    (v : Seal.Answer) (x : Option Resealed)
    (h : resume z T E.ckpt (genLines ls E.ckpt e) t (some p) = .ok (v, x)) :
    (x = none → ResultOk z T ls e E v) ∧
    (∀ s, x = some s → GenOk z T ls ⟨s.ckpt, E.days ++ s.days, E.window ++ s.window, e⟩ ∧
      ResultOk z T ls e ⟨s.ckpt, E.days ++ s.days, E.window ++ s.window, e⟩ v) := by
  obtain ⟨T₀, L, hK, hs, hck, hkl, hD, hW⟩ := hE
  have hgl : ∀ n, genLines ls E.ckpt n = (ls.drop E.ckpt.cut).take (n - E.ckpt.cut) := fun n => rfl
  rw [hgl] at hK hs h
  generalize hc0 : E.ckpt.cut = c at hK hs hck hD hW h
  generalize ha : ls.take c = a at hK hs hD hW
  generalize hr : (ls.drop c).take (E.known - c) = r at hK hs
  generalize hb : (ls.drop c).take (e - c) = b at h
  have hab : a ++ b = ls.take e := by rw [← ha, ← hb]; exact genLines_append ls c e (by omega)
  have hcab : Log.contiguousFrom 1 (a ++ b) = true := by rw [hab]; exact contiguousFrom_take 1 ls e hc
  have hrb : r <+: b := by rw [← hr, ← hb]; exact List.take_prefix_take_left (by omega)
  rw [hK] at h
  -- the answer and the records below `L`
  obtain ⟨run, hrun, hvrun⟩ := resume_ok_answer h
  have hv : v = answer (ckptOf z T₀ L (ls.take e) []) := by
    rw [← hvrun, resume_answer_eq z T₀ T L a r b run hcab hrb hrun, hab]
  obtain ⟨hDb, hWb⟩ := resume_keeps_the_sealed_records z T₀ T L a r b t (some p) (v, x) hcab hrb hs h
  have hDe : E.days = dayRecordsBetween z T 0 L (ls.take e) := by
    rw [hD, ← hab]; exact hDb.symm
  have hWe : E.window = windowRecordsBetween z T 0 (horizonOf L) (ls.take e) := by
    rw [hW, ← hab]; exact hWb.symm
  refine ⟨fun _ => ⟨T₀, L, [], [], hv, by rw [List.append_nil]; exact hDe, by simp,
    by rw [List.append_nil]; exact hWe, by simp⟩, fun s hx => ?_⟩
  subst hx
  -- laws 6 and 7 on this call
  obtain ⟨hLL, hS, hck', hsd, hsw⟩ := reseal_is_seal z T₀ T L a r b t p v s hcab hrb hs h
  have h7 := a_resealed_checkpoint_accepts_its_own_suffix z T₀ T L a r b t p v s hcab hrb hs h T (Nat.le_refl T) t
  obtain ⟨run', hrun', hseal', -⟩ := resume_some_reseal z T _ b t p v s h
  have hjle : foldPoint z T (ckptOf z T₀ L a r) b t p ≤ b.length := by
    rw [foldPoint_eq z T _ b t p run' hrun']
    exact (cutOk_parts (resealOf_some z T _ b t p run' s hseal').2).1
  generalize foldPoint z T (ckptOf z T₀ L a r) b t p = j at hS hck' hsd hsw h7 hjle
  generalize sealDay z T (ckptOf z T₀ L a r) b t p = L' at hLL hS hck' hsd hsw
  have hblen : b.length = e - c := by rw [← hb]; exact length_genLines ls c e hel
  have hcl : c ≤ ls.length := by omega
  have hcut' : s.ckpt.cut = c + j := by
    rw [hck']
    show (a ++ b.take j).length = c + j
    rw [List.length_append, List.length_take, ← ha, List.length_take]
    omega
  have htake : ls.take (c + j) = a ++ b.take j := by
    rw [← ha, ← hb, genLines_take ls c e j (by omega), ← List.take_add]
  have hdrop : (ls.drop (c + j)).take (e - (c + j)) = b.drop j := by
    rw [← hb, genLines_drop]
  have hgl' : genLines ls s.ckpt e = b.drop j := by
    unfold genLines; rw [hcut', hdrop]
  -- the resealed checkpoint's records below its horizons
  obtain ⟨x', hx'⟩ := (isOk_iff_exists _).1 h7
  have hc' : Log.contiguousFrom 1 ((a ++ b.take j) ++ b.drop j) = true := by
    rw [List.append_assoc, List.take_append_drop]; exact hcab
  rw [hck'] at hx'
  obtain ⟨hDb', hWb'⟩ := resume_keeps_the_sealed_records z T T L' (a ++ b.take j) (b.drop j) (b.drop j) t none x' hc'
    (List.prefix_refl _) hS hx'
  have hbelowD : dayRecordsBetween z T 0 L' (a ++ b) = dayRecordsBetween z T 0 L' (a ++ b.take j) := by
    have := hDb'; rw [List.append_assoc, List.take_append_drop] at this; exact this
  have hbelowW : windowRecordsBetween z T 0 (horizonOf L') (a ++ b)
      = windowRecordsBetween z T 0 (horizonOf L') (a ++ b.take j) := by
    have := hWb'; rw [List.append_assoc, List.take_append_drop] at this; exact this
  have hdays : E.days ++ s.days = dayRecordsBetween z T 0 L' (a ++ b.take j) := by
    rw [hsd, hDe, ← hab, dayRecordsBetween_restrict z T L L' (a ++ b.take j), ← hbelowD,
      ← dayRecordsBetween_restrict z T L L' (a ++ b), ← dayRecordsBetween_split z T L L' (a ++ b) hLL]
  have hwins : E.window ++ s.window = windowRecordsBetween z T 0 (horizonOf L') (a ++ b.take j) := by
    rw [hsw, hWe, ← hab, windowRecordsBetween_restrict z T (horizonOf L) (horizonOf L') (a ++ b.take j), ← hbelowW,
      ← windowRecordsBetween_restrict z T (horizonOf L) (horizonOf L') (a ++ b),
      ← windowRecordsBetween_split z T (horizonOf L) (horizonOf L') (a ++ b) (horizonOf_mono hLL)]
  refine ⟨⟨T, L', ?_, ?_, ?_, hel, ?_, ?_⟩, T₀, L, s.days, s.window, hv, ?_, fun r hr => ?_, ?_, fun w hw => ?_⟩
  · show s.ckpt = ckptOf z T L' (ls.take s.ckpt.cut) (genLines ls s.ckpt e)
    rw [hgl', hcut', htake]; exact hck'
  · show sealable z T L' (ls.take s.ckpt.cut) (genLines ls s.ckpt e) = true
    rw [hgl', hcut', htake]; exact hS
  · show s.ckpt.cut ≤ e
    rw [hcut']; omega
  · show E.days ++ s.days = dayRecordsBetween z T 0 L' (ls.take s.ckpt.cut)
    rw [hcut', htake]; exact hdays
  · show E.window ++ s.window = windowRecordsBetween z T 0 (horizonOf L') (ls.take s.ckpt.cut)
    rw [hcut', htake]; exact hwins
  · show E.days ++ s.days = dayRecordsBetween z T 0 L (ls.take e) ++ s.days
    rw [hDe]
  · rw [hsd] at hr; exact (mem_dayRecordsBetween z T L L' _ r hr).1
  · show E.window ++ s.window = windowRecordsBetween z T 0 (horizonOf L) (ls.take e) ++ s.window
    rw [hWe]
  · rw [hsw] at hw; exact (mem_windowRecordsBetween z T _ _ _ w hw).1

end Seal
end Tm
