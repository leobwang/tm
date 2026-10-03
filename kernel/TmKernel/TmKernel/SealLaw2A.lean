import TmKernel.SealRun
import TmKernel.SealIndex
import TmKernel.SealBounds
import TmKernel.SealStep
import TmKernel.SealMask
/-!
# SealLaw2A — an accepted resume's mask, index and fold are the whole log's (stage 5, D9, W2, law 2's first half)

Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State survivors wakeInstants keptWakes dayOf)
open Log (Entry)

section CkptFields

variable (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn))

theorem ckpt_tagLast : (ckptOfEntries z T₀ L cut es er ws).tagLast = keptTags (foldedSurvivors es er) := by
  simp only [ckptOfEntries]
theorem ckpt_tagOverflow : (ckptOfEntries z T₀ L cut es er ws).tagOverflow
    = decide ((keptTags (foldedSurvivors es er)).length < (tagLines (foldedSurvivors es er)).length) := by
  simp only [ckptOfEntries]
theorem ckpt_settled : (ckptOfEntries z T₀ L cut es er ws).settled = settledOf es er := by simp only [ckptOfEntries]
theorem ckpt_maxT : (ckptOfEntries z T₀ L cut es er ws).maxT
    = maxInstant? ((es.flatMap entryInstants).filter (fun q => !isFuture T₀ q)) := by simp only [ckptOfEntries]
theorem ckpt_futureFloor : (ckptOfEntries z T₀ L cut es er ws).futureFloor
    = minInstant? ((es.flatMap entryInstants).filter (isFuture T₀)) := by simp only [ckptOfEntries]
theorem ckpt_wakes : (ckptOfEntries z T₀ L cut es er ws).wakes = storedWakes L (foldedIndex z es er) := by
  simp only [ckptOfEntries]
theorem ckpt_sleptByDay : (ckptOfEntries z T₀ L cut es er ws).sleptByDay
    = storedSlept (Replay.sleptByDay z (foldedIndex z es er) (foldedSurvivors es er)) L := by simp only [ckptOfEntries]
theorem ckpt_ledgerDay' : (ckptOfEntries z T₀ L cut es er ws).ledgerDay = L := by simp only [ckptOfEntries]

end CkptFields

theorem wakeInstants_append (X Y : List Entry) : wakeInstants (X ++ Y) = wakeInstants X ++ wakeInstants Y := by
  unfold wakeInstants; rw [List.filter_append, List.map_append]

theorem mem_wakeInstants {sv : List Entry} {w : Cal.Instant} (h : w ∈ wakeInstants sv) :
    ∃ e ∈ sv, Replay.isWake e = true ∧ e.t.val = w := by
  unfold wakeInstants at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  exact ⟨e, (List.mem_filter.1 he).1, (List.mem_filter.1 he).2, rfl⟩

theorem mem_foldQueries (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (q : Cal.Instant), q ∈ foldQueries z dy sl st sv →
      ∃ pre e post, sv = pre ++ e :: post ∧ q ∈ stepQueries (pre.foldl (Replay.stepWith z dy sl) st).machine e
  | [], _, _, h => by simp [foldQueries] at h
  | e :: sv, st, q, h => by
    unfold foldQueries at h
    rcases List.mem_append.1 h with h | h
    · exact ⟨[], e, sv, rfl, h⟩
    · obtain ⟨pre, e', post, hs, hq⟩ := mem_foldQueries z dy sl sv _ q h
      exact ⟨e :: pre, e', post, by rw [hs]; rfl, by rw [List.foldl_cons]; exact hq⟩

theorem entryInstants_ns (e : Entry) : ∀ q ∈ entryInstants e, q.ns < 2000000000 := by
  intro q hq
  unfold entryInstants at hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact ns_lt_of_wf _ e.t.property
  rcases List.mem_append.1 hq with hq | hq
  · unfold gapStart? at hq
    split at hq
    · simp only [Option.toList_some, List.mem_singleton] at hq; subst hq
      exact ns_lt_of_wf _ (Cal.subMinutes_wf _ _ e.t.property)
    · split at hq
      · simp only [Option.toList_some, List.mem_singleton] at hq; subst hq
        exact ns_lt_of_wf _ (Cal.subMinutes_wf _ _ e.t.property)
      · simp at hq
    · simp at hq
  · -- a break's end (D87): `addMinutes` keeps the nanoseconds, or takes a leap second's 10⁹ off them
    unfold brkEndAt? at hq
    split at hq
    · simp only [Option.toList_some, List.mem_singleton] at hq; subst hq
      have h := ns_lt_of_wf _ e.t.property
      unfold Replay.brkEnd Replay.addMinutes
      split
      · exact h
      · split <;> (simp only; omega)
    · simp at hq

/-! ## The mask, the separation, the head, and the tail's fold -/

/-- **A1: the survivors of the whole log split at the cut** under G1. -/
theorem resume_survivors (z : Cal.Tz) (T₀ L cut : Nat) (A R B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (A ++ (R ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut A R ws) (unsettled (ckptOfEntries z T₀ L cut A R ws).settled (R ++ B')) = none) :
    survivors (A ++ (R ++ B')) = foldedSurvivors A R ++ survivors (unsettled (settledOf A R) (R ++ B')) := by
  have h := survivors_append_of_g1 A R B' hd (ckptOfEntries z T₀ L cut A R ws) (ckpt_tagLast z T₀ L cut A R ws)
    (ckpt_tagOverflow z T₀ L cut A R ws) (ckpt_settled z T₀ L cut A R ws) hg
  rwa [ckpt_settled] at h

/-- **A2: every surviving tail wake that passed G2 is after the folded non-future instants and inside the fence of the
future ones, and at or after the head second.** -/
theorem resume_sep (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st0 : State)
    (T₀ : Nat) (QA : List Cal.Instant) (SB : List Entry)
    (hmaxT : K.maxT = maxInstant? (QA.filter (fun q => !isFuture T₀ q)))
    (hff : K.futureFloor = minInstant? (QA.filter (isFuture T₀)))
    (hsteps : ∀ pre e post, SB = pre ++ e :: post →
      (stepCheck z dy sl K (pre.foldl (Replay.stepWith z dy sl) st0) e).2 = none) :
    (∀ w ∈ wakeInstants SB, ∀ q ∈ QA, ((fun q => !isFuture T₀ q) q = true → q < w) ∧
      ((fun q => !isFuture T₀ q) q = false → w.sec + fenceSec < q.sec)) ∧
    (∀ w ∈ wakeInstants SB, headSec K.ledgerDay ≤ w.sec) := by
  constructor
  · intro w hw
    obtain ⟨e, he, hwk, rfl⟩ := mem_wakeInstants hw
    obtain ⟨pre, post, hs⟩ := List.append_of_mem he
    obtain ⟨-, h2, -⟩ := stepCheck_none z dy sl K _ e (hsteps pre e post hs)
    obtain ⟨hm, hf⟩ := h2 hwk
    exact sep_of_bounds T₀ QA e.t.val (fun m hm' => hm m (by rw [hmaxT]; exact hm')) (fun f hf' => hf f (by rw [hff]; exact hf'))
  · intro w hw
    obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
    obtain ⟨pre, post, hs⟩ := List.append_of_mem he
    obtain ⟨h1, -, -⟩ := stepCheck_none z dy sl K _ e (hsteps pre e post hs)
    exact h1 e.t.val (List.mem_append_left _ (by simp [entryInstants]))

/-- **A6: the tail's checked fold reads the index only after the head second**, so any index agreeing there gives the
same fold. -/
theorem resume_fold_congr (z : Cal.Tz) (dy₁ dy₂ : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st0 : State)
    (SB : List Entry)
    (hsteps : ∀ pre e post, SB = pre ++ e :: post →
      (stepCheck z dy₁ sl K (pre.foldl (Replay.stepWith z dy₁ sl) st0) e).2 = none)
    (hagree : ∀ q, headSec K.ledgerDay ≤ q.sec → dy₁ q = dy₂ q) :
    SB.foldl (Replay.stepWith z dy₁ sl) st0 = SB.foldl (Replay.stepWith z dy₂ sl) st0 := by
  apply foldl_stepWith_congr
  intro q hq
  obtain ⟨pre, e, post, hs, hqe⟩ := mem_foldQueries z dy₁ sl SB st0 q hq
  obtain ⟨h1, -, -⟩ := stepCheck_none z dy₁ sl K _ e (hsteps pre e post hs)
  exact hagree q (h1 q hqe)

end Seal
end Tm
