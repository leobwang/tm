import TmKernel.SealBits
import TmKernel.SealRestore
/-!
# SealHeaders — the headers a resume reads, day by day (stage 5, D9, W2)

A checkpoint's stored headers, read on a day at or after its ledger day, are the folded lines' headers on that day
(`storedHeaders_filter`); the tail's headers carry each entry's day on the tail's index and whether it survives the
unsettled tail (`tailHeaders_eq_spec`, whose foldl form is `tailHeaders_foldl` and whose specification-side
equality is `tailHeadersSpec_eq`).  Specification only (D9-21).  (This read tailHeaders_eq until W-19 — a prefix of three
real names and the name of none of them.  Unbackticked on purpose; README gap 830.)
-/
namespace Tm
namespace Seal

open Replay (State HeaderRec survivors)
open Log (Entry)

theorem storedHeaders_filter (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn)) (d : Nat)
    (hd : L ≤ d) :
    (storedHeaders (ckptOfEntries z T₀ L cut es er ws)).filter (fun p => decide (p.1 = d))
      = (foldedHeaders z es er).filter (fun p => decide (p.1 = d)) := by
  unfold storedHeaders
  rw [ckpt_openDays]
  generalize foldedState z es er = st
  generalize foldedHeaders z es er = hs
  rw [openDays_flatMap]
  have e : (fun d' => (openDayOf st hs d').headers.map (fun h => ((openDayOf st hs d').day, h)))
      = (fun d' => hs.filter (fun p => decide (p.1 = d'))) := by
    funext d'
    show ((hs.filter (fun p => decide (p.1 = d'))).map Prod.snd).map (fun h => (d', h)) = _
    rw [List.map_map]
    exact map_pair_of_fst _ d' (fun p hp => of_decide_eq_true (List.mem_filter.1 hp).2)
  rw [e]
  exact restore_list Prod.fst hs st hs L d hd (fun h => filter_day_eq_nil hs Prod.fst d (not_mem_dayKeys h).2.2.2.2.2.2.2.1)

theorem unsettled_cons (S : List Nat) (e : Entry) (bs : List Entry) :
    unsettled S (e :: bs) = if e.ev.isUndo && S.contains e.line then unsettled S bs else e :: unsettled S bs := by
  unfold unsettled
  rw [List.filter_cons]
  cases hh : (e.ev.isUndo && S.contains e.line) <;> simp [hh]

/-- The tail's headers, as a recursion carrying the unsettled tail's position. -/
def tailHeadersSpec (dy : Cal.Instant → Nat) (S : List Nat) (dead : Array Bool) : Nat → List Entry → List (Nat × HeaderRec)
  | _, [] => []
  | k, e :: bs =>
    if e.ev.isUndo && S.contains e.line then (dy e.t.val, HeaderRec.of e true) :: tailHeadersSpec dy S dead k bs
    else (dy e.t.val, HeaderRec.of e (Replay.deadAt dead k)) :: tailHeadersSpec dy S dead (k + 1) bs

theorem tailHeaders_foldl (dy : Cal.Instant → Nat) (S : List Nat) (dead : Array Bool) :
    ∀ (bs : List Entry) (l : List (Nat × HeaderRec)) (k : Nat),
      bs.foldl (fun (acc : List (Nat × HeaderRec) × Nat) e =>
        if e.ev.isUndo && S.contains e.line then ((dy e.t.val, HeaderRec.of e true) :: acc.1, acc.2)
        else ((dy e.t.val, HeaderRec.of e (Replay.deadAt dead acc.2)) :: acc.1, acc.2 + 1)) (l, k)
      = ((tailHeadersSpec dy S dead k bs).reverse ++ l, k + (unsettled S bs).length)
  | [], l, k => by simp [tailHeadersSpec, unsettled]
  | e :: bs, l, k => by
    rw [List.foldl_cons]
    by_cases hs : (e.ev.isUndo && S.contains e.line) = true
    · have hs' : e.ev.isUndo = true ∧ e.line ∈ S := by simpa using hs
      simp only [hs, if_true]
      rw [tailHeaders_foldl dy S dead bs]
      simp [tailHeadersSpec, hs', unsettled_cons]
    · simp only [hs, Bool.false_eq_true, if_false]
      rw [tailHeaders_foldl dy S dead bs]
      simp only [tailHeadersSpec, hs, Bool.false_eq_true, if_false, unsettled_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.length_cons]
      refine Prod.ext rfl ?_
      simp only; omega

theorem tailHeaders_eq_spec (dy : Cal.Instant → Nat) (S : List Nat) (bs : List Entry) :
    tailHeaders dy S bs = tailHeadersSpec dy S (Replay.maskFast (unsettled S bs)) 0 bs := by
  unfold tailHeaders
  simp only
  rw [tailHeaders_foldl]
  simp

theorem mem_unsettled_sub (S : List Nat) (bs : List Entry) (x : Entry) (h : x ∈ unsettled S bs) : x ∈ bs :=
  (List.mem_filter.1 h).1

/-- **Each tail header's bit is whether its entry survives the unsettled tail**, on distinct lines. -/
theorem tailHeadersSpec_eq (dy : Cal.Instant → Nat) (S : List Nat) (N : List Entry)
    (hN : N.Pairwise (fun x y => x.line < y.line)) :
    ∀ (bs N₀ : List Entry), N = N₀ ++ unsettled S bs →
      tailHeadersSpec dy S (Replay.maskFast N) N₀.length bs
        = bs.map (fun e => (dy e.t.val, HeaderRec.of e (!decide (e ∈ survivors N))))
  | [], _, _ => rfl
  | e :: bs, N₀, hN₀ => by
    simp only [tailHeadersSpec, List.map_cons]
    by_cases hs : (e.ev.isUndo && S.contains e.line) = true
    · rw [if_pos hs]
      rw [unsettled_cons, if_pos hs] at hN₀
      rw [tailHeadersSpec_eq dy S N hN bs N₀ hN₀]
      congr 3
      have hund : e.ev.isUndo = true := by simp only [Bool.and_eq_true] at hs; exact hs.1
      have : e ∉ survivors N := fun hm => by
        unfold survivors at hm
        rw [List.mem_reverse] at hm
        have h2 := Replay.not_undo_of_mem_foldl_maskStep N [] e (by simp) hm
        rw [hund] at h2; cases h2
      simp [this]
    · rw [if_neg hs]
      rw [unsettled_cons, if_neg hs] at hN₀
      have hN₁ : N = (N₀ ++ [e]) ++ unsettled S bs := by rw [hN₀]; simp
      have ih := tailHeadersSpec_eq dy S N hN bs (N₀ ++ [e]) hN₁
      rw [List.length_append, List.length_singleton] at ih
      rw [ih]
      congr 3
      have hat : N[N₀.length]? = some e := by rw [hN₀]; simp
      have hmem : (e, N₀.length) ∈ N.zipIdx := by
        rw [List.mem_iff_getElem?]
        exact ⟨N₀.length, by rw [List.getElem?_zipIdx, hat]; simp⟩
      rw [← Replay.cancelledAt_eq_deadAt N (e, N₀.length) hmem]
      have := mem_survivors_iff_uncancelled N hN N₀.length e hat
      cases hc : Replay.cancelledAt N N₀.length with
      | false => have := this.2 hc; simp [this]
      | true =>
        have : e ∉ survivors N := fun hm => by rw [this.1 hm] at hc; cases hc
        simp [this]

end Seal
end Tm
