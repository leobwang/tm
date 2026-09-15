import TmKernel.SealResume
/-!
# SealCutTags — the resealed tag lines (stage 5, D9, W2: law 6)

The latest line per tag of appended survivors merges the two lists by tag, the later list's line winning
(`tagLines_append`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Log (Entry)

/-- The latest line of a tag among survivors, as `tagLines` reads it. -/
def lastLineOf (sv : List Entry) (t : List Char) : Nat :=
  (sv.filter (fun e => decide (e.ev.tag = t))).foldl (fun _ e => e.line) 0

theorem tagLines_eq (sv : List Entry) :
    tagLines sv = (canon idLt (sv.map (·.ev.tag))).map (fun t => (t, lastLineOf sv t)) := rfl

theorem foldl_line_of_ne_nil : ∀ (L : List Entry) (a b : Nat), L ≠ [] →
    L.foldl (fun _ e => e.line) a = L.foldl (fun _ e => e.line) b
  | [], _, _, h => absurd rfl h
  | x :: L, _, _, _ => by rw [List.foldl_cons, List.foldl_cons]

theorem lastLineOf_append (X Y : List Entry) (t : List Char) :
    lastLineOf (X ++ Y) t = if t ∈ Y.map (·.ev.tag) then lastLineOf Y t else lastLineOf X t := by
  unfold lastLineOf
  rw [List.filter_append, List.foldl_append]
  split
  · rename_i hm
    obtain ⟨e, he, het⟩ := List.mem_map.1 hm
    exact foldl_line_of_ne_nil _ _ _ (List.ne_nil_of_mem (List.mem_filter.2 ⟨he, by simp [het]⟩))
  · rename_i hm
    have : Y.filter (fun e => decide (e.ev.tag = t)) = [] := List.filter_eq_nil_iff.2 (fun e he het => by
      simp only [decide_eq_true_eq] at het
      exact hm (List.mem_map.2 ⟨e, he, het⟩))
    rw [this]; rfl

theorem find?_eq_of_mem_nodup : ∀ (l : List (List Char)) (t : List Char), l.Nodup →
    l.find? (fun t' => t' == t) = if t ∈ l then some t else none
  | [], _, _ => rfl
  | a :: l, t, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hat : a = t
    · subst hat; simp
    · have : (a == t) = false := by simpa using hat
      rw [this, find?_eq_of_mem_nodup l t hnd.2]
      simp only [List.mem_cons]
      by_cases ht : t ∈ l
      · simp [ht]
      · simp [ht, Ne.symm hat]

theorem find?_map_key (f : List Char → Nat) (t : List Char) : ∀ (l : List (List Char)), l.Nodup →
    (l.map (fun t' => (t', f t'))).find? (fun p => p.1 == t) = if t ∈ l then some (t, f t) else none
  | [], _ => rfl
  | a :: l, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.find?_cons]
    by_cases hat : a = t
    · subst hat; simp
    · have hb : ((a, f a).1 == t) = false := by simpa using hat
      rw [hb, find?_map_key f t l hnd.2]
      by_cases ht : t ∈ l
      · simp [ht]
      · simp [ht, Ne.symm hat]

theorem tagLines_find (sv : List Entry) (t : List Char) :
    (tagLines sv).find? (fun p => p.1 == t) = if t ∈ sv.map (·.ev.tag) then some (t, lastLineOf sv t) else none := by
  rw [tagLines_eq, find?_map_key (lastLineOf sv) t _ (nodup_canon idLt_strictTotal _)]
  by_cases hm : t ∈ sv.map (·.ev.tag)
  · rw [if_pos hm, if_pos ((mem_canon idLt_strictTotal _ _).2 hm)]
  · rw [if_neg hm, if_neg (fun h => hm ((mem_canon idLt_strictTotal _ _).1 h))]

theorem tagLines_fst (sv : List Entry) : (tagLines sv).map Prod.fst = canon idLt (sv.map (·.ev.tag)) := by
  rw [tagLines_eq, List.map_map]
  exact List.map_id' _

/-- **The latest line per tag of appended survivors is the merge of the two lists, the later one's line winning.** -/
theorem tagLines_append (X Y : List Entry) : tagLines (X ++ Y) = mergeTagLines (tagLines X) (tagLines Y) := by
  unfold mergeTagLines
  rw [tagLines_fst, tagLines_fst, tagLines_eq]
  have hc : canon idLt ((X ++ Y).map (·.ev.tag))
      = canon idLt (canon idLt (X.map (·.ev.tag)) ++ canon idLt (Y.map (·.ev.tag))) :=
    canon_eq_of_mem_iff idLt_strictTotal _ _ (fun t => by
      simp only [List.map_append, List.mem_append, mem_canon idLt_strictTotal])
  rw [hc]
  apply List.map_congr_left
  intro t ht
  rw [mem_canon idLt_strictTotal, List.mem_append, mem_canon idLt_strictTotal, mem_canon idLt_strictTotal] at ht
  rw [tagLines_find, tagLines_find, lastLineOf_append]
  by_cases hY : t ∈ Y.map (·.ev.tag)
  · simp [hY]
  · have hX : t ∈ X.map (·.ev.tag) := ht.resolve_right hY
    simp [hY, hX]

theorem take_filter_of_prefix {α : Type} (R : α → Bool) : ∀ (L : List α) (k : Nat), (∀ x ∈ L.take k, R x = true) →
    (L.filter R).take k = L.take k
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: L, k + 1, h => by
    have ha : R a = true := h a (by simp)
    rw [List.filter_cons_of_pos ha, List.take_succ_cons, List.take_succ_cons,
      take_filter_of_prefix R L k (fun x hx => h x (by simp [hx]))]

/-- **In a list strictly sorted by key, an entry is among the first `k` exactly when fewer than `k` keys are below
its own.** -/
theorem mem_take_iff_count {β : Type} {lt : List Char → List Char → Bool} (hlt : StrictTotal lt) :
    ∀ (M : List (List Char × β)), M.Pairwise (fun a b => lt a.1 b.1 = true) → ∀ (x : List Char × β) (k : Nat),
      x ∈ M → (x ∈ M.take k ↔ (M.filter (fun p => lt p.1 x.1)).length < k)
  | [], _, _, _, hx => by cases hx
  | a :: M, hs, x, k, hx => by
    by_cases hxa : x = a
    · subst hxa
      have hnone : M.filter (fun p => lt p.1 x.1) = [] := List.filter_eq_nil_iff.2 (fun p hp hpl => by
        have := List.rel_of_pairwise_cons hs hp
        rw [hlt.asymm this] at hpl; cases hpl)
      simp only [List.filter_cons, hlt.irrefl, Bool.false_eq_true, ↓reduceIte, hnone]
      cases k with
      | zero => simp
      | succ k => simp
    · have hxM : x ∈ M := (List.mem_cons.1 hx).resolve_left hxa
      have hax : lt a.1 x.1 = true := List.rel_of_pairwise_cons hs hxM
      simp only [List.filter_cons, hax, ↓reduceIte]
      cases k with
      | zero => simp
      | succ k =>
        show x ∈ List.take (k + 1) (a :: M) ↔ (a :: M.filter (fun p => lt p.1 x.1)).length < k + 1
        simp only [List.take_succ_cons, List.mem_cons, List.length_cons, hxa, false_or,
          mem_take_iff_count hlt M hs.of_cons x k hxM]
        omega

end Seal
end Tm
