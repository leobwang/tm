import TmKernel.SealCutTags
import TmKernel.SealGroup
/-!
# SealCutTags2 — the resealed tag lines, truncated (stage 5, D9, W2: law 6)

A checkpoint keeps its folded survivors' tag lines with the unknown tags bounded (`keepTags`: the known ones, and the
first `maxUnknownTags` unknown ones of at most `maxTagChars` characters, in tag order).  A reseal merges the stored,
truncated lines with the folded tail's and truncates again.  That is the truncation of the whole merge
(`keptTags_append`): a stored line the first truncation dropped is past the kept unknown tags, and stays past them once
more tags are merged.  The overflow flag composes (`tagOverflow_append`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Log (Entry)

/-- A line of a short unknown tag: the lines `keepTags` bounds. -/
def shortUnknown (p : List Char × Nat) : Bool := !Log.isKnownTag p.1 && decide (p.1.length ≤ maxTagChars)

/-- Whether `keepTags` keeps a line of a list. -/
def keptBy (all : List (List Char × Nat)) (p : List Char × Nat) : Bool :=
  Log.isKnownTag p.1 || ((all.filter shortUnknown).take maxUnknownTags).contains p

theorem keepTags_eq (all : List (List Char × Nat)) : keepTags all = all.filter (keptBy all) := rfl

theorem keptTags_eq_keepTags (sv : List Entry) : keptTags sv = keepTags (tagLines sv) := rfl

theorem shortUnknown_key {p q : List Char × Nat} (h : q.1 = p.1) : shortUnknown q = shortUnknown p := by
  unfold shortUnknown; rw [h]

theorem tagSorted_map (l : List (List Char)) (f : List Char → Nat) (h : l.Pairwise (fun a b => idLt a b = true)) :
    (l.map (fun t => (t, f t))).Pairwise (fun a b => idLt a.1 b.1 = true) := by
  rw [List.pairwise_map]; exact h

theorem tagSorted_tagLines (sv : List Entry) : (tagLines sv).Pairwise (fun a b => idLt a.1 b.1 = true) :=
  tagSorted_map _ _ (sorted_canon idLt_strictTotal _)

theorem tagSorted_merge (old new : List (List Char × Nat)) :
    (mergeTagLines old new).Pairwise (fun a b => idLt a.1 b.1 = true) := by
  unfold mergeTagLines; exact tagSorted_map _ _ (sorted_canon idLt_strictTotal _)

theorem find?_key_of_mem : ∀ (M : List (List Char × Nat)), M.Pairwise (fun a b => idLt a.1 b.1 = true) →
    ∀ x ∈ M, M.find? (fun p => p.1 == x.1) = some x
  | [], _, x, hx => by cases hx
  | a :: M, hs, x, hx => by
    rw [List.pairwise_cons] at hs
    rw [List.find?_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have hne : (a.1 == x.1) = false := by
        have := hs.1 x hx
        cases hb : (a.1 == x.1)
        · rfl
        · have hax : a.1 = x.1 := by simpa using hb
          rw [hax, idLt_strictTotal.irrefl] at this; cases this
      rw [hne]; exact find?_key_of_mem M hs.2 x hx

theorem mem_tagLines_fst (sv : List Entry) (t : List Char) :
    t ∈ (tagLines sv).map Prod.fst ↔ t ∈ sv.map (·.ev.tag) := by
  rw [tagLines_fst, mem_canon idLt_strictTotal]

theorem mem_merge_fst (old new : List (List Char × Nat)) (t : List Char) :
    t ∈ (mergeTagLines old new).map Prod.fst ↔ t ∈ old.map Prod.fst ∨ t ∈ new.map Prod.fst := by
  unfold mergeTagLines
  rw [List.map_map]
  have : (Prod.fst ∘ fun t => (t, ((new.find? (fun p => p.1 == t)).map Prod.snd).getD
      (((old.find? (fun p => p.1 == t)).map Prod.snd).getD 0))) = id := by funext t; rfl
  rw [this, List.map_id, mem_canon idLt_strictTotal, List.mem_append]

/-- **A merge with a filtered old list is the merge filtered to the tags left.** -/
theorem merge_filter_old (A B : List (List Char × Nat)) (hA : A.Pairwise (fun a b => idLt a.1 b.1 = true))
    (P : List Char × Nat → Bool) :
    mergeTagLines (A.filter P) B
      = (mergeTagLines A B).filter (fun p => decide (p.1 ∈ (A.filter P).map Prod.fst ∨ p.1 ∈ B.map Prod.fst)) := by
  unfold mergeTagLines
  rw [List.filter_map, canon_filter idLt_strictTotal]
  have hc : canon idLt ((A.filter P).map Prod.fst ++ B.map Prod.fst)
      = canon idLt ((A.map Prod.fst ++ B.map Prod.fst).filter ((fun p : List Char × Nat =>
          decide (p.1 ∈ (A.filter P).map Prod.fst ∨ p.1 ∈ B.map Prod.fst)) ∘ fun t =>
          (t, ((B.find? (fun p => p.1 == t)).map Prod.snd).getD (((A.find? (fun p => p.1 == t)).map Prod.snd).getD 0)))) := by
    apply canon_eq_of_mem_iff idLt_strictTotal
    intro t
    simp only [List.mem_append, List.mem_filter, Function.comp_apply, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · refine ⟨Or.inl ?_, Or.inl h⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
        exact List.mem_map.2 ⟨x, (List.mem_filter.1 hx).1, rfl⟩
      · exact ⟨Or.inr h, Or.inr h⟩
    · rintro ⟨-, h⟩; exact h
  rw [hc]
  apply List.map_congr_left
  intro t ht
  rw [mem_canon idLt_strictTotal, List.mem_filter] at ht
  simp only [Function.comp_apply, decide_eq_true_eq] at ht
  obtain ⟨-, ht⟩ := ht
  cases hB : B.find? (fun p => p.1 == t) with
  | some q => simp
  | none =>
    have htB : t ∉ B.map Prod.fst := fun h => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      have hBs : B.Pairwise (fun a b => idLt a.1 b.1 = true) ∨ True := Or.inr trivial
      clear hBs
      have := List.find?_eq_none.1 hB y hy
      simp at this
    have htA : t ∈ (A.filter P).map Prod.fst := ht.resolve_right htB
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 htA
    have h1 := find?_key_of_mem (A.filter P) (hA.sublist List.filter_sublist) x hx
    have h2 := find?_key_of_mem A hA x (List.mem_filter.1 hx).1
    simp only [Option.map_none, Option.getD_none, h1, h2]

/-- **In a list sorted by tag, a line is kept exactly when its tag is known, or it is short and unknown with fewer than
`maxUnknownTags` short unknown tags below it.** -/
theorem keptBy_iff (M : List (List Char × Nat)) (hM : M.Pairwise (fun a b => idLt a.1 b.1 = true))
    (p : List Char × Nat) (hp : p ∈ M) :
    keptBy M p = true ↔ Log.isKnownTag p.1 = true ∨
      (shortUnknown p = true ∧ ((M.filter shortUnknown).filter (fun q => idLt q.1 p.1)).length < maxUnknownTags) := by
  unfold keptBy
  simp only [Bool.or_eq_true, List.contains_iff_mem]
  apply or_congr Iff.rfl
  by_cases hs : shortUnknown p = true
  · have hmem : p ∈ M.filter shortUnknown := List.mem_filter.2 ⟨hp, hs⟩
    rw [mem_take_iff_count idLt_strictTotal (M.filter shortUnknown) (hM.sublist List.filter_sublist) p _ hmem]
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  · constructor
    · intro h
      exact absurd (List.mem_filter.1 (List.mem_of_mem_take h)).2 hs
    · intro h; exact absurd h.1 hs

/-- **Fewer tags give fewer short unknown tags below a tag.** -/
theorem count_below_mono (A M : List (List Char × Nat)) (hA : A.Pairwise (fun a b => idLt a.1 b.1 = true))
    (hsub : ∀ q ∈ A, ∃ q' ∈ M, q'.1 = q.1) (t : List Char) :
    ((A.filter shortUnknown).filter (fun q => idLt q.1 t)).length
      ≤ ((M.filter shortUnknown).filter (fun q => idLt q.1 t)).length := by
  have hs : ((A.filter shortUnknown).filter (fun q => idLt q.1 t)).Pairwise (fun a b => idLt a.1 b.1 = true) :=
    hA.sublist (List.filter_sublist.trans List.filter_sublist)
  have hnd : (((A.filter shortUnknown).filter (fun q => idLt q.1 t)).map Prod.fst).Nodup :=
    nodup_of_sorted idLt_strictTotal (List.pairwise_map.2 hs)
  have := List.Nodup.length_le_of_subset hnd (l₂ := ((M.filter shortUnknown).filter (fun q => idLt q.1 t)).map Prod.fst)
    (fun u hu => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu
      simp only [List.mem_filter] at hq
      obtain ⟨⟨hqA, hsu⟩, hlt⟩ := hq
      obtain ⟨q', hq', hk⟩ := hsub q hqA
      exact List.mem_map.2 ⟨q', List.mem_filter.2 ⟨List.mem_filter.2 ⟨hq', by rw [shortUnknown_key hk]; exact hsu⟩,
        by rw [hk]; exact hlt⟩, hk⟩)
  simpa only [List.length_map] using this

theorem keptBy_filter (M : List (List Char × Nat)) (R : List Char × Nat → Bool)
    (hR : ∀ x ∈ (M.filter shortUnknown).take maxUnknownTags, R x = true) : keptBy (M.filter R) = keptBy M := by
  funext p
  unfold keptBy
  have h1 : (M.filter R).filter shortUnknown = (M.filter shortUnknown).filter R := by
    rw [List.filter_filter, List.filter_filter]
    exact List.filter_congr (fun a _ => Bool.and_comm _ _)
  rw [h1, take_filter_of_prefix R _ _ hR]

theorem keepTags_filter (M : List (List Char × Nat)) (R : List Char × Nat → Bool)
    (hR : ∀ x ∈ (M.filter shortUnknown).take maxUnknownTags, R x = true) (hall : ∀ x ∈ keepTags M, R x = true) :
    keepTags (M.filter R) = keepTags M := by
  rw [keepTags_eq, keepTags_eq, keptBy_filter M R hR]
  have : keepTags M = (keepTags M).filter R := (List.filter_eq_self.2 hall).symm
  rw [keepTags_eq] at this
  rw [this, List.filter_filter, List.filter_filter]
  exact List.filter_congr (fun a _ => Bool.and_comm _ _)

section Merge

variable (X Y : List Entry)

/-- The stored line of a tag of the folded survivors. -/
theorem tag_line_exists (M : List (List Char × Nat)) (hM : ∀ t, t ∈ (tagLines X).map Prod.fst → t ∈ M.map Prod.fst) :
    ∀ q ∈ tagLines X, ∃ q' ∈ M, q'.1 = q.1 := by
  intro q hq
  obtain ⟨q', hq', hk⟩ := List.mem_map.1 (hM q.1 (List.mem_map.2 ⟨q, hq, rfl⟩))
  exact ⟨q', hq', hk⟩

/-- Every line of the whole merge whose tag is not in the stored truncation nor the tail is a stored line dropped. -/
theorem merge_first_kept (x : List Char × Nat)
    (hx : x ∈ ((mergeTagLines (tagLines X) (tagLines Y)).filter shortUnknown).take maxUnknownTags) :
    x.1 ∈ (keptTags X).map Prod.fst ∨ x.1 ∈ (tagLines Y).map Prod.fst := by
  by_cases hY : x.1 ∈ (tagLines Y).map Prod.fst
  · exact Or.inr hY
  · left
    have hxM : x ∈ (mergeTagLines (tagLines X) (tagLines Y)).filter shortUnknown := List.mem_of_mem_take hx
    have hxM' := (List.mem_filter.1 hxM).1
    have hxA : x.1 ∈ (tagLines X).map Prod.fst :=
      ((mem_merge_fst _ _ x.1).1 (List.mem_map.2 ⟨x, hxM', rfl⟩)).resolve_right hY
    obtain ⟨p0, hp0, hk⟩ := List.mem_map.1 hxA
    have hcount := (mem_take_iff_count idLt_strictTotal _
      ((tagSorted_merge _ _).sublist List.filter_sublist) x _ hxM).1 hx
    have hmono := count_below_mono (tagLines X) (mergeTagLines (tagLines X) (tagLines Y)) (tagSorted_tagLines X)
      (tag_line_exists X _ (fun t ht => (mem_merge_fst _ _ t).2 (Or.inl ht))) x.1
    have hsu : shortUnknown p0 = true := by rw [shortUnknown_key hk]; exact (List.mem_filter.1 hxM).2
    have hkept : keptBy (tagLines X) p0 = true :=
      (keptBy_iff (tagLines X) (tagSorted_tagLines X) p0 hp0).2 (Or.inr ⟨hsu, by rw [hk]; omega⟩)
    exact List.mem_map.2 ⟨p0, List.mem_filter.2 ⟨hp0, hkept⟩, hk⟩

/-- Every line the whole merge keeps has its tag in the stored truncation or the tail. -/
theorem merge_kept_in (x : List Char × Nat) (hx : x ∈ keepTags (mergeTagLines (tagLines X) (tagLines Y))) :
    x.1 ∈ (keptTags X).map Prod.fst ∨ x.1 ∈ (tagLines Y).map Prod.fst := by
  rw [keepTags_eq] at hx
  obtain ⟨hxM, hk⟩ := List.mem_filter.1 hx
  unfold keptBy at hk
  simp only [Bool.or_eq_true, List.contains_iff_mem] at hk
  rcases hk with hk | hk
  · by_cases hY : x.1 ∈ (tagLines Y).map Prod.fst
    · exact Or.inr hY
    · left
      have hxA : x.1 ∈ (tagLines X).map Prod.fst :=
        ((mem_merge_fst _ _ x.1).1 (List.mem_map.2 ⟨x, hxM, rfl⟩)).resolve_right hY
      obtain ⟨p0, hp0, hkey⟩ := List.mem_map.1 hxA
      have hkept : keptBy (tagLines X) p0 = true :=
        (keptBy_iff (tagLines X) (tagSorted_tagLines X) p0 hp0).2 (Or.inl (by rw [hkey]; exact hk))
      exact List.mem_map.2 ⟨p0, List.mem_filter.2 ⟨hp0, hkept⟩, hkey⟩
  · exact merge_first_kept X Y x hk

/-- **The truncated tag lines of appended survivors are the truncation of the stored truncation merged with the
tail's.** -/
theorem keptTags_append : keptTags (X ++ Y) = keepTags (mergeTagLines (keptTags X) (tagLines Y)) := by
  rw [keptTags_eq_keepTags, tagLines_append, keptTags_eq_keepTags X, keepTags_eq (tagLines X),
    merge_filter_old (tagLines X) (tagLines Y) (tagSorted_tagLines X), ← keepTags_eq (tagLines X),
    ← keptTags_eq_keepTags X]
  exact (keepTags_filter _ _ (fun x hx => decide_eq_true (merge_first_kept X Y x hx))
    (fun x hx => decide_eq_true (merge_kept_in X Y x hx))).symm

theorem length_keepTags_lt_iff (M : List (List Char × Nat)) :
    (keepTags M).length < M.length ↔ ∃ x ∈ M, keptBy M x = false := by
  rw [keepTags_eq, List.length_filter_lt_length_iff_exists]
  simp

/-- **The resealed overflow flag**: the whole merge drops a line exactly when the stored truncation dropped one or the
merge of the stored truncation drops one. -/
theorem tagOverflow_append :
    decide ((keptTags (X ++ Y)).length < (tagLines (X ++ Y)).length)
      = (decide ((keptTags X).length < (tagLines X).length)
        || decide ((keepTags (mergeTagLines (keptTags X) (tagLines Y))).length
            < (mergeTagLines (keptTags X) (tagLines Y)).length)) := by
  have hM1 : mergeTagLines (keepTags (tagLines X)) (tagLines Y)
      = (mergeTagLines (tagLines X) (tagLines Y)).filter
          (fun p => decide (p.1 ∈ (keepTags (tagLines X)).map Prod.fst ∨ p.1 ∈ (tagLines Y).map Prod.fst)) := by
    rw [keepTags_eq]
    exact merge_filter_old _ _ (tagSorted_tagLines X) _
  have hK : keptBy (mergeTagLines (keepTags (tagLines X)) (tagLines Y))
      = keptBy (mergeTagLines (tagLines X) (tagLines Y)) := by
    rw [hM1]; exact keptBy_filter _ _ (fun x hx => by simpa [keptTags_eq_keepTags] using merge_first_kept X Y x hx)
  rw [keptTags_eq_keepTags, keptTags_eq_keepTags X, tagLines_append]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, length_keepTags_lt_iff]
  constructor
  · rintro ⟨q, hq, hnk⟩
    by_cases hR : q.1 ∈ (keepTags (tagLines X)).map Prod.fst ∨ q.1 ∈ (tagLines Y).map Prod.fst
    · right
      refine ⟨q, ?_, by rw [hK]; exact hnk⟩
      rw [hM1]; exact List.mem_filter.2 ⟨hq, by simpa using hR⟩
    · left
      have hY : q.1 ∉ (tagLines Y).map Prod.fst := fun h => hR (Or.inr h)
      have hA : q.1 ∈ (tagLines X).map Prod.fst :=
        ((mem_merge_fst _ _ q.1).1 (List.mem_map.2 ⟨q, hq, rfl⟩)).resolve_right hY
      obtain ⟨p0, hp0, hk⟩ := List.mem_map.1 hA
      refine ⟨p0, hp0, ?_⟩
      cases hkb : keptBy (tagLines X) p0
      · rfl
      · exact absurd (Or.inl (List.mem_map.2 ⟨p0, List.mem_filter.2 ⟨hp0, hkb⟩, hk⟩)) hR
  · rintro (⟨p, hp, hnk⟩ | ⟨q, hq, hnk⟩)
    · obtain ⟨q, hq, hk⟩ := List.mem_map.1 ((mem_merge_fst (tagLines X) (tagLines Y) p.1).2
        (Or.inl (List.mem_map.2 ⟨p, hp, rfl⟩)))
      refine ⟨q, hq, ?_⟩
      cases hkb : keptBy (mergeTagLines (tagLines X) (tagLines Y)) q
      · rfl
      · exfalso
        rcases (keptBy_iff _ (tagSorted_merge _ _) q hq).1 hkb with h | ⟨hsu, hc⟩
        · have := (keptBy_iff (tagLines X) (tagSorted_tagLines X) p hp).2 (Or.inl (by rw [← hk]; exact h))
          rw [hnk] at this; cases this
        · have hmono := count_below_mono (tagLines X) (mergeTagLines (tagLines X) (tagLines Y)) (tagSorted_tagLines X)
            (tag_line_exists X _ (fun t ht => (mem_merge_fst _ _ t).2 (Or.inl ht))) p.1
          have := (keptBy_iff (tagLines X) (tagSorted_tagLines X) p hp).2
            (Or.inr ⟨by rw [← shortUnknown_key hk]; exact hsu, by rw [hk] at hc; omega⟩)
          rw [hnk] at this; cases this
    · rw [hM1] at hq
      exact ⟨q, (List.mem_filter.1 hq).1, by rw [← hK]; exact hnk⟩

end Merge

end Seal
end Tm
