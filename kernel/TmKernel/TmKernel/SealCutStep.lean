import TmKernel.SealCutMask
/-!
# SealCutStep — an undo past the fold point never reaches the folded lines (stage 5, D9, W2: law 6)

Under G1, and with the fold point's condition (vi) (the stored settled undos are folded, and no undo is cut from its
tail target), every undo of the tail past the cut finds its first match on the whole log's stack past the cut, or
none.  So the folded lines' mask does not see the unfolded lines, and the settled undos at the cut are exactly the
unfolded ones that dangle.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (maskStep survivors danglingOf dangleStep)
open Log (Entry)

theorem split_stackOf (A X : List Entry) (hX : ∀ x ∈ X, A.contains x = false) : Split A (stackOf (A ++ X)) := by
  rw [stackOf_append]
  refine Split.foldl X (stackOf A) ⟨[], stackOf A, rfl, (fun u hu => by cases hu), (fun v hv => ?_)⟩ hX
  rcases mem_foldl_maskStep' A [] v hv with h | h
  · cases h
  · simp [h]

/-- The first match on a split stack is its unfolded part's, if any. -/
theorem find?_split {A st : List Entry} (h : Split A st) (p : Entry → Bool) :
    st.find? p = ((st.filter (fun x => !A.contains x)).find? p).or ((st.filter (fun x => A.contains x)).find? p) := by
  conv => lhs; rw [h.eq]
  rw [List.find?_append]

/-- A settled line stays settled. -/
theorem settled_lines_mono (A : List Entry) : ∀ (X : List Entry) (acc : List Entry × List Nat) (n : Nat),
    n ∈ acc.2 → n ∈ (X.foldl (settledStep A) acc).2
  | [], _, _, h => h
  | e :: X, acc, n, h => by
    rw [List.foldl_cons]
    apply settled_lines_mono A X
    unfold settledStep
    cases hev : e.ev with
    | undo of_ id =>
      simp only
      split
      · exact List.mem_cons_of_mem _ h
      · exact h
    | _ => exact h

/-- **The settled lines of a prefix are the whole list's, on the prefix's entries.** -/
theorem settled_prefix_lines (A X Y : List Entry) (acc : List Entry × List Nat)
    (hne : ∀ x ∈ X, ∀ y ∈ Y, x.line ≠ y.line) (x : Entry) (hx : x ∈ X) :
    x.line ∈ ((X ++ Y).foldl (settledStep A) acc).2 ↔ x.line ∈ (X.foldl (settledStep A) acc).2 := by
  rw [List.foldl_append]
  generalize X.foldl (settledStep A) acc = acc'
  constructor
  · intro h
    rcases settled_lines_sub A Y acc' x.line h with h | ⟨y, hy, hyl⟩
    · exact h
    · exact absurd hyl.symm (hne x hx y hy)
  · intro h
    exact settled_lines_mono A Y acc' x.line h

/-- **Undos that never erase a folded entry leave the folded part of the stack.** -/
theorem foldl_maskStep_filter (P : Entry → Bool) :
    ∀ (Y S : List Entry), (∀ y ∈ Y, P y = false) →
      (∀ pre u post of_ id, Y = pre ++ u :: post → u.ev = .undo of_ id →
        ∀ m, (pre.foldl maskStep S).find? (Replay.«matches» of_ id) = some m → P m = false) →
      (Y.foldl maskStep S).filter P = S.filter P
  | [], _, _, _ => rfl
  | y :: Y, S, hP, hU => by
    rw [List.foldl_cons, foldl_maskStep_filter P Y (maskStep S y) (fun y' hy' => hP y' (List.mem_cons_of_mem _ hy'))
      (fun pre u post of_ id hs hev m hm => hU (y :: pre) u post of_ id (by rw [hs]; rfl) hev m hm)]
    unfold maskStep
    cases hev : y.ev with
    | undo of_ id =>
      simp only
      cases hf : S.find? (Replay.«matches» of_ id) with
      | none => rw [eraseP_eq_self_of_find?_none _ _ hf]
      | some m => exact eraseP_filter_of_first_not _ P S m hf (hU [] y Y of_ id rfl hev m hf)
    | _ => simp [List.filter_cons, hP y List.mem_cons_self]

theorem g1_prefix (K : Ckpt) (N₁ N₂ : List Entry) (hg : g1 K (N₁ ++ N₂) = none) : g1 K N₁ = none := by
  unfold g1 at hg ⊢
  rw [List.findSome?_eq_none_iff] at hg ⊢
  intro u hu
  apply hg u
  rw [List.mem_reverse] at hu ⊢
  unfold danglingOf at hu ⊢
  rw [List.foldl_append]
  exact Replay.danglingOf_snd_mono N₂ _ u hu

theorem dangles_of_no_match (N₁ N₂ : List Entry) (u : Entry) (of_ : List Char) (id : Option Log.Id)
    (hev : u.ev = .undo of_ id) (hf : (N₁.foldl maskStep []).find? (Replay.«matches» of_ id) = none) :
    u ∈ (danglingOf (N₁ ++ u :: N₂)).2 := by
  unfold danglingOf
  rw [List.foldl_append, List.foldl_cons]
  apply Replay.danglingOf_snd_mono
  have h1 := Replay.danglingOf_fst_go N₁ [] []
  generalize N₁.foldl dangleStep ([], []) = acc at h1 ⊢
  rw [Replay.dangleStep_of_no_match acc u of_ id hev (by
    rw [h1]
    cases ha : (N₁.foldl maskStep []).any (Replay.«matches» of_ id) with
    | false => rfl
    | true =>
      obtain ⟨x, hx, hxm⟩ := List.any_eq_true.1 ha
      exact absurd (List.find?_eq_none.1 hf x hx) (by simpa using hxm))]
  exact List.mem_cons_self

/-- The unsettled tail splits at an undo past every settled line. -/
theorem unsettled_split_at (As Rs : List Entry) (Y P post : List Entry) (u : Entry) (hY : Y = P ++ u :: post)
    (huS : u.line ∉ settledOf As Rs) :
    unsettled (settledOf As Rs) Y = unsettled (settledOf As Rs) P ++ u :: unsettled (settledOf As Rs) post := by
  rw [hY, unsettled_append, unsettled_cons, if_neg (by simp [huS])]

/-- **The cut step, past the stored remainder**: the stack is the unsettled tail's, then the folded survivors. -/
theorem cut_step_past (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut As Rs ws) (unsettled (settledOf As Rs) (Rs ++ B')) = none)
    (c : Nat) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (hvi : ∀ ut ∈ undoTargets (unsettled (settledOf As Rs) (Rs ++ B')), ¬ (ut.2.line ≤ c ∧ c < ut.1.line))
    (a' post : List Entry) (u : Entry) (hB' : B' = a' ++ u :: post) (hu : c < u.line)
    (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id)
    (m : Entry) (hm : (stackOf (As ++ (Rs ++ a'))).find? (Replay.«matches» of_ id) = some m) : c < m.line := by
  obtain ⟨-, -, hdX⟩ := List.pairwise_append.1 hd
  have hAx : ∀ x ∈ Rs ++ B', As.contains x = false := fun x hx => by
    have : x ∉ As := fun hxA => by have := hdX x hxA x hx; omega
    simpa using this
  have hmemB : ∀ x ∈ Rs ++ a', x ∈ Rs ++ B' := fun x hx => by
    rcases List.mem_append.1 hx with h | h
    · exact List.mem_append_left _ h
    · rw [hB']; exact List.mem_append_right _ (List.mem_append_left _ h)
  have huS : u.line ∉ settledOf As Rs := fun h => by have := hsettled _ h; omega
  have hNsplit := unsettled_split_at As Rs (Rs ++ B') (Rs ++ a') post u (by rw [hB']; simp) huS
  have hd' : (As ++ (Rs ++ a')).Pairwise (fun x y => x.line < y.line) :=
    hd.sublist (List.Sublist.append_left (List.Sublist.append_left (by rw [hB']; exact List.sublist_append_left _ _) Rs) As)
  have hg' : g1 (ckptOfEntries z T₀ L cut As Rs ws)
      (unsettled (ckptOfEntries z T₀ L cut As Rs ws).settled (Rs ++ a')) = none := by
    rw [ckpt_settled]
    rw [hNsplit] at hg
    exact g1_prefix _ _ _ hg
  have hsurv := survivors_append_of_g1 As Rs a' hd' _ (ckpt_tagLast z T₀ L cut As Rs ws)
    (ckpt_tagOverflow z T₀ L cut As Rs ws) (ckpt_settled z T₀ L cut As Rs ws) hg'
  rw [ckpt_settled] at hsurv
  have hst : stackOf (As ++ (Rs ++ a')) = stackOf (unsettled (settledOf As Rs) (Rs ++ a'))
      ++ (foldedSurvivors As Rs).reverse := by
    have := congrArg List.reverse hsurv
    simp only [survivors, List.reverse_append, List.reverse_reverse] at this
    exact this
  have hmemN : ∀ x ∈ stackOf (unsettled (settledOf As Rs) (Rs ++ a')), As.contains x = false := fun x hx => by
    rcases mem_foldl_maskStep' _ [] x hx with h | h
    · cases h
    · exact hAx x (hmemB x (mem_unsettled_sub _ _ x h))
  rw [hst, List.find?_append] at hm
  cases hNf : (stackOf (unsettled (settledOf As Rs) (Rs ++ a'))).find? (Replay.«matches» of_ id) with
  | some m' =>
    rw [hNf] at hm
    simp only [Option.some_or, Option.some.injEq] at hm
    subst hm
    have hmem := mem_undoTargets _ _ _ u of_ id hNsplit hev m' hNf
    have := hvi _ hmem
    simp only at this
    omega
  | none =>
    exfalso
    rw [hNf] at hm
    simp only [Option.none_or] at hm
    have hdang := dangles_of_no_match (unsettled (settledOf As Rs) (Rs ++ a')) (unsettled (settledOf As Rs) post)
      u of_ id hev hNf
    rw [← hNsplit] at hdang
    have hreach : reachOf (ckptOfEntries z T₀ L cut As Rs ws) u = none :=
      (List.findSome?_eq_none_iff.1 hg) u (List.mem_reverse.2 hdang)
    have hmSA : m ∈ foldedSurvivors As Rs := List.mem_reverse.1 (List.mem_of_find?_eq_some hm)
    have := dangling_misses_the_folded As Rs _ (ckpt_tagLast z T₀ L cut As Rs ws)
      (ckpt_tagOverflow z T₀ L cut As Rs ws) u hreach of_ id hev m hmSA
    rw [List.find?_some hm] at this
    cases this

/-- **The cut step, within the stored remainder**: the undo is unsettled, so its first match is unfolded and on the
tail's stack. -/
theorem cut_step_within (As Rs B' : List Entry)
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (c : Nat) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (hvi : ∀ ut ∈ undoTargets (unsettled (settledOf As Rs) (Rs ++ B')), ¬ (ut.2.line ≤ c ∧ c < ut.1.line))
    (P c'' : List Entry) (u : Entry) (hRs : Rs = P ++ u :: c'') (hu : c < u.line)
    (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id)
    (m : Entry) (hm : (stackOf (As ++ P)).find? (Replay.«matches» of_ id) = some m) : c < m.line := by
  obtain ⟨-, hdRB, hdX⟩ := List.pairwise_append.1 hd
  have hAx : ∀ x ∈ Rs ++ B', As.contains x = false := fun x hx => by
    have : x ∉ As := fun hxA => by have := hdX x hxA x hx; omega
    simpa using this
  have hPR : ∀ x ∈ P, x ∈ Rs := fun x hx => by rw [hRs]; exact List.mem_append_left _ hx
  have hPA : ∀ x ∈ P, As.contains x = false := fun x hx => hAx x (List.mem_append_left _ (hPR x hx))
  have huS : u.line ∉ settledOf As Rs := fun h => by have := hsettled _ h; omega
  have hNsplit := unsettled_split_at As Rs (Rs ++ B') P (c'' ++ B') u (by rw [hRs]; simp) huS
  have hdR : Rs.Pairwise (fun x y => x.line < y.line) := (List.pairwise_append.1 hdRB).1
  have hne : ∀ x ∈ P, ∀ y ∈ u :: c'', x.line ≠ y.line := fun x hx y hy => by
    rw [hRs] at hdR
    exact Nat.ne_of_lt ((List.pairwise_append.1 hdR).2.2 x hx y hy)
  have hPne : P.Pairwise (fun x y => x.line ≠ y.line) := by
    rw [hRs] at hdR
    exact (List.pairwise_append.1 hdR).1.imp (fun h => Nat.ne_of_lt h)
  let acc0 : List Entry × List Nat := (stackOf As, [])
  have hA0 : (stackOf As).filter (fun x => !As.contains x) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by
      rcases mem_foldl_maskStep' As [] x hx with h | h
      · cases h
      · simp [h])
  have hset : settledOf As Rs = (Rs.foldl (settledStep As) acc0).2.reverse := rfl
  have hfst : (P.foldl (settledStep As) acc0).1 = stackOf (As ++ P) := by rw [settledStep_fst, stackOf_append]
  -- the undo's step does not settle it, so its first match is not folded
  have hmA : As.contains m = false := by
    have hsplitRs : Rs.foldl (settledStep As) acc0
        = c''.foldl (settledStep As) (settledStep As (P.foldl (settledStep As) acc0) u) := by
      rw [hRs, List.foldl_append, List.foldl_cons]
    have hfst' := hfst
    generalize P.foldl (settledStep As) acc0 = accP at hfst' hsplitRs
    cases hA : As.contains m with
    | false => rfl
    | true =>
      exfalso
      apply huS
      rw [hset, List.mem_reverse, hsplitRs]
      apply settled_lines_mono
      have hcond : (accP.1.find? (Replay.«matches» of_ id)).all (fun t => As.contains t) = true := by
        rw [hfst', hm]; exact hA
      unfold settledStep
      rw [hev]
      simp only [hcond, ↓reduceIte]
      exact List.mem_cons_self
  -- so it is on the unfolded part, which is the unsettled tail's stack
  have hp1 := part1 As P acc0 [] hPA (fun x _ n hn => by cases hn) hPne hA0
  rw [hfst] at hp1
  have hunsP : unsettled (P.foldl (settledStep As) acc0).2 P = unsettled (settledOf As Rs) P :=
    List.filter_congr (fun x hx => by
      have hiff := settled_prefix_lines As P (u :: c'') acc0 hne x hx
      rw [← hRs] at hiff
      have h2 : (settledOf As Rs).contains x.line = (Rs.foldl (settledStep As) acc0).2.contains x.line := by
        rw [hset]; simp
      rw [h2]
      congr 1
      cases h1 : (P.foldl (settledStep As) acc0).2.contains x.line <;>
        cases h3 : (Rs.foldl (settledStep As) acc0).2.contains x.line <;> simp_all)
  rw [hunsP] at hp1
  have hspl := split_stackOf As P hPA
  rw [find?_split hspl] at hm
  cases hUf : ((stackOf (As ++ P)).filter (fun x => !As.contains x)).find? (Replay.«matches» of_ id) with
  | some m' =>
    rw [hUf] at hm
    simp only [Option.some_or, Option.some.injEq] at hm
    subst hm
    rw [hp1] at hUf
    have hmem := mem_undoTargets _ _ _ u of_ id hNsplit hev m' hUf
    have := hvi _ hmem
    simp only at this
    omega
  | none =>
    exfalso
    rw [hUf] at hm
    simp only [Option.none_or] at hm
    have := (List.mem_filter.1 (List.mem_of_find?_eq_some hm)).2
    rw [hmA] at this
    cases this

/-- **An undo past the cut finds its first match on the whole log's stack past the cut, or none** (G1, and the fold
point's condition (vi)). -/
theorem cut_step (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut As Rs ws) (unsettled (settledOf As Rs) (Rs ++ B')) = none)
    (c : Nat) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (hvi : ∀ ut ∈ undoTargets (unsettled (settledOf As Rs) (Rs ++ B')), ¬ (ut.2.line ≤ c ∧ c < ut.1.line))
    (P post : List Entry) (u : Entry) (hs : Rs ++ B' = P ++ u :: post) (hu : c < u.line)
    (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id)
    (m : Entry) (hm : (stackOf (As ++ P)).find? (Replay.«matches» of_ id) = some m) : c < m.line := by
  rcases List.append_eq_append_iff.1 hs with ⟨a', hP, hB'⟩ | ⟨c', hRs, hc'⟩
  · subst hP
    exact cut_step_past z T₀ L cut As Rs B' ws hd hg c hsettled hvi a' post u hB' hu of_ id hev m hm
  · cases c' with
    | nil =>
      simp only [List.append_nil] at hRs
      simp only [List.nil_append] at hc'
      subst hRs
      exact cut_step_past z T₀ L cut As Rs B' ws hd hg c hsettled hvi [] post u (by rw [← hc']; rfl) hu of_ id hev m
        (by simpa using hm)
    | cons x c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc'
      obtain ⟨rfl, -⟩ := hc'
      exact cut_step_within As Rs B' hd c hsettled hvi P c'' u hRs hu of_ id hev m hm

/-- **The folded lines' own mask at the cut**: under G1 and the fold point's condition (vi), the survivors of the
folded lines alone are the stored survivors, then the folded tail's; the unfolded lines cancel nothing folded. -/
theorem survivors_at_cut (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut As Rs ws) (unsettled (settledOf As Rs) (Rs ++ B')) = none)
    (c : Nat) (hAc : ∀ x ∈ As, x.line ≤ c) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (hvi : ∀ ut ∈ undoTargets (unsettled (settledOf As Rs) (Rs ++ B')), ¬ (ut.2.line ≤ c ∧ c < ut.1.line))
    (Bj Brest : List Entry) (hsplit : Rs ++ B' = Bj ++ Brest) (hBj : ∀ x ∈ Bj, x.line ≤ c)
    (hBrest : ∀ x ∈ Brest, c < x.line) :
    survivors (As ++ Bj) = foldedSurvivors (As ++ Bj) Brest := by
  have hd' : ((As ++ Bj) ++ Brest).Pairwise (fun x y => x.line < y.line) := by
    rw [List.append_assoc, ← hsplit]; exact hd
  rw [foldedSurvivors_eq_filter (As ++ Bj) Brest hd']
  have hP : ∀ x ∈ Brest, (As ++ Bj).contains x = false := fun x hx => by
    have hxl := hBrest x hx
    have : x ∉ As ++ Bj := fun h => by
      rcases List.mem_append.1 h with h | h
      · have := hAc x h; omega
      · have := hBj x h; omega
    simpa using this
  have hstack : (Brest.foldl maskStep (stackOf (As ++ Bj))).filter (fun x => (As ++ Bj).contains x)
      = (stackOf (As ++ Bj)).filter (fun x => (As ++ Bj).contains x) := by
    refine foldl_maskStep_filter _ Brest _ hP (fun pre u post of_ id hs hev m hm => ?_)
    have hu : c < u.line := hBrest u (by rw [hs]; simp)
    have hs' : Rs ++ B' = (Bj ++ pre) ++ u :: post := by rw [hsplit, hs]; simp
    have hm' : (stackOf (As ++ (Bj ++ pre))).find? (Replay.«matches» of_ id) = some m := by
      rw [← List.append_assoc, stackOf_append]; exact hm
    have hml := cut_step z T₀ L cut As Rs B' ws hd hg c hsettled hvi (Bj ++ pre) post u hs' hu of_ id hev m hm'
    have : m ∉ As ++ Bj := fun h => by
      rcases List.mem_append.1 h with h | h
      · have := hAc m h; omega
      · have := hBj m h; omega
    simpa using this
  have hall : (stackOf (As ++ Bj)).filter (fun x => (As ++ Bj).contains x) = stackOf (As ++ Bj) :=
    List.filter_eq_self.2 (fun x hx => by
      rcases mem_foldl_maskStep' _ [] x hx with h | h
      · cases h
      · simpa using h)
  show (stackOf (As ++ Bj)).reverse
    = (stackOf ((As ++ Bj) ++ Brest)).reverse.filter (fun x => (As ++ Bj).contains x)
  rw [stackOf_append (As ++ Bj) Brest, List.filter_reverse, hstack, hall]

theorem dangleStep_fst (acc : List Entry × List Entry) (e : Entry) : (dangleStep acc e).1 = maskStep acc.1 e := by
  have := Replay.danglingOf_fst_go [e] acc.1 acc.2
  simpa using this

theorem settledStep_fst_one (A : List Entry) (acc : List Entry × List Nat) (e : Entry) :
    (settledStep A acc e).1 = maskStep acc.1 e := by
  have := settledStep_fst A [e] acc
  simpa using this

theorem mem_of_mem_dangling : ∀ (N : List Entry) (acc : List Entry × List Entry) (u : Entry),
    u ∈ (N.foldl dangleStep acc).2 → u ∈ acc.2 ∨ u ∈ N
  | [], _, _, h => Or.inl h
  | e :: N, acc, u, h => by
    rw [List.foldl_cons] at h
    rcases mem_of_mem_dangling N _ u h with h | h
    · unfold dangleStep at h
      cases hev : e.ev with
      | undo of_ id =>
        simp only [hev] at h
        split at h
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
      | _ => simp only [hev] at h; exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **The first-match equality, past the stored remainder.** -/
theorem cut_find_past (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut As Rs ws) (unsettled (settledOf As Rs) (Rs ++ B')) = none)
    (c : Nat) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (a' post : List Entry) (u : Entry) (hB' : B' = a' ++ u :: post) (hu : c < u.line)
    (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id) :
    (stackOf (As ++ (Rs ++ a'))).find? (Replay.«matches» of_ id)
      = (stackOf (unsettled (settledOf As Rs) (Rs ++ a'))).find? (Replay.«matches» of_ id) := by
  have huS : u.line ∉ settledOf As Rs := fun h => by have := hsettled _ h; omega
  have hNsplit := unsettled_split_at As Rs (Rs ++ B') (Rs ++ a') post u (by rw [hB']; simp) huS
  have hd' : (As ++ (Rs ++ a')).Pairwise (fun x y => x.line < y.line) :=
    hd.sublist (List.Sublist.append_left (List.Sublist.append_left (by rw [hB']; exact List.sublist_append_left _ _) Rs) As)
  have hg' : g1 (ckptOfEntries z T₀ L cut As Rs ws)
      (unsettled (ckptOfEntries z T₀ L cut As Rs ws).settled (Rs ++ a')) = none := by
    rw [ckpt_settled]
    rw [hNsplit] at hg
    exact g1_prefix _ _ _ hg
  have hsurv := survivors_append_of_g1 As Rs a' hd' _ (ckpt_tagLast z T₀ L cut As Rs ws)
    (ckpt_tagOverflow z T₀ L cut As Rs ws) (ckpt_settled z T₀ L cut As Rs ws) hg'
  rw [ckpt_settled] at hsurv
  have hst : stackOf (As ++ (Rs ++ a')) = stackOf (unsettled (settledOf As Rs) (Rs ++ a'))
      ++ (foldedSurvivors As Rs).reverse := by
    have := congrArg List.reverse hsurv
    simp only [survivors, List.reverse_append, List.reverse_reverse] at this
    exact this
  rw [hst, List.find?_append]
  cases hNf : (stackOf (unsettled (settledOf As Rs) (Rs ++ a'))).find? (Replay.«matches» of_ id) with
  | some m' => rfl
  | none =>
    have hdang := dangles_of_no_match (unsettled (settledOf As Rs) (Rs ++ a')) (unsettled (settledOf As Rs) post)
      u of_ id hev hNf
    rw [← hNsplit] at hdang
    have hreach : reachOf (ckptOfEntries z T₀ L cut As Rs ws) u = none :=
      (List.findSome?_eq_none_iff.1 hg) u (List.mem_reverse.2 hdang)
    have hSA : (foldedSurvivors As Rs).reverse.find? (Replay.«matches» of_ id) = none :=
      List.find?_eq_none.2 (fun x hx => by
        have := dangling_misses_the_folded As Rs _ (ckpt_tagLast z T₀ L cut As Rs ws)
          (ckpt_tagOverflow z T₀ L cut As Rs ws) u hreach of_ id hev x (List.mem_reverse.1 hx)
        simp [this])
    rw [hSA]; rfl

/-- **The first-match equality, within the stored remainder.** -/
theorem cut_find_within (As Rs B' : List Entry)
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (c : Nat) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (P c'' : List Entry) (u : Entry) (hRs : Rs = P ++ u :: c'') (hu : c < u.line)
    (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id) :
    (stackOf (As ++ P)).find? (Replay.«matches» of_ id)
      = (stackOf (unsettled (settledOf As Rs) P)).find? (Replay.«matches» of_ id) := by
  obtain ⟨-, hdRB, hdX⟩ := List.pairwise_append.1 hd
  have hAx : ∀ x ∈ Rs ++ B', As.contains x = false := fun x hx => by
    have : x ∉ As := fun hxA => by have := hdX x hxA x hx; omega
    simpa using this
  have hPR : ∀ x ∈ P, x ∈ Rs := fun x hx => by rw [hRs]; exact List.mem_append_left _ hx
  have hPA : ∀ x ∈ P, As.contains x = false := fun x hx => hAx x (List.mem_append_left _ (hPR x hx))
  have huS : u.line ∉ settledOf As Rs := fun h => by have := hsettled _ h; omega
  have hdR : Rs.Pairwise (fun x y => x.line < y.line) := (List.pairwise_append.1 hdRB).1
  have hne : ∀ x ∈ P, ∀ y ∈ u :: c'', x.line ≠ y.line := fun x hx y hy => by
    rw [hRs] at hdR
    exact Nat.ne_of_lt ((List.pairwise_append.1 hdR).2.2 x hx y hy)
  have hPne : P.Pairwise (fun x y => x.line ≠ y.line) := by
    rw [hRs] at hdR
    exact (List.pairwise_append.1 hdR).1.imp (fun h => Nat.ne_of_lt h)
  let acc0 : List Entry × List Nat := (stackOf As, [])
  have hA0 : (stackOf As).filter (fun x => !As.contains x) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by
      rcases mem_foldl_maskStep' As [] x hx with h | h
      · cases h
      · simp [h])
  have hset : settledOf As Rs = (Rs.foldl (settledStep As) acc0).2.reverse := rfl
  have hfst : (P.foldl (settledStep As) acc0).1 = stackOf (As ++ P) := by rw [settledStep_fst, stackOf_append]
  have hp1 := part1 As P acc0 [] hPA (fun x _ n hn => by cases hn) hPne hA0
  rw [hfst] at hp1
  have hunsP : unsettled (P.foldl (settledStep As) acc0).2 P = unsettled (settledOf As Rs) P :=
    List.filter_congr (fun x hx => by
      have hiff := settled_prefix_lines As P (u :: c'') acc0 hne x hx
      rw [← hRs] at hiff
      have h2 : (settledOf As Rs).contains x.line = (Rs.foldl (settledStep As) acc0).2.contains x.line := by
        rw [hset]; simp
      rw [h2]
      congr 1
      cases h1 : (P.foldl (settledStep As) acc0).2.contains x.line <;>
        cases h3 : (Rs.foldl (settledStep As) acc0).2.contains x.line <;> simp_all)
  rw [hunsP] at hp1
  have hspl := split_stackOf As P hPA
  rw [find?_split hspl, hp1]
  change ((stackOf (unsettled (settledOf As Rs) P)).find? (Replay.«matches» of_ id)).or
      (((stackOf (As ++ P)).filter (fun x => As.contains x)).find? (Replay.«matches» of_ id))
    = (stackOf (unsettled (settledOf As Rs) P)).find? (Replay.«matches» of_ id)
  cases hUf : (stackOf (unsettled (settledOf As Rs) P)).find? (Replay.«matches» of_ id) with
  | some m' => rfl
  | none =>
    cases hVf : ((stackOf (As ++ P)).filter (fun x => As.contains x)).find? (Replay.«matches» of_ id) with
    | none => rfl
    | some m =>
      exfalso
      have hmA : As.contains m = true := (List.mem_filter.1 (List.mem_of_find?_eq_some hVf)).2
      have hfind : (stackOf (As ++ P)).find? (Replay.«matches» of_ id) = some m := by
        rw [find?_split hspl, hp1]
        change ((stackOf (unsettled (settledOf As Rs) P)).find? (Replay.«matches» of_ id)).or
          (((stackOf (As ++ P)).filter (fun x => As.contains x)).find? (Replay.«matches» of_ id)) = some m
        rw [hUf, hVf]; rfl
      have hsplitRs : Rs.foldl (settledStep As) acc0
          = c''.foldl (settledStep As) (settledStep As (P.foldl (settledStep As) acc0) u) := by
        rw [hRs, List.foldl_append, List.foldl_cons]
      have hfst' := hfst
      generalize P.foldl (settledStep As) acc0 = accP at hfst' hsplitRs
      apply huS
      rw [hset, List.mem_reverse, hsplitRs]
      apply settled_lines_mono
      have hcond : (accP.1.find? (Replay.«matches» of_ id)).all (fun t => As.contains t) = true := by
        rw [hfst', hfind]; exact hmA
      unfold settledStep
      rw [hev]
      simp only [hcond, ↓reduceIte]
      exact List.mem_cons_self

/-- **At an undo past the cut, the whole log's first match is the unsettled tail's** (G1). -/
theorem cut_find_eq (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut As Rs ws) (unsettled (settledOf As Rs) (Rs ++ B')) = none)
    (c : Nat) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (P post : List Entry) (u : Entry) (hs : Rs ++ B' = P ++ u :: post) (hu : c < u.line)
    (of_ : List Char) (id : Option Log.Id) (hev : u.ev = .undo of_ id) :
    (stackOf (As ++ P)).find? (Replay.«matches» of_ id)
      = (stackOf (unsettled (settledOf As Rs) P)).find? (Replay.«matches» of_ id) := by
  rcases List.append_eq_append_iff.1 hs with ⟨a', hP, hB'⟩ | ⟨c', hRs, hc'⟩
  · subst hP
    exact cut_find_past z T₀ L cut As Rs B' ws hd hg c hsettled a' post u hB' hu of_ id hev
  · cases c' with
    | nil =>
      simp only [List.append_nil] at hRs
      simp only [List.nil_append] at hc'
      subst hRs
      simpa using cut_find_past z T₀ L cut As Rs B' ws hd hg c hsettled [] post u (by rw [← hc']; rfl) hu of_ id hev
    | cons x c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc'
      obtain ⟨rfl, -⟩ := hc'
      exact cut_find_within As Rs B' hd c hsettled P c'' u hRs hu of_ id hev

theorem stackOf_snoc (X : List Entry) (y : Entry) : stackOf (X ++ [y]) = maskStep (stackOf X) y := by
  unfold stackOf; rw [List.foldl_append]; rfl

/-- **The resealed `settled`**: the unfolded undos of the unsettled tail that dangle there are exactly the settled
undos of the folded lines at the cut (G1 and the fold point's condition (vi)). -/
theorem settled_at_cut (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn))
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (hg : g1 (ckptOfEntries z T₀ L cut As Rs ws) (unsettled (settledOf As Rs) (Rs ++ B')) = none)
    (c : Nat) (hAc : ∀ x ∈ As, x.line ≤ c) (hsettled : ∀ n ∈ settledOf As Rs, n ≤ c)
    (hvi : ∀ ut ∈ undoTargets (unsettled (settledOf As Rs) (Rs ++ B')), ¬ (ut.2.line ≤ c ∧ c < ut.1.line))
    (Bj Brest : List Entry) (hsplit : Rs ++ B' = Bj ++ Brest) (hBj : ∀ x ∈ Bj, x.line ≤ c)
    (hBrest : ∀ x ∈ Brest, c < x.line) :
    (((danglingOf (unsettled (settledOf As Rs) (Rs ++ B'))).2.filter (fun u => decide (c < u.line))).map
      (·.line)).reverse = settledOf (As ++ Bj) Brest := by
  have hnotS : ∀ x ∈ Brest, x.line ∉ settledOf As Rs := fun x hx h => by
    have := hsettled _ h; have := hBrest x hx; omega
  have hN : unsettled (settledOf As Rs) (Rs ++ B') = unsettled (settledOf As Rs) Bj ++ Brest := by
    rw [hsplit, unsettled_append, unsettled_of_lines _ Brest hnotS]
  have hpre : ∀ pre, (∃ Y, Brest = pre ++ Y) →
      unsettled (settledOf As Rs) (Bj ++ pre) = unsettled (settledOf As Rs) Bj ++ pre := fun pre ⟨Y, hY⟩ => by
    rw [unsettled_append, unsettled_of_lines _ pre (fun x hx => hnotS x (by rw [hY]; exact List.mem_append_left _ hx))]
  suffices G : ∀ (Y pre : List Entry) (accD : List Entry × List Entry) (accS : List Entry × List Nat),
      Brest = pre ++ Y → accD.1 = stackOf (unsettled (settledOf As Rs) Bj ++ pre) →
      accS.1 = stackOf (As ++ (Bj ++ pre)) →
      (accD.2.filter (fun u => decide (c < u.line))).map (·.line) = accS.2 →
      ((Y.foldl dangleStep accD).2.filter (fun u => decide (c < u.line))).map (·.line)
        = (Y.foldl (settledStep (As ++ Bj)) accS).2 by
    rw [hN]
    unfold danglingOf settledOf
    rw [List.foldl_append]
    congr 1
    refine G Brest [] _ _ (by simp) ?_ (by rw [List.append_nil]; rfl) ?_
    · rw [Replay.danglingOf_fst_go, List.append_nil]; rfl
    · rw [List.filter_eq_nil_iff.2 (fun u hu => by
        rcases mem_of_mem_dangling _ ([], []) u hu with h | h
        · cases h
        · have := hBj u (mem_unsettled_sub _ _ u h)
          simp only [decide_eq_true_eq]; omega)]
      rfl
  intro Y
  induction Y with
  | nil => intro pre accD accS _ _ _ h; exact h
  | cons y Y ih =>
    intro pre accD accS hY hD hS h2
    rw [List.foldl_cons, List.foldl_cons]
    have hyB : y ∈ Brest := by rw [hY]; simp
    refine ih (pre ++ [y]) _ _ (by rw [hY]; simp) ?_ ?_ ?_
    · have e' : unsettled (settledOf As Rs) Bj ++ (pre ++ [y]) = (unsettled (settledOf As Rs) Bj ++ pre) ++ [y] := by
        simp
      rw [dangleStep_fst, hD, e', stackOf_snoc]
    · have e : As ++ (Bj ++ (pre ++ [y])) = (As ++ (Bj ++ pre)) ++ [y] := by simp
      rw [settledStep_fst_one, hS, e, stackOf_snoc]
    · unfold dangleStep settledStep
      cases hev : y.ev with
      | undo of_ id =>
        simp only
        have hs : Rs ++ B' = (Bj ++ pre) ++ y :: Y := by rw [hsplit, hY]; simp
        have hu : c < y.line := hBrest y hyB
        have hfeq := cut_find_eq z T₀ L cut As Rs B' ws hd hg c hsettled (Bj ++ pre) Y y hs hu of_ id hev
        rw [hpre pre ⟨y :: Y, hY⟩, ← hD, ← hS] at hfeq
        cases hf : accD.1.find? (Replay.«matches» of_ id) with
        | none =>
          have hany : accD.1.any (Replay.«matches» of_ id) = false := by
            rw [List.any_eq_false]; intro x hx hxm; exact absurd hxm (by simpa using List.find?_eq_none.1 hf x hx)
          rw [hf] at hfeq
          simp only [hany, Bool.false_eq_true, ↓reduceIte, hfeq, Option.all_none, List.filter_cons,
            decide_eq_true_eq, hu, List.map_cons, h2]
        | some m =>
          have hany : accD.1.any (Replay.«matches» of_ id) = true :=
            List.any_eq_true.2 ⟨m, List.mem_of_find?_eq_some hf, List.find?_some hf⟩
          rw [hf] at hfeq
          have hml := cut_step z T₀ L cut As Rs B' ws hd hg c hsettled hvi (Bj ++ pre) Y y hs hu of_ id hev m
            (by rw [← hS, hfeq])
          have hmE : (As ++ Bj).contains m = false := by
            have : m ∉ As ++ Bj := fun hm' => by
              rcases List.mem_append.1 hm' with hm' | hm'
              · have := hAc m hm'; omega
              · have := hBj m hm'; omega
            simpa using this
          simp only [hany, ↓reduceIte, hfeq, Option.all_some, hmE, Bool.false_eq_true, h2]
      | _ => simp only; exact h2

end Seal
end Tm
