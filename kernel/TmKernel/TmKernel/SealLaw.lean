import TmKernel.Seal
/-!
# SealLaw — the partition laws: the checkpoint and the sealed records read as the replay (stage 5, D9, W2)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.5 laws 1 and 11, §14.5's W2 row.  **Law 1** is stated query by
query over every stored form: the answer at or above its horizons (`the_answer_reads_the_replay`), the day records
below the ledger day (`a_day_record_is_the_replays_day`), the window records below the window horizon
(`a_window_record_is_the_replays_window`) and their merge (`seal_partition_is_the_replay`).  **Law 11** puts the
sealed and the live observations back together by line (`sealed_and_live_observations_are_the_replays`).

Each holds for every log and every ledger day: the stored forms are canonical lists read through `get` (W1), so the
proofs are about canonical lists (`canon`, strictly sorted and one pair a key) and a stable sort that commutes with a
filter.  `sealable` is not needed by either law (the §15 statements carry it; the companions here do not).

Nothing here is on the wire (D9-21): every definition is specification.
-/
namespace Tm
namespace Seal

open Replay (State Doc Obs EnergyObs DurationObs HeaderRec Machine DayAcc SeamAcc)
open Log (Entry)

/-! ## Strict total orders and canonical lists -/

/-- **A strict total order**, as a Boolean test. -/
structure StrictTotal {α : Type} (lt : α → α → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

theorem StrictTotal.eq_of_not {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) {a b : α}
    (h1 : lt a b = false) (h2 : lt b a = false) : a = b := by
  refine Classical.byContradiction (fun hne => ?_)
  rcases h.total a b hne with h3 | h3
  · rw [h1] at h3; cases h3
  · rw [h2] at h3; cases h3

theorem StrictTotal.asymm {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) {a b : α}
    (hab : lt a b = true) : lt b a = false := by
  cases hba : lt b a with
  | false => rfl
  | true => have := h.trans a b a hab hba; rw [h.irrefl] at this; cases this

theorem mem_insUniq {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (x : α) :
    ∀ (l : List α) (y : α), y ∈ insUniq lt x l ↔ y = x ∨ y ∈ l
  | [], y => by simp [insUniq]
  | a :: l, y => by
    unfold insUniq
    split
    · simp
    · split
      · rw [List.mem_cons, mem_insUniq h x l y, List.mem_cons]
        constructor
        · rintro (h1 | h1 | h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h1)
        · rintro (h1 | h1 | h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h1)
      · rename_i h1 h2
        have hxa : x = a := h.eq_of_not (by simpa using h1) (by simpa using h2)
        subst hxa
        simp

theorem sorted_insUniq {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (x : α) :
    ∀ (l : List α), l.Pairwise (fun a b => lt a b = true) → (insUniq lt x l).Pairwise (fun a b => lt a b = true)
  | [], _ => by simp [insUniq]
  | a :: l, hl => by
    unfold insUniq
    split
    · rename_i hxa
      refine List.Pairwise.cons (fun b hb => ?_) hl
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hxa
      · exact h.trans _ _ _ hxa (List.rel_of_pairwise_cons hl hb)
    · split
      · rename_i _ hax
        refine List.Pairwise.cons (fun b hb => ?_) (sorted_insUniq h x l hl.of_cons)
        rcases (mem_insUniq h x l b).1 hb with rfl | hb
        · exact hax
        · exact List.rel_of_pairwise_cons hl hb
      · exact hl

theorem mem_foldl_insUniq {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) :
    ∀ (l acc : List α) (y : α), y ∈ l.foldl (fun acc x => insUniq lt x acc) acc ↔ y ∈ l ∨ y ∈ acc
  | [], acc, y => by simp
  | x :: l, acc, y => by
    rw [List.foldl_cons, mem_foldl_insUniq h l _ y, mem_insUniq h x acc y, List.mem_cons]
    constructor
    · rintro (h1 | h1 | h1)
      · exact Or.inl (Or.inr h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
    · rintro ((h1 | h1) | h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inr h1)

theorem sorted_foldl_insUniq {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) :
    ∀ (l acc : List α), acc.Pairwise (fun a b => lt a b = true) →
      (l.foldl (fun acc x => insUniq lt x acc) acc).Pairwise (fun a b => lt a b = true)
  | [], _, hacc => hacc
  | x :: l, acc, hacc => by
    rw [List.foldl_cons]
    exact sorted_foldl_insUniq h l _ (sorted_insUniq h x acc hacc)

/-- **A canonical list holds exactly its list's elements.** -/
theorem mem_canon {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (l : List α) (y : α) :
    y ∈ canon lt l ↔ y ∈ l := by
  unfold canon
  rw [mem_foldl_insUniq h l [] y]
  simp

theorem sorted_canon {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (l : List α) :
    (canon lt l).Pairwise (fun a b => lt a b = true) :=
  sorted_foldl_insUniq h l [] List.Pairwise.nil

theorem nodup_of_sorted {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) {l : List α}
    (hs : l.Pairwise (fun a b => lt a b = true)) : l.Nodup :=
  hs.imp (fun {a b} hab heq => by subst heq; rw [h.irrefl] at hab; cases hab)

theorem nodup_canon {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (l : List α) : (canon lt l).Nodup :=
  nodup_of_sorted h (sorted_canon h l)

/-- Two strictly sorted lists with one set of elements are one list. -/
theorem eq_of_sorted_of_mem_iff {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) :
    ∀ (l₁ l₂ : List α), l₁.Pairwise (fun a b => lt a b = true) → l₂.Pairwise (fun a b => lt a b = true) →
      (∀ y, y ∈ l₁ ↔ y ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hm => absurd ((hm b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, hm => absurd ((hm a).1 List.mem_cons_self) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, hm => by
    have hab : a = b := by
      refine Classical.byContradiction (fun hne => ?_)
      rcases h.total a b hne with hlt | hlt
      · -- `a` is in the second list, after `b`, so `b < a`
        have ha2 := (hm a).1 List.mem_cons_self
        rcases List.mem_cons.1 ha2 with rfl | ha2
        · exact hne rfl
        · have := List.rel_of_pairwise_cons h₂ ha2
          rw [h.asymm hlt] at this; cases this
      · have hb1 := (hm b).2 List.mem_cons_self
        rcases List.mem_cons.1 hb1 with rfl | hb1
        · exact hne rfl
        · have := List.rel_of_pairwise_cons h₁ hb1
          rw [h.asymm hlt] at this; cases this
    subst hab
    congr 1
    refine eq_of_sorted_of_mem_iff h l₁ l₂ h₁.of_cons h₂.of_cons (fun y => ?_)
    constructor
    · intro hy
      have hne : y ≠ a := fun heq => by
        subst heq; have := List.rel_of_pairwise_cons h₁ hy; rw [h.irrefl] at this; cases this
      rcases List.mem_cons.1 ((hm y).1 (List.mem_cons_of_mem _ hy)) with h' | h'
      · exact absurd h' hne
      · exact h'
    · intro hy
      have hne : y ≠ a := fun heq => by
        subst heq; have := List.rel_of_pairwise_cons h₂ hy; rw [h.irrefl] at this; cases this
      rcases List.mem_cons.1 ((hm y).2 (List.mem_cons_of_mem _ hy)) with h' | h'
      · exact absurd h' hne
      · exact h'

/-- **A canonical list depends only on the set of its list's elements.** -/
theorem canon_eq_of_mem_iff {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) (l₁ l₂ : List α)
    (hm : ∀ y, y ∈ l₁ ↔ y ∈ l₂) : canon lt l₁ = canon lt l₂ :=
  eq_of_sorted_of_mem_iff h _ _ (sorted_canon h l₁) (sorted_canon h l₂)
    (fun y => by rw [mem_canon h, mem_canon h, hm y])

/-! ### The orders of the checkpoint's keys are strict total orders -/

theorem natLt_strictTotal : StrictTotal natLt :=
  ⟨fun a => by simp [natLt], fun a b c h₁ h₂ => by simp [natLt] at *; omega,
   fun a b hne => by simp only [natLt, decide_eq_true_eq]; omega⟩

theorem charsLt_trans : ∀ (a b c : List Char), Log.charsLt a b = true → Log.charsLt b c = true → Log.charsLt a c = true
  | [], [], _, h, _ => by simp [Log.charsLt] at h
  | [], _ :: _, [], _, h => by simp [Log.charsLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [Log.charsLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [Log.charsLt] at h
  | x :: as, y :: bs, w :: cs, h₁, h₂ => by
    simp only [Log.charsLt] at h₁ h₂ ⊢
    by_cases hxy : x.val < y.val
    · by_cases hyw : y.val < w.val
      · have hxw : x.val < w.val := by rw [UInt32.lt_iff_toNat_lt] at *; omega
        simp [hxw]
      · simp only [hyw, if_false] at h₂
        split at h₂
        · rename_i hyw'; subst hyw'; simp [hxy]
        · cases h₂
    · simp only [hxy, if_false] at h₁
      split at h₁
      · rename_i hxy'; subst hxy'
        by_cases hyw : x.val < w.val
        · simp [hyw]
        · simp only [hyw, if_false] at h₂ ⊢
          split at h₂
          · rename_i hxw; subst hxw; simp only [if_true]; exact charsLt_trans as bs cs h₁ h₂
          · cases h₂
      · cases h₁

theorem charsLt_total : ∀ (a b : List Char), a ≠ b → Log.charsLt a b = true ∨ Log.charsLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | x :: as, y :: bs, hne => by
    simp only [Log.charsLt]
    by_cases hxy : x.val < y.val
    · simp [hxy]
    · by_cases hyx : y.val < x.val
      · simp [hyx]
      · have hv : x = y := by
          rw [UInt32.lt_iff_toNat_lt] at hxy hyx
          exact Char.ext (UInt32.toNat_inj.1 (by omega))
        subst hv
        simp only [hxy, if_false, if_true]
        exact charsLt_total as bs (fun h => hne (by rw [h]))

theorem idLt_strictTotal : StrictTotal idLt := ⟨Log.charsLt_irrefl, charsLt_trans, charsLt_total⟩

theorem lexLt_strictTotal {α β : Type} [DecidableEq α] {lt₁ : α → α → Bool} {lt₂ : β → β → Bool}
    (h₁ : StrictTotal lt₁) (h₂ : StrictTotal lt₂) : StrictTotal (lexLt lt₁ lt₂) := by
  refine ⟨fun a => by simp [lexLt, h₁.irrefl, h₂.irrefl], fun a b c hab hbc => ?_, fun a b hne => ?_⟩
  · simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
    rcases hab with hab | ⟨hab, hab2⟩ <;> rcases hbc with hbc | ⟨hbc, hbc2⟩
    · exact Or.inl (h₁.trans _ _ _ hab hbc)
    · rw [← hbc]; exact Or.inl hab
    · rw [hab]; exact Or.inl hbc
    · exact Or.inr ⟨hab.trans hbc, h₂.trans _ _ _ hab2 hbc2⟩
  · simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h1 : a.1 = b.1
    · have h2 : a.2 ≠ b.2 := fun h2 => hne (Prod.ext h1 h2)
      rcases h₂.total _ _ h2 with h3 | h3
      · exact Or.inl (Or.inr ⟨h1, h3⟩)
      · exact Or.inr (Or.inr ⟨h1.symm, h3⟩)
    · rcases h₁.total _ _ h1 with h3 | h3
      · exact Or.inl (Or.inl h3)
      · exact Or.inr (Or.inl h3)

theorem optLt_strictTotal {α : Type} {lt : α → α → Bool} (h : StrictTotal lt) : StrictTotal (optLt lt) := by
  refine ⟨fun a => by cases a <;> simp [optLt, h.irrefl], fun a b c hab hbc => ?_, fun a b hne => ?_⟩
  · cases a <;> cases b <;> cases c <;> simp_all [optLt]
    exact h.trans _ _ _ hab hbc
  · cases a <;> cases b <;> simp_all [optLt]
    exact h.total _ _ hne

theorem instKeyLt_strictTotal : StrictTotal instKeyLt := lexLt_strictTotal idLt_strictTotal idLt_strictTotal

theorem namedKeyLt_strictTotal : StrictTotal namedKeyLt :=
  lexLt_strictTotal idLt_strictTotal (optLt_strictTotal idLt_strictTotal)

/-! ### Reading a canonical list -/

/-- A lookup by key over a list of distinct keys, each mapped to its value when it has one. -/
theorem find?_filterMap_of_nodup {κ β : Type} [DecidableEq κ] (g : κ → Option β) (k : κ) :
    ∀ (ks : List κ), ks.Nodup →
      (ks.filterMap (fun j => (g j).map (fun v => (j, v)))).find? (fun p => decide (p.1 = k))
        = if k ∈ ks then (g k).map (fun v => (k, v)) else none
  | [], _ => by simp
  | j :: ks, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.filterMap_cons]
    by_cases hjk : j = k
    · subst hjk
      cases hg : g j with
      | none =>
        simp only [Option.map_none, List.mem_cons, true_or, if_true]
        rw [find?_filterMap_of_nodup g j ks hnd.2]
        simp [hnd.1]
      | some v => simp
    · have hrest := find?_filterMap_of_nodup g k ks hnd.2
      cases hg : g j with
      | none =>
        simp only [Option.map_none]
        rw [hrest]
        simp [List.mem_cons, Ne.symm hjk]
      | some v =>
        simp only [Option.map_some, List.find?_cons, hjk, decide_false]
        rw [hrest]
        simp [List.mem_cons, Ne.symm hjk]

/-- A lookup by day over the records of a list of distinct days, each record carrying its day. -/
theorem find?_map_filter_of_nodup {γ : Type} (F : Nat → γ) (dayOfF : γ → Nat) (hF : ∀ d, dayOfF (F d) = d)
    (P : Nat → Bool) (d : Nat) :
    ∀ (ks : List Nat), ks.Nodup →
      ((ks.filter P).map F).find? (fun r => decide (dayOfF r = d)) = if d ∈ ks ∧ P d = true then some (F d) else none
  | [], _ => by simp
  | j :: ks, hnd => by
    rw [List.nodup_cons] at hnd
    have hrest := find?_map_filter_of_nodup F dayOfF hF P d ks hnd.2
    rw [List.filter_cons]
    by_cases hjd : j = d
    · subst hjd
      by_cases hP : P j = true
      · simp [hP, hF]
      · simp only [hP, Bool.false_eq_true, if_false]
        rw [hrest]
        simp [hP, hnd.1]
    · split
      · simp only [List.map_cons, List.find?_cons, hF, hjd, decide_false]
        rw [hrest]
        simp [List.mem_cons, Ne.symm hjd]
      · rw [hrest]
        simp [List.mem_cons, Ne.symm hjd]

/-! ## Every map of the replay's state is keyed -/

/-- **Every bucketed map of a state is keyed** (C7's `HMap.Keyed`): so a key is among a map's pairs exactly when
`get` finds it. -/
def AllKeyed (st : State) : Prop :=
  st.days.Keyed ∧ st.items.Keyed ∧ st.itemDays.Keyed ∧ st.lastDone.Keyed ∧ st.doneDates.Keyed ∧
  st.instances.Keyed ∧ st.named.Keyed ∧ st.dropped.Keyed ∧ st.seams.Keyed

theorem allKeyed_init (n : Nat) : AllKeyed (State.init n) :=
  ⟨Replay.HMap.keyed_empty n, Replay.HMap.keyed_empty n, Replay.HMap.keyed_empty n, Replay.HMap.keyed_empty n,
   Replay.HMap.keyed_empty n, Replay.HMap.keyed_empty n, Replay.HMap.keyed_empty n, Replay.HMap.keyed_empty n,
   Replay.HMap.keyed_empty n⟩

theorem AllKeyed.apply {a : State} (h : AllKeyed a) (x : Replay.Effect) : AllKeyed (Replay.applyEffect a x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases x with
  | dayAdd d op => exact ⟨Replay.HMap.keyed_alter _ _ _ h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | itemAdd i op => exact ⟨h1, Replay.HMap.keyed_alter _ _ _ h2, h3, h4, h5, h6, h7, h8, h9⟩
  | itemDay i d m => exact ⟨h1, h2, Replay.HMap.keyed_alter _ _ _ h3, h4, h5, h6, h7, h8, h9⟩
  | itemDaySub i d m =>
    simp only [Replay.applyEffect]
    split
    · exact ⟨h1, h2, Replay.HMap.keyed_alter _ _ _ h3, h4, h5, h6, h7, h8, h9⟩
    · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | markDone i t => exact ⟨h1, h2, h3, Replay.HMap.keyed_alter _ _ _ h4, h5, h6, h7, h8, h9⟩
  | doneDate i d => exact ⟨h1, h2, h3, h4, Replay.HMap.keyed_alter _ _ _ h5, h6, h7, h8, h9⟩
  | inst item inst r => exact ⟨h1, h2, h3, h4, h5, Replay.HMap.keyed_alter _ _ _ h6, h7, h8, h9⟩
  | named name id line t date => exact ⟨h1, h2, h3, h4, h5, h6, Replay.HMap.keyed_alter _ _ _ h7, h8, h9⟩
  | drop i => exact ⟨h1, h2, h3, h4, h5, h6, h7, Replay.HMap.keyed_alter _ _ _ h8, h9⟩
  | seam d op => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, Replay.HMap.keyed_alter _ _ _ h9⟩
  | obs o => cases o <;> exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | _ => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem AllKeyed.applyEffects {a : State} (h : AllKeyed a) :
    ∀ (fx : List Replay.Effect), AllKeyed (Replay.applyEffects a fx)
  | [] => h
  | x :: fx => by
    unfold Replay.applyEffects
    rw [List.foldl_cons]
    exact AllKeyed.applyEffects (h.apply x) fx

theorem AllKeyed.foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) {a : State}, AllKeyed a → AllKeyed (sv.foldl (Replay.stepWith z dy sl) a)
  | [], _, h => h
  | e :: sv, a, h => by
    rw [List.foldl_cons]
    exact AllKeyed.foldl z dy sl sv (h.applyEffects _)

theorem allKeyed_foldedState (z : Cal.Tz) (es er : List Entry) : AllKeyed (foldedState z es er) :=
  AllKeyed.foldl z _ _ _ (allKeyed_init _)

/-- A keyed map finds no key outside its pairs. -/
theorem get_eq_none_of_not_mem_keys {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (m : Replay.HMap κ β)
    (hm : m.Keyed) (k : κ) (h : k ∉ m.pairs.map Prod.fst) : m.get k = none := by
  cases hg : m.get k with
  | none => rfl
  | some v => exact absurd ((Replay.HMap.mem_keys_pairs_iff m hm k).2 (by simp [hg])) h

theorem mem_keys_of_get {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (m : Replay.HMap κ β)
    (hm : m.Keyed) (k : κ) (v : β) (h : m.get k = some v) : k ∈ m.pairs.map Prod.fst :=
  (Replay.HMap.mem_keys_pairs_iff m hm k).2 (by simp [h])

/-! ## A stable sort commutes with a filter -/

theorem insBy_nil' {α : Type} (le : α → α → Bool) (a : α) : Replay.insBy le a [] = [a] := rfl

theorem insBy_cons' {α : Type} (le : α → α → Bool) (a b : α) (l : List α) :
    Replay.insBy le a (b :: l) = if le a b then a :: b :: l else b :: Replay.insBy le a l := rfl

theorem insSort_cons' {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    Replay.insSort le (a :: l) = Replay.insBy le a (Replay.insSort le l) := rfl

theorem insBy_of_all {α : Type} (le : α → α → Bool) (a : α) :
    ∀ (l : List α), (∀ c ∈ l, le a c = true) → Replay.insBy le a l = a :: l
  | [], _ => rfl
  | c :: l, h => by rw [insBy_cons', if_pos (h c List.mem_cons_self)]

theorem insBy_filter {α : Type} (le : α → α → Bool) (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (p : α → Bool) (a : α) :
    ∀ (l : List α), l.Pairwise (fun x y => le x y = true) →
      (Replay.insBy le a l).filter p = if p a then Replay.insBy le a (l.filter p) else l.filter p
  | [], _ => by cases hp : p a <;> simp [insBy_nil', hp]
  | b :: l, hl => by
    have hb : ∀ c ∈ l, le b c = true := fun c hc => List.rel_of_pairwise_cons hl hc
    have ih := insBy_filter le trans p a l hl.of_cons
    rw [insBy_cons']
    by_cases hab : le a b = true
    · have hall : ∀ c ∈ l.filter p, le a c = true := fun c hc => trans a b c hab (hb c (List.mem_filter.1 hc).1)
      rw [if_pos hab]
      cases hpa : p a <;> cases hpb : p b
      · simp [List.filter_cons, hpa, hpb]
      · simp [List.filter_cons, hpa, hpb]
      · simp only [List.filter_cons, hpa, hpb, if_true, if_false, Bool.false_eq_true]
        rw [insBy_of_all le a _ hall]
      · simp only [List.filter_cons, hpa, hpb, if_true]
        rw [insBy_cons', if_pos hab]
    · rw [if_neg hab]
      cases hpa : p a <;> cases hpb : p b
      · simp only [List.filter_cons, hpa, hpb, Bool.false_eq_true, if_false] at ih ⊢
        exact ih
      · simp only [List.filter_cons, hpa, hpb, Bool.false_eq_true, if_false, if_true] at ih ⊢
        rw [ih]
      · simp only [List.filter_cons, hpa, hpb, Bool.false_eq_true, if_false, if_true] at ih ⊢
        exact ih
      · simp only [List.filter_cons, hpa, hpb, if_true] at ih ⊢
        rw [ih, insBy_cons', if_neg hab]

theorem insBy_sorted {α : Type} (le : α → α → Bool) (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true) (a : α) :
    ∀ (l : List α), l.Pairwise (fun x y => le x y = true) → (Replay.insBy le a l).Pairwise (fun x y => le x y = true)
  | [], _ => by simp [insBy_nil']
  | b :: l, hl => by
    rw [insBy_cons']
    split
    · rename_i hab
      refine List.Pairwise.cons (fun c hc => ?_) hl
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hab
      · exact trans _ _ _ hab (List.rel_of_pairwise_cons hl hc)
    · rename_i hab
      have hba : le b a = true := by
        rcases total a b with h | h
        · exact absurd h hab
        · exact h
      refine List.Pairwise.cons (fun c hc => ?_) (insBy_sorted le trans total a l hl.of_cons)
      rcases List.mem_cons.1 ((Replay.insBy_perm le a l).mem_iff.1 hc) with rfl | hc
      · exact hba
      · exact List.rel_of_pairwise_cons hl hc

theorem insSort_sorted {α : Type} (le : α → α → Bool) (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true) :
    ∀ (l : List α), (Replay.insSort le l).Pairwise (fun x y => le x y = true)
  | [] => List.Pairwise.nil
  | a :: l => by rw [insSort_cons']; exact insBy_sorted le trans total a _ (insSort_sorted le trans total l)

/-- **A stable sort commutes with a filter.** -/
theorem insSort_filter {α : Type} (le : α → α → Bool) (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true) (p : α → Bool) :
    ∀ (l : List α), (Replay.insSort le l).filter p = Replay.insSort le (l.filter p)
  | [] => rfl
  | a :: l => by
    rw [insSort_cons', insBy_filter le trans p a _ (insSort_sorted le trans total l), insSort_filter le trans total p l,
      List.filter_cons]
    cases hpa : p a
    · rfl
    · rfl

theorem obsLe_trans : ∀ a b c : EnergyObs, Replay.obsLe a b = true → Replay.obsLe b c = true → Replay.obsLe a c = true :=
  fun a b c h₁ h₂ => by simp [Replay.obsLe] at *; omega

theorem obsLe_total : ∀ a b : EnergyObs, Replay.obsLe a b = true ∨ Replay.obsLe b a = true :=
  fun a b => by simp only [Replay.obsLe, decide_eq_true_eq]; omega

theorem sortObs_filter (p : EnergyObs → Bool) (l : List EnergyObs) :
    (Replay.sortObs l).filter p = Replay.sortObs (l.filter p) :=
  insSort_filter Replay.obsLe obsLe_trans obsLe_total p l


/-! ## Law 1: the partition, query by query

Every reading of a state `st` grouped as the checkpoint groups it is the reading of `Replay.finish st`: a day's through
its record (`dayRead_state`), a window date's through its record (`winRead_state`), and an all-time one through the
items and the non-date instances.  The records are found by key in canonical lists (`find?_map_filter_of_nodup`). -/

section Partition

theorem filter_day_eq_nil {α : Type} (l : List α) (f : α → Nat) (d : Nat) (h : d ∉ l.map f) :
    l.filter (fun x => decide (f x = d)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx hfx
  exact h (List.mem_map.2 ⟨x, hx, by simpa using hfx⟩)

theorem not_mem_dayKeys {st : State} {hs : List (Nat × HeaderRec)} {d : Nat} (h : d ∉ dayKeys st hs) :
    d ∉ st.days.pairs.map Prod.fst ∧ d ∉ st.seams.pairs.map Prod.fst ∧ d ∉ st.energy.map (·.day) ∧
    d ∉ st.durations.map (·.day) ∧ d ∉ st.interrupts.map (·.day) ∧ d ∉ st.demotions.map Prod.fst ∧
    d ∉ st.closes.map Prod.fst ∧ d ∉ hs.map Prod.fst ∧ d ∉ ((st.machine.block.bind (·.obs)).map (·.day)).toList := by
  unfold dayKeys at h
  rw [mem_canon natLt_strictTotal] at h
  simp only [List.mem_append, not_or] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

theorem pendingOn_eq (m : Machine) (d : Nat) :
    pendingOn m d = ((m.block.bind (·.obs)).toList).filter (fun o => decide (o.day = d)) := by
  unfold pendingOn
  cases m.block.bind (·.obs) with
  | none => rfl
  | some o => by_cases h : o.day = d <;> simp [Option.filter, h]

/-- **A day's reading from its grouped record is the finished state's.** -/
theorem dayRead_state (st : State) (hs : List (Nat × HeaderRec)) (n : Nat) (hk : AllKeyed st) (d : Nat) (dq : DayQ) :
    dayRead (if d ∈ dayKeys st hs then some (OpenDay.finish st.machine (openDayOf st hs d)) else none) dq
      = Replay.ask ⟨Replay.finish st, hs, n⟩ (.day d dq) := by
  by_cases hd : d ∈ dayKeys st hs
  · rw [if_pos hd]
    cases dq with
    | record =>
      show Replay.Answer.dayRecord _ = Replay.Answer.dayRecord _
      simp [OpenDay.finish, openDayOf, Replay.finish, Replay.HMap.get_mapVals]
    | seam =>
      show Replay.Answer.seam _ = Replay.Answer.seam _
      simp [OpenDay.finish, openDayOf, Replay.finish, Replay.HMap.get_mapVals]
    | energy =>
      show Replay.Answer.energy (Replay.sortObs ((st.energy.filter (fun o => decide (o.day = d))).reverse
          ++ pendingOn st.machine d))
        = Replay.Answer.energy ((Replay.sortObs (st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList)).filter
          (fun o => decide (o.day = d)))
      rw [sortObs_filter, List.filter_append, List.filter_reverse, pendingOn_eq]
    | durations =>
      show Replay.Answer.durations (st.durations.filter (fun o => decide (o.day = d))).reverse
        = Replay.Answer.durations (st.durations.reverse.filter (fun o => decide (o.day = d)))
      rw [List.filter_reverse]
    | interrupts =>
      show Replay.Answer.interrupts (st.interrupts.filter (fun o => decide (o.day = d))).reverse
        = Replay.Answer.interrupts (st.interrupts.reverse.filter (fun o => decide (o.day = d)))
      rw [List.filter_reverse]
    | demotions =>
      show Replay.Answer.demotions ((st.demotions.filter (fun p => decide (p.1 = d))).map Prod.snd).reverse
        = Replay.Answer.demotions ((st.demotions.reverse.filter (fun p => decide (p.1 = d))).map Prod.snd)
      rw [List.filter_reverse, List.map_reverse]
    | closes =>
      show Replay.Answer.closes ((st.closes.filter (fun p => decide (p.1 = d))).map Prod.snd).reverse
        = Replay.Answer.closes ((st.closes.reverse.filter (fun p => decide (p.1 = d))).map Prod.snd)
      rw [List.filter_reverse, List.map_reverse]
    | headers => rfl
  · rw [if_neg hd]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := not_mem_dayKeys hd
    cases dq with
    | record =>
      show Replay.Answer.dayRecord none = Replay.Answer.dayRecord _
      simp [Replay.finish, Replay.HMap.get_mapVals, get_eq_none_of_not_mem_keys _ hk.1 d h1]
    | seam =>
      show Replay.Answer.seam none = Replay.Answer.seam _
      simp [Replay.finish, Replay.HMap.get_mapVals, get_eq_none_of_not_mem_keys _ hk.2.2.2.2.2.2.2.2 d h2]
    | energy =>
      show Replay.Answer.energy [] = Replay.Answer.energy _
      simp only [Replay.finish]
      rw [sortObs_filter, List.filter_append, List.filter_reverse, filter_day_eq_nil _ _ d h3,
        ← pendingOn_eq]
      unfold pendingOn
      cases hb : st.machine.block.bind (·.obs) with
      | none => rfl
      | some o =>
        rw [hb] at h9
        have : ¬ o.day = d := fun he => h9 (by simp [he])
        simp [Option.filter, this]; rfl
    | durations =>
      show Replay.Answer.durations [] = Replay.Answer.durations _
      simp only [Replay.finish]
      rw [List.filter_reverse, filter_day_eq_nil _ _ d h4]; rfl
    | interrupts =>
      show Replay.Answer.interrupts [] = Replay.Answer.interrupts _
      simp only [Replay.finish]
      rw [List.filter_reverse, filter_day_eq_nil _ _ d h5]; rfl
    | demotions =>
      show Replay.Answer.demotions [] = Replay.Answer.demotions _
      simp only [Replay.finish]
      rw [List.filter_reverse, filter_day_eq_nil _ Prod.fst d h6]; rfl
    | closes =>
      show Replay.Answer.closes [] = Replay.Answer.closes _
      simp only [Replay.finish]
      rw [List.filter_reverse, filter_day_eq_nil _ Prod.fst d h7]; rfl
    | headers =>
      show Replay.Answer.headers [] = Replay.Answer.headers _
      rw [filter_day_eq_nil _ Prod.fst d h8]; rfl

/-- **A day found among the grouped days of a range** is its record when the day has a reading. -/
theorem findDay_days (st : State) (hs : List (Nat × HeaderRec)) (m : Machine) (P : Nat → Bool) (d : Nat)
    (hP : P d = true) :
    findDay ((((dayKeys st hs).filter P).map (openDayOf st hs)).map (OpenDay.finish m)) d
      = if d ∈ dayKeys st hs then some (OpenDay.finish m (openDayOf st hs d)) else none := by
  unfold findDay
  rw [List.map_map]
  have := find?_map_filter_of_nodup (fun d => OpenDay.finish m (openDayOf st hs d)) DayRecord.day (fun _ => rfl) P d
    (dayKeys st hs) (by unfold dayKeys; exact nodup_canon natLt_strictTotal _)
  simp only [Function.comp_def] at this ⊢
  rw [this]
  by_cases hd : d ∈ dayKeys st hs <;> simp [hd, hP]

/-- A key among a keyed map's pairs is one `get` finds; a key not among them, `get` does not. -/
theorem get_filterMap_find {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (m : Replay.HMap κ β) (hm : m.Keyed)
    {lt : κ → κ → Bool} (hlt : StrictTotal lt) (P : κ → Bool) (k : κ) (hP : P k = true) :
    (((canon lt ((m.pairs.filter (fun p => P p.1)).map Prod.fst)).filterMap
      (fun j => (m.get j).map (fun v => (j, v)))).find? (fun p => decide (p.1 = k))).map Prod.snd = m.get k := by
  rw [find?_filterMap_of_nodup (fun j => m.get j) k _ (nodup_canon hlt _)]
  by_cases hk : k ∈ canon lt ((m.pairs.filter (fun p => P p.1)).map Prod.fst)
  · rw [if_pos hk, Option.map_map]
    cases m.get k <;> rfl
  · rw [if_neg hk]
    refine (get_eq_none_of_not_mem_keys m hm k (fun hmem => hk ?_)).symm
    rw [mem_canon hlt]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmem
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, hP⟩, rfl⟩

theorem not_mem_winKeys {st : State} {d : Nat} (h : d ∉ winKeys st) :
    d ∉ st.itemDays.pairs.map (·.1.1) ∧ d ∉ st.doneDates.pairs.map (·.1.1) ∧
    d ∉ st.instances.pairs.filterMap (fun p => Log.instDate? p.1.2) := by
  unfold winKeys at h
  rw [mem_canon natLt_strictTotal] at h
  simp only [List.mem_append, not_or] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pair_not_mem_keys {γ : Type} (l : List ((Nat × Log.Id) × γ)) (d : Nat) (i : Log.Id)
    (h : d ∉ l.map (·.1.1)) : (d, i) ∉ l.map Prod.fst := by
  intro hm
  obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
  exact h (List.mem_map.2 ⟨p, hp, by rw [hpe]⟩)

/-- **A window date's reading from its grouped record is the finished state's.** -/
theorem winRead_state (st : State) (hs : List (Nat × HeaderRec)) (n : Nat) (hk : AllKeyed st) (d : Nat) (wq : WinQ) :
    winRead (if d ∈ winKeys st then some (windowOf st d) else none) d wq
      = Replay.ask ⟨Replay.finish st, hs, n⟩ (.win d wq) := by
  by_cases hd : d ∈ winKeys st
  · rw [if_pos hd]
    cases wq with
    | itemMin i =>
      show Replay.Answer.minutes ((((canon idLt ((st.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))).filterMap
          (fun i => (st.itemDays.get (d, i)).map (fun m => (i, m)))).find? (fun p => decide (p.1 = i))).map Prod.snd)
        = Replay.Answer.minutes (st.itemDays.get (d, i))
      rw [find?_filterMap_of_nodup (fun j => st.itemDays.get (d, j)) i _ (nodup_canon idLt_strictTotal _)]
      by_cases hi : i ∈ canon idLt ((st.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))
      · rw [if_pos hi, Option.map_map]
        cases st.itemDays.get (d, i) <;> rfl
      · rw [if_neg hi]
        have hnone : st.itemDays.get (d, i) = none := get_eq_none_of_not_mem_keys _ hk.2.2.1 (d, i) (fun hmem => hi (by
          rw [mem_canon idLt_strictTotal]
          obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hmem
          exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hpe]⟩, by simp [hpe]⟩))
        rw [hnone]; rfl
    | done i =>
      show Replay.Answer.bool ((canon idLt ((st.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))).contains i)
        = Replay.Answer.bool (st.doneDates.get (d, i)).isSome
      congr 1
      rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_canon idLt_strictTotal,
        ← Replay.HMap.mem_keys_pairs_iff _ hk.2.2.2.2.1]
      constructor
      · intro hm
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
        have hpd := (List.mem_filter.1 hp).2
        simp only [decide_eq_true_eq] at hpd
        exact List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, by rw [← hpe, ← hpd]⟩
      · intro hm
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
        exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hpe]⟩, by simp [hpe]⟩
    | inst item inst =>
      show Replay.Answer.inst (if Log.instDate? inst = some d then
          (((canon instKeyLt ((st.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst)).filterMap
            (fun key => (st.instances.get key).map (fun r => (key, r)))).find? (fun p => decide (p.1 = (item, inst)))).map Prod.snd
          else none)
        = Replay.Answer.inst (if Log.instDate? inst = some d then st.instances.get (item, inst) else none)
      by_cases hi : Log.instDate? inst = some d
      · rw [if_pos hi, if_pos hi]
        exact congrArg _ (get_filterMap_find st.instances hk.2.2.2.2.2.1 instKeyLt_strictTotal
          (fun key => decide (Log.instDate? key.2 = some d)) (item, inst) (by simp [hi]))
      · rw [if_neg hi, if_neg hi]
  · rw [if_neg hd]
    obtain ⟨h1, h2, h3⟩ := not_mem_winKeys hd
    cases wq with
    | itemMin i =>
      show Replay.Answer.minutes none = Replay.Answer.minutes (st.itemDays.get (d, i))
      rw [get_eq_none_of_not_mem_keys _ hk.2.2.1 (d, i) (pair_not_mem_keys _ d i h1)]
    | done i =>
      show Replay.Answer.bool false = Replay.Answer.bool (st.doneDates.get (d, i)).isSome
      rw [get_eq_none_of_not_mem_keys _ hk.2.2.2.2.1 (d, i) (pair_not_mem_keys _ d i h2)]; rfl
    | inst item inst =>
      show Replay.Answer.inst (if Log.instDate? inst = some d then none else none)
        = Replay.Answer.inst (if Log.instDate? inst = some d then st.instances.get (item, inst) else none)
      by_cases hi : Log.instDate? inst = some d
      · have hnone : st.instances.get (item, inst) = none :=
          get_eq_none_of_not_mem_keys _ hk.2.2.2.2.2.1 (item, inst) (fun hm => h3 (by
            obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
            exact List.mem_filterMap.2 ⟨p, hp, by rw [hpe, hi]⟩))
        rw [if_pos hi, if_pos hi, hnone]
      · rw [if_neg hi, if_neg hi]

/-- **A window date found among the grouped windows of a range** is its record when the date has a fact. -/
theorem findWin_windows (st : State) (P : Nat → Bool) (d : Nat) (hP : P d = true) :
    findWin (((winKeys st).filter P).map (windowOf st)) d = if d ∈ winKeys st then some (windowOf st d) else none := by
  unfold findWin
  rw [find?_map_filter_of_nodup (windowOf st) WindowRecord.day (fun _ => rfl) P d (winKeys st)
    (by unfold winKeys; exact nodup_canon natLt_strictTotal _)]
  by_cases hd : d ∈ winKeys st <;> simp [hd, hP]

/-- A lookup by key over the images of a list of distinct keys, each image carrying its key. -/
theorem find?_map_of_nodup {κ γ : Type} [DecidableEq κ] (F : κ → γ) (key : γ → κ) (hF : ∀ k, key (F k) = k) (k : κ) :
    ∀ (ks : List κ), ks.Nodup → (ks.map F).find? (fun r => decide (key r = k)) = if k ∈ ks then some (F k) else none
  | [], _ => by simp
  | j :: ks, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.find?_cons, hF, find?_map_of_nodup F key hF k ks hnd.2]
    by_cases hjk : j = k
    · subst hjk; simp [hnd.1]
    · simp [hjk, Ne.symm hjk]

theorem not_mem_itemIds {st : State} {i : Log.Id} (h : i ∉ itemIds st) :
    i ∉ st.items.pairs.map Prod.fst ∧ i ∉ st.lastDone.pairs.map Prod.fst ∧ i ∉ st.dropped.pairs.map Prod.fst ∧
    i ∉ st.doneDates.pairs.map (·.1.2) := by
  unfold itemIds at h
  rw [mem_canon idLt_strictTotal] at h
  simp only [List.mem_append, not_or] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem findItem_items (st : State) (i : Log.Id) :
    findItem (((itemIds st).map (itemAggOf st)).map ItemAgg.finish) i
      = if i ∈ itemIds st then some (itemAggOf st i).finish else none := by
  unfold findItem
  rw [List.map_map]
  have h := find?_map_of_nodup (fun j => (itemAggOf st j).finish) ItemAgg.id (fun _ => rfl) i (itemIds st)
    (nodup_canon idLt_strictTotal _)
  by_cases hi : i ∈ itemIds st
  · rw [if_pos hi] at h ⊢; exact h
  · rw [if_neg hi] at h ⊢; exact h

theorem doneDays_nil_of_not_mem (l : List ((Nat × Log.Id) × Unit)) (i : Log.Id) (h : i ∉ l.map (·.1.2)) :
    l.filter (fun p => decide (p.1.2 = i)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp hpi
  exact h (List.mem_map.2 ⟨p, hp, by simpa using hpi⟩)

/-- **Every all-time reading of an item from the grouped items is the finished state's.** -/
theorem items_read_state (st : State) (hs : List (Nat × HeaderRec)) (n : Nat) (hk : AllKeyed st)
    (v : Seal.Answer) (hv : v.items = ((itemIds st).map (itemAggOf st)).map ItemAgg.finish) (i : Log.Id) :
    askAnswer v (.item i) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.item i)) ∧
    askAnswer v (.lastDone i) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.lastDone i)) ∧
    askAnswer v (.doneFirst i) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.doneFirst i)) ∧
    askAnswer v (.doneCount i) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.doneCount i)) ∧
    askAnswer v (.dropped i) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.dropped i)) := by
  have hf := findItem_items st i
  rw [← hv] at hf
  by_cases hi : i ∈ itemIds st
  · rw [if_pos hi] at hf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show some (Replay.Answer.item ((findItem v.items i).bind (·.acc)))
        = some (Replay.Answer.item ((st.items.mapVals Replay.ItemAcc.finish).get i))
      rw [hf, Replay.HMap.get_mapVals]; rfl
    · show some (Replay.Answer.stamp ((findItem v.items i).bind (·.lastDone))) = some (Replay.Answer.stamp (st.lastDone.get i))
      rw [hf]; rfl
    · show some (Replay.Answer.date ((findItem v.items i).bind (·.doneFirst)))
        = some (Replay.Answer.date (Replay.minDay? ((st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1))))
      rw [hf]; rfl
    · show some (Replay.Answer.count (((findItem v.items i).map (·.doneCount)).getD 0))
        = some (Replay.Answer.count ((st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)).length)
      rw [hf]; simp [itemAggOf, ItemAgg.finish]
    · show some (Replay.Answer.bool (((findItem v.items i).map (·.dropped)).getD false))
        = some (Replay.Answer.bool (st.dropped.get i).isSome)
      rw [hf]; rfl
  · rw [if_neg hi] at hf
    obtain ⟨h1, h2, h3, h4⟩ := not_mem_itemIds hi
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show some (Replay.Answer.item ((findItem v.items i).bind (·.acc)))
        = some (Replay.Answer.item ((st.items.mapVals Replay.ItemAcc.finish).get i))
      rw [hf, Replay.HMap.get_mapVals, get_eq_none_of_not_mem_keys _ hk.2.1 i h1]; rfl
    · show some (Replay.Answer.stamp ((findItem v.items i).bind (·.lastDone))) = some (Replay.Answer.stamp (st.lastDone.get i))
      rw [hf, get_eq_none_of_not_mem_keys _ hk.2.2.2.1 i h2]; rfl
    · show some (Replay.Answer.date ((findItem v.items i).bind (·.doneFirst)))
        = some (Replay.Answer.date (Replay.minDay? ((st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1))))
      rw [hf, doneDays_nil_of_not_mem _ i h4]; rfl
    · show some (Replay.Answer.count (((findItem v.items i).map (·.doneCount)).getD 0))
        = some (Replay.Answer.count ((st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)).length)
      rw [hf, doneDays_nil_of_not_mem _ i h4]; rfl
    · show some (Replay.Answer.bool (((findItem v.items i).map (·.dropped)).getD false))
        = some (Replay.Answer.bool (st.dropped.get i).isSome)
      rw [hf, get_eq_none_of_not_mem_keys _ hk.2.2.2.2.2.2.2.1 i h3]; rfl

/-- **The non-date instances and the named events from their grouped lists are the finished state's.** -/
theorem others_read_state (st : State) (hs : List (Nat × HeaderRec)) (n : Nat) (hk : AllKeyed st)
    (v : Seal.Answer) (hi : v.instOther = instOtherOf st) (hn : v.named = namedOf st) (item inst name : List Char)
    (id : Option Log.Id) :
    askAnswer v (.instOther item inst) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.instOther item inst)) ∧
    askAnswer v (.named name id) = some (Replay.ask ⟨Replay.finish st, hs, n⟩ (.named name id)) := by
  constructor
  · show some (Replay.Answer.inst (if Log.instDate? inst = none then
        (v.instOther.find? (fun p => decide (p.1 = (item, inst)))).map Prod.snd else none))
      = some (Replay.Answer.inst (if Log.instDate? inst = none then st.instances.get (item, inst) else none))
    by_cases hd : Log.instDate? inst = none
    · rw [if_pos hd, if_pos hd, hi]
      exact congrArg (fun x => some (Replay.Answer.inst x)) (get_filterMap_find st.instances hk.2.2.2.2.2.1
        instKeyLt_strictTotal (fun key => (Log.instDate? key.2).isNone) (item, inst) (by simp [hd]))
    · rw [if_neg hd, if_neg hd]
  · show some (Replay.Answer.named ((v.named.find? (fun p => decide (p.1 = (name, id)))).map Prod.snd))
      = some (Replay.Answer.named (st.named.get (name, id)))
    have h := get_filterMap_find st.named hk.2.2.2.2.2.2.1 namedKeyLt_strictTotal (fun _ => true) (name, id) rfl
    have hfe : st.named.pairs.filter (fun p => (fun _ => true) p.1) = st.named.pairs := List.filter_eq_self.2 (fun _ _ => rfl)
    rw [hfe] at h
    rw [hn]
    exact congrArg (fun x => some (Replay.Answer.named x)) h

/-- **Every scalar all-time reading** of an answer holding a state's scalars is the finished state's. -/
theorem scalars_read_state (st : State) (hs : List (Nat × HeaderRec)) (n : Nat) (v : Seal.Answer)
    (h1 : v.openBlock = Replay.openOf st.machine)
    (h2 : v.openInterrupt = st.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩))
    (h3 : v.lastDay = Replay.maxDay? (st.days.pairs.map Prod.fst)) (h4 : v.lastEffective = st.global.lastEffective)
    (h5 : v.unknown = st.unknown) (h6 : v.longestLeak = st.longestLeak) (h7 : v.rwarns = st.rwarns.reverse)
    (h8 : v.entryCount = n) :
    askAnswer v .openBlock = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .openBlock) ∧
    askAnswer v .openInterrupt = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .openInterrupt) ∧
    askAnswer v .lastDay = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .lastDay) ∧
    askAnswer v .lastEffective = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .lastEffective) ∧
    askAnswer v .unknown = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .unknown) ∧
    askAnswer v .longestLeak = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .longestLeak) ∧
    askAnswer v .replayWarnings = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .replayWarnings) ∧
    askAnswer v .entryCount = some (Replay.ask ⟨Replay.finish st, hs, n⟩ .entryCount) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show some (Replay.Answer.openBlock v.openBlock) = some (Replay.Answer.openBlock (Replay.finish st).openBlock)
    rw [h1]; rfl
  · show some (Replay.Answer.openInterrupt v.openInterrupt)
      = some (Replay.Answer.openInterrupt (Replay.finish st).openInterrupt)
    rw [h2]; rfl
  · show some (Replay.Answer.date v.lastDay)
      = some (Replay.Answer.date (Replay.maxDay? ((st.days.mapVals Replay.DayAcc.finish).pairs.map Prod.fst)))
    rw [h3, Replay.HMap.keys_pairs_mapVals]
  · show some (Replay.Answer.stamp v.lastEffective) = some (Replay.Answer.stamp st.global.lastEffective)
    rw [h4]
  · show some (Replay.Answer.count v.unknown) = some (Replay.Answer.count st.unknown)
    rw [h5]
  · show some (Replay.Answer.leak v.longestLeak) = some (Replay.Answer.leak st.longestLeak)
    rw [h6]
  · show some (Replay.Answer.warnings v.rwarns) = some (Replay.Answer.warnings st.rwarns.reverse)
    rw [h7]
  · show some (Replay.Answer.count v.entryCount) = some (Replay.Answer.count n)
    rw [h8]

/-! ### The answer of a specification checkpoint, field by field -/

section Proj

variable (z : Cal.Tz) (T₀ L cut : Nat) (es er : List Entry) (ws : List (Nat × Log.LWarn))

theorem ckptOf_eq (ls r : List Log.Line) :
    ckptOf z T₀ L ls r = ckptOfEntries z T₀ L ls.length (Log.lineEntries ls) (Log.lineEntries r) (Log.lineWarnings ls) :=
  rfl
theorem answer_ledgerDay : (answer (ckptOfEntries z T₀ L cut es er ws)).ledgerDay = L := by
  simp only [answer, ckptOfEntries]
theorem answer_horizon : (answer (ckptOfEntries z T₀ L cut es er ws)).horizon = horizonOf L := by
  simp only [answer, ckptOfEntries]
theorem answer_days : (answer (ckptOfEntries z T₀ L cut es er ws)).days
    = (daysFrom (foldedState z es er) (foldedHeaders z es er) L).map (OpenDay.finish (foldedState z es er).machine) := by
  simp only [answer, ckptOfEntries]
theorem answer_window :
    (answer (ckptOfEntries z T₀ L cut es er ws)).window = windowsFrom (foldedState z es er) (horizonOf L) := by
  simp only [answer, ckptOfEntries]
theorem answer_items : (answer (ckptOfEntries z T₀ L cut es er ws)).items
    = ((itemIds (foldedState z es er)).map (itemAggOf (foldedState z es er))).map ItemAgg.finish := by
  simp only [answer, ckptOfEntries]
theorem answer_instOther : (answer (ckptOfEntries z T₀ L cut es er ws)).instOther = instOtherOf (foldedState z es er) := by
  simp only [answer, ckptOfEntries]
theorem answer_named : (answer (ckptOfEntries z T₀ L cut es er ws)).named = namedOf (foldedState z es er) := by
  simp only [answer, ckptOfEntries]
theorem answer_openBlock : (answer (ckptOfEntries z T₀ L cut es er ws)).openBlock
    = Replay.openOf (foldedState z es er).machine := by
  simp only [answer, ckptOfEntries]
theorem answer_openInterrupt : (answer (ckptOfEntries z T₀ L cut es er ws)).openInterrupt
    = (foldedState z es er).machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩) := by
  simp only [answer, ckptOfEntries]
theorem answer_lastDay :
    (answer (ckptOfEntries z T₀ L cut es er ws)).lastDay = Replay.maxDay? ((foldedState z es er).days.pairs.map Prod.fst) := by
  simp only [answer, ckptOfEntries]
theorem answer_lastEffective :
    (answer (ckptOfEntries z T₀ L cut es er ws)).lastEffective = (foldedState z es er).global.lastEffective := by
  simp only [answer, ckptOfEntries]
theorem answer_entryCount : (answer (ckptOfEntries z T₀ L cut es er ws)).entryCount = es.length := by
  simp only [answer, ckptOfEntries]
theorem answer_unknown : (answer (ckptOfEntries z T₀ L cut es er ws)).unknown = (foldedState z es er).unknown := by
  simp only [answer, ckptOfEntries]
theorem answer_longestLeak :
    (answer (ckptOfEntries z T₀ L cut es er ws)).longestLeak = (foldedState z es er).longestLeak := by
  simp only [answer, ckptOfEntries]
theorem answer_rwarns : (answer (ckptOfEntries z T₀ L cut es er ws)).rwarns = (foldedState z es er).rwarns.reverse := by
  simp only [answer, ckptOfEntries]

end Proj

/-- **Law 1, the answer, over entries**: every query at or above the horizons reads the checkpoint of entries with
nothing unfolded as the finished fold. -/
theorem answer_reads_state (z : Cal.Tz) (T₀ L cut : Nat) (es : List Entry) (ws : List (Nat × Log.LWarn)) (q : Q)
    (hq : q.atOrAbove L (horizonOf L) = true) :
    askAnswer (answer (ckptOfEntries z T₀ L cut es [] ws)) q
      = some (Replay.ask ⟨Replay.finish (foldedState z es []), foldedHeaders z es [], es.length⟩ q) := by
  have hk := allKeyed_foldedState z es []
  have hitems := items_read_state (foldedState z es []) (foldedHeaders z es []) es.length hk
    (answer (ckptOfEntries z T₀ L cut es [] ws)) (answer_items z T₀ L cut es [] ws)
  have hoth := others_read_state (foldedState z es []) (foldedHeaders z es []) es.length hk
    (answer (ckptOfEntries z T₀ L cut es [] ws)) (answer_instOther z T₀ L cut es [] ws) (answer_named z T₀ L cut es [] ws)
  have hsc := scalars_read_state (foldedState z es []) (foldedHeaders z es []) es.length
    (answer (ckptOfEntries z T₀ L cut es [] ws))
    (answer_openBlock z T₀ L cut es [] ws) (answer_openInterrupt z T₀ L cut es [] ws) (answer_lastDay z T₀ L cut es [] ws)
    (answer_lastEffective z T₀ L cut es [] ws) (answer_unknown z T₀ L cut es [] ws) (answer_longestLeak z T₀ L cut es [] ws)
    (answer_rwarns z T₀ L cut es [] ws) (answer_entryCount z T₀ L cut es [] ws)
  cases q with
  | day d dq =>
    simp only [Q.atOrAbove, decide_eq_true_eq] at hq
    have hnd : ¬ d < L := by omega
    simp only [askAnswer, answer_ledgerDay, answer_days, hnd, ↓reduceIte]
    unfold daysFrom
    rw [findDay_days _ _ _ _ d (by simpa using hq), dayRead_state _ _ _ hk]
  | win d wq =>
    simp only [Q.atOrAbove, decide_eq_true_eq] at hq
    have hnd : ¬ d < horizonOf L := by omega
    simp only [askAnswer, answer_horizon, answer_window, hnd, ↓reduceIte]
    unfold windowsFrom
    rw [findWin_windows _ _ d (by simpa using hq), winRead_state _ _ _ hk]
  | item i => exact (hitems i).1
  | lastDone i => exact (hitems i).2.1
  | doneFirst i => exact (hitems i).2.2.1
  | doneCount i => exact (hitems i).2.2.2.1
  | dropped i => exact (hitems i).2.2.2.2
  | instOther item inst => exact (hoth item inst [] none).1
  | named name id => exact (hoth [] [] name id).2
  | openBlock => exact hsc.1
  | openInterrupt => exact hsc.2.1
  | lastDay => exact hsc.2.2.1
  | lastEffective => exact hsc.2.2.2.1
  | unknown => exact hsc.2.2.2.2.1
  | longestLeak => exact hsc.2.2.2.2.2.1
  | replayWarnings => exact hsc.2.2.2.2.2.2.1
  | entryCount => exact hsc.2.2.2.2.2.2.2

/-- **Law 1, the day records, over entries.** -/
theorem day_records_read_state (z : Cal.Tz) (L : Nat) (es : List Entry) (d : Nat) (q : DayQ) (hd : d < L) :
    askDayRecords (dayRecordsOfEntries z 0 L es) d q
      = Replay.ask ⟨Replay.finish (foldedState z es []), foldedHeaders z es [], es.length⟩ (.day d q) := by
  have hk := allKeyed_foldedState z es []
  unfold askDayRecords dayRecordsOfEntries daysIn
  rw [findDay_days _ _ _ _ d (by simp [hd]), dayRead_state _ _ _ hk]

/-- **Law 1, the window records, over entries.** -/
theorem window_records_read_state (z : Cal.Tz) (H : Nat) (es : List Entry) (d : Nat) (q : WinQ) (hd : d < H) :
    askWindowRecords (windowRecordsOfEntries z 0 H es) d q
      = Replay.ask ⟨Replay.finish (foldedState z es []), foldedHeaders z es [], es.length⟩ (.win d q) := by
  have hk := allKeyed_foldedState z es []
  unfold askWindowRecords windowRecordsOfEntries windowsIn
  rw [findWin_windows _ _ d (by simp [hd]), winRead_state _ _ _ hk]

/-! ### Law 1 over lines -/

theorem replayLines_eq (z : Cal.Tz) (ls : List Log.Line) :
    replayLines z ls = ⟨Replay.finish (foldedState z (Log.lineEntries ls) []),
      foldedHeaders z (Log.lineEntries ls) [], (Log.lineEntries ls).length⟩ := by
  unfold replayLines Replay.replayDoc
  rw [replay_eq_finish_foldedState, entryHeaders_eq_foldedHeaders]

theorem ckptOf_nil (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) :
    ckptOf z T₀ L ls [] = ckptOfEntries z T₀ L ls.length (Log.lineEntries ls) [] (Log.lineWarnings ls) := rfl

/-- **Law 1, the answer (A, O, W), for every log and every ledger day** (the companion of §15's goal, which also
carries `contiguousFrom` and `sealable`: neither is needed). -/
theorem answer_reads_the_replay (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (q : Q)
    (hq : q.atOrAbove L (horizonOf L) = true) :
    askAnswer (answer (ckptOf z T₀ L ls [])) q = some (Replay.ask (replayLines z ls) q) := by
  rw [ckptOf_nil, replayLines_eq]
  exact answer_reads_state z T₀ L ls.length (Log.lineEntries ls) (Log.lineWarnings ls) q hq

/-- **Law 1, the day records (DR)**, for every log and every ledger day. -/
theorem day_record_is_the_replays_day (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (d : Nat) (q : DayQ)
    (hd : d < L) :
    askDayRecords (dayRecordsBelow z T₀ L ls) d q = Replay.ask (replayLines z ls) (.day d q) := by
  rw [replayLines_eq]
  exact day_records_read_state z L (Log.lineEntries ls) d q hd

/-- **Law 1, the window records (WR)**, for every log and every ledger day. -/
theorem window_record_is_the_replays_window (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (d : Nat) (q : WinQ)
    (hd : d < horizonOf L) :
    askWindowRecords (windowRecordsBelow z T₀ L ls) d q = Replay.ask (replayLines z ls) (.win d q) := by
  rw [replayLines_eq]
  exact window_records_read_state z (horizonOf L) (Log.lineEntries ls) d q hd

/-- **Law 1, the partition**, for every log and every ledger day. -/
theorem partition_is_the_replay (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (q : Q) :
    askMerged (dayRecordsBelow z T₀ L ls) (windowRecordsBelow z T₀ L ls) (answer (ckptOf z T₀ L ls [])) q
      = Replay.ask (replayLines z ls) q := by
  unfold askMerged
  by_cases hq : q.atOrAbove L (horizonOf L) = true
  · rw [answer_reads_the_replay z T₀ L ls q hq]
  · cases q with
    | day d dq =>
      simp only [Q.atOrAbove, decide_eq_true_eq] at hq
      have : askAnswer (answer (ckptOf z T₀ L ls [])) (.day d dq) = none := by
        have hlt : d < L := by omega
        rw [ckptOf_nil]; simp only [askAnswer, answer_ledgerDay, hlt, ↓reduceIte]
      rw [this]
      exact day_record_is_the_replays_day z T₀ L ls d dq (by omega)
    | win d wq =>
      simp only [Q.atOrAbove, decide_eq_true_eq] at hq
      have : askAnswer (answer (ckptOf z T₀ L ls [])) (.win d wq) = none := by
        have hlt : d < horizonOf L := by omega
        rw [ckptOf_nil]; simp only [askAnswer, answer_horizon, hlt, ↓reduceIte]
      rw [this]
      exact window_record_is_the_replays_window z T₀ L ls d wq (by omega)
    | _ => simp [Q.atOrAbove] at hq

end Partition

/-! ## Law 11: the sealed and the live observations, by line, are the replay's

A day record and the answer hold each day's observations; together they are a permutation of the replay's, because
every observation's day is a day with a reading and each day is listed once.  Sorted by line they are one list: the
lines of a log's observations are distinct (each entry adds at most one observation, energy or duration, on its own
line), so a sort by line has no ties to break. -/

section Observations

open Replay (Effect)

/-- **A line's entry carries the line's number** (the reader stamps it). -/
theorem Line.entry_line (l : Log.Line) (e : Entry) (h : l.entry? = some e) : e.line = l.n := by
  unfold Log.Line.entry? Log.Line.verdict at h
  cases hv : Log.readLine l.n l.text with
  | entry e' =>
    simp only [hv, Option.some.injEq] at h
    subst h
    cases ht : l.text with
    | none => rw [ht] at hv; simp [Log.readLine] at hv
    | some t =>
      rw [ht] at hv
      obtain ⟨kvs, -, -, ho⟩ := Log.readLine_entry_inv l.n t e' hv
      unfold Log.readObject at ho
      repeat' split at ho
      all_goals first | (cases ho; done) | (cases ho; rfl)
  | _ => simp [hv] at h

/-- **Lines numbered from `k` read as entries with strictly increasing lines, each at least `k`.** -/
theorem lineEntries_pairwise : ∀ (k : Nat) (ls : List Log.Line), Log.contiguousFrom k ls = true →
    (Log.lineEntries ls).Pairwise (fun a b => a.line < b.line) ∧ ∀ e ∈ Log.lineEntries ls, k ≤ e.line
  | _, [], _ => ⟨List.Pairwise.nil, by simp [Log.lineEntries]⟩
  | k, l :: ls, h => by
    simp only [Log.contiguousFrom, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨ih1, ih2⟩ := lineEntries_pairwise (k + 1) ls h.2
    unfold Log.lineEntries at ih1 ih2 ⊢
    rw [List.filterMap_cons]
    cases he : l.entry? with
    | none => exact ⟨ih1, fun e hm => by have := ih2 e hm; omega⟩
    | some e =>
      have hel : e.line = k := by rw [Line.entry_line l e he, h.1]
      refine ⟨List.Pairwise.cons (fun b hb => by have := ih2 b hb; omega) ih1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := ih2 x hx; omega

/-- A machine arm other than `done`'s emits no duration observation. -/
theorem arm_durations_nil (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (h : ∀ id est actual went tags ci p, e.ev ≠ .done id est actual went tags ci p) :
    (Replay.arm dy sl m e t d).filterMap Effect.durationOf? = [] := by
  unfold Replay.arm
  cases hev : e.ev <;> simp only
  case done id est actual went tags ci isPartial => exact absurd hev (h _ _ _ _ _ _ _)
  case start => simp [List.filterMap_append, (Replay.cut_obs dy m t).2.1, Effect.durationOf?]
  case pause id =>
    split
    · split
      · simp [List.filterMap_append, (Replay.closeSub_obs dy m t).2.1, Effect.durationOf?]
      · rfl
    · rfl
  case unpause id =>
    split
    · split
      · simp [List.filterMap_append, (Replay.closePause_obs dy m t).2.1, Effect.durationOf?]
      · rfl
    · rfl
  case interrupt id =>
    simp [List.filterMap_append, (Replay.closeSub_obs dy m t).2.1, (Replay.closePause_obs dy _ t).2.1, Effect.durationOf?]
  case resume lost dropped => split <;> simp [Effect.durationOf?]
  case stop id rem =>
    split
    · split
      · simp [List.filterMap_append, (Replay.cut_obs dy m t).2.1, Effect.durationOf?]
      · rfl
    · rfl
  case extend id by_ => rfl
  case brk planned actual where_ =>
    rw [List.filterMap_append, (Replay.dayArm_obs dy sl e t d).2.1, List.append_nil]
    exact (Replay.brkFx_obs dy m t _ d).2
  all_goals exact (Replay.dayArm_obs dy sl e t d).2.1

/-- **Each machine arm adds at most one observation on its own line**, energy or duration, not both. -/
theorem arm_obs_one (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) :
    ∃ X : List Nat, List.Sublist (X ++ ((Replay.arm dy sl m e t d).filterMap Effect.durationOf?).map (·.line)) [e.line] ∧
      (((Replay.arm dy sl m e t d).filterMap Effect.energyOf?).map (·.line) ++
        Replay.pendLines (((Replay.arm dy sl m e t d).filterMap Effect.machineOf?).getLast?.getD m)).Perm
        (Replay.pendLines m ++ X) := by
  by_cases hd : ∃ id est actual went tags ci p, e.ev = .done id est actual went tags ci p
  · obtain ⟨id, est, actual, went, tags, ci, p, hev⟩ := hd
    obtain ⟨h1, h2⟩ := Replay.doneFx_obs dy m e.line t d id est.val actual.val went tags ci p
    have ha : Replay.arm dy sl m e t d = Replay.doneFx dy m e.line t d id est.val actual.val went tags ci p := by
      simp only [Replay.arm, hev]
    refine ⟨[], ?_, ?_⟩
    · rw [ha, List.nil_append]; exact h2
    · rw [ha, h1]; simp
  · obtain ⟨X, hX, hp, _⟩ := Replay.arm_obs dy sl m e t d
    refine ⟨X, ?_, hp⟩
    rw [arm_durations_nil dy sl m e t d (fun id est actual went tags ci p h => hd ⟨id, est, actual, went, tags, ci, p, h⟩)]
    simpa using hX

theorem stepWith_obs_one (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    ∃ W : List Nat, List.Sublist W [e.line] ∧
      (Replay.obsLines (Replay.stepWith z dy sl st e) ++ ((Replay.stepWith z dy sl st e).durations.map (·.line)).reverse).Perm
        ((Replay.obsLines st ++ (st.durations.map (·.line)).reverse) ++ W) := by
  obtain ⟨X, hX, hp⟩ := arm_obs_one dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)
  obtain ⟨c1, c2, c3⟩ := Replay.completionArm_obs z e (e.t.val, e.off.val) (dy e.t.val)
  obtain ⟨h1, h2, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  refine ⟨_, hX, ?_⟩
  have hE : (Replay.obsLines (Replay.stepWith z dy sl st e)).Perm (Replay.obsLines st ++ X) := by
    unfold Replay.obsLines Replay.stepWith
    rw [h1, h3]
    unfold Replay.effectsWith
    simp only [List.filterMap_cons, List.filterMap_append, Effect.energyOf?, Effect.machineOf?, c1, c3, List.append_nil]
    rw [List.map_append, List.map_reverse]
    have := (List.perm_append_comm (l₁ := (List.map (·.line) (List.filterMap Effect.energyOf?
      (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)))).reverse)
      (l₂ := st.energy.map (·.line))).append_right
      (Replay.pendLines ((List.filterMap Effect.machineOf? (Replay.arm dy sl st.machine e (e.t.val, e.off.val)
        (dy e.t.val))).getLast?.getD st.machine))
    refine this.trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ (((List.reverse_perm _).append_right _).trans hp)
  have hD : ((Replay.stepWith z dy sl st e).durations.map (·.line)).reverse = (st.durations.map (·.line)).reverse ++
      ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.durationOf?).map (·.line) := by
    unfold Replay.stepWith
    rw [h2]
    unfold Replay.effectsWith
    simp only [List.filterMap_cons, List.filterMap_append, Effect.durationOf?, c2, List.append_nil, List.map_append,
      List.map_reverse, List.reverse_append, List.reverse_reverse]
  rw [hD]
  refine (hE.append_right _).trans ?_
  simp only [List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

theorem foldl_stepWith_obs_one (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (l : List Entry) (st : State), ∃ Z : List Nat, List.Sublist Z (l.map (·.line)) ∧
      (Replay.obsLines (l.foldl (Replay.stepWith z dy sl) st) ++
        ((l.foldl (Replay.stepWith z dy sl) st).durations.map (·.line)).reverse).Perm
        ((Replay.obsLines st ++ (st.durations.map (·.line)).reverse) ++ Z)
  | [], st => ⟨[], List.nil_sublist _, by simp⟩
  | e :: l, st => by
    obtain ⟨W, hW, hp₁⟩ := stepWith_obs_one z dy sl st e
    obtain ⟨Z, hZ, hp₂⟩ := foldl_stepWith_obs_one z dy sl l (Replay.stepWith z dy sl st e)
    refine ⟨W ++ Z, ?_, ?_⟩
    · rw [List.map_cons]; exact (hW.append hZ).trans (by simp)
    · rw [List.foldl_cons]
      exact hp₂.trans (by rw [← List.append_assoc]; exact hp₁.append_right Z)

theorem foldedSurvivors_sublist (es er : List Entry) : List.Sublist (foldedSurvivors es er) es := by
  unfold foldedSurvivors
  have : es.zipIdx.map Prod.fst = es := by simp
  conv => rhs; rw [← this]
  exact List.Sublist.map _ List.filter_sublist

/-- **The folded state's observations sit on distinct lines**, emitted, pending and durations together. -/
theorem foldedState_obs_nodup (z : Cal.Tz) (es er : List Entry) (hp : es.Pairwise (fun a b => a.line < b.line)) :
    (Replay.obsLines (foldedState z es er) ++ ((foldedState z es er).durations.map (·.line)).reverse).Nodup := by
  have hfs : foldedState z es er = (foldedSurvivors es er).foldl (Replay.stepWith z (Replay.dayOf z (foldedIndex z es er))
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z es er) (foldedSurvivors es er)))) (State.init es.length) := rfl
  obtain ⟨Z, hZ, hperm⟩ := foldl_stepWith_obs_one z (Replay.dayOf z (foldedIndex z es er))
    (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z es er) (foldedSurvivors es er))) (foldedSurvivors es er)
    (State.init es.length)
  have hinit : Replay.obsLines (State.init es.length) ++ ((State.init es.length).durations.map (·.line)).reverse = [] :=
    rfl
  rw [hinit, List.nil_append] at hperm
  have hsv : ((foldedSurvivors es er).map (·.line)).Pairwise (· < ·) := by
    rw [List.pairwise_map]; exact hp.sublist (foldedSurvivors_sublist es er)
  rw [hfs]
  exact hperm.nodup_iff.2 (Replay.sublist_nodup_of_pairwise_lt hsv hZ)

theorem perm_flatMap_pointwise {α β : Type} (f g : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).Perm (g a)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append (perm_flatMap_pointwise f g l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem flatMap_append_perm {α β : Type} (f g : α → List β) :
    ∀ (l : List α), (l.flatMap (fun a => f a ++ g a)).Perm (l.flatMap f ++ l.flatMap g)
  | [] => List.Perm.refl _
  | a :: l => by
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine ((flatMap_append_perm f g l).append_left _).trans ?_
    exact List.perm_append_comm_assoc _ _ _

theorem flatMap_map_eq {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ (l : List α), (l.map f).flatMap g = l.flatMap (fun a => g (f a))
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.flatMap_cons, flatMap_map_eq f g l]

theorem map_flatMap_eq {α β γ : Type} (f : α → List β) (g : β → γ) :
    ∀ (l : List α), (l.flatMap f).map g = l.flatMap (fun a => (f a).map g)
  | [] => rfl
  | a :: l => by simp only [List.flatMap_cons, List.map_append, map_flatMap_eq f g l]

theorem sum_ite_mem (c k : Nat) : ∀ (ks : List Nat), ks.Nodup →
    (ks.map (fun j => if k = j then c else 0)).sum = if k ∈ ks then c else 0
  | [], _ => by simp
  | j :: ks, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, sum_ite_mem c k ks hnd.2]
    by_cases hkj : k = j
    · subst hkj; simp [hnd.1]
    · simp [hkj]

/-- **A list split by a key over a list of distinct keys holding every element's key is a permutation of it.** -/
theorem perm_flatMap_filter {β : Type} [DecidableEq β] (key : β → Nat) (ks : List Nat) (hks : ks.Nodup) (l : List β)
    (hl : ∀ x ∈ l, key x ∈ ks) : (ks.flatMap (fun k => l.filter (fun x => decide (key x = k)))).Perm l := by
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have hc : ∀ k, List.count a (l.filter (fun x => decide (key x = k))) = if key a = k then List.count a l else 0 := by
    intro k
    by_cases hk : key a = k
    · rw [if_pos hk, List.count_filter (by simp [hk])]
    · rw [if_neg hk, List.count_eq_zero_of_not_mem]
      intro hm; exact hk (by simpa using (List.mem_filter.1 hm).2)
  have : (ks.map (List.count a ∘ fun k => l.filter (fun x => decide (key x = k))))
      = ks.map (fun k => if key a = k then List.count a l else 0) := by
    apply List.map_congr_left; intro k _; exact hc k
  rw [this, sum_ite_mem _ _ ks hks]
  by_cases ha : a ∈ l
  · rw [if_pos (hl a ha)]
  · rw [List.count_eq_zero_of_not_mem ha]; split <;> rfl

theorem eq_of_perm_of_pairwise_lt {α : Type} (key : α → Nat) : ∀ (l₁ l₂ : List α), l₁.Perm l₂ →
    l₁.Pairwise (fun a b => key a < key b) → l₂.Pairwise (fun a b => key a < key b) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, hp, _, _ => absurd hp.length_eq (by simp)
  | _ :: _, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: l₁, b :: l₂, hp, h₁, h₂ => by
    have hab : a = b := by
      refine Classical.byContradiction (fun hne => ?_)
      have ha : a ∈ l₂ := by
        rcases List.mem_cons.1 (hp.mem_iff.1 List.mem_cons_self) with h | h
        · exact absurd h hne
        · exact h
      have hb : b ∈ l₁ := by
        rcases List.mem_cons.1 (hp.mem_iff.2 List.mem_cons_self) with h | h
        · exact absurd h.symm hne
        · exact h
      have := List.rel_of_pairwise_cons h₁ hb
      have := List.rel_of_pairwise_cons h₂ ha
      omega
    subst hab
    rw [eq_of_perm_of_pairwise_lt key l₁ l₂ ((List.perm_cons _).1 hp) h₁.of_cons h₂.of_cons]

theorem sortByLine_sorted (l : List Obs) : (Replay.sortByLine l).Pairwise (fun a b => a.line ≤ b.line) := by
  have := insSort_sorted Replay.obsLineLe (fun a b c h₁ h₂ => by simp [Replay.obsLineLe] at *; omega)
    (fun a b => by simp only [Replay.obsLineLe, decide_eq_true_eq]; omega) l
  exact this.imp (fun h => by simpa [Replay.obsLineLe] using h)

/-- **Two lists sorted by line, one a permutation of the other, on distinct lines, are one list.** -/
theorem sortByLine_eq_of_perm (l₁ l₂ : List Obs) (hp : l₁.Perm l₂) (hn : (l₁.map Obs.line).Nodup) :
    Replay.sortByLine l₁ = Replay.sortByLine l₂ := by
  have hp' : (Replay.sortByLine l₁).Perm (Replay.sortByLine l₂) :=
    (Replay.insSort_perm _ _).trans (hp.trans (Replay.insSort_perm _ _).symm)
  have hn₁ : ((Replay.sortByLine l₁).map Obs.line).Nodup := (((Replay.insSort_perm _ _).map _).nodup_iff).2 hn
  have hn₂ : ((Replay.sortByLine l₂).map Obs.line).Nodup := ((hp'.map _).nodup_iff).1 hn₁
  have strict : ∀ l : List Obs, l.Pairwise (fun a b => a.line ≤ b.line) → (l.map Obs.line).Nodup →
      l.Pairwise (fun a b => a.line < b.line) := fun l hs hnd =>
    (hs.and (List.pairwise_map.1 (show (l.map Obs.line).Pairwise (· ≠ ·) from hnd))).imp
      (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  exact eq_of_perm_of_pairwise_lt Obs.line _ _ hp' (strict _ (sortByLine_sorted _) hn₁) (strict _ (sortByLine_sorted _) hn₂)

theorem mem_dayKeys_energy {st : State} {hs : List (Nat × HeaderRec)} {o : EnergyObs} (h : o ∈ st.energy) :
    o.day ∈ dayKeys st hs := by
  unfold dayKeys; rw [mem_canon natLt_strictTotal]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨o, h, rfl⟩)))))))

theorem mem_dayKeys_durations {st : State} {hs : List (Nat × HeaderRec)} {o : DurationObs} (h : o ∈ st.durations) :
    o.day ∈ dayKeys st hs := by
  unfold dayKeys; rw [mem_canon natLt_strictTotal]
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨o, h, rfl⟩))))))

theorem mem_dayKeys_pending {st : State} {hs : List (Nat × HeaderRec)} {o : EnergyObs}
    (h : st.machine.block.bind (·.obs) = some o) : o.day ∈ dayKeys st hs := by
  unfold dayKeys; rw [mem_canon natLt_strictTotal]
  simp only [List.mem_append]
  exact Or.inr (by rw [h]; simp)

/-- **The days of a state, grouped below and at or above `L`, hold its observations, up to order.** -/
theorem obs_perm_state (st : State) (hs : List (Nat × HeaderRec)) (L : Nat) :
    (((((dayKeys st hs).filter (fun d => decide (0 ≤ d ∧ d < L))).map (openDayOf st hs)).map
        (OpenDay.finish st.machine)).flatMap DayRecord.obs
      ++ ((((dayKeys st hs).filter (fun d => decide (L ≤ d))).map (openDayOf st hs)).map
        (OpenDay.finish st.machine)).flatMap DayRecord.obs).Perm
      ((st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList).map Obs.energy ++
        st.durations.reverse.map Obs.duration) := by
  have hks : (dayKeys st hs).Nodup := nodup_canon natLt_strictTotal _
  have hsplit : ((dayKeys st hs).filter (fun d => decide (0 ≤ d ∧ d < L)) ++
      (dayKeys st hs).filter (fun d => decide (L ≤ d))).Perm (dayKeys st hs) := by
    have e : (dayKeys st hs).filter (fun d => decide (L ≤ d))
        = (dayKeys st hs).filter (fun d => !decide (0 ≤ d ∧ d < L)) := by
      apply List.filter_congr; intro d _; by_cases h : L ≤ d <;> simp [h] <;> omega
    rw [e]; exact List.filter_append_perm _ _
  rw [List.map_map, List.map_map, flatMap_map_eq, flatMap_map_eq, ← List.flatMap_append]
  refine (List.Perm.flatMap_right _ hsplit).trans ?_
  have hg : ∀ d, DayRecord.obs ((OpenDay.finish st.machine ∘ openDayOf st hs) d)
      = (Replay.sortObs ((st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList).filter
          (fun o => decide (o.day = d)))).map Obs.energy
        ++ (st.durations.reverse.filter (fun o => decide (o.day = d))).map Obs.duration := by
    intro d
    simp only [Function.comp_apply, DayRecord.obs, OpenDay.finish, openDayOf]
    rw [List.filter_append, List.filter_reverse, List.filter_reverse, ← pendingOn_eq]
  simp only [hg]
  refine (flatMap_append_perm _ _ _).trans (List.Perm.append ?_ ?_)
  · refine (perm_flatMap_pointwise _ (fun d => ((st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList).filter
        (fun o => decide (o.day = d))).map Obs.energy) _
      (fun d _ => (Replay.insSort_perm _ _).map _)).trans ?_
    rw [← map_flatMap_eq]
    refine List.Perm.map _ (perm_flatMap_filter _ _ hks _ (fun o ho => ?_))
    rcases List.mem_append.1 ho with ho | ho
    · exact mem_dayKeys_energy (List.mem_reverse.1 ho)
    · cases hb : st.machine.block.bind (·.obs) with
      | none => rw [hb] at ho; cases ho
      | some o' =>
        rw [hb] at ho
        simp only [Option.toList_some, List.mem_singleton] at ho
        subst ho
        exact mem_dayKeys_pending hb
  · rw [← map_flatMap_eq]
    exact List.Perm.map _ (perm_flatMap_filter _ _ hks _ (fun o ho => mem_dayKeys_durations (List.mem_reverse.1 ho)))

/-- **Law 11, over entries**: the observations of the day records below `L` and of the answer, by line, are the
replay's, on entries whose lines strictly increase. -/
theorem observations_read_state (z : Cal.Tz) (T₀ L cut : Nat) (es : List Entry) (ws : List (Nat × Log.LWarn))
    (hp : es.Pairwise (fun a b => a.line < b.line)) :
    Replay.sortByLine ((dayRecordsOfEntries z 0 L es).flatMap DayRecord.obs ++ (answer (ckptOfEntries z T₀ L cut es [] ws)).obs)
      = Replay.Doc.obs ⟨Replay.finish (foldedState z es []), foldedHeaders z es [], es.length⟩ := by
  have hn := foldedState_obs_nodup z es [] hp
  unfold Answer.obs Replay.Doc.obs
  rw [answer_days]
  unfold dayRecordsOfEntries daysIn daysFrom
  generalize foldedState z es [] = st at hn ⊢
  generalize foldedHeaders z es [] = hs
  have hperm := obs_perm_state st hs L
  have hR : ((Replay.finish st).energy.map Obs.energy ++ (Replay.finish st).durations.map Obs.duration).Perm
      ((st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList).map Obs.energy ++
        st.durations.reverse.map Obs.duration) :=
    List.Perm.append_right _ ((Replay.insSort_perm _ _).map _)
  rw [sortByLine_eq_of_perm _ _ (hperm.trans hR.symm) ?_]
  refine ((hperm.trans hR.symm).map _).nodup_iff.2 ?_
  have hP : ((Replay.sortObs (st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList)).map (·.line)
      ++ st.durations.reverse.map (·.line)).Perm (Replay.obsLines st ++ (st.durations.map (·.line)).reverse) := by
    refine List.Perm.append ?_ (by rw [List.map_reverse])
    refine ((Replay.insSort_perm _ _).map _).trans ?_
    unfold Replay.obsLines Replay.pendLines
    rw [List.map_append, List.map_reverse]
    refine List.Perm.append (List.reverse_perm _) ?_
    cases st.machine.block.bind (·.obs) <;> simp
  have e1 : ((Replay.finish st).energy.map Obs.energy ++ (Replay.finish st).durations.map Obs.duration).map Obs.line
      = (Replay.sortObs (st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList)).map (·.line)
        ++ st.durations.reverse.map (·.line) := by
    simp only [List.map_append, List.map_map]; rfl
  rw [e1]
  exact hP.nodup_iff.2 hn

/-- **Law 11, over lines**: on lines numbered from 1. -/
theorem observations_read_lines (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (hc : Log.contiguousFrom 1 ls = true) :
    Replay.sortByLine ((dayRecordsBelow z T₀ L ls).flatMap (·.obs) ++ (answer (ckptOf z T₀ L ls [])).obs)
      = (replayLines z ls).obs := by
  rw [ckptOf_nil, replayLines_eq]
  exact observations_read_state z T₀ L ls.length (Log.lineEntries ls) (Log.lineWarnings ls) (lineEntries_pairwise 1 ls hc).1

end Observations

/-! ## §15's W block, laws 1 and 11, under their names (discharged in W2)

Each is §15's statement, hypotheses included; the companions above show that law 1 needs neither `contiguousFrom` nor
`sealable`, and that law 11 needs `contiguousFrom` (a repeated line breaks it) but not `sealable`. -/

/-- **Law 1, the answer (A, O, W)** (§15). -/
theorem the_answer_reads_the_replay (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (q : Seal.Q)
    (_hc : Log.contiguousFrom 1 ls = true) (_hs : Seal.sealable z T₀ L ls [] = true)
    (hq : q.atOrAbove L (Seal.horizonOf L) = true) :
    Seal.askAnswer (Seal.answer (Seal.ckptOf z T₀ L ls [])) q = some (Replay.ask (Seal.replayLines z ls) q) :=
  answer_reads_the_replay z T₀ L ls q hq

/-- **Law 1, the day records (DR)** (§15). -/
theorem a_day_record_is_the_replays_day (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (d : Nat) (q : Seal.DayQ)
    (_hc : Log.contiguousFrom 1 ls = true) (_hs : Seal.sealable z T₀ L ls [] = true) (hd : d < L) :
    Seal.askDayRecords (Seal.dayRecordsBelow z T₀ L ls) d q = Replay.ask (Seal.replayLines z ls) (.day d q) :=
  day_record_is_the_replays_day z T₀ L ls d q hd

/-- **Law 1, the window records (WR)** (§15). -/
theorem a_window_record_is_the_replays_window (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (d : Nat) (q : Seal.WinQ)
    (_hc : Log.contiguousFrom 1 ls = true) (_hs : Seal.sealable z T₀ L ls [] = true) (hd : d < Seal.horizonOf L) :
    Seal.askWindowRecords (Seal.windowRecordsBelow z T₀ L ls) d q = Replay.ask (Seal.replayLines z ls) (.win d q) :=
  window_record_is_the_replays_window z T₀ L ls d q hd

/-- **Law 1, the partition** (§15). -/
theorem seal_partition_is_the_replay (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line) (q : Seal.Q)
    (_hc : Log.contiguousFrom 1 ls = true) (_hs : Seal.sealable z T₀ L ls [] = true) :
    Seal.askMerged (Seal.dayRecordsBelow z T₀ L ls) (Seal.windowRecordsBelow z T₀ L ls)
      (Seal.answer (Seal.ckptOf z T₀ L ls [])) q = Replay.ask (Seal.replayLines z ls) q :=
  partition_is_the_replay z T₀ L ls q

/-- **Law 11, the observations** (§15). -/
theorem sealed_and_live_observations_are_the_replays (z : Cal.Tz) (T₀ L : Nat) (ls : List Log.Line)
    (hc : Log.contiguousFrom 1 ls = true) (_hs : Seal.sealable z T₀ L ls [] = true) :
    Replay.sortByLine ((Seal.dayRecordsBelow z T₀ L ls).flatMap (·.obs)
                       ++ (Seal.answer (Seal.ckptOf z T₀ L ls [])).obs)
      = (Seal.replayLines z ls).obs :=
  observations_read_lines z T₀ L ls hc

end Seal
end Tm
