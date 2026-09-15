import TmKernel.SealResume
/-!
# SealAgg — the all-time aggregates across a resume (stage 5, D9, W2)

The first done date and the count of done dates of an item, and the last day: each reads the checkpoint's facts below
the horizon and the resumed state's at or above it, and together they are the whole log's.  Specification only.
-/
namespace Tm
namespace Seal

theorem minDay?_nil : Replay.minDay? [] = none := rfl

theorem minDay?_cons (d : Nat) (l : List Nat) : Replay.minDay? (d :: l) = minOpt (some d) (Replay.minDay? l) := by
  unfold Replay.minDay?
  simp only [List.foldl_cons]
  induction l generalizing d with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, ih x]
    cases List.foldl (fun acc d => some (match acc with | none => d | some a => Nat.min a d)) none xs <;>
      simp [minOpt, Nat.min_assoc]

theorem minOpt_assoc (a b c : Option Nat) : minOpt (minOpt a b) c = minOpt a (minOpt b c) := by
  cases a <;> cases b <;> cases c <;> simp [minOpt, Nat.min_assoc]

theorem minDay?_append (l₁ l₂ : List Nat) : Replay.minDay? (l₁ ++ l₂) = minOpt (Replay.minDay? l₁) (Replay.minDay? l₂) := by
  induction l₁ with
  | nil => rw [List.nil_append, minDay?_nil]; cases Replay.minDay? l₂ <;> rfl
  | cons d l ih => rw [List.cons_append, minDay?_cons, minDay?_cons, ih, minOpt_assoc]

theorem minDay?_spec : ∀ (l : List Nat) (m : Nat), Replay.minDay? l = some m ↔ m ∈ l ∧ ∀ d ∈ l, m ≤ d
  | [], m => by simp [minDay?_nil]
  | d :: l, m => by
    rw [minDay?_cons]
    cases hl : Replay.minDay? l with
    | none =>
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons a as =>
          exfalso
          rw [minDay?_cons] at hl
          cases hh : Replay.minDay? as <;> simp [minOpt, hh] at hl
      subst hnil
      simp only [minOpt, Option.some.injEq, List.mem_singleton, forall_eq]
      constructor
      · rintro rfl; exact ⟨rfl, Nat.le_refl _⟩
      · rintro ⟨rfl, -⟩; rfl
    | some k =>
      obtain ⟨hk1, hk2⟩ := (minDay?_spec l k).1 hl
      simp only [minOpt, Option.some.injEq, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro rfl
        refine ⟨?_, Nat.min_le_left _ _, fun a ha => Nat.le_trans (Nat.min_le_right _ _) (hk2 a ha)⟩
        rcases Nat.le_total d k with h | h
        · left; show (if d ≤ k then d else k) = d; rw [if_pos h]
        · right
          have e : Nat.min d k = k := by show (if d ≤ k then d else k) = k; split <;> omega
          rw [e]; exact hk1
      · rintro ⟨hm | hm, hmd, hml⟩
        · subst hm; show (if m ≤ k then m else k) = m; rw [if_pos (hml k hk1)]
        · have h1 : m ≤ k := hml k hk1
          have h2 : k ≤ m := hk2 m hm
          have : m = k := Nat.le_antisymm h1 h2
          subst this
          show (if d ≤ m then d else m) = m; split <;> omega

theorem minDay?_none_iff (l : List Nat) : Replay.minDay? l = none ↔ l = [] := by
  cases l with
  | nil => simp [minDay?_nil]
  | cons d l => rw [minDay?_cons]; cases Replay.minDay? l <;> simp [minOpt]

theorem minDay?_eq_of_mem_iff (l₁ l₂ : List Nat) (h : ∀ d, d ∈ l₁ ↔ d ∈ l₂) : Replay.minDay? l₁ = Replay.minDay? l₂ := by
  cases h1 : Replay.minDay? l₁ with
  | none =>
    rw [minDay?_none_iff] at h1
    subst h1
    have : l₂ = [] := List.eq_nil_iff_forall_not_mem.2 (fun d hd => by simpa using (h d).2 hd)
    rw [this]; rfl
  | some m =>
    obtain ⟨hm1, hm2⟩ := (minDay?_spec l₁ m).1 h1
    exact ((minDay?_spec l₂ m).2 ⟨(h m).1 hm1, fun d hd => hm2 d ((h d).2 hd)⟩).symm

theorem maxDay?_cons (d : Nat) (l : List Nat) : Replay.maxDay? (d :: l) = maxOpt (some d) (Replay.maxDay? l) := by
  unfold Replay.maxDay?
  simp only [List.foldl_cons]
  induction l generalizing d with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, ih x]
    cases List.foldl (fun acc d => some (match acc with | none => d | some a => Nat.max a d)) none xs <;>
      simp [maxOpt, Nat.max_assoc]

theorem maxOpt_assoc (a b c : Option Nat) : maxOpt (maxOpt a b) c = maxOpt a (maxOpt b c) := by
  cases a <;> cases b <;> cases c <;> simp [maxOpt, Nat.max_assoc]

theorem maxDay?_append (l₁ l₂ : List Nat) : Replay.maxDay? (l₁ ++ l₂) = maxOpt (Replay.maxDay? l₁) (Replay.maxDay? l₂) := by
  induction l₁ with
  | nil => rw [List.nil_append]; show Replay.maxDay? l₂ = maxOpt none (Replay.maxDay? l₂); cases Replay.maxDay? l₂ <;> rfl
  | cons d l ih => rw [List.cons_append, maxDay?_cons, maxDay?_cons, ih, maxOpt_assoc]

theorem maxDay?_spec : ∀ (l : List Nat) (m : Nat), Replay.maxDay? l = some m ↔ m ∈ l ∧ ∀ d ∈ l, d ≤ m
  | [], m => by simp [Replay.maxDay?]
  | d :: l, m => by
    rw [maxDay?_cons]
    cases hl : Replay.maxDay? l with
    | none =>
      have hnil : l = [] := by
        cases l with
        | nil => rfl
        | cons a as =>
          exfalso
          rw [maxDay?_cons] at hl
          cases hh : Replay.maxDay? as <;> simp [maxOpt, hh] at hl
      subst hnil
      simp only [maxOpt, Option.some.injEq, List.mem_singleton, forall_eq]
      constructor
      · rintro rfl; exact ⟨rfl, Nat.le_refl _⟩
      · rintro ⟨rfl, -⟩; rfl
    | some k =>
      obtain ⟨hk1, hk2⟩ := (maxDay?_spec l k).1 hl
      simp only [maxOpt, Option.some.injEq, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro rfl
        refine ⟨?_, Nat.le_max_left _ _, fun a ha => Nat.le_trans (hk2 a ha) (Nat.le_max_right _ _)⟩
        rcases Nat.le_total d k with h | h
        · right
          have e : Nat.max d k = k := by show (if d ≤ k then k else d) = k; split <;> omega
          rw [e]; exact hk1
        · left; show (if d ≤ k then k else d) = d; split <;> omega
      · rintro ⟨hm | hm, hmd, hml⟩
        · subst hm; have := hml k hk1; show (if m ≤ k then k else m) = m; split <;> omega
        · have h1 : k ≤ m := hml k hk1
          have h2 : m ≤ k := hk2 m hm
          have : m = k := Nat.le_antisymm h2 h1
          subst this
          show (if d ≤ m then m else d) = m; split <;> omega

theorem maxDay?_none_iff (l : List Nat) : Replay.maxDay? l = none ↔ l = [] := by
  cases l with
  | nil => simp [Replay.maxDay?]
  | cons d l => rw [maxDay?_cons]; cases Replay.maxDay? l <;> simp [maxOpt]

theorem maxDay?_eq_of_mem_iff (l₁ l₂ : List Nat) (h : ∀ d, d ∈ l₁ ↔ d ∈ l₂) : Replay.maxDay? l₁ = Replay.maxDay? l₂ := by
  cases h1 : Replay.maxDay? l₁ with
  | none =>
    rw [maxDay?_none_iff] at h1
    subst h1
    have : l₂ = [] := List.eq_nil_iff_forall_not_mem.2 (fun d hd => by simpa using (h d).2 hd)
    rw [this]; rfl
  | some m =>
    obtain ⟨hm1, hm2⟩ := (maxDay?_spec l₁ m).1 h1
    exact ((maxDay?_spec l₂ m).2 ⟨(h m).1 hm1, fun d hd => hm2 d ((h d).2 hd)⟩).symm

end Seal
end Tm
