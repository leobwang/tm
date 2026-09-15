import TmKernel.SealResume
/-!
# SealStep — a step reads the index only where it queries it (stage 5, D9, W2)

`stepQueries m e` is every instant a step reads the day index at.  Two index functions that agree there give one step
(`effectsWith_congr`), and a fold's queries are its entries' own instants and the instants its start state's block holds
(`foldQueries_sub`).  Specification only (D9-21): nothing here is on the wire.
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect Block)
open Log (Entry)

section Congr

variable (dy₁ dy₂ : Cal.Instant → Nat)

theorem closeSub_congr (m : Machine) (t : Replay.At) (h : ∀ q ∈ blockSince m, dy₁ q = dy₂ q) :
    Replay.closeSub dy₁ m t = Replay.closeSub dy₂ m t := by
  unfold Replay.closeSub
  cases hb : m.block with
  | none => rfl
  | some b =>
    cases hs : b.since with
    | none => simp [hs]
    | some s =>
      have : dy₁ s.1 = dy₂ s.1 := h s.1 (by simp [blockSince, hb, hs])
      simp [hs, this]

theorem closePause_congr (m : Machine) (t : Replay.At) (h : ∀ q ∈ blockPaused m, dy₁ q = dy₂ q) :
    Replay.closePause dy₁ m t = Replay.closePause dy₂ m t := by
  unfold Replay.closePause
  cases hb : m.block with
  | none => rfl
  | some b =>
    cases hs : b.pausedAt with
    | none => simp [hs]
    | some s =>
      have : dy₁ s.1 = dy₂ s.1 := h s.1 (by simp [blockPaused, hb, hs])
      simp [hs, this]

theorem closeSub_blockPaused (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    blockPaused (Replay.closeSub dy m t).1 = blockPaused m := by
  unfold Replay.closeSub blockPaused
  cases hb : m.block with
  | none => simp [hb]
  | some b => cases hs : b.since <;> simp [hb, hs]

theorem cut_congr (m : Machine) (t : Replay.At)
    (h : ∀ q ∈ blockSince m ++ blockPaused m ++ [t.1], dy₁ q = dy₂ q) : Replay.cut dy₁ m t = Replay.cut dy₂ m t := by
  have h1 := closeSub_congr dy₁ dy₂ m t (fun q hq => h q (by simp [hq]))
  have h2 := closePause_congr dy₁ dy₂ (Replay.closeSub dy₁ m t).1 t
    (fun q hq => h q (by rw [closeSub_blockPaused] at hq; simp [hq]))
  have ht : dy₁ t.1 = dy₂ t.1 := h t.1 (by simp)
  have h2' : Replay.closePause dy₁ (Replay.closeSub dy₂ m t).1 t = Replay.closePause dy₂ (Replay.closeSub dy₂ m t).1 t := by
    rw [← h1]; exact h2
  unfold Replay.cut Replay.creditFx
  simp only [h1, h2', ht]

theorem doneClose_congr (m : Machine) (t : Replay.At) (id : Log.Id) (actual : Nat) (went : Option Log.U8)
    (h : ∀ b, m.block = some b → b.id = id → ∀ q ∈ blockSince m ++ blockPaused m, dy₁ q = dy₂ q) :
    Replay.doneClose dy₁ m t id actual went = Replay.doneClose dy₂ m t id actual went := by
  unfold Replay.doneClose
  cases hb : m.block with
  | none => rfl
  | some b =>
    simp only
    split
    · rename_i hid
      have h1 := closeSub_congr dy₁ dy₂ m t (fun q hq => h b hb hid q (by simp [hq]))
      have h2 := closePause_congr dy₁ dy₂ (Replay.closeSub dy₁ m t).1 t
        (fun q hq => h b hb hid q (by rw [closeSub_blockPaused] at hq; simp [hq]))
      have h2' : Replay.closePause dy₁ (Replay.closeSub dy₂ m t).1 t = Replay.closePause dy₂ (Replay.closeSub dy₂ m t).1 t := by
        rw [← h1]; exact h2
      simp only [h1, h2']
    · rfl

/-- **An arm reads the index only at the step's queries.** -/
theorem arm_congr (sl : Nat → Option Nat) (m : Machine) (e : Entry)
    (h : ∀ q ∈ stepQueries m e, dy₁ q = dy₂ q) :
    Replay.arm dy₁ sl m e (e.t.val, e.off.val) (dy₁ e.t.val) = Replay.arm dy₂ sl m e (e.t.val, e.off.val) (dy₂ e.t.val) := by
  have ht : dy₁ e.t.val = dy₂ e.t.val := h _ (by simp [stepQueries, entryInstants])
  rw [ht]
  unfold stepQueries at h
  unfold Replay.arm
  cases hev : e.ev <;> simp only [hev] at h ⊢
  case start =>
    rw [cut_congr dy₁ dy₂ m (e.t.val, e.off.val) (fun q hq => h q (by
      simp only [List.mem_append, List.mem_singleton] at hq ⊢
      rcases hq with (hq | hq) | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr hq)
      · exact Or.inl (by simp [entryInstants, hq])))]
  case pause id =>
    split
    · split
      · rename_i b hb hc
        simp only [hb, hc, and_self, if_true] at h
        rw [closeSub_congr dy₁ dy₂ m _ (fun q hq => h q (by simp [hq]))]
      · rfl
    · rfl
  case unpause id =>
    split
    · split
      · rename_i b hb hc
        simp only [hb, hc, and_self, if_true] at h
        rw [closePause_congr dy₁ dy₂ m _ (fun q hq => h q (by simp [hq]))]
      · rfl
    · rfl
  case interrupt id =>
    have h1 := closeSub_congr dy₁ dy₂ m (e.t.val, e.off.val) (fun q hq => h q (by simp [hq]))
    have h2 := closePause_congr dy₁ dy₂ (Replay.closeSub dy₁ m (e.t.val, e.off.val)).1 (e.t.val, e.off.val)
      (fun q hq => h q (by rw [closeSub_blockPaused] at hq; simp [hq]))
    have h2' : Replay.closePause dy₁ (Replay.closeSub dy₂ m (e.t.val, e.off.val)).1 (e.t.val, e.off.val)
        = Replay.closePause dy₂ (Replay.closeSub dy₂ m (e.t.val, e.off.val)).1 (e.t.val, e.off.val) := by
      rw [← h1]; exact h2
    simp only [h1, h2']
  case stop id rem =>
    split
    · split
      · rename_i b hb hc
        simp only [hb, hc, if_true] at h
        rw [cut_congr dy₁ dy₂ m (e.t.val, e.off.val) (fun q hq => h q (by
          simp only [List.mem_append, List.mem_singleton] at hq ⊢
          rcases hq with (hq | hq) | hq
          · exact Or.inr (Or.inl hq)
          · exact Or.inr (Or.inr hq)
          · exact Or.inl (by simp [entryInstants, hq])))]
      · rfl
    · rfl
  case done id est actual went tags ci isPartial =>
    unfold Replay.doneFx Replay.creditFx
    rw [doneClose_congr dy₁ dy₂ m (e.t.val, e.off.val) id actual.val went (fun b hb hid q hq => h q (by
      simp only [hb, hid, if_true]; exact List.mem_append_right _ hq)), ht]
  case idle attributed min =>
    unfold Replay.dayArm
    simp only [hev]
    have : dy₁ (Cal.subMinutes e.t.val min.val) = dy₂ (Cal.subMinutes e.t.val min.val) :=
      h _ (by simp [entryInstants, gapStart?, hev])
    rw [this]
  case routine item inst status actual =>
    unfold Replay.dayArm
    simp only [hev]
    cases hst : Log.parseInstanceStatus status with
    | none => rfl
    | some st =>
      cases st <;> cases hact : actual <;> try rfl
      rename_i mm
      have : dy₁ (Cal.subMinutes e.t.val mm.val) = dy₂ (Cal.subMinutes e.t.val mm.val) :=
        h _ (by simp [entryInstants, gapStart?, hev, hst, hact])
      simp [this]
  all_goals first | rfl | (unfold Replay.dayArm; simp only [hev])

/-- **A step reads the index only at its queries.** -/
theorem effectsWith_congr (z : Cal.Tz) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : ∀ q ∈ stepQueries st.machine e, dy₁ q = dy₂ q) :
    Replay.effectsWith z dy₁ sl st e = Replay.effectsWith z dy₂ sl st e := by
  have ht : dy₁ e.t.val = dy₂ e.t.val := h _ (by simp [stepQueries, entryInstants])
  unfold Replay.effectsWith
  rw [arm_congr dy₁ dy₂ sl st.machine e h, ht]

end Congr

/-! ## A fold's queries -/

/-- **Every instant a fold reads the day index at**, step by step. -/
def foldQueries (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) : State → List Entry → List Cal.Instant
  | _, [] => []
  | st, e :: sv => stepQueries st.machine e ++ foldQueries z dy sl (Replay.stepWith z dy sl st e) sv

/-- **Two index functions agreeing at a fold's queries give one fold.** -/
theorem foldl_stepWith_congr (z : Cal.Tz) (dy₁ dy₂ : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State), (∀ q ∈ foldQueries z dy₁ sl st sv, dy₁ q = dy₂ q) →
      sv.foldl (Replay.stepWith z dy₁ sl) st = sv.foldl (Replay.stepWith z dy₂ sl) st
  | [], _, _ => rfl
  | e :: sv, st, h => by
    have h1 : ∀ q ∈ stepQueries st.machine e, dy₁ q = dy₂ q := fun q hq => h q (List.mem_append_left _ hq)
    have hs : Replay.stepWith z dy₁ sl st e = Replay.stepWith z dy₂ sl st e := by
      unfold Replay.stepWith; rw [effectsWith_congr dy₁ dy₂ z sl st e h1]
    rw [List.foldl_cons, List.foldl_cons, ← hs]
    exact foldl_stepWith_congr z dy₁ dy₂ sl sv _ (fun q hq => h q (List.mem_append_right _ hq))

/-- The instants an open block holds: its sub-segment start and its pause start. -/
def machineInstants (m : Machine) : List Cal.Instant := blockSince m ++ blockPaused m

theorem stepQueries_sub (m : Machine) (e : Entry) (q : Cal.Instant) (hq : q ∈ stepQueries m e) :
    q ∈ entryInstants e ∨ q ∈ machineInstants m := by
  unfold stepQueries at hq
  rcases List.mem_append.1 hq with hq | hq
  · exact Or.inl hq
  · right
    unfold machineInstants
    cases hev : e.ev <;> simp only [hev] at hq
    all_goals first
      | (simp at hq; done)
      | exact hq
      | (split at hq <;> (try split at hq) <;> simp_all)

theorem closeSub_mi (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.closeSub dy m t).1) : q ∈ machineInstants m := by
  unfold Replay.closeSub at hq
  cases hb : m.block with
  | none => simp_all [machineInstants, blockSince, blockPaused]
  | some b => cases hs : b.since <;> simp_all [machineInstants, blockSince, blockPaused]

theorem closePause_mi (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.closePause dy m t).1) : q ∈ machineInstants m := by
  unfold Replay.closePause at hq
  cases hb : m.block with
  | none => simp_all [machineInstants, blockSince, blockPaused]
  | some b => cases hs : b.pausedAt <;> simp_all [machineInstants, blockSince, blockPaused]

theorem cut_mi (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.cut dy m t).1) : q ∈ machineInstants m := by
  unfold Replay.cut at hq
  simp only at hq
  split at hq
  · simp [machineInstants, blockSince, blockPaused] at hq
  · exact closeSub_mi dy m t q (closePause_mi dy _ t q hq)

theorem doneFx_machines (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id)
    (est actual : Nat) (went : Option Log.U8) (tags : List (List Char)) (ci : Log.U8) (isPartial : Bool) :
    (Replay.doneFx dy m line t d id est actual went tags ci isPartial).filterMap Effect.machineOf?
      = [(Replay.doneClose dy m t id actual went).1] := by
  unfold Replay.doneFx
  simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_append,
    (Replay.doneClose_obs dy m t id actual went).2.2, List.nil_append]
  by_cases ha : 0 < actual <;> by_cases hp : isPartial = true <;> simp [ha, hp, Replay.creditFx, Effect.machineOf?]

theorem resumeBlock_since (b : Block) (t : Replay.At) :
    (Replay.resumeBlock b t).since = b.since ∨ (Replay.resumeBlock b t).since = some t := by
  unfold Replay.resumeBlock
  split
  · left; rfl
  · cases hs : b.since <;> simp [hs]

theorem resumeBlock_pausedAt (b : Block) (t : Replay.At) :
    (Replay.resumeBlock b t).pausedAt = b.pausedAt ∨ (Replay.resumeBlock b t).pausedAt = some t := by
  unfold Replay.resumeBlock
  split
  · cases hp : b.pausedAt <;> simp [hp]
  · cases hs : b.since <;> simp [hs]

/-- **Every machine a step's arm writes holds only the old block's instants and the step's stamp.** -/
theorem arm_mi (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = t.1 := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    simp only [machineInstants, blockSince, blockPaused] at hq
    split at hq <;> simp_all
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        rename_i b hb _
        have := closeSub_mi dy m t
        cases hc : (Replay.closeSub dy m t).1.block with
        | none => simp [machineInstants, blockSince, blockPaused, hc] at hq
        | some c =>
          simp only [machineInstants, blockSince, blockPaused, hc, Option.map_some, Option.bind_some, Option.toList_some,
            List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | hq
          · left; exact this q (List.mem_append_left _ (by simp only [blockSince, hc, Option.bind_some]; simpa using hq))
          · right; simpa using hq
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        have := closePause_mi dy m t
        cases hc : (Replay.closePause dy m t).1.block with
        | none => simp [machineInstants, blockSince, blockPaused, hc] at hq
        | some c =>
          simp only [machineInstants, blockSince, blockPaused, hc, Option.map_some, Option.bind_some, Option.toList_some,
            List.mem_append] at hq
          rcases hq with hq | hq
          · split at hq
            · right; simpa using hq
            · left; exact this q (List.mem_append_left _ (by simp only [blockSince, hc, Option.bind_some]; simpa using hq))
          · left; exact this q (List.mem_append_right _ (by simp only [blockPaused, hc, Option.bind_some]; simpa using hq))
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closeSub_obs dy m t).2.2, (Replay.closePause_obs dy _ t).2.2,
      List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    left
    apply closeSub_mi dy m t q
    apply closePause_mi dy _ t q
    split at hq <;> simpa [machineInstants, blockSince, blockPaused] using hq
  case resume lost dropped =>
    have hr : ∀ m'', m''.block = m.block.map (Replay.resumeBlock · t) →
        ∀ q ∈ machineInstants m'', q ∈ machineInstants m ∨ q = t.1 := by
      intro m'' hb q hq
      cases hmb : m.block with
      | none =>
        unfold machineInstants blockSince blockPaused at hq
        rw [hb, hmb] at hq
        simp at hq
      | some b =>
        have hq' : q ∈ ((Replay.resumeBlock b t).since.map (·.1)).toList ∨
            q ∈ ((Replay.resumeBlock b t).pausedAt.map (·.1)).toList := by
          unfold machineInstants blockSince blockPaused at hq
          rw [hb, hmb] at hq
          simp only [Option.map_some, Option.bind_some] at hq
          exact List.mem_append.1 hq
        have hs1 : q ∈ (b.since.map (·.1)).toList → q ∈ machineInstants m := fun h => by
          unfold machineInstants blockSince; simp only [hmb, Option.bind_some]; exact List.mem_append_left _ h
        have hp1 : q ∈ (b.pausedAt.map (·.1)).toList → q ∈ machineInstants m := fun h => by
          unfold machineInstants blockPaused; simp only [hmb, Option.bind_some]; exact List.mem_append_right _ h
        rcases hq' with h | h
        · rcases resumeBlock_since b t with e1 | e1 <;> rw [e1] at h
          · exact Or.inl (hs1 h)
          · right; simpa using h
        · rcases resumeBlock_pausedAt b t with e1 | e1 <;> rw [e1] at h
          · exact Or.inl (hp1 h)
          · right; simpa using h
    split at hm <;>
    · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
      subst hm
      exact hr _ rfl q hq
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (cut_mi dy m t q hq)
      · simp at hm
    · simp at hm
  case extend id by_ => simp [Effect.machineOf?] at hm
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    left
    unfold Replay.doneClose at hq
    split at hq
    · split at hq
      · simp [machineInstants, blockSince, blockPaused] at hq
      · exact hq
    · split at hq
      · split at hq
        · simpa [machineInstants, blockSince, blockPaused] using hq
        · exact hq
      · exact hq
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **A step's machine holds only the old block's instants and the step's stamp.** -/
theorem stepWith_mi (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.stepWith z dy sl st e).machine) :
    q ∈ machineInstants st.machine ∨ q = e.t.val := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  unfold Replay.stepWith at hq
  rw [h3] at hq
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  rw [hfx] at hq
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => rw [hl] at hq; exact Or.inl hq
  | some m' =>
    rw [hl, Option.getD_some] at hq
    exact arm_mi dy sl st.machine e _ _ m' (List.mem_of_getLast? hl) q hq

/-- **A fold's queries are its entries' instants and its start state's block instants.** -/
theorem foldQueries_sub (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (q : Cal.Instant), q ∈ foldQueries z dy sl st sv →
      q ∈ machineInstants st.machine ∨ q ∈ sv.flatMap entryInstants
  | [], _, _, h => by simp [foldQueries] at h
  | e :: sv, st, q, h => by
    unfold foldQueries at h
    rcases List.mem_append.1 h with h | h
    · rcases stepQueries_sub st.machine e q h with h | h
      · exact Or.inr (List.mem_append_left _ h)
      · exact Or.inl h
    · rcases foldQueries_sub z dy sl sv _ q h with h | h
      · rcases stepWith_mi z dy sl st e q h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ (by simp [entryInstants, h]))
      · exact Or.inr (List.mem_append_right _ h)

/-- **The machine after a fold holds its start's block instants and its entries' stamps.** -/
theorem foldl_mi (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (q : Cal.Instant), q ∈ machineInstants (sv.foldl (Replay.stepWith z dy sl) st).machine →
      q ∈ machineInstants st.machine ∨ q ∈ sv.flatMap entryInstants
  | [], _, _, h => Or.inl h
  | e :: sv, st, q, h => by
    rw [List.foldl_cons] at h
    rcases foldl_mi z dy sl sv _ q h with h | h
    · rcases stepWith_mi z dy sl st e q h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ (by simp [entryInstants, h]))
    · exact Or.inr (List.mem_append_right _ h)

end Seal
end Tm
