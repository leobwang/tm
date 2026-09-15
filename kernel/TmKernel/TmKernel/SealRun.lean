import TmKernel.SealResume
/-!
# SealRun — what an accepted resume checked (stage 5, D9, W2)

An accepted `resumeRun` passed every guard: the zone, the cut, `now` at or after the ledger day, G1, every checked
step of the tail (the head second, the fence, the keys) and every tail header.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect)
open Log (Entry)

/-- The state a checked fold reaches is the plain fold's. -/
theorem tailFold_fst (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) :
    ∀ (sv : List Entry) (acc : State × Option Refusal),
      (sv.foldl (tailFoldStep z dy sl K) acc).1 = sv.foldl (Replay.stepWith z dy sl) acc.1
  | [], _ => rfl
  | e :: sv, acc => by
    rw [List.foldl_cons, List.foldl_cons, tailFold_fst z dy sl K sv]
    rfl

/-- **A checked fold that refuses nothing checked every step**, at the state the plain fold reaches before it. -/
theorem tailFold_snd (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) :
    ∀ (sv : List Entry) (acc : State × Option Refusal),
      (sv.foldl (tailFoldStep z dy sl K) acc).2 = none →
        acc.2 = none ∧ ∀ (pre : List Entry) (e : Entry) (post : List Entry), sv = pre ++ e :: post →
          (stepCheck z dy sl K (pre.foldl (Replay.stepWith z dy sl) acc.1) e).2 = none
  | [], acc, h => ⟨h, fun pre e post hs => by cases pre <;> cases hs⟩
  | e :: sv, acc, h => by
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := tailFold_snd z dy sl K sv _ h
    simp only [tailFoldStep] at h1
    have ha : acc.2 = none := by cases hacc : acc.2 <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]
    have he : (stepCheck z dy sl K acc.1 e).2 = none := by
      rw [ha] at h1; simpa [HOrElse.hOrElse, OrElse.orElse, Option.orElse] using h1
    refine ⟨ha, fun pre e' post hs => ?_⟩
    have hst : (tailFoldStep z dy sl K acc e).1 = Replay.stepWith z dy sl acc.1 e := rfl
    rw [hst] at h2
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact he
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [List.foldl_cons]
      exact h2 pre e' post rfl

theorem orElse_none {α : Type} {a b : Option α} (h : (a <|> b) = none) : a = none ∧ b = none := by
  cases a <;> cases b <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- **What a step that passed its check satisfies**: every instant it reads is at or after the head second; a wake is
after the folded instants and inside the fence; every key it writes is at or above the horizons. -/
theorem stepCheck_none (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (e : Entry)
    (h : (stepCheck z dy sl K st e).2 = none) :
    (∀ q ∈ stepQueries st.machine e, headSec K.ledgerDay ≤ q.sec) ∧
    (Replay.isWake e = true → (∀ m, K.maxT = some m → m < e.t.val) ∧
      (∀ f, K.futureFloor = some f → e.t.val.sec + fenceSec < f.sec)) ∧
    (∀ x ∈ Replay.effectsWith z dy sl st e, keyAtOrAbove K.ledgerDay (horizonOf K.ledgerDay) x.key = true) := by
  unfold stepCheck at h
  simp only at h
  obtain ⟨h1, h23⟩ := orElse_none h
  obtain ⟨h2, h3⟩ := orElse_none h23
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have := Option.map_eq_none_iff.1 h1
    rw [List.find?_eq_none] at this
    have := this q hq
    simp only [decide_eq_true_eq, Nat.not_lt] at this
    exact this
  · intro hw
    have hc : (K.maxT.all (· < e.t.val) && K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec))) = true := by
      cases hcc : (K.maxT.all (· < e.t.val) && K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec))) with
      | true => rfl
      | false => rw [hw, hcc] at h2; simp at h2
    rw [Bool.and_eq_true] at hc
    obtain ⟨hm, hf⟩ := hc
    refine ⟨fun m hm' => ?_, fun f hf' => ?_⟩
    · rw [hm'] at hm; simpa using hm
    · rw [hf'] at hf; simpa using hf
  · intro x hx
    have := Option.map_eq_none_iff.1 h3
    rw [List.find?_eq_none] at this
    have := this x hx
    simpa using this

/-- **What the header check passed**: every tail entry's stamp is at or after the head second, and its day at or after
the ledger day. -/
theorem headerCheck_none (dy : Cal.Instant → Nat) (K : Ckpt) (bs : List Entry) (h : headerCheck dy K bs = none) :
    ∀ e ∈ bs, headSec K.ledgerDay ≤ e.t.val.sec ∧ K.ledgerDay ≤ dy e.t.val := by
  intro e he
  unfold headerCheck at h
  have := List.findSome?_eq_none_iff.1 h e he
  split at this
  · cases this
  · rename_i h1
    split at this
    · cases this
    · rename_i h2
      exact ⟨by omega, by omega⟩

/-- **An accepted resume, unpacked.** -/
theorem resumeRun_ok (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (run : Run)
    (h : resumeRun z T K b = .ok run) :
    K.tzKey = z.val.key ∧ b.head?.all (fun l => l.n == K.cut + 1) = true ∧ K.ledgerDay ≤ T ∧
    g1 K (unsettled K.settled (Log.lineEntries b)) = none ∧
    let bs := Log.lineEntries b
    let N := unsettled K.settled bs
    let sv := Replay.survivors N
    let kw := tailIndex z K sv
    let dy := Replay.dayOf z kw
    let sl := tailSlept z K kw sv
    let st0 := restore K (K.items.length + K.openDays.length + bs.length)
    (tailFold z dy sl K st0 sv).2 = none ∧ headerCheck dy K bs = none ∧
    run = ⟨bs, N, sv, kw, sl, rebindState sl (sv.foldl (Replay.stepWith z dy sl) st0),
      storedHeaders K ++ tailHeaders dy K.settled bs,
      resumedAnswer K (rebindState sl (sv.foldl (Replay.stepWith z dy sl) st0))
        (storedHeaders K ++ tailHeaders dy K.settled bs) bs.length (Log.lineWarnings b)⟩ := by
  simp only [resumeRun] at h
  split at h
  · cases h
  rename_i hz
  split at h
  · cases h
  rename_i hc
  split at h
  · cases h
  rename_i hT
  split at h
  · cases h
  rename_i hg
  split at h
  · cases h
  rename_i hr
  simp only [Except.ok.injEq] at h
  obtain ⟨h1, h2⟩ := orElse_none hr
  refine ⟨by simpa using hz, by simpa using hc, by omega, hg, h1, h2, ?_⟩
  rw [← h]
  simp only [tailFold, tailFold_fst]

end Seal
end Tm
