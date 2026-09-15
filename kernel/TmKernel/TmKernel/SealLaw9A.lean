import TmKernel.SealGenesis
/-!
# SealLaw9A — lines, records and the merged reading across calls (stage 5, D9, W2: law 9)

What genesis' calls compose through: a call's lines continue its checkpoint's (`genLines_append`, `genLines_take`,
`genLines_drop`); the records of `[0, L')` are those of `[0, L)` then `[L, L')` (`dayRecordsBetween_split`,
`windowRecordsBetween_split`) and a range's records are a filter of a longer range's (`…_restrict`); records at or above
an answer's horizons change no merged reading (`askMerged_extra`); and the empty log is sealable (`sealable_empty`).
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State HeaderRec)
open Log (Entry)

theorem contiguousFrom_take : ∀ (k : Nat) (ls : List Log.Line) (n : Nat), Log.contiguousFrom k ls = true →
    Log.contiguousFrom k (ls.take n) = true
  | _, [], _, _ => by simp [Log.contiguousFrom]
  | _, _ :: _, 0, _ => rfl
  | k, l :: ls, n + 1, h => by
    rw [List.take_succ_cons]
    simp only [Log.contiguousFrom, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, contiguousFrom_take (k + 1) ls n h.2⟩

theorem genLines_append (ls : List Log.Line) (c e : Nat) (hce : c ≤ e) :
    ls.take c ++ (ls.drop c).take (e - c) = ls.take e := by
  rw [← List.take_add]; congr 1; omega

theorem genLines_take (ls : List Log.Line) (c e j : Nat) (hj : j ≤ e - c) :
    ((ls.drop c).take (e - c)).take j = (ls.drop c).take j := by
  rw [List.take_take, Nat.min_eq_left hj]

theorem genLines_drop (ls : List Log.Line) (c e j : Nat) :
    ((ls.drop c).take (e - c)).drop j = (ls.drop (c + j)).take (e - (c + j)) := by
  rw [List.drop_take, List.drop_drop]; congr 1; omega

theorem length_genLines (ls : List Log.Line) (c e : Nat) (hel : e ≤ ls.length) :
    ((ls.drop c).take (e - c)).length = e - c := by
  rw [List.length_take, List.length_drop]; omega

/-- **A sorted key list splits at a day.** -/
theorem filter_range_split (L L' : Nat) (hLL : L ≤ L') : ∀ (l : List Nat), l.Pairwise (fun a b => natLt a b = true) →
    l.filter (fun d => decide (0 ≤ d ∧ d < L'))
      = l.filter (fun d => decide (0 ≤ d ∧ d < L)) ++ l.filter (fun d => decide (L ≤ d ∧ d < L'))
  | [], _ => rfl
  | a :: l, hs => by
    rw [List.pairwise_cons] at hs
    have hgt : ∀ x ∈ l, a < x := fun x hx => by simpa [natLt] using hs.1 x hx
    have ih := filter_range_split L L' hLL l hs.2
    by_cases h1 : a < L
    · have e1 : decide (0 ≤ a ∧ a < L') = true := decide_eq_true (by omega)
      have e2 : decide (0 ≤ a ∧ a < L) = true := decide_eq_true (by omega)
      have e3 : decide (L ≤ a ∧ a < L') = false := decide_eq_false (by omega)
      simp only [List.filter_cons, e1, e2, e3, ↓reduceIte, Bool.false_eq_true, ih, List.cons_append]
    · by_cases h2 : a < L'
      · have e1 : decide (0 ≤ a ∧ a < L') = true := decide_eq_true (by omega)
        have e2 : decide (0 ≤ a ∧ a < L) = false := decide_eq_false (by omega)
        have e3 : decide (L ≤ a ∧ a < L') = true := decide_eq_true (by omega)
        have h0 : l.filter (fun d => decide (0 ≤ d ∧ d < L)) = [] :=
          List.filter_eq_nil_iff.2 (fun x hx h => by have := hgt x hx; simp at h; omega)
        simp only [List.filter_cons, e1, e2, e3, ↓reduceIte, Bool.false_eq_true, ih, h0, List.nil_append]
      · have e1 : decide (0 ≤ a ∧ a < L') = false := decide_eq_false (by omega)
        have e2 : decide (0 ≤ a ∧ a < L) = false := decide_eq_false (by omega)
        have e3 : decide (L ≤ a ∧ a < L') = false := decide_eq_false (by omega)
        simp only [List.filter_cons, e1, e2, e3, ↓reduceIte, Bool.false_eq_true, ih]

theorem finish_day (m : Replay.Machine) (o : OpenDay) : (OpenDay.finish m o).day = o.day := rfl

theorem daysIn_split (st : State) (hs : List (Nat × HeaderRec)) (L L' : Nat) (hLL : L ≤ L') :
    daysIn st hs 0 L' = daysIn st hs 0 L ++ daysIn st hs L L' := by
  have hsort := sorted_canon natLt_strictTotal (st.days.pairs.map Prod.fst ++ st.seams.pairs.map Prod.fst
    ++ st.energy.map (·.day) ++ st.durations.map (·.day) ++ st.interrupts.map (·.day) ++ st.demotions.map Prod.fst
    ++ st.closes.map Prod.fst ++ hs.map Prod.fst ++ ((st.machine.block.bind (·.obs)).map (·.day)).toList)
  unfold daysIn dayKeys
  rw [filter_range_split L L' hLL _ hsort, List.map_append]

theorem windowsIn_split (st : State) (H H' : Nat) (hHH : H ≤ H') :
    windowsIn st 0 H' = windowsIn st 0 H ++ windowsIn st H H' := by
  have hsort := sorted_canon natLt_strictTotal (st.itemDays.pairs.map (·.1.1) ++ st.doneDates.pairs.map (·.1.1)
    ++ st.instances.pairs.filterMap (fun p => Log.instDate? p.1.2))
  unfold windowsIn winKeys
  rw [filter_range_split H H' hHH _ hsort, List.map_append]

theorem dayRecordsBetween_split (z : Cal.Tz) (T L L' : Nat) (X : List Log.Line) (hLL : L ≤ L') :
    dayRecordsBetween z T 0 L' X = dayRecordsBetween z T 0 L X ++ dayRecordsBetween z T L L' X := by
  unfold dayRecordsBetween dayRecordsOfEntries
  rw [daysIn_split _ _ L L' hLL, List.map_append]

theorem windowRecordsBetween_split (z : Cal.Tz) (T H H' : Nat) (X : List Log.Line) (hHH : H ≤ H') :
    windowRecordsBetween z T 0 H' X = windowRecordsBetween z T 0 H X ++ windowRecordsBetween z T H H' X := by
  unfold windowRecordsBetween windowRecordsOfEntries
  exact windowsIn_split _ H H' hHH

theorem daysIn_restrict (st : State) (hs : List (Nat × HeaderRec)) (m : Replay.Machine) (L L' : Nat) :
    (daysIn st hs L L').map (OpenDay.finish m)
      = ((daysIn st hs 0 L').map (OpenDay.finish m)).filter (fun r => decide (L ≤ r.day)) := by
  unfold daysIn
  rw [List.map_map, List.map_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro d _
  simp only [Function.comp_apply, finish_day, openDayOf_day]
  by_cases h1 : L ≤ d <;> by_cases h2 : d < L' <;> simp [h1, h2]

theorem windowsIn_restrict (st : State) (H H' : Nat) :
    windowsIn st H H' = (windowsIn st 0 H').filter (fun w => decide (H ≤ w.day)) := by
  unfold windowsIn
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro d _
  simp only [Function.comp_apply, windowOf_day]
  by_cases h1 : H ≤ d <;> by_cases h2 : d < H' <;> simp [h1, h2]

theorem dayRecordsBetween_restrict (z : Cal.Tz) (T L L' : Nat) (X : List Log.Line) :
    dayRecordsBetween z T L L' X = (dayRecordsBetween z T 0 L' X).filter (fun r => decide (L ≤ r.day)) := by
  unfold dayRecordsBetween dayRecordsOfEntries
  exact daysIn_restrict _ _ _ L L'

theorem windowRecordsBetween_restrict (z : Cal.Tz) (T H H' : Nat) (X : List Log.Line) :
    windowRecordsBetween z T H H' X = (windowRecordsBetween z T 0 H' X).filter (fun w => decide (H ≤ w.day)) := by
  unfold windowRecordsBetween windowRecordsOfEntries
  exact windowsIn_restrict _ H H'

theorem mem_daysIn_finish (st : State) (hs : List (Nat × HeaderRec)) (m : Replay.Machine) (lo hi : Nat) (r : DayRecord)
    (h : r ∈ (daysIn st hs lo hi).map (OpenDay.finish m)) : lo ≤ r.day ∧ r.day < hi := by
  unfold daysIn at h
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ho
  exact of_decide_eq_true (List.mem_filter.1 hd).2

theorem mem_windowsIn (st : State) (lo hi : Nat) (w : WindowRecord) (h : w ∈ windowsIn st lo hi) :
    lo ≤ w.day ∧ w.day < hi := by
  unfold windowsIn at h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
  exact of_decide_eq_true (List.mem_filter.1 hd).2

theorem mem_dayRecordsBetween (z : Cal.Tz) (T lo hi : Nat) (X : List Log.Line) (r : DayRecord)
    (h : r ∈ dayRecordsBetween z T lo hi X) : lo ≤ r.day ∧ r.day < hi :=
  mem_daysIn_finish _ _ _ lo hi r h

theorem mem_windowRecordsBetween (z : Cal.Tz) (T lo hi : Nat) (X : List Log.Line) (w : WindowRecord)
    (h : w ∈ windowRecordsBetween z T lo hi X) : lo ≤ w.day ∧ w.day < hi :=
  mem_windowsIn _ lo hi w h

/-- **Records at or above an answer's horizons change no merged reading.** -/
theorem askMerged_extra (ds X : List DayRecord) (ws W : List WindowRecord) (v : Seal.Answer) (q : Q)
    (hX : ∀ r ∈ X, v.ledgerDay ≤ r.day) (hW : ∀ w ∈ W, v.horizon ≤ w.day) :
    askMerged (ds ++ X) (ws ++ W) v q = askMerged ds ws v q := by
  unfold askMerged
  cases hq : askAnswer v q with
  | some a => rfl
  | none =>
    cases q with
    | day d dq =>
      simp only [askAnswer] at hq
      split at hq
      · rename_i hd
        simp only [askDayRecords, findDay, List.find?_append]
        rw [Option.or_eq_left_of_none (List.find?_eq_none.2 (fun r hr h => by
          have := hX r hr; simp only [decide_eq_true_eq] at h; omega))]
      · cases hq
    | win d wq =>
      simp only [askAnswer] at hq
      split at hq
      · rename_i hd
        simp only [askWindowRecords, findWin, List.find?_append]
        rw [Option.or_eq_left_of_none (List.find?_eq_none.2 (fun w hw h => by
          have := hW w hw; simp only [decide_eq_true_eq] at h; omega))]
      · cases hq
    | _ => simp [askAnswer] at hq

/-- **The empty log is sealable at day 0.** -/
theorem sealable_empty (z : Cal.Tz) : sealable z 0 0 [] [] = true := by
  unfold sealable sealableEntries
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ?_⟩, ?_⟩
  · unfold dayRecordsOfEntries; exact beq_self_eq_true _
  · unfold windowRecordsOfEntries; exact beq_self_eq_true _

theorem popTo_sub (e : Refusal) : ∀ (l : List GenEntry) (x : GenEntry), x ∈ popTo e l → x ∈ l
  | [], _, h => h
  | [_], _, h => h
  | a :: b :: rest, x, h => by
    unfold popTo at h
    split at h
    · exact h
    · exact List.mem_cons_of_mem _ (popTo_sub e (b :: rest) x h)

theorem popTo_ne_nil (e : Refusal) : ∀ (l : List GenEntry), l ≠ [] → popTo e l ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [popTo]
  | a :: b :: rest, _ => by
    unfold popTo
    split
    · simp
    · exact popTo_ne_nil e (b :: rest) (by simp)

theorem endsFrom_spec : ∀ (s : Nat) (cs : List (List Log.Line)),
    (endsFrom s cs).Pairwise (· ≤ ·) ∧ (∀ e ∈ endsFrom s cs, s ≤ e ∧ e ≤ s + cs.flatten.length) ∧
    (cs ≠ [] → (endsFrom s cs).getLast? = some (s + cs.flatten.length)) ∧ (endsFrom s cs = [] ↔ cs = [])
  | s, [] => by simp [endsFrom]
  | s, c :: cs => by
    obtain ⟨h1, h2, h3, h4⟩ := endsFrom_spec (s + c.length) cs
    refine ⟨?_, ?_, fun _ => ?_, by simp [endsFrom]⟩
    · simp only [endsFrom, List.pairwise_cons]
      exact ⟨fun e he => (h2 e he).1, h1⟩
    · intro e he
      simp only [endsFrom, List.mem_cons] at he
      simp only [List.flatten_cons, List.length_append]
      rcases he with rfl | he
      · omega
      · have := h2 e he; omega
    · simp only [endsFrom, List.flatten_cons, List.length_append]
      by_cases hcs : cs = []
      · subst hcs; simp [endsFrom]
      · rw [List.getLast?_cons, h3 hcs]
        simp only [Option.getD_some]
        congr 1; omega

end Seal
end Tm
