import TmKernel.SealLaw2D
import TmKernel.SealPending
/-!
# SealLaw4 — law 4: what Rust stored is still true (stage 5, D9, W2)

An accepted resume's tail names no key below the horizons and heads no day below the ledger day, its pending start
observation is on a day at or after it, and the folded part of the whole log's fold reads as the folded lines' below
the horizons.  So the whole log's day and window records below the horizons are the folded lines' (`resume_below`),
which `sealable` makes the records of `a` alone.  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Effect HMap HeaderRec survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **Two states agree below the horizons**: each day below `L`, each window date below `H`. -/
structure AgreeBelow (L H : Nat) (x y : State) : Prop where
  days : ∀ d, d < L → x.days.get d = y.days.get d
  seams : ∀ d, d < L → x.seams.get d = y.seams.get d
  energy : ∀ d, d < L → x.energy.filter (fun o => decide (o.day = d)) = y.energy.filter (fun o => decide (o.day = d))
  durations : ∀ d, d < L →
    x.durations.filter (fun o => decide (o.day = d)) = y.durations.filter (fun o => decide (o.day = d))
  interrupts : ∀ d, d < L →
    x.interrupts.filter (fun o => decide (o.day = d)) = y.interrupts.filter (fun o => decide (o.day = d))
  demotions : ∀ d, d < L →
    x.demotions.filter (fun p => decide (p.1 = d)) = y.demotions.filter (fun p => decide (p.1 = d))
  closes : ∀ d, d < L → x.closes.filter (fun p => decide (p.1 = d)) = y.closes.filter (fun p => decide (p.1 = d))
  itemDays : ∀ d i, d < H → x.itemDays.get (d, i) = y.itemDays.get (d, i)
  doneDates : ∀ d i, d < H → x.doneDates.get (d, i) = y.doneDates.get (d, i)
  instances : ∀ k d, Log.instDate? k.2 = some d → d < H → x.instances.get k = y.instances.get k

theorem AgreeBelow.symm {L H : Nat} {x y : State} (h : AgreeBelow L H x y) : AgreeBelow L H y x :=
  ⟨fun d hd => (h.days d hd).symm, fun d hd => (h.seams d hd).symm, fun d hd => (h.energy d hd).symm,
   fun d hd => (h.durations d hd).symm, fun d hd => (h.interrupts d hd).symm, fun d hd => (h.demotions d hd).symm,
   fun d hd => (h.closes d hd).symm, fun d i hd => (h.itemDays d i hd).symm, fun d i hd => (h.doneDates d i hd).symm,
   fun k d hk hd => (h.instances k d hk hd).symm⟩

/-- A machine's pending start observation is on a day at or after `L`. -/
def PendingAbove (L : Nat) (m : Replay.Machine) : Prop := ∀ o, m.block.bind (·.obs) = some o → L ≤ o.day

theorem pendingOn_below {L : Nat} {m : Replay.Machine} (hp : PendingAbove L m) (d : Nat) (hd : d < L) :
    pendingOn m d = [] := by
  unfold pendingOn
  cases hb : m.block.bind (·.obs) with
  | none => rfl
  | some o =>
    have := hp o hb
    simp [Option.filter, show o.day ≠ d by omega]

theorem not_mem_pending_below {L : Nat} {m : Replay.Machine} (hp : PendingAbove L m) (d : Nat) (hd : d < L) :
    d ∉ ((m.block.bind (·.obs)).map (·.day)).toList := by
  cases hb : m.block.bind (·.obs) with
  | none => simp
  | some o => have := hp o hb; simp; omega

section Below

variable {L H : Nat} {x y : State} (hx : AllKeyed x) (hy : AllKeyed y) (h : AgreeBelow L H x y)
include hx hy h

theorem winKeys_filter_below :
    (winKeys x).filter (fun d => decide (0 ≤ d ∧ d < H)) = (winKeys y).filter (fun d => decide (0 ≤ d ∧ d < H)) := by
  unfold winKeys
  rw [canon_filter natLt_strictTotal, canon_filter natLt_strictTotal]
  apply canon_eq_of_mem_iff natLt_strictTotal
  intro d
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
  have key : ∀ (u v : State) (hu : AllKeyed u) (hv : AllKeyed v) (huv : AgreeBelow L H u v), d < H →
      ((d ∈ u.itemDays.pairs.map (·.1.1) ∨ d ∈ u.doneDates.pairs.map (·.1.1)) ∨
        d ∈ u.instances.pairs.filterMap (fun p => Log.instDate? p.1.2)) →
      ((d ∈ v.itemDays.pairs.map (·.1.1) ∨ d ∈ v.doneDates.pairs.map (·.1.1)) ∨
        d ∈ v.instances.pairs.filterMap (fun p => Log.instDate? p.1.2)) := by
    intro u v hu hv huv hd hm
    rcases hm with (hm | hm) | hm
    · obtain ⟨k, rfl, hk⟩ := (mem_keys_map_iff u.itemDays hu.2.2.1 (·.1) _).1 hm
      rw [huv.itemDays k.1 k.2 hd] at hk
      exact Or.inl (Or.inl ((mem_keys_map_iff v.itemDays hv.2.2.1 (·.1) _).2 ⟨k, rfl, hk⟩))
    · obtain ⟨k, rfl, hk⟩ := (mem_keys_map_iff u.doneDates hu.2.2.2.2.1 (·.1) _).1 hm
      rw [huv.doneDates k.1 k.2 hd] at hk
      exact Or.inl (Or.inr ((mem_keys_map_iff v.doneDates hv.2.2.2.2.1 (·.1) _).2 ⟨k, rfl, hk⟩))
    · obtain ⟨p, hp, hpd⟩ := List.mem_filterMap.1 hm
      have hk := (Replay.HMap.mem_keys_pairs_iff u.instances hu.2.2.2.2.2.1 p.1).1 (List.mem_map.2 ⟨p, hp, rfl⟩)
      rw [huv.instances p.1 d hpd hd] at hk
      obtain ⟨q, hq, hqk⟩ := List.mem_map.1 ((Replay.HMap.mem_keys_pairs_iff v.instances hv.2.2.2.2.2.1 p.1).2 hk)
      exact Or.inr (List.mem_filterMap.2 ⟨q, hq, by rw [hqk]; exact hpd⟩)
  exact ⟨fun ⟨hm, hd⟩ => ⟨key x y hx hy h hd.2 hm, hd⟩, fun ⟨hm, hd⟩ => ⟨key y x hy hx h.symm hd.2 hm, hd⟩⟩

theorem windowOf_below (d : Nat) (hd : d < H) : windowOf x d = windowOf y d := by
  have hc1 : canon idLt ((x.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))
      = canon idLt ((y.itemDays.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)) :=
    canon_eq_of_mem_iff idLt_strictTotal _ _ (fun i => by
      rw [mem_ids_of_day _ hx.2.2.1, mem_ids_of_day _ hy.2.2.1, h.itemDays d i hd])
  have hc2 : canon idLt ((x.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2))
      = canon idLt ((y.doneDates.pairs.filter (fun p => decide (p.1.1 = d))).map (·.1.2)) :=
    canon_eq_of_mem_iff idLt_strictTotal _ _ (fun i => by
      rw [mem_ids_of_day _ hx.2.2.2.2.1, mem_ids_of_day _ hy.2.2.2.2.1, h.doneDates d i hd])
  have hc3 : canon instKeyLt ((x.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst)
      = canon instKeyLt ((y.instances.pairs.filter (fun p => decide (Log.instDate? p.1.2 = some d))).map Prod.fst) :=
    canon_eq_of_mem_iff instKeyLt_strictTotal _ _ (fun k => by
      rw [mem_keys_filter_iff x.instances hx.2.2.2.2.2.1 (fun k => decide (Log.instDate? k.2 = some d)),
        mem_keys_filter_iff y.instances hy.2.2.2.2.2.1 (fun k => decide (Log.instDate? k.2 = some d))]
      constructor
      · rintro ⟨hk1, hk2⟩
        exact ⟨hk1, by rw [← h.instances k d (of_decide_eq_true hk1) hd]; exact hk2⟩
      · rintro ⟨hk1, hk2⟩
        exact ⟨hk1, by rw [h.instances k d (of_decide_eq_true hk1) hd]; exact hk2⟩)
  unfold windowOf
  rw [hc1, hc2, hc3]
  congr 1
  · exact filterMap_congr' _ _ _ (fun i _ => by rw [h.itemDays d i hd])
  · refine filterMap_congr' _ _ _ (fun k hk => ?_)
    have hk1 := ((mem_keys_filter_iff y.instances hy.2.2.2.2.2.1 (fun k => decide (Log.instDate? k.2 = some d)) k).1
      ((mem_canon instKeyLt_strictTotal _ _).1 hk)).1
    rw [h.instances k d (of_decide_eq_true hk1) hd]

theorem windowsIn_below : windowsIn x 0 H = windowsIn y 0 H := by
  unfold windowsIn
  rw [winKeys_filter_below hx hy h]
  exact List.map_congr_left (fun d hd => windowOf_below hx hy h d (of_decide_eq_true (List.mem_filter.1 hd).2).2)

theorem dayKeys_filter_below (hsx hsy : List (Nat × HeaderRec))
    (hhs : ∀ d, d < L → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d)))
    (hpx : PendingAbove L x.machine) (hpy : PendingAbove L y.machine) :
    (dayKeys x hsx).filter (fun d => decide (0 ≤ d ∧ d < L))
      = (dayKeys y hsy).filter (fun d => decide (0 ≤ d ∧ d < L)) := by
  unfold dayKeys
  rw [canon_filter natLt_strictTotal, canon_filter natLt_strictTotal]
  apply canon_eq_of_mem_iff natLt_strictTotal
  intro d
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hd⟩
    refine ⟨?_, hd⟩
    rw [Replay.HMap.mem_keys_pairs_iff _ hx.1, Replay.HMap.mem_keys_pairs_iff _ hx.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil x.energy, mem_map_iff_filter_ne_nil x.durations, mem_map_iff_filter_ne_nil x.interrupts,
      mem_map_iff_filter_ne_nil x.demotions, mem_map_iff_filter_ne_nil x.closes, mem_map_iff_filter_ne_nil hsx,
      h.days d hd.2, h.seams d hd.2, h.energy d hd.2, h.durations d hd.2, h.interrupts d hd.2, h.demotions d hd.2,
      h.closes d hd.2, hhs d hd.2, iff_false_intro (not_mem_pending_below hpx d hd.2), or_false] at hm
    rw [Replay.HMap.mem_keys_pairs_iff _ hy.1, Replay.HMap.mem_keys_pairs_iff _ hy.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil y.energy, mem_map_iff_filter_ne_nil y.durations, mem_map_iff_filter_ne_nil y.interrupts,
      mem_map_iff_filter_ne_nil y.demotions, mem_map_iff_filter_ne_nil y.closes, mem_map_iff_filter_ne_nil hsy,
      iff_false_intro (not_mem_pending_below hpy d hd.2), or_false]
    exact hm
  · rintro ⟨hm, hd⟩
    refine ⟨?_, hd⟩
    rw [Replay.HMap.mem_keys_pairs_iff _ hy.1, Replay.HMap.mem_keys_pairs_iff _ hy.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil y.energy, mem_map_iff_filter_ne_nil y.durations, mem_map_iff_filter_ne_nil y.interrupts,
      mem_map_iff_filter_ne_nil y.demotions, mem_map_iff_filter_ne_nil y.closes, mem_map_iff_filter_ne_nil hsy,
      ← h.days d hd.2, ← h.seams d hd.2, ← h.energy d hd.2, ← h.durations d hd.2, ← h.interrupts d hd.2,
      ← h.demotions d hd.2, ← h.closes d hd.2, ← hhs d hd.2, iff_false_intro (not_mem_pending_below hpy d hd.2),
      or_false] at hm
    rw [Replay.HMap.mem_keys_pairs_iff _ hx.1, Replay.HMap.mem_keys_pairs_iff _ hx.2.2.2.2.2.2.2.2,
      mem_map_iff_filter_ne_nil x.energy, mem_map_iff_filter_ne_nil x.durations, mem_map_iff_filter_ne_nil x.interrupts,
      mem_map_iff_filter_ne_nil x.demotions, mem_map_iff_filter_ne_nil x.closes, mem_map_iff_filter_ne_nil hsx,
      iff_false_intro (not_mem_pending_below hpx d hd.2), or_false]
    exact hm

omit hx hy in
theorem openDayOf_below (hsx hsy : List (Nat × HeaderRec))
    (hhs : ∀ d, d < L → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d)))
    (d : Nat) (hd : d < L) : openDayOf x hsx d = openDayOf y hsy d := by
  unfold openDayOf
  rw [h.days d hd, h.seams d hd, h.energy d hd, h.durations d hd, h.interrupts d hd, h.demotions d hd, h.closes d hd,
    hhs d hd]

theorem daysIn_below (hsx hsy : List (Nat × HeaderRec))
    (hhs : ∀ d, d < L → hsx.filter (fun p => decide (p.1 = d)) = hsy.filter (fun p => decide (p.1 = d)))
    (hpx : PendingAbove L x.machine) (hpy : PendingAbove L y.machine) :
    (daysIn x hsx 0 L).map (OpenDay.finish x.machine) = (daysIn y hsy 0 L).map (OpenDay.finish y.machine) := by
  unfold daysIn
  rw [dayKeys_filter_below hx hy h hsx hsy hhs hpx hpy, List.map_map, List.map_map]
  exact List.map_congr_left (fun d hd => by
    have hdL := (of_decide_eq_true (List.mem_filter.1 hd).2).2
    simp only [Function.comp_apply]
    rw [openDayOf_below h hsx hsy hhs d hdL]
    unfold OpenDay.finish
    rw [openDayOf_day, pendingOn_below hpx d hdL, pendingOn_below hpy d hdL])

end Below

/-! ## The whole log's fold below the horizons -/

theorem valueAt_day_view {x y : State} {d : Nat} (h : x.valueAt (.day d) = y.valueAt (.day d)) :
    x.days.get d = y.days.get d ∧ x.seams.get d = y.seams.get d ∧
    x.energy.filter (fun o => decide (o.day = d)) = y.energy.filter (fun o => decide (o.day = d)) ∧
    x.durations.filter (fun o => decide (o.day = d)) = y.durations.filter (fun o => decide (o.day = d)) ∧
    x.interrupts.filter (fun o => decide (o.day = d)) = y.interrupts.filter (fun o => decide (o.day = d)) ∧
    (x.demotions.filter (fun p => decide (p.1 = d))).map Prod.snd
      = (y.demotions.filter (fun p => decide (p.1 = d))).map Prod.snd ∧
    (x.closes.filter (fun p => decide (p.1 = d))).map Prod.snd
      = (y.closes.filter (fun p => decide (p.1 = d))).map Prod.snd := by
  simp only [Replay.State.valueAt, Replay.Val.day.injEq, Replay.DayView.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem valueAt_itemDay_get {x y : State} {i : Log.Id} {d : Nat}
    (h : x.valueAt (.itemDay i d) = y.valueAt (.itemDay i d)) : x.itemDays.get (d, i) = y.itemDays.get (d, i) := by
  simp only [Replay.State.valueAt, Replay.Val.itemDay.injEq] at h
  exact h

theorem valueAt_instDate_get {x y : State} {item inst : List Char} {d : Nat} (hd : Log.instDate? inst = some d)
    (h : x.valueAt (.instDate item inst d) = y.valueAt (.instDate item inst d)) :
    x.instances.get (item, inst) = y.instances.get (item, inst) := by
  simp only [Replay.State.valueAt, Replay.Val.inst.injEq, hd, ↓reduceIte] at h
  exact h

theorem filter_fst_eq_of_snd {β : Type} (X Y : List (Nat × β)) (d : Nat)
    (h : (X.filter (fun p => decide (p.1 = d))).map Prod.snd = (Y.filter (fun p => decide (p.1 = d))).map Prod.snd) :
    X.filter (fun p => decide (p.1 = d)) = Y.filter (fun p => decide (p.1 = d)) := by
  have hX := map_pair_of_fst (X.filter (fun p => decide (p.1 = d))) d
    (fun p hp => of_decide_eq_true (List.mem_filter.1 hp).2)
  have hY := map_pair_of_fst (Y.filter (fun p => decide (p.1 = d))) d
    (fun p hp => of_decide_eq_true (List.mem_filter.1 hp).2)
  have eX : (X.filter (fun p => decide (p.1 = d))).map (fun p => (d, p.2))
      = ((X.filter (fun p => decide (p.1 = d))).map Prod.snd).map (fun r => (d, r)) := by
    rw [List.map_map]; rfl
  have eY : (Y.filter (fun p => decide (p.1 = d))).map (fun p => (d, p.2))
      = ((Y.filter (fun p => decide (p.1 = d))).map Prod.snd).map (fun r => (d, r)) := by
    rw [List.map_map]; rfl
  rw [← hX, ← hY, eX, eY, h]

/-- **A fold whose steps never name a key leaves its reading.** -/
theorem foldl_frame (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (k : Replay.Key) :
    ∀ (sv : List Entry) (st : State),
      (∀ pre e post, sv = pre ++ e :: post →
        ∀ x ∈ Replay.effectsWith z dy sl (pre.foldl (Replay.stepWith z dy sl) st) e, x.key ≠ k) →
      (sv.foldl (Replay.stepWith z dy sl) st).valueAt k = st.valueAt k
  | [], _, _ => rfl
  | e :: sv, st, h => by
    rw [List.foldl_cons]
    have h0 : (Replay.stepWith z dy sl st e).valueAt k = st.valueAt k :=
      Replay.applyEffects_touches_only_named_keys st _ k (fun hk => by
        obtain ⟨x, hx, hxk⟩ := List.mem_map.1 hk
        exact h [] e sv rfl x hx hxk)
    rw [foldl_frame z dy sl k sv _ (fun pre e' post hs x hx => h (e :: pre) e' post (by rw [hs]; rfl) x hx), h0]

/-- **Rebinding observations below `L` to a table that agrees there with the one they read changes nothing.** -/
theorem filter_rebind_below (g sl : Nat → Option Nat) (L d : Nat) (hd : d < L) (hg : ∀ d', d' < L → g d' = sl d') :
    ∀ (l : List Replay.EnergyObs), (∀ o ∈ l, o.fromStart = false → o.sleptMin = sl o.day) →
      (l.map (rebindObs g)).filter (fun o => decide (o.day = d)) = l.filter (fun o => decide (o.day = d))
  | [], _ => rfl
  | o :: l, h => by
    have ih := filter_rebind_below g sl L d hd hg l (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    have hday : (rebindObs g o).day = o.day := by unfold rebindObs; split <;> rfl
    by_cases hod : o.day = d
    · have heq : rebindObs g o = o := by
        unfold rebindObs
        split
        · rfl
        · rename_i hf
          have := h o List.mem_cons_self (by simpa using hf)
          rw [hg o.day (by omega), ← this]
      rw [List.map_cons, List.filter_cons_of_pos (by simp [hday, hod]), List.filter_cons_of_pos (by simp [hod]), heq, ih]
    · rw [List.map_cons, List.filter_cons_of_neg (by simp [hday, hod]), List.filter_cons_of_neg (by simp [hod]), ih]

/-- **Below the horizons, an accepted resume's whole log reads as its folded lines**: every day and window reading, the
pending start observation's day, and the headers. -/
theorem resume_below (z : Cal.Tz) (T₀ L cut : Nat) (As Rs B' : List Entry) (ws : List (Nat × Log.LWarn)) (n : Nat)
    (hd : (As ++ (Rs ++ B')).Pairwise (fun x y => x.line < y.line))
    (K : Ckpt) (hK : K = ckptOfEntries z T₀ L cut As Rs ws)
    (sv : List Entry) (hsv : sv = survivors (unsettled K.settled (Rs ++ B')))
    (hg : g1 K (unsettled K.settled (Rs ++ B')) = none)
    (kw : List Cal.Instant) (hkw : kw = tailIndex z K sv)
    (sl : Nat → Option Nat) (hsl : sl = tailSlept z K kw sv)
    (hsteps : ∀ pre e post, sv = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl K (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore K n)) e).2 = none)
    (hhdr : headerCheck (dayOf z kw) K (Rs ++ B') = none)
    (hpend : PendingAbove L (foldedState z As Rs).machine) :
    AgreeBelow L (horizonOf L) (foldedState z (As ++ (Rs ++ B')) []) (foldedState z As Rs) ∧
    PendingAbove L (foldedState z (As ++ (Rs ++ B')) []).machine ∧
    (∀ d, d < L → (foldedHeaders z (As ++ (Rs ++ B')) []).filter (fun p => decide (p.1 = d))
      = (foldedHeaders z As Rs).filter (fun p => decide (p.1 = d))) := by
  obtain ⟨hsurv, hI1, hI2, -⟩ := resume_index z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps
  have hHdr := resume_headers z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsteps hhdr
  have hAgree := (resume_state_agrees z T₀ L cut As Rs B' ws n hd K hK sv hsv hg kw hkw sl hsl hsteps).1
  have hhb := headerCheck_none (dayOf z kw) K (Rs ++ B') hhdr
  subst hK
  have hL := ckpt_ledgerDay' z T₀ L cut As Rs ws
  rw [hL] at hhb
  have hPS := pendingStart_restore z T₀ L cut As Rs ws n
  have hsvB : ∀ e ∈ sv, e ∈ Rs ++ B' := fun e he => by
    rw [hsv] at he; exact mem_unsettled_sub _ _ _ (Replay.mem_of_mem_survivors _ _ he)
  obtain ⟨KW, hKW⟩ : ∃ KW, KW = keptWakes z (wakeInstants (foldedSurvivors As Rs) ++ wakeInstants sv) := ⟨_, rfl⟩
  rw [← hKW] at hI1 hI2
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = Replay.KMap.get (Replay.sleptByDay z KW (foldedSurvivors As Rs ++ sv)) := ⟨_, rfl⟩
  have hF : foldedState z (As ++ (Rs ++ B')) [] = sv.foldl (Replay.stepWith z (dayOf z KW) SL)
      ((foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL) (State.init (As ++ (Rs ++ B')).length)) := by
    rw [foldedState_nil, hsurv, wakeInstants_append, List.foldl_append, ← hKW, ← hSL]
  obtain ⟨G, hGdef⟩ : ∃ G, G = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z KW) SL)
      (State.init (As ++ (Rs ++ B')).length) := ⟨_, rfl⟩
  rw [← hGdef] at hF
  have hq1 : ∀ q ∈ foldQueries z (dayOf z KW) SL (State.init (As ++ (Rs ++ B')).length) (foldedSurvivors As Rs),
      dayOf z KW q = dayOf z (foldedIndex z As Rs) q := by
    intro q hq
    rcases foldQueries_sub z _ _ _ _ q hq with h | h
    · simp [machineInstants, blockSince, blockPaused, State.init] at h
    · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.1 h
      exact hI1 q (List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, hqe⟩)
  obtain ⟨X, hXdef⟩ : ∃ X, X = (foldedSurvivors As Rs).foldl (Replay.stepWith z (dayOf z (foldedIndex z As Rs))
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))))
      (State.init (As ++ (Rs ++ B')).length) := ⟨_, rfl⟩
  have hGX : G = rebindState SL X := by
    rw [hGdef, foldl_stepWith_congr z _ _ SL _ _ hq1, hXdef]
    have := foldl_rebind z (dayOf z (foldedIndex z As Rs)) SL
      (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs))) (foldedSurvivors As Rs)
      (State.init (As ++ (Rs ++ B')).length) (pendingStart_init _)
    rwa [rebindState_init] at this
  have hXs : Replay.SameReadings X (foldedState z As Rs) := by
    rw [hXdef, foldedState_eq]; exact Replay.SameReadings.foldl z _ _ _ (Replay.sameReadings_init _ _)
  have hG : AgreeAbove L (horizonOf L) G (rebindState SL (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) := by
    rw [hGX]
    exact AgreeAbove.rebind ((AgreeAbove.of_sameReadings hXs).trans (restore_agrees z T₀ L cut As Rs ws n).symm) SL SL
      (fun _ _ => rfl)
  -- `slept_by_day` below the ledger day is the folded lines'
  have hinv : Replay.SleptInv (Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs)))
      (foldedState z As Rs) := by
    rw [foldedState_eq]
    exact Replay.sleptInv_foldl z _ _ _ _ (Replay.sleptInv_init _ _)
  have hSLb : ∀ d, d < L →
      SL d = Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs)) d := by
    intro d hdL
    have e1 : Replay.sleptByDay z KW (foldedSurvivors As Rs)
        = Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs) :=
      sleptByDay_congr z KW (foldedIndex z As Rs) _ (fun e he _ =>
        hI1 e.t.val (List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist As Rs).subset he, by simp [entryInstants]⟩))
    have hnone : Replay.KMap.get (Replay.sleptByDay z KW sv) d = none := by
      rw [kmap_get_eq]
      have hf : (Replay.sleptByDay z KW sv).find? (fun p => decide (p.1 = d)) = none := by
        apply List.find?_eq_none.2
        intro p hp
        unfold Replay.sleptByDay at hp
        obtain ⟨e, he, hep⟩ := List.mem_filterMap.1 hp
        cases hs : Replay.sleptOf e with
        | none => rw [hs] at hep; cases hep
        | some s =>
          rw [hs] at hep
          simp only [Option.map_some, Option.some.injEq] at hep
          subst hep
          obtain ⟨h1, h2⟩ := hhb e (hsvB e he)
          have := hI2 _ h1
          simp only [decide_eq_true_eq]
          omega
      rw [hf]; rfl
    rw [hSL, sleptByDay_append, kmap_get_append, e1, hnone]
    cases Replay.KMap.get (Replay.sleptByDay z (foldedIndex z As Rs) (foldedSurvivors As Rs)) d <;> rfl
  -- the tail names no key below the horizons, on the whole index
  have hpre : ∀ pre post, sv = pre ++ post →
      pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)
        = pre.foldl (Replay.stepWith z (dayOf z KW) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n) := by
    intro pre post hs
    refine resume_fold_congr z (dayOf z kw) (dayOf z KW) sl _ _ pre
      (fun pre' e' post' h' => hsteps pre' e' (post' ++ post) (by rw [hs, h']; simp)) (fun q hq => ?_)
    exact (hI2 q (by rwa [hL] at hq)).symm
  have hkeys : ∀ pre e post, sv = pre ++ e :: post →
      ∀ x ∈ Replay.effectsWith z (dayOf z KW) SL (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G) e,
        keyAtOrAbove L (horizonOf L) x.key = true := by
    intro pre e post hs x hx
    have hc := stepCheck_none z (dayOf z kw) sl _ _ e (hsteps pre e post hs)
    rw [hL] at hc
    obtain ⟨hhq, -, hck⟩ := hc
    have hm : (pre.foldl (Replay.stepWith z (dayOf z KW) SL) G).machine
        = (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)).machine := by
      rw [(AgreeAbove.foldl z _ _ pre hG).machine, foldl_rebind z (dayOf z KW) SL sl pre _ hPS, hpre pre (e :: post) hs]
      rfl
    rw [effectsWith_machine z _ _ _ _ e hm] at hx
    have hmem : x.key ∈ (Replay.effectsWith z (dayOf z KW) SL
        (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOfEntries z T₀ L cut As Rs ws) n)) e).map
          Replay.Effect.key := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [effectsWith_keys z (dayOf z KW) sl SL _ e (pendingStart_foldl z _ _ pre _ hPS),
      effectsWith_congr (dayOf z KW) (dayOf z kw) z sl _ e (fun q hq => hI2 q (hhq q hq))] at hmem
    obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hmem
    rw [← hyk]; exact hck y hy
  have hbelowF := foldl_below z (dayOf z KW) SL L (horizonOf L) sv G hkeys
  have hframe : ∀ item inst d, d < horizonOf L →
      (sv.foldl (Replay.stepWith z (dayOf z KW) SL) G).valueAt (.instDate item inst d)
        = G.valueAt (.instDate item inst d) := by
    intro item inst d hdH
    apply foldl_frame
    intro pre e post hs x hx hxk
    have := hkeys pre e post hs x hx
    rw [hxk] at this
    simp [keyAtOrAbove] at this
    omega
  -- the pending observation
  have hpendF : PendingAbove L (foldedState z (As ++ (Rs ++ B')) []).machine := by
    intro o ho
    rw [← hAgree.machine] at ho
    rcases foldl_pending z (dayOf z kw) sl sv _ o ho with h | ⟨e, he, hed⟩
    · have hm : (restore (ckptOfEntries z T₀ L cut As Rs ws) n).machine = (foldedState z As Rs).machine :=
        ckpt_machine z T₀ L cut As Rs ws
      rw [hm] at h
      exact hpend o h
    · rw [hed]; exact (hhb e (hsvB e he)).2
  -- the headers
  have hHS : ∀ d, d < L → (foldedHeaders z (As ++ (Rs ++ B')) []).filter (fun p => decide (p.1 = d))
      = (foldedHeaders z As Rs).filter (fun p => decide (p.1 = d)) := by
    intro d hdL
    rw [hHdr, List.filter_append]
    have hN : (unsettled (ckptOfEntries z T₀ L cut As Rs ws).settled (Rs ++ B')).Pairwise
        (fun x y => x.line < y.line) := ((List.pairwise_append.1 hd).2.1).sublist List.filter_sublist
    have htail := tailHeadersSpec_eq (dayOf z kw) (ckptOfEntries z T₀ L cut As Rs ws).settled
      (unsettled (ckptOfEntries z T₀ L cut As Rs ws).settled (Rs ++ B')) hN (Rs ++ B') [] (by simp)
    simp only [List.length_nil] at htail
    rw [tailHeaders_eq_spec, htail, ← hsv]
    have hnil : ((Rs ++ B').map (fun e => (dayOf z kw e.t.val, HeaderRec.of e (!decide (e ∈ sv))))).filter
        (fun p => decide (p.1 = d)) = [] := List.filter_eq_nil_iff.2 (fun p hp => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      have := (hhb e he).2
      simp only [decide_eq_true_eq]
      omega)
    rw [hnil, List.append_nil]
  refine ⟨⟨fun d hdL => ?_, fun d hdL => ?_, fun d hdL => ?_, fun d hdL => ?_, fun d hdL => ?_, fun d hdL => ?_,
    fun d hdL => ?_, fun d i hdH => ?_, fun d i hdH => ?_, fun k d hk hdH => ?_⟩, hpendF, hHS⟩
  · rw [hF, (valueAt_day_view (hbelowF.1 d hdL)).1, hGX]; exact hXs.days d
  · rw [hF, (valueAt_day_view (hbelowF.1 d hdL)).2.1, hGX]; exact hXs.seams d
  · rw [hF, (valueAt_day_view (hbelowF.1 d hdL)).2.2.1, hGX]
    show (X.energy.map (rebindObs SL)).filter _ = _
    rw [hXs.energy]
    exact filter_rebind_below SL _ L d hdL hSLb _ hinv.1
  · rw [hF, (valueAt_day_view (hbelowF.1 d hdL)).2.2.2.1, hGX]
    show X.durations.filter _ = _
    rw [hXs.durations]
  · rw [hF, (valueAt_day_view (hbelowF.1 d hdL)).2.2.2.2.1, hGX]
    show X.interrupts.filter _ = _
    rw [hXs.interrupts]
  · rw [hF, filter_fst_eq_of_snd _ _ d (valueAt_day_view (hbelowF.1 d hdL)).2.2.2.2.2.1, hGX]
    show X.demotions.filter _ = _
    rw [hXs.demotions]
  · rw [hF, filter_fst_eq_of_snd _ _ d (valueAt_day_view (hbelowF.1 d hdL)).2.2.2.2.2.2, hGX]
    show X.closes.filter _ = _
    rw [hXs.closes]
  · rw [hF, valueAt_itemDay_get (hbelowF.2.1 i d hdH), hGX]; exact hXs.itemDays (d, i)
  · rw [hF, valueAt_doneDate_get (hbelowF.2.2 i d hdH), hGX]; exact hXs.doneDates (d, i)
  · obtain ⟨item, inst⟩ := k
    rw [hF, valueAt_instDate_get hk (hframe item inst d hdH), hGX]; exact hXs.instances (item, inst)

/-- **Law 4, two-run**: what Rust stored is still true. -/
theorem resume_keeps_the_sealed_records (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool)
    (p : Option Seal.Policy) (x : Seal.Answer × Option Seal.Resealed)
    (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b) (hs : Seal.sealable z T₀ L a r = true)
    (h : Seal.resume z T (Seal.ckptOf z T₀ L a r) b term p = .ok x) :
    Seal.dayRecordsBelow z T₀ L (a ++ b) = Seal.dayRecordsBelow z T₀ L a ∧
    Seal.windowRecordsBelow z T₀ L (a ++ b) = Seal.windowRecordsBelow z T₀ L a := by
  obtain ⟨t, rfl⟩ := hr
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hd : (Log.lineEntries a ++ (Log.lineEntries r ++ Log.lineEntries t)).Pairwise (fun x y => x.line < y.line) := by
    have := (lineEntries_pairwise 1 (a ++ (r ++ t)) hc).1
    rwa [hLE, hLE] at this
  have hrun : ∃ run, resumeRun z T (ckptOf z T₀ L a r) (r ++ t) = .ok run := by
    unfold resume at h
    cases hr' : resumeRun z T (ckptOf z T₀ L a r) (r ++ t) with
    | error e => rw [hr'] at h; simp at h
    | ok run => exact ⟨run, rfl⟩
  obtain ⟨run, hrun⟩ := hrun
  obtain ⟨-, -, -, hg, hfold, hhdr, -⟩ := resumeRun_ok z T _ _ run hrun
  rw [hLE r t] at hg hfold hhdr
  have hs' := hs
  unfold sealable sealableEntries at hs'
  simp only [Bool.and_eq_true, beq_iff_eq] at hs'
  obtain ⟨⟨⟨⟨-, -⟩, hmd⟩, hdays⟩, hwins⟩ := hs'
  have hpend : PendingAbove L (foldedState z (Log.lineEntries a) (Log.lineEntries r)).machine := by
    intro o ho
    have hmem : o.day ∈ machineDays (foldedState z (Log.lineEntries a) (Log.lineEntries r)).machine := by
      unfold machineDays; rw [ho]; simp
    simpa using List.all_eq_true.1 hmd o.day hmem
  obtain ⟨sv, hsv⟩ : ∃ sv, sv = survivors (unsettled (ckptOf z T₀ L a r).settled
      (Log.lineEntries r ++ Log.lineEntries t)) := ⟨_, rfl⟩
  obtain ⟨kw, hkw⟩ : ∃ kw, kw = tailIndex z (ckptOf z T₀ L a r) sv := ⟨_, rfl⟩
  obtain ⟨sl, hsl⟩ : ∃ sl, sl = tailSlept z (ckptOf z T₀ L a r) kw sv := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (ckptOf z T₀ L a r).items.length + (ckptOf z T₀ L a r).openDays.length
      + (Log.lineEntries r ++ Log.lineEntries t).length := ⟨_, rfl⟩
  rw [← hsv, ← hkw, ← hsl, ← hn] at hfold
  rw [← hsv, ← hkw] at hhdr
  have hsteps := (tailFold_snd z (dayOf z kw) sl _ sv (restore (ckptOf z T₀ L a r) n, none) hfold).2
  obtain ⟨hAB, hPF, hHS⟩ := resume_below z T₀ L a.length _ _ _ (Log.lineWarnings a) n hd _ rfl sv hsv hg kw hkw sl
    hsl hsteps hhdr hpend
  constructor
  · show dayRecordsOfEntries z 0 L (Log.lineEntries (a ++ (r ++ t))) = dayRecordsOfEntries z 0 L (Log.lineEntries a)
    rw [← hdays, hLE a (r ++ t), hLE r t]
    exact daysIn_below (allKeyed_foldedState _ _ _) (allKeyed_foldedState _ _ _) hAB _ _ hHS hPF hpend
  · show windowRecordsOfEntries z 0 (horizonOf L) (Log.lineEntries (a ++ (r ++ t)))
      = windowRecordsOfEntries z 0 (horizonOf L) (Log.lineEntries a)
    rw [← hwins, hLE a (r ++ t), hLE r t]
    exact windowsIn_below (allKeyed_foldedState _ _ _) (allKeyed_foldedState _ _ _) hAB

end Seal
end Tm
