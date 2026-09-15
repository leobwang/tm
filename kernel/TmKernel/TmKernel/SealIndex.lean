import TmKernel.SealResume
/-! # The day index as lists: sorting separated blocks, dedup runs, the stored suffix (W2) -/
namespace Tm
namespace Seal

open Replay (sortWakes dedupFrom keptStep keptWakes keptFrom lastWakeLe)

/-! ## On the clock -/

/-- **Two instants more than three days apart have different local dates**, under every zone table (offsets are under
a day). -/
theorem localDate_ne_of_far (z : Cal.Tz) (a w : Cal.Instant) (h : a.sec + fenceSec < w.sec) :
    Cal.localDate z a ≠ Cal.localDate z w := by
  have ha := Cal.localDate_near_the_utc_date z a
  have hw := Cal.localDate_near_the_utc_date z w
  unfold fenceSec at h
  intro heq
  omega

/-- **More than three days apart is more than a day of chrono's duration**, on representable nanoseconds. -/
theorem duration_of_far (a b : Cal.Instant) (ha : a.ns < 2000000000) (hb : b.ns < 2000000000)
    (h : a.sec + fenceSec < b.sec) : 86400 ≤ (Cal.durationBetween a b).1 := by
  obtain ⟨adj, hadj, -, heq, h0, h1⟩ := Cal.durationBetween_total a b
  unfold fenceSec at h
  omega

theorem ns_lt_of_wf (i : Cal.Instant) (h : i.wf = true) : i.ns < 2000000000 := by
  simp only [Cal.Instant.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- **An instant whose last wake is more than three days back reads its own date.** -/
theorem dayOf_of_far (z : Cal.Tz) (kw : List Cal.Instant) (q : Cal.Instant) (hq : q.ns < 2000000000)
    (hkw : ∀ v ∈ kw, v.ns < 2000000000) (h : ∀ v, Replay.lastWakeLe kw q = some v → v.sec + fenceSec < q.sec) :
    Replay.dayOf z kw q = Cal.localDate z q :=
  Replay.dayOf_without_a_recent_wake_is_the_local_date z kw q (fun w hw =>
    duration_of_far w q (hkw w (Replay.lastWakeLe_le kw q w hw).2) hq (h w hw))

/-- **The head second bounds the day**: an instant before `headSec L` has a date before `L`, and so does every wake
at or before it. -/
theorem localDate_lt_of_head (z : Cal.Tz) (L : Nat) (q : Cal.Instant) (h : q.sec < headSec L) :
    Cal.localDate z q < L := by
  have hq := Cal.localDate_near_the_utc_date z q
  unfold headSec at h
  have : q.sec / 86400 + 1 < L := by
    rcases Nat.lt_or_ge L 1 with hL | hL
    · omega
    · have : q.sec / 86400 < L - 1 := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      omega
  omega

theorem dayOf_lt_of_head (z : Cal.Tz) (L : Nat) (kw : List Cal.Instant) (q : Cal.Instant) (h : q.sec < headSec L) :
    Replay.dayOf z kw q < L := by
  unfold Replay.dayOf
  cases hw : Replay.lastWakeLe kw q with
  | none => exact localDate_lt_of_head z L q h
  | some w =>
    simp only
    have hle := (Replay.lastWakeLe_le kw q w hw).1
    rw [Cal.Instant.le_iff] at hle
    split
    · exact localDate_lt_of_head z L w (by omega)
    · exact localDate_lt_of_head z L q h


/-! ## As lists -/


theorem sortWakes_eq_of_perm {l₁ l₂ : List Cal.Instant} (h : l₁.Perm l₂) : sortWakes l₁ = sortWakes l₂ :=
  Replay.eq_of_perm_of_sorted ((Replay.sortWakes_perm l₁).trans (h.trans (Replay.sortWakes_perm l₂).symm))
    (Replay.sortWakes_sorted l₁) (Replay.sortWakes_sorted l₂)

theorem sortWakes_of_sorted (l : List Cal.Instant) (h : l.Pairwise (· ≤ ·)) : sortWakes l = l :=
  Replay.eq_of_perm_of_sorted (Replay.sortWakes_perm l) (Replay.sortWakes_sorted l) h

theorem sortWakes_three (lo mid hi : List Cal.Instant) (h1 : ∀ a ∈ lo, ∀ b ∈ mid, a < b)
    (h2 : ∀ a ∈ lo, ∀ c ∈ hi, a < c) (h3 : ∀ b ∈ mid, ∀ c ∈ hi, b < c) :
    sortWakes (lo ++ mid ++ hi) = sortWakes lo ++ sortWakes mid ++ sortWakes hi := by
  rw [Replay.sortWakes_append_of_later (lo ++ mid) hi (fun a ha c hc => by
    rcases List.mem_append.1 ha with ha | ha
    · exact h2 a ha c hc
    · exact h3 a ha c hc), Replay.sortWakes_append_of_later lo mid h1]

/-- One step of the dedup, unfolded. -/
theorem dedupFrom_cons (z : Cal.Tz) (prev : Option Cal.Instant) (w : Cal.Instant) (ws : List Cal.Instant) :
    dedupFrom z prev (w :: ws) = match prev with
      | some k => if Cal.localDate z w = Cal.localDate z k then dedupFrom z prev ws else w :: dedupFrom z (some w) ws
      | none => w :: dedupFrom z (some w) ws := by
  unfold dedupFrom
  rw [List.foldl_cons]
  cases prev with
  | none =>
    simp only [keptStep]
    rw [Replay.foldl_keptStep_acc z ws (some w) [w]]
    simp
  | some k =>
    simp only [keptStep]
    split
    · rfl
    · rw [Replay.foldl_keptStep_acc z ws (some w) [w]]
      simp

theorem dedupFrom_nil (z : Cal.Tz) (prev : Option Cal.Instant) : dedupFrom z prev [] = [] := rfl

/-- **No two consecutive wakes on one local date**, continuing a run whose last kept wake is `prev`. -/
def noRuns (z : Cal.Tz) : Option Cal.Instant → List Cal.Instant → Bool
  | _, [] => true
  | none, w :: ws => noRuns z (some w) ws
  | some k, w :: ws => decide (Cal.localDate z w ≠ Cal.localDate z k) && noRuns z (some w) ws

theorem dedupFrom_of_noRuns (z : Cal.Tz) : ∀ (prev : Option Cal.Instant) (l : List Cal.Instant),
    noRuns z prev l = true → dedupFrom z prev l = l
  | _, [], _ => rfl
  | none, w :: ws, h => by
    rw [dedupFrom_cons]
    simp only [noRuns] at h
    rw [dedupFrom_of_noRuns z (some w) ws h]
  | some k, w :: ws, h => by
    rw [dedupFrom_cons]
    simp only [noRuns, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only
    rw [if_neg h.1, dedupFrom_of_noRuns z (some w) ws h.2]

/-- The last kept wake of a dedup, as the fold carries it. -/
def lastKept (z : Cal.Tz) (prev : Option Cal.Instant) (l : List Cal.Instant) : Option Cal.Instant :=
  (l.foldl (keptStep z) (prev, [])).1

theorem lastKept_cons (z : Cal.Tz) (prev : Option Cal.Instant) (w : Cal.Instant) (ws : List Cal.Instant) :
    lastKept z prev (w :: ws) = match prev with
      | some k => if Cal.localDate z w = Cal.localDate z k then lastKept z prev ws else lastKept z (some w) ws
      | none => lastKept z (some w) ws := by
  unfold lastKept
  rw [List.foldl_cons]
  cases prev with
  | none =>
    simp only [keptStep]
    rw [Replay.foldl_keptStep_acc z ws (some w) [w]]
  | some k =>
    simp only [keptStep]
    split
    · rfl
    · rw [Replay.foldl_keptStep_acc z ws (some w) [w]]

theorem noRuns_dedupFrom (z : Cal.Tz) : ∀ (l : List Cal.Instant) (prev : Option Cal.Instant),
    noRuns z prev (dedupFrom z prev l) = true
  | [], _ => rfl
  | w :: ws, none => by
    rw [dedupFrom_cons]; simp only [noRuns]; exact noRuns_dedupFrom z ws (some w)
  | w :: ws, some k => by
    rw [dedupFrom_cons]
    simp only
    by_cases hne : Cal.localDate z w = Cal.localDate z k
    · rw [if_pos hne]; exact noRuns_dedupFrom z ws (some k)
    · rw [if_neg hne]
      simp only [noRuns, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hne, noRuns_dedupFrom z ws (some w)⟩

theorem dedupFrom_dedupFrom (z : Cal.Tz) (prev : Option Cal.Instant) (l : List Cal.Instant) :
    dedupFrom z prev (dedupFrom z prev l) = dedupFrom z prev l :=
  dedupFrom_of_noRuns z prev _ (noRuns_dedupFrom z l prev)

/-- A dropped prefix of a list without runs has none, from any start. -/
theorem noRuns_drop (z : Cal.Tz) : ∀ (l : List Cal.Instant) (prev : Option Cal.Instant) (i : Nat),
    noRuns z prev l = true → noRuns z none (l.drop i) = true
  | [], _, _, _ => by simp [noRuns]
  | w :: ws, prev, 0, h => by
    simp only [List.drop_zero, noRuns]
    cases prev with
    | none => simpa [noRuns] using h
    | some k => simp only [noRuns, Bool.and_eq_true] at h; exact h.2
  | w :: ws, prev, i + 1, h => by
    simp only [List.drop_succ_cons]
    cases prev with
    | none => simp only [noRuns] at h; exact noRuns_drop z ws (some w) i h
    | some k => simp only [noRuns, Bool.and_eq_true] at h; exact noRuns_drop z ws (some w) i h.2

/-- **A start far from every wake does not change the dedup**: the first wake is kept either way. -/
theorem dedupFrom_far (z : Cal.Tz) (x y : Option Cal.Instant) (ws : List Cal.Instant)
    (hx : ∀ a ∈ x, ∀ w ∈ ws, a.sec + fenceSec < w.sec) (hy : ∀ a ∈ y, ∀ w ∈ ws, a.sec + fenceSec < w.sec) :
    dedupFrom z x ws = dedupFrom z y ws := by
  cases ws with
  | nil => rfl
  | cons w rest =>
    have hkeep : ∀ (o : Option Cal.Instant), (∀ a ∈ o, ∀ w' ∈ w :: rest, a.sec + fenceSec < w'.sec) →
        dedupFrom z o (w :: rest) = w :: dedupFrom z (some w) rest := by
      intro o ho
      rw [dedupFrom_cons]
      cases o with
      | none => rfl
      | some k =>
        have hne := localDate_ne_of_far z k w (ho k rfl w List.mem_cons_self)
        simp only
        rw [if_neg (Ne.symm hne)]
    rw [hkeep x hx, hkeep y hy]

/-! ### The stored suffix -/

theorem sec_le_of_le {a b : Cal.Instant} (h : a ≤ b) : a.sec ≤ b.sec := by
  rw [Cal.Instant.le_iff] at h; omega

theorem filter_sec_split (s : Nat) : ∀ (kw : List Cal.Instant), kw.Pairwise (· ≤ ·) →
    kw.filter (fun w => decide (w.sec < s)) ++ kw.filter (fun w => decide (s ≤ w.sec)) = kw
  | [], _ => rfl
  | x :: rest, hs => by
    have ih := filter_sec_split s rest hs.of_cons
    by_cases hx : x.sec < s
    · simp only [List.filter_cons, hx, decide_true, if_true, List.cons_append]
      have : decide (s ≤ x.sec) = false := by simp; omega
      rw [this]; simp only [Bool.false_eq_true, if_false]; rw [ih]
    · have hall : ∀ y ∈ rest, s ≤ y.sec := fun y hy => by
        have := sec_le_of_le (List.rel_of_pairwise_cons hs hy); omega
      have h1 : rest.filter (fun w => decide (w.sec < s)) = [] :=
        List.filter_eq_nil_iff.2 (fun y hy => by have := hall y hy; simp; omega)
      have h2 : rest.filter (fun w => decide (s ≤ w.sec)) = rest :=
        List.filter_eq_self.2 (fun y hy => by simpa using hall y hy)
      simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, if_false, h1, List.nil_append]
      have : decide (s ≤ x.sec) = true := by simp; omega
      rw [this, if_pos rfl, h2]

/-- **The stored wakes are a suffix of the index**, after a prefix of wakes at or before them, starting, when anything
precedes them, with a wake before the head second. -/
theorem storedWakes_suffix (L : Nat) (kw : List Cal.Instant) (hs : kw.Pairwise (· ≤ ·)) :
    ∃ P, kw = P ++ storedWakes L kw ∧ (∀ p ∈ P, ∀ y ∈ storedWakes L kw, p ≤ y) ∧
      (P ≠ [] → ∃ h rest, storedWakes L kw = h :: rest ∧ h.sec < headSec L) := by
  have hsplit := filter_sec_split (headSec L) kw hs
  unfold storedWakes
  generalize hF : kw.filter (fun w => decide (w.sec < headSec L)) = F at hsplit
  generalize hG : kw.filter (fun w => decide (headSec L ≤ w.sec)) = G at hsplit
  rcases List.eq_nil_or_concat F with hF0 | ⟨F', h, hFe⟩
  · subst hF0
    refine ⟨[], by simpa using hsplit.symm, by simp, by simp⟩
  · rw [List.concat_eq_append] at hFe
    subst hFe
    have hh : h.sec < headSec L := by
      have : h ∈ kw.filter (fun w => decide (w.sec < headSec L)) := by rw [hF]; simp
      simpa using (List.mem_filter.1 this).2
    refine ⟨F', ?_, ?_, fun _ => ⟨h, G, by simp, hh⟩⟩
    · rw [List.getLast?_concat, Option.toList_some, ← hsplit]; simp
    · intro p hp y hy
      rw [← hsplit] at hs
      simp only [List.getLast?_concat, Option.toList_some, List.singleton_append] at hy
      have hs' : (F' ++ (h :: G)).Pairwise (· ≤ ·) := by simpa using hs
      exact (List.pairwise_append.1 hs').2.2 p hp y hy

theorem lastWakeLe_isSome (Y : List Cal.Instant) (q y : Cal.Instant) (hy : y ∈ Y) (hyq : y ≤ q) :
    (lastWakeLe Y q).isSome = true := by
  induction Y with
  | nil => cases hy
  | cons x xs ih =>
    rw [Replay.lastWakeLe_cons]
    rcases List.mem_cons.1 hy with rfl | hy
    · cases lastWakeLe xs q <;> simp [hyq]
    · have := ih hy
      cases h : lastWakeLe xs q <;> simp_all

/-- **A wake at or before `q` in the later part decides `q`'s last wake.** -/
theorem lastWakeLe_append (X Y : List Cal.Instant) (q : Cal.Instant) :
    lastWakeLe (X ++ Y) q = (lastWakeLe Y q).or (lastWakeLe X q) := by
  conv => lhs; unfold lastWakeLe
  rw [List.foldl_append, Replay.foldl_lastWake_or]; rfl

theorem lastWakeLe_append_of_mem (X Y : List Cal.Instant) (q y : Cal.Instant) (hy : y ∈ Y) (hyq : y ≤ q) :
    lastWakeLe (X ++ Y) q = lastWakeLe Y q := by
  have hs := lastWakeLe_isSome Y q y hy hyq
  rw [lastWakeLe_append]
  cases h : lastWakeLe Y q with
  | none => rw [h] at hs; cases hs
  | some v => rfl

/-! ### The dedup in pieces -/

theorem keptWakes_eq (z : Cal.Tz) (ws : List Cal.Instant) : keptWakes z ws = dedupFrom z none (sortWakes ws) := rfl

theorem lastKept_append (z : Cal.Tz) (prev : Option Cal.Instant) (V U : List Cal.Instant) :
    lastKept z prev (V ++ U) = lastKept z (lastKept z prev V) U := by
  unfold lastKept
  rw [List.foldl_append, Replay.foldl_keptStep_acc z U]

theorem dedupFrom_append' (z : Cal.Tz) (prev : Option Cal.Instant) (V U : List Cal.Instant) :
    dedupFrom z prev (V ++ U) = dedupFrom z prev V ++ dedupFrom z (lastKept z prev V) U :=
  Replay.dedupFrom_append z prev V U

theorem lastKept_mem (z : Cal.Tz) : ∀ (V : List Cal.Instant) (prev : Option Cal.Instant) (a : Cal.Instant),
    lastKept z prev V = some a → prev = some a ∨ a ∈ V
  | [], _, _, h => Or.inl h
  | w :: ws, prev, a, h => by
    rw [lastKept_cons] at h
    cases prev with
    | none =>
      rcases lastKept_mem z ws (some w) a h with h | h
      · exact Or.inr (by simp at h; simp [h])
      · exact Or.inr (List.mem_cons_of_mem _ h)
    | some k =>
      simp only at h
      split at h
      · rcases lastKept_mem z ws (some k) a h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases lastKept_mem z ws (some w) a h with h | h
        · exact Or.inr (by simp at h; simp [h])
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_of_mem_dedupFrom (z : Cal.Tz) (prev : Option Cal.Instant) (V : List Cal.Instant) (x : Cal.Instant)
    (h : x ∈ dedupFrom z prev V) : x ∈ V := by
  unfold dedupFrom at h
  rw [List.mem_reverse] at h
  rcases Replay.mem_foldl_keptStep z V _ x h with h | h
  · simp at h
  · exact h

theorem mem_sortWakes (V : List Cal.Instant) (x : Cal.Instant) : x ∈ sortWakes V ↔ x ∈ V :=
  (Replay.sortWakes_perm V).mem_iff

theorem mem_keptWakes (z : Cal.Tz) (V : List Cal.Instant) (x : Cal.Instant) (h : x ∈ keptWakes z V) : x ∈ V :=
  (mem_sortWakes V x).1 (mem_of_mem_dedupFrom z none _ x h)

theorem lt_of_lt_of_le' {a b c : Cal.Instant} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [Cal.Instant.lt_iff] at *; rw [Cal.Instant.le_iff] at h2; omega

theorem lt_of_far {a b : Cal.Instant} (h : a.sec + fenceSec < b.sec) : a < b := by
  rw [Cal.Instant.lt_iff]; unfold fenceSec at h; omega

theorem far_of_lt_of_far {a b c : Cal.Instant} (h1 : a < b) (h2 : b.sec + fenceSec < c.sec) : a.sec + fenceSec < c.sec := by
  rw [Cal.Instant.lt_iff] at h1; omega

/-! ## I1: tail wakes between the folded low instants and, three days short, the folded future ones leave every folded
instant's day alone -/

/-- **The folded instants keep their days** (§9.3's G2 as a law): when every surviving tail wake is after every folded
instant `P` marks and more than three days before every other folded instant, adding the tail's wakes to the index
changes no folded instant's day. -/
theorem dayOf_folded_agrees (z : Cal.Tz) (P : Cal.Instant → Bool) (QA WA WB : List Cal.Instant)
    (hWA : ∀ w ∈ WA, w ∈ QA) (hns : ∀ q ∈ QA ++ WB, q.ns < 2000000000)
    (hsep : ∀ w ∈ WB, ∀ q ∈ QA, (P q = true → q < w) ∧ (P q = false → w.sec + fenceSec < q.sec))
    (q : Cal.Instant) (hq : q ∈ QA) :
    Replay.dayOf z (keptWakes z (WA ++ WB)) q = Replay.dayOf z (keptWakes z WA) q := by
  cases WB with
  | nil => rw [List.append_nil]
  | cons b WB' =>
    have hsepb := hsep b List.mem_cons_self
    let lo := WA.filter P
    let hi := WA.filter (fun x => !P x)
    have hlo : ∀ a ∈ lo, ∀ w ∈ b :: WB', a < w := fun a ha w hw =>
      (hsep w hw a (hWA a (List.mem_filter.1 ha).1)).1 (List.mem_filter.1 ha).2
    have hhi : ∀ w ∈ b :: WB', ∀ c ∈ hi, w.sec + fenceSec < c.sec := fun w hw c hc =>
      (hsep w hw c (hWA c (List.mem_filter.1 hc).1)).2 (by simpa using (List.mem_filter.1 hc).2)
    have hlohi : ∀ a ∈ lo, ∀ c ∈ hi, a.sec + fenceSec < c.sec := fun a ha c hc =>
      far_of_lt_of_far (hlo a ha b List.mem_cons_self) (hhi b List.mem_cons_self c hc)
    have hperm : (WA ++ (b :: WB')).Perm (lo ++ (b :: WB') ++ hi) := by
      have h1 : (lo ++ hi).Perm WA := List.filter_append_perm P WA
      refine ((h1.symm).append_right _).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    have hs1 : sortWakes (WA ++ (b :: WB')) = sortWakes lo ++ sortWakes (b :: WB') ++ sortWakes hi := by
      rw [sortWakes_eq_of_perm hperm]
      exact sortWakes_three lo (b :: WB') hi hlo (fun a ha c hc => lt_of_far (hlohi a ha c hc))
        (fun w hw c hc => lt_of_far (hhi w hw c hc))
    have hs2 : sortWakes WA = sortWakes lo ++ sortWakes hi := by
      rw [sortWakes_eq_of_perm (List.filter_append_perm P WA).symm]
      exact Replay.sortWakes_append_of_later lo hi (fun a ha c hc => lt_of_far (hlohi a ha c hc))
    have hfarB : ∀ a ∈ lastKept z (lastKept z none (sortWakes lo)) (sortWakes (b :: WB')), ∀ c ∈ sortWakes hi,
        a.sec + fenceSec < c.sec := by
      intro a ha c hc
      rcases lastKept_mem z _ _ a ha with ha | ha
      · rcases lastKept_mem z _ none a ha with ha | ha
        · cases ha
        · exact hlohi a ((mem_sortWakes lo a).1 ha) c ((mem_sortWakes hi c).1 hc)
      · exact hhi a ((mem_sortWakes _ a).1 ha) c ((mem_sortWakes hi c).1 hc)
    have hfarA : ∀ a ∈ lastKept z none (sortWakes lo), ∀ c ∈ sortWakes hi, a.sec + fenceSec < c.sec := by
      intro a ha c hc
      rcases lastKept_mem z _ none a ha with ha | ha
      · cases ha
      · exact hlohi a ((mem_sortWakes lo a).1 ha) c ((mem_sortWakes hi c).1 hc)
    have hD := dedupFrom_far z _ _ (sortWakes hi) hfarB hfarA
    have hKW : keptWakes z (WA ++ (b :: WB')) = dedupFrom z none (sortWakes lo)
        ++ dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes (b :: WB'))
        ++ dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes hi) := by
      rw [keptWakes_eq, hs1, dedupFrom_append', dedupFrom_append', lastKept_append, hD]
    have hKWA : keptWakes z WA = dedupFrom z none (sortWakes lo)
        ++ dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes hi) := by
      rw [keptWakes_eq, hs2, dedupFrom_append']
    have hq_ns : q.ns < 2000000000 := hns q (List.mem_append_left _ hq)
    rw [hKW, hKWA]
    generalize hK1 : dedupFrom z none (sortWakes lo) = K1 at *
    generalize hDB : dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes (b :: WB')) = DB at *
    generalize hDH : dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes hi) = DH at *
    have mK1 : ∀ v ∈ K1, v ∈ lo := fun v hv => by
      rw [← hK1] at hv; exact (mem_sortWakes lo v).1 (mem_of_mem_dedupFrom z _ _ v hv)
    have mDB : ∀ v ∈ DB, v ∈ b :: WB' := fun v hv => by
      rw [← hDB] at hv; exact (mem_sortWakes _ v).1 (mem_of_mem_dedupFrom z _ _ v hv)
    have mDH : ∀ v ∈ DH, v ∈ hi := fun v hv => by
      rw [← hDH] at hv; exact (mem_sortWakes hi v).1 (mem_of_mem_dedupFrom z _ _ v hv)
    cases hPq : P q with
    | true =>
      have hlt : ∀ w ∈ b :: WB', q < w := fun w hw => (hsep w hw q hq).1 hPq
      unfold Replay.dayOf
      rw [Replay.lastWakeLe_append_of_later (K1 ++ DB) DH q (fun c hc => Cal.Instant.lt_trans (hlt b List.mem_cons_self)
          (lt_of_far (hhi b List.mem_cons_self c (mDH c hc)))),
        Replay.lastWakeLe_append_of_later K1 DB q (fun w hw => hlt w (mDB w hw)),
        Replay.lastWakeLe_append_of_later K1 DH q (fun c hc => Cal.Instant.lt_trans (hlt b List.mem_cons_self)
          (lt_of_far (hhi b List.mem_cons_self c (mDH c hc))))]
    | false =>
      have hfar : ∀ w ∈ b :: WB', w.sec + fenceSec < q.sec := fun w hw => (hsep w hw q hq).2 hPq
      unfold Replay.dayOf
      rw [lastWakeLe_append (K1 ++ DB) DH, lastWakeLe_append K1 DH]
      cases hl : Replay.lastWakeLe DH q with
      | some v => rfl
      | none =>
        simp only [Option.none_or]
        have e1 := dayOf_of_far z (K1 ++ DB) q hq_ns (fun v hv => by
            rcases List.mem_append.1 hv with h | h
            · exact hns v (List.mem_append_left _ (hWA v (List.mem_filter.1 (mK1 v h)).1))
            · exact hns v (List.mem_append_right _ (mDB v h)))
          (fun v hv => by
            rcases List.mem_append.1 (Replay.lastWakeLe_le _ q v hv).2 with h | h
            · exact far_of_lt_of_far (hlo v (mK1 v h) b List.mem_cons_self) (hfar b List.mem_cons_self)
            · exact hfar v (mDB v h))
        have e2 := dayOf_of_far z K1 q hq_ns (fun v hv => hns v (List.mem_append_left _ (hWA v (List.mem_filter.1 (mK1 v hv)).1)))
          (fun v hv => far_of_lt_of_far (hlo v (mK1 v (Replay.lastWakeLe_le _ q v hv).2) b List.mem_cons_self)
            (hfar b List.mem_cons_self))
        unfold Replay.dayOf at e1 e2
        rw [e1, e2]

/-! ## I2: the stored wakes and the tail's give every tail instant after the head second its day -/

theorem storedWakes_append_of_ge (L : Nat) (X Y : List Cal.Instant) (hY : ∀ c ∈ Y, headSec L ≤ c.sec) :
    storedWakes L (X ++ Y) = storedWakes L X ++ Y := by
  unfold storedWakes
  have h1 : Y.filter (fun w => decide (w.sec < headSec L)) = [] :=
    List.filter_eq_nil_iff.2 (fun c hc => by have := hY c hc; simp; omega)
  have h2 : Y.filter (fun w => decide (headSec L ≤ w.sec)) = Y :=
    List.filter_eq_self.2 (fun c hc => by simpa using hY c hc)
  rw [List.filter_append, List.filter_append, h1, h2, List.append_nil, List.append_assoc]

theorem noRuns_of_far_start (z : Cal.Tz) (x y : Option Cal.Instant) (l : List Cal.Instant) (h : noRuns z x l = true)
    (hy : ∀ a ∈ y, ∀ w ∈ l, a.sec + fenceSec < w.sec) : noRuns z y l = true := by
  cases l with
  | nil => rfl
  | cons w ws =>
    have hrest : noRuns z (some w) ws = true := by
      cases x with
      | none => simpa [noRuns] using h
      | some k => simp only [noRuns, Bool.and_eq_true] at h; exact h.2
    cases y with
    | none => simpa [noRuns] using hrest
    | some a =>
      simp only [noRuns, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Ne.symm (localDate_ne_of_far z a w (hy a rfl w List.mem_cons_self)), hrest⟩

theorem dedupFrom_sorted (z : Cal.Tz) (prev : Option Cal.Instant) (l : List Cal.Instant) (hs : l.Pairwise (· ≤ ·)) :
    (dedupFrom z prev l).Pairwise (· ≤ ·) :=
  hs.sublist (Replay.foldl_keptStep_sublist z l prev)

theorem storedWakes_nil (L : Nat) : storedWakes L [] = [] := rfl

theorem storedWakes_ne_nil (L : Nat) (K : List Cal.Instant) (hK : K ≠ []) : storedWakes L K ≠ [] := by
  unfold storedWakes
  intro h
  have hs := List.append_eq_nil_iff.1 h
  have hF : K.filter (fun w => decide (w.sec < headSec L)) = [] := by
    cases hF : K.filter (fun w => decide (w.sec < headSec L)) with
    | nil => rfl
    | cons a as => rw [hF] at hs; simp at hs
  rw [List.filter_eq_nil_iff] at hF
  rw [List.filter_eq_nil_iff] at hs
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil K hK
  have a1 := hF x hx
  have a2 := hs.2 x hx
  simp at a1 a2
  omega

theorem noRuns_storedWakes (z : Cal.Tz) (L : Nat) (K : List Cal.Instant) (hs : K.Pairwise (· ≤ ·))
    (hK : noRuns z none K = true) : noRuns z none (storedWakes L K) = true := by
  obtain ⟨P0, hP, -, -⟩ := storedWakes_suffix L K hs
  have : storedWakes L K = K.drop P0.length := by
    conv => rhs; rw [hP]
    simp
  rw [this]
  exact noRuns_drop z K none P0.length hK

theorem sorted_storedWakes (L : Nat) (K : List Cal.Instant) (hs : K.Pairwise (· ≤ ·)) :
    (storedWakes L K).Pairwise (· ≤ ·) := by
  obtain ⟨P0, hP, -, -⟩ := storedWakes_suffix L K hs
  rw [hP] at hs
  exact (List.pairwise_append.1 hs).2.1

theorem lastKept_none_eq (z : Cal.Tz) (V : List Cal.Instant) : lastKept z none V = (dedupFrom z none V).getLast? :=
  Replay.dedupFrom_last z V

theorem noRuns_nil_dedup (z : Cal.Tz) (V : List Cal.Instant) : noRuns z none (dedupFrom z none V) = true :=
  noRuns_dedupFrom z V none

/-- **The tail's instants after the head second read their day off the stored wakes and the tail's** (§9.3's
`wakes`, W2): under G2's separation and the head second on the tail's wakes. -/
theorem dayOf_tail_agrees (z : Cal.Tz) (L : Nat) (P : Cal.Instant → Bool) (QA WA WB : List Cal.Instant)
    (hWA : ∀ w ∈ WA, w ∈ QA)
    (hsep : ∀ w ∈ WB, ∀ q ∈ QA, (P q = true → q < w) ∧ (P q = false → w.sec + fenceSec < q.sec))
    (hhead : ∀ w ∈ WB, headSec L ≤ w.sec) (q : Cal.Instant) (hq : headSec L ≤ q.sec) :
    Replay.dayOf z (keptWakes z (WA ++ WB)) q = Replay.dayOf z (keptWakes z (storedWakes L (keptWakes z WA) ++ WB)) q := by
  have hsortedKA := Replay.keptWakes_sorted z WA
  -- the index before the stored wakes is decided by a stored wake at or before `q`
  have hsplit : ∀ (K ST R : List Cal.Instant), K.Pairwise (· ≤ ·) → storedWakes L K = ST →
      Replay.dayOf z (K ++ R) q = Replay.dayOf z (ST ++ R) q := by
    intro K ST R hK hST
    obtain ⟨P0, hP, -, hhd⟩ := storedWakes_suffix L K hK
    rw [hST] at hP hhd
    by_cases hP0 : P0 = []
    · rw [hP, hP0, List.nil_append]
    · obtain ⟨h, rest, hh, hhs⟩ := hhd hP0
      have hle : h ≤ q := by rw [Cal.Instant.le_iff]; omega
      unfold Replay.dayOf
      rw [hP, List.append_assoc, lastWakeLe_append_of_mem P0 (ST ++ R) q h (by rw [hh]; simp) hle]
  cases WB with
  | nil =>
    rw [List.append_nil, List.append_nil]
    have hST : keptWakes z (storedWakes L (keptWakes z WA)) = storedWakes L (keptWakes z WA) := by
      rw [keptWakes_eq, sortWakes_of_sorted _ (sorted_storedWakes L _ hsortedKA)]
      exact dedupFrom_of_noRuns z none _ (noRuns_storedWakes z L _ hsortedKA
        (by rw [keptWakes_eq]; exact noRuns_nil_dedup z _))
    rw [hST]
    have := hsplit (keptWakes z WA) (storedWakes L (keptWakes z WA)) [] hsortedKA rfl
    simpa using this
  | cons b WB' =>
    let lo := WA.filter P
    let hi := WA.filter (fun x => !P x)
    have hlo : ∀ a ∈ lo, ∀ w ∈ b :: WB', a < w := fun a ha w hw =>
      (hsep w hw a (hWA a (List.mem_filter.1 ha).1)).1 (List.mem_filter.1 ha).2
    have hhi : ∀ w ∈ b :: WB', ∀ c ∈ hi, w.sec + fenceSec < c.sec := fun w hw c hc =>
      (hsep w hw c (hWA c (List.mem_filter.1 hc).1)).2 (by simpa using (List.mem_filter.1 hc).2)
    have hlohi : ∀ a ∈ lo, ∀ c ∈ hi, a.sec + fenceSec < c.sec := fun a ha c hc =>
      far_of_lt_of_far (hlo a ha b List.mem_cons_self) (hhi b List.mem_cons_self c hc)
    have hs2 : sortWakes WA = sortWakes lo ++ sortWakes hi := by
      rw [sortWakes_eq_of_perm (List.filter_append_perm P WA).symm]
      exact Replay.sortWakes_append_of_later lo hi (fun a ha c hc => lt_of_far (hlohi a ha c hc))
    have hperm : (WA ++ (b :: WB')).Perm (lo ++ (b :: WB') ++ hi) := by
      have h1 : (lo ++ hi).Perm WA := List.filter_append_perm P WA
      refine ((h1.symm).append_right _).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    have hs1 : sortWakes (WA ++ (b :: WB')) = sortWakes lo ++ sortWakes (b :: WB') ++ sortWakes hi := by
      rw [sortWakes_eq_of_perm hperm]
      exact sortWakes_three lo (b :: WB') hi hlo (fun a ha c hc => lt_of_far (hlohi a ha c hc))
        (fun w hw c hc => lt_of_far (hhi w hw c hc))
    have hfarB : ∀ a ∈ lastKept z (lastKept z none (sortWakes lo)) (sortWakes (b :: WB')), ∀ c ∈ sortWakes hi,
        a.sec + fenceSec < c.sec := by
      intro a ha c hc
      rcases lastKept_mem z _ _ a ha with ha | ha
      · rcases lastKept_mem z _ none a ha with ha | ha
        · cases ha
        · exact hlohi a ((mem_sortWakes lo a).1 ha) c ((mem_sortWakes hi c).1 hc)
      · exact hhi a ((mem_sortWakes _ a).1 ha) c ((mem_sortWakes hi c).1 hc)
    have hfarA : ∀ a ∈ lastKept z none (sortWakes lo), ∀ c ∈ sortWakes hi, a.sec + fenceSec < c.sec := by
      intro a ha c hc
      rcases lastKept_mem z _ none a ha with ha | ha
      · cases ha
      · exact hlohi a ((mem_sortWakes lo a).1 ha) c ((mem_sortWakes hi c).1 hc)
    generalize hK1 : dedupFrom z none (sortWakes lo) = K1
    generalize hDB : dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes (b :: WB')) = DB
    generalize hDH : dedupFrom z (lastKept z none (sortWakes lo)) (sortWakes hi) = DH
    have mK1 : ∀ v ∈ K1, v ∈ lo := fun v hv => by
      rw [← hK1] at hv; exact (mem_sortWakes lo v).1 (mem_of_mem_dedupFrom z _ _ v hv)
    have mDH : ∀ v ∈ DH, v ∈ hi := fun v hv => by
      rw [← hDH] at hv; exact (mem_sortWakes hi v).1 (mem_of_mem_dedupFrom z _ _ v hv)
    have hKW : keptWakes z (WA ++ (b :: WB')) = K1 ++ DB ++ DH := by
      rw [keptWakes_eq, hs1, dedupFrom_append', dedupFrom_append', lastKept_append, dedupFrom_far z _ _ _ hfarB hfarA,
        hK1, hDB, hDH]
    have hKA : keptWakes z WA = K1 ++ DH := by
      rw [keptWakes_eq, hs2, dedupFrom_append', hK1, hDH]
    have hDHhead : ∀ c ∈ DH, headSec L ≤ c.sec := fun c hc => by
      have := hhi b List.mem_cons_self c (mDH c hc); have := hhead b List.mem_cons_self; unfold fenceSec at *; omega
    have hsK1 : K1.Pairwise (· ≤ ·) := by rw [← hK1]; exact dedupFrom_sorted z none _ (Replay.sortWakes_sorted lo)
    have hsDH : DH.Pairwise (· ≤ ·) := by rw [← hDH]; exact dedupFrom_sorted z _ _ (Replay.sortWakes_sorted hi)
    have hST : storedWakes L (keptWakes z WA) = storedWakes L K1 ++ DH := by
      rw [hKA, storedWakes_append_of_ge L K1 DH hDHhead]
    generalize hSK : storedWakes L K1 = SK at hST
    have mSK : ∀ v ∈ SK, v ∈ K1 := fun v hv => by
      obtain ⟨P0, hP, -, -⟩ := storedWakes_suffix L K1 hsK1
      rw [hSK] at hP; rw [hP]; exact List.mem_append_right _ hv
    have hsSK : SK.Pairwise (· ≤ ·) := by rw [← hSK]; exact sorted_storedWakes L K1 hsK1
    have hRsort : sortWakes (SK ++ DH ++ (b :: WB')) = SK ++ sortWakes (b :: WB') ++ DH := by
      have hp2 : (SK ++ DH ++ (b :: WB')).Perm (SK ++ (b :: WB') ++ DH) := by
        simp only [List.append_assoc]; exact List.Perm.append_left _ List.perm_append_comm
      rw [sortWakes_eq_of_perm hp2, sortWakes_three SK (b :: WB') DH
        (fun a ha w hw => hlo a (mK1 a (mSK a ha)) w hw)
        (fun a ha c hc => lt_of_far (hlohi a (mK1 a (mSK a ha)) c (mDH c hc)))
        (fun w hw c hc => lt_of_far (hhi w hw c (mDH c hc))), sortWakes_of_sorted SK hsSK, sortWakes_of_sorted DH hsDH]
    have hlast : lastKept z none SK = lastKept z none (sortWakes lo) := by
      rw [lastKept_none_eq, lastKept_none_eq, hK1, dedupFrom_of_noRuns z none SK (by
        rw [← hSK]; exact noRuns_storedWakes z L K1 hsK1 (by rw [← hK1]; exact noRuns_nil_dedup z _))]
      obtain ⟨P0, hP, -, -⟩ := storedWakes_suffix L K1 hsK1
      rw [hSK] at hP
      by_cases hK1e : K1 = []
      · have : SK = [] := by rw [← hSK, hK1e, storedWakes_nil]
        rw [this, hK1e]
      · have hSKne : SK ≠ [] := by rw [← hSK]; exact storedWakes_ne_nil L K1 hK1e
        rw [hP, List.getLast?_append]
        cases h : SK.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 h) hSKne
        | some v => rfl
    have hKR : keptWakes z (storedWakes L (keptWakes z WA) ++ (b :: WB')) = SK ++ DB ++ DH := by
      rw [hST, keptWakes_eq, hRsort, dedupFrom_append', dedupFrom_append', hlast, hDB,
        dedupFrom_of_noRuns z none SK (by rw [← hSK]; exact noRuns_storedWakes z L K1 hsK1 (by rw [← hK1]; exact noRuns_nil_dedup z _)),
        lastKept_append]
      congr 1
      apply dedupFrom_of_noRuns
      apply noRuns_of_far_start z (lastKept z none (sortWakes lo)) _ DH (by rw [← hDH]; exact noRuns_dedupFrom z _ _)
      intro a ha c hc
      rcases lastKept_mem z _ _ a ha with ha | ha
      · rcases lastKept_mem z _ none a (by rw [← hlast]; exact ha) with ha | ha
        · cases ha
        · exact hlohi a ((mem_sortWakes lo a).1 ha) c (mDH c hc)
      · exact hhi a ((mem_sortWakes _ a).1 ha) c (mDH c hc)
    rw [hKW, hKR, List.append_assoc, List.append_assoc]
    have := hsplit K1 SK (DB ++ DH) hsK1 hSK
    exact this

end Seal
end Tm
