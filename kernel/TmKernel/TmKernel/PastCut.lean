/-!
# PastCut — the cut the owner's D65 draws the replayed past through (stage 6, W-37 track T)

**D65** (2026-09-28, README gaps 3044, 3141 and 3142; parity **P56**): a meeting that paused the
running block is drawn as the WALL ALONE.  D61 stops a running block's timer at a calendar wall
with the log's own `pause`/`unpause` pair, and until W-37 both pasts — fork `past_segments` and
`Planner.pastRows` — drew the replayed Pause segment as a Lost row noted `paused`, so the day showed
the meeting twice: its Wall row, and a `paused` Lost row over the same span that `tm review day`
counts as no lost time at all.  One span, two readings (AGENTS §5.3).

The rule is gap 3044's own: a renderer rule over `(pause, wall)` pairs — **the part of a paused
row a wall of the day covers is not drawn**.  This module is that cut and nothing else, over plain
`[lo, hi)` spans of seconds: `cutOne` takes one span out of one piece, `cutAll` every span out of
every piece, and `clipCut` a segment's clip to `[day_start, now]` with the spans cut out of it.
`Planner.pastSpans` hands it the day's walls for a Pause and no spans for any other kind, so a
Block, a Break, a closed interruption, a routine and an idle mark are drawn over their whole clip,
as they were.

**Why a module of its own.**  `Planner.lean` carries 175 check-9 pin sites (`kernel/mutations.txt`,
`file:line declaration`) after the replayed past, and every line inserted above them moves them all;
a moved site fails check 9 until `mutate.py --verify --write` re-runs its row, one kernel build per
constant.  The cut's laws have no reason to live in the planner — they are about spans of `Nat` —
so they live here, `Planner.lean` imports this module, and the planner's own edit stays
line-neutral.

**The laws.**  Every piece lies inside its clip and is not empty (`clipCut_within`); every piece is
apart from every non-empty span it was cut by (`clipCut_apart`), which is what
`Planner.a_paused_row_lies_under_no_wall` reads; and spans that do not reach a piece leave it whole
(`clipCut_untouched`), which is what `Planner.a_pause_no_wall_touches_is_drawn_whole` reads — the
cut over-bites nothing (AGENTS §5.8).  `the_cut_is_run` runs it (AGENTS §5.2).
-/

namespace Tm
namespace Planner

/-- **One span cut out of one piece**: what is left before it and what is left after it.  An empty
span (`s.2 ≤ s.1`) cuts nothing. -/
def cutOne (s p : Nat × Nat) : List (Nat × Nat) :=
  if s.2 ≤ s.1 then [p]
  else (if p.1 < min p.2 s.1 then [(p.1, min p.2 s.1)] else []) ++
    (if max p.1 s.2 < p.2 then [(max p.1 s.2, p.2)] else [])

/-- **Every span cut out of every piece**, structural on the spans (so `decide` runs it). -/
def cutAll : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ps => ps
  | s :: ss, ps => cutAll ss (ps.flatMap (cutOne s))

/-- **A clip with the spans cut out of it**: nothing when the clip `[a, b)` is empty, else the
pieces `cutAll` leaves of it.  With no spans it is the clip itself (`clipCut_nil`). -/
def clipCut (a b : Nat) (ss : List (Nat × Nat)) : List (Nat × Nat) :=
  if b ≤ a then [] else cutAll ss [(a, b)]

theorem cutOne_sub {s p q : Nat × Nat} (h : q ∈ cutOne s p) : p.1 ≤ q.1 ∧ q.2 ≤ p.2 := by
  unfold cutOne at h
  split at h
  · simp only [List.mem_singleton] at h; subst h; omega
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; simp only; omega
      · simp at h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; simp only; omega
      · simp at h

theorem cutOne_nonempty {s p q : Nat × Nat} (hp : p.1 < p.2) (h : q ∈ cutOne s p) : q.1 < q.2 := by
  unfold cutOne at h
  split at h
  · simp only [List.mem_singleton] at h; subst h; exact hp
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; simp only; omega
      · simp at h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; simp only; omega
      · simp at h

/-- **A piece left by a cut is apart from the span that cut it.** -/
theorem cutOne_apart {s p q : Nat × Nat} (hs : s.1 < s.2) (h : q ∈ cutOne s p) :
    q.2 ≤ s.1 ∨ s.2 ≤ q.1 := by
  unfold cutOne at h
  rw [if_neg (by omega)] at h
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton] at h; subst h; simp only; omega
    · simp at h
  · split at h
    · simp only [List.mem_singleton] at h; subst h; simp only; omega
    · simp at h

/-- **A span that does not reach a piece leaves it whole.** -/
theorem cutOne_untouched {s p : Nat × Nat} (hp : p.1 < p.2)
    (h : s.2 ≤ s.1 ∨ s.2 ≤ p.1 ∨ p.2 ≤ s.1) : cutOne s p = [p] := by
  unfold cutOne
  by_cases he : s.2 ≤ s.1
  · rw [if_pos he]
  · rw [if_neg he]
    rcases h with h | h | h
    · exact absurd h he
    · rw [if_neg (by omega), if_pos (by omega)]
      have : max p.1 s.2 = p.1 := by omega
      rw [this]; rfl
    · rw [if_pos (by omega), if_neg (by omega)]
      have : min p.2 s.1 = p.2 := by omega
      rw [this]; rfl

/-- **Every piece `cutAll` leaves lies inside a piece it was given.** -/
theorem cutAll_sub {ss ps : List (Nat × Nat)} {q : Nat × Nat} (h : q ∈ cutAll ss ps) :
    ∃ p ∈ ps, p.1 ≤ q.1 ∧ q.2 ≤ p.2 := by
  induction ss generalizing ps with
  | nil => exact ⟨q, h, Nat.le_refl _, Nat.le_refl _⟩
  | cons s ss ih =>
    obtain ⟨p', hp', h1, h2⟩ := ih h
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hp'
    have := cutOne_sub hq
    exact ⟨p, hp, by omega, by omega⟩

/-- **…and is never empty**, when no piece it was given was. -/
theorem cutAll_nonempty {ss ps : List (Nat × Nat)} {q : Nat × Nat}
    (hps : ∀ p ∈ ps, p.1 < p.2) (h : q ∈ cutAll ss ps) : q.1 < q.2 := by
  induction ss generalizing ps with
  | nil => exact hps q h
  | cons s ss ih =>
    refine ih (fun p' hp' => ?_) h
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hp'
    exact cutOne_nonempty (hps p hp) hq

/-- **…and is apart from every non-empty span it was cut by.** -/
theorem cutAll_apart {ss ps : List (Nat × Nat)} {q : Nat × Nat} (h : q ∈ cutAll ss ps) :
    ∀ s ∈ ss, s.1 < s.2 → q.2 ≤ s.1 ∨ s.2 ≤ q.1 := by
  induction ss generalizing ps with
  | nil => intro s hs; cases hs
  | cons s ss ih =>
    intro s' hs' hlt
    rcases List.mem_cons.1 hs' with he | hm
    · subst he
      have h' : q ∈ cutAll ss (ps.flatMap (cutOne s')) := h
      obtain ⟨p', hp', h1, h2⟩ := cutAll_sub h'
      obtain ⟨p, -, hq⟩ := List.mem_flatMap.1 hp'
      have := cutOne_apart hlt hq
      omega
    · exact ih h s' hm hlt

/-- **Spans that do not reach a piece leave it whole** — the cut over-bites nothing. -/
theorem cutAll_untouched {ss : List (Nat × Nat)} {p : Nat × Nat} (hp : p.1 < p.2)
    (h : ∀ s ∈ ss, s.2 ≤ s.1 ∨ s.2 ≤ p.1 ∨ p.2 ≤ s.1) : cutAll ss [p] = [p] := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show cutAll ss ([p].flatMap (cutOne s)) = [p]
    rw [List.flatMap_singleton, cutOne_untouched hp (h s (List.mem_cons_self ..))]
    exact ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

/-- **Every piece of a clip lies inside it and is not empty.** -/
theorem clipCut_within {a b : Nat} {ss : List (Nat × Nat)} {q : Nat × Nat}
    (h : q ∈ clipCut a b ss) : a ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ b := by
  unfold clipCut at h
  split at h
  · simp at h
  · rename_i hc
    obtain ⟨p, hp, h1, h2⟩ := cutAll_sub h
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨h1, cutAll_nonempty (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact Nat.lt_of_not_le hc) h, h2⟩

/-- **Every piece of a clip is apart from every non-empty span cut out of it.** -/
theorem clipCut_apart {a b : Nat} {ss : List (Nat × Nat)} {q : Nat × Nat}
    (h : q ∈ clipCut a b ss) : ∀ s ∈ ss, s.1 < s.2 → q.2 ≤ s.1 ∨ s.2 ≤ q.1 := by
  unfold clipCut at h
  split at h
  · simp at h
  · exact cutAll_apart h

/-- **With no spans a clip is itself** — what every kind but a Pause is drawn over. -/
theorem clipCut_nil (a b : Nat) : clipCut a b [] = if b ≤ a then [] else [(a, b)] := by
  unfold clipCut
  split <;> rfl

/-- **Spans that do not reach a non-empty clip leave it whole.** -/
theorem clipCut_untouched {a b : Nat} {ss : List (Nat × Nat)} (hab : a < b)
    (h : ∀ s ∈ ss, s.2 ≤ s.1 ∨ s.2 ≤ a ∨ b ≤ s.1) : clipCut a b ss = [(a, b)] := by
  unfold clipCut
  rw [if_neg (Nat.not_le.2 hab)]
  exact cutAll_untouched hab h

/-- **The cut, run** (AGENTS §5.2): two spans cut three pieces out of one; a span covering the
piece leaves nothing; one that does not reach it leaves it whole; an empty one cuts nothing; an
empty clip is nothing whatever the spans. -/
theorem the_cut_is_run :
    cutAll [(5, 8), (2, 3)] [(0, 10)] = [(0, 2), (3, 5), (8, 10)] ∧
    cutAll [(0, 10)] [(0, 10)] = [] ∧
    cutAll [(12, 20)] [(0, 10)] = [(0, 10)] ∧
    cutAll [(6, 4)] [(0, 10)] = [(0, 10)] ∧
    clipCut 7 7 [] = [] ∧ clipCut 3 9 [(4, 6)] = [(3, 4), (6, 9)] := by
  decide

end Planner
end Tm
