import TmKernel.Lookahead
import TmKernel.Json
/-!
# `Width.lean` — a duration a line carries is refused past the host's width (stage 6 W-38)

The campaign's **D69** call on README gap **3345**: the kernel's LOADER refuses, BY NAME, a leading
estimate past the host's width, and `tm check` names that line — as D32 does for a key collision.

**Two bounds on one value** is what the gap measured.  The host reads a duration with `Dur::parse`
into `u32` minutes (`tm-core/src/model.rs`), so since W-37 (P57) `- [ ] 2 99999999999m Big …` is
`tm check`'s `bad-value` error; the kernel's `Field.estSlot` reads any `Nat`, so the same tree was
loaded, planned and closed by every kernel-backed verb.  DRIVEN at `f91bb90`, on a `tm init
--example` tree with that line appended to `backlog.md`: `tm check` exits 2 naming
`backlog.md:13`, and `tm drop ^a1` exits 0 and rewrites the tree.

**The class, not the list.**  The leading estimate is one of FOUR places a line carries a
`Field.Dur` that the host reads with that same `Dur::parse` into `u32` minutes (`grammar.rs`'
`build_item`): the leading slot, `est:`, `dur:` and `buffer:`.  The same drive with
`est:99999999999m` in place of the leading estimate gives the same two answers, so all four are
refused here, by one rule (`durs`, `fits`).  A duration inside a compound value — `pref:`, the
`min:`/`max:` rates, `after-done:`, `on-event:` — and `every:`'s counts have widths of their own
on the host; they are README gap 3431, named rather than silently left.

**The width is one number**: `Look.maxPlanMinutes` — fork `u32`, the bound `remaining` already has,
which `Boundary.maxRemaining` and the `est` op's `badValue est` already read (README gap 2929).
REUSED (R10), never minted.

**The block length.**  `Nb` is `n × blockMin` minutes, and the loader knows the block length only
when the request carries `blockMin`.  With one, the check is the host's exactly — minutes at the
request's block length.  Without one, a block is read as one minute, the numeral itself, which
refuses exactly what NO block length could hold, because every block length is at least a minute
(`fits_at_one_of_fits`); and the host sends its block length on every request that loads its tree
(`kernel_bridge`), so the check the shipped binary runs is the exact one.

**Why a module of its own.**  `Boundary.runLoad` is where the loader refuses a tree, and every
check-9 pin site below it would move with a line inserted there (the W-37 `PastCut` precedent).
So the rule and its laws live here, `Boundary` imports this module in the line that imported
`Lookahead` (which this module imports), and `runLoad`'s edit is line-neutral.
-/

namespace Tm
namespace Width

open Field (Dur)

/-- **Where on a line a duration the host reads as `u32` minutes sits**: the leading estimate,
and the three keys `build_item` reads with `Dur::parse`. -/
inductive Slot | lead | est | dur | buffer
deriving DecidableEq, Repr

/-- The word the refusal names the slot by. -/
def Slot.name : Slot → List Char
  | .lead => ['l','e','a','d']
  | .est => ['e','s','t']
  | .dur => ['d','u','r']
  | .buffer => ['b','u','f','f','e','r']

/-- **The durations a line carries, with where** — each through the kernel's one view of it
(`Field.estLeadOf`, `Field.viewEstKey`, `Field.viewDur`, `Field.viewBuffer`). -/
def durs (r : RawItem) : List (Slot × Dur) :=
  [(Slot.lead, Field.estLeadOf r), (.est, Field.viewEstKey r), (.dur, Field.viewDur r),
    (.buffer, Field.viewBuffer r)].filterMap (fun p => p.2.map (p.1, ·))

/-- **Within the host's width** at block length `bm`: the minutes fit fork `u32`. -/
def fits (bm : Nat) (d : Dur) : Bool := decide (d.minutes bm ≤ Look.maxPlanMinutes)

/-- The first slot of a line whose duration does not fit, if any. -/
def pastWidth (bm : Nat) (r : RawItem) : Option Slot :=
  ((durs r).find? (fun p => !fits bm p.2)).map (·.1)

/-- **The first item line of a document past the width**: its line index and slot.  The lines are
the loader's own — `splitDoc`'s items, so a line inside an HTML comment is prose and is not
asked (D47). -/
def firstPastWidth (bm : Nat) (ls : List (List Char)) : Option (Nat × Slot) :=
  (splitDoc 0 ls).items.findSome? (fun q => (pastWidth bm q.2.2.2).map (q.1, ·))

/-- **The refusal, by name**: `{"pastWidth":{"path","line","slot"}}` — the line 0-based, as
`badLine`'s is, and the slot by `Slot.name`. -/
def refusalJson (path : List Char) (line : Nat) (s : Slot) : JVal :=
  jone "pastWidth" (.obj [("path".toList, .str path), ("line".toList, .num line),
    ("slot".toList, .str s.name)])

/-! ## The laws -/

/-- **A line passes exactly when every duration it carries fits.** -/
theorem pastWidth_eq_none_iff (bm : Nat) (r : RawItem) :
    pastWidth bm r = none ↔ ∀ p ∈ durs r, fits bm p.2 = true := by
  simp [pastWidth, List.find?_eq_none]

/-- **A refused slot names a duration that is really past the width.** -/
theorem pastWidth_eq_some (bm : Nat) (r : RawItem) (s : Slot) (h : pastWidth bm r = some s) :
    ∃ d, (s, d) ∈ durs r ∧ Look.maxPlanMinutes < d.minutes bm := by
  unfold pastWidth at h
  cases hf : (durs r).find? (fun p => !fits bm p.2) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    subst h
    refine ⟨p.2, by simpa using hm, ?_⟩
    simp [fits] at hp
    omega

/-- **A document passes exactly when every item line the loader reads fits.** -/
theorem firstPastWidth_eq_none_iff (bm : Nat) (ls : List (List Char)) :
    firstPastWidth bm ls = none ↔ ∀ q ∈ (splitDoc 0 ls).items, pastWidth bm q.2.2.2 = none := by
  simp [firstPastWidth, List.findSome?_eq_none_iff]

/-- **A refused document names one of the loader's item lines, and its slot.** -/
theorem firstPastWidth_eq_some (bm : Nat) (ls : List (List Char)) (k : Nat) (s : Slot)
    (h : firstPastWidth bm ls = some (k, s)) :
    ∃ i g r, (k, i, g, r) ∈ (splitDoc 0 ls).items ∧ pastWidth bm r = some s := by
  unfold firstPastWidth at h
  obtain ⟨q, hq, hs⟩ := List.exists_of_findSome?_eq_some h
  cases hp : pastWidth bm q.2.2.2 with
  | none => simp [hp] at hs
  | some s' =>
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨q.2.1, q.2.2.1, q.2.2.2, by simpa using hq, hp⟩

/-- **A longer block only makes a block estimate longer**: what fits at one block length fits at
every shorter one. -/
theorem fits_of_fits_at_a_longer_block (d : Dur) {bm bm' : Nat} (hle : bm ≤ bm')
    (h : fits bm' d = true) : fits bm d = true := by
  unfold fits at h ⊢
  have h' := of_decide_eq_true h
  apply decide_eq_true
  cases d with
  | simple n u =>
    cases u
    · exact Nat.le_trans (Nat.mul_le_mul_left n hle) h'
    all_goals exact h'
  | hm a b => exact h'

/-- **Without a block length the loader refuses only what no block length could hold**: what fits
at any block length of at least a minute fits at one minute a block. -/
theorem fits_at_one_of_fits (d : Dur) {bm : Nat} (h1 : 1 ≤ bm) (h : fits bm d = true) :
    fits 1 d = true :=
  fits_of_fits_at_a_longer_block d h1 h

/-! ## Witnesses — the rule bites, does not over-bite, and reads the block length -/

set_option maxRecDepth 20000 in
/-- **Gap 3345's own line is refused, at its leading estimate** — and the width's last minute is
not. -/
theorem the_leading_estimate_past_the_width_is_refused :
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','9','9','9','9','9','9','9','9','9','9','9','m',' ','B','i','g',' ','m','i','g','r','a','t','i','o','n',' ','^','z','9']]
      = some (0, .lead) ∧
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','4','2','9','4','9','6','7','2','9','6','m',' ','B','i','g',' ','^','z','9']]
      = some (0, .lead) ∧
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','4','2','9','4','9','6','7','2','9','5','m',' ','B','i','g',' ','^','z','9']]
      = none := by
  decide

set_option maxRecDepth 20000 in
/-- **The three keys are refused by the same rule**, each by its own name. -/
theorem the_three_keys_past_the_width_are_refused :
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','B','i','g',' ','e','s','t',':','4','2','9','4','9','6','7','2','9','6','m',' ','^','z','9']]
      = some (0, .est) ∧
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','B','i','g',' ','d','u','r',':','4','2','9','4','9','6','7','2','9','6','m',' ','^','z','9']]
      = some (0, .dur) ∧
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','B','i','g',' ','b','u','f','f','e','r',':','4','2','9','4','9','6','7','2','9','6','m',' ','^','z','9']]
      = some (0, .buffer) := by
  decide

set_option maxRecDepth 20000 in
/-- **A block estimate is read at the request's block length**: `71582789b` is 4,294,967,340
minutes at sixty and past the width, and within it when no block length is known (one minute a
block — what no block length could refuse). -/
theorem a_block_estimate_is_read_at_the_block_length :
    firstPastWidth 60 [['-',' ','[',' ',']',' ','2',' ','7','1','5','8','2','7','8','9','b',' ','B','i','g',' ','^','z','9']]
      = some (0, .lead) ∧
    firstPastWidth 1 [['-',' ','[',' ',']',' ','2',' ','7','1','5','8','2','7','8','9','b',' ','B','i','g',' ','^','z','9']]
      = none := by
  decide

set_option maxRecDepth 20000 in
/-- **A line inside an HTML comment is prose, and is not asked** (D47): the loader's own split. -/
theorem a_commented_line_past_the_width_is_prose :
    firstPastWidth 60 [['<','!','-','-'],
      ['-',' ','[',' ',']',' ','2',' ','9','9','9','9','9','9','9','9','9','9','9','m',' ','B','i','g',' ','m','i','g','r','a','t','i','o','n',' ','^','z','9'],
      ['-','-','>']] = none := by
  decide

/-- **The refusal spells itself** — the name, the line, and the slot by its word.  The slot's word
is what `kernel_bridge` reads to say which duration of the line is past the width. -/
theorem the_slots_spell_themselves :
    [Slot.lead, .est, .dur, .buffer].map Slot.name
      = [['l','e','a','d'], ['e','s','t'], ['d','u','r'], ['b','u','f','f','e','r']] := rfl

theorem refusalJson_is_the_err_shape :
    refusalJson ['a'] 3 .est = jone "pastWidth" (.obj [("path".toList, .str ['a']),
      ("line".toList, .num 3), ("slot".toList, .str ['e','s','t'])]) := rfl

end Width
end Tm
