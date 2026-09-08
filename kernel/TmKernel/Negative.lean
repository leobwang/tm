import TmKernel
/-!
# The demonstration: the shipped bug does not compile

Each block below writes something the Rust wrote (or something a future writer
would plausibly write) and **fails to compile**.  This file is the only test
that checks the type system is still doing its job, so CI must assert that
`lean Negative.lean` FAILS.

    LEAN_PATH=.lake/build/lib/lean lean Negative.lean     # must print errors
-/
namespace Tm

/- CHEAT 1 — write `tm move` the way `horizon.rs::move_to` writes it: put the
   line where it is going, no question asked about what is already there. -/
def moveCheat1 (t : Site) (e : Entity) : Entity :=
  { e.val with live := t }

/- CHEAT 2 — skip the check by asserting the proof. -/
def moveCheat2 (t : Site) (e : Entity) : Entity :=
  ⟨{ e.val with live := t }, rfl⟩

/- CHEAT 3 — the bug in its original shape: `move_to` **appends the rendered
   line to the destination file**.  In this kernel a document holds prose only,
   and `planWf` says none of it parses as an item, so an appended item line is
   a plan that cannot be constructed. -/
def appendLine (l : List Char) (d : Doc) : Doc := ⟨d.path, d.prose ++ [(0, l)], d.region⟩

def moveCheat3 (i : Id) (g : Glyph) (r : RawItem) (k : DocIx) (p : WfPlan) : WfPlan :=
  ⟨⟨p.val.docs.modify k (appendLine (serializeItem i g r)), p.val.store⟩, p.property⟩

/- CHEAT 4 — a close that zeroes the remaining estimate it just measured.
   The definition is legal; the conservation obligation is not dischargeable. -/
def closeCheat (e : Entity) : Entity :=
  ⟨{ e.val with line := setEst 0 e.val.line }, e.property⟩

theorem close_conserves (bm : Nat) (e : Entity) :
    remainingOf bm e.val.line ≤ remainingOf bm (closeCheat e).val.line := by
  simp [closeCheat]

/- CHEAT 5 — export `setLeadWord` as "edit the estimate", which is what
   `tm edit ^id est=` did.  Every setter must discharge `view ∘ set = id`; this
   one cannot, and `lead_edit_is_silent` says why. -/
theorem lead_set_is_not_silent (bm : Nat) (w : List Char) (r : RawItem) :
    viewRemaining bm (setLeadWord w r) = unitValue bm w := rfl

/- CHEAT 6 — take the destination straight off the wire, which is what let
   `move ^m1 7` delete the item from a one-document plan and return `ok`.  A
   `Dest` is an index **plus a proof it is a document of this plan**, and a
   `Nat` decoded from JSON cannot supply the second field. -/
def destCheat (n : Nat) (p : WfPlan) : Dest p.val := ⟨n, by omega⟩

/- CHEAT 7 — read a `[-]` line back as an ordinary open item, which is what
   the first loader did: it sent `Glyph.demoted` to `live free` with no archive
   and `glyphAt` rendered `[ ]`.  The inverse of `glyphAt` is a *partial*
   function, and `statusOfGlyph .demoted` is `none` for a reason. -/
def loneDemotedCheat (q : Placement) : Entity :=
  ⟨{ live := ⟨q.doc, q.rank⟩, archive := none, status := (statusOfGlyph q.glyph).get rfl,
     line := q.item, stamps := [] }, rfl⟩

/- CHEAT 8 — build the plan without answering which of a demotion's two `[-]`
   lines is the tombstone.  Deciding it by the order the host listed the
   documents was this, with the assertion hidden in a `match` that tried one
   orientation and then the other: three of `planWf`'s parts discharged and the
   rest waved through.  (`planWf` has five parts since the item fields joined
   the plan-level tier, so the first `rfl` Lean reaches is `itemsWf`'s; the
   cheat is the same one.) -/
def loadCheat (planDocs : List Doc) (store : Store)
    (h1 : docsWf ⟨planDocs, store⟩ = true) (h2 : sitesInRange ⟨planDocs, store⟩ = true)
    (h3 : pathsDistinct ⟨planDocs, store⟩ = true) : WfPlan :=
  ⟨⟨planDocs, store⟩, planWf_of_parts h1 h2 h3 rfl rfl⟩

-- ===========================================================================
-- APPENDED: the item fields and the rest of the plan-level tier
-- (State.lean / Plan.lean).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 9 — wave the **item half** of the plan-level tier through, which is
   what "cycles are only a `tm check` warning" amounts to once `tm check` and
   the acceptance rule are the same function.  `planWf` has five parts now and
   `itemsWf` is one of them; `rfl` cannot supply it. -/
def itemTierCheat (planDocs : List Doc) (store : Store)
    (h1 : docsWf ⟨planDocs, store⟩ = true) (h2 : sitesInRange ⟨planDocs, store⟩ = true)
    (h3 : pathsDistinct ⟨planDocs, store⟩ = true)
    (h4 : demotionsOriented ⟨planDocs, store⟩ = true) : WfPlan :=
  ⟨⟨planDocs, store⟩, planWf_of_parts h1 h2 h3 h4 rfl⟩

/- CHEAT 10 — the sharpest of the new ones: claim a transform that lands in
   range and keeps its tombstone behind it always succeeds.  It does not, since
   `Normalized` and `after:` acyclicity joined `planWf`: a move onto an occupied
   rank, or an edit that closes a dependency cycle, is refused by `mapAt`'s
   re-check.  The residual obligation is `hrest`, and it cannot be forgotten
   because the theorem will not apply without it. -/
theorem move_always_works (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity)
    (e e' : Entity) (hget : p.val.store.get i = some e) (hf : f e = .ok e')
    (hin : entityInRange p.val e' = true) (hor : demotionOriented p.val e' = true) :
    ∃ q : WfPlan, p.mapAt i f = .ok q ∧ q.val.store.get i = some e' ∧
      q.val.docs = p.val.docs :=
  mapAt_ok_of_inRange p i f e e' hget hf hin hor

/- CHEAT 11 — `ci: 9`.  The Rust field is a `u8` and the parser clamped; here
   the bound is the type.  (Note the shape of the cheat: `(9 : Fin 6)` would
   *silently* wrap to 3 through `OfNat`, which is why every bounded value in
   this kernel comes from a smart constructor and not from a numeral.) -/
def ciCheat : Fin 6 := ⟨9, by omega⟩

/- CHEAT 12 — `#lean #lean` as two tags.  Tags are a set structurally, so the
   duplicate is not something a later `dedup` has to catch. -/
def tagCheat : TagSet := ⟨[['l', 'e', 'a', 'n'], ['l', 'e', 'a', 'n']], by decide⟩

/- CHEAT 13 — hand a raw list where the set is wanted. -/
def rawTagsCheat (c : Core) : Core := { c with tags := [['a'], ['a']] }

/- CHEAT 14 — `win:25:00-…`.  A time of day is `Fin 1440`. -/
def clockCheat : Clock := ⟨1500, by omega⟩

/- CHEAT 15 — `every:month:32`. -/
def monthDayCheat : MonthDay := ⟨31, by omega⟩

end Tm

/- ======================================================================
   THE EXACT-ARITHMETIC LAYER (`TmKernel/Arith.lean`).
   Appended as its own block so that the three stage-one branches merge.
   ====================================================================== -/
namespace Tm

/- CHEAT 16 — form the quotient.  `u = need/avail` in `Nat` is integer
   division, which throws the fraction away before the comparison sees it:
   `u = 3/4` reaches the `1/2` edge, and `3/4 = 0` reaches nothing.  This is
   why `utilGe` cross-multiplies and no ratio is ever divided. -/
def utilNatDiv (need avail : Nat) (e : Arith.Q) : Bool :=
  decide (e.num ≤ e.den * (need / avail))

theorem the_quotient_is_the_comparison :
    utilNatDiv 3 4 ⟨1, 2⟩ = Arith.utilGe 3 4 ⟨1, 2⟩ := by decide

/- CHEAT 17 — round a ratio whose denominator nobody checked.  `n / 0` is
   `0` in Lean, so §8.1's budget with `block_min = 0` would be a silent
   wrong answer rather than an error.  A rounding site takes a `Pos`, and a
   raw `Q` is not one. -/
def budgetCheat (windowMin blockMin : Nat) : Nat :=
  Arith.floorQ (⟨windowMin, blockMin⟩ : Arith.Q)

/- CHEAT 18 — round the safety margin the way `priority.rs:349` does.  A
   margin rounded down stops being a margin: the reservation for one minute
   of work at `safety = 1.3` becomes one minute, which does not cover
   `13/10`.  R1's rule is a ceiling, and `needMin_covers` is why. -/
def needFloor (rem : Nat) : Nat := Arith.floorQ (Arith.scale Arith.safety rem)

theorem floor_still_covers_the_need :
    Arith.Q.le (Arith.scale Arith.safety 1).val (Arith.ofNat (needFloor 1)) = true := by decide

/- CHEAT 19 — derive §7.1's bin edges instead of tabulating them.  Three of
   the four are halvings, so `1/2^i` looks like the generating structure; it
   disagrees with the spec on every `u` in `[0.1, 0.125)`, and at `u = 0.11`
   it gives `+3` where the table gives `+2`. -/
theorem log2_ladder_is_the_table :
    Arith.binOf Arith.log2Bins 11 100 = Arith.binOf Arith.defaultBins 11 100 := by decide

/- CHEAT 20 — guard the division by zero, which is what `is_finite()` does
   in the Rust.  §7.1 says capacity zero makes `u = ∞`, so it reaches every
   edge and the item is HOT; a guard that answers "not urgent" inverts the
   rule at exactly the point where the item cannot possibly be finished. -/
def utilGuarded (need avail : Nat) (e : Arith.Q) : Bool :=
  if avail = 0 then false else Arith.utilGe need avail e

theorem the_finite_guard_is_harmless :
    utilGuarded 1 0 Arith.hotEdge = Arith.utilGe 1 0 Arith.hotEdge := by decide

end Tm

/- ═══════════════════════════════════════════════════════════════════════════
   CALENDAR CHEATS (Cal.lean / Grain.lean).  Appended; nothing above is edited.
   ═══════════════════════════════════════════════════════════════════════════ -/
-- Only so the failures below are the *type* errors they claim to be, and not
-- an elaborator budget running out first.  It applies from here on only.
set_option maxRecDepth 10000

namespace Tm

/- CHEAT 21 — hand a date straight through as valid, which is how `Feb 30`
   reaches a calendar.  `ValidDate` is a `Subtype` over a *decidable* predicate,
   so the second field is `Date.valid ⟨2024,2,30⟩ = true`, and that computes to
   `false = true`. -/
def dateCheat : Cal.ValidDate := ⟨⟨2024, 2, 30⟩, by decide⟩

/- CHEAT 22 — number the weeks inside the civil year, which is what "week 1
   starts on January 1st" does, and claim it is the ISO week.  It is not: on
   2027-01-01 this says week 1 and ISO says 2026-W53. -/
def naiveWeek (n : Nat) : Nat := (n - Cal.jan1 (Cal.ofDay n).year) / 7 + 1

theorem naive_week_is_iso :
    naiveWeek (Cal.toDay ⟨2027, 1, 1⟩) = (Cal.isoOf (Cal.toDay ⟨2027, 1, 1⟩)).week := by
  decide

/- CHEAT 23 — name a week's month without naming a tie-break, by assuming the
   week determines the month.  The rewrite is where the derivation stops:
   `week_does_not_refine_month` is the counterexample (2026-W36). -/
theorem week_refines_month : refines week month := by
  intro a b h
  rw [index_week] at h
  rw [index_month, index_month, h]

/- CHEAT 24 — declare `horizon.rs:1543`'s rule stable.  "The month of today" is
   a function of `now`, so two callers on two days of one week get two answers,
   and this does not even hold definitionally. -/
theorem month_of_today_is_stable :
    Cal.monthOfWeekByToday (Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩))
        (Cal.toDay ⟨2026, 8, 31⟩)
      = Cal.monthOfWeekByToday (Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩))
        (Cal.toDay ⟨2026, 9, 6⟩) := by
  decide

/- CHEAT 25 — drop the century rule and keep "every fourth year".  Refuted by
   computation at y = 100. -/
def isLeapCheat (y : Nat) : Bool := y % 4 == 0

theorem leap_is_every_fourth_year : ∀ y, y < 2000 → Cal.isLeap y = isLeapCheat y := by
  decide

/- CHEAT 26 — get the phase of the seven-day cycle wrong by one.  The three
   cross-checks in `Cal.lean` exist to catch exactly this, and they do. -/
def weekdayCheat (n : Nat) : Cal.Weekday := Cal.Weekday.ofIndex (n % 7 + 1)

theorem cheat_weekday_1970 : weekdayCheat (Cal.toDay ⟨1970, 1, 1⟩) = .thursday := by decide

end Tm

/- ===================================================================
   FOUND BY THE CORPUS HARNESS AND THE DIFFERENTIAL ORACLE, appended as a
   block so the stage-two branches merge.  Numbered from 27 provisionally;
   whoever merges renumbers.

   Each one is an assumption a reader of §4.1 would make, that the shipped
   Rust makes, and that this kernel does not satisfy.  They are here rather
   than in a report because a refutation that only lives in prose is one the
   next writer re-derives differently.  All four were found by running the
   fixture corpus (`kernel/corpus/`) and 2,048 lines from `main`'s own
   `grammar_proptest` generator through the boundary and comparing with
   `tm-core::grammar`; the counts are in `kernel/README.md`.
   =================================================================== -/
namespace Tm

/- CHEAT 27 — §4.1 says an item line's tokens are "whitespace-separated
   words", and `tm-core::grammar` splits on any whitespace run.  `Text.lean`'s
   separator is `isSp c := c == ' '`, so a tab is an ordinary word character:
   `a<TAB>b` is ONE token, not two.  Consequences the oracle found:
   `- [ ] x<TAB>^a1` is refused as `noId`, `- [ ] x ^a1<TAB>` yields the id
   `"a1\t"` — a store key the Rust's `Id::is_valid` rejects — and `tm edit est=`
   lands on a different token than the Rust's does when an earlier `est:` is
   glued to the previous word by a tab. -/
theorem tokens_are_whitespace_separated :
    (tokenize "a\tb".toList).length = 2 := by decide

/- CHEAT 28 — the same rule at the head of the line.  `parseBody` matches the
   literal `- [`, so `- <TAB>[ ] …` and `-  [ ] …` (two spaces) are not item
   lines at all.  They are kept as prose and written back unchanged, so nothing
   reports anything: the item is simply invisible to every command, to ranks,
   and to `tm check`.  1,049 of 2,048 generated lines land here. -/
theorem one_space_is_not_the_only_separator_after_the_bullet :
    isItemLine "-  [ ] 2 30m Spaced ^a1".toList = true := by decide

/- CHEAT 29 — §4.1 says a token the parser cannot classify stays in the title,
   and the Rust keeps `^`, `^%` and `^é` there and records a `tm check`
   problem.  `isIdWord w := w.head? == some '^'` makes every one of them an id
   token, so a bare `^` names an entity whose id is the empty list (and two such
   lines are `dupId ""`), `^%` names one called `%`, and a line carrying both
   `^%` and a real `^q7` is refused as `manyIds`.  The last of those is
   `plan-conflicts/week/2026-W37.md:23`, a line the shipped parser reads with
   id `q7`. -/
theorem a_bare_caret_is_not_an_id : isIdWord ['^'] = false := by decide

/- CHEAT 30 — §4.3's calendar rule ("generated intervals") as `shapeWfFor`
   states it, against the `Core` the loader actually builds.  Nothing in
   `Line.lean` interprets `at:` yet — every token but the id and the estimate is
   kept verbatim — so `Core.shape` is `Shape.none` for every entity the boundary
   constructs, and the `.calendar` clause is unsatisfiable rather than merely
   unsatisfied.  All 16 calendar item lines in the corpus are refused with
   `itemCheck: fileKindShape`, including four that are `at:<date>T<hh:mm>/<hh:mm>`
   exactly as §4.1 writes them.  The same latent hole is in the `.routines` and
   `.optional` clauses; it is invisible only because those files' lines carry no
   `[ ]` box and are therefore prose. -/
theorem a_loaded_line_can_satisfy_the_calendar_shape_rule
    (live : Site) (st : Status) (r : RawItem) :
    shapeWfFor DocKind.calendar
      { live := live, archive := none, status := st, line := r, stamps := [] } = true := rfl

end Tm
