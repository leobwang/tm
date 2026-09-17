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

/- CHEAT 7 — **withdrawn, and its replacements are CHEAT 36-40.**  It read: a
   record beside a standing tombstone may not be `[ ]`, so
   `statusOfGlyphDemoted .todo` is `none` and the entity below cannot be built.
   §6.3 refutes it — `tm readopt` is "`[-]` → `[ ]`, stamp kept", and §4.3's
   own fixture pair is a `[ ]` in `week/2026-W37.md` beside the `[-]` in
   `month/2026-09.md # Demoted`.  The kernel now reads that pair, so the cheat
   asserted a restriction the model no longer has and could not stay: a
   negative test that refuses something legitimate is a trapdoor, not a check.
   What replaces it is the rule that is genuinely gone (CHEAT 37), the type
   that makes a byte-less tombstone unwritable (CHEAT 36), and the
   unconditional horizon rule (CHEAT 38). -/

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

/- CHEAT 13 — hand a raw list where the set is wanted.  `Core.tags` is a
   *view* of the line now, so the cheat is one level down: build the value the
   view returns out of a list with a duplicate in it. -/
def rawTagsCheat : TagSet := ⟨[['a'], ['a']], by decide⟩

/- CHEAT 14 — `win:25:00-…`.  A time of day is `Fin 1440`. -/
def clockCheat : Field.Clock := ⟨1500, by omega⟩

/- CHEAT 15 — `every:month:32`.  The only door into a monthly rule is
   `parseMonthDay`, and it refuses. -/
theorem monthDayCheat :
    Field.parseMonthDay ['3','2'] = some (Field.Rule.monthly 32) := by decide

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


/- ======================================================================
   §4.1's field grammar — cheats added with the field grammar (Line.lean,
   Text.lean).  Every block below is a plausible claim about the grammar
   that is FALSE, and Lean says so.
   ====================================================================== -/

/- CHEAT A — drop `Rule.wf` from the `every:` round trip.  `every:0d` renders
   as `0d` and `grammar.rs` rejects `n == 0`, so `.everyNDays 0` does not come
   back; the side condition is load-bearing and `rfl` cannot supply it. -/
theorem every_needs_no_side_condition (r : Field.Rule) :
    Field.parseRule (Field.renderRule r) = some r :=
  Field.parse_render_rule r rfl

/- CHEAT B — the shipped `tm edit est=` bug, stated as a law: read the
   remaining estimate off the *leading* slot.  §4.1 says `est:` overrides it,
   and `spec_line_remaining` is the counterexample. -/
theorem leading_estimate_is_the_remaining_estimate (r : RawItem) :
    Field.viewRemainingDur r = Field.estLeadOf r := rfl

/- CHEAT C — accept a date that is not zero-padded.  `parse_date` checks the
   width (`s.len() != 10`) and so does this kernel. -/
theorem date_accepts_unpadded :
    Field.parseDate ['2','0','2','6','-','9','-','1','1'] ≠ none := by decide

/- CHEAT D — treat a flag word inside the title as a flag.  §4.1 reads a flag
   only after a `@ # ! ^ key:` token, which is why `setFlag` inserts after the
   `^id` and why it returns `none` when there is no id. -/
theorem flag_word_in_the_title_is_a_flag :
    Field.flagsOf (Field.itemOf Field.flagInTitleLine) = [Field.Flag.openEnded] := by decide

/- CHEAT E — give `cap:` a field of its own.  It is an alias of `max:`; two
   places for one budget is the defect class this kernel exists to remove. -/
theorem cap_is_its_own_field :
    Field.Key.ofName? ['c','a','p'] ≠ Field.Key.ofName? ['m','a','x'] := by decide

/- CHEAT F — drop `slotGuard` from round trip B.  A title beginning with `5`
   is eaten by the empty ci slot, so the fields do not come back: the line
   reads as `ci = 5` with a one-word title.  This is `grammar.rs`'s
   `EditError::Ambiguous`, and refusing to write the line is the fix. -/
def ambiguousFields : Field.Fields :=
  { title := [['5'], ['a','p','p','l','e','s']] }

theorem the_slot_guard_is_unnecessary :
    Field.viewFields (Field.renderItem ['t','3'] ambiguousFields) = ambiguousFields := by
  decide

end Tm

/- ==================================================================== -/
/- Round trip and `Normalized`: the cheats the plan-level proofs refuse. -/
/- ==================================================================== -/

namespace Tm

/- CHEAT 27 — "the store hands its lines back in rank order, so the sort is a
   formality."  It is not: the store enumerates its domain, not the file.  A
   two-line list in the wrong order is the whole counterexample. -/
def unsortedRanks : List (Nat × List Char) := [(2, "b".toList), (1, "a".toList)]

theorem sorting_is_a_formality : sortByRank unsortedRanks = unsortedRanks := by decide

/- CHEAT 28 — drop rank distinctness from the round trip and keep the
   conclusion.  `sorted_ext_by_key` needs a **strict** order: with `≤`, two
   lines at one rank are two different files with the same members and the sort
   has nothing to choose between them.  `Normalized` is what supplies the
   strictness, and this is the type error that says so. -/
theorem sorted_ext_by_le : ∀ (l₁ l₂ : List (Nat × List Char)),
    l₁.Pairwise (fun a b => a.1 ≤ b.1) → l₂.Pairwise (fun a b => a.1 ≤ b.1) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ :=
  sorted_ext_by_key (fun x : Nat × List Char => x.1)

/- CHEAT 29 — read the file back without asking whether ranks are distinct.
   `renderDocAt_loadCore` takes `normalized` because without it the sorted list
   is not determined by its members, and which of two lines sharing a rank comes
   first depends on the order the store enumerated its domain — i.e. on the
   order the host listed its documents. -/
theorem round_trip_without_rank_distinctness (docs : List ReqDoc)
    (items : List (Id × Entity))
    (hb : buildEntities (placementsOf 0 docs) = .ok items)
    (k : Nat) (rd : ReqDoc) (hk : docs[k]? = some rd) :
    renderDocAt (loadCore docs items) k (mkDoc rd) = rd.lines :=
  renderDocAt_loadCore docs items hb k rd hk

/- CHEAT 30 — "any rank will do."  `freshRank` is not decoration: a move onto a
   rank another line of the destination already holds is exactly the ambiguity
   `Normalized` forbids, and rank 0 is the rank a naive implementation picks. -/
theorem move_to_rank_zero_keeps_ranks_distinct (p : WfPlan) (i : Id) (e a : Entity)
    (k : DocIx) (hs : (p.val.store.get i).isSome = true)
    (hget : p.val.store.get i = some e) (hva : a.val = { e.val with live := ⟨k, 0⟩ }) :
    normalized { p.val with store := p.val.store.set i a hs } = true :=
  move_at_freshRank_normalized p i e a k hs hget hva

/- CHEAT 31 — count only the item lines when checking a rank is free.  A
   document's ranks are its prose ranks *and* its item ranks in one list, because
   `weave` orders them against each other; a relocated line landing on a
   heading's rank would move that heading with no command run.  `SitesFree` has
   two clauses for this reason. -/
theorem normalized_set_ignoring_prose (p : PlanCore) (i : Id) (e e' : Entity)
    (hs : (p.store.get i).isSome = true) (hget : p.store.get i = some e)
    (hnorm : normalized p = true)
    (hfree : ∀ l ∈ render i e', ∀ m ∈ p.lines, m.site = l.site → m ∈ render i e) :
    normalized { p with store := p.store.set i e' hs } = true :=
  normalized_set p i e e' hs hget hnorm hfree

end Tm

/- ===================================================================
   FOUND BY THE CORPUS HARNESS AND THE DIFFERENTIAL ORACLE, appended as a
   block so the stage-two branches merge.  Numbered from 27 provisionally;
   whoever merges renumbers.  Renumbered 27-30 -> 122-125 in the W-1 audit
   repair (AGENTS 6.5 item 1): the rank block above keeps 27-30.

   Each one is an assumption a reader of §4.1 would make, that the shipped
   Rust makes, and that this kernel does not satisfy.  They are here rather
   than in a report because a refutation that only lives in prose is one the
   next writer re-derives differently.  All four were found by running the
   fixture corpus (`kernel/corpus/`) and 2,048 lines from `main`'s own
   `grammar_proptest` generator through the boundary and comparing with
   `tm-core::grammar`; the counts are in `kernel/README.md`.
   =================================================================== -/
namespace Tm

/- CHEAT 122 — §4.1 says an item line's tokens are "whitespace-separated
   words", and `tm-core::grammar` splits on any whitespace run.  `Text.lean`'s
   separator is `isSp c := c == ' '`, so a tab is an ordinary word character:
   `a<TAB>b` is ONE token, not two.  Consequences the oracle found:
   `- [ ] x<TAB>^a1` is refused as `noId`, `- [ ] x ^a1<TAB>` yields the id
   `"a1\t"` — a store key the Rust's `Id::is_valid` rejects — and `tm edit est=`
   lands on a different token than the Rust's does when an earlier `est:` is
   glued to the previous word by a tab. -/
theorem tokens_are_whitespace_separated :
    (tokenize "a\tb".toList).length = 2 := by decide

/- CHEAT 123 — the same rule at the head of the line.  `parseBody` matches the
   literal `- [`, so `- <TAB>[ ] …` and `-  [ ] …` (two spaces) are not item
   lines at all.  They are kept as prose and written back unchanged, so nothing
   reports anything: the item is simply invisible to every command, to ranks,
   and to `tm check`.  1,049 of 2,048 generated lines land here. -/
theorem one_space_is_not_the_only_separator_after_the_bullet :
    isItemLine "-  [ ] 2 30m Spaced ^a1".toList = true := by decide

/- CHEAT 124 — §4.1 says a token the parser cannot classify stays in the title,
   and the Rust keeps `^`, `^%` and `^é` there and records a `tm check`
   problem.  `isIdWord w := w.head? == some '^'` makes every one of them an id
   token, so a bare `^` names an entity whose id is the empty list (and two such
   lines are `dupId ""`), `^%` names one called `%`, and a line carrying both
   `^%` and a real `^q7` is refused as `manyIds`.  The last of those is
   `plan-conflicts/week/2026-W37.md:23`, a line the shipped parser reads with
   id `q7`. -/
theorem a_bare_caret_is_not_an_id : isIdWord ['^'] = false := by decide

/- CHEAT 125 — §4.3's calendar rule ("generated intervals") waved through: hold
   it of *every* line the loader builds.  It used to be `rfl`, and that is the
   defect this branch fixes.  Nothing joined §4.1's `at:` to §3.1's
   `Core.shape`, so the shape was `none` for every entity the boundary
   constructed and the `.calendar` clause was unsatisfiable rather than merely
   unsatisfied — all 16 calendar item lines in the corpus refused with
   `itemCheck: fileKindShape`, four of them written exactly as §4.1 writes
   them.  `Core.shape` is `Field.viewShape` of the line now, so the rule is a
   real question about the bytes: true of `at:2026-09-07T12:50/13:50`
   (`the_spec_calendar_line_is_an_interval`, State.lean) and false of
   `plan-conflicts`' `- [ ] 3 Office hours  loc:JCL ^g7`, which is the line
   that fixture exists to have refused. -/
theorem a_loaded_line_always_satisfies_the_calendar_shape_rule
    (live : Site) (st : Status) (r : RawItem) :
    shapeWfFor DocKind.calendar
      { live := live, archive := none, status := st, line := r } = true := rfl

/- ======================================================================
   APPENDED — the cheats §3.1's field wiring makes available, and refuses.

   §3.1's item fields are **views of `Core.line`**, and §3.1's value types
   **are** §4.1's.  Each cheat below re-opens one of the two holes that were
   there before: a slot beside the line for a field to drift in, or a second
   definition of a type §4.1 already has.
   ====================================================================== -/

/- CHEAT 32 — the duplication itself: a `shape` slot on `Core`, settable
   without moving the bytes.  Two definitions of `Shape` in one kernel is how
   `est:` and the leading estimate came to disagree in the Rust; there is one
   `Shape` now and it is not something a record update can move. -/
def shapeSlotCheat (c : Core) (s : Field.Shape) : Core := { c with shape := s }

/- CHEAT 33 — a `stamps` slot beside the line, which is what `Core` used to
   carry.  `renderCore` prints the line, so a stamp written here is a stamp no
   file ever sees — and §6.3's month review cuts on "≥ 2 stamps". -/
def stampSlotCheat (c : Core) (st : Field.Stamp) : Core :=
  { c with stamps := c.stamps ++ [st] }

/- CHEAT 34 — `demote` that records the stamp without writing it.  This is the
   law the old `Core` satisfied: a line came through a demotion untouched,
   because the stamp had somewhere else to go. -/
theorem demote_leaves_the_line_alone (t : Site) (st : Field.Stamp) (e a : Entity)
    (h : demote t st e = .ok a) : a.val.line = e.val.line := by
  rw [lift_roundtrips _ _ h]

/- CHEAT 35 — refuse a lone `[-]` again.  §4.3's `month/2026-09.md#Demoted`
   holds one, `tm close month` carries it into the next month file without
   touching the week file it was paired with, and the Rust core resolves a key
   group of size one without looking for a partner.  `orphanDemotion` was the
   loader saying otherwise, and it is not a diagnostic any more. -/
def orphanDemotionCheat (i : Id) : LErr := .orphanDemotion i

-- ===========================================================================
-- APPENDED: the demotion pair — which line is the tombstone, and the bytes
-- that stand at it (State.lean / Plan.lean / Boundary.lean).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 36 — a tombstone that is a placement and nothing else.  This is the
   entity the whole corpus foundered on: one token vector, rendered at two
   sites, so §6.3's pair — the week line as it stood and the month copy with
   `est:` = remaining and `demoted:W37` appended — had no value that denotes
   it, and the loader called it `splitLine`.  A `Tomb` is a site **and** the
   bytes standing there, in one field, so "the archive has a placement but no
   text" is not a state that exists. -/
def tomblessArchiveCheat (live arch : Site) (st : Status) (r : RawItem) : Core :=
  { live := live, archive := some arch, status := st, line := r }

/- CHEAT 37 — the rule that made §4.3's fixture unreadable: force `[-]` on the
   record whenever a tombstone stands.  It was defensible as a reading of the
   *post-close* snapshot and it is false of every readopted item; the box at a
   live site is now the status and nothing else (`glyphAt_live`). -/
theorem a_record_beside_a_tombstone_always_reads_demoted
    (live arch : Site) (a l : RawItem) :
    glyphAt { live := live, archive := some ⟨arch, a⟩, status := .live .free, line := l } live
      = Glyph.demoted := rfl

/- CHEAT 38 — demand the horizon order of every demotion pair, not only of the
   ones whose boxes tie.  This is `demotionsOriented` as it was, and it is what
   refused three of the five fixture plans: §4.3's pair has its record live in
   a **week** and its archive in a **month**, so the archive's horizon does not
   precede the record's and never had to — the boxes settle that pair without
   consulting a file. -/
theorem every_tombstone_is_behind_its_record (p : WfPlan) (i : Id) (e : Entity) (r : Site)
    (hget : p.val.store.get i = some e) (harch : e.val.archiveSite = some r) :
    horizonPrecedes (docRegion p.val r.doc) (docRegion p.val e.val.live.doc) = true :=
  the_tombstone_is_behind_the_live_line p i e r hget harch

/- CHEAT 39 — refuse a pair whose two lines differ.  `LErr.splitLine` said "an
   entity owns one token vector, so there is no value that renders both", which
   was true of the model and never of the data: §6.3's close writes the two
   lines differently on purpose.  The constructor is gone. -/
def splitLineCheat (i : Id) : LErr := .splitLine i

/- CHEAT 40 — `demote` that writes one token vector to both sites, which is
   what it did before the tombstone carried its own bytes: the `demoted:` stamp
   §6.3 appends to the **copy** appeared in the week file too, and the week
   line the close was supposed to leave alone came back changed. -/
theorem demote_writes_one_token_vector (t : Site) (st : Field.Stamp) (e a : Entity)
    (h : demote t st e = .ok a) :
    a.val.archive = some ⟨e.val.live, a.val.line⟩ := by
  rw [demote_roundtrips _ _ _ _ h]

/- CHEAT 41 — `readopt` that reopens anything.  §6.3 says it "moves a *demoted
   line* into the current week (`[-]` → `[ ]`, stamp kept)", and run on a
   record that is already `[ ]` it consumes a tombstone whose bytes carry the
   `est:` and the stamp — so "stamp kept" is precisely what it loses, on the
   very pair this kernel was changed to admit.  `readopt` returns an `Except`
   now, and `KErr.notDemoted` is what it returns. -/
def readoptAnythingCheat (t : Site) (e : Entity) : Entity := readopt t e

/- CHEAT 42 — the assumption the withdrawn `demote_not_idem` rested on: that a
   second `demote` can succeed at all.  It is how the standing tombstone got
   overwritten and its file's line dropped from the render with the kernel
   returning `ok`.  §6.3 gives an item one archive record and the month close
   *moves* it, so the composite is `alreadyDemoted`
   (`demote_twice_is_not_a_thing`) — and a refutation whose second hypothesis
   has no witness is vacuous, which is why that law is withdrawn rather than
   kept.  `stamps_accumulate_across_readopt` is what replaces it. -/
theorem demote_twice_succeeds (t t' : Site) (st : Field.Stamp) (e a : Entity)
    (h1 : demote t st e = .ok a) : ∃ b, demote t' st a = .ok b :=
  ⟨_, rfl⟩

-- ===========================================================================
-- APPENDED: the `add` verb's freshness door (Plan.lean / Boundary.lean).
-- CHEAT 43 landed with the add session (9840ea8) but rode under the
-- demotion-pair banner above; this banner was added 2026-09-12 to say why
-- the block exists.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 43 — insert an item over a standing one.  `Store.set` demands
   `(get i).isSome = true`, `Store.insertFresh` demands the dual
   `(get i).isNone = true`, and handing the first proof to the second is a
   type error — which is the whole point: the two doors are complementary and
   there is no third door that takes neither proof.  Freshness for `add` is
   L21's theorem, not a runtime retry. -/
def insertOver (s : Store) (i : Id) (e : Entity) (h : (s.get i).isSome = true) :
    Store :=
  s.insertFresh i e h

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3 edit-widening session): the keyed edit's
-- bounded doors.  R10 says every bounded type crossing the wire goes through
-- the smart constructor its decoder uses; these are the three doors staying
-- shut when the smart constructor is bypassed.  Everything below must FAIL
-- to compile.
-- ===========================================================================

/- CHEAT 44 — a `ci` above the bound.  `EditVal.ci` carries `Fin 6`, so the
   wire value `7` cannot become a payload: `parseCi` is the smart constructor
   (`if h : n < 6`), and building the `Fin` by hand fails because `decide`
   cannot prove `7 < 6`. -/
def sneakCi : EditVal := .ci ⟨7, by decide⟩

/- CHEAT 45 — unset a key the edit path is not wired for.  `EditKey` demands
   `keyEditable k = true`, and `keyEditable .demoted` is `false` — `demoted:`
   is lifecycle state that `demote`/`readopt` own, and `rfl` here is a type
   error, not a policy comment.  The only door is `parseCmd`'s `dif`, which
   never opens for an unwired key. -/
def unsetDemoted : EditKey := ⟨.demoted, rfl⟩

/- CHEAT 46 — a day-carrying estimate.  `NdDur` demands `noDays = true`, and
   `(Dur.simple 3 .days).noDays` is `false`: `est=3d` dies in `ndDur?` on the
   wire, and here at `rfl`.  The value class is bounded in the type, not in a
   comment. -/
def dayEst : NdDur := ⟨Field.Dur.simple 3 Field.DurUnit.days, rfl⟩

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 2): the JSON round trip's one
-- hypothesis door.  `jval_jemit` is the induction under `jparse_jemit`, and
-- the numeral is the one value whose end is decided by the byte after it, so
-- the lemma demands `notDigitStart rest = true`.  This block is that door
-- staying shut.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 47 — read a numeral that is followed by a digit as if it stopped.
   `jval_jemit` would give `7` then `7` reading back as `(7, "7")`; the guard
   is `notDigitStart ['7'] = true`, which is `false`, so `rfl` is an
   application type mismatch.  The evaluated truth is
   `the_jval_jemit_digit_guard_bites`: those bytes read as `77`. -/
theorem sevenThenSevenReadsAsSeven :
    jval 4 (jemit (JVal.num 7) ++ ['7']) = .ok (.num 7, ['7']) :=
  jval_jemit (.num 7) 4 ['7'] (by decide) rfl

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, step 5: gap 40's bridges).  The eight keys
-- wired through `guardWf` carry wf-bounded subtypes, so the bound is in the
-- type (R10), not in a comment.  The controls — `⟨[.item "m1".toList], rfl⟩`
-- and `⟨.named "ab".toList, rfl⟩` — were checked to compile, so each failure
-- below is the bound and not `rfl` giving up.  Everything below must FAIL to
-- compile.
-- ===========================================================================

/- CHEAT 48 — an `after:` with no dependencies.  §4.1 has no empty `after:`
   (`depsWf` demands a non-empty list of well-formed deps), and `parseDeps`
   never yields one; building the payload by hand is `rfl` against
   `depsWf [] = true`, an application type mismatch. -/
def emptyAfter : EditVal := .after ⟨[], rfl⟩

/- CHEAT 49 — a `loc:` name that is not one word.  `WordLoc` demands
   `locOk`, whose `locWordOk` conjunct refuses a space: written, `loc:a b`
   would read back as `loc:a` and a title word `b`.  The wire refuses it as
   `badValue loc`; here it is `rfl` against `locOk (.named "a b") = true`. -/
def spacedLoc : WordLoc := ⟨.named "a b".toList, rfl⟩

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-4 session, step 2): `ClosePolicy` is a table, and a
-- table is only as good as the check that a corrupted row fails.  Each cheat
-- below corrupts one row and restates, over the corrupted table, the bridge
-- Close.lean proves over the real one (`closeStamp_names_the_closed_grain`,
-- `closePolicy_copies_only_below_month`).  The controls are those theorems,
-- which compile.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 50 — a day close that stamps a week stamp.  Swap the day row's stamp
   rule for `isoWeek` and the stamp it names is a week's, so the month review's
   "≥ 2 stamps" cut list would count a day's leftovers as a week's.  `decide`
   evaluates the corrupted row and proves the equation false. -/
def dayRowStampsAWeek (g : Grain) : ClosePolicy :=
  if g = day then { closePolicy g with stamp := .isoWeek } else closePolicy g

theorem dayRowStampsAWeek_names_the_closed_grain :
    (stampRuleOf (dayRowStampsAWeek day).stamp 0).map Field.Stamp.grain = some day := by
  decide

/- CHEAT 51 — a month close that leaves a tombstone.  Give the month row the
   week row's `copy` and it would demote a record a second time, which §6.3's
   month row does not do and `KErr.alreadyDemoted` refuses; the bridge's
   statement over the corrupted table is false at `month`, and `decide` says
   so. -/
def monthRowCopies (g : Grain) : ClosePolicy :=
  if g = month then { closePolicy g with disposition := .copy } else closePolicy g

theorem monthRowCopies_copies_only_below_month :
    ∀ g : Grain, (monthRowCopies g).disposition = .copy → g ≠ month := by
  decide

/- CHEAT 52 — minutes with a zero denominator.  The report emits an integer
   numerator and denominator and the host divides (AGENTS §8.2 rule 4); an
   `Arith.Pos` whose denominator is `0` would hand the host a division by zero
   inside a verified report.  `Q.ok ⟨300, 0⟩` is `false`, so `rfl` cannot prove
   it `true`. -/
def reportMinutesOverZero : CloseEntry :=
  ⟨"m2".toList, week, .copy, 0, 2, some (.week 36), some ⟨⟨300, 0⟩, rfl⟩⟩

/- CHEAT 53 — a disposition decoded from a near-miss name.  `CloseDid.ofName?`
   accepts exactly the four constructor names; reading `moved` as `move` is a
   host silently defaulting an unknown variant, which rule 2 exists to stop. -/
theorem movedDecodesAsMove : CloseDid.ofName? "moved".toList = some .move := by
  decide

/- CHEAT 54 — a close that invents its instant.  `ReqCmd.close` takes the
   request's `now` and `blockMin`; a command built without them is not a
   `ReqCmd` at all, so a host-side default has nowhere to hide. -/
def closeWithoutNow : ReqCmd := .close week

/- CHEAT 55 — a fast checker that is not the checker.  `@[csimp]` lets the
   compiler run a twin in place of a definition, and Fast.lean uses it for every
   hot conjunct of `planWf` (README gap 62); the licence is the equality.  The
   fastest `normalized` there is skips the rank check, and it has no proof of
   being `normalized`, so the swap never reaches the compiled kernel —
   `@[implemented_by]` would have taken it on trust (R4). -/
def normalizedSkip (_ : PlanCore) : Bool := true

@[csimp] theorem normalized_eq_normalizedSkip : @normalized = @normalizedSkip := by
  funext p; rfl

-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, step 2: gap 55 closed — the owner's D7 and
-- D8).  A past-due `persist` line at a week close moves to `backlog.md # Overdue`,
-- and the month rule "an outcome carries no date" reads outcomes only.  Each cheat
-- below is a door the step narrowed or opened, restated over what it must not
-- admit; the controls are `a_dated_record_loads_and_a_dated_outcome_does_not` and
-- `a_dated_month_outcome_is_rejected` (56), `closePolicy_routes_overdue_only_at_week`
-- (57) and `CloseDid.ofName?_refuses_near_overdue` (58), which compile.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 56 — a dated outcome loads.  D8 exempted `# Demoted` records from the
   month rule and nothing else: a month file whose `# Outcomes` line carries a
   `due:` is still refused, `itemCheck: fileKindShape`.  `decide` evaluates the
   loader and proves the equation false. -/
theorem datedOutcomeLoads : loadsOk datedOutcomeWitness = true := by
  decide

/- CHEAT 57 — a month close that routes overdue lines.  D7 is §6.3's week row
   ("moved to `backlog.md#Overdue` instead"); a month row with the same column
   would pull a dated `# Demoted` record out of the month review into the backlog,
   which no clause of §6.3 says.  The bridge's statement over the corrupted table
   is false at `month`. -/
def monthRowRoutesOverdue (g : Grain) : ClosePolicy :=
  if g = month then { closePolicy g with overdue := .toBacklogOverdue } else closePolicy g

theorem monthRowRoutesOverdue_routes_only_at_week :
    ∀ g : Grain, (monthRowRoutesOverdue g).overdue = .toBacklogOverdue ↔ g = week := by
  decide

/- CHEAT 58 — the fork-point report's name decoded as the kernel's.  The Rust
   `CloseReport` listed `overdue_to_backlog`; the wire's name is the constructor's,
   `moveOverdue`, and `CloseDid.ofName?` accepts exactly the six.  A host reading
   the old name as the new would be defaulting an unknown variant (rule 2). -/
theorem overdueToBacklogDecodes : CloseDid.ofName? "overdue_to_backlog".toList = some .moveOverdue := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, step 3: README gap 22 closed — the owner's
-- D6).  `Core.parent` is a view of the line, and a dangling or cyclic `@parent`
-- refuses the whole tree by name.  Each cheat below is a door the step closed;
-- the controls, which compile, are `Core.parent` and `coreOfLine_parent` (59),
-- `the_parent_tree_loads` and `a_typod_parent_refuses_the_whole_tree_by_name`
-- (60), and `a_parent_cycle_refuses_the_whole_tree_by_name` (61).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 59 — the stored slot, back.  A `parent` field beside the line is a second
   reader of `@O2` (AGENTS §5.3), and before D6 it disagreed with every file that
   carried one: it was `none` while the line said `@O2`.  There is no slot for a
   record update to set; the parent is what the bytes say. -/
def parentSlotCheat (c : Core) (j : Id) : Core := { c with parent := some j }

/- CHEAT 60 — a typo'd parent loads.  Fork-point `tm check` reported an `@ghost`
   parent and let every other command run; D6 refuses the tree, by name.  `decide`
   evaluates the loader and proves the equation false. -/
set_option maxRecDepth 40000 in
theorem typoParentLoads : loadsOk parentTypoWitness = true := by
  decide

/- CHEAT 61 — a cycle reported as a dangling link.  Both links of the ouroboros
   resolve, so the name is `parentCycle`: the dangling lemma's hypothesis is false
   at the cycle witness, and the two refusals cannot be confused. -/
set_option maxRecDepth 40000 in
theorem cycleIsDangling :
    loadPlan parentCycleWitness =
      .error (jone "err" (jone "itemCheck" (.str "danglingParent".toList))) :=
  loadPlan_refuses_a_dangling_parent _ true (by decide)

-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, step 4: goal B3 — the week row's child fold,
-- refuted as additive and performed by §6.4's `max`).  Each cheat below is a door
-- the step closed; the controls, which compile, are
-- `close_week_does_not_add_a_dropped_child_to_its_parent` (62),
-- `closePolicy_drops_children_only_at_week` (63), `CloseDid.ofName?_refuses_near_fold`
-- (64), `the_week_close_folds_dropped_children_on_a_loaded_plan` (65) and `close_dom`
-- with `close_week_drops_a_child_with_its_parent` (66).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 62 — the additive fold goal B3 stated.  `^p2` (`6b`) with its dropped `1b`
   subtask `^c3` would carry 350 minutes; §6.4's parent estimate already covers its
   decomposition, and the record reads 300.  `decide` runs the close on the loaded
   witness and proves the equation false. -/
set_option maxRecDepth 40000 in
theorem additiveFoldHolds :
    foldClosed (fun q => (q.val.store.get "p2".toList).map (fun f => remainingOf 50 f.val.line)) =
      some (some 350) := by
  decide

/- CHEAT 63 — a month close that drops children.  §6.3's child rule is the week row's;
   a month row with the same column would fold a `# Demoted` record's children into it
   at the month review's cut.  The bridge's statement over the corrupted table is false
   at `month`. -/
def monthRowDropsChildren (g : Grain) : ClosePolicy :=
  if g = month then { closePolicy g with children := .dropIntoParent } else closePolicy g

theorem monthRowDropsChildren_only_at_week :
    ∀ g : Grain, (monthRowDropsChildren g).children = .dropIntoParent ↔ g = week := by
  decide

/- CHEAT 64 — the fork-point report's list decoded as the kernel's name.  The Rust
   `CloseReport` listed `dropped_children`; the wire's name is the constructor's,
   `dropIntoParent`, and `CloseDid.ofName?` accepts exactly the nine. -/
theorem droppedChildrenDecodes : CloseDid.ofName? "dropped_children".toList = some .dropIntoParent := by
  decide

/- CHEAT 65 — a fold that forgets the stale parent.  `^p1` (`2b`) had `2b + 1b` of
   subtasks dropped with it; a close that dropped them and left the record at 100
   minutes would lose 50 minutes of open work (§0 principle 6).  The record reads
   150. -/
set_option maxRecDepth 40000 in
theorem staleParentKeepsItsEstimate :
    foldClosed (fun q => (q.val.store.get "p1".toList).map (fun f => remainingOf 50 f.val.line)) =
      some (some 100) := by
  decide

/- CHEAT 66 — the fork point's `remove_line_in`: a dropped child deleted from the plan.
   The kernel removes no entity (`close_dom`); `^c3` is still there, `[~]`. -/
set_option maxRecDepth 40000 in
theorem aDroppedChildIsDeleted :
    foldClosed (fun q => (q.val.store.get "c3".toList).isSome) = some false := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, repair: the mixed pair's order and `NhMm`
-- in the fold).  The controls, which compile, are `unitValue_renderDur` and
-- `the_week_close_folds_an_hours_and_minutes_child` (67, 68) and
-- `the_mixed_pair_keeps_its_order_on_the_loaded_witness` (69).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 67 — the stage-one reader blind to `NhMm`, as it was.  `unitValue` reads
   `2h30m` as 150; `decide` proves the equation false. -/
theorem hoursAndMinutesReadNothing : unitValue 50 "2h30m".toList = none := by
  decide

/- CHEAT 68 — the fold that loses an `NhMm` child.  `^p1` (`6b`) with `5h + 2h30m`
   dropped would keep a record with only its stamp, 150 minutes short of its
   children; the record carries `est:9b`. -/
set_option maxRecDepth 40000 in
theorem hoursAndMinutesChildIsLost :
    closedFileLines week closeHmWitness = some
      [["# Milestones".toList,
        "- [-] 6b Parent project ^p1".toList,
        "# Tasks".toList,
        "- [~] 5h Part one @p1 ^c1".toList,
        "- [~] 2h30m Part two @p1 ^c2".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 6b Parent project demoted:W36 ^p1".toList]] := by
  decide

/- CHEAT 69 — the mixed pair inverted.  A close that left `^p1`'s tombstone below the
   child `^c1` it dropped would reorder the week file it closed; the tombstone stands
   above. -/
set_option maxRecDepth 40000 in
theorem mixedPairInverts :
    foldClosed (fun q => match q.val.store.get "p1".toList, q.val.store.get "c1".toList with
      | some fp, some fc =>
        fp.val.archiveSite.map (fun t => decide (t.doc = fc.val.live.doc ∧ fc.val.live.rank < t.rank))
      | _, _ => none) = some (some true) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5 step 1: §6.4's `remaining` and §5.4's series
-- head).  The controls, which compile, are in Boundary.lean:
-- `remaining_reads_the_est_key_over_the_leading_estimate_on_a_loaded_plan` (70),
-- `remaining_of_a_settled_line_is_zero_on_a_loaded_plan` (71),
-- `remaining_sums_two_children_on_a_loaded_plan` (72),
-- `remaining_reads_dur_on_a_loaded_plan` (73) and
-- `the_series_head_skips_a_settled_member_on_a_loaded_plan` (74).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 70 — C1 re-entering through the rollup.  A rollup that read the leading
   estimate over the `est:` key would give `^a1` (`2b … est:30m`) its 120 minutes at a
   60-minute block; it has 30. -/
set_option maxRecDepth 40000 in
theorem theLeadingEstimateWinsOverTheKey : remainingMin 60 treePlan "a1".toList = 120 := by
  decide

/- CHEAT 71 — a Done line still owing its estimate.  `^d1` is `[x] 1b … est:40m`;
   fork-point `remaining_inner` answers `Some(0)` for a closed item, and so does the
   kernel. -/
set_option maxRecDepth 40000 in
theorem aDoneLineKeepsItsEstimate : remainingMin 60 treePlan "d1".toList = 40 := by
  decide

/- CHEAT 72 — a parent with no estimate reading nothing.  `^p1` writes no estimate;
   its children `30m` and `20m` sum to 50. -/
set_option maxRecDepth 40000 in
theorem aParentWithNoEstimateReadsNothing : remainingMin 60 treePlan "p1".toList = 0 := by
  decide

/- CHEAT 73 — `dur:` ignored.  `^w1` writes only `dur:30m`; `Item::own_remaining`
   reads it, and so does the kernel. -/
set_option maxRecDepth 40000 in
theorem aDurOnlyLineReadsNothing : remainingMin 60 treePlan "w1".toList = 0 := by
  decide

/- CHEAT 74 — the settled volume kept active.  `^v1` is `[x]`; the head of
   `## series:vols` is the next open member, `^v2`. -/
set_option maxRecDepth 40000 in
theorem theSettledVolumeIsTheHead : seriesHead treePlan 0 "vols".toList = some "v1".toList := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5 step 2: §7.1's priority, §7.2's rule table and
-- §7.4's hysteresis).  The controls, which compile, are in Priority.lean and
-- Boundary.lean: `prio_of_hot_is_zero` (75), `hysteresis_holds_one_step_back` (76),
-- `hysteresis_never_delays_hot` (77), `binsOf?_refuses_unsorted_edges` (78),
-- `rawPrio_of_pure_rank` (79), `finalPrio_of_an_optional` (80),
-- `zero_need_on_zero_capacity_is_hot` (81), `flooring_the_mixture_changes_the_bin`
-- (82) and `prio_reads_the_root_priority_on_a_loaded_plan` (83).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 75 — a `!4` root pushing a HOT item off the front.  §7.2: HOT is `p = 0`,
   whatever `k` is. -/
theorem hotYieldsToTheRootPriority : prio 4 Arith.Bin.hot = 4 := by
  decide

/- CHEAT 76 — hysteresis letting a four-step improvement through.  Yesterday `5`, raw
   `1`: §7.4 holds it at `4`. -/
theorem hysteresisLetsFourStepsThrough : hysteresis 5 1 = 1 := by
  decide

/- CHEAT 77 — hysteresis delaying HOT.  Yesterday `3`, raw `0`: "unless the new value
   is 0", so `0`, not `2`. -/
theorem hysteresisDelaysHot : hysteresis 3 0 = 2 := by
  decide

/- CHEAT 78 — gap 27's loader accepting swapped edges.  `[1/10, 1/2]` is antitone but
   not §7.1's ladder; `binsOf?` refuses it. -/
theorem swappedBinsAccepted : (binsOf? [⟨1, 10⟩, ⟨1, 2⟩]).isSome = true := by
  decide

/- CHEAT 79 — a corrupted row of §7.2's table: pure rank as `k + 3`.  The row is
   `k + 2`. -/
theorem theRankRowIsKPlusThree : (rowTable .rank).1 = .kPlus (.plus 3) := by
  decide

/- CHEAT 80 — a corrupted column of §7.2's table: `optional.md` damped by hysteresis.
   §7.2 pins it at `5` (fork-point `priority::compute`'s deviation 5). -/
theorem anOptionalIsDamped : (rowTable .optional).2 = true := by
  decide

/- CHEAT 81 — gap 25 decided the float's way.  `0/0` at a rational availability is
   HOT, not the lowest bin. -/
theorem zeroOverZeroIsTheLowestBin : binOfQ Arith.defaultBins 0 (Arith.posOfNat 0) = .plus 3 := by
  decide

/- CHEAT 82 — D10's mixture floored.  `156½` minutes and `156` put a 78-minute need in
   different bins. -/
theorem theMixtureMayBeFloored :
    binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.mkPos 313 2 (by decide))
      = binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 156) := by
  decide

/- CHEAT 83 — §7.1's `k` read as the default instead of the root's `!k`.  `^t1`'s root
   `^O1` writes `!1`. -/
set_option maxRecDepth 40000 in
theorem theRootPriorityIsIgnored : rootK parentTreePlan.val specDefaultPrio "t1".toList = 3 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5 step 3: §7.3's EDF reservation pass over D10's
-- rational capacity).  Banner added by the stage-5 repair; cheats 84-90 were
-- committed at fea3f81 under the step-2 banner above.  The controls, which
-- compile, are in Capacity.lean and Boundary.lean:
-- `reserve_takes_the_best_levels_earliest` (84),
-- `edf_spends_before_the_deadline_and_not_after_on_a_witness` (85, 86),
-- `edf_serves_the_earlier_deadline_first_on_a_witness` (87, 88),
-- `flooring_the_capacity_changes_the_verdict` (89), `denOf?_refuses_zero` (90)
-- and `edf_serves_a_loaded_plans_needs_earliest_deadline_first`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 84 — `capacity::reserve`'s inner loop run upward: the lowest matching level
   spent first.  30 minutes at `ci ≥ 3` from `[0,0,0,60,60,60]` come off level 5. -/
theorem theLowestMatchingLevelGoesFirst :
    (reserveRest 8 3 [DayCapacity.ofLevels 7 [0, 0, 0, 60, 60, 60]] 30).map DayCapacity.levels =
      [[0, 0, 0, 30, 60, 60]] := by
  decide

/- CHEAT 85 — a later day spent before an earlier one.  Earliest day first. -/
theorem aLaterDayGoesFirst :
    (reserveRest 2 3 edfExampleCaps 30).map DayCapacity.levels =
      [[0, 0, 0, 60, 0, 0], [0, 0, 0, 30, 0, 0]] := by
  decide

/- CHEAT 86 — a reservation taken after the deadline.  A 90-minute need due on day 1
   finds 60 minutes and leaves day 2 whole; it does not borrow day 2's. -/
theorem aDayAfterTheDeadlineIsSpent :
    (edf Den.one edfExampleCaps [⟨90, 3, 1⟩]).map DayCapacity.levels =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 30, 0, 0]] := by
  decide

/- CHEAT 87 — the deadlines served in input order.  §7.3 sorts by due: day 1 first. -/
theorem inputOrderIsServed :
    (edfGrants Den.one edfExampleCaps edfExampleDeadlines).map (fun g => g.deadline.due) = [2, 1] := by
  decide

/- CHEAT 88 — the shortfall hidden.  The due-2 deadline is 30 minutes short, and says so. -/
theorem theShortfallIsHidden :
    (edfGrants Den.one edfExampleCaps edfExampleDeadlines).map (fun g => g.shortfall 1) = [0, 0] := by
  decide

/- CHEAT 89 — D10's mixture floored before the pass.  `30½ + 30½` minutes meet a 61-minute
   need; `30 + 30` do not, so §7.3's IMPOSSIBLE verdict differs. -/
theorem theMixtureMayBeFlooredForTheVerdict :
    (edfGrants halfDen mixtureCaps [⟨61, 4, 1⟩]).map (fun g => g.impossible halfDen) =
      (edfGrants Den.one flooredCaps [⟨61, 4, 1⟩]).map (fun g => g.impossible Den.one) := by
  decide

/- CHEAT 90 — a zero denominator accepted as the lookahead's unit (R10). -/
theorem aZeroDenominatorIsAccepted : (denOf? 0).isSome = true := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L1: the exact mixture,
-- `Lookahead.lean`).  Numbers are the design's reserved labels (design §16):
-- 108 and 109 are L1's; 117 is L5's label, taken here because the refutation it
-- inverts moved into L1 (README "Stage 5 D10 L1").  The merge renumbers.  The
-- controls, which compile, are in Lookahead.lean: `mix_at_zero_is_home` and
-- `mix_on_a_witness` (108), `mkWeight?_above_one` and `mkWeight?_on_witnesses`
-- (109), `mixing_before_the_budget_is_not_the_expectation` and
-- `mixing_before_the_budget_on_the_witness` (117).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 108 — D10's mixture with `w` and `capDen − w` swapped: the lounge weighed by
   `1 − p`.  At weight 0 the day must be home's, which has nothing at level 5. -/
def swappedMix (w : Look.Weight) (L H : Look.Hist) : Look.Hist := fun l =>
  (Look.capDen - w.val) * L l + w.val * H l

theorem theSwappedMixIsHomeAtZero :
    swappedMix Look.Weight.home (Look.histOf [0, 0, 0, 0, 0, 60]) (Look.histOf [0, 0, 0, 120, 0, 0]) 5
      = Look.capDen * Look.histOf [0, 0, 0, 120, 0, 0] 5 := by
  decide

/- CHEAT 109 — a weight above one accepted: `3/2` decoded as `1.5 · capDen`.  The type
   refuses the value, and `mkWeight?` refuses the pair by name. -/
def threeHalvesIsAWeight : Look.Weight := ⟨1500000000000000000, by decide⟩

theorem mkWeightAcceptsThreeHalves :
    (Look.mkWeight? 3 2).map Subtype.val = .ok 1500000000000000000 := by
  rfl

/- CHEAT 117 — mixing before the budget limit taken for the expectation.  Budget 60,
   lounge 60 at levels 5 and 4, home 120 at level 3, `p = ½`: the expected day keeps
   30 minutes at level 3, and the limited mixture keeps none. -/
theorem mixingBeforeTheBudgetIsTheExpectation :
    Look.mix Look.halfWeight (Look.limitHist 60 Look.budgetWitnessL) (Look.limitHist 60 Look.budgetWitnessH) 3
      = Look.limitHist (60 * Look.capDen) (Look.mix Look.halfWeight Look.budgetWitnessL Look.budgetWitnessH) 3 := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step A2: JSON gains an exact decimal;
-- gaps 42 and 43).  Numbered 119-121 because the design labels cheats 91-118
-- (its §16) and the D10 track numbers in parallel; the merge renumbers.  The
-- controls, which compile, are in Json.lean: `JVal.ofDec_plain` and
-- `jparse_reads_a_signed_decimal_as_dec` (119), `the_jval_jemit_fraction_guard_bites`
-- and `jval_jemit` over `numEnd` (120), and `jparse_reads_an_exponent_as_written`
-- (121).  CHEAT 47's guard is now `numEnd`, whose first conjunct is the
-- `notDigitStart` its comment names; it still fails for that reason.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 119 — a bare natural built as a decimal.  `7` would then have two values,
   `num 7` and `dec 7`, and `jparse` could return only one of them, so
   `jparse_jemit` would be false.  `JVal.dec` demands `d.plain = false`, and
   `⟨false, 7, [], none⟩.plain` is `true`: `rfl` is a type error. -/
def sevenAsADecimal : JVal := .dec ⟨⟨false, 7, [], none⟩, rfl⟩

/- CHEAT 120 — read a numeral followed by a fraction as if it stopped.
   `jval_jemit` would give `1` then `.5` reading back as `(1, ".5")`; the guard
   is `numEnd ['.', '5'] = true`, which is `false`, so `rfl` is an application
   type mismatch.  The old guard `notDigitStart` would have let it through;
   the evaluated truth is `the_jval_jemit_fraction_guard_bites`: `1.5`. -/
theorem oneThenAFractionReadsAsOne :
    jval 4 (jemit (JVal.num 1) ++ ['.', '5']) = .ok (.num 1, ['.', '5']) :=
  jval_jemit (.num 1) 4 ['.', '5'] (by decide) rfl

/- CHEAT 121 — an exponent marker with no digit.  The design's `JDec` stored the
   exponent as a sign and a digit list, where `some (false, [])` emits `1e`, which
   no reader takes back (`jparse_refuses_a_numeral_missing_a_digit`).  Here the
   exponent is a first digit and the rest, so the empty list is not an exponent. -/
def aBareExponentMarker : JDec := ⟨false, 1, [], some (false, [])⟩


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B1: instants, offsets and the
-- zone table in Cal.lean).  Numbered 91 and 92, the design's own labels for B1
-- (its §16); nothing in this checkout had taken them.  The D10 track numbers in
-- parallel and the merge renumbers.  The controls, which compile, are in
-- Cal.lean: `chicago_2026_offsets` and `offsetAt_reads_the_last_transition`
-- (91), `the_written_clock_is_not_the_instant_order` and `Instant.lt_irrefl`
-- (92).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 91 — a zone transition applied one second early.  Chicago springs
   forward at 2026-03-08T08:00:00Z; at 07:59:59Z the last transition at or before
   the instant is none, so `offsetAt` reads the base −06:00
   (`offsetAt_reads_the_last_transition`, `chicago_2026_offsets`), and claiming
   −05:00 there is false: `decide` refuses it. -/
theorem aTransitionAppliedOneSecondEarly :
    Cal.offsetAt Cal.chicago ⟨63908553599, 0⟩ = ⟨true, 18000⟩ := by
  decide

/- CHEAT 92 — two stamps of one instant ordered by their written clocks.
   `2026-09-07T22:00:00-05:00` reads earlier on the clock than
   `2026-09-08T03:00:00+00:00`, but local time minus offset is one UTC second
   for both (`the_written_clock_is_not_the_instant_order`), and no instant is
   before itself (`Instant.lt_irrefl`): `decide` refuses the order. -/
theorem twoStampsOfOneInstantOrderedByTheirClocks :
    (⟨(Cal.utcSecAt ⟨true, 18000⟩ (Cal.toDay ⟨2026, 9, 7⟩ * 86400 + 22 * 3600)).getD 0, 0⟩ :
        Cal.Instant)
      < ⟨(Cal.utcSecAt Cal.Offset.utc (Cal.toDay ⟨2026, 9, 8⟩ * 86400 + 3 * 3600)).getD 0, 0⟩ := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L2: the day's window, E7, in
-- `Lookahead.lean`).  Numbers 110 and 111 are the design's own L2 labels (its
-- §16); nothing in this checkout had taken them.  The D9 track numbers in
-- parallel and the merge renumbers.  The controls, which compile, are in
-- Lookahead.lean: `the_window_end_is_not_the_least_solution_over_walls_wholly_inside`
-- and `the_window_end_is_the_least_solution` (110),
-- `the_window_end_solves_the_equation` and `overlapping_walls_count_once` (111).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 110 — walls counted only when wholly inside the window (Goals.lean
   STAGE 6's `wallsInside`).  Arrival 07:00, eight hours, cap 19:00, a wall
   14:50–15:50: the stage-6 equation is solved at 15:00, because the wall is not
   wholly inside `[07:00, 15:00]`.  The fork, and `windowEnd`, extend the window
   by the wall's whole hour to 16:00, so claiming 15:00 is false: `decide`
   refuses it. -/
theorem theWindowEndCountsOnlyWallsWhollyInside :
    Look.windowEnd 420 480 1140 [(890, 950)]
      = min (420 + 480) 1140 + Look.wallsInside 420 900 [(890, 950)] := by
  decide

/- CHEAT 111 — overlapping walls not merged before the walk.  Walls 10:00–11:40
   and 10:50–12:30 each extend the window by their own length, 200 minutes, where
   their union is 150: the unmerged walk ends at 18:20 and the least solution of
   E7 at 17:30 (`the_window_end_solves_the_equation`,
   `overlapping_walls_count_once`).  `decide` refuses the equality. -/
def unmergedWindowEnd (a wm wc : Nat) (ws : List (Nat × Nat)) : Nat :=
  (Look.sortByStart (Look.clipWalls a ws)).foldl Look.extendStep (Look.windowBase a wm wc)

theorem theUnmergedWalkIsTheWindowEnd :
    unmergedWindowEnd 420 480 1140 [(650, 750), (600, 700)]
      = Look.windowEnd 420 480 1140 [(650, 750), (600, 700)] := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L3: the slot cut in
-- `Lookahead.lean`).  Numbers 112 and 113 are the design's own L3 labels (its
-- §16); nothing in this checkout had taken them.  The D9 track numbers in
-- parallel and the merge renumbers.  Each cheat is the real loop with one line
-- changed, run over the same free stretches, and claimed equal to `cutSlots` on
-- a fork-test window.  The controls, which compile, are in Lookahead.lean:
-- `a_cut_never_ends_on_a_break` and `every_break_is_followed_by_a_slot` (112),
-- `a_cut_never_ends_on_a_break` and `cutSlots_short_block_is_at_least_min_last`
-- (113).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 112 — a stretch that ends on a break: the loop places a due break
   without checking that `min_last` still fits after it.  From 07:00 to 09:45
   the break due at 09:00 leaves 25 minutes, so the fork places neither it nor a
   block (`a_cut_never_ends_on_a_break`); the cheat places the break and ends
   the stretch on it, which `every_break_is_followed_by_a_slot` forbids.
   `decide` refuses the equality.  (The design names the §4.3 cut as this
   cheat's witness, but the guard never fires on that day, so the cheat and the
   fork agree there; see the README's L3 block.) -/
def cutStretchEndingOnABreak (c : Look.CutCfg) (stop : Nat) :
    Nat → Nat → Nat → Look.CutAcc → Nat × Look.CutAcc
  | 0, _, k, acc => (k, acc)
  | fuel + 1, t, k, acc =>
    if t < stop then
      if (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k then
        cutStretchEndingOnABreak c stop fuel (t + 60 * c.breakMin) 0
          (acc.1, (t, t + 60 * c.breakMin) :: acc.2)
      else if t + 60 * c.blockMin ≤ stop then
        cutStretchEndingOnABreak c stop fuel (t + 60 * c.blockMin) (k + 1)
          (⟨t, t + 60 * c.blockMin, .block⟩ :: acc.1, acc.2)
      else if t + 60 * c.minLast ≤ stop then
        cutStretchEndingOnABreak c stop fuel stop (k + 1) (⟨t, stop, .short⟩ :: acc.1, acc.2)
      else (k, acc)
    else (k, acc)

def cutEndingOnABreak (c : Look.CutCfg) (lo hi : Nat) (walls : List (Nat × Nat)) : Look.Cut :=
  let r := (Look.freeIntervals lo hi walls).foldl
    (fun acc iv => cutStretchEndingOnABreak c iv.2 (iv.2 - iv.1 + 1) iv.1 acc.1 acc.2) (0, ([], []))
  ⟨r.2.1.reverse, r.2.2.reverse⟩

theorem aStretchEndsOnABreak :
    cutEndingOnABreak Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 585) []
      = Look.cutSlots Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 585) [] [] 0 := by
  decide

/- CHEAT 113 — the short last block dropped at exactly `min_last`: the loop
   keeps a tail only when it is strictly longer than `min_last`.  From 07:00 to
   09:50 the fork places the break at 09:00 and a 30-minute short block after it
   (`a_cut_never_ends_on_a_break`; `cutSlots_short_block_is_at_least_min_last`
   allows exactly `min_last`); the cheat drops the block and so ends on the
   break.  `decide` refuses the equality. -/
def cutStretchDroppingAtMinLast (c : Look.CutCfg) (stop : Nat) :
    Nat → Nat → Nat → Look.CutAcc → Nat × Look.CutAcc
  | 0, _, k, acc => (k, acc)
  | fuel + 1, t, k, acc =>
    if t < stop then
      if (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k then
        if stop < t + 60 * c.breakMin + 60 * c.minLast then (k, acc)
        else cutStretchDroppingAtMinLast c stop fuel (t + 60 * c.breakMin) 0
          (acc.1, (t, t + 60 * c.breakMin) :: acc.2)
      else if t + 60 * c.blockMin ≤ stop then
        cutStretchDroppingAtMinLast c stop fuel (t + 60 * c.blockMin) (k + 1)
          (⟨t, t + 60 * c.blockMin, .block⟩ :: acc.1, acc.2)
      else if t + 60 * c.minLast < stop then
        cutStretchDroppingAtMinLast c stop fuel stop (k + 1) (⟨t, stop, .short⟩ :: acc.1, acc.2)
      else (k, acc)
    else (k, acc)

def cutDroppingAtMinLast (c : Look.CutCfg) (lo hi : Nat) (walls : List (Nat × Nat)) : Look.Cut :=
  let r := (Look.freeIntervals lo hi walls).foldl
    (fun acc iv => cutStretchDroppingAtMinLast c iv.2 (iv.2 - iv.1 + 1) iv.1 acc.1 acc.2) (0, ([], []))
  ⟨r.2.1.reverse, r.2.2.reverse⟩

theorem theShortBlockDroppedAtMinLast :
    cutDroppingAtMinLast Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 590) []
      = Look.cutSlots Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 590) [] [] 0 := by
  decide



-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L4: energy and the budget limit
-- in `Lookahead.lean`).  Numbers 114, 115 and 116 are the design's own L4 labels
-- (its §16); nothing in this checkout had taken them.  The D9 track numbers in
-- parallel and the merge renumbers.  Each cheat is the real function with one
-- step changed, claimed to agree with the fork on a fork-test input.  The
-- controls, which compile, are in Lookahead.lean: `futureEnergy_home_is_capped`
-- and `energize_applies_the_home_cap` (114), `the_bucket_reads_seconds` and
-- `the_bucket_reads_seconds_on_the_spec_day` (115), `buckets_clamp` and
-- `predict_uses_the_learned_curve` (116).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 114 — no home cap: a future home day's slot energy is the prediction
   itself.  At 08:00 on the spec day, woken at 06:05, the shipped home prior is
   `1-4`'s 4, above `home_max_ci = 3`, which the fork's `cap_for_location` (and
   `futureEnergy_home_is_capped`) forbid.  `decide` refuses the claim. -/
def futureEnergyWithoutTheHomeCap (c : Look.Curves) (_homeMax : Nat) (loc : Look.Loc)
    (wake t : Cal.Instant) : Fin 6 :=
  Look.predictAt c loc.curve (Look.hswAt wake t)

theorem theHomeCapDropped :
    (futureEnergyWithoutTheHomeCap Look.Curves.shipped 3 .home ⟨Look.onTheSpecDay 365, 0⟩
      ⟨Look.onTheSpecDay 480, 0⟩).val ≤ 3 := by
  decide

/- CHEAT 115 — hours since wake from whole minutes: the wake and the slot are
   read as clock minutes before subtracting.  Woken at 06:05:40, a slot at 07:05
   is 3,560 seconds away, `hsw` 0.99 and bucket 0 in the fork; whole minutes say
   60 and bucket 1 (CRIT 6).  `decide` refuses the equality. -/
def hswFromWholeMinutes (wake t : Cal.Instant) : Int :=
  Look.hsw100 (60 * ((t.sec / 60 : Nat) - (wake.sec / 60 : Nat) : Int))

theorem hoursSinceWakeFromWholeMinutes :
    Look.bucket (hswFromWholeMinutes ⟨Look.onTheSpecDay 365 + 40, 0⟩ ⟨Look.onTheSpecDay 425, 0⟩)
      = Look.bucket (Look.hswAt ⟨Look.onTheSpecDay 365 + 40, 0⟩ ⟨Look.onTheSpecDay 425, 0⟩) := by
  decide

/- CHEAT 116 — the hours-since-wake bucket without its clamp to `0..11`: the
   learned curve is indexed by `floor(hsw)` itself.  At 30 hours the fork's
   `Model::energy_at` reads the fixture lounge curve's last entry, 2
   (`predict_uses_the_learned_curve`); the unclamped index 30 is past the
   curve's 12 entries and reads nothing.  `decide` refuses the equality. -/
def bucketWithoutTheClamp (h : Int) : Nat := if h ≤ 0 then 0 else h.toNat / 100

def learnedWithoutTheClamp (energy : List (List Char × List Nat)) (curve : List Char) (h : Int) :
    Option Nat :=
  (Look.curveLookup energy curve).bind (fun c => c[bucketWithoutTheClamp h]?)

theorem theBucketWithoutItsClamp :
    learnedWithoutTheClamp Look.fixtureEnergy Look.loungeKey 3000
      = Look.learnedLevel Look.fixtureEnergy Look.loungeKey 3000 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B2: the log's timestamps in
-- `Stamp.lean`).  The design's §16 gives B2 no cheat label, so 126 and 127 are
-- taken above the highest number in this checkout (125, W-1's repair); the D10
-- track numbers in parallel and the merge renumbers.  The controls, which
-- compile, are in Stamp.lean: `renderStamp_is_fmt_timestamp` (126) and
-- `a_leap_second_stamp_is_before_the_next_second` with `stampBefore_iff` (127).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 126 — a UTC stamp written with `Z`.  The fork's `fmt_timestamp` is
   `to_rfc3339_opts(SecondsFormat::Secs, false)`, and `use_z = false` writes
   UTC as `+00:00` (`renderStamp_is_fmt_timestamp`).  Claiming the writer's
   bytes for `2026-09-08T03:00:00Z` end in `Z` is false: `decide` refuses it. -/
theorem aUtcStampWrittenWithZ :
    LogStamp.renderStamp ⟨⟨63924433200, 0⟩, by decide⟩ ⟨⟨false, 0⟩, by decide⟩ =
      ['2','0','2','6','-','0','9','-','0','8','T','0','3',':','0','0',':','0','0','Z'] := by
  decide

/- CHEAT 127 — stamps ordered by nanosecond counts.  chrono orders a
   `DateTime<FixedOffset>` by its UTC `(secs, frac)`, and a leap second
   `2016-12-31T23:59:60.5Z` is before `2017-01-01T00:00:00Z`
   (`a_leap_second_stamp_is_before_the_next_second`).  An order by
   `Instant.nanos` puts it after, so claiming that order agrees with
   `stampBefore` on this pair is false (carried note 1): `decide` refuses it. -/
def stampBeforeByNanos (a b : Cal.VInstant × Cal.VOffset) : Bool :=
  decide (a.1.val.nanos < b.1.val.nanos)

theorem stampsOrderedByNanoseconds :
    stampBeforeByNanos (⟨⟨63618825599, 1500000000⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
        (⟨⟨63618825600, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
      = LogStamp.stampBefore (⟨⟨63618825599, 1500000000⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
        (⟨⟨63618825600, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B3: the typed event grammar in
-- `Log.lean`).  The design's §16 labels these 93, 94 and 106; those numbers are
-- the design's reserved-unused ones (W-1's repair left them unused), so the
-- block takes 128, 129 and 130, above the highest number in this checkout (127,
-- B2).  The D10 track numbers in parallel and the merge renumbers.  The
-- controls, which compile, are in Log.lean: `an_unknown_tag_is_never_a_warning`
-- with `malformed_line_9_is_an_unknown_mood` (128),
-- `a_known_event_is_never_read_as_unknown` with
-- `malformed_line_5_is_a_done_with_est_min_sixty` (129), and
-- `an_out_of_range_numeral_warns_even_in_an_unknown_event` (130).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 128 — an unknown tag read as a warning.  A reader that refuses every
   tag it does not know turns the fork's `{"ev":"mood","level":3}` (the fixture's
   line 9, an `Event::Unknown`) into a warning.  Claiming that reader keeps
   `an_unknown_tag_is_never_a_warning` on that line is false: once the kernel's
   verdict is rewritten in (`malformed_line_9_is_an_unknown_mood`), `decide`
   refuses it. -/
def readLineRefusingUnknownTags (n : Nat) (seg : Option (List Char)) : Log.Verdict :=
  match Log.readLine n seg with
  | .entry ⟨_, _, _, .unknown _ _⟩ => .warn n .notAnObject
  | v => v

theorem anUnknownTagReadAsAWarning :
    readLineRefusingUnknownTags 9 (some Log.malformedLine9) ≠ .warn 9 .notAnObject := by
  simp only [readLineRefusingUnknownTags, Log.malformed_line_9_is_an_unknown_mood.1, Log.malformedEntry9]
  decide

/- CHEAT 129 — a known event with a bad field read as `unknown`.  serde's
   derived `Known` never falls back: `est_min:"sixty"` on a `done` is the
   warning `event "done": est_min: …`.  A reader that files a bad payload under
   `unknown` instead reads the fixture's line 5 as an unknown event, so claiming
   `a_known_event_is_never_read_as_unknown` of it is false: `decide` refuses it on
   the line's value (never its 96 characters). -/
def readObjectFallingThroughToUnknown (n : Nat) (kvs : List (List Char × JVal)) : Log.Verdict :=
  match Log.readObject n kvs with
  | .warn _ (.badField _) =>
    match Log.readT kvs, Log.lastVal kvs Log.kEv with
    | .ok (t, o), some (.str tag) => .entry ⟨n, t, o, .unknown tag []⟩
    | _, _ => .warn n .noEv
  | v => v

def malformedPairs5 : List (List Char × JVal) :=
  match Log.malformedValue5 with
  | .obj kvs => kvs
  | _ => []

theorem aBadFieldReadAsUnknown :
    (match readObjectFallingThroughToUnknown 5 malformedPairs5 with
     | .entry e => e.ev.isUnknown
     | _ => false) = false := by
  decide

/- CHEAT 130 — `finiteF64` applied only to `hsw` (CRIT 15).  The fork collects
   the whole line as a `Map<String, Value>` before it reads a field, so `1e400`
   under any key of any event fails the line.  A reader that checks only `hsw`
   reads `{"t":…,"ev":"mood","x":1e400}` as an entry; claiming it warns
   `numberOutOfRange` there, as
   `an_out_of_range_numeral_warns_even_in_an_unknown_event` says the kernel does,
   is false: `decide` refuses it. -/
def readValueCheckingOnlyHsw (n : Nat) (v : JVal) : Log.Verdict :=
  match v with
  | .obj kvs =>
    match Log.lastVal kvs ['h','s','w'] with
    | some (.dec d) => if Log.finiteF64 d.val then Log.readObject n kvs else .warn n .numberOutOfRange
    | _ => Log.readObject n kvs
  | _ => .warn n .notAnObject

def moodOutOfRangeValue : JVal :=
  .obj [(Log.kT, .str ['2','0','2','6','-','0','9','-','0','7','T','0','8',':','0','0',':','0','0','-','0','5',':','0','0']),
    (Log.kEv, .str ['m','o','o','d']), (['x'], .dec ⟨⟨false, 1, [], some (false, 4, [0, 0])⟩, rfl⟩)]

theorem finiteF64CheckedOnlyAtHsw :
    (match readValueCheckingOnlyHsw 1 moodOutOfRangeValue with
     | .warn _ .numberOutOfRange => true
     | _ => false) = true := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B4: the `tz` and `log` sections
-- of the request, Boundary.lean).  The design's §16 names no B4 cheat; these two
-- guard its R10 constructors.  They take 131 and 132, above the highest number in
-- this checkout (130, B3); the D10 track numbers in parallel and the merge
-- renumbers.  The controls, which compile, are in Boundary.lean:
-- `readTz_refuses_by_name` (131) and
-- `mkLogReq?_refuses_a_render_line_outside_the_tail` (132).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 131 — a zone table built without `Cal.mkTz?`.  Rust sends the
   transitions; a decoder that wraps them in a `Cal.Tz` by asserting the proof
   would let two transitions out of order through, and `offsetAt` would read the
   last one written rather than the last one in time.  `Cal.Tz` is a subtype of
   `TzTable.wf = true`, so the assertion is a type error: `rfl` cannot prove
   `false = true`. -/
def unsortedZone : Cal.Tz :=
  ⟨⟨['k'], ⟨false, 0⟩, [(⟨200, 0⟩, ⟨false, 3600⟩), (⟨100, 0⟩, ⟨false, 0⟩)]⟩, rfl⟩

/- CHEAT 132 — a render line outside the tail answered.  A request whose tail is
   line 2 alone asks for line 1; `mkLogReq?` refuses it `renderNotInTail`, so
   claiming the request is accepted is false: `decide` refuses it. -/
theorem aRenderLineOutsideTheTailAccepted :
    (mkLogReq? ⟨2, [some ['x']], true, none, [1], false, Replay.utcZone⟩).toBool = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L5: the lookahead in
-- `Lookahead.lean`).  Numbers 133 and 134 (126 and 127 on the branch, renumbered at the merge of
-- the D9 track's B2-B4, which took 126-132) were the next free numbers in this
-- checkout (the highest was 125, after W-1's repair).  The design's L5 label,
-- 117 (mixing before the budget limit), was taken by L1 and still fails there.
-- The D9 track numbers in parallel and the merge renumbers.  Each cheat is the
-- real function with one step changed, claimed to agree with the fork on a
-- fork-shaped input.  The controls, which compile, are in Lookahead.lean:
-- `a_future_day_reads_todays_wake_to_the_second` (133) and
-- `sunday_mixes_at_its_own_weight` (134).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 133 — a future day's wake at whole minutes: `local_dt` of today's wake clock with
   its seconds dropped.  On Tuesday 2026-09-08 with a 07:05 arrival and a wake at 06:05:40,
   the fork puts the 07:05 block at 0.99 h (the lounge's `0-1`, level 4) and keeps 180
   minutes at level 5; whole minutes put it at 1.00 h (level 5) and keep 240.  `decide`
   refuses the equality. -/
def pureDayWakingOnTheMinute (I : Look.Input) (loc : Look.Loc) (d : Nat) : Look.Hist :=
  Look.limitHist (Look.budgetMinOf I.day) (Look.histOf' (Look.energize I.curves I.homeMax loc
    (Cal.instantOf I.tz d ⟨I.wake.sec / 60 % 1440, Nat.mod_lt _ (by decide)⟩) (Look.dayCut I d).slots))

theorem aFutureWakeOnTheMinute :
    pureDayWakingOnTheMinute { Look.specInput with arrival := fun _ => 425, wake := ⟨6 * 3600 + 5 * 60 + 40, 0⟩ }
        .lounge 739866 5
      = Look.pureDay { Look.specInput with arrival := fun _ => 425, wake := ⟨6 * 3600 + 5 * 60 + 40, 0⟩ }
        .lounge 739866 5 := by
  decide

/- CHEAT 134 — every future day mixed at today's weekday's weight.  The fork reads
   `p_lounge_on(date.weekday())` for each date: on Sunday 2026-09-13 the shipped 0.4, where
   Monday's is 0.9.  The Sunday lounge day keeps 120 minutes at level 5, so the expected level
   5 is 48 minutes and the cheat's 108.  `decide` refuses the equality. -/
def dayOfAtTodaysWeight (I : Look.Input) (i : Nat) : DayCapacity :=
  if i = 0 then Look.ofHist I.today (Look.day0Hist I)
  else Look.mixDay (I.today + i) (I.weight (Cal.weekdayOf I.today))
    (Look.pureDay I .lounge (I.today + i)) (Look.pureDay I .home (I.today + i))

theorem everyDayAtTodaysWeight :
    (dayOfAtTodaysWeight Look.specInput 6).numAt 5 = (Look.dayOf Look.specInput 6).numAt 5 := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L6 (design §13.6, §14.8 row
-- L6): capacity on the wire.  Numbers 135, 136 and 137 (128-130 on the branch, renumbered at the merge)
-- were the next free
-- numbers in this checkout (the highest was L5's).  The D9 track numbers
-- in parallel and the merge renumbers.  The controls, which compile, are
-- `CapWire.readWeight_on_witnesses` and `readWeight_refuses_more_than_18_places`
-- (135), `Look.curveOk_refuses_an_unsorted_curve` and `CapWire.readPrior_on_witnesses`
-- (136), and `CapWire.the_lookahead_response_emits_in_build_order` (137), in
-- Lookahead.lean and Boundary.lean.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 135 — a lounge weight of 19 decimal places accepted on the wire.  `10^-19` sent as
   the digit strings `1` / `10000000000000000000` does not divide `capDen = 10^18` (D17), so
   the wire refuses it `weightPrecision`; `decide` refuses the claim that it reads. -/
theorem aWeightOf19PlacesReads :
    (CapWire.readWeight .model .tuesday (CapWire.pairJ (.str ['1'])
      (.str ['1', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']))).isOk
      = true := by
  decide

/- CHEAT 136 — a prior curve accepted out of `from` order.  Fork `StepFn::from_pairs` sorts a
   curve by its start, and `stepAt` reads it in that order; the wire refuses an unsorted curve
   (`badStep`) rather than sorting it silently.  `4+` before `1-4`: `decide` refuses. -/
theorem anUnsortedCurveIsAccepted :
    Look.curveOk [Look.Step.from 4 3, Look.Step.range 1 4 4] = true := by
  decide

/- CHEAT 137 — a unit count as a JSON number a double holds exactly.  One hour at `capDen`
   is `60 · 10^18` units, past `2^53`; that is why every unit count crosses as a digit string
   (D17, `unitsJson`).  `decide` refuses the bound. -/
theorem anHourOfUnitsFitsADouble : Look.capDen * 60 < 2 ^ 53 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, kernel half (design
-- §13.6, §13.8): the grants on the wire.  Numbers 138, 139 and 140 were the
-- next free numbers in this checkout (the highest was L6's 137).  The D9
-- track numbers in parallel and the merge renumbers.  The controls, which
-- compile, are `Look.grantAt_none_of_not_enters` and
-- `Look.an_answer_carries_a_grant_iff_its_candidate_enters` (138),
-- `Look.priorities_on_a_witness` and `Look.servedGrants_are_the_pass` (139),
-- and `CapWire.readCands_on_witnesses` (140), in Lookahead.lean and
-- Boundary.lean.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 138 — a wall enters the EDF pass.  Fork `priority::compute` reserves only for dated
   candidates that are not walls, not optional and have no placement window (gap 80): a wall is
   placed by §8.2 step 1 and would otherwise reserve its own hours twice.  `decide` refuses. -/
theorem aWallEntersThePass :
    (Look.entering Arith.safety [⟨['w'], 3, none, 60, some 1, false, true, false, false, false, false, none⟩]).length
      = 1 := by
  decide

/- CHEAT 139 — the pass served in request order.  `^a2` (due day 2) is listed before `^a1` (due
   day 1); served first it would see all 90 minutes.  EDF serves `^a1` first, so `^a2` sees the 51
   minutes `^a1` left (`Look.priorities_on_a_witness`).  `decide` refuses the 90. -/
theorem thePassServesInRequestOrder :
    ((Look.priorities Look.defaultBinsV Arith.safety specDefaultPrio true Look.witnessCaps Look.witnessCands)[1]?.bind
      (·.grant)).map (·.avail) = some (90 * Look.capDen) := by
  decide

/- CHEAT 140 — a candidate at energy level 6 reads.  A level is `0..5` (`levelOf?`, R10); the
   wire refuses the record by its position and key, `badCandidate 0 ci`.  `decide` refuses the
   claim that it reads. -/
theorem aCandidateAtLevelSixReads :
    (CapWire.readCands (CapWire.inCands (.bool true)
      [CapWire.candJ ['a'] (.num 6) .null (.num 30) CapWire.sep8J (.bool false) .null])).isOk = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, host half (design
-- §13.8; gap 79): the floor pass.  Numbers 141 and 142 are the next free
-- numbers in this checkout (the highest was 140; the D9 track's highest on
-- rebuild-on-lean is 137, read-only check).  The controls, which compile, are
-- `Look.prioritiesWithFloors_on_a_roomier_witness` and
-- `Look.a_floor_answer_reads_what_the_pass_left` (141), and
-- `Look.the_pass_wins_over_a_floor` and `Look.prioritiesWithFloors_on_a_witness`
-- (142), in Lookahead.lean.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 141 — a floor reads the capacity before the pass.  Fork `floor_pass` reads `work`, the
   capacity the EDF pass left (§7.1: "net of reservations made by earlier deadlines").  Over
   `witnessFloorCaps` the pass leaves 82 minutes, so `^r`'s need of 26 is the `+1` bin and `p = 2`; read
   against the 180 minutes before the pass it would be the `+2` bin, `p = 3`.  `decide` refuses. -/
theorem aFloorReadsTheCapacityBeforeThePass :
    ((Look.prioritiesWithFloors Look.defaultBinsV Arith.safety specDefaultPrio true Look.witnessFloorCaps
      Look.witnessFloors)[4]?).map (fun o => o.out.p) = some (some 3) := by
  decide

/- CHEAT 142 — a candidate that enters the pass is answered at its floor.  Fork `compute` takes
   `edf[i].or(floor)`: the grant wins.  `^a1` enters and carries a floor in `witnessFloors`; it is
   answered by its grant and carries no floor answer.  `decide` refuses. -/
theorem aGrantedCandidateIsAnsweredAtItsFloor :
    ((Look.prioritiesWithFloors Look.defaultBinsV Arith.safety specDefaultPrio true Look.witnessCaps
      Look.witnessFloors)[2]?).map (fun o => o.floor.isSome) = some true := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step C1: the undo mask in
-- `Replay.lean`).  Design §16's label 95 ("an undo that does not cancel itself").
-- Number 143 is the next free number in this checkout (the highest was 142,
-- the merge-back).  The control, which compiles, is `Replay.an_undo_never_survives`
-- with the witnesses `Replay.the_mask_ignores_isStateChange` and
-- `Replay.undo_mask_pairs_and_dangling_ported`.  Everything below must FAIL to
-- compile.
-- ===========================================================================

/- CHEAT 143 — an undo that does not cancel itself.  Fork `undo_mask` sets
   `cancelled[i] = true` for every undo, whether or not it finds a target, so a
   replay never sees one (`Replay.an_undo_never_survives`).  A mask step that
   erases the target and then keeps the undo on the stack claims the same law and
   cannot have it: over the one-line log `[undo{of:"note"}]` the undo survives.
   `decide` refuses. -/
def maskStepKeepingTheUndo (st : List Log.Entry) (e : Log.Entry) : List Log.Entry :=
  match e.ev with
  | .undo of_ id => e :: st.eraseP (Replay.matches of_ id)
  | _            => e :: st

theorem anUndoThatKeepsItselfNeverSurvives :
    ∀ u ∈ ([Replay.wEnt 1 (.undo Log.Kind.note.tag none)].foldl maskStepKeepingTheUndo []).reverse,
      u.ev.isUndo = false := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step C2: the day index in
-- `Replay.lean`).  Design §16's label 96 ("a 25-hour wake day").  Number 144 is
-- the next free number in this checkout (the highest was 143, C1).  The control,
-- which compiles, is `Replay.a_wake_day_is_shorter_than_a_day` with its witness
-- `Replay.a_wake_day_is_shorter_than_a_day_is_not_vacuous`.  Everything below
-- must FAIL to compile.
-- ===========================================================================

/- CHEAT 144 — a 25-hour wake day.  Fork `DayIndex::day_of` attributes an instant
   to its last wake's date only while `t.signed_duration_since(w) < 24 h`
   (`Replay.a_wake_day_is_shorter_than_a_day`).  A `dayOf` whose window is 25
   hours claims the same law and cannot have it: in Chicago, 06:35 on 2026-09-08
   is 24 h 30 min after the 06:05 wake of the 7th, a different date, and this
   `dayOf` still puts it on the 7th.  `decide` refuses. -/
def dayOfWithA25HourDay (z : Cal.Tz) (kw : List Cal.Instant) (t : Cal.Instant) : Nat :=
  match Replay.lastWakeLe kw t with
  | some w => if (Cal.durationBetween w t).1 < 90000 then Cal.localDate z w else Cal.localDate z t
  | none => Cal.localDate z t

theorem aWakeDayOf25HoursIsShorterThanADay :
    let kw := Replay.keptWakes Cal.chicago [⟨63924375900, 0⟩]
    let t : Cal.Instant := ⟨63924464100, 0⟩
    let w : Cal.Instant := ⟨63924375900, 0⟩
    Replay.lastWakeLe kw t = some w →
    dayOfWithA25HourDay Cal.chicago kw t = Cal.localDate Cal.chicago w →
    Cal.localDate Cal.chicago t ≠ Cal.localDate Cal.chicago w →
    (Cal.durationBetween w t).1 < 86400 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C3: the machine's effects in
-- `Replay.lean`).  Design §16 names no cheat for C3; this one guards the frame
-- law, which is what lets a sealed day refuse a line (G3).  Number 145 is the
-- next free number in this checkout (the highest was 144, C2).  The control,
-- which compiles, is `Replay.applyEffects_touches_only_named_keys`.  Everything
-- below must FAIL to compile.
-- ===========================================================================

/- CHEAT 145 — an effect that writes a key it does not name.  A header effect
   names its day (`Key.day d`).  One that also counts the entry in the
   bookkeeping writes `Key.global` too, and claims the frame law for itself:
   the value at `.global` is unchanged by an effect list whose keys do not
   include `.global`.  On the empty state it is changed, and `decide` refuses. -/
def applyEffectCountingOnHeader (st : Replay.State) : Replay.Effect → Replay.State
  | .header d h => { Replay.applyEffect st (.header d h) with global := ⟨st.global.lastEffective, st.global.entries + 1⟩ }
  | e => Replay.applyEffect st e

theorem aHeaderThatCountsTouchesOnlyItsDay :
    (applyEffectCountingOnHeader (Replay.State.init 1) (.header 739865 ⟨1, ['n'], none, false⟩)).valueAt .global
      = (Replay.State.init 1).valueAt .global := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C4: the completion family in
-- `Replay.lean`).  Design §16 names no cheat for C4; this one guards quirk
-- Q6(b) (gap 118), the owner's "keep: they answer different questions".  Number 146 is
-- the next free number in this checkout (the highest was 145, C3).  The
-- control, which compiles, is `Replay.an_instance_is_its_last_record_in_file_order`
-- with its witness `Replay.instances_and_last_done_order_differently`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 146 — an instance kept by instant.  The tempting "one definition"
   port of quirk Q6(b) keeps each instance's latest record by stamp, as
   `last_done` is kept.  Fork `instances[item][inst]` is a map overwrite: the
   last record in file order wins.  On a retro append (`routine s #1 done` at
   10:00, then the same instance `done` at 08:00) the instance kept by instant
   is the 10:00 record, and the fork's is the 08:00 one, so `decide` refuses. -/
def instanceKeptByInstant (item ins : List Char) (es : List Log.Entry) : Option Replay.InstRec :=
  es.foldl (fun acc e =>
    match Replay.instRecordOf item ins e, acc with
    | some r, some a => if a.t.1 < r.t.1 then some r else some a
    | some r, none => some r
    | none, acc => acc) none

theorem anInstanceKeptByInstantIsTheLastRecordInFileOrder :
    instanceKeptByInstant ['s'] ['#', '1']
        [Replay.bE 1 63924372000 (Replay.rDone ['s'] ['#', '1']), Replay.bE 2 63924364800 (Replay.rDone ['s'] ['#', '1'])]
      = ([Replay.bE 1 63924372000 (Replay.rDone ['s'] ['#', '1']),
          Replay.bE 2 63924364800 (Replay.rDone ['s'] ['#', '1'])].reverse.findSome? (Replay.instRecordOf ['s'] ['#', '1'])) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C5: the day header and records
-- family in `Replay.lean`).  Design §16 names no cheat for C5; this one guards
-- late binding, which §8.2 lists as a rule to port ("energy_obs_slept_is_the_days_
-- first_logged_sleep").  Number 147 is the next free number in this checkout (the
-- highest was 146, C4).  The control, which compiles, is
-- `Replay.energy_obs_slept_is_the_days_first_logged_sleep` with its witness
-- `Replay.an_energy_line_before_its_wake_reads_the_wakes_sleep`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 147 — an energy observation bound early.  The tempting port reads the
   day's sleep from what has been replayed so far, so an `energy` line logged
   before its day's `wake` (`tm wake 06:05` typed after `tm energy 4`) carries no
   sleep.  Fork `slept_by_day` is built from every surviving wake before the walk:
   on `[energy 09:00, wake 06:00 slept 420]` the observation reads 420, so
   `decide` refuses the early-bound `none`. -/
theorem anEnergyLineReadsOnlyTheWakesLoggedBeforeIt :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (.energy 3 4 (.nat 2) ['h']),
        Replay.bE 2 63924357600 (.wake 420 none)]).energy.map (·.sleptMin) = [none] := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C6: the facts, the observations
-- and the headers in `Replay.lean`).  Design §16's label 105 ("an observation
-- effect keyed `global` instead of its day", CRIT 9).  Number 148 is the next
-- free number in this checkout (the highest was 147, C5).  The control, which
-- compiles, is `Replay.every_dated_output_names_its_day_key`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 148 — an observation keyed `global`.  The tempting key for an energy
   observation is the all-time one, like `last_done`'s: the fit reads every
   observation.  But an observation is dated (it lives in its day's record, and a
   sealed day's record is written once), so a guard reading keys would miss a tail
   line writing an observation into a sealed day.  `every_dated_output_names_its_
   day_key` says the key names the date `Effect.day?` gives: on an observation of
   2026-09-07 (day 739865) the global key names no date, so `decide` refuses. -/
def keyObservationsGlobally : Replay.Effect → Replay.Key
  | .obs _ => .global
  | fx => fx.key

theorem anObservationKeyedGloballyNamesItsDay :
    (keyObservationsGlobally (.obs (.energy ⟨1, (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865, 3, 4, .nat 2, ['h'], none, none,
        none, false⟩))).date?
      = (Replay.Effect.obs (.energy ⟨1, (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865, 3, 4, .nat 2, ['h'], none, none, none,
        false⟩)).day? := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C7: the undo law in
-- `Replay.lean`).  Design §16's label 107 ("`undosFor` emitted oldest first").
-- Number 149 is the next free number in this checkout (the highest was 148, C6).
-- The control, which compiles, is `Replay.undoing_a_command_replays_the_log_without_it`
-- over `Replay.undosFor`, most recent first.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 149 — `undosFor` emitted oldest first.  The tempting port walks the
   recorded events in the order the command wrote them.  But an undo takes the
   most recent surviving match, so an older event's undo can take a newer event
   of the command: `event e` (no id) then `event e` with id `x`, undone oldest
   first, writes `undo{of:"event"}` first, which takes the newer (id `x`) event,
   and then `undo{of:"event", id:"x"}`, which finds nothing and dangles.  The
   older event survives, so the undone log's `(e, none)` record is not the empty
   log's, and `decide` refuses the undo law on it (with `L = M = []`, where
   `untouchedBy` holds). -/
def undosOldestFirst (E : List Log.Entry) (n : Nat) (t : Cal.VInstant) (o : Cal.VOffset) : List Log.Entry :=
  (E.zipIdx n).map (fun p => ⟨p.2, t, o, .undo p.1.ev.tag p.1.ev.primaryId⟩)

theorem undoingOldestFirstReplaysTheLogWithoutTheCommand :
    Replay.factsView (Replay.replay Replay.utcZone
        ([Replay.bE 1 63924368400 (.named ['e'] none), Replay.bE 2 63924368460 (.named ['e'] (some ['x']))]
          ++ undosOldestFirst [Replay.bE 1 63924368400 (.named ['e'] none),
            Replay.bE 2 63924368460 (.named ['e'] (some ['x']))] 3 Replay.undoStamp Replay.undoOffset))
        (.named ['e'] none)
      = Replay.factsView (Replay.replay Replay.utcZone []) (.named ['e'] none) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step W1: the checkpoint and the
-- sealed records in `Seal.lean`).  Design §16's labels 97 ("a view without
-- `lastDone` still satisfies the partition law on its minimal witness") and 98
-- ("`readCkpt` defaulting a missing `ledgerDay` to 0").  Numbers 150 and 151 are
-- the next free numbers in this checkout (the highest was 149, C7).  The
-- controls, which compile, are `Seal.a_log_sealed_anywhere_answers_as_its_replay`
-- with `Seal.the_last_done_outlives_the_seal_of_its_days`, and
-- `Seal.readCkpt_refuses_a_checkpoint_without_its_ledgerDay`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 150 — a view without `last_done`.  The tempting answer keeps no
   all-time `last_done` and reads it off the open days: the latest completed
   duration observation of the id on a day at or after the ledger day.  It
   agrees with the replay while a `done`'s day is open, which is why a law
   checked on a log sealed before its days still holds.  Sealed after both days
   (two `done x`, on the 7th and the 8th, sealed at 2026-10-12), the open days
   hold nothing, the view reads no `last_done`, and `decide` refuses the claim
   that it reads the replay's. -/
def lastDoneFromOpenDays (v : Seal.Answer) (i : Log.Id) : Option Replay.At :=
  Replay.maxByInstant? (((v.days.flatMap (·.durations)).filter (fun o => decide (o.id = i) && !o.isPartial)).map (·.t))

theorem aViewWithoutLastDoneReadsTheReplays :
    Replay.Answer.stamp (lastDoneFromOpenDays
        (Seal.answer (Seal.ckptOfEntries Replay.utcZone 739870 739900 2 Seal.twoDoneDays [] [])) ['x'])
      = Replay.ask (Replay.replayDoc Replay.utcZone Seal.twoDoneDays) (.lastDone ['x']) := by
  decide

/- CHEAT 151 — `readCkpt` defaulting a missing `ledgerDay` to 0.  The
   tempting reader fills an absent field with its zero, as a serde default
   would.  But a ledger day of 0 makes every sealed day open again with nothing
   in it: the checkpoint of the two-done log sealed at the 8th, read without its
   `ledgerDay`, would answer the 7th as an empty open day.  `readCkpt` refuses
   `badCkpt ledgerDay` by name; `decide` refuses the claim that the defaulting
   reader does. -/
def readCkptDefaultingLedgerDay (j : JVal) : Except Seal.CkErr Seal.Ckpt :=
  match j with
  | .obj kvs =>
    if kvs.any (fun p => p.1 == Seal.kLedgerDay) then Seal.readCkpt j
    else Seal.readCkpt (.obj (kvs.take 3 ++ (Seal.kLedgerDay, .num 0) :: kvs.drop 3))
  | _ => Seal.readCkpt j

theorem aDefaultingReaderRefusesAMissingLedgerDay :
    (match readCkptDefaultingLedgerDay (.obj ((Seal.ckptPairs
        (Seal.ckptOfEntries Replay.utcZone 739870 739866 2 Seal.twoDoneDays [] [])).filter
          (fun p => !(p.1 == Seal.kLedgerDay)))) with
      | .error (.badCkpt .ledgerDay) => true
      | _ => false) = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step W2).  Design §16's labels 99
-- ("`resume` accepting an unsettled undo whose target is folded") and 102
-- ("the window compacted to `horizonOf L + 1`").  Numbers 152 and 153 are the
-- next free numbers in this checkout (the highest was 151, W1).  The controls,
-- which compile, are `Seal.resume_without_the_guards_is_not_replay` and
-- `Seal.the_window_at_the_horizon_reads_the_replay`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 152 — a resume accepting an unsettled undo whose target is folded
   (design label 99).  The tempting resume folds the tail's survivors from the
   restored state and skips G1.  After a folded `done a`, the tail's
   `undo done a` finds nothing on the tail's own stack, so the resumed answer
   keeps `a` done, while the replay of both lines cancels it.  `decide` refuses
   the claim that the unguarded resume reads the replay's `last_done`. -/
set_option maxRecDepth 8000 in
theorem anUnguardedResumeReadsTheReplaysLastDone :
    Seal.askAnswer (Seal.resumeUnguarded Replay.utcZone
        (Seal.ckptOfEntries Replay.utcZone 739865 739865 1 [Replay.bE 1 63924368400 (Replay.bDone ['a'] 50 false)] [] [])
        [Replay.bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] []) (.lastDone ['a'])
      = Seal.askAnswer (Seal.answer (Seal.ckptOfEntries Replay.utcZone 739865 739865 2
        [Replay.bE 1 63924368400 (Replay.bDone ['a'] 50 false),
         Replay.bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] [] [])) (.lastDone ['a']) := by
  decide

/- CHEAT 153 — the window compacted to `horizonOf L + 1` (design label 102,
   CRIT 3).  The tempting compaction keeps the window from the day after the
   horizon, since the window records cover every date below it.  But the
   horizon itself is then in neither: one `done x` on 2026-08-29, sealed on
   2026-09-14 (whose horizon is the 29th), reads no done date there, and
   `decide` refuses the claim that the compacted answer reads the replay's. -/
def compactedAnswer (L : Nat) (es : List Log.Entry) : Seal.Answer :=
  { Seal.answer (Seal.ckptOfEntries Replay.utcZone L L es.length es [] []) with
      window := Seal.windowsFrom (Seal.foldedState Replay.utcZone es []) (Seal.horizonOf L + 1) }

set_option maxRecDepth 8000 in
theorem aWindowCompactedPastItsHorizonReadsTheReplay :
    Seal.askMerged (Seal.dayRecordsOfEntries Replay.utcZone 0 739872 Seal.oneDoneOnTheHorizon)
        (Seal.windowRecordsOfEntries Replay.utcZone 0 (Seal.horizonOf 739872) Seal.oneDoneOnTheHorizon)
        (compactedAnswer 739872 Seal.oneDoneOnTheHorizon) (.win 739856 (.done ['x']))
      = Replay.ask (Replay.replayDoc Replay.utcZone Seal.oneDoneOnTheHorizon) (.win 739856 (.done ['x'])) := by
  decide

/- CHEAT 154 — a reseal whose ledger day moves backwards (design label 100).
   The tempting new ledger day is the least of `F` and the unfolded lines' days,
   without the floor at the stored ledger day.  A checkpoint sealed at
   2026-09-14 and resumed the same day with `keepDays = 5` and an empty tail
   then reseals at 2026-09-09, before the days it has already sealed, and
   `decide` refuses the claim that the ledger day never moves back
   (`reseal_is_seal`'s `L ≤ L'`). -/
def resealEmptyRun : Seal.Run :=
  ⟨[], [], [], [], fun _ => none, Replay.State.init 0, [], Seal.answer (Seal.Ckpt.empty Replay.utcZone)⟩

def sealDayWithoutTheLedgerFloor (z : Cal.Tz) (T : Nat) (K : Seal.Ckpt) (p : Seal.Policy) (r : Seal.Run) (j : Nat) :
    Nat :=
  Seal.sealDayOf z T { K with ledgerDay := 0 } p r j

set_option maxRecDepth 8000 in
theorem aResealNeverMovesItsLedgerDayBack :
    ({ Seal.Ckpt.empty Replay.utcZone with ledgerDay := 739865 } : Seal.Ckpt).ledgerDay
      ≤ sealDayWithoutTheLedgerFloor Replay.utcZone 739865 { Seal.Ckpt.empty Replay.utcZone with ledgerDay := 739865 }
          ⟨5, none⟩ resealEmptyRun 0 := by
  decide

/- CHEAT 155 — a reseal that leaves a folded-target undo out of `settled`, still
   accepted afterwards (design label 101).  The tempting resealed checkpoint
   keeps no settled undos.  Folded `done b` and `done a`, and an unfolded
   `undo done a` whose target is folded: without its settled line, the undo
   dangles in the suffix and the folded `done` tag makes G1 refuse it, and
   `decide` refuses the claim that the suffix passes G1
   (`a_resealed_checkpoint_accepts_its_own_suffix`, through `tagsClear_iff`). -/
def aCheckpointWithASettledUndo : Seal.Ckpt :=
  Seal.ckptOfEntries Replay.utcZone 739865 739865 2
    [Replay.bE 1 63924368400 (Replay.bDone ['b'] 50 false), Replay.bE 2 63924368460 (Replay.bDone ['a'] 50 false)]
    [Replay.bE 3 63924368520 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] []

set_option maxRecDepth 8000 in
theorem aResealWithoutItsSettledUndoAcceptsItsSuffix :
    Seal.g1 { aCheckpointWithASettledUndo with settled := [] }
      (Seal.unsettled [] [Replay.bE 3 63924368520 (.undo ['d', 'o', 'n', 'e'] (some ['a']))]) = none := by
  decide

/- CHEAT 156 — `F` computed from the log's latest day without the `T − keepDays`
   bound (design label 103, CRIT 1).  The tempting floor is the latest day any
   surviving line heads, less `keepDays`.  One note dated a year ahead, folded
   on 2026-09-14 with `keepDays = 2`, then seals to 2027-09-12, and `decide`
   refuses the claim that the reseal never seals past now
   (`a_reseal_never_seals_past_now`). -/
def aLineAYearAhead : Log.Entry := Replay.bE 1 63955872000 (.note ['x'])

def aRunOfALineAYearAhead : Seal.Run :=
  ⟨[aLineAYearAhead], [aLineAYearAhead], [aLineAYearAhead], [], fun _ => none, Replay.State.init 1, [],
   Seal.answer (Seal.Ckpt.empty Replay.utcZone)⟩

def floorFromTheLatestDay (keep : Nat) (dy : Cal.Instant → Nat) (sv : List Log.Entry) : Nat :=
  (sv.map (fun e => dy e.t.val)).foldl Nat.max 0 - keep

def sealDayFromTheLatestDay (z : Cal.Tz) (K : Seal.Ckpt) (p : Seal.Policy) (r : Seal.Run) (j : Nat) : Nat :=
  let dy := Replay.dayOf z r.index
  let n := K.items.length + K.openDays.length + r.entries.length
  let Brest := r.entries.filter (fun e => decide (K.cut + j < e.line))
  let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
  let lows := Brest.map (fun e => dy e.t.val) ++ Brest.map (fun e => e.t.val.sec / 86400 + 1)
    ++ Seal.stepLows z dy r.slept (fun e => decide (K.cut + j < e.line)) (Seal.restore K n) r.survivors
    ++ Seal.machineDays (svj.foldl (Replay.stepWith z dy r.slept) (Seal.restore K n)).machine
  Nat.max K.ledgerDay (lows.foldl Nat.min (floorFromTheLatestDay p.keepDays dy r.survivors))

set_option maxRecDepth 8000 in
theorem aFloorFromTheLatestDayNeverSealsPastNow :
    sealDayFromTheLatestDay Replay.utcZone (Seal.Ckpt.empty Replay.utcZone) ⟨2, none⟩ aRunOfALineAYearAhead 1 = 0 ∨
      sealDayFromTheLatestDay Replay.utcZone (Seal.Ckpt.empty Replay.utcZone) ⟨2, none⟩ aRunOfALineAYearAhead 1 + 2
        ≤ 739865 := by
  decide

/- CHEAT 157 — an unterminated last segment folded (design label 104, CRIT 8).
   The tempting fold point reads every tail as terminated.  One unterminated
   line, a note dated a year ahead (so no other condition holds it back), then
   folds, and `decide` refuses the claim that the unterminated line stays
   unfolded (`the_unterminated_segment_is_never_folded`). -/
def foldPointIgnoringTheEnd (z : Cal.Tz) (T : Nat) (K : Seal.Ckpt) (b : List Log.Line) (_terminated : Bool)
    (p : Seal.Policy) (r : Seal.Run) : Nat :=
  Seal.foldPointOf z T K b true p r

set_option maxRecDepth 8000 in
theorem aFoldPointIgnoringTheEndLeavesTheLastLineUnfolded :
    foldPointIgnoringTheEnd Replay.utcZone 739865 (Seal.Ckpt.empty Replay.utcZone) [⟨1, some ['x']⟩] false ⟨2, none⟩
      aRunOfALineAYearAhead < 1 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-16 (stage 6, run W-13, step L9 — day 0 is the kernel's own;
-- design §13.5, gap 93).  Cheat 158 is the design's reserved **cheat 118**,
-- "the posterior applied after the cap"; it is numbered from the end of this
-- file (§6.2: append, never renumber), and the design's label is recorded here
-- so the two can be read together.
-- ===========================================================================

/- CHEAT 158 (design label 118) — today's posterior applied AFTER the home cap.
   `EnergyCtx::energy_at` predicts, corrects with the posterior, and caps: the
   cap is last, so a report that lifts a home level above `home_max_ci` is still
   capped.  Applying the correction after the cap lets it through.  On the §4.3
   Monday at home, with `home_max_ci = 3` and a 09:00 report of 5 against a
   prediction of 3, the fork keeps every minute at 3 and the cheat lifts three
   blocks to 5.  `decide` refuses the equality. -/
def todayEnergyCappedFirst (I : Look.Input) (t : Cal.Instant) : Fin 6 :=
  Look.correctAt I.today0.post I.today0.reports t
    (Look.capForLocation I.homeMax I.today0.allowHome (Look.capLoc I.today0.loc)
      (Look.predictShift I.curves (Look.curveKeyOf I.curves I.today0.loc)
        (Look.hswAt (Look.wakeOn I I.today) t) (I.today0.sleep.shiftOf I.today0.slept))).val

def aHomeDayWithALiftingReport : Look.Input :=
  { Look.specWalled with today0 :=
      { Look.specToday with loc := Look.homeKey, reports := [⟨Look.atSpec 540, 3, 5⟩] } }

def day0HistCappedFirst (I : Look.Input) : Look.Hist :=
  Look.histOf' ((Look.day0Cut I).slots.map fun s => (todayEnergyCappedFirst I ⟨s.start, 0⟩, s))

theorem aPosteriorAfterTheCap :
    (List.finRange 6).map (day0HistCappedFirst aHomeDayWithALiftingReport)
      = (List.finRange 6).map (Look.day0Hist aHomeDayWithALiftingReport) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-14, track P step P0 — the planner's
-- vocabulary; design §16's two P0 cheats).  Numbered from the end of this file
-- (§6.2: append, never renumber).
-- ===========================================================================

/- CHEAT 159 — a segment that ends before it starts, accepted.  `Seg.wf` is
   `start ≤ stop` and the end inside the calendar; the fork's `Segment` has no
   such check at all and `Segment::minutes` papers over it with
   `.max(0)`, so a wall written `17:00-09:00` renders as a zero-minute row
   instead of being refused.  `mkSeg?` names it `.inverted`.  `decide` refuses
   the claim that the inverted one is well-formed. -/
def anInvertedSeg : Planner.Seg :=
  { start := 61200, stop := 32400, kind := Planner.SegKind.wall, energy := none,
    item := none, inst := none, flags := {}, planned := none, mult := none, note := none }

theorem anInvertedSegIsWellFormed : Planner.Seg.wf anInvertedSeg = true := by decide

/- CHEAT 160 — a batch of seventeen.  §7.5 gathers small items into ONE slot
   under `batch_max_min`, so `BatchIds` is bounded at `maxBatch = 16`; the
   fork's `SegKind::Batch(Vec<Id>)` is unbounded, which is the hole R10 exists
   to close.  `decide` refuses the claim that `mkBatch?` accepts seventeen. -/
def seventeenIds : List Id :=
  [['a'], ['b'], ['c'], ['d'], ['e'], ['f'], ['g'], ['h'], ['i'],
   ['j'], ['k'], ['l'], ['m'], ['n'], ['o'], ['p'], ['q']]

theorem aBatchOfSeventeenIsAccepted : (Planner.mkBatch? seventeenIds).isSome = true := by decide

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-14, track P step P1 — the walls;
-- design §16's two P1 cheats).  Numbered from the end of this file (§6.2).
-- ===========================================================================

/-- The §4.3 meeting as `wallIndex` lists it, with an hour of `buffer:` in front:
   blocked from 11:50, the event 12:50-13:50, on one day. -/
def aBufferedWall : Look.WallIx :=
  ⟨['g','1'], 739865, 739865, 42600, 46200, 49800⟩

/-- The same day's second meeting, overlapping it: 13:30-14:30. -/
def anOverlappingWall : Look.WallIx :=
  ⟨['g','2'], 739865, 739865, 48600, 48600, 52200⟩

/- CHEAT 161 — a wall placed where there was room.  §8.2 step 1 places an
   Interval instance EXACTLY where it is written; `Planner.wallRows` reads both
   ends off the index and contributes neither.  A planner that treated a wall as
   something to fit — first free position, same duration — is what
   `plan_never_moves_a_wall` exists to rule out, and it is what
   `horizon.rs`-shaped code does with everything else.  `decide` refuses the
   claim that the two agree. -/
def wallRowsAtTheFirstFreePosition (dayLo : Nat) (x : Look.WallIx) : List Planner.Seg :=
  [{ start := dayLo, stop := dayLo + (x.hi - x.evLo), kind := Planner.SegKind.wall,
     energy := none, item := some x.id, inst := none, flags := {}, planned := none,
     mult := none, note := none }]

theorem aWallPlacedWhereThereWasRoom :
    wallRowsAtTheFirstFreePosition 39600 aBufferedWall = Planner.wallRows false aBufferedWall := by
  decide

/- CHEAT 162 — an overlap filled.  §8.2 step 1: overlapping walls are reported
   pairwise in `diagnostics.conflicts`, the planner "does not resolve them", and
   BOTH stay blocked so nothing is placed in the overlap.  Shunting the later
   wall to the end of the earlier one fills the overlap and makes the conflict
   disappear — the failure that looks like success, because the report goes
   quiet.  `decide` refuses the claim that the resolved pair reports what the
   written pair reports. -/
def resolveOverlap (a b : Look.WallIx) : Look.WallIx :=
  if b.evLo < a.hi ∧ a.evLo < b.hi then { b with lo := a.hi, evLo := a.hi } else b

theorem anOverlapFilled :
    Planner.wallConflicts [aBufferedWall, resolveOverlap aBufferedWall anOverlappingWall]
      = Planner.wallConflicts [aBufferedWall, anOverlappingWall] := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-14, track G — L26's eleven single-run
-- laws as one checker battery, `PlanCheck.lean`, design §6).  Appended at the
-- end (§6.2: append, never renumber).
--
-- **The labels start at 171, not 161, on purpose.**  Track P is running its
-- planner steps in parallel on another branch (D26) and design §16 gives P1-P8
-- two to three cheats each, so 161-170 is left to it.  A hole in the labels
-- costs nothing; a duplicate label costs a merge-time renumber and leaves a
-- wrong number in a commit message, which this campaign has paid for twice.
-- ===========================================================================

/- CHEAT 171 — the battery cannot refuse a day.  This is AGENTS §9.2's own
   disguised gap, written out: *"a check no input can fail"*.  A checker battery
   that is true of every `(r, d)` proves nothing about `dayPlan`, and the whole
   value of `dayPlan_ok_core` rests on `planOkCore` being falsifiable.  It is —
   `PlanCheck.planOkCore_can_fail` exhibits the day it refuses — so the claim
   below does not close. -/
theorem theBatteryCannotRefuseADay (r : Planner.PlanReq) (d : Planner.DayPlan) :
    PlanCheck.planOkCore r d = true := by rfl

/- CHEAT 172 — a block laid across a wall passes the wall check.  §8.3's "no
   segment overlaps a Wall" is the law, and `PlanCheck.theBlockOverAWallDay`
   puts an hour-long block at [0, 3600) under a wall at [1800, 5400).  The
   checker answers `false` and the claim that it answers `true` does not close.
   This is the pair to design §16's P1 cheat "an overlap filled": that one will
   catch the *planner* placing it, this one catches the *checker* going
   blind. -/
theorem aBlockLaidAcrossAWallPassesTheWallCheck (r : Planner.PlanReq) :
    PlanCheck.noBlockOverAWall r PlanCheck.theBlockOverAWallDay = true := by rfl

/- CHEAT 173 — a kept reservation still leaves a prefix.  This is the belief
   D29 corrects: §8.2 choice 5b reserves the running block BEFORE the budget is
   consulted, so a candidate ranking ahead of it can leave the day while the
   reservation stays, and the shorter assignment is then not a prefix of the
   longer one.  `PlanCheck.a_kept_reservation_defeats_the_prefix_but_not_the_erasure`
   proves both halves; this block asserts the half that is false. -/
theorem aKeptReservationStillLeavesAPrefix (a x : Id) (hne : x ≠ a) :
    ∃ n : Nat, ([a] : List Id) = ([x, a] : List Id).take n := ⟨1, by simp⟩

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-15**, track P, step P2 — §8.2 step 2:
-- the routines and the evening).  Appended at the end (§6.2: append, never
-- renumber).  Labels 163-165: P1 took 161-162 out of the 161-170 track P
-- reserved for its own steps, and track G's 171-173 are above.
-- ===========================================================================

/- CHEAT 163 — a routine placed outside its window.  §8.2 step 2 places a window
   instance inside ITS OWN window: `place_mandatory_and_pref` searches
   `[span.0.max(now), span.1]` and nothing else.  The tempting shortcut is "the
   earliest free position in the day" — it is shorter, it always succeeds, and it
   silently moves a 14:00-15:00 chore to breakfast, which is the failure that
   looks like success because the routine IS placed.  `decide` refuses the claim
   that the two searches agree. -/
def theEarliestFreePositionInTheWholeDay (durSec : Nat) (ws : List (Nat × Nat)) : Option Nat :=
  Planner.earliestFree 28800 79200 durSec ws

theorem aRoutinePlacedOutsideItsWindow :
    theEarliestFreePositionInTheWholeDay 1800 [] = Planner.earliestFree 50400 54000 1800 [] := by
  decide

/- CHEAT 164 — a routine whose declared window is malformed, planned anyway
   (README gap 285).  Driven on the audit's own workspace, `- lunch
   win:25:99-13:30 dur:30m  every:day` makes `tm check` name the line twice and
   `tm now` and `tm plan` proceed with rc=0, the invalid window simply dropped.
   `25:99` is not a clock, so `Field.parseWindow` answers `none`, so the item's
   shape is `Shape.none` and it declares no window at all — while its instance
   still carries one.  `Planner.mkRoutine?` answers `undeclaredWindow` and the
   verb refuses.  This block asserts the fork's behaviour instead, with both
   hypotheses satisfiable by an ordinary plan. -/
theorem aMalformedWindowIsPlannedAnyway (p : PlanCore) (x : Planner.RoutineIn) (e : Entity)
    (hget : p.store.get x.id = some e)
    (hd : Planner.declaresAWindow p x.id = false) :
    Planner.mkRoutine? p x = .ok x := by
  simp [Planner.mkRoutine?, hget, hd]

/- CHEAT 165 — the small hours reopened.  `Planner.night()` runs from the
   wind-down to the end of TOMORROW, not to midnight (fork `Planner::night`):
   §8.1's wall extension can push the window past midnight and the small hours
   are not a second working evening.  Ending the night at midnight leaves
   00:00-06:00 free, and a mandatory routine whose window closes tomorrow morning
   is then placed at 00:00 — placed, reported, and wrong.  `decide` refuses the
   claim that the two nights leave the same earliest position. -/
theorem theSmallHoursReopened :
    Planner.earliestFree 75600 108000 1800 [(75600, 86400)]
      = Planner.earliestFree 75600 108000 1800 [(75600, 172800)] := by
  decide

end Tm
