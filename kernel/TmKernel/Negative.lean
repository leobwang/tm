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

/- CHEAT 30 — §4.3's calendar rule ("generated intervals") waved through: hold
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

end Tm
