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
  ⟨⟨⟨q.doc, q.rank⟩, none, (statusOfGlyph q.glyph).get rfl, q.item, []⟩, rfl⟩

/- CHEAT 8 — build the plan without answering which of a demotion's two `[-]`
   lines is the tombstone.  Deciding it by the order the host listed the
   documents was this, with the assertion hidden in a `match` that tried one
   orientation and then the other: three of `planWf`'s four parts discharged and
   the fourth waved through. -/
def loadCheat (planDocs : List Doc) (store : Store)
    (h1 : docsWf ⟨planDocs, store⟩ = true) (h2 : sitesInRange ⟨planDocs, store⟩ = true)
    (h3 : pathsDistinct ⟨planDocs, store⟩ = true) : WfPlan :=
  ⟨⟨planDocs, store⟩, planWf_of_parts h1 h2 h3 rfl⟩

end Tm

/- ═══════════════════════════════════════════════════════════════════════════
   CALENDAR CHEATS (Cal.lean / Grain.lean).  Appended; nothing above is edited.
   ═══════════════════════════════════════════════════════════════════════════ -/
-- Only so the failures below are the *type* errors they claim to be, and not
-- an elaborator budget running out first.  It applies from here on only.
set_option maxRecDepth 10000

namespace Tm

/- CHEAT 9 — hand a date straight through as valid, which is how `Feb 30`
   reaches a calendar.  `ValidDate` is a `Subtype` over a *decidable* predicate,
   so the second field is `Date.valid ⟨2024,2,30⟩ = true`, and that computes to
   `false = true`. -/
def dateCheat : Cal.ValidDate := ⟨⟨2024, 2, 30⟩, by decide⟩

/- CHEAT 10 — number the weeks inside the civil year, which is what "week 1
   starts on January 1st" does, and claim it is the ISO week.  It is not: on
   2027-01-01 this says week 1 and ISO says 2026-W53. -/
def naiveWeek (n : Nat) : Nat := (n - Cal.jan1 (Cal.ofDay n).year) / 7 + 1

theorem naive_week_is_iso :
    naiveWeek (Cal.toDay ⟨2027, 1, 1⟩) = (Cal.isoOf (Cal.toDay ⟨2027, 1, 1⟩)).week := by
  decide

/- CHEAT 11 — name a week's month without naming a tie-break, by assuming the
   week determines the month.  The rewrite is where the derivation stops:
   `week_does_not_refine_month` is the counterexample (2026-W36). -/
theorem week_refines_month : refines week month := by
  intro a b h
  rw [index_week] at h
  rw [index_month, index_month, h]

/- CHEAT 12 — declare `horizon.rs:1543`'s rule stable.  "The month of today" is
   a function of `now`, so two callers on two days of one week get two answers,
   and this does not even hold definitionally. -/
theorem month_of_today_is_stable :
    Cal.monthOfWeekByToday (Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩))
        (Cal.toDay ⟨2026, 8, 31⟩)
      = Cal.monthOfWeekByToday (Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩))
        (Cal.toDay ⟨2026, 9, 6⟩) := by
  decide

/- CHEAT 13 — drop the century rule and keep "every fourth year".  Refuted by
   computation at y = 100. -/
def isLeapCheat (y : Nat) : Bool := y % 4 == 0

theorem leap_is_every_fourth_year : ∀ y, y < 2000 → Cal.isLeap y = isLeapCheat y := by
  decide

/- CHEAT 14 — get the phase of the seven-day cycle wrong by one.  The three
   cross-checks in `Cal.lean` exist to catch exactly this, and they do. -/
def weekdayCheat (n : Nat) : Cal.Weekday := Cal.Weekday.ofIndex (n % 7 + 1)

theorem cheat_weekday_1970 : weekdayCheat (Cal.toDay ⟨1970, 1, 1⟩) = .thursday := by decide

end Tm
