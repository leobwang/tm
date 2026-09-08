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

/- ======================================================================
   THE EXACT-ARITHMETIC LAYER (`TmKernel/Arith.lean`).
   Appended as its own block so that the three stage-one branches merge.
   ====================================================================== -/
namespace Tm

/- CHEAT 9 — form the quotient.  `u = need/avail` in `Nat` is integer
   division, which throws the fraction away before the comparison sees it:
   `u = 3/4` reaches the `1/2` edge, and `3/4 = 0` reaches nothing.  This is
   why `utilGe` cross-multiplies and no ratio is ever divided. -/
def utilNatDiv (need avail : Nat) (e : Arith.Q) : Bool :=
  decide (e.num ≤ e.den * (need / avail))

theorem the_quotient_is_the_comparison :
    utilNatDiv 3 4 ⟨1, 2⟩ = Arith.utilGe 3 4 ⟨1, 2⟩ := by decide

/- CHEAT 10 — round a ratio whose denominator nobody checked.  `n / 0` is
   `0` in Lean, so §8.1's budget with `block_min = 0` would be a silent
   wrong answer rather than an error.  A rounding site takes a `Pos`, and a
   raw `Q` is not one. -/
def budgetCheat (windowMin blockMin : Nat) : Nat :=
  Arith.floorQ (⟨windowMin, blockMin⟩ : Arith.Q)

/- CHEAT 11 — round the safety margin the way `priority.rs:349` does.  A
   margin rounded down stops being a margin: the reservation for one minute
   of work at `safety = 1.3` becomes one minute, which does not cover
   `13/10`.  R1's rule is a ceiling, and `needMin_covers` is why. -/
def needFloor (rem : Nat) : Nat := Arith.floorQ (Arith.scale Arith.safety rem)

theorem floor_still_covers_the_need :
    Arith.Q.le (Arith.scale Arith.safety 1).val (Arith.ofNat (needFloor 1)) = true := by decide

/- CHEAT 12 — derive §7.1's bin edges instead of tabulating them.  Three of
   the four are halvings, so `1/2^i` looks like the generating structure; it
   disagrees with the spec on every `u` in `[0.1, 0.125)`, and at `u = 0.11`
   it gives `+3` where the table gives `+2`. -/
theorem log2_ladder_is_the_table :
    Arith.binOf Arith.log2Bins 11 100 = Arith.binOf Arith.defaultBins 11 100 := by decide

/- CHEAT 13 — guard the division by zero, which is what `is_finite()` does
   in the Rust.  §7.1 says capacity zero makes `u = ∞`, so it reaches every
   edge and the item is HOT; a guard that answers "not urgent" inverts the
   rule at exactly the point where the item cannot possibly be finished. -/
def utilGuarded (need avail : Nat) (e : Arith.Q) : Bool :=
  if avail = 0 then false else Arith.utilGe need avail e

theorem the_finite_guard_is_harmless :
    utilGuarded 1 0 Arith.hotEdge = Arith.utilGe 1 0 Arith.hotEdge := by decide

end Tm
