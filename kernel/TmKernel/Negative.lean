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
