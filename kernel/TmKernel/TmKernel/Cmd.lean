import TmKernel.Plan
/-!
# The command algebra

Every command is one transformation on the plan value.  Each carries a claimed
law with its **subdomain**, and the refutations are theorems too: several of
tm's stated laws are false as written, and a kernel that stayed silent about
that would be repeating the mistake.

The invariant splits into a part that is free and a part that is not, and being
clear about which is which is the whole point of the bottom section.

* **Free.** Two lines of one id in one file are the same line for *every*
  `PlanCore` (`no_two_lines_of_one_id_in_one_path`, Plan.lean), so no command
  has to preserve it and none can break it, including commands nobody has
  written yet.
* **Not free.** That every placement names a file that exists, that no two
  files share a path, and that a tombstone sits in a horizon strictly before the
  live line it was left by, are decidable predicates `WfPlan.mapAt`
  re-establishes by computation on the post-state of every command — `lift`, at
  the plan level.  `mapAt_ok_of_inRange` and `cmdMove_succeeds` are the proofs
  that the commands can discharge them, so the check is an obligation and not a
  trapdoor; `mapAt_rejects_unoriented` and
  `demote_into_a_horizon_that_does_not_follow_is_rejected` are the proofs that
  it bites.

An earlier version of this module claimed the first bullet for all three, in a
theorem whose command argument was unused.  It is withdrawn.
-/
namespace Tm

inductive KErr
  | occupied          -- the destination file already holds this id's other line
  | noSuchId
  | notDemoted
  /-- the destination is not a horizon this item may occupy: either not a
      document of this plan at all, or — while a tombstone stands — not ahead of
      the file that tombstone is in.  Both are "the post-state fails `planWf`". -/
  | badHorizon
deriving DecidableEq, Repr

/-- The only way to make an `Entity`.  Both cheats are compile errors:
handing the raw `Core` through is a type mismatch, and `⟨c, rfl⟩` fails
because `rfl : ?a = ?a` is not `wf c = true`.  See `Negative.lean`. -/
def lift (c : Core) : Except KErr Entity :=
  if h : wf c = true then .ok ⟨c, h⟩ else .error .occupied

theorem lift_roundtrips (c : Core) (e : Entity) (h : lift c = .ok e) : e.val = c := by
  unfold lift at h; split at h
  · injection h with h; exact congrArg Subtype.val h.symm
  · exact absurd h (by simp)

/-! ## Entity-level transforms -/

/-- `tm move ^id <horizon>`.  **There is no append**: the destination replaces
the live *site*, and `lift` refuses when that would put two lines of one id in
one file.  `horizon::move_line`'s missing precondition has nowhere to live. -/
def moveTo (t : Site) (e : Entity) : Except KErr Entity := lift { e.val with live := t }

def drop (e : Entity) : Entity :=
  ⟨{ e.val with status := .settled .dropped }, e.property⟩

def setEstE (v : Nat) (e : Entity) : Entity :=
  ⟨{ e.val with line := setEst v e.val.line }, e.property⟩

/-- `close`/`demote`: the live line moves to the coarser file and a tombstone
stays behind in the file that was closed. -/
def demote (target : Site) (period : Nat) (e : Entity) : Except KErr Entity :=
  lift { e.val with live := target, archive := some e.val.live,
                    stamps := e.val.stamps ++ [period] }

/-- `readopt` **consumes** the tombstone, which is why it cannot leave a second
line in the file the stale one was in (bug 5). -/
def readopt (t : Site) (e : Entity) : Entity :=
  ⟨{ live := t, archive := none, status := .live .free,
     line := e.val.line, stamps := e.val.stamps }, rfl⟩

/-! ## Plan-level commands -/

/-- **Every command has this type.**  A `WfPlan` in, a `WfPlan` or a structured
error out — there is no third possibility and no partial write. -/
abbrev Transform := WfPlan → Except KErr WfPlan

/-- **A destination that exists.**

`Site.doc` is a `Nat`, and the request format hands one over as a `Nat`.  If a
command is allowed to take that `Nat` straight to a `Site`, then `move ^m1 7` in
a one-document plan writes a placement into document 7, `renderDocAt` renders
only the documents that are there, and the item is gone with the kernel
returning `ok`.  That is the same missing precondition this rebuild exists to
eliminate, moved from "the destination already holds this id" to "the
destination is not a file".

So a relocating command does not take a `Nat`.  It takes a `Dest`, whose only
field besides the index is a proof that the index is a document of *this* plan,
and whose only source is `resolveDest`.  The out-of-range destination is not a
command that gets rejected; it is a command that cannot be written. -/
structure Dest (p : PlanCore) where
  ix : DocIx
  ok : ix < p.docs.length

/-- The only way to make a `Dest`: ask the plan. -/
def resolveDest (p : PlanCore) (n : Nat) : Except KErr (Dest p) :=
  if h : n < p.docs.length then .ok ⟨n, h⟩ else .error .badHorizon

theorem resolveDest_ix {p : PlanCore} {n : Nat} {d : Dest p} (h : resolveDest p n = .ok d) :
    d.ix = n := by
  unfold resolveDest at h; split at h
  · injection h with h; exact congrArg Dest.ix h.symm
  · simp at h

theorem resolveDest_rejects (p : PlanCore) (n : Nat) (h : ¬ n < p.docs.length) :
    resolveDest p n = .error .badHorizon := by simp [resolveDest, h]

def Dest.site {p : PlanCore} (d : Dest p) (rank : Nat) : Site := ⟨d.ix, rank⟩

/-- A relocating command.  Its destination is a handle into the plan it is
applied to, so the type itself carries "this file exists". -/
abbrev Relocation := (p : WfPlan) → Dest p.val → Except KErr WfPlan

/-- Apply an entity transform at one id.  The store obligations are discharged
here once; the plan-level obligation is **re-established by computation** on the
post-state, which is what makes it impossible to forget.  `planWf` includes
`sitesInRange` and `demotionsOriented`, so this one check is the reason a
transform cannot leave a placement pointing at a file that is not there, and the
reason it cannot leave a demotion whose two lines the loader could not tell
apart. -/
def WfPlan.mapAt (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity) :
    Except KErr WfPlan :=
  match h : p.val.store.get i with
  | none   => .error .noSuchId
  | some e =>
    match f e with
    | .error k => .error k
    | .ok e'   =>
      if hq : planWf { p.val with store := p.val.store.set i e' (by rw [h]; rfl) } = true then
        .ok ⟨_, hq⟩
      else .error .badHorizon

theorem mapAt_get (p q : WfPlan) (i : Id) (f : Entity → Except KErr Entity) (e' : Entity)
    (hq : p.mapAt i f = .ok q) (he : q.val.store.get i = some e') :
    ∃ e, p.val.store.get i = some e ∧ f e = .ok e' := by
  unfold WfPlan.mapAt at hq
  split at hq
  · simp at hq
  · rename_i e hget
    refine ⟨e, hget, ?_⟩
    split at hq
    · simp at hq
    · rename_i a ha
      split at hq
      · injection hq with hq
        subst hq
        rw [Store.get_set_self] at he
        injection he with he
        rw [ha, he]
      · simp at hq

/-! ### That the plan-level check is a proof obligation, not a trapdoor

A decidable re-check is only honest if the commands can actually discharge it.
These are the lemmas that say so: a transform whose result stays inside the
documents that exist always passes, so `mapAt` never converts a legitimate
command into `badHorizon`. -/

theorem entityInRange_of_mem (p : WfPlan) (i : Id) (e : Entity)
    (h : p.val.store.get i = some e) : entityInRange p.val e = true := by
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr (by rw [h]; rfl)
  have hall := List.all_eq_true.1 (planWf_parts p.property).2.1 i hdom
  rw [h] at hall
  exact hall

theorem sitesInRange_set (p : PlanCore) (i : Id) (e' : Entity) (h : (p.store.get i).isSome = true)
    (hp : sitesInRange p = true) (hin : entityInRange p e' = true) :
    sitesInRange { p with store := p.store.set i e' h } = true := by
  simp only [sitesInRange, List.all_eq_true]
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [Store.get_set_self]
    exact hin
  · rw [Store.get_set_other _ _ _ _ _ hji]
    exact List.all_eq_true.1 hp j (by simpa using hj)

theorem demotionsOriented_set (p : PlanCore) (i : Id) (e' : Entity)
    (h : (p.store.get i).isSome = true) (hp : demotionsOriented p = true)
    (hor : demotionOriented p e' = true) :
    demotionsOriented { p with store := p.store.set i e' h } = true := by
  simp only [demotionsOriented, List.all_eq_true]
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [Store.get_set_self]
    exact hor
  · rw [Store.get_set_other _ _ _ _ _ hji]
    exact List.all_eq_true.1 hp j (by simpa using hj)

/-- **The preservation proof, with every hypothesis load-bearing.**  Given an
entity transform that succeeds, lands inside the plan's documents, and leaves
any tombstone behind the live line, `mapAt` succeeds, writes exactly that
entity, and leaves `docs` alone. -/
theorem mapAt_ok_of_inRange (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity)
    (e e' : Entity) (hget : p.val.store.get i = some e) (hf : f e = .ok e')
    (hin : entityInRange p.val e' = true) (hor : demotionOriented p.val e' = true) :
    ∃ q : WfPlan, p.mapAt i f = .ok q ∧ q.val.store.get i = some e' ∧
      q.val.docs = p.val.docs := by
  have hsome : (p.val.store.get i).isSome = true := by rw [hget]; rfl
  have hparts := planWf_parts p.property
  have hq : planWf { p.val with store := p.val.store.set i e' hsome } = true :=
    planWf_of_parts hparts.1 (sitesInRange_set p.val i e' hsome hparts.2.1 hin) hparts.2.2.1
      (demotionsOriented_set p.val i e' hsome hparts.2.2.2 hor)
  refine ⟨⟨_, hq⟩, ?_, ?_, rfl⟩
  · unfold WfPlan.mapAt
    split
    · rename_i hn; rw [hget] at hn; simp at hn
    · rename_i a hget'
      rw [hget] at hget'
      injection hget' with hget'
      subst hget'
      rw [hf]
      simp only [dif_pos hq]
  · exact Store.get_set_self p.val.store i e' hsome

/-- **And the check bites.**  A transform whose result would leave a tombstone
in a horizon the live line does not follow is refused, and nothing is written.
This is the half that keeps the loader honest: the kernel cannot emit a pair of
`[-]` lines whose orientation the files do not fix, so `ambiguousDemotion`
(Boundary) is never a diagnosis of the kernel's own output. -/
theorem mapAt_rejects_unoriented (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity)
    (e e' : Entity) (hget : p.val.store.get i = some e) (hf : f e = .ok e')
    (hbad : demotionOriented p.val e' = false) : p.mapAt i f = .error .badHorizon := by
  have hsome : (p.val.store.get i).isSome = true := by rw [hget]; rfl
  have hdom : i ∈ p.val.store.dom := (p.val.store.domSpec i).mpr hsome
  have hq : ¬ (planWf { p.val with store := p.val.store.set i e' hsome } = true) := by
    intro hc
    have hall := List.all_eq_true.1 (planWf_parts hc).2.2.2 i (by simpa using hdom)
    rw [Store.get_set_self] at hall
    -- the updated plan has the same `docs`, and `demotionOriented` reads only those
    have hbad' : demotionOriented p.val e' = true := hall
    rw [hbad] at hbad'
    simp at hbad'
  unfold WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [hf]
    simp only [dif_neg hq]

/-- `tm move`.  The destination is a `Dest`, not a `Nat`. -/
def cmdMove (i : Id) (rank : Nat) : Relocation := fun p d => p.mapAt i (moveTo (d.site rank))
/-- `tm drop`. -/
def cmdDrop (i : Id) : Transform := (·.mapAt i (fun e => .ok (drop e)))
/-- `tm edit ^id est=v`. -/
def cmdSetEst (v : Nat) (i : Id) : Transform := (·.mapAt i (fun e => .ok (setEstE v e)))
/-- `tm demote`. -/
def cmdDemote (i : Id) (rank per : Nat) : Relocation :=
  fun p d => p.mapAt i (demote (d.site rank) per)
/-- `tm readopt`. -/
def cmdReadopt (i : Id) (rank : Nat) : Relocation :=
  fun p d => p.mapAt i (fun e => .ok (readopt (d.site rank) e))

/-! ## Where a horizon *name* is resolved, and why not here

A previous version of this module carried `DocRegion`, `findDoc`,
`resolveHorizon` and `demoteTarget` — "`tm move ^id week` names a grain and the
file is computed" — and **nothing called any of them**.  They are deleted rather
than left standing, because dead code that reads like a design decision is worse
than no code: it says a question has been settled that has not been.

The wire form names a *document*, and `resolveDest` turns that into a `Dest`.
Turning the word `week` into a document needs `now` and real ISO-week and
civil-month arithmetic; `index` here is `d`, `d/7`, `d/30`, deliberately a toy
(Grain.lean), and wiring a toy calendar into the command path would be a worse
lie than the dead code was.  So horizon-name resolution stays with the host
until the calendar layer exists.

What the derived order *is* load-bearing for is stated where it is used:
`horizonPrecedes` orders the two files of a demotion
(`demotion_target_follows_the_closed_region`, Grain.lean), `demotionsOriented`
makes that part of what a plan is (Plan.lean), and the loader inverts it
(`orientPair`, Boundary.lean).

## The laws

Legend: **P** proved here, **R** refuted here. -/

/-- **L5 (P).**  The precondition the Rust never had, as a theorem: a move into
the file the tombstone occupies is *rejected*, not silently duplicated.  This
is the single missing check behind 164 violating command sequences that are
still reachable at tm HEAD. -/
theorem move_into_archive_file_is_rejected (e : Entity) (t r : Site)
    (h : e.val.archive = some r) (hd : r.doc = t.doc) : moveTo t e = .error .occupied := by
  unfold moveTo lift
  have hbad : ¬ (wfPair t e.val.archive = true) := by simp [h, hd]
  simp [hbad]

/-- The same at the plan level: the command fails, the plan is unchanged. -/
theorem plan_move_into_archive_file_is_rejected (p : WfPlan) (i : Id) (e : Entity)
    (d : Dest p.val) (rank : Nat) (r : Site)
    (hget : p.val.store.get i = some e) (h : e.val.archive = some r) (hd : r.doc = d.ix) :
    cmdMove i rank p d = .error .occupied := by
  unfold cmdMove WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i e' hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [move_into_archive_file_is_rejected e (d.site rank) r h hd]

/-- **The other half of the same story, and the reason the plan-level check is
not a trapdoor.**  A move to a destination that exists and is *ahead of* this
id's tombstone — which for an item with no tombstone is every destination —
succeeds, and the item is where the user asked for it.  Both hypotheses are
used; drop either and the conclusion is false.

`hfree` subsumes the older "the destination does not hold the tombstone": a
horizon does not precede itself (`horizonPrecedes_irrefl`), so a destination
ahead of the tombstone is in particular not the tombstone's own file. -/
theorem cmdMove_succeeds (p : WfPlan) (i : Id) (e : Entity) (d : Dest p.val) (rank : Nat)
    (hget : p.val.store.get i = some e)
    (hfree : ∀ r, e.val.archive = some r →
      horizonPrecedes (docRegion p.val r.doc) (docRegion p.val d.ix) = true) :
    ∃ q : WfPlan, cmdMove i rank p d = .ok q ∧
      (∃ e', q.val.store.get i = some e' ∧ e'.val.live = d.site rank) := by
  have hrange := entityInRange_of_mem p i e hget
  simp only [entityInRange, Bool.and_eq_true] at hrange
  have hne : ∀ r, e.val.archive = some r → r.doc ≠ d.ix := by
    intro r hr hc
    have h1 := hfree r hr
    rw [hc, horizonPrecedes_irrefl] at h1
    simp at h1
  have hwf : wf { e.val with live := d.site rank } = true := by
    cases ha : e.val.archive with
    | none => simp [wf, ha]
    | some r =>
        have := hne r ha
        simp [wf, ha, Dest.site]
        omega
  have hf : moveTo (d.site rank) e = .ok ⟨_, hwf⟩ := by
    unfold moveTo lift; simp only [dif_pos hwf]
  have hin : entityInRange p.val (⟨_, hwf⟩ : Entity) = true := by
    simp only [entityInRange, Bool.and_eq_true, siteInRange, decide_eq_true_eq]
    refine ⟨d.ok, ?_⟩
    have := hrange.2
    exact this
  have hor : demotionOriented p.val (⟨_, hwf⟩ : Entity) = true := by
    unfold demotionOriented
    cases ha : e.val.archive with
    | none => simp [ha]
    | some r => simpa [ha, Dest.site] using hfree r ha
  obtain ⟨q, hq, hqi, _⟩ := mapAt_ok_of_inRange p i (moveTo (d.site rank)) e _ hget hf hin hor
  exact ⟨q, hq, _, hqi, rfl⟩

/-- **A demotion files work forward, or it does not happen.**  §6.3's close
files leftovers into `closeTo`, which is never itself closed
(`closeTo_target_is_open`), so the tombstone's horizon always precedes the live
line's.  A `demote` whose destination is not ahead of the file the item is in
would write two `[-]` lines that no reader could tell apart; it is refused
instead.  Both hypotheses are load-bearing: with `e.val.live.doc = d.ix` the
entity-level `wf` fires first and the error is `occupied`. -/
theorem demote_into_a_horizon_that_does_not_follow_is_rejected (p : WfPlan) (i : Id) (e : Entity)
    (d : Dest p.val) (rank per : Nat) (hget : p.val.store.get i = some e)
    (hne : e.val.live.doc ≠ d.ix)
    (hbad : horizonPrecedes (docRegion p.val e.val.live.doc) (docRegion p.val d.ix) = false) :
    cmdDemote i rank per p d = .error .badHorizon := by
  have hwf : wf { e.val with live := d.site rank, archive := some e.val.live,
                             stamps := e.val.stamps ++ [per] } = true := by
    simp only [wf, wfPair, Dest.site, bne_iff_ne, ne_eq]
    exact hne
  have hf : demote (d.site rank) per e = .ok ⟨_, hwf⟩ := by
    unfold demote lift; simp only [dif_pos hwf]
  refine mapAt_rejects_unoriented p i _ e _ hget hf ?_
  simpa [demotionOriented, Dest.site] using hbad

/-- **L1 (P).**  `move` is idempotent on the subdomain where it succeeds. -/
theorem move_idem (t : Site) (e e' : Entity) (h : moveTo t e = .ok e') :
    (moveTo t e').map Subtype.val = .ok e'.val := by
  have hv : e'.val = { e.val with live := t } := lift_roundtrips _ _ h
  have hlive : e'.val.live = t := by rw [hv]
  have hp : wfPair e'.val.live e'.val.archive = true := by have := e'.property; simpa using this
  unfold moveTo lift
  rw [← hlive]; simp [hp, Except.map]

/-- **L2 (P).**  `move` is last-wins — **on the subdomain where the first move
succeeds.**  The subdomain is not decoration; see L3. -/
theorem move_last_wins (t t' : Site) (e a : Entity) (h : moveTo t e = .ok a) :
    (moveTo t' a).map Subtype.val = (moveTo t' e).map Subtype.val := by
  have hv : a.val = { e.val with live := t } := lift_roundtrips _ _ h
  unfold moveTo lift; rw [hv]

/-- **L3 (R).**  `move` is *not* last-wins globally: a **failed** first move is
not the same as no first move.  The composite errors where the single move
succeeds.  This matters for the TUI, which retries. -/
theorem move_last_wins_refuted_globally :
    ∃ (t t' : Site) (e : Entity),
      ((moveTo t e).bind (moveTo t')).map Subtype.val ≠ (moveTo t' e).map Subtype.val := by
  refine ⟨⟨1, 0⟩, ⟨2, 0⟩,
    ⟨⟨⟨0, 0⟩, some ⟨1, 0⟩, .live .free, ⟨[], []⟩, []⟩, rfl⟩, ?_⟩
  simp [moveTo, lift, Except.map, Except.bind]

/-! ### L4: what `move` is and is not invertible by

The first version of this refutation picked `moveTo ⟨e.live.doc, 0⟩` as the
inverse and showed it does not restore an entity whose rank was 3.  That is a
strawman: nobody proposes rank 0 as an inverse, and the opposite theorem —
`move_back_restores` — is provable in this same kernel.  So the claim is
withdrawn and replaced by the two statements that are actually true. -/

/-- **L4a (P).  `move` *is* invertible at the `Site` level**, by the inverse a
reasonable person would propose: move it back where it came from.  Nothing is
lost — not the rank, not the tombstone, not the bytes. -/
theorem move_back_restores (t : Site) (e a : Entity) (h : moveTo t e = .ok a) :
    (moveTo e.val.live a).map Subtype.val = .ok e.val := by
  have hv : a.val = { e.val with live := t } := lift_roundtrips _ _ h
  have hp : wf e.val = true := e.property
  unfold moveTo lift
  rw [hv]
  simp only [wf_eq] at hp
  simp [hp, Except.map]

/-- **L4b (R).  The *command* is not invertible**, and this is where the real
obstruction is: the wire form of `move` carries a document, not a rank, and the
rank is generated fresh in the destination (`freshRank`, Boundary.lean).  So the
"inverse" a user can issue puts the line back in the right file at the wrong
place, and `tm undo` must replay the log rather than apply an inverse command.

The hypothesis is exactly "the generated rank is not the one the item had", and
`freshRank_gt` in Boundary.lean discharges it for every item the plan holds. -/
theorem move_back_at_a_fresh_rank_is_not_the_inverse (t : Site) (n : Nat) (e a : Entity)
    (hne : n ≠ e.val.live.rank) (h : moveTo t e = .ok a) :
    (moveTo ⟨e.val.live.doc, n⟩ a).map Subtype.val ≠ .ok e.val := by
  have hv : a.val = { e.val with live := t } := lift_roundtrips _ _ h
  unfold moveTo lift
  rw [hv]
  split
  · intro hc
    simp only [Except.map, Except.ok.injEq] at hc
    apply hne
    have := congrArg (fun c => c.live.rank) hc
    simpa using this
  · simp [Except.map]

/-- **L6/L7 (P).** -/
theorem drop_idem (e : Entity) : (drop (drop e)).val = (drop e).val := rfl
theorem settled_absorbing (e : Entity) : (drop e).val.status = .settled .dropped := rfl

/-- **L8 (P).**  Bug 2 — `tm close month --drop` marking the *archive copy*
`[~]`, so both lines read as live — is `rfl` here, because archive-ness is
positional and not a stored glyph. -/
theorem drop_preserves_archive_glyph (e : Entity) (r : Site) (h : e.val.archive = some r) :
    glyphAt (drop e).val r = Glyph.demoted := by simp [glyphAt, drop, h]

/-- §6.3's "readopt: `[-]` → `[ ]`, stamp kept" is **derived** from clearing
the archive, not written down as a rule a writer can forget. -/
theorem readopt_clears_archive (t : Site) (e : Entity) : (readopt t e).val.archive = none := rfl
theorem readopt_reopens (t : Site) (e : Entity) : glyphAt (readopt t e).val t = Glyph.todo := rfl
theorem readopt_keeps_stamps (t : Site) (e : Entity) :
    (readopt t e).val.stamps = e.val.stamps := rfl

/-- **L9 (P).**  `tm edit ^id est=v` writes the slot the view reads.  In the
Rust it wrote the other slot, reported success, and changed nothing. -/
theorem set_is_not_silent (bm v : Nat) (e : Entity) :
    viewRemaining bm (setEstE v e).val.line = some v := view_set_is_not_silent bm v e.val.line

/-- **L10 (P).** -/
theorem set_last_wins (bm v v' : Nat) (e : Entity) :
    viewRemaining bm (setEstE v' (setEstE v e)).val.line = some v' :=
  view_set_is_not_silent bm v' _

/-! ## demote / readopt: the stamp laws -/

theorem demote_stamps (t : Site) (per : Nat) (e a : Entity) (h : demote t per e = .ok a) :
    a.val.stamps = e.val.stamps ++ [per] := by
  have := lift_roundtrips _ _ h; rw [this]

/-- **L11 (R).**  `demote` is **not** idempotent, and that is correct: stamps
accumulate deliberately, to drive the month review's "≥ 2 stamps" cut list.
Idempotence holds only *modulo* `stamps`, and the kernel must say which it
means rather than leave two readings of §6.3 available. -/
theorem demote_not_idem (t t' : Site) (per : Nat) (e a b : Entity)
    (h1 : demote t per e = .ok a) (h2 : demote t' per a = .ok b) :
    b.val.stamps ≠ a.val.stamps := by
  have ha := demote_stamps t per e a h1
  have hb := demote_stamps t' per a b h2
  rw [hb, ha]
  intro hc
  have := congrArg List.length hc
  simp at this

/-- **L12 (R).**  `readopt ∘ demote ≠ id` on the nose, because `demote` stamps.
§6.3's own wording ("stamp kept") already admits this; here the admission is a
theorem. -/
theorem readopt_demote_not_id (t : Site) (per : Nat) (e a : Entity)
    (h : demote t per e = .ok a) : (readopt e.val.live a).val.stamps ≠ e.val.stamps := by
  have ha := demote_stamps t per e a h
  show a.val.stamps ≠ e.val.stamps
  rw [ha]
  intro hc
  have := congrArg List.length hc
  simp at this

/-- **L13 (P).**  Modulo stamps, on the subdomain a week item is in before a
close (`archive = none`, status `live free`), `readopt` undoes `demote`
exactly: same file, same rank, same tombstone state, same bytes. -/
theorem readopt_demote_id_mod_stamps (t : Site) (per : Nat) (e a : Entity)
    (harch : e.val.archive = none) (hst : e.val.status = .live .free)
    (h : demote t per e = .ok a) :
    (readopt e.val.live a).val.live = e.val.live ∧
    (readopt e.val.live a).val.archive = e.val.archive ∧
    (readopt e.val.live a).val.status = e.val.status ∧
    (readopt e.val.live a).val.line = e.val.line := by
  have hv := lift_roundtrips _ _ h
  refine ⟨rfl, by rw [harch]; rfl, by rw [hst]; rfl, ?_⟩
  show a.val.line = e.val.line
  rw [hv]

/-! ## Conservation: the invariant three Rust commits tried to enforce -/

/-- "A close's measurement must not be lost": floor `remaining` at the value
the close recorded. -/
def FloorsAtRecorded (bm : Nat) (f : Nat → Entity → Entity) : Prop :=
  ∀ rec e, rec ≤ remainingOf bm (f rec e).val.line

/-- "A deliberate `tm edit ^id est=1b` is not silently overwritten." -/
def RespectsUserEdit (bm : Nat) (f : Nat → Entity → Entity) : Prop :=
  ∀ rec e, remainingOf bm (f rec e).val.line = remainingOf bm e.val.line

/-- **L14 (R).  The most important refutation.**  No rule can do both, so the
naive conservation law — the one three separate Rust fixes tried to enforce —
is false, and it is false for a reason no test suite volunteered: flooring at
the recorded value also silently overrides a deliberate `tm edit est=`.

Lean refuses the naive law.  It does **not** hand you the exception; only
running the binary did that.  What the kernel buys is that the exception is
written once, in the signature, where a later writer cannot fail to read it. -/
theorem floor_and_respect_are_incompatible (bm : Nat) (f : Nat → Entity → Entity)
    (hf : FloorsAtRecorded bm f) : ¬ RespectsUserEdit bm f := by
  intro hr
  let e0 : Entity := ⟨⟨⟨0, 0⟩, none, .live .free, ⟨[], []⟩, []⟩, rfl⟩
  have h1 : 1 ≤ remainingOf bm (f 1 e0).val.line := hf 1 e0
  have h2 : remainingOf bm (f 1 e0).val.line = remainingOf bm e0.val.line := hr 1 e0
  have h3 : remainingOf bm e0.val.line = 0 := rfl
  omega

/-- The corrected rule.  The exception lives in the **signature**: a close
cannot silently forget to ask whether the user set an estimate since. -/
def demoteEst (bm : Nat) (userSet : Bool) (rec : Nat) (e : Entity) : Entity :=
  match userSet with
  | true  => e
  | false =>
    (⟨{ e.val with line := setEst (max (remainingOf bm e.val.line) rec) e.val.line },
      e.property⟩ : Entity)

/-- **L15a (P).**  When the user has not set an estimate, the close's
measurement is a floor. -/
theorem demoteEst_conserves (bm rec : Nat) (e : Entity) :
    rec ≤ remainingOf bm (demoteEst bm false rec e).val.line ∧
    remainingOf bm e.val.line ≤ remainingOf bm (demoteEst bm false rec e).val.line := by
  have hv : remainingOf bm (demoteEst bm false rec e).val.line
      = max (remainingOf bm e.val.line) rec := by
    have hline : (demoteEst bm false rec e).val.line
        = setEst (max (remainingOf bm e.val.line) rec) e.val.line := rfl
    unfold remainingOf
    rw [hline, view_set_is_not_silent]
    rfl
  rw [hv]
  exact ⟨Nat.le_max_right _ _, Nat.le_max_left _ _⟩

/-- **L15b (P).**  When the user has set one, it stands, byte for byte. -/
theorem demoteEst_respects_user (bm rec : Nat) (e : Entity) :
    (demoteEst bm true rec e).val.line = e.val.line := rfl

/-! ## What is actually structural, and what is proved

An earlier version of this section carried a theorem named
`every_transform_preserves_the_invariant` whose `f`, `p` and `_h` binders were
all unused — it was `no_two_lines_of_one_id_in_one_file` with three ignorable
arguments, and its name promised a closure property it did not state.  It is
withdrawn.  What replaces it is the honest split:

* the id-uniqueness half genuinely **is** structural, and the theorem that says
  so is `no_two_lines_of_one_id_in_one_path` (Plan.lean).  It quantifies over
  every `PlanCore` and mentions no command, so there is nothing for a command to
  preserve.  Restating it with a command bound in front adds no information;
* the other two halves — every placement names a file that exists, and no two
  files share a path — are **not** free.  They are decidable predicates that
  `mapAt` re-establishes on the post-state of every command, and the proof that
  the commands can discharge them is `mapAt_ok_of_inRange` and `cmdMove_succeeds`
  above, where the hypotheses do work.

So the closure statement below is about the pair of them together, and it is not
a restatement: the `.ok` branch needs `mapAt`'s check to have passed, and the
`.error` branch is what makes "no partial write" true. -/

/-- The state a command produces with the refinement **forgotten** — a bare
`PlanCore`, which is what a host would hold if the kernel handed back a record
instead of a subtype.  Closure is a real claim at this type and a tautology at
the other one, so this is where it is stated. -/
def Transform.state (f : Transform) (p : WfPlan) : Option PlanCore :=
  match f p with
  | .ok q    => some q.val
  | .error _ => none

/-- **Closure.**  For every command and every accepted plan, if the command
produces a state at all, that state passes the decidable checker — the same
`planWf` that admitted the input, covering all three halves: no prose line is an
item line, every placement names a file that exists, and no two files share a
path.  There is no third outcome: `Transform.state` is `none` exactly when the
command returned a structured error, and then nothing was written. -/
theorem transform_closed (f : Transform) (p : WfPlan) (q : PlanCore)
    (h : f.state p = some q) : planWf q = true := by
  unfold Transform.state at h
  split at h
  · rename_i r _
    injection h with h
    subst h
    exact r.property
  · simp at h

theorem transform_state_none (f : Transform) (p : WfPlan) (h : f.state p = none) :
    ∃ k : KErr, f p = .error k := by
  unfold Transform.state at h
  split at h
  · simp at h
  · rename_i k _; exact ⟨k, by assumption⟩

end Tm
