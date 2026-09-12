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
  record it was left by **whenever the record's box is `[-]` too** — the case
  in which the two lines are otherwise indistinguishable — are decidable
  predicates `WfPlan.mapAt`
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

open Field (Stamp Dur DurUnit)

inductive KErr
  | occupied          -- the destination file already holds this id's other line
  | noSuchId
  | notDemoted
  /-- the item already carries a tombstone, so there is no second one to write.
      §6.3 gives an item **one** archive record: the week close creates it, and
      `tm close month` then *moves* the record ("moves them to the next month
      file", touching nothing else) rather than demoting it again.  Both ways
      of proceeding here lose a line — overwrite the standing tombstone and its
      file's line vanishes; keep it and the line the record is leaving does. -/
  | alreadyDemoted
  /-- the destination is not a horizon this item may occupy: either not a
      document of this plan at all, or — while a tombstone stands and the record
      still reads `[-]` — not ahead of the file that tombstone is in.  Both are
      "the post-state fails `planWf`". -/
  | badHorizon
  /-- an **insertion** whose post-state fails `planWf` for an item reason: a
      title carrying a dangling `after:^…`, a day file whose placement is not
      `# Pinned`, an `optional` line saying no duration.  Kept distinct from
      `badHorizon` because that fault is about *relocation* and the two names
      let the host give different advice.  On the command path the name is all
      the wire carries — `{"err":{"kernel":"badItem"}}`; `firstItemFault` is
      the *loader's* diagnostic (the `itemCheck` field) and never accompanies
      a command refusal. -/
  | badItem
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

/-- The positive half of the same reading: a `Core` that passes `wf` lifts to
exactly the entity with that proof. -/
theorem lift_ok_of_wf (c : Core) (hc : wf c = true) : lift c = .ok ⟨c, hc⟩ := by
  unfold lift
  exact dif_pos hc

/-! ## Entity-level transforms -/

/-- `tm move ^id <horizon>`.  **There is no append**: the destination replaces
the live *site*, and `lift` refuses when that would put two lines of one id in
one file.  `horizon::move_line`'s missing precondition has nowhere to live. -/
def moveTo (t : Site) (e : Entity) : Except KErr Entity := lift { e.val with live := t }

def drop (e : Entity) : Entity :=
  ⟨{ e.val with status := .settled .dropped }, e.property⟩

/-- `tm edit ^id est=v`.  This is now the **field** setter (`Field.setEst`
over `setKey`), the same reader pair `Core.est` consumes — gap 4's two
readers are collapsed on the command path, and the stage-one `Nat` setter
below survives only as the fold arithmetic `demoteEst` still shares.  The
written token is byte-identical to the stage one's
(`the_two_est_setters_write_the_same_token`), so no wire behaviour moves. -/
def setEstE (v : Nat) (e : Entity) : Entity :=
  ⟨{ e.val with line := Field.setEst (Dur.simple v DurUnit.minutes) e.val.line },
    e.property⟩

/-- **Gap 4, closed: the command path writes what the field path reads.**
The `est` request lands on `setEstE`; `Core.est` is
`Field.viewRemainingDur`; `view_set_remaining` says the second reads the
first verbatim, with no hypothesis on the entity's other bytes. -/
theorem the_command_path_writes_what_the_field_path_reads (v : Nat) (e : Entity) :
    (setEstE v e).val.est = some (Dur.simple v DurUnit.minutes) :=
  Field.view_set_remaining (Dur.simple v DurUnit.minutes) e.val.line (by rfl)

/-- The stage-one `Nat` entity setter, in its own name now: the body `setEstE`
carried until gap 4 closed.  It survives as **fold arithmetic** — `demoteEst`
is its only user, the close floor that reads `remainingOf` and writes the same
`Nat` view back — and it is deliberately *not* on the request path anymore, so
a command line is never read through one reader and written through another. -/
def setEstFoldE (v : Nat) (e : Entity) : Entity :=
  ⟨{ e.val with line := setEst v e.val.line }, e.property⟩

/-- `tm rank ^id n`.  Rank moves an item **within its own file**: the wire
carries no destination, and there is no `Dest` proof because no file changes —
which is what separates it from `move` and why it cannot reuse `Relocation`.
The new rank is the caller's, verbatim; `mapAt` re-checks the post-state, so a
rank that collides with another line of this file dies there as `badHorizon`
rather than silently renumbering the file.  Both §5.8 directions are theorems
now (end of Boundary.lean): `rank_onto_a_taken_rank_is_refused` is the
collision refusal, and `cmdRank_succeeds` mirrors `cmdMove_succeeds` on the
replacement lemma (`lines_set`/`normalized_set`, Plan.lean). -/
def setRankE (n : Nat) (e : Entity) : Except KErr Entity :=
  lift { e.val with live := ⟨e.val.live.doc, n⟩ }

/-- `wf` speaks only of *which files* hold an id's lines, never of where inside
a file a line sits — so rewriting a live rank leaves `wf` unchanged.  This is
the reason `lift` below can refuse a genuine collision yet never refuse for a
reason it was not designed for. -/
theorem wf_setRank (c : Core) (n : Nat) :
    wf { c with live := ⟨c.live.doc, n⟩ } = wf c := by
  cases c with
  | mk live archive status line parent =>
      unfold wf wfPair Core.archiveSite
      cases archive <;> rfl

/-- **L20a at entity level.**  Re-ranking a line to the rank it already has is
a no-op: the second `lift` sees the same `Core` the first produced. -/
theorem setRankE_idem (n : Nat) (e e' : Entity) (h : setRankE n e = .ok e') :
    setRankE n e' = .ok e' := by
  have hv : e'.val = { e.val with live := ⟨e.val.live.doc, n⟩ } := by
    unfold setRankE at h
    exact lift_roundtrips _ _ h
  unfold setRankE
  have hlive : e'.val.live = ⟨e'.val.live.doc, n⟩ := by rw [hv]
  have hupd : { e'.val with live := ⟨e'.val.live.doc, n⟩ } = e'.val := by
    rw [hlive.symm]
  have hwf : wf e'.val = true := by rw [hv, wf_setRank]; exact e.property
  rw [hupd]
  exact lift_ok_of_wf _ hwf

/-- `close`/`demote`, §6.3's week row, as one entity transform.  Read the row
literally and it says three things, and this writes all three:

* "`[ ]`/`[>]` → `[-]` in the week file" — the tombstone keeps the **bytes it
  had**, box excepted, and `renderCore` writes `[-]` over any archive
  placement.  So the tombstone is `⟨e.live, e.line⟩`: where it was, saying what
  it said;
* "the line is copied to `month/<current>#Demoted` … with `demoted:W37`
  appended" — the copy is the record, it goes to `target`, and the stamp goes
  on **its** line and not on the tombstone's.  Before the tombstone carried its
  own bytes there was one token vector for both sites, so the stamp appeared
  in the week file too, which §6.3 does not say and `tm` does not do;
* the record's own box is `[-]` as well until something reopens it, and that is
  now an explicit `status := .demoted` rather than a positional effect of the
  archive being present.  `readopt` is what turns it back to `[ ]`.

(§6.3 also says the copy carries `est:` = remaining.  That needs the rollup,
which is stage 4 — README gap 20 — so it is not written here; the caller's
`demoteEst` is the piece that exists.)

**And it is the week close, once.**  §6.3 gives an item one archive record;
the *month* close "moves them to the next month file", which is `move`, not a
second demotion.  So an item that already carries a tombstone is refused, and
that refusal is what makes the tombstone's bytes safe: overwrite the standing
one and its file's line disappears from the render with the kernel returning
`ok` — the failure `no_line_is_lost` is named after, reached through the one
field that theorem cannot see, since the entity still has two placements and
both are in range.  Keeping the standing one instead loses the line the record
is *leaving*, which is the line §6.3's week row says must stay behind as `[-]`.
Neither is §6.3, so neither is written. -/
def demote (target : Site) (s : Stamp) (e : Entity) : Except KErr Entity :=
  if e.val.archive.isSome then .error .alreadyDemoted
  else lift { e.val with live := target, archive := some ⟨e.val.live, e.val.line⟩,
                         status := .demoted,
                         line := Field.setDemoted (e.val.stamps ++ [s]) e.val.line }

/-- **A second demotion is refused, and no line is dropped.**  The state this
rules out is `tm close month` written as a demote; the verb for that is
`move`. -/
theorem demote_on_a_standing_tombstone_is_refused (t : Site) (s : Stamp) (e : Entity)
    (h : e.val.archive.isSome = true) : demote t s e = .error .alreadyDemoted := by
  simp [demote, h]

theorem demote_ok (t : Site) (s : Stamp) (e : Entity) (h : e.val.archive = Option.none) :
    demote t s e = lift { e.val with live := t, archive := some ⟨e.val.live, e.val.line⟩,
                                     status := .demoted,
                                     line := Field.setDemoted (e.val.stamps ++ [s]) e.val.line } := by
  simp [demote, h]

/-- What `demote` produces where it succeeds — `lift_roundtrips` through the
precondition. -/
theorem demote_roundtrips (t : Site) (st : Stamp) (e a : Entity) (h : demote t st e = .ok a) :
    a.val = { e.val with live := t, archive := some ⟨e.val.live, e.val.line⟩,
                         status := .demoted,
                         line := Field.setDemoted (e.val.stamps ++ [st]) e.val.line } := by
  rw [demote] at h
  split at h
  · simp at h
  · exact lift_roundtrips _ _ h

/-- Where it succeeds, the item had no tombstone. -/
theorem demote_archive_none (t : Site) (st : Stamp) (e a : Entity)
    (h : demote t st e = .ok a) : e.val.archive = Option.none := by
  rw [demote] at h
  split at h
  · simp at h
  · rename_i hn; simpa using hn

/-- `readopt` **consumes** the tombstone, which is why it cannot leave a second
line in the file the stale one was in (bug 5).  §6.3's "`[-]` → `[ ]`" is the
status going back to `live free`; the record's bytes, stamp and all, are kept.

**And it is a demoted line or it is nothing**, which is the precondition §6.3
states in the same sentence: "moves a *demoted line* into the current week
(`[-]` → `[ ]`, stamp kept)".  Without it `readopt` is data loss on the very
pair this kernel was changed to admit — §4.3's fixture, where the record is
already `[ ]` and the tombstone is the line carrying `est:` = remaining and
`demoted:W37`.  Consuming that tombstone throws both away and returns `ok`,
and "stamp kept" is exactly what is lost.  There is no demoted line to reopen
there; the item is already adopted, and the stale record is a `drop`'s job.

`KErr.notDemoted` was a constructor no function produced.  This is what it is
for. -/
def readopt (t : Site) (e : Entity) : Except KErr Entity :=
  if e.val.status = Status.demoted
  then .ok ⟨{ live := t, archive := none, status := .live .free, line := e.val.line }, rfl⟩
  else .error .notDemoted

/-- **Reopening a line that is not demoted is refused**, so the bytes the
tombstone carries can never be dropped on the floor. -/
theorem readopt_of_a_live_record_is_refused (t : Site) (e : Entity)
    (h : e.val.status ≠ Status.demoted) : readopt t e = .error .notDemoted := by
  simp [readopt, h]

theorem readopt_ok (t : Site) (e : Entity) (h : e.val.status = Status.demoted) :
    readopt t e = .ok ⟨{ live := t, archive := none, status := .live .free,
                         line := e.val.line }, rfl⟩ := by
  simp [readopt, h]

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

/-- **Inserting a fresh entity re-runs the whole of `planWf` on the post-state,
by computation** — exactly the contract `mapAt` enforces for replacement, and
the reason `add` cannot forget the check.  A title that parses as a dangling
`after:^…` or lands a day-file item outside `# Pinned` is refused with the
named `badItem` — the name is all the wire carries on the command path;
`firstItemFault` is the loader's `itemCheck` diagnostic, not a command-path
field (§5.7).  The
freshness hypothesis is what makes the insert legal at all (§L21); a
non-fresh id is a type error here, not a runtime overwrite. -/
def WfPlan.insertFresh (p : WfPlan) (i : Id) (e : Entity)
    (hfresh : (p.val.store.get i).isNone = true) : Except KErr WfPlan :=
  if hq : planWf { p.val with store := p.val.store.insertFresh i e hfresh } = true then
    .ok ⟨_, hq⟩
  else .error .badItem

theorem WfPlan.insertFresh_get (p : WfPlan) (i : Id) (e : Entity)
    (hfresh : (p.val.store.get i).isNone = true) (q : WfPlan)
    (hq : p.insertFresh i e hfresh = .ok q) : q.val.store.get i = some e := by
  unfold WfPlan.insertFresh at hq
  split at hq
  · cases hq
    exact Store.get_insertFresh_self p.val.store i e hfresh
  · simp at hq

theorem WfPlan.insertFresh_other (p : WfPlan) (i j : Id) (e : Entity)
    (hfresh : (p.val.store.get i).isNone = true) (q : WfPlan)
    (hq : p.insertFresh i e hfresh = .ok q) (hij : j ≠ i) :
    q.val.store.get j = p.val.store.get j := by
  unfold WfPlan.insertFresh at hq
  split at hq
  · cases hq
    exact Store.get_insertFresh_other p.val.store i j e hfresh hij
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
entity transform that succeeds, lands inside the plan's documents, leaves any
tombstone behind the live line, and leaves the item-level checks standing,
`mapAt` succeeds, writes exactly that entity, and leaves `docs` alone.

`hrest` is the last obligation and it is not decoration: since §3.1's item
fields joined the plan-level tier (`itemsWf`, Plan.lean), a transform can break
rank distinctness or `after:` acyclicity, and `mapAt`'s re-check will refuse it.
It is stated as a hypothesis rather than derived, because deriving it — even
for a transform that touches neither the placement nor the item fields — needs a
replacement lemma for `PlanCore.lines` under a single-entity update, which is
not written (README gap 11). -/
theorem mapAt_ok_of_inRange (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity)
    (e e' : Entity) (hget : p.val.store.get i = some e) (hf : f e = .ok e')
    (hin : entityInRange p.val e' = true) (hor : demotionOriented p.val e' = true)
    (hrest : ∀ hs : (p.val.store.get i).isSome = true,
      itemsWf { p.val with store := p.val.store.set i e' hs } = true) :
    ∃ q : WfPlan, p.mapAt i f = .ok q ∧ q.val.store.get i = some e' ∧
      q.val.docs = p.val.docs := by
  have hsome : (p.val.store.get i).isSome = true := by rw [hget]; rfl
  have hparts := planWf_parts p.property
  have hq : planWf { p.val with store := p.val.store.set i e' hsome } = true :=
    planWf_of_parts (p := { p.val with store := p.val.store.set i e' hsome })
      hparts.1 (sitesInRange_set p.val i e' hsome hparts.2.1 hin) hparts.2.2.1
      (demotionsOriented_set p.val i e' hsome hparts.2.2.2.1 hor) (hrest hsome)
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

/-- Forward success form, with the refinement kept: the post-state is exactly
`⟨_, hq⟩`, so a law stated over `q.val` can talk about `(mapAt i f)` without
inverting the subtype.  (`mapAt_ok_shape`, Boundary.lean, is the inverse
reading — it forgets `hq` and exists so a law can *decompose* a given `ok`.) -/
theorem mapAt_at {p : WfPlan} {i : Id} {f : Entity → Except KErr Entity} {e e' : Entity}
    (hget : p.val.store.get i = some e) (hfe : f e = .ok e')
    (hq : planWf { p.val with store := p.val.store.set i e' (by rw [hget]; rfl) } = true) :
    p.mapAt i f = .ok ⟨_, hq⟩ := by
  unfold WfPlan.mapAt
  split
  · rename_i hn
    rw [hget] at hn
    simp at hn
  · rename_i a hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [hfe]
    simp only [dif_pos hq]

/-- **Storing back the entity that was already there does nothing.**  The
dependent `isSome` proof rides along — `Store.set` is a `funext` away from the
identity once the replaced value equals the found value. -/
theorem Store.set_same (s : Store) (i : Id) (e : Entity) (h : (s.get i).isSome = true)
    (hget : s.get i = some e) : s.set i e h = s := by
  have hfun : (fun j => if j = i then some e else s.get j) = s.get := by
    funext j
    by_cases hji : j = i <;> simp_all
  cases s
  simp [Store.set, hfun]

/-- ...and so is re-writing a `PlanCore` whose only change was writing back
the entity it already held. -/
theorem planCore_set_same {p : PlanCore} {i : Id} {e : Entity}
    (hget : p.store.get i = some e) :
    { p with store := p.store.set i e (by rw [hget]; rfl) } = p := by
  rw [Store.set_same _ _ _ _ hget]

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
    have hall := List.all_eq_true.1 (planWf_parts hc).2.2.2.1 i (by simpa using hdom)
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
def cmdDemote (i : Id) (rank : Nat) (s : Stamp) : Relocation :=
  fun p d => p.mapAt i (demote (d.site rank) s)
/-- `tm readopt`. -/
def cmdReadopt (i : Id) (rank : Nat) : Relocation :=
  fun p d => p.mapAt i (readopt (d.site rank))
/-- `tm rank ^id n`.  Note the type: a plain `Transform`, not a `Relocation`.
No `Dest` is demanded because rank is not a relocation — no file changes, and
§6.3's "line order is your rank within a priority class" (§7.4) is a fact about
indices *inside one file*.  §13's verb list calls it, and until this line the
kernel answered with `unknown op rank`. -/
def cmdRank (i : Id) (n : Nat) : Transform := (·.mapAt i (setRankE n))

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
is the single missing check behind 426 violating command pairs that are
still reachable at tm HEAD. -/
theorem move_into_archive_file_is_rejected (e : Entity) (t r : Site)
    (h : e.val.archiveSite = some r) (hd : r.doc = t.doc) : moveTo t e = .error .occupied := by
  unfold moveTo lift
  have hh : ({ e.val with live := t } : Core).archiveSite = some r := h
  have hbad : ¬ (wf { e.val with live := t } = true) := by simp [wf_eq, hh, hd]
  rw [dif_neg hbad]

/-- The same at the plan level: the command fails, the plan is unchanged. -/
theorem plan_move_into_archive_file_is_rejected (p : WfPlan) (i : Id) (e : Entity)
    (d : Dest p.val) (rank : Nat) (r : Site)
    (hget : p.val.store.get i = some e) (h : e.val.archiveSite = some r) (hd : r.doc = d.ix) :
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
succeeds, and the item is where the user asked for it.  Every hypothesis is
used; drop any one and the conclusion is false.

`hfree` subsumes the older "the destination does not hold the tombstone": a
horizon does not precede itself (`horizonPrecedes_irrefl`), so a destination
ahead of the tombstone is in particular not the tombstone's own file.

It is a **sufficient** condition and no longer a tight one, and that is the
orientation change showing through: `demotionsOriented` asks for the horizon
order only when the record's box is `[-]`, so a record that has been reopened
can in fact be moved anywhere.  This theorem does not cover that case and does
not need to — its job is to show the check can be discharged, and the wider
domain is recorded in the README rather than proved here.

`hrank` is the third, and it is the price of `Normalized` joining `planWf`
(Plan.lean): `rank` is a `Nat` the caller chose, and a move onto a rank another
line of this document already occupies leaves an order the file does not
determine.  `applyCmd` (Boundary.lean) always passes `freshRank`, and
`freshRank_gt` proves that is strictly greater than every rank already in the
destination — but the step from there to *this* hypothesis is not written, so at
the boundary rank freshness still rests on `mapAt`'s decidable re-check rather
than on a theorem.  That gap is README 11, and it is recorded rather than
papered over. -/
theorem cmdMove_succeeds (p : WfPlan) (i : Id) (e : Entity) (d : Dest p.val) (rank : Nat)
    (hget : p.val.store.get i = some e)
    (hfree : ∀ r, e.val.archiveSite = some r →
      horizonPrecedes (docRegion p.val r.doc) (docRegion p.val d.ix) = true)
    (hrank : ∀ a : Entity, a.val = { e.val with live := d.site rank } →
      ∀ hs : (p.val.store.get i).isSome = true,
      itemsWf { p.val with store := p.val.store.set i a hs } = true) :
    ∃ q : WfPlan, cmdMove i rank p d = .ok q ∧
      (∃ e', q.val.store.get i = some e' ∧ e'.val.live = d.site rank) := by
  have hrange := entityInRange_of_mem p i e hget
  simp only [entityInRange, Bool.and_eq_true] at hrange
  have hne : ∀ r, e.val.archiveSite = some r → r.doc ≠ d.ix := by
    intro r hr hc
    have h1 := hfree r hr
    rw [hc, horizonPrecedes_irrefl] at h1
    simp at h1
  have hwf : wf { e.val with live := d.site rank } = true := by
    cases ha : e.val.archive with
    | none => simp [wf, Core.archiveSite, ha]
    | some t =>
        have := hne t.site (Core.archiveSite_some ha)
        simp only [wf_eq, Core.archiveSite, ha, Option.map_some, wfPair_some, Dest.site,
          bne_iff_ne, ne_eq]
        exact this
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
    | some t =>
        have := hfree t.site (Core.archiveSite_some ha)
        simp only [ha, Dest.site]
        split
        · exact this
        · rfl
  obtain ⟨q, hq, hqi, _⟩ := mapAt_ok_of_inRange p i (moveTo (d.site rank)) e _ hget hf hin hor
    (fun hs => hrank ⟨_, hwf⟩ rfl hs)
  exact ⟨q, hq, _, hqi, rfl⟩

/-- **A demotion files work forward, or it does not happen.**  §6.3's close
files leftovers into `closeTo`, which is never itself closed
(`closeTo_target_is_open`), so the tombstone's horizon always precedes the live
line's.  A `demote` whose destination is not ahead of the file the item is in
would write two `[-]` lines that no reader could tell apart; it is refused
instead.  Every hypothesis is load-bearing: with `e.val.live.doc = d.ix` the
entity-level `wf` fires first and the error is `occupied`, and with a tombstone
already standing `demote` refuses before any of this
(`demote_on_a_standing_tombstone_is_refused`) — which is why `harch` is here
and is the subdomain §6.3's week close is on. -/
theorem demote_into_a_horizon_that_does_not_follow_is_rejected (p : WfPlan) (i : Id) (e : Entity)
    (d : Dest p.val) (rank : Nat) (st : Stamp) (hget : p.val.store.get i = some e)
    (harch : e.val.archive = Option.none)
    (hne : e.val.live.doc ≠ d.ix)
    (hbad : horizonPrecedes (docRegion p.val e.val.live.doc)
              (docRegion p.val d.ix) = false) :
    cmdDemote i rank st p d = .error .badHorizon := by
  have hwf : wf { e.val with live := d.site rank,
                             archive := some ⟨e.val.live, e.val.line⟩,
                             status := .demoted,
                             line := Field.setDemoted (e.val.stamps ++ [st]) e.val.line }
               = true := by
    simp only [wf_eq, Core.archiveSite, Option.map_some, wfPair_some, Dest.site,
      bne_iff_ne, ne_eq]
    exact hne
  have hf : demote (d.site rank) st e = .ok ⟨_, hwf⟩ := by
    rw [demote_ok _ _ _ harch]; unfold lift; simp only [dif_pos hwf]
  refine mapAt_rejects_unoriented p i _ e _ hget hf ?_
  simpa [demotionOriented, Dest.site, glyphOfStatus] using hbad

/-- **L1 (P).**  `move` is idempotent on the subdomain where it succeeds. -/
theorem move_idem (t : Site) (e e' : Entity) (h : moveTo t e = .ok e') :
    (moveTo t e').map Subtype.val = .ok e'.val := by
  have hv : e'.val = { e.val with live := t } := lift_roundtrips _ _ h
  have hlive : e'.val.live = t := by rw [hv]
  have hp : wfPair e'.val.live e'.val.archiveSite = true := by have := e'.property; simpa using this
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
    ⟨{ live := ⟨0, 0⟩, archive := some ⟨⟨1, 0⟩, ⟨[], []⟩⟩, status := .live .free,
       line := ⟨[], []⟩ }, rfl⟩, ?_⟩
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
theorem drop_preserves_archive_glyph (e : Entity) (r : Site) (h : e.val.archiveSite = some r) :
    glyphAt (drop e).val r = Glyph.demoted := by
  have hh : ((drop e).val).archiveSite = some r := h
  simp [glyphAt, hh]

/-- §6.3's "readopt: `[-]` → `[ ]`, stamp kept" is **derived** from clearing
the archive, not written down as a rule a writer can forget. -/
theorem readopt_clears_archive (t : Site) (e a : Entity) (h : readopt t e = .ok a) :
    a.val.archive = none := by
  rw [readopt] at h; split at h
  · injection h with h; rw [← h]
  · simp at h
theorem readopt_reopens (t : Site) (e a : Entity) (h : readopt t e = .ok a) :
    glyphAt a.val t = Glyph.todo := by
  rw [readopt] at h; split at h
  · injection h with h; rw [← h]; rfl
  · simp at h
/-- §6.3's "stamp kept", and now it really is kept: `readopt` only fires on a
demoted record, which is the line the stamp is on. -/
theorem readopt_keeps_stamps (t : Site) (e a : Entity) (h : readopt t e = .ok a) :
    a.val.stamps = e.val.stamps := by
  rw [readopt] at h; split at h
  · injection h with h; rw [← h]; rfl
  · simp at h

/-- **L9 (P).**  `tm edit ^id est=v` writes the slot the view reads.  In the
Rust it wrote the other slot, reported success, and changed nothing.  The
statement is kept for the **fold** setter, whose law it always was; the
request path gained the stronger field-view law
`the_command_path_writes_what_the_field_path_reads` when gap 4 closed. -/
theorem set_is_not_silent (bm v : Nat) (e : Entity) :
    viewRemaining bm (setEstFoldE v e).val.line = some v :=
  view_set_is_not_silent bm v e.val.line

/-- **L10 (P).** -/
theorem set_last_wins (bm v v' : Nat) (e : Entity) :
    viewRemaining bm (setEstFoldE v' (setEstFoldE v e)).val.line = some v' :=
  view_set_is_not_silent bm v' _

/-! ## demote / readopt: the stamp laws -/

theorem demote_stamps (t : Site) (st : Stamp) (e a : Entity) (h : demote t st e = .ok a) :
    a.val.stamps = e.val.stamps ++ [st] := by
  have hv := demote_roundtrips _ _ _ _ h
  show (Field.viewDemoted a.val.line).getD [] = _
  rw [hv]
  show (Field.viewDemoted (Field.setDemoted (e.val.stamps ++ [st]) e.val.line)).getD [] = _
  rw [Field.view_set_demoted _ _ (by simp)]
  rfl

/-! ### L11: `demote` is not idempotent, and *why* is not what it was

The old statement was `demote t st e = .ok a → demote t' st a = .ok b →
b.stamps ≠ a.stamps`, and it is **withdrawn because it became vacuous**: a
`demote` leaves a tombstone and `demote` now refuses an item that has one, so
`h2` has no witness and the theorem says nothing.  A vacuous refutation is
worse than none — it reads as a proof that the composite behaves, when the
composite does not exist.

What is true, and is what §6.3 actually describes, is that stamps accumulate
across the **cycle**: an item demoted at the close of W36, readopted into W37,
and demoted again at the close of W37 carries `demoted:W36,W37`, which is the
list the month review's "≥ 2 stamps" cut runs on.  That is stated below, and it
is a stronger claim than the `≠` it replaces — it names the list rather than
saying two of them differ. -/

/-- **L11a (P).**  §6.3's `demoted:W36,W37`: two closes with a readopt between
them leave both stamps, in order, on the record's line. -/
theorem stamps_accumulate_across_readopt (t r t' : Site) (st st' : Stamp)
    (e a b c : Entity) (h1 : demote t st e = .ok a) (h2 : readopt r a = .ok b)
    (h3 : demote t' st' b = .ok c) :
    c.val.stamps = e.val.stamps ++ [st, st'] := by
  have ha := demote_stamps t st e a h1
  have hb : b.val.stamps = a.val.stamps := readopt_keeps_stamps _ a b h2
  have hc := demote_stamps t' st' b c h3
  rw [hc, hb, ha]
  simp

/-- **L11b (R).**  And the reason the old L11 went vacuous, as a theorem: the
second close of a *single* demotion is not a `demote` at all.  §6.3's month
close "moves them to the next month file", and `move` is the verb for that. -/
theorem demote_twice_is_not_a_thing (t t' : Site) (st : Stamp) (e a : Entity)
    (h1 : demote t st e = .ok a) : demote t' st a = .error .alreadyDemoted := by
  refine demote_on_a_standing_tombstone_is_refused _ _ a ?_
  rw [demote_roundtrips _ _ _ _ h1]
  rfl

/-- **L12 (R).**  `readopt ∘ demote ≠ id` on the nose, because `demote` stamps.
§6.3's own wording ("stamp kept") already admits this; here the admission is a
theorem. -/
theorem readopt_demote_not_id (t : Site) (st : Stamp) (e a b : Entity)
    (h : demote t st e = .ok a) (hr : readopt e.val.live a = .ok b) :
    b.val.stamps ≠ e.val.stamps := by
  have ha := demote_stamps t st e a h
  have hb : b.val.stamps = a.val.stamps := readopt_keeps_stamps _ a b hr
  rw [hb, ha]
  intro hc
  have := congrArg List.length hc
  simp at this

/-- **L13 (P).**  Modulo the stamp, on the subdomain a week item is in before a
close (`archive = none`, status `live free`), `readopt` undoes `demote`
exactly: same file, same rank, same tombstone state.

"Modulo the stamp" is now a statement about **bytes**, and that is the change
this law records.  §6.3's `readopt` keeps the stamp, and the stamp is a
`demoted:` token in the line, so the line that comes back is the line that went
in with that token appended — spelled out here rather than left as a `≠`.  When
the stamp was a slot beside the line the fourth conjunct read
`… = e.val.line`, and it was true only because nothing ever wrote the stamp
into the file. -/
theorem readopt_demote_id_mod_stamps (t : Site) (st : Stamp) (e a b : Entity)
    (harch : e.val.archive = none) (hst : e.val.status = .live .free)
    (h : demote t st e = .ok a) (hr : readopt e.val.live a = .ok b) :
    b.val.live = e.val.live ∧
    b.val.archive = e.val.archive ∧
    b.val.status = e.val.status ∧
    b.val.line = Field.setDemoted (e.val.stamps ++ [st]) e.val.line := by
  have hv := demote_roundtrips _ _ _ _ h
  rw [readopt] at hr
  split at hr
  · injection hr with hr
    subst hr
    refine ⟨rfl, by rw [harch], by rw [hst], ?_⟩
    show a.val.line = _
    rw [hv]
  · simp at hr

/-- The round trip is **reachable**: `demote` leaves a `[-]` record, which is
exactly `readopt`'s precondition, so the pair of hypotheses above is satisfied
by every close. -/
theorem readopt_after_demote_succeeds (t : Site) (st : Stamp) (e a : Entity)
    (h : demote t st e = .ok a) :
    readopt e.val.live a = .ok ⟨{ live := e.val.live, archive := none,
                                  status := .live .free, line := a.val.line }, rfl⟩ := by
  have hv := demote_roundtrips _ _ _ _ h
  exact readopt_ok _ a (by rw [hv])

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
  let e0 : Entity := ⟨{ live := ⟨0, 0⟩, archive := none, status := .live .free,
                        line := ⟨[], []⟩ }, rfl⟩
  have h1 : 1 ≤ remainingOf bm (f 1 e0).val.line := hf 1 e0
  have h2 : remainingOf bm (f 1 e0).val.line = remainingOf bm e0.val.line := hr 1 e0
  have h3 : remainingOf bm e0.val.line = 0 := rfl
  omega

/-- The corrected rule.  The exception lives in the **signature**: a close
cannot silently forget to ask whether the user set an estimate since. -/
def demoteEst (bm : Nat) (userSet : Bool) (rec : Nat) (e : Entity) : Entity :=
  match userSet with
  | true  => e
  | false => setEstFoldE (max (remainingOf bm e.val.line) rec) e

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
