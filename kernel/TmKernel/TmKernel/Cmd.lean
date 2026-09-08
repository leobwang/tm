import TmKernel.Plan
/-!
# The command algebra

Every command is one transformation on the plan value.  Each carries a claimed
law with its **subdomain**, and the refutations are theorems too: several of
tm's stated laws are false as written, and a kernel that stayed silent about
that would be repeating the mistake.

The load-bearing fact is `every_transform_preserves_the_invariant` at the
bottom: the id-uniqueness invariant is a theorem about the *type*, so no
command has to preserve it and no command can break it — including commands
nobody has written yet.  That is what "structural" means here, and it is the
difference from a runtime check someone must remember to run.
-/
namespace Tm

inductive KErr
  | occupied          -- the destination file already holds this id's other line
  | noSuchId
  | notDemoted
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

/-- Apply an entity transform at one id.  Both store obligations and the
plan-level obligation are discharged here, once, for every command. -/
def WfPlan.mapAt (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity) :
    Except KErr WfPlan :=
  match h : p.val.store.get i with
  | none   => .error .noSuchId
  | some e =>
    match f e with
    | .error k => .error k
    | .ok e'   =>
      .ok ⟨{ p.val with store := p.val.store.set i e' (by rw [h]; rfl) }, p.property⟩

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
      injection hq with hq
      subst hq
      rw [Store.get_set_self] at he
      injection he with he
      rw [ha, he]

/-- `tm move`. -/
def cmdMove (i : Id) (t : Site) : Transform := (·.mapAt i (moveTo t))
/-- `tm drop`. -/
def cmdDrop (i : Id) : Transform := (·.mapAt i (fun e => .ok (drop e)))
/-- `tm edit ^id est=v`. -/
def cmdSetEst (v : Nat) (i : Id) : Transform := (·.mapAt i (fun e => .ok (setEstE v e)))
/-- `tm demote`. -/
def cmdDemote (i : Id) (t : Site) (per : Nat) : Transform := (·.mapAt i (demote t per))
/-- `tm readopt`. -/
def cmdReadopt (i : Id) (t : Site) : Transform := (·.mapAt i (fun e => .ok (readopt t e)))

/-! ## Resolving a horizon to a file

This is where the derived containment order (`Grain`, `coarsen`) becomes
load-bearing: `move ^id week` names a *grain*, and the file is computed. -/

/-- A document knows which horizon block it is, or `none` for backlog — the
*absence* of a bound, not a coarser grain. -/
structure DocRegion where
  region : Option Region
deriving DecidableEq, Repr, Inhabited

def findDoc (rs : List DocRegion) (target : Option Region) : Option DocIx :=
  let rec go (k : Nat) : List DocRegion → Option DocIx
    | []      => none
    | d :: ds => if d.region = target then some k else go (k + 1) ds
  go 0 rs

/-- `tm move ^id <horizon>` resolves through the derived order. -/
def resolveHorizon (rs : List DocRegion) (hr : HorizonRef) (now : Day) : Except KErr DocIx :=
  match findDoc rs (hr.regionAt now) with
  | some d => .ok d
  | none   => .error .badHorizon

/-- `demote` targets the next coarser grain — one step along the chain, not a
row in a table. -/
def demoteTarget (rs : List DocRegion) (g : Grain) (now : Day) : Except KErr DocIx :=
  resolveHorizon rs (.bounded (demoteGrain g)) now

/-! ## The laws

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
theorem plan_move_into_archive_file_is_rejected (p : WfPlan) (i : Id) (e : Entity) (t r : Site)
    (hget : p.val.store.get i = some e) (h : e.val.archive = some r) (hd : r.doc = t.doc) :
    cmdMove i t p = .error .occupied := by
  unfold cmdMove WfPlan.mapAt
  split
  · rename_i hn; rw [hget] at hn; simp at hn
  · rename_i e' hget'
    rw [hget] at hget'
    injection hget' with hget'
    subst hget'
    rw [move_into_archive_file_is_rejected e t r h hd]

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

/-- **L4 (R).**  `move` is *not* invertible: it assigns a fresh rank in the
destination section, and moving back does not restore the old one.  Therefore
`tm undo` must replay the log, never apply an inverse. -/
theorem move_not_invertible :
    ∃ (e : Entity) (t : Site),
      ((moveTo t e).bind (fun a => moveTo ⟨e.val.live.doc, 0⟩ a)).map Subtype.val ≠ .ok e.val := by
  refine ⟨⟨⟨⟨0, 3⟩, none, .live .free, ⟨[], []⟩, []⟩, rfl⟩, ⟨0, 9⟩, ?_⟩
  simp [moveTo, lift, Except.map, Except.bind]

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

/-! ## The punchline -/

/-- **Every transformation preserves the identity invariant, including ones
nobody has written yet.**

There is no preservation proof here, and there is none to write: two lines of
one id in one file are the same line for *every* `PlanCore`, so a command
cannot produce a counterexample.  That is the structural difference from a
runtime check — `Tree::duplicate_ids` was already correct Rust; what was
missing was anything that ran it on the post-state of every command. -/
theorem every_transform_preserves_the_invariant
    (f : Transform) (p q : WfPlan) (_h : f p = .ok q) :
    ∀ l₁ ∈ q.val.lines, ∀ l₂ ∈ q.val.lines,
      l₁.id = l₂.id → l₁.site.doc = l₂.site.doc → l₁.site = l₂.site :=
  fun l₁ h₁ l₂ h₂ hid hdoc => no_two_lines_of_one_id_in_one_file q.val l₁ l₂ h₁ h₂ hid hdoc

/-- And the same for the count: no plan, reachable or not, has three lines of
one id. -/
theorem every_transform_keeps_lines_le_two
    (f : Transform) (p q : WfPlan) (_h : f p = .ok q) (i : Id) :
    ((q.val.lines).filter (fun l => l.id == i)).length ≤ 2 := lines_per_id_le_two q.val i

end Tm
