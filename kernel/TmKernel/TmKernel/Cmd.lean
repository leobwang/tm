import TmKernel.Fast
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

An earlier version of this module claimed the first bullet for all three, in
a theorem whose command argument was unused.  It is withdrawn.  (The reflow is
deliberate: `check.sh` check 3 reconciles declared theorems against audit lines
with a column-0 `^theorem ` grep, and this prose line used to be counted as a
tenth unaudited declaration -- AGENTS §6.3's documented off-by-one.)
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
      file's line vanishes; keep it and the line the record is leaving does.
      `demote` answers it for any standing tombstone; since README gap 53 the
      close and the verb run `refile`, which merges an open line into its record
      and answers it for a `[-]` record filed again; the close and the verb also
      answer it for an open line whose tombstone is not a `# Demoted` record — a
      stray `[-]` line in an earlier week, which a merge would delete
      (`closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb`). -/
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
  /-- the line's raw bytes contain a tab.  `Text.isSp` is space-only (gap 32),
      so a tab is a *word* character to this kernel while it is whitespace to
      the shipped Rust tokenizer: on a line with a tab before a repeated
      `est:`, `tm edit` writes the first occurrence and the kernel would
      write the second.  An edit routed through two token readings is the S2
      shape, so the edit path refuses such a line loudly instead of shipping
      a wrong write.  Widening `isSp` is a grammar-wide behaviour change and
      stays plan-tier; this refusal is the sanctioned narrow route. -/
  | tabbedLine
  /-- `tm edit ^id <key>=` (unset) of a key the line does not carry: there is
      no token to remove, and reporting success would be the "success
      reported, nothing changed" shape C1 died of. -/
  | keyAbsent
  /-- a keyed `after:` edit whose post-state names an id no item of the plan
      carries (`afterTotal` fails).  Before gap 40's `after` wiring the only
      name a plan-tier edit refusal had was `badHorizon`, which is advice about
      relocation; an edit moves nothing (`nameEditFault`). -/
  | danglingDep
  /-- a keyed `after:` edit whose post-state has a dependency cycle
      (`afterAcyclic` fails, §5.5) — a self-dependency included. -/
  | depCycle
  /-- a close has a line to file (or a wall to carry) and the plan holds no
      document of the kind and region it goes to.  The kernel has regions and
      no path grammar (README gap 10), so it cannot create the file; the host
      must hand it over (Close.lean). -/
  | noTarget
  /-- a close's destination file has no section to receive the line: no
      `# Demoted` for §6.3's week row, or no heading matching the one the line
      stood under for its month row (Close.lean). -/
  | noSection
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

/-! ## D56: `tm edit est=` writes the slot the view reads — the leading one included

`est:` overrides the leading estimate (§4.1), so the key setter `Field.setEst` writes the key,
and `Field.view_set_remaining` holds whatever else the line carried.  On a line with a
**leading** estimate and no `est:` token that leaves **two** estimates on one line: the
leading one, which the day row's estimate cell prints (fork `est_original`), and the key, which
`Core.est` and so the planner read — and `tm check` sees nothing wrong.  W-33's auditor drove it
on the shipped binary (`tm edit ^x3 est=20b` on `- [ ] 2 30b Big migration … ^x3` appended
`est:1200m`), which is AGENTS §5.3's founding bug — *two syntactic slots for one field* — in a
new form (README gap 2572).  The owner's **D56** settles it as the pre-switch fork did (fork
`ItemLine::set_leading_est`): the leading estimate is rewritten **in place, as written**.

So the edit path's one est setter, `Field.setRemaining`, reads the slot first: the `est:` token
if the line carries one, else the leading estimate if the line carries one
(`Field.leadIsTheSlot`), else a new `est:` token.  It carries two renderings of one value — the
leading slot's, as written, and the key's — because the two slots are written differently on
purpose: §3.1's leading estimate is "as written", and the key is the canonical minutes D49
settled (`EditVal.estAt`, which states the one value both denote). -/

namespace Field

/-- The leading estimate's token, rewritten **in place**: phase 1's token — the first, or the
second when the first is a positional ci (`classifyPhase0`) — and only when phase 1 reads it
as an estimate (`classifyPhase1`).  Every other token, and every separator, is kept. -/
def setLeadToks (w : List Char) : List Tok → List Tok
  | []      => []
  | t :: ts =>
    match ciSlot t.word with
    | some _ =>
      (match ts with
       | []      => [t]
       | u :: us => if (estSlot u.word).isSome then t :: ⟨u.sep, w⟩ :: us else t :: u :: us)
    | none => if (estSlot t.word).isSome then ⟨t.sep, w⟩ :: ts else t :: ts

/-- The rewrite on a line.  Only a boxed line has positional slots (`kinds`), so a bare line
is returned as it is. -/
def setLead (w : List Char) (r : RawItem) : RawItem :=
  if r.boxed then ⟨r.indent, r.boxed, setLeadToks w r.toks⟩ else r

/-- **The leading estimate is the slot the view reads**: the line carries no `est:` token, and
phase 1 read a leading estimate.  (`viewRemainingDur` reads `est:` first, else this.) -/
def leadIsTheSlot (r : RawItem) : Bool := !hasKeyTok .est r && (estLeadOf r).isSome

/-- **`tm edit ^id est=`, D56.**  `lead` is written where the leading estimate is the slot — AS TYPED,
the value's own spelling, never the line's old unit (`2h` edited `90m` reads `90m`: D62, gap 2928) — and
`key` everywhere else: the `est:` token, or a new one before the `^id` (`setEst`).  D62: also `tm extend`/`stop`/`done --partial`'s. -/
def setRemaining (lead key : Dur) (r : RawItem) : RawItem :=
  if leadIsTheSlot r then setLead (renderDur lead) r else setEst key r

theorem kEst_classifyWord (w : List Char) : kEst (classifyWord w) = none := by
  unfold classifyWord
  split
  · unfold classifySigil
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · unfold classifyBang; split <;> rfl
          · split <;> rfl
  · split
    · unfold classifyKeyed; split <;> rfl
    · unfold classifyPlain; split <;> rfl

theorem findSome_kEst_phase3 : ∀ ts : List Tok, (classifyPhase3 ts).findSome? kEst = none
  | [] => rfl
  | t :: ts => by
    show (classifyWord t.word :: classifyPhase3 ts).findSome? kEst = none
    rw [findSome_cons_none kEst _ _ (kEst_classifyWord t.word)]
    exact findSome_kEst_phase3 ts

/-- **Past the two positional slots, no word is an estimate.** -/
theorem findSome_kEst_phase2 : ∀ ts : List Tok, (classifyPhase2 ts).findSome? kEst = none
  | [] => rfl
  | t :: ts => by
    unfold classifyPhase2
    split
    · exact findSome_kEst_phase3 _
    · rw [findSome_cons_none kEst _ _ rfl]
      exact findSome_kEst_phase2 ts

/-- A line with no state box has no leading estimate: phase 1 is read only after a box. -/
theorem estLeadOf_bare (r : RawItem) (h : r.boxed = false) : estLeadOf r = none := by
  unfold estLeadOf
  rw [kinds_bare r h]
  exact findSome_kEst_phase2 r.toks

theorem boxed_of_estLeadOf (r : RawItem) (h : (estLeadOf r).isSome = true) : r.boxed = true := by
  cases hb : r.boxed with
  | true => rfl
  | false => rw [estLeadOf_bare r hb] at h; exact absurd h (by simp)

/-- **The leading estimate is rewritten, and read back as the value written.** -/
theorem estLeadOf_setLead (w : List Char) (d : Dur) (r : RawItem)
    (hw : estSlot w = some d) (hc : ciSlot w = none) (h : (estLeadOf r).isSome = true) :
    estLeadOf (setLead w r) = some d := by
  have hb := boxed_of_estLeadOf r h
  unfold estLeadOf at h ⊢
  rw [kinds_boxed r hb] at h
  unfold setLead
  rw [if_pos hb, kinds_boxed { indent := r.indent, boxed := r.boxed, toks := setLeadToks w r.toks } hb]
  show (classifyPhase0 (setLeadToks w r.toks)).findSome? kEst = some d
  generalize r.toks = ts at h ⊢
  cases ts with
  | nil => exact absurd h (by simp [classifyPhase0])
  | cons t rest =>
    cases hct : ciSlot t.word with
    | some c =>
      cases rest with
      | nil =>
        simp only [classifyPhase0, hct] at h
        exact absurd h (by simp [classifyPhase1, kEst])
      | cons u us =>
        cases hu : estSlot u.word with
        | none =>
          simp only [classifyPhase0, hct, classifyPhase1, hu] at h
          rw [findSome_cons_none kEst _ _ rfl, findSome_kEst_phase2] at h
          exact absurd h (by simp)
        | some du =>
          simp only [setLeadToks, hct, hu, Option.isSome_some, if_true, classifyPhase0,
            classifyPhase1, hw]
          rfl
    | none =>
      cases ht : estSlot t.word with
      | none =>
        simp only [classifyPhase0, hct, classifyPhase1, ht] at h
        rw [findSome_kEst_phase2] at h
        exact absurd h (by simp)
      | some dt =>
        simp only [setLeadToks, hct, ht, Option.isSome_some, if_true, classifyPhase0, hc,
          classifyPhase1, hw]
        rfl

/-- **In place**: the rewrite keeps every separator, so the line's spacing does not move. -/
theorem setLeadToks_seps (w : List Char) : ∀ ts : List Tok,
    (setLeadToks w ts).map Tok.sep = ts.map Tok.sep
  | [] => rfl
  | t :: ts => by
    cases hc : ciSlot t.word with
    | some c =>
      cases ts with
      | nil => simp only [setLeadToks, hc]
      | cons u us =>
        cases hu : estSlot u.word with
        | none => simp only [setLeadToks, hc, hu, Option.isSome_none, Bool.false_eq_true, if_false]
        | some du => simp only [setLeadToks, hc, hu, Option.isSome_some, if_true, List.map_cons]
    | none =>
      cases ht : estSlot t.word with
      | none => simp only [setLeadToks, hc, ht, Option.isSome_none, Bool.false_eq_true, if_false]
      | some dt => simp only [setLeadToks, hc, ht, Option.isSome_some, if_true, List.map_cons]

/-- Every token of the rewrite is a token of the line, or carries the written word. -/
theorem mem_setLeadToks (w : List Char) (x : Tok) : ∀ ts : List Tok,
    x ∈ setLeadToks w ts → x ∈ ts ∨ x.word = w
  | [] => fun h => by simp [setLeadToks] at h
  | t :: ts => fun h => by
    cases hc : ciSlot t.word with
    | some c =>
      cases ts with
      | nil => simp only [setLeadToks, hc] at h; exact Or.inl h
      | cons u us =>
        cases hu : estSlot u.word with
        | none =>
          simp only [setLeadToks, hc, hu, Option.isSome_none, Bool.false_eq_true, if_false] at h
          exact Or.inl h
        | some du =>
          simp only [setLeadToks, hc, hu, Option.isSome_some, if_true, List.mem_cons] at h
          rcases h with rfl | rfl | h
          · exact Or.inl (by simp)
          · exact Or.inr rfl
          · exact Or.inl (by simp [h])
    | none =>
      cases ht : estSlot t.word with
      | none =>
        simp only [setLeadToks, hc, ht, Option.isSome_none, Bool.false_eq_true, if_false] at h
        exact Or.inl h
      | some dt =>
        simp only [setLeadToks, hc, ht, Option.isSome_some, if_true, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr rfl
        · exact Or.inl (by simp [h])

/-- A duration is written with a digit first… -/
theorem renderDur_head (d : Dur) : headSat isDigitC (renderDur d) = true := by
  cases d with
  | simple n u =>
    show headSat isDigitC (digitsOf n ++ [DurUnit.char u]) = true
    cases hn : digitsOf n with
    | nil => exact absurd hn (digitsOf_ne_nil n)
    | cons a t => exact digitsOf_isDigitC n a (by rw [hn]; simp)
  | hm h m =>
    show headSat isDigitC (digitsOf h ++ 'h' :: (digitsOf m ++ ['m'])) = true
    cases hn : digitsOf h with
    | nil => exact absurd hn (digitsOf_ne_nil h)
    | cons a t => exact digitsOf_isDigitC h a (by rw [hn]; simp)

/-- …so it is never a `key:` word… -/
theorem keyOf_renderDur (d : Dur) : keyOf (renderDur d) = none := by
  unfold keyOf
  rw [keyPrefix_none_of (headSat_false_of digit_not_key _ (renderDur_head d))]
  rfl

/-- …and never an `^id` word; nor is any word a leading estimate is read from. -/
theorem isIdWord_of_digit_head {w : List Char} (h : headSat isDigitC w = true) :
    isIdWord w = false := by
  cases w with
  | nil => exact absurd h (by simp [headSat])
  | cons a t =>
    have ha : isDigitC a = true := h
    have hne : a ≠ '^' := by
      intro hc; rw [hc] at ha; exact absurd ha (by decide)
    simp [isIdWord, hne]

theorem isIdWord_renderDur (d : Dur) : isIdWord (renderDur d) = false :=
  isIdWord_of_digit_head (renderDur_head d)

theorem isIdWord_of_estSlot {w : List Char} {d : Dur} (h : estSlot w = some d) :
    isIdWord w = false :=
  isIdWord_of_digit_head (estSlot_head h)

/-- A line none of whose tokens is a `k:` token has no `k:` value. -/
theorem lookupKey_none_of_no_keyTok (k : Key) (r : RawItem) (h : hasKeyTok k r = false) :
    lookupKey k r = none := by
  unfold lookupKey
  rw [keyPairs_raw]
  unfold hasKeyTok at h
  generalize r.toks = ts at h ⊢
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    rw [lookup_cons_skip k t ts h.1]
    exact ih h.2

/-- The rewrite adds no `k:` token when the written word is not one. -/
theorem hasKeyTok_setLead (k : Key) (w : List Char) (r : RawItem) (hw : keyOf w = none)
    (h : hasKeyTok k r = false) : hasKeyTok k (setLead w r) = false := by
  unfold setLead
  split
  · unfold hasKeyTok at h ⊢
    show (setLeadToks w r.toks).any (isKeyTok k) = false
    cases hany : (setLeadToks w r.toks).any (isKeyTok k) with
    | false => rfl
    | true =>
      obtain ⟨x, hx, hk⟩ := List.any_eq_true.1 hany
      rcases mem_setLeadToks w x r.toks hx with hm | hm
      · have := List.any_eq_true.2 ⟨x, hm, hk⟩
        rw [h] at this
        exact absurd this (by simp)
      · unfold isKeyTok at hk
        rw [hm, hw] at hk
        exact absurd hk (by simp)
  · exact h

/-- **D56's law: the edit path writes the slot the view reads, the leading one included.**  On
a line whose leading estimate is the slot, `Core.est`'s view reads the value written there; on
every other line, the value the `est:` token carries — which is `view_set_remaining`,
unchanged. -/
theorem view_set_remaining_slot (lead key : Dur) (r : RawItem) (hl : lead.noDays = true)
    (hk : key.noDays = true) :
    viewRemainingDur (setRemaining lead key r) = some (if leadIsTheSlot r then lead else key) := by
  unfold setRemaining
  by_cases hs : leadIsTheSlot r = true
  · rw [if_pos hs, if_pos hs]
    have hs' := hs
    unfold leadIsTheSlot at hs'
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs'
    unfold viewRemainingDur viewEstKey
    rw [lookupKey_none_of_no_keyTok .est _
      (hasKeyTok_setLead .est _ r (keyOf_renderDur lead) hs'.1)]
    exact estLeadOf_setLead _ lead r (estSlot_renderDur lead hl) (ciSlot_renderDur lead) hs'.2
  · rw [if_neg hs, if_neg hs]
    exact view_set_remaining key r hk

/-- **One estimate per line**: where the leading estimate is the slot, no `est:` token is
written — the defect D56 closes was exactly that token, beside the leading one. -/
theorem setRemaining_writes_no_key_over_a_leading_estimate (lead key : Dur) (r : RawItem)
    (hs : leadIsTheSlot r = true) : hasKeyTok .est (setRemaining lead key r) = false := by
  unfold setRemaining
  rw [if_pos hs]
  unfold leadIsTheSlot at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
  exact hasKeyTok_setLead .est _ r (keyOf_renderDur lead) hs.1

@[simp] theorem setRemaining_boxed (lead key : Dur) (r : RawItem) :
    (setRemaining lead key r).boxed = r.boxed := by
  unfold setRemaining setLead
  split
  · split <;> rfl
  · exact setKey_boxed _ _ _

/-- `toksWf` does not care which word a token carries, only that it is one word. -/
theorem toksWf_head_word (t : Tok) (w : List Char) (hw : wordWf w = true) (ts : List Tok)
    (h : toksWf (t :: ts) = true) : toksWf (⟨t.sep, w⟩ :: ts) = true := by
  have ht : t.wf = true := by
    cases ts with
    | nil => simpa [toksWf] using h
    | cons u r => simp only [toksWf, Bool.and_eq_true] at h; exact h.1.1
  obtain ⟨hne, hns⟩ := (wordWf_iff w).1 hw
  have ht' : (⟨t.sep, w⟩ : Tok).wf = true := (tok_wf_iff _).2 ⟨((tok_wf_iff t).1 ht).1, hne, hns⟩
  cases ts with
  | nil => simpa [toksWf] using ht'
  | cons u r =>
    simp only [toksWf, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ht', h.1.2⟩, h.2⟩

theorem toksWf_setLeadToks (w : List Char) (hw : wordWf w = true) : ∀ ts : List Tok,
    toksWf ts = true → toksWf (setLeadToks w ts) = true
  | [] => fun h => h
  | t :: ts => fun h => by
    cases hc : ciSlot t.word with
    | some c =>
      cases ts with
      | nil => simp only [setLeadToks, hc]; exact h
      | cons u us =>
        cases hu : estSlot u.word with
        | none =>
          simp only [setLeadToks, hc, hu, Option.isSome_none, Bool.false_eq_true, if_false]
          exact h
        | some du =>
          simp only [setLeadToks, hc, hu, Option.isSome_some, if_true]
          simp only [toksWf, Bool.and_eq_true] at h ⊢
          exact ⟨⟨h.1.1, h.1.2⟩, toksWf_head_word u w hw us h.2⟩
    | none =>
      cases ht : estSlot t.word with
      | none =>
        simp only [setLeadToks, hc, ht, Option.isSome_none, Bool.false_eq_true, if_false]
        exact h
      | some dt =>
        simp only [setLeadToks, hc, ht, Option.isSome_some, if_true]
        exact toksWf_head_word t w hw ts h

theorem idWords_setLeadToks (w : List Char) (hw : isIdWord w = false) : ∀ ts : List Tok,
    ((setLeadToks w ts).filter (fun t => isIdWord t.word)).map Tok.word
      = (ts.filter (fun t => isIdWord t.word)).map Tok.word
  | [] => rfl
  | t :: ts => by
    cases hc : ciSlot t.word with
    | some c =>
      cases ts with
      | nil => simp only [setLeadToks, hc]
      | cons u us =>
        cases hu : estSlot u.word with
        | none => simp only [setLeadToks, hc, hu, Option.isSome_none, Bool.false_eq_true, if_false]
        | some du =>
          simp only [setLeadToks, hc, hu, Option.isSome_some, if_true]
          simp [List.filter_cons, hw, isIdWord_of_estSlot hu]
    | none =>
      cases ht : estSlot t.word with
      | none => simp only [setLeadToks, hc, ht, Option.isSome_none, Bool.false_eq_true, if_false]
      | some dt =>
        simp only [setLeadToks, hc, ht, Option.isSome_some, if_true]
        simp [hw, isIdWord_of_estSlot ht]

/-- **Whatever the leading-slot rewrite writes, the kernel reads back.** -/
theorem setLead_canonical (i : Id) (w : List Char) (r : RawItem) (hw : wordWf w = true)
    (hid : isIdWord w = false) (h : CanonicalItem i r = true) :
    CanonicalItem i (setLead w r) = true := by
  obtain ⟨hb, hind, htw, hids⟩ := (canonical_iff i r).1 h
  unfold setLead
  rw [if_pos hb]
  refine (canonical_iff i _).2 ⟨hb, hind, toksWf_setLeadToks w hw r.toks htw, ?_⟩
  unfold idToks at hids ⊢
  rw [idWords_setLeadToks w hid r.toks]
  exact hids

theorem setRemaining_canonical (i : Id) (lead key : Dur) (r : RawItem)
    (h : CanonicalItem i r = true) : CanonicalItem i (setRemaining lead key r) = true := by
  unfold setRemaining
  split
  · exact setLead_canonical i _ r (wordWf_renderDur lead) (isIdWord_renderDur lead) h
  · exact setKey_canonical i .est _ r (wordWf_renderDur key) h

/-- **The payoff**, as `setKey_line_reparses` is for the key setters: whatever `tm edit ^id
est=` writes, on either slot, the kernel parses back to the same item. -/
theorem setRemaining_line_reparses (i : Id) (g : Glyph) (lead key : Dur) (r : RawItem)
    (h : CanonicalItem i r = true) :
    parseItem (serializeItem i g (setRemaining lead key r))
      = .ok (some i, g, setRemaining lead key r) :=
  parse_serialize i g _ (setRemaining_canonical i lead key r h)

/-! ### The three lines D56 is about, computed

`- [ ] 2 30b Big migration ^x3` is W-33's auditor's line (its `due:` dropped); the other two are
the lines D56 leaves as they were — one with no estimate, one carrying `est:`.  The value is
`20b` as written and 1,200 canonical minutes at a 60-minute block.  The lines are written out in
each statement rather than named by a `def`: a fixture here would be code the export never runs
(check 12). -/

/-- **The auditor's line carries ONE estimate, `20b`, rewritten in place**, and the view reads
twenty blocks — 1,200 minutes at a 60-minute block, the number the planner uses. -/
theorem the_leading_estimate_is_rewritten_in_place :
    let r : RawItem := ⟨[], true, [⟨[' '], ['2']⟩, ⟨[' '], ['3','0','b']⟩, ⟨[' '], ['B','i','g']⟩,
      ⟨[' '], ['m','i','g','r','a','t','i','o','n']⟩, ⟨[' '], ['^','x','3']⟩]⟩
    leadIsTheSlot r = true ∧
    (setRemaining (.simple 20 .blocks) (.simple 1200 .minutes) r).toks.map Tok.word
      = [['2'], ['2','0','b'], ['B','i','g'], ['m','i','g','r','a','t','i','o','n'],
         ['^','x','3']] ∧
    (setRemaining (.simple 20 .blocks) (.simple 1200 .minutes) r).toks.map Tok.sep
      = r.toks.map Tok.sep ∧
    hasKeyTok .est (setRemaining (.simple 20 .blocks) (.simple 1200 .minutes) r) = false ∧
    (viewRemainingDur (setRemaining (.simple 20 .blocks) (.simple 1200 .minutes) r)).map
      (Dur.minutes 60) = some 1200 := by
  decide

/-- **…and the two lines D56 leaves as they were**: no estimate gains an `est:` token in
canonical minutes before the `^id`; an `est:` token is rewritten, and the leading `30b` — §3.1's
estimate as written — is not touched. -/
theorem a_line_without_a_leading_estimate_gets_the_key :
    let none_ : RawItem := ⟨[], true, [⟨[' '], ['2']⟩, ⟨[' '], ['B','i','g']⟩,
      ⟨[' '], ['m','i','g','r','a','t','i','o','n']⟩, ⟨[' '], ['^','x','3']⟩]⟩
    let key_ : RawItem := ⟨[], true, [⟨[' '], ['2']⟩, ⟨[' '], ['3','0','b']⟩,
      ⟨[' '], ['B','i','g']⟩, ⟨[' '], ['m','i','g','r','a','t','i','o','n']⟩,
      ⟨[' '], ['e','s','t',':','5','b']⟩, ⟨[' '], ['^','x','3']⟩]⟩
    leadIsTheSlot none_ = false ∧ leadIsTheSlot key_ = false ∧
    (setRemaining (.simple 20 .blocks) (.simple 1200 .minutes) none_).toks.map Tok.word
      = [['2'], ['B','i','g'], ['m','i','g','r','a','t','i','o','n'],
         ['e','s','t',':','1','2','0','0','m'], ['^','x','3']] ∧
    (setRemaining (.simple 20 .blocks) (.simple 1200 .minutes) key_).toks.map Tok.word
      = [['2'], ['3','0','b'], ['B','i','g'], ['m','i','g','r','a','t','i','o','n'],
         ['e','s','t',':','1','2','0','0','m'], ['^','x','3']] := by
  decide

end Field

/-- `tm edit ^id est=v` at the entity, `v` in minutes.  This is the **field** setter the edit
path writes through — `Field.setRemaining`, D56's slot-reading setter, since W-35; the key
setter `Field.setEst` over `setKey` until then — the same reader pair `Core.est` consumes, so
gap 4's two readers stay collapsed.  With one value in minutes the two renderings are the same
`Nm`: on a line whose leading estimate is the slot it is rewritten in place, elsewhere the
`est:` token is written, byte-identical to the stage one's token
(`the_two_est_setters_write_the_same_token`).  The request path reaches the same setter through
`cmdSetEst` → `setVal`; this entity form is what the normalisation lemmas are stated over. -/
def setEstE (v : Nat) (e : Entity) : Entity :=
  ⟨{ e.val with
      line := Field.setRemaining (Dur.simple v DurUnit.minutes) (Dur.simple v DurUnit.minutes)
        e.val.line }, e.property⟩

/-- **Gap 4, closed: the command path writes what the field path reads.**
The `est` request lands on `setEstE`; `Core.est` is
`Field.viewRemainingDur`; `Field.view_set_remaining_slot` says the second reads the
first verbatim, with no hypothesis on the entity's other bytes — on either slot, because
the one value is both renderings.  **Re-proved at W-35 (D5, D56), its statement unchanged.** -/
theorem the_command_path_writes_what_the_field_path_reads (v : Nat) (e : Entity) :
    (setEstE v e).val.est = some (Dur.simple v DurUnit.minutes) := by
  have h := Field.view_set_remaining_slot (Dur.simple v DurUnit.minutes)
    (Dur.simple v DurUnit.minutes) e.val.line rfl rfl
  rw [ite_self] at h
  exact h

/-- **The entity setter rewrites the leading estimate in place** — `1200m`, the one value in
minutes, where the `30b` stood, and no `est:` token beside it (D56's line, open in document 0,
no tombstone). -/
theorem setEstE_rewrites_the_leading_estimate :
    let r : RawItem := ⟨[], true, [⟨[' '], ['2']⟩, ⟨[' '], ['3','0','b']⟩, ⟨[' '], ['B','i','g']⟩,
      ⟨[' '], ['m','i','g','r','a','t','i','o','n']⟩, ⟨[' '], ['^','x','3']⟩]⟩
    let e : Entity :=
      ⟨{ live := ⟨0, 0⟩, archive := none, status := .live .free, line := r }, by decide⟩
    (setEstE 1200 e).val.line.toks.map Tok.word
      = [['2'], ['1','2','0','0','m'], ['B','i','g'], ['m','i','g','r','a','t','i','o','n'],
         ['^','x','3']] := by
  decide

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
  | mk live archive status line =>
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

/-! ## The keyed edit — §4.1's other fields through gap 4's collapsed path

`tm edit ^id <key>=<value>`, generalised from the single `est` shape.  The
discipline is §5.3's one-reader rule, in both directions:

* **read**: the value arriving on the wire is parsed by the *same* `Field`
  value parser the loader's view for that key calls — `editValOf` below names
  one parser per key and every one of them is the view's own.  There is no
  boundary re-encoding of any value grammar.
* **write**: the accepted value goes through the *same* per-key setter whose
  `view ∘ set = id` proof stands in Line.lean (`setDur`, `setPref`, … — all
  of them `setKey` under one name, R11's condition).  What lands on the line
  is the field's canonical rendering of the parsed value, so re-loading reads
  back exactly what the command wrote.

Seventeen of the eighteen `Field.Key`s are wired.  The edit widening wired
nine: `est`, `dur`, `buffer`, `pref`, `on-miss`, `after-done`, `min`, `max`
(spelled `cap` or `max` on the wire, written as `max:` — `set_max_writes_max`),
`ci`.  Stage 3's step 5 wired eight more — `due`, `at`, `win`, `every`,
`on-event`, `loc`, `waiting`, `after` — once Line.lean's `parse ⇒ wf` bridges
existed for the hypotheses their `view_set_*` proofs carry (README gap 40 and
its step-5 successor paragraph).  The eighteenth, `demoted`, is lifecycle
state that `demote`/`readopt` own and `edit` must not forge.  R10: the bounded value
classes crossing here — day-free durations, `Fin 6`, and the eight wf-bounded
subtypes (`WfMoment` … `WfDeps`, and `WordLoc`) — go through the smart
constructors their decoders use (`ndDur?`, `parseCi`, `guardWf`). -/

/-- Gap 32's guard: a tab anywhere in the raw bytes the line renders from —
indent, any separator, any word.  `toksWf` keeps separators space-only, so on
a loaded line a tab can only hide inside a word, but the guard checks all
three so it is a fact about the bytes and not about a parse. -/
def lineHasTab (r : RawItem) : Bool :=
  r.indent.any (· == '\t') ||
    r.toks.any (fun t => t.sep.any (· == '\t') || t.word.any (· == '\t'))

/-- A day-free duration — `est:`/`dur:` refuse `3d`.  The bound lives in the
type so a days-carrying `Dur` cannot reach `setEst`/`setDur` from the wire at
all (R10); `Negative.lean` CHEAT 46 is the door staying shut. -/
abbrev NdDur := { d : Dur // d.noDays = true }

/-- R10's smart constructor for `NdDur`, and it is the loader's own grammar:
`ndDur?_is_parseDurND` says accepting and bounding here *is* `parseDurND`. -/
def ndDur? (w : List Char) : Option NdDur :=
  (Field.parseDur w).bind (fun d => if h : d.noDays = true then some ⟨d, h⟩ else none)

theorem ndDur?_is_parseDurND (w : List Char) :
    (ndDur? w).map Subtype.val = Field.parseDurND w := by
  unfold ndDur? Field.parseDurND
  cases Field.parseDur w with
  | none => rfl
  | some d =>
      simp only [Option.bind_some]
      by_cases h : d.noDays = true <;> simp [h]

/-- R10's smart constructor for every wf-bounded value class the widened edit
carries: the parser's answer, kept only with its wf proof.  The bridges in
Line.lean (`parseDate_dayWf`, `parseMoment_wf`, …) are what make the guard
refuse nothing the parser accepted — `guardWf_isSome` — except where a bridge
is honestly false (`at:`/`win:`'s year-9999 rollover). -/
def guardWf {α : Type} (p : α → Bool) (o : Option α) : Option { a : α // p a = true } :=
  o.bind (fun a => if h : p a = true then some ⟨a, h⟩ else none)

theorem guardWf_isSome {α : Type} (p : α → Bool) (o : Option α)
    (hb : ∀ a, o = some a → p a = true) : (guardWf p o).isSome = o.isSome := by
  unfold guardWf
  cases ho : o with
  | none => rfl
  | some a =>
      simp only [Option.bind_some]
      rw [dif_pos (hb a ho)]
      rfl

theorem guardWf_none_iff {α : Type} (p : α → Bool) (o : Option α) :
    guardWf p o = none ↔ ∀ a, o = some a → p a = false := by
  unfold guardWf
  cases o with
  | none => simp
  | some a =>
      by_cases h : p a = true
      · simp [h]
      · simp only [Bool.not_eq_true] at h; simp [h]

/-- A `loc:` name is free text to `parseLoc`, so unlike every other value it
could carry a byte that is not a word: a space would split the token when the
line is read back, a newline would split the line, and a tab is gap 32's
unreadable separator.  The edit path writes `loc:` only for a value made of
characters that are none of those — no space and no C0 control byte.  A
loaded line's `loc:` word can never hold a space or a newline, so this narrows
the loader's reading only by the control bytes, which are recorded (gap 40's
successor paragraph). -/
def locWordOk (w : List Char) : Bool := w.all (fun c => c != ' ' && decide (32 ≤ c.toNat))

/-- The bound a `loc:` value carries onto the line: the enum's own wf, and a
rendering the tokenizer reads back as one word. -/
def locOk (c : Field.Loc) : Bool := c.wf && locWordOk (Field.renderLoc c)

abbrev WfMoment   := { m : Field.Moment // m.wf = true }
abbrev WfInterval := { se : Field.DT × Field.DT // Field.intervalWf se.1 se.2 = true }
abbrev WfWindow   := { g : Field.WindowRange // Field.windowWf g = true }
abbrev WfRule     := { u : Field.Rule // u.wf = true }
abbrev WfOnEvent  := { e : Field.OnEvent // e.wf = true }
abbrev WordLoc    := { c : Field.Loc // locOk c = true }
abbrev WfDay      := { n : Nat // Field.dayWf n = true }
abbrev WfDeps     := { ds : List Field.Dep // Field.depsWf ds = true }

/-- One wire value, already parsed and bounded.  One constructor per wired
key, carrying the same type the loader's view for that key produces. -/
inductive EditVal
  /-- `est=`: the value as the leading slot writes it (as written, D56) and as an `est:` token
      writes it — two renderings of one value (`EditVal.estAt` says which). -/
  | est       (lead key : NdDur)
  | dur       (d : NdDur)
  | buffer    (d : Dur)
  | pref      (p : Field.Pref)
  | onMiss    (m : Field.OnMiss)
  | afterDone (a : Field.AfterDone)
  | floor     (q : Field.Rate)
  | cap       (q : Field.Rate)
  | ci        (c : Fin 6)
  | due       (m : WfMoment)
  | interval  (se : WfInterval)
  | window    (g : WfWindow)
  | every     (u : WfRule)
  | onEvent   (e : WfOnEvent)
  | loc       (c : WordLoc)
  | waiting   (n : WfDay)
  | after     (ds : WfDeps)
deriving DecidableEq

/-- The key each value writes. -/
def EditVal.key : EditVal → Field.Key
  | .est _ _ => .est | .dur _ => .dur | .buffer _ => .buffer
  | .pref _ => .pref | .onMiss _ => .onMiss | .afterDone _ => .afterDone
  | .floor _ => .floor | .cap _ => .cap | .ci _ => .ci
  | .due _ => .due | .interval _ => .interval | .window _ => .window
  | .every _ => .every | .onEvent _ => .onEvent | .loc _ => .loc
  | .waiting _ => .waiting | .after _ => .after

/-- The token body the setter writes: the field's own renderer, per key. -/
def EditVal.rendered : EditVal → List Char
  | .est _ key => Field.renderDur key.val
  | .dur d => Field.renderDur d.val
  | .buffer d => Field.renderDur d
  | .pref p => Field.renderPref p
  | .onMiss m => Field.renderOnMiss m
  | .afterDone a => Field.renderAfterDone a
  | .floor q => Field.renderRate q
  | .cap q => Field.renderRate q
  | .ci c => Field.renderCi c
  | .due m => Field.renderMoment m.val
  | .interval se => Field.renderInterval se.val.1 se.val.2
  | .window g => Field.renderWindow g.val
  | .every u => Field.renderRule u.val
  | .onEvent e => Field.renderOnEvent e.val
  | .loc c => Field.renderLoc c.val
  | .waiting n => Field.renderDate n.val
  | .after ds => Field.renderDeps ds.val

/-- One write path: every branch is a field setter that carries its `view ∘ set = id` proof,
and nothing else is exported as a setter (R11).  Sixteen are Line.lean's key setters; the est
branch is `Field.setRemaining` (above, D56), whose law is `Field.view_set_remaining_slot`. -/
def setVal : EditVal → RawItem → RawItem
  | .est lead key, r => Field.setRemaining lead.val key.val r
  | .dur d, r => Field.setDur d.val r
  | .buffer d, r => Field.setBuffer d r
  | .pref p, r => Field.setPref p r
  | .onMiss m, r => Field.setOnMiss m r
  | .afterDone a, r => Field.setAfterDone a r
  | .floor q, r => Field.setMin q r
  | .cap q, r => Field.setMax q r
  | .ci c, r => Field.setCi c r
  | .due m, r => Field.setDue m.val r
  | .interval se, r => Field.setAt se.val.1 se.val.2 r
  | .window g, r => Field.setWin g.val r
  | .every u, r => Field.setEvery u.val r
  | .onEvent e, r => Field.setOnEvent e.val r
  | .loc c, r => Field.setLoc c.val r
  | .waiting n, r => Field.setWaiting n.val r
  | .after ds, r => Field.setAfter ds.val r

/-- **An edit never adds or removes a state box** — every arm is `setKey`.
`Plan.boxesWf` therefore costs the edit path nothing. -/
@[simp] theorem setVal_boxed (v : EditVal) (r : RawItem) : (setVal v r).boxed = r.boxed := by
  cases v <;> first | exact Field.setRemaining_boxed _ _ _ | exact Field.setKey_boxed _ _ _

/-- **setVal_writes_the_token_the_loader_reads is REFUTED** (W-35, the owner's D56; AGENTS §3.1
item 3).  It said that whatever the edit writes, the key's own token lands and reads back — for
every line.  On a line whose leading estimate is the slot that WAS the hole: the est edit
appended an `est:` token beside the leading estimate, two estimates on one line (README gap
2572).  At D56's own line the edit now writes no `est:` token at all. -/
theorem setVal_writes_the_token_the_loader_reads_is_refuted :
    ¬ ∀ (v : EditVal) (r : RawItem), Field.lookupKey v.key (setVal v r) = some v.rendered := by
  intro h
  exact absurd (h (.est ⟨.simple 20 .blocks, rfl⟩ ⟨.simple 1200 .minutes, rfl⟩)
    ⟨[], true, [⟨[' '], ['2']⟩, ⟨[' '], ['3','0','b']⟩, ⟨[' '], ['B','i','g']⟩,
      ⟨[' '], ['m','i','g','r','a','t','i','o','n']⟩, ⟨[' '], ['^','x','3']⟩]⟩) (by decide)

/-- **The law, on its subdomain, named** (§3.1 item 4): every edit but the est edit of a line
whose leading estimate is the slot lands its own key's token, read back as the rendered value —
`lookupKey_setKey`, once, for all seventeen.  The excluded case is the one D56 decided, and
`setVal_est_rewrites_the_leading_estimate` is what happens there. -/
theorem setVal_writes_the_token_the_loader_reads_unless_it_rewrites_the_leading_estimate
    (v : EditVal) (r : RawItem) (h : (v.key == .est && Field.leadIsTheSlot r) = false) :
    Field.lookupKey v.key (setVal v r) = some v.rendered := by
  cases v with
  | est lead key =>
    have hs : Field.leadIsTheSlot r = false := by simpa [EditVal.key] using h
    show Field.lookupKey .est (Field.setRemaining lead.val key.val r) = _
    unfold Field.setRemaining
    rw [if_neg (by simp [hs])]
    exact Field.lookupKey_setKey _ _ _
  | _ => exact Field.lookupKey_setKey _ _ _

/-- **…and the excluded case**: where the leading estimate is the slot, the est edit rewrites
it — read back as the value as written — and writes no `est:` token. -/
theorem setVal_est_rewrites_the_leading_estimate (lead key : NdDur) (r : RawItem)
    (h : Field.leadIsTheSlot r = true) :
    Field.estLeadOf (setVal (.est lead key) r) = some lead.val ∧
      Field.hasKeyTok .est (setVal (.est lead key) r) = false := by
  refine ⟨?_, Field.setRemaining_writes_no_key_over_a_leading_estimate _ _ r h⟩
  show Field.estLeadOf (Field.setRemaining lead.val key.val r) = _
  unfold Field.setRemaining
  rw [if_pos h]
  have h' := h
  unfold Field.leadIsTheSlot at h'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h'
  exact Field.estLeadOf_setLead _ lead.val r (Field.estSlot_renderDur lead.val lead.property)
    (Field.ciSlot_renderDur lead.val) h'.2

/-- **D56's est edit of a value as written, at a block length** — the one the host sends
(`{"op":"est","value":…,"blockMin":…}`, `Boundary.parseCmd`): the leading slot writes the
value as written (`20b`), and an `est:` token its canonical minutes at that block length
(`est:1200m`), the bytes the `min` form always wrote — D49's settled rendering, unchanged. -/
def EditVal.estAt (d : NdDur) (bm : Nat) : EditVal :=
  .est d ⟨.simple (d.val.minutes bm) .minutes, rfl⟩

/-- Which keys the wire can edit today.  `editValOf` is defined on exactly
these (`editValOf_refuses_unwired_keys`); the one key left out, `demoted`, is
excluded by policy (README gap 40). -/
def keyEditable : Field.Key → Bool
  | .est | .dur | .buffer | .pref | .onMiss | .afterDone | .floor | .cap | .ci => true
  | .due | .interval | .window | .every | .onEvent | .loc | .waiting | .after => true
  | _ => false

/-- An unset can only name a key the edit path is wired for; the proof rides
in the type, so `unsetKey .demoted` cannot be reached from the wire at all
(`Negative.lean` CHEAT 45). -/
abbrev EditKey := { k : Field.Key // keyEditable k = true }

/-- **The one value-grammar table (§5.3).**  Each branch is the parser the
loader's view for that key binds — `viewDur` is `parseDurND`, `viewPref` is
`parsePref`, and so on — so a value accepted here is a value the loader reads,
and a value the loader would refuse never reaches a setter. -/
def editValOf : Field.Key → List Char → Option EditVal
  | .est, w => (ndDur? w).map (fun d => .est d d)
  | .dur, w => (ndDur? w).map .dur
  | .buffer, w => (Field.parseDur w).map .buffer
  | .pref, w => (Field.parsePref w).map .pref
  | .onMiss, w => (Field.parseOnMiss w).map .onMiss
  | .afterDone, w => (Field.parseAfterDone w).map .afterDone
  | .floor, w => (Field.parseRate w).map .floor
  | .cap, w => (Field.parseRate w).map .cap
  | .ci, w => (Field.parseCi w).map .ci
  | .due, w => (guardWf Field.Moment.wf (Field.parseMoment w)).map .due
  | .interval, w =>
      (guardWf (fun se => Field.intervalWf se.1 se.2) (Field.parseInterval w)).map .interval
  | .window, w => (guardWf Field.windowWf (Field.parseWindow w)).map .window
  | .every, w => (guardWf Field.Rule.wf (Field.parseRule w)).map .every
  | .onEvent, w => (guardWf Field.OnEvent.wf (Field.parseOnEvent w)).map .onEvent
  | .loc, w => (guardWf locOk (Field.parseLoc w)).map .loc
  | .waiting, w => (guardWf Field.dayWf (Field.parseDate w)).map .waiting
  | .after, w => (guardWf Field.depsWf (Field.parseDeps w)).map .after
  | _, _ => none

/-- The table and the exposure predicate agree, downward: a key outside the
wired nine parses nothing, whatever the bytes. -/
theorem editValOf_refuses_unwired_keys (k : Field.Key) (w : List Char)
    (h : keyEditable k = false) : editValOf k w = none := by
  cases k <;> first | rfl | exact absurd h (by decide)

/-- …and upward: the exposure is not vacuous — each wired key accepts its
§4.1 spec value.  (`cap` is parsed under its written spelling `max`;
`Key.ofName?` maps both spellings to `.cap`.) -/
theorem the_nine_wired_keys_accept_their_spec_values :
    ((editValOf .est "1b".toList).isSome &&
     (editValOf .dur "45m".toList).isSome &&
     (editValOf .buffer "3d".toList).isSome &&
     (editValOf .pref "wake+2h".toList).isSome &&
     (editValOf .onMiss "persist".toList).isSome &&
     (editValOf .afterDone "2d~1d".toList).isSome &&
     (editValOf .floor "2b/w".toList).isSome &&
     (editValOf .cap "6b/w".toList).isSome &&
     (editValOf .ci "3".toList).isSome) = true := by decide

theorem key_of_map {α : Type} {f : α → EditVal} {k : Field.Key} {o : Option α} {v : EditVal}
    (h : o.map f = some v) (hf : ∀ x, (f x).key = k) : v.key = k := by
  cases o with
  | none => exact absurd h (by simp)
  | some x =>
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact hf x

/-- The table never answers for a different key than it was asked — the
"one setter out of a family writing the wrong slot" shape (C1) cannot hide in
the dispatch table either. -/
theorem editValOf_key (k : Field.Key) (w : List Char) (v : EditVal)
    (h : editValOf k w = some v) : v.key = k := by
  cases k <;> simp only [editValOf] at h <;>
    first
      | exact key_of_map h (fun _ => rfl)
      | exact absurd h (by simp)

/-! ### Gap 40's bridges, at the table

The eight keys wired in stage 3's step 5 each go through `guardWf`, and each
gets the theorem that the guard is not a second grammar: what `editValOf`
refuses is what the loader's parser refuses — exactly, for `due`, `every`,
`on-event`, `waiting` and `after`; up to the word bound for `loc`; and up to
the one stated rollover for `at` and `win`. -/

theorem editValOf_due_refuses_only_what_parseMoment_refuses (w : List Char) :
    (editValOf .due w).isSome = (Field.parseMoment w).isSome := by
  show ((guardWf _ _).map _).isSome = _
  rw [Option.isSome_map, guardWf_isSome _ _ (fun _ h => Field.parseMoment_wf h)]

theorem editValOf_every_refuses_only_what_parseRule_refuses (w : List Char) :
    (editValOf .every w).isSome = (Field.parseRule w).isSome := by
  show ((guardWf _ _).map _).isSome = _
  rw [Option.isSome_map, guardWf_isSome _ _ (fun _ h => Field.parseRule_wf h)]

theorem editValOf_onEvent_refuses_only_what_parseOnEvent_refuses (w : List Char) :
    (editValOf .onEvent w).isSome = (Field.parseOnEvent w).isSome := by
  show ((guardWf _ _).map _).isSome = _
  rw [Option.isSome_map, guardWf_isSome _ _ (fun _ h => Field.parseOnEvent_wf h)]

theorem editValOf_after_refuses_only_what_parseDeps_refuses (w : List Char) :
    (editValOf .after w).isSome = (Field.parseDeps w).isSome := by
  show ((guardWf _ _).map _).isSome = _
  rw [Option.isSome_map, guardWf_isSome _ _ (fun _ h => Field.parseDeps_wf h)]

theorem editValOf_waiting_refuses_only_what_parseDate_refuses (w : List Char) :
    (editValOf .waiting w).isSome = (Field.parseDate w).isSome := by
  show ((guardWf _ _).map _).isSome = _
  rw [Option.isSome_map, guardWf_isSome _ _ (fun _ h => Field.parseDate_dayWf h)]

/-- `parseLoc` hands back the word it read: the enum's four spellings are
exactly themselves, and a name is the word. -/
theorem renderLoc_parseLoc {w : List Char} {c : Field.Loc} (h : Field.parseLoc w = some c) :
    Field.renderLoc c = w := by
  unfold Field.parseLoc at h
  split at h
  · simp at h
  split at h
  · rename_i hw; simp only [Option.some.injEq] at h; rw [← h, hw]; rfl
  split at h
  · rename_i hw; simp only [Option.some.injEq] at h; rw [← h, hw]; rfl
  split at h
  · rename_i hw; simp only [Option.some.injEq] at h; rw [← h, hw]; rfl
  split at h
  · rename_i hw; simp only [Option.some.injEq] at h; rw [← h, hw]; rfl
  simp only [Option.some.injEq] at h
  rw [← h]; rfl

/-- `loc:`'s table entry refuses what `parseLoc` refuses, and a value that is
not one word (`locWordOk`) — nothing else. -/
theorem editValOf_loc_refuses_only_a_bad_or_unworded_value (w : List Char) :
    (editValOf .loc w).isSome = ((Field.parseLoc w).isSome && locWordOk w) := by
  show ((guardWf _ _).map _).isSome = _
  rw [Option.isSome_map]
  unfold guardWf
  cases hp : Field.parseLoc w with
  | none => rfl
  | some c =>
      simp only [Option.bind_some, Option.isSome_some, Bool.true_and]
      have hwf := Field.parseLoc_wf hp
      have hr := renderLoc_parseLoc hp
      by_cases hw : locWordOk w = true
      · have hok : locOk c = true := by
          show (c.wf && locWordOk (Field.renderLoc c)) = true
          rw [hwf, hr, hw]; rfl
        rw [hw, dif_pos hok]; rfl
      · simp only [Bool.not_eq_true] at hw
        have hok : ¬ locOk c = true := by
          show ¬ (c.wf && locWordOk (Field.renderLoc c)) = true
          rw [hwf, hr, hw]; decide
        rw [hw, dif_neg hok]; rfl

/-- **`at:`'s table entry refuses what `parseInterval` refuses — and one more
thing, by name**: a short end that rolls past 9999-12-31 onto a day no
four-digit year can write. -/
theorem editValOf_interval_refuses_only_a_bad_value_or_the_rollover (w : List Char)
    (h : editValOf .interval w = none) :
    Field.parseInterval w = none ∨
      ∃ s e, Field.parseInterval w = some (s, e) ∧ e.day = s.day + 1 ∧
        Field.dayWf (s.day + 1) = false := by
  have hg : guardWf (fun se : Field.DT × Field.DT => Field.intervalWf se.1 se.2)
      (Field.parseInterval w) = none := by
    have h' : ((guardWf (fun se : Field.DT × Field.DT => Field.intervalWf se.1 se.2)
        (Field.parseInterval w)).map EditVal.interval) = none := h
    simpa using h'
  cases hp : Field.parseInterval w with
  | none => exact Or.inl rfl
  | some se =>
      refine Or.inr ⟨se.1, se.2, rfl, ?_⟩
      have hbad := (guardWf_none_iff _ _).1 hg se hp
      exact Field.parseInterval_wf_unless_rollover (s := se.1) (e := se.2) hp hbad

/-- The same for `win:`, whose absolute form is an `at:` interval. -/
theorem editValOf_window_refuses_only_a_bad_value_or_the_rollover (w : List Char)
    (h : editValOf .window w = none) :
    Field.parseWindow w = none ∨
      ∃ s e, Field.parseWindow w = some (.absolute s e) ∧ e.day = s.day + 1 ∧
        Field.dayWf (s.day + 1) = false := by
  have hg : guardWf Field.windowWf (Field.parseWindow w) = none := by
    have h' : ((guardWf Field.windowWf (Field.parseWindow w)).map EditVal.window) = none := h
    simpa using h'
  cases hp : Field.parseWindow w with
  | none => exact Or.inl rfl
  | some g =>
      have hbad := (guardWf_none_iff _ _).1 hg g hp
      obtain ⟨s, e, hge, hd⟩ := Field.parseWindow_wf_unless_rollover hp hbad
      exact Or.inr ⟨s, e, by rw [hge], hd⟩

/-- …and upward: the eight bridged keys each accept their §4.1 spec value —
both `due:` forms, `at:`'s short end, a daily `win:`, a weekday list, an
`on-event:` with a timeout, one of `loc:`'s four enum names, a `waiting:`
date, and §4.1's mixed `after:` list. -/
theorem the_eight_bridged_keys_accept_their_spec_values :
    ((editValOf .due "2026-09-11".toList).isSome &&
     (editValOf .due "2026-09-11T23:59".toList).isSome &&
     (editValOf .interval "2026-09-07T12:50/13:50".toList).isSome &&
     (editValOf .window "11:30-13:30".toList).isSome &&
     (editValOf .every "Mon,Wed,Fri".toList).isSome &&
     (editValOf .onEvent "reply/7d".toList).isSome &&
     (editValOf .loc "lounge".toList).isSome &&
     (editValOf .waiting "2026-09-20".toList).isSome &&
     (editValOf .after "^k7q2,event:visa".toList).isSome) = true := by decide

/-- **The one bridge that is false, as a witness.**  The loader reads
`at:9999-12-31T23:00/01:00` — the short end rolls onto 10000-01-01 — and the
edit path refuses it, because `renderDate` cannot write a five-digit year back
(`intervalWf`).  The day before is not refused: the bite is exactly the
rollover `editValOf_interval_refuses_only_a_bad_value_or_the_rollover` names. -/
theorem the_year_9999_rollover_parses_but_the_edit_refuses_it :
    (Field.parseInterval "9999-12-31T23:00/01:00".toList).isSome = true ∧
    editValOf .interval "9999-12-31T23:00/01:00".toList = none ∧
    (editValOf .interval "9999-12-30T23:00/01:00".toList).isSome = true := by decide

/-- What `loc:` writes is one word, so the written line reparses to the same
tokens (`Field.setKey_line_reparses`'s `wordWf` hypothesis, discharged). -/
theorem wordLoc_renders_a_word (c : WordLoc) : Field.wordWf (Field.renderLoc c.val) = true := by
  have h := c.property
  simp only [locOk, Bool.and_eq_true] at h
  obtain ⟨hwf, hw⟩ := h
  have hne : Field.renderLoc c.val ≠ [] := by
    cases hc : c.val with
    | named n =>
        rw [hc] at hwf
        simp only [Field.Loc.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
        intro hn; simp only [Field.renderLoc] at hn; rw [hn] at hwf; simp at hwf
    | _ => simp [Field.renderLoc]
  simp only [Field.wordWf, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨by cases hr : Field.renderLoc c.val with
            | nil => exact absurd hr hne
            | cons a t => rfl, ?_⟩
  simp only [locWordOk, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
  simp only [List.all_eq_true]
  intro x hx
  simpa [isSp] using (hw x hx).1

/-! ### The entity transforms, behind gap 32's guard -/

/-- `tm edit ^id <key>=<value>` at the entity: refuse a tabbed line by name,
otherwise write through the field setter.  `wf` never reads the line's bytes,
so the standing proof rides along — an edit cannot move a placement. -/
def editE (v : EditVal) (e : Entity) : Except KErr Entity :=
  if lineHasTab e.val.line then .error .tabbedLine
  else .ok ⟨{ e.val with line := setVal v e.val.line }, e.property⟩

/-- `tm edit ^id <key>=` at the entity: same guard, then remove the key's
tokens — or refuse by name if there is nothing to remove. -/
def unsetE (k : EditKey) (e : Entity) : Except KErr Entity :=
  if lineHasTab e.val.line then .error .tabbedLine
  else if Field.hasKeyTok k.val e.val.line then
    .ok ⟨{ e.val with line := Field.unsetKey k.val e.val.line }, e.property⟩
  else .error .keyAbsent

/-- **The gap-32 check bites** (§5.8): a line carrying a tab anywhere in its
raw bytes is refused, whatever the key and value. -/
theorem editE_refuses_a_tabbed_line (v : EditVal) (e : Entity)
    (h : lineHasTab e.val.line = true) : editE v e = .error .tabbedLine := by
  unfold editE; rw [if_pos h]

/-- **…and does not over-bite**: a tabless line is never refused on that
ground — the edit goes through, to exactly the field-setter write. -/
theorem editE_ok_of_tabless (v : EditVal) (e : Entity)
    (h : lineHasTab e.val.line = false) :
    editE v e = .ok ⟨{ e.val with line := setVal v e.val.line }, e.property⟩ := by
  unfold editE; rw [if_neg (by simp [h])]

/-- **Gap 4's collapse, generalised over the wired keys.**  Whatever keyed
value the command path accepts, the field path — the very view the loader and
`Core`'s readers consume — reads back exactly that value.  The `est` case is
`Core.est` itself (C1's slot pair), the `ci` case is `Core.ci` (C2's), and no
hypothesis is asked about the entity's other bytes.

**Re-proved over the leading slot at W-35 (the owner's D56, README gap 2572).**  The est arm
names which of its two renderings the view reads: the value as written where the line's
leading estimate is the slot (`Field.leadIsTheSlot` of the line the edit was given), the
`est:` token's everywhere else — `Field.view_set_remaining_slot`.  Its old arm, `a.val.est =
some d.val` over one value, is the case `lead = key`, which `cmdSetEst` and the keyed edit
still are; the minutes the host's value denotes are read back on either slot
(`the_edit_path_writes_the_minutes_it_was_given`). -/
theorem the_edit_path_writes_what_the_field_path_reads (v : EditVal) (e a : Entity)
    (h : editE v e = .ok a) :
    match v with
    | .est lead key =>
        a.val.est = some (if Field.leadIsTheSlot e.val.line then lead.val else key.val)
    | .dur d => Field.viewDur a.val.line = some d.val
    | .buffer d => a.val.buffer = some d
    | .pref p => Field.viewPref a.val.line = some p
    | .onMiss m => a.val.onMiss = some m
    | .afterDone x => Field.viewAfterDone a.val.line = some x
    | .floor q => Field.viewMin a.val.line = some q
    | .cap q => Field.viewMax a.val.line = some q
    | .ci c => a.val.ci = some c
    | .due m => Field.viewDue a.val.line = some m.val
    | .interval se => Field.viewAt a.val.line = some se.val
    | .window g => Field.viewWin a.val.line = some g.val
    | .every u => Field.viewEvery a.val.line = some u.val
    | .onEvent x => Field.viewOnEvent a.val.line = some x.val
    | .loc c => Field.viewLoc a.val.line = some c.val
    | .waiting n => Field.viewWaiting a.val.line = some n.val
    | .after ds => a.val.after = ds.val := by
  unfold editE at h
  split at h
  · injection h
  · injection h with h
    subst h
    cases v with
    | est lead key =>
        exact Field.view_set_remaining_slot lead.val key.val e.val.line lead.property key.property
    | dur d => exact Field.view_set_dur d.val e.val.line d.property
    | buffer d => exact Field.view_set_buffer d e.val.line
    | pref p => exact Field.view_set_pref p e.val.line
    | onMiss m => exact Field.view_set_onMiss m e.val.line
    | afterDone x => exact Field.view_set_afterDone x e.val.line
    | floor q => exact Field.view_set_min q e.val.line
    | cap q => exact Field.view_set_max q e.val.line
    | ci c => exact Field.view_set_ci c e.val.line
    | due m => exact Field.view_set_due m.val e.val.line m.property
    | interval se => exact Field.view_set_at se.val.1 se.val.2 e.val.line se.property
    | window g => exact Field.view_set_win g.val e.val.line g.property
    | every u => exact Field.view_set_every u.val e.val.line u.property
    | onEvent x => exact Field.view_set_onEvent x.val e.val.line x.property
    | loc c =>
        have hc : c.val.wf = true := by
          have h := c.property; simp only [locOk, Bool.and_eq_true] at h; exact h.1
        exact Field.view_set_loc c.val e.val.line hc
    | waiting n => exact Field.view_set_waiting n.val e.val.line n.property
    | after ds =>
        show (Field.viewAfter (Field.setAfter ds.val e.val.line)).getD [] = ds.val
        rw [Field.view_set_after ds.val e.val.line ds.property]; rfl

/-- **What the planner reads is the minutes the host's value denotes, whichever slot took it**
(D56): the leading slot keeps `20b`, an `est:` token carries `1200m`, and at the block length
the value was written at both are the same number of minutes. -/
theorem the_edit_path_writes_the_minutes_it_was_given (d : NdDur) (bm : Nat) (e a : Entity)
    (h : editE (EditVal.estAt d bm) e = .ok a) :
    a.val.est.map (Field.Dur.minutes bm) = some (d.val.minutes bm) := by
  have hl := the_edit_path_writes_what_the_field_path_reads _ e a h
  simp only [EditVal.estAt] at hl
  rw [hl]
  split <;> rfl

/-- The unset guard bites like the edit guard. -/
theorem unsetE_refuses_a_tabbed_line (k : EditKey) (e : Entity)
    (h : lineHasTab e.val.line = true) : unsetE k e = .error .tabbedLine := by
  unfold unsetE; rw [if_pos h]

/-- **The absence check bites** (§5.7): unsetting a key the line does not
carry is `keyAbsent`, by name, not a reported success that removed nothing. -/
theorem unset_of_a_key_the_line_does_not_carry_is_refused (k : EditKey) (e : Entity)
    (ht : lineHasTab e.val.line = false) (hk : Field.hasKeyTok k.val e.val.line = false) :
    unsetE k e = .error .keyAbsent := by
  unfold unsetE
  rw [if_neg (by simp [ht]), if_neg (by simp [hk])]

/-- …and does not over-bite: present key, tabless line, the removal goes
through. -/
theorem unsetE_ok_of_present (k : EditKey) (e : Entity)
    (ht : lineHasTab e.val.line = false) (hk : Field.hasKeyTok k.val e.val.line = true) :
    unsetE k e = .ok ⟨{ e.val with line := Field.unsetKey k.val e.val.line }, e.property⟩ := by
  unfold unsetE
  rw [if_neg (by simp [ht]), if_pos hk]

/-- What the unset removes, the field path stops seeing — `lookupKey_unsetKey`
carried through the command path. -/
theorem the_unset_path_removes_what_the_field_path_reads (k : EditKey) (e a : Entity)
    (h : unsetE k e = .ok a) : Field.lookupKey k.val a.val.line = none := by
  unfold unsetE at h
  split at h
  · injection h
  · split at h
    · injection h with h
      subst h
      exact Field.lookupKey_unsetKey k.val e.val.line
    · injection h

/-- `tm move`.  The destination is a `Dest`, not a `Nat`. -/
def cmdMove (i : Id) (rank : Nat) : Relocation := fun p d => p.mapAt i (moveTo (d.site rank))
/-- `tm drop`. -/
def cmdDrop (i : Id) : Transform := (·.mapAt i (fun e => .ok (drop e)))
/-- `tm edit ^id <key>=<value>` — the keyed form, on the wire since the edit
widening. -/
def cmdEdit (v : EditVal) (i : Id) : Transform := (·.mapAt i (editE v))
/-- The plan an edit of `i` to `v` proposes, when `i` is an item.  Exactly the
store `WfPlan.mapAt` re-checks for `cmdEdit`, so a fault read off it is the
fault that refused the command. -/
def editPost (p : WfPlan) (i : Id) (e : Entity) (v : EditVal)
    (hs : (p.val.store.get i).isSome = true) : PlanCore :=
  { p.val with store := p.val.store.set i ⟨{ e.val with line := setVal v e.val.line }, e.property⟩ hs }

/-- Which plan-tier refusal an edit met: the dependency conjuncts by name, and
`badHorizon` — `mapAt`'s standing name — for everything else. -/
def editFault (p : WfPlan) (i : Id) (v : EditVal) : KErr :=
  match h : p.val.store.get i with
  | none => .badHorizon
  | some e =>
    if !afterTotal (editPost p i e v (by rw [h]; rfl)) then .danglingDep
    else if !afterAcyclic (editPost p i e v (by rw [h]; rfl)) then .depCycle
    else .badHorizon

/-- Gap 40's `after` refusal, named at the plan tier: an edit whose post-state
fails `planWf` used to surface as `mapAt`'s `badHorizon` whatever broke; now a
dangling or cyclic `after:` is `danglingDep` / `depCycle`, and every other
plan-tier edit refusal keeps the name it had.  Nothing but the name changes —
`.ok` and every other error pass through untouched. -/
def nameEditFault (p : WfPlan) (i : Id) (v : EditVal) :
    Except KErr WfPlan → Except KErr WfPlan
  | .error .badHorizon => .error (editFault p i v)
  | r => r

/-- Naming a fault never manufactures a success: an `.ok` out is the `.ok` in. -/
theorem nameEditFault_ok {p : WfPlan} {i : Id} {v : EditVal} {r : Except KErr WfPlan}
    {q : WfPlan} (h : nameEditFault p i v r = .ok q) : r = .ok q := by
  unfold nameEditFault at h
  split at h
  · simp at h
  · exact h

theorem nameEditFault_ok_of {p : WfPlan} {i : Id} {v : EditVal} {q : WfPlan} :
    nameEditFault p i v (.ok q) = .ok q := rfl
/-- `tm edit ^id <key>=` — remove the key's tokens. -/
def cmdUnset (k : EditKey) (i : Id) : Transform := (·.mapAt i (unsetE k))
/-- `tm edit ^id est=v`.  Since the edit widening this **is** the keyed edit at
`.est` — one path, one guard, one reader — so the wire behaviour of the
standing `est` op moves in exactly one respect: a tabbed line is now refused
as `tabbedLine` where it was silently edited against the wrong token reading
(gap 32).  The written token is unchanged: `renderDur (Dur.simple v minutes)`,
the same bytes `setEstE` wrote — and since W-35 (D56) it is written where the view reads:
into the leading slot, in place, on a line whose leading estimate is the slot.  This `min`
form's one value is in minutes, so its leading slot reads `Nm`; the host sends the value as
written instead (`EditVal.estAt`), so the leading slot keeps the unit the user typed. -/
def cmdSetEst (v : Nat) (i : Id) : Transform :=
  cmdEdit (.est ⟨Dur.simple v DurUnit.minutes, rfl⟩ ⟨Dur.simple v DurUnit.minutes, rfl⟩) i
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
    ⟨{ live := ⟨0, 0⟩, archive := some ⟨⟨1, 0⟩, ⟨[], true, []⟩⟩, status := .live .free,
       line := ⟨[], true, []⟩ }, rfl⟩, ?_⟩
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
                        line := ⟨[], true, []⟩ }, rfl⟩
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

/-! ## A standing record is merged, not refused (README gap 53)

§4.3's own pre-close pair — a `[ ]` line in a week beside its `[-]` copy under a
month's `# Demoted` — loads as one item whose live line is open and whose
tombstone is the record an earlier demotion filed.  `demote` refuses to demote it
again (`alreadyDemoted`), and the week close used to refuse with it.  Fork-point
`horizon::demote_one` does not refuse: it **rewrites the standing record** — the
two lines' stamps merged (`merge_stamps`), the record's `est:` kept as a floor
under a live line that states no estimate of its own (`demote_est`) — and the old
copy is gone, so the id keeps the one archive record §6.3 gives it.  Replacing the
record *without* the floor would be defect B2's "supersede"; `refile` is the merge
with L15's floor in it (`carryEst_reads_as_demoteEst`, `refile_conserves`,
`refile_respects_user`).

Two of `demoteEst`'s three inputs come off the bytes here, and the third is not
needed: `rec` is the standing record's own `est:` (`recordedEst`), `userSet` is
`ownsEstimate` of the live line, and the block length only scales a reading —
`carryEst` copies the record's token, so the rule holds at every `bm` at once. -/

/-- The `demoted:` history a line carries — `Core.stamps` of any core with these
bytes. -/
def stampsOfLine (r : RawItem) : List Stamp := (Field.viewDemoted r).getD []

/-- One step of fork-point `union_stamps`: keep a stamp already seen, append a new
one. -/
def stampStep (v : List Stamp) (s : Stamp) : List Stamp := if v.contains s then v else v ++ [s]

/-- Fork-point `union_stamps a b`: the stamps of `a`, then of `b`, each once, in the
order first found.  A stamp is `W37` or `D07` with no year, so there is no age
order to sort by; the order is where each stamp was found. -/
def unionStamps (a b : List Stamp) : List Stamp := (a ++ b).foldl stampStep []

/-- Fork-point `merge_stamps prior own add`: the standing record's history, then
what the live line adds, then this demotion's stamp — each once, so a second close
in one period does not write `W37,W37` (fork-point `stamps_with`). -/
def mergeStamps (prior own : List Stamp) (add : Stamp) : List Stamp :=
  unionStamps (unionStamps prior own) [add]

/-- **`userSet`, read off the bytes** — whether a user may have set an estimate since
the standing record was written.  The log that would say so is stage 5's, so this
reads the one line every estimate-writing verb lands on: the live one (`tm edit
^id est=`, `tm stop` and `tm done --partial` all address the id's live line, never
its record).  Fork-point `demote_est` drops the recorded floor exactly when
`item.own_remaining()` — `est:`, else the leading estimate, else `dur:` — is
`Some`.  This is that rule, widened to every estimate reader the kernel has: the
stage-one `viewRemaining` (`est:` over the leading estimate), the field view
`Field.viewRemainingDur` (the one `Core.est` reads), `dur:`, and an `est:` key of
any value.  A disagreement between readers therefore falls on the user's side:
the floor is skipped, never imposed over something a reader calls an estimate
(L14, `floor_and_respect_are_incompatible`).

**Known limit, shared with the Rust:** an estimate the live line carried before the
record was written counts as the user's, so a recorded remaining larger than it —
say an earlier close folded dropped children into the record — is not used as a
floor, and the record's measurement is lost.  Rejected, with the reason: "the live
reading differs from the recorded one" — it drops the floor on a line with no
estimate (the case the Rust keeps it for) and imposes it on a line whose own
estimate equals the record's. -/
def ownsEstimate (r : RawItem) : Bool :=
  hasEst r || (viewRemaining 0 r).isSome || (Field.viewRemainingDur r).isSome ||
    (Field.viewDur r).isSome

/-- **`rec`**: the remaining the standing record measured — its own `est:` token read
at block length `bm` (fork-point `ArchivedRecord.est_min`), `0` when it has none.
A leading estimate on the record is the item's original size, not a measurement,
and the Rust does not read it either. -/
def recordedEst (bm : Nat) (t : RawItem) : Nat :=
  match estKeyTok t with
  | some tok => (unitValue bm (tok.word.drop 4)).getD 0
  | none     => 0

/-- **The estimate the merged record carries.**  A live line that owns an estimate
keeps its bytes (`demoteEst bm true`); one that owns none takes the standing
record's `est:` token verbatim, inserted where `setEst` inserts one.  The reading
is `demoteEst bm false`'s at every block length (`carryEst_reads_as_demoteEst`),
and the bytes keep the unit the record was written in (§4.1: "including the
original estimate unit"). -/
def carryEst (t line : RawItem) : RawItem :=
  if ownsEstimate line then line
  else match estKeyTok t with
    | some tok => ⟨line.indent, line.boxed, insertBeforeId tok.word line.toks⟩
    | none     => line

/-- The bytes a demotion files forward: with no standing record, `demote`'s; with
one, the merged stamps over the carried estimate. -/
def refiledLine (st : Stamp) : Option RawItem → RawItem → RawItem
  | none,   l => Field.setDemoted (stampsOfLine l ++ [st]) l
  | some t, l => Field.setDemoted (mergeStamps (stampsOfLine t) (stampsOfLine l) st) (carryEst t l)

/-- **§6.3's week row, whatever stands.**  With no tombstone, `demote`.  With one,
the item's live line is an open line whose record an earlier demotion filed:
the record is rewritten — its tombstone becomes the line being left, its bytes the
merged stamps over the carried estimate — and the old record's placement is gone,
so the item still has one archive record.  A `[-]` record is refused as `demote`
refuses it (`alreadyDemoted`): filing a record again is the month close's `move`,
not a second demotion (`refile_twice_is_not_a_thing`). -/
def refile (target : Site) (st : Stamp) (e : Entity) : Except KErr Entity :=
  match e.val.archive with
  | none   => demote target st e
  | some t =>
    if e.val.status = .demoted then .error .alreadyDemoted
    else lift { e.val with live := target, archive := some ⟨e.val.live, e.val.line⟩,
                           status := .demoted, line := refiledLine st (some t.line) e.val.line }

/-- What `refile` produces where it succeeds. -/
theorem refile_roundtrips (t : Site) (st : Stamp) (e a : Entity) (h : refile t st e = .ok a) :
    a.val = { e.val with live := t, archive := some ⟨e.val.live, e.val.line⟩, status := .demoted,
                         line := refiledLine st (e.val.archive.map Tomb.line) e.val.line } := by
  unfold refile at h
  cases ha : e.val.archive with
  | none =>
    simp only [ha] at h
    rw [demote_roundtrips _ _ _ _ h]
    rfl
  | some tb =>
    simp only [ha] at h
    split at h
    · simp at h
    · rw [lift_roundtrips _ _ h]
      rfl

/-- With no standing record, `refile` is `demote`. -/
theorem refile_of_no_record (t : Site) (st : Stamp) (e : Entity) (h : e.val.archive = none) :
    refile t st e = demote t st e := by
  simp [refile, h]

/-- **L11b, for `refile`.**  A record `refile` wrote is `[-]` with a tombstone, so
filing it again is refused. -/
theorem refile_twice_is_not_a_thing (t t' : Site) (st st' : Stamp) (e a : Entity)
    (h : refile t st e = .ok a) : refile t' st' a = .error .alreadyDemoted := by
  have hv := refile_roundtrips _ _ _ _ h
  simp [refile, hv]

/-- **The refusal is gone for open lines.**  `refile` answers `alreadyDemoted` only
for a line whose own box is `[-]` — never for §4.3's pre-close pair.  (`refile`
cannot see where its tombstone sits; the close and the verb refuse, before it
merges, an item whose tombstone is not a `# Demoted` record — `guardStray`,
Close.lean.) -/
theorem refile_refuses_only_a_record {t : Site} {st : Stamp} {e : Entity}
    (h : refile t st e = .error .alreadyDemoted) : e.val.status = .demoted := by
  unfold refile at h
  cases ha : e.val.archive with
  | none =>
    simp only [ha, demote, Option.isSome_none, Bool.false_eq_true, if_false, lift] at h
    split at h <;> simp at h
  | some tb =>
    simp only [ha] at h
    split at h
    · assumption
    · unfold lift at h
      split at h <;> simp at h

/-! ### The merged stamps -/

theorem foldl_stampStep_mem : ∀ (l v : List Stamp) (x : Stamp),
    x ∈ l.foldl stampStep v ↔ x ∈ v ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro v x; simp
  | cons s l ih =>
    intro v x
    simp only [List.foldl_cons, ih, List.mem_cons]
    unfold stampStep
    by_cases hs : v.contains s = true
    · have hm : s ∈ v := by simpa using hs
      simp only [hs, if_true]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hm
        · exact Or.inr h
    · simp only [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_eq_true, if_false, List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem foldl_stampStep_nodup : ∀ (l v : List Stamp), v.Nodup → (l.foldl stampStep v).Nodup := by
  intro l
  induction l with
  | nil => intro v h; exact h
  | cons s l ih =>
    intro v h
    apply ih
    unfold stampStep
    by_cases hs : v.contains s = true
    · simp only [hs, if_true]; exact h
    · simp only [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_eq_true, if_false]
      exact List.nodup_append.2 ⟨h, List.pairwise_singleton _ s, fun a ha b hb hab => by
        simp only [List.mem_singleton] at hb
        subst hb hab
        simp [ha] at hs⟩

theorem foldl_stampStep_of_nodup : ∀ (l v : List Stamp), (v ++ l).Nodup → l.foldl stampStep v = v ++ l := by
  intro l
  induction l with
  | nil => intro v _; simp
  | cons s l ih =>
    intro v h
    have hs : v.contains s = false := by
      have hd := (List.nodup_append.1 h).2.2
      cases hc : v.contains s with
      | false => rfl
      | true => exact absurd rfl (hd s (by simpa using hc) s (List.mem_cons_self ..))
    simp only [List.foldl_cons, stampStep, hs, Bool.false_eq_true, if_false]
    rw [ih (v ++ [s]) (by simpa using h)]
    simp

/-- **The Rust's order.**  When the record's stamps, the live line's and the new one
are all distinct, the merge is the record's history, then the live line's, then
the new stamp — nothing reordered, nothing dropped. -/
theorem mergeStamps_of_nodup (prior own : List Stamp) (add : Stamp)
    (h : (prior ++ own ++ [add]).Nodup) : mergeStamps prior own add = prior ++ own ++ [add] := by
  have h1 : (prior ++ own).Nodup := (List.nodup_append.1 h).1
  have e1 : unionStamps prior own = prior ++ own := by
    unfold unionStamps
    exact foldl_stampStep_of_nodup _ [] (by simpa using h1)
  unfold mergeStamps
  rw [e1]
  unfold unionStamps
  exact foldl_stampStep_of_nodup _ [] (by simpa using h)

/-- **Nothing lost, nothing invented, nothing twice.** -/
theorem mergeStamps_spec (prior own : List Stamp) (add : Stamp) :
    (mergeStamps prior own add).Nodup ∧
      ∀ x, x ∈ mergeStamps prior own add ↔ x ∈ prior ∨ x ∈ own ∨ x = add := by
  refine ⟨foldl_stampStep_nodup _ _ List.nodup_nil, fun x => ?_⟩
  unfold mergeStamps
  have hu : ∀ a b : List Stamp, x ∈ unionStamps a b ↔ x ∈ a ∨ x ∈ b := by
    intro a b
    unfold unionStamps
    rw [foldl_stampStep_mem]
    simp
  rw [hu, hu]
  simp [or_assoc]

/-! ### The merged estimate: L15 through the merge -/

theorem unitValue_isSome (bm : Nat) (w : List Char) :
    (unitValue bm w).isSome = (unitValue 0 w).isSome := by
  unfold unitValue
  split <;> simp

theorem estKeyTok_of_hasEst {r : RawItem} (h : hasEst r = false) : estKeyTok r = none := by
  unfold estKeyTok
  unfold hasEst at h
  exact List.find?_eq_none.2 (fun t ht => by simpa using List.any_eq_false.1 h t ht)

theorem remainingOf_of_not_ownsEstimate (bm : Nat) {r : RawItem} (h : ownsEstimate r = false) :
    remainingOf bm r = 0 := by
  simp only [ownsEstimate, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := h
  have hv : viewRemaining bm r = none := by
    unfold viewRemaining at h2 ⊢
    rw [estKeyTok_of_hasEst h1] at h2 ⊢
    cases hl : leadEstTok r with
    | none => rfl
    | some t =>
      simp only [hl, Option.bind_some] at h2 ⊢
      rw [← Option.not_isSome_iff_eq_none, unitValue_isSome]
      simpa using h2
  unfold remainingOf
  rw [hv]
  rfl

/-- **The merged record reads as `demoteEst` wrote it, at every block length.** -/
theorem carryEst_reads_as_demoteEst (bm : Nat) (t : RawItem) (e : Entity) :
    remainingOf bm (carryEst t e.val.line) =
      remainingOf bm (demoteEst bm (ownsEstimate e.val.line) (recordedEst bm t) e).val.line := by
  cases ho : ownsEstimate e.val.line with
  | true => simp [carryEst, ho, demoteEst]
  | false =>
    have h0 := remainingOf_of_not_ownsEstimate bm ho
    have hset : ∀ v, remainingOf bm (setEst v e.val.line) = v := by
      intro v
      unfold remainingOf
      rw [view_set_is_not_silent]
      rfl
    have hr : remainingOf bm (demoteEst bm false (recordedEst bm t) e).val.line = recordedEst bm t := by
      show remainingOf bm (setEst (max (remainingOf bm e.val.line) (recordedEst bm t)) e.val.line) = _
      rw [hset, h0]
      simp
    rw [hr]
    have hno : hasEst e.val.line = false := by
      simp only [ownsEstimate, Bool.or_eq_false_iff] at ho
      exact ho.1.1.1
    unfold carryEst recordedEst
    simp only [ho, Bool.false_eq_true, if_false]
    cases hk : estKeyTok t with
    | none => exact h0
    | some tok =>
      simp only
      have hkey : isEstKey tok.word = true := by
        unfold estKeyTok at hk
        have := List.find?_some hk
        simpa using this
      have hf := find_insertBeforeId tok.word e.val.line.toks hkey (by simpa [hasEst] using hno)
      unfold remainingOf viewRemaining estKeyTok
      simp only
      cases hff : (insertBeforeId tok.word e.val.line.toks).find? (fun u => isEstKey u.word) with
      | none => rw [hff] at hf; simp at hf
      | some u =>
        rw [hff] at hf
        simp only [Option.map_some, Option.some.injEq] at hf
        simp [hf]

/-- **L15a, through the merge.**  When the live line owns no estimate, the standing
record's measured remaining is a floor, and so is the line's own reading. -/
theorem refile_conserves (bm : Nat) {t : Site} {st : Stamp} {e a : Entity} {tb : Tomb}
    (harch : e.val.archive = some tb) (hu : ownsEstimate e.val.line = false)
    (h : refile t st e = .ok a) :
    recordedEst bm tb.line ≤ remainingOf bm a.val.line ∧
      remainingOf bm e.val.line ≤ remainingOf bm a.val.line := by
  have hv := refile_roundtrips _ _ _ _ h
  have hl : remainingOf bm a.val.line =
      remainingOf bm (demoteEst bm false (recordedEst bm tb.line) e).val.line := by
    rw [hv, harch]
    show remainingOf bm (Field.setDemoted _ (carryEst tb.line e.val.line)) = _
    rw [Field.remainingOf_setDemoted, carryEst_reads_as_demoteEst, hu]
  rw [hl]
  exact demoteEst_conserves bm _ e

/-- **L15b, through the merge.**  When the live line owns an estimate, it stands byte
for byte: the record is the live line with only the merged stamps set. -/
theorem refile_respects_user {t : Site} {st : Stamp} {e a : Entity} {tb : Tomb}
    (harch : e.val.archive = some tb) (hu : ownsEstimate e.val.line = true)
    (h : refile t st e = .ok a) :
    a.val.line = Field.setDemoted (mergeStamps (stampsOfLine tb.line) e.val.stamps st) e.val.line := by
  rw [refile_roundtrips _ _ _ _ h, harch]
  simp [refiledLine, carryEst, hu, Core.stamps, stampsOfLine]

/-! ## The week row's child fold: §6.4's `max`, through L15's floor (goal B3's repair)

§6.3's week row: "Unfinished children are dropped from the week file (their
remaining is folded into the parent's `est:`)."  §6.4 makes a parent's own estimate
cover its decomposition — `remaining(item)` is its own `est` if set, else
`est_original`, else Σ over its children — so the fold is **not** a sum: fork-point
`horizon::demote_est` floors the parent's remaining at the children's (`folded`),
which is `max(remaining(parent), Σ own remaining of the children dropped with it)`
(module doc, "Folding children").  Here that floor is `foldEst`, and it reads as
`demoteEst bm false` reads with `rec :=` the children's minutes
(`foldEst_reads_as_demoteEst`).  **No user exception applies to it**, as in the
fork point: `demote_est` drops the *record's* floor under a line that owns an
estimate (`carryEst`, L15b), never the children's — the dropped lines are about
to leave the plan's open work, and the parent's record is the only place their
minutes survive.  L14 (`floor_and_respect_are_incompatible`) is not contradicted:
the fold floors, and it says so.

The bytes: nothing, when the parent's reading already covers the children (the
`max` changes nothing, so neither does the line); otherwise one `est:` token, set
where `setEst` sets one, in whole blocks when the block length divides the minutes
(fork-point `est_dur`, `3b`), else whole hours, else minutes.  The fork point
writes minutes over an hour as `NhMm`, which the reader `remainingOf` does not read,
so the kernel writes `Nm` there (README "Stage 4 final, step 4"). -/

/-- The stage-one `est:` setter over an arbitrary value word: replace the value of
the first `est:` token, or insert one before the id.  `setEst v` is this with the
minutes word `digitsOf v ++ "m"`. -/
def setEstInTo (w : List Char) : List Tok → List Tok
  | []      => []
  | t :: ts => if isEstKey t.word then ⟨t.sep, w⟩ :: ts else t :: setEstInTo w ts

def setEstTo (v : List Char) (r : RawItem) : RawItem :=
  if hasEst r then ⟨r.indent, r.boxed, setEstInTo (['e', 's', 't', ':'] ++ v) r.toks⟩
  else ⟨r.indent, r.boxed, insertBeforeId (['e', 's', 't', ':'] ++ v) r.toks⟩

theorem find_setEstInTo (w : List Char) (hw : isEstKey w = true) (ts : List Tok)
    (h : ts.any (fun t => isEstKey t.word) = true) :
    ((setEstInTo w ts).find? (fun t => isEstKey t.word)).map Tok.word = some w := by
  induction ts with
  | nil => simp at h
  | cons t ts' ih =>
    by_cases hk : isEstKey t.word = true
    · simp only [setEstInTo, if_pos hk, List.find?_cons]
      simp [hw]
    · simp only [setEstInTo, if_neg hk, List.find?_cons]
      simp only [Bool.not_eq_true] at hk
      simp only [hk, Bool.false_eq_true]
      exact ih (by simpa [hk] using h)

/-- **What the fold's setter writes, the stage-one reader reads** — the
`view_set_is_not_silent` obligation, for any value word. -/
theorem viewRemaining_setEstTo (bm : Nat) (v : List Char) (r : RawItem) :
    viewRemaining bm (setEstTo v r) = unitValue bm v := by
  have hw : isEstKey (['e', 's', 't', ':'] ++ v) = true := by simp [isEstKey]
  have hdrop : (['e', 's', 't', ':'] ++ v).drop 4 = v := rfl
  unfold setEstTo viewRemaining estKeyTok
  by_cases h : hasEst r = true
  · rw [if_pos h]
    have := find_setEstInTo _ hw r.toks (by simpa [hasEst] using h)
    cases hf : (setEstInTo (['e', 's', 't', ':'] ++ v) r.toks).find? (fun t => isEstKey t.word) with
    | none => rw [hf] at this; simp at this
    | some t =>
      rw [hf] at this
      simp only [Option.map_some, Option.some.injEq] at this
      simp only [this, hdrop]
  · simp only [Bool.not_eq_true] at h
    rw [if_neg (by simp [h])]
    have := find_insertBeforeId _ r.toks hw (by simpa [hasEst] using h)
    cases hf : (insertBeforeId (['e', 's', 't', ':'] ++ v) r.toks).find? (fun t => isEstKey t.word) with
    | none => rw [hf] at this; simp at this
    | some t =>
      rw [hf] at this
      simp only [Option.map_some, Option.some.injEq] at this
      simp only [this, hdrop]

/-- The duration the fold writes for `n` minutes at block length `bm`. -/
def foldDur (bm n : Nat) : Dur :=
  if 0 < bm ∧ n % bm = 0 then .simple (n / bm) .blocks
  else if n % 60 = 0 then .simple (n / 60) .hours
  else .simple n .minutes

theorem unitValue_digits_b (bm k : Nat) : unitValue bm (digitsOf k ++ ['b']) = some (k * bm) := by
  unfold unitValue; simp [readNat_digitsOf]

theorem unitValue_digits_h (bm k : Nat) : unitValue bm (digitsOf k ++ ['h']) = some (k * 60) := by
  unfold unitValue; simp [readNat_digitsOf]

theorem unitValue_digits_m (bm k : Nat) : unitValue bm (digitsOf k ++ ['m']) = some k := by
  unfold unitValue; simp [readNat_digitsOf]

/-- **The token the fold writes reads back as the minutes it was given**, at the
block length it was written for. -/
theorem unitValue_foldDur (bm n : Nat) : unitValue bm (Field.renderDur (foldDur bm n)) = some n := by
  unfold foldDur
  split
  · rename_i h
    show unitValue bm (digitsOf (n / bm) ++ ['b']) = some n
    rw [unitValue_digits_b, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)]
  · split
    · rename_i h
      show unitValue bm (digitsOf (n / 60) ++ ['h']) = some n
      rw [unitValue_digits_h, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]
    · show unitValue bm (digitsOf n ++ ['m']) = some n
      rw [unitValue_digits_m]

/-- **The fold's estimate.**  A line whose reading covers the children's `n`
minutes is left byte for byte; otherwise its `est:` becomes `n`. -/
def foldEst (bm n : Nat) (l : RawItem) : RawItem :=
  if n ≤ remainingOf bm l then l else setEstTo (Field.renderDur (foldDur bm n)) l

theorem foldEst_of_le {bm n : Nat} {l : RawItem} (h : n ≤ remainingOf bm l) : foldEst bm n l = l := by
  unfold foldEst; rw [if_pos h]

theorem foldEst_of_lt {bm n : Nat} {l : RawItem} (h : remainingOf bm l < n) :
    foldEst bm n l = setEstTo (Field.renderDur (foldDur bm n)) l := by
  unfold foldEst; rw [if_neg (Nat.not_le.2 h)]

/-- Nothing folded writes nothing. -/
theorem foldEst_zero (bm : Nat) (l : RawItem) : foldEst bm 0 l = l := foldEst_of_le (Nat.zero_le _)

/-- **§6.4's `max`**: the folded line reads as the larger of its own reading and the
children's minutes. -/
theorem remainingOf_foldEst (bm n : Nat) (l : RawItem) :
    remainingOf bm (foldEst bm n l) = max (remainingOf bm l) n := by
  by_cases h : n ≤ remainingOf bm l
  · rw [foldEst_of_le h, Nat.max_eq_left h]
  · have h' := Nat.lt_of_not_le h
    rw [foldEst_of_lt h', Nat.max_eq_right (Nat.le_of_lt h')]
    unfold remainingOf
    rw [viewRemaining_setEstTo, unitValue_foldDur]
    rfl

/-- **The fold is `demoteEst`'s floor**, with the children's minutes as the recorded
measurement and no user exception (`userSet := false`), at every block length the
fold was computed for. -/
theorem foldEst_reads_as_demoteEst (bm n : Nat) (e : Entity) :
    remainingOf bm (foldEst bm n e.val.line) = remainingOf bm (demoteEst bm false n e).val.line := by
  rw [remainingOf_foldEst]
  show _ = remainingOf bm (setEst (max (remainingOf bm e.val.line) n) e.val.line)
  unfold remainingOf
  rw [view_set_is_not_silent]
  rfl

/-- **What the week row's child fold asks of one line** — computed once per close
from the plan the close is handed (`foldFxOf`, Close.lean). -/
inductive FoldFx
  /-- no fold: the line is filed as it was before B3's repair -/
  | none
  /-- a child dropped with its parent: `[~]` in place, its minutes in the parent's record -/
  | drop
  /-- a line that files forward carrying `n` minutes of the children dropped with it,
      read at block length `bm` -/
  | lift (bm n : Nat)
deriving DecidableEq, Repr

def FoldFx.isDrop : FoldFx → Bool
  | .drop => true
  | _     => false

/-- The estimate a filed line's record carries under the fold. -/
def FoldFx.apply : FoldFx → RawItem → RawItem
  | .lift bm n, l => foldEst bm n l
  | _,          l => l

/-- The bytes a demotion files forward, the fold included: `refiledLine`'s, with the
children's floor applied to the estimate **before** the stamp is set — fork-point
`demote_one` sets `est` and then `demoted`, so an inserted `est:` stands ahead of
the `demoted:` token. -/
def refiledLineX (x : FoldFx) (st : Stamp) : Option RawItem → RawItem → RawItem
  | none,   l => Field.setDemoted (stampsOfLine l ++ [st]) (x.apply l)
  | some t, l => Field.setDemoted (mergeStamps (stampsOfLine t) (stampsOfLine l) st) (x.apply (carryEst t l))

/-- Without a lift, the fold writes what `refiledLine` wrote. -/
theorem refiledLineX_of_apply {x : FoldFx} (hx : ∀ l, x.apply l = l) (st : Stamp) (a : Option RawItem)
    (l : RawItem) : refiledLineX x st a l = refiledLine st a l := by
  cases a <;> simp [refiledLineX, refiledLine, hx]

theorem refiledLineX_none (st : Stamp) (a : Option RawItem) (l : RawItem) :
    refiledLineX .none st a l = refiledLine st a l := refiledLineX_of_apply (fun _ => rfl) st a l

/-- `refile`, with the fold: the same refusal, the same placements and box, and
`refiledLineX`'s bytes. -/
def refileX (x : FoldFx) (target : Site) (st : Stamp) (e : Entity) : Except KErr Entity :=
  match e.val.archive with
  | none   => lift { e.val with live := target, archive := some ⟨e.val.live, e.val.line⟩,
                                status := .demoted, line := refiledLineX x st none e.val.line }
  | some t =>
    if e.val.status = .demoted then .error .alreadyDemoted
    else lift { e.val with live := target, archive := some ⟨e.val.live, e.val.line⟩,
                           status := .demoted, line := refiledLineX x st (some t.line) e.val.line }

theorem refileX_roundtrips (x : FoldFx) (t : Site) (st : Stamp) (e a : Entity) (h : refileX x t st e = .ok a) :
    a.val = { e.val with live := t, archive := some ⟨e.val.live, e.val.line⟩, status := .demoted,
                         line := refiledLineX x st (e.val.archive.map Tomb.line) e.val.line } := by
  unfold refileX at h
  cases ha : e.val.archive with
  | none =>
    simp only [ha] at h
    rw [lift_roundtrips _ _ h]
    rfl
  | some tb =>
    simp only [ha] at h
    split at h
    · simp at h
    · rw [lift_roundtrips _ _ h]
      rfl

/-- **Without a lift, `refileX` is `refile`** — the transform the close ran before
B3's repair and the demote verb still runs. -/
theorem refileX_none (t : Site) (st : Stamp) (e : Entity) : refileX .none t st e = refile t st e := by
  unfold refileX refile
  cases ha : e.val.archive with
  | none =>
    simp only [demote, ha, Option.isSome_none, Bool.false_eq_true, if_false]
    rfl
  | some tb => rfl

theorem refileX_refuses_only_a_record {x : FoldFx} {t : Site} {st : Stamp} {e : Entity}
    (h : refileX x t st e = .error .alreadyDemoted) : e.val.status = .demoted := by
  unfold refileX at h
  cases ha : e.val.archive with
  | none =>
    simp only [ha, lift] at h
    split at h <;> simp at h
  | some tb =>
    simp only [ha] at h
    split at h
    · assumption
    · unfold lift at h
      split at h <;> simp at h

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

/-- **The token an est edit writes, at the value the host sends** (W-35 track E, D56; README gap
2851).  `tm edit est=20b` at a 60-minute block is `EditVal.estAt 20b 60` — the value as written for
the leading slot, its canonical minutes for an `est:` token (D49) — and the token's bytes,
`EditVal.rendered`, are `1200m`, never the `20b` the leading slot keeps; a `ci=3` edit renders `3`.
Written because re-rostering `EditVal.rendered` after D56 changed its est arm found
`setVal_writes_the_token_the_loader_reads_unless_it_rewrites_the_leading_estimate` ALONE: with that
law's proof sorried, nothing told the table from `fun _ => []`.  Appended at the end of the module
so that no other roster row's pin site moves. -/
theorem EditVal.rendered_is_the_tokens_bytes :
    (EditVal.estAt ⟨.simple 20 .blocks, rfl⟩ 60).rendered = ['1', '2', '0', '0', 'm'] ∧
    EditVal.estAt ⟨.simple 20 .blocks, rfl⟩ 60
      = .est ⟨.simple 20 .blocks, rfl⟩ ⟨.simple 1200 .minutes, rfl⟩ ∧
    (EditVal.ci 3).rendered = ['3'] := by decide

end Tm
