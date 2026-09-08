import TmKernel.Text
/-!
# The item line

The grammar subset this stage interprets (§4.1):

```
<indent>- [<state>] <tokens…>
```

* `<state>` is one of `[ ] [>] [x] [-] [~] [?]` and is **rendered from the
  status and the placement**, never stored — §6.3's `[-]` is positional.
* tokens are whitespace-separated words, kept **verbatim**;
* exactly one token must be `^<id>`, and its word is **rendered from the store
  key**, never stored;
* `est:<N>b|m|h` and the leading estimate `<N>b|m|h` are *interpreted*
  (they are where the `tm edit est=` bug lived);
* every other token — `@parent`, `#tag`, `!k`, `due:`, `at:`, `every:`, … — is
  preserved byte for byte and not interpreted at this stage.

Round trip A (`serialize ∘ parse = id` on accepted lines) is unconditional.
Round trip B (`parse ∘ serialize = id`) holds on `CanonicalItem`, which is
decidable.

**Gap, stated rather than glossed:** that the setters below *preserve*
`CanonicalItem` is not proved here.  It is true for `setEst`'s replace branch
and it is **false in general for its insert branch** — inserting a token before
an id token that was the line's first token leaves that id token needing a
separator it does not have.  Real lines (`- [ ] title ^id`) never hit that, but
"never in practice" is exactly the kind of reasoning this kernel exists to stop
relying on.  Until it is proved, `CanonicalItem` is decidable and can be
checked.
-/
namespace Tm

structure RawItem where
  indent : List Char
  toks   : List Tok
deriving DecidableEq, Repr, Inhabited

def isIdWord (w : List Char) : Bool := w.head? == some '^'

/-- The id token's word comes from the **store key**, not from the file. -/
def Tok.rawFor (i : Id) (t : Tok) : List Char :=
  t.sep ++ (if isIdWord t.word then '^' :: i else t.word)

def serializeItem (i : Id) (g : Glyph) (r : RawItem) : List Char :=
  r.indent ++ ('-' :: ' ' :: '[' :: g.char :: ']' :: r.toks.flatMap (Tok.rawFor i))

inductive PErr | notAnItem | badState (c : Char) | noId | manyIds
deriving DecidableEq, Repr

def idToks (r : RawItem) : List Tok := r.toks.filter (fun t => isIdWord t.word)

def parseToks (indent : List Char) (g : Glyph) (ts : List Tok) :
    Except PErr (Id × Glyph × RawItem) :=
  match ts.filter (fun t => isIdWord t.word) with
  | [t] => .ok (t.word.tail, g, ⟨indent, ts⟩)
  | []  => .error .noId
  | _   => .error .manyIds

def parseBody (indent rest : List Char) : Except PErr (Id × Glyph × RawItem) :=
  match rest with
  | '-' :: ' ' :: '[' :: c :: ']' :: tail =>
    match Glyph.ofChar? c with
    | none   => .error (.badState c)
    | some g => parseToks indent g (tokenize tail)
  | _ => .error .notAnItem

def parseItem (cs : List Char) : Except PErr (Id × Glyph × RawItem) :=
  parseBody (cs.takeWhile isSp) (cs.dropWhile isSp)

/-- `.toOption` is banned in this kernel (it is how the FFI spike silently
erased `est: -3`), so this is a match. -/
def isItemLine (cs : List Char) : Bool :=
  match parseItem cs with
  | .ok _    => true
  | .error _ => false

/-! ## Round trip A -/

theorem ofChar_char {c : Char} {g : Glyph} (h : Glyph.ofChar? c = some g) : g.char = c := by
  unfold Glyph.ofChar? at h
  split at h <;> first
    | (injection h with h; subst h; rfl)
    | simp at h

theorem head_cons_tail {w : List Char} (h : w.head? = some '^') : w = '^' :: w.tail := by
  cases w with
  | nil => simp at h
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

theorem rawFor_eq_raw (i : Id) (ts : List Tok)
    (h : ∀ t ∈ ts, isIdWord t.word = true → t.word = '^' :: i) :
    ts.flatMap (Tok.rawFor i) = ts.flatMap Tok.raw := by
  induction ts with
  | nil => rfl
  | cons t ts' ih =>
      simp only [List.flatMap_cons]
      have hd : Tok.rawFor i t = Tok.raw t := by
        unfold Tok.rawFor Tok.raw
        by_cases hid : isIdWord t.word = true
        · rw [if_pos hid, ← h t (by simp) hid]
        · rw [if_neg hid]
      rw [hd, ih (fun u hu => h u (by simp [hu]))]

/-- **Round trip A.**  Every line the parser accepts serialises back to exactly
the bytes it was read from — including the state box and the `^id`, which are
*regenerated* from the status and the store key rather than copied.  §17's "a
line that crosses a horizon crosses it byte for byte" is the representation,
not a property tested afterwards. -/
theorem serialize_parse (cs : List Char) (i : Id) (g : Glyph) (r : RawItem)
    (h : parseItem cs = .ok (i, g, r)) : serializeItem i g r = cs := by
  unfold parseItem parseBody at h
  split at h
  · rename_i c tail heq
    split at h
    · simp at h
    · rename_i g' hg
      unfold parseToks at h
      split at h
      · rename_i t hfilter
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, hgg, hr⟩ := h
        subst hgg; subst hr
        have hid : ∀ u ∈ tokenize tail, isIdWord u.word = true → u.word = '^' :: i := by
          intro u hu hidw
          have humem : u ∈ (tokenize tail).filter (fun t => isIdWord t.word) := by
            simp [List.mem_filter, hu, hidw]
          rw [show (tokenize tail).filter (fun t => isIdWord t.word) = [t] from hfilter] at humem
          simp only [List.mem_singleton] at humem
          subst humem
          have : u.word.head? = some '^' := by simpa [isIdWord] using hidw
          rw [← hi]
          exact head_cons_tail this
        unfold serializeItem
        simp only
        rw [rawFor_eq_raw i _ hid, tokenize_raw, ofChar_char hg, ← heq,
          List.takeWhile_append_dropWhile]
      · simp at h
      · simp at h
  · simp at h

/-! ## Round trip B -/

/-- Decidable.  See the module header for what is *not* proved about it. -/
def CanonicalItem (i : Id) (r : RawItem) : Bool :=
  r.indent.all isSp && toksWf r.toks &&
    (match idToks r with
     | [t] => t.word == '^' :: i
     | _   => false)

/-- **Round trip B.**  Anything the kernel writes, it reads back identically.
This is the direction that matters after an edit. -/
theorem parse_serialize (i : Id) (g : Glyph) (r : RawItem) (h : CanonicalItem i r = true) :
    parseItem (serializeItem i g r) = .ok (i, g, r) := by
  unfold CanonicalItem at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hind, htw⟩, hids⟩ := h
  -- the one id token
  cases hft : idToks r with
  | nil => rw [hft] at hids; simp at hids
  | cons t rest =>
    cases rest with
    | cons u rs => rw [hft] at hids; simp at hids
    | nil =>
      rw [hft] at hids
      simp only [beq_iff_eq] at hids
      have hid : ∀ v ∈ r.toks, isIdWord v.word = true → v.word = '^' :: i := by
        intro v hv hidw
        have hmem : v ∈ idToks r := by simp [idToks, List.mem_filter, hv, hidw]
        rw [hft] at hmem
        simp only [List.mem_singleton] at hmem
        subst hmem; exact hids
      have hbody : r.toks.flatMap (Tok.rawFor i) = r.toks.flatMap Tok.raw :=
        rawFor_eq_raw i r.toks hid
      have hindsp : ∀ c ∈ r.indent, isSp c = true := fun c hc => List.all_eq_true.1 hind c hc
      have hhd : ∀ c, ('-' :: ' ' :: '[' :: g.char :: ']' :: r.toks.flatMap (Tok.rawFor i)).head?
          = some c → isSp c = false := by
        intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc; subst hc; rfl
      have hsplit := takeWhile_append_all isSp r.indent
        ('-' :: ' ' :: '[' :: g.char :: ']' :: r.toks.flatMap (Tok.rawFor i)) hindsp hhd
      unfold parseItem serializeItem
      rw [hsplit.1, hsplit.2]
      unfold parseBody
      simp only [glyph_roundtrip]
      rw [hbody, tokenize_toks r.toks htw]
      unfold parseToks
      have hidt : r.toks.filter (fun t => isIdWord t.word) = [t] := hft
      rw [hidt]
      show Except.ok (t.word.tail, g, (⟨r.indent, r.toks⟩ : RawItem)) = Except.ok (i, g, r)
      have htail : t.word.tail = i := by rw [hids]; rfl
      rw [htail]

/-! ## Views: the estimate

§3.2's `remaining` is a three-way fallback over two syntactic slots.  Here it
is a **view** of the token vector, computed, so "which slot wins" is a fact
about one function rather than a rule spread over the code. -/

def isEstKey (w : List Char) : Bool := w.take 4 == ['e', 's', 't', ':']

/-- `Nb` = N blocks, `Nm` = N minutes, `Nh` = N hours. -/
def unitValue (blockMin : Nat) (w : List Char) : Option Nat :=
  match w.reverse with
  | 'b' :: ds => (readNat ds.reverse).map (· * blockMin)
  | 'm' :: ds => readNat ds.reverse
  | 'h' :: ds => (readNat ds.reverse).map (· * 60)
  | _ => none

def isCiWord (w : List Char) : Bool :=
  match w with
  | [c] => '0' ≤ c && c ≤ '5'
  | _   => false

/-- The leading estimate: the first token, or the second if the first is a
`ci` digit (§4.1: "must directly follow ci"). -/
def leadEstTok (r : RawItem) : Option Tok :=
  match r.toks with
  | []          => none
  | t :: rest   => if isCiWord t.word then rest.head? else some t

def estKeyTok (r : RawItem) : Option Tok := r.toks.find? (fun t => isEstKey t.word)

/-- **`est:` overrides the leading estimate.**  One function, one answer. -/
def viewRemaining (blockMin : Nat) (r : RawItem) : Option Nat :=
  match estKeyTok r with
  | some t => unitValue blockMin (t.word.drop 4)
  | none   => (leadEstTok r).bind (fun t => unitValue blockMin t.word)

def remainingOf (blockMin : Nat) (r : RawItem) : Nat := (viewRemaining blockMin r).getD 0

/-! ## Setters -/

def estWord (v : Nat) : List Char := ['e', 's', 't', ':'] ++ digitsOf v ++ ['m']

def setEstIn (v : Nat) : List Tok → List Tok
  | []      => []
  | t :: ts => if isEstKey t.word then ⟨t.sep, estWord v⟩ :: ts else t :: setEstIn v ts

/-- Insert a word immediately before the id token.

**The separator is the whole difficulty, and getting it wrong was a bug.**
`- [ ]^m1` is a line the parser accepts: its id token carries no separator,
because nothing precedes it.  Inserting a token in front of that with a leading
space produced `- [ ] est:45m^m1`, in which `est:45m^m1` is a single word and
the line no longer has an id token at all — one `tm edit est=` turned a line the
kernel accepted into a line the kernel reads as prose.  So when the id token has
no separator of its own, the inserted word takes that position and the id token
takes the space.  `setEst_canonical` below is the proof that this is now
airtight, and it closes the gap this module's header used to record. -/
def insertBeforeId (w : List Char) : List Tok → List Tok
  | []      => [⟨[' '], w⟩]
  | u :: us =>
    if isIdWord u.word then
      (if u.sep.isEmpty then ⟨[], w⟩ :: ⟨[' '], u.word⟩ :: us
       else ⟨[' '], w⟩ :: u :: us)
    else u :: insertBeforeId w us

def hasEst (r : RawItem) : Bool := r.toks.any (fun t => isEstKey t.word)

/-- `tm edit ^id est=v`: write the slot the view reads. -/
def setEst (v : Nat) (r : RawItem) : RawItem :=
  if hasEst r then ⟨r.indent, setEstIn v r.toks⟩
  else ⟨r.indent, insertBeforeId (estWord v) r.toks⟩

/-- The one thing `est:` values must do: survive a write followed by a read. -/
theorem unitValue_estWord (bm v : Nat) : unitValue bm ((estWord v).drop 4) = some v := by
  have hdrop : (estWord v).drop 4 = digitsOf v ++ ['m'] := by
    simp [estWord]
  rw [hdrop]
  unfold unitValue
  rw [List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rw [List.reverse_reverse]
  exact readNat_digitsOf v

theorem isEstKey_estWord (v : Nat) : isEstKey (estWord v) = true := by
  simp [isEstKey, estWord]

theorem find_setEstIn (v : Nat) (ts : List Tok) (h : ts.any (fun t => isEstKey t.word) = true) :
    ((setEstIn v ts).find? (fun t => isEstKey t.word)).map Tok.word = some (estWord v) := by
  induction ts with
  | nil => simp at h
  | cons t ts' ih =>
      by_cases hk : isEstKey t.word = true
      · simp only [setEstIn, if_pos hk, List.find?_cons]
        simp [isEstKey_estWord v]
      · simp only [setEstIn, if_neg hk, List.find?_cons]
        simp only [Bool.not_eq_true] at hk
        simp only [hk, Bool.false_eq_true]
        exact ih (by simpa [hk] using h)

theorem find_insertBeforeId (w : List Char) (ts : List Tok) (hn : isEstKey w = true)
    (h : ts.any (fun t => isEstKey t.word) = false) :
    ((insertBeforeId w ts).find? (fun t => isEstKey t.word)).map Tok.word = some w := by
  induction ts with
  | nil => simp [insertBeforeId, hn]
  | cons u us ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      by_cases hid : isIdWord u.word = true
      · by_cases hsep : u.sep.isEmpty = true <;>
          simp [insertBeforeId, hid, hsep, hn]
      · simp only [insertBeforeId, if_neg hid, List.find?_cons]
        simp only [h.1, Bool.false_eq_true]
        exact ih h.2

/-- **The obligation that kills the shipped `tm edit est=` bug.**  In the Rust,
`est:` overrode the leading estimate but `tm edit est=` wrote the *leading*
slot; the command reported success and changed nothing.  A setter is not
exported without this proof. -/
theorem view_set_is_not_silent (bm v : Nat) (r : RawItem) :
    viewRemaining bm (setEst v r) = some v := by
  unfold setEst viewRemaining estKeyTok
  by_cases h : hasEst r = true
  · rw [if_pos h]
    have := find_setEstIn v r.toks (by simpa [hasEst] using h)
    cases hf : (setEstIn v r.toks).find? (fun t => isEstKey t.word) with
    | none => rw [hf] at this; simp at this
    | some t =>
        rw [hf] at this
        simp only [Option.map_some, Option.some.injEq] at this
        simp only [this]
        exact unitValue_estWord bm v
  · simp only [Bool.not_eq_true] at h
    rw [if_neg (by simp [h])]
    have hn : isEstKey (estWord v) = true := isEstKey_estWord v
    have := find_insertBeforeId (estWord v) r.toks hn (by simpa [hasEst] using h)
    cases hf : (insertBeforeId (estWord v) r.toks).find? (fun t => isEstKey t.word) with
    | none => rw [hf] at this; simp at this
    | some t =>
        rw [hf] at this
        simp only [Option.map_some, Option.some.injEq] at this
        simp only [this]
        exact unitValue_estWord bm v

/-- Replace the *leading* estimate token's word — the slot `tm edit est=`
actually wrote. -/
def setLeadWord (w : List Char) (r : RawItem) : RawItem :=
  match r.toks with
  | []      => r
  | t :: ts =>
    if isCiWord t.word then
      match ts with
      | []       => r
      | u :: us  => ⟨r.indent, t :: ⟨u.sep, w⟩ :: us⟩
    else ⟨r.indent, ⟨t.sep, w⟩ :: ts⟩

/-- **The shipped bug, as a theorem.**  With an `est:` token present, writing
the leading estimate changes nothing the kernel reads.  Lean will not let you
export `setLeadWord` as "edit the estimate", because it cannot be given the
`view ∘ set = id` proof above. -/
theorem lead_edit_is_silent :
    ∃ (r : RawItem) (w : List Char) (bm : Nat),
      viewRemaining bm (setLeadWord w r) = viewRemaining bm r ∧
      viewRemaining bm r ≠ unitValue bm w := by
  refine ⟨⟨[], [⟨[' '], ['6', 'b']⟩, ⟨[' '], ['e','s','t',':','1','b']⟩,
              ⟨[' '], ['^','m','1']⟩]⟩, ['3', 'b'], 90, ?_, ?_⟩ <;> decide

/-! ## The setters preserve `CanonicalItem`

This module's header used to record a gap: that the setters preserve
`CanonicalItem` was not proved, and was **false** for `setEst`'s insert branch.
That was not a missing proof, it was a bug — the counterexample is one command
away from a line the kernel accepts (`- [ ]^m1`, whose id token has no
separator).  `insertBeforeId` now places the inserted word so that no two words
can run together, and the obligation is discharged here.

The payoff is `setEst_line_reparses`: whatever `tm edit ^id est=v` writes, the
kernel reads back as the same item, with the same id and the same box. -/

theorem tok_wf_iff (t : Tok) : t.wf = true ↔
    (t.sep.all isSp = true ∧ t.word.isEmpty = false ∧ t.word.all (fun c => !isSp c) = true) := by
  simp [Tok.wf, and_assoc]

theorem digitsOf_no_space (v : Nat) : ∀ c ∈ digitsOf v, isSp c = false := by
  intro c hc
  have hd := digitsOf_all_digits v c hc
  by_cases h : c = ' '
  · subst h; simp [charDigit] at hd
  · simpa [isSp] using h

theorem estWord_ne_nil (v : Nat) : (estWord v).isEmpty = false := by simp [estWord]

theorem estWord_no_space (v : Nat) : (estWord v).all (fun c => !isSp c) = true := by
  simp only [estWord, List.all_eq_true]
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · rcases List.mem_append.1 h with h1 | h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl | rfl <;> rfl
    · simp [digitsOf_no_space v c h1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; rfl

theorem estWord_not_id (v : Nat) : isIdWord (estWord v) = false := by simp [isIdWord, estWord]

theorem est_tok_wf (v : Nat) (sp : List Char) (hsp : sp.all isSp = true) :
    (⟨sp, estWord v⟩ : Tok).wf = true :=
  (tok_wf_iff _).2 ⟨hsp, estWord_ne_nil v, estWord_no_space v⟩

/-- `toksWf` does not care what the head's separator is, only that it is
spaces — which is what lets `insertBeforeId` hand the id token a space. -/
theorem toksWf_head_sep (t : Tok) (sp : List Char) (hsp : sp.all isSp = true) (ts : List Tok)
    (h : toksWf (t :: ts) = true) : toksWf (⟨sp, t.word⟩ :: ts) = true := by
  have ht : t.wf = true := by
    cases ts with
    | nil => simpa [toksWf] using h
    | cons u r => simp only [toksWf, Bool.and_eq_true] at h; exact h.1.1
  have ht' : (⟨sp, t.word⟩ : Tok).wf = true :=
    (tok_wf_iff _).2 ⟨hsp, ((tok_wf_iff t).1 ht).2.1, ((tok_wf_iff t).1 ht).2.2⟩
  cases ts with
  | nil => simpa [toksWf] using ht'
  | cons u r =>
      simp only [toksWf, Bool.and_eq_true] at h ⊢
      exact ⟨⟨ht', h.1.2⟩, h.2⟩

theorem insertBeforeId_head (w : List Char) (u : Tok) (us : List Tok)
    (hsep : u.sep.isEmpty = false) :
    ∃ v vs, insertBeforeId w (u :: us) = v :: vs ∧ v.sep.isEmpty = false := by
  unfold insertBeforeId
  by_cases hid : isIdWord u.word = true
  · rw [if_pos hid, if_neg (by simp [hsep])]
    exact ⟨_, _, rfl, by simp⟩
  · rw [if_neg hid]
    exact ⟨u, _, rfl, hsep⟩

theorem toksWf_insertBeforeId (v : Nat) : ∀ ts : List Tok, toksWf ts = true →
    ts.any (fun t => isIdWord t.word) = true → toksWf (insertBeforeId (estWord v) ts) = true := by
  intro ts
  induction ts with
  | nil => intro _ hid; simp at hid
  | cons u us ih =>
      intro h hid
      unfold insertBeforeId
      by_cases hidu : isIdWord u.word = true
      · rw [if_pos hidu]
        by_cases hsep : u.sep.isEmpty = true
        · rw [if_pos hsep]
          simp only [toksWf, Bool.and_eq_true]
          refine ⟨⟨est_tok_wf v [] rfl, by simp⟩, ?_⟩
          exact toksWf_head_sep u [' '] rfl us h
        · rw [if_neg hsep]
          simp only [toksWf, Bool.and_eq_true]
          exact ⟨⟨est_tok_wf v [' '] rfl, by simpa using hsep⟩, h⟩
      · rw [if_neg hidu]
        have husid : us.any (fun t => isIdWord t.word) = true := by
          simp only [List.any_cons, Bool.or_eq_true] at hid
          rcases hid with hc | hc
          · exact absurd hc hidu
          · exact hc
        cases us with
        | nil => simp at husid
        | cons x r =>
            simp only [toksWf, Bool.and_eq_true] at h
            obtain ⟨y, ys, hy, hys⟩ :=
              insertBeforeId_head (estWord v) x r (by simpa using h.1.2)
            rw [hy]
            simp only [toksWf, Bool.and_eq_true]
            refine ⟨⟨h.1.1, by simpa using hys⟩, ?_⟩
            have := ih h.2 husid
            rwa [hy] at this

theorem toksWf_setEstIn (v : Nat) : ∀ ts : List Tok, toksWf ts = true →
    toksWf (setEstIn v ts) = true := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons u us ih =>
      intro h
      unfold setEstIn
      by_cases hk : isEstKey u.word = true
      · rw [if_pos hk]
        have hu : u.wf = true := by
          cases us with
          | nil => simpa [toksWf] using h
          | cons x r => simp only [toksWf, Bool.and_eq_true] at h; exact h.1.1
        have hnew : (⟨u.sep, estWord v⟩ : Tok).wf = true :=
          est_tok_wf v u.sep ((tok_wf_iff u).1 hu).1
        cases us with
        | nil => simpa [toksWf] using hnew
        | cons x r =>
            simp only [toksWf, Bool.and_eq_true] at h ⊢
            exact ⟨⟨hnew, h.1.2⟩, h.2⟩
      · rw [if_neg hk]
        cases us with
        | nil => simpa [toksWf, setEstIn] using h
        | cons x r =>
            simp only [toksWf, Bool.and_eq_true] at h
            have hset : ∃ y ys, setEstIn v (x :: r) = y :: ys ∧ y.sep = x.sep := by
              unfold setEstIn
              by_cases hkx : isEstKey x.word = true
              · rw [if_pos hkx]; exact ⟨⟨x.sep, estWord v⟩, r, rfl, rfl⟩
              · rw [if_neg hkx]; exact ⟨x, setEstIn v r, rfl, rfl⟩
            obtain ⟨y, ys, hy, hysep⟩ := hset
            rw [hy]
            simp only [toksWf, Bool.and_eq_true]
            refine ⟨⟨h.1.1, ?_⟩, ?_⟩
            · rw [hysep]; exact h.1.2
            · have := ih h.2
              rwa [hy] at this

theorem idWords_insertBeforeId (v : Nat) : ∀ ts : List Tok,
    ((insertBeforeId (estWord v) ts).filter (fun t => isIdWord t.word)).map Tok.word
      = (ts.filter (fun t => isIdWord t.word)).map Tok.word := by
  intro ts
  induction ts with
  | nil => simp [insertBeforeId, estWord_not_id v]
  | cons u us ih =>
      unfold insertBeforeId
      by_cases hid : isIdWord u.word = true
      · by_cases hsep : u.sep.isEmpty = true <;>
          simp [hid, hsep, estWord_not_id v]
      · rw [if_neg hid]
        simp only [List.filter_cons, hid, Bool.false_eq_true, if_false]
        exact ih

theorem estKey_not_id (w : List Char) (h : isEstKey w = true) : isIdWord w = false := by
  cases w with
  | nil => simp [isEstKey] at h
  | cons a t =>
      have ha : a = 'e' := by
        simp only [isEstKey, List.take_succ_cons, beq_iff_eq, List.cons.injEq] at h
        exact h.1
      subst ha
      rfl

theorem idWords_setEstIn (v : Nat) : ∀ ts : List Tok,
    ((setEstIn v ts).filter (fun t => isIdWord t.word)).map Tok.word
      = (ts.filter (fun t => isIdWord t.word)).map Tok.word := by
  intro ts
  induction ts with
  | nil => rfl
  | cons u us ih =>
      unfold setEstIn
      by_cases hk : isEstKey u.word = true
      · rw [if_pos hk]
        simp [estKey_not_id u.word hk, estWord_not_id v]
      · rw [if_neg hk]
        by_cases hid : isIdWord u.word = true <;> simp [hid, ih]

theorem canonical_iff (i : Id) (r : RawItem) : CanonicalItem i r = true ↔
    (r.indent.all isSp = true ∧ toksWf r.toks = true ∧
      (idToks r).map Tok.word = ['^' :: i]) := by
  unfold CanonicalItem idToks
  cases r.toks.filter (fun t => isIdWord t.word) with
  | nil => simp
  | cons t rest =>
      cases rest with
      | cons u rs => simp
      | nil => simp [and_assoc]

/-- **The obligation the header used to defer.**  `tm edit ^id est=v` takes a
canonical line to a canonical line — the id token survives, every token stays
well shaped, and no two words run together. -/
theorem setEst_canonical (i : Id) (v : Nat) (r : RawItem) (h : CanonicalItem i r = true) :
    CanonicalItem i (setEst v r) = true := by
  obtain ⟨hind, htw, hids⟩ := (canonical_iff i r).1 h
  refine (canonical_iff i (setEst v r)).2 ⟨?_, ?_, ?_⟩
  · unfold setEst; by_cases hE : hasEst r = true <;> simp [hE, hind]
  · unfold setEst
    by_cases hE : hasEst r = true
    · simp only [hE, if_pos]
      exact toksWf_setEstIn v r.toks htw
    · simp only [Bool.not_eq_true] at hE
      rw [if_neg (by simp [hE])]
      refine toksWf_insertBeforeId v r.toks htw ?_
      -- the line has an id token, because `idToks r` is a singleton
      unfold idToks at hids
      cases hf : r.toks.filter (fun t => isIdWord t.word) with
      | nil => rw [hf] at hids; simp at hids
      | cons t rest =>
          have hm : t ∈ r.toks.filter (fun x => isIdWord x.word) := by rw [hf]; simp
          have := (List.mem_filter.1 hm).2
          simp only [List.any_eq_true]
          exact ⟨t, (List.mem_filter.1 hm).1, this⟩
  · unfold setEst idToks
    by_cases hE : hasEst r = true
    · simp only [hE, if_pos]
      rw [idWords_setEstIn v r.toks]
      exact hids
    · simp only [Bool.not_eq_true] at hE
      rw [if_neg (by simp [hE])]
      rw [idWords_insertBeforeId v r.toks]
      exact hids

/-- **The payoff, and the answer to "one command from an accepted input".**
Serialise what `tm edit ^id est=v` produced and the kernel parses it back to the
same item: same id, same box, same tokens. -/
theorem setEst_line_reparses (i : Id) (g : Glyph) (v : Nat) (r : RawItem)
    (h : CanonicalItem i r = true) :
    parseItem (serializeItem i g (setEst v r)) = .ok (i, g, setEst v r) :=
  parse_serialize i g (setEst v r) (setEst_canonical i v r h)

end Tm
