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

**The setters preserve `CanonicalItem`, and that is proved here**, not
deferred: see `setEst_canonical` below.  Both branches are covered — the
replace branch, and the insert branch that once produced a line the kernel
could not parse back, by inserting a token before an id token that was the
line's first and leaving it without the separator it needs.  `CanonicalItem`
is decidable as well, so a host can check a line it did not get from us.
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



/-!
# §4.1's field grammar

Everything above this point treats a token as bytes.  This half reads them:
§4.1's nineteen `key:value` spellings, its five flags, the two positional slots
and the four sigils, each with the value grammar the table gives it.

**The shape of the claim.**  Round trip A — bytes → tokens → the same bytes —
is `serialize_parse` above, and it is free, because the token vector *is* the
bytes.  What this half has to earn is the other direction at the level of
*fields*:

* a value the kernel writes is the value it reads back — `parse_render_*`, one
  per key;
* a field a setter writes is the field the view reports — `view_set_*`, one
  per field, the family the shipped `tm edit est=` bug is a missing member of;
* and, over the whole line, `viewFields (renderItem i f) = f` — round trip B
  at the level of fields (`field_round_trip`), by induction over the token
  grammar.

**Two rules from §4.1 that are easy to lose**, and are theorems here:

* an unknown `key:` is **preserved verbatim and reported**, never dropped;
* a word the parser cannot classify **stays in the title**.

The value types live in `Tm.Field`, not `Tm`.  §3.1's own copies
(`Tm.Shape`, `Tm.Recur`, `Tm.Rule`, …) are declared in `State.lean`, which
imports this file, so the grammar cannot name them; `Tm.Field.Shape` and the
rest are the same data one module earlier.  Joining the two is a map per
constructor and it belongs in `State.lean` — see the README's gap list.

**A note on style that is load-bearing.**  Definitions here use `Option.bind`,
`Option.map` and `if` rather than `match` on a computed scrutinee.  A `match`
whose scrutinee is a rewritten term does not reduce under `rw`, and the proofs
below rewrite scrutinees constantly; `bind` keeps every one of them a one-step
`Option.bind_some`.
-/
namespace Tm
namespace Field

/-! ## Character classes

The four alphabets §4.1 and `grammar.rs` actually use: decimal digits,
`[a-z-]` for a key, `[A-Za-z0-9_-]` for an id or an event name, and the four
sigils. -/

def isDigitC (c : Char) : Bool := (charDigit c).isSome
/-- Character classes are stated on `Char.toNat`, not on `Char`'s `≤`: the
disjointness lemmas below (`upper_not_lower`, `digit_not_lower`, …) are what
the round-trip case splits run on, and on `Nat` they are `omega`. -/
def isLowerC (c : Char) : Bool := decide (97 ≤ c.toNat ∧ c.toNat ≤ 122)
def isUpperC (c : Char) : Bool := decide (65 ≤ c.toNat ∧ c.toNat ≤ 90)
def isAlnumC (c : Char) : Bool := isDigitC c || isLowerC c || isUpperC c

/-- Which characters `charDigit` accepts, spelled out — the bridge from the
numeral reader to the arithmetic classes. -/
theorem isDigitC_cases {c : Char} (h : isDigitC c = true) :
    c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨
    c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
  unfold isDigitC charDigit at h
  split at h <;> simp_all

theorem upper_not_lower : ∀ c : Char, isUpperC c = true → isLowerC c = false := by
  intro c h
  simp only [isUpperC, decide_eq_true_eq] at h
  simp only [isLowerC, decide_eq_false_iff_not]
  omega

theorem upper_not_digit : ∀ c : Char, isUpperC c = true → isDigitC c = false := by
  intro c h
  by_cases hd : isDigitC c = true
  · rcases isDigitC_cases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (revert h; decide)
  · simpa using hd

theorem digit_not_lower : ∀ c : Char, isDigitC c = true → isLowerC c = false := by
  intro c h
  rcases isDigitC_cases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem digit_not_upper : ∀ c : Char, isDigitC c = true → isUpperC c = false := by
  intro c h
  rcases isDigitC_cases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- `Id::is_valid`'s alphabet: alphanumeric plus `_` and `-`. -/
def isNameC (c : Char) : Bool := isAlnumC c || c == '_' || c == '-'

/-- `key_prefix`'s alphabet: `[a-z-]`. -/
def isKeyC (c : Char) : Bool := isLowerC c || c == '-'

/-- A non-empty word over the id alphabet (`Id::is_valid`). -/
def isName (w : List Char) : Bool := !w.isEmpty && w.all isNameC

theorem isName_all {w : List Char} (h : isName w = true) : w.all isNameC = true := by
  unfold isName at h; simp only [Bool.and_eq_true] at h; exact h.2

theorem isName_ne_nil {w : List Char} (h : isName w = true) : w ≠ [] := by
  unfold isName at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hc; rw [hc] at h; simp at h

theorem isNameC_ne {c : Char} (h : isNameC c = true) :
    c ≠ ':' ∧ c ≠ ',' ∧ c ≠ '/' ∧ c ≠ '~' ∧ c ≠ '^' ∧ c ≠ ' ' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro hc; subst hc; revert h; decide)

theorem isName_avoids {w : List Char} (h : isName w = true) (c : Char) (hc : c ∈ w) :
    c ≠ ':' ∧ c ≠ ',' ∧ c ≠ '/' ∧ c ≠ '~' ∧ c ≠ '^' ∧ c ≠ ' ' :=
  isNameC_ne (List.all_eq_true.1 (isName_all h) c hc)

theorem isName_no_space {w : List Char} (h : isName w = true) : ∀ c ∈ w, isSp c = false := by
  intro c hc
  have := (isName_avoids h c hc).2.2.2.2.2
  simpa [isSp] using this

/-! ## The keys

Eighteen fields, nineteen spellings: `cap:` is an alias of `max:` (§4.1's table
lists it, `build_item` folds it).  The enum is named for the **field**, so the
alias has nowhere to hide — `Key.cap` is the budget cap and its canonical
spelling is `max`.

`at` is a Lean keyword, so the four keys whose spelling collides are named for
what they mean: `interval` is `at:`, `window` is `win:`, `floor` is `min:`,
`cap` is `max:`/`cap:`. -/

inductive Key
  | due | interval | window | dur | pref | every | afterDone | onEvent | onMiss
  | floor | cap | after | loc | est | demoted | waiting | buffer | ci
deriving DecidableEq, Repr, Inhabited

/-- The spelling the kernel *writes*. -/
def Key.name : Key → List Char
  | .due => ['d','u','e']
  | .interval => ['a','t']
  | .window => ['w','i','n']
  | .dur => ['d','u','r']
  | .pref => ['p','r','e','f']
  | .every => ['e','v','e','r','y']
  | .afterDone => ['a','f','t','e','r','-','d','o','n','e']
  | .onEvent => ['o','n','-','e','v','e','n','t']
  | .onMiss => ['o','n','-','m','i','s','s']
  | .floor => ['m','i','n']
  | .cap => ['m','a','x']
  | .after => ['a','f','t','e','r']
  | .loc => ['l','o','c']
  | .est => ['e','s','t']
  | .demoted => ['d','e','m','o','t','e','d']
  | .waiting => ['w','a','i','t','i','n','g']
  | .buffer => ['b','u','f','f','e','r']
  | .ci => ['c','i']

/-- Every spelling the kernel *reads*, the `cap:` alias included. -/
def Key.ofName? (w : List Char) : Option Key :=
  match w with
  | ['d','u','e'] => some .due
  | ['a','t'] => some .interval
  | ['w','i','n'] => some .window
  | ['d','u','r'] => some .dur
  | ['p','r','e','f'] => some .pref
  | ['e','v','e','r','y'] => some .every
  | ['a','f','t','e','r','-','d','o','n','e'] => some .afterDone
  | ['o','n','-','e','v','e','n','t'] => some .onEvent
  | ['o','n','-','m','i','s','s'] => some .onMiss
  | ['m','i','n'] => some .floor
  | ['m','a','x'] => some .cap
  | ['a','f','t','e','r'] => some .after
  | ['l','o','c'] => some .loc
  | ['e','s','t'] => some .est
  | ['d','e','m','o','t','e','d'] => some .demoted
  | ['w','a','i','t','i','n','g'] => some .waiting
  | ['b','u','f','f','e','r'] => some .buffer
  | ['c','i'] => some .ci
  | ['c','a','p'] => some .cap
  | _ => none


/-- The nineteenth spelling has no field of its own — and writing normalises
it, so `cap:4h/w` becomes `max:4h/w` the moment anything edits the line. -/
theorem cap_is_an_alias_of_max : Key.ofName? ['c','a','p'] = Key.ofName? ['m','a','x'] := rfl

theorem cap_writes_as_max : Key.name .cap = ['m','a','x'] := rfl

/-- Every key the kernel writes, it reads back as the same key. -/
theorem key_name_roundtrip (k : Key) : Key.ofName? (Key.name k) = some k := by
  cases k <;> rfl

theorem key_name_isKey (k : Key) : (Key.name k).all isKeyC = true := by
  cases k <;> decide

theorem key_name_ne_nil (k : Key) : Key.name k ≠ [] := by
  cases k <;> decide

theorem key_name_avoids (k : Key) (c : Char) (hc : c ∈ Key.name k) :
    c ≠ ':' ∧ isSp c = false := by
  have hk := List.all_eq_true.1 (key_name_isKey k) c hc
  constructor
  · intro h; subst h; revert hk; decide
  · by_cases h : c = ' '
    · subst h; revert hk; decide
    · simpa [isSp] using h

/-! ## The flags

`open` is a Lean keyword, so the constructor follows `Scope.openEnded`'s
precedent in `State.lean`. -/

inductive Flag | openEnded | atomic | manual | travelDay | hot
deriving DecidableEq, Repr, Inhabited

def Flag.name : Flag → List Char
  | .openEnded => ['o','p','e','n']
  | .atomic => ['a','t','o','m','i','c']
  | .manual => ['m','a','n','u','a','l']
  | .travelDay => ['t','r','a','v','e','l','-','d','a','y']
  | .hot => ['h','o','t']

def Flag.ofName? (w : List Char) : Option Flag :=
  match w with
  | ['o','p','e','n'] => some .openEnded
  | ['a','t','o','m','i','c'] => some .atomic
  | ['m','a','n','u','a','l'] => some .manual
  | ['t','r','a','v','e','l','-','d','a','y'] => some .travelDay
  | ['h','o','t'] => some .hot
  | _ => none


theorem flag_name_roundtrip (f : Flag) : Flag.ofName? (Flag.name f) = some f := by
  cases f <;> rfl

theorem flag_name_ne_nil (f : Flag) : Flag.name f ≠ [] := by cases f <;> decide

theorem flag_name_no_space (f : Flag) : ∀ c ∈ Flag.name f, isSp c = false := by
  intro c hc
  have h : ∀ g : Flag, (Flag.name g).all (fun x => !isSp x) = true := by intro g; cases g <;> decide
  have := List.all_eq_true.1 (h f) c hc
  simpa using this

/-- A flag never carries a colon, so it is never mistaken for a `key:value`. -/
theorem flag_name_no_colon (f : Flag) : ∀ c ∈ Flag.name f, c ≠ ':' := by
  intro c hc
  have h : ∀ g : Flag, (Flag.name g).all (fun x => !(x == ':')) = true := by
    intro g; cases g <;> decide
  have := List.all_eq_true.1 (h f) c hc
  simpa using this

/-! ## Durations

§4.1's `Nb | Nm | Nh`, plus `grammar.rs`'s `Nd` and `NhMm`.  The **unit is part
of the value**, because §4.1 says a rewrite keeps "the original estimate unit";
`Dur.minutes` is the reading and takes `block_min` as an argument, so nothing
inside the kernel is a block. -/

inductive DurUnit | blocks | minutes | hours | days
deriving DecidableEq, Repr, Inhabited

def DurUnit.char : DurUnit → Char
  | .blocks => 'b' | .minutes => 'm' | .hours => 'h' | .days => 'd'

inductive Dur
  | simple (n : Nat) (u : DurUnit)
  | hm (h m : Nat)
deriving DecidableEq, Repr, Inhabited

/-- The reading, in minutes.  `b` is the only unit that needs configuration. -/
def Dur.minutes (blockMin : Nat) : Dur → Nat
  | .simple n .blocks  => n * blockMin
  | .simple n .minutes => n
  | .simple n .hours   => n * 60
  | .simple n .days    => n * 1440
  | .hm h m            => h * 60 + m

/-- `est:`, `dur:` and the leading estimate reject `Nd` (`parse_no_days`). -/
def Dur.noDays : Dur → Bool
  | .simple _ .days => false
  | _               => true

def renderDur : Dur → List Char
  | .simple n u => digitsOf n ++ [DurUnit.char u]
  | .hm h m     => digitsOf h ++ 'h' :: (digitsOf m ++ ['m'])

/-- `NhMm`: the tail after the `h`. -/
def hmOf (k : Nat) (t : List Char) : Option Dur :=
  if t.getLast? = some 'm' then (readNat t.dropLast).map (fun m => Dur.hm k m) else none

def durTail (k : Nat) (rest : List Char) : Option Dur :=
  if rest = ['b'] then some (.simple k .blocks)
  else if rest = ['m'] then some (.simple k .minutes)
  else if rest = ['h'] then some (.simple k .hours)
  else if rest = ['d'] then some (.simple k .days)
  else if rest.head? = some 'h' then hmOf k rest.tail
  else none

def parseDur (w : List Char) : Option Dur :=
  (readNat (w.takeWhile isDigitC)).bind (fun k => durTail k (w.dropWhile isDigitC))

def parseDurND (w : List Char) : Option Dur :=
  (parseDur w).bind (fun d => if d.noDays then some d else none)

theorem digitsOf_isDigitC (n : Nat) : ∀ x ∈ digitsOf n, isDigitC x = true := by
  intro x hx; simpa [isDigitC] using digitsOf_all_digits n x hx

theorem hmOf_concat (k : Nat) (m : Nat) : hmOf k (digitsOf m ++ ['m']) = some (Dur.hm k m) := by
  unfold hmOf
  rw [List.getLast?_concat, if_pos rfl, List.dropLast_concat, readNat_digitsOf]
  rfl

/-- **The duration round trip.**  `6b`, `90m`, `2h`, `3d` and `2h30m` all come
back as themselves, unit included. -/
theorem parse_render_dur (d : Dur) : parseDur (renderDur d) = some d := by
  cases d with
  | simple n u =>
      have hh : ∀ x, ([DurUnit.char u] : List Char).head? = some x → isDigitC x = false := by
        intro x hx
        simp only [List.head?_cons, Option.some.injEq] at hx
        subst hx; cases u <;> rfl
      have hs := takeWhile_append_all isDigitC (digitsOf n) [DurUnit.char u]
        (digitsOf_isDigitC n) hh
      show parseDur (digitsOf n ++ [DurUnit.char u]) = _
      unfold parseDur
      rw [hs.1, hs.2, readNat_digitsOf]
      simp only [Option.bind_some]
      cases u <;> rfl
  | hm h m =>
      have hh : ∀ x, (('h' :: (digitsOf m ++ ['m'])) : List Char).head? = some x →
          isDigitC x = false := by
        intro x hx
        simp only [List.head?_cons, Option.some.injEq] at hx
        subst hx; rfl
      have hs := takeWhile_append_all isDigitC (digitsOf h) ('h' :: (digitsOf m ++ ['m']))
        (digitsOf_isDigitC h) hh
      show parseDur (digitsOf h ++ 'h' :: (digitsOf m ++ ['m'])) = _
      unfold parseDur
      rw [hs.1, hs.2, readNat_digitsOf]
      simp only [Option.bind_some]
      unfold durTail
      have h1 : ('h' :: (digitsOf m ++ ['m'])) ≠ ['b'] := by simp
      have h2 : ('h' :: (digitsOf m ++ ['m'])) ≠ ['m'] := by simp
      have h3 : ('h' :: (digitsOf m ++ ['m'])) ≠ ['h'] := by
        intro hc
        have : digitsOf m ++ ['m'] = [] := by simpa using hc
        simp at this
      have h4 : ('h' :: (digitsOf m ++ ['m'])) ≠ ['d'] := by simp
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos (by rfl : ('h' :: (digitsOf m ++ ['m'])).head? = some 'h')]
      show hmOf h (digitsOf m ++ ['m']) = _
      exact hmOf_concat h m

theorem parse_render_durND (d : Dur) (h : d.noDays = true) : parseDurND (renderDur d) = some d := by
  unfold parseDurND
  rw [parse_render_dur d]
  simp only [Option.bind_some, h, if_pos]

theorem renderDur_ne_nil (d : Dur) : renderDur d ≠ [] := by
  cases d with
  | simple n u =>
      cases hd : digitsOf n with
      | nil => exact absurd hd (digitsOf_ne_nil n)
      | cons a t => simp [renderDur, hd]
  | hm h m =>
      cases hd : digitsOf h with
      | nil => exact absurd hd (digitsOf_ne_nil h)
      | cons a t => simp [renderDur, hd]

/-- Every character a duration writes: digits and the four unit letters.  This
is what keeps a duration safe inside a comma list, a `~` pair and a token. -/
theorem renderDur_chars (d : Dur) : ∀ c ∈ renderDur d,
    isDigitC c = true ∨ c = 'b' ∨ c = 'm' ∨ c = 'h' ∨ c = 'd' := by
  cases d with
  | simple n u =>
      intro c hc
      rcases List.mem_append.1 hc with h | h
      · exact Or.inl (digitsOf_isDigitC n c h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h; cases u <;> decide
  | hm h m =>
      intro c hc
      rcases List.mem_append.1 hc with h1 | h1
      · exact Or.inl (digitsOf_isDigitC h c h1)
      · simp only [List.mem_cons] at h1
        rcases h1 with rfl | h1
        · decide
        · rcases List.mem_append.1 h1 with h2 | h2
          · exact Or.inl (digitsOf_isDigitC m c h2)
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            subst h2; decide

theorem renderDur_head_digit (d : Dur) :
    ∃ c, (renderDur d).head? = some c ∧ isDigitC c = true := by
  cases d with
  | simple n u =>
      cases hd : digitsOf n with
      | nil => exact absurd hd (digitsOf_ne_nil n)
      | cons a t =>
          exact ⟨a, by simp [renderDur, hd], digitsOf_isDigitC n a (by rw [hd]; simp)⟩
  | hm h m =>
      cases hd : digitsOf h with
      | nil => exact absurd hd (digitsOf_ne_nil h)
      | cons a t =>
          exact ⟨a, by simp [renderDur, hd], digitsOf_isDigitC h a (by rw [hd]; simp)⟩

/-! ## Clock times

`win:11:30-13:30`, `pref:12:00`: minutes since midnight, bounded, so `25:00` is
not a value this kernel can hold — the move `State.lean` makes for `Clock`. -/

abbrev Clock := Fin 1440

def mkClock? (h m : Nat) : Option Clock :=
  if hh : h < 24 ∧ m < 60 then some ⟨h * 60 + m, by omega⟩ else none

def renderClock (c : Clock) : List Char := padTo 2 (c.val / 60) ++ ':' :: padTo 2 (c.val % 60)

def parseClock (w : List Char) : Option Clock :=
  (splitFirst ':' w).bind (fun p =>
    if p.1.length = 2 ∧ p.2.length = 2 then
      (readNat p.1).bind (fun h => (readNat p.2).bind (fun m => mkClock? h m))
    else none)

theorem clock_rejects_2500 : parseClock ['2','5',':','0','0'] = none := by decide
theorem clock_rejects_minute_60 : parseClock ['1','1',':','6','0'] = none := by decide
theorem clock_rejects_unpadded : parseClock ['9',':','0','5'] = none := by decide
theorem clock_reads_1130 : (parseClock ['1','1',':','3','0']).map Fin.val = some 690 := by decide

theorem padTo2_length (n : Nat) (h : n < 100) : (padTo 2 n).length = 2 :=
  padTo_length 2 n (by
    have h2 : n < 10 ^ (1 + 1) := by simpa using h
    have := digitsOf_length_le 1 n h2
    omega)

theorem padTo_digits (w n : Nat) : ∀ c ∈ padTo w n, isDigitC c = true := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · rw [zeros_all_zero _ c h]; rfl
  · exact digitsOf_isDigitC n c h

theorem padTo_no_colon (w n : Nat) : ∀ c ∈ padTo w n, c ≠ ':' := by
  intro c hc hcc
  have := padTo_digits w n c hc
  subst hcc; revert this; decide

/-- **The clock round trip.** -/
theorem parse_render_clock (c : Clock) : parseClock (renderClock c) = some c := by
  have hh : c.val / 60 < 24 := by omega
  have hm : c.val % 60 < 60 := by omega
  unfold renderClock parseClock
  rw [splitFirst_append ':' (padTo 2 (c.val / 60)) (padTo 2 (c.val % 60))
        (padTo_no_colon 2 (c.val / 60))]
  simp only [Option.bind_some]
  rw [if_pos (And.intro (padTo2_length _ (by omega)) (padTo2_length _ (by omega)))]
  rw [readNat_padTo, readNat_padTo]
  simp only [Option.bind_some]
  unfold mkClock?
  rw [dif_pos (And.intro hh hm)]
  have hv : c.val / 60 * 60 + c.val % 60 = c.val := by omega
  simp [Fin.ext_iff, hv]

theorem renderClock_length (c : Clock) : (renderClock c).length = 5 := by
  unfold renderClock
  rw [List.length_append, List.length_cons, padTo2_length _ (by omega),
    padTo2_length _ (by omega)]

theorem renderClock_chars (c : Clock) : ∀ x ∈ renderClock c, isDigitC x = true ∨ x = ':' := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact Or.inl (padTo_digits 2 _ x h)
  · simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (padTo_digits 2 _ x h)

theorem renderClock_head_digit (c : Clock) :
    ∃ x, (renderClock c).head? = some x ∧ isDigitC x = true := by
  unfold renderClock
  cases hp : padTo 2 (c.val / 60) with
  | nil => exact absurd hp (padTo_ne_nil 2 _)
  | cons a t =>
      refine ⟨a, by simp, padTo_digits 2 _ a (by rw [hp]; simp)⟩


/-! ## Dates

`due:2026-09-11` is `Cal`'s calendar, not a second one: a date **is** a day
number, and `Cal.ofDay` / `Cal.toDay` is the proved bijection between the two.
`parseDate` therefore cannot accept 2026-02-30, and nothing here re-derives a
leap rule.

Widths are checked the way `parse_date` checks them (`s.len() != 10`), so
`2026-9-11` is not a date — which means the round trip needs the year to fit
in four digits.  `dayWf` is that side condition, decidable, and stated rather
than assumed. -/

/-- Decidable: this day number's year fits the four-digit field. -/
def dayWf (n : Nat) : Bool := decide ((Cal.ofDay n).year < 10000)

theorem ofDay_month_bounds (n : Nat) : 1 ≤ (Cal.ofDay n).month ∧ (Cal.ofDay n).month < 100 := by
  have h := (Cal.valid_iff _).1 (Cal.ofDay_valid n)
  omega

theorem ofDay_day_bounds (n : Nat) : 1 ≤ (Cal.ofDay n).day ∧ (Cal.ofDay n).day < 100 := by
  have h := (Cal.valid_iff _).1 (Cal.ofDay_valid n)
  have hm : (Cal.ofDay n).month < 13 := by omega
  have := Cal.monthLen_le_31 (Cal.isLeap (Cal.ofDay n).year) hm
  omega

theorem padTo4_length (n : Nat) (h : n < 10000) : (padTo 4 n).length = 4 :=
  padTo_length 4 n (by
    have hp : (10 : Nat) ^ (3 + 1) = 10000 := rfl
    have h2 : n < 10 ^ (3 + 1) := by rw [hp]; exact h
    have := digitsOf_length_le 3 n h2
    omega)

theorem padTo_not_char (w n : Nat) (x : Char) (hx : isDigitC x = false) :
    ∀ c ∈ padTo w n, c ≠ x := by
  intro c hc hcx
  subst hcx
  rw [padTo_digits w n c hc] at hx
  exact Bool.noConfusion hx

def renderDate (n : Nat) : List Char :=
  padTo 4 (Cal.ofDay n).year ++
    '-' :: (padTo 2 (Cal.ofDay n).month ++ '-' :: padTo 2 (Cal.ofDay n).day)

def mkDate? (y m d : Nat) : Option Nat :=
  if Cal.Date.valid ⟨y, m, d⟩ then some (Cal.toDay ⟨y, m, d⟩) else none

def parseDate (w : List Char) : Option Nat :=
  (splitFirst '-' w).bind (fun p =>
    (splitFirst '-' p.2).bind (fun q =>
      if p.1.length = 4 ∧ q.1.length = 2 ∧ q.2.length = 2 then
        (readNat p.1).bind (fun y =>
          (readNat q.1).bind (fun m =>
            (readNat q.2).bind (fun d => mkDate? y m d)))
      else none))

theorem date_rejects_feb30 : parseDate ['2','0','2','4','-','0','2','-','3','0'] = none := by decide
theorem date_accepts_feb29_2024 :
    parseDate ['2','0','2','4','-','0','2','-','2','9'] = some (Cal.toDay ⟨2024, 2, 29⟩) := by decide
theorem date_rejects_unpadded : parseDate ['2','0','2','6','-','9','-','1','1'] = none := by decide
theorem date_rejects_year_zero : parseDate ['0','0','0','0','-','0','1','-','0','1'] = none := by decide

/-- **The date round trip.** -/
theorem parse_render_date (n : Nat) (h : dayWf n = true) : parseDate (renderDate n) = some n := by
  have hy : (Cal.ofDay n).year < 10000 := by simpa [dayWf] using h
  have hm := ofDay_month_bounds n
  have hd := ofDay_day_bounds n
  unfold renderDate parseDate
  rw [splitFirst_append '-' (padTo 4 (Cal.ofDay n).year)
        (padTo 2 (Cal.ofDay n).month ++ '-' :: padTo 2 (Cal.ofDay n).day)
        (padTo_not_char 4 _ '-' rfl)]
  simp only [Option.bind_some]
  rw [splitFirst_append '-' (padTo 2 (Cal.ofDay n).month) (padTo 2 (Cal.ofDay n).day)
        (padTo_not_char 2 _ '-' rfl)]
  simp only [Option.bind_some]
  rw [if_pos (And.intro (padTo4_length _ hy)
        (And.intro (padTo2_length _ hm.2) (padTo2_length _ hd.2)))]
  rw [readNat_padTo, readNat_padTo, readNat_padTo]
  simp only [Option.bind_some]
  unfold mkDate?
  have hvalid : Cal.Date.valid ⟨(Cal.ofDay n).year, (Cal.ofDay n).month, (Cal.ofDay n).day⟩
      = true := Cal.ofDay_valid n
  rw [if_pos hvalid]
  have : (⟨(Cal.ofDay n).year, (Cal.ofDay n).month, (Cal.ofDay n).day⟩ : Cal.Date)
      = Cal.ofDay n := rfl
  rw [this, Cal.toDay_ofDay]

theorem renderDate_chars (n : Nat) : ∀ c ∈ renderDate n, isDigitC c = true ∨ c = '-' := by
  intro c hc
  unfold renderDate at hc
  rcases List.mem_append.1 hc with h | h
  · exact Or.inl (padTo_digits 4 _ c h)
  · simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr rfl
    · rcases List.mem_append.1 h with h1 | h1
      · exact Or.inl (padTo_digits 2 _ c h1)
      · simp only [List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact Or.inr rfl
        · exact Or.inl (padTo_digits 2 _ c h1)

theorem renderDate_avoid (n : Nat) (x : Char) (h1 : isDigitC x = false) (h2 : x ≠ '-') :
    ∀ c ∈ renderDate n, c ≠ x := by
  intro c hc hcx
  subst hcx
  rcases renderDate_chars n c hc with h | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · exact h2 h

theorem renderDate_head_digit (n : Nat) :
    ∃ c, (renderDate n).head? = some c ∧ isDigitC c = true := by
  unfold renderDate
  cases hp : padTo 4 (Cal.ofDay n).year with
  | nil => exact absurd hp (padTo_ne_nil 4 _)
  | cons a t => exact ⟨a, by simp, padTo_digits 4 _ a (by rw [hp]; simp)⟩

/-! ## Date-times, and §4.1's two `at:` forms

`at:2026-09-07T12:50/13:50` (the short, same-day end) and
`at:…T08:15/2026-09-12T10:40` (the long, cross-day end).  `grammar.rs` picks
the short form when the end is on the start's date, and rolls a short end that
precedes the start to the next day.  Both are here, and the round trip says the
pair survives whichever form was chosen. -/

structure DT where
  day  : Nat
  time : Clock
deriving DecidableEq, Repr, Inhabited

/-- Minutes since the calendar origin — the ordering `at:` needs. -/
def DT.abs (x : DT) : Nat := x.day * 1440 + x.time.val

def DT.wf (x : DT) : Bool := dayWf x.day

def renderDT (x : DT) : List Char := renderDate x.day ++ 'T' :: renderClock x.time

def parseDT (w : List Char) : Option DT :=
  (splitFirst 'T' w).bind (fun p =>
    (parseDate p.1).bind (fun d => (parseClock p.2).map (fun t => DT.mk d t)))

theorem renderDT_chars (x : DT) :
    ∀ c ∈ renderDT x, isDigitC c = true ∨ c = '-' ∨ c = 'T' ∨ c = ':' := by
  intro c hc
  unfold renderDT at hc
  rcases List.mem_append.1 hc with h | h
  · rcases renderDate_chars x.day c h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr (Or.inr (Or.inl rfl))
    · rcases renderClock_chars x.time c h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inr h1))

theorem renderDT_avoid (x : DT) (y : Char) (h1 : isDigitC y = false) (h2 : y ≠ '-')
    (h3 : y ≠ 'T') (h4 : y ≠ ':') : ∀ c ∈ renderDT x, c ≠ y := by
  intro c hc hcy
  subst hcy
  rcases renderDT_chars x c hc with h | h | h | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · exact h2 h
  · exact h3 h
  · exact h4 h

theorem parse_render_DT (x : DT) (h : x.wf = true) : parseDT (renderDT x) = some x := by
  unfold renderDT parseDT
  rw [splitFirst_append 'T' (renderDate x.day) (renderClock x.time)
        (renderDate_avoid x.day 'T' rfl (by decide))]
  simp only [Option.bind_some]
  rw [parse_render_date x.day (by simpa [DT.wf] using h)]
  simp only [Option.bind_some]
  rw [parse_render_clock]
  rfl

/-- A clock is never a date-time: it carries no `T`, so the long form and the
short form cannot be confused. -/
theorem parseDT_clock_none (t : Clock) : parseDT (renderClock t) = none := by
  have hns : splitFirst 'T' (renderClock t) = none := by
    apply splitFirst_none
    intro x hx hxT
    subst hxT
    rcases renderClock_chars t 'T' hx with h | h
    · exact Bool.noConfusion h
    · exact absurd h (by decide)
  unfold parseDT
  rw [hns]
  rfl


/-! ### `due:` — a date or a date-time

§4.1's table: `due:2026-09-11` or `due:2026-09-11T23:59`.  The two are distinct
values and the grammar keeps them apart, because which one was written is what
gets written back. -/

inductive Moment
  | date     (d : Nat)
  | dateTime (d : Nat) (t : Clock)
deriving DecidableEq, Repr, Inhabited

def Moment.day : Moment → Nat
  | .date d       => d
  | .dateTime d _ => d

def Moment.wf : Moment → Bool
  | .date d       => dayWf d
  | .dateTime d _ => dayWf d

def renderMoment : Moment → List Char
  | .date d       => renderDate d
  | .dateTime d t => renderDate d ++ 'T' :: renderClock t

def parseMomentDT (w : List Char) : Option Moment :=
  (splitFirst 'T' w).bind (fun p =>
    (parseDate p.1).bind (fun d => (parseClock p.2).map (fun t => Moment.dateTime d t)))

def parseMoment (w : List Char) : Option Moment :=
  match parseMomentDT w with
  | some m => some m
  | none   => (parseDate w).map Moment.date

/-- **The `due:` round trip**, in both forms. -/
theorem parse_render_moment (m : Moment) (h : m.wf = true) :
    parseMoment (renderMoment m) = some m := by
  cases m with
  | date d =>
      have hd : dayWf d = true := h
      have hnone : parseMomentDT (renderDate d) = none := by
        unfold parseMomentDT
        rw [splitFirst_none 'T' (renderDate d) (renderDate_avoid d 'T' rfl (by decide))]
        rfl
      show parseMoment (renderDate d) = _
      unfold parseMoment
      rw [hnone]
      show (parseDate (renderDate d)).map Moment.date = _
      rw [parse_render_date d hd]
      rfl
  | dateTime d t =>
      have hd : dayWf d = true := h
      have hsome : parseMomentDT (renderDate d ++ 'T' :: renderClock t)
          = some (Moment.dateTime d t) := by
        unfold parseMomentDT
        rw [splitFirst_append 'T' (renderDate d) (renderClock t)
              (renderDate_avoid d 'T' rfl (by decide))]
        simp only [Option.bind_some]
        rw [parse_render_date d hd]
        simp only [Option.bind_some]
        rw [parse_render_clock t]
        rfl
      show parseMoment (renderDate d ++ 'T' :: renderClock t) = _
      unfold parseMoment
      rw [hsome]

theorem moment_date_form :
    parseMoment ['2','0','2','6','-','0','9','-','1','1']
      = some (.date (Cal.toDay ⟨2026, 9, 11⟩)) := by decide

theorem moment_datetime_form :
    parseMoment ['2','0','2','6','-','0','9','-','1','1','T','2','3',':','5','9']
      = some (.dateTime (Cal.toDay ⟨2026, 9, 11⟩) ⟨1439, by decide⟩) := by decide

/-- The short end form: a bare `HH:MM` on the start's day, rolled forward when
it precedes the start (`parse_interval`). -/
def parseEndShort (s : DT) (b : List Char) : Option DT :=
  (parseClock b).map (fun t => if t.val < s.time.val then DT.mk (s.day + 1) t else DT.mk s.day t)

def parseEnd (s : DT) (b : List Char) : Option DT :=
  match parseDT b with
  | some e => if s.abs ≤ e.abs then some e else none
  | none   => parseEndShort s b

def parseInterval (w : List Char) : Option (DT × DT) :=
  (splitFirst '/' w).bind (fun p =>
    (parseDT p.1).bind (fun s => (parseEnd s p.2).map (fun e => (s, e))))

/-- §4.1's serializer: the short end when the end is on the start's date. -/
def renderInterval (s e : DT) : List Char :=
  if s.day = e.day then renderDT s ++ '/' :: renderClock e.time
  else renderDT s ++ '/' :: renderDT e

/-- An interval is oriented and both ends are writable. -/
def intervalWf (s e : DT) : Bool := s.wf && e.wf && decide (s.abs ≤ e.abs)

/-- **The interval round trip, both forms.**  `at:` survives whichever end form
the serializer picked, and an end that rolls past midnight comes back as the
next day rather than as an interval running backwards. -/
theorem parse_render_interval (s e : DT) (h : intervalWf s e = true) :
    parseInterval (renderInterval s e) = some (s, e) := by
  have hs : s.wf = true := by
    unfold intervalWf at h; simp only [Bool.and_eq_true] at h; exact h.1.1
  have he : e.wf = true := by
    unfold intervalWf at h; simp only [Bool.and_eq_true] at h; exact h.1.2
  have habs : s.abs ≤ e.abs := by
    unfold intervalWf at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  unfold renderInterval
  by_cases hday : s.day = e.day
  · rw [if_pos hday]
    have htime : ¬ (e.time.val < s.time.val) := by
      unfold DT.abs at habs; rw [hday] at habs; omega
    unfold parseInterval
    rw [splitFirst_append '/' (renderDT s) (renderClock e.time)
          (renderDT_avoid s '/' rfl (by decide) (by decide) (by decide))]
    simp only [Option.bind_some]
    rw [parse_render_DT s hs]
    simp only [Option.bind_some]
    unfold parseEnd
    rw [parseDT_clock_none e.time]
    unfold parseEndShort
    rw [parse_render_clock e.time]
    simp only [Option.map_some, if_neg htime]
    rw [hday]
  · rw [if_neg hday]
    unfold parseInterval
    rw [splitFirst_append '/' (renderDT s) (renderDT e)
          (renderDT_avoid s '/' rfl (by decide) (by decide) (by decide))]
    simp only [Option.bind_some]
    rw [parse_render_DT s hs]
    simp only [Option.bind_some]
    unfold parseEnd
    rw [parse_render_DT e he]
    show Option.map (fun e' => (s, e')) (if s.abs ≤ e.abs then some e else none) = some (s, e)
    rw [if_pos habs]
    rfl

/-! ## `win:` — the window range

Daily (`11:30-13:30`, and `to ≤ from` is the overnight window §4.1 allows) or
absolute (a full interval). -/

inductive WindowRange
  | daily    (fromT toT : Clock)
  | absolute (start finish : DT)
deriving DecidableEq, Repr, Inhabited

def renderWindow : WindowRange → List Char
  | .daily f t     => renderClock f ++ '-' :: renderClock t
  | .absolute s e  => renderInterval s e

def parseWindowDaily (w : List Char) : Option WindowRange :=
  (splitFirst '-' w).bind (fun p =>
    (parseClock p.1).bind (fun a => (parseClock p.2).map (fun b => WindowRange.daily a b)))

def parseWindow (w : List Char) : Option WindowRange :=
  match parseInterval w with
  | some se => some (.absolute se.1 se.2)
  | none    => parseWindowDaily w

def windowWf : WindowRange → Bool
  | .daily _ _    => true
  | .absolute s e => intervalWf s e

theorem renderClock_no_slash (t : Clock) : ∀ c ∈ renderClock t, c ≠ '/' := by
  intro c hc hcx
  subst hcx
  rcases renderClock_chars t '/' hc with h | h
  · exact Bool.noConfusion h
  · exact absurd h (by decide)

theorem renderClock_no_dash (t : Clock) : ∀ c ∈ renderClock t, c ≠ '-' := by
  intro c hc hcx
  subst hcx
  rcases renderClock_chars t '-' hc with h | h
  · exact Bool.noConfusion h
  · exact absurd h (by decide)

/-- **The window round trip**, including the overnight daily form. -/
theorem parse_render_window (r : WindowRange) (h : windowWf r = true) :
    parseWindow (renderWindow r) = some r := by
  cases r with
  | daily f t =>
      unfold renderWindow parseWindow
      have hnone : parseInterval (renderClock f ++ '-' :: renderClock t) = none := by
        have hns : splitFirst '/' (renderClock f ++ '-' :: renderClock t) = none := by
          apply splitFirst_none
          intro x hx
          rcases List.mem_append.1 hx with h1 | h1
          · exact renderClock_no_slash f x h1
          · simp only [List.mem_cons] at h1
            rcases h1 with rfl | h1
            · exact fun hc => absurd hc (by decide)
            · exact renderClock_no_slash t x h1
        unfold parseInterval
        rw [hns]
        rfl
      rw [hnone]
      show parseWindowDaily (renderClock f ++ '-' :: renderClock t) = _
      unfold parseWindowDaily
      rw [splitFirst_append '-' (renderClock f) (renderClock t) (renderClock_no_dash f)]
      simp only [Option.bind_some]
      rw [parse_render_clock f]
      simp only [Option.bind_some]
      rw [parse_render_clock t]
      rfl
  | absolute s e =>
      unfold renderWindow parseWindow
      rw [parse_render_interval s e (by simpa [windowWf] using h)]

/-- The overnight window §4.1 allows (`to ≤ from` crosses midnight):
`win:22:00-02:00` is a real value, it writes as written, and it comes back as
itself rather than as a window that closes before it opens. -/
theorem overnight_window_roundtrips :
    renderWindow (.daily ⟨1320, by decide⟩ ⟨120, by decide⟩)
        = ['2','2',':','0','0','-','0','2',':','0','0'] ∧
      parseWindow ['2','2',':','0','0','-','0','2',':','0','0']
        = some (.daily ⟨1320, by decide⟩ ⟨120, by decide⟩) := by
  constructor <;> decide

/-! ## `pref:` — the anchor inside a window -/

def wakePrefix : List Char := ['w','a','k','e','+']

inductive Pref
  | wakePlus (d : Dur)
  | clock    (t : Clock)
deriving DecidableEq, Repr, Inhabited

def renderPref : Pref → List Char
  | .wakePlus d => wakePrefix ++ renderDur d
  | .clock t    => renderClock t

def parsePref (w : List Char) : Option Pref :=
  match stripPre wakePrefix w with
  | some rest => (parseDur rest).map Pref.wakePlus
  | none      =>
    if w = ['w','a','k','e'] then some (.wakePlus (.simple 0 .minutes))
    else (parseClock w).map Pref.clock

theorem pref_bare_wake : parsePref ['w','a','k','e'] = some (.wakePlus (.simple 0 .minutes)) := by
  decide

/-- **The `pref:` round trip.** -/
theorem parse_render_pref (p : Pref) : parsePref (renderPref p) = some p := by
  cases p with
  | wakePlus d =>
      unfold renderPref parsePref
      rw [stripPre_append wakePrefix (renderDur d)]
      show (parseDur (renderDur d)).map Pref.wakePlus = _
      rw [parse_render_dur d]
      rfl
  | clock t =>
      unfold renderPref parsePref
      have hnone : stripPre wakePrefix (renderClock t) = none := by
        obtain ⟨x, hx, hdig⟩ := renderClock_head_digit t
        refine stripPre_head_ne 'w' ['a','k','e','+'] (renderClock t) ?_
        intro y hy hyw
        rw [hx] at hy
        simp only [Option.some.injEq] at hy
        subst hy; subst hyw
        exact Bool.noConfusion hdig
      rw [hnone]
      show (if renderClock t = ['w','a','k','e'] then _
            else (parseClock (renderClock t)).map Pref.clock) = _
      have hne : renderClock t ≠ ['w','a','k','e'] := by
        intro hc
        have hl := renderClock_length t
        rw [hc] at hl
        exact absurd hl (by decide)
      rw [if_neg hne, parse_render_clock t]
      rfl


/-! ## Lists inside a value

`every:Mon,Wed,Fri`, `after:^k7q2,^m2` and `demoted:W36,W37` are comma lists.
One traversal, one round trip, three uses. -/

def mapOpt {α β : Type} (f : α → Option β) : List α → Option (List β)
  | []     => some []
  | a :: t => (f a).bind (fun b => (mapOpt f t).map (fun r => b :: r))

theorem mapOpt_map {α β : Type} (f : β → Option α) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f (g a) = some a) → mapOpt f (l.map g) = some l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      simp only [List.map_cons, mapOpt]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
      rfl

/-- The head test the literal-versus-computed case splits all reduce to.  It
matches on the **list**, not on `head?`, so every use reduces under `cases`. -/
def headSat (p : Char → Bool) (l : List Char) : Bool :=
  match l with
  | []     => false
  | c :: _ => p c

theorem headSat_ne {p : Char → Bool} {l₁ l₂ : List Char}
    (h₁ : headSat p l₁ = true) (h₂ : headSat p l₂ = false) : l₁ ≠ l₂ := by
  intro hc; rw [hc, h₂] at h₁; exact Bool.noConfusion h₁

theorem headSat_cons (p : Char → Bool) (c : Char) (t : List Char) :
    headSat p (c :: t) = p c := rfl

theorem headSat_append (p : Char → Bool) (a b : List Char) (h : a ≠ []) :
    headSat p (a ++ b) = headSat p a := by
  cases a with
  | nil => exact absurd rfl h
  | cons c t => rfl

theorem headSat_digitsOf (n : Nat) : headSat isDigitC (digitsOf n) = true := by
  cases hd : digitsOf n with
  | nil => exact absurd hd (digitsOf_ne_nil n)
  | cons a t =>
      rw [headSat_cons]
      exact digitsOf_isDigitC n a (by rw [hd]; simp)

/-- Disjoint classes at the head: this is the whole literal-versus-computed
case analysis, once. -/
theorem headSat_false_of {p q : Char → Bool} (hpq : ∀ c, p c = true → q c = false) :
    ∀ l : List Char, headSat p l = true → headSat q l = false := by
  intro l h
  cases l with
  | nil => rfl
  | cons c t => exact hpq c h

theorem headSat_not (p : Char → Bool) (l : List Char) (a : Char)
    (hh : headSat p l = true) (hp : p a = false) : ∀ x, l.head? = some x → x ≠ a := by
  intro x hx hxa
  subst hxa
  cases l with
  | nil => simp at hx
  | cons c t =>
      simp only [List.head?_cons, Option.some.injEq] at hx
      subst hx
      have hpc : p c = true := hh
      rw [hp] at hpc
      exact Bool.noConfusion hpc

/-! ## `every:` — the calendar rules

§4.1's six forms plus `grammar.rs`'s `every:week` / `every:Nw` (the spec's own
routines example uses it and the enum in §3.1 has no constructor for it — a
gap in the spec, recorded rather than papered over). -/

def renderWeekday : Cal.Weekday → List Char
  | .monday => ['M','o','n']
  | .tuesday => ['T','u','e']
  | .wednesday => ['W','e','d']
  | .thursday => ['T','h','u']
  | .friday => ['F','r','i']
  | .saturday => ['S','a','t']
  | .sunday => ['S','u','n']

def parseWeekday (w : List Char) : Option Cal.Weekday :=
  match w with
  | ['M','o','n'] => some .monday
  | ['m','o','n'] => some .monday
  | ['M','o','n','d','a','y'] => some .monday
  | ['m','o','n','d','a','y'] => some .monday
  | ['T','u','e'] => some .tuesday
  | ['t','u','e'] => some .tuesday
  | ['T','u','e','s','d','a','y'] => some .tuesday
  | ['t','u','e','s','d','a','y'] => some .tuesday
  | ['W','e','d'] => some .wednesday
  | ['w','e','d'] => some .wednesday
  | ['W','e','d','n','e','s','d','a','y'] => some .wednesday
  | ['w','e','d','n','e','s','d','a','y'] => some .wednesday
  | ['T','h','u'] => some .thursday
  | ['t','h','u'] => some .thursday
  | ['T','h','u','r','s','d','a','y'] => some .thursday
  | ['t','h','u','r','s','d','a','y'] => some .thursday
  | ['F','r','i'] => some .friday
  | ['f','r','i'] => some .friday
  | ['F','r','i','d','a','y'] => some .friday
  | ['f','r','i','d','a','y'] => some .friday
  | ['S','a','t'] => some .saturday
  | ['s','a','t'] => some .saturday
  | ['S','a','t','u','r','d','a','y'] => some .saturday
  | ['s','a','t','u','r','d','a','y'] => some .saturday
  | ['S','u','n'] => some .sunday
  | ['s','u','n'] => some .sunday
  | ['S','u','n','d','a','y'] => some .sunday
  | ['s','u','n','d','a','y'] => some .sunday
  | _ => none


theorem parse_render_weekday (d : Cal.Weekday) : parseWeekday (renderWeekday d) = some d := by
  cases d <;> rfl

theorem renderWeekday_no_comma (d : Cal.Weekday) : ∀ c ∈ renderWeekday d, c ≠ ',' := by
  intro c hc
  have h : ∀ e : Cal.Weekday, (renderWeekday e).all (fun x => !(x == ',')) = true := by
    intro e; cases e <;> decide
  have := List.all_eq_true.1 (h d) c hc
  simpa using this

theorem headSat_renderWeekday (d : Cal.Weekday) : headSat isUpperC (renderWeekday d) = true := by
  cases d <;> decide

inductive Rule
  | daily
  | weekdays
  | weekly      (days : List Cal.Weekday)
  | everyNDays  (n : Nat)
  | everyNWeeks (n : Nat) (d : Cal.Weekday)
  | weeks       (n : Nat)
  | monthly     (d : Nat)
deriving DecidableEq, Repr, Inhabited

/-- Decidable side conditions the value grammar cannot express: a weekday list
is non-empty, a period is positive, a month day is a day of some month. -/
def Rule.wf : Rule → Bool
  | .daily           => true
  | .weekdays        => true
  | .weekly ds       => !ds.isEmpty
  | .everyNDays n    => decide (0 < n)
  | .everyNWeeks n _ => decide (0 < n)
  | .weeks n         => decide (0 < n)
  | .monthly d       => decide (1 ≤ d ∧ d ≤ 31)

def renderRule : Rule → List Char
  | .daily            => ['d','a','y']
  | .weekdays         => ['w','e','e','k','d','a','y']
  | .weekly ds        => joinWith ',' (ds.map renderWeekday)
  | .everyNDays n     => digitsOf n ++ ['d']
  | .everyNWeeks n d  => digitsOf n ++ 'w' :: ':' :: renderWeekday d
  | .weeks n          => if n = 1 then ['w','e','e','k'] else digitsOf n ++ ['w']
  | .monthly d        => ['m','o','n','t','h',':'] ++ digitsOf d

def parseMonthDay (v : List Char) : Option Rule :=
  (readNat v).bind (fun d => if 1 ≤ d ∧ d ≤ 31 then some (Rule.monthly d) else none)

def parseNumRule (w : List Char) : Option Rule :=
  (readNat (w.takeWhile isDigitC)).bind (fun n =>
    if n = 0 then none
    else if w.dropWhile isDigitC = ['d'] then some (.everyNDays n)
    else if w.dropWhile isDigitC = ['w'] then some (.weeks n)
    else (stripPre ['w',':'] (w.dropWhile isDigitC)).bind (fun wd =>
      (parseWeekday wd).map (fun d => Rule.everyNWeeks n d)))

def parseWeeklyList (w : List Char) : Option Rule :=
  (mapOpt parseWeekday (splitOn ',' w)).bind (fun ds =>
    if ds.isEmpty then none else some (.weekly ds))

def parseRuleTail (w : List Char) : Option Rule :=
  match stripPre ['m','o','n','t','h',':'] w with
  | some v => parseMonthDay v
  | none   => if headSat isDigitC w then parseNumRule w else parseWeeklyList w

def parseRule (w : List Char) : Option Rule :=
  if w = ['d','a','y'] then some .daily
  else if w = ['d','a','i','l','y'] then some .daily
  else if w = ['w','e','e','k','d','a','y'] then some .weekdays
  else if w = ['w','e','e','k','d','a','y','s'] then some .weekdays
  else if w = ['w','e','e','k'] then some (.weeks 1)
  else if w = ['w','e','e','k','l','y'] then some (.weeks 1)
  else parseRuleTail w

theorem rule_day       : parseRule ['d','a','y'] = some .daily := by decide
theorem rule_weekday   : parseRule ['w','e','e','k','d','a','y'] = some .weekdays := by decide
theorem rule_mwf       : parseRule ['M','o','n',',','W','e','d',',','F','r','i']
    = some (.weekly [.monday, .wednesday, .friday]) := by decide
theorem rule_2w_sun    : parseRule ['2','w',':','S','u','n'] = some (.everyNWeeks 2 .sunday) := by decide
theorem rule_3d        : parseRule ['3','d'] = some (.everyNDays 3) := by decide
theorem rule_month_15  : parseRule ['m','o','n','t','h',':','1','5'] = some (.monthly 15) := by decide
theorem rule_week      : parseRule ['w','e','e','k'] = some (.weeks 1) := by decide
theorem rule_month_0_rejected  : parseRule ['m','o','n','t','h',':','0'] = none := by decide
theorem rule_month_32_rejected : parseRule ['m','o','n','t','h',':','3','2'] = none := by decide
theorem rule_0d_rejected       : parseRule ['0','d'] = none := by decide

/-- The literals `parseRule` tries first all begin with a lower-case letter, so
a rule whose rendering begins with a digit or a capital cannot be shadowed by
one of them.  This is the case analysis the round trip below turns on. -/
theorem renderRule_not_literal (w : List Char) (h : headSat isLowerC w = false) :
    w ≠ ['d','a','y'] ∧ w ≠ ['d','a','i','l','y'] ∧ w ≠ ['w','e','e','k','d','a','y'] ∧
      w ≠ ['w','e','e','k','d','a','y','s'] ∧ w ≠ ['w','e','e','k'] ∧
      w ≠ ['w','e','e','k','l','y'] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro hc; rw [hc] at h; exact Bool.noConfusion h)

/-- **The `every:` round trip.**  All seven forms. -/
theorem parse_render_rule (r : Rule) (h : r.wf = true) : parseRule (renderRule r) = some r := by
  cases r with
  | daily => rfl
  | weekdays => rfl
  | weekly ds =>
      have hne : ds ≠ [] := by
        intro hc; rw [hc] at h; exact Bool.noConfusion h
      cases hds : ds with
      | nil => exact absurd hds hne
      | cons d rest =>
          have hhead : headSat isUpperC (joinWith ',' ((d :: rest).map renderWeekday)) = true := by
            cases hrw : renderWeekday d with
            | nil =>
                have := headSat_renderWeekday d
                rw [hrw] at this; exact absurd this (by decide)
            | cons a t =>
                cases rest with
                | nil =>
                    show headSat isUpperC (renderWeekday d) = true
                    exact headSat_renderWeekday d
                | cons e r2 =>
                    show headSat isUpperC (renderWeekday d ++
                      ',' :: joinWith ',' ((e :: r2).map renderWeekday)) = true
                    rw [headSat_append _ _ _ (by rw [hrw]; simp)]
                    exact headSat_renderWeekday d
          have hlow : headSat isLowerC (joinWith ',' ((d :: rest).map renderWeekday)) = false :=
            headSat_false_of upper_not_lower _ hhead
          have hdig : headSat isDigitC (joinWith ',' ((d :: rest).map renderWeekday)) = false :=
            headSat_false_of upper_not_digit _ hhead
          obtain ⟨n1, n2, n3, n4, n5, n6⟩ := renderRule_not_literal _ hlow
          show parseRule (joinWith ',' ((d :: rest).map renderWeekday)) = _
          unfold parseRule
          rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]
          show parseRuleTail (joinWith ',' ((d :: rest).map renderWeekday)) = _
          unfold parseRuleTail
          have hstrip : stripPre ['m','o','n','t','h',':']
              (joinWith ',' ((d :: rest).map renderWeekday)) = none := by
            refine stripPre_head_ne 'm' ['o','n','t','h',':'] _ ?_
            exact headSat_not isUpperC _ 'm' hhead (by decide)
          rw [hstrip]
          show (if headSat isDigitC (joinWith ',' ((d :: rest).map renderWeekday)) then _ else _) = _
          rw [hdig]
          simp only [Bool.false_eq_true, if_false]
          unfold parseWeeklyList
          rw [splitOn_joinWith ',' ((d :: rest).map renderWeekday) (by simp)
                (by intro g hg; simp only [List.mem_map] at hg
                    obtain ⟨e, _, rfl⟩ := hg
                    exact renderWeekday_no_comma e)]
          rw [mapOpt_map parseWeekday renderWeekday (d :: rest)
                (fun a _ => parse_render_weekday a)]
          rfl
  | everyNDays n =>
      have hn : 0 < n := by simpa [Rule.wf] using h
      have hhead : headSat isDigitC (digitsOf n ++ ['d']) = true := by
        rw [headSat_append _ _ _ (digitsOf_ne_nil n)]; exact headSat_digitsOf n
      have hlow : headSat isLowerC (digitsOf n ++ ['d']) = false :=
        headSat_false_of digit_not_lower _ hhead
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := renderRule_not_literal _ hlow
      show parseRule (digitsOf n ++ ['d']) = _
      unfold parseRule
      rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]
      show parseRuleTail (digitsOf n ++ ['d']) = _
      unfold parseRuleTail
      rw [stripPre_head_ne 'm' ['o','n','t','h',':'] _
            (headSat_not isDigitC _ 'm' hhead (by decide))]
      show (if headSat isDigitC (digitsOf n ++ ['d']) then _ else _) = _
      rw [hhead]
      simp only [if_true]
      unfold parseNumRule
      have hs := takeWhile_append_all isDigitC (digitsOf n) ['d'] (digitsOf_isDigitC n)
        (by intro x hx; simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; rfl)
      rw [hs.1, hs.2, readNat_digitsOf]
      simp only [Option.bind_some]
      rw [if_neg (by omega)]
      simp
  | weeks n =>
      have hn : 0 < n := by simpa [Rule.wf] using h
      by_cases h1 : n = 1
      · subst h1; rfl
      · have hhead : headSat isDigitC (digitsOf n ++ ['w']) = true := by
          rw [headSat_append _ _ _ (digitsOf_ne_nil n)]; exact headSat_digitsOf n
        have hlow : headSat isLowerC (digitsOf n ++ ['w']) = false :=
          headSat_false_of digit_not_lower _ hhead
        obtain ⟨n1, n2, n3, n4, n5, n6⟩ := renderRule_not_literal _ hlow
        show parseRule (if n = 1 then ['w','e','e','k'] else digitsOf n ++ ['w']) = _
        rw [if_neg h1]
        unfold parseRule
        rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]
        show parseRuleTail (digitsOf n ++ ['w']) = _
        unfold parseRuleTail
        rw [stripPre_head_ne 'm' ['o','n','t','h',':'] _
              (headSat_not isDigitC _ 'm' hhead (by decide))]
        show (if headSat isDigitC (digitsOf n ++ ['w']) then _ else _) = _
        rw [hhead]
        simp only [if_true]
        unfold parseNumRule
        have hs := takeWhile_append_all isDigitC (digitsOf n) ['w'] (digitsOf_isDigitC n)
          (by intro x hx; simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; rfl)
        rw [hs.1, hs.2, readNat_digitsOf]
        simp only [Option.bind_some]
        rw [if_neg (by omega), if_neg (by simp)]
        simp
  | everyNWeeks n d =>
      have hn : 0 < n := by simpa [Rule.wf] using h
      have hhead : headSat isDigitC (digitsOf n ++ 'w' :: ':' :: renderWeekday d) = true := by
        rw [headSat_append _ _ _ (digitsOf_ne_nil n)]; exact headSat_digitsOf n
      have hlow : headSat isLowerC (digitsOf n ++ 'w' :: ':' :: renderWeekday d) = false :=
        headSat_false_of digit_not_lower _ hhead
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := renderRule_not_literal _ hlow
      show parseRule (digitsOf n ++ 'w' :: ':' :: renderWeekday d) = _
      unfold parseRule
      rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]
      show parseRuleTail (digitsOf n ++ 'w' :: ':' :: renderWeekday d) = _
      unfold parseRuleTail
      rw [stripPre_head_ne 'm' ['o','n','t','h',':'] _
            (headSat_not isDigitC _ 'm' hhead (by decide))]
      show (if headSat isDigitC (digitsOf n ++ 'w' :: ':' :: renderWeekday d) then _ else _) = _
      rw [hhead]
      simp only [if_true]
      unfold parseNumRule
      have hs := takeWhile_append_all isDigitC (digitsOf n) ('w' :: ':' :: renderWeekday d)
        (digitsOf_isDigitC n)
        (by intro x hx; simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; rfl)
      rw [hs.1, hs.2, readNat_digitsOf]
      simp only [Option.bind_some]
      rw [if_neg (by omega), if_neg (by simp), if_neg (by simp)]
      rw [show stripPre ['w',':'] ('w' :: ':' :: renderWeekday d) = some (renderWeekday d) from
            stripPre_append ['w',':'] (renderWeekday d)]
      simp only [Option.bind_some]
      rw [parse_render_weekday d]
      rfl
  | monthly d =>
      have hd : 1 ≤ d ∧ d ≤ 31 := by simpa [Rule.wf] using h
      have hlow : headSat isLowerC (['m','o','n','t','h',':'] ++ digitsOf d) = true := by rfl
      show parseRule (['m','o','n','t','h',':'] ++ digitsOf d) = _
      unfold parseRule
      rw [if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp),
        if_neg (by simp), if_neg (by simp)]
      show parseRuleTail (['m','o','n','t','h',':'] ++ digitsOf d) = _
      unfold parseRuleTail
      rw [stripPre_append ['m','o','n','t','h',':'] (digitsOf d)]
      show parseMonthDay (digitsOf d) = _
      unfold parseMonthDay
      rw [readNat_digitsOf]
      simp only [Option.bind_some]
      rw [if_pos hd]

/-! ## `after-done:` and `on-event:` -/

structure AfterDone where
  offset : Dur
  window : Option Dur
deriving DecidableEq, Repr, Inhabited

def renderAfterDone (a : AfterDone) : List Char :=
  match a.window with
  | none   => renderDur a.offset
  | some v => renderDur a.offset ++ '~' :: renderDur v

def parseAfterDone (w : List Char) : Option AfterDone :=
  match splitFirst '~' w with
  | some p => (parseDur p.1).bind (fun o => (parseDur p.2).map (fun v => AfterDone.mk o (some v)))
  | none   => (parseDur w).map (fun o => AfterDone.mk o none)

theorem renderDur_no (d : Dur) (x : Char) (hx : isDigitC x = false)
    (h1 : x ≠ 'b') (h2 : x ≠ 'm') (h3 : x ≠ 'h') (h4 : x ≠ 'd') :
    ∀ c ∈ renderDur d, c ≠ x := by
  intro c hc hcx
  subst hcx
  rcases renderDur_chars d c hc with h | h | h | h | h
  · rw [h] at hx; exact Bool.noConfusion hx
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h

/-- **The `after-done:` round trip** — `2d` and `2d~1d`. -/
theorem parse_render_afterDone (a : AfterDone) : parseAfterDone (renderAfterDone a) = some a := by
  obtain ⟨o, wn⟩ := a
  cases wn with
  | none =>
      show parseAfterDone (renderDur o) = _
      unfold parseAfterDone
      rw [splitFirst_none '~' (renderDur o)
            (renderDur_no o '~' rfl (by decide) (by decide) (by decide) (by decide))]
      show (parseDur (renderDur o)).map (fun x => AfterDone.mk x none) = _
      rw [parse_render_dur o]
      rfl
  | some v =>
      show parseAfterDone (renderDur o ++ '~' :: renderDur v) = _
      unfold parseAfterDone
      rw [splitFirst_append '~' (renderDur o) (renderDur v)
            (renderDur_no o '~' rfl (by decide) (by decide) (by decide) (by decide))]
      show (parseDur (renderDur o)).bind
        (fun x => (parseDur (renderDur v)).map (fun y => AfterDone.mk x (some y))) = _
      rw [parse_render_dur o]
      simp only [Option.bind_some]
      rw [parse_render_dur v]
      rfl

structure OnEvent where
  name    : List Char
  timeout : Option Dur
deriving DecidableEq, Repr, Inhabited

def OnEvent.wf (e : OnEvent) : Bool := isName e.name

def renderOnEvent (e : OnEvent) : List Char :=
  match e.timeout with
  | none   => e.name
  | some t => e.name ++ '/' :: renderDur t

def parseOnEvent (w : List Char) : Option OnEvent :=
  match splitFirst '/' w with
  | some p => if isName p.1 then (parseDur p.2).map (fun t => OnEvent.mk p.1 (some t)) else none
  | none   => if isName w then some (OnEvent.mk w none) else none

/-- **The `on-event:` round trip** — `reply` and `reply/7d`. -/
theorem parse_render_onEvent (e : OnEvent) (h : e.wf = true) :
    parseOnEvent (renderOnEvent e) = some e := by
  obtain ⟨nm, tm⟩ := e
  have hn : isName nm = true := h
  cases tm with
  | none =>
      show parseOnEvent nm = _
      unfold parseOnEvent
      rw [splitFirst_none '/' nm (fun c hc => (isName_avoids hn c hc).2.2.1)]
      show (if isName nm then some (OnEvent.mk nm none) else none) = _
      rw [if_pos hn]
  | some t =>
      show parseOnEvent (nm ++ '/' :: renderDur t) = _
      unfold parseOnEvent
      rw [splitFirst_append '/' nm (renderDur t) (fun c hc => (isName_avoids hn c hc).2.2.1)]
      show (if isName nm then (parseDur (renderDur t)).map (fun x => OnEvent.mk nm (some x))
            else none) = _
      rw [if_pos hn, parse_render_dur t]
      rfl

/-! ## `on-miss:`, budgets, `after:`, `loc:`, the stamps, `ci` and `!k` -/

inductive OnMiss | expire | persist | next
deriving DecidableEq, Repr, Inhabited

def renderOnMiss : OnMiss → List Char
  | .expire  => ['e','x','p','i','r','e']
  | .persist => ['p','e','r','s','i','s','t']
  | .next    => ['n','e','x','t']

def parseOnMiss (w : List Char) : Option OnMiss :=
  match w with
  | ['e','x','p','i','r','e']     => some .expire
  | ['p','e','r','s','i','s','t'] => some .persist
  | ['n','e','x','t']             => some .next
  | _                             => none

theorem parse_render_onMiss (m : OnMiss) : parseOnMiss (renderOnMiss m) = some m := by
  cases m <;> rfl

inductive Period | day | week | month
deriving DecidableEq, Repr, Inhabited

def renderPeriod : Period → List Char
  | .day => ['d'] | .week => ['w'] | .month => ['m']

def parsePeriod (w : List Char) : Option Period :=
  match w with
  | ['d']                     => some .day
  | ['d','a','y']             => some .day
  | ['w']                     => some .week
  | ['w','e','e','k']         => some .week
  | ['m']                     => some .month
  | ['m','o','n','t','h']     => some .month
  | _                         => none

theorem parse_render_period (p : Period) : parsePeriod (renderPeriod p) = some p := by
  cases p <;> rfl

structure Rate where
  amount : Dur
  per    : Period
deriving DecidableEq, Repr, Inhabited

def renderRate (r : Rate) : List Char := renderDur r.amount ++ '/' :: renderPeriod r.per

def parseRate (w : List Char) : Option Rate :=
  (splitFirst '/' w).bind (fun p =>
    (parseDur p.1).bind (fun a => (parsePeriod p.2).map (fun q => Rate.mk a q)))

/-- **The budget round trip** — `6b/w`, `2b/d`, `4h/w`. -/
theorem parse_render_rate (r : Rate) : parseRate (renderRate r) = some r := by
  unfold renderRate parseRate
  rw [splitFirst_append '/' (renderDur r.amount) (renderPeriod r.per)
        (renderDur_no r.amount '/' rfl (by decide) (by decide) (by decide) (by decide))]
  simp only [Option.bind_some]
  rw [parse_render_dur r.amount]
  simp only [Option.bind_some]
  rw [parse_render_period r.per]
  rfl

theorem rate_6b_w : parseRate ['6','b','/','w'] = some ⟨.simple 6 .blocks, .week⟩ := by decide
theorem rate_4h_w : parseRate ['4','h','/','w'] = some ⟨.simple 4 .hours, .week⟩ := by decide
theorem rate_2b_d : parseRate ['2','b','/','d'] = some ⟨.simple 2 .blocks, .day⟩ := by decide

inductive Dep
  | item  (i : List Char)
  | event (name : List Char)
deriving DecidableEq, Repr, Inhabited

def Dep.wf : Dep → Bool
  | .item i  => isName i
  | .event n => isName n

def eventPrefix : List Char := ['e','v','e','n','t',':']

def renderDep : Dep → List Char
  | .item i  => '^' :: i
  | .event n => eventPrefix ++ n

def parseDepBare (w : List Char) : Option Dep :=
  let i := if w.head? = some '^' then w.tail else w
  if isName i then some (.item i) else none

def parseDep (w : List Char) : Option Dep :=
  match stripPre eventPrefix w with
  | some n => if isName n then some (.event n) else none
  | none   => parseDepBare w

theorem parse_render_dep (d : Dep) (h : d.wf = true) : parseDep (renderDep d) = some d := by
  cases d with
  | item i =>
      have hi : isName i = true := h
      show parseDep ('^' :: i) = _
      unfold parseDep eventPrefix
      rw [stripPre_head_ne 'e' ['v','e','n','t',':'] ('^' :: i)
            (by intro x hx; simp only [List.head?_cons, Option.some.injEq] at hx
                subst hx; decide)]
      show parseDepBare ('^' :: i) = _
      unfold parseDepBare
      show (if isName (if ('^' :: i).head? = some '^' then ('^' :: i).tail else '^' :: i) = true
            then some (Dep.item (if ('^' :: i).head? = some '^' then ('^' :: i).tail else '^' :: i))
            else none) = _
      rw [if_pos (show ('^' :: i).head? = some '^' from rfl)]
      show (if isName i = true then some (Dep.item i) else none) = _
      rw [if_pos hi]
  | event n =>
      have hn : isName n = true := h
      show parseDep (eventPrefix ++ n) = _
      unfold parseDep
      rw [stripPre_append eventPrefix n]
      show (if isName n then some (Dep.event n) else none) = _
      rw [if_pos hn]

theorem eventPrefix_no_comma : ∀ c ∈ eventPrefix, c ≠ ',' := by decide

theorem renderDep_no_comma (d : Dep) (h : d.wf = true) : ∀ c ∈ renderDep d, c ≠ ',' := by
  cases d with
  | item i =>
      intro c hc
      simp only [renderDep, List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact (isName_avoids h c hc).2.1
  | event n =>
      intro c hc
      rcases List.mem_append.1 hc with h1 | h1
      · exact eventPrefix_no_comma c h1
      · exact (isName_avoids h c h1).2.1

def renderDeps (ds : List Dep) : List Char := joinWith ',' (ds.map renderDep)

def parseDeps (w : List Char) : Option (List Dep) :=
  (mapOpt parseDep (splitOn ',' w)).bind (fun ds => if ds.isEmpty then none else some ds)

def depsWf (ds : List Dep) : Bool := !ds.isEmpty && ds.all Dep.wf

/-- **The `after:` round trip** — an id list, an `event:` name, or a mix. -/
theorem parse_render_deps (ds : List Dep) (h : depsWf ds = true) :
    parseDeps (renderDeps ds) = some ds := by
  simp only [depsWf, Bool.and_eq_true, Bool.not_eq_true'] at h
  have hne : ds ≠ [] := by intro hc; rw [hc] at h; simp at h
  have hall : ∀ d ∈ ds, Dep.wf d = true := fun d hd => List.all_eq_true.1 h.2 d hd
  unfold parseDeps renderDeps
  rw [splitOn_joinWith ',' (ds.map renderDep) (by simp [hne])
        (by intro g hg
            simp only [List.mem_map] at hg
            obtain ⟨e, he, rfl⟩ := hg
            exact renderDep_no_comma e (hall e he))]
  rw [mapOpt_map parseDep renderDep ds (fun a ha => parse_render_dep a (hall a ha))]
  simp only [Option.bind_some]
  rw [if_neg (by simp [hne])]

theorem deps_mixed :
    parseDeps ['^','k','7','q','2',',','e','v','e','n','t',':','v','i','s','a']
      = some [.item ['k','7','q','2'], .event ['v','i','s','a']] := by decide

inductive Loc | any | lounge | home | out | named (n : List Char)
deriving DecidableEq, Repr, Inhabited

def renderLoc : Loc → List Char
  | .any     => ['a','n','y']
  | .lounge  => ['l','o','u','n','g','e']
  | .home    => ['h','o','m','e']
  | .out     => ['o','u','t']
  | .named n => n

def parseLoc (w : List Char) : Option Loc :=
  if w = [] then none
  else if w = ['a','n','y'] then some .any
  else if w = ['l','o','u','n','g','e'] then some .lounge
  else if w = ['h','o','m','e'] then some .home
  else if w = ['o','u','t'] then some .out
  else some (.named w)

/-- A named location may not spell one of the four the enum already has: two
names for one value is the shape of the defect this kernel exists to remove. -/
def Loc.wf : Loc → Bool
  | .named n => !n.isEmpty && n != ['a','n','y'] && n != ['l','o','u','n','g','e'] &&
                n != ['h','o','m','e'] && n != ['o','u','t']
  | _        => true

theorem parse_render_loc (l : Loc) (h : l.wf = true) : parseLoc (renderLoc l) = some l := by
  cases l with
  | any => rfl
  | lounge => rfl
  | home => rfl
  | out => rfl
  | named n =>
      simp only [Loc.wf, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
      show parseLoc n = _
      unfold parseLoc
      have h0 : n ≠ [] := by intro hc; rw [hc] at h; simp at h
      rw [if_neg h0, if_neg h.1.1.1.2, if_neg h.1.1.2, if_neg h.1.2, if_neg h.2]

inductive Stamp | week (n : Nat) | day (n : Nat)
deriving DecidableEq, Repr, Inhabited

def renderStamp : Stamp → List Char
  | .week n => 'W' :: padTo 2 n
  | .day n  => 'D' :: padTo 2 n

def parseStamp (w : List Char) : Option Stamp :=
  if w.head? = some 'W' then (readNat w.tail).map Stamp.week
  else if w.head? = some 'D' then (readNat w.tail).map Stamp.day
  else none

theorem parse_render_stamp (s : Stamp) : parseStamp (renderStamp s) = some s := by
  cases s with
  | week n =>
      show parseStamp ('W' :: padTo 2 n) = _
      unfold parseStamp
      rw [if_pos (by rfl)]
      show (readNat (padTo 2 n)).map Stamp.week = _
      rw [readNat_padTo]
      rfl
  | day n =>
      show parseStamp ('D' :: padTo 2 n) = _
      unfold parseStamp
      rw [if_neg (by simp)]
      show (if ('D' :: padTo 2 n).head? = some 'D' then (readNat ('D' :: padTo 2 n).tail).map Stamp.day
            else none) = _
      rw [if_pos (by rfl)]
      show (readNat (padTo 2 n)).map Stamp.day = _
      rw [readNat_padTo]
      rfl

theorem renderStamp_no_comma (s : Stamp) : ∀ c ∈ renderStamp s, c ≠ ',' := by
  cases s with
  | week n =>
      intro c hc
      simp only [renderStamp, List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact padTo_not_char 2 n ',' rfl c hc
  | day n =>
      intro c hc
      simp only [renderStamp, List.mem_cons] at hc
      rcases hc with rfl | hc
      · decide
      · exact padTo_not_char 2 n ',' rfl c hc

def renderStamps (ss : List Stamp) : List Char := joinWith ',' (ss.map renderStamp)

def parseStamps (w : List Char) : Option (List Stamp) :=
  (mapOpt parseStamp (splitOn ',' w)).bind (fun ss => if ss.isEmpty then none else some ss)

/-- **The `demoted:` round trip** — the tool-written stamp list. -/
theorem parse_render_stamps (ss : List Stamp) (h : ss ≠ []) :
    parseStamps (renderStamps ss) = some ss := by
  unfold parseStamps renderStamps
  rw [splitOn_joinWith ',' (ss.map renderStamp) (by simp [h])
        (by intro g hg
            simp only [List.mem_map] at hg
            obtain ⟨e, _, rfl⟩ := hg
            exact renderStamp_no_comma e)]
  rw [mapOpt_map parseStamp renderStamp ss (fun a _ => parse_render_stamp a)]
  simp only [Option.bind_some]
  rw [if_neg (by simp [h])]

theorem stamps_W36_W37 :
    parseStamps ['W','3','6',',','W','3','7'] = some [.week 36, .week 37] := by decide

/-! ## The two small numeric fields

`ci` is 0–5 and `!k` is 1–4; both are `Fin`, so an out-of-range value is not
something the kernel can hold — `--energy 9` (G5) has nowhere to land. -/

def renderCi (c : Fin 6) : List Char := [digitChar c.val]

def parseCi (w : List Char) : Option (Fin 6) :=
  (readNat w).bind (fun n => if h : n < 6 then some ⟨n, h⟩ else none)

theorem readNat_single (k : Nat) (h : k < 10) : readNat [digitChar k] = some k := by
  have : digitsOf k = [digitChar k] := by rw [digitsOf_eq, if_pos h]
  rw [← this, readNat_digitsOf]

theorem parse_render_ci (c : Fin 6) : parseCi (renderCi c) = some c := by
  unfold renderCi parseCi
  rw [readNat_single c.val (by omega)]
  simp only [Option.bind_some]
  rw [dif_pos c.isLt]

theorem ci_rejects_6 : parseCi ['6'] = none := by decide
theorem ci_rejects_9 : parseCi ['9'] = none := by decide

/-- §4.1's `!k`, held zero-based the way `State.lean` holds it. -/
def renderPrio (k : Fin 4) : List Char := ['!', digitChar (k.val + 1)]

def parsePrio (w : List Char) : Option (Fin 4) :=
  if w.head? = some '!' then
    (readNat w.tail).bind (fun n => if h : 1 ≤ n ∧ n ≤ 4 then some ⟨n - 1, by omega⟩ else none)
  else none

theorem parse_render_prio (k : Fin 4) : parsePrio (renderPrio k) = some k := by
  unfold renderPrio parsePrio
  rw [if_pos (by rfl)]
  show (readNat [digitChar (k.val + 1)]).bind
    (fun n => if h : 1 ≤ n ∧ n ≤ 4 then some (⟨n - 1, by omega⟩ : Fin 4) else none) = _
  rw [readNat_single (k.val + 1) (by omega)]
  simp only [Option.bind_some]
  rw [dif_pos (And.intro (by omega) (by omega : k.val + 1 ≤ 4))]
  simp only [Option.some.injEq, Fin.ext_iff]
  omega

theorem prio_rejects_5 : parsePrio ['!','5'] = none := by decide
theorem prio_rejects_0 : parsePrio ['!','0'] = none := by decide
theorem prio_reads_1 : (parsePrio ['!','1']).map Fin.val = some 0 := by decide


/-! ## The token grammar

§4.1's EBNF after the state box:

```
line  = "- " state SP [ci SP] [est SP] title { SP token } ;
token = "@" ref | "#" tag | "!" ("1".."4") | "^" id | key ":" value | flag ;
```

Two positional slots, then a title that runs to the first word that *ends* it,
then classified tokens.  That is a four-phase machine and it is written as
four functions, each structurally recursive on its own list, so the whole
grammar is total with no termination argument.

**The two §4.1 rules that are easy to lose live here.**

* A word the classifier cannot place stays in the title (`.unparsed`, which
  `titleWords` reads and `problems` reports) — `!9`, `^%`, `@@`.
* A `key:` the kernel does not know is `.extra`: kept with its key and value,
  reported, and — because the token vector is the bytes — written back
  untouched.

And one rule that is easy to get *wrong in the other direction*: a flag name is
a flag only **after** the title has ended.  `- [ ] Lean practice open ^l1` has
the word `open` in its title, not the flag.  That is why `flagsOf` is the one
view with no raw-scan agreement theorem below, and why `setFlag` inserts after
the `^id` rather than wherever it likes. -/

def sigilOf (w : List Char) : Option Char :=
  match w with
  | c :: _ => if c == '@' || c == '#' || c == '!' || c == '^' then some c else none
  | []     => none

/-- The key of a `key:value` word, when the part before the first colon is a
non-empty `[a-z-]+` (`key_prefix`). -/
def keyPrefix (w : List Char) : Option (List Char) :=
  (splitFirst ':' w).bind (fun p => if !p.1.isEmpty && p.1.all isKeyC then some p.1 else none)

def keyValue (w : List Char) : Option (List Char) := (splitFirst ':' w).map Prod.snd

def keyOf (w : List Char) : Option Key := (keyPrefix w).bind Key.ofName?

/-- The word ends the title (`starts_token`). -/
def startsToken (w : List Char) : Bool := (sigilOf w).isSome || (keyPrefix w).isSome

/-- The positional ci slot: one character, 0–5. -/
def ciSlot (w : List Char) : Option (Fin 6) :=
  match w with
  | [c] => parseCi [c]
  | _   => none

/-- The positional leading-estimate slot: a duration without `Nd`. -/
def estSlot (w : List Char) : Option Dur := parseDurND w

inductive TokKind
  | ci       (c : Fin 6)
  | est      (d : Dur)
  | title    (w : List Char)
  | parent   (r : List Char)
  | tag      (t : List Char)
  | prio     (k : Fin 4)
  | id       (i : List Char)
  | key      (k : Key) (v : List Char)
  | extra    (k v : List Char)
  | flag     (f : Flag)
  | unparsed (w : List Char)
deriving DecidableEq, Repr, Inhabited

/-- `!k` in token position: a priority, or a word the parser cannot classify. -/
def classifyBang (w : List Char) : TokKind :=
  match parsePrio w with
  | some k => .prio k
  | none   => .unparsed w

/-- A word that begins with one of `@ # ! ^`.  A **lone** sigil is punctuation
("Meet Kun @ 7pm"), not a broken token — §4.1, and `classify`'s first arm. -/
def classifySigil (c : Char) (w : List Char) : TokKind :=
  if w.length = 1 then .title w
  else if c = '@' then .parent w.tail
  else if c = '#' then .tag w.tail
  else if c = '!' then classifyBang w
  else if isName w.tail then .id w.tail else .unparsed w

/-- A `key:value` word.  An unrecognised key becomes `.extra`, which is kept
verbatim and reported — never dropped. -/
def classifyKeyed (k : List Char) (w : List Char) : TokKind :=
  match Key.ofName? k with
  | some kk => .key kk ((keyValue w).getD [])
  | none    => .extra k ((keyValue w).getD [])

/-- A bare word in token position: a flag, or title text. -/
def classifyPlain (w : List Char) : TokKind :=
  match Flag.ofName? w with
  | some f => .flag f
  | none   => .title w

/-- Classify a word in token position (`classify`). -/
def classifyWord (w : List Char) : TokKind :=
  match sigilOf w with
  | some c => classifySigil c w
  | none   =>
    match keyPrefix w with
    | some k => classifyKeyed k w
    | none   => classifyPlain w


def classifyPhase3 : List Tok → List TokKind
  | []      => []
  | t :: ts => classifyWord t.word :: classifyPhase3 ts

def classifyPhase2 : List Tok → List TokKind
  | []      => []
  | t :: ts =>
    if startsToken t.word then classifyPhase3 (t :: ts)
    else TokKind.title t.word :: classifyPhase2 ts

def classifyPhase1 : List Tok → List TokKind
  | []      => []
  | t :: ts =>
    match estSlot t.word with
    | some d => TokKind.est d :: classifyPhase2 ts
    | none   => classifyPhase2 (t :: ts)

def classifyPhase0 : List Tok → List TokKind
  | []      => []
  | t :: ts =>
    match ciSlot t.word with
    | some c => TokKind.ci c :: classifyPhase1 ts
    | none   => classifyPhase1 (t :: ts)

/-- The token grammar applied to a line. -/
def kinds (r : RawItem) : List TokKind := classifyPhase0 r.toks

/-! ### Where a word can and cannot be classified

Four little facts carry every case split below: the head character of a word
decides which of the four shapes it can have. -/

theorem keyPrefix_head {w : List Char} {k : List Char} (h : keyPrefix w = some k) :
    headSat isKeyC w = true := by
  unfold keyPrefix at h
  cases hs : splitFirst ':' w with
  | none => rw [hs] at h; simp at h
  | some p =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      by_cases hc : (!p.1.isEmpty && p.1.all isKeyC) = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        have hw := splitFirst_sound ':' w p.1 p.2 hs
        cases hk : p.1 with
        | nil => rw [hk] at hc; simp at hc
        | cons a t =>
            rw [hw, hk]
            show isKeyC a = true
            have := List.all_eq_true.1 hc.2 a (by rw [hk]; simp)
            exact this
      · rw [if_neg hc] at h; simp at h

theorem sigilOf_head {w : List Char} {c : Char} (h : sigilOf w = some c) :
    headSat (fun x => decide (x = '@' ∨ x = '#' ∨ x = '!' ∨ x = '^')) w = true := by
  cases w with
  | nil => simp [sigilOf] at h
  | cons a t =>
      have h' : (if (a == '@' || a == '#' || a == '!' || a == '^') = true then some a else none)
          = some c := h
      by_cases hb : (a == '@' || a == '#' || a == '!' || a == '^') = true
      · show decide (a = '@' ∨ a = '#' ∨ a = '!' ∨ a = '^') = true
        simp only [Bool.or_eq_true, beq_iff_eq] at hb
        simp only [decide_eq_true_eq]
        rcases hb with ((h1 | h1) | h1) | h1 <;> simp [h1]
      · rw [if_neg hb] at h'; simp at h'

theorem sigil_not_key : ∀ c : Char,
    (fun x => decide (x = '@' ∨ x = '#' ∨ x = '!' ∨ x = '^')) c = true → isKeyC c = false := by
  intro c h
  simp only [decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem sigil_not_digit : ∀ c : Char,
    (fun x => decide (x = '@' ∨ x = '#' ∨ x = '!' ∨ x = '^')) c = true → isDigitC c = false := by
  intro c h
  simp only [decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem digit_not_key : ∀ c : Char, isDigitC c = true → isKeyC c = false := by
  intro c h
  have hl := digit_not_lower c h
  rcases isDigitC_cases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- A word whose head is not a key character has no key prefix. -/
theorem keyPrefix_none_of {w : List Char} (h : headSat isKeyC w = false) : keyPrefix w = none := by
  cases hk : keyPrefix w with
  | none => rfl
  | some k => rw [keyPrefix_head hk] at h; exact Bool.noConfusion h

theorem sigilOf_none_of {w : List Char}
    (h : headSat (fun x => decide (x = '@' ∨ x = '#' ∨ x = '!' ∨ x = '^')) w = false) :
    sigilOf w = none := by
  cases hs : sigilOf w with
  | none => rfl
  | some c => rw [sigilOf_head hs] at h; exact Bool.noConfusion h

/-- A leading estimate begins with a digit. -/
theorem estSlot_head {w : List Char} {d : Dur} (h : estSlot w = some d) :
    headSat isDigitC w = true := by
  unfold estSlot parseDurND parseDur at h
  cases hr : readNat (w.takeWhile isDigitC) with
  | none => rw [hr] at h; simp at h
  | some k =>
      have hne : w.takeWhile isDigitC ≠ [] := by
        intro hc
        rw [hc] at hr
        simp [readNat] at hr
      cases w with
      | nil => simp [List.takeWhile] at hne
      | cons a t =>
          show isDigitC a = true
          by_cases ha : isDigitC a = true
          · exact ha
          · simp only [Bool.not_eq_true] at ha
            rw [List.takeWhile_cons, ha] at hne
            simp at hne

theorem ciSlot_head {w : List Char} {c : Fin 6} (h : ciSlot w = some c) :
    headSat isDigitC w = true := by
  cases w with
  | nil => simp [ciSlot] at h
  | cons a t =>
      cases t with
      | cons b t' => simp [ciSlot] at h
      | nil =>
          show isDigitC a = true
          have : parseCi [a] = some c := h
          unfold parseCi at this
          cases hr : readNat [a] with
          | none => rw [hr] at this; simp at this
          | some n =>
              unfold readNat readNatAux at hr
              simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.foldl_cons,
                List.foldl_nil] at hr
              cases hc : charDigit a with
              | none => rw [hc] at hr; simp at hr
              | some _ => simp [isDigitC, hc]

theorem startsToken_not_digit {w : List Char} (h : startsToken w = true) :
    headSat isDigitC w = false := by
  unfold startsToken at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · cases hs : sigilOf w with
    | none => rw [hs] at h; simp at h
    | some c => exact headSat_false_of sigil_not_digit w (sigilOf_head hs)
  · cases hk : keyPrefix w with
    | none => rw [hk] at h; simp at h
    | some k =>
        have hkey := keyPrefix_head hk
        cases hd : headSat isDigitC w with
        | false => rfl
        | true =>
            have hx := headSat_false_of digit_not_key w hd
            rw [hkey] at hx
            exact Bool.noConfusion hx

theorem estSlot_none_of_startsToken {w : List Char} (h : startsToken w = true) :
    estSlot w = none := by
  cases he : estSlot w with
  | none => rfl
  | some d =>
      have h2 := startsToken_not_digit h
      rw [estSlot_head he] at h2
      exact Bool.noConfusion h2

theorem ciSlot_none_of_startsToken {w : List Char} (h : startsToken w = true) :
    ciSlot w = none := by
  cases hc : ciSlot w with
  | none => rfl
  | some c =>
      have := startsToken_not_digit h
      rw [ciSlot_head hc] at this
      exact Bool.noConfusion this

/-! ### One induction, five agreements

`kinds` is position-dependent, but most of the *views* are not: a `key:` token
is a key token wherever it sits, because a word that has a key prefix is
neither a ci digit, nor a duration, nor a word that keeps the title open.  That
argument is the same for `@parent`, `#tag`, `!k` and `^id`, so it is proved
once, parameterised by the extraction — this is the induction over the token
grammar.

`flagsOf` is deliberately **not** an instance: a flag name in the title
segment is title text, and §4.1 says so. -/

theorem filterMap_cons_none' {α β : Type} (f : α → Option β) (a : α) (l : List α)
    (h : f a = none) : (a :: l).filterMap f = l.filterMap f := by
  rw [List.filterMap_cons, h]

theorem filterMap_cons_some' {α β : Type} (f : α → Option β) (a : α) (b : β) (l : List α)
    (h : f a = some b) : (a :: l).filterMap f = b :: l.filterMap f := by
  rw [List.filterMap_cons, h]

theorem extract_phase3 {α : Type} (f : TokKind → Option α) (g : List Char → Option α)
    (hword : ∀ w : List Char, f (classifyWord w) = g w) :
    ∀ ts : List Tok, (classifyPhase3 ts).filterMap f = ts.filterMap (fun t => g t.word) := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      show (classifyWord t.word :: classifyPhase3 ts).filterMap f
        = (t :: ts).filterMap (fun x => g x.word)
      cases hg : g t.word with
      | none =>
          rw [filterMap_cons_none' f _ _ (by rw [hword t.word]; exact hg),
            filterMap_cons_none' (fun x : Tok => g x.word) t ts hg, ih]
      | some b =>
          rw [filterMap_cons_some' f _ b _ (by rw [hword t.word]; exact hg),
            filterMap_cons_some' (fun x : Tok => g x.word) t b ts hg, ih]

theorem extract_phase2 {α : Type} (f : TokKind → Option α) (g : List Char → Option α)
    (hword : ∀ w : List Char, f (classifyWord w) = g w)
    (htitle : ∀ w : List Char, startsToken w = false → f (TokKind.title w) = none ∧ g w = none) :
    ∀ ts : List Tok, (classifyPhase2 ts).filterMap f = ts.filterMap (fun t => g t.word) := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      show (if startsToken t.word then classifyPhase3 (t :: ts)
            else TokKind.title t.word :: classifyPhase2 ts).filterMap f = _
      by_cases hst : startsToken t.word = true
      · rw [if_pos hst]
        exact extract_phase3 f g hword (t :: ts)
      · rw [if_neg hst]
        simp only [Bool.not_eq_true] at hst
        obtain ⟨hf, hg⟩ := htitle t.word hst
        rw [filterMap_cons_none' f _ _ hf, ih,
          filterMap_cons_none' (fun x : Tok => g x.word) t ts hg]

theorem extract_phase1 {α : Type} (f : TokKind → Option α) (g : List Char → Option α)
    (hword : ∀ w : List Char, f (classifyWord w) = g w)
    (hest : ∀ (d : Dur) (w : List Char), estSlot w = some d →
      f (TokKind.est d) = none ∧ g w = none)
    (htitle : ∀ w : List Char, startsToken w = false → f (TokKind.title w) = none ∧ g w = none) :
    ∀ ts : List Tok, (classifyPhase1 ts).filterMap f = ts.filterMap (fun t => g t.word) := by
  intro ts
  cases ts with
  | nil => rfl
  | cons t ts =>
      cases he : estSlot t.word with
      | none =>
          show (match estSlot t.word with
                | some d => TokKind.est d :: classifyPhase2 ts
                | none   => classifyPhase2 (t :: ts)).filterMap f = _
          rw [he]
          exact extract_phase2 f g hword htitle (t :: ts)
      | some d =>
          obtain ⟨hf, hg⟩ := hest d t.word he
          show (match estSlot t.word with
                | some d => TokKind.est d :: classifyPhase2 ts
                | none   => classifyPhase2 (t :: ts)).filterMap f = _
          rw [he]
          show (TokKind.est d :: classifyPhase2 ts).filterMap f
            = (t :: ts).filterMap (fun x => g x.word)
          rw [filterMap_cons_none' f _ _ hf, extract_phase2 f g hword htitle ts,
            filterMap_cons_none' (fun x : Tok => g x.word) t ts hg]

/-- **The induction over the token grammar.**  Any view that reads a word the
same way wherever the word sits reads the whole line as a plain scan — so
`due:`, `@parent`, `#tag`, `!k` and `^id` need no positional reasoning at all.
The three hypotheses are exactly the places where position could matter: the ci
slot, the estimate slot, and the title segment. -/
theorem extract_phase0 {α : Type} (f : TokKind → Option α) (g : List Char → Option α)
    (hword : ∀ w : List Char, f (classifyWord w) = g w)
    (hci : ∀ (c : Fin 6) (w : List Char), ciSlot w = some c →
      f (TokKind.ci c) = none ∧ g w = none)
    (hest : ∀ (d : Dur) (w : List Char), estSlot w = some d →
      f (TokKind.est d) = none ∧ g w = none)
    (htitle : ∀ w : List Char, startsToken w = false → f (TokKind.title w) = none ∧ g w = none) :
    ∀ ts : List Tok, (classifyPhase0 ts).filterMap f = ts.filterMap (fun t => g t.word) := by
  intro ts
  cases ts with
  | nil => rfl
  | cons t ts =>
      cases hc : ciSlot t.word with
      | none =>
          show (match ciSlot t.word with
                | some c => TokKind.ci c :: classifyPhase1 ts
                | none   => classifyPhase1 (t :: ts)).filterMap f = _
          rw [hc]
          exact extract_phase1 f g hword hest htitle (t :: ts)
      | some c =>
          obtain ⟨hf, hg⟩ := hci c t.word hc
          show (match ciSlot t.word with
                | some c => TokKind.ci c :: classifyPhase1 ts
                | none   => classifyPhase1 (t :: ts)).filterMap f = _
          rw [hc]
          show (TokKind.ci c :: classifyPhase1 ts).filterMap f
            = (t :: ts).filterMap (fun x => g x.word)
          rw [filterMap_cons_none' f _ _ hf, extract_phase1 f g hword hest htitle ts,
            filterMap_cons_none' (fun x : Tok => g x.word) t ts hg]

/-! ### The tail of the line is classified word by word

Once a token ends the title, every token after it — the `^id` included — is
classified by `classifyWord` alone.  This is what makes "insert the flag after
the `^id`" a safe place to put a flag, and it is the only thing `setFlag`
needs. -/

theorem classifyPhase3_append (a b : List Tok) :
    classifyPhase3 (a ++ b) = classifyPhase3 a ++ classifyPhase3 b := by
  induction a with
  | nil => rfl
  | cons t a' ih =>
      show classifyWord t.word :: classifyPhase3 (a' ++ b)
        = classifyWord t.word :: (classifyPhase3 a' ++ classifyPhase3 b)
      rw [ih]

theorem classifyPhase2_suffix (u : Tok) (b : List Tok) (h : startsToken u.word = true) :
    ∀ a : List Tok, ∃ ks, classifyPhase2 (a ++ u :: b) = ks ++ classifyPhase3 (u :: b) := by
  intro a
  induction a with
  | nil =>
      refine ⟨[], ?_⟩
      show (if startsToken u.word then classifyPhase3 (u :: b)
            else TokKind.title u.word :: classifyPhase2 b) = _
      rw [if_pos h]; rfl
  | cons t a' ih =>
      by_cases hst : startsToken t.word = true
      · refine ⟨classifyPhase3 (t :: a'), ?_⟩
        show (if startsToken t.word then classifyPhase3 (t :: (a' ++ u :: b))
              else TokKind.title t.word :: classifyPhase2 (a' ++ u :: b)) = _
        rw [if_pos hst]
        show classifyPhase3 ((t :: a') ++ u :: b) = _
        rw [classifyPhase3_append]
      · obtain ⟨ks, hks⟩ := ih
        refine ⟨TokKind.title t.word :: ks, ?_⟩
        show (if startsToken t.word then classifyPhase3 (t :: (a' ++ u :: b))
              else TokKind.title t.word :: classifyPhase2 (a' ++ u :: b)) = _
        rw [if_neg hst, hks]
        rfl

theorem classifyPhase1_suffix (u : Tok) (b : List Tok) (h : startsToken u.word = true) :
    ∀ a : List Tok, ∃ ks, classifyPhase1 (a ++ u :: b) = ks ++ classifyPhase3 (u :: b) := by
  intro a
  cases a with
  | nil =>
      have he := estSlot_none_of_startsToken h
      obtain ⟨ks, hks⟩ := classifyPhase2_suffix u b h []
      refine ⟨ks, ?_⟩
      show (match estSlot u.word with
            | some d => TokKind.est d :: classifyPhase2 b
            | none   => classifyPhase2 (u :: b)) = _
      rw [he]
      exact hks
  | cons t a' =>
      cases he : estSlot t.word with
      | none =>
          obtain ⟨ks, hks⟩ := classifyPhase2_suffix u b h (t :: a')
          refine ⟨ks, ?_⟩
          show (match estSlot t.word with
                | some d => TokKind.est d :: classifyPhase2 (a' ++ u :: b)
                | none   => classifyPhase2 (t :: (a' ++ u :: b))) = _
          rw [he]
          exact hks
      | some d =>
          obtain ⟨ks, hks⟩ := classifyPhase2_suffix u b h a'
          refine ⟨TokKind.est d :: ks, ?_⟩
          show (match estSlot t.word with
                | some d => TokKind.est d :: classifyPhase2 (a' ++ u :: b)
                | none   => classifyPhase2 (t :: (a' ++ u :: b))) = _
          rw [he]
          show TokKind.est d :: classifyPhase2 (a' ++ u :: b) = _
          rw [hks]; rfl

/-- **A token after a boundary is classified by its word alone.** -/
theorem classifyPhase0_suffix (a : List Tok) (u : Tok) (b : List Tok)
    (h : startsToken u.word = true) :
    ∃ ks, classifyPhase0 (a ++ u :: b) = ks ++ classifyPhase3 (u :: b) := by
  cases a with
  | nil =>
      have hc := ciSlot_none_of_startsToken h
      obtain ⟨ks, hks⟩ := classifyPhase1_suffix u b h []
      refine ⟨ks, ?_⟩
      show (match ciSlot u.word with
            | some c => TokKind.ci c :: classifyPhase1 b
            | none   => classifyPhase1 (u :: b)) = _
      rw [hc]
      exact hks
  | cons t a' =>
      cases hc : ciSlot t.word with
      | none =>
          obtain ⟨ks, hks⟩ := classifyPhase1_suffix u b h (t :: a')
          refine ⟨ks, ?_⟩
          show (match ciSlot t.word with
                | some c => TokKind.ci c :: classifyPhase1 (a' ++ u :: b)
                | none   => classifyPhase1 (t :: (a' ++ u :: b))) = _
          rw [hc]
          exact hks
      | some c =>
          obtain ⟨ks, hks⟩ := classifyPhase1_suffix u b h a'
          refine ⟨TokKind.ci c :: ks, ?_⟩
          show (match ciSlot t.word with
                | some c => TokKind.ci c :: classifyPhase1 (a' ++ u :: b)
                | none   => classifyPhase1 (t :: (a' ++ u :: b))) = _
          rw [hc]
          show TokKind.ci c :: classifyPhase1 (a' ++ u :: b) = _
          rw [hks]; rfl


/-! ### The views

Every field is a `filterMap` or a `lookup` over `kinds`.  There is exactly one
function per field and it is the only thing that reads that field, which is the
whole point: §4.1 gives `est` two syntactic slots and `ci` two, and a *second*
reader is how `tm edit est=` came to report success and change nothing. -/

def kpOne : TokKind → Option (Key × List Char)
  | .key k v => some (k, v)
  | _        => none

def rawKeyPair (w : List Char) : Option (Key × List Char) :=
  (keyOf w).bind (fun k => (keyValue w).map (fun v => (k, v)))

def keyPairs (r : RawItem) : List (Key × List Char) := (kinds r).filterMap kpOne

def lookupKey (k : Key) (r : RawItem) : Option (List Char) := List.lookup k (keyPairs r)

def extraPairs (r : RawItem) : List (List Char × List Char) :=
  (kinds r).filterMap (fun x => match x with | .extra k v => some (k, v) | _ => none)

def unparsedWords (r : RawItem) : List (List Char) :=
  (kinds r).filterMap (fun x => match x with | .unparsed w => some w | _ => none)

def titleSegment (r : RawItem) : List (List Char) :=
  (kinds r).filterMap (fun x => match x with | .title w => some w | _ => none)

/-- §4.1: "tokens the parser cannot classify stay in the title". -/
def titleWords (r : RawItem) : List (List Char) :=
  (kinds r).filterMap (fun x => match x with
    | .title w => some w | .unparsed w => some w | _ => none)

def tagWords (r : RawItem) : List (List Char) :=
  (kinds r).filterMap (fun x => match x with | .tag t => some t | _ => none)

def flagsOf (r : RawItem) : List Flag :=
  (kinds r).filterMap (fun x => match x with | .flag f => some f | _ => none)

def parentRef (r : RawItem) : Option (List Char) :=
  (kinds r).findSome? (fun x => match x with | .parent p => some p | _ => none)

def prioOf (r : RawItem) : Option (Fin 4) :=
  (kinds r).findSome? (fun x => match x with | .prio k => some k | _ => none)

def idWordOf (r : RawItem) : Option (List Char) :=
  (kinds r).findSome? (fun x => match x with | .id i => some i | _ => none)

def ciSlotOf (r : RawItem) : Option (Fin 6) :=
  (kinds r).findSome? (fun x => match x with | .ci c => some c | _ => none)

def estLeadOf (r : RawItem) : Option Dur :=
  (kinds r).findSome? (fun x => match x with | .est d => some d | _ => none)

/-! ### One view per key -/

def viewDue       (r : RawItem) : Option Moment       := (lookupKey .due r).bind parseMoment
def viewAt        (r : RawItem) : Option (DT × DT)    := (lookupKey .interval r).bind parseInterval
def viewWin       (r : RawItem) : Option WindowRange  := (lookupKey .window r).bind parseWindow
def viewDur       (r : RawItem) : Option Dur          := (lookupKey .dur r).bind parseDurND
def viewPref      (r : RawItem) : Option Pref         := (lookupKey .pref r).bind parsePref
def viewEvery     (r : RawItem) : Option Rule         := (lookupKey .every r).bind parseRule
def viewAfterDone (r : RawItem) : Option AfterDone    := (lookupKey .afterDone r).bind parseAfterDone
def viewOnEvent   (r : RawItem) : Option OnEvent      := (lookupKey .onEvent r).bind parseOnEvent
def viewOnMiss    (r : RawItem) : Option OnMiss       := (lookupKey .onMiss r).bind parseOnMiss
def viewMin       (r : RawItem) : Option Rate         := (lookupKey .floor r).bind parseRate
def viewMax       (r : RawItem) : Option Rate         := (lookupKey .cap r).bind parseRate
def viewAfter     (r : RawItem) : Option (List Dep)   := (lookupKey .after r).bind parseDeps
def viewLoc       (r : RawItem) : Option Loc          := (lookupKey .loc r).bind parseLoc
def viewEstKey    (r : RawItem) : Option Dur          := (lookupKey .est r).bind parseDurND
def viewDemoted   (r : RawItem) : Option (List Stamp) := (lookupKey .demoted r).bind parseStamps
def viewWaiting   (r : RawItem) : Option Nat          := (lookupKey .waiting r).bind parseDate
def viewBuffer    (r : RawItem) : Option Dur          := (lookupKey .buffer r).bind parseDur
def viewCiKey     (r : RawItem) : Option (Fin 6)      := (lookupKey .ci r).bind parseCi

/-- **C2, as one function.**  `ci:` overrides the positional digit — the rule
`--unset ci` could not see, because it read only one of the two slots. -/
def viewCi (r : RawItem) : Option (Fin 6) :=
  match viewCiKey r with
  | some c => some c
  | none   => ciSlotOf r

/-- **C1, as one function.**  §4.1: `est:` overrides the leading estimate. -/
def viewRemainingDur (r : RawItem) : Option Dur :=
  match viewEstKey r with
  | some d => some d
  | none   => estLeadOf r

/-! ### The shape and the recurrence are derived, not stored

§4.1 gives three shape keys and three recurrence keys, and `build_item` states
a precedence between them.  Here that precedence is a *function*, so there is
one answer and it is the same answer everywhere. -/

inductive Shape
  | none
  | point    (m : Moment)
  | interval (start finish : DT)
  | window   (range : WindowRange) (dur : Dur)
deriving DecidableEq, Repr, Inhabited

def viewShape (r : RawItem) : Shape :=
  match viewAt r with
  | some se => .interval se.1 se.2
  | none    =>
    match viewWin r with
    | some rg =>
      (match viewDur r with
       | some d => .window rg d
       | none   => .none)
    | none    =>
      (match viewDue r with
       | some m => .point m
       | none   => .none)

inductive Recur
  | none
  | calendar  (rule : Rule)
  | afterDone (a : AfterDone)
  | onEvent   (e : OnEvent)
deriving DecidableEq, Repr, Inhabited

def viewRecur (r : RawItem) : Recur :=
  match viewEvery r with
  | some rl => .calendar rl
  | none    =>
    match viewAfterDone r with
    | some a => .afterDone a
    | none   =>
      match viewOnEvent r with
      | some e => .onEvent e
      | none   => .none

/-- `at:` wins, whatever else the line says (`build_item`: "conflicting shape
keys (at: wins)"). -/
theorem shape_at_wins (r : RawItem) (s e : DT) (h : viewAt r = some (s, e)) :
    viewShape r = .interval s e := by
  unfold viewShape; rw [h]

/-- `win:` without `dur:` is not a window — §4.1 needs both, and `build_item`
records it as a problem rather than inventing a duration. -/
theorem shape_win_needs_dur (r : RawItem) (rg : WindowRange)
    (h1 : viewAt r = none) (h2 : viewWin r = some rg) (h3 : viewDur r = none) :
    viewShape r = .none := by
  unfold viewShape
  rw [h1]
  show (match viewWin r with
        | some rg => (match viewDur r with | some d => Shape.window rg d | none => Shape.none)
        | none => (match viewDue r with | some m => Shape.point m | none => Shape.none)) = _
  rw [h2]
  show (match viewDur r with | some d => Shape.window rg d | none => Shape.none) = _
  rw [h3]

/-- `due:` is the shape only when neither `at:` nor `win:` claims it. -/
theorem shape_due_is_last (r : RawItem) (m : Moment)
    (h1 : viewAt r = none) (h2 : viewWin r = none) (h3 : viewDue r = some m) :
    viewShape r = .point m := by
  unfold viewShape
  rw [h1]
  show (match viewWin r with
        | some rg => (match viewDur r with | some d => Shape.window rg d | none => Shape.none)
        | none => (match viewDue r with | some m => Shape.point m | none => Shape.none)) = _
  rw [h2]
  show (match viewDue r with | some m => Shape.point m | none => Shape.none) = _
  rw [h3]

/-- `every:` outranks `after-done:` outranks `on-event:`. -/
theorem recur_every_wins (r : RawItem) (rl : Rule) (h : viewEvery r = some rl) :
    viewRecur r = .calendar rl := by
  unfold viewRecur; rw [h]

theorem recur_afterDone_beats_onEvent (r : RawItem) (a : AfterDone)
    (h1 : viewEvery r = none) (h2 : viewAfterDone r = some a) :
    viewRecur r = .afterDone a := by
  unfold viewRecur
  rw [h1]
  show (match viewAfterDone r with
        | some a => Recur.afterDone a
        | none => (match viewOnEvent r with | some e => Recur.onEvent e | none => Recur.none)) = _
  rw [h2]

/-! ### §4.1's two preservation rules

An unknown `key:` is kept **and reported**; a word the classifier cannot place
stays in the title.  Both are properties of `kinds`, so they hold of every
line, not of the ones a test happened to try. -/

inductive Problem
  | unknownKey   (k v : List Char)
  | unclassified (w : List Char)
deriving DecidableEq, Repr

/-- What `tm check` reports about one line. -/
def problems (r : RawItem) : List Problem :=
  (kinds r).filterMap (fun x => match x with
    | .extra k v  => some (Problem.unknownKey k v)
    | .unparsed w => some (Problem.unclassified w)
    | _           => none)

theorem unparsed_sub_title : ∀ (ks : List TokKind) (w : List Char),
    w ∈ ks.filterMap (fun x => match x with | .unparsed w => some w | _ => none) →
    w ∈ ks.filterMap (fun x => match x with
      | .title w => some w | .unparsed w => some w | _ => none) := by
  intro ks
  induction ks with
  | nil => intro w hw; simp at hw
  | cons x xs ih =>
      intro w hw
      cases x <;>
        first
        | (simp only [List.filterMap_cons] at hw ⊢; exact ih w hw)
        | (simp only [List.filterMap_cons, List.mem_cons] at hw ⊢
           exact Or.inr (ih w hw))
        | (simp only [List.filterMap_cons, List.mem_cons] at hw ⊢
           rcases hw with rfl | hw
           · exact Or.inl rfl
           · exact Or.inr (ih w hw))

/-- **§4.1: a token the parser cannot classify stays in the title.** -/
theorem unclassified_token_stays_in_the_title (r : RawItem) :
    ∀ w ∈ unparsedWords r, w ∈ titleWords r :=
  fun w hw => unparsed_sub_title (kinds r) w hw

theorem extra_sub_problems : ∀ (ks : List TokKind) (p : List Char × List Char),
    p ∈ ks.filterMap (fun x => match x with | .extra k v => some (k, v) | _ => none) →
    Problem.unknownKey p.1 p.2 ∈ ks.filterMap (fun x => match x with
      | .extra k v  => some (Problem.unknownKey k v)
      | .unparsed w => some (Problem.unclassified w)
      | _           => none) := by
  intro ks
  induction ks with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
      intro p hp
      cases x <;>
        first
        | (simp only [List.filterMap_cons] at hp ⊢; exact ih p hp)
        | (simp only [List.filterMap_cons, List.mem_cons] at hp ⊢
           exact Or.inr (ih p hp))
        | (simp only [List.filterMap_cons, List.mem_cons] at hp ⊢
           rcases hp with rfl | hp
           · exact Or.inl rfl
           · exact Or.inr (ih p hp))

/-- **§4.1: an unknown `key:` is preserved *and* reported**, never dropped. -/
theorem unknown_key_is_reported (r : RawItem) :
    ∀ p ∈ extraPairs r, Problem.unknownKey p.1 p.2 ∈ problems r :=
  fun p hp => extra_sub_problems (kinds r) p hp


theorem classifySigil_ne_extra (c : Char) (w : List Char) (k v : List Char) :
    classifySigil c w ≠ TokKind.extra k v := by
  unfold classifySigil
  by_cases h1 : w.length = 1
  · rw [if_pos h1]; simp
  · rw [if_neg h1]
    by_cases h2 : c = '@'
    · rw [if_pos h2]; simp
    · rw [if_neg h2]
      by_cases h3 : c = '#'
      · rw [if_pos h3]; simp
      · rw [if_neg h3]
        by_cases h4 : c = '!'
        · rw [if_pos h4]
          unfold classifyBang
          cases parsePrio w <;> simp
        · rw [if_neg h4]
          by_cases h5 : isName w.tail = true
          · rw [if_pos h5]; simp
          · rw [if_neg h5]; simp

theorem classifyPlain_ne_extra (w : List Char) (k v : List Char) :
    classifyPlain w ≠ TokKind.extra k v := by
  unfold classifyPlain
  cases Flag.ofName? w <;> simp

theorem kpOne_classifyBang (w : List Char) : kpOne (classifyBang w) = none := by
  unfold classifyBang; cases parsePrio w <;> rfl

theorem kpOne_classifySigil (c : Char) (w : List Char) : kpOne (classifySigil c w) = none := by
  unfold classifySigil
  by_cases h1 : w.length = 1
  · rw [if_pos h1]; rfl
  · rw [if_neg h1]
    by_cases h2 : c = '@'
    · rw [if_pos h2]; rfl
    · rw [if_neg h2]
      by_cases h3 : c = '#'
      · rw [if_pos h3]; rfl
      · rw [if_neg h3]
        by_cases h4 : c = '!'
        · rw [if_pos h4]; exact kpOne_classifyBang w
        · rw [if_neg h4]
          by_cases h5 : isName w.tail = true
          · rw [if_pos h5]; rfl
          · rw [if_neg h5]; rfl

theorem kpOne_classifyPlain (w : List Char) : kpOne (classifyPlain w) = none := by
  unfold classifyPlain; cases Flag.ofName? w <;> rfl

theorem keyValue_isSome {w k : List Char} (h : keyPrefix w = some k) :
    ∃ v, keyValue w = some v := by
  unfold keyPrefix at h
  cases hsp : splitFirst ':' w with
  | none => rw [hsp] at h; simp at h
  | some p => exact ⟨p.2, by unfold keyValue; rw [hsp]; rfl⟩

/-- A `key:` token is read the same way wherever it sits. -/
theorem kpOne_classifyWord (w : List Char) : kpOne (classifyWord w) = rawKeyPair w := by
  unfold classifyWord rawKeyPair keyOf
  cases hs : sigilOf w with
  | some c =>
      have hk : keyPrefix w = none :=
        keyPrefix_none_of (headSat_false_of sigil_not_key w (sigilOf_head hs))
      rw [hk]
      show kpOne (classifySigil c w) = none
      exact kpOne_classifySigil c w
  | none =>
      cases hk : keyPrefix w with
      | none =>
          show kpOne (classifyPlain w) = none
          exact kpOne_classifyPlain w
      | some k =>
          obtain ⟨v, hv⟩ := keyValue_isSome hk
          show kpOne (classifyKeyed k w)
            = (Key.ofName? k).bind (fun kk => (keyValue w).map (fun x => (kk, x)))
          unfold classifyKeyed
          rw [hv]
          cases hn : Key.ofName? k with
          | none => rfl
          | some kk => rfl

/-- And it is never silently promoted: the `.extra` kind is produced only where
`Key.ofName?` said no. -/
theorem extra_key_is_unknown (w k v : List Char) (h : classifyWord w = .extra k v) :
    Key.ofName? k = none := by
  unfold classifyWord at h
  cases hs : sigilOf w with
  | some c =>
      rw [hs] at h
      have : classifySigil c w = TokKind.extra k v := h
      exact absurd this (classifySigil_ne_extra c w k v)
  | none =>
      rw [hs] at h
      cases hk : keyPrefix w with
      | none =>
          rw [hk] at h
          have : classifyPlain w = TokKind.extra k v := h
          exact absurd this (classifyPlain_ne_extra w k v)
      | some k' =>
          rw [hk] at h
          have h' : classifyKeyed k' w = TokKind.extra k v := h
          unfold classifyKeyed at h'
          cases hn : Key.ofName? k' with
          | none =>
              rw [hn] at h'
              have : k' = k := by
                simp only [TokKind.extra.injEq] at h'
                exact h'.1
              rw [← this]; exact hn
          | some kk => rw [hn] at h'; simp at h'

/-! ### The key views need no positional reasoning

A word with a known `key:` prefix is a key token wherever it sits: it is
neither a ci digit (one character, 0–5), nor a duration (it starts with a
letter), nor a word that keeps the title open (it ends it).  So `lookupKey`
is a plain scan of the token vector, and that is what makes the setters
below provable by list induction rather than by re-deriving the phases. -/

theorem rawKeyPair_none_of_keyPrefix {w : List Char} (h : keyPrefix w = none) :
    rawKeyPair w = none := by
  unfold rawKeyPair keyOf; rw [h]; rfl

theorem rawKeyPair_none_of_digit {w : List Char} (h : headSat isDigitC w = true) :
    rawKeyPair w = none :=
  rawKeyPair_none_of_keyPrefix (keyPrefix_none_of (headSat_false_of digit_not_key w h))

theorem rawKeyPair_none_of_notStarts {w : List Char} (h : startsToken w = false) :
    rawKeyPair w = none := by
  refine rawKeyPair_none_of_keyPrefix ?_
  unfold startsToken at h
  simp only [Bool.or_eq_false_iff] at h
  cases hk : keyPrefix w with
  | none => rfl
  | some k => rw [hk] at h; simp at h

/-- **The key views are a plain scan.**  One instance of the token-grammar
induction; it is the theorem the setters rest on. -/
theorem keyPairs_raw (r : RawItem) :
    keyPairs r = r.toks.filterMap (fun t => rawKeyPair t.word) :=
  extract_phase0 kpOne rawKeyPair kpOne_classifyWord
    (fun _ w h => ⟨rfl, rawKeyPair_none_of_digit (ciSlot_head h)⟩)
    (fun _ w h => ⟨rfl, rawKeyPair_none_of_digit (estSlot_head h)⟩)
    (fun w h => ⟨rfl, rawKeyPair_none_of_notStarts h⟩)
    r.toks


/-! ## The setters, and `view ∘ set = id`

§4.1's `tm edit ^id <key>=<value>`.  There is **one** generic setter, `setKey`,
and one theorem — `lookupKey_setKey` — from which every field's
`view ∘ set = id` follows in three lines.  That is deliberate: the shipped bug
(C1) was one setter out of a family writing the wrong slot, and a family with
one member cannot have an odd one out.

A setter that cannot satisfy the law is not exported as a setter.  `setFlag`
is the one whose domain has to be bounded — §4.1 reads a flag only after a
`@ # ! ^ key:` token, so a flag on a line with no such token would be absorbed
into the title.  It returns `Option`, and the boundary condition is in the
signature rather than in a comment. -/

/-- A value must be one word: non-empty and space-free, or the token it is
written into would re-tokenise as two. -/
def wordWf (w : List Char) : Bool := !w.isEmpty && w.all (fun c => !isSp c)

theorem wordWf_iff (w : List Char) :
    wordWf w = true ↔ (w.isEmpty = false ∧ w.all (fun c => !isSp c) = true) := by
  simp [wordWf]

def keyWord (k : Key) (v : List Char) : List Char := Key.name k ++ ':' :: v

theorem keyPrefix_keyWord (k : Key) (v : List Char) : keyPrefix (keyWord k v) = some (Key.name k) := by
  unfold keyPrefix keyWord
  rw [splitFirst_append ':' (Key.name k) v (fun c hc => (key_name_avoids k c hc).1)]
  simp only [Option.bind_some]
  have h1 : (Key.name k).isEmpty = false := by
    cases hn : Key.name k with
    | nil => exact absurd hn (key_name_ne_nil k)
    | cons a t => rfl
  rw [if_pos (by simp [h1, key_name_isKey k])]

theorem keyValue_keyWord (k : Key) (v : List Char) : keyValue (keyWord k v) = some v := by
  unfold keyValue keyWord
  rw [splitFirst_append ':' (Key.name k) v (fun c hc => (key_name_avoids k c hc).1)]
  rfl

theorem keyOf_keyWord (k : Key) (v : List Char) : keyOf (keyWord k v) = some k := by
  unfold keyOf
  rw [keyPrefix_keyWord k v]
  show Key.ofName? (Key.name k) = some k
  exact key_name_roundtrip k

/-- The token a setter writes is read back as the key and value it wrote. -/
theorem rawKeyPair_keyWord (k : Key) (v : List Char) : rawKeyPair (keyWord k v) = some (k, v) := by
  unfold rawKeyPair
  rw [keyOf_keyWord k v]
  show (keyValue (keyWord k v)).map (fun x => (k, x)) = _
  rw [keyValue_keyWord k v]
  rfl

theorem keyWord_wordWf (k : Key) (v : List Char) (h : wordWf v = true) :
    wordWf (keyWord k v) = true := by
  obtain ⟨hne, hns⟩ := (wordWf_iff v).1 h
  refine (wordWf_iff _).2 ⟨?_, ?_⟩
  · unfold keyWord
    cases hn : Key.name k with
    | nil => exact absurd hn (key_name_ne_nil k)
    | cons a t => rfl
  · simp only [keyWord, List.all_eq_true]
    intro c hc
    rcases List.mem_append.1 hc with h1 | h1
    · simpa using (key_name_avoids k c h1).2
    · simp only [List.mem_cons] at h1
      rcases h1 with rfl | h1
      · rfl
      · exact List.all_eq_true.1 hns c h1

theorem keyWord_not_id (k : Key) (v : List Char) : isIdWord (keyWord k v) = false := by
  unfold isIdWord keyWord
  cases hn : Key.name k with
  | nil => exact absurd hn (key_name_ne_nil k)
  | cons a t =>
      have hk := List.all_eq_true.1 (key_name_isKey k) a (by rw [hn]; simp)
      have hne : ¬ (a = '^') := by intro hc; rw [hc] at hk; exact Bool.noConfusion hk
      simp [hne]

/-! ### The generic key setter -/

def isKeyTok (k : Key) (t : Tok) : Bool := keyOf t.word == some k

def setKeyIn (k : Key) (v : List Char) : List Tok → List Tok
  | []      => []
  | t :: ts => if isKeyTok k t then ⟨t.sep, keyWord k v⟩ :: ts else t :: setKeyIn k v ts

def hasKeyTok (k : Key) (r : RawItem) : Bool := r.toks.any (isKeyTok k)

/-- `tm edit ^id <key>=<value>`: replace the key's token, or insert one before
the `^id` (which is where `insertBeforeId` puts it, with the separator care
that the `est:` insert branch needed). -/
def setKey (k : Key) (v : List Char) (r : RawItem) : RawItem :=
  if hasKeyTok k r then ⟨r.indent, setKeyIn k v r.toks⟩
  else ⟨r.indent, insertBeforeId (keyWord k v) r.toks⟩

/-- `tm edit ^id <key>=` — remove the key's tokens. -/
def unsetKey (k : Key) (r : RawItem) : RawItem :=
  ⟨r.indent, r.toks.filter (fun t => !isKeyTok k t)⟩

theorem setKeyIn_cons_pos (k : Key) (v : List Char) (t : Tok) (ts : List Tok)
    (h : isKeyTok k t = true) : setKeyIn k v (t :: ts) = ⟨t.sep, keyWord k v⟩ :: ts := by
  show (if isKeyTok k t then (⟨t.sep, keyWord k v⟩ : Tok) :: ts else t :: setKeyIn k v ts) = _
  rw [if_pos h]

theorem setKeyIn_cons_neg (k : Key) (v : List Char) (t : Tok) (ts : List Tok)
    (h : isKeyTok k t = false) : setKeyIn k v (t :: ts) = t :: setKeyIn k v ts := by
  show (if isKeyTok k t then (⟨t.sep, keyWord k v⟩ : Tok) :: ts else t :: setKeyIn k v ts) = _
  rw [if_neg (by simp [h])]

theorem insertBeforeId_nil (w : List Char) : insertBeforeId w [] = [⟨[' '], w⟩] := rfl

theorem insertBeforeId_id_nosep (w : List Char) (u : Tok) (us : List Tok)
    (hid : isIdWord u.word = true) (hs : u.sep.isEmpty = true) :
    insertBeforeId w (u :: us) = ⟨[], w⟩ :: ⟨[' '], u.word⟩ :: us := by
  show (if isIdWord u.word then
          (if u.sep.isEmpty then (⟨[], w⟩ : Tok) :: ⟨[' '], u.word⟩ :: us
           else ⟨[' '], w⟩ :: u :: us)
        else u :: insertBeforeId w us) = _
  rw [if_pos hid, if_pos hs]

theorem insertBeforeId_id_sep (w : List Char) (u : Tok) (us : List Tok)
    (hid : isIdWord u.word = true) (hs : u.sep.isEmpty = false) :
    insertBeforeId w (u :: us) = ⟨[' '], w⟩ :: u :: us := by
  show (if isIdWord u.word then
          (if u.sep.isEmpty then (⟨[], w⟩ : Tok) :: ⟨[' '], u.word⟩ :: us
           else ⟨[' '], w⟩ :: u :: us)
        else u :: insertBeforeId w us) = _
  rw [if_pos hid, if_neg (by simp [hs])]

theorem insertBeforeId_other (w : List Char) (u : Tok) (us : List Tok)
    (hid : isIdWord u.word = false) : insertBeforeId w (u :: us) = u :: insertBeforeId w us := by
  show (if isIdWord u.word then
          (if u.sep.isEmpty then (⟨[], w⟩ : Tok) :: ⟨[' '], u.word⟩ :: us
           else ⟨[' '], w⟩ :: u :: us)
        else u :: insertBeforeId w us) = _
  rw [if_neg (by simp [hid])]

theorem rawKeyPair_key {w : List Char} {p : Key × List Char} (h : rawKeyPair w = some p) :
    keyOf w = some p.1 := by
  unfold rawKeyPair at h
  cases hk : keyOf w with
  | none => rw [hk] at h; simp at h
  | some k =>
      rw [hk] at h
      simp only [Option.bind_some] at h
      cases hv : keyValue w with
      | none => rw [hv] at h; simp at h
      | some v =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]

theorem lookup_cons_ne {β : Type} (k k' : Key) (b : β) (l : List (Key × β)) (h : ¬ (k = k')) :
    List.lookup k ((k', b) :: l) = List.lookup k l := by
  show (match k == k' with | true => some b | false => List.lookup k l) = _
  have hb : (k == k') = false := by simpa using h
  rw [hb]

theorem lookup_cons_self {β : Type} (k : Key) (b : β) (l : List (Key × β)) :
    List.lookup k ((k, b) :: l) = some b := by
  show (match k == k with | true => some b | false => List.lookup k l) = _
  rw [show (k == k) = true from by simp]

theorem lookup_cons_skip (k : Key) (t : Tok) (ts : List Tok) (h : isKeyTok k t = false) :
    List.lookup k ((t :: ts).filterMap (fun x => rawKeyPair x.word))
      = List.lookup k (ts.filterMap (fun x => rawKeyPair x.word)) := by
  cases hr : rawKeyPair t.word with
  | none => rw [filterMap_cons_none' (fun x : Tok => rawKeyPair x.word) t ts hr]
  | some p =>
      rw [filterMap_cons_some' (fun x : Tok => rawKeyPair x.word) t p ts hr]
      have hk := rawKeyPair_key hr
      have hne : ¬ (k = p.1) := by
        intro hc
        unfold isKeyTok at h
        rw [hk, ← hc] at h
        simp at h
      exact lookup_cons_ne k p.1 p.2 _ hne

theorem lookup_setKeyIn (k : Key) (v : List Char) : ∀ ts : List Tok,
    ts.any (isKeyTok k) = true →
      List.lookup k ((setKeyIn k v ts).filterMap (fun x => rawKeyPair x.word)) = some v := by
  intro ts
  induction ts with
  | nil => intro h; simp at h
  | cons t ts ih =>
      intro h
      by_cases hk : isKeyTok k t = true
      · rw [setKeyIn_cons_pos k v t ts hk,
          filterMap_cons_some' (fun x : Tok => rawKeyPair x.word) _ (k, v) ts (rawKeyPair_keyWord k v)]
        exact lookup_cons_self k v _
      · simp only [Bool.not_eq_true] at hk
        rw [setKeyIn_cons_neg k v t ts hk, lookup_cons_skip k t _ hk]
        refine ih ?_
        simp only [List.any_cons, Bool.or_eq_true] at h
        rcases h with hc | hc
        · rw [hc] at hk; exact Bool.noConfusion hk
        · exact hc

theorem lookup_insertBeforeId (k : Key) (v : List Char) : ∀ ts : List Tok,
    ts.any (isKeyTok k) = false →
      List.lookup k ((insertBeforeId (keyWord k v) ts).filterMap (fun x => rawKeyPair x.word))
        = some v := by
  intro ts
  induction ts with
  | nil =>
      intro _
      rw [insertBeforeId_nil,
        filterMap_cons_some' (fun x : Tok => rawKeyPair x.word) _ (k, v) [] (rawKeyPair_keyWord k v)]
      exact lookup_cons_self k v _
  | cons u us ih =>
      intro h
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      by_cases hid : isIdWord u.word = true
      · by_cases hsep : u.sep.isEmpty = true
        · rw [insertBeforeId_id_nosep _ u us hid hsep,
            filterMap_cons_some' (fun x : Tok => rawKeyPair x.word) _ (k, v) _ (rawKeyPair_keyWord k v)]
          exact lookup_cons_self k v _
        · simp only [Bool.not_eq_true] at hsep
          rw [insertBeforeId_id_sep _ u us hid hsep,
            filterMap_cons_some' (fun x : Tok => rawKeyPair x.word) _ (k, v) _ (rawKeyPair_keyWord k v)]
          exact lookup_cons_self k v _
      · simp only [Bool.not_eq_true] at hid
        rw [insertBeforeId_other _ u us hid, lookup_cons_skip k u _ h.1]
        exact ih h.2

/-- **`view ∘ set`, generically.**  Whatever key a setter writes, the key view
reads back the value it wrote — replace branch and insert branch alike. -/
theorem lookupKey_setKey (k : Key) (v : List Char) (r : RawItem) :
    lookupKey k (setKey k v r) = some v := by
  unfold lookupKey
  rw [keyPairs_raw]
  unfold setKey
  by_cases h : hasKeyTok k r = true
  · rw [if_pos h]
    exact lookup_setKeyIn k v r.toks (by simpa [hasKeyTok] using h)
  · simp only [Bool.not_eq_true] at h
    rw [if_neg (by simp [h])]
    exact lookup_insertBeforeId k v r.toks (by simpa [hasKeyTok] using h)

theorem lookup_filter_none (k : Key) : ∀ ts : List Tok,
    List.lookup k ((ts.filter (fun t => !isKeyTok k t)).filterMap (fun x => rawKeyPair x.word))
      = none := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rw [List.filter_cons]
      by_cases hk : isKeyTok k t = true
      · rw [if_neg (by simp [hk])]; exact ih
      · simp only [Bool.not_eq_true] at hk
        rw [if_pos (by simp [hk]), lookup_cons_skip k t _ hk]
        exact ih

/-- **`view ∘ unset`.**  What a removal removes, the view stops seeing. -/
theorem lookupKey_unsetKey (k : Key) (r : RawItem) : lookupKey k (unsetKey k r) = none := by
  unfold lookupKey
  rw [keyPairs_raw]
  exact lookup_filter_none k r.toks

/-! ### One `view ∘ set = id` per key

Eighteen fields, eighteen theorems, each of them the obligation `tm edit
^id est=` failed to discharge. -/

def setDue       (m : Moment)        (r : RawItem) : RawItem := setKey .due (renderMoment m) r
def setAt        (s e : DT)          (r : RawItem) : RawItem := setKey .interval (renderInterval s e) r
def setWin       (g : WindowRange)   (r : RawItem) : RawItem := setKey .window (renderWindow g) r
def setDur       (d : Dur)           (r : RawItem) : RawItem := setKey .dur (renderDur d) r
def setPref      (p : Pref)          (r : RawItem) : RawItem := setKey .pref (renderPref p) r
def setEvery     (u : Rule)          (r : RawItem) : RawItem := setKey .every (renderRule u) r
def setAfterDone (a : AfterDone)     (r : RawItem) : RawItem := setKey .afterDone (renderAfterDone a) r
def setOnEvent   (e : OnEvent)       (r : RawItem) : RawItem := setKey .onEvent (renderOnEvent e) r
def setOnMiss    (m : OnMiss)        (r : RawItem) : RawItem := setKey .onMiss (renderOnMiss m) r
def setMin       (q : Rate)          (r : RawItem) : RawItem := setKey .floor (renderRate q) r
def setMax       (q : Rate)          (r : RawItem) : RawItem := setKey .cap (renderRate q) r
def setAfter     (ds : List Dep)     (r : RawItem) : RawItem := setKey .after (renderDeps ds) r
def setLoc       (c : Loc)           (r : RawItem) : RawItem := setKey .loc (renderLoc c) r
def setEst       (d : Dur)           (r : RawItem) : RawItem := setKey .est (renderDur d) r
def setDemoted   (ss : List Stamp)   (r : RawItem) : RawItem := setKey .demoted (renderStamps ss) r
def setWaiting   (n : Nat)           (r : RawItem) : RawItem := setKey .waiting (renderDate n) r
def setBuffer    (d : Dur)           (r : RawItem) : RawItem := setKey .buffer (renderDur d) r
def setCi        (c : Fin 6)         (r : RawItem) : RawItem := setKey .ci (renderCi c) r

theorem view_set_due (m : Moment) (r : RawItem) (h : m.wf = true) :
    viewDue (setDue m r) = some m := by
  unfold viewDue setDue; rw [lookupKey_setKey]
  show parseMoment (renderMoment m) = _
  exact parse_render_moment m h

theorem view_set_at (s e : DT) (r : RawItem) (h : intervalWf s e = true) :
    viewAt (setAt s e r) = some (s, e) := by
  unfold viewAt setAt; rw [lookupKey_setKey]
  show parseInterval (renderInterval s e) = _
  exact parse_render_interval s e h

theorem view_set_win (g : WindowRange) (r : RawItem) (h : windowWf g = true) :
    viewWin (setWin g r) = some g := by
  unfold viewWin setWin; rw [lookupKey_setKey]
  show parseWindow (renderWindow g) = _
  exact parse_render_window g h

theorem view_set_dur (d : Dur) (r : RawItem) (h : d.noDays = true) :
    viewDur (setDur d r) = some d := by
  unfold viewDur setDur; rw [lookupKey_setKey]
  show parseDurND (renderDur d) = _
  exact parse_render_durND d h

theorem view_set_pref (p : Pref) (r : RawItem) : viewPref (setPref p r) = some p := by
  unfold viewPref setPref; rw [lookupKey_setKey]
  show parsePref (renderPref p) = _
  exact parse_render_pref p

theorem view_set_every (u : Rule) (r : RawItem) (h : u.wf = true) :
    viewEvery (setEvery u r) = some u := by
  unfold viewEvery setEvery; rw [lookupKey_setKey]
  show parseRule (renderRule u) = _
  exact parse_render_rule u h

theorem view_set_afterDone (a : AfterDone) (r : RawItem) :
    viewAfterDone (setAfterDone a r) = some a := by
  unfold viewAfterDone setAfterDone; rw [lookupKey_setKey]
  show parseAfterDone (renderAfterDone a) = _
  exact parse_render_afterDone a

theorem view_set_onEvent (e : OnEvent) (r : RawItem) (h : e.wf = true) :
    viewOnEvent (setOnEvent e r) = some e := by
  unfold viewOnEvent setOnEvent; rw [lookupKey_setKey]
  show parseOnEvent (renderOnEvent e) = _
  exact parse_render_onEvent e h

theorem view_set_onMiss (m : OnMiss) (r : RawItem) : viewOnMiss (setOnMiss m r) = some m := by
  unfold viewOnMiss setOnMiss; rw [lookupKey_setKey]
  show parseOnMiss (renderOnMiss m) = _
  exact parse_render_onMiss m

theorem view_set_min (q : Rate) (r : RawItem) : viewMin (setMin q r) = some q := by
  unfold viewMin setMin; rw [lookupKey_setKey]
  show parseRate (renderRate q) = _
  exact parse_render_rate q

theorem view_set_max (q : Rate) (r : RawItem) : viewMax (setMax q r) = some q := by
  unfold viewMax setMax; rw [lookupKey_setKey]
  show parseRate (renderRate q) = _
  exact parse_render_rate q

theorem view_set_after (ds : List Dep) (r : RawItem) (h : depsWf ds = true) :
    viewAfter (setAfter ds r) = some ds := by
  unfold viewAfter setAfter; rw [lookupKey_setKey]
  show parseDeps (renderDeps ds) = _
  exact parse_render_deps ds h

theorem view_set_loc (c : Loc) (r : RawItem) (h : c.wf = true) :
    viewLoc (setLoc c r) = some c := by
  unfold viewLoc setLoc; rw [lookupKey_setKey]
  show parseLoc (renderLoc c) = _
  exact parse_render_loc c h

theorem view_set_estKey (d : Dur) (r : RawItem) (h : d.noDays = true) :
    viewEstKey (setEst d r) = some d := by
  unfold viewEstKey setEst; rw [lookupKey_setKey]
  show parseDurND (renderDur d) = _
  exact parse_render_durND d h

theorem view_set_demoted (ss : List Stamp) (r : RawItem) (h : ss ≠ []) :
    viewDemoted (setDemoted ss r) = some ss := by
  unfold viewDemoted setDemoted; rw [lookupKey_setKey]
  show parseStamps (renderStamps ss) = _
  exact parse_render_stamps ss h

theorem view_set_waiting (n : Nat) (r : RawItem) (h : dayWf n = true) :
    viewWaiting (setWaiting n r) = some n := by
  unfold viewWaiting setWaiting; rw [lookupKey_setKey]
  show parseDate (renderDate n) = _
  exact parse_render_date n h

theorem view_set_buffer (d : Dur) (r : RawItem) : viewBuffer (setBuffer d r) = some d := by
  unfold viewBuffer setBuffer; rw [lookupKey_setKey]
  show parseDur (renderDur d) = _
  exact parse_render_dur d

theorem view_set_ciKey (c : Fin 6) (r : RawItem) : viewCiKey (setCi c r) = some c := by
  unfold viewCiKey setCi; rw [lookupKey_setKey]
  show parseCi (renderCi c) = _
  exact parse_render_ci c

/-! ### The two fields with two slots

C1 and C2.  `est:` overrides the leading estimate and `ci:` overrides the
positional digit, so the setter must write the slot the *view* reads — which is
exactly what `tm edit ^id est=` did not do. -/

/-- **C1 is dead.**  What `setEst` writes, `viewRemainingDur` reports — whatever
leading estimate the line already carried. -/
theorem view_set_remaining (d : Dur) (r : RawItem) (h : d.noDays = true) :
    viewRemainingDur (setEst d r) = some d := by
  unfold viewRemainingDur
  rw [view_set_estKey d r h]

/-- **C2 is dead.**  What `setCi` writes, `viewCi` reports — whatever positional
digit the line already carried. -/
theorem view_set_ci (c : Fin 6) (r : RawItem) : viewCi (setCi c r) = some c := by
  unfold viewCi
  rw [view_set_ciKey c r]

theorem est_key_beats_lead (r : RawItem) (d : Dur) (h : viewEstKey r = some d) :
    viewRemainingDur r = some d := by
  unfold viewRemainingDur; rw [h]

theorem ci_key_beats_positional (r : RawItem) (c : Fin 6) (h : viewCiKey r = some c) :
    viewCi r = some c := by
  unfold viewCi; rw [h]

/-- **The shipped bug as a line.**  `- [ ] 6b Read est:1b ^t3` has a leading
estimate of six blocks and an `est:` of one, and the remaining estimate the
kernel reports is one block.  A setter that wrote the *leading* slot would
change the first number and leave the answer at `1b` — success reported,
nothing changed. -/
theorem est_key_overrides_the_leading_estimate :
    estLeadOf ⟨[], [⟨[' '], ['6','b']⟩, ⟨[' '], ['R','e','a','d']⟩,
                    ⟨[' '], ['e','s','t',':','1','b']⟩, ⟨[' '], ['^','t','3']⟩]⟩
        = some (.simple 6 .blocks) ∧
      viewRemainingDur ⟨[], [⟨[' '], ['6','b']⟩, ⟨[' '], ['R','e','a','d']⟩,
                            ⟨[' '], ['e','s','t',':','1','b']⟩, ⟨[' '], ['^','t','3']⟩]⟩
        = some (.simple 1 .blocks) := by
  constructor <;> decide

/-- **The `--unset ci` shape, stated rather than fixed.**  `ci:` and the
positional digit are two slots; removing the key leaves the digit, so a
complete `--unset ci` has to clear both.  Here is a line where it matters. -/
theorem unset_ci_key_leaves_the_positional_digit :
    viewCi ⟨[], [⟨[' '], ['4']⟩, ⟨[' '], ['R','e','a','d']⟩,
                 ⟨[' '], ['c','i',':','2']⟩, ⟨[' '], ['^','t','3']⟩]⟩
        = some ⟨2, by decide⟩ ∧
      viewCi (unsetKey .ci ⟨[], [⟨[' '], ['4']⟩, ⟨[' '], ['R','e','a','d']⟩,
                                 ⟨[' '], ['c','i',':','2']⟩, ⟨[' '], ['^','t','3']⟩]⟩)
        = some ⟨4, by decide⟩ := by
  constructor <;> decide

/-- `cap:` normalises to `max:` on write, so the alias cannot become a second
place a budget lives. -/
theorem set_max_writes_max (q : Rate) (r : RawItem) :
    lookupKey .cap (setMax q r) = some (renderRate q) ∧ Key.name .cap = ['m','a','x'] :=
  ⟨lookupKey_setKey _ _ _, rfl⟩

/-! ### The setters preserve `CanonicalItem`

The obligation `setEst` had to discharge, generalised: whatever `tm edit
^id <key>=<value>` writes, `parseItem ∘ serializeItem` reads back identically. -/

theorem tok_wf_of_wordWf (sp w : List Char) (hsp : sp.all isSp = true) (hw : wordWf w = true) :
    (Tok.mk sp w).wf = true :=
  (tok_wf_iff _).2 ⟨hsp, ((wordWf_iff w).1 hw).1, ((wordWf_iff w).1 hw).2⟩

theorem toksWf_setKeyIn (k : Key) (v : List Char) (hv : wordWf v = true) :
    ∀ ts : List Tok, toksWf ts = true → toksWf (setKeyIn k v ts) = true := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons u us ih =>
      intro h
      by_cases hk : isKeyTok k u = true
      · rw [setKeyIn_cons_pos k v u us hk]
        have hu : u.wf = true := by
          cases us with
          | nil => simpa [toksWf] using h
          | cons x r => simp only [toksWf, Bool.and_eq_true] at h; exact h.1.1
        have hnew : (Tok.mk u.sep (keyWord k v)).wf = true :=
          tok_wf_of_wordWf u.sep _ ((tok_wf_iff u).1 hu).1 (keyWord_wordWf k v hv)
        cases us with
        | nil => simpa [toksWf] using hnew
        | cons x r =>
            simp only [toksWf, Bool.and_eq_true] at h ⊢
            exact ⟨⟨hnew, h.1.2⟩, h.2⟩
      · simp only [Bool.not_eq_true] at hk
        rw [setKeyIn_cons_neg k v u us hk]
        cases us with
        | nil => simpa [toksWf, setKeyIn] using h
        | cons x r =>
            simp only [toksWf, Bool.and_eq_true] at h
            have hset : ∃ y ys, setKeyIn k v (x :: r) = y :: ys ∧ y.sep = x.sep := by
              by_cases hkx : isKeyTok k x = true
              · exact ⟨⟨x.sep, keyWord k v⟩, r, setKeyIn_cons_pos k v x r hkx, rfl⟩
              · exact ⟨x, setKeyIn k v r, setKeyIn_cons_neg k v x r (by simpa using hkx), rfl⟩
            obtain ⟨y, ys, hy, hysep⟩ := hset
            rw [hy]
            simp only [toksWf, Bool.and_eq_true]
            refine ⟨⟨h.1.1, ?_⟩, ?_⟩
            · rw [hysep]; exact h.1.2
            · have := ih h.2
              rwa [hy] at this

theorem toksWf_insertBeforeId_gen (w : List Char) (hw : wordWf w = true) :
    ∀ ts : List Tok, toksWf ts = true → ts.any (fun t => isIdWord t.word) = true →
      toksWf (insertBeforeId w ts) = true := by
  intro ts
  induction ts with
  | nil => intro _ hid; simp at hid
  | cons u us ih =>
      intro h hid
      by_cases hidu : isIdWord u.word = true
      · by_cases hsep : u.sep.isEmpty = true
        · rw [insertBeforeId_id_nosep w u us hidu hsep]
          simp only [toksWf, Bool.and_eq_true]
          exact ⟨⟨tok_wf_of_wordWf [] w rfl hw, by simp⟩, toksWf_head_sep u [' '] rfl us h⟩
        · simp only [Bool.not_eq_true] at hsep
          rw [insertBeforeId_id_sep w u us hidu hsep]
          simp only [toksWf, Bool.and_eq_true]
          exact ⟨⟨tok_wf_of_wordWf [' '] w rfl hw, by simpa using hsep⟩, h⟩
      · simp only [Bool.not_eq_true] at hidu
        rw [insertBeforeId_other w u us hidu]
        have husid : us.any (fun t => isIdWord t.word) = true := by
          simp only [List.any_cons, Bool.or_eq_true] at hid
          rcases hid with hc | hc
          · rw [hc] at hidu; exact Bool.noConfusion hidu
          · exact hc
        cases us with
        | nil => simp at husid
        | cons x r =>
            simp only [toksWf, Bool.and_eq_true] at h
            obtain ⟨y, ys, hy, hys⟩ := insertBeforeId_head w x r (by simpa using h.1.2)
            rw [hy]
            simp only [toksWf, Bool.and_eq_true]
            refine ⟨⟨h.1.1, by simpa using hys⟩, ?_⟩
            have := ih h.2 husid
            rwa [hy] at this

theorem idWords_setKeyIn (k : Key) (v : List Char) : ∀ ts : List Tok,
    ((setKeyIn k v ts).filter (fun t => isIdWord t.word)).map Tok.word
      = (ts.filter (fun t => isIdWord t.word)).map Tok.word := by
  intro ts
  induction ts with
  | nil => rfl
  | cons u us ih =>
      by_cases hk : isKeyTok k u = true
      · rw [setKeyIn_cons_pos k v u us hk]
        have hnid : isIdWord u.word = false := by
          by_cases hid : isIdWord u.word = true
          · -- an id word has no key prefix, so it is not a key token
            have hs : sigilOf u.word = some '^' := by
              unfold isIdWord at hid
              cases hu : u.word with
              | nil => rw [hu] at hid; simp at hid
              | cons a t =>
                  rw [hu] at hid
                  simp only [List.head?_cons, beq_iff_eq, Option.some.injEq] at hid
                  subst hid
                  rfl
            have hkp : keyPrefix u.word = none :=
              keyPrefix_none_of (headSat_false_of sigil_not_key u.word (sigilOf_head hs))
            unfold isKeyTok keyOf at hk
            rw [hkp] at hk
            simp at hk
          · simpa using hid
        simp [List.filter_cons, hnid, keyWord_not_id k v]
      · simp only [Bool.not_eq_true] at hk
        rw [setKeyIn_cons_neg k v u us hk]
        by_cases hid : isIdWord u.word = true <;> simp [List.filter_cons, hid, ih]

theorem idWords_insertBeforeId_gen (w : List Char) (hw : isIdWord w = false) : ∀ ts : List Tok,
    ((insertBeforeId w ts).filter (fun t => isIdWord t.word)).map Tok.word
      = (ts.filter (fun t => isIdWord t.word)).map Tok.word := by
  intro ts
  induction ts with
  | nil => rw [insertBeforeId_nil]; simp [hw]
  | cons u us ih =>
      by_cases hid : isIdWord u.word = true
      · by_cases hsep : u.sep.isEmpty = true
        · rw [insertBeforeId_id_nosep w u us hid hsep]; simp [hid, hw]
        · simp only [Bool.not_eq_true] at hsep
          rw [insertBeforeId_id_sep w u us hid hsep]; simp [hid, hw]
      · simp only [Bool.not_eq_true] at hid
        rw [insertBeforeId_other w u us hid]
        simp only [List.filter_cons, hid, Bool.false_eq_true, if_false]
        exact ih

/-- **Whatever a key setter writes, the kernel reads back.** -/
theorem setKey_canonical (i : Id) (k : Key) (v : List Char) (r : RawItem)
    (hv : wordWf v = true) (h : CanonicalItem i r = true) :
    CanonicalItem i (setKey k v r) = true := by
  obtain ⟨hind, htw, hids⟩ := (canonical_iff i r).1 h
  refine (canonical_iff i (setKey k v r)).2 ⟨?_, ?_, ?_⟩
  · unfold setKey; by_cases hE : hasKeyTok k r = true <;> simp [hE, hind]
  · unfold setKey
    by_cases hE : hasKeyTok k r = true
    · simp only [hE, if_pos]
      exact toksWf_setKeyIn k v hv r.toks htw
    · simp only [Bool.not_eq_true] at hE
      rw [if_neg (by simp [hE])]
      refine toksWf_insertBeforeId_gen (keyWord k v) (keyWord_wordWf k v hv) r.toks htw ?_
      unfold idToks at hids
      cases hf : r.toks.filter (fun t => isIdWord t.word) with
      | nil => rw [hf] at hids; simp at hids
      | cons t rest =>
          have hm : t ∈ r.toks.filter (fun x => isIdWord x.word) := by rw [hf]; simp
          simp only [List.any_eq_true]
          exact ⟨t, (List.mem_filter.1 hm).1, (List.mem_filter.1 hm).2⟩
  · unfold setKey idToks
    by_cases hE : hasKeyTok k r = true
    · simp only [hE, if_pos]
      rw [idWords_setKeyIn k v r.toks]; exact hids
    · simp only [Bool.not_eq_true] at hE
      rw [if_neg (by simp [hE])]
      rw [idWords_insertBeforeId_gen (keyWord k v) (keyWord_not_id k v) r.toks]
      exact hids

/-- The payoff: `tm edit ^id <key>=<value>` produces a line the kernel parses
back to the same item — same id, same box, same tokens. -/
theorem setKey_line_reparses (i : Id) (g : Glyph) (k : Key) (v : List Char) (r : RawItem)
    (hv : wordWf v = true) (h : CanonicalItem i r = true) :
    parseItem (serializeItem i g (setKey k v r)) = .ok (i, g, setKey k v r) :=
  parse_serialize i g (setKey k v r) (setKey_canonical i k v r hv h)

/-! ### Flags: the one setter whose domain has to be bounded

§4.1 reads a flag only after a `@ # ! ^ key:` token.  On a line with no such
token, a flag word is title text — `- [ ] Lean practice open ^l1` has the word
`open` in its title — so `setFlag` refuses rather than writing something that
reads back differently.  `grammar.rs` calls that `EditError::FlagNeedsBoundary`;
here it is an `Option`, and the theorem below only fires when it succeeded. -/

def insertAfterId (w : List Char) : List Tok → Option (List Tok)
  | []      => none
  | u :: us =>
    if isIdWord u.word then some (u :: ⟨[' '], w⟩ :: us)
    else (insertAfterId w us).map (fun r => u :: r)

def setFlag (f : Flag) (r : RawItem) : Option RawItem :=
  (insertAfterId (Flag.name f) r.toks).map (fun ts => ⟨r.indent, ts⟩)

theorem isIdWord_startsToken {w : List Char} (h : isIdWord w = true) : startsToken w = true := by
  unfold isIdWord at h
  cases hu : w with
  | nil => rw [hu] at h; simp at h
  | cons a t =>
      rw [hu] at h
      simp only [List.head?_cons, beq_iff_eq, Option.some.injEq] at h
      subst h
      rfl

theorem classifyWord_flag (f : Flag) : classifyWord (Flag.name f) = .flag f := by
  have hs : sigilOf (Flag.name f) = none := by cases f <;> rfl
  have hk : keyPrefix (Flag.name f) = none := by
    unfold keyPrefix
    rw [splitFirst_none ':' (Flag.name f) (flag_name_no_colon f)]
    rfl
  unfold classifyWord
  rw [hs, hk]
  show classifyPlain (Flag.name f) = _
  unfold classifyPlain
  rw [flag_name_roundtrip f]

theorem insertAfterId_shape (w : List Char) : ∀ ts ts' : List Tok,
    insertAfterId w ts = some ts' →
      ∃ a u b, ts' = a ++ u :: ⟨[' '], w⟩ :: b ∧ isIdWord u.word = true := by
  intro ts
  induction ts with
  | nil => intro ts' h; simp [insertAfterId] at h
  | cons u us ih =>
      intro ts' h
      by_cases hid : isIdWord u.word = true
      · rw [show insertAfterId w (u :: us) = some (u :: ⟨[' '], w⟩ :: us) from by
              simp [insertAfterId, hid]] at h
        simp only [Option.some.injEq] at h
        exact ⟨[], u, us, by rw [← h]; rfl, hid⟩
      · rw [show insertAfterId w (u :: us) = (insertAfterId w us).map (fun r => u :: r) from by
              simp [insertAfterId, hid]] at h
        cases hr : insertAfterId w us with
        | none => rw [hr] at h; simp at h
        | some vs =>
            rw [hr] at h
            simp only [Option.map_some, Option.some.injEq] at h
            obtain ⟨a, u2, b, hb, hid2⟩ := ih vs hr
            exact ⟨u :: a, u2, b, by rw [← h, hb]; rfl, hid2⟩

/-- **`view ∘ set` for a flag.**  When `setFlag` succeeds, the flag is in the
line's flag set — and it is there because the `^id` before it ended the title,
which is the only place a flag can safely go. -/
theorem view_set_flag (f : Flag) (r r' : RawItem) (h : setFlag f r = some r') :
    f ∈ flagsOf r' := by
  unfold setFlag at h
  cases hi : insertAfterId (Flag.name f) r.toks with
  | none => rw [hi] at h; simp at h
  | some ts =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨a, u, b, hb, hid⟩ := insertAfterId_shape (Flag.name f) r.toks ts hi
      obtain ⟨ks, hks⟩ := classifyPhase0_suffix a u (⟨[' '], Flag.name f⟩ :: b)
        (isIdWord_startsToken hid)
      have hkinds : kinds r' = ks ++ classifyPhase3 (u :: ⟨[' '], Flag.name f⟩ :: b) := by
        unfold kinds
        rw [← h]
        show classifyPhase0 ts = _
        rw [hb]
        exact hks
      have hmem : TokKind.flag f ∈ kinds r' := by
        rw [hkinds]
        refine List.mem_append_right _ ?_
        show TokKind.flag f ∈ classifyWord u.word :: classifyWord (Flag.name f) :: classifyPhase3 b
        rw [classifyWord_flag f]
        simp
      unfold flagsOf
      exact List.mem_filterMap.2 ⟨TokKind.flag f, hmem, rfl⟩

/-- And the refusal is real: with no `^id` on the line there is no safe place,
so `setFlag` returns `none` rather than writing a word that reads back as
title text. -/
theorem insertAfterId_none (w : List Char) : ∀ ts : List Tok,
    ts.all (fun t => !isIdWord t.word) = true → insertAfterId w ts = none := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons u us ih =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      show (if isIdWord u.word then some (u :: ⟨[' '], w⟩ :: us)
            else (insertAfterId w us).map (fun x => u :: x)) = none
      rw [if_neg (by simpa using h.1), ih h.2]
      rfl

theorem setFlag_needs_a_boundary (f : Flag) (r : RawItem)
    (h : r.toks.all (fun t => !isIdWord t.word) = true) : setFlag f r = none := by
  unfold setFlag
  rw [insertAfterId_none (Flag.name f) r.toks h]
  rfl


/-! ## Round trip B, at the level of fields

Round trip A is `serialize_parse`: the token vector *is* the bytes, so a line
the parser accepts writes back byte for byte.  Round trip B is the other
direction and it is the one the plan calls the stage's biggest unknown:
**everything the kernel writes, it reads back as the same fields**.

The statement is `viewFields (renderItem i f) = f` on `Fields.wf`, and the
proof is an induction over the token grammar: `renderToks` lays a `Fields` out
as `[ci] [est] title… ^id @parent #tags !k key:value… extra… flag…`, and the
four-phase classifier is run over exactly that shape.

**Two layout choices are load-bearing and are choices, not accidents.**

* The `^id` **leads the token run**, right after the title.  §4.1 says tokens
  come in any order; putting the id first makes "the title ended here" true by
  construction, because the id is the one token that is always present.  With
  the id last, the first token could be any of seven blocks and the proof would
  be a seven-way case analysis of something that has no reason to be a case
  analysis.  It is also what makes a trailing flag safe (§4.1 reads a flag only
  after a `@ # ! ^ key:` token) with no side condition at all.
* The **title word guard** is `Fields.wf`'s `slotGuard`, and it is `grammar.rs`'s
  `EditError::Ambiguous` written as a precondition: a title that begins with
  `5` would be eaten by the empty ci slot, and one that begins with `2h` by the
  empty estimate slot.  The kernel refuses to write such a line rather than
  writing one that reads back differently. -/

structure Fields where
  ci        : Option (Fin 6)                := Option.none
  estLead   : Option Dur                    := Option.none
  title     : List (List Char)              := []
  parent    : Option (List Char)            := Option.none
  tags      : List (List Char)              := []
  prio      : Option (Fin 4)                := Option.none
  due       : Option Moment                 := Option.none
  interval  : Option (DT × DT)              := Option.none
  window    : Option WindowRange            := Option.none
  dur       : Option Dur                    := Option.none
  pref      : Option Pref                   := Option.none
  every     : Option Rule                   := Option.none
  afterDone : Option AfterDone              := Option.none
  onEvent   : Option OnEvent                := Option.none
  onMiss    : Option OnMiss                 := Option.none
  floor     : Option Rate                   := Option.none
  cap       : Option Rate                   := Option.none
  after     : Option (List Dep)             := Option.none
  loc       : Option Loc                    := Option.none
  est       : Option Dur                    := Option.none
  demoted   : Option (List Stamp)           := Option.none
  waiting   : Option Nat                    := Option.none
  buffer    : Option Dur                    := Option.none
  ciKey     : Option (Fin 6)                := Option.none
  extra     : List (List Char × List Char)  := []
  unparsed  : List (List Char)              := []
  flags     : List Flag                     := []
deriving DecidableEq, Repr, Inhabited

/-- §4.1's table order, as data.  Every `key:` the kernel writes is one row of
this list, so "which keys exist" is a fact about one value. -/
def kvList (f : Fields) : List (Key × Option (List Char)) :=
  [(Key.due,       f.due.map renderMoment),
   (Key.interval,  f.interval.map (fun p => renderInterval p.1 p.2)),
   (Key.window,    f.window.map renderWindow),
   (Key.dur,       f.dur.map renderDur),
   (Key.pref,      f.pref.map renderPref),
   (Key.every,     f.every.map renderRule),
   (Key.afterDone, f.afterDone.map renderAfterDone),
   (Key.onEvent,   f.onEvent.map renderOnEvent),
   (Key.onMiss,    f.onMiss.map renderOnMiss),
   (Key.floor,     f.floor.map renderRate),
   (Key.cap,       f.cap.map renderRate),
   (Key.after,     f.after.map renderDeps),
   (Key.loc,       f.loc.map renderLoc),
   (Key.est,       f.est.map renderDur),
   (Key.demoted,   f.demoted.map renderStamps),
   (Key.waiting,   f.waiting.map renderDate),
   (Key.buffer,    f.buffer.map renderDur),
   (Key.ci,        f.ciKey.map renderCi)]

def kvOf (f : Fields) : List (Key × List Char) :=
  (kvList f).filterMap (fun p => p.2.map (fun v => (p.1, v)))

def tokOf (w : List Char) : Tok := ⟨[' '], w⟩

def keyToks   (f : Fields) : List Tok := (kvOf f).map (fun p => tokOf (keyWord p.1 p.2))
def extraToks (f : Fields) : List Tok := f.extra.map (fun p => tokOf (p.1 ++ ':' :: p.2))
def unparsedToks (f : Fields) : List Tok := f.unparsed.map tokOf
def flagToks  (f : Fields) : List Tok := f.flags.map (fun fl => tokOf (Flag.name fl))
def tagToks   (f : Fields) : List Tok := f.tags.map (fun t => tokOf ('#' :: t))
def titleToks (f : Fields) : List Tok := f.title.map tokOf

def parentToks (f : Fields) : List Tok := (f.parent.map (fun p => tokOf ('@' :: p))).toList
def prioToks   (f : Fields) : List Tok := (f.prio.map (fun k => tokOf (renderPrio k))).toList
def ciToks     (f : Fields) : List Tok := (f.ci.map (fun c => tokOf (renderCi c))).toList
def estToks    (f : Fields) : List Tok := (f.estLead.map (fun d => tokOf (renderDur d))).toList

/-- The token run after the title.  The `^id` leads it — see the header. -/
def midToks (i : Id) (f : Fields) : List Tok :=
  tokOf ('^' :: i) ::
    (parentToks f ++ tagToks f ++ prioToks f ++ keyToks f ++ extraToks f
      ++ unparsedToks f ++ flagToks f)

def renderToks (i : Id) (f : Fields) : List Tok :=
  ciToks f ++ estToks f ++ titleToks f ++ midToks i f

def renderItem (i : Id) (f : Fields) : RawItem := ⟨[], renderToks i f⟩

/-! ### The key half: every `key:` renders and parses back

`keyPairs` is a plain scan (`keyPairs_raw`), so this half needs no phase
reasoning at all — only that no other block of the layout writes a token with
a known key prefix. -/

theorem filterMap_map_none' {α β : Type} (g : α → Tok) (fv : Tok → Option β)
    (h : ∀ a, fv (g a) = none) : ∀ l : List α, (l.map g).filterMap fv = [] := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, filterMap_cons_none' fv (g a) _ (h a), ih]

theorem filterMap_map_id' {α β : Type} (g : α → Tok) (fv : Tok → Option β) (k : α → β)
    (h : ∀ a, fv (g a) = some (k a)) : ∀ l : List α, (l.map g).filterMap fv = l.map k := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, filterMap_cons_some' fv (g a) (k a) _ (h a), ih, List.map_cons]

theorem filterMap_opt_none {α β : Type} (x : Option α) (g : α → Tok) (fv : Tok → Option β)
    (h : ∀ a, fv (g a) = none) : ((x.map g).toList).filterMap fv = [] := by
  cases x with
  | none => rfl
  | some a =>
      show ([g a] : List Tok).filterMap fv = []
      rw [filterMap_cons_none' fv (g a) [] (h a)]
      rfl

/-- The characters a key's own token starts with: a lower-case letter. -/
theorem rawKeyPair_tokOf_sigil (c : Char) (w : List Char)
    (h : sigilOf w = some c) : rawKeyPair w = none :=
  rawKeyPair_none_of_keyPrefix
    (keyPrefix_none_of (headSat_false_of sigil_not_key w (sigilOf_head h)))

theorem sigilOf_cons (c : Char) (t : List Char)
    (h : (c == '@' || c == '#' || c == '!' || c == '^') = true) : sigilOf (c :: t) = some c := by
  show (if (c == '@' || c == '#' || c == '!' || c == '^') = true then some c else none) = _
  rw [if_pos h]

theorem rawKeyPair_at (p : List Char) : rawKeyPair ('@' :: p) = none :=
  rawKeyPair_tokOf_sigil '@' _ (sigilOf_cons '@' p (by decide))

theorem rawKeyPair_hash (p : List Char) : rawKeyPair ('#' :: p) = none :=
  rawKeyPair_tokOf_sigil '#' _ (sigilOf_cons '#' p (by decide))

theorem rawKeyPair_caret (p : List Char) : rawKeyPair ('^' :: p) = none :=
  rawKeyPair_tokOf_sigil '^' _ (sigilOf_cons '^' p (by decide))

theorem rawKeyPair_prio (k : Fin 4) : rawKeyPair (renderPrio k) = none :=
  rawKeyPair_tokOf_sigil '!' _ (sigilOf_cons '!' _ (by decide))

theorem renderCi_head (c : Fin 6) : headSat isDigitC (renderCi c) = true := by
  show isDigitC (digitChar c.val) = true
  simp [isDigitC, digit_roundtrip c.val (by omega)]

theorem rawKeyPair_ci (c : Fin 6) : rawKeyPair (renderCi c) = none :=
  rawKeyPair_none_of_digit (renderCi_head c)

theorem renderDur_headSat (d : Dur) : headSat isDigitC (renderDur d) = true := by
  obtain ⟨c, hc, hd⟩ := renderDur_head_digit d
  cases hw : renderDur d with
  | nil => rw [hw] at hc; simp at hc
  | cons a t =>
      rw [hw] at hc
      simp only [List.head?_cons, Option.some.injEq] at hc
      subst hc
      show isDigitC a = true
      exact hd

theorem rawKeyPair_estWordD (d : Dur) : rawKeyPair (renderDur d) = none :=
  rawKeyPair_none_of_digit (renderDur_headSat d)

theorem keyPrefix_flag (fl : Flag) : keyPrefix (Flag.name fl) = none := by
  unfold keyPrefix
  rw [splitFirst_none ':' (Flag.name fl) (flag_name_no_colon fl)]
  rfl

theorem rawKeyPair_flag (fl : Flag) : rawKeyPair (Flag.name fl) = none :=
  rawKeyPair_none_of_keyPrefix (keyPrefix_flag fl)

/-- A word `k:v` whose `k` is a well-formed key spelling the kernel does not
know is an `.extra`: its key is read, and `Key.ofName?` refuses it. -/
def extraPairWf (p : List Char × List Char) : Bool :=
  wordWf (p.1 ++ ':' :: p.2) && !p.1.isEmpty && p.1.all isKeyC && (Key.ofName? p.1).isNone

theorem keyPrefix_extra {p : List Char × List Char} (h : extraPairWf p = true) :
    keyPrefix (p.1 ++ ':' :: p.2) = some p.1 := by
  simp only [extraPairWf, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨_, hne⟩, hall⟩, _⟩ := h
  unfold keyPrefix
  rw [splitFirst_append ':' p.1 p.2 (by
    intro c hc hcc
    subst hcc
    have := List.all_eq_true.1 hall ':' hc
    exact Bool.noConfusion this)]
  simp only [Option.bind_some]
  rw [if_pos (by simp [hne, hall])]

theorem rawKeyPair_extra {p : List Char × List Char} (h : extraPairWf p = true) :
    rawKeyPair (p.1 ++ ':' :: p.2) = none := by
  have hkn : Key.ofName? p.1 = none := by
    simp only [extraPairWf, Bool.and_eq_true] at h
    cases hn : Key.ofName? p.1 with
    | none => rfl
    | some k => rw [hn] at h; simp at h
  unfold rawKeyPair keyOf
  rw [keyPrefix_extra h]
  show ((Key.ofName? p.1).bind
      (fun k => (keyValue (p.1 ++ ':' :: p.2)).map (fun v => (k, v)))) = none
  rw [hkn]
  rfl

/-! ### Well-formedness of a `Fields`

Twenty decidable conjuncts.  Eight are about the *tokens* the layout will
write (a title word must not end the title, an unknown key must really be
unknown, a value must be one word) and twelve are the value-level side
conditions the round trips above already carry. -/

def titleWordWf (w : List Char) : Bool := wordWf w && !startsToken w

def unparsedWordWf (w : List Char) : Bool := wordWf w && (classifyWord w == TokKind.unparsed w)

def optWf {α : Type} (p : α → Bool) : Option α → Bool
  | none   => true
  | some a => p a

/-- `grammar.rs`'s `EditError::Ambiguous`, as a precondition: with the ci slot
empty a title beginning with `5` would be eaten, and with the estimate slot
empty one beginning with `2h` would be. -/
def slotGuard (f : Fields) : Bool :=
  match f.title.head? with
  | none   => true
  | some w =>
    (match f.estLead with
     | some _ => true
     | none   => (estSlot w).isNone) &&
    (match f.ci with
     | some _ => true
     | none   =>
       match f.estLead with
       | some _ => true
       | none   => (ciSlot w).isNone)

def Fields.wf (i : Id) (f : Fields) : Bool :=
  isName i
  && f.title.all titleWordWf
  && f.unparsed.all unparsedWordWf
  && f.extra.all extraPairWf
  && optWf (fun p => wordWf p && !p.isEmpty) f.parent
  && f.tags.all (fun t => wordWf t && !t.isEmpty)
  && (kvOf f).all (fun p => wordWf p.2)
  && slotGuard f
  && optWf Dur.noDays f.estLead
  && optWf Moment.wf f.due
  && optWf (fun p => intervalWf p.1 p.2) f.interval
  && optWf windowWf f.window
  && optWf Dur.noDays f.dur
  && optWf Rule.wf f.every
  && optWf OnEvent.wf f.onEvent
  && optWf depsWf f.after
  && optWf Loc.wf f.loc
  && optWf Dur.noDays f.est
  && optWf (fun ss => !List.isEmpty ss) f.demoted
  && optWf dayWf f.waiting

/-! ### The key half of round trip B -/

theorem filterMap_map_none_mem {α β : Type} (g : α → Tok) (fv : Tok → Option β) :
    ∀ l : List α, (∀ a ∈ l, fv (g a) = none) → (l.map g).filterMap fv = [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      rw [List.map_cons, filterMap_cons_none' fv (g a) _ (h a (by simp)),
        ih (fun x hx => h x (by simp [hx]))]

theorem classifyWord_unparsed_sigil {w w' : List Char} (h : classifyWord w = TokKind.unparsed w') :
    ∃ c, sigilOf w = some c := by
  cases hs : sigilOf w with
  | some c => exact ⟨c, rfl⟩
  | none =>
      exfalso
      unfold classifyWord at h
      rw [hs] at h
      cases hk : keyPrefix w with
      | some k =>
          rw [hk] at h
          have h' : classifyKeyed k w = TokKind.unparsed w' := h
          unfold classifyKeyed at h'
          cases hn : Key.ofName? k with
          | none => rw [hn] at h'; simp at h'
          | some kk => rw [hn] at h'; simp at h'
      | none =>
          rw [hk] at h
          have h' : classifyPlain w = TokKind.unparsed w' := h
          unfold classifyPlain at h'
          cases hn : Flag.ofName? w with
          | none => rw [hn] at h'; simp at h'
          | some fl => rw [hn] at h'; simp at h'

theorem rawKeyPair_unparsed {w : List Char} (h : unparsedWordWf w = true) :
    rawKeyPair w = none := by
  simp only [unparsedWordWf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨c, hc⟩ := classifyWord_unparsed_sigil h.2
  exact rawKeyPair_tokOf_sigil c w hc

/-- **The key half of round trip B.**  Only the key block writes key tokens, so
the eighteen `key:` fields are exactly what `kvOf` says they are. -/
theorem keyPairs_render (i : Id) (f : Fields)
    (htitle : f.title.all titleWordWf = true)
    (hunp : f.unparsed.all unparsedWordWf = true)
    (hextra : f.extra.all extraPairWf = true) :
    keyPairs (renderItem i f) = kvOf f := by
  have RKc : ∀ (c : Fin 6), (fun t : Tok => rawKeyPair t.word) (tokOf (renderCi c)) = none :=
    fun c => rawKeyPair_ci c
  rw [keyPairs_raw]
  show ((ciToks f ++ estToks f ++ titleToks f ++ midToks i f).filterMap
        (fun t : Tok => rawKeyPair t.word)) = kvOf f
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append]
  rw [show (ciToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_opt_none f.ci (fun c => tokOf (renderCi c)) _ RKc]
  rw [show (estToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_opt_none f.estLead (fun d => tokOf (renderDur d)) _
          (fun d => rawKeyPair_estWordD d)]
  rw [show (titleToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_map_none_mem tokOf _ f.title
          (fun w hw => rawKeyPair_none_of_notStarts (by
            have := List.all_eq_true.1 htitle w hw
            simp only [titleWordWf, Bool.and_eq_true, Bool.not_eq_true'] at this
            exact this.2))]
  show ([] ++ [] ++ [] ++ (midToks i f).filterMap (fun t : Tok => rawKeyPair t.word)) = _
  simp only [List.nil_append]
  show ((tokOf ('^' :: i) :: (parentToks f ++ tagToks f ++ prioToks f ++ keyToks f
        ++ extraToks f ++ unparsedToks f ++ flagToks f)).filterMap
        (fun t : Tok => rawKeyPair t.word)) = _
  rw [filterMap_cons_none' (fun t : Tok => rawKeyPair t.word) _ _ (rawKeyPair_caret i)]
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append,
    List.filterMap_append, List.filterMap_append, List.filterMap_append]
  rw [show (parentToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_opt_none f.parent (fun p => tokOf ('@' :: p)) _ (fun p => rawKeyPair_at p)]
  rw [show (tagToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_map_none_mem (fun t => tokOf ('#' :: t)) _ f.tags
          (fun t _ => rawKeyPair_hash t)]
  rw [show (prioToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_opt_none f.prio (fun k => tokOf (renderPrio k)) _ (fun k => rawKeyPair_prio k)]
  rw [show (extraToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_map_none_mem (fun p => tokOf (p.1 ++ ':' :: p.2)) _ f.extra
          (fun p hp => rawKeyPair_extra (List.all_eq_true.1 hextra p hp))]
  rw [show (unparsedToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_map_none_mem tokOf _ f.unparsed
          (fun w hw => rawKeyPair_unparsed (List.all_eq_true.1 hunp w hw))]
  rw [show (flagToks f).filterMap (fun t : Tok => rawKeyPair t.word) = [] from
        filterMap_map_none_mem (fun fl => tokOf (Flag.name fl)) _ f.flags
          (fun fl _ => rawKeyPair_flag fl)]
  rw [show (keyToks f).filterMap (fun t : Tok => rawKeyPair t.word) = kvOf f from
        (filterMap_map_id' (fun p => tokOf (keyWord p.1 p.2)) _ (fun p => p)
          (fun p => rawKeyPair_keyWord p.1 p.2) (kvOf f)).trans (List.map_id _)]
  simp

/-! ### The assoc-list lookup

`kvList` is the §4.1 table as data and its keys are distinct, so a lookup in
the rendered line is a lookup in the table. -/

theorem lookup_pair_self {β : Type} (p : Key × β) (l : List (Key × β)) :
    List.lookup p.1 (p :: l) = some p.2 := by
  show (match p.1 == p.1 with | true => some p.2 | false => List.lookup p.1 l) = _
  rw [show (p.1 == p.1) = true from by simp]

theorem lookup_pair_ne {β : Type} (k : Key) (p : Key × β) (l : List (Key × β))
    (h : ¬ (k = p.1)) : List.lookup k (p :: l) = List.lookup k l := by
  show (match k == p.1 with | true => some p.2 | false => List.lookup k l) = _
  rw [show (k == p.1) = false from by simpa using h]

theorem lookup_filterMap_notMem {β : Type} (k : Key) : ∀ l : List (Key × Option β),
    k ∉ l.map Prod.fst →
    List.lookup k (l.filterMap (fun p => p.2.map (fun v => (p.1, v)))) = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p t ih =>
      intro h
      simp only [List.map_cons, List.mem_cons, not_or] at h
      cases hv : p.2 with
      | none =>
          rw [filterMap_cons_none' _ p t (by rw [hv]; rfl)]
          exact ih h.2
      | some v =>
          rw [filterMap_cons_some' _ p (p.1, v) t (by rw [hv]; rfl)]
          rw [lookup_pair_ne k (p.1, v) _ h.1]
          exact ih h.2

theorem lookup_filterMap_pairs {β : Type} (k : Key) : ∀ l : List (Key × Option β),
    (l.map Prod.fst).Nodup →
    List.lookup k (l.filterMap (fun p => p.2.map (fun v => (p.1, v))))
      = (List.lookup k l).join := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p t ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hk : k = p.1
      · rw [hk, lookup_pair_self p t]
        cases hv : p.2 with
        | none =>
            rw [filterMap_cons_none' _ p t (by rw [hv]; rfl)]
            rw [lookup_filterMap_notMem p.1 t hnd.1]
            rfl
        | some v =>
            rw [filterMap_cons_some' _ p (p.1, v) t (by rw [hv]; rfl)]
            rw [lookup_pair_self (p.1, v) _]
            rfl
      · rw [lookup_pair_ne k p t hk]
        cases hv : p.2 with
        | none =>
            rw [filterMap_cons_none' _ p t (by rw [hv]; rfl)]
            exact ih hnd.2
        | some v =>
            rw [filterMap_cons_some' _ p (p.1, v) t (by rw [hv]; rfl)]
            rw [lookup_pair_ne k (p.1, v) _ hk]
            exact ih hnd.2

theorem kvList_keys (f : Fields) :
    (kvList f).map Prod.fst =
      [Key.due, Key.interval, Key.window, Key.dur, Key.pref, Key.every, Key.afterDone,
       Key.onEvent, Key.onMiss, Key.floor, Key.cap, Key.after, Key.loc, Key.est,
       Key.demoted, Key.waiting, Key.buffer, Key.ci] := rfl

theorem kvList_nodup (f : Fields) : ((kvList f).map Prod.fst).Nodup := by
  rw [kvList_keys]; decide

theorem lookupKey_render (i : Id) (f : Fields) (k : Key)
    (htitle : f.title.all titleWordWf = true)
    (hunp : f.unparsed.all unparsedWordWf = true)
    (hextra : f.extra.all extraPairWf = true) :
    lookupKey k (renderItem i f) = (List.lookup k (kvList f)).join := by
  unfold lookupKey
  rw [keyPairs_render i f htitle hunp hextra]
  exact lookup_filterMap_pairs k (kvList f) (kvList_nodup f)

theorem bind_map_render {α : Type} (x : Option α) (rend : α → List Char)
    (prs : List Char → Option α) (h : ∀ a, x = some a → prs (rend a) = some a) :
    (x.map rend).bind prs = x := by
  cases x with
  | none => rfl
  | some a =>
      show prs (rend a) = some a
      exact h a rfl

theorem optWf_some {α : Type} {p : α → Bool} {x : Option α} {a : α}
    (h : optWf p x = true) (hx : x = some a) : p a = true := by
  rw [hx] at h; exact h


/-! ### One theorem per key: what the layout writes, the view reads back

Eighteen corollaries of `lookupKey_render`, one per `key:` in §4.1's table.
The `cap:` alias has no row of its own because it has no field of its own: it
is `Key.cap`, written `max`. -/

theorem kv_due (f : Fields) :
    (List.lookup Key.due (kvList f)).join = f.due.map renderMoment := rfl

theorem kv_interval (f : Fields) :
    (List.lookup Key.interval (kvList f)).join = f.interval.map (fun p => renderInterval p.1 p.2) := rfl

theorem kv_window (f : Fields) :
    (List.lookup Key.window (kvList f)).join = f.window.map renderWindow := rfl

theorem kv_dur (f : Fields) :
    (List.lookup Key.dur (kvList f)).join = f.dur.map renderDur := rfl

theorem kv_pref (f : Fields) :
    (List.lookup Key.pref (kvList f)).join = f.pref.map renderPref := rfl

theorem kv_every (f : Fields) :
    (List.lookup Key.every (kvList f)).join = f.every.map renderRule := rfl

theorem kv_afterDone (f : Fields) :
    (List.lookup Key.afterDone (kvList f)).join = f.afterDone.map renderAfterDone := rfl

theorem kv_onEvent (f : Fields) :
    (List.lookup Key.onEvent (kvList f)).join = f.onEvent.map renderOnEvent := rfl

theorem kv_onMiss (f : Fields) :
    (List.lookup Key.onMiss (kvList f)).join = f.onMiss.map renderOnMiss := rfl

theorem kv_floor (f : Fields) :
    (List.lookup Key.floor (kvList f)).join = f.floor.map renderRate := rfl

theorem kv_cap (f : Fields) :
    (List.lookup Key.cap (kvList f)).join = f.cap.map renderRate := rfl

theorem kv_after (f : Fields) :
    (List.lookup Key.after (kvList f)).join = f.after.map renderDeps := rfl

theorem kv_loc (f : Fields) :
    (List.lookup Key.loc (kvList f)).join = f.loc.map renderLoc := rfl

theorem kv_est (f : Fields) :
    (List.lookup Key.est (kvList f)).join = f.est.map renderDur := rfl

theorem kv_demoted (f : Fields) :
    (List.lookup Key.demoted (kvList f)).join = f.demoted.map renderStamps := rfl

theorem kv_waiting (f : Fields) :
    (List.lookup Key.waiting (kvList f)).join = f.waiting.map renderDate := rfl

theorem kv_buffer (f : Fields) :
    (List.lookup Key.buffer (kvList f)).join = f.buffer.map renderDur := rfl

theorem kv_ci (f : Fields) :
    (List.lookup Key.ci (kvList f)).join = f.ciKey.map renderCi := rfl

section KeyRoundTrip
variable (i : Id) (f : Fields)
  (htitle : f.title.all titleWordWf = true)
  (hunp : f.unparsed.all unparsedWordWf = true)
  (hextra : f.extra.all extraPairWf = true)

include htitle hunp hextra in
theorem view_render_due
    (hv : optWf Moment.wf f.due = true) :
    viewDue (renderItem i f) = f.due := by
  unfold viewDue
  rw [lookupKey_render i f Key.due htitle hunp hextra, kv_due f]
  exact bind_map_render f.due renderMoment parseMoment (fun a hx => parse_render_moment a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_interval
    (hv : optWf (fun p => intervalWf p.1 p.2) f.interval = true) :
    viewAt (renderItem i f) = f.interval := by
  unfold viewAt
  rw [lookupKey_render i f Key.interval htitle hunp hextra, kv_interval f]
  refine bind_map_render f.interval (fun p => renderInterval p.1 p.2) parseInterval ?_
  intro a hx
  have hwf := optWf_some (p := fun p : DT × DT => intervalWf p.1 p.2) hv hx
  exact parse_render_interval a.1 a.2 hwf

include htitle hunp hextra in
theorem view_render_window
    (hv : optWf windowWf f.window = true) :
    viewWin (renderItem i f) = f.window := by
  unfold viewWin
  rw [lookupKey_render i f Key.window htitle hunp hextra, kv_window f]
  exact bind_map_render f.window renderWindow parseWindow (fun a hx => parse_render_window a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_dur
    (hv : optWf Dur.noDays f.dur = true) :
    viewDur (renderItem i f) = f.dur := by
  unfold viewDur
  rw [lookupKey_render i f Key.dur htitle hunp hextra, kv_dur f]
  exact bind_map_render f.dur renderDur parseDurND (fun a hx => parse_render_durND a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_pref :
    viewPref (renderItem i f) = f.pref := by
  unfold viewPref
  rw [lookupKey_render i f Key.pref htitle hunp hextra, kv_pref f]
  exact bind_map_render f.pref renderPref parsePref (fun a _ => parse_render_pref a)

include htitle hunp hextra in
theorem view_render_every
    (hv : optWf Rule.wf f.every = true) :
    viewEvery (renderItem i f) = f.every := by
  unfold viewEvery
  rw [lookupKey_render i f Key.every htitle hunp hextra, kv_every f]
  exact bind_map_render f.every renderRule parseRule (fun a hx => parse_render_rule a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_afterDone :
    viewAfterDone (renderItem i f) = f.afterDone := by
  unfold viewAfterDone
  rw [lookupKey_render i f Key.afterDone htitle hunp hextra, kv_afterDone f]
  exact bind_map_render f.afterDone renderAfterDone parseAfterDone (fun a _ => parse_render_afterDone a)

include htitle hunp hextra in
theorem view_render_onEvent
    (hv : optWf OnEvent.wf f.onEvent = true) :
    viewOnEvent (renderItem i f) = f.onEvent := by
  unfold viewOnEvent
  rw [lookupKey_render i f Key.onEvent htitle hunp hextra, kv_onEvent f]
  exact bind_map_render f.onEvent renderOnEvent parseOnEvent (fun a hx => parse_render_onEvent a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_onMiss :
    viewOnMiss (renderItem i f) = f.onMiss := by
  unfold viewOnMiss
  rw [lookupKey_render i f Key.onMiss htitle hunp hextra, kv_onMiss f]
  exact bind_map_render f.onMiss renderOnMiss parseOnMiss (fun a _ => parse_render_onMiss a)

include htitle hunp hextra in
theorem view_render_floor :
    viewMin (renderItem i f) = f.floor := by
  unfold viewMin
  rw [lookupKey_render i f Key.floor htitle hunp hextra, kv_floor f]
  exact bind_map_render f.floor renderRate parseRate (fun a _ => parse_render_rate a)

include htitle hunp hextra in
theorem view_render_cap :
    viewMax (renderItem i f) = f.cap := by
  unfold viewMax
  rw [lookupKey_render i f Key.cap htitle hunp hextra, kv_cap f]
  exact bind_map_render f.cap renderRate parseRate (fun a _ => parse_render_rate a)

include htitle hunp hextra in
theorem view_render_after
    (hv : optWf depsWf f.after = true) :
    viewAfter (renderItem i f) = f.after := by
  unfold viewAfter
  rw [lookupKey_render i f Key.after htitle hunp hextra, kv_after f]
  exact bind_map_render f.after renderDeps parseDeps (fun a hx => parse_render_deps a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_loc
    (hv : optWf Loc.wf f.loc = true) :
    viewLoc (renderItem i f) = f.loc := by
  unfold viewLoc
  rw [lookupKey_render i f Key.loc htitle hunp hextra, kv_loc f]
  exact bind_map_render f.loc renderLoc parseLoc (fun a hx => parse_render_loc a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_est
    (hv : optWf Dur.noDays f.est = true) :
    viewEstKey (renderItem i f) = f.est := by
  unfold viewEstKey
  rw [lookupKey_render i f Key.est htitle hunp hextra, kv_est f]
  exact bind_map_render f.est renderDur parseDurND (fun a hx => parse_render_durND a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_demoted
    (hv : optWf (fun ss => !List.isEmpty ss) f.demoted = true) :
    viewDemoted (renderItem i f) = f.demoted := by
  unfold viewDemoted
  rw [lookupKey_render i f Key.demoted htitle hunp hextra, kv_demoted f]
  exact bind_map_render f.demoted renderStamps parseStamps (fun a hx => parse_render_stamps a (by simpa using optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_waiting
    (hv : optWf dayWf f.waiting = true) :
    viewWaiting (renderItem i f) = f.waiting := by
  unfold viewWaiting
  rw [lookupKey_render i f Key.waiting htitle hunp hextra, kv_waiting f]
  exact bind_map_render f.waiting renderDate parseDate (fun a hx => parse_render_date a (optWf_some hv hx))

include htitle hunp hextra in
theorem view_render_buffer :
    viewBuffer (renderItem i f) = f.buffer := by
  unfold viewBuffer
  rw [lookupKey_render i f Key.buffer htitle hunp hextra, kv_buffer f]
  exact bind_map_render f.buffer renderDur parseDur (fun a _ => parse_render_dur a)

include htitle hunp hextra in
theorem view_render_ci :
    viewCiKey (renderItem i f) = f.ciKey := by
  unfold viewCiKey
  rw [lookupKey_render i f Key.ci htitle hunp hextra, kv_ci f]
  exact bind_map_render f.ciKey renderCi parseCi (fun a _ => parse_render_ci a)

end KeyRoundTrip
end Field
end Tm
