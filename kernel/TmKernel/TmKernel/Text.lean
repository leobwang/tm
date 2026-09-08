import TmKernel.Grain
/-!
# The item line: tokens with verbatim spelling

§4.1 of the spec says serialization is byte-faithful.  In the Rust that is a
property tested afterwards by a 512-case proptest.  Here it is the
**representation**: an item line *is* its token vector, each token carrying the
bytes that were read, and the semantic fields are a *view* of that vector.

Two things are deliberately **not** stored in the token vector, because storing
them would create a second source of truth for something the state already
knows:

* the state box `[ ]` — it is rendered from `Status` and placement (§6.3's
  `[-]` is positional, not a stored glyph);
* the `^id` token's word — it is rendered from the store key.

So a line whose `^id` disagrees with the id that names it is not a state this
kernel can hold, and neither is a line whose box disagrees with its status.
-/
namespace Tm

/-- An id is a token of characters.  Deliberately **not** `String`: in this
Lean, `String` is backed by a `ByteArray` and the `List Char` round trip is not
a core theorem, so keeping ids as characters keeps the proofs off UTF-8.
(§3.1 says 4 chars of `[a-z0-9]`; the spec's own §4.3 fixture ships `^O1`, so
the type is deliberately weaker than the prose — see the README.) -/
abbrev Id := List Char

/-! ## Glyphs -/

inductive Glyph | todo | active | done | demoted | dropped | waiting
deriving DecidableEq, Repr, Inhabited

def Glyph.char : Glyph → Char
  | .todo => ' ' | .active => '>' | .done => 'x'
  | .demoted => '-' | .dropped => '~' | .waiting => '?'

def Glyph.ofChar? : Char → Option Glyph
  | ' ' => some .todo | '>' => some .active | 'x' => some .done
  | '-' => some .demoted | '~' => some .dropped | '?' => some .waiting
  | _   => none

theorem glyph_roundtrip (g : Glyph) : Glyph.ofChar? g.char = some g := by
  cases g <;> rfl

/-! ## Decimal numerals

`est:` values must survive a write followed by a read, or `tm edit est=` is
silent again — this time inside the kernel.  So the numeral round trip is a
theorem, not an assumption. -/

def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

def charDigit : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _   => none

theorem digit_roundtrip : ∀ k < 10, charDigit (digitChar k) = some k := by decide

/-- Decimal digits of `n`, most significant first. -/
def digitsOf (n : Nat) : List Char :=
  if h : n < 10 then [digitChar n]
  else digitsOf (n / 10) ++ [digitChar (n % 10)]
decreasing_by omega

/-- Fold a digit list into a number. -/
def natStep (a : Nat) (c : Char) : Nat := a * 10 + (charDigit c).getD 0

def readNatAux (l : List Char) : Option Nat :=
  l.foldl (fun acc c => match acc, charDigit c with
                        | some a, some d => some (a * 10 + d)
                        | _, _ => none) (some 0)

/-- Read a decimal numeral.  `none` on the empty list or on any non-digit. -/
def readNat (l : List Char) : Option Nat :=
  if l.isEmpty then none else readNatAux l

theorem digitsOf_ne_nil (n : Nat) : digitsOf n ≠ [] := by
  rw [digitsOf]; by_cases h : n < 10
  · rw [dif_pos h]; simp
  · rw [dif_neg h]; simp

theorem digitsOf_all_digits : ∀ (m : Nat), ∀ c ∈ digitsOf m, (charDigit c).isSome := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihm =>
    rw [digitsOf]
    by_cases hm : m < 10
    · rw [dif_pos hm]
      simp only [List.mem_singleton]
      intro c hc; subst hc
      simp [digit_roundtrip m hm]
    · rw [dif_neg hm]
      intro c hc
      rcases List.mem_append.1 hc with h1 | h1
      · exact ihm (m / 10) (by omega) c h1
      · simp only [List.mem_singleton] at h1; subst h1
        simp [digit_roundtrip (m % 10) (by omega)]

theorem readNatAux_of_digits (a : Nat) (l : List Char) (h : ∀ c ∈ l, (charDigit c).isSome) :
    l.foldl (fun acc c => match acc, charDigit c with
                          | some a, some d => some (a * 10 + d)
                          | _, _ => none) (some a)
      = some (l.foldl natStep a) := by
  induction l generalizing a with
  | nil => rfl
  | cons c t ih =>
      have hc : (charDigit c).isSome := h c (by simp)
      cases hcd : charDigit c with
      | none => rw [hcd] at hc; simp at hc
      | some d =>
          simp only [List.foldl_cons, hcd]
          rw [ih _ (fun x hx => h x (by simp [hx]))]
          simp [natStep, hcd]

/-- The digits of `n` fold back to `n`. -/
theorem natStep_digitsOf (n : Nat) : (digitsOf n).foldl natStep 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digitsOf]
    by_cases h : n < 10
    · rw [dif_pos h]
      simp only [List.foldl_cons, List.foldl_nil, natStep]
      rw [digit_roundtrip n h]; simp
    · rw [dif_neg h]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) (by omega)]
      simp only [natStep]
      rw [digit_roundtrip (n % 10) (by omega)]
      simp; omega

/-- **The numeral round trip.**  Everything the kernel writes as a number it
reads back as the same number.  Without this, `tm edit est=` could be silent
again — this time inside the verified kernel. -/
theorem readNat_digitsOf (n : Nat) : readNat (digitsOf n) = some n := by
  unfold readNat
  have hne : (digitsOf n).isEmpty = false := by
    cases hd : digitsOf n with
    | nil => exact absurd hd (digitsOf_ne_nil n)
    | cons a t => simp
  rw [hne]
  simp only [Bool.false_eq_true, if_false, readNatAux]
  rw [readNatAux_of_digits 0 _ (digitsOf_all_digits n), natStep_digitsOf]

/-! ## Tokens

A token is the verbatim separator that preceded it plus the verbatim word.
There is no stored "kind": the kind is a *function* of the word and its
position, computed on demand, so a stored kind cannot drift from the bytes. -/

structure Tok where
  sep  : List Char        -- verbatim whitespace before the word
  word : List Char        -- verbatim word
deriving DecidableEq, Repr, Inhabited

def Tok.raw (t : Tok) : List Char := t.sep ++ t.word

def isSp (c : Char) : Bool := c == ' '

/-- Right-to-left chunking.  Structurally recursive, so it is total with no
termination argument and no `partial`. -/
def chunk (c : Char) (gs : List (List Char)) : List (List Char) :=
  match gs with
  | []      => [[c]]
  | g :: gs' => if !isSp c && g.head? == some ' ' then [c] :: g :: gs' else (c :: g) :: gs'

def group : List Char → List (List Char)
  | []      => []
  | c :: cs => chunk c (group cs)

def toTok (g : List Char) : Tok := ⟨g.takeWhile isSp, g.dropWhile isSp⟩

def tokenize (cs : List Char) : List Tok := (group cs).map toTok

@[simp] theorem toTok_raw (g : List Char) : (toTok g).raw = g := by
  simp [toTok, Tok.raw, List.takeWhile_append_dropWhile]

theorem chunk_flatten (c : Char) (gs : List (List Char)) :
    (chunk c gs).flatten = c :: gs.flatten := by
  cases gs with
  | nil => simp [chunk]
  | cons g gs' => by_cases h : (!isSp c && g.head? == some ' ') = true <;> simp [chunk, h]

theorem group_flatten (cs : List Char) : (group cs).flatten = cs := by
  induction cs with
  | nil => rfl
  | cons c t ih => rw [group, chunk_flatten, ih]

/-- **Byte-faithfulness of the tokenizer**: the token vector concatenates back
to exactly the bytes that were read. -/
theorem tokenize_raw (cs : List Char) : (tokenize cs).flatMap Tok.raw = cs := by
  unfold tokenize
  rw [List.flatMap_map]
  have : ∀ gs : List (List Char), gs.flatMap (fun g => (toTok g).raw) = gs.flatten := by
    intro gs; induction gs with
    | nil => rfl
    | cons g t ih => simp [ih]
  rw [this, group_flatten]

/-! ## The tokenizer is invertible on well-shaped token vectors

Round trip A (bytes → tokens → the same bytes) is free from `tokenize_raw`.
Round trip B (tokens → bytes → the same tokens) is the one that matters after
an *edit*, and it needs the token vector to be well shaped: separators are
spaces, words are non-empty and space-free, and every token after the first
carries at least one space of separator. -/

theorem takeWhile_append_all {α} (p : α → Bool) (a b : List α)
    (ha : ∀ x ∈ a, p x = true) (hb : ∀ x, b.head? = some x → p x = false) :
    (a ++ b).takeWhile p = a ∧ (a ++ b).dropWhile p = b := by
  induction a with
  | nil =>
      cases b with
      | nil => simp
      | cons y t =>
          have := hb y rfl
          simp [List.takeWhile_cons, List.dropWhile_cons, this]
  | cons x t ih =>
      have hx : p x = true := ha x (by simp)
      have hrest := ih (fun z hz => ha z (by simp [hz]))
      simp [List.takeWhile_cons, List.dropWhile_cons, hx, hrest.1, hrest.2]

theorem chunk_head (c : Char) (gs : List (List Char)) :
    ((chunk c gs).head?).bind List.head? = some c := by
  cases gs with
  | nil => simp [chunk]
  | cons g gs' =>
      by_cases h : (!isSp c && g.head? == some ' ') = true <;> simp [chunk, h]

theorem chunk_merge (c : Char) (g : List Char) (gs : List (List Char))
    (h : (g.head? == some ' ') = false) : chunk c (g :: gs) = (c :: g) :: gs := by
  simp [chunk, h]

theorem group_head (cs : List Char) : ((group cs).head?).bind List.head? = cs.head? := by
  cases cs with
  | nil => rfl
  | cons c t =>
      simp only [List.head?_cons]
      rw [group]
      exact chunk_head c (group t)

/-- Prepending a maximal word to a chunk list starts a new chunk, provided the
next chunk begins with a space (or there is no next chunk). -/
theorem group_word (w ys : List Char) (hw : w ≠ []) (hws : ∀ c ∈ w, isSp c = false)
    (hy : ys = [] ∨ (∃ c, ys.head? = some c ∧ isSp c = true)) :
    group (w ++ ys) = w :: group ys := by
  induction w with
  | nil => exact absurd rfl hw
  | cons c w' ih =>
      cases w' with
      | nil =>
          have hc : isSp c = false := hws c (by simp)
          rcases hy with rfl | ⟨y, hy1, hy2⟩
          · simp [group, chunk]
          · cases hg : group ys with
            | nil =>
                have := group_head ys
                rw [hg, hy1] at this; simp at this
            | cons g gs =>
                have hgh : g.head? = ys.head? := by
                  have := group_head ys; rw [hg] at this; simpa using this
                have : g.head? = some ' ' := by
                  rw [hgh, hy1]
                  have : y = ' ' := by
                    simpa [isSp] using hy2
                  rw [this]
                simp [group, chunk, hc, hg, this]
      | cons d w'' =>
          have hne : (d :: w'') ≠ [] := by simp
          have hsub : ∀ x ∈ d :: w'', isSp x = false := fun x hx => hws x (by simp [hx])
          have hIH := ih hne hsub
          have hd : isSp d = false := hsub d (by simp)
          have hne2 : ((d :: w'').head? == some ' ') = false := by
            simp only [List.head?_cons, beq_iff_eq, Option.some.injEq]
            simp only [isSp, beq_iff_eq] at hd
            simp [hd]
          have step : group (c :: ((d :: w'') ++ ys)) = chunk c (group ((d :: w'') ++ ys)) := rfl
          rw [show (c :: d :: w'') ++ ys = c :: ((d :: w'') ++ ys) from rfl, step, hIH,
            chunk_merge c (d :: w'') (group ys) hne2]

/-- Prepending spaces never starts a new chunk. -/
theorem group_sep (sp rest : List Char) (hsp : ∀ c ∈ sp, isSp c = true)
    (g : List Char) (gs : List (List Char)) (h : group rest = g :: gs) :
    group (sp ++ rest) = (sp ++ g) :: gs := by
  induction sp with
  | nil => simpa using h
  | cons s sp' ih =>
      have hs : isSp s = true := hsp s (by simp)
      have hIH := ih (fun x hx => hsp x (by simp [hx]))
      have step : group (s :: (sp' ++ rest)) = chunk s (group (sp' ++ rest)) := rfl
      rw [show (s :: sp') ++ rest = s :: (sp' ++ rest) from rfl, step, hIH]
      have hs' : (!isSp s) = false := by simp [hs]
      simp [chunk, hs']

def Tok.wf (t : Tok) : Bool :=
  t.sep.all isSp && !t.word.isEmpty && t.word.all (fun c => !isSp c)

/-- Every token after the first must carry at least one space of separator, or
two tokens would run together and re-tokenize as one. -/
def toksWf : List Tok → Bool
  | []            => true
  | [t]           => t.wf
  | t :: u :: rest => t.wf && !u.sep.isEmpty && toksWf (u :: rest)

theorem toTok_of_wf (t : Tok) (h : t.wf = true) : toTok t.raw = t := by
  unfold Tok.wf at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hsep, hne⟩, hword⟩ := h
  have hsep' : ∀ c ∈ t.sep, isSp c = true := by
    intro c hc; exact List.all_eq_true.1 hsep c hc
  have hhd : ∀ c, t.word.head? = some c → isSp c = false := by
    intro c hc
    have : c ∈ t.word := List.mem_of_mem_head? hc
    have := List.all_eq_true.1 hword c this
    simpa using this
  have := takeWhile_append_all isSp t.sep t.word hsep' hhd
  unfold toTok Tok.raw
  rw [this.1, this.2]

theorem group_tok (t : Tok) (ys : List Char) (ht : t.wf = true)
    (hy : ys = [] ∨ (∃ c, ys.head? = some c ∧ isSp c = true)) :
    group (t.raw ++ ys) = t.raw :: group ys := by
  unfold Tok.wf at ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
  obtain ⟨⟨hsep, hne⟩, hword⟩ := ht
  have hsep' : ∀ c ∈ t.sep, isSp c = true := fun c hc => List.all_eq_true.1 hsep c hc
  have hw : t.word ≠ [] := by
    intro hc; rw [hc] at hne; simp at hne
  have hws : ∀ c ∈ t.word, isSp c = false := by
    intro c hc; have := List.all_eq_true.1 hword c hc; simpa using this
  have hgw := group_word t.word ys hw hws hy
  unfold Tok.raw
  rw [List.append_assoc]
  rw [group_sep t.sep (t.word ++ ys) hsep' t.word (group ys) hgw]

/-- **Round trip B for the token vector.**  Serialising a well-shaped token
vector and re-tokenising it returns the identical vector. -/
theorem tokenize_toks : ∀ ts : List Tok, toksWf ts = true → tokenize (ts.flatMap Tok.raw) = ts := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t ts' ih =>
      intro h
      have ht : t.wf = true := by
        cases ts' with
        | nil => simpa [toksWf] using h
        | cons u r => simp only [toksWf, Bool.and_eq_true] at h; exact h.1.1
      have hrest : toksWf ts' = true := by
        cases ts' with
        | nil => rfl
        | cons u r => simp only [toksWf, Bool.and_eq_true] at h; exact h.2
      have hy : (ts'.flatMap Tok.raw) = [] ∨
          (∃ c, (ts'.flatMap Tok.raw).head? = some c ∧ isSp c = true) := by
        cases ts' with
        | nil => left; rfl
        | cons u r =>
            right
            have husep : u.sep ≠ [] := by
              simp only [toksWf, Bool.and_eq_true, Bool.not_eq_true'] at h
              intro hc; rw [hc] at h; simp at h
            have huwf : u.wf = true := by
              cases r with
              | nil => simpa [toksWf] using hrest
              | cons v r' => simp only [toksWf, Bool.and_eq_true] at hrest; exact hrest.1.1
            unfold Tok.wf at huwf
            simp only [Bool.and_eq_true] at huwf
            have hsep' : ∀ c ∈ u.sep, isSp c = true :=
              fun c hc => List.all_eq_true.1 huwf.1.1 c hc
            cases hu : u.sep with
            | nil => exact absurd hu husep
            | cons a rest =>
                refine ⟨a, ?_, ?_⟩
                · simp [List.flatMap_cons, Tok.raw, hu]
                · exact hsep' a (by rw [hu]; simp)
      simp only [List.flatMap_cons]
      unfold tokenize
      rw [group_tok t _ ht hy, List.map_cons, toTok_of_wf t ht]
      have := ih hrest
      unfold tokenize at this
      rw [this]

end Tm
