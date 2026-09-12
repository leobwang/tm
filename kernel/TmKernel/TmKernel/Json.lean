import TmKernel.Text
/-!
# The kernel's own JSON fragment: the value, the escaping, the numerals

`Lean.Json` cannot be reasoned about here.  Its printer (`Json.compress`,
`Json.render`) and every recursive worker of `Json.parse` are `partial def`s in
v4.33.1, which elaborate to **opaque constants**: no equation lemmas, nothing to
unfold, nothing `simp`/`decide`/induction can touch.  The README's
"Gap 39 REPRICED" paragraph measures that and prices the replacement as J0–J6;
this module is J0–J2.  It is gap 12's move one level up — own the function,
prove the round trip, and let agreement with the *host's* reader (serde_json,
which is the only reader these bytes ever had in production) stay corpus and
FFI evidence rather than a theorem.

**Nothing here is on the wire yet.**  `Boundary.lean` still builds `Lean.Json`.
J3–J5 move it; until then this module is foundations with its own tests.

## The three decisions this module takes, stated rather than left implicit

1. **The numerals are `Nat`.**  Every number the boundary emits today is a
   `Nat` — `lerrJson`'s `badLine` line number, `regionJson`'s `grain` (a `Fin 4`
   value) and its `ix` — and every number it ingests goes through
   `Boundary.getNat`.  There is no negative and no exponent anywhere on the
   wire, so `JVal.num` carries a `Nat` and the fragment has no `JsonNumber`.
   If a site ever needs a negative, it must widen this type, and that widening
   is then visible in a diff.

2. **Emit narrow, accept wide.**  `jescape` emits exactly what Lean's own
   printer emits — `\"`, `\\`, `\n`, `\r`, a `\u00xx` hex quad (lowercase) for
   every other character below `0x20`, and every character at or above `0x20`
   verbatim, non-ASCII and `DEL` included.  `junescape` additionally *accepts*
   `\/`, `\t`, `\b` and `\f`, which serde_json does emit, and accepts hex quads
   in either case.  `the_accepted_escapes_exceed_the_emitted_ones` states the
   asymmetry as a theorem rather than a comment.

3. **A lone surrogate escape is refused by name.**  Lean's `Char` is a Unicode
   *scalar* value, so `0xd800`–`0xdfff` is not a character and `jescape` can
   never emit one; `junescape` refuses `\ud83d` with `JEsc.surrogateEscape`
   rather than guessing at a pair.  serde_json never emits a surrogate pair (it
   writes astral characters as UTF-8 bytes), so nothing the real host sends is
   lost.  A non-serde host that escapes astral characters as pairs is refused,
   by name — README gap 42.

`junescape` is also strict in the other direction: a raw `"` (`JEsc.rawQuote`)
and a raw character below `0x20` (`JEsc.rawControl`) are refused, as RFC 8259
requires, so that when J4's scanner hands it the bytes between two quotes the
refusals are the scanner's guarantees restated.

Everything is structural, with no well-founded recursion anywhere: §5.10's
lesson is that a well-founded definition does not *reduce* in the kernel, and
every theorem below that pins down bytes is a `decide`.
-/
namespace Tm

set_option maxRecDepth 4000

/-! ## J0 — the fragment type

Objects are an **ordered association list**, not a map.  Lean's `Json.mkObj`
carries a `Std.TreeMap.Raw String Json` and prints its keys sorted; an assoc
list keeps build order and has no rebuild hazard to reason about.  The byte
consequence is measured at J5, not here.  Strings are `List Char` for the same
reason `Id` is (see `Text.lean`'s header): the proofs stay off UTF-8. -/

inductive JVal
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : List Char)
  | arr (xs : List JVal)
  | obj (kvs : List (List Char × JVal))
deriving Repr, Inhabited

/-! ### Decidable equality, by hand and structurally

`deriving DecidableEq` **fails** on this type — measured, not assumed: v4.33.1
answers *"None of the deriving handlers for class `DecidableEq` applied to
`JVal`"*, because the recursion is *nested* (it goes through `List`), not
mutual.  The usual escape is a `termination_by sizeOf` definition, and §5.10
says why that is the wrong escape here: a well-founded definition does not
reduce in the kernel, so every `decide` below — every theorem that pins down
what the kernel writes — would stop working.

So the comparison is three **mutually structural** `Bool` functions, and the
instance is `decidable_of_iff`-shaped, built from soundness and reflexivity.
The four-motive `JVal.rec` the nested inductive generates is what makes both
proofs go through, and it is the same eliminator J4's `jparse_jemit` will
need — this section is a rehearsal for it as much as it is J0. -/

mutual
/-- Structural equality on values. -/
def jbeq : JVal → JVal → Bool
  | .null,   .null   => true
  | .bool a, .bool b => a == b
  | .num a,  .num b  => a == b
  | .str a,  .str b  => a == b
  | .arr a,  .arr b  => jbeqL a b
  | .obj a,  .obj b  => jbeqO a b
  | _, _ => false
/-- Elementwise on arrays.  Length mismatch is inequality, not a crash. -/
def jbeqL : List JVal → List JVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => jbeq x y && jbeqL xs ys
  | _, _ => false
/-- Pairwise on objects, **key order included** — see
`jval_objects_keep_their_order`. -/
def jbeqO : List (List Char × JVal) → List (List Char × JVal) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => (k == l) && jbeq x y && jbeqO xs ys
  | _, _ => false
end

theorem jbeq_sound (a : JVal) : ∀ b : JVal, jbeq a b = true → a = b := by
  refine JVal.rec
    (motive_1 := fun a => ∀ b, jbeq a b = true → a = b)
    (motive_2 := fun xs => ∀ ys, jbeqL xs ys = true → xs = ys)
    (motive_3 := fun kvs => ∀ ls, jbeqO kvs ls = true → kvs = ls)
    (motive_4 := fun p => ∀ q : List Char × JVal,
        ((p.1 == q.1) && jbeq p.2 q.2) = true → p = q)
    ?null ?bool ?num ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair a
  case null =>
    intro b h; cases b <;> simp_all [jbeq]
  case bool =>
    intro x b h; cases b <;> simp_all [jbeq]
  case num =>
    intro x b h; cases b <;> simp_all [jbeq]
  case str =>
    intro x b h; cases b <;> simp_all [jbeq]
  case arr =>
    intro xs ih b h
    cases b <;> simp_all [jbeq]
    exact ih _ h
  case obj =>
    intro kvs ih b h
    cases b <;> simp_all [jbeq]
    exact ih _ h
  case lnil =>
    intro ys h; cases ys <;> simp_all [jbeqL]
  case lcons =>
    intro x xs ihx ihxs ys h
    cases ys <;> simp_all [jbeqL]
    exact ⟨ihx _ h.1, ihxs _ h.2⟩
  case onil =>
    intro ls h; cases ls <;> simp_all [jbeqO]
  case ocons =>
    intro p ps ihp ihps ls h
    cases ls with
    | nil => simp [jbeqO] at h
    | cons q qs =>
      obtain ⟨k, x⟩ := p
      obtain ⟨l, y⟩ := q
      simp only [jbeqO, Bool.and_eq_true] at h
      have h1 := ihp (l, y) (by simp only [Bool.and_eq_true]; exact ⟨h.1.1, h.1.2⟩)
      have h2 := ihps qs h.2
      simp_all
  case pair =>
    intro k v ihv q h
    obtain ⟨l, y⟩ := q
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := ihv y h.2
    simp_all

theorem jbeq_refl (a : JVal) : jbeq a a = true := by
  refine JVal.rec
    (motive_1 := fun a => jbeq a a = true)
    (motive_2 := fun xs => jbeqL xs xs = true)
    (motive_3 := fun kvs => jbeqO kvs kvs = true)
    (motive_4 := fun p => ((p.1 == p.1) && jbeq p.2 p.2) = true)
    ?null ?bool ?num ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair a <;>
    intros <;> simp_all [jbeq, jbeqL, jbeqO]

/-- **Both directions** (§5.8): `jbeq` says yes exactly when the values are
equal.  `jbeq_sound` is the biting half, `jbeq_refl` the discharging one. -/
theorem jbeq_iff (a b : JVal) : jbeq a b = true ↔ a = b :=
  ⟨jbeq_sound a b, fun h => h ▸ jbeq_refl a⟩

instance : DecidableEq JVal := fun a b =>
  if h : jbeq a b = true then isTrue (jbeq_sound a b h)
  else isFalse (fun e => h (e ▸ jbeq_refl a))

/-- A value of every shape the boundary builds: the `ok`/`err` object wrapper,
a document array, a line list of strings, and a `Nat` field.  It exists so the
type's `DecidableEq` is exercised on something with real nesting. -/
def demoJVal : JVal :=
  .obj [(['o','k'], .obj
    [(['d','o','c','s'], .arr
       [.obj [(['p','a','t','h'], .str ['w','.','m','d']),
              (['l','i','n','e','s'], .arr [.str ['-',' ','a'], .str ['-',' ','b']]),
              (['i','x'], .num 3),
              (['g','r','a','i','n'], .num 1)]]),
     (['d','o','n','e'], .bool true),
     (['w','h','y'], .null)])]

/-- **The order is in the value.**  Two objects with the same pairs in a
different order are distinct `JVal`s — which is the whole point of the assoc
list, and is exactly what `Json.mkObj` cannot express. -/
theorem jval_objects_keep_their_order :
    (JVal.obj [(['a'], .num 1), (['b'], .num 2)])
      ≠ (JVal.obj [(['b'], .num 2), (['a'], .num 1)]) := by decide

/-- Non-vacuity for J0: `DecidableEq` decides a nested value against itself and
against a one-byte perturbation deep inside it. -/
theorem demo_jval_is_decidable :
    demoJVal = demoJVal ∧
    demoJVal ≠ JVal.obj [(['o','k'], .num 0)] ∧
    demoJVal ≠ JVal.obj [(['o','k'], .obj
      [(['d','o','c','s'], .arr
         [.obj [(['p','a','t','h'], .str ['w','.','m','d']),
                (['l','i','n','e','s'], .arr [.str ['-',' ','a'], .str ['-',' ','B']]),
                (['i','x'], .num 3),
                (['g','r','a','i','n'], .num 1)]]),
       (['d','o','n','e'], .bool true),
       (['w','h','y'], .null)])] := by decide

/-! ## J1 — escaping

The crux.  `junescape (jescape cs) = .ok cs` for **every** `cs`: no hypothesis,
no fragment restriction.  The kernel's doc lines are arbitrary user bytes, so
an escaping that only round-trips on a subset would be the boundary hole
§5.4 names. -/

/-- Lowercase hex, matching `Nat.digitChar`, which is what Lean's own printer
uses for its `\u` quads. -/
def hexChar (k : Nat) : Char :=
  if k < 10 then digitChar k
  else match k with
    | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

/-- Either case is accepted: a host is free to write a quad with lowercase or
with uppercase hex letters.  The kernel writes lowercase. -/
def hexDigit : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9
  | 'a' => some 10 | 'b' => some 11 | 'c' => some 12
  | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | 'A' => some 10 | 'B' => some 11 | 'C' => some 12
  | 'D' => some 13 | 'E' => some 14 | 'F' => some 15
  | _ => none

theorem hexDigit_hexChar : ∀ k < 16, hexDigit (hexChar k) = some k := by decide

/-- The two characters JSON has a short escape for that this kernel accepts but
never emits: backspace `0x08` and form feed `0x0c`.  Named rather than written
as literals so the tests below say which byte they mean. -/
def bsChar : Char := Char.ofNat 8
def ffChar : Char := Char.ofNat 12

def hexQuad (a b c d : Char) : Option Nat :=
  match hexDigit a, hexDigit b, hexDigit c, hexDigit d with
  | some x, some y, some z, some w => some (((x * 16 + y) * 16 + z) * 16 + w)
  | _, _, _, _ => none

/-- One character's escaped spelling.  Exactly Lean's printer's classes:
`"`, `\`, `\n`, `\r`, a `\u00xx` quad below `0x20`, everything else verbatim. -/
def escOf (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else if c = '\r' then ['\\', 'r']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', hexChar (c.toNat / 16), hexChar (c.toNat % 16)]
  else [c]

/-- The bytes between the two quotes of a JSON string.  Structural. -/
def jescape : List Char → List Char
  | [] => []
  | c :: cs => escOf c ++ jescape cs

/-- Why `junescape` refused.  §5.7: every diagnostic is named. -/
inductive JEsc
  /-- A `\` with nothing after it, or a `\u` with fewer than four bytes after it. -/
  | truncatedEscape
  /-- A `\` followed by a byte that is not an escape letter. -/
  | unknownEscape (c : Char)
  /-- `\u` followed by four bytes that are not all hex. -/
  | badHexQuad (a b c d : Char)
  /-- A quad in `0xd800`–`0xdfff`: not a Unicode scalar value.  Decision 3. -/
  | surrogateEscape (v : Nat)
  /-- An unescaped `"` inside string content. -/
  | rawQuote
  /-- An unescaped character below `0x20`, which RFC 8259 forbids. -/
  | rawControl (v : Nat)
deriving DecidableEq, Repr, Inhabited

/-- Undo `jescape`.  Structural: every recursive call is on a proper tail, the
`\uXXXX` branch six characters in.  No fuel, no well-founded recursion, so it
reduces and `decide` can see it. -/
def junescape : List Char → Except JEsc (List Char)
  | [] => .ok []
  | '\\' :: '"'  :: rest => (junescape rest).map (fun t => '"' :: t)
  | '\\' :: '\\' :: rest => (junescape rest).map (fun t => '\\' :: t)
  | '\\' :: '/'  :: rest => (junescape rest).map (fun t => '/' :: t)
  | '\\' :: 'n'  :: rest => (junescape rest).map (fun t => '\n' :: t)
  | '\\' :: 'r'  :: rest => (junescape rest).map (fun t => '\r' :: t)
  | '\\' :: 't'  :: rest => (junescape rest).map (fun t => '\t' :: t)
  | '\\' :: 'b'  :: rest => (junescape rest).map (fun t => bsChar :: t)
  | '\\' :: 'f'  :: rest => (junescape rest).map (fun t => ffChar :: t)
  | '\\' :: 'u'  :: a :: b :: c :: d :: rest =>
      match hexQuad a b c d with
      | none => .error (.badHexQuad a b c d)
      | some v =>
        if 0xd800 ≤ v && v ≤ 0xdfff then .error (.surrogateEscape v)
        else (junescape rest).map (fun t => Char.ofNat v :: t)
  | '\\' :: 'u' :: _ => .error .truncatedEscape
  | '\\' :: e :: _ => .error (.unknownEscape e)
  | '\\' :: [] => .error .truncatedEscape
  | c :: rest =>
      if c = '"' then .error .rawQuote
      else if c.toNat < 32 then .error (.rawControl c.toNat)
      else (junescape rest).map (fun t => c :: t)

/-! ### The crux -/

/-- A hex quad written by `escOf` reads back as the character it came from.
`n < 32` is what makes both nibbles hex digits and the value a scalar. -/
theorem hexQuad_escOf (c : Char) (h : c.toNat < 32) :
    hexQuad '0' '0' (hexChar (c.toNat / 16)) (hexChar (c.toNat % 16)) = some c.toNat := by
  have h1 : c.toNat / 16 < 16 := by omega
  have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
  have e1 := hexDigit_hexChar _ h1
  have e2 := hexDigit_hexChar _ h2
  unfold hexQuad
  rw [e1, e2]
  simp only [hexDigit]
  have : ((0 * 16 + 0) * 16 + c.toNat / 16) * 16 + c.toNat % 16 = c.toNat := by omega
  rw [this]

/-- **One character at a time.**  Un-escaping the escape of `c` followed by any
tail is `c` in front of un-escaping the tail.  This is where the case analysis
lives; the theorem below is then an induction with no cases of its own. -/
theorem junescape_escOf (c : Char) (t : List Char) :
    junescape (escOf c ++ t) = (junescape t).map (fun r => c :: r) := by
  unfold escOf
  by_cases hq : c = '"'
  · subst hq; simp [junescape]
  by_cases hb : c = '\\'
  · subst hb; simp [junescape, hq]
  by_cases hn : c = '\n'
  · subst hn; simp [junescape]
  by_cases hr : c = '\r'
  · subst hr; simp [junescape]
  by_cases hc : c.toNat < 32
  · simp only [hq, hb, hn, hr, if_false, hc, if_true, List.cons_append, List.nil_append]
    rw [junescape]
    rw [hexQuad_escOf c hc]
    dsimp only
    have hs : ¬ (0xd800 ≤ c.toNat && c.toNat ≤ 0xdfff) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [if_neg hs, Char.ofNat_toNat]
  · simp only [hq, hb, hn, hr, hc, if_false, List.cons_append, List.nil_append]
    simp [junescape, hq, hb, hc]

/-- **The round trip, unconditional.**  Every list of characters — every doc
line the boundary could ever carry — survives being escaped and read back.  No
fragment restriction, no hypothesis: this is the theorem `Lean.Json`'s
`partial def`s make unstatable, and it is the reason this module exists. -/
theorem junescape_jescape : ∀ cs : List Char, junescape (jescape cs) = .ok cs := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c t ih =>
    show junescape (escOf c ++ jescape t) = _
    rw [junescape_escOf c (jescape t), ih]
    rfl

/-! ### J1 non-vacuity, and both directions (§5.2, §5.8)

A theorem that compiles and means nothing is the failure mode these guard
against.  `junescape_jescape` is true of `jescape = id` too, so the witnesses
below pin the actual bytes. -/

/-- A doc line carrying a quote, a backslash and a tab — the minimum §5.2 asks
for, in the shape a real `- [ ]` line would have. -/
def demoEscLine : List Char :=
  ['-', ' ', 's', 'a', 'y', ' ', '"', 'h', 'i', '"', ' ', '\\', 'n', '\t', 'x']

/-- **The escaping does real work.**  The exact bytes, decided. -/
theorem demo_jescape_bytes :
    jescape demoEscLine =
      ['-', ' ', 's', 'a', 'y', ' ', '\\', '"', 'h', 'i', '\\', '"', ' ',
       '\\', '\\', 'n', '\\', 'u', '0', '0', '0', '9', 'x'] := by decide

theorem demo_junescape_bytes : junescape (jescape demoEscLine) = .ok demoEscLine := rfl

/-- The escape is not the identity on this line — the check `demo_jescape_bytes`
would still pass if it were, so it is stated separately. -/
theorem the_escaping_is_not_vacuous : jescape demoEscLine ≠ demoEscLine := by decide

/-- A newline and a carriage return get the short escapes; every other control
character gets a quad.  This is decision 2's emit half. -/
theorem the_emitted_escape_classes :
    jescape ['\n'] = ['\\', 'n'] ∧
    jescape ['\r'] = ['\\', 'r'] ∧
    jescape ['\t'] = ['\\', 'u', '0', '0', '0', '9'] ∧
    jescape [bsChar] = ['\\', 'u', '0', '0', '0', '8'] ∧
    jescape [ffChar] = ['\\', 'u', '0', '0', '0', 'c'] ∧
    jescape [Char.ofNat 0] = ['\\', 'u', '0', '0', '0', '0'] ∧
    jescape [Char.ofNat 31] = ['\\', 'u', '0', '0', '1', 'f'] := by decide

/-- Everything at or above `0x20` goes out verbatim: `DEL`, and a non-ASCII
character.  The kernel does not `\u`-escape what it does not have to. -/
theorem jescape_keeps_high_bytes_verbatim :
    jescape [Char.ofNat 0x7f] = [Char.ofNat 0x7f] ∧
    jescape [Char.ofNat 0xe9] = [Char.ofNat 0xe9] ∧
    jescape [Char.ofNat 0x1f600] = [Char.ofNat 0x1f600] := by decide

/-- **Decision 2, as a theorem.**  `\t`, `\b`, `\f` and `\/` are read even
though they are never written: serde_json emits all four, so a reader that
refused them would be a boundary hole with a proof attached. -/
theorem junescape_accepts_the_host_short_escapes :
    junescape ['\\', 't'] = .ok ['\t'] ∧
    junescape ['\\', 'b'] = .ok [bsChar] ∧
    junescape ['\\', 'f'] = .ok [ffChar] ∧
    junescape ['\\', '/'] = .ok ['/'] ∧
    junescape ['\\', 'u', '0', '0', '0', 'A'] = .ok ['\n'] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The asymmetry, stated where it cannot drift: the kernel's own spelling of a
tab and the host's spelling of a tab read back to the same bytes. -/
theorem the_accepted_escapes_exceed_the_emitted_ones :
    junescape (jescape ['\t']) = junescape ['\\', 't'] ∧
    jescape ['\t'] ≠ ['\\', 't'] :=
  ⟨rfl, by decide⟩

/-! ### The refusals, each by its own name (§5.7, §5.8) -/

theorem junescape_refuses_a_truncated_escape :
    junescape ['a', '\\'] = .error .truncatedEscape := rfl

theorem junescape_refuses_a_truncated_hex_quad :
    junescape ['\\', 'u', '0', '0', '9'] = .error .truncatedEscape := rfl

theorem junescape_refuses_a_bad_hex_quad :
    junescape ['\\', 'u', '0', '0', 'g', '9'] = .error (.badHexQuad '0' '0' 'g' '9') := rfl

theorem junescape_refuses_an_unknown_escape :
    junescape ['\\', 'q'] = .error (.unknownEscape 'q') := rfl

theorem junescape_refuses_a_raw_quote :
    junescape ['a', '"', 'b'] = .error .rawQuote := rfl

theorem junescape_refuses_a_raw_control :
    junescape ['a', '\t'] = .error (.rawControl 9) := rfl

/-- Decision 3, and README gap 42: a lone surrogate escape is refused rather
than guessed at.  Both halves of a pair are refused, so the failure is the same
whichever end a mis-encoding starts at. -/
theorem junescape_refuses_a_lone_surrogate :
    junescape ['\\', 'u', 'd', '8', '3', 'd'] = .error (.surrogateEscape 0xd83d) ∧
    junescape ['\\', 'u', 'd', 'e', '0', '0'] = .error (.surrogateEscape 0xde00) ∧
    junescape ['\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'd', 'e', '0', '0']
      = .error (.surrogateEscape 0xd83d) :=
  ⟨rfl, rfl, rfl⟩

/-- The surrogate guard is not swallowing the whole `\u` branch: the quads just
below and just above the surrogate block are accepted. -/
theorem the_surrogate_guard_is_not_vacuous :
    junescape ['\\', 'u', 'd', '7', 'f', 'f'] = .ok [Char.ofNat 0xd7ff] ∧
    junescape ['\\', 'u', 'e', '0', '0', '0'] = .ok [Char.ofNat 0xe000] :=
  ⟨rfl, rfl⟩

/-! ## J2 — numerals

§5.3: two definitions of one concept **is** the bug.  The JSON numeral is not a
second grammar — it is `Text.lean`'s `digitsOf`, under a name that says where
it is used.  The only thing new here is the **next-byte guard**, which is what
a numeral inside a larger document needs and a numeral alone does not. -/

/-- The JSON numeral *is* `digitsOf`.  An `abbrev`, so there is one definition
and `readNat_digitsOf`/`digitsOf_injective` apply to it unchanged. -/
abbrev jrenderNat : Nat → List Char := digitsOf

theorem jrenderNat_is_digitsOf (n : Nat) : jrenderNat n = digitsOf n := rfl

/-- What may follow a numeral: end of input, or a byte that is not a digit.  At
J4's use sites that byte is `,`, `]`, `}` or a space, and the guard is
discharged there by `decide`. -/
def notDigitStart : List Char → Bool
  | [] => true
  | c :: _ => !(charDigit c).isSome

/-- The maximal run of digits, and what is left.  Structural. -/
def jdigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if (charDigit c).isSome then
      let p := jdigits cs
      (c :: p.1, p.2)
    else ([], c :: cs)

/-- Read a numeral off the front of a document.  `none` when the front is not a
digit — a JSON number is never empty. -/
def jparseNat (l : List Char) : Option (Nat × List Char) :=
  match jdigits l with
  | ([], _) => none
  | (ds, rest) => (readNat ds).map (fun n => (n, rest))

/-- The digit run of `a ++ r` is `a`, provided `a` is all digits and `r` does
not start with one.  Both hypotheses are needed and both bite below. -/
theorem jdigits_append : ∀ (a r : List Char), (∀ c ∈ a, (charDigit c).isSome) →
    notDigitStart r = true → jdigits (a ++ r) = (a, r) := by
  intro a
  induction a with
  | nil =>
    intro r _ hr
    cases r with
    | nil => rfl
    | cons c cs =>
      unfold notDigitStart at hr
      simp only [Bool.not_eq_true'] at hr
      unfold jdigits
      simp [hr]
  | cons x xs ih =>
    intro r ha hr
    have hx : (charDigit x).isSome := ha x (List.mem_cons_self ..)
    have hxs : ∀ c ∈ xs, (charDigit c).isSome := fun c hc => ha c (List.mem_cons_of_mem _ hc)
    show jdigits (x :: (xs ++ r)) = _
    unfold jdigits
    simp only [hx, if_true]
    rw [ih r hxs hr]

/-- **The numeral round trip at the JSON level.**  Whatever the kernel writes as
a number, a reader positioned on it reads back — *and stops in the right
place*, which is the half `readNat_digitsOf` alone does not give. -/
theorem jparseNat_jrenderNat (n : Nat) (rest : List Char) (h : notDigitStart rest = true) :
    jparseNat (jrenderNat n ++ rest) = some (n, rest) := by
  unfold jparseNat
  rw [jrenderNat_is_digitsOf, jdigits_append (digitsOf n) rest (digitsOf_all_digits n) h]
  cases hd : digitsOf n with
  | nil => exact absurd hd (digitsOf_ne_nil n)
  | cons a t =>
    simp only []
    have : readNat (a :: t) = some n := by rw [← hd]; exact readNat_digitsOf n
    rw [this]
    rfl

/-! ### J2 non-vacuity and the guard's bite -/

/-- Real bytes: a year, then the `,` that follows it in a document. -/
theorem demo_jparseNat :
    jparseNat (jrenderNat 2026 ++ [',', ' ', '"', 'i', 'x', '"']) =
      some (2026, [',', ' ', '"', 'i', 'x', '"']) ∧
    jrenderNat 2026 = ['2', '0', '2', '6'] := by decide

/-- **The next-byte guard is a real guard, not decoration.**  Drop it and the
conclusion is false: `1` followed by `2` reads as `12` with nothing left over,
not as `1` with `2` left over.  §5.8 — the check bites. -/
theorem the_next_byte_guard_bites :
    notDigitStart ['2'] = false ∧
    jparseNat (jrenderNat 1 ++ ['2']) = some (12, []) ∧
    jparseNat (jrenderNat 1 ++ ['2']) ≠ some (1, ['2']) := by decide

/-- The guard holds of every byte a numeral is actually followed by in a JSON
document, so `jparseNat_jrenderNat` is not a hypothesis nothing satisfies
(§7.4 item 2). -/
theorem the_next_byte_guard_is_satisfiable :
    notDigitStart [] = true ∧ notDigitStart [','] = true ∧
    notDigitStart [']'] = true ∧ notDigitStart ['}'] = true ∧
    notDigitStart [' '] = true := by decide

theorem jparseNat_refuses_a_non_numeral :
    jparseNat ['x', '1'] = none ∧ jparseNat [] = none ∧ jparseNat ['-', '3'] = none := by decide

/-- A numeral runs to the end of the document when nothing follows it, and
`jdigits` leaves nothing behind. -/
theorem jparseNat_reads_a_bare_numeral :
    jparseNat (jrenderNat 0) = some (0, []) ∧
    jparseNat (jrenderNat 1000000) = some (1000000, []) := by decide

end Tm
