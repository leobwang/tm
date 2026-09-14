import TmKernel.Text
/-!
# The kernel's own JSON fragment: the value, the escaping, the numerals

`Lean.Json` cannot be reasoned about here.  Its printer (`Json.compress`,
`Json.render`) and every recursive worker of `Json.parse` are `partial def`s in
v4.33.1, which elaborate to **opaque constants**: no equation lemmas, nothing to
unfold, nothing `simp`/`decide`/induction can touch.  The README's
"Gap 39 REPRICED" paragraph measures that and prices the replacement as J0–J6;
this module is J0–J2 (step 1) and J3–J4 (step 2: the emitter `jemit`, the
fuel-structural parser `jparse`, `jparse_jemit` and `jparse_never_runs_out`).
It is gap 12's move one level up — own the function, prove the round trip, and
let agreement with the *host's* reader (serde_json, which is the only reader
these bytes ever had in production) stay corpus and FFI evidence rather than a
theorem.

**On the wire since J5, both ways.**  `Boundary.call` reads the request with
`jparse` and every field with `jget` (end of this module), and writes every
response as a `JVal` with `jemit`; no kernel module imports `Lean.Data.Json`.
The per-character recursions run as proved `@[csimp]` twins (`jescapeTR`,
`junescapeTR`, `jscanTR`), and since stage 5 A1 so do the per-element ones
(`jemitAcc`…`jemitOTailAcc`, `jvalAcc`…`jotailAcc`; README gap 44, closed).

## The three decisions this module takes, stated rather than left implicit

1. **A bare natural is `num`; every other numeral is `dec`, exactly as
   written.**  Every number the boundary emits is a `Nat` — `lerrJson`'s
   `badLine` line number, `regionJson`'s `grain` (a `Fin 4` value) and its
   `ix` — and every number it ingests goes through `Boundary.getNat`, so until
   stage 5 `JVal.num` carried a `Nat` and the fragment had no other numeral.
   **Widened at stage 5 A2** (design §5.1), visibly, in this diff: D9's log
   carries `hsw` decimals and hand-appended unknown numerals, so `JVal.dec`
   holds a `JDec` — sign, integer digits' value, fraction digits and exponent
   *digits*, never evaluated.  A wire reader still wants `num` and refuses a
   `dec` by its own name (`Boundary.getNat`, `parseClock`).  Leading zeros are
   refused as serde_json refuses them (README gap 43, closed).

   One disagreement with the design, recorded in the README: §5.1 stores the
   exponent as `Option (Bool × List (Fin 10))`, and over that type
   `jparse_jemit` is **false** — `some (false, [])` would emit `1e`, which no
   reader takes back.  The type here forbids it instead (§3.1 item 1): the
   exponent is a first digit and the rest.

2. **Emit narrow, accept wide.**  `jescape` emits exactly what Lean's own
   printer emits — `\"`, `\\`, `\n`, `\r`, a `\u00xx` hex quad (lowercase) for
   every other character below `0x20`, and every character at or above `0x20`
   verbatim, non-ASCII and `DEL` included.  `junescape` additionally *accepts*
   `\/`, `\t`, `\b` and `\f`, which serde_json does emit, and accepts hex quads
   in either case.  `the_accepted_escapes_exceed_the_emitted_ones` states the
   asymmetry as a theorem rather than a comment.

3. **A surrogate pair is read; a lone surrogate escape is refused by name.**
   Lean's `Char` is a Unicode *scalar* value, so `0xd800`–`0xdfff` is not a
   character and `jescape` can never emit one.  Since stage 5 A2 `junescape`
   reads `😀` as the one character it stands for, as serde_json
   does, and refuses every surrogate that is not the high half of such a pair
   with `JEsc.surrogateEscape` (README gap 42, closed).  serde_json never
   emits a pair itself (it writes astral characters as UTF-8 bytes), but a
   hand-edited log line may carry one.

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

/-- **A JSON numeral that is not a bare natural, kept exactly as written.**
Never evaluated (stage 5 A2, design §5.1).  `int` is the integer digits' value:
leading zeros are refused (gap 43), so the digits are `digitsOf int` and nothing
is lost.  `frac` is the fraction digits verbatim, `[]` exactly when no `.` was
read.  `exp` is the exponent marker's sign and its **digits**, a first digit and
the rest, never a value: no reader can build `10^e` from a short numeral by
accident, and `1e0005` re-emits as written.  `E` and `+` are not kept, so `1E+5`
and `1e5` are one value. -/
structure JDec where
  neg  : Bool
  int  : Nat
  frac : List (Fin 10)
  exp  : Option (Bool × Fin 10 × List (Fin 10))
deriving DecidableEq, Repr

/-- A numeral with no sign, no fraction and no exponent: that is `JVal.num`,
never `JVal.dec`, so one numeral has one value. -/
def JDec.plain (d : JDec) : Bool := !d.neg && d.frac.isEmpty && d.exp.isNone

inductive JVal
  | null
  | bool (b : Bool)
  | num (n : Nat)
  /-- The stage-5 A2 widening (AGENTS §8.3: visibly, in a diff). -/
  | dec (d : { d : JDec // d.plain = false })
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
  | .dec a,  .dec b  => a.val == b.val
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
    ?null ?bool ?num ?dec ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair a
  case null =>
    intro b h; cases b <;> simp_all [jbeq]
  case bool =>
    intro x b h; cases b <;> simp_all [jbeq]
  case num =>
    intro x b h; cases b <;> simp_all [jbeq]
  case dec =>
    intro x b h; cases b <;> simp_all [jbeq]
    exact Subtype.ext h
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
    ?null ?bool ?num ?dec ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair a <;>
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

/-- **`jescape`'s runtime twin (J5).**  Compiled as written, `jescape` takes one
stack frame per character — it is structural, not tail-recursive — and on the
wire that was measured, not guessed: a single 100 000-character line overflowed
a 2 MiB thread through `call`, where `Lean.Json`'s printer (a work loop) wrote a
1 000 000-character line on the same stack.  `List.flatMap` runs as core's
`flatMapTR`, so this twin writes any line in constant stack.  The proofs never
see it: `jescape_eq_jescapeTR` is a `@[csimp]` theorem, so the compiler's
substitution is itself proved — the opposite of an `@[implemented_by]` promise
(R4) — and every `decide`/`rfl` above and below still reduces `jescape`. -/
def jescapeTR (cs : List Char) : List Char := cs.flatMap escOf

@[csimp] theorem jescape_eq_jescapeTR : @jescape = @jescapeTR := by
  funext cs
  induction cs with
  | nil => rfl
  | cons c t ih =>
    show escOf c ++ jescape t = (c :: t).flatMap escOf
    rw [List.flatMap_cons, ih]
    rfl

/-- Why `junescape` refused.  §5.7: every diagnostic is named. -/
inductive JEsc
  /-- A `\` with nothing after it, or a `\u` with fewer than four bytes after it. -/
  | truncatedEscape
  /-- A `\` followed by a byte that is not an escape letter. -/
  | unknownEscape (c : Char)
  /-- `\u` followed by four bytes that are not all hex. -/
  | badHexQuad (a b c d : Char)
  /-- A quad in `0xd800`–`0xdfff` that is not the high half of a surrogate pair:
  not a Unicode scalar value.  Decision 3; since stage 5 A2 a pair is read. -/
  | surrogateEscape (v : Nat)
  /-- An unescaped `"` inside string content. -/
  | rawQuote
  /-- An unescaped character below `0x20`, which RFC 8259 forbids. -/
  | rawControl (v : Nat)
deriving DecidableEq, Repr, Inhabited

/-- The high half of a UTF-16 surrogate pair. -/
def isHighSurrogate (v : Nat) : Bool := 0xd800 ≤ v && v ≤ 0xdbff
/-- The low half. -/
def isLowSurrogate (v : Nat) : Bool := 0xdc00 ≤ v && v ≤ 0xdfff
/-- The scalar a high and a low surrogate stand for, as serde_json combines them. -/
def pairScalar (hi lo : Nat) : Nat := 0x10000 + (hi - 0xd800) * 0x400 + (lo - 0xdc00)

/-- Undo `jescape`.  Structural: every recursive call is on a proper tail, the
`\uXXXX` branch six characters in and a surrogate pair twelve.  No fuel, no
well-founded recursion, so it reduces and `decide` can see it.

**A surrogate pair is read (stage 5 A2; README gap 42, closed)**, as serde_json
reads it: a high surrogate quad followed at once by a low one is the one scalar
`pairScalar` gives.  Every other surrogate — a low one, or a high one not
followed by a low quad — is refused with `surrogateEscape` and the first quad's
value; a high one followed by a `\u` whose four bytes are not hex is that
quad's `badHexQuad`. -/
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
        if isHighSurrogate v then
          match rest with
          | '\\' :: 'u' :: e :: f :: g :: h :: rest' =>
            match hexQuad e f g h with
            | none => .error (.badHexQuad e f g h)
            | some w =>
              if isLowSurrogate w then (junescape rest').map (fun t => Char.ofNat (pairScalar v w) :: t)
              else .error (.surrogateEscape v)
          | _ => .error (.surrogateEscape v)
        else if isLowSurrogate v then .error (.surrogateEscape v)
        else (junescape rest).map (fun t => Char.ofNat v :: t)
  | '\\' :: 'u' :: _ => .error .truncatedEscape
  | '\\' :: e :: _ => .error (.unknownEscape e)
  | '\\' :: [] => .error .truncatedEscape
  | c :: rest =>
      if c = '"' then .error .rawQuote
      else if c.toNat < 32 then .error (.rawControl c.toNat)
      else (junescape rest).map (fun t => c :: t)

/-! ### `junescape`'s runtime twin (J5)

Structural and not tail-recursive, `junescape` compiled as written takes a
stack frame per character of every string the request carries — the same
defect `jescapeTR` fixed on the response side, now on the request side.  The
twin carries the reversed output in an accumulator, and `@[csimp]` makes the
compiler run it; `junescape_eq_junescapeTR` is the proof that the substitution
changes nothing.  Every theorem in this module is still about `junescape`. -/

/-- The accumulator form.  The same patterns, in the same order, as
`junescape`; only the recursive calls move into tail position. -/
def junescapeTR.go : List Char → List Char → Except JEsc (List Char)
  | [], acc => .ok acc.reverse
  | '\\' :: '"'  :: rest, acc => junescapeTR.go rest ('"' :: acc)
  | '\\' :: '\\' :: rest, acc => junescapeTR.go rest ('\\' :: acc)
  | '\\' :: '/'  :: rest, acc => junescapeTR.go rest ('/' :: acc)
  | '\\' :: 'n'  :: rest, acc => junescapeTR.go rest ('\n' :: acc)
  | '\\' :: 'r'  :: rest, acc => junescapeTR.go rest ('\r' :: acc)
  | '\\' :: 't'  :: rest, acc => junescapeTR.go rest ('\t' :: acc)
  | '\\' :: 'b'  :: rest, acc => junescapeTR.go rest (bsChar :: acc)
  | '\\' :: 'f'  :: rest, acc => junescapeTR.go rest (ffChar :: acc)
  | '\\' :: 'u'  :: a :: b :: c :: d :: rest, acc =>
      match hexQuad a b c d with
      | none => .error (.badHexQuad a b c d)
      | some v =>
        if isHighSurrogate v then
          match rest with
          | '\\' :: 'u' :: e :: f :: g :: h :: rest' =>
            match hexQuad e f g h with
            | none => .error (.badHexQuad e f g h)
            | some w =>
              if isLowSurrogate w then junescapeTR.go rest' (Char.ofNat (pairScalar v w) :: acc)
              else .error (.surrogateEscape v)
          | _ => .error (.surrogateEscape v)
        else if isLowSurrogate v then .error (.surrogateEscape v)
        else junescapeTR.go rest (Char.ofNat v :: acc)
  | '\\' :: 'u' :: _, _ => .error .truncatedEscape
  | '\\' :: e :: _, _ => .error (.unknownEscape e)
  | '\\' :: [], _ => .error .truncatedEscape
  | c :: rest, acc =>
      if c = '"' then .error .rawQuote
      else if c.toNat < 32 then .error (.rawControl c.toNat)
      else junescapeTR.go rest (c :: acc)
termination_by structural l => l

def junescapeTR (l : List Char) : Except JEsc (List Char) := junescapeTR.go l []

/-- Consing onto the result is pushing onto the accumulator. -/
theorem junescapeTR_step (x : Except JEsc (List Char)) (acc : List Char) (c : Char) :
    Except.map (fun t => acc.reverse ++ t) (Except.map (fun t => c :: t) x)
      = Except.map (fun t => (c :: acc).reverse ++ t) x := by
  cases x <;> simp [Except.map]

set_option linter.unusedSimpArgs false in
/-- The accumulator invariant, by strong induction on the input's length (the
`\uXXXX` branch recurses six characters in).  One case per `junescape`
pattern. -/
theorem junescapeTR_go (n : Nat) : ∀ (l acc : List Char), l.length ≤ n →
    junescapeTR.go l acc = (junescape l).map (fun t => acc.reverse ++ t) := by
  induction n with
  | zero =>
    intro l acc h
    cases l with
    | nil => simp [junescapeTR.go, junescape, Except.map]
    | cons c t => simp at h
  | succ n ih =>
    intro l acc h
    cases l with
    | nil => simp [junescapeTR.go, junescape, Except.map]
    | cons c rest =>
      simp only [List.length_cons] at h
      by_cases hb : c = '\\'
      · subst hb
        cases rest with
        | nil => simp [junescapeTR.go, junescape, Except.map]
        | cons e r =>
          simp only [List.length_cons] at h
          have ihr := ih r
          by_cases h1 : e = '"'
          · subst h1; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h2 : e = '\\'
          · subst h2; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h3 : e = '/'
          · subst h3; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h4 : e = 'n'
          · subst h4; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h5 : e = 'r'
          · subst h5; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h6 : e = 't'
          · subst h6; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h7 : e = 'b'
          · subst h7; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h8 : e = 'f'
          · subst h8; simp only [junescapeTR.go, junescape]
            rw [ihr _ (by omega), junescapeTR_step]
          by_cases h9 : e = 'u'
          · subst h9
            match r with
            | a :: b :: c :: d :: r' =>
              simp only [List.length_cons] at h
              simp only [junescapeTR.go, junescape]
              cases hx : hexQuad a b c d with
              | none => simp [Except.map]
              | some v =>
                simp only
                by_cases hh : isHighSurrogate v = true
                · rw [if_pos hh, if_pos hh]
                  split
                  · next e f g k r'' =>
                    simp only [List.length_cons] at h
                    cases hy : hexQuad e f g k with
                    | none => simp [Except.map]
                    | some w =>
                      simp only
                      by_cases hlo : isLowSurrogate w = true
                      · rw [if_pos hlo, if_pos hlo, ih r'' _ (by omega), junescapeTR_step]
                      · simp [hlo, Except.map]
                  · rfl
                · rw [if_neg hh, if_neg hh]
                  by_cases hl : isLowSurrogate v = true
                  · simp [hl, Except.map]
                  · rw [if_neg hl, if_neg hl, ih r' _ (by omega), junescapeTR_step]
            | [] => simp [junescapeTR.go, junescape, Except.map]
            | [_] => simp [junescapeTR.go, junescape, Except.map]
            | [_, _] => simp [junescapeTR.go, junescape, Except.map]
            | [_, _, _] => simp [junescapeTR.go, junescape, Except.map]
          · have e1 : junescapeTR.go ('\\' :: e :: r) acc = .error (.unknownEscape e) := by
              simp [junescapeTR.go, h1, h2, h3, h4, h5, h6, h7, h8, h9]
            have e2 : junescape ('\\' :: e :: r) = .error (.unknownEscape e) := by
              simp [junescape, h1, h2, h3, h4, h5, h6, h7, h8, h9]
            rw [e1, e2]; rfl
      · by_cases hq : c = '"'
        · subst hq; simp [junescapeTR.go, junescape, Except.map]
        by_cases hc : c.toNat < 32
        · simp [junescapeTR.go, junescape, Except.map, hb, hq, hc]
        · have e1 : junescapeTR.go (c :: rest) acc = junescapeTR.go rest (c :: acc) := by
            simp [junescapeTR.go, hb, hq, hc]
          have e2 : junescape (c :: rest) = (junescape rest).map (fun t => c :: t) := by
            simp [junescape, hb, hq, hc]
          rw [e1, e2, ih rest _ (by omega), junescapeTR_step]

/-- **The compiler runs the twin, and this is why that is sound.** -/
@[csimp] theorem junescape_eq_junescapeTR : @junescape = @junescapeTR := by
  funext l
  rw [junescapeTR, junescapeTR_go l.length l [] (Nat.le_refl _)]
  cases junescape l <;> simp [Except.map]

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
    have hs : ¬ isHighSurrogate c.toNat = true := by
      simp only [isHighSurrogate, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hs' : ¬ isLowSurrogate c.toNat = true := by
      simp only [isLowSurrogate, Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [if_neg hs, if_neg hs', Char.ofNat_toNat]
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

/-- **A surrogate pair is read** (stage 5 A2; README gap 42, closed): `\ud83d\ude00`
is U+1F600, as serde_json reads it, and so is the uppercase spelling.  This is
the refutation of stage 3's third conjunct of `junescape_refuses_a_lone_surrogate`,
which refused this pair. -/
theorem junescape_reads_a_surrogate_pair :
    junescape ['\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'd', 'e', '0', '0']
      = .ok [Char.ofNat 0x1f600] ∧
    junescape ['a', '\\', 'u', 'D', '8', '0', '0', '\\', 'u', 'D', 'C', '0', '0', 'b']
      = .ok ['a', Char.ofNat 0x10000, 'b'] ∧
    junescape ['\\', 'u', 'd', 'b', 'f', 'f', '\\', 'u', 'd', 'f', 'f', 'f']
      = .ok [Char.ofNat 0x10ffff] :=
  ⟨rfl, rfl, rfl⟩

/-- **Decision 3, restated at A2: a lone surrogate is refused by name** — a low
one, a high one at the end, a high one followed by a character, by a non-surrogate
escape, or by a second high one.  The refusal names the first quad.  (Stage 3's
statement also refused a pair; its first two conjuncts stand here unchanged.) -/
theorem junescape_refuses_a_lone_surrogate :
    junescape ['\\', 'u', 'd', '8', '3', 'd'] = .error (.surrogateEscape 0xd83d) ∧
    junescape ['\\', 'u', 'd', 'e', '0', '0'] = .error (.surrogateEscape 0xde00) ∧
    junescape ['\\', 'u', 'd', '8', '3', 'd', 'x'] = .error (.surrogateEscape 0xd83d) ∧
    junescape ['\\', 'u', 'd', '8', '3', 'd', '\\', 'u', '0', '0', '4', '1']
      = .error (.surrogateEscape 0xd83d) ∧
    junescape ['\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'd', '8', '3', 'd']
      = .error (.surrogateEscape 0xd83d) ∧
    junescape ['\\', 'u', 'd', '8', '3', 'd', '\\', 'u', 'z', 'z', 'z', 'z']
      = .error (.badHexQuad 'z' 'z' 'z' 'z') :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- `jdigits`'s runtime twin (stage 5 A2, rule D9-21): every numeral on the wire runs
through it.  Declared before `jparseNat`, because `@[csimp]` rewrites only what is
compiled after it. -/
def jdigitsTR.go : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | c :: cs, acc => if (charDigit c).isSome then jdigitsTR.go cs (c :: acc) else (acc.reverse, c :: cs)

def jdigitsTR (l : List Char) : List Char × List Char := jdigitsTR.go l []

theorem jdigitsTR_go (l : List Char) : ∀ acc : List Char,
    jdigitsTR.go l acc = (acc.reverse ++ (jdigits l).1, (jdigits l).2) := by
  induction l with
  | nil => intro acc; simp [jdigitsTR.go, jdigits]
  | cons c cs ih =>
    intro acc
    by_cases hc : (charDigit c).isSome = true
    · simp [jdigitsTR.go, jdigits, hc, ih]
    · simp [jdigitsTR.go, jdigits, hc]

@[csimp] theorem jdigits_eq_jdigitsTR : @jdigits = @jdigitsTR := by
  funext l; simp [jdigitsTR, jdigitsTR_go]

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

/-! ### J2 for every numeral: the lexical decimal (stage 5 A2, design §5.1)

APPENDED 2026-09-14 (stage-5 D9 track, step A2).  A `JDec` is written as its
sign, `digitsOf` its integer value (the one natural numeral above, so §5.3 holds:
no second integer grammar), the fraction digits after a `.`, and `e`, a `-` for a
negative exponent, and the exponent digits.  Fraction and exponent digits are
`Fin 10`, read by `jfins`, whose guard is `notDigitStart` again.  The readers
that can refuse (`jfrac`, `jexp`, `jreadDec`) need `JErr` and live in J4. -/

/-- A digit as the `Fin 10` it is, through `charDigit`: one reading of a digit. -/
def digitFin (c : Char) : Option (Fin 10) :=
  match charDigit c with
  | some k => if h : k < 10 then some ⟨k, h⟩ else none
  | none => none

/-- A `Fin 10` digit's character, through `digitChar`. -/
def finChar (d : Fin 10) : Char := digitChar d.val

theorem digitFin_finChar : ∀ d : Fin 10, digitFin (finChar d) = some d := by decide

theorem digitFin_of_not_digit (c : Char) (h : (charDigit c).isSome = false) :
    digitFin c = none := by
  unfold digitFin
  cases hc : charDigit c with
  | none => rfl
  | some k => rw [hc] at h; cases h

theorem finChar_is_digit (d : Fin 10) : (charDigit (finChar d)).isSome = true := by
  revert d; decide

/-- The maximal run of digits as `Fin 10`s, and what is left.  Structural; the
compiler runs `jfinsTR`. -/
def jfins : List Char → List (Fin 10) × List Char
  | [] => ([], [])
  | c :: cs =>
    match digitFin c with
    | some d => let p := jfins cs; (d :: p.1, p.2)
    | none => ([], c :: cs)

/-- `jfins`'s runtime twin (D9-21): the digits read so far, reversed. -/
def jfinsTR.go : List Char → List (Fin 10) → List (Fin 10) × List Char
  | [], acc => (acc.reverse, [])
  | c :: cs, acc =>
    match digitFin c with
    | some d => jfinsTR.go cs (d :: acc)
    | none => (acc.reverse, c :: cs)

def jfinsTR (l : List Char) : List (Fin 10) × List Char := jfinsTR.go l []

theorem jfinsTR_go (l : List Char) : ∀ acc : List (Fin 10),
    jfinsTR.go l acc = (acc.reverse ++ (jfins l).1, (jfins l).2) := by
  induction l with
  | nil => intro acc; simp [jfinsTR.go, jfins]
  | cons c cs ih =>
    intro acc
    simp only [jfinsTR.go, jfins]
    cases digitFin c with
    | none => simp
    | some d => simp [ih]

@[csimp] theorem jfins_eq_jfinsTR : @jfins = @jfinsTR := by
  funext l; simp [jfinsTR, jfinsTR_go]

/-- The `Fin 10` run of `fs ++ r` is `fs`, provided `r` does not start with a
digit — `jdigits_append`'s statement, one type over. -/
theorem jfins_append (fs : List (Fin 10)) (r : List Char) (h : notDigitStart r = true) :
    jfins (fs.map finChar ++ r) = (fs, r) := by
  induction fs with
  | nil =>
    cases r with
    | nil => rfl
    | cons c t =>
      simp only [notDigitStart, Bool.not_eq_true'] at h
      simp [jfins, digitFin_of_not_digit c h]
  | cons x xs ih =>
    simp [jfins, digitFin_finChar, ih]

/-- **What may follow any numeral**: end of input, or a byte that neither
continues its digits nor starts a fraction or an exponent.  `notDigitStart` was
enough while every numeral was a natural; since A2 `1` followed by `.5` reads as
one numeral (`the_jval_jemit_fraction_guard_bites`).  Its first conjunct is
`notDigitStart`, so what held of that guard holds of this one. -/
def numEnd : List Char → Bool
  | [] => true
  | c :: _ => !(charDigit c).isSome && c != '.' && c != 'e' && c != 'E'

theorem notDigitStart_of_numEnd (l : List Char) (h : numEnd l = true) :
    notDigitStart l = true := by
  cases l with
  | nil => rfl
  | cons c t => simp only [numEnd, Bool.and_eq_true] at h; exact h.1.1.1

/-- The fraction's bytes: nothing for no fraction, else `.` and the digits. -/
def JDec.renderFrac : List (Fin 10) → List Char
  | [] => []
  | f :: fs => '.' :: (f :: fs).map finChar

/-- The exponent's bytes: `e`, `-` if negative, the digits as written. -/
def JDec.renderExp : Option (Bool × Fin 10 × List (Fin 10)) → List Char
  | none => []
  | some (false, x, xs) => 'e' :: (x :: xs).map finChar
  | some (true, x, xs) => 'e' :: '-' :: (x :: xs).map finChar

/-- The bytes after the sign. -/
def JDec.renderU (d : JDec) : List Char :=
  digitsOf d.int ++ (JDec.renderFrac d.frac ++ JDec.renderExp d.exp)

/-- **A decimal's bytes**, exactly as it was read (up to `E` and `+`). -/
def JDec.render (d : JDec) : List Char :=
  if d.neg then '-' :: d.renderU else d.renderU

theorem JDec.renderU_ne_nil (d : JDec) : ∃ c t, d.renderU = c :: t ∧ (charDigit c).isSome = true := by
  unfold JDec.renderU
  cases hd : digitsOf d.int with
  | nil => exact absurd hd (digitsOf_ne_nil _)
  | cons c t =>
    exact ⟨c, _, rfl, digitsOf_all_digits d.int c (by rw [hd]; simp)⟩

/-- **A leading zero.**  `0` followed by another digit; RFC 8259 and serde_json
refuse it (gap 43).  One `0`, and `0.5`, are not. -/
def jleadingZero : List Char → Bool
  | '0' :: c :: _ => (charDigit c).isSome
  | _ => false

/-- The only natural whose digits start with `0` is `0` itself, written `0`. -/
theorem digitsOf_zero_head : ∀ (n : Nat) (t : List Char), digitsOf n = '0' :: t → n = 0 ∧ t = [] := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t h
    rw [digitsOf_eq] at h
    by_cases hn : n < 10
    · rw [if_pos hn] at h
      simp only [List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have key : ∀ k < 10, digitChar k = '0' → k = 0 := by decide
      exact ⟨key n hn h1, h2.symm⟩
    · rw [if_neg hn] at h
      cases hd : digitsOf (n / 10) with
      | nil => exact absurd hd (digitsOf_ne_nil _)
      | cons a s =>
        rw [hd] at h
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨h1, _⟩ := h
        have := ih (n / 10) (by omega) s (by rw [hd, h1])
        omega

/-- **What the kernel writes has no leading zero**, whatever follows a `0`, as
long as it is not a digit. -/
theorem jleadingZero_digitsOf (n : Nat) (Y : List Char) (h : notDigitStart Y = true) :
    jleadingZero (digitsOf n ++ Y) = false := by
  cases hd : digitsOf n with
  | nil => exact absurd hd (digitsOf_ne_nil _)
  | cons c s =>
    by_cases hc : c = '0'
    · subst hc
      obtain ⟨_, rfl⟩ := digitsOf_zero_head n s hd
      cases Y with
      | nil => rfl
      | cons y t =>
        simp only [notDigitStart, Bool.not_eq_true'] at h
        simp [jleadingZero, h]
    · simp only [List.cons_append]
      unfold jleadingZero
      split
      · next heq => simp only [List.cons.injEq] at heq; exact absurd heq.1 hc
      · rfl

/-! ## J3 — the emitter

Compress-shaped: no space, no newline, no indent.  Six mutually structural
functions rather than three, because the *parser* below has six entry points and
one emitter function per parser entry point is what makes `jparse_jemit` a
rewrite chain instead of a case analysis.  `jemitArr`/`jemitObj` are what follows
an opening bracket; `jemitTail`/`jemitOTail` are what follows an element or a
pair.  They differ only in the separator, and that difference is exactly the one
the parser has to make.

Objects emit in **assoc-list order** — build order, not sorted order.  That is
J0's decision cashed: `Json.mkObj` cannot express it, and it is why
`jparse_jemit` needs no side condition about duplicate keys (see
`the_round_trip_survives_duplicate_keys`). -/

mutual
/-- The bytes of a value. -/
def jemit : JVal → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool b => if b then ['t', 'r', 'u', 'e'] else ['f', 'a', 'l', 's', 'e']
  | .num n => jrenderNat n
  | .dec d => d.val.render
  | .str s => '"' :: (jescape s ++ ['"'])
  | .arr xs => '[' :: jemitArr xs
  | .obj kvs => '{' :: jemitObj kvs
/-- What follows `[`: the elements and the closing `]`. -/
def jemitArr : List JVal → List Char
  | [] => [']']
  | x :: xs => jemit x ++ jemitTail xs
/-- What follows an element: `]`, or `,` and more. -/
def jemitTail : List JVal → List Char
  | [] => [']']
  | x :: xs => ',' :: (jemit x ++ jemitTail xs)
/-- What follows `{`: the pairs and the closing `}`. -/
def jemitObj : List (List Char × JVal) → List Char
  | [] => ['}']
  | kv :: kvs => jemitPair kv ++ jemitOTail kvs
/-- One `"key":value`, the key escaped exactly as a string is. -/
def jemitPair : List Char × JVal → List Char
  | (k, v) => '"' :: (jescape k ++ '"' :: ':' :: jemit v)
/-- What follows a pair: `}`, or `,` and more. -/
def jemitOTail : List (List Char × JVal) → List Char
  | [] => ['}']
  | kv :: kvs => ',' :: (jemitPair kv ++ jemitOTail kvs)
end

/-! ### The emitter's runtime twin (stage 5 A1, gap 44 closed)

APPENDED 2026-09-14 (stage-5 D9 track, step A1).  Compiled as written,
`jemitArr`/`jemitTail` and `jemitObj`/`jemitOTail` take a stack frame per array
element or object pair (README gap 44).  The twin writes the output **reversed
into an accumulator**, one element after another in tail position, and reverses
once at the end; it recurses per *nesting level* only.  All six functions get a
`@[csimp]` twin, not just the two tails, because the compiler substitutes a
constant at its call sites and `jemit`'s own compiled body would otherwise keep
calling the old `jemitArr`.  The proofs never see the twin: `jparse_jemit` and
every `decide` in the kernel are still about `jemit`.  Rule D9-21. -/

mutual
def jemitRev : JVal → List Char → List Char
  | .null, acc => 'l' :: 'l' :: 'u' :: 'n' :: acc
  | .bool b, acc => if b then 'e' :: 'u' :: 'r' :: 't' :: acc else 'e' :: 's' :: 'l' :: 'a' :: 'f' :: acc
  | .num n, acc => List.reverseAux (jrenderNat n) acc
  | .dec d, acc => List.reverseAux d.val.render acc
  | .str s, acc => '"' :: List.reverseAux (jescape s) ('"' :: acc)
  | .arr xs, acc => jemitArrAcc.go xs ('[' :: acc)
  | .obj kvs, acc => jemitObjAcc.go kvs ('{' :: acc)
def jemitArrAcc.go : List JVal → List Char → List Char
  | [], acc => ']' :: acc
  | x :: xs, acc => jemitTailAcc.go xs (jemitRev x acc)
def jemitTailAcc.go : List JVal → List Char → List Char
  | [], acc => ']' :: acc
  | x :: xs, acc => jemitTailAcc.go xs (jemitRev x (',' :: acc))
def jemitObjAcc.go : List (List Char × JVal) → List Char → List Char
  | [], acc => '}' :: acc
  | kv :: kvs, acc => jemitOTailAcc.go kvs (jemitPairAcc.go kv acc)
def jemitPairAcc.go : List Char × JVal → List Char → List Char
  | (k, v), acc => jemitRev v (':' :: '"' :: List.reverseAux (jescape k) ('"' :: acc))
def jemitOTailAcc.go : List (List Char × JVal) → List Char → List Char
  | [], acc => '}' :: acc
  | kv :: kvs, acc => jemitOTailAcc.go kvs (jemitPairAcc.go kv (',' :: acc))
end

def jemitAcc (v : JVal) : List Char := (jemitRev v []).reverse
def jemitArrAcc (xs : List JVal) : List Char := (jemitArrAcc.go xs []).reverse
def jemitTailAcc (xs : List JVal) : List Char := (jemitTailAcc.go xs []).reverse
def jemitObjAcc (kvs : List (List Char × JVal)) : List Char := (jemitObjAcc.go kvs []).reverse
def jemitPairAcc (kv : List Char × JVal) : List Char := (jemitPairAcc.go kv []).reverse
def jemitOTailAcc (kvs : List (List Char × JVal)) : List Char := (jemitOTailAcc.go kvs []).reverse

theorem jemitRev_eq (v : JVal) : ∀ acc, jemitRev v acc = (jemit v).reverse ++ acc := by
  refine JVal.rec
    (motive_1 := fun v => ∀ acc, jemitRev v acc = (jemit v).reverse ++ acc)
    (motive_2 := fun xs => (∀ acc, jemitArrAcc.go xs acc = (jemitArr xs).reverse ++ acc) ∧
                           (∀ acc, jemitTailAcc.go xs acc = (jemitTail xs).reverse ++ acc))
    (motive_3 := fun kvs => (∀ acc, jemitObjAcc.go kvs acc = (jemitObj kvs).reverse ++ acc) ∧
                            (∀ acc, jemitOTailAcc.go kvs acc = (jemitOTail kvs).reverse ++ acc))
    (motive_4 := fun p => ∀ acc, jemitPairAcc.go p acc = (jemitPair p).reverse ++ acc)
    ?null ?bool ?num ?dec ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair v
  case null => intro acc; rfl
  case bool => intro b acc; cases b <;> rfl
  case num => intro n acc; simp [jemitRev, jemit, List.reverseAux_eq]
  case dec => intro d acc; simp [jemitRev, jemit, List.reverseAux_eq]
  case str => intro s acc; simp [jemitRev, jemit, List.reverseAux_eq]
  case arr => intro xs ih acc; simp [jemitRev, jemit, ih.1]
  case obj => intro kvs ih acc; simp [jemitRev, jemit, ih.1]
  case lnil => exact ⟨fun acc => rfl, fun acc => rfl⟩
  case lcons =>
    intro x xs ihx ihxs
    exact ⟨fun acc => by simp [jemitArrAcc.go, jemitArr, ihx, ihxs.2],
           fun acc => by simp [jemitTailAcc.go, jemitTail, ihx, ihxs.2]⟩
  case onil => exact ⟨fun acc => rfl, fun acc => rfl⟩
  case ocons =>
    intro kv kvs ihkv ihkvs
    exact ⟨fun acc => by simp [jemitObjAcc.go, jemitObj, ihkv, ihkvs.2],
           fun acc => by simp [jemitOTailAcc.go, jemitOTail, ihkv, ihkvs.2]⟩
  case pair =>
    intro k v ihv acc
    simp [jemitPairAcc.go, jemitPair, ihv, List.reverseAux_eq]

theorem jemitTailAcc_go_eq (xs : List JVal) (acc : List Char) :
    jemitTailAcc.go xs acc = (jemitTail xs).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [jemitTailAcc.go, jemitTail, jemitRev_eq, ih]
theorem jemitArrAcc_go_eq (xs : List JVal) (acc : List Char) :
    jemitArrAcc.go xs acc = (jemitArr xs).reverse ++ acc := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [jemitArrAcc.go, jemitArr, jemitRev_eq, jemitTailAcc_go_eq]
theorem jemitOTailAcc_go_eq (kvs : List (List Char × JVal)) (acc : List Char) :
    jemitOTailAcc.go kvs acc = (jemitOTail kvs).reverse ++ acc := by
  induction kvs generalizing acc with
  | nil => rfl
  | cons kv kvs ih =>
    obtain ⟨k, v⟩ := kv
    simp [jemitOTailAcc.go, jemitOTail, jemitPairAcc.go, jemitPair, jemitRev_eq, ih, List.reverseAux_eq]
theorem jemitPairAcc_go_eq (kv : List Char × JVal) (acc : List Char) :
    jemitPairAcc.go kv acc = (jemitPair kv).reverse ++ acc := by
  obtain ⟨k, v⟩ := kv
  simp [jemitPairAcc.go, jemitPair, jemitRev_eq, List.reverseAux_eq]
theorem jemitObjAcc_go_eq (kvs : List (List Char × JVal)) (acc : List Char) :
    jemitObjAcc.go kvs acc = (jemitObj kvs).reverse ++ acc := by
  cases kvs with
  | nil => rfl
  | cons kv kvs => simp [jemitObjAcc.go, jemitObj, jemitPairAcc_go_eq, jemitOTailAcc_go_eq]

@[csimp] theorem jemit_eq_jemitAcc : @jemit = @jemitAcc := by
  funext v; simp [jemitAcc, jemitRev_eq]
@[csimp] theorem jemitArr_eq_jemitArrAcc : @jemitArr = @jemitArrAcc := by
  funext xs; simp [jemitArrAcc, jemitArrAcc_go_eq]
@[csimp] theorem jemitTail_eq_jemitTailAcc : @jemitTail = @jemitTailAcc := by
  funext xs; simp [jemitTailAcc, jemitTailAcc_go_eq]
@[csimp] theorem jemitObj_eq_jemitObjAcc : @jemitObj = @jemitObjAcc := by
  funext kvs; simp [jemitObjAcc, jemitObjAcc_go_eq]
@[csimp] theorem jemitPair_eq_jemitPairAcc : @jemitPair = @jemitPairAcc := by
  funext kv; simp [jemitPairAcc, jemitPairAcc_go_eq]
@[csimp] theorem jemitOTail_eq_jemitOTailAcc : @jemitOTail = @jemitOTailAcc := by
  funext kvs; simp [jemitOTailAcc, jemitOTailAcc_go_eq]

/-! ### The fuel a value needs, and why it is derivable from the bytes

`jparse` is total by **fuel that is structurally consumed** (§5.10): a
well-founded definition would be total too and would not *reduce* in the kernel,
and every theorem below that pins down what the kernel reads is a statement
`decide` or `rfl` has to evaluate.  So the parser counts down a `Nat` and
`JErr.outOfFuel` is a **named** refusal (§5.7), never a silent default.

`jfuel` counts every parser frame reading `jemit v` opens, one clause per
parser entry point — an over-count of the fuel actually needed, which is only
the nesting depth, and an over-count is all an upper bound has to be.
`jfuel_le_jemit` then bounds it by twice the byte count, so `jparse` can take
its fuel from the input's own length and **no caller ever guesses**.  A factor
of one would not do: an array pays one frame for `jval` and one for `jarr`, so
`n` nested arrays around a numeral cost `3n+1` frames for `2n+1` bytes.  (For
input the kernel did *not* emit, `jparse_never_runs_out` is the theorem.) -/

mutual
/-- Parser frames `jemit v` costs. -/
def jfuel : JVal → Nat
  | .null => 1
  | .bool _ => 1
  | .num _ => 1
  | .dec _ => 1
  | .str _ => 1
  | .arr xs => 1 + jfuelL xs
  | .obj kvs => 1 + jfuelO kvs
/-- Frames `jemitArr xs` costs, which is also what `jemitTail xs` costs. -/
def jfuelL : List JVal → Nat
  | [] => 1
  | x :: xs => 1 + jfuel x + jfuelL xs
/-- Frames `jemitObj kvs` costs, which is also what `jemitOTail kvs` costs. -/
def jfuelO : List (List Char × JVal) → Nat
  | [] => 1
  | kv :: kvs => 1 + jfuelPair kv + jfuelO kvs
/-- Frames one `"key":value` costs. -/
def jfuelPair : List Char × JVal → Nat
  | (_, v) => 1 + jfuel v
end

theorem one_le_jemitTail (xs : List JVal) : 1 ≤ (jemitTail xs).length := by
  cases xs <;> simp [jemitTail]

theorem one_le_jemitOTail (kvs : List (List Char × JVal)) : 1 ≤ (jemitOTail kvs).length := by
  cases kvs <;> simp [jemitOTail]

/-- A closing `]` costs one byte more after an element than after `[`.  The
`+ 1` is exactly the slack the induction below needs, and losing it is what
makes the naive `≤ 2 * length` invariant fail at the cons case. -/
theorem jemitTail_le_jemitArr (xs : List JVal) :
    (jemitTail xs).length ≤ (jemitArr xs).length + 1 := by
  cases xs <;> simp [jemitArr, jemitTail]

theorem jemitOTail_le_jemitObj (kvs : List (List Char × JVal)) :
    (jemitOTail kvs).length ≤ (jemitObj kvs).length + 1 := by
  cases kvs <;> simp [jemitObj, jemitOTail]

/-- **The fuel is a function of the bytes.**  Twice the emitted length covers
every value, so `jparse` never asks a caller how deep the document is. -/
theorem jfuel_le_jemit (v : JVal) : jfuel v ≤ 2 * (jemit v).length := by
  refine JVal.rec
    (motive_1 := fun v => jfuel v ≤ 2 * (jemit v).length)
    (motive_2 := fun xs => jfuelL xs + 1 ≤ 2 * (jemitTail xs).length)
    (motive_3 := fun kvs => jfuelO kvs + 1 ≤ 2 * (jemitOTail kvs).length)
    (motive_4 := fun p => jfuelPair p ≤ 2 * (jemitPair p).length)
    ?null ?bool ?num ?dec ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair v
  case null => simp [jfuel, jemit]
  case bool => intro b; cases b <;> simp [jfuel, jemit]
  case num =>
    intro n
    have h : jemit (JVal.num n) = digitsOf n := rfl
    have hne : digitsOf n ≠ [] := digitsOf_ne_nil n
    have : 1 ≤ (digitsOf n).length := by
      cases hd : digitsOf n with
      | nil => exact absurd hd hne
      | cons a t => simp
    have hf : jfuel (JVal.num n) = 1 := rfl
    rw [h, hf]; omega
  case dec =>
    intro d
    have hf : jfuel (JVal.dec d) = 1 := rfl
    obtain ⟨c, t, hu, _⟩ := d.val.renderU_ne_nil
    have h : 1 ≤ (jemit (JVal.dec d)).length := by
      show 1 ≤ d.val.render.length
      unfold JDec.render; split <;> simp [hu]
    rw [hf]; omega
  case str =>
    intro s
    have h : (jemit (JVal.str s)).length = (jescape s).length + 2 := by
      show ('"' :: (jescape s ++ ['"'])).length = _
      simp
    have hf : jfuel (JVal.str s) = 1 := rfl
    rw [hf, h]; omega
  case arr =>
    intro xs ih
    have h : (jemit (JVal.arr xs)).length = (jemitArr xs).length + 1 := by
      show ('[' :: jemitArr xs).length = _
      simp
    have hf : jfuel (JVal.arr xs) = 1 + jfuelL xs := rfl
    have ht := jemitTail_le_jemitArr xs
    rw [hf, h]; omega
  case obj =>
    intro kvs ih
    have h : (jemit (JVal.obj kvs)).length = (jemitObj kvs).length + 1 := by
      show ('{' :: jemitObj kvs).length = _
      simp
    have hf : jfuel (JVal.obj kvs) = 1 + jfuelO kvs := rfl
    have ht := jemitOTail_le_jemitObj kvs
    rw [hf, h]; omega
  case lnil => simp [jfuelL, jemitTail]
  case lcons =>
    intro x xs ihx ihxs
    have hf : jfuelL (x :: xs) = 1 + jfuel x + jfuelL xs := rfl
    have hl : (jemitTail (x :: xs)).length = (jemit x).length + (jemitTail xs).length + 1 := by
      show (',' :: (jemit x ++ jemitTail xs)).length = _
      simp
    rw [hf, hl]; omega
  case onil => simp [jfuelO, jemitOTail]
  case ocons =>
    intro kv kvs ihkv ihkvs
    have hf : jfuelO (kv :: kvs) = 1 + jfuelPair kv + jfuelO kvs := rfl
    have hl : (jemitOTail (kv :: kvs)).length
        = (jemitPair kv).length + (jemitOTail kvs).length + 1 := by
      show (',' :: (jemitPair kv ++ jemitOTail kvs)).length = _
      simp
    rw [hf, hl]; omega
  case pair =>
    intro k v ihv
    have hf : jfuelPair (k, v) = 1 + jfuel v := rfl
    have hl : (jemitPair (k, v)).length = (jescape k).length + (jemit v).length + 3 := by
      show ('"' :: (jescape k ++ '"' :: ':' :: jemit v)).length = _
      simp; omega
    rw [hf, hl]; omega

/-- **A one-key object** — the shape of every `err` response, of the `ok`
wrapper and of its `docs` field (J5).  The key is spelled as a `String` at the
call site and crosses as the `List Char` a `JVal` carries. -/
def jone (k : String) (v : JVal) : JVal := .obj [(k.toList, v)]

/-! ## J4 — the parser

Six entry points, one per position a JSON document can be in, all consuming the
same structurally-decreasing fuel.  Every branch is an `if` on a single
character or a match on a list, never an overlapping pattern: that is what keeps
`rfl` able to step through the definition, and the helper equations below are
all `rfl` because of it.

Whitespace is skipped **between tokens**, wherever a host may put it: before a
value, before `]`/`}`/`,`/`:`, and after the top-level value.  It is never
skipped inside a string, where RFC 8259 forbids raw control bytes and
`junescape` refuses them by name. -/

/-- Why `jparse` refused.  §5.7: every diagnostic is named, including the fuel
one — running out is a refusal the caller can read, not a silent default. -/
inductive JErr
  /-- The fuel ran out.  `jparse` derives its own fuel, so this is reachable
  only through `jparseWith` with a fuel the caller chose —
  `jparse_never_runs_out`. -/
  | outOfFuel
  /-- End of input where a value was expected. -/
  | emptyInput
  /-- A byte that starts no value — `+` included, which RFC 8259 does not allow
  in front of a numeral.  (`-` starts a `dec` since stage 5 A2.) -/
  | notAValue (c : Char)
  /-- Digits that `readNat` would not fold.  Unreachable through `jval`, which
  only calls `jparseNat` on a digit (`jparseNat_some_of_digit`); kept so the
  case is named rather than a default. -/
  | badNumber
  /-- A string with no closing quote. -/
  | unterminatedString
  /-- The bytes between the quotes did not un-escape; carries J1's reason. -/
  | badEscape (e : JEsc)
  /-- End of input inside an array. -/
  | unterminatedArray
  /-- Something other than `,` or `]` after an array element. -/
  | expectedCommaOrBracket (c : Char)
  /-- End of input inside an object. -/
  | unterminatedObject
  /-- Something other than `,` or `}` after a pair. -/
  | expectedCommaOrBrace (c : Char)
  /-- Something other than `:` after a key. -/
  | expectedColon (c : Char)
  /-- Something other than `"` where a key was expected. -/
  | expectedKey (c : Char)
  /-- A complete value, then a non-whitespace byte. -/
  | trailingGarbage (c : Char)
  /-- `0` followed by another digit (stage 5 A2; README gap 43, closed): RFC 8259
  forbids it and serde_json refuses it. -/
  | leadingZero
  /-- A numeral that stops where a digit must follow: after `-`, `.`, the
  exponent's `e`/`E`, or its sign.  Carries that byte (stage 5 A2). -/
  | missingDigit (c : Char)
deriving DecidableEq, Repr, Inhabited

/-! Core ships no `DecidableEq (Except ε α)`, and this module does **not** add
one: an instance for a core type is an orphan every downstream module would
inherit.  Step 1's house decision (and `Boundary.lean`'s
`parseCmd_rejects_add_title_variants`) stands — every `Except`-valued witness
below is `rfl`, or a tuple of `rfl`s, and every `≠` is refuted through the
constructors' injectivity. -/

/-- RFC 8259's four insignificant bytes. -/
def wsChar (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t'

/-- Drop leading whitespace.  Structural. -/
def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if wsChar c then skipWs cs else c :: cs

theorem skipWs_cons_of_not_ws (c : Char) (t : List Char) (h : wsChar c = false) :
    skipWs (c :: t) = c :: t := by
  simp [skipWs, h]

/-- Find the quote that ends a string, respecting escapes: a `\` consumes the
byte after it, so `\"` does not terminate.  Returns the raw bytes between the
quotes and what follows the closing quote.  Structural — the escape branch
recurses two characters in, still on a proper tail. -/
def jscan : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '"' then some ([], rest)
    else if c = '\\' then
      match rest with
      | [] => none
      | e :: rest' =>
        match jscan rest' with
        | none => none
        | some (s, r) => some ('\\' :: e :: s, r)
    else
      match jscan rest with
      | none => none
      | some (s, r) => some (c :: s, r)

/-- **`jscan`'s runtime twin (J5)** — the scanner recursed once per byte of a
string, like `junescape`.  The accumulator holds the scanned bytes reversed. -/
def jscanTR.go : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | c :: rest, acc =>
    if c = '"' then some (acc.reverse, rest)
    else if c = '\\' then
      match rest with
      | [] => none
      | e :: rest' => jscanTR.go rest' (e :: '\\' :: acc)
    else jscanTR.go rest (c :: acc)

def jscanTR (l : List Char) : Option (List Char × List Char) := jscanTR.go l []

/-- The accumulator invariant, by strong induction on the length (the escape
branch recurses two bytes in). -/
theorem jscanTR_go (n : Nat) : ∀ (l acc : List Char), l.length ≤ n →
    jscanTR.go l acc = (jscan l).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction n with
  | zero =>
    intro l acc h
    cases l with
    | nil => rfl
    | cons c t => simp at h
  | succ n ih =>
    intro l acc h
    cases l with
    | nil => rfl
    | cons c rest =>
      rw [jscanTR.go.eq_def, jscan.eq_def]
      simp only
      by_cases hq : c = '"'
      · simp [hq]
      by_cases hb : c = '\\'
      · simp only [if_neg hq, if_pos hb]
        cases rest with
        | nil => rfl
        | cons e rest' =>
          simp only [List.length_cons] at h
          simp only
          rw [ih rest' _ (by omega)]
          cases hs : jscan rest' with
          | none => rfl
          | some p => simp
      · simp only [List.length_cons] at h
        simp only [if_neg hq, if_neg hb]
        rw [ih rest _ (by omega)]
        cases hs : jscan rest with
        | none => rfl
        | some p => simp

@[csimp] theorem jscan_eq_jscanTR : @jscan = @jscanTR := by
  funext l
  rw [jscanTR, jscanTR_go l.length l [] (Nat.le_refl _)]
  cases jscan l with
  | none => rfl
  | some p => rfl

/-- Read a string body: scan to the closing quote, then un-escape with J1's
`junescape`, whose refusals become `JErr.badEscape`. -/
def jstring (l : List Char) : Except JErr (List Char × List Char) :=
  match jscan l with
  | none => .error .unterminatedString
  | some (s, r) =>
    match junescape s with
    | .error e => .error (.badEscape e)
    | .ok cs => .ok (cs, r)

/-! ### Reading a numeral (stage 5 A2, design §5.1)

APPENDED 2026-09-14 (stage-5 D9 track, step A2).  None of these recurses except
through `jparseNat` and `jfins`, whose per-digit loops run as `jdigitsTR` and
`jfinsTR`.  The integer digits are `jparseNat`'s, so a natural numeral has one
reader. -/

/-- After `.`: at least one digit.  No `.`: no fraction, nothing consumed. -/
def jfrac : List Char → Except JErr (List (Fin 10) × List Char)
  | '.' :: r =>
    match jfins r with
    | ([], _) => .error (.missingDigit '.')
    | (fs, r') => .ok (fs, r')
  | l => .ok ([], l)

/-- The exponent's digits, at least one, after the marker or sign `m`. -/
def jexpDigits (neg : Bool) (m : Char) (l : List Char) :
    Except JErr (Option (Bool × Fin 10 × List (Fin 10)) × List Char) :=
  match jfins l with
  | ([], _) => .error (.missingDigit m)
  | (x :: xs, r) => .ok (some (neg, x, xs), r)

/-- After `e`/`E` (`m`): an optional sign, then the digits. -/
def jexpAfter (m : Char) : List Char →
    Except JErr (Option (Bool × Fin 10 × List (Fin 10)) × List Char)
  | '-' :: r => jexpDigits true '-' r
  | '+' :: r => jexpDigits false '+' r
  | l => jexpDigits false m l

/-- `e`/`E` and an exponent, or no exponent and nothing consumed. -/
def jexp : List Char → Except JErr (Option (Bool × Fin 10 × List (Fin 10)) × List Char)
  | 'e' :: r => jexpAfter 'e' r
  | 'E' :: r => jexpAfter 'E' r
  | l => .ok (none, l)

/-- **A numeral after its sign.**  `neg` says whether a `-` was read.  The integer
digits are `jparseNat`'s, refused with a leading zero; then the fraction and the
exponent.  `badNumber` is unreachable with `neg = false` from `jval`, which calls
this only on a digit (`jparseNat_some_of_digit`). -/
def jreadDec (neg : Bool) (l : List Char) : Except JErr (JDec × List Char) :=
  match jparseNat l with
  | none => .error (if neg then .missingDigit '-' else .badNumber)
  | some (n, r1) =>
    if jleadingZero l then .error .leadingZero
    else
      match jfrac r1 with
      | .error e => .error e
      | .ok (fs, r2) =>
        match jexp r2 with
        | .error e => .error e
        | .ok (ex, r3) => .ok (⟨neg, n, fs, ex⟩, r3)

/-- **The one smart constructor from a read numeral to a value**: a plain numeral
is `num`, anything else `dec`.  So `7` is never `dec` and `jparse` has one answer. -/
def JVal.ofDec (d : JDec) : JVal :=
  if h : d.plain = true then .num d.int else .dec ⟨d, by simpa using h⟩

/-- A numeral as a value: `jval`'s number branch. -/
def jnumber (neg : Bool) (l : List Char) : Except JErr (JVal × List Char) :=
  match jreadDec neg l with
  | .error e => .error e
  | .ok (d, r) => .ok (JVal.ofDec d, r)

mutual
/-- A value, with whatever whitespace precedes it. -/
def jval : Nat → List Char → Except JErr (JVal × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .emptyInput
    | c :: r =>
      if (charDigit c).isSome then jnumber false (c :: r)
      else if c = '-' then jnumber true r
      else if c = '"' then
        match jstring r with
        | .error e => .error e
        | .ok (s, r') => .ok (.str s, r')
      else if c = '[' then
        match jarr f r with
        | .error e => .error e
        | .ok (xs, r') => .ok (.arr xs, r')
      else if c = '{' then
        match jobj f r with
        | .error e => .error e
        | .ok (kvs, r') => .ok (.obj kvs, r')
      else
        match c, r with
        | 'n', 'u' :: 'l' :: 'l' :: r' => .ok (.null, r')
        | 't', 'r' :: 'u' :: 'e' :: r' => .ok (.bool true, r')
        | 'f', 'a' :: 'l' :: 's' :: 'e' :: r' => .ok (.bool false, r')
        | _, _ => .error (.notAValue c)
/-- Just after `[`: zero or more elements, then `]`. -/
def jarr : Nat → List Char → Except JErr (List JVal × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedArray
    | c :: r =>
      if c = ']' then .ok ([], r)
      else
        match jval f (c :: r) with
        | .error e => .error e
        | .ok (x, r') =>
          match jtail f r' with
          | .error e => .error e
          | .ok (xs, r'') => .ok (x :: xs, r'')
/-- Just after an element: `]`, or `,` and at least one more element.  A `,`
followed by `]` is therefore refused — no trailing comma. -/
def jtail : Nat → List Char → Except JErr (List JVal × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedArray
    | c :: r =>
      if c = ']' then .ok ([], r)
      else if c = ',' then
        match jval f r with
        | .error e => .error e
        | .ok (x, r') =>
          match jtail f r' with
          | .error e => .error e
          | .ok (xs, r'') => .ok (x :: xs, r'')
      else .error (.expectedCommaOrBracket c)
/-- Just after `{`: zero or more pairs, then `}`. -/
def jobj : Nat → List Char → Except JErr (List (List Char × JVal) × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedObject
    | c :: r =>
      if c = '}' then .ok ([], r)
      else
        match jpair f (c :: r) with
        | .error e => .error e
        | .ok (kv, r') =>
          match jotail f r' with
          | .error e => .error e
          | .ok (kvs, r'') => .ok (kv :: kvs, r'')
/-- One `"key" : value`.  The key is a string, so a bare or numeric key is
refused by name. -/
def jpair : Nat → List Char → Except JErr ((List Char × JVal) × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedObject
    | c :: r =>
      if c = '"' then
        match jstring r with
        | .error e => .error e
        | .ok (k, r') =>
          match skipWs r' with
          | [] => .error .unterminatedObject
          | c' :: r'' =>
            if c' = ':' then
              match jval f r'' with
              | .error e => .error e
              | .ok (v, r3) => .ok ((k, v), r3)
            else .error (.expectedColon c')
      else .error (.expectedKey c)
/-- Just after a pair: `}`, or `,` and at least one more pair. -/
def jotail : Nat → List Char → Except JErr (List (List Char × JVal) × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedObject
    | c :: r =>
      if c = '}' then .ok ([], r)
      else if c = ',' then
        match jpair f r with
        | .error e => .error e
        | .ok (kv, r') =>
          match jotail f r' with
          | .error e => .error e
          | .ok (kvs, r'') => .ok (kv :: kvs, r'')
      else .error (.expectedCommaOrBrace c)
end

/-! ### The parser's runtime twin (stage 5 A1, gap 44 closed)

APPENDED 2026-09-14 (stage-5 D9 track, step A1).  `jarr`/`jtail` and
`jobj`/`jotail` recursed once per element, not in tail position: 21 500
one-line strings in one array read and 22 000 aborted on a 2 MiB stack.  The
twin block is the same six fuel-structural functions with the per-element loops
(`jtailAcc.go`, `jotailAcc.go`) carrying the elements read so far **reversed** in
an accumulator, so their recursive call is a tail call; the stack grows per
nesting level only.  Depth is not bounded here: a deeply nested document still
costs a frame per level (design P14's depth warning is step B3's).  `jvalAcc` and `jpairAcc` exist only so the
twins call twins: `@[csimp]` rewrites call sites, and `jval`'s compiled body
calls `jarr`.  `jparserAcc` is the one six-conjunct fuel induction, the shape
`jparser_fuel` already has; the six `@[csimp]` theorems read off it.  Every
proof about the parser is still about `jval`…`jotail`. -/

mutual
def jvalAcc : Nat → List Char → Except JErr (JVal × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .emptyInput
    | c :: r =>
      if (charDigit c).isSome then jnumber false (c :: r)
      else if c = '-' then jnumber true r
      else if c = '"' then
        match jstring r with
        | .error e => .error e
        | .ok (s, r') => .ok (.str s, r')
      else if c = '[' then
        match jarrAcc f r with
        | .error e => .error e
        | .ok (xs, r') => .ok (.arr xs, r')
      else if c = '{' then
        match jobjAcc f r with
        | .error e => .error e
        | .ok (kvs, r') => .ok (.obj kvs, r')
      else
        match c, r with
        | 'n', 'u' :: 'l' :: 'l' :: r' => .ok (.null, r')
        | 't', 'r' :: 'u' :: 'e' :: r' => .ok (.bool true, r')
        | 'f', 'a' :: 'l' :: 's' :: 'e' :: r' => .ok (.bool false, r')
        | _, _ => .error (.notAValue c)
def jarrAcc : Nat → List Char → Except JErr (List JVal × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedArray
    | c :: r =>
      if c = ']' then .ok ([], r)
      else
        match jvalAcc f (c :: r) with
        | .error e => .error e
        | .ok (x, r') => jtailAcc.go f r' [x]
def jtailAcc.go : Nat → List Char → List JVal → Except JErr (List JVal × List Char)
  | 0, _, _ => .error .outOfFuel
  | f + 1, l, acc =>
    match skipWs l with
    | [] => .error .unterminatedArray
    | c :: r =>
      if c = ']' then .ok (acc.reverse, r)
      else if c = ',' then
        match jvalAcc f r with
        | .error e => .error e
        | .ok (x, r') => jtailAcc.go f r' (x :: acc)
      else .error (.expectedCommaOrBracket c)
def jobjAcc : Nat → List Char → Except JErr (List (List Char × JVal) × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedObject
    | c :: r =>
      if c = '}' then .ok ([], r)
      else
        match jpairAcc f (c :: r) with
        | .error e => .error e
        | .ok (kv, r') => jotailAcc.go f r' [kv]
def jpairAcc : Nat → List Char → Except JErr ((List Char × JVal) × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .unterminatedObject
    | c :: r =>
      if c = '"' then
        match jstring r with
        | .error e => .error e
        | .ok (k, r') =>
          match skipWs r' with
          | [] => .error .unterminatedObject
          | c' :: r'' =>
            if c' = ':' then
              match jvalAcc f r'' with
              | .error e => .error e
              | .ok (v, r3) => .ok ((k, v), r3)
            else .error (.expectedColon c')
      else .error (.expectedKey c)
def jotailAcc.go : Nat → List Char → List (List Char × JVal) →
    Except JErr (List (List Char × JVal) × List Char)
  | 0, _, _ => .error .outOfFuel
  | f + 1, l, acc =>
    match skipWs l with
    | [] => .error .unterminatedObject
    | c :: r =>
      if c = '}' then .ok (acc.reverse, r)
      else if c = ',' then
        match jpairAcc f r with
        | .error e => .error e
        | .ok (kv, r') => jotailAcc.go f r' (kv :: acc)
      else .error (.expectedCommaOrBrace c)
end

def jtailAcc (f : Nat) (l : List Char) : Except JErr (List JVal × List Char) :=
  jtailAcc.go f l []
def jotailAcc (f : Nat) (l : List Char) : Except JErr (List (List Char × JVal) × List Char) :=
  jotailAcc.go f l []

theorem jparserAcc (n : Nat) :
    (∀ l, jvalAcc n l = jval n l) ∧
    (∀ l, jarrAcc n l = jarr n l) ∧
    (∀ l acc, jtailAcc.go n l acc = (jtail n l).map (fun p => (acc.reverse ++ p.1, p.2))) ∧
    (∀ l, jobjAcc n l = jobj n l) ∧
    (∀ l, jpairAcc n l = jpair n l) ∧
    (∀ l acc, jotailAcc.go n l acc = (jotail n l).map (fun p => (acc.reverse ++ p.1, p.2))) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
  | succ f ih =>
    obtain ⟨hv, ha, ht, ho, hp, hot⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      simp only [jvalAcc, jval, ha, ho] <;> rfl
    · intro l
      simp only [jarrAcc, jarr]
      generalize skipWs l = s
      cases s with
      | nil => rfl
      | cons c r =>
        by_cases hc : c = ']'
        · simp only [hc, if_true]
        · simp only [hc, if_false, hv]
          cases jval f (c :: r) with
          | error e => rfl
          | ok p =>
            obtain ⟨x, r'⟩ := p
            simp only [ht]
            cases jtail f r' with
            | error e => rfl
            | ok q => rfl
    · intro l acc
      simp only [jtailAcc.go, jtail]
      generalize skipWs l = s
      cases s with
      | nil => rfl
      | cons c r =>
        by_cases hc : c = ']'
        · simp [hc, Except.map]
        · by_cases hk : c = ','
          · simp only [hk, if_true, hv]
            cases jval f r with
            | error e => rfl
            | ok p =>
              obtain ⟨x, r'⟩ := p
              simp only [ht]
              cases jtail f r' with
              | error e => rfl
              | ok q => simp [Except.map]
          · simp only [hc, hk, if_false]; rfl
    · intro l
      simp only [jobjAcc, jobj]
      generalize skipWs l = s
      cases s with
      | nil => rfl
      | cons c r =>
        by_cases hc : c = '}'
        · simp only [hc, if_true]
        · simp only [hc, if_false, hp]
          cases jpair f (c :: r) with
          | error e => rfl
          | ok p =>
            obtain ⟨x, r'⟩ := p
            simp only [hot]
            cases jotail f r' with
            | error e => rfl
            | ok q => rfl
    · intro l
      simp only [jpairAcc, jpair, hv] <;> rfl
    · intro l acc
      simp only [jotailAcc.go, jotail]
      generalize skipWs l = s
      cases s with
      | nil => rfl
      | cons c r =>
        by_cases hc : c = '}'
        · simp [hc, Except.map]
        · by_cases hk : c = ','
          · simp only [hk, if_true, hp]
            cases jpair f r with
            | error e => rfl
            | ok p =>
              obtain ⟨x, r'⟩ := p
              simp only [hot]
              cases jotail f r' with
              | error e => rfl
              | ok q => simp [Except.map]
          · simp only [hc, hk, if_false]; rfl

@[csimp] theorem jval_eq_jvalAcc : @jval = @jvalAcc := by
  funext n l; exact ((jparserAcc n).1 l).symm
@[csimp] theorem jarr_eq_jarrAcc : @jarr = @jarrAcc := by
  funext n l; exact ((jparserAcc n).2.1 l).symm
@[csimp] theorem jtail_eq_jtailAcc : @jtail = @jtailAcc := by
  funext n l
  rw [jtailAcc, (jparserAcc n).2.2.1 l []]
  cases jtail n l <;> rfl
@[csimp] theorem jobj_eq_jobjAcc : @jobj = @jobjAcc := by
  funext n l; exact ((jparserAcc n).2.2.2.1 l).symm
@[csimp] theorem jpair_eq_jpairAcc : @jpair = @jpairAcc := by
  funext n l; exact ((jparserAcc n).2.2.2.2.1 l).symm
@[csimp] theorem jotail_eq_jotailAcc : @jotail = @jotailAcc := by
  funext n l
  rw [jotailAcc, (jparserAcc n).2.2.2.2.2 l []]
  cases jotail n l <;> rfl

/-- A whole document: one value, then nothing but whitespace.  `fuel` is
explicit so the refusal `JErr.outOfFuel` is reachable and testable. -/
def jparseWith (fuel : Nat) (l : List Char) : Except JErr JVal :=
  match jval fuel l with
  | .error e => .error e
  | .ok (v, rest) =>
    match skipWs rest with
    | [] => .ok v
    | c :: _ => .error (.trailingGarbage c)

/-- **The parser a caller uses.**  The fuel is the input's own length doubled,
plus two — derived from the bytes, never guessed; the `+ 2` is what lets the
empty input be refused as `emptyInput` rather than for fuel.  `jfuel_le_jemit`
is why that is enough for anything the kernel emitted, and
`jparse_never_runs_out` why it is enough for any input at all. -/
def jparse (l : List Char) : Except JErr JVal := jparseWith (2 * l.length + 2) l

/-! ### The scanner finds the quote the emitter wrote

`jscan` is the only place the parser has to know about escaping, and
`jscan_jescape` says it stops at exactly the quote `jemit` put there: an escaped
quote inside the content does not end the string.  With `junescape_jescape` from
J1 that gives `jstring_jescape`, which is the whole string case of the round
trip. -/

theorem jscan_cons_plain (c : Char) (x a b : List Char) (hq : c ≠ '"') (hb : c ≠ '\\')
    (h : jscan x = some (a, b)) : jscan (c :: x) = some (c :: a, b) := by
  rw [jscan.eq_def]
  simp [hq, hb, h]

theorem jscan_cons_esc (e : Char) (x a b : List Char) (h : jscan x = some (a, b)) :
    jscan ('\\' :: e :: x) = some ('\\' :: e :: a, b) := by
  rw [jscan.eq_def]
  simp [h]

/-- The two bytes `escOf`'s hex quad can produce are neither a quote nor a
backslash, so the scanner walks straight over them. -/
theorem hexChar_ne_quote_or_backslash : ∀ k < 16, hexChar k ≠ '"' ∧ hexChar k ≠ '\\' := by
  decide

/-- **One character at a time**, exactly as `junescape_escOf` is for J1: the
scan of `escOf c ++ x` is the scan of `x` with `escOf c` put back in front.
Every branch of `escOf` is covered, the `\u00xx` quad included. -/
theorem jscan_escOf (c : Char) (x a b : List Char) (h : jscan x = some (a, b)) :
    jscan (escOf c ++ x) = some (escOf c ++ a, b) := by
  unfold escOf
  by_cases hq : c = '"'
  · subst hq; simpa using jscan_cons_esc '"' x a b h
  by_cases hbs : c = '\\'
  · subst hbs; simp only [if_neg hq]
    simpa using jscan_cons_esc '\\' x a b h
  by_cases hn : c = '\n'
  · subst hn; simp only [if_neg hq, if_neg hbs]
    simpa using jscan_cons_esc 'n' x a b h
  by_cases hr : c = '\r'
  · subst hr; simp only [if_neg hq, if_neg hbs, if_neg hn]
    simpa using jscan_cons_esc 'r' x a b h
  by_cases hc : c.toNat < 32
  · simp only [if_neg hq, if_neg hbs, if_neg hn, if_neg hr, if_pos hc]
    have k1 : c.toNat / 16 < 16 := by omega
    have k2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
    have p1 := hexChar_ne_quote_or_backslash _ k1
    have p2 := hexChar_ne_quote_or_backslash _ k2
    have s2 := jscan_cons_plain (hexChar (c.toNat % 16)) x a b p2.1 p2.2 h
    have s1 := jscan_cons_plain (hexChar (c.toNat / 16)) _ _ _ p1.1 p1.2 s2
    have s0 := jscan_cons_plain '0' _ _ _ (by decide) (by decide) s1
    have s0' := jscan_cons_plain '0' _ _ _ (by decide) (by decide) s0
    simpa using jscan_cons_esc 'u' _ _ _ s0'
  · simp only [if_neg hq, if_neg hbs, if_neg hn, if_neg hr, if_neg hc]
    simpa using jscan_cons_plain c x a b hq hbs h

theorem jscan_jescape (s rest : List Char) :
    jscan (jescape s ++ '"' :: rest) = some (jescape s, rest) := by
  induction s with
  | nil => rw [jescape, List.nil_append, jscan.eq_def]; simp
  | cons c t ih =>
    rw [jescape, List.append_assoc, jscan_escOf c _ _ _ ih]

/-- **The string round trip.**  Whatever bytes the emitter put between two
quotes come back, and the parser resumes at exactly the byte after the closing
quote. -/
theorem jstring_jescape (s rest : List Char) :
    jstring (jescape s ++ '"' :: rest) = .ok (s, rest) := by
  unfold jstring
  rw [jscan_jescape s rest]
  show (match junescape (jescape s) with
        | .error e => Except.error (JErr.badEscape e)
        | .ok cs => Except.ok (cs, rest)) = _
  rw [junescape_jescape s]

/-! ### What a digit is not, and what `jemit` never starts with -/

theorem charDigit_cases (c : Char) (h : (charDigit c).isSome = true) :
    c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨
    c = '5' ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9' := by
  unfold charDigit at h
  split at h <;> simp_all

theorem charDigit_not_ws (c : Char) (h : (charDigit c).isSome = true) : wsChar c = false := by
  rcases charDigit_cases c h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem charDigit_ne_closers (c : Char) (h : (charDigit c).isSome = true) :
    c ≠ ']' ∧ c ≠ '}' := by
  rcases charDigit_cases c h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by decide, by decide⟩

/-- **The emitter never starts a value with whitespace or a closer.**  That is
what lets `jarr`/`jobj` tell "the array is empty" from "an element follows"
without looking any further than one byte. -/
theorem jemit_head (v : JVal) :
    ∃ c t, jemit v = c :: t ∧ wsChar c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases v with
  | null => exact ⟨'n', ['u','l','l'], rfl, by decide, by decide, by decide⟩
  | bool b =>
    cases b with
    | false => exact ⟨'f', ['a','l','s','e'], rfl, by decide, by decide, by decide⟩
    | true => exact ⟨'t', ['r','u','e'], rfl, by decide, by decide, by decide⟩
  | num n =>
    cases hd : digitsOf n with
    | nil => exact absurd hd (digitsOf_ne_nil n)
    | cons c t =>
      have hc : (charDigit c).isSome = true :=
        digitsOf_all_digits n c (by rw [hd]; simp)
      exact ⟨c, t, hd, charDigit_not_ws c hc,
             (charDigit_ne_closers c hc).1, (charDigit_ne_closers c hc).2⟩
  | dec d =>
    obtain ⟨c, t, hu, hc⟩ := d.val.renderU_ne_nil
    show ∃ c t, d.val.render = c :: t ∧ wsChar c = false ∧ c ≠ ']' ∧ c ≠ '}'
    unfold JDec.render
    split
    · exact ⟨'-', _, rfl, by decide, by decide, by decide⟩
    · exact ⟨c, t, hu, charDigit_not_ws c hc,
             (charDigit_ne_closers c hc).1, (charDigit_ne_closers c hc).2⟩
  | str s => exact ⟨'"', jescape s ++ ['"'], rfl, by decide, by decide, by decide⟩
  | arr xs => exact ⟨'[', jemitArr xs, rfl, by decide, by decide, by decide⟩
  | obj kvs => exact ⟨'{', jemitObj kvs, rfl, by decide, by decide, by decide⟩

/-- A numeral inside a document is always followed by `]`, `}` or `,` — never by
another digit.  This is the hypothesis `jparseNat_jrenderNat` needs, discharged
at every site rather than assumed. -/
theorem numEnd_jemitTail (xs : List JVal) (rest : List Char) :
    numEnd (jemitTail xs ++ rest) = true := by
  cases xs <;> rfl

theorem numEnd_jemitOTail (kvs : List (List Char × JVal)) (rest : List Char) :
    numEnd (jemitOTail kvs ++ rest) = true := by
  cases kvs <;> rfl

theorem notDigitStart_jemitTail (xs : List JVal) (rest : List Char) :
    notDigitStart (jemitTail xs ++ rest) = true := by
  cases xs <;> rfl

theorem notDigitStart_jemitOTail (kvs : List (List Char × JVal)) (rest : List Char) :
    notDigitStart (jemitOTail kvs ++ rest) = true := by
  cases kvs <;> rfl

/-! ### The parser's equations at the shapes the emitter produces

Each of these is one step of `jval`/`jarr`/`jtail`/`jobj`/`jpair`/`jotail` at a
head byte the emitter can write.  They exist so the round-trip proof is a chain
of rewrites and not eleven re-derivations of the same case split. -/

theorem jval_null (f : Nat) (r : List Char) :
    jval (f + 1) ('n' :: 'u' :: 'l' :: 'l' :: r) = .ok (.null, r) := rfl

theorem jval_true (f : Nat) (r : List Char) :
    jval (f + 1) ('t' :: 'r' :: 'u' :: 'e' :: r) = .ok (.bool true, r) := rfl

theorem jval_false (f : Nat) (r : List Char) :
    jval (f + 1) ('f' :: 'a' :: 'l' :: 's' :: 'e' :: r) = .ok (.bool false, r) := rfl

theorem jval_string (f : Nat) (x : List Char) :
    jval (f + 1) ('"' :: x) =
      (match jstring x with
       | .error e => .error e
       | .ok (s, r) => .ok (JVal.str s, r)) := rfl

theorem jval_lbracket (f : Nat) (x : List Char) :
    jval (f + 1) ('[' :: x) =
      (match jarr f x with
       | .error e => .error e
       | .ok (xs, r) => .ok (JVal.arr xs, r)) := rfl

theorem jval_lbrace (f : Nat) (x : List Char) :
    jval (f + 1) ('{' :: x) =
      (match jobj f x with
       | .error e => .error e
       | .ok (kvs, r) => .ok (JVal.obj kvs, r)) := rfl

/-- A digit starts a numeral with no sign.  (Stage 5 A2 restated this equation:
until then the branch read a `Nat` with `jparseNat` and nothing else.) -/
theorem jval_digit (f : Nat) (c : Char) (r : List Char) (h : (charDigit c).isSome = true) :
    jval (f + 1) (c :: r) = jnumber false (c :: r) := by
  simp only [jval, skipWs_cons_of_not_ws c r (charDigit_not_ws c h), h, if_true]

/-- A `-` starts a negative numeral (stage 5 A2). -/
theorem jval_minus (f : Nat) (r : List Char) : jval (f + 1) ('-' :: r) = jnumber true r := rfl

/-! ### The numeral round trip (stage 5 A2)

`jreadDec` reads back what `JDec.render` wrote, and stops exactly where the
numeral ends, whenever what follows satisfies `numEnd`.  Every step is a rewrite
by a J2 lemma; nothing is evaluated. -/

theorem notDigitStart_renderExp (ex : Option (Bool × Fin 10 × List (Fin 10))) (rest : List Char)
    (h : numEnd rest = true) : notDigitStart (JDec.renderExp ex ++ rest) = true := by
  rcases ex with _ | ⟨b, x, xs⟩
  · exact notDigitStart_of_numEnd rest h
  · cases b <;> rfl

theorem notDigitStart_renderFrac (fs : List (Fin 10)) (ex : Option (Bool × Fin 10 × List (Fin 10)))
    (rest : List Char) (h : numEnd rest = true) :
    notDigitStart (JDec.renderFrac fs ++ (JDec.renderExp ex ++ rest)) = true := by
  cases fs with
  | nil => exact notDigitStart_renderExp ex rest h
  | cons _ _ => rfl

theorem jexpAfter_digit (m c : Char) (t : List Char) (hc : (charDigit c).isSome = true) :
    jexpAfter m (c :: t) = jexpDigits false m (c :: t) := by
  rcases charDigit_cases c hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem jexp_renderExp (ex : Option (Bool × Fin 10 × List (Fin 10))) (rest : List Char)
    (h : numEnd rest = true) : jexp (JDec.renderExp ex ++ rest) = .ok (ex, rest) := by
  rcases ex with _ | ⟨b, x, xs⟩
  · cases rest with
    | nil => rfl
    | cons c t =>
      simp only [numEnd, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨_, _⟩, he⟩, hE⟩ := h
      show jexp (c :: t) = _
      unfold jexp
      split
      · next heq => simp only [List.cons.injEq] at heq; exact absurd heq.1 he
      · next heq => simp only [List.cons.injEq] at heq; exact absurd heq.1 hE
      · rfl
  · have hd : notDigitStart rest = true := notDigitStart_of_numEnd rest h
    cases b with
    | false =>
      show jexpAfter 'e' (finChar x :: (xs.map finChar ++ rest)) = _
      rw [jexpAfter_digit 'e' _ _ (finChar_is_digit x)]
      unfold jexpDigits
      have := jfins_append (x :: xs) rest hd
      simp only [List.map_cons, List.cons_append] at this
      rw [this]
    | true =>
      show jexpDigits true '-' ((x :: xs).map finChar ++ rest) = _
      unfold jexpDigits
      rw [jfins_append (x :: xs) rest hd]

theorem jfrac_renderFrac (fs : List (Fin 10)) (ex : Option (Bool × Fin 10 × List (Fin 10)))
    (rest : List Char) (h : numEnd rest = true) :
    jfrac (JDec.renderFrac fs ++ (JDec.renderExp ex ++ rest)) = .ok (fs, JDec.renderExp ex ++ rest) := by
  cases fs with
  | cons f fs =>
    show jfrac ('.' :: ((f :: fs).map finChar ++ (JDec.renderExp ex ++ rest))) = _
    unfold jfrac
    simp only [jfins_append (f :: fs) _ (notDigitStart_renderExp ex rest h)]
  | nil =>
    rcases ex with _ | ⟨b, x, xs⟩
    · cases rest with
      | nil => rfl
      | cons c t =>
        simp only [numEnd, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        obtain ⟨⟨⟨_, hdot⟩, _⟩, _⟩ := h
        show jfrac (c :: t) = _
        unfold jfrac
        split
        · next heq => simp only [List.cons.injEq] at heq; exact absurd heq.1 hdot
        · rfl
    · cases b <;> rfl

/-- **The reader reads the renderer**, after the sign. -/
theorem jreadDec_renderU (d : JDec) (rest : List Char) (h : numEnd rest = true) :
    jreadDec d.neg (d.renderU ++ rest) = .ok (d, rest) := by
  obtain ⟨neg, n, fs, ex⟩ := d
  have hY := notDigitStart_renderFrac fs ex rest h
  have hn : jparseNat (digitsOf n ++ (JDec.renderFrac fs ++ (JDec.renderExp ex ++ rest)))
      = some (n, JDec.renderFrac fs ++ (JDec.renderExp ex ++ rest)) :=
    jparseNat_jrenderNat n _ hY
  simp only [JDec.renderU, List.append_assoc]
  unfold jreadDec
  rw [hn]
  simp only [jleadingZero_digitsOf n _ hY, Bool.false_eq_true, if_false]
  rw [jfrac_renderFrac fs ex rest h]
  simp only []
  rw [jexp_renderExp ex rest h]

/-- **`jval` reads every numeral the kernel writes** back to `JVal.ofDec` of it. -/
theorem jval_render (d : JDec) (g : Nat) (rest : List Char) (h : numEnd rest = true) :
    jval (g + 1) (d.render ++ rest) = .ok (JVal.ofDec d, rest) := by
  have hr := jreadDec_renderU d rest h
  unfold JDec.render
  cases hn : d.neg
  · rw [hn] at hr
    simp only [Bool.false_eq_true, if_false]
    obtain ⟨c, t, hu, hc⟩ := d.renderU_ne_nil
    rw [hu, List.cons_append, jval_digit g c _ hc, ← List.cons_append, ← hu]
    unfold jnumber
    rw [hr]
  · rw [hn] at hr
    simp only [if_true]
    rw [List.cons_append, jval_minus]
    unfold jnumber
    rw [hr]

theorem JVal.ofDec_plain (n : Nat) : JVal.ofDec ⟨false, n, [], none⟩ = .num n := rfl

theorem JVal.ofDec_dec (d : { d : JDec // d.plain = false }) : JVal.ofDec d.val = .dec d := by
  unfold JVal.ofDec
  rw [dif_neg (by simp [d.property])]

theorem jemit_num_is_render (n : Nat) : jemit (.num n) = JDec.render ⟨false, n, [], none⟩ := by
  simp [jemit, JDec.render, JDec.renderU, JDec.renderFrac, JDec.renderExp]

theorem jarr_empty (f : Nat) (r : List Char) : jarr (f + 1) (']' :: r) = .ok ([], r) := rfl

theorem jarr_value (f : Nat) (c : Char) (t : List Char) (hw : wsChar c = false) (hb : c ≠ ']') :
    jarr (f + 1) (c :: t) =
      (match jval f (c :: t) with
       | .error e => .error e
       | .ok (x, r) =>
         match jtail f r with
         | .error e => .error e
         | .ok (xs, r') => .ok (x :: xs, r')) := by
  simp only [jarr, skipWs_cons_of_not_ws c t hw, if_neg hb]

/-- The same step, but with the head byte supplied by `jemit_head` rather than
by the caller. -/
theorem jarr_of_jemit (f : Nat) (x : JVal) (Y : List Char) :
    jarr (f + 1) (jemit x ++ Y) =
      (match jval f (jemit x ++ Y) with
       | .error e => .error e
       | .ok (y, r) =>
         match jtail f r with
         | .error e => .error e
         | .ok (ys, r') => .ok (y :: ys, r')) := by
  obtain ⟨c, t, hct, hw, hb, _⟩ := jemit_head x
  rw [hct, List.cons_append]
  exact jarr_value f c (t ++ Y) hw hb

theorem jtail_end (f : Nat) (r : List Char) : jtail (f + 1) (']' :: r) = .ok ([], r) := rfl

theorem jtail_comma (f : Nat) (r : List Char) :
    jtail (f + 1) (',' :: r) =
      (match jval f r with
       | .error e => .error e
       | .ok (x, r') =>
         match jtail f r' with
         | .error e => .error e
         | .ok (xs, r'') => .ok (x :: xs, r'')) := rfl

theorem jobj_empty (f : Nat) (r : List Char) : jobj (f + 1) ('}' :: r) = .ok ([], r) := rfl

theorem jobj_pair (f : Nat) (c : Char) (t : List Char) (hw : wsChar c = false) (hb : c ≠ '}') :
    jobj (f + 1) (c :: t) =
      (match jpair f (c :: t) with
       | .error e => .error e
       | .ok (kv, r) =>
         match jotail f r with
         | .error e => .error e
         | .ok (kvs, r') => .ok (kv :: kvs, r')) := by
  simp only [jobj, skipWs_cons_of_not_ws c t hw, if_neg hb]

theorem jobj_of_jemitPair (f : Nat) (kv : List Char × JVal) (Y : List Char) :
    jobj (f + 1) (jemitPair kv ++ Y) =
      (match jpair f (jemitPair kv ++ Y) with
       | .error e => .error e
       | .ok (p, r) =>
         match jotail f r with
         | .error e => .error e
         | .ok (kvs, r') => .ok (p :: kvs, r')) := by
  obtain ⟨k, v⟩ := kv
  show jobj (f + 1) (('"' :: (jescape k ++ '"' :: ':' :: jemit v)) ++ Y) = _
  rw [List.cons_append]
  exact jobj_pair f '"' _ (by decide) (by decide)

theorem jotail_end (f : Nat) (r : List Char) : jotail (f + 1) ('}' :: r) = .ok ([], r) := rfl

theorem jotail_comma (f : Nat) (r : List Char) :
    jotail (f + 1) (',' :: r) =
      (match jpair f r with
       | .error e => .error e
       | .ok (kv, r') =>
         match jotail f r' with
         | .error e => .error e
         | .ok (kvs, r'') => .ok (kv :: kvs, r'')) := rfl

theorem jpair_key (f : Nat) (x : List Char) :
    jpair (f + 1) ('"' :: x) =
      (match jstring x with
       | .error e => .error e
       | .ok (k, r) =>
         match skipWs r with
         | [] => .error .unterminatedObject
         | c' :: r'' =>
           if c' = ':' then
             match jval f r'' with
             | .error e => .error e
             | .ok (v, r3) => .ok ((k, v), r3)
           else .error (.expectedColon c')) := rfl

/-! ### The theorem

`jval_jemit` is the induction; `jparse_jemit` is the statement a caller reads.

The eliminator is the same four-motive `JVal.rec` J0 rehearsed on `jbeq_sound`,
and the two list motives are **conjunctions**, one component per parser entry
point: what follows `[` and what follows an element are different functions, and
the emitter has a function for each.  `motive_1` and `motive_4` carry the
`numEnd` hypothesis because a numeral is the one value whose end is decided by
the bytes after it; the list motives do not need it, because a list element is
always followed by `,` or a closer.  (Until stage 5 A2 the hypothesis was
`notDigitStart`, which a fraction or an exponent defeats:
`the_jval_jemit_fraction_guard_bites`.)

**No side condition, and in particular none about duplicate keys.**  A `JVal`
object is an ordered assoc list (J0), so `{"a":1,"a":2}` is a value the kernel
can build, emit and read back unchanged — see
`the_round_trip_survives_duplicate_keys`.  The hazard a `Std.TreeMap`-backed
object would have created here does not exist. -/

theorem jval_jemit (v : JVal) : ∀ (f : Nat) (rest : List Char),
    jfuel v ≤ f → numEnd rest = true →
    jval f (jemit v ++ rest) = .ok (v, rest) := by
  refine JVal.rec
    (motive_1 := fun v => ∀ f rest, jfuel v ≤ f → numEnd rest = true →
      jval f (jemit v ++ rest) = .ok (v, rest))
    (motive_2 := fun xs =>
      (∀ f rest, jfuelL xs ≤ f → jarr f (jemitArr xs ++ rest) = .ok (xs, rest)) ∧
      (∀ f rest, jfuelL xs ≤ f → jtail f (jemitTail xs ++ rest) = .ok (xs, rest)))
    (motive_3 := fun kvs =>
      (∀ f rest, jfuelO kvs ≤ f → jobj f (jemitObj kvs ++ rest) = .ok (kvs, rest)) ∧
      (∀ f rest, jfuelO kvs ≤ f → jotail f (jemitOTail kvs ++ rest) = .ok (kvs, rest)))
    (motive_4 := fun p => ∀ f rest, jfuelPair p ≤ f → numEnd rest = true →
      jpair f (jemitPair p ++ rest) = .ok (p, rest))
    ?null ?bool ?num ?dec ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair v
  case null =>
    intro f rest hf _
    cases f with
    | zero => have h : jfuel JVal.null = 1 := rfl; omega
    | succ g => exact jval_null g rest
  case bool =>
    intro b f rest hf _
    cases f with
    | zero => have h : jfuel (JVal.bool b) = 1 := rfl; omega
    | succ g =>
      cases b with
      | false => exact jval_false g rest
      | true => exact jval_true g rest
  case num =>
    intro n f rest hf hr
    cases f with
    | zero => have h : jfuel (JVal.num n) = 1 := rfl; omega
    | succ g =>
      rw [jemit_num_is_render, jval_render _ g rest hr, JVal.ofDec_plain]
  case dec =>
    intro d f rest hf hr
    cases f with
    | zero => have h : jfuel (JVal.dec d) = 1 := rfl; omega
    | succ g =>
      show jval (g + 1) (d.val.render ++ rest) = _
      rw [jval_render _ g rest hr, JVal.ofDec_dec]
  case str =>
    intro s f rest hf _
    cases f with
    | zero => have h : jfuel (JVal.str s) = 1 := rfl; omega
    | succ g =>
      show jval (g + 1) (('"' :: (jescape s ++ ['"'])) ++ rest) = _
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [jval_string, jstring_jescape s rest]
  case arr =>
    intro xs ih f rest hf _
    have he : jfuel (JVal.arr xs) = 1 + jfuelL xs := rfl
    cases f with
    | zero => omega
    | succ g =>
      have h1 : jfuelL xs ≤ g := by omega
      show jval (g + 1) (('[' :: jemitArr xs) ++ rest) = _
      rw [List.cons_append, jval_lbracket, ih.1 g rest h1]
  case obj =>
    intro kvs ih f rest hf _
    have he : jfuel (JVal.obj kvs) = 1 + jfuelO kvs := rfl
    cases f with
    | zero => omega
    | succ g =>
      have h1 : jfuelO kvs ≤ g := by omega
      show jval (g + 1) (('{' :: jemitObj kvs) ++ rest) = _
      rw [List.cons_append, jval_lbrace, ih.1 g rest h1]
  case lnil =>
    have he : jfuelL ([] : List JVal) = 1 := rfl
    constructor
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g => exact jarr_empty g rest
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g => exact jtail_end g rest
  case lcons =>
    intro x xs ihx ihxs
    have he : jfuelL (x :: xs) = 1 + jfuel x + jfuelL xs := rfl
    constructor
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g =>
        have h1 : jfuel x ≤ g := by omega
        have h2 : jfuelL xs ≤ g := by omega
        show jarr (g + 1) ((jemit x ++ jemitTail xs) ++ rest) = _
        rw [List.append_assoc, jarr_of_jemit]
        simp only [ihx g (jemitTail xs ++ rest) h1 (numEnd_jemitTail xs rest),
                   ihxs.2 g rest h2]
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g =>
        have h1 : jfuel x ≤ g := by omega
        have h2 : jfuelL xs ≤ g := by omega
        show jtail (g + 1) ((',' :: (jemit x ++ jemitTail xs)) ++ rest) = _
        rw [List.cons_append, jtail_comma, List.append_assoc]
        simp only [ihx g (jemitTail xs ++ rest) h1 (numEnd_jemitTail xs rest),
                   ihxs.2 g rest h2]
  case onil =>
    have he : jfuelO ([] : List (List Char × JVal)) = 1 := rfl
    constructor
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g => exact jobj_empty g rest
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g => exact jotail_end g rest
  case ocons =>
    intro kv kvs ihkv ihkvs
    have he : jfuelO (kv :: kvs) = 1 + jfuelPair kv + jfuelO kvs := rfl
    constructor
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g =>
        have h1 : jfuelPair kv ≤ g := by omega
        have h2 : jfuelO kvs ≤ g := by omega
        show jobj (g + 1) ((jemitPair kv ++ jemitOTail kvs) ++ rest) = _
        rw [List.append_assoc, jobj_of_jemitPair]
        simp only [ihkv g (jemitOTail kvs ++ rest) h1 (numEnd_jemitOTail kvs rest),
                   ihkvs.2 g rest h2]
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g =>
        have h1 : jfuelPair kv ≤ g := by omega
        have h2 : jfuelO kvs ≤ g := by omega
        show jotail (g + 1) ((',' :: (jemitPair kv ++ jemitOTail kvs)) ++ rest) = _
        rw [List.cons_append, jotail_comma, List.append_assoc]
        simp only [ihkv g (jemitOTail kvs ++ rest) h1 (numEnd_jemitOTail kvs rest),
                   ihkvs.2 g rest h2]
  case pair =>
    intro k v ihv f rest hf hr
    have he : jfuelPair (k, v) = 1 + jfuel v := rfl
    cases f with
    | zero => omega
    | succ g =>
      have h1 : jfuel v ≤ g := by omega
      show jpair (g + 1) (('"' :: (jescape k ++ '"' :: ':' :: jemit v)) ++ rest) = _
      simp only [List.cons_append, List.append_assoc]
      rw [jpair_key, jstring_jescape k (':' :: (jemit v ++ rest))]
      show (match jval g (jemit v ++ rest) with
            | .error e => Except.error e
            | .ok (v', r3) => .ok ((k, v'), r3)) = _
      rw [ihv g rest h1 hr]

/-- **The payload of the whole route: `jparse ∘ jemit = id` on `JVal`.**
Unconditional — every value the kernel can build survives being written and read
back, with no fragment restriction and no side condition.  This is the theorem
`Lean.Json`'s `partial def`s make unstatable (README "Gap 39 REPRICED"), and it
is what J5 will need before any of these bytes reach the wire. -/
theorem jparse_jemit (v : JVal) : jparse (jemit v) = .ok v := by
  have hb := jfuel_le_jemit v
  have h : jval (2 * (jemit v).length + 2) (jemit v ++ []) = .ok (v, []) :=
    jval_jemit v _ [] (by omega) rfl
  rw [List.append_nil] at h
  show jparseWith (2 * (jemit v).length + 2) (jemit v) = _
  unfold jparseWith
  rw [h]
  rfl

/-! ### The derived fuel is enough for every input, not only for emitted bytes

`jfuel_le_jemit` covers what the kernel writes; J5 will hand `jparse` what the
**host** writes, which is not a `jemit` image (whitespace, `\t`, either-case
hex).  `jparse_never_runs_out` closes that: for **every** `List Char`, the fuel
`jparse` derives from the input's length is enough, so `JErr.outOfFuel` is a
refusal of `jparseWith` alone and never of `jparse`.

The argument is two inductions on the fuel over all six entry points.  The
first (`jparser_consumes`) says every successful frame consumes at least one
byte, at any fuel.  The second (`jparser_fuel`) says a frame handed at least
twice its input's length in fuel (plus one or two, by entry point) never runs
out, because every recursive call is on a strictly shorter suffix and costs one
unit.  Nothing here evaluates the parser on bytes; every step is symbolic. -/

theorem skipWs_length_le : ∀ l : List Char, (skipWs l).length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    rw [skipWs.eq_2]
    split
    · exact Nat.le_succ_of_le (skipWs_length_le cs)
    · exact Nat.le_refl _

/-- The scanner consumes at least the closing quote.  By induction on a length
bound, because the escape branch recurses two bytes in. -/
theorem jscan_length (n : Nat) : ∀ (l s r : List Char), l.length ≤ n →
    jscan l = some (s, r) → r.length < l.length := by
  induction n with
  | zero =>
    intro l s r hl h
    cases l with
    | nil => simp [jscan] at h
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l s r hl h
    match l with
    | [] => simp [jscan] at h
    | c :: rest =>
      rw [jscan.eq_def] at h
      simp only at h
      by_cases hq : c = '"'
      · rw [if_pos hq] at h
        cases h
        simp
      · rw [if_neg hq] at h
        by_cases hb : c = '\\'
        · rw [if_pos hb] at h
          match rest with
          | [] => simp at h
          | e :: rest' =>
            simp only at h
            cases hj : jscan rest' with
            | none => rw [hj] at h; simp at h
            | some p =>
              obtain ⟨s', r'⟩ := p
              rw [hj] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              have := ih rest' s' r' (by simp at hl; omega) hj
              simp; omega
        · rw [if_neg hb] at h
          cases hj : jscan rest with
          | none => rw [hj] at h; simp at h
          | some p =>
            obtain ⟨s', r'⟩ := p
            rw [hj] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have := ih rest s' r' (by simp at hl; omega) hj
            simp; omega

theorem jstring_length (l s r : List Char) (h : jstring l = .ok (s, r)) :
    r.length < l.length := by
  unfold jstring at h
  cases hj : jscan l with
  | none => rw [hj] at h; cases h
  | some p =>
    obtain ⟨s', r'⟩ := p
    rw [hj] at h
    simp only at h
    cases hu : junescape s' with
    | error e => rw [hu] at h; cases h
    | ok cs =>
      rw [hu] at h
      cases h
      exact jscan_length l.length l s' r (Nat.le_refl _) hj

/-- A string's refusals are its own — never the fuel one. -/
theorem jstring_ne_outOfFuel (l : List Char) : jstring l ≠ .error .outOfFuel := by
  unfold jstring
  split
  · nofun
  · split <;> nofun

theorem jdigits_length : ∀ l : List Char, (jdigits l).2.length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold jdigits
    split
    · exact Nat.le_succ_of_le (jdigits_length cs)
    · exact Nat.le_refl _

theorem jparseNat_length (c : Char) (r r' : List Char) (n : Nat)
    (hc : (charDigit c).isSome = true) (h : jparseNat (c :: r) = some (n, r')) :
    r'.length < (c :: r).length := by
  unfold jparseNat at h
  have hd : jdigits (c :: r) = (c :: (jdigits r).1, (jdigits r).2) := by
    rw [jdigits.eq_def]; simp [hc]
  rw [hd] at h
  simp only at h
  cases hn : readNat (c :: (jdigits r).1) with
  | none => rw [hn] at h; cases h
  | some m =>
    rw [hn] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have := jdigits_length r
    simp; omega

theorem jdigits_fst_digits : ∀ l : List Char, ∀ d ∈ (jdigits l).1, (charDigit d).isSome = true
  | [] => by simp [jdigits]
  | c :: cs => by
    unfold jdigits
    split
    · next hc =>
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hc
      · exact jdigits_fst_digits cs d hd
    · simp

/-- **`JErr.badNumber` is unreachable through `jval`**, which calls `jparseNat`
only on a digit: a digit always starts a numeral `readNat` folds. -/
theorem jparseNat_some_of_digit (c : Char) (r : List Char) (hc : (charDigit c).isSome = true) :
    (jparseNat (c :: r)).isSome = true := by
  unfold jparseNat
  have hd : jdigits (c :: r) = (c :: (jdigits r).1, (jdigits r).2) := by
    rw [jdigits.eq_def]; simp [hc]
  rw [hd]
  simp only
  have hall : ∀ d ∈ c :: (jdigits r).1, (charDigit d).isSome = true := by
    intro d hd'
    simp only [List.mem_cons] at hd'
    rcases hd' with rfl | hd'
    · exact hc
    · exact jdigits_fst_digits r d hd'
  have : readNat (c :: (jdigits r).1) = some ((c :: (jdigits r).1).foldl natStep 0) := by
    unfold readNat
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
    exact readNatAux_of_digits 0 _ hall
  rw [this]
  rfl

/-! #### A numeral consumes a byte, and never refuses for fuel (stage 5 A2) -/

theorem jdigits_split : ∀ l : List Char, (jdigits l).1 ++ (jdigits l).2 = l
  | [] => rfl
  | c :: cs => by
    unfold jdigits
    split
    · simp [jdigits_split cs]
    · rfl

theorem jfins_length : ∀ l : List Char, (jfins l).2.length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    unfold jfins
    split
    · exact Nat.le_succ_of_le (jfins_length cs)
    · exact Nat.le_refl _

theorem jparseNat_consumes (l r : List Char) (n : Nat) (h : jparseNat l = some (n, r)) :
    r.length < l.length := by
  unfold jparseNat at h
  have hs := jdigits_split l
  revert hs h
  generalize jdigits l = p
  obtain ⟨ds, rest⟩ := p
  intro h hs
  cases ds with
  | nil => cases h
  | cons d ds =>
    simp only at h
    cases hn : readNat (d :: ds) with
    | none => rw [hn] at h; cases h
    | some m =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rw [← hs]; simp; omega

theorem jfrac_length (l r : List Char) (fs : List (Fin 10)) (h : jfrac l = .ok (fs, r)) :
    r.length ≤ l.length := by
  unfold jfrac at h
  split at h
  · next r0 =>
    have := jfins_length r0
    revert this h
    generalize jfins r0 = p
    obtain ⟨fs', r'⟩ := p
    intro h hl
    cases fs' with
    | nil => cases h
    | cons _ _ =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp at hl ⊢; omega
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact Nat.le_refl _

theorem jexpDigits_length (neg : Bool) (m : Char) (l r : List Char)
    (ex : Option (Bool × Fin 10 × List (Fin 10))) (h : jexpDigits neg m l = .ok (ex, r)) :
    r.length ≤ l.length := by
  unfold jexpDigits at h
  have := jfins_length l
  revert this h
  generalize jfins l = p
  obtain ⟨fs', r'⟩ := p
  intro h hl
  cases fs' with
  | nil => cases h
  | cons _ _ =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact hl

theorem jexp_length (l r : List Char) (ex : Option (Bool × Fin 10 × List (Fin 10)))
    (h : jexp l = .ok (ex, r)) : r.length ≤ l.length := by
  unfold jexp at h
  split at h
  · next r0 =>
    unfold jexpAfter at h
    split at h <;> (have := jexpDigits_length _ _ _ _ _ h; simp at this ⊢; omega)
  · next r0 =>
    unfold jexpAfter at h
    split at h <;> (have := jexpDigits_length _ _ _ _ _ h; simp at this ⊢; omega)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact Nat.le_refl _

theorem jreadDec_length (neg : Bool) (l r : List Char) (d : JDec) (h : jreadDec neg l = .ok (d, r)) :
    r.length < l.length := by
  unfold jreadDec at h
  split at h
  · split at h <;> cases h
  · next n r1 hn =>
    have h1 := jparseNat_consumes l r1 n hn
    split at h
    · cases h
    · split at h
      · cases h
      · next fs r2 hf =>
        have h2 := jfrac_length r1 r2 fs hf
        split at h
        · cases h
        · next ex r3 he =>
          have h3 := jexp_length r2 r3 ex he
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          omega

theorem jnumber_length (neg : Bool) (l r : List Char) (v : JVal) (h : jnumber neg l = .ok (v, r)) :
    r.length < l.length := by
  unfold jnumber at h
  split at h
  · cases h
  · next d r' hd =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact jreadDec_length neg l r' d hd

theorem jnumber_ne_outOfFuel (neg : Bool) (l : List Char) : jnumber neg l ≠ .error .outOfFuel := by
  unfold jnumber jreadDec
  split
  · next e he =>
    split at he
    · split at he <;> (simp only [Except.error.injEq] at he; subst he; nofun)
    · split at he
      · simp only [Except.error.injEq] at he; subst he; nofun
      · split at he
        · next e' hf =>
          simp only [Except.error.injEq] at he; subst he
          unfold jfrac at hf
          split at hf
          · split at hf <;> first | (simp only [Except.error.injEq] at hf; subst hf; nofun) | cases hf
          · cases hf
        · split at he
          · next e' _ hx =>
            simp only [Except.error.injEq] at he; subst he
            unfold jexp at hx
            split at hx
            all_goals first
              | cases hx
              | (unfold jexpAfter jexpDigits at hx
                 split at hx <;> split at hx <;>
                   first | (simp only [Except.error.injEq] at hx; subst hx; nofun) | cases hx)
          · cases he
  · nofun

/-! #### Every successful frame consumes a byte -/

theorem jval_consumes_step (f : Nat)
    (harr : ∀ l xs r, jarr f l = .ok (xs, r) → r.length < l.length)
    (hobj : ∀ l kvs r, jobj f l = .ok (kvs, r) → r.length < l.length) :
    ∀ l v r, jval (f + 1) l = .ok (v, r) → r.length < l.length := by
  intro l v r h
  rw [jval.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only at h
    by_cases hd : (charDigit c).isSome = true
    · rw [if_pos hd] at h
      have := jnumber_length false (c :: t) r v h
      omega
    · rw [if_neg hd] at h
      by_cases hm : c = '-'
      · rw [if_pos hm] at h
        have := jnumber_length true t r v h
        simp only [List.length_cons] at hl; omega
      rw [if_neg hm] at h
      by_cases hq : c = '"'
      · rw [if_pos hq] at h
        cases hj : jstring t with
        | error e => rw [hj] at h; cases h
        | ok p =>
          obtain ⟨s, r'⟩ := p
          rw [hj] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have := jstring_length t s r' hj
          simp only [List.length_cons] at hl; omega
      · rw [if_neg hq] at h
        by_cases hb : c = '['
        · rw [if_pos hb] at h
          cases hj : jarr f t with
          | error e => rw [hj] at h; cases h
          | ok p =>
            obtain ⟨xs, r'⟩ := p
            rw [hj] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have := harr t xs r' hj
            simp only [List.length_cons] at hl; omega
        · rw [if_neg hb] at h
          by_cases hc : c = '{'
          · rw [if_pos hc] at h
            cases hj : jobj f t with
            | error e => rw [hj] at h; cases h
            | ok p =>
              obtain ⟨kvs, r'⟩ := p
              rw [hj] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              have := hobj t kvs r' hj
              simp only [List.length_cons] at hl; omega
          · rw [if_neg hc] at h
            split at h <;> first
              | (cases h; done)
              | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
                 obtain ⟨_, rfl⟩ := h
                 simp only [List.length_cons] at hl ⊢; omega)

theorem jarr_consumes_step (f : Nat)
    (hval : ∀ l v r, jval f l = .ok (v, r) → r.length < l.length)
    (htail : ∀ l xs r, jtail f l = .ok (xs, r) → r.length < l.length) :
    ∀ l xs r, jarr (f + 1) l = .ok (xs, r) → r.length < l.length := by
  intro l xs r h
  rw [jarr.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only at h
    by_cases hb : c = ']'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp only [List.length_cons] at hl; omega
    · rw [if_neg hb] at h
      cases hv : jval f (c :: t) with
      | error e => rw [hv] at h; cases h
      | ok p =>
        obtain ⟨x, r1⟩ := p
        rw [hv] at h
        simp only at h
        cases ht : jtail f r1 with
        | error e => rw [ht] at h; cases h
        | ok q =>
          obtain ⟨ys, r2⟩ := q
          rw [ht] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have h1 := hval _ _ _ hv
          have h2 := htail _ _ _ ht
          omega

theorem jtail_consumes_step (f : Nat)
    (hval : ∀ l v r, jval f l = .ok (v, r) → r.length < l.length)
    (htail : ∀ l xs r, jtail f l = .ok (xs, r) → r.length < l.length) :
    ∀ l xs r, jtail (f + 1) l = .ok (xs, r) → r.length < l.length := by
  intro l xs r h
  rw [jtail.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only at h
    by_cases hb : c = ']'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp only [List.length_cons] at hl; omega
    · rw [if_neg hb] at h
      by_cases hc : c = ','
      · rw [if_pos hc] at h
        cases hv : jval f t with
        | error e => rw [hv] at h; cases h
        | ok p =>
          obtain ⟨x, r1⟩ := p
          rw [hv] at h
          simp only at h
          cases ht : jtail f r1 with
          | error e => rw [ht] at h; cases h
          | ok q =>
            obtain ⟨ys, r2⟩ := q
            rw [ht] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have h1 := hval _ _ _ hv
            have h2 := htail _ _ _ ht
            simp only [List.length_cons] at hl; omega
      · rw [if_neg hc] at h; cases h

theorem jobj_consumes_step (f : Nat)
    (hpair : ∀ l kv r, jpair f l = .ok (kv, r) → r.length < l.length)
    (hotail : ∀ l kvs r, jotail f l = .ok (kvs, r) → r.length < l.length) :
    ∀ l kvs r, jobj (f + 1) l = .ok (kvs, r) → r.length < l.length := by
  intro l kvs r h
  rw [jobj.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only at h
    by_cases hb : c = '}'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp only [List.length_cons] at hl; omega
    · rw [if_neg hb] at h
      cases hv : jpair f (c :: t) with
      | error e => rw [hv] at h; cases h
      | ok p =>
        obtain ⟨kv, r1⟩ := p
        rw [hv] at h
        simp only at h
        cases ht : jotail f r1 with
        | error e => rw [ht] at h; cases h
        | ok q =>
          obtain ⟨ys, r2⟩ := q
          rw [ht] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have h1 := hpair _ _ _ hv
          have h2 := hotail _ _ _ ht
          omega

theorem jpair_consumes_step (f : Nat)
    (hval : ∀ l v r, jval f l = .ok (v, r) → r.length < l.length) :
    ∀ l kv r, jpair (f + 1) l = .ok (kv, r) → r.length < l.length := by
  intro l kv r h
  rw [jpair.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only at h
    by_cases hq : c = '"'
    · rw [if_pos hq] at h
      cases hj : jstring t with
      | error e => rw [hj] at h; cases h
      | ok p =>
        obtain ⟨k, r1⟩ := p
        rw [hj] at h
        simp only at h
        have h1 := jstring_length t k r1 hj
        have hl1 := skipWs_length_le r1
        cases hs1 : skipWs r1 with
        | nil => rw [hs1] at h; cases h
        | cons c' r2 =>
          rw [hs1] at h hl1
          simp only at h
          by_cases hc : c' = ':'
          · rw [if_pos hc] at h
            cases hv : jval f r2 with
            | error e => rw [hv] at h; cases h
            | ok q =>
              obtain ⟨v, r3⟩ := q
              rw [hv] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl⟩ := h
              have h2 := hval _ _ _ hv
              simp only [List.length_cons] at hl hl1; omega
          · rw [if_neg hc] at h; cases h
    · rw [if_neg hq] at h; cases h

theorem jotail_consumes_step (f : Nat)
    (hpair : ∀ l kv r, jpair f l = .ok (kv, r) → r.length < l.length)
    (hotail : ∀ l kvs r, jotail f l = .ok (kvs, r) → r.length < l.length) :
    ∀ l kvs r, jotail (f + 1) l = .ok (kvs, r) → r.length < l.length := by
  intro l kvs r h
  rw [jotail.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only at h
    by_cases hb : c = '}'
    · rw [if_pos hb] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      simp only [List.length_cons] at hl; omega
    · rw [if_neg hb] at h
      by_cases hc : c = ','
      · rw [if_pos hc] at h
        cases hv : jpair f t with
        | error e => rw [hv] at h; cases h
        | ok p =>
          obtain ⟨kv, r1⟩ := p
          rw [hv] at h
          simp only at h
          cases ht : jotail f r1 with
          | error e => rw [ht] at h; cases h
          | ok q =>
            obtain ⟨ys, r2⟩ := q
            rw [ht] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have h1 := hpair _ _ _ hv
            have h2 := hotail _ _ _ ht
            simp only [List.length_cons] at hl; omega
      · rw [if_neg hc] at h; cases h

/-- **Every successful parser frame, at any fuel, consumes at least one byte.**
The six components are the six entry points; the induction is on the fuel. -/
theorem jparser_consumes (f : Nat) :
    (∀ l v r, jval f l = .ok (v, r) → r.length < l.length) ∧
    (∀ l xs r, jarr f l = .ok (xs, r) → r.length < l.length) ∧
    (∀ l xs r, jtail f l = .ok (xs, r) → r.length < l.length) ∧
    (∀ l kvs r, jobj f l = .ok (kvs, r) → r.length < l.length) ∧
    (∀ l kv r, jpair f l = .ok (kv, r) → r.length < l.length) ∧
    (∀ l kvs r, jotail f l = .ok (kvs, r) → r.length < l.length) := by
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro l x r h <;> cases h
  | succ f ih =>
    obtain ⟨hv, ha, ht, ho, hp, hot⟩ := ih
    exact ⟨jval_consumes_step f ha ho, jarr_consumes_step f hv ht, jtail_consumes_step f hv ht,
           jobj_consumes_step f hp hot, jpair_consumes_step f hv, jotail_consumes_step f hp hot⟩

/-! #### A frame with twice its input in fuel never runs out -/

theorem jval_fuel_step (f : Nat)
    (harr : ∀ l, 2 * l.length + 2 ≤ f → jarr f l ≠ .error .outOfFuel)
    (hobj : ∀ l, 2 * l.length + 2 ≤ f → jobj f l ≠ .error .outOfFuel) :
    ∀ l, 2 * l.length + 1 ≤ f + 1 → jval (f + 1) l ≠ .error .outOfFuel := by
  intro l hf h
  rw [jval.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only [List.length_cons] at hl
    simp only at h
    by_cases hd : (charDigit c).isSome = true
    · rw [if_pos hd] at h
      exact jnumber_ne_outOfFuel false (c :: t) h
    · rw [if_neg hd] at h
      by_cases hm : c = '-'
      · rw [if_pos hm] at h
        exact jnumber_ne_outOfFuel true t h
      rw [if_neg hm] at h
      by_cases hq : c = '"'
      · rw [if_pos hq] at h
        cases hj : jstring t with
        | error e =>
          rw [hj] at h
          simp only [Except.error.injEq] at h
          subst h
          exact jstring_ne_outOfFuel t hj
        | ok p => obtain ⟨s, r'⟩ := p; rw [hj] at h; cases h
      · rw [if_neg hq] at h
        by_cases hb : c = '['
        · rw [if_pos hb] at h
          cases hj : jarr f t with
          | error e =>
            rw [hj] at h
            simp only [Except.error.injEq] at h
            subst h
            exact harr t (by omega) hj
          | ok p => obtain ⟨xs, r'⟩ := p; rw [hj] at h; cases h
        · rw [if_neg hb] at h
          by_cases hc : c = '{'
          · rw [if_pos hc] at h
            cases hj : jobj f t with
            | error e =>
              rw [hj] at h
              simp only [Except.error.injEq] at h
              subst h
              exact hobj t (by omega) hj
            | ok p => obtain ⟨kvs, r'⟩ := p; rw [hj] at h; cases h
          · rw [if_neg hc] at h
            split at h <;> cases h

theorem jarr_fuel_step (f : Nat)
    (hcons : ∀ l v r, jval f l = .ok (v, r) → r.length < l.length)
    (hval : ∀ l, 2 * l.length + 1 ≤ f → jval f l ≠ .error .outOfFuel)
    (htail : ∀ l, 2 * l.length + 2 ≤ f → jtail f l ≠ .error .outOfFuel) :
    ∀ l, 2 * l.length + 2 ≤ f + 1 → jarr (f + 1) l ≠ .error .outOfFuel := by
  intro l hf h
  rw [jarr.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only [List.length_cons] at hl
    simp only at h
    by_cases hb : c = ']'
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h
      cases hv : jval f (c :: t) with
      | error e =>
        rw [hv] at h
        simp only [Except.error.injEq] at h
        subst h
        exact hval (c :: t) (by simp only [List.length_cons]; omega) hv
      | ok p =>
        obtain ⟨x, r1⟩ := p
        rw [hv] at h
        simp only at h
        have h1 := hcons _ _ _ hv
        simp only [List.length_cons] at h1
        cases ht : jtail f r1 with
        | error e =>
          rw [ht] at h
          simp only [Except.error.injEq] at h
          subst h
          exact htail r1 (by omega) ht
        | ok q => obtain ⟨ys, r2⟩ := q; rw [ht] at h; cases h

theorem jtail_fuel_step (f : Nat)
    (hcons : ∀ l v r, jval f l = .ok (v, r) → r.length < l.length)
    (hval : ∀ l, 2 * l.length + 1 ≤ f → jval f l ≠ .error .outOfFuel)
    (htail : ∀ l, 2 * l.length + 2 ≤ f → jtail f l ≠ .error .outOfFuel) :
    ∀ l, 2 * l.length + 2 ≤ f + 1 → jtail (f + 1) l ≠ .error .outOfFuel := by
  intro l hf h
  rw [jtail.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only [List.length_cons] at hl
    simp only at h
    by_cases hb : c = ']'
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h
      by_cases hc : c = ','
      · rw [if_pos hc] at h
        cases hv : jval f t with
        | error e =>
          rw [hv] at h
          simp only [Except.error.injEq] at h
          subst h
          exact hval t (by omega) hv
        | ok p =>
          obtain ⟨x, r1⟩ := p
          rw [hv] at h
          simp only at h
          have h1 := hcons _ _ _ hv
          cases ht : jtail f r1 with
          | error e =>
            rw [ht] at h
            simp only [Except.error.injEq] at h
            subst h
            exact htail r1 (by omega) ht
          | ok q => obtain ⟨ys, r2⟩ := q; rw [ht] at h; cases h
      · rw [if_neg hc] at h; cases h

theorem jobj_fuel_step (f : Nat)
    (hcons : ∀ l kv r, jpair f l = .ok (kv, r) → r.length < l.length)
    (hpair : ∀ l, 2 * l.length + 1 ≤ f → jpair f l ≠ .error .outOfFuel)
    (hotail : ∀ l, 2 * l.length + 2 ≤ f → jotail f l ≠ .error .outOfFuel) :
    ∀ l, 2 * l.length + 2 ≤ f + 1 → jobj (f + 1) l ≠ .error .outOfFuel := by
  intro l hf h
  rw [jobj.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only [List.length_cons] at hl
    simp only at h
    by_cases hb : c = '}'
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h
      cases hv : jpair f (c :: t) with
      | error e =>
        rw [hv] at h
        simp only [Except.error.injEq] at h
        subst h
        exact hpair (c :: t) (by simp only [List.length_cons]; omega) hv
      | ok p =>
        obtain ⟨kv, r1⟩ := p
        rw [hv] at h
        simp only at h
        have h1 := hcons _ _ _ hv
        simp only [List.length_cons] at h1
        cases ht : jotail f r1 with
        | error e =>
          rw [ht] at h
          simp only [Except.error.injEq] at h
          subst h
          exact hotail r1 (by omega) ht
        | ok q => obtain ⟨ys, r2⟩ := q; rw [ht] at h; cases h

theorem jpair_fuel_step (f : Nat)
    (hval : ∀ l, 2 * l.length + 1 ≤ f → jval f l ≠ .error .outOfFuel) :
    ∀ l, 2 * l.length + 1 ≤ f + 1 → jpair (f + 1) l ≠ .error .outOfFuel := by
  intro l hf h
  rw [jpair.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only [List.length_cons] at hl
    simp only at h
    by_cases hq : c = '"'
    · rw [if_pos hq] at h
      cases hj : jstring t with
      | error e =>
        rw [hj] at h
        simp only [Except.error.injEq] at h
        subst h
        exact jstring_ne_outOfFuel t hj
      | ok p =>
        obtain ⟨k, r1⟩ := p
        rw [hj] at h
        simp only at h
        have h1 := jstring_length t k r1 hj
        have hl1 := skipWs_length_le r1
        cases hs1 : skipWs r1 with
        | nil => rw [hs1] at h; cases h
        | cons c' r2 =>
          rw [hs1] at h hl1
          simp only [List.length_cons] at hl1
          simp only at h
          by_cases hc : c' = ':'
          · rw [if_pos hc] at h
            cases hv : jval f r2 with
            | error e =>
              rw [hv] at h
              simp only [Except.error.injEq] at h
              subst h
              exact hval r2 (by omega) hv
            | ok q => obtain ⟨v, r3⟩ := q; rw [hv] at h; cases h
          · rw [if_neg hc] at h; cases h
    · rw [if_neg hq] at h; cases h

theorem jotail_fuel_step (f : Nat)
    (hcons : ∀ l kv r, jpair f l = .ok (kv, r) → r.length < l.length)
    (hpair : ∀ l, 2 * l.length + 1 ≤ f → jpair f l ≠ .error .outOfFuel)
    (hotail : ∀ l, 2 * l.length + 2 ≤ f → jotail f l ≠ .error .outOfFuel) :
    ∀ l, 2 * l.length + 2 ≤ f + 1 → jotail (f + 1) l ≠ .error .outOfFuel := by
  intro l hf h
  rw [jotail.eq_2] at h
  have hl := skipWs_length_le l
  cases hs : skipWs l with
  | nil => rw [hs] at h; cases h
  | cons c t =>
    rw [hs] at h hl
    simp only [List.length_cons] at hl
    simp only at h
    by_cases hb : c = '}'
    · rw [if_pos hb] at h; cases h
    · rw [if_neg hb] at h
      by_cases hc : c = ','
      · rw [if_pos hc] at h
        cases hv : jpair f t with
        | error e =>
          rw [hv] at h
          simp only [Except.error.injEq] at h
          subst h
          exact hpair t (by omega) hv
        | ok p =>
          obtain ⟨kv, r1⟩ := p
          rw [hv] at h
          simp only at h
          have h1 := hcons _ _ _ hv
          cases ht : jotail f r1 with
          | error e =>
            rw [ht] at h
            simp only [Except.error.injEq] at h
            subst h
            exact hotail r1 (by omega) ht
          | ok q => obtain ⟨ys, r2⟩ := q; rw [ht] at h; cases h
      · rw [if_neg hc] at h; cases h

/-- **Fuel twice the input's length is enough for every entry point.**  The
bounds differ by one between entry points because `jval` hands `jarr`/`jobj`
the bytes after the bracket, and `jpair` hands `jval` the bytes after the
colon. -/
theorem jparser_fuel (f : Nat) :
    (∀ l, 2 * l.length + 1 ≤ f → jval f l ≠ .error .outOfFuel) ∧
    (∀ l, 2 * l.length + 2 ≤ f → jarr f l ≠ .error .outOfFuel) ∧
    (∀ l, 2 * l.length + 2 ≤ f → jtail f l ≠ .error .outOfFuel) ∧
    (∀ l, 2 * l.length + 2 ≤ f → jobj f l ≠ .error .outOfFuel) ∧
    (∀ l, 2 * l.length + 1 ≤ f → jpair f l ≠ .error .outOfFuel) ∧
    (∀ l, 2 * l.length + 2 ≤ f → jotail f l ≠ .error .outOfFuel) := by
  induction f with
  | zero => refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro l hf <;> omega
  | succ f ih =>
    obtain ⟨hv, ha, ht, ho, hp, hot⟩ := ih
    obtain ⟨cv, -, -, -, cp, -⟩ := jparser_consumes f
    exact ⟨jval_fuel_step f ha ho, jarr_fuel_step f cv hv ht, jtail_fuel_step f cv hv ht,
           jobj_fuel_step f cp hp hot, jpair_fuel_step f hv, jotail_fuel_step f cp hp hot⟩

/-- **`jparse` never refuses for fuel — on any input at all.**  `JErr.outOfFuel`
is reachable only through `jparseWith` with a fuel the caller chose
(`jparseWith_refuses_when_the_fuel_runs_out` is that half); the fuel `jparse`
derives from the bytes is always enough, host bytes included. -/
theorem jparse_never_runs_out (l : List Char) : jparse l ≠ .error .outOfFuel := by
  intro h
  unfold jparse jparseWith at h
  cases hv : jval (2 * l.length + 2) l with
  | error e =>
    rw [hv] at h
    simp only [Except.error.injEq] at h
    subst h
    exact (jparser_fuel _).1 l (by omega) hv
  | ok p =>
    obtain ⟨v, rest⟩ := p
    rw [hv] at h
    simp only at h
    split at h <;> cases h

/-! ### J3/J4 non-vacuity, and both directions (§5.2, §5.8)

`jparse_jemit` would hold just as well of an emitter and a parser that agreed on
some *other* encoding, so the bytes are pinned separately below.  The refusals
are the biting half; the round trip's instances on real request bytes and the
evaluated witnesses on small host-shaped inputs are the half that shows the
parser does not over-bite.

**How these witnesses are written, and why — measured 2026-09-12.**  A parser
run is evaluated only over an explicit `List Char` literal, never over
`"…".toList`.  Evaluating `jparse` over a string literal's `toList` directly
re-forces the literal's decoding every time the parser inspects an unevaluated
tail: `{"a" 1}` (seven bytes) exhausted the 200000-heartbeat `whnf` budget at
~2 GB, and `{"a":1 "b":2}` passed an 8 GB memory cap in 15 s — and kernel
reduction has no heartbeat limit at all, so uncapped this is what exhausted the
machine.  The same bytes spelled as a `List Char` literal evaluate in well under
a second, and `toList` alone, or `rw`-ing a literal to its characters first, is
cheap too.  The rule the module follows: **a parser run over bytes is small and
over a `List Char` literal; a realistic input is an instance of `jparse_jemit`,
with only its emission (`jemit v = bytes`, a `List Char` comparison) evaluated.** -/

/-- Every shape at once, with a key order the alphabet would not choose and a
string that needs escaping. -/
def demoDoc : JVal :=
  .obj [(['o', 'k'], .arr [.num 1, .str ['a', '"', 'b'], .bool false, .null]),
        (['b'], .obj [])]

/-- **The exact bytes.**  Compress-shaped: no space after `:` or `,`. -/
theorem demo_jemit_bytes :
    jemit demoDoc = "{\"ok\":[1,\"a\\\"b\",false,null],\"b\":{}}".toList := by decide

/-- **The order is the value's, not the alphabet's.**  A `Json.mkObj`-backed
printer sorts its keys and would put `"b"` first; these bytes differ. -/
theorem the_emitter_keeps_build_order :
    jemit demoDoc ≠
      jemit (.obj [(['b'], .obj []),
                   (['o', 'k'], .arr [.num 1, .str ['a', '"', 'b'], .bool false, .null])]) := by
  decide

/-- The emitter writes no whitespace of its own — but it does not touch the
whitespace inside a string, and the parser does not skip it either. -/
theorem the_emitter_is_compress_shaped :
    (jemit demoDoc).all (fun c => !wsChar c) = true ∧
    jemit (.str ['a', ' ', 'b']) = ['"', 'a', ' ', 'b', '"'] ∧
    jparse ['"', ' ', 'a', ' ', '"'] = .ok (.str [' ', 'a', ' ']) :=
  ⟨by decide, by decide, rfl⟩

/-- §5.2: the emitter writes bytes, and the parser is not a constant function —
the two empty containers, one byte apart, read back to different values, by
evaluation and by the theorem alike. -/
theorem the_json_round_trip_is_not_vacuous :
    jemit demoDoc ≠ [] ∧
    jparse ['[', ']'] = .ok (.arr []) ∧
    jparse ['{', '}'] = .ok (.obj []) ∧
    jparse (jemit (.arr [])) ≠ jparse (jemit (.obj [])) := by
  refine ⟨by decide, rfl, rfl, ?_⟩
  rw [jparse_jemit, jparse_jemit]
  nofun

/-! #### Real request and response bytes

Taken verbatim from `kernel/tm-kernel-ffi/tests/kernel.rs` —
`duplicate_ids_are_rejected_at_load` sends the first and asserts the second.
Each is stated as emission (evaluated) plus an instance of `jparse_jemit`
(proved), per the rule above. -/

def demoRequestBytes : List Char :=
  ("{\"docs\":[{\"path\":\"w.md\",\"grain\":1,\"ix\":35," ++
   "\"lines\":[\"- [ ] a ^x1\",\"- [ ] b ^x1\"]}],\"cmds\":[]}").toList

def demoRequest : JVal :=
  .obj [("docs".toList,
          .arr [.obj [("path".toList, .str "w.md".toList),
                      ("grain".toList, .num 1),
                      ("ix".toList, .num 35),
                      ("lines".toList, .arr [.str "- [ ] a ^x1".toList,
                                             .str "- [ ] b ^x1".toList])]]),
        ("cmds".toList, .arr [])]

def demoResponseBytes : List Char := "{\"err\":{\"dupId\":\"x1\"}}".toList

def demoResponse : JVal :=
  .obj [("err".toList, .obj [("dupId".toList, .str "x1".toList)])]

/-- **The kernel's own emitter reproduces a real request byte for byte**, and
the parser reads those bytes back to the value they came from.  The first half
is evaluated; the second is `jparse_jemit` at `demoRequest`, not a parser run. -/
theorem the_real_request_bytes_round_trip :
    jemit demoRequest = demoRequestBytes ∧
    jparse demoRequestBytes = .ok demoRequest := by
  have h : jemit demoRequest = demoRequestBytes := by decide
  exact ⟨h, by rw [← h]; exact jparse_jemit demoRequest⟩

theorem the_real_response_bytes_round_trip :
    jemit demoResponse = demoResponseBytes ∧
    jparse demoResponseBytes = .ok demoResponse := by
  have h : jemit demoResponse = demoResponseBytes := by decide
  exact ⟨h, by rw [← h]; exact jparse_jemit demoResponse⟩

/-- **Whitespace between tokens is accepted wherever a host may put it** — at
both ends; after `{`, `[`, `:` and each `,`; before each `,`, `:`, `]` and `}`
— in all four of RFC 8259's spellings, and the document reads to the value
whose compressed bytes the kernel emits (and, by `jparse_jemit`, reads back). -/
theorem jparse_accepts_host_whitespace :
    jparse [' ', '{', '\n', '"', 'a', '"', ' ', ':', '\t', '[', ' ', '1', '\r', ',',
            ' ', '2', ' ', ']', ' ', ',', ' ', '"', 'b', '"', ':', ' ', 'n', 'u', 'l', 'l',
            '\n', '}', ' ']
      = .ok (.obj [(['a'], .arr [.num 1, .num 2]), (['b'], .null)]) ∧
    jemit (.obj [(['a'], .arr [.num 1, .num 2]), (['b'], .null)])
      = ['{', '"', 'a', '"', ':', '[', '1', ',', '2', ']', ',', '"', 'b', '"', ':',
         'n', 'u', 'l', 'l', '}'] ∧
    jparse ['{', '"', 'a', '"', ':', '[', '1', ',', '2', ']', ',', '"', 'b', '"', ':',
            'n', 'u', 'l', 'l', '}']
      = .ok (.obj [(['a'], .arr [.num 1, .num 2]), (['b'], .null)]) := by
  have h : jemit (.obj [(['a'], .arr [.num 1, .num 2]), (['b'], .null)])
      = ['{', '"', 'a', '"', ':', '[', '1', ',', '2', ']', ',', '"', 'b', '"', ':',
         'n', 'u', 'l', 'l', '}'] := by decide
  exact ⟨rfl, h, by rw [← h]; exact jparse_jemit _⟩

/-- **No side condition about duplicate keys, and none is needed.**  An object
is an ordered assoc list (J0), so a host that sends the same key twice gets both
pairs back in order — the hazard a sorted-map object would have created here
does not exist.  Stated three ways: the bytes, the theorem's instance,
and a parser run over those bytes. -/
theorem the_round_trip_survives_duplicate_keys :
    jemit (.obj [(['a'], .num 1), (['a'], .num 2)])
      = ['{', '"', 'a', '"', ':', '1', ',', '"', 'a', '"', ':', '2', '}'] ∧
    jparse (jemit (.obj [(['a'], .num 1), (['a'], .num 2)]))
      = .ok (.obj [(['a'], .num 1), (['a'], .num 2)]) ∧
    jparse ['{', '"', 'a', '"', ':', '1', ',', '"', 'a', '"', ':', '2', '}']
      = .ok (.obj [(['a'], .num 1), (['a'], .num 2)]) :=
  ⟨by decide, jparse_jemit _, rfl⟩

/-- **Leading zeros are refused, as serde_json refuses them** (stage 5 A2;
README gap 43, closed).  This is the refutation of stage 3's
`jparse_accepts_leading_zeros`, which read `007` as `7`: RFC 8259 forbids the
spelling, and a reader that took it would give one value two spellings the host
never agrees to.  A lone `0`, `-0` and `0.5` are not leading zeros, so the
refusal does not over-bite (§5.8). -/
theorem jparse_refuses_a_leading_zero :
    jparse ['0', '0', '7'] = .error .leadingZero ∧
    jparse ['-', '0', '1'] = .error .leadingZero ∧
    jparse ['0', '0', '.', '5'] = .error .leadingZero ∧
    jparse ['0'] = .ok (.num 0) ∧
    jparse ['-', '0'] = .ok (.dec ⟨⟨true, 0, [], none⟩, rfl⟩) ∧
    jparse ['0', '.', '5'] = .ok (.dec ⟨⟨false, 0, [5], none⟩, rfl⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A bare natural is still `num`** — every one, by the round trip, and on bytes. -/
theorem jparse_reads_a_plain_numeral_as_num :
    (∀ n : Nat, jparse (jrenderNat n) = .ok (.num n)) ∧
    jparse ['1', '0'] = .ok (.num 10) :=
  ⟨fun n => jparse_jemit (.num n), rfl⟩

/-- **A signed decimal is `dec`**, digit for digit (design §5.1's witness). -/
theorem jparse_reads_a_signed_decimal_as_dec :
    jparse ['-', '0', '.', '5'] = .ok (.dec ⟨⟨true, 0, [5], none⟩, rfl⟩) :=
  rfl

/-- **The exponent is kept as digits.**  `E` and `+` are spellings of `e` and of
no sign, so `1E+5` is `1e5`; but `1e05` is not `1e5`, and `1e0005` is emitted
as written — the emission evaluated, the read back `jparse_jemit`'s instance
(design K18). -/
theorem jparse_reads_an_exponent_as_written :
    jparse ['1', 'E', '+', '5'] = .ok (.dec ⟨⟨false, 1, [], some (false, 5, [])⟩, rfl⟩) ∧
    jparse ['1', 'e', '5'] = .ok (.dec ⟨⟨false, 1, [], some (false, 5, [])⟩, rfl⟩) ∧
    jparse ['2', 'e', '-', '0', '5'] = .ok (.dec ⟨⟨false, 2, [], some (true, 0, [5])⟩, rfl⟩) ∧
    jemit (.dec ⟨⟨false, 1, [], some (false, 0, [0, 0, 5])⟩, rfl⟩) = ['1', 'e', '0', '0', '0', '5'] ∧
    jparse ['1', 'e', '0', '0', '0', '5']
      = .ok (.dec ⟨⟨false, 1, [], some (false, 0, [0, 0, 5])⟩, rfl⟩) := by
  have h : jemit (.dec ⟨⟨false, 1, [], some (false, 0, [0, 0, 5])⟩, rfl⟩)
      = ['1', 'e', '0', '0', '0', '5'] := by decide
  exact ⟨rfl, rfl, rfl, h, by rw [← h]; exact jparse_jemit _⟩

/-- **A numeral stops where a digit must follow, by name.**  After `-`, `.`, the
marker and its sign.  The `1e` conjunct is why the exponent's digits are a first
digit and the rest: the design's `some (false, [])` would have emitted exactly
these refused bytes, so over its type `jparse_jemit` was false (README). -/
theorem jparse_refuses_a_numeral_missing_a_digit :
    jparse ['-'] = .error (.missingDigit '-') ∧
    jparse ['-', 'x'] = .error (.missingDigit '-') ∧
    jparse ['1', '.'] = .error (.missingDigit '.') ∧
    jparse ['1', '.', 'e', '5'] = .error (.missingDigit '.') ∧
    jparse ['1', 'e'] = .error (.missingDigit 'e') ∧
    jparse ['1', 'E', '+'] = .error (.missingDigit '+') ∧
    jparse ['+', '1'] = .error (.notAValue '+') :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! #### The refusals, each by its own name (§5.7, §5.8) -/

theorem jparse_refuses_empty_input : jparse [] = .error .emptyInput := rfl

theorem jparse_refuses_an_unterminated_string :
    jparse ['"', 'a', 'b', 'c'] = .error .unterminatedString := rfl

theorem jparse_refuses_trailing_garbage :
    jparse ['n', 'u', 'l', 'l', ' ', 'j', 'u', 'n', 'k'] = .error (.trailingGarbage 'j') := rfl

theorem jparse_refuses_a_bad_escape :
    jparse ['"', 'a', '\\', 'q', '"'] = .error (.badEscape (.unknownEscape 'q')) := rfl

theorem jparse_refuses_a_raw_control_byte :
    jparse ['"', Char.ofNat 7, '"'] = .error (.badEscape (.rawControl 7)) := rfl

/-- No trailing comma, in either container. -/
theorem jparse_refuses_a_trailing_comma :
    jparse ['[', '1', ',', ']'] = .error (.notAValue ']') ∧
    jparse ['{', '"', 'a', '"', ':', '1', ',', '}'] = .error (.expectedKey '}') :=
  ⟨rfl, rfl⟩

theorem jparse_refuses_an_unterminated_array :
    jparse ['[', '1'] = .error .unterminatedArray := rfl

theorem jparse_refuses_a_missing_separator :
    jparse ['[', '1', ' ', '2', ']'] = .error (.expectedCommaOrBracket '2') ∧
    jparse ['{', '"', 'a', '"', ':', '1', ' ', '"', 'b', '"', ':', '2', '}']
      = .error (.expectedCommaOrBrace '"') :=
  ⟨rfl, rfl⟩

theorem jparse_refuses_a_bare_key :
    jparse ['{', 'a', ':', '1', '}'] = .error (.expectedKey 'a') := rfl

theorem jparse_refuses_a_missing_colon :
    jparse ['{', '"', 'a', '"', ' ', '1', '}'] = .error (.expectedColon '1') := rfl

theorem jparse_refuses_an_unterminated_object :
    jparse ['{', '"', 'a', '"', ':', '1'] = .error .unterminatedObject := rfl

/-- **Refutation and rename of stage 3's
`jparse_refuses_what_the_fragment_has_no_type_for`** (stage 5 A2, design §5.1).
That theorem said `-3`, `1.5` and `1e3` were refused because `JVal.num` was a
`Nat`; after the widening each reads, exactly as written, so it is false.  What
keeps the wire honest now is the reader, not the parser:
`a_request_number_that_is_not_a_nat_is_refused_by_its_reader` in `Boundary.lean`.
Nothing is truncated — the `.toOption` failure §5.10 records stays impossible,
because a `dec` is not a `num` to any reader. -/
theorem jparse_reads_what_the_fragment_had_no_type_for :
    jparse ['-', '3'] = .ok (.dec ⟨⟨true, 3, [], none⟩, rfl⟩) ∧
    jparse ['1', '.', '5'] = .ok (.dec ⟨⟨false, 1, [5], none⟩, rfl⟩) ∧
    jparse ['1', 'e', '3'] = .ok (.dec ⟨⟨false, 1, [], some (false, 3, [])⟩, rfl⟩) :=
  ⟨rfl, rfl, rfl⟩

/-- **Running out of fuel is a named refusal** (§5.7), and it is reachable only
through `jparseWith`: the same bytes parse under the fuel `jparse` derives for
itself, and `jparse_never_runs_out` says that fuel is always enough. -/
theorem jparseWith_refuses_when_the_fuel_runs_out :
    jparseWith 2 ['[', '[', '1', ']', ']'] = .error .outOfFuel ∧
    jparseWith 0 ['n', 'u', 'l', 'l'] = .error .outOfFuel ∧
    jparse ['[', '[', '1', ']', ']'] = .ok (.arr [.arr [.num 1]]) :=
  ⟨rfl, rfl, rfl⟩

/-! #### `jval_jemit`'s own hypotheses (§7.4 item 2) -/

/-- Both hypotheses are satisfiable, exhibited rather than asserted — and
`jparse_jemit` discharges them for every value, at `rest = []`. -/
theorem the_jval_jemit_hypotheses_are_satisfiable :
    jfuel (JVal.num 7) ≤ 2 * (jemit (JVal.num 7)).length ∧
    numEnd [] = true ∧ numEnd [','] = true ∧ numEnd [']'] = true ∧ numEnd ['}'] = true ∧
    jval (2 * (jemit (JVal.num 7)).length) (jemit (JVal.num 7) ++ [])
      = .ok (.num 7, []) :=
  ⟨by decide, by decide, by decide, by decide, by decide, rfl⟩

/-- And the `notDigitStart` one **bites**: drop it and the conclusion is false,
because a `7` written next to a `7` reads back as `77`.  This is the same guard
`the_next_byte_guard_bites` states for J2, now at the value level; `Negative.lean`
CHEAT 47 is the same fact as a type error. -/
theorem the_jval_jemit_digit_guard_bites :
    notDigitStart ['7'] = false ∧
    jval 4 (jemit (JVal.num 7) ++ ['7']) = .ok (.num 77, []) ∧
    jval 4 (jemit (JVal.num 7) ++ ['7']) ≠ .ok (.num 7, ['7']) := by
  have h : jval 4 (jemit (JVal.num 7) ++ ['7']) = .ok (.num 77, []) := rfl
  refine ⟨by decide, h, ?_⟩
  rw [h]
  nofun

/-- **Why the guard is `numEnd` and not `notDigitStart`** (stage 5 A2).  With the
old guard `jval_jemit` would be false: `.5` does not start with a digit, and `1`
followed by `.5` reads as the one numeral `1.5`, not as `1` with `.5` left over.
So stage 3's statement of `jval_jemit` is refuted by this witness and restated
over `numEnd`; `jparse_jemit`, which sits on it at `rest = []`, is unchanged.
`Negative.lean` CHEAT 120 is the same fact as a type error. -/
theorem the_jval_jemit_fraction_guard_bites :
    notDigitStart ['.', '5'] = true ∧
    numEnd ['.', '5'] = false ∧
    jval 4 (jemit (JVal.num 1) ++ ['.', '5']) = .ok (.dec ⟨⟨false, 1, [5], none⟩, rfl⟩, []) ∧
    jval 4 (jemit (JVal.num 1) ++ ['.', '5']) ≠ .ok (.num 1, ['.', '5']) := by
  have h : jval 4 (jemit (JVal.num 1) ++ ['.', '5'])
      = .ok (.dec ⟨⟨false, 1, [5], none⟩, rfl⟩, []) := rfl
  refine ⟨by decide, by decide, h, ?_⟩
  rw [h]
  nofun


/-! ## J5 — reading a request

`Boundary.call` now reads the request with `jparse` and the fields out of the
`JVal` with `jget`; nothing of `Lean.Json` is on the wire.  Two things a reader
needs that the codec itself does not: a name for every parse refusal, so the
host's `{"err":"bad json: …"}` carries a diagnostic rather than a default
(§5.7), and **one rule for a duplicate key**. -/

/-- A `JEsc` as the text the host sees.  Every constructor by name. -/
def jescText : JEsc → String
  | .truncatedEscape => "truncatedEscape"
  | .unknownEscape c => s!"unknownEscape {c}"
  | .badHexQuad a b c d => s!"badHexQuad {a}{b}{c}{d}"
  | .surrogateEscape v => s!"surrogateEscape {v}"
  | .rawQuote => "rawQuote"
  | .rawControl v => s!"rawControl {v}"

/-- A `JErr` as the text the host sees.  Every constructor by name. -/
def jerrText : JErr → String
  | .outOfFuel => "outOfFuel"
  | .emptyInput => "emptyInput"
  | .notAValue c => s!"notAValue {c}"
  | .badNumber => "badNumber"
  | .unterminatedString => "unterminatedString"
  | .badEscape e => s!"badEscape {jescText e}"
  | .unterminatedArray => "unterminatedArray"
  | .expectedCommaOrBracket c => s!"expectedCommaOrBracket {c}"
  | .unterminatedObject => "unterminatedObject"
  | .expectedCommaOrBrace c => s!"expectedCommaOrBrace {c}"
  | .expectedColon c => s!"expectedColon {c}"
  | .expectedKey c => s!"expectedKey {c}"
  | .trailingGarbage c => s!"trailingGarbage {c}"
  | .leadingZero => "leadingZero"
  | .missingDigit c => s!"missingDigit {c}"

/-- **The one way a request field is read.**  `none` is an absent key and
`some v` the value of the **only** pair carrying it.  A key carried twice is
refused, by name: `jparse` keeps both pairs (an object is an ordered assoc
list, J0), and taking either would be the reader picking between two readings
— §5.6's defect class, one layer out.  `Lean.Json`'s parser and serde_json's
`Value` both silently keep the last; the kernel does not guess.  Only the key
being read is checked, so a duplicate the kernel never reads is not a reading
it picks.  A non-object has no fields and is refused too. -/
def jget (j : JVal) (k : String) : Except String (Option JVal) :=
  match j with
  | .obj kvs =>
    match kvs.filter (fun kv => kv.1 == k.toList) with
    | [] => .ok none
    | [(_, v)] => .ok (some v)
    | _ => .error s!"duplicateKey {k}"
  | _ => .error "object expected"

/-- A key carried once reads as its value; an absent key reads as `none`. -/
theorem jget_reads_the_one_pair :
    jget (.obj [(['i', 'd'], .str ['m', '1']), (['d', 'o', 'c'], .num 1)]) "doc"
      = .ok (some (.num 1)) ∧
    jget (.obj [(['i', 'd'], .str ['m', '1'])]) "doc" = .ok none :=
  ⟨rfl, rfl⟩

/-- **The duplicate-key rule bites** — both orders, so neither the first nor the
last pair is quietly preferred — and a non-object has no fields. -/
theorem jget_refuses_a_duplicate_key :
    jget (.obj [(['i', 'd'], .str ['a']), (['i', 'd'], .str ['b'])]) "id"
      = .error "duplicateKey id" ∧
    jget (.obj [(['i', 'd'], .str ['b']), (['i', 'd'], .str ['a'])]) "id"
      = .error "duplicateKey id" ∧
    jget (.arr []) "id" = .error "object expected" :=
  ⟨rfl, rfl, rfl⟩

/-- A duplicate the kernel does not read is not a reading it picks: the other
key still reads. -/
theorem jget_ignores_a_duplicate_it_does_not_read :
    jget (.obj [(['x'], .num 1), (['x'], .num 2), (['i', 'd'], .str ['a'])]) "id"
      = .ok (some (.str ['a'])) := rfl

end Tm
