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

**On the wire since J5 (response side).**  `Boundary.lean` builds every response
as a `JVal` and `call` writes it with `jemit`; `jescapeTR` is the one runtime
twin that move needed (a `@[csimp]` theorem, see there).

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
    ?null ?bool ?num ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair v
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
  /-- A byte that starts no value of this fragment — `-` and `+` included, since
  `JVal.num` is a `Nat`. -/
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

/-- Read a string body: scan to the closing quote, then un-escape with J1's
`junescape`, whose refusals become `JErr.badEscape`. -/
def jstring (l : List Char) : Except JErr (List Char × List Char) :=
  match jscan l with
  | none => .error .unterminatedString
  | some (s, r) =>
    match junescape s with
    | .error e => .error (.badEscape e)
    | .ok cs => .ok (cs, r)

mutual
/-- A value, with whatever whitespace precedes it. -/
def jval : Nat → List Char → Except JErr (JVal × List Char)
  | 0, _ => .error .outOfFuel
  | f + 1, l =>
    match skipWs l with
    | [] => .error .emptyInput
    | c :: r =>
      if (charDigit c).isSome then
        match jparseNat (c :: r) with
        | none => .error .badNumber
        | some (n, r') => .ok (.num n, r')
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
  | str s => exact ⟨'"', jescape s ++ ['"'], rfl, by decide, by decide, by decide⟩
  | arr xs => exact ⟨'[', jemitArr xs, rfl, by decide, by decide, by decide⟩
  | obj kvs => exact ⟨'{', jemitObj kvs, rfl, by decide, by decide, by decide⟩

/-- A numeral inside a document is always followed by `]`, `}` or `,` — never by
another digit.  This is the hypothesis `jparseNat_jrenderNat` needs, discharged
at every site rather than assumed. -/
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

theorem jval_digit (f : Nat) (c : Char) (r : List Char) (h : (charDigit c).isSome = true) :
    jval (f + 1) (c :: r) =
      (match jparseNat (c :: r) with
       | none => .error .badNumber
       | some (n, r') => .ok (JVal.num n, r')) := by
  simp only [jval, skipWs_cons_of_not_ws c r (charDigit_not_ws c h), h, if_true]

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
`notDigitStart` hypothesis because a numeral is the one value whose end is
decided by the byte after it; the list motives do not need it, because a list
element is always followed by `,` or a closer.

**No side condition, and in particular none about duplicate keys.**  A `JVal`
object is an ordered assoc list (J0), so `{"a":1,"a":2}` is a value the kernel
can build, emit and read back unchanged — see
`the_round_trip_survives_duplicate_keys`.  The hazard a `Std.TreeMap`-backed
object would have created here does not exist. -/

theorem jval_jemit (v : JVal) : ∀ (f : Nat) (rest : List Char),
    jfuel v ≤ f → notDigitStart rest = true →
    jval f (jemit v ++ rest) = .ok (v, rest) := by
  refine JVal.rec
    (motive_1 := fun v => ∀ f rest, jfuel v ≤ f → notDigitStart rest = true →
      jval f (jemit v ++ rest) = .ok (v, rest))
    (motive_2 := fun xs =>
      (∀ f rest, jfuelL xs ≤ f → jarr f (jemitArr xs ++ rest) = .ok (xs, rest)) ∧
      (∀ f rest, jfuelL xs ≤ f → jtail f (jemitTail xs ++ rest) = .ok (xs, rest)))
    (motive_3 := fun kvs =>
      (∀ f rest, jfuelO kvs ≤ f → jobj f (jemitObj kvs ++ rest) = .ok (kvs, rest)) ∧
      (∀ f rest, jfuelO kvs ≤ f → jotail f (jemitOTail kvs ++ rest) = .ok (kvs, rest)))
    (motive_4 := fun p => ∀ f rest, jfuelPair p ≤ f → notDigitStart rest = true →
      jpair f (jemitPair p ++ rest) = .ok (p, rest))
    ?null ?bool ?num ?str ?arr ?obj ?lnil ?lcons ?onil ?ocons ?pair v
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
      have hnum : jparseNat (digitsOf n ++ rest) = some (n, rest) :=
        jparseNat_jrenderNat n rest hr
      cases hd : digitsOf n with
      | nil => exact absurd hd (digitsOf_ne_nil n)
      | cons c t =>
        have hc : (charDigit c).isSome = true :=
          digitsOf_all_digits n c (by rw [hd]; simp)
        rw [hd, List.cons_append] at hnum
        show jval (g + 1) (digitsOf n ++ rest) = _
        rw [hd, List.cons_append, jval_digit g c (t ++ rest) hc, hnum]
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
        simp only [ihx g (jemitTail xs ++ rest) h1 (notDigitStart_jemitTail xs rest),
                   ihxs.2 g rest h2]
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g =>
        have h1 : jfuel x ≤ g := by omega
        have h2 : jfuelL xs ≤ g := by omega
        show jtail (g + 1) ((',' :: (jemit x ++ jemitTail xs)) ++ rest) = _
        rw [List.cons_append, jtail_comma, List.append_assoc]
        simp only [ihx g (jemitTail xs ++ rest) h1 (notDigitStart_jemitTail xs rest),
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
        simp only [ihkv g (jemitOTail kvs ++ rest) h1 (notDigitStart_jemitOTail kvs rest),
                   ihkvs.2 g rest h2]
    · intro f rest hf
      cases f with
      | zero => omega
      | succ g =>
        have h1 : jfuelPair kv ≤ g := by omega
        have h2 : jfuelO kvs ≤ g := by omega
        show jotail (g + 1) ((',' :: (jemitPair kv ++ jemitOTail kvs)) ++ rest) = _
        rw [List.cons_append, jotail_comma, List.append_assoc]
        simp only [ihkv g (jemitOTail kvs ++ rest) h1 (notDigitStart_jemitOTail kvs rest),
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
      cases hn : jparseNat (c :: t) with
      | none => rw [hn] at h; cases h
      | some p =>
        obtain ⟨n, r'⟩ := p
        rw [hn] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        have := jparseNat_length c t r' n hd hn
        omega
    · rw [if_neg hd] at h
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
      cases hn : jparseNat (c :: t) with
      | none => rw [hn] at h; cases h
      | some p => obtain ⟨n, r'⟩ := p; rw [hn] at h; cases h
    · rw [if_neg hd] at h
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

/-- **Two spellings, one value: leading zeros are accepted** (README gap 43).
RFC 8259 forbids `007`; `jparseNat` folds it through `readNat`, which does not,
and the kernel emits only the canonical `7`.  So `jparse` is a left inverse of
`jemit` and not a right one — which whitespace and `\t` already made true. -/
theorem jparse_accepts_leading_zeros :
    jparse ['0', '0', '7'] = .ok (.num 7) ∧
    jemit (.num 7) = ['7'] ∧
    jparse ['0'] = .ok (.num 0) :=
  ⟨rfl, by decide, rfl⟩

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

/-- **The fragment is narrow, and refuses by name rather than truncating.**
`JVal.num` is a `Nat`, so a sign, a fraction and an exponent have no type here —
and a reader that quietly dropped them is exactly the `.toOption` failure §5.10
records. -/
theorem jparse_refuses_what_the_fragment_has_no_type_for :
    jparse ['-', '3'] = .error (.notAValue '-') ∧
    jparse ['1', '.', '5'] = .error (.trailingGarbage '.') ∧
    jparse ['1', 'e', '3'] = .error (.trailingGarbage 'e') :=
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
    notDigitStart [] = true ∧
    jval (2 * (jemit (JVal.num 7)).length) (jemit (JVal.num 7) ++ [])
      = .ok (.num 7, []) :=
  ⟨by decide, by decide, rfl⟩

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

end Tm
