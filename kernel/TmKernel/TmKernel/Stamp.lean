import TmKernel.Cal
import TmKernel.Line
/-!
# Stamp — the log's timestamps (stage 5, D9 track, step B2)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §5.3 and §14.2 row B2.  Every line of
`.tm/log.jsonl` carries a `"t"` field, and the fork point reads and writes it with two
functions in `tm-core/src/log.rs`:

* `parse_timestamp(s)` is `DateTime::parse_from_rfc3339(s)`, and, only when that fails,
  `DateTime::parse_from_str(s, "%Y-%m-%dT%H:%M%:z")`.  This module's `parseStamp` ports both,
  from chrono 0.4.45's source (`format/parse.rs` `parse_rfc3339`, `parse_internal`;
  `format/scan.rs` `nanosecond`, `timezone_offset`, `colon_or_space`; `format/parsed.rs`).
* `fmt_timestamp(t)` is `t.to_rfc3339_opts(SecondsFormat::Secs, false)`: whole seconds, the
  offset as `±HH:MM` rounded to the minute, `+00:00` for UTC, and a leap second written as
  second `60` (`format/formatting.rs` `write_rfc3339`).  This module's `renderStamp` ports it.
* The human `tm log` column is `e.t.format("%Y-%m-%d %H:%M")`, the local clock in the written
  offset.  `displayStamp` ports it, so Rust never parses a stamp (§11.4).

A stamp is a pair: the instant (`Cal.VInstant`, UTC seconds since 0001-01-01 and chrono's
nanoseconds) and the offset it was written in (`Cal.VOffset`).  chrono's `DateTime<FixedOffset>`
compares **only the instant** (`PartialOrd` compares the UTC datetimes), so `stampBefore`
is `Cal.Instant`'s `<`, which is chrono's order and **not** `Instant.nanos`' (B1's refutation
`the_instant_order_is_not_the_nanos_order`; carried note 1).  Two stamps of one instant written
in two offsets are neither before the other (`stamp_order_is_the_instant_order`), and a leap
second is before the next second although its nanosecond count is larger
(`a_leap_second_stamp_is_before_the_next_second`).

## The namespace: `Tm.LogStamp`, never `Tm.Stamp`

`Line.lean` already has `Tm.Field.Stamp` (the `demoted:` stamp, `W36`/`D07`) with
`Field.parseStamp`, `Field.renderStamp`, `Field.parseStamps` and `Field.renderStamps`, and
`Goals.lean` opens `Field (… Stamp …)`.  A namespace `Tm.Stamp` there would make `Stamp.x` mean
two things, and an `open` of both namespaces would make the bare `parseStamp` ambiguous.  So
this module's names live in **`Tm.LogStamp`**, a name nothing else in the kernel uses, and
every caller writes them qualified (`LogStamp.parseStamp`, `LogStamp.StampErr`).  **Do not
`open LogStamp` in a file that opens `Field`.**  The design's `Stamp.parseStamp`,
`Stamp.renderStamp` and `Stamp.StampErr` are these.

## The grammar (chrono's, exactly, inside the instant range)

`rfc3339`: at least 19 characters; `YYYY-MM-DD` read by `Field.parseDate` (the one date
grammar, AGENTS §5.3), or `0000-12-31` (below); a separator `T`, `t` or a space; `HH:MM` read
by `Field.parseClock`; `:SS` with second `60` read as second 59 plus 10⁹ ns (chrono's leap
rule); an optional `.` and at least one digit, the first nine counted and the rest skipped;
then `Z`, `z` or a sign (`+`, `-`, or U+2212 MINUS SIGN, which chrono accepts) with `HH:MM`
(minutes below 60, the whole offset below a day), and the end.  `fallback`, taken only when
`rfc3339` fails, is chrono's generic parser over `%Y-%m-%dT%H:%M%:z`: Rust's Unicode
whitespace may precede each number and the offset; a year of up to four digits, or signed
with any number; one or two digits for month, day, hour and minute; a literal `T`; any mix of
`:` and whitespace between the offset's hours and minutes; no seconds.

**Year 0.**  `Cal.Date` starts at year 1, and chrono's proleptic year 0 exists.  The one year-0
day an instant of `Cal.VInstant` can read is **0000-12-31**, west of UTC in the first day after
the origin, so both parsers read that date as a base one day before `Day` 0, and `renderStamp`
writes it.  Every other year-0 date is before the origin.

**What the kernel refuses that chrono reads** (parity entry P23, measured): a stamp whose
instant is before 0001-01-01T00:00:00Z or at or after 10000-01-01T00:00:00Z (`beforeOrigin`,
`pastYear9999`).  `Cal.Instant.wf` bounds the instant (R10), so no `VInstant` holds one.  The
scratch differential of step B2 found no other difference (README, "Stage 5 B2").

## The errors

`StampErr` names the class a refusal falls in.  It is the `rfc3339` reader's error, even when
the fallback also failed (the fork returns the fallback's error text, which for a stamp with
seconds would name the wrong thing); parity entry P15 already records that warning text is
named rather than serde's.  chrono's error kinds (`TOO_SHORT`, `INVALID`, `OUT_OF_RANGE`) are
not ported one for one: only acceptance and the value are parity.

## Rule D9-21

A `"t"` string can be as long as a line (65,536 characters).  Every function here that walks it
is tail recursive or bounded: `List.length`, `take` and `takeWhile` compile through core's
`@[csimp]` twins, `drop` and `dropWhile` are tail recursive, `readNat` is a `foldl`, and the
digit runs a number is read from are cut to 9 (a fraction), 4 (an unsigned year) or 2 digits
before they are read.  A signed year reads its whole digit run with `readNat` only after
`yearOf` has refused one with more than four significant digits, so the numeral is a run of
zeros and at most four digits.  `Field.parseDate` and `Field.parseClock` (`splitFirst`, not
tail recursive) only ever see 10 and 5 characters.
-/

namespace Tm
namespace LogStamp

open Cal (Instant Offset VInstant VOffset)

/-! ## Reading -/

/-- Why a `"t"` string is not a stamp. -/
inductive StampErr
  /-- fewer characters than the grammar needs -/
  | tooShort
  /-- not a date, or a date that does not exist -/
  | badDate
  /-- the date and the time are not separated by `T`, `t` or a space -/
  | badSeparator
  /-- not a time of day -/
  | badTime
  /-- a `.` with no digit after it -/
  | badFraction
  /-- not an offset, or an offset of a day or more -/
  | badOffset
  /-- characters after the offset -/
  | tooLong
  /-- the instant is before 0001-01-01T00:00:00Z, the origin of `Cal.Instant` -/
  | beforeOrigin
  /-- the instant is at or after 10000-01-01T00:00:00Z (`Cal.Instant.wf`, R10) -/
  | pastYear9999
deriving DecidableEq, Repr

/-- Rust's `char::is_whitespace`: the Unicode `White_Space` property, which `str::trim_start`
and chrono's `colon_or_space` use. -/
def isRustSpace (c : Char) : Bool :=
  c.toNat == 32 || (9 ≤ c.toNat && c.toNat ≤ 13) || c.toNat == 0x85 || c.toNat == 0xA0 ||
    c.toNat == 0x1680 || (0x2000 ≤ c.toNat && c.toNat ≤ 0x200A) || c.toNat == 0x2028 ||
    c.toNat == 0x2029 || c.toNat == 0x202F || c.toNat == 0x205F || c.toNat == 0x3000

/-- An offset's sign, `true` west of UTC: chrono's `timezone_offset` accepts `+`, `-` and
U+2212 MINUS SIGN. -/
def signOf : Char → Option Bool
  | '+' => some false
  | '-' => some true
  | '−' => some true
  | _ => none

/-- Exactly two decimal digits. -/
def twoDigits (l : List Char) : Option Nat := if l.length = 2 then readNat l else none

/-- `FixedOffset::east_opt` of `±(h·3600 + m·60)`: below a day, and `-00:00` is UTC. -/
def offsetOf (neg : Bool) (h m : Nat) : Except StampErr VOffset :=
  match Cal.mkOffset? (neg && h * 3600 + m * 60 != 0) (h * 3600 + m * 60) with
  | some o => .ok o
  | none => .error .badOffset

def utc : VOffset := ⟨Offset.utc, by decide⟩

/-- `parse_rfc3339`'s offset: `Z`, `z`, or a sign, `HH`, `:`, `MM`, then the end. -/
def rfcOffset : List Char → Except StampErr VOffset
  | [] => .error .tooShort
  | c :: t =>
    if c == 'Z' || c == 'z' then (if t.isEmpty then .ok utc else .error .tooLong)
    else match signOf c with
      | none => .error .badOffset
      | some neg =>
        if t.length < 5 then .error .tooShort
        else if 5 < t.length then .error .tooLong
        else if (t.drop 2).head? != some ':' then .error .badOffset
        else match twoDigits (t.take 2), twoDigits (t.drop 3) with
          | some h, some m => if m < 60 then offsetOf neg h m else .error .badOffset
          | _, _ => .error .badOffset

/-- `scan::nanosecond` after a `.`: at least one digit, the first nine scaled to nanoseconds,
the rest skipped.  Without a `.`, no nanoseconds and nothing consumed. -/
def fracOf : List Char → Except StampErr (Nat × List Char)
  | '.' :: t =>
    if (t.takeWhile Field.isDigitC).isEmpty then .error .badFraction
    else .ok ((readNat ((t.takeWhile Field.isDigitC).take 9)).getD 0
                * 10 ^ (9 - ((t.takeWhile Field.isDigitC).take 9).length),
              t.dropWhile Field.isDigitC)
  | s => .ok (0, s)

/-- Local time minus offset.  `base` counts whole days from 0000-12-31 (so `Day` `d` is base
`d + 1`), `clk` minutes and `sec` seconds into the local day; the UTC second is one day less
than `Cal.utcSecAt`'s reading of the shifted clock. -/
def build (base clk sec ns : Nat) (o : VOffset) : Except StampErr (VInstant × VOffset) :=
  match Cal.utcSecAt o.val (base * 86400 + clk * 60 + sec) with
  | none => .error .beforeOrigin
  | some u =>
    if u < 86400 then .error .beforeOrigin else
    match Cal.mkInstant? (u - 86400) ns with
    | some i => .ok (i, o)
    | none => .error .pastYear9999

/-- The one year-0 date a representable instant can read. -/
def year0Dec31 : List Char := ['0','0','0','0','-','1','2','-','3','1']

/-- A ten-character date as a base: `Field.parseDate`'s day plus one, or 0 for `0000-12-31`. -/
def dateBase (d : List Char) : Option Nat :=
  if d = year0Dec31 then some 0 else (Field.parseDate d).map (· + 1)

def sepOk : Option Char → Bool
  | some 'T' => true
  | some 't' => true
  | some ' ' => true
  | _ => false

/-- chrono 0.4.45 `format::parse::parse_rfc3339`. -/
def rfc3339 (s : List Char) : Except StampErr (VInstant × VOffset) :=
  if s.length < 19 then .error .tooShort else
  match dateBase (s.take 10) with
  | none => .error .badDate
  | some base =>
    if !sepOk (s.drop 10).head? then .error .badSeparator else
    match Field.parseClock ((s.drop 11).take 5) with
    | none => .error .badTime
    | some clk =>
      if (s.drop 16).head? != some ':' then .error .badTime else
      match readNat ((s.drop 17).take 2) with
      | none => .error .badTime
      | some sec =>
        if 60 < sec then .error .badTime else
        match fracOf (s.drop 19) with
        | .error e => .error e
        | .ok (ns, rest) =>
          match rfcOffset rest with
          | .error e => .error e
          | .ok o =>
            build base clk.val (if sec = 60 then 59 else sec)
              ((if sec = 60 then 1000000000 else 0) + ns) o

/-- `str::trim_start`. -/
def trimWs (s : List Char) : List Char := s.dropWhile isRustSpace

/-- `Item::Literal`: exactly `c`. -/
def lit (c : Char) (e : StampErr) : List Char → Except StampErr (List Char)
  | [] => .error .tooShort
  | x :: t => if x == c then .ok t else .error e

/-- An unsigned `Item::Numeric` of width `w`: whitespace, then one to `w` digits, in `[lo, hi]`
(`Parsed`'s setters' ranges). -/
def numIn (w lo hi : Nat) (e : StampErr) (s : List Char) : Except StampErr (Nat × List Char) :=
  match readNat (((trimWs s).take w).takeWhile Field.isDigitC) with
  | none => .error e
  | some v =>
    if lo ≤ v ∧ v ≤ hi then .ok (v, (trimWs s).drop (((trimWs s).take w).takeWhile Field.isDigitC).length)
    else .error e

/-- `%Y`: whitespace, then `-` or `+` with any number of digits, or one to four digits.  A
negative year is before the origin; `-0…0` is year 0; a signed year of more than four
significant digits is past 9999. -/
def yearOf (s : List Char) : Except StampErr (Nat × List Char) :=
  match trimWs s with
  | '-' :: t =>
    if (t.takeWhile Field.isDigitC).isEmpty then .error .badDate
    else if (t.takeWhile Field.isDigitC).all (· == '0') then .ok (0, t.dropWhile Field.isDigitC)
    else .error .beforeOrigin
  | '+' :: t =>
    if (t.takeWhile Field.isDigitC).isEmpty then .error .badDate
    else if 4 < ((t.takeWhile Field.isDigitC).dropWhile (· == '0')).length then .error .pastYear9999
    else .ok ((readNat (t.takeWhile Field.isDigitC)).getD 0, t.dropWhile Field.isDigitC)
  | _ => numIn 4 0 9999 .badDate s

/-- `%:z` in the generic parser: whitespace, a sign, two digits, any mix of `:` and whitespace,
two digits below 60, then the end (`format::parse::parse`'s `TOO_LONG`). -/
def fallbackOffset (s : List Char) : Except StampErr VOffset :=
  match trimWs s with
  | [] => .error .tooShort
  | c :: t =>
    match signOf c with
    | none => .error .badOffset
    | some neg =>
      match t with
      | h1 :: h2 :: t2 =>
        match twoDigits [h1, h2] with
        | none => .error .badOffset
        | some hh =>
          match t2.dropWhile (fun x => x == ':' || isRustSpace x) with
          | m1 :: m2 :: rest =>
            match twoDigits [m1, m2] with
            | some mm =>
              if mm < 60 then (if rest.isEmpty then offsetOf neg hh mm else .error .tooLong)
              else .error .badOffset
            | none => .error .badOffset
          | _ => .error .tooShort
      | _ => .error .tooShort

/-- chrono 0.4.45 `DateTime::parse_from_str(s, "%Y-%m-%dT%H:%M%:z")`. -/
def fallback (s0 : List Char) : Except StampErr (VInstant × VOffset) := do
  let (y, s) ← yearOf s0
  let s ← lit '-' .badDate s
  let (mo, s) ← numIn 2 1 12 .badDate s
  let s ← lit '-' .badDate s
  let (d, s) ← numIn 2 1 31 .badDate s
  let s ← lit 'T' .badSeparator s
  let (h, s) ← numIn 2 0 23 .badTime s
  let s ← lit ':' .badTime s
  let (mi, s) ← numIn 2 0 59 .badTime s
  let o ← fallbackOffset s
  if y = 0 ∧ mo = 12 ∧ d = 31 then build 0 (h * 60 + mi) 0 0 o
  else if Cal.Date.valid ⟨y, mo, d⟩ then build (Cal.toDay ⟨y, mo, d⟩ + 1) (h * 60 + mi) 0 0 o
  else .error .badDate

/-- **The stamp reader**: the fork's `parse_timestamp`.  The one smart constructor for a
stamp (R10): an accepted stamp is a `VInstant` and a `VOffset`. -/
def parseStamp (s : List Char) : Except StampErr (VInstant × VOffset) :=
  match rfc3339 s with
  | .ok r => .ok r
  | .error e =>
    match fallback s with
    | .ok r => .ok r
    | .error _ => .error e

/-- What a read accepted, as plain values (for decided witnesses: `Except` has no
`DecidableEq`). -/
def accepted : Except StampErr (VInstant × VOffset) → Option (Instant × Offset)
  | .ok (i, o) => some (i.val, o.val)
  | .error _ => none

/-! ## Writing -/

/-- 10000-01-01T00:00:00Z in `Cal.Instant` seconds (`Cal.Instant.wf`'s bound). -/
def yearEnd : Nat := 315537897600

def year10000Jan1 : List Char := ['+','1','0','0','0','0','-','0','1','-','0','1']

/-- chrono's `naive_local()`: the local date's text and the seconds into the local day.  West of
UTC in the origin's first day the date is 0000-12-31; east of UTC in 9999's last day it is
`+10000-01-01`, as `write_rfc3339` and `%Y` write a year past 9999. -/
def localDateTod (i : Instant) (o : Offset) : List Char × Nat :=
  if o.west && decide (i.sec < o.sec) then (year0Dec31, 86400 - (o.sec - i.sec))
  else if Cal.localSecAt o i < yearEnd then
    (Field.renderDate (Cal.localSecAt o i / 86400), Cal.localSecAt o i % 86400)
  else (year10000Jan1, Cal.localSecAt o i - yearEnd)

def clockOf (tod : Nat) : Field.Clock := ⟨tod / 60 % 1440, Nat.mod_lt _ (by decide)⟩

/-- `OffsetFormat { precision: Minutes, colons: Colon, allow_zulu: false }`: the sign of
`local_minus_utc` (`+` at zero), then the offset rounded to the nearest minute. -/
def renderOffset (o : Offset) : List Char :=
  (if o.west && o.sec != 0 then '-' else '+') ::
    (padTo 2 ((o.sec + 30) / 60 / 60) ++ ':' :: padTo 2 ((o.sec + 30) / 60 % 60))

/-- **The stamp writer**: the fork's `fmt_timestamp`.  Whole seconds; a leap second is second
`60`; the fraction is dropped. -/
def renderStamp (i : VInstant) (o : VOffset) : List Char :=
  (localDateTod i.val o.val).1 ++ 'T' ::
    (Field.renderClock (clockOf (localDateTod i.val o.val).2) ++ ':' ::
      (padTo 2 ((localDateTod i.val o.val).2 % 60 + (if 1000000000 ≤ i.val.ns then 1 else 0))
        ++ renderOffset o.val))

/-- **The `tm log` column**: `e.t.format("%Y-%m-%d %H:%M")`, the local clock in the written
offset. -/
def displayStamp (i : VInstant) (o : VOffset) : List Char :=
  (localDateTod i.val o.val).1 ++ ' ' :: Field.renderClock (clockOf (localDateTod i.val o.val).2)

/-! ## The order -/

/-- chrono's `DateTime<FixedOffset>` order: the instants', in `Cal.Instant`'s (chrono's) order.
The offset never enters. -/
def stampBefore (a b : VInstant × VOffset) : Bool := decide (a.1.val < b.1.val)

theorem stampBefore_iff (a b : VInstant × VOffset) : stampBefore a b = true ↔ a.1.val < b.1.val := by
  simp [stampBefore]

theorem stampBefore_ignores_the_offset (i j : VInstant) (o o' p p' : VOffset) :
    stampBefore (i, o) (j, p) = stampBefore (i, o') (j, p') := rfl

theorem stampBefore_irrefl (a b : VInstant × VOffset) (h : a.1 = b.1) : stampBefore a b = false := by
  simp only [stampBefore, h, decide_eq_false_iff_not]; exact Cal.Instant.lt_irrefl _

/-! ## The round trip -/

theorem renderOffset_length (o : Offset) (h : o.sec < 86400) : (renderOffset o).length = 6 := by
  unfold renderOffset
  simp only [List.length_cons, List.length_append]
  rw [Field.padTo2_length _ (by omega), Field.padTo2_length _ (by omega)]

theorem rfcOffset_renderOffset (o : VOffset) (hmin : o.val.sec % 60 = 0)
    (hutc : o.val.sec = 0 → o.val.west = false) : rfcOffset (renderOffset o.val) = .ok o := by
  obtain ⟨⟨w, s⟩, hw⟩ := o
  have hs : s < 86400 := by simpa [Offset.wf] using hw
  simp only at hmin hutc
  have h30 : (s + 30) / 60 = s / 60 := by omega
  have hsign : signOf (if (w && s != 0) = true then '-' else '+') = some (w && s != 0) := by
    cases w <;> by_cases h0 : s = 0 <;> simp [h0, signOf]
  unfold renderOffset
  simp only [h30]
  have hz : ((if (w && s != 0) = true then '-' else '+') == 'Z' ||
      (if (w && s != 0) = true then '-' else '+') == 'z') = false := by
    split <;> decide
  simp only [rfcOffset, hz, Bool.false_eq_true, if_false, hsign]
  have hl : (padTo 2 (s / 60 / 60) ++ ':' :: padTo 2 (s / 60 % 60)).length = 5 := by
    simp only [List.length_cons, List.length_append]
    rw [Field.padTo2_length _ (by omega), Field.padTo2_length _ (by omega)]
  rw [hl]
  have hd2 : (padTo 2 (s / 60 / 60) ++ ':' :: padTo 2 (s / 60 % 60)).drop 2 =
      ':' :: padTo 2 (s / 60 % 60) :=
    List.drop_left' (Field.padTo2_length _ (by omega))
  have ht2 : (padTo 2 (s / 60 / 60) ++ ':' :: padTo 2 (s / 60 % 60)).take 2 = padTo 2 (s / 60 / 60) :=
    List.take_left' (Field.padTo2_length _ (by omega))
  have hd3 : (padTo 2 (s / 60 / 60) ++ ':' :: padTo 2 (s / 60 % 60)).drop 3 = padTo 2 (s / 60 % 60) := by
    rw [show 3 = 2 + 1 from rfl, ← List.drop_drop, hd2]; rfl
  simp only [hd2, ht2, hd3, twoDigits, Field.padTo2_length _ (show s / 60 / 60 < 100 by omega),
    Field.padTo2_length _ (show s / 60 % 60 < 100 by omega), readNat_padTo]
  have hm60 : s / 60 % 60 < 60 := Nat.mod_lt _ (by decide)
  simp only [List.head?_cons, bne_self_eq_false, Bool.false_eq_true, if_false, if_true,
    Nat.lt_irrefl, hm60]
  unfold offsetOf Cal.mkOffset?
  have he : s / 60 / 60 * 3600 + s / 60 % 60 * 60 = s := by omega
  have hww : (w && s != 0) = w := by
    cases w
    · rfl
    · by_cases h0 : s = 0
      · exact absurd (hutc h0) (by simp)
      · simp [h0]
  simp only [he, hww]
  rw [dif_pos hw]

theorem year_of_a_day_before_the_end (n : Nat) (h : n < yearEnd / 86400) : Field.dayWf n = true := by
  have hy : (Cal.ofDay n).year = Cal.yearOfZ (n + 366) := rfl
  unfold yearEnd at h
  have hm := Cal.yearOfZ_mono (show n + 366 ≤ 3652058 + 366 by omega)
  have h9 : Cal.yearOfZ (3652058 + 366) = 9999 := by decide
  simp only [Field.dayWf, decide_eq_true_eq, hy]; omega

theorem dateBase_renderDate (n : Nat) (h : Field.dayWf n = true) :
    dateBase (Field.renderDate n) = some (n + 1) := by
  have hp := Field.parse_render_date n h
  have hne : Field.renderDate n ≠ year0Dec31 := by
    intro he
    have h0 : Field.parseDate year0Dec31 = none := by decide
    rw [he, h0] at hp; cases hp
  simp [dateBase, hne, hp]

theorem renderDate_length (n : Nat) (h : Field.dayWf n = true) : (Field.renderDate n).length = 10 := by
  have hy : (Cal.ofDay n).year < 10000 := by simpa [Field.dayWf] using h
  unfold Field.renderDate
  simp only [List.length_append, List.length_cons]
  rw [Field.padTo4_length _ hy, Field.padTo2_length _ (Field.ofDay_month_bounds n).2,
    Field.padTo2_length _ (Field.ofDay_day_bounds n).2]

/-- What the local-date half of a render hands the reader: a ten-character date naming a base,
a time of day, the UTC second one day on, and second 59 under a leap second. -/
theorem localDateTod_spec (i : VInstant) (o : VOffset) (hmin : o.val.sec % 60 = 0)
    (hend : o.val.west = true ∨ i.val.sec + o.val.sec < yearEnd) :
    ∃ b, (localDateTod i.val o.val).2 < 86400 ∧ ((localDateTod i.val o.val).1).length = 10 ∧
      dateBase (localDateTod i.val o.val).1 = some b ∧
      Cal.utcSecAt o.val (b * 86400 + (localDateTod i.val o.val).2) = some (i.val.sec + 86400) ∧
      (1000000000 ≤ i.val.ns → (localDateTod i.val o.val).2 % 60 = 59) := by
  obtain ⟨⟨s, ns⟩, hi⟩ := i
  obtain ⟨⟨w, os⟩, ho⟩ := o
  have hos : os < 86400 := by simpa [Offset.wf] using ho
  have hiw : (ns < 2000000000 ∧ (ns < 1000000000 ∨ s % 60 = 59)) ∧ s < 315537897600 := by
    simpa [Cal.Instant.wf] using hi
  simp only at hmin hend ⊢
  unfold localDateTod
  by_cases h1 : (w && decide (s < os)) = true
  · have hw : w = true := by simp at h1; exact h1.1
    have hlt : s < os := by simp at h1; exact h1.2
    simp only [h1, if_true]
    refine ⟨0, by omega, rfl, by simp [dateBase], ?_, ?_⟩
    · simp [Cal.utcSecAt, hw]; omega
    · intro hns; omega
  · simp only [h1, Bool.false_eq_true, if_false]
    have hl : Cal.localSecAt ⟨w, os⟩ ⟨s, ns⟩ < yearEnd := by
      unfold Cal.localSecAt yearEnd; cases w
      · simp only [Bool.false_eq_true, if_false]; simpa [yearEnd] using hend
      · simp only [if_true]; omega
    simp only [hl, if_true]
    have hwf := year_of_a_day_before_the_end (Cal.localSecAt ⟨w, os⟩ ⟨s, ns⟩ / 86400)
      (by unfold yearEnd at hl ⊢; omega)
    refine ⟨Cal.localSecAt ⟨w, os⟩ ⟨s, ns⟩ / 86400 + 1, Nat.mod_lt _ (by decide),
      renderDate_length _ hwf, dateBase_renderDate _ hwf, ?_, ?_⟩
    · unfold Cal.utcSecAt Cal.localSecAt
      cases w
      · simp only [Bool.false_eq_true, if_false]
        rw [if_pos (by omega)]; congr 1; omega
      · simp at h1
        simp only [if_true]; congr 1; omega
    · intro hns
      have h59 : s % 60 = 59 := by omega
      unfold Cal.localSecAt
      cases w
      · simp only [Bool.false_eq_true, if_false]; omega
      · simp at h1
        simp only [if_true]; omega

theorem fracOf_renderOffset (o : Offset) : fracOf (renderOffset o) = .ok (0, renderOffset o) := by
  unfold renderOffset; split <;> rfl

/-- The RFC 3339 reader reads back every stamp the writer writes in whole seconds or on a leap
second, with a whole-minute offset, `+00:00` for UTC, and a local clock before year 10000.  The
proof reads the render by position: `Field.parse_render_date` and `Field.parse_render_clock`
are the date and the clock, `readNat_padTo` the seconds, `rfcOffset_renderOffset` the offset.

(`Nat` additions of `86400` are rewritten, never simplified by instance: `simp` evaluating the
decidable `x + 86400 < 86400` for a variable `x` sends the kernel into a deep recursion.) -/
theorem rfc3339_renderStamp (i : VInstant) (o : VOffset)
    (hns : i.val.ns = 0 ∨ i.val.ns = 1000000000) (hmin : o.val.sec % 60 = 0)
    (hutc : o.val.sec = 0 → o.val.west = false)
    (hend : o.val.west = true ∨ i.val.sec + o.val.sec < yearEnd) :
    rfc3339 (renderStamp i o) = .ok (i, o) := by
  obtain ⟨b, hT, hD, hbase, hutcsec, hleap⟩ := localDateTod_spec i o hmin hend
  have hos : o.val.sec < 86400 := by simpa [Offset.wf] using o.property
  generalize hp : localDateTod i.val o.val = p at hT hD hbase hutcsec hleap
  obtain ⟨D, T⟩ := p
  simp only at hT hD hbase hutcsec hleap
  have hRO := renderOffset_length o.val hos
  have hRC := Field.renderClock_length (clockOf T)
  let lp : Nat := if 1000000000 ≤ i.val.ns then 1 else 0
  have hv : T % 60 + lp < 100 := by
    have : lp ≤ 1 := by simp only [lp]; split <;> omega
    have : T % 60 < 60 := Nat.mod_lt _ (by decide); omega
  have hPS := Field.padTo2_length (T % 60 + lp) hv
  have hr : renderStamp i o =
      (D ++ ['T'] ++ Field.renderClock (clockOf T) ++ [':'] ++ padTo 2 (T % 60 + lp)) ++
        renderOffset o.val := by
    simp [renderStamp, hp, lp]
  have hlen : ¬ (renderStamp i o).length < 19 := by
    rw [hr]; simp only [List.length_append, List.length_cons, List.length_nil, hD, hRC, hPS, hRO]; omega
  have ht10 : (renderStamp i o).take 10 = D := by
    rw [hr]; simp only [List.append_assoc]; exact List.take_left' hD
  have hd10 : (renderStamp i o).drop 10 =
      'T' :: (Field.renderClock (clockOf T) ++ ':' :: (padTo 2 (T % 60 + lp) ++ renderOffset o.val)) := by
    rw [hr]; simp only [List.append_assoc, List.cons_append, List.nil_append]; exact List.drop_left' hD
  have hd11 : (renderStamp i o).drop 11 =
      Field.renderClock (clockOf T) ++ ':' :: (padTo 2 (T % 60 + lp) ++ renderOffset o.val) := by
    rw [show 11 = 10 + 1 from rfl, ← List.drop_drop, hd10]; rfl
  have hc5 : ((renderStamp i o).drop 11).take 5 = Field.renderClock (clockOf T) := by
    rw [hd11]; exact List.take_left' hRC
  have hd16 : (renderStamp i o).drop 16 = ':' :: (padTo 2 (T % 60 + lp) ++ renderOffset o.val) := by
    rw [show 16 = 11 + 5 from rfl, ← List.drop_drop, hd11]; exact List.drop_left' hRC
  have hd17 : (renderStamp i o).drop 17 = padTo 2 (T % 60 + lp) ++ renderOffset o.val := by
    rw [show 17 = 16 + 1 from rfl, ← List.drop_drop, hd16]; rfl
  have hs2 : ((renderStamp i o).drop 17).take 2 = padTo 2 (T % 60 + lp) := by
    rw [hd17]; exact List.take_left' hPS
  have hd19 : (renderStamp i o).drop 19 = renderOffset o.val := by
    rw [show 19 = 17 + 2 from rfl, ← List.drop_drop, hd17]; exact List.drop_left' hPS
  unfold rfc3339
  rw [if_neg hlen, ht10, hbase, hd10, hc5, Field.parse_render_clock, hd16, hs2, readNat_padTo, hd19,
    fracOf_renderOffset]
  simp only [sepOk, List.head?_cons, Bool.not_true, Bool.false_eq_true, if_false, bne_self_eq_false]
  rw [rfcOffset_renderOffset o hmin hutc]
  have hclk : (clockOf T).val = T / 60 := by
    show T / 60 % 1440 = T / 60; omega
  have hmk : Cal.mkInstant? i.val.sec i.val.ns = some i := by
    unfold Cal.mkInstant?; rw [dif_pos i.property]
  have hnot : ¬ (i.val.sec + 86400 < 86400) := by omega
  rcases hns with h0 | h1
  · have hlp : lp = 0 := by simp only [lp, h0]; exact if_neg (by omega)
    have hlt : ¬ 60 < T % 60 + lp := by
      rw [hlp]; have := Nat.mod_lt T (show 60 > 0 by decide); omega
    have hne : ¬ (T % 60 + lp = 60) := by
      rw [hlp]; have := Nat.mod_lt T (show 60 > 0 by decide); omega
    simp only [hlt, hne, if_false, build, hclk]
    rw [show b * 86400 + T / 60 * 60 + (T % 60 + lp) = b * 86400 + T by rw [hlp]; omega, hutcsec]
    dsimp only
    rw [if_neg hnot, Nat.add_sub_cancel, Nat.add_zero]
    rw [show Cal.mkInstant? i.val.sec 0 = some i from h0 ▸ hmk]
  · have hlp : lp = 1 := by simp only [lp, h1]; exact if_pos (by omega)
    have h59 := hleap (by omega)
    have he : T % 60 + lp = 60 := by rw [hlp]; omega
    simp only [he, if_true, build, hclk]
    rw [show b * 86400 + T / 60 * 60 + 59 = b * 86400 + T by omega, hutcsec]
    dsimp only
    rw [if_neg hnot, Nat.add_sub_cancel, Nat.add_zero]
    rw [show Cal.mkInstant? i.val.sec 1000000000 = some i from h1 ▸ hmk, if_neg (Nat.lt_irrefl 60)]

/-- **`parseStamp_renderStamp`** (design §5.3 and §15, B2 in-step), restated.  The reader reads
back what the writer writes, for a stamp in whole seconds **or on a leap second** (chrono writes
second `60`, and reads it back as 59 plus 10⁹ ns), a whole-minute offset, UTC written `+00:00`,
and a local clock before year 10000.  §15 states it without `hend`, and as stated it is false:
`parseStamp_renderStamp_fails_past_year_9999`.  `hns` is §15's `ns = 0` widened by the leap
second. -/
theorem parseStamp_renderStamp (i : VInstant) (o : VOffset)
    (hns : i.val.ns = 0 ∨ i.val.ns = 1000000000) (hmin : o.val.sec % 60 = 0)
    (hutc : o.val.sec = 0 → o.val.west = false)
    (hend : o.val.west = true ∨ i.val.sec + o.val.sec < yearEnd) :
    parseStamp (renderStamp i o) = .ok (i, o) := by
  unfold parseStamp; rw [rfc3339_renderStamp i o hns hmin hutc hend]

/-- **Refuted** (§15's `parseStamp_renderStamp` without a year bound).  East of UTC in the last
seconds of 9999 the local clock is in year 10000, `fmt_timestamp` writes
`+10000-01-01T00:00:59+00:01`, and neither chrono's RFC 3339 reader (whose year is four digits)
nor its fallback (which has no seconds) reads it back; the kernel's reader refuses it too. -/
theorem parseStamp_renderStamp_fails_past_year_9999 :
    ∃ (i : VInstant) (o : VOffset), i.val.ns = 0 ∧ o.val.sec % 60 = 0 ∧ o.val.west = false ∧
      renderStamp i o = ['+','1','0','0','0','0','-','0','1','-','0','1','T','0','0',':','0','0',':',
        '5','9','+','0','0',':','0','1'] ∧
      accepted (parseStamp (renderStamp i o)) = none :=
  ⟨⟨⟨315537897599, 0⟩, by decide⟩, ⟨⟨false, 60⟩, by decide⟩, rfl, rfl, rfl, by decide, by decide⟩

/-! ## Witnesses: the fork's own spellings -/

/-- `fmt_timestamp`'s doc example, `2026-09-07T06:05:00-05:00`, and a UTC stamp, which
`use_z = false` writes `+00:00`. -/
theorem renderStamp_is_fmt_timestamp :
    renderStamp ⟨⟨63924375900, 0⟩, by decide⟩ ⟨⟨true, 18000⟩, by decide⟩ =
      ['2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0','-','0','5',':','0','0'] ∧
    renderStamp ⟨⟨63924433200, 0⟩, by decide⟩ ⟨⟨false, 0⟩, by decide⟩ =
      ['2','0','2','6','-','0','9','-','0','8','T','0','3',':','0','0',':','0','0','+','0','0',':','0','0'] :=
  ⟨by decide, by decide⟩

/-- A leap second is written as second `60`, its fraction dropped (`SecondsFormat::Secs`), and
the `tm log` column shows its minute. -/
theorem renderStamp_writes_a_leap_second_as_60 :
    renderStamp ⟨⟨63618825599, 1500000000⟩, by decide⟩ ⟨⟨false, 0⟩, by decide⟩ =
      ['2','0','1','6','-','1','2','-','3','1','T','2','3',':','5','9',':','6','0','+','0','0',':','0','0'] ∧
    displayStamp ⟨⟨63618825599, 1500000000⟩, by decide⟩ ⟨⟨false, 0⟩, by decide⟩ =
      ['2','0','1','6','-','1','2','-','3','1',' ','2','3',':','5','9'] :=
  ⟨by decide, by decide⟩

/-- `displayStamp` is the local clock in the written offset: the CDT stamp shows 06:05 on
2026-09-07, not its UTC 11:05. -/
theorem displayStamp_is_the_written_clock :
    displayStamp ⟨⟨63924375900, 0⟩, by decide⟩ ⟨⟨true, 18000⟩, by decide⟩ =
      ['2','0','2','6','-','0','9','-','0','7',' ','0','6',':','0','5'] := by
  decide

/-- The year-0 day: one minute west of UTC, the origin reads `0000-12-31T23:59:00-00:01`, as
chrono writes it, and the reader reads it back. -/
theorem the_origin_west_of_utc_is_year_zero :
    renderStamp ⟨⟨0, 0⟩, by decide⟩ ⟨⟨true, 60⟩, by decide⟩ =
      ['0','0','0','0','-','1','2','-','3','1','T','2','3',':','5','9',':','0','0','-','0','0',':','0','1'] ∧
    accepted (parseStamp ['0','0','0','0','-','1','2','-','3','1','T','2','3',':','5','9',':','0','0',
      '-','0','0',':','0','1']) = some (⟨0, 0⟩, ⟨true, 60⟩) :=
  ⟨by decide, by decide⟩

/-- **The order witness, in chrono's order** (design §5.3's `stamp_order_is_the_instant_order`).
`2026-09-08T03:00:00+00:00` and `2026-09-07T22:00:00-05:00` read as one instant in two offsets,
and neither is before the other, although their written clocks are five hours apart (cheat 92
is the clock-ordered cheat). -/
theorem stamp_order_is_the_instant_order :
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','8','T','0','3',':','0','0',':','0','0',
      '+','0','0',':','0','0']) = some (⟨63924433200, 0⟩, ⟨false, 0⟩) ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','2','2',':','0','0',':','0','0',
      '-','0','5',':','0','0']) = some (⟨63924433200, 0⟩, ⟨true, 18000⟩) ∧
    stampBefore (⟨⟨63924433200, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
      (⟨⟨63924433200, 0⟩, by decide⟩, ⟨⟨true, 18000⟩, by decide⟩) = false ∧
    stampBefore (⟨⟨63924433200, 0⟩, by decide⟩, ⟨⟨true, 18000⟩, by decide⟩)
      (⟨⟨63924433200, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩) = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **A leap second is before the next second** (carried note 1).  `2016-12-31T23:59:60.5Z`
reads as second 63,618,825,599 with 1.5·10⁹ ns, and it is before `2017-01-01T00:00:00Z` in
chrono's order, although its nanosecond count is the larger. -/
theorem a_leap_second_stamp_is_before_the_next_second :
    accepted (parseStamp ['2','0','1','6','-','1','2','-','3','1','T','2','3',':','5','9',':','6','0',
      '.','5','Z']) = some (⟨63618825599, 1500000000⟩, ⟨false, 0⟩) ∧
    accepted (parseStamp ['2','0','1','7','-','0','1','-','0','1','T','0','0',':','0','0',':','0','0',
      'Z']) = some (⟨63618825600, 0⟩, ⟨false, 0⟩) ∧
    stampBefore (⟨⟨63618825599, 1500000000⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩) (⟨⟨63618825600, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩) = true ∧
    (⟨63618825600, 0⟩ : Instant).nanos < (⟨63618825599, 1500000000⟩ : Instant).nanos :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The RFC 3339 reader's other spellings: a lower-case `t`, a space, a lower-case `z`,
`-00:00` (which is UTC), U+2212 as the sign, and ten fraction digits (the tenth skipped). -/
theorem parseStamp_reads_the_rfc3339_spellings :
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','8','t','0','3',':','0','0',':','0','0','z'])
      = some (⟨63924433200, 0⟩, ⟨false, 0⟩) ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','8',' ','0','3',':','0','0',':','0','0',
      '-','0','0',':','0','0']) = some (⟨63924433200, 0⟩, ⟨false, 0⟩) ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','2','2',':','0','0',':','0','0',
      '−','0','5',':','0','0']) = some (⟨63924433200, 0⟩, ⟨true, 18000⟩) ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','8','T','0','3',':','0','0',':','0','0',
      '.','1','2','3','4','5','6','7','8','9','9','Z']) = some (⟨63924433200, 123456789⟩, ⟨false, 0⟩) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The fallback: no seconds (`2026-09-07T06:05-05:00`), and chrono's generic parser's
tolerance, one-digit fields after whitespace and a space for the offset's colon. -/
theorem parseStamp_reads_the_fallback :
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',
      '-','0','5',':','0','0']) = some (⟨63924375900, 0⟩, ⟨true, 18000⟩) ∧
    accepted (parseStamp [' ','2','0','2','6','-',' ','9','-','7','T','6',':','5',' ',
      '-','0','5',' ','0','0']) = some (⟨63924375900, 0⟩, ⟨true, 18000⟩) :=
  ⟨by decide, by decide⟩

/-- **Refusals (R10)**: a date that does not exist, hour 24, second 61, an offset of a day, a
minute 60 in the offset, text after the offset, the instant before the origin, and year 10000
through the fallback's sign. -/
theorem parseStamp_refuses_what_is_not_a_stamp :
    accepted (parseStamp ['2','0','2','6','-','0','2','-','2','9','T','0','0',':','0','0',':','0','0','Z']) = none ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','2','4',':','0','0',':','0','0','Z']) = none ∧
    accepted (parseStamp ['2','0','1','6','-','1','2','-','3','1','T','2','3',':','5','9',':','6','1','Z']) = none ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0',
      '+','2','4',':','0','0']) = none ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0',
      '+','0','5',':','6','0']) = none ∧
    accepted (parseStamp ['2','0','2','6','-','0','9','-','0','7','T','0','6',':','0','5',':','0','0','Z','x']) = none ∧
    accepted (parseStamp ['0','0','0','1','-','0','1','-','0','1','T','0','0',':','0','0',':','0','0',
      '+','0','0',':','0','1']) = none ∧
    accepted (parseStamp ['+','1','0','0','0','0','-','0','1','-','0','1','T','0','0',':','0','0',
      '+','0','0',':','0','0']) = none :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end LogStamp
end Tm
