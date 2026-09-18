import TmKernel.Tree
import TmKernel.Replay
/-!
# Recur — §5's occurrences, inside the kernel (stage 6, track K, step K3b)

Fork-point `tm-core/src/recur.rs` is the oracle, read by function name:
`recur::instances`, `instance_info`, `is_mandatory`, `today_instances`,
`after_done_state`, `waiting_state`, and the private `calendar_instances`,
`after_done_instances`, `on_event_instances`, `one_off_instances`,
`rule_occurrences`, `window_on`, `span`, `close_on`, `status_of`,
`logged_status`, `next_ordinal`, `completion_count`, `logged_instances`.

**What this module is for.**  Design §12's F2 row and §14.1's `K3` row: "the
recurrence family … read inside the kernel".  Four of D27's nine candidate
facts — `due`, `overdue`, `mandatory` and `window` — are not properties of a
*line*, they are properties of the *occurrence* a line has today, and nothing
in the kernel could name an occurrence before this module.  `Look.Cand` takes
them from the host (README gap 113); this is the half that has to exist before
they can stop being taken.

**What it is NOT.**  It collects no candidates and it ranks nothing: `Cand` is
still built by the host and `readCand` still decodes the nine fields off the
wire.  **Nothing in the shipped binary calls anything here** — `Boundary.lean`
has no planner or candidate derivation on this module, so no verb reaches it.
That sentence is a measurement, not an expectation: it was checked by grepping
the host path and by driving `tm plan`, `tm now`, `tm review day` and `tm drop`
on a real tree (README, this step's block).  W-15 recorded the opposite of what
its binary did by not doing exactly that.

## The one representation decision

Every instant here is a **local wall clock** (`LocalT`): seconds since the
calendar origin in the plan's own zone, which is precisely what fork
`NaiveDateTime` is in `recur.rs` ("Instance windows and dues are wall-clock
`Naive*` values in `cfg.tz`, exactly as the line writes them").  It is
`Cal.instantOf`'s own local second, `d * 86400 + c.val * 60`, so a caller turns
an absolute instant into one with `Cal.localSec` and never with a second
conversion of its own.

Seconds and not minutes, although every value this module *builds* lands on a
whole minute: `today_instances` compares a close against `now`, and `now` has
seconds in it.  `close_of(i) >= now` is **not** preserved by flooring `now` to
the minute (`a_close_at_or_after_now_needs_the_seconds` is the witness), so the
seconds stay.

## D9-21, the recursion rule

Three fueled walks, each bounded by the range the caller fixes and each
carrying a length bound: `eachDayGo` (one step per day), `monthsGo` (one per
month), `mondaysGo` (one per week).  `ruleOccurrences` is those three and
nothing else recurses over a range.  Everything else walks a list through core:
`loggedInstances` is `filterMap` over `Facts.instancesOf` then stage 5's own
`Replay.insSort`; `nextOrdinal` and `completionCount` are `filterMap`/`filter`
and a `foldl`; `todayInstances` is `filterMap` over the ids given
(`todayInstances_length_le`).  `charsLe` recurses once per character of an
`inst` key, which the log's own line guard bounds.  No new `@[csimp]` twin is
owed: nothing here is a hand-written structural recursion over a wire list.

**R10.**  This module adds no wire type and decodes nothing: `InstKey`, `Inst`,
`InstInfo`, `AfterDoneSt` and `WaitingSt` are *derived* values, every field of
which comes from a plan the loader already bounded or a replay the log guard
already bounded.
-/

namespace Tm
namespace Recur

open Field (Shape WindowRange Clock DT Dur Moment AfterDone OnEvent)

/-! ## The local wall clock -/

/-- **A local wall-clock instant**: seconds since the calendar origin, read in
the plan's zone.  Fork `NaiveDateTime`.  `Cal.instantOf` builds an absolute
instant from `d * 86400 + c.val * 60`; this is that number. -/
abbrev LocalT := Nat

/-- Fork `NaiveDateTime::date()`. -/
def dateOfT (t : LocalT) : Nat := t / 86400

/-- A day and a clock as a local instant. -/
def atClock (d : Nat) (c : Clock) : LocalT := d * 86400 + c.val * 60

/-- Fork `end_of_day`: `23:59:00`, which is what `close_on` gives a shapeless
item. -/
def endOfDay (d : Nat) : LocalT := d * 86400 + 1439 * 60

theorem dateOfT_atClock (d : Nat) (c : Clock) : dateOfT (atClock d c) = d := by
  unfold dateOfT atClock
  have hc : c.val * 60 < 86400 := by have := c.isLt; omega
  rw [Nat.mul_comm d 86400, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hc]
  rfl

/-- **Why `LocalT` is seconds and not minutes.**  Both strict comparisons this
module makes against `now` survive flooring `now` to the minute — `not_yet`'s
`start > now` and `last_chance`'s `now < close`, which is `⌊n/60⌋ < c ↔ n < 60c`
— but `today_instances`' own filter asks `close_of(i) >= now`, and that one does
**not**: at `close = 00:01` and `now = 00:01:01` the fork says the chance is
gone and the floored reading says it is open.  So the seconds stay. -/
theorem a_close_at_or_after_now_needs_the_seconds :
    (∀ c n : Nat, n / 60 < c ↔ n < 60 * c) ∧ (∃ c n : Nat, 60 * c < n ∧ n / 60 ≤ c) :=
  ⟨fun _ _ => by omega, ⟨1, 61, by omega, by omega⟩⟩

theorem dateOfT_endOfDay (d : Nat) : dateOfT (endOfDay d) = d := by
  unfold dateOfT endOfDay
  rw [Nat.mul_comm d 86400, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
  rfl

/-! ## An instance key -/

/-- Fork `model::InstanceKey`: a calendar occurrence is keyed by its date, an
ordinal one by its number. -/
inductive InstKey
  | date (d : Nat)
  | nth  (n : Nat)
deriving DecidableEq, Repr, Inhabited

/-- Fork `InstanceKey`'s `Display` — the `inst` string a log line carries. -/
def renderInstKey : InstKey → List Char
  | .date d => Field.renderDate d
  | .nth n  => '#' :: digitsOf n

/-- Fork `parse_instance_key`.  The date arm is `Log.instDate?`, the kernel's
one reader of "is this log `inst` a date" (`factsView` asks it the same way);
reading it a second way here is the defect AGENTS §5.3 is about. -/
def parseInstKey (s : List Char) : Option InstKey :=
  match s with
  | '#' :: t => (readNat t).map InstKey.nth
  | _        => (Log.instDate? s).map InstKey.date

/-- An ordinal key round-trips. -/
theorem parseInstKey_renderInstKey_nth (n : Nat) :
    parseInstKey (renderInstKey (.nth n)) = some (.nth n) := by
  show (readNat (digitsOf n)).map InstKey.nth = some (.nth n)
  rw [readNat_digitsOf]
  rfl

/-- **The ordering the fork sorts logged instances by** (`out.sort_by_key(|i| i.key)`):
`InstanceKey` derives `Ord` over `Date(NaiveDate)` before `Nth(u32)`, so every
dated key precedes every ordinal one and each family is in its own order. -/
def InstKey.le : InstKey → InstKey → Bool
  | .date a, .date b => decide (a ≤ b)
  | .date _, .nth _  => true
  | .nth _,  .date _ => false
  | .nth a,  .nth b  => decide (a ≤ b)

/-! ## One occurrence -/

/-- Fork `model::Instance`.  `due` is the end of the *on-time* chance; `window`
is the whole stretch it may be placed in. -/
structure Inst where
  item   : List Char
  key    : InstKey
  due    : Option LocalT
  window : Option (LocalT × LocalT)
  status : Log.InstanceStatus
deriving DecidableEq, Repr

/-- Fork `close_of`. -/
def Inst.closeAt (x : Inst) : Option LocalT := (x.window.map Prod.snd).or x.due

/-- Fork `start_of`. -/
def Inst.startAt (x : Inst) : Option LocalT := (x.window.map Prod.fst).or x.due

/-- Fork `is_actionable`: `Missed` only ever comes from the log, and both it and
`Pending` are still to be done. -/
def isActionable : Log.InstanceStatus → Bool
  | .pending | .missed => true
  | _                  => false

/-- Fork `recur::InstanceInfo` — the planner-facing flags that travel beside an
instance. -/
structure InstInfo where
  mandatory   : Bool
  lastChance  : Bool
  overdue     : Bool
  carriedFrom : Option Nat
  deferred    : Bool
  notYet      : Bool
  durMin      : Option Nat
deriving DecidableEq, Repr, Inhabited


/-! ## §5's calendar rules — `rule_occurrences`

Three fueled walks, one per shape of loop the fork writes.  Each takes its fuel
from the range the caller fixes, and each has a length bound below (D9-21).
`add_days`' saturation guard (`if next == monday { break }`, for
`NaiveDate::MAX`) has no counterpart: a `Nat` is a `Nat` and `mon + 7` is always
the next Monday. -/

/-- Fork `each_day`: one step per day of the inclusive range, keeping the days
`f` accepts as one-day occurrences.  `lo > hi` is no days, which is the guard
`instances` applies before it dispatches. -/
def eachDayGo (f : Nat → Bool) : Nat → Nat → List (Nat × Nat)
  | 0,     _ => []
  | k + 1, d => (if f d then [(d, d)] else []) ++ eachDayGo f k (d + 1)

def eachDay (lo hi : Nat) (f : Nat → Bool) : List (Nat × Nat) := eachDayGo f (hi + 1 - lo) lo

theorem eachDayGo_length_le (f : Nat → Bool) : ∀ (k : Nat) (d : Nat), (eachDayGo f k d).length ≤ k
  | 0,     _ => Nat.le_refl 0
  | k + 1, d => by
    have ih := eachDayGo_length_le f k (d + 1)
    show ((if f d then [(d, d)] else []) ++ eachDayGo f k (d + 1)).length ≤ k + 1
    rw [List.length_append]
    cases f d <;> simp <;> omega

/-- **`eachDay` walks the range and no further** (D9-21). -/
theorem eachDay_length_le (lo hi : Nat) (f : Nat → Bool) :
    (eachDay lo hi f).length ≤ hi + 1 - lo := eachDayGo_length_le f _ _

/-- **Every day `eachDay` reports is a one-day occurrence inside the range that
`f` accepted** — the half of the rules' correctness that does not depend on
which rule was asked. -/
theorem eachDayGo_mem (f : Nat → Bool) :
    ∀ (k : Nat) (d : Nat) (a b : Nat), (a, b) ∈ eachDayGo f k d →
      a = b ∧ d ≤ a ∧ a < d + k ∧ f a = true
  | 0,     _, _, _, hm => by simp [eachDayGo] at hm
  | k + 1, d, a, b, hm => by
    have ih := eachDayGo_mem f k (d + 1) a b
    have hm' : (a, b) ∈ (if f d then [(d, d)] else []) ++ eachDayGo f k (d + 1) := hm
    rcases List.mem_append.1 hm' with h | h
    · cases hf : f d with
      | false => rw [hf] at h; simp at h
      | true  =>
        rw [hf] at h
        have h2 : (a, b) = (d, d) := by simpa using h
        have ha : a = d := congrArg Prod.fst h2
        have hb : b = d := congrArg Prod.snd h2
        subst ha; subst hb
        exact ⟨rfl, Nat.le_refl _, by omega, hf⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih h
      exact ⟨h1, by omega, by omega, h4⟩

theorem eachDay_mem (lo hi : Nat) (f : Nat → Bool) (a b : Nat) (hm : (a, b) ∈ eachDay lo hi f) :
    a = b ∧ lo ≤ a ∧ a ≤ hi ∧ f a = true := by
  obtain ⟨h1, h2, h3, h4⟩ := eachDayGo_mem f (hi + 1 - lo) lo a b hm
  exact ⟨h1, h2, by omega, h4⟩

/-- Fork `i64::rem_euclid` of `a − b` by `n`, over `Nat`s: the fork's `d − anchor`
is signed, and an anchor after the day is what makes it so (a log with a
completion dated later than the day being asked about). -/
def modDist (a b n : Nat) : Nat := if b ≤ a then (a - b) % n else (n - (b - a) % n) % n

/-- The Monday of a day's ISO week.  Nat 0 is a Monday (`Cal.weekday_origin`),
so `num_days_from_monday` is `d % 7` with no offset. -/
def mondayOf (d : Nat) : Nat := d - d % 7

/-- Fork `WEEK_EPOCH`: the Monday of ISO 1970-W01.  `every:Nw` counts whole
weeks from here rather than using the ISO week *number*, which restarts every
year and would put two `every:2w` occurrences on consecutive weeks across a
53-week year. -/
def weekEpoch : Nat := Cal.toDay ⟨1969, 12, 29⟩

/-- Fork `PHASE_EPOCH`: the fixed phase `every:Nd` falls back to when the log
has no completion of the item. -/
def phaseEpoch : Nat := Cal.unixEpoch

theorem phaseEpoch_is_1970_01_01 : phaseEpoch = Cal.toDay ⟨1970, 1, 1⟩ := rfl

/-- **Both epochs are the dates the fork names**: `WEEK_EPOCH` is a Monday (so a
week index is an exact division) and it is the Monday three days before
`PHASE_EPOCH`, 1970-01-01. -/
theorem the_two_epochs_are_the_dates_the_fork_names :
    Cal.weekdayOf weekEpoch = .monday ∧ weekEpoch + 3 = phaseEpoch := by decide

theorem mondayOf_is_a_monday (d : Nat) : Cal.weekdayOf (mondayOf d) = .monday := by
  have hdm := Nat.div_add_mod d 7
  have hd : mondayOf d = 7 * (d / 7) := by unfold mondayOf; omega
  show Cal.Weekday.ofIndex (mondayOf d % 7) = _
  rw [hd, Nat.mul_mod_right]
  rfl

/-- Fork `week_index(d).rem_euclid(n)`.  `week_index` is
`(monday − WEEK_EPOCH).num_days().div_euclid(7)`; both ends are Mondays, so the
difference is a multiple of 7 and the Euclidean division is exact — which is
why the two arms below divide before they take the remainder. -/
def weekIdxMod (d n : Nat) : Nat :=
  if weekEpoch ≤ mondayOf d then ((mondayOf d - weekEpoch) / 7) % n
  else (n - ((weekEpoch - mondayOf d) / 7) % n) % n

/-- One day, kept when it lands inside the inclusive range. -/
def dayHere (lo hi d : Nat) : List (Nat × Nat) := if lo ≤ d ∧ d ≤ hi then [(d, d)] else []

theorem dayHere_length_le (lo hi d : Nat) : (dayHere lo hi d).length ≤ 1 := by
  unfold dayHere; split <;> simp

/-- Fork `u32::from(*day).clamp(1, month_len(y, m))`. -/
def clampDom (dom len : Nat) : Nat := if dom < 1 then 1 else if len < dom then len else dom

/-- One month's occurrence: the day of the month clamped to that month's length,
kept when it lands inside the range. -/
def monthHere (dom : Nat) (lo hi : Nat) (y m : Nat) : List (Nat × Nat) :=
  dayHere lo hi (Cal.toDay ⟨y, m, clampDom dom (Cal.monthLen (Cal.isLeap y) m)⟩)

theorem monthHere_length_le (dom : Nat) (lo hi : Nat) (y m : Nat) :
    (monthHere dom lo hi y m).length ≤ 1 := dayHere_length_le _ _ _

/-- Fork `Rule::Monthly`'s loop: one step per month from the range's first to
its last (`if (y, m) >= (to.year(), to.month()) { break }`). -/
def monthsGo (dom : Nat) (lo hi : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,     _, _ => []
  | k + 1, y, m =>
    monthHere dom lo hi y m ++
      (if (Cal.ofDay hi).year < y ∨ ((Cal.ofDay hi).year = y ∧ (Cal.ofDay hi).month ≤ m) then []
       else if m = 12 then monthsGo dom lo hi k (y + 1) 1 else monthsGo dom lo hi k y (m + 1))

theorem monthsGo_length_le (dom : Nat) (lo hi : Nat) :
    ∀ (k y m : Nat), (monthsGo dom lo hi k y m).length ≤ k + 1
  | 0,     _, _ => by simp [monthsGo]
  | k + 1, y, m => by
    have h1 := monthsGo_length_le dom lo hi k (y + 1) 1
    have h2 := monthsGo_length_le dom lo hi k y (m + 1)
    have h0 := monthHere_length_le dom lo hi y m
    show (monthHere dom lo hi y m ++ _).length ≤ k + 1 + 1
    rw [List.length_append]
    split
    · simp; omega
    · split <;> omega

/-- The months the range touches, as fuel. -/
def monthFuel (lo hi : Nat) : Nat :=
  ((Cal.ofDay hi).year * 12 + (Cal.ofDay hi).month) + 1 -
    ((Cal.ofDay lo).year * 12 + (Cal.ofDay lo).month)

/-- One ISO week's occurrence for `every:Nw`: Monday to Sunday, kept when the
week qualifies and its Sunday is not before the range. -/
def weekHere (n : Nat) (lo : Nat) (mon : Nat) : List (Nat × Nat) :=
  if lo ≤ mon + 6 ∧ weekIdxMod mon n = 0 then [(mon, mon + 6)] else []

theorem weekHere_length_le (n : Nat) (lo mon : Nat) : (weekHere n lo mon).length ≤ 1 := by
  unfold weekHere; split <;> simp

/-- Fork `Rule::Weeks`' loop: one step per ISO week from the Monday of the
range's first day. -/
def mondaysGo (n : Nat) (lo hi : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,     _   => []
  | k + 1, mon => if hi < mon then [] else weekHere n lo mon ++ mondaysGo n lo hi k (mon + 7)

theorem mondaysGo_length_le (n : Nat) (lo hi : Nat) :
    ∀ (k : Nat) (mon : Nat), (mondaysGo n lo hi k mon).length ≤ k
  | 0,     _   => Nat.le_refl 0
  | k + 1, mon => by
    have ih := mondaysGo_length_le n lo hi k (mon + 7)
    have h0 := weekHere_length_le n lo mon
    show (if hi < mon then [] else weekHere n lo mon ++ mondaysGo n lo hi k (mon + 7)).length ≤ k + 1
    split
    · simp
    · rw [List.length_append]; omega

/-- The weeks the range touches, as fuel. -/
def weekFuel (lo hi : Nat) : Nat := (hi + 1 - mondayOf lo) / 7 + 1

/-- **Fork `rule_occurrences`**: the occurrences of one `every:` rule whose span
intersects the range, as `(first day, last day)` — the two differ only for
`every:week` / `every:Nw`, which spans a whole ISO week.

`anchor` is the item's own phase for `every:Nd`: the earliest completion the
log knows, else `phaseEpoch`.  It is never the range's start — `today_instances`
and `week_instances` ask about different ranges, and an anchored-on-the-range
rule would put one item on different days on the two screens (`recur.rs`'s own
deviation 6). -/
def ruleOccurrences (rule : Field.Rule) (lo hi : Nat) (anchor : Nat) : List (Nat × Nat) :=
  match rule with
  | .daily            => eachDay lo hi (fun _ => true)
  | .weekdays         => eachDay lo hi (fun d => decide (d % 7 < 5))
  | .weekly ds        => eachDay lo hi (fun d => ds.any (fun w => decide (w = Cal.weekdayOf d)))
  | .everyNDays n     => eachDay lo hi (fun d => decide (modDist d anchor (max n 1) = 0))
  | .everyNWeeks n wd => eachDay lo hi (fun d =>
                           decide (Cal.weekdayOf d = wd) && decide (weekIdxMod d (max n 1) = 0))
  | .monthly dom      => monthsGo dom lo hi (monthFuel lo hi) (Cal.ofDay lo).year (Cal.ofDay lo).month
  | .weeks n          => mondaysGo (max n 1) lo hi (weekFuel lo hi) (mondayOf lo)


/-! ## The item's own readings

Every field below is read through `Plan.lean`'s or `State.lean`'s existing view
— `shapeOf`, `effectiveOnMiss`, `Core.recur`, `Core.waiting`, `Core.status`,
`Field.viewDur` — so nothing here is a second reader of a line (AGENTS §5.3).
Fork `instances` reads `item.shape`, **not** `effective_shape`, so `shapeOf` is
the right one: `effectiveShape` replaces a `Shape.none` with §3.2's prep
`Point`, and an instance built on a prep due is not an occurrence the file
wrote. -/

/-- The record an id resolves to, when the plan holds one. -/
def coreAt (p : PlanCore) (i : Id) : Option Core := (p.store.get i).map Subtype.val

/-- §5.3's `on-miss:`, the override or the shape's default.  An id the plan does
not hold answers the shapeless default (`persist`), which is unreachable through
`todayInstances` — it skips an id with no record. -/
def onMissAt (p : PlanCore) (i : Id) : Field.OnMiss :=
  match coreAt p i with
  | some c => effectiveOnMiss c
  | none   => defaultOnMiss .none

/-- Fork `item.state.is_closed()`: `[x]` and `[~]`. -/
def isClosedAt (p : PlanCore) (i : Id) : Bool :=
  match coreAt p i with
  | some c => glyphOfStatus c.status == Glyph.done || glyphOfStatus c.status == Glyph.dropped
  | none   => false

/-- Fork `item.state == State::Waiting`: `[?]`. -/
def isWaitingAt (p : PlanCore) (i : Id) : Bool :=
  match coreAt p i with
  | some c => glyphOfStatus c.status == Glyph.waiting
  | none   => false

/-- Fork `window_on`: the window on one date.  An overnight daily window
(`22:00-08:00`, `to ≤ from`) runs into the next day. -/
def windowOn (rg : WindowRange) (d : Nat) : LocalT × LocalT :=
  match rg with
  | .daily f t    => (atClock d f, if t.val ≤ f.val then atClock (d + 1) t else atClock d t)
  | .absolute s e => (s.abs * 60, e.abs * 60)

/-- Fork `close_on`: when the chance to do this item on `date` ends. -/
def closeOn (p : PlanCore) (i : Id) (d : Nat) : LocalT :=
  match shapeOf p i with
  | .window rg _            => (windowOn rg d).2
  | .point (.dateTime _ t)  => atClock d t
  | .interval s e           => atClock d s.time + (e.abs - s.abs) * 60
  | _                       => endOfDay d

/-- Fork `span`: the `(window, due)` of an occurrence running from `first` to
`last` (the same date for every rule but `every:week`). -/
def spanOf (p : PlanCore) (i : Id) (first last : Nat) : Option (LocalT × LocalT) × LocalT :=
  match shapeOf p i with
  | .window rg _  => ((some ((windowOn rg first).1, (windowOn rg last).2)), (windowOn rg last).2)
  | .interval s e => (some (atClock first s.time, atClock first s.time + (e.abs - s.abs) * 60),
                      atClock first s.time + (e.abs - s.abs) * 60)
  | _             => (none, closeOn p i last)

/-- Fork `place_minutes`: the minutes an instance takes — the window's `dur:`,
else the line's own `dur:`.

**Not `Plan.declaredDur`, and the arm that differs is named.**  `declaredDur`
answers the *file-kind* question "what duration does this line declare", and on
an `at:` interval it answers the interval's own length; `place_minutes` answers
"how many minutes does the planner place", and on an interval it answers the
line's `dur:` — which is usually nothing at all, because a wall is not placed.
On every other shape the two are the same reading and this calls `declaredDur`
for it (`placeMinutes_is_declaredDur_off_an_interval`). -/
def placeMinutesOf (bm : Nat) (c : Core) : Option Nat :=
  match c.shape with
  | .interval _ _ => (Field.viewDur c.line).map (fun d => d.minutes bm)
  | _             => (declaredDur c).map (fun d => d.minutes bm)

def placeMinutes (bm : Nat) (p : PlanCore) (i : Id) : Option Nat :=
  (coreAt p i).bind (placeMinutesOf bm)

theorem placeMinutesOf_is_declaredDur_off_an_interval (bm : Nat) (c : Core)
    (h : ∀ a b, c.shape ≠ .interval a b) :
    placeMinutesOf bm c = (declaredDur c).map (fun d => d.minutes bm) := by
  unfold placeMinutesOf
  cases hs : c.shape with
  | interval a b => exact absurd hs (h a b)
  | none => rfl
  | point _ => rfl
  | window _ _ => rfl

/-- **The one input the two readings disagree on**, written down rather than
asserted: an `at:` interval with a `dur:` beside it.  `declaredDur` answers the
interval's own length and `placeMinutesOf` answers the `dur:` — and both are
right about their own question. -/
theorem placeMinutesOf_and_declaredDur_differ_on_an_interval :
    ∃ (c : Core) (bm : Nat), placeMinutesOf bm c ≠ (declaredDur c).map (fun d => d.minutes bm) := by
  refine ⟨⟨⟨0, 0⟩, none, .live .free,
           Field.itemOf "- [ ] x at:2026-09-07T09:00/2026-09-07T11:00 dur:30m ^a1".toList⟩, 30, ?_⟩
  decide

/-- Fork `has_closing_deadline`: false only for an `after-done:` item with no
`~validity` — its instance stays pending for ever, so no day is its last
chance. -/
def hasClosingDeadline (p : PlanCore) (i : Id) : Bool :=
  match coreAt p i with
  | some c => match c.recur with
              | .afterDone a => a.window.isSome
              | _            => true
  | none   => true

/-- Fork `logged_status`: the log's status for an instance, when the log has one
that is not the default `pending`. -/
def loggedStatus (f : Replay.Facts) (i : Id) (k : InstKey) : Option Log.InstanceStatus :=
  match f.instance i (renderInstKey k) with
  | some r => if r.status == .pending then none else some r.status
  | none   => none

/-- Fork `status_of`: the log's status, else §5.3's derivation from `close` and
`on_miss`. -/
def statusOf (p : PlanCore) (f : Replay.Facts) (i : Id) (k : InstKey) (close : LocalT)
    (today : Nat) : Log.InstanceStatus :=
  match loggedStatus f i k with
  | some s => s
  | none =>
    if today ≤ dateOfT close then .pending
    else match onMissAt p i with
         | .expire  => .expired
         | .persist => .pending
         | .next    => .skipped

/-! ## The log's own instances

Fork `logged_instances`: the occurrences the log knows about, for the
ordinal-keyed recurrences.  Their window is not reconstructed — only the log
says they happened. -/

/-- `BTreeMap<String>`'s order on an `inst` key.  UTF-8 preserves code-point
order, so comparing characters is comparing bytes; this is the order
`Replay::instances_of` iterates in, and `sort_by_key(|i| i.key)` keeps it
between equal keys. -/
def charsLe : List Char → List Char → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => if a = b then charsLe as bs else decide (a < b)

/-- Fork `out.sort_by_key(|i| i.key)` over a `BTreeMap` iteration: the key
first, the `inst` string breaking a tie — which is what a *stable* sort of a
string-ordered list by key is. -/
def keyedLe (a b : InstKey × List Char × Log.InstanceStatus) : Bool :=
  if a.1 = b.1 then charsLe a.2.1 b.2.1 else InstKey.le a.1 b.1

/-- Fork `logged_instances`. -/
def loggedInstances (f : Replay.Facts) (z : Cal.Tz) (i : Id) (lo hi : Nat)
    (skip : Option InstKey) : List Inst :=
  let rows : List (InstKey × List Char × Log.InstanceStatus) :=
    (f.instancesOf i).filterMap (fun q =>
      match parseInstKey q.1 with
      | none   => none
      | some k =>
        if skip = some k then none
        else
          let date := match k with
                      | .date d => d
                      | .nth _  => Cal.localDate z q.2.t.1
          if lo ≤ date && date ≤ hi then some (k, q.1, q.2.status) else none)
  (Replay.insSort keyedLe rows).map (fun r => ⟨i, r.1, none, none, r.2.2⟩)

/-! ## `after-done:` — where the item stands (fork `after_done_state`) -/

/-- Fork `whole_days`: a sub-day duration is 0 days (valid until later the same
day). -/
def wholeDays (bm : Nat) (d : Dur) : Nat := d.minutes bm / 1440

/-- Fork `next_ordinal`: one past the highest ordinal the log has **resolved**,
with the number of completion dates as a floor for `done` events that carry no
`inst`.  The fork's `saturating_add(1)` is a `u32` guard with no counterpart
over `Nat`. -/
def nextOrdinal (f : Replay.Facts) (i : Id) : Nat :=
  let resolved := (f.instancesOf i).filterMap (fun q =>
    match parseInstKey q.1 with
    | some (.nth n) => if q.2.status == .pending then none else some n
    | _             => none)
  Nat.max (resolved.foldl Nat.max 0) (f.doneDatesOf i).length + 1

/-- Fork `completion_count`: the `done` ordinal instances the log has, or the
number of distinct completion dates, whichever is larger. -/
def completionCount (f : Replay.Facts) (i : Id) : Nat :=
  let logged := ((f.instancesOf i).filter (fun q =>
    q.2.status == .done &&
      (match parseInstKey q.1 with | some (.nth _) => true | _ => false))).length
  Nat.max logged (f.doneDatesOf i).length

/-- Fork `recur::AfterDoneState`. -/
structure AfterDoneSt where
  lastDone     : Option Replay.At
  lastDoneDate : Option Nat
  count        : Nat
  pending      : Nat
  due          : Nat
  dueAt        : LocalT
  validUntil   : Option Nat
  validUntilAt : Option LocalT
  missed       : Bool
deriving Repr

/-- Fork `after_done_state`.  Before the first completion the instance is due
today; after a miss §5.3 splits three ways, and only `expire` re-dues the
occurrence to today. -/
def afterDoneState (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (today : Nat) : Option AfterDoneSt :=
  match coreAt p i with
  | none   => none
  | some c =>
    match c.recur with
    | .afterDone a =>
      let last := f.lastDone i
      let lastDate := last.map (fun t => Cal.localDate z t.1)
      let mins := a.offset.minutes bm
      let baseDue :=
        match last, lastDate with
        | some t, some ld =>
          if mins % 1440 = 0 then ld + mins / 1440
          else Cal.localDate z ⟨t.1.sec + mins * 60, t.1.ns⟩
        | _, _ => today
      let baseValid := a.window.map (fun w => baseDue + wholeDays bm w)
      let missed := match baseValid with | some v => decide (v < today) | none => false
      let reDue := missed && onMissAt p i == .expire
      let due := if reDue then today else baseDue
      let validUntil :=
        if reDue then a.window.map (fun w => today + wholeDays bm w) else baseValid
      some ⟨last, lastDate, completionCount f i, nextOrdinal f i, due, closeOn p i due,
            validUntil, validUntil.map (fun d => closeOn p i d), missed⟩
    | _ => none

/-! ## `[?]` waiting, and the event that ends it (fork `waiting_state`) -/

/-- The merge fork `NamedRecord::for_id` performs: the latest occurrence
addressed to this id **or to nobody**.  `NamedLatest::merged` absorbs the other
record's two occurrences in order, which is `NamedRec.push` twice — the same
`pick latestRel` / `pick datedRel` step the replay folds with, so there is no
second maximum here (AGENTS §5.3).  A stamp's local date is recomputed with
`Cal.localDate`, exactly as `absorb`'s `key` does. -/
def mergeNamed (z : Cal.Tz) (a b : Replay.NamedRec) : Replay.NamedRec :=
  let s1 := Replay.NamedRec.push (some a) b.latest.1 b.latest.2 (Cal.localDate z b.latest.2.1)
  Replay.NamedRec.push (some s1) b.dated.2.1 b.dated.2.2 b.dated.1

/-- Fork `Replay::latest_named(name, id, tz)`. -/
def latestNamed (z : Cal.Tz) (f : Replay.Facts) (name : List Char) (i : Id) :
    Option Replay.NamedRec :=
  match f.namedAt name none, f.namedAt name (some i) with
  | some a, some b => some (mergeNamed z a b)
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

/-- Fork `LatestNamed::on_or_after`: "some occurrence is at or after `since`" is
"the latest occurrence is at or after `since`", and the two maxima are why the
narrowing answers it exactly. -/
def onOrAfter (z : Cal.Tz) (r : Replay.NamedRec) (since : Option Nat) : Option Replay.At :=
  match since with
  | none   => some r.latest.2
  | some s =>
    if s ≤ Cal.localDate z r.latest.2.1 then some r.latest.2
    else if s ≤ Cal.localDate z r.dated.2.2.1 then some r.dated.2.2
    else none

/-- Fork `arrival_of`: the `tm event` that resolved this item's wait, if any. -/
def arrivalOf (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id) : Option Replay.At :=
  match coreAt p i with
  | none   => none
  | some c =>
    match c.recur with
    | .onEvent e => (latestNamed z f e.name i).bind (fun r => onOrAfter z r c.waiting)
    | _          => none

/-- Fork `recur::WaitingState`. -/
structure WaitingSt where
  since       : Option Nat
  daysWaiting : Nat
  timeoutAt   : Option Nat
  expired     : Bool
  arrived     : Option Replay.At
deriving Repr

/-- Fork `waiting_state`.  `expired` is the §5.1 timeout: it becomes true the
day *after* the timeout date. -/
def waitingState (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (today : Nat) : Option WaitingSt :=
  match coreAt p i with
  | none   => none
  | some c =>
    if glyphOfStatus c.status != Glyph.waiting then none
    else
      let since := c.waiting
      let timeout := match c.recur with | .onEvent e => e.timeout | _ => none
      let timeoutAt := match since, timeout with
                       | some s, some t => some (s + wholeDays bm t)
                       | _, _           => none
      some ⟨since, match since with | some s => today - s | none => 0, timeoutAt,
            (match timeoutAt with | some t => decide (t < today) | none => false),
            arrivalOf z p f i⟩


/-! ## The four recurrence kinds (fork `instances`' dispatch) -/

/-- Fork `calendar_instances`.  The phase of `every:Nd` is the item's own — the
earliest completion the log knows, else `phaseEpoch`. -/
def calendarInstances (bm : Nat) (p : PlanCore) (f : Replay.Facts) (i : Id) (rule : Field.Rule)
    (lo hi today : Nat) : List Inst :=
  let anchor := (Replay.minDay? (f.doneDatesOf i)).getD phaseEpoch
  (ruleOccurrences rule lo hi anchor).map (fun o =>
    let sp := spanOf p i o.1 o.2
    let k : InstKey := .date o.1
    let close := match sp.1 with | some w => w.2 | none => sp.2
    ⟨i, k, some sp.2, sp.1, statusOf p f i k close today⟩)

/-- Fork `after_done_instances`.  §5.3 `on-miss:next`: the missed chance is
Skipped and the next occurrence is unchanged, so it takes the following ordinal
and keeps the state's `due`; nothing is logged for that skip, so it is
synthesised here. -/
def afterDoneInstances (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (lo hi today : Nat) : List Inst :=
  match afterDoneState bm z p f i today with
  | none    => []
  | some st =>
    let skipped := if st.missed && onMissAt p i == .next then some (InstKey.nth st.pending) else none
    let pending : InstKey := .nth (if skipped.isSome then st.pending + 1 else st.pending)
    let logged := loggedInstances f z i lo hi (some pending)
    if st.due ≤ hi && !isClosedAt p i then
      let endD := match st.validUntil with | some v => v | none => Nat.max st.due today
      let window := match shapeOf p i with
                    | .window rg _ => some ((windowOn rg st.due).1, (windowOn rg endD).2)
                    | _            => none
      let sk := match skipped with
                | some k => [(⟨i, k, some st.dueAt, window, .skipped⟩ : Inst)]
                | none   => []
      logged ++ sk ++
        [⟨i, pending, some st.dueAt, window, (loggedStatus f i pending).getD .pending⟩]
    else logged

/-- Fork `on_event_instances`.  While the item waits, no instance is pending:
the wait ends when the event arrives or the timeout elapses (§5.1). -/
def onEventInstances (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (lo hi today : Nat) : List Inst :=
  let pending : InstKey := .nth (nextOrdinal f i)
  let logged := loggedInstances f z i lo hi (some pending)
  let blocked := match waitingState bm z p f i today with
                 | some w => !w.expired && w.arrived.isNone
                 | none   => false
  if !blocked && today ≤ hi && !isClosedAt p i then
    let sp := spanOf p i today today
    logged ++ [⟨i, pending, (match shapeOf p i with | .none => none | _ => some sp.2), sp.1,
                (loggedStatus f i pending).getD .pending⟩]
  else logged

/-- Fork `one_off_instances`: a `Recur::None` item with an **absolute**
`win:`+`dur:` yields the single instance that window describes — what makes
"Pick up package" a mandatory window instance on its last day (§5.2). -/
def oneOffInstances (p : PlanCore) (f : Replay.Facts) (i : Id) (lo hi today : Nat) : List Inst :=
  match shapeOf p i with
  | .window (.absolute a b) _ =>
    if dateOfT (b.abs * 60) < lo || hi < dateOfT (a.abs * 60) then []
    else
      let k : InstKey := .date (dateOfT (a.abs * 60))
      let st0 := statusOf p f i k (b.abs * 60) today
      let g := match coreAt p i with | some c => glyphOfStatus c.status | none => Glyph.todo
      let st :=
        if st0 == .pending then
          (if g == Glyph.done || f.isDone i then .done
           else if g == Glyph.dropped then .skipped
           else st0)
        else st0
      [⟨i, k, some (b.abs * 60), some (a.abs * 60, b.abs * 60), st⟩]
  | _ => []

/-- **Fork `instances`**: the occurrences of one item whose span intersects the
inclusive range, with their status at `today`.  Non-recurring items yield
nothing, except an absolute `win:`+`dur:` item. -/
def instancesOfItem (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (lo hi today : Nat) : List Inst :=
  if hi < lo then []
  else
    match coreAt p i with
    | none   => []
    | some c =>
      match c.recur with
      | .calendar rule => calendarInstances bm p f i rule lo hi today
      | .afterDone _   => afterDoneInstances bm z p f i lo hi today
      | .onEvent _     => onEventInstances bm z p f i lo hi today
      | .none          => oneOffInstances p f i lo hi today

/-! ## The flags (fork `instance_info`, `is_mandatory`) -/

/-- Fork `is_mandatory` (§5.2, exact rule): the instance is still actionable, the
item is a `win:` item, and its span closes today or earlier.  Under
`on-miss:persist` a closed span is **still** mandatory — §5.3's carried laundry;
otherwise the chance has to be left. -/
def isMandatory (p : PlanCore) (i : Id) (x : Inst) (today : Nat) (now : LocalT) : Bool :=
  if !isActionable x.status then false
  else match shapeOf p i with
       | .window _ _ =>
         match x.closeAt with
         | none   => false
         | some c =>
           if today < dateOfT c then false
           else if onMissAt p i == .persist then true
           else hasClosingDeadline p i && decide (now < c)
       | _ => false

/-- Fork `instance_info`. -/
def instanceInfo (bm : Nat) (p : PlanCore) (i : Id) (x : Inst) (today : Nat) (now : LocalT) :
    InstInfo :=
  let close := x.closeAt
  let start := x.startAt
  let due := x.due.or close
  let overdue := isActionable x.status && (match due with | some d => decide (dateOfT d < today) | none => false)
  ⟨isMandatory p i x today now,
   isActionable x.status && onMissAt p i != .persist && hasClosingDeadline p i &&
     (match close with | some c => decide (dateOfT c = today) && decide (now < c) | none => false),
   overdue,
   (if overdue then due.map dateOfT else none),
   isActionable x.status && (match start with | some s => decide (dateOfT s < today) | none => false),
   (match start with | some s => decide (now < s) | none => false),
   placeMinutes bm p i⟩

/-- Fork `instances_with_info`. -/
def instancesWithInfo (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (lo hi today : Nat) (now : LocalT) : List (Inst × InstInfo) :=
  (instancesOfItem bm z p f i lo hi today).map (fun x => (x, instanceInfo bm p i x today now))

/-! ## `today_instances` — one occurrence per item

Fork `CARRY_LOOKBACK_DAYS` is 60, and the range is `(today − 60, today)`.

**One instance per item, and doing it clears the carry.**  A `persist` instance
that was missed is still the item's pending instance (§5.3), so while it is open
the occurrence that has since come round is not a second obligation: today's
laundry is *the* laundry.  Forwards, the instance returned is the newest
actionable occurrence, carrying the overdue badge and `carriedFrom` of the older
miss it stands for; backwards, a `done` or `skip` settles every occurrence that
closed at or before it. -/

def carryLookbackDays : Nat := 60

/-- Fork `Iterator::max_by_key` on an `Option<NaiveDateTime>` key: `None` is the
least, and **the last** maximum wins. -/
def maxByClose (l : List (Inst × InstInfo)) : Option (Inst × InstInfo) :=
  l.foldl (fun acc x =>
    match acc with
    | none => some x
    | some a =>
      match a.1.closeAt, x.1.closeAt with
      | none,   _      => some x
      | some _, none   => some a
      | some p, some q => if p ≤ q then some x else some a) none

/-- The latest occurrence the log has settled: everything at or before it is
discharged, however many misses are stacked behind it. -/
def settledAt (l : List (Inst × InstInfo)) : Option LocalT :=
  (l.filterMap (fun x =>
    if x.1.status == .done || x.1.status == .skipped then (x.1.closeAt).or x.1.startAt else none)).foldl
      (fun acc t => match acc with | none => some t | some a => some (Nat.max a t)) none

/-- **Fork `today_instances`, for one item**: the instance that can be worked on
today, with its flags, or none. -/
def todayInstanceOf (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (i : Id)
    (today : Nat) (now : LocalT) : Option (Inst × InstInfo) :=
  if isClosedAt p i then none
  else
    let lo := today - carryLookbackDays
    let all := instancesWithInfo bm z p f i lo today today now
    let settled := settledAt all
    let mine := all.filter (fun x =>
      isActionable x.1.status &&
      (match x.1.startAt with | some s => decide (dateOfT s ≤ today) | none => true) &&
      (onMissAt p i == .persist ||
        (match x.1.closeAt with | some c => decide (now ≤ c) | none => true)) &&
      (match settled with
       | none   => true
       | some s => match (x.1.closeAt).or x.1.startAt with
                   | some c => decide (s < c)
                   | none   => true))
    let carried := mine.filter (fun x =>
      match x.1.closeAt with | some c => decide (dateOfT c < today) | none => false)
    let current := mine.filter (fun x =>
      match x.1.closeAt with | some c => !decide (dateOfT c < today) | none => true)
    match maxByClose current with
    | some cur =>
      match maxByClose carried with
      | none => some cur
      | some old =>
        some (cur.1, { cur.2 with
          overdue := true,
          mandatory := cur.2.mandatory || old.2.mandatory,
          carriedFrom := old.2.carriedFrom.or ((old.1.closeAt).map dateOfT) })
    | none => maxByClose carried

/-- **Fork `today_instances`**: every instance of `items` that can be worked on
today, with its flags — the planner's step 2 input and D27's four occurrence
facts. -/
def todayInstances (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts) (ids : List Id)
    (today : Nat) (now : LocalT) : List (Inst × InstInfo) :=
  ids.filterMap (fun i => todayInstanceOf bm z p f i today now)

theorem todayInstances_length_le (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts)
    (ids : List Id) (today : Nat) (now : LocalT) :
    (todayInstances bm z p f ids today now).length ≤ ids.length :=
  List.length_filterMap_le _ _

/-- **At most one occurrence per item** — the property §5.2 needs so a routine
cannot enter the day twice, and the reason D27 can derive `due`, `window`,
`overdue` and `mandatory` from an **id** rather than from an instance key. -/
theorem todayInstances_singleton (bm : Nat) (z : Cal.Tz) (p : PlanCore) (f : Replay.Facts)
    (i : Id) (today : Nat) (now : LocalT) :
    (todayInstances bm z p f [i] today now).length ≤ 1 :=
  todayInstances_length_le bm z p f [i] today now


/-! ## Witnesses

Every one is a closed term over `Nat` dates, probed at `MemoryMax=8G timeout
120` before it was kept (AGENTS §5.10a).  No `Entry` value, no parsed text, no
`native_decide`.  2026-09-07 is a Monday (`Cal.weekday_2026_09_07`) and the
dates are written as `Cal.toDay ⟨y, m, d⟩` so a reader can check them against a
calendar. -/

section Witnesses

/-- `every:day` is every day of the range, each one day long. -/
theorem every_day_is_every_day :
    ruleOccurrences .daily (Cal.toDay ⟨2026, 9, 7⟩) (Cal.toDay ⟨2026, 9, 9⟩) 0
      = [(Cal.toDay ⟨2026, 9, 7⟩, Cal.toDay ⟨2026, 9, 7⟩),
         (Cal.toDay ⟨2026, 9, 8⟩, Cal.toDay ⟨2026, 9, 8⟩),
         (Cal.toDay ⟨2026, 9, 9⟩, Cal.toDay ⟨2026, 9, 9⟩)] := by decide

/-- `every:weekday` skips the weekend — Saturday the 12th and Sunday the 13th are
not occurrences, Monday the 14th is — and `every:Thu` is the one Thursday of the
week. -/
theorem every_weekday_and_every_thursday_pick_their_days :
    ruleOccurrences .weekdays (Cal.toDay ⟨2026, 9, 12⟩) (Cal.toDay ⟨2026, 9, 14⟩) 0
      = [(Cal.toDay ⟨2026, 9, 14⟩, Cal.toDay ⟨2026, 9, 14⟩)] ∧
    ruleOccurrences (.weekly [.thursday]) (Cal.toDay ⟨2026, 9, 7⟩) (Cal.toDay ⟨2026, 9, 13⟩) 0
      = [(Cal.toDay ⟨2026, 9, 10⟩, Cal.toDay ⟨2026, 9, 10⟩)] := by decide

/-- **`every:3d` counts from the item's own anchor, and the same rule asked about
a different range gives the same days.**  An anchored phase is what `recur.rs`'s
deviation 6 is about — `today_instances` and `week_instances` ask about different
ranges and must not disagree about which days an item falls on.  With the anchor
on the 7th the occurrences are the 7th, the 10th and the 13th, and a range that
starts on the 8th drops the 7th and moves nothing. -/
theorem every_three_days_counts_from_the_anchor_and_not_from_the_range :
    ruleOccurrences (.everyNDays 3) (Cal.toDay ⟨2026, 9, 7⟩) (Cal.toDay ⟨2026, 9, 13⟩)
        (Cal.toDay ⟨2026, 9, 7⟩)
      = [(Cal.toDay ⟨2026, 9, 7⟩, Cal.toDay ⟨2026, 9, 7⟩),
         (Cal.toDay ⟨2026, 9, 10⟩, Cal.toDay ⟨2026, 9, 10⟩),
         (Cal.toDay ⟨2026, 9, 13⟩, Cal.toDay ⟨2026, 9, 13⟩)] ∧
    ruleOccurrences (.everyNDays 3) (Cal.toDay ⟨2026, 9, 8⟩) (Cal.toDay ⟨2026, 9, 13⟩)
        (Cal.toDay ⟨2026, 9, 7⟩)
      = [(Cal.toDay ⟨2026, 9, 10⟩, Cal.toDay ⟨2026, 9, 10⟩),
         (Cal.toDay ⟨2026, 9, 13⟩, Cal.toDay ⟨2026, 9, 13⟩)] := by decide

/-- **`every:2w:Mon` skips a week**, and the week it keeps is counted from
`weekEpoch` and not from the ISO week number: the 7th is in, the 14th is not. -/
theorem every_two_weeks_skips_a_week :
    ruleOccurrences (.everyNWeeks 2 .monday) (Cal.toDay ⟨2026, 9, 7⟩) (Cal.toDay ⟨2026, 9, 20⟩) 0
      = [(Cal.toDay ⟨2026, 9, 7⟩, Cal.toDay ⟨2026, 9, 7⟩)] := by decide

/-- `every:week` is a **whole ISO week**, Monday to Sunday — the one rule whose
first and last day differ, and the reason `span` takes two dates. -/
theorem every_week_is_monday_to_sunday :
    ruleOccurrences (.weeks 1) (Cal.toDay ⟨2026, 9, 7⟩) (Cal.toDay ⟨2026, 9, 13⟩) 0
      = [(Cal.toDay ⟨2026, 9, 7⟩, Cal.toDay ⟨2026, 9, 13⟩)] := by decide

/-- `every:month:31` **clamps to the month's length**: February 2026 has 28
days, so the occurrence is the 28th and not a date that does not exist. -/
theorem every_month_31_clamps_in_february :
    ruleOccurrences (.monthly 31) (Cal.toDay ⟨2026, 2, 1⟩) (Cal.toDay ⟨2026, 2, 28⟩) 0
      = [(Cal.toDay ⟨2026, 2, 28⟩, Cal.toDay ⟨2026, 2, 28⟩)] := by decide

/-- **A daily window closes on its own date unless it runs overnight**: a
`win:11:30-13:30` ends the day it opened, and a `win:22:00-08:00` ends the next
morning (§4.1's `to ≤ from`). -/
theorem a_daily_window_closes_on_its_own_date_unless_it_runs_overnight :
    windowOn (.daily ⟨690, by omega⟩ ⟨810, by omega⟩) (Cal.toDay ⟨2026, 9, 9⟩)
      = (atClock (Cal.toDay ⟨2026, 9, 9⟩) ⟨690, by omega⟩,
         atClock (Cal.toDay ⟨2026, 9, 9⟩) ⟨810, by omega⟩) ∧
    windowOn (.daily ⟨1320, by omega⟩ ⟨480, by omega⟩) (Cal.toDay ⟨2026, 9, 9⟩)
      = (atClock (Cal.toDay ⟨2026, 9, 9⟩) ⟨1320, by omega⟩,
         atClock (Cal.toDay ⟨2026, 9, 10⟩) ⟨480, by omega⟩) := by decide

/-- The two instance-key spellings the log writes, read back. -/
theorem an_instance_key_reads_back_both_ways :
    parseInstKey "#6".toList = some (.nth 6) ∧
    parseInstKey "2026-09-09".toList = some (.date (Cal.toDay ⟨2026, 9, 9⟩)) ∧
    parseInstKey "lunch".toList = none := by decide

/-- **An anchor after the day still gives a phase** — the arm `Nat` subtraction
would have got wrong: `modDist` is `rem_euclid`, so the 7th is two days short of
an anchor on the 9th under `every:3d`, not zero. -/
theorem a_future_anchor_does_not_collapse_the_phase :
    modDist (Cal.toDay ⟨2026, 9, 7⟩) (Cal.toDay ⟨2026, 9, 9⟩) 3 = 1 ∧
    modDist (Cal.toDay ⟨2026, 9, 6⟩) (Cal.toDay ⟨2026, 9, 9⟩) 3 = 0 := by decide

end Witnesses

end Recur
end Tm
