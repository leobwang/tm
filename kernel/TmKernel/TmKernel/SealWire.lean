import TmKernel.SealTwin
/-!
# SealWire — what the `log` op carries across the wire from a resume (stage 5, D9, W3)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.2 (`meta`), §9.4 (what a reseal emits), §10.1 (`sealed`),
§10.2 (the answer), §10.4 (the bounds, law 13) and §11.3.  `Boundary.lean`'s `log` op reads a checkpoint, a reseal
policy and sealed records, resumes, and emits through what is defined here:

* **One emitter per shape** (W1's disagreement 13, AGENTS §5.3).  Every record Rust decodes from the op is emitted by
  the W1 codec the kernel reads it back with: a day record by `emitDayRecord`, a window record by `emitWindowRecord`,
  an item by `cItemAgg`, an instance by `cInstRec`, a named record by `cNamedRec`.  The facts of an answer
  (`Boundary.emitAnswer`) and the records a reseal seals (`emitResealed`) are one shape each, so what Rust stores in
  `sealed/YYYY-MM.g<gen>.json` and what it merges into a verb's `Replay` are decoded by one reader.  C6's
  string-tagged view (`factsJson`) leaves the wire.
* **What a reseal emits reads back** (§10.4's last paragraph): the op refuses `counterOverflow <field>` rather than emit
  a checkpoint or a record its own reader refuses (`Resealed.fault`), so law 10's round trips apply to every checkpoint
  the op hands Rust (`emitResealed_reads_back`).
* **Sealed records for an old date** (§10.1, D13): at most 62, each within its bounds, by strictly ascending day
  (`SealedIn.wf`).  `mergeSealed` puts the records below the answer's horizons in front of the answer's own, so a day
  or window read on the merged answer is §9.5's `askMerged` (`the_merged_days_read_as_askMerged`,
  `the_merged_window_reads_as_askMerged`), which law 1 (`seal_partition_is_the_replay`) makes the replay's on a sealed
  checkpoint's own records; a checkpoint's answer holds no day below its ledger day (`answer_ckptOf_days_ge`).
* **Law 13's check** (CRIT 14): `jnumsBelow` reads every numeral of a value (three mutually structural `Bool`
  functions, as `jemit`), and `overflowField` names the first key holding one past the bound.
* **The fold point scans down** (`greatestValidDown`): the greatest valid cut is the first valid one counting down from
  the tail's end, so a reseal whose fold point is near the end checks few cuts (`greatestValid_eq_down`).  It is
  compiled into `resealOf` through `resealOf_eq_resealOfFast` (`@[csimp]`).  W2's one-pass twin (part 4b's
  disagreement 12) stays owed for a fold point far from the end.

D9-21: every function here over a list the wire makes large is `List.map`/`filter`/`all`/`find?`/`foldl` (compiled
tail-recursively), and `jnumsBelow`'s list arms are tail calls; its depth is the value's nesting.
-/
namespace Tm
namespace Seal

open Replay (OpenBlock Interruption State)
open Log (Entry)

/-! ## The fold point, scanning down -/

/-- **The greatest `j ≤ n` a check accepts, counting down**: the first accepted cut from `n` (tail-recursive). -/
def greatestValidDown (valid : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => if valid (k + 1) then k + 1 else greatestValidDown valid k

theorem greatestValid_succ (n : Nat) (valid : Nat → Bool) :
    greatestValid (n + 1) valid = if valid (n + 1) then n + 1 else greatestValid n valid := by
  unfold greatestValid
  rw [List.range_succ, List.foldl_append]
  rfl

/-- **The downward scan is the specification scan**, for every check. -/
theorem greatestValid_eq_down (n : Nat) (valid : Nat → Bool) : greatestValid n valid = greatestValidDown valid n := by
  induction n with
  | zero => unfold greatestValid; simp [greatestValidDown]
  | succ k ih => rw [greatestValid_succ, ih]; rfl

/-- Condition (i) of a cut, with `F` given: every folded entry not future at `T` is on a day before `F`. -/
def cutFloorOk (T F : Nat) (dy : Cal.Instant → Nat) (Bj : List Entry) : Bool :=
  Bj.all (fun e => isFuture T e.t.val || decide (dy e.t.val < F))

/-- **`cutOk` with `F` computed once** (the compiled twin): the specification computes `floorOf` inside condition (i)'s
per-entry test, which is quadratic in the tail and, through `dayOf`'s scan of the wakes, cubic in practice (W3's
measurement: 10.9 s at 1,024 lines, 112 s at 2,048).  Strict evaluation computes an argument once. -/
def cutOkFast (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) (j : Nat) :
    Bool :=
  let dy := Replay.dayOf z r.index
  let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
  let svr := r.survivors.filter (fun e => decide (K.cut + j < e.line))
  let QAj := Bj.flatMap entryInstants
  let maxT' := maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q)))
  let ff' := minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T)))
  decide (j ≤ b.length)
  && cutFloorOk T (floorOf T p.keepDays dy r.survivors) dy Bj
  && (j == 0 || p.maxLine.all (fun m => decide (K.cut + j ≤ m)))
  && (Replay.wakeInstants svr).all (fun w => maxT'.all (· < w) && ff'.all (fun f => decide (w.sec + fenceSec < f.sec)))
  && decide ((settledAt K r j).length ≤ maxSettled)
  && (terminated || decide (j < b.length) || j == 0)
  && K.settled.all (fun n => decide (n ≤ K.cut + j))
  && (undoTargets r.unsettledTail).all (fun ut => !(decide (ut.2.line ≤ K.cut + j) && decide (K.cut + j < ut.1.line)))

/-- **The compiled cut check is the specification's** (`@[csimp]`). -/
@[csimp] theorem cutOk_eq_cutOkFast : @cutOk = @cutOkFast := by
  funext z T K b terminated p r j
  rfl

/-- A `slept_by_day` lookup over two tables, the first's reading first (`tailSlept`, with its tables computed). -/
def sleptLookup (a b : List (Nat × Nat)) (d : Nat) : Option Nat := (Replay.KMap.get a d).or (Replay.KMap.get b d)

/-- **`resumeRun` with the tail's `slept_by_day` computed once and a day index function** (the compiled twin's body): the
specification's `tailSlept` is a closure whose body rebuilds `sleptByDay` over the whole tail at every lookup, so each
energy observation, rebinding and reseal refold paid a pass over the tail (W3's measurement: a resume of 16,384 lines took
1,086 ms, and a reseal of 8,192 lines 2,129 ms).  Here the table is an argument, evaluated once, and the lookup a partial
application; the day index is `dyf kw` (W4: `dayFn`, the bisections). -/
def resumeRunWith (dyf : List Cal.Instant → Cal.Instant → Nat) (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) :
    Except Refusal Run :=
  if K.tzKey ≠ z.val.key then .error .zone
  else if !(b.head?.all (fun l => l.n == K.cut + 1)) then .error .cutMismatch
  else if T < K.ledgerDay then .error (.nowBelowLedger T K.ledgerDay)
  else
    let bs := Log.lineEntries b
    let N := unsettled K.settled bs
    match g1 K N with
    | some r => .error r
    | none =>
      let sv := Replay.survivors N
      let kw := tailIndex z K sv
      let dy := dyf kw
      let sl := sleptLookup K.sleptByDay (Replay.sleptByDay z kw sv)
      let r := tailFold z dy sl K (restore K (K.items.length + K.openDays.length + bs.length)) sv
      match r.2 <|> headerCheck dy K bs with
      | some x => .error x
      | none =>
        let hs := storedHeaders K ++ tailHeaders dy K.settled bs
        let st := rebindState sl r.1
        .ok ⟨bs, N, sv, kw, sl, st, hs, resumedAnswer K st hs bs.length (Log.lineWarnings b)⟩

/-- **The resume on its tail's entries `bs` and line warnings `ws`, read by the caller** (the `log` op reads each line
once: `Boundary.logOpZFast`): the day index by bisection (W4), `resumeRunWith (dayFn z)` written out.  The index is a
partial application of `dayOfZ` over arrays bound before it, so they are built once: `dayFn` itself is compiled at its
type's arity, and a branch that built the arrays inside it is lifted into the lookup's lambda, so either would rebuild both
arrays at every lookup (W4's second and third profiles; the compiler's IR shows the bound form builds them once). -/
def resumeRunV (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (bs : List Entry) (ws : List (Nat × Log.LWarn)) :
    Except Refusal Run :=
  if K.tzKey ≠ z.val.key then .error .zone
  else if !(b.head?.all (fun l => l.n == K.cut + 1)) then .error .cutMismatch
  else if T < K.ledgerDay then .error (.nowBelowLedger T K.ledgerDay)
  else
    let N := unsettled K.settled bs
    match g1 K N with
    | some r => .error r
    | none =>
      let sv := Replay.survivors N
      let kw := tailIndex z K sv
      let ta := z.val.trans.toArray
      let wa := kw.toArray
      let dy := if instAscending kw then dayOfZ z ta wa else Replay.dayOf z kw
      let sl := sleptLookup K.sleptByDay (Replay.sleptByDay z kw sv)
      let r := tailFold z dy sl K (restore K (K.items.length + K.openDays.length + bs.length)) sv
      match r.2 <|> headerCheck dy K bs with
      | some x => .error x
      | none =>
        let hs := storedHeaders K ++ tailHeaders dy K.settled bs
        let st := rebindState sl r.1
        .ok ⟨bs, N, sv, kw, sl, st, hs, resumedAnswer K st hs bs.length ws⟩

/-- **The compiled resume** (W4): `resumeRunV` on the lines' own entries and warnings. -/
def resumeRunFast (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) : Except Refusal Run :=
  resumeRunV z T K b (Log.lineEntries b) (Log.lineWarnings b)

/-- **The compiled resume is the specification's** (`@[csimp]`). -/
@[csimp] theorem resumeRun_eq_resumeRunFast : @resumeRun = @resumeRunFast := by
  funext z T K b
  have h : dayFn z = Replay.dayOf z := funext (dayFn_eq z)
  show resumeRunWith (Replay.dayOf z) z T K b = resumeRunWith (dayFn z) z T K b
  rw [h]

/-- **The resume on its lines' entries and warnings is the specification's.** -/
theorem resumeRunV_eq (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) :
    resumeRunV z T K b (Log.lineEntries b) (Log.lineWarnings b) = resumeRun z T K b := by
  rw [resumeRun_eq_resumeRunFast]; rfl

/-! ### The resume builds what its request wants (W4) -/

/-- The answer of a resume whose request asks no facts: the op never reads it (`LogReq.resumedV`). -/
def blankAnswer : Answer := ⟨0, 0, [], [], [], [], [], none, none, none, none, 0, 0, none, [], [], 0⟩

/-- A run with its answer kept only when facts are wanted, and its headers only when headers or facts are. -/
def trimRun (wa wh : Bool) (r : Run) : Run :=
  { r with headers := if wa || wh then r.headers else [], answer := if wa then r.answer else blankAnswer }

/-- **The resume building its answer only when facts are wanted (`wa`), and its headers only when headers or facts are
(`wh`)**: a genesis chunk asks neither, and the answer and headers of every chunk but the last were built and dropped (W4's
fourth profile: `resumedAnswer` and the resume's `tailHeaders`, about 8% of a genesis). -/
def resumeRunW (wa wh : Bool) (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (bs : List Entry)
    (ws : List (Nat × Log.LWarn)) : Except Refusal Run :=
  if K.tzKey ≠ z.val.key then .error .zone
  else if !(b.head?.all (fun l => l.n == K.cut + 1)) then .error .cutMismatch
  else if T < K.ledgerDay then .error (.nowBelowLedger T K.ledgerDay)
  else
    let N := unsettled K.settled bs
    match g1 K N with
    | some r => .error r
    | none =>
      let sv := Replay.survivors N
      let kw := tailIndex z K sv
      let ta := z.val.trans.toArray
      let wa' := kw.toArray
      let dy := if instAscending kw then dayOfZ z ta wa' else Replay.dayOf z kw
      let sl := sleptLookup K.sleptByDay (Replay.sleptByDay z kw sv)
      let r := tailFold z dy sl K (restore K (K.items.length + K.openDays.length + bs.length)) sv
      match r.2 <|> headerCheck dy K bs with
      | some x => .error x
      | none =>
        let hs := if wa || wh then storedHeaders K ++ tailHeaders dy K.settled bs else []
        let st := rebindState sl r.1
        .ok ⟨bs, N, sv, kw, sl, st, hs, if wa then resumedAnswer K st hs bs.length ws else blankAnswer⟩

/-- **It is the resume, trimmed**: every refusal the same, and an accepted run with only its answer and headers blanked. -/
theorem resumeRunW_eq (wa wh : Bool) (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (bs : List Entry)
    (ws : List (Nat × Log.LWarn)) :
    resumeRunW wa wh z T K b bs ws = (resumeRunV z T K b bs ws).map (trimRun wa wh) := by
  unfold resumeRunW resumeRunV
  split
  · rfl
  split
  · rfl
  split
  · rfl
  dsimp only
  split
  next x hx => (try simp only [hx]); rfl
  next hx =>
    (try simp only [hx])
    split
    next x hx2 => (try simp only [hx2]); rfl
    next hx2 =>
      (try simp only [hx2])
      cases wa <;> cases wh <;>
        simp only [Except.map, trimRun, Bool.or_self, Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false,
          if_true, if_false, Bool.false_eq_true]

/-! ## The reseal, compiled (W4): the cut check's fixed parts computed once -/

/-- One step of condition (i)'s bound: an entry neither future at `T` nor on a day before `F` lowers it to its line. -/
def badStep (T F : Nat) (dy : Cal.Instant → Nat) (acc : Option Nat) (e : Entry) : Option Nat :=
  if isFuture T e.t.val || decide (dy e.t.val < F) then acc
  else some (match acc with | none => e.line | some m => Nat.min m e.line)

/-- **Condition (i)'s bound**: the least line of an entry that no cut may fold (one pass). -/
def firstBadLine (T F : Nat) (dy : Cal.Instant → Nat) (es : List Entry) : Option Nat := es.foldl (badStep T F dy) none

theorem foldl_badStep_all (T F : Nat) (dy : Cal.Instant → Nat) (c : Nat) : ∀ (es : List Entry) (acc : Option Nat),
    (es.foldl (badStep T F dy) acc).all (fun m => decide (c < m))
      = (acc.all (fun m => decide (c < m))
          && (es.filter (fun e => decide (e.line ≤ c))).all (fun e => isFuture T e.t.val || decide (dy e.t.val < F)))
  | [], acc => by simp
  | e :: es, acc => by
    rw [List.foldl_cons, foldl_badStep_all T F dy c es, List.filter_cons]
    unfold badStep
    by_cases hp : (isFuture T e.t.val || decide (dy e.t.val < F)) = true
    · rw [if_pos hp]
      by_cases hl : e.line ≤ c
      · simp only [hl, decide_true, if_true, List.all_cons, hp, Bool.true_and]
      · simp only [hl, decide_false, Bool.false_eq_true, if_false]
    · rw [if_neg hp]
      have hp' : (isFuture T e.t.val || decide (dy e.t.val < F)) = false := by simpa using hp
      by_cases hl : e.line ≤ c
      · have hc : ¬ c < e.line := by omega
        cases acc with
        | none => simp [hl, hp', hc]
        | some m => simp [hl, hp', Nat.lt_min, hc]
      · have hc : c < e.line := by omega
        cases acc with
        | none => simp [hl, hc]
        | some m => simp [hl, Nat.lt_min, hc]

/-- **Condition (i) at a cut is its bound**: every folded entry passes exactly when the cut is below the bound. -/
theorem firstBadLine_all (T F : Nat) (dy : Cal.Instant → Nat) (es : List Entry) (c : Nat) :
    (firstBadLine T F dy es).all (fun m => decide (c < m))
      = (es.filter (fun e => decide (e.line ≤ c))).all (fun e => isFuture T e.t.val || decide (dy e.t.val < F)) := by
  unfold firstBadLine
  rw [foldl_badStep_all]
  simp

/-- The cut check's conjuncts, the constant-time ones first. -/
theorem and8_perm (a b c d e f g h : Bool) :
    (a && b && c && d && e && f && g && h) = (a && b && c && f && g && h && e && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> rfl

/-- **`cutOk` with its fixed parts given** (the compiled check): condition (i) as its bound `bad`, the tail's dangling undos
`dang` and undo targets `uts` computed once, and the conditions that read no list first, so a candidate cut that one of
them refuses costs no pass over the tail.  Condition (iii), the only one that reads the tail per cut, is last. -/
def cutCheckAt (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run)
    (bad : Option Nat) (dang : List Entry) (uts : List (Entry × Entry)) (j : Nat) : Bool :=
  decide (j ≤ b.length)
  && bad.all (fun m => decide (K.cut + j < m))
  && (j == 0 || p.maxLine.all (fun m => decide (K.cut + j ≤ m)))
  && (terminated || decide (j < b.length) || j == 0)
  && K.settled.all (fun n => decide (n ≤ K.cut + j))
  && uts.all (fun ut => !(decide (ut.2.line ≤ K.cut + j) && decide (K.cut + j < ut.1.line)))
  && decide ((((dang.filter (fun u => decide (K.cut + j < u.line))).map (·.line)).reverse).length ≤ maxSettled)
  && (let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
      let svr := r.survivors.filter (fun e => decide (K.cut + j < e.line))
      let QAj := Bj.flatMap entryInstants
      let maxT' := maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q)))
      let ff' := minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T)))
      (Replay.wakeInstants svr).all (fun w => maxT'.all (· < w) && ff'.all (fun f => decide (w.sec + fenceSec < f.sec))))

/-- **The compiled cut check is the specification's**, at every cut. -/
theorem cutCheckAt_eq (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run)
    (j : Nat) :
    cutCheckAt T K b terminated p r
        (firstBadLine T (floorOf T p.keepDays (Replay.dayOf z r.index) r.survivors) (Replay.dayOf z r.index) r.entries)
        (Replay.danglingOf r.unsettledTail).2 (undoTargets r.unsettledTail) j
      = cutOk z T K b terminated p r j := by
  simp only [cutCheckAt, cutOk, settledAt]
  rw [firstBadLine_all]
  exact (and8_perm _ _ _ _ _ _ _ _).symm

/-- The steps before a cut add no low: their state is the replay's fold. -/
theorem foldl_lowsStep_of_not (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool) :
    ∀ (l : List Entry) (st : State) (acc : List Nat), (∀ e ∈ l, P e = false) →
      l.foldl (lowsStep z dy sl P) (st, acc) = (l.foldl (Replay.stepWith z dy sl) st, acc)
  | [], _, _, _ => rfl
  | e :: l, st, acc, h => by
    rw [List.foldl_cons, List.foldl_cons]
    have he := h e List.mem_cons_self
    simp only [lowsStep, he, Bool.false_eq_true, if_false]
    exact foldl_lowsStep_of_not z dy sl P l _ acc (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- On lines that increase, the entries at or before a line and those after it are the list, split. -/
theorem filter_split_of_pairwise (c : Nat) : ∀ (l : List Entry), l.Pairwise (fun a b => a.line < b.line) →
    l.filter (fun e => decide (e.line ≤ c)) ++ l.filter (fun e => decide (c < e.line)) = l
  | [], _ => rfl
  | x :: xs, h => by
    by_cases hx : x.line ≤ c
    · have ih := filter_split_of_pairwise c xs h.of_cons
      have hn : ¬ c < x.line := by omega
      simp only [List.filter_cons, hx, hn, decide_true, decide_false, if_true, Bool.false_eq_true, if_false,
        List.cons_append, ih]
    · have hgt : ∀ y ∈ xs, c < y.line := fun y hy => by have := List.rel_of_pairwise_cons h hy; omega
      have h1 : xs.filter (fun e => decide (e.line ≤ c)) = [] :=
        List.filter_eq_nil_iff.2 (fun y hy => by have := hgt y hy; simp only [decide_eq_true_eq]; omega)
      have h2 : xs.filter (fun e => decide (c < e.line)) = xs :=
        List.filter_eq_self.2 (fun y hy => by simpa using hgt y hy)
      have hc : c < x.line := by omega
      simp only [List.filter_cons, hx, hc, decide_true, decide_false, if_true, Bool.false_eq_true, if_false, h1, h2,
        List.nil_append]

/-- **The state at a cut, and the lows of the steps after it** (specification: the reseal folds the survivors at or before
the cut from the checkpoint's state, and `stepLows` folds every survivor from it again). -/
def foldCut (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (c : Nat) (st0 : State) (sv : List Entry) :
    State × List Nat :=
  ((sv.filter (fun e => decide (e.line ≤ c))).foldl (Replay.stepWith z dy sl) st0,
   stepLows z dy sl (fun e => decide (c < e.line)) st0 sv)

/-- `foldCut` in one pass when the survivors' lines increase (a resume's always do: `the_tail_entries_have_increasing_lines`):
the lows' fold starts from the state at the cut. -/
def foldCutFast (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (c : Nat) (st0 : State)
    (sv : List Entry) : State × List Nat :=
  if Log.linesIncreasing sv then
    let Rj := (sv.filter (fun e => decide (e.line ≤ c))).foldl (Replay.stepWith z dy sl) st0
    (Rj, ((sv.filter (fun e => decide (c < e.line))).foldl (lowsStep z dy sl (fun e => decide (c < e.line))) (Rj, [])).2)
  else foldCut z dy sl c st0 sv

/-- **The one-pass state and lows are the specification's** (`@[csimp]`). -/
@[csimp] theorem foldCut_eq_foldCutFast : @foldCut = @foldCutFast := by
  funext z dy sl c st0 sv
  unfold foldCutFast
  split
  · rename_i h
    have hs := filter_split_of_pairwise c sv (Log.linesIncreasing_pairwise sv h)
    refine Prod.ext rfl ?_
    show stepLows z dy sl (fun e => decide (c < e.line)) st0 sv = _
    rw [stepLows_eq]
    conv => lhs; rw [← hs]
    rw [List.foldl_append, foldl_lowsStep_of_not z dy sl _ _ st0 []
      (fun e he => by simp only [List.mem_filter, decide_eq_true_eq] at he; simp only [decide_eq_false_iff_not]; omega)]
  · rfl

/-- **`sealDayOf` with its day index, `F`, the lows of the unfolded steps and the state at the cut given** (the specification
computes the state at the cut a second time, and folds every survivor again for the lows). -/
def sealDayOfWith (K : Ckpt) (r : Run) (j : Nat) (dy : Cal.Instant → Nat) (F : Nat) (stepLo : List Nat) (Rj : State) :
    Nat :=
  let Brest := r.entries.filter (fun e => decide (K.cut + j < e.line))
  let lows := Brest.map (fun e => dy e.t.val) ++ Brest.map (fun e => e.t.val.sec / 86400 + 1) ++ stepLo
    ++ machineDays Rj.machine
  Nat.max K.ledgerDay (lows.foldl Nat.min F)

/-- `resealOf` over a day index `dy`, a cut check `ok` and `F` (the compiled twin's body): the fold point by the downward
scan, and the state at the cut and the unfolded steps' lows in one fold (`foldCut`). -/
def resealOfWith (dy : Cal.Instant → Nat) (ok : Nat → Bool) (F : Nat) (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line)
    (lw : List (Nat × Log.LWarn)) (_p : Policy) (r : Run) : Option Resealed :=
  let j := greatestValidDown ok b.length
  if migrationOk K T && ok j then
    let n := K.items.length + K.openDays.length + r.entries.length
    let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
    let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
    let fc := foldCut z dy r.slept (K.cut + j) (restore K n) r.survivors
    let Rj := fc.1
    let kwj := Replay.keptWakes z (K.wakes ++ Replay.wakeInstants svj)
    let sleptj := K.sleptByDay ++ Replay.sleptByDay z kwj svj
    let st := rebindState (Replay.KMap.get sleptj) Rj
    let hsj := storedHeaders K ++ (tailHeaders dy K.settled r.entries).take Bj.length
    let L' := sealDayOfWith K r j dy F fc.2 Rj
    let QAj := Bj.flatMap entryInstants
    let merged := mergeTagLines K.tagLast (tagLines svj)
    let ws := lw.filter (fun w => decide (w.1 ≤ K.cut + j))
    let ck : Ckpt := ⟨ckptVersion, K.tzKey, K.cut + j, L', T,
      maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q))),
      minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T))),
      storedWakes L' kwj, storedSlept sleptj L', keepTags merged,
      K.tagOverflow || decide ((keepTags merged).length < merged.length),
      settledAt K r j, st.machine,
      mergedItems K st,
      windowsFrom st (horizonOf L'), instOtherOf st, namedOf st, daysFrom st hsj L',
      maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)), st.global.lastEffective,
      K.entryCount + Bj.length, st.unknown, st.longestLeak, st.rwarns.reverse,
      (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩
    some ⟨ck, ck.meta, (daysIn st hsj K.ledgerDay L').map (OpenDay.finish st.machine),
      windowsIn st (horizonOf K.ledgerDay) (horizonOf L')⟩
  else none

/-- On the specification's index, check and `F`, it is `resealOf`: only the fold point's scan differs. -/
theorem resealOfWith_spec (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy)
    (r : Run) :
    resealOfWith (Replay.dayOf z r.index) (cutOk z T K b terminated p r)
        (floorOf T p.keepDays (Replay.dayOf z r.index) r.survivors) z T K b (Log.lineWarnings b) p r
      = resealOf z T K b terminated p r := by
  unfold resealOf foldPointOf
  rw [greatestValid_eq_down]
  rfl

/-- **The reseal on its tail's line warnings `lw`, read by the caller**: the day index by bisection (`dayFn` written out, for the reason `resumeRunFast` gives), `F`
and the cut check's fixed parts once. -/
def resealOfV (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (lw : List (Nat × Log.LWarn)) (terminated : Bool)
    (p : Policy) (r : Run) : Option Resealed :=
  let ta := z.val.trans.toArray
  let wa := r.index.toArray
  let dy := if instAscending r.index then dayOfZ z ta wa else Replay.dayOf z r.index
  let F := floorOf T p.keepDays dy r.survivors
  resealOfWith dy
    (cutCheckAt T K b terminated p r (firstBadLine T F dy r.entries) (Replay.danglingOf r.unsettledTail).2
      (undoTargets r.unsettledTail))
    F z T K b lw p r

/-- **The compiled reseal** (W4): `resealOfV` on the lines' own warnings. -/
def resealOfFast (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) :
    Option Resealed :=
  resealOfV z T K b (Log.lineWarnings b) terminated p r

/-- **The compiled reseal is the specification's** (`@[csimp]`). -/
@[csimp] theorem resealOf_eq_resealOfFast : @resealOf = @resealOfFast := by
  funext z T K b terminated p r
  have hdy := dayFn_eq z r.index
  have hok : cutCheckAt T K b terminated p r
      (firstBadLine T (floorOf T p.keepDays (Replay.dayOf z r.index) r.survivors) (Replay.dayOf z r.index) r.entries)
      (Replay.danglingOf r.unsettledTail).2 (undoTargets r.unsettledTail) = cutOk z T K b terminated p r :=
    funext (cutCheckAt_eq z T K b terminated p r)
  have hf : resealOfFast z T K b terminated p r = resealOfWith (dayFn z r.index)
      (cutCheckAt T K b terminated p r (firstBadLine T (floorOf T p.keepDays (dayFn z r.index) r.survivors) (dayFn z r.index)
        r.entries) (Replay.danglingOf r.unsettledTail).2 (undoTargets r.unsettledTail))
      (floorOf T p.keepDays (dayFn z r.index) r.survivors) z T K b (Log.lineWarnings b) p r := rfl
  rw [hf, hdy, hok, resealOfWith_spec]

/-- **The reseal on its lines' warnings is the specification's.** -/
theorem resealOfV_eq (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) :
    resealOfV z T K b (Log.lineWarnings b) terminated p r = resealOf z T K b terminated p r := by
  rw [resealOf_eq_resealOfFast]; rfl

/-! ## The emitters a resume's wire adds -/

/-- The open block (fork `OpenBlock`): `[id, started, workedMin, since, paused]`. -/
def cOpenBlock : Codec OpenBlock :=
  cIso (cTuple <| tCons cStr <| tCons cAt <| tCons cNat <| tCons cOptAt <| tCons cBool <| tNil)
    (fun b => (b.id, b.started, b.workedMin, b.since, b.paused, ()))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1⟩) (fun _ => rfl)
theorem cOpenBlock_nonnull : cOpenBlock.NonNull := fun _ => nofun
theorem cInterruption_nonnull : cInterruption.NonNull := fun _ => nofun

abbrev cOptOpenBlock : Codec (Option OpenBlock) := cOpt cOpenBlock cOpenBlock_nonnull
abbrev cOptInterruption : Codec (Option Interruption) := cOpt cInterruption cInterruption_nonnull

/-- **The `meta` the host reads beside a checkpoint** (§9.2): `{cut, ledgerDay, horizon, resealDay, maxT, futureFloor}`,
the instants `[sec, ns]`. -/
def emitMeta (m : Meta) : JVal :=
  .obj [("cut".toList, .num m.cut), ("ledgerDay".toList, .num m.ledgerDay), ("horizon".toList, .num m.horizon),
        ("resealDay".toList, .num m.resealDay), ("maxT".toList, cOptInstant.enc m.maxT),
        ("futureFloor".toList, cOptInstant.enc m.futureFloor)]

/-- **What a reseal emits** (§9.4, §10.2): `{ckpt, meta, days, window}`, the records in the codecs' shapes. -/
def emitResealed (s : Resealed) : JVal :=
  .obj [("ckpt".toList, emitCkpt s.ckpt), ("meta".toList, emitMeta s.meta),
        ("days".toList, .arr (s.days.map emitDayRecord)), ("window".toList, .arr (s.window.map emitWindowRecord))]

/-- **The first bound a reseal's emission breaks** (§10.4's last paragraph): the checkpoint's, then a day record's, then
a window record's.  The op refuses `counterOverflow <field>` instead of emitting it. -/
def Resealed.fault (s : Resealed) : Option CkField :=
  match s.ckpt.fault with
  | some f => some f
  | none =>
    match s.days.findSome? DayRecord.fault with
    | some f => some f
    | none => s.window.findSome? WindowRecord.fault

theorem findSome?_eq_none_all {α : Type} (f : α → Option CkField) (l : List α) (h : l.findSome? f = none) :
    ∀ a ∈ l, f a = none := by
  intro a ha
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.findSome?_cons] at h
    split at h
    · cases h
    · rename_i hx
      rcases List.mem_cons.1 ha with rfl | hm
      · exact hx
      · exact ih h hm

/-- **Everything a reseal the op emits reads back** (law 10 at the wire): with no fault, the checkpoint, every day
record and every window record read back as themselves. -/
theorem emitResealed_reads_back (s : Resealed) (h : s.fault = none) :
    readCkpt (emitCkpt s.ckpt) = .ok s.ckpt ∧
    (∀ r ∈ s.days, readDayRecord (emitDayRecord r) = .ok r) ∧
    (∀ w ∈ s.window, readWindowRecord (emitWindowRecord w) = .ok w) := by
  unfold Resealed.fault at h
  split at h
  · cases h
  · rename_i hk
    split at h
    · cases h
    · rename_i hd
      refine ⟨readCkpt_emitCkpt _ (by simp [Ckpt.wf, hk]), fun r hr => ?_, fun w hw => ?_⟩
      · exact readDayRecord_emitDayRecord r (by simp [DayRecord.wf, findSome?_eq_none_all _ _ hd r hr])
      · exact readWindowRecord_emitWindowRecord w (by simp [WindowRecord.wf, findSome?_eq_none_all _ _ h w hw])

/-! ## Sealed records for an old date (§10.1, D13) -/

/-- **The `sealed` input** (§10.1): day records and window records Rust stored, for a query naming an old date. -/
structure SealedIn where
  days : List DayRecord
  window : List WindowRecord
deriving DecidableEq, Repr

/-- The most records one request carries (§10.4). -/
def maxSealedIn : Nat := 62

/-- **The `sealed` input's bounds** (§10.4): at most 62 records, each within its decoder's bounds, and each list by
strictly ascending day. -/
def SealedIn.wf (s : SealedIn) : Bool :=
  decide (s.days.length + s.window.length ≤ maxSealedIn) && s.days.all DayRecord.wf && s.window.all WindowRecord.wf
    && ascending natLt (s.days.map (·.day)) && ascending natLt (s.window.map (·.day))

/-- **An answer with sealed records in front** (§11.1's merge, in the kernel): the records below the answer's ledger
day and horizon, then the answer's own.  Records at or above the horizons are not the snapshot's and are dropped
(§9.8). -/
def mergeSealed (v : Answer) (s : SealedIn) : Answer :=
  { v with days := s.days.filter (fun r => decide (r.day < v.ledgerDay)) ++ v.days,
           window := s.window.filter (fun w => decide (w.day < v.horizon)) ++ v.window }

theorem findDay_filter_append (rs vs : List DayRecord) (L d : Nat) (hv : ∀ r ∈ vs, L ≤ r.day) :
    findDay (rs.filter (fun r => decide (r.day < L)) ++ vs) d
      = if d < L then findDay rs d else findDay vs d := by
  unfold findDay
  rw [List.find?_append]
  split
  · rename_i hd
    have hn : vs.find? (fun r => decide (r.day = d)) = none := by
      apply List.find?_eq_none.2
      intro r hr; have := hv r hr; simp; omega
    rw [hn, Option.or_none]
    induction rs with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x.day < L
      · simp only [List.filter_cons, hx, decide_true, ↓reduceIte, List.find?_cons]
        split <;> simp_all
      · simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
        rw [ih]
        have : ¬ x.day = d := by omega
        simp [this]
  · rename_i hd
    have hn : (rs.filter (fun r => decide (r.day < L))).find? (fun r => decide (r.day = d)) = none := by
      apply List.find?_eq_none.2
      intro r hr; simp only [List.mem_filter, decide_eq_true_eq] at hr; simp; omega
    rw [hn, Option.none_or]

theorem findWin_filter_append (ws vs : List WindowRecord) (H d : Nat) (hv : ∀ w ∈ vs, H ≤ w.day) :
    findWin (ws.filter (fun w => decide (w.day < H)) ++ vs) d
      = if d < H then findWin ws d else findWin vs d := by
  unfold findWin
  rw [List.find?_append]
  split
  · rename_i hd
    have hn : vs.find? (fun w => decide (w.day = d)) = none := by
      apply List.find?_eq_none.2
      intro w hw; have := hv w hw; simp; omega
    rw [hn, Option.or_none]
    induction ws with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x.day < H
      · simp only [List.filter_cons, hx, decide_true, ↓reduceIte, List.find?_cons]
        split <;> simp_all
      · simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
        rw [ih]
        have : ¬ x.day = d := by omega
        simp [this]
  · rename_i hd
    have hn : (ws.filter (fun w => decide (w.day < H))).find? (fun w => decide (w.day = d)) = none := by
      apply List.find?_eq_none.2
      intro w hw; simp only [List.mem_filter, decide_eq_true_eq] at hw; simp; omega
    rw [hn, Option.none_or]

/-- **A day read on the merged answer is `askMerged`'s** (§9.5 law 1's merge, done by the kernel): the sealed record
below the ledger day, the answer's at or above it. -/
theorem the_merged_days_read_as_askMerged (v : Answer) (s : SealedIn) (d : Nat) (dq : DayQ)
    (hv : ∀ r ∈ v.days, v.ledgerDay ≤ r.day) :
    dayRead (findDay (mergeSealed v s).days d) dq = askMerged s.days s.window v (.day d dq) := by
  simp only [mergeSealed, askMerged, askAnswer]
  rw [findDay_filter_append _ _ _ _ hv]
  by_cases hd : d < v.ledgerDay <;> simp [hd, askDayRecords]

/-- **A window read on the merged answer is `askMerged`'s.** -/
theorem the_merged_window_reads_as_askMerged (v : Answer) (s : SealedIn) (d : Nat) (wq : WinQ)
    (hv : ∀ w ∈ v.window, v.horizon ≤ w.day) :
    winRead (findWin (mergeSealed v s).window d) d wq = askMerged s.days s.window v (.win d wq) := by
  simp only [mergeSealed, askMerged, askAnswer]
  rw [findWin_filter_append _ _ _ _ hv]
  by_cases hd : d < v.horizon <;> simp [hd, askWindowRecords]

/-- The answer of a sealed checkpoint holds only days at or after its ledger day. -/
theorem answer_ckptOf_days_ge (z : Cal.Tz) (T₀ L : Nat) (ls rest : List Log.Line) :
    ∀ r ∈ (answer (ckptOf z T₀ L ls rest)).days, (answer (ckptOf z T₀ L ls rest)).ledgerDay ≤ r.day := by
  intro r hr
  simp only [ckptOf, answer_days, List.mem_map, daysFrom, List.mem_filter, decide_eq_true_eq] at hr
  obtain ⟨o, ⟨d, ⟨_, hd⟩, rfl⟩, rfl⟩ := hr
  simp only [ckptOf, answer, ckptOfEntries]
  simpa [OpenDay.finish, openDayOf] using hd

/-! ## Law 13's check: every numeral below `2^53` (CRIT 14) -/

/-- `2^53`: every numeral the `log` op emits is below it, so a host reading JSON numbers as doubles reads it exactly. -/
def numeralBound : Nat := 9007199254740992

theorem numeralBound_eq : numeralBound = 2 ^ 53 := rfl

mutual
/-- **Every numeral of a value is below `b`** (decimals are the numerals a line carried, emitted as read, and are not
counters). -/
def jnumsBelow (b : Nat) : JVal → Bool
  | .num n => decide (n < b)
  | .arr xs => jnumsBelowArr b xs
  | .obj kvs => jnumsBelowObj b kvs
  | _ => true
def jnumsBelowArr (b : Nat) : List JVal → Bool
  | [] => true
  | x :: xs => jnumsBelow b x && jnumsBelowArr b xs
def jnumsBelowObj (b : Nat) : List (List Char × JVal) → Bool
  | [] => true
  | kv :: kvs => jnumsBelow b kv.2 && jnumsBelowObj b kvs
end

/-- The first key of an object whose value holds a numeral at or past `b`. -/
def badKey (b : Nat) (kvs : List (List Char × JVal)) : Option (List Char × JVal) :=
  kvs.find? (fun kv => !jnumsBelow b kv.2)

/-- **The field `counterOverflow` names**: the first key of an object holding a numeral past the bound, and under an
object value, its first such key (`facts.entryCount`, `reseal.ckpt`). -/
def overflowField (b : Nat) (v : JVal) : List Char :=
  match v with
  | .obj kvs =>
    match badKey b kvs with
    | some (k, .obj sub) =>
      match badKey b sub with
      | some (k2, _) => k ++ ['.'] ++ k2
      | none => k
    | some (k, _) => k
    | none => []
  | _ => []

theorem jnumsBelow_obj (b : Nat) (kvs : List (List Char × JVal)) :
    jnumsBelow b (.obj kvs) = kvs.all (fun kv => jnumsBelow b kv.2) := by
  simp only [jnumsBelow]
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => simp only [jnumsBelowObj, List.all_cons, ih]

theorem jnumsBelow_arr (b : Nat) (xs : List JVal) : jnumsBelow b (.arr xs) = xs.all (jnumsBelow b) := by
  simp only [jnumsBelow]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [jnumsBelowArr, List.all_cons, ih]

/-! ## The names a refusal carries on the wire (§10.3) -/

def CkField.name : CkField → String
  | .shape => "shape" | .v => "v" | .tzKey => "tzKey" | .cut => "cut" | .ledgerDay => "ledgerDay"
  | .resealDay => "resealDay" | .maxT => "maxT" | .futureFloor => "futureFloor" | .wakes => "wakes"
  | .sleptByDay => "sleptByDay" | .tagLast => "tagLast" | .tagOverflow => "tagOverflow" | .settled => "settled"
  | .machine => "machine" | .items => "items" | .window => "window" | .instOther => "instOther" | .named => "named"
  | .openDays => "openDays" | .lastDay => "lastDay" | .lastEff => "lastEff" | .entryCount => "entryCount"
  | .unknown => "unknown" | .longestLeak => "longestLeak" | .rwarns => "replayWarnings" | .warnings => "warnings"
  | .warnOverflow => "warnOverflow" | .day => "day" | .record => "record" | .seam => "seam" | .energy => "energy"
  | .durations => "durations" | .interrupts => "interrupts" | .demotions => "demotions" | .closes => "closes"
  | .headers => "headers" | .itemMin => "itemMin" | .doneIds => "doneIds" | .inst => "inst"

end Seal
end Tm
