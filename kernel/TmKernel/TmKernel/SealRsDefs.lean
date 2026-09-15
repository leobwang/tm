import TmKernel.SealFoldPoint
/-!
# SealRsDefs — the reseal's parts, named (stage 5, D9, W2: law 6)

`resealOf` builds its checkpoint and records from a cut `j` of a run through a chain of local definitions.  They are named
here, so the laws can speak of each part (`resealOf_eq`, by definition).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State HeaderRec)
open Log (Entry)

/-- The tail entries a cut folds. -/
def rsBj (K : Ckpt) (r : Run) (j : Nat) : List Entry := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))

/-- The tail survivors a cut folds. -/
def rsSvj (K : Ckpt) (r : Run) (j : Nat) : List Entry := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))

/-- The restored maps' size. -/
def rsN (K : Ckpt) (r : Run) : Nat := K.items.length + K.openDays.length + r.entries.length

/-- The fold of the tail survivors a cut folds, on the run's index and `slept_by_day`. -/
def rsRj (z : Cal.Tz) (K : Ckpt) (r : Run) (j : Nat) : State :=
  (rsSvj K r j).foldl (Replay.stepWith z (Replay.dayOf z r.index) r.slept) (restore K (rsN K r))

/-- The folded wakes' index. -/
def rsKwj (z : Cal.Tz) (K : Ckpt) (r : Run) (j : Nat) : List Cal.Instant :=
  Replay.keptWakes z (K.wakes ++ Replay.wakeInstants (rsSvj K r j))

/-- The folded wakes' `slept_by_day`. -/
def rsSlept (z : Cal.Tz) (K : Ckpt) (r : Run) (j : Nat) : List (Nat × Nat) :=
  K.sleptByDay ++ Replay.sleptByDay z (rsKwj z K r j) (rsSvj K r j)

/-- The reseal's state: the fold rebound to the folded wakes' table. -/
def rsSt (z : Cal.Tz) (K : Ckpt) (r : Run) (j : Nat) : State :=
  rebindState (Replay.KMap.get (rsSlept z K r j)) (rsRj z K r j)

/-- The reseal's headers. -/
def rsHs (z : Cal.Tz) (K : Ckpt) (r : Run) (j : Nat) : List (Nat × HeaderRec) :=
  storedHeaders K ++ (tailHeaders (Replay.dayOf z r.index) K.settled r.entries).take (rsBj K r j).length

/-- The folded tail's instants. -/
def rsQA (K : Ckpt) (r : Run) (j : Nat) : List Cal.Instant := (rsBj K r j).flatMap entryInstants

/-- The merged tag lines. -/
def rsMerged (K : Ckpt) (r : Run) (j : Nat) : List (List Char × Nat) := mergeTagLines K.tagLast (tagLines (rsSvj K r j))

/-- The folded tail's line warnings. -/
def rsWs (K : Ckpt) (b : List Log.Line) (j : Nat) : List (Nat × Log.LWarn) :=
  (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ K.cut + j))

/-- **The resealed checkpoint** at cut `j`. -/
def rsCkpt (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (p : Policy) (r : Run) (j : Nat) : Ckpt :=
  ⟨ckptVersion, K.tzKey, K.cut + j, sealDayOf z T K p r j, T,
   maxOptI K.maxT (maxInstant? ((rsQA K r j).filter (fun q => !isFuture T q))),
   minOptI K.futureFloor (minInstant? ((rsQA K r j).filter (isFuture T))),
   storedWakes (sealDayOf z T K p r j) (rsKwj z K r j), storedSlept (rsSlept z K r j) (sealDayOf z T K p r j),
   keepTags (rsMerged K r j),
   K.tagOverflow || decide ((keepTags (rsMerged K r j)).length < (rsMerged K r j).length),
   settledAt K r j, (rsSt z K r j).machine,
   (canon idLt (K.items.map (·.id) ++ itemIds (rsSt z K r j))).map (aggMerged K (rsSt z K r j)),
   windowsFrom (rsSt z K r j) (horizonOf (sealDayOf z T K p r j)), instOtherOf (rsSt z K r j), namedOf (rsSt z K r j),
   daysFrom (rsSt z K r j) (rsHs z K r j) (sealDayOf z T K p r j),
   maxOpt K.lastDay (Replay.maxDay? ((rsSt z K r j).days.pairs.map Prod.fst)), (rsSt z K r j).global.lastEffective,
   K.entryCount + (rsBj K r j).length, (rsSt z K r j).unknown, (rsSt z K r j).longestLeak, (rsSt z K r j).rwarns.reverse,
   (K.warnings ++ rsWs K b j).take maxWarnings, K.warnings.length + K.warnOverflow + (rsWs K b j).length - maxWarnings⟩

/-- **The day records a reseal emits**, of `[L, L')`. -/
def rsDays (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j : Nat) : List DayRecord :=
  (daysIn (rsSt z K r j) (rsHs z K r j) K.ledgerDay (sealDayOf z T K p r j)).map (OpenDay.finish (rsSt z K r j).machine)

/-- **The window records a reseal emits**, of `[H, H')`. -/
def rsWindow (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j : Nat) : List WindowRecord :=
  windowsIn (rsSt z K r j) (horizonOf K.ledgerDay) (horizonOf (sealDayOf z T K p r j))

theorem resealOf_eq (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) :
    resealOf z T K b terminated p r =
      if migrationOk K T && cutOk z T K b terminated p r (foldPointOf z T K b terminated p r) then
        some ⟨rsCkpt z T K b p r (foldPointOf z T K b terminated p r),
          (rsCkpt z T K b p r (foldPointOf z T K b terminated p r)).meta,
          rsDays z T K p r (foldPointOf z T K b terminated p r), rsWindow z T K p r (foldPointOf z T K b terminated p r)⟩
      else none := rfl

/-- **An emitted reseal, by part.** -/
theorem resealOf_parts (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run)
    (s : Resealed) (h : resealOf z T K b terminated p r = some s) :
    s.ckpt = rsCkpt z T K b p r (foldPointOf z T K b terminated p r) ∧
    s.days = rsDays z T K p r (foldPointOf z T K b terminated p r) ∧
    s.window = rsWindow z T K p r (foldPointOf z T K b terminated p r) := by
  obtain ⟨hmig, hcut⟩ := resealOf_some z T K b terminated p r s h
  rw [resealOf_eq, hmig, hcut] at h
  simp only [Bool.and_self, ↓reduceIte, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

end Seal
end Tm
