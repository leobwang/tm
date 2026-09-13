import TmKernel.Plan
/-!
# The fast checker, behind the same interface

`planWf` is the definition every theorem is about, and it is written to be
proved, not run: `normalized` re-renders the whole plan once **per document**
(`docRanks`), and `Nodup` on a `List Nat` is quadratic.  On a tree with months of
history that made one kernel call take a minute (README gap 62).

AGENTS.md's settled decision for exactly this — *"a fast checker and a provable
checker may be two artifacts, and the proofs live on the interface"* — is taken
here with Lean's `@[csimp]`.  A `@[csimp] theorem f_eq : @f = @g` tells the
**compiler** to emit `g` wherever the source says `f`.  The kernel never sees it:
every theorem, and every `decide` witness the kernel evaluates by unfolding, still
reads the original definition.  Unlike `@[implemented_by]` (banned, R4), which
swaps in code the kernel has never related to the definition, a `csimp` lemma
is a proved equality between two total functions, so the compiled program is
the definition the proofs are about.  The device is not new here: `Json.lean`'s
J5 twins (`jescape_eq_jescapeTR` and two more) keep long strings off the stack
the same way, and core uses it for `List.mergeSort` (`mergeSort_eq_mergeSortTR₂`).
This module is its first use on the checker and the loader.

Each equality here is **one theorem about one single-run function**: no
relational law, nothing a stage-5 ratio decision is about.

**Where the attribute bites.**  A `csimp` lemma rewrites the code of every
definition compiled *after* it.  `itemsWf`, `planWf` and `firstItemFault` were
compiled in `Plan.lean`, before this module, so their code calls the slow
conjuncts; each gets a twin with a word-for-word identical body,
compiled here, and a `csimp` lemma whose proof is `rfl`.  Every module from
`Cmd.lean` on imports this one, so every command, close and load runs the fast
code.  Two more modules add the twins that must sit next to their definitions:
`Close.lean` compacts a shifted store (`Store.mapEntities_eq_mapEntitiesFast`),
and `Boundary.lean` gives the loader one grouping pass, a seen-set and a table
(`buildEntities_eq_buildEntitiesFast`, `dedupIds_eq_dedupIdsFast`,
`loadStore_eq_loadStoreFast`) and the response one render
(`runPlan_eq_runPlanFast`).

Measured (kernel/README.md, "Stage 4 hardening"): one `tm drop` on a tree of 232
files and 2,926 lines went from 127 s to 0.07 s, with every response byte-identical.
-/
namespace Tm

/-! ## `normalized`, in one pass and one sort

A rank collision is two equal `(document, rank)` keys.  So instead of rendering
the plan once per document and asking each document's ranks for `Nodup`, collect
every key once — the prose ranks of every document, and the sites of every
entity (the sites of its rendered lines, without rendering their bytes) — sort
them, and compare neighbours.  `normalized_eq_normalizedFast` is the equality. -/

def siteKey (s : Site) : Nat × Nat := (s.doc, s.rank)

def entityKeys (e : Entity) : List (Nat × Nat) :=
  siteKey e.val.live :: (match e.val.archive with | none => [] | some t => [siteKey t.site])

def storeKeys (p : PlanCore) : List (Nat × Nat) :=
  p.store.dom.flatMap (fun i => match p.store.get i with | none => [] | some e => entityKeys e)

def proseKeys : Nat → List Doc → List (Nat × Nat)
  | _, []      => []
  | k, d :: ds => d.prose.map (fun q => (k, q.1)) ++ proseKeys (k + 1) ds

def allKeys (p : PlanCore) : List (Nat × Nat) := proseKeys 0 p.docs ++ storeKeys p

theorem render_keys (i : Id) (e : Entity) :
    (render i e).map (fun l => siteKey l.site) = entityKeys e := by
  unfold render renderCore entityKeys; cases e.val.archive <;> rfl

theorem lines_keys (p : PlanCore) : p.lines.map (fun l => siteKey l.site) = storeKeys p := by
  unfold PlanCore.lines storeKeys
  rw [List.map_flatMap]
  congr 1; funext i
  cases p.store.get i with
  | none => rfl
  | some e => exact render_keys i e

theorem proseKeys_at : ∀ (ds : List Doc) (m k : Nat),
    ((proseKeys m ds).filter (fun q => q.1 == k)).map Prod.snd =
      if m ≤ k then (match ds[k - m]? with | none => [] | some d => d.prose.map Prod.fst) else []
  | [], m, k => by simp [proseKeys]
  | d :: ds, m, k => by
    simp only [proseKeys, List.filter_append, List.map_append, proseKeys_at ds (m + 1) k]
    by_cases hmk : m = k
    · subst hmk
      simp only [List.filter_map, Function.comp_def, beq_self_eq_true, Nat.not_succ_le_self,
        if_false, List.append_nil, Nat.le_refl, if_true, Nat.sub_self, List.getElem?_cons_zero,
        List.map_map]
      rw [List.filter_eq_self.2 (fun _ _ => rfl)]
    · rw [List.filter_map]
      have : (List.filter ((fun q : Nat × Nat => q.1 == k) ∘ fun q => (m, q.1)) d.prose) = [] := by
        simp [Function.comp_def, hmk]
      rw [this]
      by_cases hlt : m < k
      · have h1 : m + 1 ≤ k := hlt
        have h2 : k - m = (k - (m + 1)) + 1 := by omega
        simp [h1, Nat.le_of_lt hlt, h2]
      · have h1 : ¬ m + 1 ≤ k := by omega
        have h2 : ¬ m ≤ k := by omega
        simp [h1, h2]

/-- A document's item ranks, read off the sites without rendering a byte. -/
theorem ranksIn_keys (p : PlanCore) (k : DocIx) :
    ranksIn k p.lines = ((storeKeys p).filter (fun q => q.1 == k)).map Prod.snd := by
  rw [← lines_keys, List.filter_map, List.map_map]
  simp [ranksIn, Function.comp_def, siteKey]

theorem docRanks_keys (p : PlanCore) (k : DocIx) :
    docRanks p k = ((allKeys p).filter (fun q => q.1 == k)).map Prod.snd := by
  rw [docRanks_eq, allKeys, List.filter_append, List.map_append]
  congr 1
  · rw [proseKeys_at]
    simp only [Nat.zero_le, if_true, Nat.sub_zero, proseRanks]
    cases p.docs[k]? <;> rfl
  · exact ranksIn_keys p k

/-- `docRanks` for one document without rendering the plan's bytes — what a
close's `endRank` asks at every landing. -/
def docRanksFast (p : PlanCore) (k : DocIx) : List Nat :=
  proseRanks p k ++ ((storeKeys p).filter (fun q => q.1 == k)).map Prod.snd

@[csimp] theorem docRanks_eq_docRanksFast : @docRanks = @docRanksFast := by
  funext p k
  rw [docRanks_eq, docRanksFast, ranksIn_keys]

theorem nodup_pairs_iff : ∀ (L : List (Nat × Nat)),
    L.Nodup ↔ ∀ k, ((L.filter (fun q => q.1 == k)).map Prod.snd).Nodup
  | [] => by simp
  | x :: t => by
    rw [List.nodup_cons, nodup_pairs_iff t]
    constructor
    · rintro ⟨hx, ht⟩ k
      by_cases hk : x.1 = k
      · subst hk
        simp only [List.filter_cons, beq_self_eq_true, if_true, List.map_cons, List.nodup_cons]
        refine ⟨?_, ht x.1⟩
        intro hmem
        obtain ⟨y, hy, hy2⟩ := List.mem_map.1 hmem
        obtain ⟨hy, hy1⟩ := List.mem_filter.1 hy
        have hy1 : y.1 = x.1 := by simpa using hy1
        exact hx (by rw [show x = y from Prod.ext hy1.symm hy2.symm]; exact hy)
      · simpa [List.filter_cons, hk] using ht k
    · intro h
      refine ⟨fun hx => ?_, fun k => ?_⟩
      · have := h x.1
        simp only [List.filter_cons, beq_self_eq_true, if_true, List.map_cons, List.nodup_cons] at this
        exact this.1 (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simp⟩, rfl⟩)
      · have := h k
        by_cases hk : x.1 = k
        · subst hk
          simp only [List.filter_cons, beq_self_eq_true, if_true, List.map_cons, List.nodup_cons] at this
          exact this.2
        · simpa [List.filter_cons, hk] using this

theorem normalized_iff_keys (p : PlanCore) :
    normalized p = true ↔
      ((allKeys p).filter (fun q => decide (q.1 < p.docs.length))).Nodup := by
  rw [nodup_pairs_iff]
  simp only [normalized, List.all_eq_true, List.mem_range, decide_eq_true_eq, List.filter_filter]
  constructor
  · intro h k
    by_cases hk : k < p.docs.length
    · have := h k hk
      rw [docRanks_keys] at this
      have e : (List.filter (fun q : Nat × Nat => (q.1 == k) && decide (q.1 < p.docs.length)) (allKeys p)) =
          List.filter (fun q => q.1 == k) (allKeys p) := by
        apply List.filter_congr
        intro q _
        by_cases hq : q.1 = k <;> simp [hq, hk]
      rw [e]; exact this
    · have e : (List.filter (fun q : Nat × Nat => (q.1 == k) && decide (q.1 < p.docs.length)) (allKeys p)) = [] := by
        apply List.filter_eq_nil_iff.2
        intro q _
        by_cases hq : q.1 = k <;> simp [hq, hk]
      rw [e]; simp
  · intro h k hk
    have := h k
    rw [docRanks_keys]
    have e : (List.filter (fun q : Nat × Nat => (q.1 == k) && decide (q.1 < p.docs.length)) (allKeys p)) =
        List.filter (fun q => q.1 == k) (allKeys p) := by
      apply List.filter_congr
      intro q _
      by_cases hq : q.1 = k <;> simp [hq, hk]
    rw [e] at this; exact this

/-! the sort -/

def keyLe (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))
def keyLt (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

def strictAsc : List (Nat × Nat) → Bool
  | a :: b :: t => keyLt a b && strictAsc (b :: t)
  | _           => true

theorem keyLe_trans (a b c : Nat × Nat) (h1 : keyLe a b = true) (h2 : keyLe b c = true) :
    keyLe a c = true := by
  simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem keyLe_total (a b : Nat × Nat) : (keyLe a b || keyLe b a) = true := by
  simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem keyLt_trans (a b c : Nat × Nat) (h1 : keyLt a b = true) (h2 : keyLt b c = true) :
    keyLt a c = true := by
  simp only [keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem strictAsc_iff : ∀ (S : List (Nat × Nat)), strictAsc S = true ↔ S.Pairwise (fun a b => keyLt a b = true)
  | [] => by simp [strictAsc]
  | [a] => by simp [strictAsc]
  | a :: b :: t => by
    rw [strictAsc, Bool.and_eq_true, strictAsc_iff (b :: t)]
    constructor
    · rintro ⟨hab, hbt⟩
      refine List.Pairwise.cons ?_ hbt
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact keyLt_trans a b x hab (List.rel_of_pairwise_cons hbt hx)
    · intro h
      exact ⟨List.rel_of_pairwise_cons h (by simp), h.of_cons⟩

theorem strictAsc_iff_nodup (S : List (Nat × Nat)) (hS : S.Pairwise (fun a b => keyLe a b = true)) :
    strictAsc S = true ↔ S.Nodup := by
  rw [strictAsc_iff]
  constructor
  · intro h
    exact h.imp (fun {a b} hab => by
      intro heq; subst heq
      simp [keyLt] at hab)
  · intro h
    exact (hS.and h).imp (fun {a b} ⟨hle, hne⟩ => by
      simp only [keyLe, keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hle ⊢
      by_cases h1 : a.1 = b.1
      · by_cases h2 : a.2 = b.2
        · exact absurd (Prod.ext h1 h2) hne
        · omega
      · omega)

def normalizedFast (p : PlanCore) : Bool :=
  let n := p.docs.length
  strictAsc (((allKeys p).filter (fun q => decide (q.1 < n))).mergeSort keyLe)

@[csimp] theorem normalized_eq_normalizedFast : @normalized = @normalizedFast := by
  funext p
  apply Bool.eq_iff_iff.2
  rw [normalized_iff_keys, normalizedFast,
    strictAsc_iff_nodup _ (List.pairwise_mergeSort keyLe_trans keyLe_total _),
    (List.mergeSort_perm _ _).nodup_iff]


/-! ## A store lookup built once

The loader folds `Store.insert` over its items, and each insert wraps `get` in
one more closure, so a lookup walks every item inserted before it, comparing
`List Char`s: `n` lookups cost `n²/2` comparisons, and every conjunct of
`planWf` does `n` of them.  `IdMap` is the same function as a hash table of
buckets; `IdMap.get_insert` is the only fact about it the loader's `csimp`
lemma needs (`Boundary.lean`, `loadStore_eq_loadStoreFast`).  The hash decides
only which bucket is searched, never what is found, so no property of the hash
is assumed. -/

def idHash (i : Id) : Nat := i.foldl (fun h c => (h * 31 + c.toNat) % 4294967291) 7

structure IdMap (α : Type) where
  buckets : Array (List (Id × α))

def IdMap.empty {α : Type} (n : Nat) : IdMap α := ⟨Array.replicate (n + 1) []⟩

def IdMap.slot {α : Type} (t : IdMap α) (j : Id) : Nat := idHash j % t.buckets.size

def IdMap.get {α : Type} (t : IdMap α) (j : Id) : Option α :=
  match t.buckets[t.slot j]? with
  | none   => none
  | some b => (b.find? (fun q => q.1 == j)).map Prod.snd

def IdMap.insert {α : Type} (t : IdMap α) (i : Id) (a : α) : IdMap α :=
  ⟨t.buckets.modify (t.slot i) (fun b => (i, a) :: b)⟩

theorem IdMap.size_empty {α : Type} (n : Nat) : 0 < (IdMap.empty (α := α) n).buckets.size := by
  simp [IdMap.empty]

theorem IdMap.size_insert {α : Type} (t : IdMap α) (i : Id) (a : α) :
    (t.insert i a).buckets.size = t.buckets.size := by simp [IdMap.insert]

theorem IdMap.slot_insert {α : Type} (t : IdMap α) (i j : Id) (a : α) :
    (t.insert i a).slot j = t.slot j := by simp [IdMap.slot, IdMap.size_insert]

theorem IdMap.get_empty {α : Type} (n : Nat) (j : Id) : (IdMap.empty (α := α) n).get j = none := by
  simp only [IdMap.get, IdMap.slot, IdMap.empty, Array.getElem?_replicate, Array.size_replicate]
  split
  · rfl
  · rename_i b hb
    split at hb
    · cases hb; rfl
    · cases hb

theorem IdMap.get_insert {α : Type} (t : IdMap α) (i j : Id) (a : α) (hpos : 0 < t.buckets.size) :
    (t.insert i a).get j = if j = i then some a else t.get j := by
  have hlt : ∀ x, idHash x % t.buckets.size < t.buckets.size := fun x => Nat.mod_lt _ hpos
  unfold IdMap.get
  rw [IdMap.slot_insert]
  simp only [IdMap.insert, IdMap.slot, Array.getElem?_modify, Array.getElem?_eq_getElem (hlt j)]
  by_cases hji : j = i
  · subst hji; simp
  · by_cases hs : idHash i % t.buckets.size = idHash j % t.buckets.size
    · have : (i == j) = false := by simpa using Ne.symm hji
      simp [hs, hji, this]
    · simp [hs, hji]

/-! ## A store built by commands stays a table

`Store.set` wraps `get` in one more closure, so a close that lands a hundred lines
leaves a chain a hundred `List Char` comparisons deep in front of every lookup,
and re-runs the whole plan check over that chain after every landing.
`Store.compact` rebuilds the same store — the same `dom`, a `get` equal at every id
(`Store.compact_eq`) — as one `IdMap`, at the cost of one pass over the domain;
`Store.set`'s twin compacts what it builds (and `Close.lean` does the same for
`Store.mapEntities`), so a command's post-state is looked up in constant time.
`Store.ext_of` is the extensionality both the loader's and this equality use. -/

theorem Store.ext_of {a b : Store} (hg : ∀ j, a.get j = b.get j) (hd : a.dom = b.dom) :
    a = b := by
  rcases a with ⟨ga, da, _, _⟩
  rcases b with ⟨gb, db, _, _⟩
  obtain rfl : ga = gb := funext hg
  obtain rfl : da = db := hd
  rfl

def compactStep (s : Store) (t : IdMap Entity) (j : Id) : IdMap Entity :=
  match s.get j with
  | none   => t
  | some e => t.insert j e

theorem compactStep_fold (s : Store) : ∀ (L A : List Id) (t : IdMap Entity),
    0 < t.buckets.size → (∀ j, t.get j = if j ∈ A then s.get j else none) →
    0 < (L.foldl (compactStep s) t).buckets.size ∧
      ∀ j, (L.foldl (compactStep s) t).get j = if j ∈ A ∨ j ∈ L then s.get j else none
  | [], A, t, hp, hg => ⟨hp, fun j => by simpa using hg j⟩
  | x :: L, A, t, hp, hg => by
    simp only [List.foldl_cons]
    have hp' : 0 < (compactStep s t x).buckets.size := by
      unfold compactStep; split
      · exact hp
      · simpa [IdMap.size_insert] using hp
    have hg' : ∀ j, (compactStep s t x).get j = if j ∈ x :: A then s.get j else none := by
      intro j
      unfold compactStep
      split
      · rename_i hx
        rw [hg j]
        by_cases hj : j = x
        · subst hj; simp [hx]
        · simp [hj]
      · rename_i e hx
        rw [IdMap.get_insert _ _ _ _ hp, hg j]
        by_cases hj : j = x
        · subst hj; simp [hx]
        · simp [hj]
    obtain ⟨h1, h2⟩ := compactStep_fold s L (x :: A) _ hp' hg'
    refine ⟨h1, fun j => ?_⟩
    rw [h2 j]
    by_cases hjx : j = x
    · subst hjx; simp
    · simp [hjx, or_comm]

/-- The same store, with its lookups answered from one table. -/
def Store.compact (s : Store) : Store :=
  let t := s.dom.foldl (compactStep s) (IdMap.empty s.dom.length)
  { get := t.get
    dom := s.dom
    domSpec := fun i => by
      obtain ⟨_, h⟩ := compactStep_fold s s.dom [] (IdMap.empty s.dom.length) (IdMap.size_empty _)
        (fun j => by simp [IdMap.get_empty])
      rw [h i]
      by_cases hi : i ∈ s.dom
      · simp [hi, (s.domSpec i).1 hi]
      · simp [hi]
    domNodup := s.domNodup }

theorem Store.compact_eq (s : Store) : s.compact = s := by
  obtain ⟨_, h⟩ := compactStep_fold s s.dom [] (IdMap.empty s.dom.length) (IdMap.size_empty _)
    (fun j => by simp [IdMap.get_empty])
  refine Store.ext_of (fun j => ?_) rfl
  show (s.dom.foldl (compactStep s) (IdMap.empty s.dom.length)).get j = s.get j
  rw [h j]
  by_cases hj : j ∈ s.dom
  · simp [hj]
  · simp only [List.not_mem_nil, false_or, hj, if_false]
    cases hs : s.get j with
    | none => rfl
    | some e => exact absurd ((s.domSpec j).2 (by simp [hs])) hj

def Store.setFast (s : Store) (i : Id) (e : Entity) (h : (s.get i).isSome = true) : Store :=
  (s.set i e h).compact

@[csimp] theorem Store.set_eq_setFast : @Store.set = @Store.setFast := by
  funext s i e h; exact (Store.compact_eq _).symm

/-! ## `pathsDistinct` with a seen-set

`pathsDistinct` decides `Nodup` of the paths, comparing every pair: `D²/2` path
comparisons, and a path is a `List Char`.  `pathsFresh` walks the paths once and
asks an `IdMap` (paths are `List Char`, as ids are) whether each was seen;
`pathsFresh_iff` is its specification. -/

def pathsFresh : List (List Char) → IdMap Unit → Bool
  | [],      _ => true
  | d :: ds, t =>
    match (t.get d).isSome with
    | true  => false
    | false => pathsFresh ds (t.insert d ())

theorem pathsFresh_iff : ∀ (ds : List (List Char)) (t : IdMap Unit), 0 < t.buckets.size →
    (pathsFresh ds t = true ↔ ds.Nodup ∧ ∀ d ∈ ds, t.get d = none)
  | [], _, _ => by simp [pathsFresh]
  | d :: ds, t, hp => by
    unfold pathsFresh
    cases hd : (t.get d).isSome with
    | true =>
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ h
      have := h d (by simp)
      rw [this] at hd; cases hd
    | false =>
      simp only
      rw [pathsFresh_iff ds (t.insert d ()) (by simpa [IdMap.size_insert] using hp), List.nodup_cons]
      have hn : t.get d = none := by simpa using hd
      constructor
      · rintro ⟨hnd, hall⟩
        refine ⟨⟨fun hm => ?_, hnd⟩, fun x hx => ?_⟩
        · have := hall d hm
          rw [IdMap.get_insert _ _ _ _ hp] at this; simp at this
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hn
          · have := hall x hx
            rw [IdMap.get_insert _ _ _ _ hp] at this
            by_cases hxd : x = d
            · subst hxd; simp at this
            · simpa [hxd] using this
      · rintro ⟨⟨hnm, hnd⟩, hall⟩
        refine ⟨hnd, fun x hx => ?_⟩
        rw [IdMap.get_insert _ _ _ _ hp]
        have hxd : x ≠ d := fun h => hnm (h ▸ hx)
        simp [hxd, hall x (by simp [hx])]

def pathsDistinctFast (p : PlanCore) : Bool :=
  pathsFresh (p.docs.map Doc.path) (IdMap.empty p.docs.length)

@[csimp] theorem pathsDistinct_eq_pathsDistinctFast : @pathsDistinct = @pathsDistinctFast := by
  funext p
  apply Bool.eq_iff_iff.2
  rw [pathsDistinctFast, pathsFresh_iff _ _ (IdMap.size_empty _)]
  simp [pathsDistinct, IdMap.get_empty]

/-! ## `parentsAcyclic` counts its fuel once

`parentsAcyclic` computes `fuel p` — the length of the domain — inside the
lambda, so once per id: `n²` list steps before a single parent is read.  The twin
binds it once; the two bodies are the same term up to that `let`, so the
equality is `rfl`. -/

def parentsAcyclicFast (p : PlanCore) : Bool :=
  let n := fuel p
  p.store.dom.all (fun i => (anc p n i).isNone)

@[csimp] theorem parentsAcyclic_eq_parentsAcyclicFast : @parentsAcyclic = @parentsAcyclicFast := rfl

/-! ## `sitesInRange` counts the documents once

The same fault as `parentsAcyclic`'s: `siteInRange` measures `p.docs` for every
site.  The twin binds the length once; `rfl`. -/

def sitesInRangeFast (p : PlanCore) : Bool :=
  let n := p.docs.length
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => decide (e.val.live.doc < n) &&
        (match e.val.archiveSite with
         | none   => true
         | some r => decide (r.doc < n)))

@[csimp] theorem sitesInRange_eq_sitesInRangeFast : @sitesInRange = @sitesInRangeFast := rfl

/-! ## The section and shape checks read each document once

`placementSectionWf` asks, for every placement, which kind of file it is in
(`docKind`: a list index and five path prefixes), which live heading stands above
it (a fold over the file's prose, each heading asking `inComment` — itself a fold)
and whether it sits inside a comment (another fold).  `DocFacts` computes those
per document once: the kind, whether any line of the file leaves a comment open
(`clean` — true of every file with no multi-line comment, the plan block's
one-line markers included), and the live headings in prose order.  On a clean
file `inComment` is `false` at every rank (`inComment_of_clean`), so neither
question folds again; on any other file the original fold still answers.  The
three equalities are the `csimp` lemmas below. -/


/-- What the section checks read off one document, computed once per check. -/
structure DocFacts where
  doc   : Doc
  kind  : DocKind
  clean : Bool
  heads : List (Nat × List Char)

def docFacts (d : Doc) : DocFacts :=
  let clean := d.prose.all (fun q => !commentAfter false q.2)
  { doc := d, kind := docKind d, clean := clean,
    heads := d.prose.filter (fun q => isHeading q.2 && (clean || !inComment d.prose q.1)) }

theorem foldl_commentAfter_false : ∀ (l : List (Nat × List Char)),
    (∀ q ∈ l, commentAfter false q.2 = false) → l.foldl (fun s q => commentAfter s q.2) false = false
  | [], _ => rfl
  | q :: t, h => by
    simp only [List.foldl_cons]
    rw [h q (by simp)]
    exact foldl_commentAfter_false t (fun x hx => h x (by simp [hx]))

theorem inComment_of_clean (d : Doc) (h : d.prose.all (fun q => !commentAfter false q.2) = true)
    (r : Nat) : inComment d.prose r = false := by
  unfold inComment commentOpenFrom
  apply foldl_commentAfter_false
  intro q hq
  have := List.all_eq_true.1 h q (List.mem_filter.1 hq).1
  simpa using this

theorem docFacts_live (d : Doc) (q : Nat × List Char) :
    (isHeading q.2 && ((docFacts d).clean || !inComment d.prose q.1)) = liveHeading d q := by
  simp only [docFacts, liveHeading]
  cases hc : d.prose.all (fun q => !commentAfter false q.2)
  · simp
  · simp [inComment_of_clean d hc]

theorem docFacts_heads (d : Doc) : (docFacts d).heads = d.prose.filter (liveHeading d) := by
  show d.prose.filter (fun q => isHeading q.2 && ((docFacts d).clean || !inComment d.prose q.1)) = _
  exact List.filter_congr (fun q _ => docFacts_live d q)

theorem foldl_if_and_filter {α β : Type} (P Q : α → Bool) (g : β → α → β) : ∀ (l : List α) (acc : β),
    l.foldl (fun acc q => if (P q && Q q) = true then g acc q else acc) acc =
      (l.filter Q).foldl (fun acc q => if P q = true then g acc q else acc) acc
  | [], _ => rfl
  | q :: t, acc => by
    simp only [List.foldl_cons, List.filter_cons]
    cases hq : Q q
    · simp only [Bool.and_false, Bool.false_eq_true, if_false]
      exact foldl_if_and_filter P Q g t acc
    · simp only [Bool.and_true, if_true, List.foldl_cons]
      exact foldl_if_and_filter P Q g t _

def headStep (rank : Nat) (acc : Option (Nat × List Char)) (q : Nat × List Char) : Option (Nat × List Char) :=
  if decide (q.1 < rank) = true then
    match acc with
    | none   => some q
    | some b => if b.1 < q.1 then some q else some b
  else acc

theorem lastHeadingBefore_facts (d : Doc) (rank : Nat) :
    lastHeadingBefore d rank = (docFacts d).heads.foldl (headStep rank) none := by
  rw [docFacts_heads]
  unfold lastHeadingBefore
  exact foldl_if_and_filter (fun q => decide (q.1 < rank)) (liveHeading d) _ d.prose none

theorem all_if_filter {α : Type} (L C : α → Bool) : ∀ (l : List α),
    l.all (fun q => if L q = true then C q else true) = (l.filter L).all C
  | [] => rfl
  | q :: t => by
    simp only [List.all_cons, List.filter_cons]
    cases hq : L q
    · simp only [Bool.false_eq_true, if_false, Bool.true_and]
      exact all_if_filter L C t
    · simp only [if_true, List.all_cons]
      rw [all_if_filter L C t]

def headingsWfF (f : DocFacts) : Bool :=
  f.heads.all (fun q =>
    match secKind q.2 with
    | .demoted => f.kind == DocKind.month
    | .pinned  => f.kind == DocKind.day
    | _        => true)

theorem headingsWfF_docFacts (d : Doc) : headingsWfF (docFacts d) = headingsWf (docKind d) d := by
  unfold headingsWfF headingsWf
  rw [docFacts_heads]
  exact (all_if_filter (liveHeading d) _ d.prose).symm

def kindAtF (a : Array DocFacts) (k : DocIx) : DocKind :=
  match a[k]? with
  | none   => .other
  | some f => f.kind

def placementSectionWfF (a : Array DocFacts) (s : Site) : Bool :=
  match a[s.doc]? with
  | none   => true
  | some f =>
    (match f.kind with
     | .day => (match (f.heads.foldl (headStep s.rank) none).map (fun q => secKind q.2) with
                | some .pinned => true
                | _            => false)
     | _    => true) &&
    !(!f.clean && inComment f.doc.prose s.rank)

theorem docFacts_kind (d : Doc) : (docFacts d).kind = docKind d := rfl
theorem docFacts_doc (d : Doc) : (docFacts d).doc = d := rfl

theorem facts_get (p : PlanCore) (k : Nat) :
    ((p.docs.map docFacts).toArray)[k]? = (p.docs[k]?).map docFacts := by
  simp

theorem kindAtF_eq (p : PlanCore) (k : Nat) : kindAtF (p.docs.map docFacts).toArray k = docKindAt p k := by
  unfold kindAtF docKindAt
  rw [facts_get]
  cases p.docs[k]? <;> rfl

theorem placementSectionWfF_eq (p : PlanCore) (s : Site) :
    placementSectionWfF (p.docs.map docFacts).toArray s = placementSectionWf p s := by
  unfold placementSectionWfF placementSectionWf
  rw [facts_get]
  cases hd : p.docs[s.doc]? with
  | none => simp [docKindAt, commentAt, hd]
  | some d =>
    have hc : (!(docFacts d).clean && inComment d.prose s.rank) = inComment d.prose s.rank := by
      cases hcl : (docFacts d).clean
      · simp
      · simp only [docFacts] at hcl
        simp [inComment_of_clean d hcl]
    (simp only [Option.map_some, docKindAt, sectionKindAt, sectionAt, commentAt, hd, docFacts_kind,
      docFacts_doc, hc, lastHeadingBefore_facts, Option.map_map, Function.comp_def]) <;> rfl

def sectionsWfFast (p : PlanCore) : Bool :=
  let fl := p.docs.map docFacts
  let a := fl.toArray
  fl.all headingsWfF &&
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => placementSectionWfF a e.val.live &&
        (match e.val.archiveSite with
         | none   => true
         | some r => placementSectionWfF a r))

@[csimp] theorem sectionsWf_eq_sectionsWfFast : @sectionsWf = @sectionsWfFast := by
  funext p
  (simp only [sectionsWf, sectionsWfFast, placementSectionWfF_eq, List.all_map, Function.comp_def,
    headingsWfF_docFacts]) <;> rfl

def shapesWfFast (p : PlanCore) : Bool :=
  let a := (p.docs.map docFacts).toArray
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => shapeWfFor (kindAtF a e.val.live.doc) e.val)

@[csimp] theorem shapesWf_eq_shapesWfFast : @shapesWf = @shapesWfFast := by
  funext p
  (simp only [shapesWf, shapesWfFast, kindAtF_eq]) <;> rfl

/-! ## The fold's twins: the same bodies, compiled after the fast conjuncts -/

/-- `itemsWf`, word for word. -/
def itemsWfFast (p : PlanCore) : Bool :=
  normalized p && parentsTotal p && parentsAcyclic p && afterTotal p && afterAcyclic p &&
    sectionsWf p && shapesWf p

@[csimp] theorem itemsWf_eq_itemsWfFast : @itemsWf = @itemsWfFast := rfl

/-- `planWf`, word for word. -/
def planWfFast (p : PlanCore) : Bool :=
  docsWf p && sitesInRange p && pathsDistinct p && demotionsOriented p && itemsWf p

@[csimp] theorem planWf_eq_planWfFast : @planWf = @planWfFast := rfl

/-- `firstItemFault`, word for word. -/
def firstItemFaultFast (p : PlanCore) : String :=
  if !normalized p then "rankCollision"
  else if !parentsTotal p then "danglingParent"
  else if !parentsAcyclic p then "parentCycle"
  else if !afterTotal p then "danglingDep"
  else if !afterAcyclic p then "depCycle"
  else if !sectionsWf p then "sectionDiscipline"
  else "fileKindShape"

@[csimp] theorem firstItemFault_eq_firstItemFaultFast : @firstItemFault = @firstItemFaultFast := rfl

/-! ## Every document's lines, bucketed in one pass

`renderDocAt p k d` filters the whole plan's rendered lines for document `k`, and
the response renders every document — so the wire path rendered the plan once
per document.  `linesByDoc` renders it once and files each line under its
document; `linesByDoc_get` is the one fact `Boundary.lean`'s `runPlan` twin needs. -/

def linesByDoc (p : PlanCore) : Array (List Line) :=
  p.lines.foldr (fun l acc => acc.modify l.site.doc (fun b => l :: b)) (Array.replicate p.docs.length [])

theorem bucketByDoc_get (n k : Nat) (hk : k < n) : ∀ (ls : List Line),
    (ls.foldr (fun l acc => acc.modify l.site.doc (fun b => l :: b)) (Array.replicate n []))[k]? =
      some (ls.filter (fun l => l.site.doc == k))
  | [] => by simp [hk]
  | l :: t => by
    simp only [List.foldr_cons, Array.getElem?_modify, bucketByDoc_get n k hk t, List.filter_cons]
    by_cases h : l.site.doc = k <;> simp [h]

theorem linesByDoc_get (p : PlanCore) (k : Nat) (hk : k < p.docs.length) :
    ((linesByDoc p)[k]?).getD [] = p.lines.filter (fun l => l.site.doc == k) := by
  simp [linesByDoc, bucketByDoc_get _ k hk]

end Tm
