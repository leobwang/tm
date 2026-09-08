import TmKernel.State
/-!
# The plan is one object

The whole collection — every month, week and day file, backlog, routines,
optional, calendar — is a single value, and every command is one transformation
on it.

Two design decisions carry the invariant:

1. **The store is a partial function `Id → Option Entity`.**  "An id names one
   item" is therefore not an invariant to maintain — it is what "function"
   means.  There is no `record_rank`, no `is_real_duplicate`, no `choose`
   tie-break, and no `drop_stale_demotion` repair, because there is nothing
   for them to repair.
2. **A document holds prose only.**  Headings, blank lines, comments and
   generated blocks are `prose` entries carrying their exact bytes and their
   rank.  Item lines are *absent* from `Doc` entirely: they are rendered from
   the entity that owns them.

The consequence is `no_two_lines_of_one_id_in_one_file` below — a theorem about
*every* `PlanCore`, so no command has to preserve it and no command can break
it, including commands nobody has written yet.
-/
namespace Tm

/-- The entity store.  `dom` is an enumeration order and nothing more;
`Std.HashMap` instantiates this interface, and keeping the proofs behind it is
the answer to the FFI spike's "a fast checker and a provable checker may be two
artifacts". -/
structure Store where
  get      : Id → Option Entity
  dom      : List Id
  domSpec  : ∀ i, i ∈ dom ↔ (get i).isSome = true
  domNodup : dom.Nodup

/-- Replace the entity at an id that already exists.  The domain is unchanged,
so both store obligations are discharged here once, not at each call site. -/
def Store.set (s : Store) (i : Id) (e : Entity) (h : (s.get i).isSome = true) : Store where
  get := fun j => if j = i then some e else s.get j
  dom := s.dom
  domSpec := by
    intro j
    by_cases hj : j = i
    · subst hj
      constructor
      · intro _; simp
      · intro _; exact (s.domSpec j).mpr h
    · simp only [hj, if_false]
      exact s.domSpec j
  domNodup := s.domNodup

@[simp] theorem Store.get_set_self (s : Store) (i : Id) (e : Entity) (h) :
    (s.set i e h).get i = some e := by simp [Store.set]

@[simp] theorem Store.get_set_other (s : Store) (i j : Id) (e : Entity) (h) (hj : j ≠ i) :
    (s.set i e h).get j = s.get j := by simp [Store.set, hj]

@[simp] theorem Store.dom_set (s : Store) (i : Id) (e : Entity) (h) :
    (s.set i e h).dom = s.dom := rfl

/-- A document body: **prose only**.  Item lines are holes filled by `render`,
which is why `move` has no `append` to be missing a precondition on. -/
structure Doc where
  path  : List Char
  prose : List (Nat × List Char)
deriving Repr, Inhabited

structure PlanCore where
  docs  : List Doc
  store : Store

/-- Every line the plan denotes.  A fold over the store, so each id is visited
once and each entity renders at most twice. -/
def PlanCore.lines (p : PlanCore) : List Line :=
  p.store.dom.flatMap (fun i =>
    match p.store.get i with
    | none   => []
    | some e => render i e)

/-! ## The invariant, as a theorem about the type -/

/-- **The sentence six code paths violated**, proved once for every possible
plan: two lines carrying one id in one file are the same line.  Nothing in the
proof mentions a command, so nothing a command does can break it. -/
theorem no_two_lines_of_one_id_in_one_file (p : PlanCore)
    (l₁ l₂ : Line) (h₁ : l₁ ∈ p.lines) (h₂ : l₂ ∈ p.lines)
    (hid : l₁.id = l₂.id) (hdoc : l₁.site.doc = l₂.site.doc) : l₁.site = l₂.site := by
  unfold PlanCore.lines at h₁ h₂
  simp only [List.mem_flatMap] at h₁ h₂
  obtain ⟨i₁, _, hl₁⟩ := h₁
  obtain ⟨i₂, _, hl₂⟩ := h₂
  cases g₁ : p.store.get i₁ with
  | none => rw [g₁] at hl₁; simp at hl₁
  | some e₁ =>
    cases g₂ : p.store.get i₂ with
    | none => rw [g₂] at hl₂; simp at hl₂
    | some e₂ =>
      rw [g₁] at hl₁; rw [g₂] at hl₂
      have e1 : l₁.id = i₁ := render_all_same_id i₁ e₁ l₁ hl₁
      have e2 : l₂.id = i₂ := render_all_same_id i₂ e₂ l₂ hl₂
      have hk : i₁ = i₂ := by rw [← e1, ← e2, hid]
      subst hk
      have : e₁ = e₂ := by rw [g₁] at g₂; exact (Option.some.injEq _ _ ▸ g₂.symm) ▸ rfl
      subst this
      exact one_line_per_file i₁ e₁ l₁ hl₁ l₂ hl₂ hdoc

theorem filter_flatMap {α β} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.filter_append, ih]

theorem render_filter_other (i j : Id) (e : Entity) (h : ¬ (i = j)) :
    (render i e).filter (fun l => l.id == j) = [] := by
  unfold render renderCore
  cases e.val.archive <;> simp [h]

theorem render_filter_self (i : Id) (e : Entity) :
    (render i e).filter (fun l => l.id == i) = render i e := by
  unfold render renderCore
  cases e.val.archive <;> simp

theorem flatMap_of_all_empty (t : List Id) (f : Id → List Line) (h : ∀ j ∈ t, f j = []) :
    t.flatMap f = [] := by
  induction t with
  | nil => simp
  | cons b s ih => simp [h b (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem sum_over_nodup_one_key (dom : List Id) (i : Id) (f : Id → List Line)
    (hz : ∀ j ∈ dom, j ≠ i → f j = []) (hn : dom.Nodup) (hb : (f i).length ≤ 2) :
    (dom.flatMap f).length ≤ 2 := by
  induction dom with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.nodup_cons] at *
      by_cases hai : a = i
      · subst hai
        have hall : ∀ j ∈ t, f j = [] :=
          fun j hj => hz j (by simp [hj]) (by rintro rfl; exact hn.1 hj)
        rw [flatMap_of_all_empty t f hall]
        simpa using hb
      · rw [hz a (by simp) hai]
        have := ih (fun j hj => hz j (by simp [hj])) hn.2
        simpa using this

/-- **How many lines one id can produce over the whole plan: two.**  The
archive copy is the only second line, and it is in a different file. -/
theorem lines_per_id_le_two (p : PlanCore) (i : Id) :
    ((p.lines).filter (fun l => l.id == i)).length ≤ 2 := by
  unfold PlanCore.lines
  rw [filter_flatMap]
  refine sum_over_nodup_one_key p.store.dom i _ ?_ p.store.domNodup ?_
  · intro j _ hji
    cases g : p.store.get j with
    | none => simp [g]
    | some ej => simp only [g]; exact render_filter_other j i ej hji
  · cases g : p.store.get i with
    | none => simp [g]
    | some ei => simp only [g]; rw [render_filter_self i ei]; exact render_le_two i ei

/-! ## The plan-level tier: a document holds no item lines

`Doc.prose` is verbatim text, so nothing in its *type* stops a writer putting
an item line there — which would be `move_to`'s append wearing a disguise.
That obligation lives in the third tier of the design: one decidable checker
over the whole value, discharged once at the boundary.

`planWf` is exactly what `tm check` runs, so the checker cannot be weaker than
the invariant — the class of bug where three `^m2` lines across two month files
pass `tm check` at exit 0. -/

def docWf (d : Doc) : Bool := d.prose.all (fun q => !isItemLine q.2)

def docsWf (p : PlanCore) : Bool := p.docs.all docWf

/-! ### The second plan-level obligation: a placement names a file that exists

`Site.doc` is a `Nat` and `renderDocAt` renders the indices that exist, so a
placement pointing past the end of `docs` does not raise anything — the line
simply is not emitted, and the item is **gone** with the kernel reporting `ok`.
That is the same shape of missing precondition as `move_to`'s, moved from
"the destination already holds this id" to "the destination is not a file", and
it is exactly as fatal.

So it joins the decidable plan-level checker, and `no_line_is_lost` below turns
it into the sentence that matters: every line a plan denotes lands in a document
that exists.  A command reaches the destination only through `Dest` (Cmd.lean),
which carries the proof, so the out-of-range case cannot be written either. -/

def siteInRange (p : PlanCore) (s : Site) : Bool := s.doc < p.docs.length

def entityInRange (p : PlanCore) (e : Entity) : Bool :=
  siteInRange p e.val.live &&
    (match e.val.archive with
     | none   => true
     | some r => siteInRange p r)

def sitesInRange (p : PlanCore) : Bool :=
  p.store.dom.all (fun i =>
    match p.store.get i with
    | none   => true
    | some e => entityInRange p e)

/-! ### The third: two documents may not share a path

`Site.doc` is a **list index**, so a theorem quantified over `Site.doc` says
"one index, one line" — which is not the sentence anyone cares about.  What
reaches the disk is a *path*, and two documents at different indices carrying
one path put two lines of one id into one file while every index-level theorem
stays true.  Path injectivity is therefore part of what it means to be a plan,
and `no_two_lines_of_one_id_in_one_file` is restated over paths below. -/

def pathsDistinct (p : PlanCore) : Bool := decide ((p.docs.map Doc.path).Nodup)

def planWf (p : PlanCore) : Bool := docsWf p && sitesInRange p && pathsDistinct p

theorem planWf_parts {p : PlanCore} (h : planWf p = true) :
    docsWf p = true ∧ sitesInRange p = true ∧ pathsDistinct p = true := by
  simp only [planWf, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem planWf_of_parts {p : PlanCore} (h1 : docsWf p = true) (h2 : sitesInRange p = true)
    (h3 : pathsDistinct p = true) : planWf p = true := by
  simp [planWf, h1, h2, h3]

/-- The plan.  You cannot make one without discharging `planWf`. -/
def WfPlan := { p : PlanCore // planWf p = true }

def WfPlan.val' (p : WfPlan) : PlanCore := p.val

/-- The path a document index names.  `none` is out of range — which
`no_line_is_lost` rules out for any site a plan actually denotes. -/
def pathAt (p : PlanCore) (k : DocIx) : Option (List Char) := (p.docs[k]?).map Doc.path

/-- **No prose line is an item line.**  So the only item lines a document emits
are the ones its entities render, and `no_two_lines_of_one_id_in_one_file`
covers all of them. -/
theorem prose_is_never_an_item (p : WfPlan) (d : Doc) (hd : d ∈ p.val.docs)
    (q : Nat × List Char) (hq : q ∈ d.prose) : isItemLine q.2 = false := by
  have h1 : docWf d = true := List.all_eq_true.1 (planWf_parts p.property).1 d hd
  have h2 := List.all_eq_true.1 h1 q hq
  simpa using h2

/-- Changing the store cannot change the *document* half of the invariant, which
reads `docs` only.  The other two halves are not free of the store — that is the
point of adding them: `sitesInRange` is precisely the obligation a command that
relocates a line must re-discharge. -/
theorem docsWf_store (p : PlanCore) (s : Store) : docsWf { p with store := s } = docsWf p := rfl

theorem pathsDistinct_store (p : PlanCore) (s : Store) :
    pathsDistinct { p with store := s } = pathsDistinct p := rfl

/-! ## Nothing a plan denotes can fall off the end of `docs` -/

/-- A rendered line sits at one of the entity's own two placements. -/
theorem render_site (i : Id) (e : Entity) (l : Line) (h : l ∈ render i e) :
    l.site = e.val.live ∨ e.val.archive = some l.site := by
  unfold render renderCore at h
  cases ha : e.val.archive with
  | none =>
      rw [ha] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; left; rfl
  | some r =>
      rw [ha] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · left; rfl
      · right; rfl

theorem lines_mem (p : PlanCore) (l : Line) (h : l ∈ p.lines) :
    ∃ i e, p.store.get i = some e ∧ i ∈ p.store.dom ∧ l ∈ render i e := by
  unfold PlanCore.lines at h
  simp only [List.mem_flatMap] at h
  obtain ⟨i, hi, hl⟩ := h
  cases g : p.store.get i with
  | none => rw [g] at hl; simp at hl
  | some e => rw [g] at hl; exact ⟨i, e, g, hi, hl⟩

/-- **Nothing the kernel holds can silently disappear from the output.**  Every
line of every plan lands in a document that exists, so rendering document by
document over `docs` emits all of them.  Before `sitesInRange` joined `planWf`,
`move` to a document index past the end of `docs` deleted the item and returned
`ok`. -/
theorem no_line_is_lost (p : WfPlan) (l : Line) (h : l ∈ p.val.lines) :
    l.site.doc < p.val.docs.length := by
  obtain ⟨i, e, hget, hdom, hl⟩ := lines_mem p.val l h
  have hall := List.all_eq_true.1 (planWf_parts p.property).2.1 i hdom
  rw [hget] at hall
  simp only [entityInRange, Bool.and_eq_true, siteInRange, decide_eq_true_eq] at hall
  rcases render_site i e l hl with hs | hs
  · rw [hs]; exact hall.1
  · have := hall.2
    rw [hs] at this
    simpa [siteInRange] using this

/-- **The theorem the name always promised.**  Two lines carrying one id that
land in one *file* — the same path on disk, not merely the same list index —
are the same line.  The index-level version below is what this is proved from;
on its own it left two documents free to share a path, and then a demotion put
two `^m1` lines into one file with every stated theorem still true. -/
theorem no_two_lines_of_one_id_in_one_path (p : WfPlan) (l₁ l₂ : Line)
    (h₁ : l₁ ∈ p.val.lines) (h₂ : l₂ ∈ p.val.lines) (hid : l₁.id = l₂.id)
    (hpath : pathAt p.val l₁.site.doc = pathAt p.val l₂.site.doc) : l₁.site = l₂.site := by
  have k₁ : l₁.site.doc < p.val.docs.length := no_line_is_lost p l₁ h₁
  have k₂ : l₂.site.doc < p.val.docs.length := no_line_is_lost p l₂ h₂
  have hnd : (p.val.docs.map Doc.path).Nodup := by
    have := (planWf_parts p.property).2.2
    simpa [pathsDistinct] using this
  have hm₁ : l₁.site.doc < (p.val.docs.map Doc.path).length := by simpa using k₁
  have hm₂ : l₂.site.doc < (p.val.docs.map Doc.path).length := by simpa using k₂
  have heq : (p.val.docs.map Doc.path)[l₁.site.doc] = (p.val.docs.map Doc.path)[l₂.site.doc] := by
    simp only [List.getElem_map]
    have e₁ : pathAt p.val l₁.site.doc = some (p.val.docs[l₁.site.doc]).path := by
      simp [pathAt, List.getElem?_eq_getElem k₁]
    have e₂ : pathAt p.val l₂.site.doc = some (p.val.docs[l₂.site.doc]).path := by
      simp [pathAt, List.getElem?_eq_getElem k₂]
    rw [e₁, e₂] at hpath
    exact Option.some.inj hpath
  have hk : l₁.site.doc = l₂.site.doc := (List.getElem_inj hnd).mp heq
  exact no_two_lines_of_one_id_in_one_file p.val l₁ l₂ h₁ h₂ hid hk

/-! ## Documents: splitting text into prose and items, and putting it back -/

structure DocSplit where
  prose : List (Nat × List Char)
  items : List (Nat × (Id × Glyph × RawItem))
deriving Repr, Inhabited

/-- Read a file.  Rank = line index, so ranks are distinct by construction and
`Normalized` is not a predicate anyone has to maintain. -/
def splitDoc (k : Nat) (ls : List (List Char)) : DocSplit :=
  match ls with
  | []      => ⟨[], []⟩
  | l :: rest =>
    let d := splitDoc (k + 1) rest
    match parseItem l with
    | .ok (i, g, r) => ⟨d.prose, (k, i, g, r) :: d.items⟩
    | .error _      => ⟨(k, l) :: d.prose, d.items⟩

/-- Merge two rank-ordered lists of lines. -/
def weave (ps is : List (Nat × List Char)) : List (List Char) :=
  match ps, is with
  | [], js => js.map Prod.snd
  | qs, [] => qs.map Prod.snd
  | (a, x) :: ps', (b, y) :: is' =>
      if a ≤ b then x :: weave ps' ((b, y) :: is') else y :: weave ((a, x) :: ps') is'
termination_by ps.length + is.length

def renderSplit (d : DocSplit) : List (List Char) :=
  weave d.prose (d.items.map (fun p => (p.1, serializeItem p.2.1 p.2.2.1 p.2.2.2)))

theorem weave_nil_right (ps : List (Nat × List Char)) : weave ps [] = ps.map Prod.snd := by
  cases ps with
  | nil => rw [weave]
  | cons q qs => rw [weave]; simp

theorem weave_item_first (ps : List (Nat × List Char)) (b : Nat) (y : List Char)
    (is : List (Nat × List Char)) (h : ∀ p ∈ ps, b < p.1) :
    weave ps ((b, y) :: is) = y :: weave ps is := by
  cases ps with
  | nil =>
      cases is with
      | nil => simp [weave]
      | cons q qs => simp [weave]
  | cons p ps' =>
      obtain ⟨a, x⟩ := p
      have hba : b < a := h (a, x) (by simp)
      have : ¬ (a ≤ b) := by omega
      rw [weave]
      simp only [this, if_false]

theorem weave_prose_first (b : Nat) (x : List Char) (ps is : List (Nat × List Char))
    (h : ∀ p ∈ is, b ≤ p.1) : weave ((b, x) :: ps) is = x :: weave ps is := by
  cases is with
  | nil => rw [weave_nil_right, weave_nil_right]; simp
  | cons q qs =>
      obtain ⟨c, y⟩ := q
      have hbc : b ≤ c := h (c, y) (by simp)
      rw [weave]
      simp only [hbc, if_true]

theorem splitDoc_prose_ge (k : Nat) (ls : List (List Char)) :
    ∀ p ∈ (splitDoc k ls).prose, k ≤ p.1 := by
  induction ls generalizing k with
  | nil => intro p hp; simp [splitDoc] at hp
  | cons l rest ih =>
      intro p hp
      unfold splitDoc at hp
      simp only at hp
      split at hp
      · have := ih (k + 1) p hp; omega
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · have := ih (k + 1) p hp; omega

theorem splitDoc_items_ge (k : Nat) (ls : List (List Char)) :
    ∀ p ∈ (splitDoc k ls).items, k ≤ p.1 := by
  induction ls generalizing k with
  | nil => intro p hp; simp [splitDoc] at hp
  | cons l rest ih =>
      intro p hp
      unfold splitDoc at hp
      simp only at hp
      split at hp
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · have := ih (k + 1) p hp; omega
      · have := ih (k + 1) p hp; omega

/-- Prose is what did **not** parse as an item, so a loaded document satisfies
`docWf` by construction — `parse`'s success value is a `WfPlan`, not a value
that a separate validator later blesses. -/
theorem splitDoc_prose_not_item (k : Nat) (ls : List (List Char)) :
    ∀ q ∈ (splitDoc k ls).prose, isItemLine q.2 = false := by
  induction ls generalizing k with
  | nil => intro q hq; simp [splitDoc] at hq
  | cons l rest ih =>
      intro q hq
      unfold splitDoc at hq
      simp only at hq
      split at hq
      · exact ih (k + 1) q hq
      · rename_i e he
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp [isItemLine, he]
        · exact ih (k + 1) q hq

/-- **Round trip over a whole file.**  Splitting a document into prose and
items and putting it back reproduces the file byte for byte — including every
item line, whose state box and `^id` were *regenerated* rather than copied. -/
theorem renderSplit_splitDoc (k : Nat) (ls : List (List Char)) :
    renderSplit (splitDoc k ls) = ls := by
  induction ls generalizing k with
  | nil => simp [renderSplit, splitDoc, weave]
  | cons l rest ih =>
      unfold splitDoc
      simp only
      cases hp : parseItem l with
      | ok trip =>
          obtain ⟨i, g, r⟩ := trip
          simp only [renderSplit, List.map_cons]
          rw [weave_item_first _ k _ _ ?_]
          · rw [serialize_parse l i g r hp]
            have := ih (k + 1)
            unfold renderSplit at this
            rw [this]
          · intro q hq
            have := splitDoc_prose_ge (k + 1) rest q hq
            omega
      | error e =>
          simp only [renderSplit]
          rw [weave_prose_first _ _ _ _ ?_]
          · have := ih (k + 1)
            unfold renderSplit at this
            rw [this]
          · intro q hq
            simp only [List.mem_map] at hq
            obtain ⟨w, hw, rfl⟩ := hq
            have := splitDoc_items_ge (k + 1) rest w hw
            simp only
            omega

end Tm
