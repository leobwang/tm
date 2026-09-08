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

def planWf (p : PlanCore) : Bool := p.docs.all docWf

/-- The plan.  You cannot make one without discharging `planWf`. -/
def WfPlan := { p : PlanCore // planWf p = true }

def WfPlan.val' (p : WfPlan) : PlanCore := p.val

/-- **No prose line is an item line.**  So the only item lines a document emits
are the ones its entities render, and `no_two_lines_of_one_id_in_one_file`
covers all of them. -/
theorem prose_is_never_an_item (p : WfPlan) (d : Doc) (hd : d ∈ p.val.docs)
    (q : Nat × List Char) (hq : q ∈ d.prose) : isItemLine q.2 = false := by
  have h1 : docWf d = true := List.all_eq_true.1 p.property d hd
  have h2 := List.all_eq_true.1 h1 q hq
  simpa using h2

/-- Changing the store cannot change `planWf`, which only reads `docs`.  This
is why the plan-level obligation costs nothing per command. -/
theorem planWf_store (p : PlanCore) (s : Store) : planWf { p with store := s } = planWf p := rfl

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
