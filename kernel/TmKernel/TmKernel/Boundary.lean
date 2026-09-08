import TmKernel.Cmd
import Lean.Data.Json
/-!
# The boundary: `String → String`, and nothing else

The parser and the serializer are in the kernel, so **nothing is marshalled**:
the UI hands over the raw text of every file and gets raw text back.  One
`@[export]`, one shim function, and adding a command is one case in `dispatch`.

Two rules from the FFI spike, both applied here:

* **Every bounded type gets a smart constructor used by its decoder.**  A plain
  `structure Horizon where depth : Nat` accepted `horizon: 99`; `Fin 3` plus
  `Grain.ofNat?` rejects it.
* **`Except` all the way through; `.toOption` is banned.**  `.toOption` is how
  the spike silently turned `est: -3` into `est: null`, reproducing tm's own
  estimate-loss bug inside the verified kernel's boundary code.
-/
namespace Tm
open Lean

def grainCount : Nat := 3

/-- The only way in for a grain.  Rust cannot fabricate a `Fin 3`. -/
def Grain.ofNat? (n : Nat) : Option Grain :=
  if h : n < grainCount then some ⟨n, h⟩ else none

theorem grain_rejects_out_of_range : Grain.ofNat? 3 = none := by decide
theorem grain_rejects_99 : Grain.ofNat? 99 = none := by decide
theorem grain_accepts_month : Grain.ofNat? 2 = some month := by decide

/-! ## Building a plan from text -/

def emptyStore : Store where
  get := fun _ => none
  dom := []
  domSpec := by intro i; simp
  domNodup := by simp

def Store.insert (s : Store) (i : Id) (e : Entity) : Store :=
  if h : i ∈ s.dom then
    { get := fun j => if j = i then some e else s.get j
      dom := s.dom
      domSpec := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [h]
        · simp only [hj, if_false]; exact s.domSpec j
      domNodup := s.domNodup }
  else
    { get := fun j => if j = i then some e else s.get j
      dom := i :: s.dom
      domSpec := by
        intro j
        by_cases hj : j = i
        · subst hj; simp
        · simp only [List.mem_cons, hj, false_or, if_false]; exact s.domSpec j
      domNodup := by simp [List.nodup_cons, h, s.domNodup] }

structure LoadedDoc where
  path  : List Char
  reg   : Option Region
  prose : List (Nat × List Char)
deriving Repr, Inhabited

/-- Load errors are the diagnostics `tm check` prints.  Acceptance is exactly
"`load` returned `.ok`", so the checker cannot be weaker than the invariant. -/
inductive LErr
  | dupId (i : Id)
  | badLine (path : List Char) (n : Nat) (why : PErr)
deriving Repr

/-- Turn one document's parsed items into entities at their sites. -/
def entitiesOfDoc (k : DocIx) (d : DocSplit) : List (Id × Entity) :=
  d.items.map (fun p =>
    let (rank, i, g, r) := p
    let st : Status :=
      match g with
      | .done    => .settled .done
      | .dropped => .settled .dropped
      | .active  => .live .self
      | .waiting => .live .world
      | .todo    => .live .free
      | .demoted => .live .free
    (i, (⟨⟨⟨k, rank⟩, none, st, r, []⟩, rfl⟩ : Entity)))

/-- **`tm check`'s `dup-id` becomes an acceptance rule**, and downstream it is
unrepresentable: the store is a function. -/
def loadStore (items : List (Id × Entity)) : Except LErr Store :=
  match h : (items.map Prod.fst) with
  | ids =>
    if hn : ids.Nodup then
      .ok (items.foldl (fun s p => s.insert p.1 p.2) emptyStore)
    else
      match ids with
      | []     => .ok emptyStore
      | i :: _ => .error (.dupId i)

/-! ## Rendering a plan back to text -/

def insertByRank (x : Nat × List Char) : List (Nat × List Char) → List (Nat × List Char)
  | []      => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertByRank x ys

def sortByRank (l : List (Nat × List Char)) : List (Nat × List Char) :=
  l.foldr insertByRank []

def renderDocAt (p : PlanCore) (k : DocIx) (d : Doc) : List (List Char) :=
  weave (sortByRank d.prose)
    (sortByRank ((p.lines.filter (fun l => l.site.doc == k)).map
      (fun l => (l.site.rank, l.text))))

/-- Every document a request produces holds prose only, by construction. -/
def mkDocs (ds : List (List Char × List (Nat × List Char))) : List Doc :=
  ds.map (fun d => ⟨d.1, d.2⟩)

/-! ## JSON -/

def jsonErr (s : String) : Json := Json.mkObj [("err", Json.str s)]

def getStr (j : Json) (k : String) : Except String String := j.getObjValAs? String k
def getNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k

def getArr (j : Json) (k : String) : Except String (Array Json) := do
  let v ← j.getObjVal? k
  v.getArr?

def strLines (j : Json) : Except String (List (List Char)) := do
  let a ← j.getArr?
  let mut out : List (List Char) := []
  for x in a do
    let s ← x.getStr?
    out := out ++ [s.toList]
  return out

structure ReqDoc where
  path  : String
  reg   : Option Region
  lines : List (List Char)

def parseRegion (j : Json) : Except String (Option Region) := do
  match j.getObjVal? "grain" with
  | .error _ => return none
  | .ok gv =>
    match gv with
    | .null => return none
    | _ =>
      let gn ← gv.getNat?
      match Grain.ofNat? gn with
      | none   => throw s!"grain {gn} out of range (0..{grainCount - 1})"
      | some g =>
        let ix ← getNat j "ix"
        return some ⟨g, ix⟩

def parseDoc (j : Json) : Except String ReqDoc := do
  let path ← getStr j "path"
  let reg ← parseRegion j
  let lv ← j.getObjVal? "lines"
  let lines ← strLines lv
  return ⟨path, reg, lines⟩

/-- One command as the UI sends it. -/
inductive ReqCmd
  | move (i : Id) (doc : DocIx)
  | drop (i : Id)
  | est  (i : Id) (v : Nat)
  | demote (i : Id) (doc : DocIx) (period : Nat)
  | readopt (i : Id) (doc : DocIx)

def parseCmd (j : Json) : Except String ReqCmd := do
  let op ← getStr j "op"
  match op with
  | "move" => return .move (← getStr j "id").toList (← getNat j "doc")
  | "drop" => return .drop (← getStr j "id").toList
  | "est"  => return .est (← getStr j "id").toList (← getNat j "min")
  | "demote" => return .demote (← getStr j "id").toList (← getNat j "doc") (← getNat j "period")
  | "readopt" => return .readopt (← getStr j "id").toList (← getNat j "doc")
  | _ => throw s!"unknown op {op}"

def kerrName : KErr → String
  | .occupied   => "occupied"
  | .noSuchId   => "noSuchId"
  | .notDemoted => "notDemoted"
  | .badHorizon => "badHorizon"

/-- Fresh rank in the destination document: strictly greater than every rank
already there, so a move can never collide on a rank either. -/
def freshRank (p : PlanCore) (k : DocIx) : Nat :=
  let proseMax :=
    match p.docs[k]? with
    | none   => 0
    | some d => d.prose.foldl (fun a q => Nat.max a q.1) 0
  let lineMax := (p.lines.filter (fun l => l.site.doc == k)).foldl
    (fun acc l => Nat.max acc l.site.rank) 0
  1 + Nat.max proseMax lineMax

def applyCmd (c : ReqCmd) (p : WfPlan) : Except KErr WfPlan :=
  match c with
  | .move i d       => cmdMove i ⟨d, freshRank p.val d⟩ p
  | .drop i         => cmdDrop i p
  | .est i v        => cmdSetEst v i p
  | .demote i d per => cmdDemote i ⟨d, freshRank p.val d⟩ per p
  | .readopt i d    => cmdReadopt i ⟨d, freshRank p.val d⟩ p

def applyAll : List ReqCmd → WfPlan → Except KErr WfPlan
  | [],      p => .ok p
  | c :: cs, p => (applyCmd c p).bind (applyAll cs)

def lerrJson : LErr → Json
  | .dupId i        => Json.mkObj [("dupId", Json.str (String.ofList i))]
  | .badLine pa n w => Json.mkObj [("badLine", Json.mkObj
      [("path", Json.str (String.ofList pa)), ("line", Json.num n), ("why", Json.str (toString (repr w)))])]

def run (j : Json) : Except Json Json := do
  let docsJ ←
    match getArr j "docs" with
    | .ok a => pure a
    | .error e => throw (jsonErr e)
  let mut docs : List ReqDoc := []
  for dj in docsJ do
    match parseDoc dj with
    | .ok d => docs := docs ++ [d]
    | .error e => throw (jsonErr e)
  let cmdsJ ←
    match getArr j "cmds" with
    | .ok a => pure a
    | .error _ => pure #[]
  let mut cmds : List ReqCmd := []
  for cj in cmdsJ do
    match parseCmd cj with
    | .ok c => cmds := cmds ++ [c]
    | .error e => throw (jsonErr e)
  -- parse every document
  let splits := docs.map (fun d => splitDoc 0 d.lines)
  let items := (splits.zipIdx.map (fun p => entitiesOfDoc p.2 p.1)).flatten
  let store ←
    match loadStore items with
    | .ok s => pure s
    | .error e => throw (Json.mkObj [("err", lerrJson e)])
  let planDocs : List Doc :=
    docs.map (fun d => ⟨d.path.toList, (splitDoc 0 d.lines).prose⟩)
  -- `parse`'s success value is a `WfPlan` **by construction**: prose is exactly
  -- what did not parse as an item, so there is no separate validator to drift.
  let hwf : planWf ⟨planDocs, store⟩ = true := by
    show List.all planDocs docWf = true
    simp only [planDocs, List.all_eq_true, List.mem_map]
    rintro d ⟨x, _, rfl⟩
    show List.all (splitDoc 0 x.lines).prose (fun q => !isItemLine q.2) = true
    simp only [List.all_eq_true]
    intro q hq
    simp [splitDoc_prose_not_item 0 x.lines q hq]
  let plan : WfPlan := ⟨⟨planDocs, store⟩, hwf⟩
  let plan' ←
    match applyAll cmds plan with
    | .ok q => pure q
    | .error k => throw (Json.mkObj [("err", Json.mkObj [("kernel", Json.str (kerrName k))])])
  let outDocs := (plan'.val.docs.zipIdx.map (fun p =>
    Json.mkObj
      [("path", Json.str (String.ofList p.1.path)),
       ("lines", Json.arr ((renderDocAt plan'.val p.2 p.1).map
          (fun l => Json.str (String.ofList l))).toArray)]))
  return Json.mkObj [("ok", Json.mkObj [("docs", Json.arr outDocs.toArray)])]

/-- Total: every path returns a `String`.  No `panic!`, no `!`, no `partial`. -/
def call (input : String) : String :=
  match Json.parse input with
  | .error e => Json.compress (jsonErr s!"bad json: {e}")
  | .ok j =>
    match run j with
    | .error e => Json.compress e
    | .ok r    => Json.compress r

@[export tm_kernel_call]
def callExport (input : String) : String := call input

end Tm
