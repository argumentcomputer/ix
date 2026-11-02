/-
  Ix.Frontend.CanonBlock: In-Elaborator Canonicalization of Mutual Blocks
  and Inductive Constructors (Ix Paper §§4.3, 9.2).

  Performs:
  1. Structural nameless expression comparison (`compareExpr`) matching the Ixon
     canonical block comparator (`Order.lean`).
  2. Canonical sorting of inductive constructors (`sortInductiveCtors`) by nameless
     structural skeleton `(levelParams.size, numParams, numFields, type)`, breaking
     ties among structurally α-identical constructors of the same inductive
     (e.g., `Bool.false` vs `Bool.true`, `Ordering.lt`/`eq`/`gt`) by **source declaration order**.
  3. Partition-refinement canonical ordering of mutual inductive blocks (`canonicalizeInductiveBlock`)
     and mutual definition blocks (`canonicalizeDefBlock`), plus post-elaboration
     minimal SCC splitting (`splitElaboratedDefSCCs`).
-/
module

public import Ix.Frontend.Elab.Meta
public import Ix.Mutual
public import Ix.SOrder
public import Ix.SemanticContract
public import Ix.Ixon.ReduceUniverse
public import Ix.Compile.Canon.Graph

@[expose] public section

namespace Ix.Frontend.Canon

open Ix (Name Level Expr MutConst Def Ind ConstructorVal RecursorVal RecursorRule)
open Ix.Frontend

/-! ## Canonical Universe & Expression Comparator -/

/-- Context for nameless structural comparison: external constant address resolver
    and current mutual-block equivalence class map `mutCtx` (keyed by `Ix.Name.leanCmp`). -/
structure CanonCmpCtx where
  addrOf : Ix.Name → Address
  mutCtx : NameMap Nat

/-- Convert an `Ix.Level` into a positional `Ixon.Univ` relative to `ctx : List Ix.Name`. -/
def levelToUniv (ctx : List Ix.Name) : Ix.Level → Ixon.Univ
  | .zero _     => .zero
  | .succ l _   => .succ (levelToUniv ctx l)
  | .max a b _  => .max (levelToUniv ctx a) (levelToUniv ctx b)
  | .imax a b _ => .imax (levelToUniv ctx a) (levelToUniv ctx b)
  | .param n _  =>
    match ctx.idxOf? n with
    | some i => .var i.toUInt64
    | none   => .zero
  | .mvar _ _   => .zero

/-- Structural total order on `Ixon.Univ`: `zero < succ < max < imax < var`. -/
def compareUniv : Ixon.Univ → Ixon.Univ → Ordering
  | .zero, .zero => .eq
  | .zero, _     => .lt
  | _, .zero     => .gt
  | .succ x, .succ y => compareUniv x y
  | .succ _, _   => .lt
  | _, .succ _   => .gt
  | .max a b, .max c d => (compareUniv a c).then (compareUniv b d)
  | .max .., _   => .lt
  | _, .max ..   => .gt
  | .imax a b, .imax c d => (compareUniv a c).then (compareUniv b d)
  | .imax .., _  => .lt
  | _, .imax ..  => .gt
  | .var i, .var j => compare i j

/-- Compare two `Ix.Level`s after `Ixon.reduceUniv` normalization. -/
def compareLevel (xctx yctx : List Ix.Name) (x y : Ix.Level) : SOrder :=
  let ux := Ixon.reduceUniv (levelToUniv xctx x)
  let uy := Ixon.reduceUniv (levelToUniv yctx y)
  ⟨true, compareUniv ux uy⟩

/-- Pointwise comparison of universe level lists. -/
def compareLevels (xctx yctx : List Ix.Name) : List Ix.Level → List Ix.Level → SOrder
  | [], []           => ⟨true, .eq⟩
  | [], _ :: _       => ⟨true, .lt⟩
  | _ :: _, []       => ⟨true, .gt⟩
  | x :: xs, y :: ys =>
    let o := compareLevel xctx yctx x y
    if o.ord != .eq then o else SOrder.cmp o (compareLevels xctx yctx xs ys)

/-- Structural size of an `Ix.Expr` for termination of `compareExpr`. -/
def exprSize : Ix.Expr → Nat
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 1
  | .app f a _          => exprSize f + exprSize a + 1
  | .lam _ t b _ _      => exprSize t + exprSize b + 1
  | .forallE _ t b _ _  => exprSize t + exprSize b + 1
  | .letE _ t v b _ _   => exprSize t + exprSize v + exprSize b + 1
  | .proj _ _ s _       => exprSize s + 1
  | .mdata _ s _        => exprSize s + 1

@[simp] theorem exprSize_app (f a : Ix.Expr) (h : Address) :
    exprSize (.app f a h) = exprSize f + exprSize a + 1 := rfl
@[simp] theorem exprSize_lam (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo) (h : Address) :
    exprSize (.lam n t b bi h) = exprSize t + exprSize b + 1 := rfl
@[simp] theorem exprSize_forallE (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo) (h : Address) :
    exprSize (.forallE n t b bi h) = exprSize t + exprSize b + 1 := rfl
@[simp] theorem exprSize_letE (n : Ix.Name) (t v b : Ix.Expr) (nd : Bool) (h : Address) :
    exprSize (.letE n t v b nd h) = exprSize t + exprSize v + exprSize b + 1 := rfl
@[simp] theorem exprSize_proj (n : Ix.Name) (i : Nat) (s : Ix.Expr) (h : Address) :
    exprSize (.proj n i s h) = exprSize s + 1 := rfl
@[simp] theorem exprSize_mdata (d : Array (Ix.Name × Ix.DataValue)) (s : Ix.Expr) (h : Address) :
    exprSize (.mdata d s h) = exprSize s + 1 := rfl

/-- Compare two constant/structure references:
    - Identical names are `.eq` (`strong := true`).
    - Two in-block names compare by their current class index in `mutCtx` (`strong := false`).
    - In-block sorts before external (`strong := true`).
    - Two external names compare by `c.addrOf`. -/
def compareRef (c : CanonCmpCtx) (x y : Ix.Name) : SOrder :=
  if Name.beqStruct x y then
    ⟨true, .eq⟩
  else
    match c.mutCtx.get? x, c.mutCtx.get? y with
    | some nx, some ny => ⟨false, compare nx ny⟩
    | some _, none     => ⟨true, .lt⟩
    | none, some _     => ⟨true, .gt⟩
    | none, none       => ⟨true, compare (c.addrOf x) (c.addrOf y)⟩

/-- Total, name-irrelevant structural comparator on `Ix.Expr` matching the Ixon canonical order. -/
def compareExpr (c : CanonCmpCtx) (xl yl : List Ix.Name) (x y : Ix.Expr) : SOrder :=
  match x, y with
  | .mdata dx xi hx, .mdata dy yi hy =>
    if SemanticContract.hasMetadata dx then
      if SemanticContract.hasMetadata dy then
        match SemanticContract.read dx, SemanticContract.read dy with
        | .ok cx, .ok cy =>
          let o := compare cx.orderKey cy.orderKey
          if o != .eq then ⟨true, o⟩ else compareExpr c xl yl xi yi
        | _, _ => compareExpr c xl yl xi yi
      else compareExpr c xl yl (.mdata dx xi hx) yi
    else compareExpr c xl yl xi (.mdata dy yi hy)
  | .mdata d xi _, y =>
    if SemanticContract.hasMetadata d then ⟨true, .gt⟩
    else compareExpr c xl yl xi y
  | x, .mdata d yi _ =>
    if SemanticContract.hasMetadata d then ⟨true, .lt⟩
    else compareExpr c xl yl x yi
  | .bvar i _, .bvar j _ => ⟨true, compare i j⟩
  | .bvar .., _          => ⟨true, .lt⟩
  | _, .bvar ..          => ⟨true, .gt⟩
  | .sort u _, .sort v _ => compareLevel xl yl u v
  | .sort .., _          => ⟨true, .lt⟩
  | _, .sort ..          => ⟨true, .gt⟩
  | .const xn xls _, .const yn yls _ =>
    let us := compareLevels xl yl xls.toList yls.toList
    if us.ord != .eq then us else SOrder.cmp us (compareRef c xn yn)
  | .const .., _         => ⟨true, .lt⟩
  | _, .const ..         => ⟨true, .gt⟩
  | .app xf xa _, .app yf ya _ =>
    let fo := compareExpr c xl yl xf yf
    if fo.ord != .eq then fo else SOrder.cmp fo (compareExpr c xl yl xa ya)
  | .app .., _           => ⟨true, .lt⟩
  | _, .app ..           => ⟨true, .gt⟩
  | .lam _ xt xb _ _, .lam _ yt yb _ _ =>
    let to_ := compareExpr c xl yl xt yt
    if to_.ord != .eq then to_ else SOrder.cmp to_ (compareExpr c xl yl xb yb)
  | .lam .., _           => ⟨true, .lt⟩
  | _, .lam ..           => ⟨true, .gt⟩
  | .forallE _ xt xb _ _, .forallE _ yt yb _ _ =>
    let to_ := compareExpr c xl yl xt yt
    if to_.ord != .eq then to_ else SOrder.cmp to_ (compareExpr c xl yl xb yb)
  | .forallE .., _       => ⟨true, .lt⟩
  | _, .forallE ..       => ⟨true, .gt⟩
  | .letE _ xt xv xb xnd _, .letE _ yt yv yb ynd _ =>
    let to_ := compareExpr c xl yl xt yt
    if to_.ord != .eq then to_
    else
      let vo := SOrder.cmp to_ (compareExpr c xl yl xv yv)
      if vo.ord != .eq then vo
      else
        let bo := SOrder.cmp vo (compareExpr c xl yl xb yb)
        if bo.ord != .eq then bo
        else SOrder.cmp bo ⟨true, compare xnd ynd⟩
  | .letE .., _          => ⟨true, .lt⟩
  | _, .letE ..          => ⟨true, .gt⟩
  | .lit a _, .lit b _   => ⟨true, compare a b⟩
  | .lit .., _           => ⟨true, .lt⟩
  | _, .lit ..           => ⟨true, .gt⟩
  | .fvar x _, .fvar y _ => ⟨true, Name.cmpStruct x y⟩
  | .fvar .., _          => ⟨true, .lt⟩
  | _, .fvar ..          => ⟨true, .gt⟩
  | .mvar x _, .mvar y _ => ⟨true, Name.cmpStruct x y⟩
  | .mvar .., _          => ⟨true, .lt⟩
  | _, .mvar ..          => ⟨true, .gt⟩
  | .proj xn xi xs _, .proj yn yi ys _ =>
    let ro := compareRef c xn yn
    if ro.ord != .eq then ro
    else
      let io := SOrder.cmp ro ⟨true, compare xi yi⟩
      if io.ord != .eq then io
      else SOrder.cmp io (compareExpr c xl yl xs ys)
termination_by exprSize x + exprSize y
decreasing_by
  all_goals simp only [exprSize_app, exprSize_lam, exprSize_forallE,
    exprSize_letE, exprSize_proj, exprSize_mdata]
  all_goals omega

/-! ## Inductive Constructor Canonicalization (Tie-Breaking by Source Order) -/

/-- Compare two constructors `x` and `y` of an inductive by their nameless structural
    skeleton `(levelParams.size, numParams, numFields, type)`.
    Note: `cidx` is intentionally NOT compared here so that structurally distinct
    constructors (e.g. `Nat.succ` vs `Nat.zero`) are ordered by structure rather than
    initial source index; ties (`ord == .eq`) among structurally α-identical constructors
    (e.g. `Bool.false` vs `Bool.true`) are broken by source order (`compare x.cidx y.cidx`)! -/
def compareCtorSkeleton (c : CanonCmpCtx) (xl yl : List Ix.Name)
    (x y : ConstructorVal) : SOrder :=
  let o1 : SOrder := ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩
  if o1.ord != .eq then o1 else
  let o2 : SOrder := ⟨true, compare x.numParams y.numParams⟩
  if o2.ord != .eq then o2 else
  let o3 : SOrder := ⟨true, compare x.numFields y.numFields⟩
  if o3.ord != .eq then o3 else
  compareExpr c xl yl x.cnst.type y.cnst.type

/-- Pure, total insertion sort on `Array α` (avoids `Array.qsort`'s `partial` helper). -/
def sortArrayBy (xs : Array α) (lt : α → α → Bool) : Array α :=
  let rec insert (x : α) : List α → List α
    | []      => [x]
    | y :: ys => if lt y x then y :: insert x ys else x :: y :: ys
  (xs.foldl (fun acc x => insert x acc) []).toArray

/-- Canonicalize the constructors of a single inductive `indVal` under `c : CanonCmpCtx`:
    - Sorts constructors by `compareCtorSkeleton`
    - Breaks ties (`ord == .eq`) among α-identical constructors by original `cidx` (source order!)
    - Re-assigns `cidx := 0, 1, ...` and updates `indVal.ctors`. -/
def sortInductiveCtors (c : CanonCmpCtx) (indVal : Ix.InductiveVal)
    (ctors : Array ConstructorVal) : Ix.InductiveVal × Array ConstructorVal :=
  if ctors.size ≤ 1 then
    let ctors' := ctors.mapIdx fun idx cv => { cv with cidx := idx }
    ({ indVal with ctors := ctors'.map (·.cnst.name) }, ctors')
  else
    let lvlList := indVal.cnst.levelParams.toList
    let sorted := sortArrayBy ctors fun a b =>
      let so := compareCtorSkeleton c lvlList lvlList a b
      match so.ord with
      | .lt => true
      | .gt => false
      | .eq => a.cidx < b.cidx
    let reindexed := sorted.mapIdx fun newIdx cv => { cv with cidx := newIdx }
    let indVal' := { indVal with ctors := reindexed.map (·.cnst.name) }
    (indVal', reindexed)

/-! ## Mutual Inductive & Mutual Definition Partition Refinement -/

/-- Compare two `Ind` records structurally (after their constructors have been canonicalized). -/
def compareIndStruct (c : CanonCmpCtx) (x y : Ind) : SOrder :=
  let hdr := SOrder.cmpMany ⟨true, compare x.levelParams.size y.levelParams.size⟩
    [⟨true, compare x.numParams y.numParams⟩,
     ⟨true, compare x.numIndices y.numIndices⟩,
     ⟨true, compare x.ctors.size y.ctors.size⟩]
  if hdr.ord != .eq then hdr
  else
    let xl := x.levelParams.toList
    let yl := y.levelParams.toList
    let tyOrd := SOrder.cmp hdr (compareExpr c xl yl x.type y.type)
    if tyOrd.ord != .eq then tyOrd
    else
      let rec cmpCtors : List ConstructorVal → List ConstructorVal → SOrder
        | [], []           => ⟨true, .eq⟩
        | [], _ :: _       => ⟨true, .lt⟩
        | _ :: _, []       => ⟨true, .gt⟩
        | a :: as, b :: bs =>
          let co := compareCtorSkeleton c xl yl a b
          if co.ord != .eq then co else SOrder.cmp co (cmpCtors as bs)
      SOrder.cmp tyOrd (cmpCtors x.ctors.toList y.ctors.toList)

/-- Compare two `Def` records structurally by `(kind, levelParams.size, type, value)`. -/
def compareDefStruct (c : CanonCmpCtx) (x y : Def) : SOrder :=
  let o1 : SOrder := ⟨true, compare x.kind y.kind⟩
  if o1.ord != .eq then o1 else
  let o2 : SOrder := ⟨true, compare x.levelParams.size y.levelParams.size⟩
  if o2.ord != .eq then o2 else
  let xl := x.levelParams.toList
  let yl := y.levelParams.toList
  let tyOrd := compareExpr c xl yl x.type y.type
  if tyOrd.ord != .eq then tyOrd
  else SOrder.cmp tyOrd (compareExpr c xl yl x.value y.value)

/-- Compare two `MutConst` records structurally. -/
def compareMutConst (c : CanonCmpCtx) (x y : MutConst) : SOrder :=
  match x, y with
  | .defn dx, .defn dy => compareDefStruct c dx dy
  | .indc ix, .indc iy => compareIndStruct c ix iy
  | .defn _, _         => ⟨true, .lt⟩
  | _, .defn _         => ⟨true, .gt⟩
  | .indc _, .recr _   => ⟨true, .lt⟩
  | .recr _, .indc _   => ⟨true, .gt⟩
  | .recr rx, .recr ry =>
    compareExpr c rx.cnst.levelParams.toList ry.cnst.levelParams.toList rx.cnst.type ry.cnst.type

/-- Build a `NameMap Nat` mapping each equivalence class's members (and constructors) to class indices. -/
def buildClassesMutCtx (classes : List (List (Nat × MutConst))) : NameMap Nat := Id.run do
  let mut ctx : NameMap Nat := NameMap.empty
  let mut ctorSlot := classes.length
  for (cls, clsIdx) in classes.zipIdx do
    for (_, mc) in cls do
      ctx := ctx.insert mc.name clsIdx
      for (ctor, cidx) in mc.ctors.zipIdx do
        ctx := ctx.insert ctor.cnst.name (ctorSlot + cidx)
      ctorSlot := ctorSlot + mc.ctors.size
  return ctx

/-- Refine a single equivalence class of `(sourceIdx, MutConst)` pairs under `c : CanonCmpCtx`,
    breaking ties among structurally α-equivalent members by original `sourceIdx`. -/
def refineOneClass (c : CanonCmpCtx) (cls : List (Nat × MutConst)) : List (List (Nat × MutConst)) :=
  match cls with
  | []  => []
  | [x] => [[x]]
  | xs  =>
    let arr := sortArrayBy xs.toArray fun (i, a) (j, b) =>
      match (compareMutConst c a b).ord with
      | .lt => true
      | .gt => false
      | .eq => i < j
    -- Group adjacent structurally equal members (`ord == .eq`)
    let groups : Array (Array (Nat × MutConst)) := arr.foldl (fun acc elem =>
      if acc.isEmpty then
        #[#[elem]]
      else
        let lastGroup := acc.back?.getD #[elem]
        let (_, rep) := lastGroup.getD 0 elem
        if (compareMutConst c rep elem.2).ord == .eq then
          acc.pop.push (lastGroup.push elem)
        else
          acc.push #[elem]
    ) #[]
    groups.toList.map Array.toList

/-- Partition-refinement loop (`sortClasses`) until the class partition stabilizes. -/
def refineClassesLoop (addrOf : Ix.Name → Address) :
    Nat → List (List (Nat × MutConst)) → List (List (Nat × MutConst))
  | 0, classes => classes
  | fuel + 1, classes =>
    let mutCtx := buildClassesMutCtx classes
    let c : CanonCmpCtx := { addrOf, mutCtx }
    let refined := classes.flatMap (refineOneClass c)
    if refined.length == classes.length then refined
    else refineClassesLoop addrOf fuel refined

/-- Canonicalize a mutual inductive block `(indVal, ctors)` array:
    1. Canonicalizes each inductive's constructor order (breaking ties by source declaration order).
    2. Canonicalizes the mutual inductive member order via partition refinement.
    3. Updates `all` on every `InductiveVal` in the block to the canonical member name order. -/
def canonicalizeInductiveBlock (addrOf : Ix.Name → Address)
    (items : Array (Ix.InductiveVal × Array ConstructorVal)) :
    Array (Ix.InductiveVal × Array ConstructorVal) :=
  if items.isEmpty then #[]
  else
    -- Build initial `mutCtx` where all inductives in the block share class 0
    let initMutCtx : NameMap Nat := items.foldl (fun ctx (iv, _) => ctx.insert iv.cnst.name 0) NameMap.empty
    let initCmpCtx : CanonCmpCtx := { addrOf, mutCtx := initMutCtx }
    -- Step 1: Canonicalize each inductive's constructors under `initCmpCtx`
    let itemsWithSortedCtors := items.map fun (iv, ctors) =>
      sortInductiveCtors initCmpCtx iv ctors
    if itemsWithSortedCtors.size == 1 then
      match itemsWithSortedCtors[0]? with
      | some (iv, ctors) =>
        let iv' := { iv with all := #[iv.cnst.name] }
        #[(iv', ctors)]
      | none => #[]
    else
      -- Step 2: Run partition refinement on the inductives in the mutual block
      let seed : List (Nat × MutConst) := (itemsWithSortedCtors.mapIdx fun idx (iv, ctors) =>
        (idx, MutConst.fromInductiveVal iv ctors)).toList
      let refined := refineClassesLoop addrOf (seed.length + 2) [seed]
      let finalMutCtx := buildClassesMutCtx refined
      let finalCmpCtx : CanonCmpCtx := { addrOf, mutCtx := finalMutCtx }
      let orderedIdxs : Array Nat := (refined.flatMap (fun cls => cls.map (·.1))).toArray
      let orderedItems := orderedIdxs.filterMap fun idx =>
        match itemsWithSortedCtors[idx]? with
        | some (iv, ctors) => some (sortInductiveCtors finalCmpCtx iv ctors)
        | none             => none
      let canonAll : Array Ix.Name := orderedItems.map (·.1.cnst.name)
      orderedItems.map fun (iv, ctors) =>
        ({ iv with all := canonAll }, ctors)

/-! ## Post-Elaboration Minimal SCC Splitting & Canonicalization for Definitions -/

/-- Collect all constant names referenced in `e` that belong to `candidates`. -/
def collectRefsInSet (candidates : NameSet) (e : Ix.Expr) : NameSet :=
  go e NameSet.empty
where
  go : Ix.Expr → NameSet → NameSet
    | .const nm _ _, acc      => if candidates.contains nm then acc.insert nm else acc
    | .app f a _, acc         => go a (go f acc)
    | .lam _ t b _ _, acc     => go b (go t acc)
    | .forallE _ t b _ _, acc => go b (go t acc)
    | .letE _ t v b _ _, acc  => go b (go v (go t acc))
    | .proj nm _ s _, acc     => go s (if candidates.contains nm then acc.insert nm else acc)
    | .mdata _ x _, acc       => go x acc
    | _, acc                  => acc

/-- Pure fallback `Def` using `Ix.Frontend.Syntax` constructors (avoids `Ix.instInhabitedDef`). -/
def emptyCanonDef : Def := {
  name        := Name.mkAnon
  levelParams := #[]
  type        := Expr.mkBVar 0
  value       := Expr.mkBVar 0
  kind        := .defn
  safety      := .safe
  hints       := .opaque
  all         := #[]
}

/-- Given an array of elaborated value declarations (`Def`), split them into minimal
    strongly connected components based on their actual elaborated `type` and `value`
    constant references, and canonically order each SCC via partition refinement! -/
def canonicalizeElaboratedDefs (addrOf : Ix.Name → Address)
    (defs : Array Def) : Array (Array Def) :=
  if defs.isEmpty then #[]
  else if defs.size == 1 then
    let d := arrayGetD defs 0 emptyCanonDef
    #[#[{ d with all := #[d.name] }]]
  else
    let nameSet : NameSet := defs.foldl (fun s d => s.insert d.name) NameSet.empty
    let nameToIdx : NameMap Nat := (defs.mapIdx fun i d => (d.name, i)).foldl
      (fun m (nm, i) => m.insert nm i) NameMap.empty
    let adj : Array (Array Nat) := defs.mapIdx fun i d =>
      let refs := collectRefsInSet nameSet d.type
      let refs := (collectRefsInSet nameSet d.value).foldl (fun s n => s.insert n) refs
      refs.toList.filterMap (fun nm =>
        match nameToIdx.get? nm with
        | some j => if i == j then none else some j
        | none   => none) |>.toArray
    match tarjanCondensation adj with
    | none =>
      let allNames := defs.map (·.name)
      #[defs.map fun d => { d with all := allNames }]
    | some cond =>
      cond.comps.map fun comp =>
        if comp.size == 1 then
          let idx := comp.getD 0 0
          let d := defs.getD idx emptyCanonDef
          #[{ d with all := #[d.name] }]
        else
          let seed : List (Nat × MutConst) := (comp.map fun idx =>
            (idx, MutConst.defn (defs.getD idx emptyCanonDef))).toList
          let refined := refineClassesLoop addrOf (seed.length + 2) [seed]
          let orderedIdxs := (refined.flatMap (fun cls => cls.map (·.1))).toArray
          let orderedDefs := orderedIdxs.map fun idx => defs.getD idx emptyCanonDef
          let canonAll := orderedDefs.map (·.name)
          orderedDefs.map fun d => { d with all := canonAll }

end Ix.Frontend.Canon
