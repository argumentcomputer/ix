/-
  Ix.Compile.Image.Spec: from Pass 1's canonical form of a Lean block
  (`Ix.Compile.Canon.BlockCanon`) to what the image generator needs.

  * `CanonDecl`: the canonical inductive declarations of the block, one
    mutual block per component in dependency order, each class a member
    (its representative's type and constructors, every member of the Lean
    block renamed to its class's canonical inductive). These are the Ix
    inductives Pass 2 emits; the types of *their* recursors (the
    specification's `recTy`) are the generator's input. The tests obtain
    those recursors from Lean's kernel by declaring these blocks; the
    compiler has them from Pass 2.
  * `ImageSpec`: the renaming `tr_N` on the names that occur in a Lean
    recursor's type (members ↦ canonical inductive, constructors ↦ canonical
    constructor by position) and the set of canonical inductives (the first
    candidate list of the eliminator choice, design document §4.1).

  Names of canonical constants are placeholders (`Naming`): the compiler
  resolves them to addresses; the tests choose readable ones.

  Universe parameters: a canonical member keeps the Lean block's universe
  list (D3/D16, design document §2.4, §4.7 (a)).
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Block
public section

namespace Ix.Compile.Image

open Ix (Name Level Expr ConstantInfo InductiveVal ConstructorVal)
open Ix.Compile.Canon (BlockCanon ComponentCanon replaceConstNames nameReplacePrefix)

/-- Placeholder names of canonical constants. -/
structure Naming where
  /-- The canonical inductive of class `cls` of component `comp`, whose
  representative is `rep`. -/
  ind : (comp cls : Nat) → (rep : Name) → Name
  /-- The image constant of Lean recursor `r`. -/
  img : (r : Name) → Name

/-- Default placeholders: `rep._ix` for the canonical inductive (the `_ix`
reserved component of D14) and `r._img` for the image of `r`. -/
def Naming.default : Naming where
  ind _ _ rep := Ix.Name.mkStr rep "_ix"
  img r := Ix.Name.mkStr r "_img"

structure CanonCtor where
  name : Name
  type : Expr
  deriving Inhabited

structure CanonType where
  name : Name
  type : Expr
  ctors : Array CanonCtor
  deriving Inhabited

/-- One canonical inductive block (a component of the Lean block). -/
structure CanonDecl where
  comp : Nat
  levelParams : Array Name
  numParams : Nat
  isUnsafe : Bool
  types : Array CanonType
  deriving Inhabited

/-- What the image generator needs about one changed Lean block. -/
structure ImageSpec where
  block : BlockCanon
  /-- Lean member ↦ canonical inductive. -/
  tyMap : Std.HashMap Name Name
  /-- Lean constructor ↦ canonical constructor (same position in the
  representative's constructor list). -/
  ctorMap : Std.HashMap Name Name
  /-- Canonical inductives, components in dependency order, classes in
  canonical order. -/
  canonInds : Array Name
  /-- The canonical declarations, in dependency order. -/
  decls : Array CanonDecl
  naming : Naming

/-- `tr_N` on a Lean recursor's type or rule: members and constructors
renamed (constant heads only, as the prototype's `trExpr`). -/
def ImageSpec.tr (s : ImageSpec) (e : Expr) : Expr :=
  let m := s.ctorMap.fold (init := s.tyMap) fun m k v => m.insert k v
  Ix.Compile.Canon.canonicalizeConstNames m e

def ImageSpec.trName (s : ImageSpec) (n : Name) : Name :=
  match s.tyMap.get? n with
  | some m => m
  | none => (s.ctorMap.get? n).getD n

def indOf (const? : Name → Option ConstantInfo) (n : Name) : Except String InductiveVal :=
  match const? n with
  | some (.inductInfo v) => pure v
  | _ => throw s!"image spec: {n.pretty} is not an inductive"

/-- The canonical constructor name: the representative's constructor with
its prefix replaced. -/
def canonCtorName (rep canon ctor : Name) : Name :=
  let n := nameReplacePrefix ctor rep canon
  if n == ctor then
    match ctor with
    | .str _ s _ => Ix.Name.mkStr canon s
    | _ => Ix.Name.mkStr canon ctor.pretty
  else n

/-- Components in dependency order: a component comes after every component
whose members its representatives' constructors mention. Ties by position. -/
def componentOrder (const? : Name → Option ConstantInfo) (b : BlockCanon) :
    Except String (Array Nat) := do
  let n := b.components.size
  let owner : Std.HashMap Name Nat := b.components.zipIdx.foldl (init := {}) fun m (c, i) =>
    c.classes.foldl (init := m) fun m cls => cls.foldl (init := m) fun m x => m.insert x i
  let mut deps : Array (Array Nat) := #[]
  for c in b.components do
    let mut ds : Array Nat := #[]
    for rep in c.reps do
      let iv ← indOf const? rep
      for cn in iv.ctors do
        let some (.ctorInfo cv) := const? cn | throw s!"image spec: no constructor {cn.pretty}"
        for x in Ix.Compile.Canon.constsIn (owner.fold (init := {}) fun s k _ => s.insert k)
            cv.cnst.type do
          if let some j := owner.get? x then
            if !ds.contains j then ds := ds.push j
    deps := deps.push ds
  let mut out : Array Nat := #[]
  for _ in [0:n] do
    match (List.range n).find? fun i =>
        !out.contains i && (deps[i]?.all (·.all fun j => j == i || out.contains j)) with
    | some i => out := out.push i
    | none => throw "image spec: the components have no dependency order"
  return out

/-- The image specification of a Lean block from its canonical form. -/
def ImageSpec.ofBlock (naming : Naming) (const? : Name → Option ConstantInfo)
    (b : BlockCanon) : Except String ImageSpec := do
  let order ← componentOrder const? b
  let mut tyMap : Std.HashMap Name Name := {}
  for (c, ci) in b.components.zipIdx do
    for (cls, k) in c.classes.zipIdx do
      let some rep := cls[0]? | throw "image spec: empty class"
      for x in cls do tyMap := tyMap.insert x (naming.ind ci k rep)
  let mut ctorMap : Std.HashMap Name Name := {}
  let mut canonInds : Array Name := #[]
  let mut decls : Array CanonDecl := #[]
  for ci in order do
    let some c := b.components[ci]? | throw s!"image spec: component {ci} out of range"
    let mut types : Array CanonType := #[]
    let mut lps : Array Name := #[]
    let mut np := 0
    let mut unsafe_ := false
    for (cls, k) in c.classes.zipIdx do
      let some rep := cls[0]? | throw "image spec: empty class"
      let canon := naming.ind ci k rep
      canonInds := canonInds.push canon
      let riv ← indOf const? rep
      lps := riv.cnst.levelParams
      np := riv.numParams
      unsafe_ := riv.isUnsafe
      let mut ctors : Array CanonCtor := #[]
      let canonCtors := riv.ctors.map (canonCtorName rep canon)
      for x in cls do
        let xv ← indOf const? x
        if xv.ctors.size != canonCtors.size then
          throw s!"image spec: {x.pretty} and {rep.pretty} differ in constructor count"
        for (cn, cc) in xv.ctors.zip canonCtors do ctorMap := ctorMap.insert cn cc
      for (cn, cc) in riv.ctors.zip canonCtors do
        let some (.ctorInfo cv) := const? cn | throw s!"image spec: no constructor {cn.pretty}"
        ctors := ctors.push { name := cc, type := replaceConstNames tyMap cv.cnst.type }
      types := types.push { name := canon, type := riv.cnst.type, ctors }
    decls := decls.push { comp := ci, levelParams := lps, numParams := np, isUnsafe := unsafe_, types }
  return { block := b, tyMap, ctorMap, canonInds, decls, naming }

end Ix.Compile.Image

end
