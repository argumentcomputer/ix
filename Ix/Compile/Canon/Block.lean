/-
  Ix.Compile.Canon.Block: the canonical form of one Lean inductive block
  (Pass 1 for blocks), from the functions of `Graph`, `Classes` and
  `Nested`.

  For a Lean block `all` (its `InductiveVal.all`):

  1. **split**: the components of the reference graph on the members and
     their constructors (`Graph.sccsOf`);
  2. **classes and order** of each component (`Classes.sortClasses`) over
     the members as `MutConst.indc` (today's `MutConst.mkIndc`);
  3. **nested auxiliaries** of each component, gated as today
     (`generateAuxPatches`): when some member of `all` has `numNested > 0`
     or the canonical expansion of the component has auxiliaries, the
     canonical auxiliary order (`Nested.canonicalAuxOrder`) and the source
     permutation `perm` (`Nested.computePerm`) against Lean's discovery
     order over `all`;
  4. **evaporation** of source positions no component discovers.

  Everything is a function of the block's constants, the constants they
  reference (through `Env.const?`) and, where the rule set compares by
  address, the compiled addresses of external constants (`Env.addr?`). No
  names enter the result except through `Seed.byNameHash` and
  `Representative.leastNameHash` (today).
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Graph
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
public import Ix.Compile.Canon.Nested
public section

namespace Ix.Compile.Canon

open Ix (Name Level Expr ConstantInfo MutConst ConstructorVal)

/-- What Pass 1 reads of the world: constants by name, and the compiled
address of an external constant (from the side-car of the stored
environment, or the compiler's name map). -/
structure Env where
  const? : Name → Option ConstantInfo
  addr? : Name → Option Address
  /-- External groups of the canonical expansion (`Nested.GroupOf`): the
  compiled canonical classes of an external block when the caller has them;
  Lean's `I.all` otherwise (the census, which compiles nothing). -/
  groupOf : GroupOf := leanGroup

def Env.ind? (env : Env) : Name → Option IndView := IndView.ofConst? env.const?

/-- Nested data of one component. -/
structure NestedCanon where
  /-- Lean's source auxiliaries (discovery over `all`), under the rule set's
  deduplication. -/
  source : Array Sig
  /-- The canonical auxiliary classes (names in the canonical expansion). -/
  canonClasses : Array (Array Name)
  canon : Array Sig
  /-- Source position ↦ canonical position (`none`: outside the component). -/
  perm : Array (Option Nat)
  evaporated : Array Bool
  /-- The structural order changes when addresses are ignored. -/
  addrDecided : Bool
  deriving Inhabited

/-- One component of a block. -/
structure ComponentCanon where
  /-- Members, in `all` order. -/
  members : Array Name
  /-- Classes in canonical order, representative first. -/
  classes : Array (Array Name)
  /-- Classes when external references are all equal. -/
  blindClasses : Array (Array Name)
  stats : SortStats
  nested : Option NestedCanon
  deriving Inhabited

def ComponentCanon.reps (c : ComponentCanon) : Array Name := c.classes.filterMap (·[0]?)

/-- The canonical form of a Lean block. -/
structure BlockCanon where
  all : Array Name
  components : Array ComponentCanon
  deriving Inhabited

/-- The members of `all` as today's sorter sees them. -/
def mutConstOf (env : Env) (n : Name) : Except String MutConst :=
  match env.const? n with
  | some (.inductInfo v) => do
    let ctors ← v.ctors.mapM fun c =>
      match env.const? c with
      | some (.ctorInfo cv) => pure cv
      | _ => throw s!"expected constructor {namePretty c}"
    pure (MutConst.fromInductiveVal v ctors)
  | some (.defnInfo v) => pure (MutConst.fromDefinitionVal v)
  | some (.thmInfo v) => pure (MutConst.fromTheoremVal v)
  | some (.opaqueInfo v) => pure (MutConst.fromOpaqueVal v)
  | some (.recInfo v) => pure (.recr v)
  | _ => throw s!"no constant {namePretty n}"

/-- The components of a block: members and constructors under the reference
graph, each component's members in `all` order. -/
def blockComponents (env : Env) (all : Array Name) : Except String (Array (Array Name)) := do
  let mut nodes : Array Name := #[]
  for n in all do
    nodes := nodes.push n
    match env.const? n with
    | some (.inductInfo v) => nodes := nodes ++ v.ctors
    | _ => pure ()
  let refs := fun n => match env.const? n with
    | some c => refsConst c
    | none => {}
  let some comps := sccsOf nodes refs | throw "component computation ran out of fuel"
  let allSet : Std.HashSet Name := all.foldl (·.insert ·) {}
  let comps := comps.filterMap fun c =>
    let ms := all.filter fun n => c.contains n && allSet.contains n
    if ms.isEmpty then none else some ms
  -- deterministic: by first member's position in `all`
  let pos := fun (c : Array Name) => (all.idxOf? c[0]!).getD 0
  return comps.qsort (fun a b => pos a < pos b)

/-- `rep ↦ rep`, alias ↦ its representative. -/
def origToCanonOf (classes : Array (Array Name)) : Std.HashMap Name Name :=
  classes.foldl (init := {}) fun m cls =>
    match cls[0]? with
    | some rep => cls.foldl (init := m) fun m n => m.insert n rep
    | none => m

def aliasesOf (classes : Array (Array Name)) : Std.HashMap Name Name :=
  classes.foldl (init := {}) fun m cls =>
    match cls[0]? with
    | some rep => (cls.extract 1 cls.size).foldl (init := m) fun m n => m.insert n rep
    | none => m

/-- The dedup rule of a rule set. -/
def Rules.dedup (r : Rules) : Dedup :=
  match r.nested with
  | .structural => .compiler
  | .discovery => .lean

/-- Nested data of one component, before evaporation. -/
def componentNested (rules : Rules) (env : Env) (all : Array Name)
    (classes : Array (Array Name)) : Except String (Option NestedCanon) := do
  let reps := classes.filterMap (·[0]?)
  if reps.isEmpty then return none
  let metaNested := all.any fun n => match env.const? n with
    | some (.inductInfo v) => v.numNested > 0
    | _ => false
  let x ← expand env.ind? rules.dedup reps (aliasesOf classes) env.groupOf
    (if rules.nested == .discovery then some env.addr? else none)
  let structNested := x.types.size > x.nOriginals
  if !metaNested && !structNested then return none
  let (order, addrDecided) ←
    if metaNested && structNested then canonicalAuxOrder rules env.addr? x
    else pure (x.aux.map fun m => #[m.name], false)
  let canon ← sigsInOrder x order
  let src ← expand env.ind? rules.dedup all
  let source := src.sigs
  let perm ← computePerm env.addr? canon source all (origToCanonOf classes)
  return some { source, canonClasses := order, canon, perm,
                evaporated := Array.replicate perm.size false, addrDecided }

/-- Evaporation (`generateAuxPatches`, the evaporated-alias pass): see
`Nested.lean`. `comps` are all components of the block with their classes. -/
def evaporate (env : Env) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (n : NestedCanon) :
    Except String NestedCanon := do
  if !n.perm.contains none then return n
  let some all0 := all[0]? | return n
  let inHere : Std.HashSet Name := (comps[here]!).foldl (fun s c => c.foldl (·.insert ·) s) {}
  let originals : Std.HashSet Name := all.foldl (·.insert ·) {}
  let mut flags := n.evaporated
  for (p, j) in n.perm.zipIdx do
    if p.isSome then continue
    let some s := n.source[j]? | continue
    if !inHere.contains s.owner then continue
    if (env.const? (Name.mkStr all0 s!"rec_{j + 1}")).isNone then continue
    -- members the occurrence mentions (constants and projection names)
    let refs := s.specs.foldl (init := ({} : Std.HashSet Name)) fun acc e =>
      (constsIn originals e).fold (·.insert ·) acc
    let mut claimed := false
    if !refs.isEmpty then
      for (cls, ci) in comps.zipIdx do
        if ci == here then continue
        let compMembers : Std.HashSet Name := cls.foldl (fun s c => c.foldl (·.insert ·) s) {}
        if !refs.toList.any compMembers.contains then continue
        let reps := cls.filterMap (·[0]?)
        let x ← expand env.ind? rules.dedup reps (aliasesOf cls) env.groupOf
          (if rules.nested == .discovery then some env.addr? else none)
        let o2c := origToCanonOf cls
        let strict : Std.HashSet Name := all.foldl (init := {}) fun st m =>
          if compMembers.contains m then st else st.insert m
        let specs := s.specs.map (replaceConstNames o2c)
        if (matchSig env.addr? strict x.sigs s.head s.levels specs).isSome then
          claimed := true
    if claimed then continue
    let targetOk := match env.const? (Name.mkStr s.head "rec") with
      | some (.recInfo r) => r.numMotives == 1
      | _ => false
    if targetOk then flags := flags.set! j true
  return { n with evaporated := flags }

/-- The canonical form of the Lean block `all`. -/
def canonBlock (rules : Rules) (env : Env) (all : Array Name) : Except String BlockCanon := do
  let comps ← blockComponents env all
  let mut out : Array ComponentCanon := #[]
  for members in comps do
    let cs ← members.toList.mapM (mutConstOf env)
    let (classes, stats) ← sortClasses rules env.addr? cs
    let blind ← sortClassesBlind rules cs
    out := out.push { members, classes := classNames classes,
                      blindClasses := classNames blind, stats, nested := none }
  let classesAll := out.map (·.classes)
  let mut out' : Array ComponentCanon := #[]
  for (c, i) in out.zipIdx do
    let nested ← componentNested rules env all c.classes
    let nested ← nested.mapM (evaporate env rules all classesAll i)
    out' := out'.push { c with nested }
  return { all, components := out' }

/-! ## What changed -/

/-- How a block differs from its Lean presentation (the census's
categories, `exp-census-1.md`). -/
structure BlockChange where
  split : Bool
  collapse : Bool
  /-- Class representatives out of `all` order in some component. -/
  reorder : Bool
  /-- Today's predicate: some source position maps to a different
  canonical index (`auxLayoutChanged`). -/
  nestedOrder : Bool
  evaporation : Bool
  deriving Repr, Inhabited, BEq

def BlockChange.any (c : BlockChange) : Bool :=
  c.split || c.collapse || c.reorder || c.nestedOrder || c.evaporation

def BlockCanon.change (b : BlockCanon) : BlockChange :=
  let comps := b.components
  { split := comps.size > 1
    collapse := comps.any fun c => c.classes.any (·.size > 1)
    reorder := comps.any fun c =>
      let reps := c.reps
      reps != b.all.filter reps.contains
    nestedOrder := comps.any fun c => match c.nested with
      | some n => n.perm.zipIdx.any fun (p, j) => match p with
        | some i => i != j
        | none => false
      | none => false
    evaporation := comps.any fun c => match c.nested with
      | some n => n.evaporated.any id
      | none => false }

/-- The member order needs addresses in some component. -/
def BlockCanon.memberOrderAddrDecided (b : BlockCanon) : Bool :=
  b.components.any fun c => c.classes != c.blindClasses

def BlockCanon.multiClass (b : BlockCanon) : Bool :=
  b.components.any fun c => c.classes.size > 1

def BlockCanon.nestedOrderAddrDecided (b : BlockCanon) : Bool :=
  b.components.any fun c => (c.nested.map (·.addrDecided)).getD false

def BlockCanon.multiAux (b : BlockCanon) : Bool :=
  b.components.any fun c => match c.nested with
    | some n => decide (n.canonClasses.size > 1)
    | none => false

end Ix.Compile.Canon

end
