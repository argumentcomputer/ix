/- Shared canonical-block results, finite source input and class maps.
Both the unrestricted callback implementation and the retained finite-source
implementation import this data layer; it imports neither implementation. -/
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
structure SourceEnv where
  source : Ix.Environment
  addr? : Name → Option Address
  /-- External groups of the canonical expansion (`Nested.SourceGroups`): the
  compiled canonical classes of an external block when the caller has them;
  Lean's `I.all` otherwise (the census, which compiles nothing). -/
  groupOf : SourceGroups := leanSourceGroup

def SourceEnv.const? (env : SourceEnv) : Name → Option ConstantInfo := env.source.get?

def SourceEnv.ind? (env : SourceEnv) : Name → Option IndView := IndView.ofConst? env.const?

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
