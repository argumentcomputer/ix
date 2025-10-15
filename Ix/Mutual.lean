import Ix.Common
import Ix.Address
import Lean

namespace Ix

structure Def where
  name: Lean.Name
  levelParams : List Lean.Name
  type : Lean.Expr
  kind : DefKind
  value : Lean.Expr
  hints : Lean.ReducibilityHints
  safety : Lean.DefinitionSafety
  all : List Lean.Name
  deriving BEq, Repr, Nonempty, Inhabited, Ord, Hashable

structure Ind where
  name: Lean.Name
  levelParams : List Lean.Name
  type : Lean.Expr
  numParams : Nat
  numIndices : Nat
  all : List Lean.Name
  ctors : List Lean.ConstructorVal
  numNested: Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe: Bool
  deriving BEq, Repr, Nonempty, Inhabited

abbrev Rec := Lean.RecursorVal

inductive MutConst where
| defn : Def -> MutConst
| indc : Ind -> MutConst
| recr : Rec -> MutConst
deriving BEq, Repr, Nonempty, Inhabited

def MutConst.mkDefn : Lean.DefinitionVal -> MutConst
| x => .defn ⟨x.name, x.levelParams, x.type, .definition, x.value, x.hints, x.safety, x.all⟩

def MutConst.mkOpaq : Lean.OpaqueVal -> MutConst
| x => .defn ⟨x.name, x.levelParams, x.type, .opaque, x.value, .opaque,
    if x.isUnsafe then .unsafe else .safe, x.all⟩

def MutConst.mkTheo : Lean.TheoremVal -> MutConst
| x => .defn ⟨x.name, x.levelParams, x.type, .theorem, x.value, .opaque, .safe, x.all⟩

def MutConst.name : MutConst -> Lean.Name
| .defn x => x.name
| .indc x => x.name
| .recr x => x.name

def MutConst.ctors : MutConst -> List (Lean.ConstructorVal)
| .indc x => x.ctors
| .defn _ => []
| .recr _ => []

-- We have a list of classes of mutual constants, each class representing a
-- possible equivalence class. We would like to construct a unique numerical
-- index for each constant (which could be a definition, inductive+constructors
-- or recursor) within this list of classes. If the classes are true equivalence
-- classes then all constants in a class will be the same kind of constant,
-- and, if inductives, have the same number of constructors.
--
-- Unfortunately, since we use this function within the sorting function that
-- produces the equivalence classes, our indexing has to be robust to the
-- possiblity that constants are *not* the same, and that the inductives in a
-- class do *not* have the same number of constructors.
--
-- We do this by first finding the inductives in the possible class with the
-- largest number of constructors. Then we "reserve" index space for the entire
-- class based on this maximum. Inductives with a smaller number of constructors,
-- (or definitions and recursors, which can be treated the same as inductives
-- with no constructors) will be able to create unique indices without conflict,
-- since we index them as if they could have the maximum number of constructors.
-- For example, if a class has an inductive with 2 ctors
-- and an inductive with 3 ctors, then the whole class will reserve
-- 4 indices (one for each inductive type itself plus 3 ctors) for each constant.
--
-- In practice, Lean should never give us a mutual block that mixes inductives
-- definitions and recursors, but we combine them for robustness and code
-- deduplication.
def MutConst.ctx (constss: List (List MutConst)) : Map Lean.Name Nat
  := Id.run do
  let mut mutCtx := default
  let mut idx := 0
  for consts in constss do
    let mut maxCtors := 0
    for const in consts do
      maxCtors := max maxCtors const.ctors.length
      mutCtx := mutCtx.insert const.name idx
      for (c, cidx) in List.zipIdx const.ctors do
        mutCtx := mutCtx.insert c.name (idx + 1 + cidx)
    idx := idx + 1 + maxCtors
  return mutCtx

end Ix
