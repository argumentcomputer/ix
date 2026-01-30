import Ix.Common
import Ix.Address
import Ix.Environment
import Lean

namespace Ix

structure Def where
  name: Name
  levelParams : Array Name
  type : Expr
  kind : DefKind
  value : Expr
  hints : Lean.ReducibilityHints
  safety : Lean.DefinitionSafety
  all : Array Name
  deriving Repr, Nonempty, Inhabited, BEq

structure Ind where
  name: Name
  levelParams : Array Name
  type : Expr
  numParams : Nat
  numIndices : Nat
  all : Array Name
  ctors : Array ConstructorVal
  numNested: Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe: Bool
  deriving Repr, Nonempty, Inhabited, BEq

abbrev Rec := RecursorVal

inductive MutConst where
| defn : Def -> MutConst
| indc : Ind -> MutConst
| recr : Rec -> MutConst
deriving Repr, Nonempty, Inhabited, BEq

def MutConst.fromDefinitionVal (x : DefinitionVal) : MutConst :=
  .defn ⟨x.cnst.name, x.cnst.levelParams, x.cnst.type, .definition, x.value,
    x.hints, x.safety, x.all⟩

def MutConst.fromTheoremVal (x : TheoremVal) : MutConst :=
  .defn ⟨x.cnst.name, x.cnst.levelParams, x.cnst.type, .theorem, x.value,
    .opaque, .safe, x.all⟩

def MutConst.fromOpaqueVal (x : OpaqueVal) : MutConst :=
  .defn ⟨x.cnst.name, x.cnst.levelParams, x.cnst.type, .opaque, x.value,
    .opaque, if x.isUnsafe then .unsafe else .safe, x.all⟩

/-- Create a MutConst.indc from an InductiveVal and its constructor values -/
def MutConst.fromInductiveVal (i : InductiveVal) (ctorVals : Array ConstructorVal) : MutConst :=
  .indc ⟨i.cnst.name, i.cnst.levelParams, i.cnst.type, i.numParams, i.numIndices,
    i.all, ctorVals, i.numNested, i.isRec, i.isReflexive, i.isUnsafe⟩

def MutConst.name : MutConst -> Name
| .defn x => x.name
| .indc x => x.name
| .recr x => x.cnst.name

def MutConst.levelParams : MutConst -> Array Name
| .defn x => x.levelParams
| .indc x => x.levelParams
| .recr x => x.cnst.levelParams

def MutConst.ctors : MutConst -> Array ConstructorVal
| .indc x => x.ctors
| .defn _ => #[]
| .recr _ => #[]

def MutConst.contains (name: Name) : MutConst -> Bool
| .defn val => val.name == name
| .recr val => val.cnst.name == name
| .indc val => val.name == name || val.ctors.any (fun c => c.cnst.name == name)

-- We have a list of classes of mutual constants, each class representing a
-- possible equivalence class. We would like to construct a numerical
-- index for each constant (which could be a definition, inductive+constructors
-- or recursor) within this list of classes, such that each constant in the
-- same equivalence class has the same index. If the classes are true
-- equivalence classes then all constants in a class will be the same kind of
-- constant, and, if inductives, have the same number of constructors.
--
-- However, since we use this function within the sorting function that
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
-- 4 indices (one for each inductive type itself plus 3 ctors).
--
-- In practice, Lean should never give us a mutual block that mixes inductives
-- definitions and recursors, but we combine them for robustness and code
-- deduplication.
-- layout: [i0, i1, ..., iN, i0c0, ... i0cM, ... inc0, iNcM]
def MutConst.ctx (classes: List (List MutConst)) : Ix.MutCtx
  := Id.run do
  let mut mutCtx : Ix.MutCtx := default
  let mut i := classes.length
  for (consts, j) in classes.zipIdx do
    let mut maxCtors := 0
    for const in consts do
      mutCtx := mutCtx.insert const.name j
      maxCtors := max maxCtors const.ctors.size
      for (c, cidx) in Array.zipIdx const.ctors do
        mutCtx := mutCtx.insert c.cnst.name (i + cidx)
    i := i + maxCtors
  return mutCtx

end Ix
