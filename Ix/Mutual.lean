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

def MutConst.contains (name: Lean.Name) : MutConst -> Bool
| .defn val => val.name == name
| .recr val => val.name == name
| .indc val => val.name == name || val.ctors.any (fun c => c.name == name)

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
def MutConst.ctx (classes: List (List MutConst)) : Map Lean.Name Nat
  := Id.run do
  let mut mutCtx := default
  let mut i := classes.length
  for (consts, j) in classes.zipIdx do
    let mut maxCtors := 0
    for const in consts do
      mutCtx := mutCtx.insert const.name j
      maxCtors := max maxCtors const.ctors.length
      for (c, cidx) in List.zipIdx const.ctors do
        mutCtx := mutCtx.insert c.name (i + cidx)
    i := i + maxCtors
  return mutCtx


--def a0 : Lean.ConstructorVal := ⟨⟨`a0, [], .bvar 0⟩, `a, 0, 0, 0, false⟩
--def a1 : Lean.ConstructorVal := ⟨⟨`a1, [], .bvar 0⟩, `a, 1, 0, 0, false⟩
--def a2 : Lean.ConstructorVal := ⟨⟨`a2, [], .bvar 0⟩, `a, 2, 0, 0, false⟩
--def a : Ind := ⟨`a, [], .bvar 0, 0, 0, [], [a0, a1, a2], 0, false, false, false⟩
--
--def b0 : Lean.ConstructorVal := ⟨⟨`b0, [], .bvar 0⟩, `b, 0, 0, 0, false⟩
--def b1 : Lean.ConstructorVal := ⟨⟨`b1, [], .bvar 0⟩, `b, 1, 0, 0, false⟩
--def b2 : Lean.ConstructorVal := ⟨⟨`b2, [], .bvar 0⟩, `b, 2, 0, 0, false⟩
--def b : Ind := ⟨`b, [], .bvar 0, 0, 0, [], [b0, b1], 0, false, false, false⟩
--
--def c0 : Lean.ConstructorVal := ⟨⟨`c0, [], .bvar 0⟩, `c, 0, 0, 0, false⟩
--def c1 : Lean.ConstructorVal := ⟨⟨`c1, [], .bvar 0⟩, `c, 1, 0, 0, false⟩
--def c2 : Lean.ConstructorVal := ⟨⟨`c2, [], .bvar 0⟩, `c, 2, 0, 0, false⟩
--def c : Ind := ⟨`c, [], .bvar 0, 0, 0, [], [c0, c1, c2], 0, false, false, false⟩
--
--#eval MutConst.ctx [[.indc a, .indc b], [.indc c]]

end Ix
