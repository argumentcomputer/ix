module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public section

namespace Ix

structure Def where
  name: Name
  levelParams : Array Name
  type : Expr
  kind : DefKind
  value : Expr
  hints : Lean.ReducibilityHints
  safety : DefinitionSafety
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

private def convertSafety : Lean.DefinitionSafety → DefinitionSafety
  | .unsafe => .unsaf | .safe => .safe | .partial => .part

def MutConst.fromDefinitionVal (x : DefinitionVal) : MutConst :=
  .defn ⟨x.cnst.name, x.cnst.levelParams, x.cnst.type, .defn, x.value,
    x.hints, convertSafety x.safety, x.all⟩

def MutConst.fromTheoremVal (x : TheoremVal) : MutConst :=
  .defn ⟨x.cnst.name, x.cnst.levelParams, x.cnst.type, .thm, x.value,
    .opaque, .safe, x.all⟩

def MutConst.fromOpaqueVal (x : OpaqueVal) : MutConst :=
  .defn ⟨x.cnst.name, x.cnst.levelParams, x.cnst.type, .opaq, x.value,
    .opaque, if x.isUnsafe then .unsaf else .safe, x.all⟩

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

/-- Assign each ordered member its own index, followed by its constructors.
The constructor slots of earlier members precede those of later members. -/
def MutConst.ctx (members : List MutConst) : Ix.MutCtx := Id.run do
  let mut mutCtx : Ix.MutCtx := default
  let mut i := members.length
  for (member, j) in members.zipIdx do
    mutCtx := mutCtx.insert member.name j
    for (c, cidx) in Array.zipIdx member.ctors do
      mutCtx := mutCtx.insert c.cnst.name (i + cidx)
    i := i + member.ctors.size
  return mutCtx

end Ix

end
