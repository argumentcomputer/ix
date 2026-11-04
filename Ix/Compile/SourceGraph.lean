module
public import Ix.GraphM
public import Ix.Compile.ExactKey
public import Ix.RoleEvidence

@[expose] public section
namespace Ix.Compile.SourceGraph

/-! Compact Source dependency facts, captured while a canonical record is live.
The collector is unwired. It deliberately overwrites every summary and erases
an older kept record when the new winner is streamed. The concrete row constructor
drops theorem/opaque bodies; no grounding policy is implemented here.
-/

inductive Grouping where
  | plain
  | induct (all : Array Name)
  | recursor (all : Array Name)
  deriving Inhabited

inductive LiteralUse where
  | none | nat | string
  deriving Inhabited, BEq, DecidableEq

structure Node where
  direct : Ix.Set Name
  literals : LiteralUse
  grouping : Grouping

def hasStrLit : Expr → Bool
  | .lit (.strVal _) _ => true
  | .app f a _ => hasStrLit f || hasStrLit a
  | .lam _ t b _ _ | .forallE _ t b _ _ => hasStrLit t || hasStrLit b
  | .letE _ t v b _ _ => hasStrLit t || hasStrLit v || hasStrLit b
  | .mdata _ e _ | .proj _ _ e _ => hasStrLit e
  | _ => false

def hasNatLit : Expr → Bool
  | .lit (.natVal _) _ => true
  | .app f a _ => hasNatLit f || hasNatLit a
  | .lam _ t b _ _ | .forallE _ t b _ _ => hasNatLit t || hasNatLit b
  | .letE _ t v b _ _ => hasNatLit t || hasNatLit v || hasNatLit b
  | .mdata _ e _ | .proj _ _ e _ => hasNatLit e
  | _ => false

def terms : ConstantInfo → List Expr
  | .defnInfo v => [v.cnst.type, v.value]
  | .thmInfo v => [v.cnst.type, v.value]
  | .opaqueInfo v => [v.cnst.type, v.value]
  | .recInfo v => v.cnst.type :: v.rules.toList.map (·.rhs)
  | ci => [ci.getCnst.type]

def literalUse (ci : ConstantInfo) : LiteralUse :=
  if (terms ci).any hasStrLit then .string
  else if (terms ci).any hasNatLit then .nat else .none

def literalNames : LiteralUse → Array Name
  | .none => #[]
  | .nat => Ix.Kernel.Reader.natLitSupportNames.toArray.map fun k =>
      Name.fromLeanName (Ix.RoleEvidence.toLeanName (k : Ix.Kernel.Key .source))
  | .string => Ix.Kernel.Reader.strLitSupportNames.toArray.map fun k =>
      Name.fromLeanName (Ix.RoleEvidence.toLeanName (k : Ix.Kernel.Key .source))

/-- The caller may reuse its already-computed direct reference set. -/
def captureUsing (ci : ConstantInfo) (direct : Ix.Set Name) : Node :=
  { direct, literals := literalUse ci, grouping := match ci with
    | .inductInfo v => .induct v.all
    | .recInfo v => .recursor v.all
    | _ => .plain }

def capture (ci : ConstantInfo) : Node :=
  captureUsing ci (GraphM.run { consts := {} } .init (graphConst ci)).1

/-- The recursor index must come from the complete Source input. Its lookup
uses stored hashes; the first-member comparison remains structural. -/
def dependencies (rs : Map Name (Array (Name × Name))) (node : Node) : Array Name :=
  node.direct.toArray ++ literalNames node.literals ++ match node.grouping with
    | .plain => #[]
    | .recursor all => all
    | .induct all => all ++ match all[0]? with
      | none => #[]
      | some first => ((rs.getD first #[]).filter (ExactKey.nameEq ·.1 first)).map (·.2)

/-- Exactly the streamed compiler's retention rule, independent of safety. -/
def keep : ConstantInfo → Option ConstantInfo
  | .thmInfo _ | .opaqueInfo _ => none
  | ci => some ci

structure Row where
  name : Name
  node : Node
  kept : Option ConstantInfo

def rowUsing (n : Name) (ci : ConstantInfo) (direct : Ix.Set Name) : Row :=
  ⟨n, captureUsing ci direct, keep ci⟩

def rowOfCanonical (n : Name) (ci : ConstantInfo) : Row := ⟨n, capture ci, keep ci⟩

structure Collected where
  nodes : Map Name Node := {}
  code : Map Name ConstantInfo := {}
  deriving Inhabited

/-- Both maps describe the final row at each key, including hash aliases.
Destructure the owned accumulator before updating either map. -/
def mergeRow (acc : Collected) (row : Row) : Collected :=
  let ⟨nodes, code⟩ := acc
  let code := match row.kept with
    | some ci => code.insert row.name ci
    | none => code.erase row.name
  ⟨nodes.insert row.name row.node, code⟩

def collect (rows : List Row) : Collected := rows.foldl mergeRow {}

end Ix.Compile.SourceGraph
