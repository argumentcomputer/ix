import Aiur.Generic.AST

/-! Static modules. Files, imports and entrypoint declarations are deliberately
absent. Module bodies reuse the native generic expression language. -/
namespace Aiur.Modules
open Generic

inductive Ref where
  | mk (name : String) (args : List Ref)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Ref.name : Ref → String | .mk name _ => name
def Ref.args : Ref → List Ref | .mk _ args => args
def Ref.symbol : Ref → String
  | .mk name [] => name
  | .mk name args => name ++ "::<" ++ String.intercalate "," (args.map Ref.symbol) ++ ">"
termination_by r => sizeOf r

structure TypeMember where
  name : String
  typeParams : List String := []
  definition : Option Generic.Ty := none
  /-- Withhold input/hint permission; the implementation may still be transparent. -/
  isOpaque : Bool := false
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Callable where
  name : String
  typeParams : List String := []
  params : List (String × Generic.Ty)
  result : Generic.Ty
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Signature where
  name : String
  types : List TypeMember := []
  consts : List (String × Generic.Ty) := []
  /-- Functions and maps have the same callable interface. -/
  functions : List Callable := []
  tables : List (String × Generic.Ty) := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Definitions (α : Type) where
  program : Generic.Program α
  constTypes : List (String × Generic.Ty) := []
  /-- Destructuring parameter patterns, before checking their irrefutability. -/
  parameterPatterns : List (String × List (Generic.Pattern α)) := []
  /-- Declaration-level opacity, retained independently of alias normalization. -/
  opaqueTypes : List String := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr

inductive Body (α : Type) where
  | definitions (value : Definitions α)
  | alias (target : Ref)
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Module (α : Type) where
  name : String
  parameters : List (String × String) := []
  signature : Option String := none
  body : Body α
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Program (α : Type) where
  signatures : List Signature := []
  modules : List (Module α) := []
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Program.findModule? (p : Program α) (name : String) := p.modules.find? (·.name == name)
def Program.findSignature? (p : Program α) (name : String) := p.signatures.find? (·.name == name)

/-- Compose declaration fragments before checking. Duplicate definitions are
errors; this operation never reopens or merges the contents of a module. -/
def Program.append (p q : Program α) : Program α :=
  ⟨p.signatures ++ q.signatures, p.modules ++ q.modules⟩

def Definitions.map (f : α → β) (d : Definitions α) : Definitions β := {
  program := d.program.map f
  constTypes := d.constTypes
  parameterPatterns := d.parameterPatterns.map fun (n, ps) => (n, ps.map (Generic.Pattern.map f))
  opaqueTypes := d.opaqueTypes }

def Program.map (f : α → β) (p : Program α) : Program β := {
  signatures := p.signatures
  modules := p.modules.map fun m => {
    name := m.name, parameters := m.parameters, signature := m.signature
    body := match m.body with
      | .definitions d => .definitions (d.map f)
      | .alias target => .alias target } }

def Program.toField (p : Program Nat) (F : Type) [NatCast F] := p.map (Nat.cast : Nat → F)

end Aiur.Modules
