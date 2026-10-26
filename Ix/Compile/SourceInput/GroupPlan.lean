module
public import Ix.Compile.SourceInput.GroupView
public import Ix.LeanIngress

@[expose] public section
namespace Ix.Compile.SourceInput.GroupPlan
open Ix.LeanIngress

/-- Recipes retain source query keys, never full declarations or bodies. -/
inductive Recipe where
  | family (head : Ix.Name) (candidates : Array Ix.Name)
  | component (componentKey : Ix.Name) (members : Ix.Set Ix.Name)
  | unplaced (storedKey : Ix.Name)

inductive GroupKind where
  | inductiveGroup | definitions | axiomGroup | quotientGroup
  | invalid (error : Ix.Kernel.Reader.ReadError)

structure Summary where
  names : Array Ix.Name
  kind : GroupKind

def summarize (group : Group) : Summary :=
  ⟨group.names,match group with
    | .inductive .. => .inductiveGroup | .definitions _ => .definitions
    | .axiom _ => .axiomGroup | .quot _ => .quotientGroup | .invalid _ e => .invalid e⟩

/-- Summary provenance will come from the complete producer in P2B. A freely
constructed plan is data, not a certificate of grouping or reading. -/
structure Plan where
  recipe : Recipe
  summary : Summary

inductive Error where
  | source (error : SourceInput.Error)
  | absentRecipe (name : Ix.Name)
  | expectedInductive (name : Ix.Name)
  | expectedRecursor (name : Ix.Name)
  deriving Repr

/-- Only the actual missing-input branch becomes genuine absence. Header
and canonicalization errors remain errors and propagate through the helpers. -/
def lookup (carrier : Carrier) (name : Ix.Name) : Except Error (Option Ix.ConstantInfo) :=
  match carrier.canonicalAt name with
  | .ok ci => .ok (some ci)
  | .error (.missing _) => .ok none
  | .error e => .error (.source e)

def require (carrier : Carrier) (name : Ix.Name) : Except Error Ix.ConstantInfo := do
  let some ci ← lookup carrier name | throw (.absentRecipe name)
  return ci

def recursor (carrier : Carrier) (name : Ix.Name) : Except Error Ix.RecursorVal := do
  let .recInfo value ← require carrier name | throw (.expectedRecursor name)
  return value

/-- Materialize one recipe only. Full group values are temporary and are
not cached in Plan. Genuine component none and invalid Group results remain
distinct from input/recipe errors; none is not a Source-reading success. -/
def materialize (carrier : Carrier) : Recipe → Except Error (Option Group)
  | .family head candidates => do
    let .inductInfo first ← require carrier head | throw (.expectedInductive head)
    let recursors ← candidates.mapM (recursor carrier)
    return some (← inductiveGroupUsing (lookup carrier) first recursors)
  | .component _ members => componentGroupUsing (lookup carrier) members
  | .unplaced name => do
    return some (unplaced name (← require carrier name))

end Ix.Compile.SourceInput.GroupPlan
end
