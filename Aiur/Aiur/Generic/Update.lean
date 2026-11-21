import Aiur.Generic.AST
import Aiur.Eval

namespace Aiur.Generic.Update

abbrev Types := List (String × Ty)

def nominalName (types : Types) (type : Ty) : String :=
  match (type.subst types).toCore with | .enum name => name | _ => "$invalid"

def pack (types : Types) (step : UpdateStep) (values : List (SourceValue F)) : SourceValue F :=
  match step.owner with
  | none => .tuple values
  | some type => .construct (nominalName types type) structConstructor values

/-- Inspect a product value without following pointers. -/
def unpack (types : Types) (step : UpdateStep) (value : SourceValue F) : Option (List (SourceValue F)) :=
  match step.owner, value with
  | none, .tuple values => if values.length = step.width then some values else none
  | some type, .construct name ctor values =>
      if name == nominalName types type && ctor == structConstructor && values.length == step.width then some values else none
  | _, _ => none

/-- Replace one statically selected descendant. All other components retain
  their values, including opaque pointer identities. -/
def replace (types : Types) : UpdatePath → SourceValue F → SourceValue F → Option (SourceValue F)
  | [], _, replacement => some replacement
  | step :: path, base, replacement => do
      let values ← unpack types step base
      let values ← values.zipIdx.mapM fun (value, index) =>
        if index == step.position then replace types path value replacement else some value
      return pack types step values

def apply (types : Types) : List UpdatePath → SourceValue F → List (SourceValue F) → Option (SourceValue F)
  | [], base, [] => some base
  | path :: paths, base, replacement :: rest => do
      let base ← replace types path base replacement
      apply types paths base rest
  | _, _, _ => none

/-- The operands have already been evaluated: base first, then every written
  replacement. This operation performs no allocation and no heap access. -/
def value (types : Types) (paths : List UpdatePath) : List (SourceValue F) → Except EvalError (SourceValue F)
  | [] => .error .patternMismatch
  | base :: replacements => match apply types paths base replacements with
    | some result => .ok result
    | none => .error .patternMismatch

end Aiur.Generic.Update
