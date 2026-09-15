module

public import Ix.Compile.SourceContract.Basic
public import Lean.Util.FindExpr

/-!
# Source annotation markers

These markers bind frontend intent to elaborated binder domains. They are not
an Ixon encoding or optional optimization hints. An emitter that cannot consume
them must reject the source before it erases metadata.
-/

public section

namespace Ix.Compile

def sourceAnnotationKey : Lean.Name := `ix.source.binder

structure BinderAnnotation where
  origin : Nat
  binder : Lean.Name
  uses : Ixon.Uses
  owned : Ixon.Owned
  region : Option Lean.Name
  regions : Array Lean.Name
  deriving BEq, Repr, Inhabited

def hasSourceAnnotation (data : Lean.MData) : Bool :=
  data.entries.any fun (key, _) => sourceAnnotationKey.isPrefixOf key

def BinderAnnotation.toMetadata (annotation : BinderAnnotation) : Lean.MData := Id.run do
  let mut data := ({} : Lean.MData)
    |>.setNat sourceAnnotationKey 1
    |>.setNat `ix.source.binder.origin annotation.origin
    |>.setName `ix.source.binder.name annotation.binder
    |>.setNat `ix.source.binder.uses annotation.uses.toBits.toNat
    |>.setNat `ix.source.binder.owned annotation.owned.toBits.toNat
    |>.setSyntax `ix.source.binder.regions
      (Lean.mkNullNode (annotation.regions.map fun name => (Lean.mkIdent name).raw))
  if let some region := annotation.region then
    data := data.setName `ix.source.binder.region region
  return data

/-- Strictly decode the reserved namespace. Other metadata, including Lean's
native borrow hint, is orthogonal. Unknown versions, keys, and duplicate keys
are errors, including when the version marker itself is missing. -/
def BinderAnnotation.ofMetadata? (data : Lean.MData) : Except String (Option BinderAnnotation) := do
  if !hasSourceAnnotation data then return none
  let keys := #[sourceAnnotationKey, `ix.source.binder.origin, `ix.source.binder.name,
    `ix.source.binder.uses, `ix.source.binder.owned, `ix.source.binder.regions,
    `ix.source.binder.region]
  let mut seen : Std.HashSet Lean.Name := {}
  for (key, _) in data.entries do
    if sourceAnnotationKey.isPrefixOf key then
      if !keys.contains key then throw s!"unknown source annotation field {key}"
      if seen.contains key then throw s!"duplicate source annotation field {key}"
      seen := seen.insert key
  let some (.ofNat 1) := data.find sourceAnnotationKey
    | throw "unsupported or missing source annotation version"
  let some (.ofNat origin) := data.find `ix.source.binder.origin
    | throw "missing source annotation origin"
  let some (.ofName binder) := data.find `ix.source.binder.name
    | throw "missing source binder name"
  let some (.ofNat uses) := data.find `ix.source.binder.uses
    | throw "missing source binder usage"
  if uses > 3 then throw "invalid source binder usage"
  let some uses := Ixon.Uses.ofBits? uses.toUInt8
    | throw "invalid source binder usage"
  let some (.ofNat owned) := data.find `ix.source.binder.owned
    | throw "missing source binder ownership"
  if owned > 1 then throw "invalid source binder ownership"
  let some owned := Ixon.Owned.ofBits? owned.toUInt8
    | throw "invalid source binder ownership"
  let some (.ofSyntax regions) := data.find `ix.source.binder.regions
    | throw "missing source region parameters"
  unless regions.isOfKind Lean.nullKind && regions.getArgs.all (·.isIdent) do
    throw "invalid source region parameters"
  let region ← match data.find `ix.source.binder.region with
    | none => pure none
    | some (.ofName name) => pure (some name)
    | _ => throw "invalid source region reference"
  return some {
    origin, binder, uses, owned, region
    regions := regions.getArgs.map (·.getId) }

/-- Read only the domain's outer metadata chain, without reducing its type. -/
def binderAnnotation? : Lean.Expr → Except String (Option BinderAnnotation)
  | .mdata data inner => do
    let outer ← BinderAnnotation.ofMetadata? data
    let nested ← binderAnnotation? inner
    match outer, nested with
    | some _, some _ => throw "multiple source annotations on one binder domain"
    | some annotation, none | none, some annotation => return some annotation
    | none, none => return none
  | _ => .ok none

/-- Preserve existing outer metadata frames when adding the source marker.
Lean recognizes native borrow annotations only as a singleton outer frame, so
combining their entries with this marker would hide the native hint. -/
def BinderAnnotation.attach (annotation : BinderAnnotation) (type : Lean.Expr) :
    Except String Lean.Expr := do
  if (← binderAnnotation? type).isSome then throw "source binder is already annotated"
  let data := annotation.toMetadata
  let rec insert : Lean.Expr → Lean.Expr
    | .mdata native inner => .mdata native (insert inner)
    | inner => .mdata data inner
  return insert type

/-- Use Lean's shared-expression search rather than revisiting every occurrence
of an unannotated shared subtree during the production preflight. -/
def exprHasSourceAnnotations (expr : Lean.Expr) : Bool :=
  (expr.find? fun
    | .mdata data _ => hasSourceAnnotation data
    | _ => false).isSome

end Ix.Compile

end
