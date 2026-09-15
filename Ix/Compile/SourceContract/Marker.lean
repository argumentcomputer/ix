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
  value : Ixon.ValueContract
  result : Option Ixon.ValueContract := none
  letKind : Ixon.LetKind := .value
  deriving BEq, Repr, Inhabited

def hasSourceAnnotation (data : Lean.MData) : Bool :=
  data.entries.any fun (key, _) => sourceAnnotationKey.isPrefixOf key

def BinderAnnotation.toMetadata (annotation : BinderAnnotation) : Lean.MData := Id.run do
  let mut data := ({} : Lean.MData)
    |>.setNat sourceAnnotationKey 3
    |>.setNat `ix.source.binder.origin annotation.origin
    |>.setName `ix.source.binder.name annotation.binder
    |>.setNat `ix.source.binder.contract (Ixon.BinderContract.toBits ⟨annotation.uses, annotation.value⟩).toNat
    |>.setNat `ix.source.binder.letKind (match annotation.letKind with | .value => 0 | .borrowShared => 1)
  if let some result := annotation.result then
    data := data.setNat `ix.source.binder.result result.toBits.toNat
  return data

/-- Strictly decode the reserved namespace. Other metadata, including Lean's
native borrow hint, is orthogonal. Unknown versions, keys, and duplicate keys
are errors, including when the version marker itself is missing. -/
def BinderAnnotation.ofMetadata? (data : Lean.MData) : Except String (Option BinderAnnotation) := do
  if !hasSourceAnnotation data then return none
  let keys := #[sourceAnnotationKey, `ix.source.binder.origin, `ix.source.binder.name,
    `ix.source.binder.contract, `ix.source.binder.result, `ix.source.binder.letKind]
  let mut seen : Std.HashSet Lean.Name := {}
  for (key, _) in data.entries do
    if sourceAnnotationKey.isPrefixOf key then
      if !keys.contains key then throw s!"unknown source annotation field {key}"
      if seen.contains key then throw s!"duplicate source annotation field {key}"
      seen := seen.insert key
  let some (.ofNat 3) := data.find sourceAnnotationKey
    | throw "unsupported or missing source annotation version"
  let some (.ofNat origin) := data.find `ix.source.binder.origin
    | throw "missing source annotation origin"
  let some (.ofName binder) := data.find `ix.source.binder.name
    | throw "missing source binder name"
  let some (.ofNat bits) := data.find `ix.source.binder.contract
    | throw "missing source binder contract"
  if bits > 15 then throw "invalid source binder contract"
  let some contract := Ixon.BinderContract.ofBits? bits.toUInt8
    | throw "invalid source binder contract"
  let result ← match data.find `ix.source.binder.result with
    | none => pure none
    | some (.ofNat bits) => do
      if bits > 3 then throw "invalid source result contract"
      let some result := Ixon.ValueContract.ofBits? bits.toUInt8
        | throw "invalid source result contract"
      pure (some result)
    | _ => throw "invalid source result contract"
  let letKind ← match data.find `ix.source.binder.letKind with
    | some (.ofNat 0) => pure Ixon.LetKind.value
    | some (.ofNat 1) => pure Ixon.LetKind.borrowShared
    | _ => throw "invalid source let kind"
  return some { origin, binder, uses := contract.uses, value := contract.value, result, letKind }

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
