import Aiur.Execution.Interface

namespace Aiur.Execution

/-- A high-level channel entry. The expected output type is checked; lookup
identity is the channel and nominal constant key. -/
structure HintEntry (F : Type) where
  type : Generic.Ty
  key : DataValue F
  output : DataValue F
  channel : String := ""
  deriving Repr, BEq

def HintEntry.map (f : F → G) (entry : HintEntry F) : HintEntry G :=
  ⟨entry.type, entry.key.map f, entry.output.map f, entry.channel⟩

/-- Nominal key types distinguish constants even when encodings coincide.
The result type describes the answer and is not an extra dispatch argument. -/
structure FlatHintEntry (F : Type) where
  type : Ty
  keyType : Ty
  key : List F
  output : List F
  channel : String := ""
  deriving Repr, BEq

instance : Inhabited (FlatHintEntry F) := ⟨⟨.field, .field, [], [], ""⟩⟩

namespace DataTypes

def inputType (types : DataTypes) (type : Generic.Ty) : Except String Generic.Ty := do
  let resolved ← types.resolve 1024 type
  if (IOType.ofSource types.program types.opaqueNames 1024 type).isNone then
    throw "execution data type contains an opaque component or has no finite public representation"
  return resolved

private def checkChildren (types : DataTypes) (expected actual : List Generic.Ty) : Except String Unit := do
  let expected ← expected.mapM (types.resolve 1024)
  if expected != actual then throw "execution data component type mismatch"

/-- Check every child and order named fields using the declaration, then reuse
the semantic constant representation and the existing canonical layout codec. -/
def value (types : DataTypes) (input : DataValue F) : Except String (Generic.Ty × Constant F) := do
  let type ← types.inputType input.type
  match input with
  | .field x => return (type, .field x)
  | .tuple items =>
      let values ← items.mapM types.value
      return (type, .tuple (values.map Prod.snd))
  | .array element items =>
      let values ← items.mapM types.value
      types.checkChildren (List.replicate items.length element) (values.map Prod.fst)
      return (type, .tuple (values.map Prod.snd))
  | .record _ fields =>
      let .named name args := type | throw "struct data requires a nominal struct type"
      let some decl := types.program.findStruct? name | throw s!"not a struct type: {name}"
      let env ← Generic.arguments decl.typeParams args
      if fields.length != decl.fields.length || (fields.map Prod.fst).eraseDups.length != fields.length then
        throw "execution struct field count mismatch or duplicate field"
      let values ← fields.mapM fun entry => return (entry.1, ← types.value entry.2)
      let ordered ← decl.fields.mapM fun (name, expected) => do
        let some (_, actual, value) := values.find? (·.1 == name) | throw s!"missing execution struct field {name}"
        types.checkChildren [expected.subst env] [actual]
        return value
      return (type, .construct (Generic.Instance.symbol ⟨name, args⟩) Generic.structConstructor ordered)
  | .construct _ ctor children =>
      let .named name args := type | throw "constructor data requires a nominal enum type"
      let some decl := types.enums.find? (·.name == name) | throw s!"not an enum type: {name}"
      let some constructor := decl.constructors.find? (·.name == ctor) | throw s!"unknown data constructor {name}::{ctor}"
      let env ← Generic.arguments decl.typeParams args
      let values ← children.mapM types.value
      types.checkChildren (constructor.fields.map (·.subst env)) (values.map Prod.fst)
      return (type, .construct (Generic.Instance.symbol ⟨name, args⟩) ctor (values.map Prod.snd))
termination_by sizeOf input
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  all_goals first | omega | cases ‹String × DataValue F›; simp_all only [Prod.mk.sizeOf_spec]; omega

end DataTypes

private def Export.prepareHint [NatCast F] [Zero F] (exported : Export F)
    (entry : HintEntry F) : Except String (FlatHintEntry F) := do
  let expected ← exported.dataTypes.inputType entry.type
  let (keyType, key) ← exported.dataTypes.value entry.key
  let (actual, output) ← exported.dataTypes.value entry.output
  if expected != actual then throw "hint output type mismatch"
  let keyLayout ← (exported.bytecode.enums.layout keyType.toCore).mapError reprStr
  let outputLayout ← (exported.bytecode.enums.layout expected.toCore).mapError reprStr
  let key ← Compiler.need (keyLayout.encode key.toValue) "cannot encode hint key"
  let output ← Compiler.need (outputLayout.encode output.toValue) "cannot encode hint output"
  return ⟨expected.toCore, keyType.toCore, key, output, entry.channel⟩

/-- Prepare per-execution witness data in Lean. Rust validates the transport
again and builds the index, coalescing identical rows and rejecting conflicts.
Use an explicit tail loop: the generic Array.mapM implementation can retain a
native continuation frame per row when invoked through the polymorphic FFI. -/
def Export.prepareHints [NatCast F] [Zero F] (exported : Export F)
    (entries : Array (HintEntry F)) : Except String (Array (FlatHintEntry F)) :=
  let rec go : List (HintEntry F) → Array (FlatHintEntry F) → Except String (Array (FlatHintEntry F))
    | [], acc => .ok acc
    | entry :: rest, acc =>
      match exported.prepareHint entry with
      | .error error => .error error
      | .ok value => go rest (acc.push value)
  go entries.toList #[]

end Aiur.Execution
