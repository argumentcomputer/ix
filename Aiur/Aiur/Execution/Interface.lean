import Aiur.Execution.Compile
import Aiur.Execution.Data

namespace Aiur.Execution

/-- Source-facing descriptions survive only at the public boundary. There is
deliberately no pointer or opaque variant, even for zero-width arrays. -/
inductive IOType where
  | field
  | tuple (items : List IOType)
  | array (element : IOType) (length : Nat)
  | record (name : String) (fields : List (String × IOType))
  | enum (name : String) (constructors : List (String × List IOType))
  deriving Repr, BEq

structure Interface where
  name : String
  inputs : List IOType
  output : Option IOType
  deriving Repr, BEq

def typeName : Generic.Ty → String
  | .field => "Field"
  | .param name => name
  | .ptr type => "&" ++ typeName type
  | .array type length => "[" ++ typeName type ++ "; " ++ toString length ++ "]"
  | .tuple items => "(" ++ String.intercalate ", " (items.map typeName) ++
      (if items.length == 1 then ",)" else ")")
  | .named name args => name ++ if args.isEmpty then "" else
      "<" ++ String.intercalate ", " (args.map typeName) ++ ">"
termination_by type => sizeOf type

/-- Inspect retained declarations before representation aliases disappear. -/
def IOType.ofSource (p : Generic.Program α) (opaqueNames : List String) :
    Nat → Generic.Ty → Option IOType
  | 0, _ => none
  | fuel + 1, type => do
      match type with
      | .field => return .field
      | .ptr _ | .param _ => none
      | .tuple items => return .tuple (← items.mapM (IOType.ofSource p opaqueNames fuel))
      | .array element length => return .array (← IOType.ofSource p opaqueNames fuel element) length
      | .named name args =>
          if opaqueNames.contains name then none else do
            if let some decl := p.aliases.find? (·.name == name) then
              if decl.typeParams.length != args.length then none else
                IOType.ofSource p opaqueNames fuel (decl.target.subst (decl.typeParams.zip args))
            else if let some decl := p.findStruct? name then
              if decl.typeParams.length != args.length then none else do
                let fields ← decl.fields.mapM fun (fieldName, type) => do
                  return (fieldName, ← IOType.ofSource p opaqueNames fuel (type.subst (decl.typeParams.zip args)))
                return .record (typeName type) fields
            else do
              let decl ← p.findEnum? name
              if decl.typeParams.length != args.length then none else do
                let ctors ← decl.constructors.mapM fun ctor => do
                  let fields ← ctor.fields.mapM fun type =>
                    IOType.ofSource p opaqueNames fuel (type.subst (decl.typeParams.zip args))
                  return (ctor.name, fields)
                return .enum (typeName type) ctors

structure Export (F : Type) where
  bytecode : Bytecode F
  interfaces : List Interface
  dataTypes : DataTypes := {}
  deriving Repr, BEq

end Aiur.Execution

namespace Aiur.Modules

def Prepared.exportExecution [NatCast F] [Zero F] [DecidableEq F]
    (prepared : Prepared (program : Program F)) : Except String (Execution.Export F) := do
  let code ← prepared.compileExecution
  let (world, _) ← collect program (prepared.selections.map (·.external))
  let opaqueNames := opaqueNames program world (.mk "" [])
  let source := prepared.environment.assembly.program
  let interfaces ← prepared.selections.mapM fun entry => do
    let some fn := source.findFunction? entry.resolved.name
      | throw s!"missing source entry {entry.external}"
    let inputs ← fn.params.mapM fun (_, type) =>
      Execution.Compiler.need (Execution.IOType.ofSource source opaqueNames 1024 type)
        s!"entry {entry.external} has no public IO representation"
    let output := Execution.IOType.ofSource source opaqueNames 1024 fn.result
    return { name := entry.external, inputs, output : Execution.Interface }
  return ⟨code, interfaces, Execution.DataTypes.ofSource source opaqueNames⟩

end Aiur.Modules
