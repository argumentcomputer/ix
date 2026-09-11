import Ix.Compiler.UniqueReuse.ModeCheck
import Ix.Compiler.IxIR1.Serialize
import Ix.Compiler.IxIR1.ReaddressAll

/-! Consuming ownership emission for the checked reverse instantiation. Every
case field is moved before the parent is shallow-freed. No shared retain or
release is generated. The declaration is canonically addressed after emission;
the separate recursor-instance address retains the source world vector. -/

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)

def nilId (schema : Schema) : CtorId := IxIR1.Lower.ctorIdOf schema.nil 0
def consId (schema : Schema) : CtorId := IxIR1.Lower.ctorIdOf schema.cons 1

def lets : List Op → Code → Code
  | [], code => code
  | operation :: rest, code => .letOp operation (lets rest code)

def consumingBody (schema : Schema) : Code :=
  .case (.var 0) false #[
    .mk 0 0 (.letOp (.free (.var 0)) (.ret (.var 2))),
    .mk 1 2 (lets
      [.free (.var 2), .alloc .unique (consId schema) #[.var 2, .var 4],
       .callSelf #[.var 0, .var 2]] (.ret (.var 0)))]

def consumingFunction (schema : Schema) : FnDef :=
  { arity := 2, result := .unique, papSafe := false, body := consumingBody schema }

def functionAddress (schema : Schema) : Address := (Decl.fn (consumingFunction schema)).address

def inputOperations (schema : Schema) (values : List Nat) : List Op :=
  .alloc .unique (nilId schema) #[] ::
    values.reverse.map (fun value => .alloc .unique (consId schema) #[.lit (.nat value), .var 0])

def mainCode (plan : Plan) : Code :=
  lets (inputOperations plan.schema plan.values ++
    [.alloc .unique (nilId plan.schema) #[], .call (functionAddress plan.schema) #[.var 0, .var 1]])
    (.ret (.var 0))

def declarations (schema : Schema) : List (Address × Decl) :=
  [(functionAddress schema, .fn (consumingFunction schema))]

def artifacts (schema : Schema) : List ReaddressAll.Artifact :=
  [.ordinary (functionAddress schema) (.fn (consumingFunction schema))]

structure Lowered {constants : List (Address × Ixon.Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    (source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique
      checkFuel eraseFuel) where
  checked : CheckedSource source

def Lowered.plan {constants : List (Address × Ixon.Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    {source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique
      checkFuel eraseFuel} (lowered : Lowered source) : Plan := lowered.checked.recovery.checked.plan

def lower {constants : List (Address × Ixon.Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    (source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique
      checkFuel eraseFuel) : Except String (Lowered source) := do
  return { checked := ← checkSource source }

end Ix.Compiler.UniqueReuse
