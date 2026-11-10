import Aiur.Modules.Emit
import IxVM.Field
import Aiur.Library.Blake3.Goldilocks
import Aiur.Library.List.Word
import Aiur.Library.Option
import Blake3.Rust
import IxVM.Source.RBTreeMap
import IxVM.Source.Ixon
import IxVM.Source.KernelTypes
import IxVM.Source.KernelLevels
import IxVM.Source.KernelRoles
import IxVM.Source.KernelInfer
import IxVM.Source.KernelClaim
import IxVM.Source.IxByteStream
import IxVM.Source.IxonSerialize
import IxVM.Source.IxonDeserialize
import IxVM.Source.KernelKlimbs
import IxVM.Source.KernelNatPrim
import IxVM.Source.Convert
import IxVM.Source.Ingress
import IxVM.Source.KernelSubst
import IxVM.Source.KernelRoleSpec
import IxVM.Source.KernelWhnf
import IxVM.Source.KernelInferOnly
import IxVM.Source.KernelDefEq
import IxVM.Source.KernelCheck
import IxVM.Source.IxVMCompat
import IxVM.Source.KernelEval
import IxVM.Source.IxVM

/-! The IxVM program elaborator. Imported DSL declarations are resolved as one
program, then emitted once as the public definitions used by execution and proofs. -/

namespace IxVM.Elab
open Lean Elab Command
open Aiur

/-- Explicit composition order, stable across import ordering. -/
def moduleNames : List Name := [
  `IxVM.RBTreeMap, `IxVM.Ixon, `IxVM.KernelTypes, `IxVM.KernelLevels, `IxVM.KernelRoles,
  `IxVM.KernelInfer, `IxVM.KernelClaim, `IxVM.IxByteStream, `IxVM.IxonSerialize,
  `IxVM.IxonDeserialize, `IxVM.KernelKlimbs, `IxVM.KernelNatPrim, `IxVM.Convert,
  `IxVM.Ingress, `IxVM.KernelSubst, `IxVM.KernelRoleSpec, `IxVM.KernelWhnf,
  `IxVM.KernelInferOnly, `IxVM.KernelDefEq, `IxVM.KernelCheck, `IxVM.IxVMCompat,
  `IxVM.KernelEval, `IxVM.Entry]

/-- Reconstruct compiler input from imported declaration metadata. -/
def moduleProgram (env : Lean.Environment) : Except String (Modules.Program F) := do
  let source ← Modules.declaredModules env moduleNames
  let libraries := Library.Blake3.templates.append Library.List.Word.declarations
    |>.append Library.Option.declarations
  Modules.checkTemplates (libraries.append source)
  return Library.Blake3.Goldilocks.program.append (Library.List.Word.declarations.toField F)
    |>.append (Library.Option.declarations.toField F)
    |>.append (source.toField F)

/-- Library functions use their qualified Aiur names; the entry module's Lean
namespace is `Entry` to distinguish it from the enclosing `IxVM` namespace. -/
def functionName (symbol : String) : Name :=
  let parts := match symbol.splitOn "::" with
    | "IxVM" :: rest => "Entry" :: rest
    | parts => parts
  parts.foldl Name.str `IxVM


private def hexDigest (text : String) : String :=
  String.join ((Blake3.Rust.hash text.toUTF8).val.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

elab "#ixvm_program" : command => Modules.Frontend.uncounted do
  let input ← ofExcept (moduleProgram (← getEnv))
  let (world, _) ← ofExcept (Modules.collect input ["IxVM::verify_claim"])
  let assembly ← ofExcept (Modules.assemble input world)
  -- Resolve functions using table types. Static.lean proves the validity of
  -- the real rows from their generator, without embedding half a million rows.
  let headers := { assembly.program with
    tables := assembly.program.tables.map fun t => { t with rows := [] } }
  let source ← ofExcept (Generic.prepare headers)
  ofExcept (source.checkEntry "IxVM::verify_claim")
  let quoteField ← liftTermElabM (Modules.numeralQuoter (mkConst ``IxVM.F) (fun x : F => x.val))
  letI := quoteField
  Modules.emitProgram (mkConst ``IxVM.F) `IxVM functionName source.program (mkConst `IxVM.genericTables)
  liftCoreM <| addAndCompile (.defnDecl {
    name := `IxVM.programDigest, levelParams := [], type := mkConst ``String,
    value := toExpr (hexDigest (reprStr input)), hints := .regular 0, safety := .safe })
  liftCoreM <| enableRealizationsForConst `IxVM.programDigest

end IxVM.Elab
