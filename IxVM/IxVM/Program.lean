import Aiur.Modules.Frontend
import Aiur.Library.Blake3.Goldilocks
import Aiur.Library.List.Word
import Aiur.Library.Option
import Blake3.Rust
import IxVM.Modules.RBTreeMap
import IxVM.Modules.Ixon
import IxVM.Modules.KernelTypes
import IxVM.Modules.KernelLevels
import IxVM.Modules.KernelRoles
import IxVM.Modules.KernelInfer
import IxVM.Modules.KernelClaim
import IxVM.Modules.IxByteStream
import IxVM.Modules.IxonSerialize
import IxVM.Modules.IxonDeserialize
import IxVM.Modules.KernelKlimbs
import IxVM.Modules.KernelNatPrim
import IxVM.Modules.Convert
import IxVM.Modules.Ingress
import IxVM.Modules.KernelSubst
import IxVM.Modules.KernelRoleSpec
import IxVM.Modules.KernelWhnf
import IxVM.Modules.KernelInferOnly
import IxVM.Modules.KernelDefEq
import IxVM.Modules.KernelCheck
import IxVM.Modules.IxVMCompat
import IxVM.Modules.KernelEval
import IxVM.Modules.IxVM

/-! The stage-one IxVM application explicitly selects Goldilocks word and hash
implementations. The compiler, its proofs, and the runtime remain generic.

The modules are the Lean files under `IxVM/IxVM/Modules/`, written in Formal
Aiur's module language as Lean syntax (`aiur⟦ … ⟧`) and elaborated when this
package is built. They are the source of truth. `KernelRoleSpec.lean` alone is
rendered, by `lake exe ix codegen` from IxC's role specifications. -/
namespace IxVM
open Aiur

abbrev modulus := Library.U32.Goldilocks.modulus
abbrev F := Library.U32.Goldilocks.F

/-- The IxVM modules, in the order they are composed. -/
def source : Modules.Program Nat :=
  [Source.rbTreeMap, Source.ixon, Source.kernelTypes, Source.kernelLevels, Source.kernelRoles,
    Source.kernelInfer, Source.kernelClaim, Source.ixByteStream, Source.ixonSerialize,
    Source.ixonDeserialize, Source.kernelKlimbs, Source.kernelNatPrim, Source.convert,
    Source.ingress, Source.kernelSubst, Source.kernelRoleSpec, Source.kernelWhnf,
    Source.kernelInferOnly, Source.kernelDefEq, Source.kernelCheck, Source.ixvmCompat,
    Source.kernelEval, Source.ixvm].foldl Modules.Program.append {}

/-- The library templates the modules use. -/
def libraries : Modules.Program Nat :=
  Library.Blake3.templates.append Library.List.Word.declarations
    |>.append Library.Option.declarations

-- The modules check against the libraries when this file is built.
#aiur_check libraries.append source

/-- The IxVM program: the modules with the shared word and hash libraries,
over Goldilocks. Callers choose entrypoints with `Aiur.Modules.prepare` and may
export bytecode, certified circuits, or population plans from the result. -/
def program : Modules.Program F :=
  Library.Blake3.Goldilocks.program.append (Library.List.Word.declarations.toField F)
    |>.append (Library.Option.declarations.toField F)
    |>.append (source.toField F)

/-- BLAKE3, in lowercase hex, of `text`. -/
def hexDigest (text : String) : String :=
  String.join ((Blake3.Rust.hash text.toUTF8).val.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

/-- The deployed program's identity: BLAKE3 of `reprStr program`, computed when
this file is compiled. `ixvm digest` prints it, the exporter reports it, and
`ix` keys its artifact cache by it. -/
def programDigest : String := aiur_eval% hexDigest (reprStr program)

end IxVM
