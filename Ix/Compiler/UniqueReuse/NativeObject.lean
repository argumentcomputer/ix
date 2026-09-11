import Ix.Compiler.UniqueReuse.Native
import Ix.Compiler.UniqueReuse.Provenance
import Ix.Compiler.X86.ELFValidate

/-! Native object production is available only from successful checked native
selection. Both ELF notes retain the actual canonical IxIR₁ graph root. Native
lowering version 2 and role policy versions 1/2 distinguish main and release;
the extended canonical preimage also records source policy and arena ABI. -/

namespace Ix.Compiler.UniqueReuse.Native

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.X86
open Ix.Compiler.IxIR

inductive Role where
  | main | release
  deriving Repr, BEq, DecidableEq

def Role.name : Role → String | .main => "main" | .release => "release"
def Role.symbol : Role → String | .main => "compilatrix_main" | .release => "compilatrix_unique_drop"
def Role.policyVersion : Role → UInt32 | .main => 1 | .release => 2

def nativeLoweringVersion : UInt32 := 2

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

/-- This digest is an extended native policy identity, never an IxIR₁ root. -/
def Output.nativeBytes {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) : ByteArray :=
  Encoding.domain "compilatrix/native-unique-provenance/1" ++ Encoding.tag 0 ++
    Encoding.address compilation.provenance.identity ++ Encoding.address compilation.provenance.graph ++
    Encoding.string UniqueABI.policyTag ++ Encoding.string UniqueTarget.policyTag ++
    Encoding.nat UniqueABI.maxLength ++ Encoding.nat UniqueABI.headerWords ++ Encoding.nat UniqueABI.cellWords ++
    Encoding.address compilation.plan.schema.nil ++ Encoding.address compilation.plan.schema.cons ++
    Encoding.list Encoding.nat (output.words.map UInt64.toNat) ++
    Encoding.string role.name ++ Encoding.nat nativeLoweringVersion.toNat ++ Encoding.nat role.policyVersion.toNat

def Output.nativeIdentity {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) : Address := Address.blake3 (output.nativeBytes role)

def Output.objectProvenance {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (_output : Output compilation) (role : Role) : ELF.Provenance :=
  .ixir1Policy compilation.provenance.graph nativeLoweringVersion role.policyVersion

structure Object where
  role : Role
  checked : Checked
  provenance : ELF.Provenance
  policyBytes : ByteArray
  policyIdentity : Address
  encoded : Encode.Output
  bytes : ByteArray
  streamValid : Stream.Valid checked.program encoded
  objectValid : ELF.Valid { encoded, entryBlock := checked.program.entry, exportName := role.symbol, provenance } bytes

def Output.emit {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) : Except String Object := do
  let checked := match role with | .main => output.main | .release => output.release
  let stream ← (Stream.encode checked).mapError reprStr
  let encoded := stream.output
  let provenance := output.objectProvenance role
  let input : ELF.Input :=
    { encoded
      entryBlock := checked.program.entry
      exportName := role.symbol
      provenance }
  let object ← (ELF.writeChecked input).mapError reprStr
  return {
    role, checked, provenance, encoded, bytes := object.bytes
    policyBytes := output.nativeBytes role
    policyIdentity := output.nativeIdentity role
    streamValid := stream.valid, objectValid := object.valid }

end Ix.Compiler.UniqueReuse.Native
