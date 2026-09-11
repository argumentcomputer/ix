import Compilatrix.UniqueReuse.RuntimeNative
import Compilatrix.X86.AllocatingTarget

/-! Selection and artifact identity for the first allocating native helper.
The selected source family and physical reuse certificate are unchanged;
the native schedule reserves the first cons across a real internal CALL. -/

namespace Compilatrix.UniqueReuse.Runtime.AllocatingNative

open Compilatrix.Ixon (Address Constant)
open Compilatrix.IxIR Compilatrix.X86

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

structure Output (compilation : Compilation constants entry config checkFuel eraseFuel limits) where
  base : Native.Output compilation

inductive Selection (compilation : Compilation constants entry config checkFuel eraseFuel limits) where
  | skipped (reason : String)
  | native (output : Output compilation)

def select (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    (foldCounters : Bool := false) : Selection compilation :=
  match Native.select compilation foldCounters with
  | .skipped reason => .skipped reason
  | .native base => .native ⟨base⟩

def roleChecked (role : Native.Role) (foldCounters : Bool) : Checked :=
  match role with | .main => Allocating.checked foldCounters | .release => RuntimeTarget.releaseChecked

def policyVersion (role : Native.Role) (foldCounters : Bool) : UInt32 :=
  match role with | .main => if foldCounters then 5 else 4 | .release => 2

def Output.policyBytes {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Native.Role) : ByteArray :=
  Encoding.domain "compilatrix/native-runtime-allocating-provenance/1" ++ Encoding.tag 0 ++
    output.base.policyBytes role ++ Encoding.string (Allocating.policyTag output.base.foldCounters) ++
    Encoding.nat Allocating.stackBytes ++ Encoding.nat (policyVersion role output.base.foldCounters).toNat

def Output.identity {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Native.Role) : Address := Address.blake3 (output.policyBytes role)

structure Object where
  role : Native.Role
  foldCounters : Bool
  provenance : ELF.Provenance
  policyBytes : ByteArray
  policyIdentity : Address
  encoded : Encode.Output
  bytes : ByteArray
  streamValid : Stream.Valid (roleChecked role foldCounters).program encoded
  objectValid : ELF.Valid (ELF.Input.mk encoded (roleChecked role foldCounters).program.entry role.symbol provenance) bytes

def Output.emit {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Native.Role) : Except String Object := do
  let stream ← (Stream.encode (roleChecked role output.base.foldCounters)).mapError reprStr
  let encoded := stream.output
  let provenance := ELF.Provenance.ixir1Policy output.base.graph Native.loweringVersion
    (policyVersion role output.base.foldCounters)
  let object ← (ELF.writeChecked (ELF.Input.mk encoded (roleChecked role output.base.foldCounters).program.entry role.symbol provenance)).mapError reprStr
  return {
    role, foldCounters := output.base.foldCounters, provenance, encoded, bytes := object.bytes,
    policyBytes := output.policyBytes role, policyIdentity := output.identity role,
    streamValid := stream.valid, objectValid := object.valid }

theorem Output.emit_spec {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Native.Role) {object : Object} (emitted : output.emit role = .ok object) :
    object.role = role ∧ object.provenance = .ixir1Policy output.base.graph Native.loweringVersion
      (policyVersion role output.base.foldCounters) ∧ object.policyBytes = output.policyBytes role ∧
      object.policyIdentity = output.identity role ∧ object.foldCounters = output.base.foldCounters := by
  unfold Output.emit at emitted
  cases stream : Stream.encode (roleChecked role output.base.foldCounters) with
  | error error => simp [stream, Except.mapError] at emitted
  | ok streamValue =>
      simp only [stream, Except.mapError, bind, Except.bind] at emitted
      cases written : ELF.writeChecked (ELF.Input.mk streamValue.output
          (roleChecked role output.base.foldCounters).program.entry role.symbol
          (.ixir1Policy output.base.graph Native.loweringVersion (policyVersion role output.base.foldCounters))) with
      | error error => simp [written] at emitted
      | ok objectValue =>
          simp only [written, pure, Except.pure] at emitted
          cases Except.ok.inj emitted
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Object.provenance_parsed (object : Object) :
    (ELFRead.parse object.bytes).map ELFRead.View.provenance = some (ELF.expectedProvenance object.provenance) := by
  obtain ⟨view, parsed, fields⟩ := object.objectValid
  simp [parsed, fields.provenance]

end Compilatrix.UniqueReuse.Runtime.AllocatingNative
