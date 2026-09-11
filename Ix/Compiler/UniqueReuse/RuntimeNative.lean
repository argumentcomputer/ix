import Ix.Compiler.UniqueReuse.Runtime
import Ix.Compiler.X86.RuntimeTarget
import Ix.Compiler.X86.ELFValidate

/-! Native selection and artifact identity for a compiled function. The
preimage commits to the function, schema, policies, and runtime ABI; runtime
payloads are deliberately absent. -/

namespace Ix.Compiler.UniqueReuse.Runtime.Native

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR
open Ix.Compiler.X86

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

structure Output (compilation : Compilation constants entry config checkFuel eraseFuel limits) where
  reuseSelected : compilation.selection.reuse = true
  foldCounters : Bool := false

inductive Selection (compilation : Compilation constants entry config checkFuel eraseFuel limits) where
  | skipped (reason : String)
  | native (output : Output compilation)

def select (compilation : Compilation constants entry config checkFuel eraseFuel limits)
    (foldCounters : Bool := false) : Selection compilation :=
  if reused : compilation.selection.reuse = true then .native ⟨reused, foldCounters⟩
  else .skipped (compilation.selection.reason.getD "runtime native entry requires static unique reuse")

inductive Role where
  | main | release
  deriving Repr, BEq, DecidableEq

def Role.name : Role → String | .main => "main" | .release => "release"
def Role.symbol : Role → String | .main => "compilatrix_runtime_reverse" | .release => "compilatrix_runtime_drop"
def Role.policyVersion (role : Role) (foldCounters : Bool := false) : UInt32 :=
  match role with | .main => if foldCounters then 3 else 1 | .release => 2
def Role.checked (role : Role) (foldCounters : Bool := false) : Checked :=
  match role with | .main => RuntimeTarget.checked foldCounters | .release => RuntimeTarget.releaseChecked
def loweringVersion : UInt32 := 3

/-- Check exact scalar representation before preparing a native argument. -/
def ofNats (values : List Nat) : Except String (List Word) :=
  if values.length > UniqueABI.maxLength then .error "runtime input exceeds 64 cons cells"
  else if values.all (fun value => decide (value < UInt64.size)) then .ok (values.map UInt64.ofNat)
  else .error "runtime Nat does not fit an exact 64-bit Word"

theorem ofNats_exact {values : List Nat} {words : List Word} (accepted : ofNats values = .ok words) :
    words.map UInt64.toNat = values ∧ words.length ≤ UniqueABI.maxLength := by
  unfold ofNats at accepted
  split at accepted
  · contradiction
  next bounded =>
    split at accepted
    · next exactWords =>
        have equal := Except.ok.inj accepted
        subst words
        constructor
        · rw [List.map_map]
          calc
            _ = values.map (fun value => value) := List.map_congr_left fun value member =>
              UInt64.toNat_ofNat_of_lt' (of_decide_eq_true (List.all_eq_true.mp exactWords value member))
            _ = values := List.map_id' values
        · simpa using Nat.le_of_not_gt bounded
    · contradiction

def Output.graph {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (_output : Output compilation) : Address :=
  IxIR1.Optimizer.graphRoot (Runtime.artifacts compilation.schema)
    (UniqueReuse.mainCode { schema := compilation.schema, values := [] })

def Output.policyBytes {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) : ByteArray :=
  Encoding.domain "compilatrix/native-runtime-unique-provenance/1" ++ Encoding.tag 0 ++
    Encoding.address (Address.blake3 (sourceBytes constants entry)) ++ Encoding.address output.graph ++
    Encoding.address (entryAddress compilation.schema) ++ Encoding.address (functionAddress compilation.schema) ++
    Encoding.string Runtime.policyTag ++ Encoding.string Ixon.RecursorUsage.policyTag ++
    Encoding.string IxIR2.UniqueLower.policyTag ++ Encoding.string IxIR2.UniqueLower.reusePolicyTag ++
    Encoding.string IxIR2.CreditPolicy.callLocalV0.tag ++
    Encoding.nat checkFuel ++ Encoding.nat eraseFuel ++ targetLimitBytes limits ++
    Encoding.string RuntimeTarget.abiTag ++ Encoding.string (RuntimeTarget.policyTag output.foldCounters) ++
    Encoding.nat UniqueABI.maxLength ++ Encoding.nat UniqueABI.headerWords ++ Encoding.nat UniqueABI.cellWords ++
    Encoding.address compilation.schema.nil ++ Encoding.address compilation.schema.cons ++
    Encoding.string role.name ++ Encoding.nat loweringVersion.toNat ++ Encoding.nat (role.policyVersion output.foldCounters).toNat ++
    (if output.foldCounters then Encoding.string UniqueCounterFold.policyTag else ByteArray.empty)

def Output.identity {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) : Address := Address.blake3 (output.policyBytes role)

structure Object where
  role : Role
  foldCounters : Bool := false
  provenance : ELF.Provenance
  policyBytes : ByteArray
  policyIdentity : Address
  encoded : Encode.Output
  bytes : ByteArray
  streamValid : Stream.Valid (role.checked foldCounters).program encoded
  objectValid : ELF.Valid { encoded, entryBlock := (role.checked foldCounters).program.entry, exportName := role.symbol, provenance } bytes

def Output.emit {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) (role : Role) : Except String Object := do
  let stream ← (Stream.encode (role.checked output.foldCounters)).mapError reprStr
  let encoded := stream.output
  let provenance := ELF.Provenance.ixir1Policy output.graph loweringVersion (role.policyVersion output.foldCounters)
  let object ← (ELF.writeChecked { encoded, entryBlock := (role.checked output.foldCounters).program.entry, exportName := role.symbol, provenance }).mapError reprStr
  return {
    role, foldCounters := output.foldCounters, provenance, encoded, bytes := object.bytes,
    policyBytes := output.policyBytes role, policyIdentity := output.identity role
    streamValid := stream.valid, objectValid := object.valid }

def Output.targetChecked {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) :
    IxIR2.Validate.Checked limits (IxIR2.UniqueLower.context compilation.schema) (Runtime.program compilation.schema true) := by
  have checked := compilation.selection.checked
  rw [output.reuseSelected] at checked
  exact checked

end Ix.Compiler.UniqueReuse.Runtime.Native
