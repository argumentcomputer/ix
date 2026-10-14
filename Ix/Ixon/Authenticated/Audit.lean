import Ix.Ixon.Authenticated.Theorems
import Ix.Ixon.BlockOrder.Audit

/-! # The authenticated entries' boundary

The instantiation at BLAKE3 adds exactly one thing to the generic entries'
compiled closures: the admission hash's substitution, `Address.admissionHash`
executed as `Address.blake3`, with the Rust backend's foreign primitives it
reaches. The runtime audit admits it only as the ruled assumption
`Ix.Kernel.Audit.assumedSubstitutions`, and fails without it; the
instantiated entries are the generic ones applied to the admission hash
(their definitions are frozen below), so the hash argument is the only way
the foreign primitives enter. The import closure is the root library's
(`Ix.Address` brings `Lean`); the generic entries keep their hash-free
import fences (`Ixon.Projection.Audit`, `Ixon.BlockOrder.Audit`). -/

namespace Ixon.Authenticated.Audit

/-- The authenticated entries, and the admission hash itself (whose
`implemented_by` the closure reports). -/
def operations : Array Lean.Name :=
  #[``Ixon.Authenticated.checkBytes, ``Ixon.Authenticated.checkBytesProjection,
    ``Ixon.Authenticated.checkBytesBlockOrder, ``Address.admissionHash]

/-- The kernel's rulings and exactly the one assumed substitution. -/
def rulings : Ix.Kernel.Audit.RuntimeRulings :=
  { Ix.Kernel.Audit.runtimeRulings with assumed := Ix.Kernel.Audit.assumedSubstitutions }

/-- The generic entries the instantiation applies. -/
def generic : Array Lean.Name :=
  Ix.Kernel.Admission.Audit.operations ++ Ixon.Projection.Audit.operations ++
    Ixon.BlockOrder.Audit.operations

end Ixon.Authenticated.Audit

/-- info: runtime closure of [Ixon.Authenticated.checkBytes,
 Ixon.Authenticated.checkBytesProjection,
 Ixon.Authenticated.checkBytesBlockOrder,
 Address.admissionHash]: 5407 compiled functions; inherited externs 124, implemented_by 1,
unsafe 23, csimp 4; ruled assumed 4, computed_field 18, csimp 21, partial 9 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.Authenticated.Audit.operations #[`Init, `Std] Ixon.Authenticated.Audit.rulings

-- Without the assumption the closure fails on the substitution and its primitives.
/-- error: project-level execution replacements reached from [Ixon.Authenticated.checkBytes,
 Ixon.Authenticated.checkBytesProjection,
 Ixon.Authenticated.checkBytesBlockOrder,
 Address.admissionHash]:
[Address.admissionHash, Blake3.Rust.hasherFinalize, Blake3.Rust.hasherInit, Blake3.Rust.hasherUpdate] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.Authenticated.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

/-- info: Additional authenticated-entry externs: [Blake3.Rust.hasherFinalize, Blake3.Rust.hasherUpdate, Blake3.Rust.hasherInit]
---
info: Additional authenticated-entry implemented_by: [(Address.admissionHash, Address.blake3)]
---
info: Additional authenticated-entry unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ixon.Authenticated.Audit.generic
  let after := Ix.Kernel.Audit.runtimeClosure env Ixon.Authenticated.Audit.operations
  Lean.logInfo m!"Additional authenticated-entry externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional authenticated-entry implemented_by: {after.implementedBy}"
  Lean.logInfo m!"Additional authenticated-entry unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"

/-! ## The instantiation -/

/-- info: def Address.admissionHash : ByteArray → Address :=
fun x => Address.blake3Pure x -/
#guard_msgs (whitespace := lax) in
#print Address.admissionHash

/-- info: def Ixon.Authenticated.checkBytes : Ix.Kernel.Admission.Limits →
  Ix.Kernel.Admission.Records →
    Ix.Kernel.Ingress.Blobs →
      (optParam (Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) fun x => none) →
        Except Ix.Kernel.Admission.Error Ix.Kernel.Env :=
fun limits records blobs hint => Ix.Kernel.Admission.checkBytes Address.admissionHash limits records blobs hint -/
#guard_msgs (whitespace := lax) in
#print Ixon.Authenticated.checkBytes

/-- info: def Ixon.Authenticated.checkBytesProjection : Nat →
  Ix.Kernel.Admission.Limits →
    Ix.Kernel.Admission.Records →
      Ix.Kernel.Ingress.Blobs →
        (optParam (Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) fun x => none) →
          Except Ixon.Projection.CheckError Ix.Kernel.Env :=
fun maxProjections limits records blobs hint =>
  Ixon.Projection.checkBytes Address.admissionHash maxProjections limits records blobs hint -/
#guard_msgs (whitespace := lax) in
#print Ixon.Authenticated.checkBytesProjection

/-- info: def Ixon.Authenticated.checkBytesBlockOrder : Nat →
  Ix.Kernel.Admission.Limits →
    Ixon.BlockOrder.Limits →
      Ix.Kernel.Admission.Records →
        Ix.Kernel.Ingress.Blobs →
          (optParam (Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) fun x => none) →
            Except Ixon.BlockOrder.CheckError Ix.Kernel.Env :=
fun maxProjections limits orderLimits records blobs hint =>
  Ixon.BlockOrder.checkBytes Address.admissionHash maxProjections limits orderLimits records blobs hint -/
#guard_msgs (whitespace := lax) in
#print Ixon.Authenticated.checkBytesBlockOrder

#guard_kernel_axioms Address.admissionHash_eq [propext, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.admissionHash_width [propext, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesBlockOrder_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesBlockOrder [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesProjection_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesBlockOrder_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesBlockOrder_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesBlockOrder_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Authenticated.checkBytesBlockOrder_no_proof_of_False [propext, Classical.choice, Quot.sound]

/-! ## The statements at BLAKE3 -/

/-- info: @Ixon.Authenticated.checkBytes_authentic : ∀ {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Authenticated.checkBytes limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic Address.blake3Pure records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytes_authentic

/-- info: Ixon.Authenticated.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Authenticated.checkBytes limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytes_has_model

/-- info: Ixon.Authenticated.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Authenticated.checkBytes limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytes_no_proof_of_False

/-- info: @Ixon.Authenticated.checkBytesProjection_authentic : ∀ {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Authenticated.checkBytesProjection maxProjections limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output,
        Ix.Kernel.Admission.Hashed Address.blake3Pure output ∧
          Ix.Kernel.Admission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytesProjection_authentic

/-- info: @Ixon.Authenticated.checkBytesBlockOrder_authentic : ∀ {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Authenticated.checkBytesBlockOrder maxProjections limits orderLimits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output,
        Ix.Kernel.Admission.Hashed Address.blake3Pure output ∧
          Ix.Kernel.Admission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Authenticated.checkBytesBlockOrder_authentic
