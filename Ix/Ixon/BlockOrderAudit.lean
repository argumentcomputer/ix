/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.BlockOrderProofs
import Ix.Ixon.ProjectionAudit

namespace Ix.Ixon.BlockOrder.Audit

/-- The certified entry with canonical block order (L5). -/
def operations : Array Lean.Name := #[``checkBytes, ``canonicalClasses, ``compareExpr]

/-- The intrinsic reference variant (until L6). -/
def intrinsicOperations : Array Lean.Name := #[``checkBytesIntrinsic, ``canonicalClasses, ``compareExpr]

def allowedData (name : Lean.Name) : Bool :=
  Projection.Audit.allowedData name || name == `Ix.Ixon.ReduceUniverse || name == `Ix.Ixon.BlockOrder

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Projection.Audit.allowedProof name || name == `Ix.Ixon.BlockOrderProofs

end Ix.Ixon.BlockOrder.Audit

#guard_msgs (drop info) in
run_cmd Ix.Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder] Ix.Ixon.BlockOrder.Audit.allowedData

#guard_msgs (drop info) in
run_cmd Ix.Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrderProofs] Ix.Ixon.BlockOrder.Audit.allowedProof

#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrderProofs
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.Tc.CanonicalCheck
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Blake3.Rust
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Blake3.C
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.IxonUniv
#guard !Ix.Ixon.Projection.Audit.allowedData `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Audit.dataImports `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Ix.Ixon.BlockOrder

/- Measured before freezing (L5; re-measured at int-4): the certified entry
adds the order check to the certified projection entry. L5 alone froze 33643
functions and 124 externs; rebased onto L4b, the committed Nat-operation
pins are decoded from a string table instead of upstream's JSON dumps
spliced as one closed term (27,096 compiled functions), as in
`Ix.Ixon.Admission.Audit`. -/
/-- info: runtime closure of [Ix.Ixon.BlockOrder.checkBytes,
 Ix.Ixon.BlockOrder.canonicalClasses,
 Ix.Ixon.BlockOrder.compareExpr]: 5524 compiled functions; inherited externs 132, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Ixon.BlockOrder.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

/- The intrinsic reference variant, unchanged from L4. -/
/-- info: runtime closure of [Ix.Ixon.BlockOrder.checkBytesIntrinsic,
Ix.Ixon.BlockOrder.canonicalClasses, Ix.Ixon.BlockOrder.compareExpr]: 2087 compiled functions;
inherited externs 86, implemented_by 0, unsafe 3, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.BlockOrder.Audit.intrinsicOperations #[`Init, `Std]

#guard_kernel_axioms Ix.Ixon.BlockOrder.Refinement.positive [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.Refinement.fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.canonicalClasses_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBlock_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkConstants_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytesIntrinsic_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytesIntrinsic_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytesIntrinsic_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytesIntrinsic_of_ordered [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytesIntrinsic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_of_ordered [propext, Classical.choice, Quot.sound]

/-- info: Ix.Ixon.BlockOrder.refine_ok_iff : ∀ (block : Ix.Ixon.BlockOrder.Block) (comparison fuel : Nat)
  (initial result : Ix.Ixon.BlockOrder.Classes),
  Ix.Ixon.BlockOrder.refine block comparison fuel initial = Except.ok result ↔
    ∃ rounds, rounds ≤ fuel ∧ Ix.Ixon.BlockOrder.Refinement block comparison rounds initial result -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.refine_ok_iff

/-- info: @Ix.Ixon.BlockOrder.refine_fixedPoint : ∀ {block : Ix.Ixon.BlockOrder.Block} {comparison fuel : Nat}
  {initial result : Ix.Ixon.BlockOrder.Classes},
  Ix.Ixon.BlockOrder.refine block comparison fuel initial = Except.ok result →
    Ix.Ixon.BlockOrder.refineStep block comparison result = Except.ok result -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.refine_fixedPoint

/-- info: Ix.Ixon.BlockOrder.checkBlock_ok_iff : ∀ (limits : Ix.Ixon.BlockOrder.Limits) (owner : Address) (source : Ixon.Constant)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.BlockOrder.checkBlock limits owner source blobs = Except.ok () ↔
    Ix.Ixon.BlockOrder.Canonical limits owner source blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBlock_ok_iff

/-- info: Ix.Ixon.BlockOrder.checkBytesIntrinsic_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (orderLimits : Ix.Ixon.BlockOrder.Limits) (cfg : Ix.Kernel.Config) (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs) (family : Option (Ix.Kernel.ConstRef Address)) (env : Ix.Kernel.Env Address),
  Ix.Ixon.BlockOrder.checkBytesIntrinsic maxProjections limits orderLimits cfg records blobs family = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Ixon.BlockOrder.Ordered orderLimits blobs input ∧
              Ix.Kernel.checkEnv cfg output blobs family = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytesIntrinsic_ok_iff

/-- info: @Ix.Ixon.BlockOrder.checkBytesIntrinsic_of_ordered : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {orderLimits : Ix.Ixon.BlockOrder.Limits} {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records}
  {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records input →
      Ix.Ixon.Projection.Expanded maxProjections input output →
        Ix.Ixon.BlockOrder.Ordered orderLimits blobs input →
          Ix.Ixon.BlockOrder.checkBytesIntrinsic maxProjections limits orderLimits cfg records blobs family =
            Except.mapError (fun error => Ix.Ixon.BlockOrder.Error.admission (Ix.Ixon.Admission.Error.kernel error))
              (Ix.Kernel.checkEnv cfg output blobs family) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytesIntrinsic_of_ordered

/-- info: Ix.Ixon.BlockOrder.checkBytesIntrinsic_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.Model.SetTheory V]
  {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits} {orderLimits : Ix.Ixon.BlockOrder.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.BlockOrder.checkBytesIntrinsic maxProjections limits orderLimits cfg records blobs family = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytesIntrinsic_has_model

/-! ### The certified entry's theorems (L5) -/

/-- info: Ix.Ixon.BlockOrder.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (orderLimits : Ix.Ixon.BlockOrder.Limits) (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env),
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Ixon.BlockOrder.Ordered orderLimits blobs input ∧
              Ix.Ixon.ConLecheAdmission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_ok_iff

/-- info: @Ix.Ixon.BlockOrder.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    ∃ input output,
      Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
        Ix.Ixon.Projection.Expanded maxProjections input output ∧
          Ix.Ixon.BlockOrder.Ordered orderLimits blobs input ∧
            ∃ pins pre natPins,
              Ix.Kernel.ConLecheReader.defaultPins = Except.ok pins ∧
                Ix.Kernel.ConLecheReader.builtinPrelude = Except.ok pre ∧
                  Ix.Kernel.ConLecheReader.builtinNatOpPins = Except.ok natPins ∧
                    Ix.Ixon.ConLecheAdmission.Installed pins pre natPins output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_reading

/-- info: Ix.Ixon.BlockOrder.checkBytes_has_model : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint}
  {env : ConLeche.Env},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    Nonempty (ConLeche.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_has_model

/-- info: Ix.Ixon.BlockOrder.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [ConLeche.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint}
  {env : ConLeche.Env},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    ∀ (ci : ConLeche.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = ConLeche.Expr.const ConLeche.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_no_proof_of_False

/-- info: @Ix.Ixon.BlockOrder.checkBytes_of_ordered : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records}
  {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records input →
      Ix.Ixon.Projection.Expanded maxProjections input output →
        Ix.Ixon.BlockOrder.Ordered orderLimits blobs input →
          Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint =
            Except.mapError Ix.Ixon.BlockOrder.CheckError.checker
              (Ix.Ixon.ConLecheAdmission.checkConstants output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_of_ordered

/-- info: Additional block-order externs: [String.compare, UInt64.decLe, UInt64.add, Array.uget]
---
info: Additional block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.intrinsicOperations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.BlockOrder.Audit.intrinsicOperations
  Lean.logInfo m!"Additional block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"

/- The certified entry's order check reaches no extern or unsafe primitive
beyond the certified projection entry's (con-leche's closure already uses
`String.compare`, the `UInt64` operations and `Array.uget`). -/
/-- info: Additional certified block-order externs: []
---
info: Additional certified block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.BlockOrder.Audit.operations
  Lean.logInfo m!"Additional certified block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
