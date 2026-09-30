/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.BlockOrderProofs
import Ix.Ixon.ProjectionAudit

namespace Ix.Ixon.BlockOrder.Audit

def operations : Array Lean.Name := #[``checkBytes, ``canonicalClasses, ``compareExpr]

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

/-- info: runtime closure of [Ix.Ixon.BlockOrder.checkBytes,
Ix.Ixon.BlockOrder.canonicalClasses, Ix.Ixon.BlockOrder.compareExpr]: 2004 compiled functions;
inherited externs 85, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.BlockOrder.Audit.operations #[`Init, `Std]

#guard_kernel_axioms Ix.Ixon.BlockOrder.Refinement.positive [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.Refinement.fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.canonicalClasses_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBlock_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkConstants_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_of_ordered [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes [propext, Classical.choice, Quot.sound]

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

/-- info: Ix.Ixon.BlockOrder.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (orderLimits : Ix.Ixon.BlockOrder.Limits) (cfg : Ix.Kernel.Config) (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs) (family : Option (Ix.Kernel.ConstRef Address)) (env : Ix.Kernel.Env Address),
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits cfg records blobs family = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Ixon.BlockOrder.Ordered orderLimits blobs input ∧
              Ix.Kernel.checkEnv cfg output blobs family = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_ok_iff

/-- info: @Ix.Ixon.BlockOrder.checkBytes_of_ordered : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {orderLimits : Ix.Ixon.BlockOrder.Limits} {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records}
  {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records input →
      Ix.Ixon.Projection.Expanded maxProjections input output →
        Ix.Ixon.BlockOrder.Ordered orderLimits blobs input →
          Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits cfg records blobs family =
            Except.mapError (fun error => Ix.Ixon.BlockOrder.Error.admission (Ix.Ixon.Admission.Error.kernel error))
              (Ix.Kernel.checkEnv cfg output blobs family) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_of_ordered

/-- info: Ix.Ixon.BlockOrder.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.Model.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {orderLimits : Ix.Ixon.BlockOrder.Limits} {cfg : Ix.Kernel.Config}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits cfg records blobs family = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_has_model

/-- info: Additional block-order externs: [String.compare, UInt64.decLe, UInt64.add, Array.uget]
---
info: Additional block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.BlockOrder.Audit.operations
  Lean.logInfo m!"Additional block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
