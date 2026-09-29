/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify
import Ix.Kernel.Audit.Axioms
import Ix.Kernel.Audit.Imports
import Ix.Kernel.Audit.Runtime

/-! The production codec and structural wire domain depend on Lean core only.
The retained proofs additionally use Lean/Std proof tooling, including checked
bit-vector decision proofs. Neither boundary imports the host or Lean4Lean. -/

namespace Ix.Ixon.Audit

def operations : Array Lean.Name :=
  #[``_root_.Ixon.serUniv, ``_root_.Ixon.deUniv,
    ``_root_.Ixon.serExpr, ``_root_.Ixon.deExpr,
    ``_root_.Ixon.serConstant, ``_root_.Ixon.deConstant, ``_root_.Ixon.deConstantExact,
    ``_root_.Ixon.Bounded.deUniv, ``_root_.Ixon.Bounded.deConstant,
    ``_root_.Ixon.Canonical.deConstant]

def dataImports : Array Lean.Name :=
  #[`Init, `Ix.Address.Core, `Ix.Ixon.Types, `Ix.Ixon.Codec, `Ix.Ixon.Wire,
    `Ix.Ixon.Bounded, `Ix.Ixon.WireCheck, `Ix.Ixon.Canonical]

def proofImports : Array Lean.Name := dataImports ++ #[`Lean, `Std, `Ix.Ixon.Verify]

end Ix.Ixon.Audit

#guard_kernel_axioms Ix.Ixon.Verify.deUniv_serUniv [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.deExpr_serExpr [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.deConstant_serConstant [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.deConstantExact_serConstant [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.deConstantExact_noTrailing [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.runGetExact_complete [propext]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedUniverse.getUnivFuel_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedUniverse.getUnivFuel_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedUniverse.deUniv_serUniv [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedUniverse.deUniv_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedUniverse.deUniv_noTrailing [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedUniverse.deUniv_wireWF [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Codec.Ixon.Constant.getConstant_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedConstant.getUnivArray_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedConstant.getUnivArray_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedConstant.deConstant_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedConstant.deConstant_serConstant [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.BoundedConstant.deConstant_noTrailing [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getTag0Sizes_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getArray_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getArray_error_prefix [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getArray_error_work [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getArray_tooMany [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getExprFuel_bound [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.getExpr_bound [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ReaderBounds.deExpr_resource_bound [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ConstantBounds.getConstant_bound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ConstantBounds.deConstantExact_resource_bound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.ConstantBounds.boundedConstant_resource_bound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.WireCheck.validConstant_iff [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Canonical.deConstant_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Canonical.deConstant_serConstant [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Canonical.deConstant_noTrailing [propext, Classical.choice, Quot.sound]

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Codec, `Ix.Ixon.Wire,
  `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Size, `Ix.Ixon.WireCheck,
  `Ix.Ixon.Canonical] Ix.Ixon.Audit.dataImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Verify] Ix.Ixon.Audit.proofImports

/- The production codec reaches Init's byte-array access/copy/push, UInt8/UInt64
bit operations and conversions, array iteration, numeric formatting for
errors, and the inherited panic primitive in checked indexing helpers.
Canonical re-encoding additionally uses Init's `ByteArray.decEq`, backed by
`lean_sarray_dec_eq`. These were measured before freezing; no project FFI or
hash is reached. -/
/-- info: runtime closure of [Ixon.serUniv, Ixon.deUniv, Ixon.serExpr, Ixon.deExpr,
Ixon.serConstant, Ixon.deConstant, Ixon.deConstantExact, Ixon.Bounded.deUniv,
Ixon.Bounded.deConstant, Ixon.Canonical.deConstant]: 331 compiled functions;
inherited externs 52, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.Audit.operations #[`Init, `Std]

/-- info: Ix.Ixon.Verify.deUniv_serUniv : ∀ (u : Ixon.Univ),
  Ix.Ixon.Verify.UnivWireWF u → Ixon.deUniv (Ixon.serUniv u) = Except.ok u -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.deUniv_serUniv

/-- info: Ix.Ixon.Verify.deExpr_serExpr : ∀ (expr : Ixon.Expr),
  Ix.Ixon.Verify.ExprWireWF expr → Ixon.deExpr (Ixon.serExpr expr) = Except.ok expr -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.deExpr_serExpr

/-- info: Ix.Ixon.Verify.deConstant_serConstant : ∀ (constant : Ixon.Constant),
  Ix.Ixon.Verify.ConstantWireWF constant → Ixon.deConstant (Ixon.serConstant constant) = Except.ok constant -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.deConstant_serConstant

/-- info: Ix.Ixon.Verify.deConstantExact_serConstant : ∀ (constant : Ixon.Constant),
  constant.wireWF → Ixon.deConstantExact (Ixon.serConstant constant) = Except.ok constant -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.deConstantExact_serConstant

/-- info: Ix.Ixon.Verify.deConstantExact_noTrailing : ∀ (constant : Ixon.Constant),
  constant.wireWF →
    ∀ (suffix : ByteArray), suffix.size ≠ 0 → (Ixon.deConstantExact (Ixon.serConstant constant ++ suffix)).isOk = false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.deConstantExact_noTrailing

/-- info: Ix.Ixon.Verify.BoundedUniverse.deUniv_serUniv : ∀ (u : Ixon.Univ),
  u.wireWF → ∀ (maxBytes maxNodes : Nat),
  (Ixon.serUniv u).size ≤ maxBytes → u.nodeCount ≤ maxNodes →
  Ixon.Bounded.deUniv maxBytes maxNodes (Ixon.serUniv u) = Except.ok u -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.BoundedUniverse.deUniv_serUniv

/-- info: Ix.Ixon.Verify.BoundedUniverse.deUniv_spec : ∀ (maxBytes maxNodes : Nat)
  (bytes : ByteArray) (u : Ixon.Univ),
  Ixon.Bounded.deUniv maxBytes maxNodes bytes = Except.ok u →
  bytes.size ≤ maxBytes ∧ u.nodeCount ≤ maxNodes ∧ Ixon.deUniv bytes = Except.ok u -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.BoundedUniverse.deUniv_spec

/-- info: Ix.Ixon.Verify.BoundedUniverse.deUniv_wireWF : ∀ (maxBytes maxNodes : Nat)
  (bytes : ByteArray) (u : Ixon.Univ),
  maxNodes < UInt64.size → Ixon.Bounded.deUniv maxBytes maxNodes bytes = Except.ok u → u.wireWF -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.BoundedUniverse.deUniv_wireWF

/-- info: Ix.Ixon.Verify.BoundedConstant.deConstant_ok_iff : ∀ (maxBytes maxUnivNodes : Nat)
  (bytes : ByteArray) (constant : Ixon.Constant),
  Ixon.Bounded.deConstant maxBytes maxUnivNodes bytes = Except.ok constant ↔
  bytes.size ≤ maxBytes ∧ Ixon.Bounded.univNodes constant.univs ≤ maxUnivNodes ∧
  Ixon.deConstantExact bytes = Except.ok constant -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.BoundedConstant.deConstant_ok_iff

/-- info: Ix.Ixon.Verify.WireCheck.validConstant_iff : ∀ (constant : Ixon.Constant),
  Ixon.WireCheck.validConstant constant = true ↔ constant.wireWF -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.WireCheck.validConstant_iff

/-- info: Ix.Ixon.Verify.Canonical.deConstant_ok_iff : ∀ (maxBytes maxUnivNodes : Nat)
  (bytes : ByteArray) (constant : Ixon.Constant),
  Ixon.Canonical.deConstant maxBytes maxUnivNodes bytes = Except.ok constant ↔
  constant.wireWF ∧ Ixon.serConstant constant = bytes ∧ bytes.size ≤ maxBytes ∧
  Ixon.Bounded.univNodes constant.univs ≤ maxUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Canonical.deConstant_ok_iff

/- Freeze both the resource predicates and their public contracts. Successful
reads need only a valid starting cursor, not a canonicality premise. -/
/-- info: def Ix.Ixon.Verify.ReaderBounds.ReaderBound : {α : Type} → Ixon.GetM α → (α → Nat) → Prop :=
fun {α} reader units =>
  ∀ (start finish : Ixon.GetState) (value : α),
    start.idx ≤ start.bytes.size →
      reader start = EStateM.Result.ok value finish → Ix.Ixon.Verify.ReaderBounds.Span start finish (units value) -/
#guard_msgs (whitespace := lax) in
#print Ix.Ixon.Verify.ReaderBounds.ReaderBound

/-- info: @Ix.Ixon.Verify.ReaderBounds.Span.mk : ∀ {start finish : Ixon.GetState} {units : Nat},
  finish.bytes = start.bytes →
    start.idx ≤ finish.idx →
      finish.idx ≤ start.bytes.size →
        units + 2 * start.idx ≤ 2 * finish.idx → Ix.Ixon.Verify.ReaderBounds.Span start finish units -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ReaderBounds.Span.mk

/-- info: @Ix.Ixon.Verify.ReaderBounds.getArray_error_work : ∀ {α : Type} (reader : Ixon.GetM α),
  (Ix.Ixon.Verify.ReaderBounds.ReaderBound reader fun x => 2) →
    ∀ (count : Nat) (start finish : Ixon.GetState) (reason : String),
      start.idx ≤ start.bytes.size →
        Ixon.getArray reader count start = EStateM.Result.error reason finish →
          ∃ parsed values middle,
            parsed < count ∧
              parsed ≤ start.bytes.size - start.idx ∧
                values.size = parsed ∧
                  Ixon.getArray reader parsed start = EStateM.Result.ok values middle ∧
                    reader middle = EStateM.Result.error reason finish -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ReaderBounds.getArray_error_work

/-- info: @Ix.Ixon.Verify.ReaderBounds.getArray_tooMany : ∀ {α : Type} (reader : Ixon.GetM α),
  (Ix.Ixon.Verify.ReaderBounds.ReaderBound reader fun x => 2) →
    ∀ (count : Nat) (start : Ixon.GetState),
      start.idx ≤ start.bytes.size →
        start.bytes.size - start.idx < count →
          ∀ (values : Array α) (finish : Ixon.GetState),
            Ixon.getArray reader count start ≠ EStateM.Result.ok values finish -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ReaderBounds.getArray_tooMany

/-- info: Ix.Ixon.Verify.ReaderBounds.getExprFuel_bound : ∀ (fuel : Nat),
  Ix.Ixon.Verify.ReaderBounds.ReaderBound (Ixon.getExprFuel fuel) fun expr => expr.resourceSize + 1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ReaderBounds.getExprFuel_bound

/-- info: Ix.Ixon.Verify.ReaderBounds.deExpr_resource_bound : ∀ (bytes : ByteArray) (value : Ixon.Expr),
  Ixon.deExpr bytes = Except.ok value → value.resourceSize + 1 ≤ 2 * bytes.size -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ReaderBounds.deExpr_resource_bound

/-- info: Ix.Ixon.Verify.ConstantBounds.getConstant_bound : Ix.Ixon.Verify.ReaderBounds.ReaderBound Ixon.getConstant
  Ixon.Constant.resourceSize -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ConstantBounds.getConstant_bound

/-- info: Ix.Ixon.Verify.ConstantBounds.deConstantExact_resource_bound : ∀ (bytes : ByteArray) (value : Ixon.Constant),
  Ixon.deConstantExact bytes = Except.ok value → value.resourceSize ≤ 2 * bytes.size -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ConstantBounds.deConstantExact_resource_bound

/-- info: Ix.Ixon.Verify.ConstantBounds.boundedConstant_resource_bound : ∀ (maxBytes maxUnivNodes : Nat)
  (bytes : ByteArray) (value : Ixon.Constant),
  Ixon.Bounded.deConstant maxBytes maxUnivNodes bytes = Except.ok value →
    value.resourceSize + Ixon.Bounded.univNodes value.univs ≤ 2 * maxBytes + maxUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.ConstantBounds.boundedConstant_resource_bound
