import Ix.Ixon.BlockOrder.Theorems
import Ix.Ixon.Projection.Audit

namespace Ixon.BlockOrder.Audit

/-- The recursor-block order check. -/
def operations : Array Lean.Name := #[``checkRecord]

def allowedData (name : Lean.Name) : Bool :=
  Projection.Audit.allowedData name || name == `Ix.Ixon.ReduceUniverse || name == `Ix.Ixon.BlockOrder

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Projection.Audit.allowedProof name || name == `Ix.Ixon.BlockOrder.Theorems

end Ixon.BlockOrder.Audit

#guard_msgs (drop info) in
run_cmd Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder] Ixon.BlockOrder.Audit.allowedData

#guard_msgs (drop info) in
run_cmd Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder.Theorems] Ixon.BlockOrder.Audit.allowedProof

#guard !Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrder.Theorems
#guard !Ixon.BlockOrder.Audit.allowedData `Ix.Tc.CanonicalCheck
#guard !Ixon.BlockOrder.Audit.allowedData `Blake3.Rust
#guard !Ixon.BlockOrder.Audit.allowedData `Blake3.C
#guard !Ixon.BlockOrder.Audit.allowedData `Ix.IxonUniv
#guard !Ixon.Projection.Audit.allowedData `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ixon.Audit.dataImports `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrder.Audit

/- Measured before freezing: a block of recursors is checked in motive order
(`checkRecord`, `isRecursor`, `checkMotives`, `recursorMotive`), which reuses
the reader's `stripAll` and `appHead` (`Reader.analyseRecursor`). Every other
block is stored in its source's order, which is admissible, so the
structural order check of those blocks, and the certified entry that ran it
before the checker, are gone. -/
/-- info: runtime closure of [Ixon.BlockOrder.checkRecord]: 27 compiled functions; inherited externs 13, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.BlockOrder.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ixon.BlockOrder.recursorMotive_of_analyse [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.motivesFrom_cons [propext, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkMotives_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkMotiveOrder_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkRecord_ok_iff [propext, Classical.choice, Quot.sound]

/- Recursor blocks in motive order: a block of recursors must be
`MotiveOrdered` (member `j` eliminates motive `j`, read off its type as the
reader reads it, `recursorMotive_of_analyse`, and declares one motive per
member); every other record is unconstrained. These freeze what
`OrderedRecord` means. -/
/-- info: def Ixon.BlockOrder.OrderedRecord : Address × Ixon.Constant → Prop :=
fun pair =>
  match pair.snd.info with
  | Ixon.ConstantInfo.muts members =>
    if members.all Ixon.BlockOrder.isRecursor = true then Ixon.BlockOrder.MotiveOrdered pair.snd members else True
  | x => True -/
#guard_msgs (whitespace := lax) in
#print Ixon.BlockOrder.OrderedRecord

/-- info: def Ixon.BlockOrder.MotivesFrom : Ixon.Constant → Nat → Nat → List Ixon.MutConst → Prop :=
fun source size start members =>
  ∀ (j : Nat) (h : j < members.length),
    ∃ r,
      members[j] = Ixon.MutConst.recr r ∧
        r.motives.toNat = size ∧ Ixon.BlockOrder.recursorMotive source r = some (start + j) -/
#guard_msgs (whitespace := lax) in
#print Ixon.BlockOrder.MotivesFrom

/-- info: Ixon.BlockOrder.checkRecord_ok_iff : ∀ (owner : Address) (source : Ixon.Constant),
  Ixon.BlockOrder.checkRecord owner source = Except.ok () ↔ Ixon.BlockOrder.OrderedRecord (owner, source) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkRecord_ok_iff

/- The order check reaches no extern and no unsafe primitive beyond the
certified projection entry's. -/
/-- info: Additional block-order externs: []
---
info: Additional block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ixon.Projection.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ixon.BlockOrder.Audit.operations
  Lean.logInfo m!"Additional block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
