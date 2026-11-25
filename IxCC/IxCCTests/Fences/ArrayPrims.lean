import IxCC.Sem.ValModel

/-! Required axiom fences for the array primitives on the certified pipeline
(`plans/ONE-PIPELINE.md`, lane `prims-core`): the operations' meaning over a value model
(`IxCC.Src.ArrOp`, `IxCC/Src/ArrayOp.lean`), their outcomes, and the one parametricity theorem
every pass uses (`IxCC/Sem/ValModel.lean`). Expected messages are preserved verbatim. -/

/-- info: 'IxCC.Sem.Forall2.replicate' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Forall2.replicate

/-- info: 'IxCC.Sem.Forall2.set' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.Forall2.set

/-- info: 'IxCC.Sem.Forall2.dropLast' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Forall2.dropLast

/-- info: 'IxCC.Sem.Forall2.get_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Forall2.get_none

/-- info: 'IxCC.Sem.Forall2.extractList' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Forall2.extractList

/-- info: 'IxCC.Sem.Forall2.copySliceList' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Sem.Forall2.copySliceList

/-- info: 'IxCC.Sem.SimUpTo.of_refines' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.SimUpTo.of_refines

/-- info: 'IxCC.Src.ArrOp.eval_arity' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_arity

/-- info: 'IxCC.Src.ArrOp.eval_ne_timeout' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_ne_timeout

/-- info: 'IxCC.Src.ArrOp.eval_ne_resource' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_ne_resource

/-- info: 'IxCC.Src.ArrOp.eval_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_cases

/-- info: 'IxCC.Src.ArrOp.eval_trap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_trap

/-- info: 'IxCC.Src.ArrOp.eval_pure' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_pure

/-- info: 'IxCC.Src.ArrOp.eval_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.eval_refines

/-- info: 'IxCC.Src.ArrOp.sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.sim

/-- info: 'IxCC.Src.ArrOp.parametric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.parametric

/-- info: 'IxCC.Src.ArrOp.neverResource' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArrOp.neverResource
