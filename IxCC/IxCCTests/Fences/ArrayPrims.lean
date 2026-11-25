import IxCC.Sem.ValModel
import IxCC.Anf.Proof.Rel.ValModel
import IxCC.Anf.Proof.Defun.Narrow
import IxCC.Anf.Proof.Defun.ValModel
import IxCC.Anf.Proof.Convert.ValModel
import IxCC.Fir.Proof.Lowering

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

/-! The array value encoding below erasure (decision D1: a constructor value under the reserved
key `Key.CtorKey.arr`): every Anf relation of the `Base` shape, closure conversion's relation and
Lam-to-Anf conversion's relation respect the value models (`Sem.ModelRel`), and the
closure-narrowing proof's array scrutinee case. -/

/-- info: 'IxCC.Anf.Rel.Pw.toForall2' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Pw.toForall2

/-- info: 'IxCC.Anf.Rel.Pw.ofForall2' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Pw.ofForall2

/-- info: 'IxCC.Anf.Rel.Base.modelRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Base.modelRel

/-- info: 'IxCC.Anf.Defun.Narrow.Proof.evalAlts_allClo_arr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Narrow.Proof.evalAlts_allClo_arr

/-- info: 'IxCC.Anf.Defun.Proof.DVs.toForall2' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.DVs.toForall2

/-- info: 'IxCC.Anf.Defun.Proof.DVs.ofForall2' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.DVs.ofForall2

/-- info: 'IxCC.Anf.Defun.Proof.dv_modelRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dv_modelRel

/-- info: 'IxCC.Anf.Convert.Proof.VRs.toForall2' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Convert.Proof.VRs.toForall2

/-- info: 'IxCC.Anf.Convert.Proof.VRs.ofForall2' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Convert.Proof.VRs.ofForall2

/-- info: 'IxCC.Anf.Convert.Proof.CloR.lam_clos' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Convert.Proof.CloR.lam_clos

/-- info: 'IxCC.Anf.Convert.Proof.vr_modelRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Convert.Proof.vr_modelRel

/-! The Anf → Fir lowering declines array primitives (`fir.arrays`) until stage B. -/

/-- info: 'IxCC.Fir.Proof.exp_prim_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.exp_prim_arr
