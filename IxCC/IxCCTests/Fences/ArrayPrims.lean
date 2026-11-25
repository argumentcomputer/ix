import IxCC.Sem.ValModel
import IxCC.Anf.Proof.Defun.Narrow
import IxCC.Anf.Proof.Defun.ValModel
import IxCC.Anf.Proof.Convert.ValModel
import IxCC.Fir.Proof.Lowering
import IxCC.Anf.Props
import IxCC.Lam.Props
import IxCC.Fir.Proof.ArrFree
import IxCC.Own.Proof.Immortal
import IxCC.Own.Plain.Proof.Owned.PrimStep
import IxCC.Cfg.Proof.Sim

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

/-! The Anf → Fir lowering declines array primitives (`fir.arrays`); the immortal route that
lowering feeds is to be retired (design D9), so array primitives reach only the RC route. -/

/-- info: 'IxCC.Fir.Proof.exp_prim_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.exp_prim_arr

/-! The Lam and Anf evaluators give the array primitives their meaning (`Src.ArrOp.eval` at the
level's value model) in `primResult`. -/

/-- info: 'IxCC.Lam.Prim.isArr_eq_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Prim.isArr_eq_true

/-- info: 'IxCC.Lam.Prim.mayTrap_of_not_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Prim.mayTrap_of_not_arr

/-- info: 'IxCC.Lam.arrResult_of_not_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.arrResult_of_not_arr

/-- info: 'IxCC.Lam.primResult_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.primResult_arr

/-- info: 'IxCC.Anf.arrResult_of_not_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.arrResult_of_not_arr

/-- info: 'IxCC.Anf.primResult_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.primResult_arr

/-! Fir's evaluator gives the array primitives their meaning over `Fir.model` (an array is a
constructor value under `Fir.arrInfo n`); a lowered body binds none (`Code.arrFree`). -/

/-- info: 'IxCC.Fir.arrResult_of_not_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.arrResult_of_not_arr

/-- info: 'IxCC.Fir.primResult_arr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.primResult_arr

/-- info: 'IxCC.Fir.Rhs.isArrPrim_eq_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Rhs.isArrPrim_eq_true

/-- info: 'IxCC.Fir.Proof.projections_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.projections_arrFree

/-- info: 'IxCC.Fir.Proof.exp_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.exp_arrFree

/-- info: 'IxCC.Fir.Proof.exps_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.exps_arrFree

/-- info: 'IxCC.Fir.Proof.opt_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.opt_arrFree

/-! Own's code evaluator gives an array-primitive binding its meaning (`arrStep`: the operation
over pending values `pmodel`, then the result placed on the heap); the immortal lock-step
relation covers it (`arrStep_lock`). -/

/-- info: 'IxCC.Own.Rhs.isArrPrim_eq_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rhs.isArrPrim_eq_true

/-- info: 'IxCC.Own.eval_bindArr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.eval_bindArr

/-- info: 'IxCC.Own.Proof.PDen.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.PDen.ext

/-- info: 'IxCC.Own.Proof.PDens.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.PDens.ext

/-- info: 'IxCC.Own.Proof.pdens_of_forall2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.pdens_of_forall2

/-- info: 'IxCC.Own.Proof.forall2_of_pdens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.forall2_of_pdens

/-- info: 'IxCC.Own.Proof.forall2_val_of_dens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.forall2_val_of_dens

/-- info: 'IxCC.Own.Proof.modelRel_pden' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.modelRel_pden

/-- info: 'IxCC.Own.Proof.place_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.place_den

/-- info: 'IxCC.Own.Proof.placeList_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.placeList_den

/-- info: 'IxCC.Own.Proof.arrStep_lock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Proof.arrStep_lock

/-- info: 'IxCC.Own.Proof.isArrPrim_immRhs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Proof.isArrPrim_immRhs

/-- info: 'IxCC.Own.Proof.immCode_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Proof.immCode_arrFree

/-- info: 'IxCC.Own.Proof.immAlts_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Proof.immAlts_arrFree

/-- info: 'IxCC.Own.Proof.immOpt_arrFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Proof.immOpt_arrFree

/-! The ownership checker declines an array primitive (`own.arrays`) until the reference-counted
route gives it a meaning. -/

/-- info: 'IxCC.Own.Plain.bindStep_prim' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.bindStep_prim

/-- info: 'IxCC.Own.Plain.bindStep_isArrPrim' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.bindStep_isArrPrim

/-! Cfg's instructions run `Own.evalRhs`, which has no array case: the immortal-route
simulation carries `Code.arrFree` of every body and join body. -/

/-- info: 'IxCC.Cfg.Proof.JArr.lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Proof.JArr.lookup

/-- info: 'IxCC.Cfg.Proof.JArr.after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Proof.JArr.after
