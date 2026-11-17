import IxVMRefinement.Binding.OpRefine
import IxVMRefinement.StatementRel.BoolInhabit
import IxC.Kernel.Semantics.Bridge.DeclRun
import IxVMRefinement.RoleOps.Inhabit

/-! # An operation's check facts at a concrete environment: `Nat.pred`

`natPred_opChecked`: **the operations interface (`RoleOps.OpChecked`) holds for `Nat.pred` at
the pinned basis environment**, for the value `fun n => Nat.rec (motive := fun _ => Nat) Nat.zero
(fun m _ => m) n` at the type `Nat → Nat`. IxC's executable check of the definition at the
operation's key (its run at fuel 16, with one definitional evidence entry per recurrence) is
evaluated; the bridge `declDefnRun_of` turns it into the kernel's run record and the operations
lane's converse (`RoleOps.structOp_of_verifiedRun`) into the prefix half and the check half of
the interface. The environment the check installs is the basis environment with the operation
stored (`RoleOps.installed`).

What this shows: the check facts `roleOp_step` and `op_step` take for a structural operation are
satisfiable together with their prefix at a concrete environment, by a value of the standard
structural recursion. What it does not show: the boundary invariant below the operation's group
(group 7) at an environment that also stores `Bool` and its records, which `roleOp_step` takes
as well (the `Bool` group's step is proved modulo two hypotheses, `Binding.bool_step_instance`).
-/

namespace IxVM.Refinement.Binding.OpInhabit

open Ix.Kernel
open IxVM.Refinement.TableInhabit (basisEnv)

/-- Binder data for the declared terms (the check writes its own). -/
def bm : BinderMeta := { pw := .never }

/-- `Nat`. -/
def natTy : Expr .anon := .const natName []

/-- `Nat → Nat`. -/
def predTy : Expr .anon := .forallE natTy natTy bm

/-- `fun n => Nat.rec (motive := fun _ => Nat) Nat.zero (fun m _ => m) n`. -/
def predVal : Expr .anon :=
  .lam natTy
    (.app (.app (.app (.app (.const natRecName [.succ .zero]) (.lam natTy natTy bm))
      (.const natZeroName [])) (.lam natTy (.lam natTy (.bvar 1) bm) bm)) (.bvar 0)) bm

/-- The declared header at `Nat.pred`'s key. -/
def predCv : ConstantVal .anon := ⟨.role .natPred, [], predTy⟩

/-- One definitional evidence entry per recurrence. -/
def predEv : Evidences .anon := [(.natPred, [.defeq, .defeq])]

/-- The reducibility hint. -/
def predHint : ReducibilityHint := .regular 1

/-- IxC's executable check of the definition at the basis environment, at fuel 16. -/
def predRun :=
  checkDecl .verified (fueledOps .verified 16) predEv basisEnv (.defnDecl predCv predVal predHint)

/-- The environment the check installs. -/
def predEnv : Env .anon := BoolInhabit.okOr predRun basisEnv

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **IxC's check of `Nat.pred` passes at the basis environment** (evaluated). -/
theorem predRun_ok : predRun.toBool = true := by
  decide +kernel

theorem predRun_eq : predRun = .ok predEnv :=
  BoolInhabit.ok_okOr predRun_ok

/-- **The kernel's run record of the definition.** -/
theorem predDeclRun :
    Ix.Kernel.Semantics.DeclDefnRun .verified 16 basisEnv predCv predVal predHint predEnv :=
  Ix.Kernel.Semantics.declDefnRun_of predRun_eq

/-- **The operations interface holds for `Nat.pred` at the basis environment**: the
environment the check installs is the basis environment with the operation stored, and the
prefix half and the check half of the interface hold. -/
theorem natPred_opChecked :
    ∃ ty val : Expr .anon, predEnv = RoleOps.installed basisEnv (.role .natPred) ty val predHint ∧
      RoleOps.OpChecked basisEnv (.role .natPred) predTy predVal ty val := by
  have hc : (Key.role .natPred : Key .anon) ∈ natOpNames := by decide
  obtain ⟨ty, val, -, henv, hpre, hk⟩ :=
    IxVM.Refinement.RoleOps.structOp_of_verifiedRun (cv := predCv) hc predDeclRun
  exact ⟨ty, val, henv, .struct hc hpre hk⟩

end IxVM.Refinement.Binding.OpInhabit
