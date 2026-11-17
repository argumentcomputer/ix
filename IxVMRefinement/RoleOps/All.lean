import IxVMRefinement.RoleOps.Install
import IxVMRefinement.RoleOps.Companions

/-! # The step of an operation, for all fifteen

`OpChecked env c ty₀ val₀ ty val` is the check of either family with its prefix. `op_step` is the
one statement a fold uses at the key of any of the fifteen operations: the declared definition
is installed, the fold invariant is kept in every set theory, `OpsPinned` is kept (so a later
operation finds this one stored as pinned), and every stored key stays stored. `op_companion`
gives the stored shapes the checker's native arithmetic reads of the operation.
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KExpr KKey)
open IxVM.Refinement.Decl (FoldInv FullDeclInv)
open Ix.Kernel (Env Expr ReducibilityHint natOpNames natDivModNames)

set_option linter.unusedVariables false

universe u

/-- **An operation checked, with its prefix**: a structural operation with `OpPrefix` and
`StructOpCheck`, or a well-founded one with `WfPrefix` and `WfOpCheck`. -/
inductive OpChecked (env : Env .anon) (c : KKey) (ty₀ val₀ ty val : KExpr) : Prop where
  | struct (hc : c ∈ natOpNames) (hp : OpPrefix env c)
      (hk : StructOpCheck env c ty₀ val₀ ty val)
  | wf (hc : c ∈ natDivModNames) (hp : WfPrefix env c) (hk : WfOpCheck env c ty₀ val₀ ty val)

theorem OpChecked.mem {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (h : OpChecked env c ty₀ val₀ ty val) : c ∈ opNames := by
  cases h with
  | struct hc _ _ => exact mem_opNames.mpr (Or.inl hc)
  | wf hc _ _ => exact mem_opNames.mpr (Or.inr hc)

theorem OpChecked.opPrefix {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (h : OpChecked env c ty₀ val₀ ty val) : OpPrefix env c := by
  cases h with
  | struct _ hp _ => exact hp
  | wf _ hp _ => exact hp.op

theorem OpChecked.front {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (h : OpChecked env c ty₀ val₀ ty val) : OpFront env ty₀ val₀ ty val := by
  cases h with
  | struct _ _ hk => exact hk.front
  | wf _ _ hk => exact hk.front

theorem OpChecked.tyShape {env : Env .anon} {c : KKey} {ty₀ val₀ ty val : KExpr}
    (h : OpChecked env c ty₀ val₀ ty val) : OpTyShape c ty := by
  cases h with
  | struct _ _ hk => exact hk.tyShape
  | wf _ _ hk => exact hk.tyShape

/-- **The step of an operation.** From its check and its prefix, for any of the fifteen
operations: the declared definition is installed at the operation's key, the fold invariant is
kept in every set theory, `OpsPinned` is kept, and every stored key stays stored. `tyD`, `valD`
are the declared type and value, `ty`, `val` the stored ones. -/
theorem op_step {env : Env .anon} {c : KKey} {ty₀ val₀ ty val tyD valD : KExpr}
    (hint : ReducibilityHint) (h : OpChecked env c ty₀ val₀ ty val)
    (hty : IxVM.Consistency.Annotates ty tyD) (hval : IxVM.Consistency.Annotates val valD) :
    IxVM.Consistency.InstallStep env (.defnDecl ⟨c, [], tyD⟩ valD hint)
        (installed env c ty val hint) ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FoldInv V env → FoldInv V (installed env c ty val hint)) ∧
      (∀ (V : Type u) [Ix.Kernel.SetTheory V],
        FullDeclInv V env → FullDeclInv V (installed env c ty val hint)) ∧
      (OpsPinned env → OpsPinned (installed env c ty val hint)) ∧
      ∀ k : KKey, (env.find? k).isSome = true →
        ((installed env c ty val hint).find? k).isSome = true := by
  have hco := h.mem
  have hpin : OpsPinned env → OpsPinned (installed env c ty val hint) := fun hp =>
    hp.install_op h.opPrefix (isBaseKey_of_mem_opNames hco) h.tyShape val hint
  have hmono := (op_cleanInstall (hint := hint) hco h.opPrefix.fresh hty hval).monoSome
  cases h with
  | struct hc hp hk =>
    obtain ⟨h1, h2, h3⟩ := structOp_step hint hc hp hk hty hval
    exact ⟨h1, h2, h3, hpin, hmono⟩
  | wf hc hp hk =>
    obtain ⟨h1, h2, h3⟩ := wfOp_step hint hc hp hk hty hval
    exact ⟨h1, h2, h3, hpin, hmono⟩

/-- **What the checker's native arithmetic reads of the operation once it is stored**, for any
of the fifteen operations. -/
theorem op_companion {env : Env .anon} {r : Ix.Kernel.Role} {ty₀ val₀ ty val : KExpr}
    (hint : ReducibilityHint) (h : OpChecked env (.role r) ty₀ val₀ ty val) :
    OpCompanion (installed env (.role r) ty val hint) r :=
  opCompanion_installed h.mem h.opPrefix h.front h.tyShape hint

/-- The operation keys are the role keys of the fifteen operation roles. -/
theorem opNames_eq :
    opNames = [.role .natPred, .role .natAdd, .role .natSub, .role .natMul, .role .natPow,
      .role .natBeq, .role .natBle, .role .natDiv, .role .natMod, .role .natGcd,
      .role .natLand, .role .natLor, .role .natXor, .role .natShiftLeft,
      .role .natShiftRight] := rfl

end IxVM.Refinement.RoleOps
