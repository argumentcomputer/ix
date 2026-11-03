import Ix.Cert.IxVM.RoleSpec
import IxC.Kernel.Admission.Theorems
import Ix.Ixon.Authenticated.Theorems

/-! # Role Admission & Eager Validation Bridge (`IxVM` ↔ `IxC`)

This module bridges `IxVM`'s eager role-table admission and validation
(`validate_binding` and `validate_role` in `Ix/IxVM/Kernel/Claim.lean` and
`Formal Aiur`'s `Claim.aiur`) to `IxC`'s role-table admission
(`Ix.Kernel.Admission.admitBinding`, `Ix.Kernel.Admission.BindingAdmitted`,
`Ix.Kernel.RoleTable.check`) and role specification satisfaction (`Ix.Kernel.Role.spec`).

## Key Results
1. **`ixvm_validate_binding_admitBinding`**: `IxVM`'s binding check (authenticating
   `b.bytes` under `hash`, canonically decoding `RoleTable.ofBytes b.bytes = some t`,
   and checking `t.check = .ok ()`) is equivalent to `Admission.admitBinding hash b = .ok t`
   and `Admission.BindingAdmitted hash b t`.
2. **`ixvm_validate_binding_blake3`**: Instantiated at `Address.blake3Pure` /
   `Address.admissionHash`, `IxVM`'s binding check yields `Admission.BindingAdmitted Address.blake3Pure b t`.
3. **`roleTable_check_properties`**: Any table passing `t.check = .ok ()` satisfies:
   - `t.version = specVersion` (`3`),
   - `(t.bound.toList.map Prod.fst).Nodup` (no duplicate bound roles),
   - `RoleTable.firstRepeat (t.bound.toList.map Prod.snd) = none` (no duplicate bound addresses),
   - `t.wf = Bool.true`.
4. **`validate_anchor_role_bridge`, `validate_axiom_role_bridge`, `validate_eqn_type_role_bridge`,
   `validate_op_eq_entry_bridge`, `validate_eqn_statement_entry_bridge`**: `IxVM`'s DAG-table
   evaluation of a role's anchor type, axiom type, operation/equation type, unconditional
   equations, and certificate/equation statements agrees with `Ix.Kernel.Role.spec r`
   under `substRoleKeysM t.keyOf`.
-/

namespace Ix.Cert.IxVM

open Ix.Kernel
open Ix.Kernel.Admission

/-! ## 1. Functional Model of `IxVM`'s `validate_binding` Header & Structural Checks -/

/-- The structural and cryptographic checks performed by `IxVM`'s `validate_binding`
on the raw binding section `b : Binding`:
1. The binding bytes hash to `b.address` (`hash b.bytes = b.address`).
2. `RoleTable.ofBytes b.bytes` decodes canonically to `some t`.
3. `t.check = .ok ()` (which checks `t.version = specVersion`,
   injectivity of roles and addresses, block closure, dependency closure,
   and evidence kind admissibility). -/
structure IxVMValidateBindingHeader (hash : ByteArray → Address) (b : Binding)
    (t : RoleTable) : Prop where
  authentic : hash b.bytes = b.address
  decoded : RoleTable.ofBytes b.bytes = some t
  checked : t.check = .ok ()

/-- **Equivalence of `IxVMValidateBindingHeader` and `Admission.BindingAdmitted`**:
`IxVM`'s binding header validation holds if and only if `IxC`'s `BindingAdmitted`
predicate holds. -/
theorem ixvm_validate_binding_iff_bindingAdmitted (hash : ByteArray → Address)
    (b : Binding) (t : RoleTable) :
    IxVMValidateBindingHeader hash b t ↔ BindingAdmitted hash b t := by
  constructor
  · rintro ⟨ha, hd, hc⟩
    exact ⟨ha, (RoleTable.ofBytes_eq_some_iff b.bytes t).mp hd, hc⟩
  · rintro ⟨ha, hcan, hc⟩
    exact ⟨ha, (RoleTable.ofBytes_eq_some_iff b.bytes t).mpr hcan, hc⟩

/-- **Soundness of `IxVMValidateBindingHeader` for `Admission.admitBinding`**:
`IxVM`'s binding header validation holds if and only if
`Admission.admitBinding hash b = .ok t`. -/
theorem ixvm_validate_binding_admitBinding (hash : ByteArray → Address)
    (b : Binding) (t : RoleTable) :
    IxVMValidateBindingHeader hash b t ↔ admitBinding hash b = .ok t := by
  rw [ixvm_validate_binding_iff_bindingAdmitted, admitBinding_ok_iff]

/-- **Instantiation at BLAKE3 (`Address.blake3Pure` / `Address.admissionHash`)**:
When `IxVM` authenticates the binding section with BLAKE3, both
`admitBinding Address.blake3Pure b = .ok t` and
`admitBinding Address.admissionHash b = .ok t` hold. -/
theorem ixvm_validate_binding_blake3 (b : Binding) (t : RoleTable)
    (h : IxVMValidateBindingHeader Address.blake3Pure b t) :
    admitBinding Address.blake3Pure b = .ok t ∧
      admitBinding Address.admissionHash b = .ok t ∧
      BindingAdmitted Address.blake3Pure b t := by
  have hadm : admitBinding Address.blake3Pure b = .ok t :=
    (ixvm_validate_binding_admitBinding Address.blake3Pure b t).mp h
  have hba : BindingAdmitted Address.blake3Pure b t :=
    (ixvm_validate_binding_iff_bindingAdmitted Address.blake3Pure b t).mp h
  refine ⟨hadm, ?_, hba⟩
  rw [Address.admissionHash_eq]
  exact hadm

/-! ## 2. Structural Consequences of `RoleTable.check = .ok ()` -/

/-- **Structural Properties of an Admitted `RoleTable`**:
Every `RoleTable` passing `t.check = .ok ()` (and hence every table admitted by
`IxVMValidateBindingHeader`) has:
1. `t.version = specVersion` (`3`),
2. no duplicate bound roles (`(t.bound.toList.map Prod.fst).Nodup`),
3. no duplicate bound addresses (`RoleTable.firstRepeat (t.bound.toList.map Prod.snd) = none`),
4. `t.wf = Bool.true`. -/
theorem roleTable_check_properties {t : RoleTable} (hc : t.check = .ok ()) :
    t.version = specVersion ∧
    (t.bound.toList.map Prod.fst).Nodup ∧
    RoleTable.firstRepeat (t.bound.toList.map Prod.snd) = none ∧
    t.wf = Bool.true := by
  have hwf : t.wf = Bool.true := by unfold RoleTable.wf; rw [hc]; rfl
  unfold RoleTable.check at hc
  dsimp only at hc
  have hver : t.version = specVersion := by
    by_cases hv : (t.version == specVersion) = Bool.true
    · exact beq_iff_eq.mp hv
    · simp [hv, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hc
  have hv : (t.version == specVersion) = Bool.true := beq_iff_eq.mpr hver
  simp only [hv, ↓reduceIte] at hc
  have hrnodup : (t.bound.toList.map Prod.fst).Nodup := by
    by_cases hn : (t.bound.toList.map Prod.fst).Nodup
    · exact hn
    · simp [hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hc
  simp only [hrnodup, ↓reduceIte] at hc
  have hrep : RoleTable.firstRepeat (t.bound.toList.map Prod.snd) = none := by
    cases hr : RoleTable.firstRepeat (t.bound.toList.map Prod.snd) with
    | none => rfl
    | some a =>
      rw [hr] at hc
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hc
  exact ⟨hver, hrnodup, hrep, hwf⟩

/-! ## 3. Functional Specification of `IxVM`'s `validate_role` & Exact `Role.spec` Bridge -/

/-- Whether an expression `actual` matches a resolved specification expression `expected`
up to `PropWhen` binder annotations (`Expr.erasePwEq`). -/
def ExprMatchesSpec (actual expected : Expr .anon) : Bool :=
  actual.erasePwEq expected

theorem ExprMatchesSpec_iff (actual expected : Expr .anon) :
    ExprMatchesSpec actual expected = Bool.true ↔ actual.erasePw = expected.erasePw :=
  Expr.erasePwEq_iff actual expected

/-- **Eager Role Specification Satisfaction (`RoleTypeMatchesDAG`)**:
Given a `RoleTable` `t`, a role's declared type `actualTy` matches its DAG specification
at `(idx, tbl)` when `evalSpecExpr t.keyOf ps tbl fuel idx` evaluates to `some expectedTy`
and `actualTy.erasePw = expectedTy.erasePw`. -/
def RoleTypeMatchesDAG (t : RoleTable) (ps : List LevelParam)
    (idx : Nat) (tbl : SpecExprTable) (fuel : Nat) (actualTy : Expr .anon) : Prop :=
  ∃ expectedTy,
    evalSpecExpr t.keyOf ps tbl fuel idx = some expectedTy ∧
    actualTy.erasePw = expectedTy.erasePw

/-- **Bridge Theorem for Anchor Role Validation (`Spec.anchor`)**:
If `r.spec = .anchor n ty` and `substRoleKeysM t.keyOf ty = some ty'`, then
`buildAnchorType r` produces `(n, idx, tbl)` and `RoleTypeMatchesDAG` at fuel `ty.dagDepth`
holds if and only if `actualTy.erasePw = ty'.erasePw`. -/
theorem validate_anchor_role_bridge (t : RoleTable) (r : Role)
    {n : Nat} {ty ty' : Expr .anon} (actualTy : Expr .anon)
    (hspec : r.spec (md := .anon) = .anchor n ty)
    (hwf : ty.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM t.keyOf ty = some ty') :
    ∃ idx tbl,
      buildAnchorType r = some (n, idx, tbl) ∧
      (RoleTypeMatchesDAG t (List.range n) idx tbl ty.dagDepth actualTy ↔
        actualTy.erasePw = ty'.erasePw) := by
  obtain ⟨idx, tbl, hb, hev⟩ := buildAnchorType_spec t.keyOf r hspec hwf hsub
  refine ⟨idx, tbl, hb, ?_⟩
  unfold RoleTypeMatchesDAG
  rw [hev]
  constructor
  · rintro ⟨e, he, hmatch⟩
    cases he
    exact hmatch
  · intro hmatch
    exact ⟨ty', rfl, hmatch⟩

/-- **Bridge Theorem for Axiom Role Validation (`Spec.axiom`)**:
If `r.spec = .axiom n (some ty)` and `substRoleKeysM t.keyOf ty = some ty'`, then
`buildAxiomType r` produces `(n, idx, tbl)` and `RoleTypeMatchesDAG` at fuel `ty.dagDepth`
holds if and only if `actualTy.erasePw = ty'.erasePw`. -/
theorem validate_axiom_role_bridge (t : RoleTable) (r : Role)
    {n : Nat} {ty ty' : Expr .anon} (actualTy : Expr .anon)
    (hspec : r.spec (md := .anon) = .axiom n (some ty))
    (hwf : ty.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM t.keyOf ty = some ty') :
    ∃ idx tbl,
      buildAxiomType r = some (n, idx, tbl) ∧
      (RoleTypeMatchesDAG t (List.range n) idx tbl ty.dagDepth actualTy ↔
        actualTy.erasePw = ty'.erasePw) := by
  obtain ⟨idx, tbl, hb, hev⟩ := buildAxiomType_spec t.keyOf r hspec hwf hsub
  refine ⟨idx, tbl, hb, ?_⟩
  unfold RoleTypeMatchesDAG
  rw [hev]
  constructor
  · rintro ⟨e, he, hmatch⟩
    cases he
    exact hmatch
  · intro hmatch
    exact ⟨ty', rfl, hmatch⟩

/-- **Bridge Theorem for Operation/Equation Role Type Validation (`Spec.ops` / `Spec.eqns`)**:
If `specEqnTypeOf r = some (n, ty)` and `substRoleKeysM t.keyOf ty = some ty'`, then
`buildEqnType r` produces `(n, idx, tbl)` and `RoleTypeMatchesDAG` at fuel `ty.dagDepth`
holds if and only if `actualTy.erasePw = ty'.erasePw`. -/
theorem validate_eqn_type_role_bridge (t : RoleTable) (r : Role)
    {n : Nat} {ty ty' : Expr .anon} (actualTy : Expr .anon)
    (hspec : specEqnTypeOf r = some (n, ty))
    (hwf : ty.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM t.keyOf ty = some ty') :
    ∃ idx tbl,
      buildEqnType r = some (n, idx, tbl) ∧
      (RoleTypeMatchesDAG t (List.range n) idx tbl ty.dagDepth actualTy ↔
        actualTy.erasePw = ty'.erasePw) := by
  obtain ⟨idx, tbl, hb, hev⟩ := buildEqnType_spec t.keyOf r hspec hwf hsub
  refine ⟨idx, tbl, hb, ?_⟩
  unfold RoleTypeMatchesDAG
  rw [hev]
  constructor
  · rintro ⟨e, he, hmatch⟩
    cases he
    exact hmatch
  · intro hmatch
    exact ⟨ty', rfl, hmatch⟩

/-- **Bridge Theorem for Unconditional Operation/Equation Checking (`buildOpEqs`)**:
Evaluating the `(lIdx, rIdx, tbl₂)` DAG built for any `(n, lhs, rhs)` pair under `t.keyOf`
and checking `isDefEqCore .verified env F 0` on the resulting expressions is equivalent
to checking `isDefEqCore .verified env F 0 lhs' rhs'` on the role-resolved specification
sides `lhs'` and `rhs'`. -/
theorem validate_op_eq_entry_bridge (t : RoleTable) (env : Env .anon) (F : Nat)
    (n : Nat) (lhs rhs lhs' rhs' : Expr .anon)
    (hwfL : lhs.specClosedWF (List.range n) = Bool.true)
    (hwfR : rhs.specClosedWF (List.range n) = Bool.true)
    (hsubL : substRoleKeysM t.keyOf lhs = some lhs')
    (hsubR : substRoleKeysM t.keyOf rhs = some rhs') :
    ∃ lIdx rIdx tbl₁ tbl₂,
      buildSpecExpr (List.range n) lhs {} = some (lIdx, tbl₁) ∧
      buildSpecExpr (List.range n) rhs tbl₁ = some (rIdx, tbl₂) ∧
      ((∃ el er,
          evalSpecExpr t.keyOf (List.range n) tbl₂ (Nat.max lhs.dagDepth rhs.dagDepth) lIdx = some el ∧
          evalSpecExpr t.keyOf (List.range n) tbl₂ (Nat.max lhs.dagDepth rhs.dagDepth) rIdx = some er ∧
          isDefEqCore .verified env F 0 el er = .ok Bool.true) ↔
        isDefEqCore .verified env F 0 lhs' rhs' = .ok Bool.true) := by
  obtain ⟨lIdx, rIdx, tbl₁, tbl₂, hbL, hbR, hevL, hevR⟩ :=
    buildOpEqEntry_spec t.keyOf n lhs rhs lhs' rhs' hwfL hwfR hsubL hsubR
  refine ⟨lIdx, rIdx, tbl₁, tbl₂, hbL, hbR, ?_⟩
  rw [hevL, hevR]
  constructor
  · rintro ⟨el, er, ⟨rfl⟩, ⟨rfl⟩, hdeq⟩
    exact hdeq
  · intro hdeq
    exact ⟨lhs', rhs', rfl, rfl, hdeq⟩

/-- **Bridge Theorem for Proof-Certificate Statement Checking (`buildEqnList`)**:
Evaluating the `(idx, tbl)` DAG built for a closed statement `(n, stmt)` under `t.keyOf`
and checking `isDefEqCore .verified env F 0 thmTy` against the resulting expression is
equivalent to checking `isDefEqCore .verified env F 0 thmTy stmt'` against the
role-resolved statement `stmt'`. -/
theorem validate_eqn_statement_entry_bridge (t : RoleTable) (env : Env .anon) (F : Nat)
    (n : Nat) (stmt stmt' thmTy : Expr .anon)
    (hwf : stmt.specClosedWF (List.range n) = Bool.true)
    (hsub : substRoleKeysM t.keyOf stmt = some stmt') :
    ∃ idx tbl,
      buildSpecExpr (List.range n) stmt {} = some (idx, tbl) ∧
      ((∃ estmt,
          evalSpecExpr t.keyOf (List.range n) tbl stmt.dagDepth idx = some estmt ∧
          isDefEqCore .verified env F 0 thmTy estmt = .ok Bool.true) ↔
        isDefEqCore .verified env F 0 thmTy stmt' = .ok Bool.true) := by
  obtain ⟨idx, tbl, hb, hev⟩ := buildEqnStatementEntry_spec t.keyOf n stmt stmt' hwf hsub
  refine ⟨idx, tbl, hb, ?_⟩
  rw [hev]
  constructor
  · rintro ⟨estmt, ⟨rfl⟩, hdeq⟩
    exact hdeq
  · intro hdeq
    exact ⟨stmt', rfl, hdeq⟩

end Ix.Cert.IxVM
