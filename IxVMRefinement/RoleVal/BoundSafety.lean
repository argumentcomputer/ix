import IxVMRefinement.RoleVal.GroupWalkLim

/-! # The safety check a role's validation makes of its bound constant

`KernelRoles::validate_role` loads the constant at the role's bound address with
`Ingress::get_ci` and hands the loaded value to the validation of the role's kind. Four kinds
check that value's safety:

* a member of a block (kind 0) and an anchor (kind 1): `KernelRoles::assert_safe_role`, that is
  `KernelCheck::is_unsafe_ci` answers `0`;
* an operation (kind 2) and a definition specified by equations (kind 5): the value is matched as
  `KConstantInfo::Defn(_, _, _, safety, _)` and the safety must be `Safe`
  (`KernelRoles::validate_op`, `KernelRoles::validate_eqns`).

`ValidateRoleIn.bound_load_safe` reads this off the observed validation: the run loaded the
constant at the role's bound address, and the loaded value passed one of the two checks
(`BoundValueSafe`).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)


set_option linter.unusedVariables false

/-- **A loaded constant that passed a role's safety check**: `KernelCheck::is_unsafe_ci`
answered `0` on it, or it is a definition value whose safety is `Safe`. -/
def BoundValueSafe (v : SourceValue F) : Prop :=
  (∃ (h h' : Heap F) (cs : List (Call F)),
    ObsFn W "KernelCheck::is_unsafe_ci" [v] h (.field 0) h' cs) ∨
  ∃ nl ty val hint : SourceValue F,
    v = .construct "KernelTypes::KConstantInfo" "Defn"
      [nl, ty, val, .construct "Ixon::DefinitionSafety" "Safe" [], hint]

/-- **The run loaded the constant at `a` and the loaded value passed a role's safety check**:
an observed `Ingress::get_ci` at `a` among `calls` whose value is `BoundValueSafe`. -/
def BoundLoadSafeIn (calls : List (Call F)) (a : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (ap ptr v : SourceValue F) (cs : List (Call F)),
    S0.addr h ap a ∧ ObsFn W "Ingress::get_ci" [ap] h ptr h' cs ∧ (∀ cl ∈ cs, cl ∈ calls) ∧
    loadValue h' ptr = .ok v ∧ BoundValueSafe v

private theorem assert_safe_role_zero {x_ci r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::assert_safe_role" [x_ci] h r h' cs) : BoundValueSafe x_ci := by
  match Obs.«KernelRoles::assert_safe_role».obs ev with
  | .run (ev25 := ev25) (heq40 := heq) .. =>
    subst heq
    exact .inl ⟨_, _, _, ev25⟩

private theorem validate_member_safe {x_rc x_tbl x_r x_a x_ci r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::validate_member" [x_rc, x_tbl, x_r, x_a, x_ci] h r h' cs) :
    BoundValueSafe x_ci := by
  match Obs.«KernelRoles::validate_member».obs ev with
  | .n0 (ev14 := ev14) .. | .n1 (ev14 := ev14) .. | .n2 (ev14 := ev14) ..
  | .n3 (ev14 := ev14) .. | .n4 (ev14 := ev14) .. | .n5 (ev14 := ev14) ..
  | .n6 (ev14 := ev14) .. | .n7 (ev14 := ev14) .. =>
    exact assert_safe_role_zero ev14

private theorem validate_anchor_safe {x_rc x_tbl x_r x_ci r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::validate_anchor" [x_rc, x_tbl, x_r, x_ci] h r h' cs) :
    BoundValueSafe x_ci := by
  match Obs.«KernelRoles::validate_anchor».obs ev with
  | .n1 (ev14 := ev14) .. | .other (ev14 := ev14) .. =>
    exact assert_safe_role_zero ev14

private theorem validate_op_safe {x_rc x_tbl x_r x_a x_ci r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::validate_op" [x_rc, x_tbl, x_r, x_a, x_ci] h r h' cs) :
    BoundValueSafe x_ci := by
  match Obs.«KernelRoles::validate_op».obs ev with
  | .Defn (hv114 := hv) (sg207 := sg) .. =>
    cases sg with
    | Safe hs _ _ _ =>
      subst hs
      exact .inr ⟨_, _, _, _, hv⟩
    | other _ heq _ _ _ => exact absurd (Value.field.inj heq) zero_ne_one
  | .other (heq575 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one

private theorem validate_eqns_safe {x_rc x_tbl x_r x_a x_ci r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelRoles::validate_eqns" [x_rc, x_tbl, x_r, x_a, x_ci] h r h' cs) :
    BoundValueSafe x_ci := by
  match Obs.«KernelRoles::validate_eqns».obs ev with
  | .run (hv15 := hv) (sg108 := sg) .. =>
    cases sg with
    | Safe hs _ _ _ =>
      subst hs
      exact .inr ⟨_, _, _, _, hv⟩
    | other _ heq _ _ _ => exact absurd (Value.field.inj heq) zero_ne_one

/-- **The safety check of a role's validation, as observed**: for a role of kind 0, 1, 2 or 5,
the observed `KernelRoles::validate_role` loaded the constant at the role's bound address, and
the loaded value passed the kind's safety check. -/
theorem ValidateRoleIn.bound_load_safe {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro)
    (hk : roleSpecKindNat ro = 0 ∨ roleSpecKindNat ro = 1 ∨ roleSpecKindNat ro = 2 ∨
      roleSpecKindNat ro = 5) :
    ∃ a, t.addressOf? ro = some a ∧ BoundLoadSafeIn calls a := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  match Obs.«KernelRoles::validate_role».obs ev with
  | .n0 (v1 := v1) (m2 := m2) (v31 := v31) (cs45 := cs45) (ev14 := ev14) (ev47 := ev47)
      (ld41 := ld41) (ev142 := evk) (hc183 := hc) .. =>
    obtain ⟨-, a, ha, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    exact ⟨a, had, _, _, _, _, _, _, ha, ev47,
      fun cl (hm : cl ∈ cs45) => hsub cl (by rw [hc]; simp [hm]), ld41, validate_member_safe evk⟩
  | .n1 (v1 := v1) (m2 := m2) (v31 := v31) (cs45 := cs45) (ev14 := ev14) (ev47 := ev47)
      (ld41 := ld41) (ev194 := evk) (hc227 := hc) .. =>
    obtain ⟨-, a, ha, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    exact ⟨a, had, _, _, _, _, _, _, ha, ev47,
      fun cl (hm : cl ∈ cs45) => hsub cl (by rw [hc]; simp [hm]), ld41, validate_anchor_safe evk⟩
  | .n2 (v1 := v1) (m2 := m2) (v31 := v31) (cs45 := cs45) (ev14 := ev14) (ev47 := ev47)
      (ld41 := ld41) (ev238 := evk) (hc279 := hc) .. =>
    obtain ⟨-, a, ha, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    exact ⟨a, had, _, _, _, _, _, _, ha, ev47,
      fun cl (hm : cl ∈ cs45) => hsub cl (by rw [hc]; simp [hm]), ld41, validate_op_safe evk⟩
  | .n3 (ev124 := ev124) .. =>
    obtain ⟨hsk, -⟩ := role_spec_kind_spec ev124
    exfalso
    rcases hk with h0 | h0 | h0 | h0 <;> rw [h0] at hsk <;>
      exact absurd (Value.field.inj hsk) (by decide)
  | .n4 (ev124 := ev124) .. =>
    obtain ⟨hsk, -⟩ := role_spec_kind_spec ev124
    exfalso
    rcases hk with h0 | h0 | h0 | h0 <;> rw [h0] at hsk <;>
      exact absurd (Value.field.inj hsk) (by decide)
  | .n5 (v1 := v1) (m2 := m2) (v31 := v31) (cs45 := cs45) (ev14 := ev14) (ev47 := ev47)
      (ld41 := ld41) (ev378 := evk) (hc419 := hc) .. =>
    obtain ⟨-, a, ha, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    exact ⟨a, had, _, _, _, _, _, _, ha, ev47,
      fun cl (hm : cl ∈ cs45) => hsub cl (by rw [hc]; simp [hm]), ld41, validate_eqns_safe evk⟩

set_option maxRecDepth 100000 in
/-- **A role whose bound record its validation walks is of kind 0, 1, 2 or 5.** -/
theorem roleSpecKind_of_walked (ro : Ix.Kernel.Role) :
    (roleWalksBound ro = true ∨ anchorWalked ro = true) →
    roleSpecKindNat ro = 0 ∨ roleSpecKindNat ro = 1 ∨ roleSpecKindNat ro = 2 ∨
      roleSpecKindNat ro = 5 := by
  cases ro <;> decide

end IxVM.Refinement.RoleVal
