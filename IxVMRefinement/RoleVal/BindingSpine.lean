import IxVMRefinement.RoleVal.GroupAdmit
import IxVMRefinement.Decl.NativeCommon

/-! # The spine of `KernelRoles::validate_binding`

A `binding` claim runs `KernelRoles::validate_binding(binding)`: it loads the role table, asserts
that every role is bound (`assert_all_roles_bound`, a loop over the 108 roles), and admits every
validation group in order (`admit_all_groups`, a loop over the 77 groups, each a call of
`group_admit`).

* `assert_all_roles_bound_spec`: from a role index on, every role is bound.
* `admit_all_groups_observed`: from a group on, every role of every group has its observed
  `validate_role` call under the role context at its group's validation limit
  (`ValidateRoleIn`).
* `validate_binding_spine`: the observed `validate_binding` call holds the observed
  `load_role_table` call, and for every table that the loaded value represents, the table binds
  every role and every role of each of the 77 groups has its observed validation.

What is not here: that the loaded value represents an admitted table. `Claim.load_role_table_spec`
has that for a table given in advance (the typing direction); the binding direction has to produce
the table from the parse.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-- Two small naturals with the same field cast are equal. -/
private theorem natCast_field_inj {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (h : ((a : Nat) : F) = ((b : Nat) : F)) : a = b := by
  have hv := congrArg ZMod.val h
  rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hv
  exact hv

/-- Every index below 108 is a role's. -/
theorem exists_role_idx {k : Nat} (hk : k < 108) : ∃ ro : Ix.Kernel.Role, ro.idx = k := by
  have hc := Ix.Kernel.Role.ofIdx?_idx_below k hk
  cases hro : Ix.Kernel.Role.ofIdx? k with
  | none =>
    simp [hro] at hc
  | some ro => exact ⟨ro, Ix.Kernel.Role.idx_ofIdx? hro⟩

/-- **`KernelRoles::assert_all_roles_bound(tbl, k)`**: every role from index `k` on is bound. -/
theorem assert_all_roles_bound_spec {t : Ix.Kernel.RoleTable} :
    ∀ (n k : Nat), k + n = 108 →
      ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        TableRep t h x_tbl →
        ObsFn W "KernelRoles::assert_all_roles_bound" [x_tbl, .field ((k : Nat) : F)] h r h'
          calls →
        ∀ ro : Ix.Kernel.Role, k ≤ ro.idx → (t.addressOf? ro).isSome = true := by
  intro n
  induction n with
  | zero =>
    intro k hk x_tbl r h h' calls htbl ev ro hle
    have := ro.idx_lt
    omega
  | succ n ih =>
    intro k hk x_tbl r h h' calls htbl ev ro hle
    cases Obs.«KernelRoles::assert_all_roles_bound».obs ev with
    | n0 m2 y11 cs22 ev24 op17 he31 he32 hc33 =>
      obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::role_count».obs ev24
      obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op17
      have e : ((k : Nat) : F) = ((108 : Nat) : F) := by
        rw [Nat.cast_ofNat]
        exact (Value.field.inj hx1).trans (Value.field.inj hx2).symm
      have := natCast_field_inj (by omega) (by omega) e
      omega
    | other v1 m2 y11 cs22 v49 m52 cs60 cs89 v93 ev24 op17 hne34 ev62 heq85 op114 ev91 hc116 =>
      obtain ⟨rfl, hm2, -⟩ := Obs.«KernelRoleSpec::role_count».obs ev24
      subst hm2
      obtain rfl := Decl.evalBinOp_add_one k op114
      obtain ⟨ro₀, hro₀⟩ := exists_role_idx (k := k) (by omega)
      subst hro₀
      have htbl' := htbl
      obtain ⟨bp, byRole, byAddr, evMap, hload, -, -, -⟩ := htbl'
      have hby : Specs.Roles.ByRole _ x_tbl byRole := ⟨bp, byAddr, evMap, hload⟩
      have hv_ne : v49 ≠ .field 0 := by
        rw [heq85]
        exact fun e => one_ne_zero (Value.field.inj e)
      obtain ⟨res, -, hbound⟩ := role_is_bound_uncond (ro := ro₀) htbl hv_ne hby ev62
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have hro : ro = ro₀ := Ix.Kernel.Role.idx_inj heq.symm
        rw [hro]
        cases res with
        | some v =>
          obtain ⟨a, -, haddr⟩ := hbound
          simp [haddr]
        | none =>
          have haddr : t.addressOf? ro₀ = some (ixAddr Specs.Roles.zeroAddr) := hbound
          simp [haddr]
      · exact ih (ro₀.idx + 1) (by omega) (htbl.mono ev62.heap_extends) ev91 ro
          (Nat.succ_le_of_lt hlt)

/-- **`KernelRoles::admit_all_groups(tbl, k)`, as observed**: every role of every group from `k`
to 76 has its observed validation under the role context at its group's validation limit. -/
theorem admit_all_groups_observed {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} :
    ∀ (n k : Nat), k + n = 77 →
      ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        Claim.TableFullRep t bAddr h x_tbl →
        ObsFn W "KernelRoles::admit_all_groups" [x_tbl, .field ((k : Nat) : F)] h r h' calls →
        ∀ g, k ≤ g → g < 77 → ∀ ro ∈ groupRoles g, ValidateRoleIn calls bAddr t g ro := by
  intro n
  induction n with
  | zero =>
    intro k hk x_tbl r h h' calls htbl ev g hkg hg
    omega
  | succ n ih =>
    intro k hk x_tbl r h h' calls htbl ev g hkg hg ro hro
    cases Obs.«KernelRoles::admit_all_groups».obs ev with
    | n0 m2 y11 cs22 ev24 op17 he31 he32 hc33 =>
      obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::group_count».obs ev24
      obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op17
      have e : ((k : Nat) : F) = ((77 : Nat) : F) := by
        rw [Nat.cast_ofNat]
        exact (Value.field.inj hx1).trans (Value.field.inj hx2).symm
      have := natCast_field_inj (by omega) (by omega) e
      omega
    | other v1 m2 y11 cs22 v38 m39 cs49 cs71 v75 ev24 op17 hne34 ev51 op96 ev73 hc98 =>
      obtain ⟨rfl, hm2, -⟩ := Obs.«KernelRoleSpec::group_count».obs ev24
      subst hm2
      obtain rfl := Decl.evalBinOp_add_one k op96
      obtain ⟨ext1, hhere⟩ := group_admit_role_observations (g := k) (by omega) htbl ev51
      have hsub1 : ∀ cl ∈ cs49, cl ∈ calls := fun cl hm => by rw [hc98]; simp [hm]
      have hsub2 : ∀ cl ∈ cs71, cl ∈ calls := fun cl hm => by rw [hc98]; simp [hm]
      rcases Nat.eq_or_lt_of_le hkg with heq | hlt
      · subst heq
        exact (hhere ro hro).mono hsub1
      · exact (ih (k + 1) (by omega) (htbl.mono ext1) ev73 g (Nat.succ_le_of_lt hlt) hg ro
          hro).mono hsub2

/-- **The observed validation of the binding at `a`**: a call of `KernelRoles::validate_binding`
on the address `a`, among `calls`. -/
def ValidateBindingIn (calls : List (Call F)) (a : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (x_a res : SourceValue F) (cs : List (Call F)),
    BaseSeams.addr h x_a a ∧ ObsFn W "KernelRoles::validate_binding" [x_a] h res h' cs ∧
    ∀ cl ∈ cs, cl ∈ calls

theorem ValidateBindingIn.mono {cs₁ cs₂ : List (Call F)} {a : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hv : ValidateBindingIn cs₁ a) : ValidateBindingIn cs₂ a := by
  obtain ⟨h, h', x_a, res, cs, ha, ev, hs⟩ := hv
  exact ⟨h, h', x_a, res, cs, ha, ev, fun cl hm => hsub cl (hs cl hm)⟩

/-- **The spine of `KernelRoles::validate_binding`** (module docstring): the observed call is the
observed calls of `load_role_table`, `assert_all_roles_bound` and `admit_all_groups` in turn, and
for every table the loaded value represents at an address, the table binds every role and every
role of each of the 77 groups has its observed validation. -/
theorem validate_binding_spine {x_a res : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::validate_binding" [x_a] h res h' calls) :
    ∃ (x_tbl v : SourceValue F) (h₁ h₂ : Heap F) (cs₁ cs₂ cs₃ : List (Call F)),
      ObsFn W "KernelRoles::load_role_table" [x_a] h x_tbl h₁ cs₁ ∧
      ObsFn W "KernelRoles::assert_all_roles_bound" [x_tbl, .field 0] h₁ v h₂ cs₂ ∧
      ObsFn W "KernelRoles::admit_all_groups" [x_tbl, .field 0] h₂ res h' cs₃ ∧
      (∀ cl ∈ cs₁, cl ∈ calls) ∧
      ∀ (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address),
        Claim.TableFullRep t bAddr h₁ x_tbl →
        (∀ ro : Ix.Kernel.Role, (t.addressOf? ro).isSome = true) ∧
        ∀ g, g < 77 → ∀ ro ∈ groupRoles g, ValidateRoleIn calls bAddr t g ro := by
  obtain ⟨v1, m2, cs12, v23, m24, cs34, cs55, ev14, ev36, ev57, hc73⟩ :=
    Obs.«KernelRoles::validate_binding».obs ev
  have hsub1 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hm => by rw [hc73]; simp [hm]
  have hsub3 : ∀ cl ∈ cs55, cl ∈ calls := fun cl hm => by rw [hc73]; simp [hm]
  refine ⟨v1, v23, m2, m24, cs12, cs34, cs55, ev14, ev36, ev57, hsub1,
    fun t bAddr htbl => ⟨?_, ?_⟩⟩
  · intro ro
    have ev36' : ObsFn W "KernelRoles::assert_all_roles_bound" [v1, .field ((0 : Nat) : F)]
        m2 v23 m24 cs34 := by
      rw [Nat.cast_zero]
      exact ev36
    exact assert_all_roles_bound_spec 108 0 (by omega) htbl.toTableRep ev36' ro (Nat.zero_le _)
  · intro g hg ro hro
    have ev57' : ObsFn W "KernelRoles::admit_all_groups" [v1, .field ((0 : Nat) : F)]
        m24 res h' cs55 := by
      rw [Nat.cast_zero]
      exact ev57
    exact (admit_all_groups_observed 77 0 (by omega) (htbl.mono ev36.heap_extends) ev57' g
      (Nat.zero_le _) hg ro hro).mono hsub3

end IxVM.Refinement.RoleVal
