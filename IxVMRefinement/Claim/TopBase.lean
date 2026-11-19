import IxVMRefinement.Claim.Phase
import IxVMRefinement.RoleVal.GroupAdmit
import IxVMRefinement.Roles.Tables
import Ix.IxVM.Consistency.TableValid

/-! # The claim walk at a role-context limit: representation and small specifications

A typing claim runs its walk under the top-level role context of its table: `Mk(tbl, 77, Nil)`
when it validates the table, `Assumed(tbl, Nil)` when it assumes it. A validation of a role
group runs its walk under `Mk(tbl, groupValLimit g, Nil)`. This module represents a context by
its limit (`RCLimRep t bAddr lim`: `some n` for `Mk(tbl, n, Nil)`, `none` for `Assumed`) and
proves the specifications of the context operations the walks use at every limit:

* `load_role_ctx_lim_spec`: `load_role_ctx(binding, v, None)` gives the context at `some 77`
  for `v = 3` and at `none` for `v = 4` (the table loaded by `load_role_table`, with its
  evidence check and basis pin);
* `walk_covered_lim_spec`, `walk_ctx_lim_spec`: a reference the walk skips, or walks under a
  context other than its own, is bound to a role whose record a validation walks, in force at
  the limit (`CoveredAt`);
* the accessors `role_ctx_table`, `role_ctx_binding`, `role_ctx_validator`, `role_ctx_limit`;
* `run_check`, `check_muts_member_at`, `check_muts_all` with their check witnesses at the
  limit (`CheckedLimAt`, `MemberCheckedLimAt`).

It also defines what a walk at a limit records (`TopRec`, `TopRecsClosed`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## The context at a limit -/

/-- **A role context at the limit `lim`**: `Mk(tbl, n, Nil)` for `some n` (the tree's
`RCFullRep`), `Assumed(tbl, Nil)` for `none`, with the table `t` at the binding `bAddr`. -/
def RCLimRep (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address) :
    Option Nat → Heap F → SourceValue F → Prop
  | some n, h, rc => RCFullRep t bAddr n h rc
  | none, h, rc => ∃ tbl,
      loadValue h rc = .ok (.construct rcEnum "Assumed" [tbl, .construct addrMapEnum "Nil" []]) ∧
      TableFullRep t bAddr h tbl

theorem RCLimRep.mono {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {h₁ h₂ : Heap F} {rc : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (hrc : RCLimRep t bAddr lim h₁ rc) : RCLimRep t bAddr lim h₂ rc := by
  cases lim with
  | some n => exact RCFullRep.mono ext hrc
  | none =>
    obtain ⟨tbl, hl, htbl⟩ := hrc
    exact ⟨tbl, ext.loadValue_eq hl, htbl.mono ext⟩

/-- The two shapes of a context at a limit. -/
theorem RCLimRep.cases {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {h : Heap F} {rc : SourceValue F} (hrc : RCLimRep t bAddr lim h rc) :
    ∃ tbl, TableFullRep t bAddr h tbl ∧
      ((∃ n, lim = some n ∧ n < 4294967296 ∧
          loadValue h rc = .ok (.construct rcEnum "Mk"
            [tbl, .field (n : F), .construct addrMapEnum "Nil" []])) ∨
        (lim = none ∧ loadValue h rc = .ok (.construct rcEnum "Assumed"
            [tbl, .construct addrMapEnum "Nil" []]))) := by
  cases lim with
  | some n =>
    obtain ⟨hn, tbl, hl, htbl⟩ := hrc
    exact ⟨tbl, htbl, .inl ⟨n, rfl, hn, hl⟩⟩
  | none =>
    obtain ⟨tbl, hl, htbl⟩ := hrc
    exact ⟨tbl, htbl, .inr ⟨rfl, hl⟩⟩

/-! ## Roles whose record a validation walks -/

/-- **`b` is bound to a role whose record a validation walks, in force at `lim`**: a walk at
`lim` skips such a reference (`Assumed`) or walks it under a context of its own (`Mk`). At the
top level (`some 77` or `none`) it is the assembly's `Typing.Covered`. -/
def CoveredAt (t : Ix.Kernel.RoleTable) (lim : Option Nat) (b : _root_.Address) : Prop :=
  ∃ r, t.addressOf? r = some b ∧ IxVM.Consistency.walkedRole r = true ∧
    ∀ n, lim = some n → Ix.SpecDigest.groupOf r < n

theorem walkedRole_eq_roleWalksBound (ro : Ix.Kernel.Role) :
    IxVM.Consistency.walkedRole ro = RoleVal.roleWalksBound ro := by
  cases ro <;> decide

/-- The value `KernelRoleSpec::role_member_kind` gives a role. -/
def memberKindF (ro : Ix.Kernel.Role) : F :=
  (RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body)
    (roleNum ro)).getD 0

set_option maxRecDepth 100000 in
theorem role_member_kind_table (ro : Ix.Kernel.Role) :
    RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body)
      (roleNum ro) = some (memberKindF ro) := by
  cases ro <;> decide

theorem role_member_kind_full {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_member_kind" [.field (roleNum ro)] h r h' calls) :
    r = .field (memberKindF ro) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_member_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_member_kind, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.role_member_kind.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_member_kind.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨v1, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable (role_member_kind_table ro) sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- The roles `role_admission_checks` answers `1` for are the walked roles. -/
theorem walks_of_admission (ro : Ix.Kernel.Role) :
    ((((RoleVal.roleSpecKindNat ro : Nat) : F) = 0 →
        (memberKindF ro = 0 ∨ memberKindF ro = 1 ∨ memberKindF ro = 2) →
        RoleVal.roleWalksBound ro = true) ∧
      (((RoleVal.roleSpecKindNat ro : Nat) : F) = 2 → RoleVal.roleWalksBound ro = true) ∧
      (((RoleVal.roleSpecKindNat ro : Nat) : F) = 5 → RoleVal.roleWalksBound ro = true)) := by
  cases ro <;> decide

/-- **`KernelRoles::role_admission_checks` at a role**: `0`, or `1` at a walked role. -/
theorem role_admission_checks_walks {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::role_admission_checks" [.field (roleNum ro)] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ (r = .field 1 ∧ IxVM.Consistency.walkedRole ro = true)) := by
  rw [walkedRole_eq_roleWalksBound]
  obtain ⟨hw0, hw2, hw5⟩ := walks_of_admission ro
  match Obs.«KernelRoles::role_admission_checks».obs ev with
  | .n0_n0 (ev15 := ev15) (ev42 := ev42) (he55 := he) (he56 := hh) .. =>
    obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    obtain ⟨hm, rfl⟩ := role_member_kind_full ev42
    exact ⟨hh, .inr ⟨he, hw0 (Value.field.inj hk).symm (.inl (Value.field.inj hm).symm)⟩⟩
  | .n0_n1 (ev15 := ev15) (ev42 := ev42) (he63 := he) (he64 := hh) .. =>
    obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    obtain ⟨hm, rfl⟩ := role_member_kind_full ev42
    exact ⟨hh, .inr ⟨he, hw0 (Value.field.inj hk).symm (.inr (.inl (Value.field.inj hm).symm))⟩⟩
  | .n0_n2 (ev15 := ev15) (ev42 := ev42) (he71 := he) (he72 := hh) .. =>
    obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    obtain ⟨hm, rfl⟩ := role_member_kind_full ev42
    exact ⟨hh, .inr ⟨he, hw0 (Value.field.inj hk).symm (.inr (.inr (Value.field.inj hm).symm))⟩⟩
  | .n0_other (ev15 := ev15) (ev42 := ev42) (he78 := he) (he79 := hh) .. =>
    obtain ⟨-, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    obtain ⟨-, rfl⟩ := role_member_kind_full ev42
    exact ⟨hh, .inl he⟩
  | .n2 (ev15 := ev15) (he86 := he) (he87 := hh) .. =>
    obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    exact ⟨hh, .inr ⟨he, hw2 (Value.field.inj hk).symm⟩⟩
  | .n5 (ev15 := ev15) (he94 := he) (he95 := hh) .. =>
    obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    exact ⟨hh, .inr ⟨he, hw5 (Value.field.inj hk).symm⟩⟩
  | .other (ev15 := ev15) (he101 := he) (he102 := hh) .. =>
    obtain ⟨-, rfl⟩ := RoleVal.role_spec_kind_spec ev15
    exact ⟨hh, .inl he⟩

/-! ## The address index -/

/-- **A lookup in the table's address index** finds the role the table binds to the address,
or nothing when it binds none. -/
theorem addr_index_lookup {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {x_tbl x_a v51 v36 : SourceValue F} {h m61 m37 : Heap F} {cs69 cs47 : List (Call F)}
    (htbl : TableFullRep t bAddr h x_tbl) (ha : S0.addr h x_a a)
    (ev71 : ObsFn W "KernelRoles::role_addr_index" [x_tbl] h v51 m61 cs69)
    (ev49 : ObsFn W Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>»
      [x_a, v51, .field 0] m61 v36 m37 cs47) :
    m61 = h ∧ m37 = h ∧
      ((v36 = .field 0 ∧ ∀ ro, t.addressOf? ro ≠ some a) ∨
        ∃ ro : Ix.Kernel.Role, v36 = .field (roleNum ro + 1) ∧ t.addressOf? ro = some a) := by
  obtain ⟨ab, hab, hix⟩ := ha
  obtain ⟨rfl, ⟨es, hbst, hie, hmem⟩⟩ := role_addr_index_full_spec htbl ev71
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev49
  obtain ⟨hlk, rfl⟩ := rbtree_map_lookup_or_default_spec hab hbst ev49
  refine ⟨rfl, rfl, ?_⟩
  by_cases hex : ∃ w, (ab, w) ∈ es
  · obtain ⟨w, hw⟩ := hex
    rw [lookupEntries_eq_of_mem hbst.2 hw] at hlk
    obtain ⟨ro, hw_eq, hof⟩ := hie (ab, w) hw
    rw [hix] at hof
    exact .inr ⟨ro, hlk.trans hw_eq, hof⟩
  · have hno : ∀ w, (ab, w) ∉ es := fun w hw => hex ⟨w, hw⟩
    rw [lookupEntries_eq_dflt_of_not_mem hno] at hlk
    refine .inl ⟨hlk, ?_⟩
    intro ro hof
    have hm_bound := mem_bound_of_addressOf_eq_some hof
    obtain ⟨b0, hix0, hb0⟩ := hmem ro a hm_bound
    have hb_eq : b0 = ab := ixAddr_injective (hix0.trans hix.symm)
    subst hb_eq
    exact hno _ hb0

private theorem sub_one_roleNum {ro : Ix.Kernel.Role} {v : SourceValue F}
    (op : evalBinOp .sub (.field (roleNum ro + 1)) (.field 1) = .ok v) :
    v = .field (roleNum ro) := by
  simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
  exact op.symm

/-! ## `walk_covered` and `walk_ctx` at a limit -/

/-- **`KernelRoles::walk_covered` at a limit**: `0`, unless the reference is covered (only
under `Assumed`: under `Mk` it is always `0`). -/
theorem walk_covered_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::walk_covered" [x_rc, x_a] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ CoveredAt t lim a) := by
  obtain ⟨tbl, htbl, ⟨n, rfl, -, hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::walk_covered».obs ev with
    | .Mk (he38 := he) (he39 := hh) .. => exact ⟨hh, .inl he⟩
    | .Assumed_n0 (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed_other (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · match Obs.«KernelRoles::walk_covered».obs ev with
    | .Mk (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed_n0 (ld12 := ld12) (ev94 := ev94) (ev72 := ev72) (he123 := he) (he124 := hh) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, -⟩ := addr_index_lookup htbl ha ev94 ev72
      exact ⟨hh, .inl he⟩
    | .Assumed_other (ld12 := ld12) (ev94 := ev94) (ev72 := ev72) (hne126 := hne)
        (op150 := op) (ev135 := ev135) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl ha ev94 ev72
      rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
      · exact absurd rfl hne
      · rw [sub_one_roleNum op] at ev135
        obtain ⟨rfl, hr⟩ := role_admission_checks_walks ev135
        rcases hr with hr0 | ⟨-, hw⟩
        · exact ⟨rfl, .inl hr0⟩
        · exact ⟨rfl, .inr ⟨ro, hof, hw, fun n hn => by cases hn⟩⟩

private theorem groupValLimit_le_self (g : Nat) : RoleVal.groupValLimit g ≤ g := by
  unfold RoleVal.groupValLimit
  split
  · omega
  · split
    · omega
    · split <;> omega

/-- **`KernelRoles::walk_ctx` at a limit**: the context itself, or a reference covered at the
limit gets a validation context at a smaller limit. -/
theorem walk_ctx_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::walk_ctx" [x_rc, x_a] h r h' calls) :
    Heap.Extends h h' ∧
      (r = x_rc ∨
        (CoveredAt t lim a ∧ ∃ lim', (∀ n, lim = some n → lim' < n) ∧
          RCFullRep t bAddr lim' h' r)) := by
  have ext := ev.heap_extends
  obtain ⟨tbl, htbl, ⟨n, rfl, hn, hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::walk_ctx».obs ev with
    | .Mk_n0 (he101 := he) .. => exact ⟨ext, .inl he⟩
    | .Mk_other_n0 (he250 := he) .. => exact ⟨ext, .inl he⟩
    | .Mk_other_other (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) (hne104 := hne)
        (op136 := op136) (ev121 := ev121) (ev206 := ev206) (op243 := op243) (ev228 := ev228)
        (op200 := op200) (hne253 := hne253) (he261 := he261) (hm260 := hm260)
        (ev286 := ev286) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
      · exact absurd rfl hne
      · rw [sub_one_roleNum op136] at ev121
        rw [sub_one_roleNum op243] at ev228
        obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev121
        obtain ⟨hgl, -, hlt_iff, hx01, rfl⟩ := Lib.less_than_fields_field ev206
        obtain ⟨rfl, hadm⟩ := role_admission_checks_walks ev228
        have hx1 : ∀ x y : SourceValue F, (x = .field 0 ∨ x = .field 1) →
            (y = .field 0 ∨ (y = .field 1 ∧ IxVM.Consistency.walkedRole ro = true)) →
            ∀ v, evalBinOp .mul x y = .ok v → v ≠ .field 0 →
              x = .field 1 ∧ IxVM.Consistency.walkedRole ro = true := by
          intro x y hx hy v hop hv
          rcases hx with rfl | rfl <;> rcases hy with rfl | ⟨rfl, hw⟩ <;>
            simp only [evalBinOp, Except.ok.injEq] at hop <;> subst hop <;> simp at hv
          exact ⟨rfl, hw⟩
        obtain ⟨hx1', hw⟩ := hx1 _ _ hx01 hadm _ op200 hne253
        have hglt : Ix.SpecDigest.groupOf ro < n := by
          have h1 := hlt_iff.mp hx1'
          rwa [RolesAux.val_groupOf, RolesAux.val_natCast
            (Nat.lt_trans hn (by decide))] at h1
        have hg32 : Ix.SpecDigest.groupOf ro < 4294967296 := by omega
        obtain ⟨rfl, rfl⟩ := RoleVal.group_validation_limit_of_nat hg32 ev286
        subst he261 hm260
        refine ⟨ext, .inr ⟨⟨ro, hof, hw, fun n' hn' => by cases hn'; exact hglt⟩,
          RoleVal.groupValLimit (Ix.SpecDigest.groupOf ro),
          fun n' hn' => by
            cases hn'
            exact Nat.lt_of_le_of_lt (groupValLimit_le_self _) hglt, ?_⟩⟩
        refine ⟨by have := RoleVal.groupValLimit_le (Ix.SpecDigest.groupOf ro); omega, tbl,
          loadValue_snoc_construct _ rcEnum "Mk" _, htbl.mono ext⟩
    | .Assumed (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · match Obs.«KernelRoles::walk_ctx».obs ev with
    | .Mk_n0 (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Mk_other_n0 (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Mk_other_other (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed (he325 := he) .. => exact ⟨ext, .inl he⟩

/-! ## The context accessors at a limit -/

theorem role_ctx_table_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_table" [x_rc] h r h' calls) :
    h' = h ∧ TableFullRep t bAddr h r := by
  obtain ⟨tbl, htbl, ⟨n, -, -, hl⟩ | ⟨-, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::role_ctx_table».obs ev with
    | .Mk (ld12 := ld12) (he38 := he) (he39 := hh) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      subst he
      exact ⟨hh, htbl⟩
    | .Assumed (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · match Obs.«KernelRoles::role_ctx_table».obs ev with
    | .Mk (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed (ld12 := ld12) (he60 := he) (he61 := hh) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      subst he
      exact ⟨hh, htbl⟩

theorem role_ctx_binding_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_binding" [x_rc] h r h' calls) :
    h' = h ∧ S0.addr h r bAddr := by
  obtain ⟨m2, p10, _, x_binding, _, _, _, ev18, ld12, rfl, rfl, -⟩ :=
    Obs.«KernelRoles::role_ctx_binding».obs ev
  obtain ⟨rfl, _, bp, _, _, _, hl_tbl, hbp, -, -, -⟩ := role_ctx_table_lim_spec hrc ev18
  rw [hl_tbl] at ld12
  injection ld12 with hv
  injection hv with _ _ hargs
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, -⟩ := hargs
  exact ⟨rfl, hbp⟩

/-- **`KernelRoles::role_ctx_validator` at a limit**: `3` under `Mk`, `4` under `Assumed`. -/
theorem role_ctx_validator_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_validator" [x_rc] h r h' calls) :
    h' = h ∧ (((∃ n, lim = some n) ∧ r = .field 3) ∨ (lim = none ∧ r = .field 4)) := by
  obtain ⟨tbl, htbl, ⟨n, rfl, -, hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · obtain ⟨y2, _, ev14, op8, -⟩ := Obs.«KernelRoles::role_ctx_validator».obs ev
    match Obs.«KernelRoles::role_ctx_is_assumed».obs ev14 with
    | .Mk (he38 := he) (he39 := hh) .. =>
      subst he hh
      simp only [evalBinOp, add_zero, Except.ok.injEq] at op8
      exact ⟨rfl, .inl ⟨⟨n, rfl⟩, op8.symm⟩⟩
    | .Assumed (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · obtain ⟨y2, _, ev14, op8, -⟩ := Obs.«KernelRoles::role_ctx_validator».obs ev
    match Obs.«KernelRoles::role_ctx_is_assumed».obs ev14 with
    | .Mk (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed (he60 := he) (he61 := hh) .. =>
      subst he hh
      simp only [evalBinOp, Except.ok.injEq] at op8
      refine ⟨rfl, .inr ⟨rfl, ?_⟩⟩
      rw [← op8]
      norm_num

/-- **`KernelRoles::role_ctx_limit` at a limit**: the limit under `Mk`, `0` under `Assumed`. -/
theorem role_ctx_limit_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_ctx_limit" [x_rc] h r h' calls) :
    h' = h ∧ r = .field ((lim.getD 0 : Nat) : F) := by
  obtain ⟨tbl, htbl, ⟨n, rfl, -, hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::role_ctx_limit».obs ev with
    | .Assumed (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Mk (ld12 := ld12) (he60 := he) (he61 := hh) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      exact ⟨hh, he⟩
  · match Obs.«KernelRoles::role_ctx_limit».obs ev with
    | .Assumed (he32 := he) (he33 := hh) .. => exact ⟨hh, by rw [he]; simp⟩
    | .Mk (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12

/-! ## Loading the context (A0) -/

/-- **`KernelRoles::load_role_ctx(binding, v, None)`** for an admitted table: the run hashed a
collision with `extra`, or the context is the table's at limit `77` (`v = 3`, validating) or
assumed (`v = 4`). The table is loaded by `load_role_table`, with its evidence check and its
basis pin (`load_role_table_spec`). -/
theorem load_role_ctx_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    {x_binding x_v r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : S0.addr h x_binding b.address)
    (ev : ObsFn W "KernelRoles::load_role_ctx"
      [x_binding, x_v,
       .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧
      ((x_v = .field 3 ∧ RCLimRep t b.address (some 77) h' r) ∨
        (x_v = .field 4 ∧ RCLimRep t b.address none h' r))) := by
  match Obs.«KernelRoles::load_role_ctx».obs ev with
  | .n3 v1 m2 cs12 v126 m127 cs129 v158 m168 cs176 ev14 sg134 hv148 he153 hm152 ev178 hc186 =>
    rcases load_role_table_spec (V := V) hadm hb_extra hb ev14 with hcoll | ⟨ext1, htbl⟩
    · exact .inl (hashedCollision_mono (by intro c hc; rw [hc186]; simp [hc]) hcoll)
    · rcases sg134 with ⟨_, rfl, hm_sg, _⟩ | ⟨_, _, _, _, _, _, _, _, hne45, -⟩
      · obtain ⟨rfl, hm_gc, -⟩ := Obs.«KernelRoleSpec::group_count».obs ev178
        rw [← hm_sg, ← hm_gc] at ext1 htbl
        subst he153 hm152
        let rcNode := Value.construct rcEnum "Mk"
          [v1, .field (77 : F), .construct addrMapEnum "Nil" []]
        have extSnoc := Heap.Extends.snoc m168 rcNode
        exact .inr ⟨ext1.trans extSnoc, .inl ⟨hv148, by decide, v1,
          loadValue_snoc_construct m168 rcEnum "Mk"
            [v1, .field (77 : F), .construct addrMapEnum "Nil" []],
          htbl.mono extSnoc⟩⟩
      · exact absurd rfl (hne45 [] rfl)
  | .n4 v1 m2 cs12 v126 m127 cs129 ev14 sg134 hne187 hv191 he196 hm195 hc =>
    rcases load_role_table_spec (V := V) hadm hb_extra hb ev14 with hcoll | ⟨ext1, htbl⟩
    · exact .inl (hashedCollision_mono (by intro c hc'; rw [hc]; simp [hc']) hcoll)
    · rcases sg134 with ⟨_, rfl, hm_sg, _⟩ | ⟨_, _, _, _, _, _, _, _, hne45, -⟩
      · rw [← hm_sg] at ext1 htbl
        subst he196 hm195
        let rcNode := Value.construct rcEnum "Assumed" [v1, .construct addrMapEnum "Nil" []]
        have extSnoc := Heap.Extends.snoc m127 rcNode
        exact .inr ⟨ext1.trans extSnoc, .inr ⟨hv191, v1,
          loadValue_snoc_construct m127 rcEnum "Assumed" [v1, .construct addrMapEnum "Nil" []],
          htbl.mono extSnoc⟩⟩
      · exact absurd rfl (hne45 [] rfl)
  | .other (heq246 := heq) .. =>
    exact absurd (Value.field.inj heq) (by decide)

/-- `KernelRoles::role_ctx_for_validator(binding, v)`: `load_role_ctx_lim_spec`. -/
theorem role_ctx_for_validator_lim_spec {V : View} {extra : List ByteArray}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hb_extra : b.bytes ∈ extra)
    {x_binding x_v r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : S0.addr h x_binding b.address)
    (ev : ObsFn W "KernelRoles::role_ctx_for_validator" [x_binding, x_v] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧
      ((x_v = .field 3 ∧ RCLimRep t b.address (some 77) h' r) ∨
        (x_v = .field 4 ∧ RCLimRep t b.address none h' r))) := by
  obtain ⟨cs4, ev6, hc33⟩ := Obs.«KernelRoles::role_ctx_for_validator».obs ev
  rcases load_role_ctx_lim_spec (V := V) hadm hb_extra hb ev6 with hcoll | hok
  · exact .inl (hashedCollision_mono (by intro c hc; rw [hc33]; simp [hc]) hcoll)
  · exact .inr hok

/-! ## Check witnesses at a limit -/

/-- **The walk's check of the record at `a` under the context at `lim`**: the body of
`Claim.CheckedAtFull` over `RCLimRep`. At `some n` it is `Typing.CheckedAtFullAt … n`. -/
def CheckedLimAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (a : _root_.Address) (lim : Option Nat) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
    (cs_load cs_chk : List (Call F)),
    RCLimRep t bAddr lim h_pre rc ∧
    RCLimRep t bAddr lim m_chk rc ∧
    S0.addr h_pre ap a ∧
    S0.addr m_chk ap a ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (⟨"Ingress::get_ci", [ap], h_pre⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok v ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
    (⟨"KernelCheck::check_const", [rc, v, ap], m_chk⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

/-- **The walk's check of member `k` of the block at `addr` under the context at `lim`**: the
body of `Claim.MutsMemberCheckedAtFull` over `RCLimRep`. -/
def MemberCheckedLimAt (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (addr : _root_.Address) (ms : Array Ixon.MutConst) (k : Nat)
    (lim : Option Nat) : Prop :=
  ∃ (h_pa h_pre m_chk h'_chk : Heap F)
    (rc x_members x_block ap ptr v r_chk : SourceValue F)
    (cs_pa cs_load cs_chk : List (Call F)),
    Specs.Callees.MembersRep h_pa ms.toList x_members ∧
    S0.addr h_pa x_block addr ∧
    ObsFn Obs.W "Ingress::projection_addr" [x_members, x_block, .field (k : F)] h_pa ap h_pre cs_pa ∧
    (⟨"Ingress::projection_addr", [x_members, x_block, .field (k : F)], h_pa⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_pa, cl ∈ calls) ∧
    RCLimRep t bAddr lim h_pre rc ∧
    RCLimRep t bAddr lim m_chk rc ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧
    (⟨"Ingress::get_ci", [ap], h_pre⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok v ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
    (⟨"KernelCheck::check_const", [rc, v, ap], m_chk⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

theorem CheckedLimAt.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {a : _root_.Address} {lim : Option Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hc : CheckedLimAt cs₁ bAddr t a lim) :
    CheckedLimAt cs₂ bAddr t a lim := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hc
  exact ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m,
    ev_ld, hsub _ hcl_ld, fun cl hm => hsub cl (hsub_ld cl hm), hld,
    ev_chk, hsub _ hcl_chk, fun cl hm => hsub cl (hsub_chk cl hm)⟩

theorem MemberCheckedLimAt.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {addr : _root_.Address} {ms : Array Ixon.MutConst} {k : Nat}
    {lim : Option Nat} (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂)
    (hm : MemberCheckedLimAt cs₁ bAddr t addr ms k lim) :
    MemberCheckedLimAt cs₂ bAddr t addr ms k lim := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hcl_pa, hsub_pa,
    hrc_pre, hrc_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hm
  exact ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk,
    ev_pa, hsub _ hcl_pa, fun cl hm => hsub cl (hsub_pa cl hm),
    hrc_pre, hrc_m,
    ev_ld, hsub _ hcl_ld, fun cl hm => hsub cl (hsub_ld cl hm), hld,
    ev_chk, hsub _ hcl_chk, fun cl hm => hsub cl (hsub_chk cl hm)⟩

theorem run_check_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::run_check" [x_rc, x_addr] h r h' calls) :
    Heap.Extends h h' ∧ CheckedLimAt calls bAddr t addr lim := by
  obtain ⟨v1, m2, p9, cs15, cs29, ev17, ld11, ev31, hc56⟩ := Obs.«KernelClaim::run_check».obs ev
  have ext1 := ev17.heap_extends
  have ext2 := ev31.heap_extends
  refine ⟨ext1.trans ext2,
    h, m2, h', x_rc, x_addr, p9, v1, r, cs15, cs29,
    hrc, hrc.mono ext1, ha, S0.addr_mono ext1 ha,
    ev17, by rw [hc56]; simp, fun cl hcl => by rw [hc56]; simp [hcl],
    ld11,
    ev31, by rw [hc56]; simp, fun cl hcl => by rw [hc56]; simp [hcl]⟩

theorem check_muts_member_at_lim_spec {t : Ix.Kernel.RoleTable} {bAddr addr : _root_.Address}
    {lim : Option Nat} {k : Nat} {ms : Array Ixon.MutConst}
    {x_rc x_block_addr x_all_members x_m r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_block_addr addr)
    (hmems : Specs.Callees.MembersRep h ms.toList x_all_members)
    (ev : ObsFn Obs.W "KernelClaim::check_muts_member_at"
      [x_rc, x_block_addr, x_all_members, x_m, .field (k : F)] h r h' calls) :
    Heap.Extends h h' ∧ MemberCheckedLimAt calls bAddr t addr ms k lim := by
  obtain ⟨v1, m2, cs12, v39, m40, p47, cs53, cs67, ev14, ev55, ld49, ev69, hc94⟩ :=
    Obs.«KernelClaim::check_muts_member_at».obs ev
  have ext1 := ev14.heap_extends
  have ext2 := ev55.heap_extends
  have ext3 := ev69.heap_extends
  refine ⟨ext1.trans (ext2.trans ext3),
    h, m2, m40, h', x_rc, x_all_members, x_block_addr, v1, p47, v39, r,
    cs12, cs53, cs67,
    hmems, ha,
    ev14, by rw [hc94]; simp, fun cl hcl => by rw [hc94]; simp [hcl],
    hrc.mono ext1, hrc.mono (ext1.trans ext2),
    ev55, by rw [hc94]; simp, fun cl hcl => by rw [hc94]; simp [hcl],
    ld49,
    ev69, by rw [hc94]; simp, fun cl hcl => by rw [hc94]; simp [hcl]⟩

private theorem mutShape_heapMono₂' : HeapMono₂ Specs.Callees.MutShape :=
  fun _ _ _ _ _ h => h

private theorem check_muts_all_lim_aux {t : Ix.Kernel.RoleTable} {bAddr addr : _root_.Address}
    {ms : Array Ixon.MutConst} {lim : Option Nat} (cur : List Ixon.MutConst) :
    ∀ {pos : Nat} {x_rc x_block_addr x_all_members x_cur r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      RCLimRep t bAddr lim h x_rc →
      S0.addr h x_block_addr addr →
      Specs.Callees.MembersRep h ms.toList x_all_members →
      Specs.Callees.MembersRep h cur x_cur →
      ObsFn Obs.W "KernelClaim::check_muts_all"
        [x_rc, x_block_addr, x_all_members, x_cur, .field (pos : F)] h r h' calls →
      Heap.Extends h h' ∧
      ∀ (j : Nat), j < cur.length → MemberCheckedLimAt calls bAddr t addr ms (pos + j) lim := by
  induction cur with
  | nil =>
    intro pos x_rc x_block_addr x_all_members x_cur r h h' calls hrc ha hall hcur ev
    rcases Obs.«KernelClaim::check_muts_all».obs ev with
      ⟨ld12, _, rfl, -⟩ | ⟨_, _, _, _, _, _, _, ld12, -⟩
    · exact ⟨Heap.Extends.refl _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    · obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hcur ld12
      cases hbad
  | cons m rest ih =>
    intro pos x_rc x_block_addr x_all_members x_cur r h h' calls hrc ha hall hcur ev
    rcases Obs.«KernelClaim::check_muts_all».obs ev with
      ⟨ld12, -⟩ |
      ⟨x_m, x_rest, v42, m43, cs53, cs99, v106, ld12, ev55, op148, ev101, hc150⟩
    · cases Lib.rep_nil_of_load hcur ld12
    · obtain ⟨_, rest', heq, _, hrest⟩ := Lib.rep_cons_of_load hcur ld12
      injection heq with _ he2
      subst he2
      obtain ⟨ext1, hchk_hd⟩ := check_muts_member_at_lim_spec hrc ha hall ev55
      simp only [evalBinOp, Except.ok.injEq] at op148
      subst op148
      have hv_inc : ((pos : F) + 1) = ((pos + 1 : Nat) : F) := by push_cast; rfl
      rw [hv_inc] at ev101
      obtain ⟨ext2, hchk_tl⟩ :=
        ih (hrc.mono ext1) (S0.addr_mono ext1 ha)
          (repList_heapMono₂ _ mutShape_heapMono₂' ext1 hall)
          (repList_heapMono₂ _ mutShape_heapMono₂' ext1 hrest)
          ev101
      have hsub1 : ∀ cl ∈ cs53, cl ∈ calls := fun cl hcl => by rw [hc150]; simp [hcl]
      have hsub2 : ∀ cl ∈ cs99, cl ∈ calls := fun cl hcl => by rw [hc150]; simp [hcl]
      refine ⟨ext1.trans ext2, fun j hj => ?_⟩
      cases j with
      | zero =>
        rw [Nat.add_zero]
        exact hchk_hd.mono hsub1
      | succ j' =>
        have hj' : j' < rest.length := by simp at hj; omega
        have heq_idx : pos + (j' + 1) = (pos + 1) + j' := by omega
        rw [heq_idx]
        exact (hchk_tl j' hj').mono hsub2

theorem check_muts_all_lim_spec {t : Ix.Kernel.RoleTable} {bAddr addr : _root_.Address}
    {lim : Option Nat} {ms : Array Ixon.MutConst}
    {x_rc x_block_addr x_members r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_block_addr addr)
    (hmems : Specs.Callees.MembersRep h ms.toList x_members)
    (ev : ObsFn Obs.W "KernelClaim::check_muts_all"
      [x_rc, x_block_addr, x_members, x_members, .field 0] h r h' calls) :
    Heap.Extends h h' ∧
    ∀ (k : Nat), k < ms.size → MemberCheckedLimAt calls bAddr t addr ms k lim := by
  have ev0 : ObsFn Obs.W "KernelClaim::check_muts_all"
      [x_rc, x_block_addr, x_members, x_members, .field ((0 : Nat) : F)] h r h' calls := by
    simpa using ev
  obtain ⟨ext, hk⟩ := check_muts_all_lim_aux ms.toList hrc ha hmems hmems ev0
  refine ⟨ext, fun k hlt => ?_⟩
  have hlt' : k < ms.toList.length := by rwa [Array.length_toList]
  simpa only [Nat.zero_add] using hk k hlt'

/-! ## What a walk at a limit records -/

/-- **The walk asked `assert_ref_allowed` about `b` under a context at `lim`**, and the call
returned. `TopRefs` reads what that excludes (an inert axiom in force). -/
def RefAllowedIn (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (lim : Option Nat) (b : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (rc x_b r : SourceValue F) (cs : List (Call F)),
    RCLimRep t bAddr lim h rc ∧ S0.addr h x_b b ∧
    ObsFn Obs.W "KernelRoles::assert_ref_allowed" [rc, x_b] h r h' cs ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-- **The walk loaded the record at `b` and found no block record** (`assert_not_block_ref`). -/
def NotBlockIn (calls : List (Call F)) (b : _root_.Address) : Prop :=
  ∃ (raw : ByteArray) (c : Ixon.Constant), Hashed calls raw ∧ Address.blake3Pure raw = b ∧
    Ixon.deConstant raw = .ok c ∧ ∀ ms, c.info ≠ .muts ms

theorem RefAllowedIn.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr b : _root_.Address} {lim : Option Nat} (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂)
    (h : RefAllowedIn cs₁ t bAddr lim b) : RefAllowedIn cs₂ t bAddr lim b := by
  obtain ⟨h, h', rc, x_b, r, cs, hrc, hb, ev, hcs⟩ := h
  exact ⟨h, h', rc, x_b, r, cs, hrc, hb, ev, fun cl hm => hsub cl (hcs cl hm)⟩

theorem NotBlockIn.mono {cs₁ cs₂ : List (Call F)} {b : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : NotBlockIn cs₁ b) : NotBlockIn cs₂ b := by
  obtain ⟨raw, c, hh, hb, hd, hn⟩ := h
  exact ⟨raw, c, hashed_mono hsub hh, hb, hd, hn⟩

/-- The outer walk executed the source-conditioned reference guard on this very record.
The represented record is retained so that repeated loads can be tied through the run store. -/
def RecordRefsIn (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (lim : Option Nat) (a : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∃ (h h' : Heap F) (rc ap cp r : SourceValue F) (cs : List (Call F)),
    RCLimRep t bAddr lim h rc ∧ S0.addr h ap a ∧ RepConstant h c cp ∧
    ObsFn Obs.W "KernelClaim::assert_safe_record_refs" [rc, ap, cp] h r h' cs ∧
    ∀ cl ∈ cs, cl ∈ calls

/-- Guard observations are retained when a subwalk is included in the enclosing run. -/
theorem RecordRefsIn.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hg : RecordRefsIn cs₁ t bAddr lim a c) :
    RecordRefsIn cs₂ t bAddr lim a c := by
  obtain ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hc, ev, hs⟩ := hg
  exact ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hc, ev, fun cl hcl => hsub cl (hs cl hcl)⟩

/-- The outer walk executed the quotient-record reference guard on this very record. -/
def QuotRecordRefsIn (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (lim : Option Nat) (a : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∃ (h h' : Heap F) (rc ap cp r : SourceValue F) (cs : List (Call F)),
    RCLimRep t bAddr lim h rc ∧ S0.addr h ap a ∧ RepConstant h c cp ∧
    ObsFn Obs.W "KernelClaim::assert_quot_record_refs" [rc, ap, cp] h r h' cs ∧
    ∀ cl ∈ cs, cl ∈ calls

/-- Quotient-record guard observations are retained when a subwalk is included in the run. -/
theorem QuotRecordRefsIn.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hg : QuotRecordRefsIn cs₁ t bAddr lim a c) :
    QuotRecordRefsIn cs₂ t bAddr lim a c := by
  obtain ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hc, ev, hs⟩ := hg
  exact ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hc, ev, fun cl hcl => hsub cl (hs cl hcl)⟩

/-- A record checked and guarded by the walk at its context limit, tagged with its depth. -/
structure TopRec (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) where
  addr : _root_.Address
  rawBytes : ByteArray
  c : Ixon.Constant
  depth : Nat
  hsz : rawBytes.size < 4294967296
  hhashed : Hashed calls rawBytes
  hblake : Address.blake3Pure rawBytes = addr
  hde : Ixon.deConstant rawBytes = .ok c
  hdeExact : Ixon.deConstantExact rawBytes = .ok c
  hchecked :
    (∃ ms, c.info = .muts ms ∧
      ∀ (k : Nat), k < ms.size → MemberCheckedLimAt calls bAddr t addr ms k lim) ∨
    CheckedLimAt calls bAddr t addr lim
  hguard : RecordRefsIn calls t bAddr lim addr c
  hquot : QuotRecordRefsIn calls t bAddr lim addr c

/-- Lift a `TopRec` along call-list inclusion (preserving `depth`). -/
def TopRec.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (r : TopRec cs₁ bAddr t lim) :
    TopRec cs₂ bAddr t lim where
  addr := r.addr
  rawBytes := r.rawBytes
  c := r.c
  depth := r.depth
  hsz := r.hsz
  hhashed := hashed_mono hsub r.hhashed
  hblake := r.hblake
  hde := r.hde
  hdeExact := r.hdeExact
  hchecked := r.hchecked.elim
    (fun ⟨ms, hms, hk⟩ => .inl ⟨ms, hms, fun k hlt => (hk k hlt).mono hsub⟩)
    (fun hc => .inr (hc.mono hsub))
  hguard := r.hguard.mono hsub
  hquot := r.hquot.mono hsub

@[simp]
theorem map_addr_topRec_mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (recs : List (TopRec cs₁ bAddr t lim)) :
    (recs.map (TopRec.mono hsub)).map (·.addr) = recs.map (·.addr) := by
  induction recs with
  | nil => rfl
  | cons r rs ih => simp [TopRec.mono, ih]

/-- A projection record (its owner is its block). -/
def IsProjRec (c : Ixon.Constant) : Prop :=
  (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨ (∃ p, c.info = .cPrj p) ∨
    ∃ p, c.info = .rPrj p

/-- **The records of a walk at `lim` are closed**: the block of a projection record is a record
of the walk at a smaller depth (so not the record's own address); a reference a record uses was
asked about (`RefAllowedIn`), and is a record of the walk at a smaller depth that is no block
record, or is covered at `lim`. -/
def TopRecsClosed {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} (recs : List (TopRec calls bAddr t lim)) : Prop :=
  ∀ r ∈ recs,
    (IsProjRec r.c →
      ∃ r' ∈ recs, r'.addr = Ix.Cert.ownerOf r.addr r.c ∧ r'.depth < r.depth) ∧
    (∀ i ∈ S0.usedRefIdxs r.c, ∀ b, r.c.refs[i]? = some b →
      RefAllowedIn calls t bAddr lim b ∧
      ((NotBlockIn calls b ∧ ∃ r' ∈ recs, r'.addr = b ∧ r'.depth < r.depth) ∨
        CoveredAt t lim b))

theorem TopRecsClosed.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) {recs : List (TopRec cs₁ bAddr t lim)}
    (hcl : TopRecsClosed recs) : TopRecsClosed (recs.map (TopRec.mono hsub)) := by
  intro r_m hr_m
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr_m
  obtain ⟨ho, hu⟩ := hcl r hr
  refine ⟨fun hne => ?_, fun i hi b hb => ?_⟩
  · obtain ⟨r', hr', ha', hlt'⟩ := ho hne
    exact ⟨TopRec.mono hsub r', List.mem_map_of_mem hr', ha', hlt'⟩
  · obtain ⟨hal, hrest⟩ := hu i hi b hb
    refine ⟨hal.mono hsub, ?_⟩
    rcases hrest with ⟨hnb, r', hr', ha', hlt'⟩ | hcov
    · exact .inl ⟨hnb.mono hsub, TopRec.mono hsub r', List.mem_map_of_mem hr', ha', hlt'⟩
    · exact .inr hcov

/-- **The records of `xs` are closed within `ys`**, for `xs` contained in `ys`. -/
def TopRecsClosedIn {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} (xs ys : List (TopRec calls bAddr t lim)) : Prop :=
  ∀ r ∈ xs,
    (IsProjRec r.c →
      ∃ r' ∈ ys, r'.addr = Ix.Cert.ownerOf r.addr r.c ∧ r'.depth < r.depth) ∧
    (∀ i ∈ S0.usedRefIdxs r.c, ∀ b, r.c.refs[i]? = some b →
      RefAllowedIn calls t bAddr lim b ∧
      ((NotBlockIn calls b ∧ ∃ r' ∈ ys, r'.addr = b ∧ r'.depth < r.depth) ∨
        CoveredAt t lim b))

theorem TopRecsClosed.sub {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {xs ys : List (TopRec calls bAddr t lim)}
    (hxy : ∀ x ∈ xs, x ∈ ys) (hc : TopRecsClosed xs) : TopRecsClosedIn xs ys := by
  intro r hr
  obtain ⟨ho, hu⟩ := hc r hr
  refine ⟨fun hne => ?_, fun i hi b hb => ?_⟩
  · obtain ⟨r', hr', ha', hlt'⟩ := ho hne
    exact ⟨r', hxy r' hr', ha', hlt'⟩
  · obtain ⟨hal, hrest⟩ := hu i hi b hb
    refine ⟨hal, ?_⟩
    rcases hrest with ⟨hnb, r', hr', ha', hlt'⟩ | hcov
    · exact .inl ⟨hnb, r', hxy r' hr', ha', hlt'⟩
    · exact .inr hcov

theorem TopRecsClosedIn.union {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {r₁ r₂ : List (TopRec calls bAddr t lim)}
    (h₁ : TopRecsClosedIn r₁ (r₁ ++ r₂)) (h₂ : TopRecsClosedIn r₂ (r₁ ++ r₂)) :
    TopRecsClosed (r₁ ++ r₂) := by
  intro r hr
  rcases List.mem_append.mp hr with hr1 | hr2
  · exact h₁ r hr1
  · exact h₂ r hr2

theorem TopRecsClosed.append {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {r₁ r₂ : List (TopRec calls bAddr t lim)} (h₁ : TopRecsClosed r₁) (h₂ : TopRecsClosed r₂) :
    TopRecsClosed (r₁ ++ r₂) :=
  TopRecsClosed.sub (fun x hx => List.mem_append_left _ hx) h₁ |>.union
    (TopRecsClosed.sub (fun x hx => List.mem_append_right _ hx) h₂)

end IxVM.Refinement.Claim
