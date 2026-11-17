import IxVMRefinement.Claim.TopBase

/-! # No used reference is an inert axiom in force (A2)

`KernelRoles::assert_ref_allowed(rc, b)` refuses a reference bound to an inert role (`sorryAx`
and Lean's compiler-trust axioms) when `role_of(rc, b)` answers the role: always under
`Assumed`, and under `Mk(tbl, n, Nil)` exactly when the role's group is below `n`. So a walk at
a limit that asked about `b` (`RefAllowedIn`) leaves `b` an inert axiom only at a limit `n`
no greater than its role's group (`refAllowed_inert`), and never at the top level of a typing
run (`refAllowed_not_inert_top`: limit `77` or assumed). -/

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

private theorem sub_one_roleNum' {ro : Ix.Kernel.Role} {v : SourceValue F}
    (op : evalBinOp .sub (.field (roleNum ro + 1)) (.field 1) = .ok v) :
    v = .field (roleNum ro) := by
  simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
  exact op.symm

theorem field_eq_of_sub_zero {a b : F}
    (op : evalBinOp .sub (.field a) (.field b) = .ok (.field 0)) : a = b := by
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op
  exact sub_eq_zero.mp op

set_option maxRecDepth 100000 in
/-- An inert role is none of the three standard axioms. -/
theorem inert_not_standard (ro : Ix.Kernel.Role) (hin : ro.inert = true) :
    roleNum ro ≠ (56 : F) ∧ roleNum ro ≠ (57 : F) ∧ roleNum ro ≠ (36 : F) := by
  cases ro <;> first | exact absurd hin (by decide) | decide

/-- **`KernelRoles::axiom_role_standing` at an inert role** is `2`. -/
theorem axiom_role_standing_inert {ro : Ix.Kernel.Role} (hin : ro.inert = true)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::axiom_role_standing" [.field (roleNum ro + 1)] h r h' calls) :
    r = .field 2 := by
  obtain ⟨h56, h57, h36⟩ := inert_not_standard ro hin
  match Obs.«KernelRoles::axiom_role_standing».obs ev with
  | .n0 (hv14 := hv) .. => exact absurd (Value.field.inj hv) (RolesAux.roleNum_add_one_ne_zero ro)
  | .other_n0 (op37 := op37) (ev62 := ev62) (op55 := op55) .. =>
    rw [sub_one_roleNum' op37] at op55
    obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::role_propext».obs ev62
    exact absurd (field_eq_of_sub_zero op55) h56
  | .other_other_n0 (op37 := op37) (ev62 := ev62) (ev97 := ev97) (op90 := op90) .. =>
    rw [sub_one_roleNum' op37] at op90
    obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::role_choice».obs ev97
    exact absurd (field_eq_of_sub_zero op90) h57
  | .other_other_other_n0 (op37 := op37) (ev132 := ev132) (op125 := op125) .. =>
    rw [sub_one_roleNum' op37] at op125
    obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::role_quot_sound».obs ev132
    exact absurd (field_eq_of_sub_zero op125) h36
  | .other_other_other_other_n0 (he179 := he) .. => exact he
  | .other_other_other_other_other (op37 := op37) (ev166 := ev166) (op160 := op160)
      (hne182 := hne) .. =>
    rw [sub_one_roleNum' op37] at ev166
    obtain ⟨rfl, -⟩ := role_spec_kind_inert_eq hin ev166
    simp only [evalBinOp, sub_self, Except.ok.injEq] at op160
    exact absurd op160.symm hne

private theorem table_wf_of_lim {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {h : Heap F} {rc : SourceValue F} (hrc : RCLimRep t bAddr lim h rc) :
    t.wf = true := by
  obtain ⟨_, ⟨hwf, -⟩, -⟩ := hrc.cases
  exact hwf

/-- **`KernelRoles::role_of` at a bound address answers `0` only below the role's group**:
under `Mk(tbl, n, Nil)` with `n` at most the group of the role bound there; never under
`Assumed`. -/
theorem role_of_zero_lim {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {ro : Ix.Kernel.Role} {x_rc x_a : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc) (ha : S0.addr h x_a a)
    (hof : t.addressOf? ro = some a)
    (ev : ObsFn W "KernelRoles::role_of" [x_rc, x_a] h (.field 0) h' calls) :
    ∃ n, lim = some n ∧ n ≤ Ix.SpecDigest.groupOf ro := by
  have hwf := table_wf_of_lim hrc
  obtain ⟨tbl, htbl, ⟨n, rfl, hn, hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::role_of».obs ev with
    | .Mk_n0 (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      obtain ⟨-, -, hlk⟩ := addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨-, hnone⟩ | ⟨ro', hv', -⟩
      · exact absurd hof (hnone ro)
      · exact absurd (Value.field.inj hv') (fun e => RolesAux.roleNum_add_one_ne_zero ro' e.symm)
    | .Mk_other_n1 (hne103 := hne) (he215 := he) .. =>
      exact absurd he.symm hne
    | .Mk_other_other (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) (hne103 := hne)
        (op150 := op150) (ev135 := ev135) (ev121 := ev121) (hne218 := hne218) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨rfl, -⟩ | ⟨ro', rfl, hof'⟩
      · exact absurd rfl hne
      · have hro : ro' = ro :=
          Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
        subst hro
        rw [sub_one_roleNum' op150] at ev135
        obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev135
        obtain ⟨-, -, hlt_iff, -, -⟩ := Lib.less_than_fields_field ev121
        refine ⟨n, rfl, ?_⟩
        by_contra hlt
        apply hne218
        apply hlt_iff.mpr
        rw [RolesAux.val_groupOf, RolesAux.val_natCast (Nat.lt_trans hn (by decide))]
        omega
    | .Assumed (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
  · match Obs.«KernelRoles::role_of».obs ev with
    | .Mk_n0 (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Mk_other_n1 (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Mk_other_other (ld12 := ld12) .. => rw [hl] at ld12; simp at ld12
    | .Assumed (ld12 := ld12) (ev270 := ev270) (ev248 := ev248) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      obtain ⟨-, -, hlk⟩ := addr_index_lookup htbl ha ev270 ev248
      rcases hlk with ⟨-, hnone⟩ | ⟨ro', hv', -⟩
      · exact absurd hof (hnone ro)
      · exact absurd (Value.field.inj hv') (fun e => RolesAux.roleNum_add_one_ne_zero ro' e.symm)

/-- **A reference the walk at `lim` asked about is an inert axiom only below its group**: if
`t` binds an inert role to `b`, the limit is some `n` no greater than the role's group. -/
theorem refAllowed_inert {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr b : _root_.Address} {lim : Option Nat} (hal : RefAllowedIn calls t bAddr lim b)
    {ro : Ix.Kernel.Role} (hin : ro.inert = true) (hof : t.addressOf? ro = some b) :
    ∃ n, lim = some n ∧ n ≤ Ix.SpecDigest.groupOf ro := by
  obtain ⟨h, h', rc, x_b, r, cs, hrc, hb, ev, -⟩ := hal
  have hwf := table_wf_of_lim hrc
  match Obs.«KernelRoles::assert_ref_allowed».obs ev with
  | .n2 (heq61 := heq) .. => exact absurd (Value.field.inj heq) (by decide)
  | .other (ev15 := ev15) (hne67 := hne67) .. =>
    match Obs.«KernelRoles::axiom_standing».obs ev15 with
    | .n0 (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) .. =>
      obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
      obtain ⟨-, -, hlk⟩ := addr_index_lookup htbl hb ev58 ev36
      rcases hlk with ⟨-, hnone⟩ | ⟨ro', hv', -⟩
      · exact absurd hof (hnone ro)
      · exact absurd (Value.field.inj hv') (fun e => RolesAux.roleNum_add_one_ne_zero ro' e.symm)
    | .other_n0 (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) (hne130 := hne)
        (ev147 := ev147) .. =>
      obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl hb ev58 ev36
      rcases hlk with ⟨rfl, -⟩ | ⟨ro', rfl, hof'⟩
      · exact absurd rfl hne
      · have hro : ro' = ro :=
          Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
        subst hro
        have := axiom_role_standing_inert hin ev147
        exact absurd (Value.field.inj this) (by decide)
    | .other_other_n0 (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) (ev147 := ev147)
        (ev191 := ev191) .. =>
      obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
      obtain ⟨rfl, rfl, -⟩ := addr_index_lookup htbl hb ev58 ev36
      have ext := ev147.heap_extends
      exact role_of_zero_lim (hrc.mono ext) (S0.addr_mono ext hb) hof ev191
    | .other_other_other (ev14 := ev14) (ev58 := ev58) (ev36 := ev36) (hne130 := hne)
        (ev147 := ev147) (he220 := he) .. =>
      obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev14
      obtain ⟨rfl, rfl, hlk⟩ := addr_index_lookup htbl hb ev58 ev36
      rcases hlk with ⟨rfl, -⟩ | ⟨ro', rfl, hof'⟩
      · exact absurd rfl hne
      · have hro : ro' = ro :=
          Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
        subst hro
        have h2 := axiom_role_standing_inert hin ev147
        exact absurd (he.trans h2) hne67

/-- **At the top level of a typing run no used reference is an inert axiom** (A2): the walk
at limit `77` or assumed asked about `b`, so `t` binds no inert role to `b`. -/
theorem refAllowed_not_inert_top {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr b : _root_.Address} {lim : Option Nat} (hal : RefAllowedIn calls t bAddr lim b)
    (hlim : lim = some 77 ∨ lim = none) : ¬ IxVM.Consistency.InertAt t b := by
  rintro ⟨ro, hin, hof⟩
  obtain ⟨n, rfl, hle⟩ := refAllowed_inert hal hin hof
  rcases hlim with h77 | hnone
  · cases h77
    have := RoleVal.groupOf_lt_77 ro
    omega
  · cases hnone

end IxVM.Refinement.Claim
