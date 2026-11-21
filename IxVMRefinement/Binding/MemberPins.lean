import IxVMRefinement.Ingress.Convert
import IxVMRefinement.Roles.Tables
import IxVMRefinement.Obs.KernelInfer0
import IxVMRefinement.Obs.KernelRoles2
import IxVMRefinement.Obs.KernelRoles3

/-! # The type and recursor counts checked by the binding member validator

The scoped pointer and the pointer compared with the role specification are two
reads of the same loaded member. At the recursors in groups 16 and 17 the
major index and rule prefix are sums of four or three decoded counts. The
bounds accompanying the raw recursor conversion make these natural sums exact.
-/

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM (F)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem level_field {tag : String} {nl ty : SourceValue F} {rest : List (SourceValue F)}
    {r h h' cs} (ev : ObsFn W "KernelInfer::const_num_lvls"
      [.construct kciEnum tag (nl :: ty :: rest)] h r h' cs) : r = nl := by
  cases Obs.«KernelInfer::const_num_lvls».obs ev <;> rename_i shape ret _ _
  all_goals
    have fs := (Value.construct.inj shape).2.2
    simp only [List.cons.injEq] at fs
    exact ret.trans fs.1.symm

private theorem type_field {tag : String} {nl ty : SourceValue F} {rest : List (SourceValue F)}
    {r h h' cs} (ev : ObsFn W "KernelInfer::const_type_of"
      [.construct kciEnum tag (nl :: ty :: rest)] h r h' cs) : r = ty := by
  cases Obs.«KernelInfer::const_type_of».obs ev <;> rename_i shape ret _ _
  all_goals
    have fs := (Value.construct.inj shape).2.2
    simp only [List.cons.injEq] at fs
    exact ret.trans fs.2.1.symm

/-- The scoped check belongs to the caller's trace, and the same term is pinned
against the role type rendered by this validation. The heap inclusions allow
the original bindings and term representation to be reused at both checks. -/
def MemberTypePin (tbl role nl ty : SourceValue F) (h : Heap F) (calls : List (Call F)) : Prop :=
  ∃ (s s' p m m' : Heap F) (u spec result : SourceValue F) (sc tc pc : List (Call F)),
    Heap.Extends h s ∧
    ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] s u s' sc ∧
    (⟨"KernelCheck::validate_expr_well_scoped", [ty, .field 0, nl], s⟩ : Call F) ∈ calls ∧
    Heap.Extends s' p ∧
    ObsFn W "KernelRoleSpec::role_type" [tbl, role] p spec m tc ∧
    ObsFn W "KernelRoles::assert_type_pinned" [ty, spec] m result m' pc

/-- Every path of the member validator checks the loaded term at depth zero
with its own level count, then pins that term against its own role. -/
theorem validateMember_typePin {rc tbl role addr nl ty : SourceValue F}
    {tag : String} {rest : List (SourceValue F)} {h h' result calls}
    (path : Obs.«KernelRoles::validate_member».Path rc tbl role addr
      (.construct kciEnum tag (nl :: ty :: rest)) h result h' calls) :
    MemberTypePin tbl role nl ty h calls := by
  match path with
  | .n0 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc240 := events) ..
  | .n1 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc642 := events) ..
  | .n2 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc754 := events) ..
  | .n3 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc892 := events) ..
  | .n4 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc920 := events) ..
  | .n5 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc947 := events) ..
  | .n6 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc974 := events) ..
  | .n7 (ev14 := safe) (ev_wwewoqqa := before) (ev_boirmbwn := levels)
      (ev_wpzdvuuy := scope) (ev50 := after) (ev70 := render) (ev36 := pin) (hc1001 := events) .. =>
    have scopedType := type_field before
    have scopedLevels := level_field levels
    have pinnedType := type_field after
    rw [scopedType, scopedLevels] at scope events
    rw [pinnedType] at pin
    exact ⟨_, _, _, _, _, _, _, _, _, _, _,
      safe.heap_extends.trans (before.heap_extends.trans levels.heap_extends), scope,
      by rw [events]; simp, after.heap_extends, render, pin⟩

/-- The standard-axiom recursors and their required major index and rule prefix. -/
inductive StdRecPin : Ix.Kernel.Role → Nat → Prop where
  | iff : StdRecPin .iffRec 4
  | nonempty : StdRecPin .nonemptyRec 3

/-- Read the member-kind match table at the selected role number. -/
theorem memberKind_of_table {role : Ix.Kernel.Role} {kind : F}
    (table : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body)
      (roleNum role) = some kind)
    {h h' result calls} (ev : ObsFn W "KernelRoleSpec::role_member_kind" [.field (roleNum role)]
      h result h' calls) : result = .field kind := by
  have d := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_member_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_member_kind, ControlLower.hasControl]) ev
  have params : (IxVM.KernelRoleSpec.role_member_kind.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have body : IxVM.KernelRoleSpec.role_member_kind.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body) := rfl
  rw [params, body] at d
  obtain ⟨_, _, _, _, _, _, arg, sel, out, -⟩ := d.matchValue_inv
  obtain ⟨name, rfl, -⟩ := arg.var_inv
  simp at name
  subst name
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable table sel
  exact out.literal_inv.1

private theorem rec_member_kind {role : Ix.Kernel.Role} {n : Nat} (pin : StdRecPin role n)
    {h h' result calls} (ev : ObsFn W "KernelRoleSpec::role_member_kind" [.field (roleNum role)]
      h result h' calls) : result = .field 2 :=
  memberKind_of_table (by cases pin <;> decide +kernel) ev

private theorem rec_adds {np ni mo mi a b c d e : SourceValue F} {n : F}
    (h₁ : evalBinOp .add np mo = .ok a) (h₂ : evalBinOp .add a mi = .ok b)
    (h₃ : evalBinOp .add b ni = .ok c) (major : c = .field n)
    (h₄ : evalBinOp .add np mo = .ok d) (h₅ : evalBinOp .add d mi = .ok e)
    (prefix' : e = .field n) :
    ∃ (p i m q : F), np = .field p ∧ ni = .field i ∧ mo = .field m ∧ mi = .field q ∧
      p + m + q + i = n ∧ p + m + q = n := by
  obtain ⟨p, m, rfl, rfl⟩ := SubstAux.binop_fields h₁
  obtain rfl := SubstAux.add_ok h₁
  obtain ⟨_, q, -, rfl⟩ := SubstAux.binop_fields h₂
  obtain rfl := SubstAux.add_ok h₂
  obtain ⟨_, i, -, rfl⟩ := SubstAux.binop_fields h₃
  obtain rfl := SubstAux.add_ok h₃
  obtain rfl := SubstAux.add_ok h₄
  obtain rfl := SubstAux.add_ok h₅
  exact ⟨p, i, m, q, rfl, rfl, rfl, rfl, Value.field.inj major, Value.field.inj prefix'⟩

private theorem rec_segment {role : Ix.Kernel.Role} {n : Nat} (pin : StdRecPin role n)
    {np ni mo mi rc tbl addr ci : SourceValue F} {h h' result calls}
    (s : Obs.«KernelRoles::validate_member».Seg_tmveinrh np ni mo mi rc tbl (.field (roleNum role))
      addr ci h result h' calls) :
    ∃ (p i m q : F), np = .field p ∧ ni = .field i ∧ mo = .field m ∧ mi = .field q ∧
      p + m + q + i = (n : F) ∧ p + m + q = (n : F) := by
  cases s with
  | n25 _ _ _ _ _ tag h₁ h₂ h₃ maj h₄ h₅ pre _ _ _ =>
    cases pin with
    | iff => exact rec_adds h₁ h₂ h₃ maj h₄ h₅ pre
    | nonempty => exact absurd (Value.field.inj tag) (by decide)
  | n28 _ _ _ _ _ ne tag h₁ h₂ h₃ maj h₄ h₅ pre _ _ _ =>
    cases pin with
    | iff => exact False.elim (ne rfl)
    | nonempty => exact rec_adds h₁ h₂ h₃ maj h₄ h₅ pre
  | other h25 h28 _ _ _ =>
    cases pin with
    | iff => exact False.elim (h25 rfl)
    | nonempty => exact False.elim (h28 rfl)

/-- A successful validation at either recursor selects a Rec value. Its two
count pins refer to the fields of that very value. -/
theorem validateMember_recCounts {role : Ix.Kernel.Role} {n : Nat} (pin : StdRecPin role n)
    {rc tbl addr ci : SourceValue F} {h h' result calls}
    (path : Obs.«KernelRoles::validate_member».Path rc tbl (.field (roleNum role)) addr ci
      h result h' calls) :
    ∃ (nl ty rules k unsafeFlag block idx : SourceValue F) (p i m q : F),
      ci = .construct kciEnum "Rec"
        [nl, ty, .field p, .field i, .field m, .field q, rules, k, unsafeFlag, block, idx] ∧
      p + m + q + i = (n : F) ∧ p + m + q = (n : F) := by
  match path with
  | .n2 (hv_gruyyoia := shape) (sg_ejvytjpf := s) .. =>
    obtain ⟨p, i, m, q, rfl, rfl, rfl, rfl, major, pre⟩ := rec_segment pin s
    exact ⟨_, _, _, _, _, _, _, p, i, m, q, shape, major, pre⟩
  | .n0 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)
  | .n1 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)
  | .n3 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)
  | .n4 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)
  | .n5 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)
  | .n6 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)
  | .n7 (ev101 := kind) .. => exact absurd (Value.field.inj (rec_member_kind pin kind)) (by decide)

/-- At a converted recursor the two pins are natural equalities. The four
56-bit source bounds also cover a recursor selected by an rPrj load. -/
theorem validateMember_rawRecCounts {role : Ix.Kernel.Role} {n : Nat} (pin : StdRecPin role n)
    {rc tbl addr ci : SourceValue F} {h h' result calls}
    (path : Obs.«KernelRoles::validate_member».Path rc tbl (.field (roleNum role)) addr ci
      h result h' calls)
    {refs recurs univs sharing blobs loadHeap block idx} {record : Ixon.Recursor}
    (raw : Ingress.RawRecrValRep refs recurs univs sharing blobs loadHeap record block idx ci) :
    record.params.toNat + record.motives.toNat + record.minors.toNat + record.indices.toNat = n ∧
    record.params.toNat + record.motives.toNat + record.minors.toNat = n := by
  obtain ⟨-, hp, hi, hm, hq, -, _, _, _, _, -, -, rfl, -⟩ := raw
  obtain ⟨_, _, _, _, _, _, _, p, i, m, q, shape, major, pre⟩ := validateMember_recCounts pin path
  have fs := (Value.construct.inj shape).2.2
  simp only [List.cons.injEq, Value.field.injEq, and_true] at fs
  obtain ⟨_, _, rfl, rfl, rfl, rfl, _⟩ := fs
  rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add] at major
  rw [← Nat.cast_add, ← Nat.cast_add] at pre
  have hn : n < 18446744069414584321 := by cases pin <;> decide
  exact ⟨(RolesAux.val_natCast (by omega)).symm.trans
      ((congrArg ZMod.val major).trans (RolesAux.val_natCast hn)),
    (RolesAux.val_natCast (by omega)).symm.trans
      ((congrArg ZMod.val pre).trans (RolesAux.val_natCast hn))⟩

end IxVM.Refinement.Binding
