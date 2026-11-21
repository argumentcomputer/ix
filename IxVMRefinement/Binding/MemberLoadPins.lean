import IxVMRefinement.Binding.MemberPins
import Ix.IxVM.Consistency.StatementRel

/-! # Member pins at a role validation and at its recursor's stored reading -/

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM (F)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The six members of groups 16 and 17 with their checked universe arity. -/
inductive StdMemberLevels : Ix.Kernel.Role → Nat → Prop where
  | iff : StdMemberLevels .iff 0
  | iffIntro : StdMemberLevels .iffIntro 0
  | iffRec : StdMemberLevels .iffRec 1
  | nonempty : StdMemberLevels .nonempty 1
  | nonemptyIntro : StdMemberLevels .nonemptyIntro 1
  | nonemptyRec : StdMemberLevels .nonemptyRec 1

private theorem literal_role_table {role answer : F} {arms : List (Generic.Pattern F × Generic.Expr F)}
    {h h' result calls} (table : RolesAux.evalLitTable arms role = some answer)
    (d : ObsExpr W [] [("r", .field role)] (.matchValue (.var "r") arms) h result h' calls) :
    result = .field answer := by
  obtain ⟨_, _, _, _, _, _, arg, sel, out, -⟩ := d.matchValue_inv
  obtain ⟨name, rfl, -⟩ := arg.var_inv
  simp at name
  subst name
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable table sel
  exact out.literal_inv.1

private theorem std_member_kind {role : Ix.Kernel.Role} {n : Nat} (which : StdMemberLevels role n)
    {h h' result calls} (ev : ObsFn W "KernelRoleSpec::role_spec_kind" [.field (roleNum role)]
      h result h' calls) : result = .field 0 := by
  have table : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_spec_kind.body)
      (roleNum role) = some 0 := by cases which <;> decide +kernel
  exact literal_role_table table (ObsFn.function_inv (s := IxVM.source)
    IxVM.KernelRoleSpec.role_spec_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_spec_kind, ControlLower.hasControl]) ev)

private theorem std_member_levels {role : Ix.Kernel.Role} {n : Nat} (which : StdMemberLevels role n)
    {h h' result calls} (ev : ObsFn W "KernelRoleSpec::role_levels" [.field (roleNum role)]
      h result h' calls) : result = .field (n : F) := by
  have table : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.role_levels.body)
      (roleNum role) = some (n : F) := by cases which <;> decide +kernel
  exact literal_role_table table (ObsFn.function_inv (s := IxVM.source)
    IxVM.KernelRoleSpec.role_levels.lookup
    (by simp [IxVM.KernelRoleSpec.role_levels, ControlLower.hasControl]) ev)

private theorem shape_from_levels {ci : SourceValue F} {h h' result calls}
    (ev : ObsFn W "KernelInfer::const_num_lvls" [ci] h result h' calls) :
    ∃ (tag : String) (ty : SourceValue F) (rest : List (SourceValue F)),
      ci = .construct kciEnum tag (result :: ty :: rest) := by
  cases Obs.«KernelInfer::const_num_lvls».obs ev <;> rename_i shape ret _ _
  all_goals rw [ret]; exact ⟨_, _, _, shape⟩

/-- The enclosing role validation ties the member's checked type pointer and
level count to its load at the table's chosen address. Both child traces and
the scoped call belong to the same outer validation. -/
theorem validateRole_stdMember {role : Ix.Kernel.Role} {n : Nat} (which : StdMemberLevels role n)
    {rc tbl : SourceValue F} {h h' result calls}
    (path : Obs.«KernelRoles::validate_role».Path rc tbl (.field (roleNum role)) h result h' calls) :
    ∃ (addr ptr ci ty : SourceValue F) (tag : String) (rest : List (SourceValue F))
      (beforeLoad loaded beforeMember : Heap F) (addrCalls loadCalls memberCalls : List (Call F)),
      ObsFn W "KernelRoles::role_bound_addr" [tbl, .field (roleNum role)] h addr beforeLoad addrCalls ∧
      ObsFn W "Ingress::get_ci" [addr] beforeLoad ptr loaded loadCalls ∧
      (∀ cl ∈ loadCalls, cl ∈ calls) ∧ loadValue loaded ptr = .ok ci ∧
      ci = .construct kciEnum tag (.field (n : F) :: ty :: rest) ∧
      Heap.Extends loaded beforeMember ∧
      Obs.«KernelRoles::validate_member».Path rc tbl (.field (roleNum role)) addr ci beforeMember
        result h' memberCalls ∧ (∀ cl ∈ memberCalls, cl ∈ calls) ∧
      MemberTypePin tbl (.field (roleNum role)) (.field (n : F)) ty beforeMember calls := by
  match path with
  | .n0 (ev14 := lookup) (ev47 := get) (ld41 := ld) (ev80 := count)
      (ev100 := levels) (heq109 := eq) (ev124 := kind) (ev142 := member) (hc183 := events) .. =>
    have level := eq.trans (std_member_levels which levels)
    obtain ⟨tag, ty, rest, shape⟩ := shape_from_levels count
    rw [level] at shape
    have mp := Obs.«KernelRoles::validate_member».obs member
    have typed := mp
    rw [shape] at typed
    obtain ⟨s, s', p, m, m', u, spec, out, sc, tc, pc, ext, scope, entry, later, render, pin⟩ :=
      validateMember_typePin typed
    exact ⟨_, _, _, ty, tag, rest, _, _, _, _, _, _, lookup, get,
      fun cl hm => by rw [events]; simp [hm], ld, shape,
      count.heap_extends.trans (levels.heap_extends.trans kind.heap_extends), mp,
      fun cl hm => by rw [events]; simp [hm],
      s, s', p, m, m', u, spec, out, sc, tc, pc, ext, scope,
      by rw [events]; simp [entry], later, render, pin⟩
  | .n1 (ev124 := kind) .. => exact absurd (Value.field.inj (std_member_kind which kind)) (by decide)
  | .n2 (ev124 := kind) .. => exact absurd (Value.field.inj (std_member_kind which kind)) (by decide)
  | .n3 (ev124 := kind) .. => exact absurd (Value.field.inj (std_member_kind which kind)) (by decide)
  | .n4 (ev124 := kind) .. => exact absurd (Value.field.inj (std_member_kind which kind)) (by decide)
  | .n5 (ev124 := kind) .. => exact absurd (Value.field.inj (std_member_kind which kind)) (by decide)

open IxVM.Consistency in
/-- A stored reading of the decoded recursor has precisely the two natural
counts required by stdAxiomOk. Its level parameters and type are exactly the
ones named by the reading of that recursor's family. -/
theorem validateMember_storedRecCounts {role : Ix.Kernel.Role} {n : Nat} (pin : StdRecPin role n)
    {rc tbl addr ci : SourceValue F} {h h' result calls}
    (path : Obs.«KernelRoles::validate_member».Path rc tbl (.field (roleNum role)) addr ci
      h result h' calls)
    {refs recurs univs sharing blobs loadHeap block idx} {record : Ixon.Recursor}
    (raw : Ingress.RawRecrValRep refs recurs univs sharing blobs loadHeap record block idx ci)
    {t store blob src self name declared stored}
    (read : RecReads t store blob src self name record declared) (kept : StoredAs stored declared) :
    ∃ cv rules, stored = .recInfo cv n n rules ∧ cv.name = name ∧
      ∃ tyP kF B i ind ty,
        (exprReader t blob src id self).read record.typ = .ok tyP ∧
        familyKey record tyP = some kF ∧ IndKeyAt t store kF B i ind ∧
        cv.levelParams = Ix.Kernel.Reader.recLps (decide (record.lvls.toNat = ind.lvls.toNat + 1))
          (List.range ind.lvls.toNat) ∧
        (exprReader t blob src (Ix.Kernel.Reader.recParam cv.levelParams) self).read record.typ =
          .ok ty ∧ Annotates cv.type ty := by
  obtain ⟨major, pre⟩ := validateMember_rawRecCounts pin path raw
  obtain ⟨tyP, ty, kF, _, B, _, i, _, ind, _, ps, _, pos, fam, origin, _, _, levels, named,
    _, _, rfl⟩ := read
  rw [major, pre] at kept
  cases stored with
  | recInfo cv m p rules =>
    obtain ⟨⟨hn, hps, ann⟩, hm, hp, _⟩ := kept
    change cv.levelParams = ps at hps
    exact ⟨cv, rules, by rw [hm, hp], hn, tyP, kF, B, i, ind, ty, pos, fam, origin,
      hps.trans levels, hps.symm ▸ named, ann⟩
  | _ => exact False.elim kept.2

end IxVM.Refinement.Binding
