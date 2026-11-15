import IxVMRefinement.RoleVal.LookupSpec
import IxVMRefinement.Claim.RoleTable
import IxVMRefinement.Claim.Walk

/-! # Structural call and walk extraction for `KernelRoles::group_admit` and role lookups

Refines the on-demand group admission and transitive constant-walk structure of `KernelRoles`:
* `group_admit_spec` / `group_admit_nat_spec` (under `TableRep`) and
  `group_admit_full_spec` / `group_admit_full_nat_spec` (under `Claim.TableFullRep`):
  extracts the `Ingress::get_ci` loads and `KernelClaim::run_check_transitive` sub-derivations
  (and closed `Claim.WalkedRec` lists) executed across all bound addresses (`roleWalksBound`)
  and `.proof thm` evidence entries of group `g` and recursively `group_admit_needs`
  (`GroupReachable`);
* `role_used_implicitly_spec` / `role_used_implicitly_full_spec`,
  `role_addr_admit_spec` / `role_addr_full_admit_spec`, and
  `role_of_admit_spec` / `role_of_full_admit_spec`:
  extracts the bound address, limit guard `groupOf ro < n`, `group_admit` call, and
  `run_check_transitive` walk triggered when roles are queried under `RCRep` / `Claim.RCFullRep`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

section GroupAdmit

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Validation limit, schedule groups, and reachability -/

/-- Exact group validation limit computed by `KernelRoles::group_validation_limit(g)`. -/
def groupValLimit (g : Nat) : Nat :=
  if g < 38 then g else if g < 46 then 38 else 46

theorem groupValLimit_le (g : Nat) : groupValLimit g ≤ 46 := by
  unfold groupValLimit
  split <;> try omega
  split <;> omega

theorem groupValLimit_lt_u32 (g : Nat) : groupValLimit g < 4294967296 :=
  Nat.lt_of_le_of_lt (groupValLimit_le g) (by decide)

private theorem natCast_val_eq (x : F) : ((ZMod.val x : Nat) : F) = x := by
  apply ZMod.val_injective
  exact RolesAux.val_natCast (ZMod.val_lt x)

/-- **`KernelRoles::group_validation_limit(x_g)`**: forces `x_g = .field (g : F)` with `g < 2^32`
and returns `.field (groupValLimit g : F)` without modifying the heap. -/
theorem group_validation_limit_exact {x_g r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::group_validation_limit" [x_g] h r h' calls) :
    h' = h ∧ ∃ g : Nat, g < 4294967296 ∧ x_g = .field (g : F) ∧
      r = .field (groupValLimit g : F) := by
  rcases Obs.«KernelRoles::group_validation_limit».obs ev with
    ⟨v1, m2, _, m16, _, ev14, ev29, rfl, rfl, -⟩ |
    ⟨v1, m2, _, v15, m16, _, v58, m59, _, m73, _, ev14, ev29, hne, ev71, ev86, rfl, rfl, -⟩ |
    ⟨v1, m2, _, v15, m16, _, v58, m59, _, v72, m73, _, ev14, ev29, hne1, ev71, ev86, hne2, rfl, rfl, -⟩
  · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev14
    obtain ⟨gf, bf, rfl, hbf, hgf_lt, _, hr29, rfl⟩ := Lib.less_than_fields_spec ev29
    injection hbf with hbf_eq
    subst hbf_eq
    have h38 : ZMod.val (38 : F) = 38 := RolesAux.val_natCast (by decide)
    have hlt38 : gf.val < 38 := by
      by_cases hc : gf.val < 38
      · exact hc
      · simp only [h38, hc, ↓reduceIte] at hr29
        exact absurd (Value.field.inj hr29) one_ne_zero
    refine ⟨rfl, gf.val, hgf_lt, congrArg Value.field (natCast_val_eq gf).symm, ?_⟩
    unfold groupValLimit
    simp only [hlt38, ↓reduceIte, natCast_val_eq]
  · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev14
    obtain ⟨gf, bf, rfl, hbf, hgf_lt, _, hr29, rfl⟩ := Lib.less_than_fields_spec ev29
    injection hbf with hbf_eq
    subst hbf_eq
    have h38 : ZMod.val (38 : F) = 38 := RolesAux.val_natCast (by decide)
    have hge38 : ¬ gf.val < 38 := fun hc => by
      simp only [h38, hc, ↓reduceIte] at hr29
      exact hne hr29
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_equation_group».obs ev71
    obtain ⟨_, _, hlt46_iff, _, rfl⟩ := Lib.less_than_fields_field ev86
    have h46 : ZMod.val (46 : F) = 46 := RolesAux.val_natCast (by decide)
    have hlt46 : gf.val < 46 := by
      have h := hlt46_iff.mp rfl
      rwa [h46] at h
    refine ⟨rfl, gf.val, hgf_lt, congrArg Value.field (natCast_val_eq gf).symm, ?_⟩
    unfold groupValLimit
    simp only [hge38, hlt46, ↓reduceIte]
    rfl
  · obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_well_founded_group».obs ev14
    obtain ⟨gf, bf, rfl, hbf, hgf_lt, _, hr29, rfl⟩ := Lib.less_than_fields_spec ev29
    injection hbf with hbf_eq
    subst hbf_eq
    have h38 : ZMod.val (38 : F) = 38 := RolesAux.val_natCast (by decide)
    have hge38 : ¬ gf.val < 38 := fun hc => by
      simp only [h38, hc, ↓reduceIte] at hr29
      exact hne1 hr29
    obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::first_equation_group».obs ev71
    obtain ⟨_, _, hlt46_iff, _, rfl⟩ := Lib.less_than_fields_field ev86
    have h46 : ZMod.val (46 : F) = 46 := RolesAux.val_natCast (by decide)
    have hge46 : ¬ gf.val < 46 := fun hc => by
      have hc' : gf.val < ZMod.val (46 : F) := by rwa [h46]
      exact hne2 (hlt46_iff.mpr hc')
    refine ⟨rfl, gf.val, hgf_lt, congrArg Value.field (natCast_val_eq gf).symm, ?_⟩
    unfold groupValLimit
    simp only [hge38, hge46, ↓reduceIte]
    rfl

theorem group_validation_limit_of_nat {g : Nat} (hg : g < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::group_validation_limit" [.field (g : F)] h r h' calls) :
    h' = h ∧ r = .field (groupValLimit g : F) := by
  obtain ⟨rfl, g', hg', hxg, hr⟩ := group_validation_limit_exact ev
  have hval := congrArg ZMod.val (Value.field.inj hxg)
  rw [RolesAux.val_natCast (Nat.lt_trans hg (by decide)),
    RolesAux.val_natCast (Nat.lt_trans hg' (by decide))] at hval
  subst hval
  exact ⟨rfl, hr⟩

/-- Roles belonging to group `g` (`[]` for `g ≥ 77`, matching `KernelRoleSpec::group_roles`). -/
def groupRoles (g : Nat) : List Ix.Kernel.Role :=
  Ix.SpecDigest.groups.getD g []

/-- Roles directly needed by group `g` (`[]` for `g ≥ 77`, matching `KernelRoleSpec::group_needs`). -/
def groupNeededRoles (g : Nat) : List Ix.Kernel.Role :=
  if g < 77 then Ix.SpecDigest.groupNeeds (groupRoles g) else []

theorem groups_length : Ix.SpecDigest.groups.length = 77 := by decide

theorem groupRoles_eq_getElem {g : Nat} (hg : g < 77) :
    groupRoles g = Ix.SpecDigest.groups[g]'(by rw [groups_length]; exact hg) := by
  unfold groupRoles
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [groups_length]; exact hg)]
  rfl

set_option maxRecDepth 100000 in
theorem groupOf_lt_77 (ro : Ix.Kernel.Role) : Ix.SpecDigest.groupOf ro < 77 := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
theorem mem_groupRoles_groupOf (ro : Ix.Kernel.Role) :
    ro ∈ groupRoles (Ix.SpecDigest.groupOf ro) := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
private theorem groupNeededRoles_lt_fin :
    ∀ i : Fin 77,
      ((groupNeededRoles i.val).all fun ro => decide (Ix.SpecDigest.groupOf ro < i.val)) = true := by
  decide +kernel

theorem groupNeeds_groupOf_lt {g : Nat} {ro : Ix.Kernel.Role}
    (hm : ro ∈ groupNeededRoles g) : Ix.SpecDigest.groupOf ro < g := by
  unfold groupNeededRoles at hm
  by_cases hg : g < 77
  · have hfin := groupNeededRoles_lt_fin ⟨g, hg⟩
    simp only [groupNeededRoles, hg, ↓reduceIte] at hfin
    simp only [hg, ↓reduceIte] at hm
    have hall := List.all_eq_true.mp hfin ro hm
    exact of_decide_eq_true hall
  · simp only [hg, ↓reduceIte] at hm
    cases hm

/-- Reflexive-transitive group dependency relation induced by `KernelRoles::group_admit_needs`. -/
inductive GroupReachable : Nat → Nat → Prop where
  | refl (g : Nat) : GroupReachable g g
  | step {g g' : Nat} {ro : Ix.Kernel.Role}
      (hm : ro ∈ groupNeededRoles g)
      (hr : GroupReachable (Ix.SpecDigest.groupOf ro) g') :
      GroupReachable g g'

theorem GroupReachable.trans {g₁ g₂ g₃ : Nat}
    (h₁ : GroupReachable g₁ g₂) (h₂ : GroupReachable g₂ g₃) :
    GroupReachable g₁ g₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hm _ ih => exact .step hm (ih h₂)

theorem GroupReachable.le {g g' : Nat} (hr : GroupReachable g g') : g' ≤ g := by
  induction hr with
  | refl => exact Nat.le_refl _
  | step hm _ ih => exact Nat.le_of_lt (Nat.lt_of_le_of_lt ih (groupNeeds_groupOf_lt hm))

/-! ## Role classification and well-formed evidence coverage -/

/-- Specification dispatch tag matching `KernelRoleSpec::role_spec_kind`. -/
def roleSpecKindNat (ro : Ix.Kernel.Role) : Nat :=
  match ro.spec (md := .anon) with
  | .block .. => 0
  | .anchor .. => 1
  | .ops .. => 2
  | .axiom .. => if ro.inert then 4 else 3
  | .eqns .. => 5

/-- Whether `ro` is one of the five `Quot` roles (`member_kind ∈ 3..7`). -/
def isQuotRole : Ix.Kernel.Role → Bool
  | .quot | .quotMk | .quotLift | .quotInd | .quotSound => true
  | _ => false

/-- Roles whose bound address `a` is walked via `KernelClaim::run_check_transitive(rc, a)`
during `KernelRoles::validate_role(rc, tbl, r)`: non-`Quot` block members, `.ops`, and `.eqns`. -/
def roleWalksBound (ro : Ix.Kernel.Role) : Bool :=
  match ro.spec (md := .anon) with
  | .block .. => !isQuotRole ro
  | .ops .. | .eqns .. => true
  | _ => false

/-- Roles carrying equation evidence in `validate_role` (`.ops` and `.eqns`). -/
def roleHasEquations (ro : Ix.Kernel.Role) : Bool :=
  match ro.spec (md := .anon) with
  | .ops .. | .eqns .. => true
  | _ => false

set_option maxRecDepth 100000 in
private theorem evidenceAllowed_isEmpty_eq (ro : Ix.Kernel.Role) :
    ((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed.isEmpty = !roleHasEquations ro := by
  cases ro <;> decide

/-- A table passing `RoleTable.check` has duplicate-free evidence keys, and every evidence entry
belongs to a role with `roleHasEquations ro = true`. -/
theorem check_evidence_nodup_and_eqns {t : Ix.Kernel.RoleTable} (hchk : t.check = .ok ()) :
    (t.evidence.toList.map (·.1)).Nodup ∧
    ∀ p ∈ t.evidence.toList, roleHasEquations p.1 = true := by
  unfold Ix.Kernel.RoleTable.check at hchk
  by_cases hv : (t.version == Ix.Kernel.specVersion) = true
  case neg =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at hchk
    obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hchk
    first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
  by_cases hbn : (List.map (fun x => x.1) t.bound.toList).Nodup
  case neg =>
    simp only [hv, hbn, ↓reduceIte] at hchk
    obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hchk
    first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
  cases hfr : Ix.Kernel.RoleTable.firstRepeat (List.map (fun x => x.2) t.bound.toList) with
  | some a0 =>
    simp only [hv, hbn, hfr, ↓reduceIte] at hchk
    obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hchk
    first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
  | none =>
    simp only [hv, hbn, hfr, ↓reduceIte] at hchk
    obtain ⟨_, _, hchk2⟩ := RoleClosure.except_bind_ok hchk
    by_cases hnd : (List.map (fun x => x.1) t.evidence.toList).Nodup
    case neg =>
      simp only [hnd, ↓reduceIte] at hchk2
      obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hchk2
      first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
    simp only [hnd, ↓reduceIte] at hchk2
    refine ⟨hnd, ?_⟩
    obtain ⟨u, hev, -⟩ := RoleClosure.except_bind_ok hchk2
    cases u
    rw [← Array.forIn_toList] at hev
    have hall := RoleClosure.forIn_ok_all hev (by
      intro p _ hst
      rcases p with ⟨r, es⟩
      dsimp only at hst
      by_cases hrc : (List.map (fun x => x.1) t.bound.toList).contains r = true
      case neg =>
        simp only [hrc, Bool.false_eq_true, ↓reduceIte] at hst
        obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hst
        first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
      simp only [hrc, ↓reduceIte] at hst
      by_cases hke : ((Ix.Kernel.Role.spec (md := .anon)) r).evidenceAllowed.isEmpty = true
      case pos =>
        simp only [hke, ↓reduceIte] at hst
        obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hst
        first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
      simp only [hke, Bool.false_eq_true, ↓reduceIte] at hst
      split at hst
      · simp only [pure, Except.pure, Except.ok.injEq] at hst
        exact hst.symm
      · obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hst
        first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1)
    intro p hp
    have hp_ok := hall p hp
    rcases p with ⟨r, es⟩
    dsimp only at hp_ok ⊢
    by_cases hrc : (List.map (fun x => x.1) t.bound.toList).contains r = true
    case neg =>
      simp only [hrc, Bool.false_eq_true, ↓reduceIte] at hp_ok
      obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hp_ok
      first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
    simp only [hrc, ↓reduceIte] at hp_ok
    by_cases hreq : roleHasEquations r = true
    · exact hreq
    · have hfalse : roleHasEquations r = false := Bool.eq_false_iff.mpr hreq
      have hemp : ((Ix.Kernel.Role.spec (md := .anon)) r).evidenceAllowed.isEmpty = true := by
        rw [evidenceAllowed_isEmpty_eq, hfalse]
        rfl
      simp only [hemp, ↓reduceIte] at hp_ok
      obtain ⟨_, h1, -⟩ := RoleClosure.except_bind_ok hp_ok
      first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1

private theorem eq_of_mem_nodup_fst {α β : Type} :
    ∀ {l : List (α × β)} {k : α} {v₁ v₂ : β},
      (l.map (·.1)).Nodup → (k, v₁) ∈ l → (k, v₂) ∈ l → v₁ = v₂
  | [], _, _, _, _, h1, _ => by cases h1
  | (a, b) :: ls, k, v₁, v₂, hnd, h1, h2 => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with heq1 | ht1
    · injection heq1 with hk hv1
      subst hk hv1
      rcases List.mem_cons.mp h2 with heq2 | ht2
      · injection heq2 with _ hv2
        exact hv2.symm
      · exact absurd (List.mem_map_of_mem (f := (·.1)) ht2) hnd.1
    · rcases List.mem_cons.mp h2 with heq2 | ht2
      · injection heq2 with hk _
        subst hk
        exact absurd (List.mem_map_of_mem (f := (·.1)) ht1) hnd.1
      · exact eq_of_mem_nodup_fst hnd.2 ht1 ht2

theorem evidence_eq_of_wf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {ro : Ix.Kernel.Role} {arr₁ arr₂ : Array (Ix.Kernel.Evidence _root_.Address)}
    (h₁ : (ro, arr₁) ∈ t.evidence.toList) (h₂ : (ro, arr₂) ∈ t.evidence.toList) :
    arr₁ = arr₂ :=
  eq_of_mem_nodup_fst (check_evidence_nodup_and_eqns (RoleClosure.check_ok_of_wf hwf)).1 h₁ h₂

theorem evidence_roleHasEquations_of_wf {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {ro : Ix.Kernel.Role} {arr : Array (Ix.Kernel.Evidence _root_.Address)}
    (hm : (ro, arr) ∈ t.evidence.toList) :
    roleHasEquations ro = true :=
  (check_evidence_nodup_and_eqns (RoleClosure.check_ok_of_wf hwf)).2 (ro, arr) hm

/-! ## Pure AST evaluators for `KernelRoleSpec` match tables -/

private def evalNatLitMatchNat (k : Nat) :
    List (Generic.Pattern F × Generic.Expr F) → Option Nat
  | (.literal c, .literal v) :: rest =>
    if k == ZMod.val c then some (ZMod.val v) else evalNatLitMatchNat k rest
  | (.wildcard, .literal v) :: _ => some (ZMod.val v)
  | _ => none

private theorem selectArm_natLitMatch {arms : List (Generic.Pattern F × Generic.Expr F)}
    {x : F} {m : Nat}
    (ht : evalNatLitMatchNat (ZMod.val x) arms = some m)
    {h : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (hsel : selectArm W [] h (.field x) arms = Except.ok (some (bs, body))) :
    bs = [] ∧ body = .literal (m : F) := by
  induction arms with
  | nil => simp [evalNatLitMatchNat] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, expr⟩
    cases pat with
    | literal c =>
      cases expr with
      | literal v =>
        simp only [evalNatLitMatchNat] at ht
        by_cases hxc_b : (ZMod.val x == ZMod.val c) = true
        · rw [ite_eq_left hxc_b] at ht
          injection ht with hm_eq
          have hxc : x = c := ZMod.val_injective _ (beq_iff_eq.mp hxc_b)
          subst hxc
          rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, _⟩
          · obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal x) mt
            refine ⟨rfl, congrArg Generic.Expr.literal ?_⟩
            rw [← hm_eq, natCast_val_eq]
          · exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal x) nm)
        · rw [ite_eq_right hxc_b] at ht
          have hxc_ne : x ≠ c := fun e => hxc_b (beq_iff_eq.mpr (congrArg ZMod.val e))
          rcases selectArm_cons_inv hsel with ⟨mt, _⟩ | ⟨_, hsel'⟩
          · obtain ⟨hv, _⟩ := MatchesConst.some_inv (MatchesConst.literal c) mt
            exact absurd (Value.field.inj hv) hxc_ne
          · exact ih ht hsel'
      | _ => simp [evalNatLitMatchNat] at ht
    | wildcard =>
      cases expr with
      | literal v =>
        simp only [evalNatLitMatchNat, Option.some.injEq] at ht
        rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, _⟩
        · refine ⟨matchPattern_wildcard_inv mt, congrArg Generic.Expr.literal ?_⟩
          rw [← ht, natCast_val_eq]
        · exact (matchPattern_wildcard_none nm).elim
      | _ => simp [evalNatLitMatchNat] at ht
    | _ => simp [evalNatLitMatchNat] at ht

set_option maxRecDepth 100000 in
private theorem role_spec_kind_table (ro : Ix.Kernel.Role) :
    evalNatLitMatchNat ro.idx (RolesAux.matchArms IxVM.KernelRoleSpec.role_spec_kind.body) =
      some (roleSpecKindNat ro) := by
  cases ro <;> decide

theorem role_spec_kind_spec {ro : Ix.Kernel.Role} {r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_spec_kind" [.field (roleNum ro)] h r h' calls) :
    r = .field (roleSpecKindNat ro : F) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_spec_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_spec_kind, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.role_spec_kind.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_spec_kind.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_spec_kind.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have ht : evalNatLitMatchNat (ZMod.val (roleNum ro))
      (RolesAux.matchArms IxVM.KernelRoleSpec.role_spec_kind.body) =
      some (roleSpecKindNat ro) := by
    rw [RolesAux.val_roleNum]
    exact role_spec_kind_table ro
  obtain ⟨rfl, rfl⟩ := selectArm_natLitMatch ht sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
private theorem role_member_kind_lt3_table (ro : Ix.Kernel.Role)
    (h0 : roleSpecKindNat ro = 0) (hw : roleWalksBound ro = true) :
    (match evalNatLitMatchNat ro.idx (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body) with
     | some mk => decide (mk < 3)
     | none => false) = true := by
  cases ro <;> first | exact absurd h0 (by decide) | exact absurd hw (by decide) | decide

theorem role_member_kind_lt3_of_walks {ro : Ix.Kernel.Role}
    (h0 : roleSpecKindNat ro = 0) (hw : roleWalksBound ro = true)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::role_member_kind" [.field (roleNum ro)] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ r = .field 1 ∨ r = .field 2) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_member_kind.lookup
    (by simp [IxVM.KernelRoleSpec.role_member_kind, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.role_member_kind.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_member_kind.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have htab := role_member_kind_lt3_table ro h0 hw
  cases hm : evalNatLitMatchNat ro.idx
      (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body) with
  | none => rw [hm] at htab; cases htab
  | some mk =>
    rw [hm] at htab
    have hlt3 : mk < 3 := of_decide_eq_true htab
    have ht : evalNatLitMatchNat (ZMod.val (roleNum ro))
        (RolesAux.matchArms IxVM.KernelRoleSpec.role_member_kind.body) = some mk := by
      rw [RolesAux.val_roleNum]
      exact hm
    obtain ⟨rfl, rfl⟩ := selectArm_natLitMatch ht sel8
    obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
    refine ⟨rfl, ?_⟩
    interval_cases mk
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

set_option maxRecDepth 100000 in
private theorem op_equation_count_table_pos (ro : Ix.Kernel.Role)
    (h2 : roleSpecKindNat ro = 2) :
    (match evalNatLitMatchNat ro.idx (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body) with
     | some k => decide (0 < k ∧ k < 10)
     | none => false) = true := by
  cases ro <;> first | exact absurd h2 (by decide) | decide

theorem op_equation_count_pos {ro : Ix.Kernel.Role} (h2 : roleSpecKindNat ro = 2)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::op_equation_count" [.field (roleNum ro)] h r h' calls) :
    h' = h ∧ ∃ k : Nat, 0 < k ∧ k < 10 ∧ r = .field (k : F) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_equation_count.lookup
    (by simp [IxVM.KernelRoleSpec.op_equation_count, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.op_equation_count.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.op_equation_count.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have htab := op_equation_count_table_pos ro h2
  cases hm : evalNatLitMatchNat ro.idx
      (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body) with
  | none => rw [hm] at htab; cases htab
  | some k =>
    rw [hm] at htab
    obtain ⟨hk0, hk10⟩ := of_decide_eq_true htab
    have ht : evalNatLitMatchNat (ZMod.val (roleNum ro))
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body) = some k := by
      rw [RolesAux.val_roleNum]
      exact hm
    obtain ⟨rfl, rfl⟩ := selectArm_natLitMatch ht sel8
    obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
    exact ⟨rfl, k, hk0, hk10, rfl⟩

set_option maxRecDepth 100000 in
private theorem eqns_equation_count_table_pos (ro : Ix.Kernel.Role)
    (h5 : roleSpecKindNat ro = 5) :
    (match evalNatLitMatchNat ro.idx (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) with
     | some k => decide (0 < k ∧ k < 10)
     | none => false) = true := by
  cases ro <;> first | exact absurd h5 (by decide) | decide

theorem eqns_equation_count_pos {ro : Ix.Kernel.Role} (h5 : roleSpecKindNat ro = 5)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::eqns_equation_count" [.field (roleNum ro)] h r h' calls) :
    h' = h ∧ ∃ k : Nat, 0 < k ∧ k < 10 ∧ r = .field (k : F) := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.eqns_equation_count.lookup
    (by simp [IxVM.KernelRoleSpec.eqns_equation_count, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.eqns_equation_count.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.eqns_equation_count.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have htab := eqns_equation_count_table_pos ro h5
  cases hm : evalNatLitMatchNat ro.idx
      (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) with
  | none => rw [hm] at htab; cases htab
  | some k =>
    rw [hm] at htab
    obtain ⟨hk0, hk10⟩ := of_decide_eq_true htab
    have ht : evalNatLitMatchNat (ZMod.val (roleNum ro))
        (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) = some k := by
      rw [RolesAux.val_roleNum]
      exact hm
    obtain ⟨rfl, rfl⟩ := selectArm_natLitMatch ht sel8
    obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
    exact ⟨rfl, k, hk0, hk10, rfl⟩

/-! ### Linked-list AST decoder for `group_roles` and `group_needs` -/

private def repRoleIdx (_ : Heap F) (n : Nat) (v : SourceValue F) : Prop :=
  v = .field (n : F)

private theorem repRoleIdx_heapMono₂ : HeapMono₂ repRoleIdx :=
  fun _ _ _ _ _ h => h

private def repRoleNum (_ : Heap F) (ro : Ix.Kernel.Role) (v : SourceValue F) : Prop :=
  v = .field (roleNum ro)

private theorem repRoleNum_heapMono₂ : HeapMono₂ repRoleNum :=
  fun _ _ _ _ _ h => h

private theorem repList_map_idx_to_role :
    ∀ {rs : List Ix.Kernel.Role} {h : Heap F} {p : SourceValue F},
      RepList Obs.Names.«Lists::Node<Field>» repRoleIdx h (rs.map Ix.Kernel.Role.idx) p →
      RepList Obs.Names.«Lists::Node<Field>» repRoleNum h rs p
  | [], _, _, .nil cell => .nil cell
  | _ :: _, _, _, .cons cell rh rt => .cons cell rh (repList_map_idx_to_role rt)

private def isFieldListCtor (ctorWant : String) :
    Generic.Expr F → Option (List (Generic.Expr F))
  | .construct name args ctor es =>
    if ctor == ctorWant && instanceName [] name args == Obs.Names.«Lists::Node<Field>» then
      some es
    else none
  | .constructAs _ t ctor es =>
    if ctor == ctorWant && constructorName [] t == Obs.Names.«Lists::Node<Field>» then
      some es
    else none
  | _ => none

private theorem isFieldListCtor_sound {ctorWant : String} {inner : Generic.Expr F}
    {es : List (Generic.Expr F)} (hc : isFieldListCtor ctorWant inner = some es)
    {locals : Environment F Nat} {h : Heap F} {v : SourceValue F} {h' : Heap F}
    {calls : List (Call F)}
    (d : ObsExpr W [] locals inner h v h' calls) :
    ∃ vs, ObsArgs W [] locals es h vs h' calls ∧
      v = .construct Obs.Names.«Lists::Node<Field>» ctorWant vs := by
  cases inner with
  | construct name args ctor es' =>
    simp only [isFieldListCtor] at hc
    split at hc
    case isTrue hcond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨rfl, hinst⟩ := hcond
      injection hc with hes
      subst hes
      obtain ⟨vs, a, hres⟩ := d.construct_inv
      rw [hinst] at hres
      exact ⟨vs, a, hres⟩
    case isFalse => cases hc
  | constructAs ps t ctor es' =>
    simp only [isFieldListCtor] at hc
    split at hc
    case isTrue hcond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨rfl, hctor⟩ := hcond
      injection hc with hes
      subst hes
      obtain ⟨vs, a, hres⟩ := d.constructAs_inv
      rw [hctor] at hres
      exact ⟨vs, a, hres⟩
    case isFalse => cases hc
  | _ => simp [isFieldListCtor] at hc

private def decodeNatListExpr : Nat → Generic.Expr F → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .builtin (.ascribe _) [e] => decodeNatListExpr fuel e
  | fuel + 1, .store inner =>
    match isFieldListCtor "Nil" inner with
    | some [] => some []
    | _ =>
      match isFieldListCtor "Cons" inner with
      | some [.literal x, tail] => (decodeNatListExpr fuel tail).map (ZMod.val x :: ·)
      | _ => none
  | _, _ => none

private theorem decodeNatListExpr_sound :
    ∀ (fuel : Nat) {e : Generic.Expr F} {ns : List Nat}
      (hd : decodeNatListExpr fuel e = some ns)
      {locals : Environment F Nat} {h : Heap F} {r : SourceValue F} {h' : Heap F}
      {calls : List (Call F)}
      (d : ObsExpr W [] locals e h r h' calls),
      Heap.Extends h h' ∧
      RepList Obs.Names.«Lists::Node<Field>» repRoleIdx h' ns r
  | 0, _, _, hd, _, _, _, _, _, _ => by simp [decodeNatListExpr] at hd
  | fuel + 1, e, ns, hd, locals, h, r, h', calls, d => by
    cases e with
    | builtin op es =>
      cases op with
      | ascribe t =>
        cases es with
        | nil => simp [decodeNatListExpr] at hd
        | cons e0 es1 =>
          cases es1 with
          | nil =>
            simp only [decodeNatListExpr] at hd
            obtain ⟨vs, a, ap⟩ := d.builtin_inv
            obtain ⟨v0, vs1, m1, _, _, rfl, d0, a1, _⟩ := a.cons_inv
            obtain ⟨rfl, rfl, _⟩ := a1.nil_inv
            obtain rfl := Builtin.ascribe_inv ap
            exact decodeNatListExpr_sound fuel hd d0
          | cons _ _ => simp [decodeNatListExpr] at hd
      | _ => simp [decodeNatListExpr] at hd
    | store inner =>
      simp only [decodeNatListExpr] at hd
      obtain ⟨vin, min, din, rfl, rfl⟩ := d.store_inv
      cases hnil : isFieldListCtor "Nil" inner with
      | some es_nil =>
        rw [hnil] at hd
        cases es_nil with
        | nil =>
          simp only [Option.some.injEq] at hd
          subst hd
          obtain ⟨vs, a, hvin⟩ := isFieldListCtor_sound hnil din
          obtain ⟨rfl, rfl, _⟩ := a.nil_inv
          subst hvin
          rw [Value.type]
          exact ⟨Heap.Extends.snoc _ _,
            Lib.rep_store_nil (en := Obs.Names.«Lists::Node<Field>») (R := repRoleIdx) min⟩
        | cons _ _ =>
          cases hcons : isFieldListCtor "Cons" inner with
          | none => rw [hcons] at hd; cases hd
          | some es_cons =>
            obtain ⟨_, _, h1⟩ := isFieldListCtor_sound hnil din
            obtain ⟨_, _, h2⟩ := isFieldListCtor_sound hcons din
            exact (RolesAux.construct_ctor_ne (by decide) (h1.symm.trans h2)).elim
      | none =>
        rw [hnil] at hd
        cases hcons : isFieldListCtor "Cons" inner with
        | none => rw [hcons] at hd; cases hd
        | some es_cons =>
          rw [hcons] at hd
          cases es_cons with
          | nil => simp at hd
          | cons e_head es_tail1 =>
            cases e_head with
            | literal x =>
              cases es_tail1 with
              | nil => simp at hd
              | cons tail es_tail2 =>
                cases es_tail2 with
                | nil =>
                  simp only [Option.map_eq_some_iff] at hd
                  obtain ⟨ns', htail, rfl⟩ := hd
                  obtain ⟨vs, a, hvin⟩ := isFieldListCtor_sound hcons din
                  obtain ⟨vx, vs1, m1, _, _, rfl, dx, a1, _⟩ := a.cons_inv
                  obtain ⟨rfl, rfl, _⟩ := dx.literal_inv
                  obtain ⟨vt, vs2, m2, _, _, rfl, dt, a2, _⟩ := a1.cons_inv
                  obtain ⟨rfl, rfl, _⟩ := a2.nil_inv
                  subst hvin
                  rw [Value.type]
                  obtain ⟨ext_t, hrep_t⟩ := decodeNatListExpr_sound fuel htail dt
                  have hhead : repRoleIdx _ (ZMod.val x) (.field x) :=
                    congrArg Value.field (natCast_val_eq x).symm
                  exact ⟨ext_t.trans (Heap.Extends.snoc _ _),
                    Lib.rep_store_cons repRoleIdx_heapMono₂ hhead hrep_t⟩
                | cons _ _ => simp at hd
            | _ =>
              cases es_tail1 with
              | nil => simp at hd
              | cons _ es_tail2 =>
                cases es_tail2 <;> simp at hd
    | _ => simp [decodeNatListExpr] at hd

private def evalNatListMatchNat (k : Nat) :
    List (Generic.Pattern F × Generic.Expr F) → Option (List Nat)
  | (.literal c, body) :: rest =>
    if k == ZMod.val c then decodeNatListExpr 32 body else evalNatListMatchNat k rest
  | (.wildcard, body) :: _ => decodeNatListExpr 32 body
  | _ => none

private def wildcardBodyAbove77 :
    List (Generic.Pattern F × Generic.Expr F) → Option (List Nat)
  | (.literal c, _) :: rest => if ZMod.val c < 77 then wildcardBodyAbove77 rest else none
  | [(.wildcard, body)] => decodeNatListExpr 32 body
  | _ => none

private theorem evalNatListMatchNat_of_above77 {k : Nat} (hk : 77 ≤ k)
    {arms : List (Generic.Pattern F × Generic.Expr F)} {ns : List Nat}
    (hw : wildcardBodyAbove77 arms = some ns) :
    evalNatListMatchNat k arms = some ns := by
  induction arms with
  | nil => simp [wildcardBodyAbove77] at hw
  | cons arm rest ih =>
    rcases arm with ⟨pat, body⟩
    cases pat with
    | literal c =>
      simp only [wildcardBodyAbove77] at hw
      split at hw
      case isTrue hlt =>
        have hne : (k == ZMod.val c) = false := beq_false_of_ne (by omega)
        simp only [evalNatListMatchNat, hne]
        exact ih hw
      case isFalse => cases hw
    | wildcard =>
      cases rest with
      | nil =>
        simp only [wildcardBodyAbove77] at hw
        exact hw
      | cons _ _ => simp [wildcardBodyAbove77] at hw
    | _ => simp [wildcardBodyAbove77] at hw

private theorem selectArm_natListMatch {arms : List (Generic.Pattern F × Generic.Expr F)}
    {x : F} {ns : List Nat}
    (ht : evalNatListMatchNat (ZMod.val x) arms = some ns)
    {h : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (hsel : selectArm W [] h (.field x) arms = Except.ok (some (bs, body))) :
    decodeNatListExpr 32 body = some ns := by
  induction arms with
  | nil => simp [evalNatListMatchNat] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, armBody⟩
    cases pat with
    | literal c =>
      simp only [evalNatListMatchNat] at ht
      by_cases hxc_b : (ZMod.val x == ZMod.val c) = true
      · rw [ite_eq_left hxc_b] at ht
        have hxc : x = c := ZMod.val_injective _ (beq_iff_eq.mp hxc_b)
        subst hxc
        rcases selectArm_cons_inv hsel with ⟨_, rfl⟩ | ⟨nm, _⟩
        · exact ht
        · exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal x) nm)
      · rw [ite_eq_right hxc_b] at ht
        have hxc_ne : x ≠ c := fun e => hxc_b (beq_iff_eq.mpr (congrArg ZMod.val e))
        rcases selectArm_cons_inv hsel with ⟨mt, _⟩ | ⟨_, hsel'⟩
        · obtain ⟨hv, _⟩ := MatchesConst.some_inv (MatchesConst.literal c) mt
          exact absurd (Value.field.inj hv) hxc_ne
        · exact ih ht hsel'
    | wildcard =>
      simp only [evalNatListMatchNat] at ht
      rcases selectArm_cons_inv hsel with ⟨_, rfl⟩ | ⟨nm, _⟩
      · exact ht
      · exact (matchPattern_wildcard_none nm).elim
    | _ => simp [evalNatListMatchNat] at ht

set_option maxRecDepth 100000 in
private theorem group_roles_table_fin :
    ∀ i : Fin 77,
      evalNatListMatchNat i.val (RolesAux.matchArms IxVM.KernelRoleSpec.group_roles.body) =
        some ((groupRoles i.val).map Ix.Kernel.Role.idx) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem group_roles_above77 :
    wildcardBodyAbove77 (RolesAux.matchArms IxVM.KernelRoleSpec.group_roles.body) = some [] := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem group_needs_table_fin :
    ∀ i : Fin 77,
      evalNatListMatchNat i.val (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) =
        some ((groupNeededRoles i.val).map Ix.Kernel.Role.idx) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem group_needs_above77 :
    wildcardBodyAbove77 (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) = some [] := by
  decide +kernel

theorem group_roles_spec {g : Nat} (hg : g < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::group_roles" [.field (g : F)] h r h' calls) :
    Heap.Extends h h' ∧
    RepList Obs.Names.«Lists::Node<Field>» repRoleNum h' (groupRoles g) r := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.group_roles.lookup
    (by simp [IxVM.KernelRoleSpec.group_roles, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.group_roles.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["g"] := rfl
  have hb : IxVM.KernelRoleSpec.group_roles.body =
      .matchValue (.var "g") (RolesAux.matchArms IxVM.KernelRoleSpec.group_roles.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have hval : ZMod.val (g : F) = g := RolesAux.val_natCast (Nat.lt_trans hg (by decide))
  have ht : evalNatListMatchNat (ZMod.val (g : F))
      (RolesAux.matchArms IxVM.KernelRoleSpec.group_roles.body) =
      some ((groupRoles g).map Ix.Kernel.Role.idx) := by
    rw [hval]
    by_cases hg77 : g < 77
    · exact group_roles_table_fin ⟨g, hg77⟩
    · have hge : 77 ≤ g := Nat.le_of_not_lt hg77
      have hemp : groupRoles g = [] := by
        unfold groupRoles
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [groups_length]; exact hge)]
        rfl
      rw [hemp, List.map_nil]
      exact evalNatListMatchNat_of_above77 hge group_roles_above77
  have hdec := selectArm_natListMatch ht sel8
  obtain ⟨ext, hrep⟩ := decodeNatListExpr_sound 32 hdec d9
  exact ⟨ext, repList_map_idx_to_role hrep⟩

theorem group_needs_spec {g : Nat} (hg : g < 4294967296)
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::group_needs" [.field (g : F)] h r h' calls) :
    Heap.Extends h h' ∧
    RepList Obs.Names.«Lists::Node<Field>» repRoleNum h' (groupNeededRoles g) r := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.group_needs.lookup
    (by simp [IxVM.KernelRoleSpec.group_needs, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.group_needs.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["g"] := rfl
  have hb : IxVM.KernelRoleSpec.group_needs.body =
      .matchValue (.var "g") (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  have hval : ZMod.val (g : F) = g := RolesAux.val_natCast (Nat.lt_trans hg (by decide))
  have ht : evalNatListMatchNat (ZMod.val (g : F))
      (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) =
      some ((groupNeededRoles g).map Ix.Kernel.Role.idx) := by
    rw [hval]
    by_cases hg77 : g < 77
    · exact group_needs_table_fin ⟨g, hg77⟩
    · have hge : 77 ≤ g := Nat.le_of_not_lt hg77
      have hemp : groupNeededRoles g = [] := by
        unfold groupNeededRoles
        simp only [hg77, ↓reduceIte]
      rw [hemp, List.map_nil]
      exact evalNatListMatchNat_of_above77 hge group_needs_above77
  have hdec := selectArm_natListMatch ht sel8
  obtain ⟨ext, hrep⟩ := decodeNatListExpr_sound 32 hdec d9
  exact ⟨ext, repList_map_idx_to_role hrep⟩

/-! ## Unconditional `role_is_bound` and `role_bound_addr` under `TableRep` -/

theorem role_is_bound_uncond {t : Ix.Kernel.RoleTable} {ro : Ix.Kernel.Role}
    {tbl r byRole : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (htbl : TableRep t h tbl) (hr_ne : r ≠ .field 0)
    (hby : Specs.Roles.ByRole h tbl byRole)
    (ev : ObsFn W "KernelRoles::role_is_bound" [tbl, .field (roleNum ro)] h r h' calls) :
    ∃ res : Option (SourceValue F),
      Specs.Roles.RoleMapSearch roleAddrMapEnum h (roleNum ro) byRole res ∧
      match res with
      | some v => ∃ a : Bytes.Address,
          Bytes.RepAddressRef addrTy h a v ∧ t.addressOf? ro = some (ixAddr a)
      | none => t.addressOf? ro = some (ixAddr Specs.Roles.zeroAddr) := by
  let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
  cases Obs.«KernelRoles::role_is_bound».obs ev with
  | other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he110 _ _ =>
    exact absurd he110 hr_ne
  | n0 v1 m2 cs12 x40 y41 m42 cs51 v55 m65 cs73 ev14 ev75 ev53 op97 op47 _ _ _ =>
    obtain ⟨res, hs, hres⟩ :=
      role_bound_addr_or_zero_step c₀ ev14 tbl (roleNum ro) rfl byRole hby
    have htbl' := htbl
    obtain ⟨bp, byRole', byAddr, evMap, hload, hbyRoleAll, _, _⟩ := htbl'
    obtain ⟨bp', byAddr', evMap', hload'⟩ := hby
    have hbr_eq : byRole = byRole' := by
      rw [hload] at hload'
      injection hload' with hv
      injection hv with _ _ hxs
      injection hxs with _ hxs1
      injection hxs1 with he
      exact he.symm
    subst hbr_eq
    cases res with
    | some v =>
      obtain ⟨ro', a, hk, ha, haddr⟩ := RolesAux.roleMapSearch_mem_all hbyRoleAll hs
      obtain rfl := RolesAux.roleNum_inj hk.symm
      exact ⟨some v, hs, a, ha, haddr⟩
    | none =>
      rcases hres with hnone | ⟨_, ha_zero⟩
      · cases hnone
      have htbl_m2 : TableRep c₀.t m2 tbl := htbl.mono ev14.heap_extends
      obtain ⟨rfl, hIdx⟩ := role_addr_index_step c₀ ev75 tbl rfl htbl_m2
      have hlookup :=
        rbtree_map_lookup_or_default_field_step c₀ ev53
          v1 v55 (.field 0) rfl Specs.Roles.zeroAddr ha_zero (IndexEntry c₀.t) hIdx
      obtain rfl := RolesAux.evalBinOp_add_field_inv op97
      obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op47
      have hx40 : x40 = .field (roleNum ro + 1) := hx1.trans hx2.symm
      rcases hlookup with hx0 | ⟨ro', hxr, haddr⟩
      · exfalso
        exact RolesAux.roleNum_add_one_ne_zero ro (Value.field.inj (hx40.symm.trans hx0))
      · obtain rfl := RolesAux.roleNum_add_one_inj (Value.field.inj (hx40.symm.trans hxr))
        exact ⟨none, hs, haddr⟩

theorem role_bound_addr_uncond {t : Ix.Kernel.RoleTable} {ro : Ix.Kernel.Role}
    {tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (htbl : TableRep t h tbl)
    (ev : ObsFn W "KernelRoles::role_bound_addr" [tbl, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧ ∃ a : _root_.Address, S0.addr h' r a ∧ t.addressOf? ro = some a := by
  let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
  obtain ⟨v12, m15, cs23, cs52, ev25, heq48, ev54, _⟩ :=
    Obs.«KernelRoles::role_bound_addr».obs ev
  have htbl' := htbl
  obtain ⟨bp, byRole, byAddr, evMap, hload, _, _, _⟩ := htbl'
  have hby : Specs.Roles.ByRole h tbl byRole := ⟨bp, byAddr, evMap, hload⟩
  have hv12_ne : v12 ≠ .field 0 := by
    rw [heq48]
    exact fun e => one_ne_zero (Value.field.inj e)
  obtain ⟨res₁, hs₁, hbound⟩ := role_is_bound_uncond htbl hv12_ne hby ev25
  have ext1 : Heap.Extends h m15 := ev25.heap_extends
  have hby_m15 : Specs.Roles.ByRole m15 tbl byRole :=
    ⟨bp, byAddr, evMap, ext1.loadValue_eq hload⟩
  obtain ⟨res₂, hs₂, hres₂⟩ :=
    role_bound_addr_or_zero_step c₀ ev54 tbl (roleNum ro) rfl byRole hby_m15
  have hdet : res₁ = res₂ := RolesAux.roleMapSearch_det (RolesAux.roleMapSearch_mono ext1 hs₁) hs₂
  subst hdet
  refine ⟨ev.heap_extends, ?_⟩
  cases res₁ with
  | some v =>
    rcases hres₂ with hsome | ⟨hnone, _⟩
    · injection hsome with hvr
      subst hvr
      obtain ⟨a, ha, haddr⟩ := hbound
      exact ⟨ixAddr a,
        ⟨a, Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ev54.heap_extends) ha, rfl⟩, haddr⟩
    · cases hnone
  | none =>
    rcases hres₂ with hsome | ⟨_, ha_zero⟩
    · cases hsome
    · exact ⟨ixAddr Specs.Roles.zeroAddr, ⟨Specs.Roles.zeroAddr, ha_zero, rfl⟩, hbound⟩

/-! ## Structural sub-call and walk witnesses -/

/-- Witness that `Ingress::get_ci` loaded a `KConstantInfo` cell at `addr` inside `calls`. -/
def GetCiIn (calls : List (Call F)) (addr : _root_.Address) : Prop :=
  ∃ (h_ld m_ld : Heap F) (ap ptr v_ci : SourceValue F) (cs_ld : List (Call F)),
    S0.addr h_ld ap addr ∧
    ObsFn W "Ingress::get_ci" [ap] h_ld ptr m_ld cs_ld ∧
    (⟨"Ingress::get_ci", [ap], h_ld⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_ld, cl ∈ calls) ∧
    loadValue m_ld ptr = .ok v_ci

theorem GetCiIn.mono {cs₁ cs₂ : List (Call F)} {addr : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : GetCiIn cs₁ addr) : GetCiIn cs₂ addr := by
  obtain ⟨h_ld, m_ld, ap, ptr, v_ci, cs_ld, ha, ev, hcl, hcs, hload⟩ := h
  exact ⟨h_ld, m_ld, ap, ptr, v_ci, cs_ld, ha, ev, hsub _ hcl, fun cl hm => hsub cl (hcs cl hm),
    hload⟩

/-- Witness that `Ingress::get_ci` loaded a `"Thm"` constant cell at `addr` inside `calls`. -/
def GetThmCiIn (calls : List (Call F)) (addr : _root_.Address) : Prop :=
  ∃ (h_ld m_ld : Heap F) (ap ptr x_nlvls x_tty x_val : SourceValue F) (cs_ld : List (Call F)),
    S0.addr h_ld ap addr ∧
    ObsFn W "Ingress::get_ci" [ap] h_ld ptr m_ld cs_ld ∧
    (⟨"Ingress::get_ci", [ap], h_ld⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_ld, cl ∈ calls) ∧
    loadValue m_ld ptr =
      .ok (.construct "KernelTypes::KConstantInfo" "Thm" [x_nlvls, x_tty, x_val])

theorem GetThmCiIn.mono {cs₁ cs₂ : List (Call F)} {addr : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : GetThmCiIn cs₁ addr) : GetThmCiIn cs₂ addr := by
  obtain ⟨h_ld, m_ld, ap, ptr, nl, ty, val, cs_ld, ha, ev, hcl, hcs, hload⟩ := h
  exact ⟨h_ld, m_ld, ap, ptr, nl, ty, val, cs_ld, ha, ev, hsub _ hcl,
    fun cl hm => hsub cl (hcs cl hm), hload⟩

theorem GetThmCiIn.toGetCiIn {calls : List (Call F)} {addr : _root_.Address}
    (h : GetThmCiIn calls addr) : GetCiIn calls addr := by
  obtain ⟨h_ld, m_ld, ap, ptr, nl, ty, val, cs_ld, ha, ev, hcl, hcs, hload⟩ := h
  exact ⟨h_ld, m_ld, ap, ptr, _, cs_ld, ha, ev, hcl, hcs, hload⟩

/-- Witness that `KernelClaim::run_check_transitive(rc, ap)` ran on `addr` under `RCRep t lim`
inside `calls`. -/
def RunCheckIn (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (addr : _root_.Address) : Prop :=
  ∃ (h_w h'_w : Heap F) (rc ap r_w : SourceValue F) (cs_w : List (Call F)),
    RCRep t lim h_w rc ∧
    S0.addr h_w ap addr ∧
    ObsFn W "KernelClaim::run_check_transitive" [rc, ap] h_w r_w h'_w cs_w ∧
    (⟨"KernelClaim::run_check_transitive", [rc, ap], h_w⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_w, cl ∈ calls)

theorem RunCheckIn.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} {addr : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : RunCheckIn cs₁ t lim addr) :
    RunCheckIn cs₂ t lim addr := by
  obtain ⟨h_w, h'_w, rc, ap, r_w, cs_w, hrc, ha, ev, hcl, hcs⟩ := h
  exact ⟨h_w, h'_w, rc, ap, r_w, cs_w, hrc, ha, ev, hsub _ hcl, fun cl hm => hsub cl (hcs cl hm)⟩

/-- Witness that `KernelRoles::group_admit(tbl, .field (g : F))` ran under `TableRep t`
inside `calls`. -/
def GroupAdmitIn (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∃ (h_ga h'_ga : Heap F) (tbl r_ga : SourceValue F) (cs_ga : List (Call F)),
    TableRep t h_ga tbl ∧
    ObsFn W "KernelRoles::group_admit" [tbl, .field (g : F)] h_ga r_ga h'_ga cs_ga ∧
    (⟨"KernelRoles::group_admit", [tbl, .field (g : F)], h_ga⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs_ga, cl ∈ calls)

theorem GroupAdmitIn.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable} {g : Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : GroupAdmitIn cs₁ t g) :
    GroupAdmitIn cs₂ t g := by
  obtain ⟨h_ga, h'_ga, tbl, r_ga, cs_ga, htbl, ev, hcl, hcs⟩ := h
  exact ⟨h_ga, h'_ga, tbl, r_ga, cs_ga, htbl, ev, hsub _ hcl, fun cl hm => hsub cl (hcs cl hm)⟩

/-- Structural call and walk facts extracted from `KernelRoles::validate_role` on role `ro`
in group `g` (validated at limit `groupValLimit g`). -/
def RoleValidatedAt (t : Ix.Kernel.RoleTable) (calls : List (Call F))
    (g : Nat) (ro : Ix.Kernel.Role) : Prop :=
  ∃ a : _root_.Address,
    t.addressOf? ro = some a ∧
    GetCiIn calls a ∧
    (roleWalksBound ro = true → RunCheckIn calls t (some (groupValLimit g)) a) ∧
    (roleHasEquations ro = true →
      ∃ arr : Array (Ix.Kernel.Evidence _root_.Address),
        (ro, arr) ∈ t.evidence.toList ∧
        0 < arr.size ∧
        ∀ thm : _root_.Address, .proof thm ∈ arr.toList →
          GetThmCiIn calls thm ∧ RunCheckIn calls t (some (groupValLimit g)) thm)

theorem RoleValidatedAt.mono {t : Ix.Kernel.RoleTable} {cs₁ cs₂ : List (Call F)}
    {g : Nat} {ro : Ix.Kernel.Role}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hv : RoleValidatedAt t cs₁ g ro) :
    RoleValidatedAt t cs₂ g ro := by
  obtain ⟨a, had, hci, hwalk, heqns⟩ := hv
  refine ⟨a, had, hci.mono hsub, fun hw => (hwalk hw).mono hsub, fun he => ?_⟩
  obtain ⟨arr, hmem, hpos, hprf⟩ := heqns he
  refine ⟨arr, hmem, hpos, fun thm hthm => ?_⟩
  obtain ⟨htci, htw⟩ := hprf thm hthm
  exact ⟨htci.mono hsub, htw.mono hsub⟩

/-! ## Equation loops: `validate_op_equations` and `validate_eqns_equations` -/

private theorem evRep_proof_inv {h : Heap F} {thm : _root_.Address} {x_e x_thm : SourceValue F}
    (hev : EvRep h (.proof thm) x_e)
    (hx : x_e = .construct "KernelRoles::RoleEvidence" "Proof" [x_thm]) :
    S0.addr h x_thm thm := by
  rcases hev with ⟨hdef, _⟩ | ⟨a, p, hprf, hv, ha⟩
  · cases hdef
  · injection hprf with hix
    rw [hx] at hv
    injection hv with _ _ hargs
    injection hargs with hp _
    subst hp
    exact ⟨a, ha, hix.symm⟩

private theorem evRep_proof_not_defeq {h : Heap F} {thm : _root_.Address} {x_e : SourceValue F}
    (hev : EvRep h (.proof thm) x_e)
    (hx : x_e = .construct "KernelRoles::RoleEvidence" "Defeq" []) : False := by
  rcases hev with ⟨hdef, _⟩ | ⟨_, p, _, hv, _⟩
  · cases hdef
  · rw [hx] at hv
    exact RolesAux.construct_ctor_ne (by decide) hv

private theorem validate_op_equations_walks {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {es : List (Ix.Kernel.Evidence _root_.Address)} :
    ∀ {x_rc x_tbl x_r x_ev x_k r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RCRep t lim h x_rc →
      RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_op_equations" [x_rc, x_tbl, x_r, x_ev, x_k] h r h' calls →
      Heap.Extends h h' ∧
      ∀ thm : _root_.Address, .proof thm ∈ es →
        GetThmCiIn calls thm ∧ RunCheckIn calls t lim thm
  | x_rc, x_tbl, x_r, x_ev, x_k, r, h, h', calls, hrc, hlist, ev => by
    cases Obs.«KernelRoles::validate_op_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm)⟩
    | Cons x_e x_rest v493 m494 cs496 cs505 v512 ld12 sg501 _ ev507 hc556 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have hseg : Heap.Extends h m494 ∧
          (∀ thm : _root_.Address, e = .proof thm →
            GetThmCiIn cs496 thm ∧ RunCheckIn cs496 t lim thm) := by
        cases sg501 with
        | n0_Defeq m43 _ _ m99 _ _ _ m122 _ m158 _ m194
            ev56 hv83 ev132 ev168 hm202 ev109 _ _ he216 _ =>
          have ext_seg : Heap.Extends h m494 := by
            rw [he216]
            exact ev56.heap_extends.trans (ev132.heap_extends.trans (ev168.heap_extends.trans
              ((by rw [hm202]; exact Heap.Extends.snoc m158 _ : Heap.Extends m158 m194).trans
                ev109.heap_extends)))
          refine ⟨ext_seg, fun thm he => ?_⟩
          have he_prf : EvRep h (.proof thm) x_e := by rwa [← he]
          exact (evRep_proof_not_defeq he_prf hv83).elim
        | n0_Proof _ _ _ _ _ _ heq256 _ _ _ =>
          exact absurd (Value.field.inj heq256) zero_ne_one
        | other_Defeq _ _ _ _ _ _ heq308 _ _ _ =>
          exact absurd (Value.field.inj heq308) zero_ne_one
        | other_Proof v42 m43 cs54 x_thm m327 p335 cs341 x_nlvls x_tty w358
            v401 m402 cs412 cs434 v439 m455 cs463
            ev56 _ _ hv319 ev343 ld337 _ ev414 ev465 ev436 hc490 =>
          have ext_seg : Heap.Extends h m494 :=
            ev56.heap_extends.trans (ev343.heap_extends.trans (ev414.heap_extends.trans
              (ev465.heap_extends.trans ev436.heap_extends)))
          refine ⟨ext_seg, fun thm he => ?_⟩
          have he_prf : EvRep h (.proof thm) x_e := by rwa [← he]
          have ha_h : S0.addr h x_thm thm := evRep_proof_inv he_prf hv319
          have ha_m43 : S0.addr m43 x_thm thm := S0.addr_mono ev56.heap_extends ha_h
          have ha_m327 : S0.addr m327 x_thm thm := S0.addr_mono ev343.heap_extends ha_m43
          have hrc_m327 : RCRep t lim m327 x_rc :=
            hrc.mono (ev56.heap_extends.trans ev343.heap_extends)
          refine ⟨⟨m43, m327, x_thm, p335, x_nlvls, x_tty, w358, cs341, ha_m43, ev343,
            by rw [hc490]; simp, fun cl hm => by rw [hc490]; simp [hm], ld337⟩,
            ⟨m327, m402, x_rc, x_thm, v401, cs412, hrc_m327, ha_m327, ev414,
              by rw [hc490]; simp, fun cl hm => by rw [hc490]; simp [hm]⟩⟩
      obtain ⟨ext1, hhead⟩ := hseg
      have hsub1 : ∀ cl ∈ cs496, cl ∈ calls := fun cl hm => by rw [hc556]; simp [hm]
      have hsub2 : ∀ cl ∈ cs505, cl ∈ calls := fun cl hm => by rw [hc556]; simp [hm]
      obtain ⟨ext2, htail⟩ :=
        validate_op_equations_walks (hrc.mono ext1)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev507
      refine ⟨ext1.trans ext2, fun thm hmem => ?_⟩
      rcases List.mem_cons.mp hmem with he | hrest
      · obtain ⟨hci, hrw⟩ := hhead thm he.symm
        exact ⟨hci.mono hsub1, hrw.mono hsub1⟩
      · obtain ⟨hci, hrw⟩ := htail thm hrest
        exact ⟨hci.mono hsub2, hrw.mono hsub2⟩

private theorem validate_op_equations_full_walks {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {lim : Nat}
    {es : List (Ix.Kernel.Evidence _root_.Address)} :
    ∀ {x_rc x_tbl x_r x_ev x_k r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.RCFullRep t bAddr lim h x_rc →
      RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_op_equations" [x_rc, x_tbl, x_r, x_ev, x_k] h r h' calls →
      Heap.Extends h h' ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        ∀ thm : _root_.Address, .proof thm ∈ es → thm ∈ recs.map (·.addr)
  | x_rc, x_tbl, x_r, x_ev, x_k, r, h, h', calls, hrc, hlist, ev => by
    cases Obs.«KernelRoles::validate_op_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, [], by simp [Claim.RecsClosed], fun _ hm => (nomatch hm)⟩
    | Cons x_e x_rest v493 m494 cs496 cs505 v512 ld12 sg501 _ ev507 hc556 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have hseg : Heap.Extends h m494 ∧
          ∃ recs₁ : List (Claim.WalkedRec cs496 bAddr t),
            Claim.RecsClosed recs₁ ∧
            (∀ thm : _root_.Address, e = .proof thm → thm ∈ recs₁.map (·.addr)) := by
        cases sg501 with
        | n0_Defeq m43 _ _ m99 _ _ _ m122 _ m158 _ m194
            ev56 hv83 ev132 ev168 hm202 ev109 _ _ he216 _ =>
          have ext_seg : Heap.Extends h m494 := by
            rw [he216]
            exact ev56.heap_extends.trans (ev132.heap_extends.trans (ev168.heap_extends.trans
              ((by rw [hm202]; exact Heap.Extends.snoc m158 _ : Heap.Extends m158 m194).trans
                ev109.heap_extends)))
          refine ⟨ext_seg, [], by simp [Claim.RecsClosed], fun thm he => ?_⟩
          have he_prf : EvRep h (.proof thm) x_e := by rwa [← he]
          exact (evRep_proof_not_defeq he_prf hv83).elim
        | n0_Proof _ _ _ _ _ _ heq256 _ _ _ =>
          exact absurd (Value.field.inj heq256) zero_ne_one
        | other_Defeq _ _ _ _ _ _ heq308 _ _ _ =>
          exact absurd (Value.field.inj heq308) zero_ne_one
        | other_Proof v42 m43 cs54 x_thm m327 p335 cs341 x_nlvls x_tty w358
            v401 m402 cs412 cs434 v439 m455 cs463
            ev56 _ _ hv319 ev343 _ _ ev414 ev465 ev436 hc490 =>
          have ext_seg : Heap.Extends h m494 :=
            ev56.heap_extends.trans (ev343.heap_extends.trans (ev414.heap_extends.trans
              (ev465.heap_extends.trans ev436.heap_extends)))
          cases e with
          | defeq =>
            exact ⟨ext_seg, [], by simp [Claim.RecsClosed], fun _ he => by cases he⟩
          | proof thm₀ =>
            have ha_h : S0.addr h x_thm thm₀ := evRep_proof_inv he_rep hv319
            have ha_m327 : S0.addr m327 x_thm thm₀ :=
              S0.addr_mono (ev56.heap_extends.trans ev343.heap_extends) ha_h
            have hrc_m327 : Claim.RCFullRep t bAddr lim m327 x_rc :=
              hrc.mono (ev56.heap_extends.trans ev343.heap_extends)
            obtain ⟨_, recs_w, hmem_w, hcl_w, _⟩ :=
              Claim.run_check_transitive_spec hrc_m327 ha_m327 ev414
            have hsub_w : ∀ cl ∈ cs412, cl ∈ cs496 := fun cl hm => by rw [hc490]; simp [hm]
            refine ⟨ext_seg, recs_w.map (Claim.WalkedRec.mono hsub_w), hcl_w.mono hsub_w,
              fun thm he => ?_⟩
            injection he with hthm
            subst hthm
            rw [Claim.map_addr_walkedRec_mono]
            exact hmem_w
      obtain ⟨ext1, recs₁, hcl₁, hhead⟩ := hseg
      obtain ⟨ext2, recs₂, hcl₂, htail⟩ :=
        validate_op_equations_full_walks (hrc.mono ext1)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev507
      have hsub1 : ∀ cl ∈ cs496, cl ∈ calls := fun cl hm => by rw [hc556]; simp [hm]
      have hsub2 : ∀ cl ∈ cs505, cl ∈ calls := fun cl hm => by rw [hc556]; simp [hm]
      refine ⟨ext1.trans ext2,
        recs₁.map (Claim.WalkedRec.mono hsub1) ++ recs₂.map (Claim.WalkedRec.mono hsub2),
        (hcl₁.mono hsub1).append (hcl₂.mono hsub2), fun thm hmem => ?_⟩
      rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
      rcases List.mem_cons.mp hmem with he | hrest
      · exact List.mem_append_left _ (hhead thm he.symm)
      · exact List.mem_append_right _ (htail thm hrest)

private theorem validate_eqns_equations_walks {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {es : List (Ix.Kernel.Evidence _root_.Address)} :
    ∀ {x_rc x_tbl x_r x_ev x_k r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RCRep t lim h x_rc →
      RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_eqns_equations" [x_rc, x_tbl, x_r, x_ev, x_k] h r h' calls →
      Heap.Extends h h' ∧
      ∀ thm : _root_.Address, .proof thm ∈ es →
        GetThmCiIn calls thm ∧ RunCheckIn calls t lim thm
  | x_rc, x_tbl, x_r, x_ev, x_k, r, h, h', calls, hrc, hlist, ev => by
    cases Obs.«KernelRoles::validate_eqns_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm)⟩
    | Cons x_e x_rest v432 m433 cs435 cs444 v451 ld12 sg440 _ ev446 hc495 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have hseg : Heap.Extends h m433 ∧
          (∀ thm : _root_.Address, e = .proof thm →
            GetThmCiIn cs435 thm ∧ RunCheckIn cs435 t lim thm) := by
        cases sg440 with
        | Defeq _ m72 _ _ m120 _ _ _ m143 _ m179 _ m215
            hv56 ev82 _ ev153 ev189 hm223 ev130 _ _ he237 _ =>
          have ext_seg : Heap.Extends h m433 := by
            rw [he237]
            exact ev82.heap_extends.trans (ev153.heap_extends.trans (ev189.heap_extends.trans
              ((by rw [hm223]; exact Heap.Extends.snoc m179 _ : Heap.Extends m179 m215).trans
                ev130.heap_extends)))
          refine ⟨ext_seg, fun thm he => ?_⟩
          have he_prf : EvRep h (.proof thm) x_e := by rwa [← he]
          exact (evRep_proof_not_defeq he_prf hv56).elim
        | Proof x_thm m252 p260 cs266 x_nlvls x_tty w283 v311 m320 cs328
            v340 m341 cs351 cs373 v378 m394 cs402
            _ hv244 ev268 ld262 ev330 _ ev353 ev404 ev375 hc429 =>
          have ext_seg : Heap.Extends h m433 :=
            ev268.heap_extends.trans (ev330.heap_extends.trans (ev353.heap_extends.trans
              (ev404.heap_extends.trans ev375.heap_extends)))
          refine ⟨ext_seg, fun thm he => ?_⟩
          have he_prf : EvRep h (.proof thm) x_e := by rwa [← he]
          have ha_h : S0.addr h x_thm thm := evRep_proof_inv he_prf hv244
          have ha_m320 : S0.addr m320 x_thm thm :=
            S0.addr_mono (ev268.heap_extends.trans ev330.heap_extends) ha_h
          have hrc_m320 : RCRep t lim m320 x_rc :=
            hrc.mono (ev268.heap_extends.trans ev330.heap_extends)
          refine ⟨⟨h, m252, x_thm, p260, x_nlvls, x_tty, w283, cs266, ha_h, ev268,
            by rw [hc429]; simp, fun cl hm => by rw [hc429]; simp [hm], ld262⟩,
            ⟨m320, m341, x_rc, x_thm, v340, cs351, hrc_m320, ha_m320, ev353,
              by rw [hc429]; simp, fun cl hm => by rw [hc429]; simp [hm]⟩⟩
      obtain ⟨ext1, hhead⟩ := hseg
      have hsub1 : ∀ cl ∈ cs435, cl ∈ calls := fun cl hm => by rw [hc495]; simp [hm]
      have hsub2 : ∀ cl ∈ cs444, cl ∈ calls := fun cl hm => by rw [hc495]; simp [hm]
      obtain ⟨ext2, htail⟩ :=
        validate_eqns_equations_walks (hrc.mono ext1)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev446
      refine ⟨ext1.trans ext2, fun thm hmem => ?_⟩
      rcases List.mem_cons.mp hmem with he | hrest
      · obtain ⟨hci, hrw⟩ := hhead thm he.symm
        exact ⟨hci.mono hsub1, hrw.mono hsub1⟩
      · obtain ⟨hci, hrw⟩ := htail thm hrest
        exact ⟨hci.mono hsub2, hrw.mono hsub2⟩

private theorem validate_eqns_equations_full_walks {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {lim : Nat}
    {es : List (Ix.Kernel.Evidence _root_.Address)} :
    ∀ {x_rc x_tbl x_r x_ev x_k r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.RCFullRep t bAddr lim h x_rc →
      RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_eqns_equations" [x_rc, x_tbl, x_r, x_ev, x_k] h r h' calls →
      Heap.Extends h h' ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        ∀ thm : _root_.Address, .proof thm ∈ es → thm ∈ recs.map (·.addr)
  | x_rc, x_tbl, x_r, x_ev, x_k, r, h, h', calls, hrc, hlist, ev => by
    cases Obs.«KernelRoles::validate_eqns_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, [], by simp [Claim.RecsClosed], fun _ hm => (nomatch hm)⟩
    | Cons x_e x_rest v432 m433 cs435 cs444 v451 ld12 sg440 _ ev446 hc495 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have hseg : Heap.Extends h m433 ∧
          ∃ recs₁ : List (Claim.WalkedRec cs435 bAddr t),
            Claim.RecsClosed recs₁ ∧
            (∀ thm : _root_.Address, e = .proof thm → thm ∈ recs₁.map (·.addr)) := by
        cases sg440 with
        | Defeq _ m72 _ _ m120 _ _ _ m143 _ m179 _ m215
            hv56 ev82 _ ev153 ev189 hm223 ev130 _ _ he237 _ =>
          have ext_seg : Heap.Extends h m433 := by
            rw [he237]
            exact ev82.heap_extends.trans (ev153.heap_extends.trans (ev189.heap_extends.trans
              ((by rw [hm223]; exact Heap.Extends.snoc m179 _ : Heap.Extends m179 m215).trans
                ev130.heap_extends)))
          refine ⟨ext_seg, [], by simp [Claim.RecsClosed], fun thm he => ?_⟩
          have he_prf : EvRep h (.proof thm) x_e := by rwa [← he]
          exact (evRep_proof_not_defeq he_prf hv56).elim
        | Proof x_thm m252 p260 cs266 x_nlvls x_tty w283 v311 m320 cs328
            v340 m341 cs351 cs373 v378 m394 cs402
            _ hv244 ev268 _ ev330 _ ev353 ev404 ev375 hc429 =>
          have ext_seg : Heap.Extends h m433 :=
            ev268.heap_extends.trans (ev330.heap_extends.trans (ev353.heap_extends.trans
              (ev404.heap_extends.trans ev375.heap_extends)))
          cases e with
          | defeq =>
            exact ⟨ext_seg, [], by simp [Claim.RecsClosed], fun _ he => by cases he⟩
          | proof thm₀ =>
            have ha_h : S0.addr h x_thm thm₀ := evRep_proof_inv he_rep hv244
            have ha_m320 : S0.addr m320 x_thm thm₀ :=
              S0.addr_mono (ev268.heap_extends.trans ev330.heap_extends) ha_h
            have hrc_m320 : Claim.RCFullRep t bAddr lim m320 x_rc :=
              hrc.mono (ev268.heap_extends.trans ev330.heap_extends)
            obtain ⟨_, recs_w, hmem_w, hcl_w, _⟩ :=
              Claim.run_check_transitive_spec hrc_m320 ha_m320 ev353
            have hsub_w : ∀ cl ∈ cs351, cl ∈ cs435 := fun cl hm => by rw [hc429]; simp [hm]
            refine ⟨ext_seg, recs_w.map (Claim.WalkedRec.mono hsub_w), hcl_w.mono hsub_w,
              fun thm he => ?_⟩
            injection he with hthm
            subst hthm
            rw [Claim.map_addr_walkedRec_mono]
            exact hmem_w
      obtain ⟨ext1, recs₁, hcl₁, hhead⟩ := hseg
      obtain ⟨ext2, recs₂, hcl₂, htail⟩ :=
        validate_eqns_equations_full_walks (hrc.mono ext1)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev446
      have hsub1 : ∀ cl ∈ cs435, cl ∈ calls := fun cl hm => by rw [hc495]; simp [hm]
      have hsub2 : ∀ cl ∈ cs444, cl ∈ calls := fun cl hm => by rw [hc495]; simp [hm]
      refine ⟨ext1.trans ext2,
        recs₁.map (Claim.WalkedRec.mono hsub1) ++ recs₂.map (Claim.WalkedRec.mono hsub2),
        (hcl₁.mono hsub1).append (hcl₂.mono hsub2), fun thm hmem => ?_⟩
      rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
      rcases List.mem_cons.mp hmem with he | hrest
      · exact List.mem_append_left _ (hhead thm he.symm)
      · exact List.mem_append_right _ (htail thm hrest)

/-! ## `validate_role` and `validate_group_roles` -/

set_option maxRecDepth 100000 in
private theorem roleSpecKind_of_roleWalksBound {ro : Ix.Kernel.Role}
    (hw : roleWalksBound ro = true) :
    roleSpecKindNat ro = 0 ∨ roleSpecKindNat ro = 2 ∨ roleSpecKindNat ro = 5 := by
  cases ro <;> first | exact absurd hw (by decide) | decide

set_option maxRecDepth 100000 in
private theorem roleSpecKind_of_roleHasEquations {ro : Ix.Kernel.Role}
    (he : roleHasEquations ro = true) :
    roleSpecKindNat ro = 2 ∨ roleSpecKindNat ro = 5 := by
  cases ro <;> first | exact absurd he (by decide) | decide

private theorem nonempty_evidence_of_len_eq {ro : Ix.Kernel.Role} {t : Ix.Kernel.RoleTable}
    {es : List (Ix.Kernel.Evidence _root_.Address)} {k : Nat}
    (hk0 : 0 < k) (hk10 : k < 10)
    (hes : es = [] ∨ ∃ arr, (ro, arr) ∈ t.evidence.toList ∧ arr.toList = es)
    (heq : (Value.field (es.length : F) : SourceValue F) = .field (k : F)) :
    ∃ arr : Array (Ix.Kernel.Evidence _root_.Address),
      (ro, arr) ∈ t.evidence.toList ∧ arr.toList = es ∧ 0 < arr.size := by
  rcases hes with rfl | ⟨arr, hmem, harr⟩
  · exfalso
    have hz := congrArg ZMod.val (Value.field.inj heq)
    rw [List.length_nil, Nat.cast_zero, ZMod.val_zero,
      RolesAux.val_natCast (Nat.lt_trans hk10 (by decide))] at hz
    omega
  · refine ⟨arr, hmem, harr, ?_⟩
    have hz := congrArg ZMod.val (Value.field.inj heq)
    rw [← harr, Array.length_toList] at hz
    by_cases hsz0 : arr.size = 0
    · rw [hsz0, Nat.cast_zero, ZMod.val_zero,
        RolesAux.val_natCast (Nat.lt_trans hk10 (by decide))] at hz
      omega
    · omega

private theorem evList_length {es : List (Ix.Kernel.Evidence _root_.Address)}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<KernelRoles::RoleEvidence>» [l] h r h' cs)
    (hl : RepList evListEnum EvRep h es l) :
    r = .field (es.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [.named "KernelRoles::RoleEvidence" []]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelRoles::RoleEvidence>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.named "KernelRoles::RoleEvidence" []]).symbol
      EvRep h es l := by
    rw [Obs.Names.«Lists::Node<KernelRoles::RoleEvidence>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

theorem validate_role_walks {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    {x_rc x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCRep t (some (groupValLimit g)) h x_rc)
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧ RoleValidatedAt t calls g ro := by
  let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
  refine ⟨ev.heap_extends, ?_⟩
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs140
      ev14 ev47 ld41 ev80 ev100 _ ev124 ev142 hc183 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 0 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    have hci : GetCiIn calls a := ⟨m2, m32, v1, p39, v31, cs45, ha_m2, ev47,
      by rw [hc183]; simp, fun cl hm => by rw [hc183]; simp [hm], ld41⟩
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    have hrc_m111 : RCRep t (some (groupValLimit g)) m111 x_rc :=
      hrc.mono (ext_ba.trans ext_m111)
    have ha_m111 : S0.addr m111 v1 a := S0.addr_mono ext_m111 ha_m2
    refine ⟨a, had, hci, fun hw => ?_, fun he => ?_⟩
    · have hsub_mem : ∀ cl ∈ cs140, cl ∈ calls := fun cl hm => by rw [hc183]; simp [hm]
      cases Obs.«KernelRoles::validate_member».obs ev142 with
      | n0 _ m2' _ _ m24' _ _ _ m40' _ m60' _ m88' _ _ _ _ _ _ _ _ _ _ m198' _ cs221'
          ev14' ev50' ev70' ev36' ev101' _ ev208' _ ev223' hc240' =>
        have ext_w : Heap.Extends m111 m198' :=
          ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
            (ev36'.heap_extends.trans (ev101'.heap_extends.trans ev208'.heap_extends))))
        exact RunCheckIn.mono hsub_mem ⟨m198', h', x_rc, v1, r, cs221', hrc_m111.mono ext_w,
          S0.addr_mono ext_w ha_m111, ev223', by rw [hc240']; simp,
          fun cl hm => by rw [hc240']; simp [hm]⟩
      | n1 _ m2' _ _ m24' _ _ _ m40' _ m60' _ m88' _ _ _ _ _ _ _ _ _ m307' _ _ _ _ _
          m360' _ _ _ m379' _ _ _ _ _ _ _ _ _ _ m472' _ cs623'
          ev14' ev50' ev70' ev36' ev101' _ ev319' ev389' ev376' _ ev482' _ _ _ _ _ ev625' hc642' =>
        have ext_w : Heap.Extends m111 m472' :=
          ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
            (ev36'.heap_extends.trans (ev101'.heap_extends.trans (ev319'.heap_extends.trans
              (ev389'.heap_extends.trans (ev376'.heap_extends.trans ev482'.heap_extends)))))))
        exact RunCheckIn.mono hsub_mem ⟨m472', h', x_rc, v1, r, cs623', hrc_m111.mono ext_w,
          S0.addr_mono ext_w ha_m111, ev625', by rw [hc642']; simp,
          fun cl hm => by rw [hc642']; simp [hm]⟩
      | n2 _ m2' _ _ m24' _ _ _ m40' _ m60' _ m88' _ _ _ _ _ _ _ _ _ _ _ _ cs735'
          ev14' ev50' ev70' ev36' ev101' _ ev737' hc754' =>
        have ext_w : Heap.Extends m111 m88' :=
          ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
            (ev36'.heap_extends.trans ev101'.heap_extends)))
        exact RunCheckIn.mono hsub_mem ⟨m88', h', x_rc, v1, r, cs735', hrc_m111.mono ext_w,
          S0.addr_mono ext_w ha_m111, ev737', by rw [hc754']; simp,
          fun cl hm => by rw [hc754']; simp [hm]⟩
      | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ _ _ _ _ _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
    · rcases roleSpecKind_of_roleHasEquations he with h2 | h5 <;> omega
  | n1 v1 m2 cs12 v31 m32 p39 cs45 _ _ _ _ _ _ _ _ _
      ev14 ev47 ld41 _ _ _ ev124 _ hc227 =>
    obtain ⟨_, a, ha_m2, had⟩ := role_bound_addr_uncond htbl ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 1 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    refine ⟨a, had, ⟨m2, m32, v1, p39, v31, cs45, ha_m2, ev47,
      by rw [hc227]; simp, fun cl hm => by rw [hc227]; simp [hm], ld41⟩,
      fun hw => ?_, fun he => ?_⟩
    · rcases roleSpecKind_of_roleWalksBound hw with h0 | h2 | h5 <;> omega
    · rcases roleSpecKind_of_roleHasEquations he with h2 | h5 <;> omega
  | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
      ev14 ev47 ld41 ev80 ev100 _ ev124 ev238 hc279 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 2 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    have hsub_op : ∀ cl ∈ cs236, cl ∈ calls := fun cl hm => by rw [hc279]; simp [hm]
    obtain ⟨_, _, _, _, _, _, m102_op, _, _, m111_op, _, _, m134_op, _,
      v161, m162, cs172, v191, m192, cs202, v232, v233, m235, cs243, m255, cs263, cs278,
      _, sg109, ev144, ev123, ev174, ev204, ev245, ev265, heq274, ev280, hc320⟩ :=
      Obs.«KernelRoles::validate_op».obs ev238
    have ext_sg : Heap.Extends m111 m102_op := by
      cases sg109 with
      | Safe _ _ he64 _ => rw [he64]
      | other _ heq95 _ _ _ => exact absurd (Value.field.inj heq95) zero_ne_one
    have ext_w : Heap.Extends m111 m111_op :=
      ext_sg.trans (ev144.heap_extends.trans ev123.heap_extends)
    have hrc_w : RCRep t (some (groupValLimit g)) m111_op x_rc :=
      hrc.mono (ext_ba.trans (ext_m111.trans ext_w))
    have ha_w : S0.addr m111_op v1 a := S0.addr_mono (ext_m111.trans ext_w) ha_m2
    have hwalk_a : RunCheckIn calls t (some (groupValLimit g)) a :=
      RunCheckIn.mono hsub_op ⟨m111_op, m162, x_rc, v1, v161, cs172, hrc_w, ha_w, ev174,
        by rw [hc320]; simp, fun cl hm => by rw [hc320]; simp [hm]⟩
    have htbl_m162 : TableRep c₀.t m162 x_tbl :=
      htbl.mono (ext_ba.trans (ext_m111.trans (ext_w.trans ev174.heap_extends)))
    obtain ⟨es, hlist_m192, hes⟩ := role_evidence_step c₀ ev204 x_tbl ro rfl htbl_m162
    obtain ⟨rfl, rfl⟩ := evList_length ev245 hlist_m192
    obtain ⟨rfl, k, hk0, hk10, rfl⟩ := op_equation_count_pos hsk ev265
    obtain ⟨arr, hmem_ev, harr_eq, hpos⟩ := nonempty_evidence_of_len_eq hk0 hk10 hes heq274
    have hrc_m255 : RCRep t (some (groupValLimit g)) m255 x_rc :=
      hrc_w.mono (ev174.heap_extends.trans ev204.heap_extends)
    obtain ⟨_, hprfs⟩ := validate_op_equations_walks hrc_m255 hlist_m192 ev280
    have hsub_eqs : ∀ cl ∈ cs278, cl ∈ calls := fun cl hm =>
      hsub_op cl (by rw [hc320]; simp [hm])
    refine ⟨a, had, ⟨m2, m32, v1, p39, v31, cs45, ha_m2, ev47,
      by rw [hc279]; simp, fun cl hm => by rw [hc279]; simp [hm], ld41⟩,
      fun _ => hwalk_a, fun _ => ⟨arr, hmem_ev, hpos, fun thm hthm => ?_⟩⟩
    rw [harr_eq] at hthm
    obtain ⟨htci, htw⟩ := hprfs thm hthm
    exact ⟨htci.mono hsub_eqs, htw.mono hsub_eqs⟩
  | n3 v1 m2 cs12 v31 m32 p39 cs45 _ _ _ _ _ _ _ _ _
      ev14 ev47 ld41 _ _ _ ev124 _ hc323 =>
    obtain ⟨_, a, ha_m2, had⟩ := role_bound_addr_uncond htbl ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 3 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    refine ⟨a, had, ⟨m2, m32, v1, p39, v31, cs45, ha_m2, ev47,
      by rw [hc323]; simp, fun cl hm => by rw [hc323]; simp [hm], ld41⟩,
      fun hw => ?_, fun he => ?_⟩
    · rcases roleSpecKind_of_roleWalksBound hw with h0 | h2 | h5 <;> omega
    · rcases roleSpecKind_of_roleHasEquations he with h2 | h5 <;> omega
  | n4 v1 m2 cs12 v31 m32 p39 cs45 _ _ _ _ _ _ _ _ _
      ev14 ev47 ld41 _ _ _ ev124 _ hc367 =>
    obtain ⟨_, a, ha_m2, had⟩ := role_bound_addr_uncond htbl ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 4 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    refine ⟨a, had, ⟨m2, m32, v1, p39, v31, cs45, ha_m2, ev47,
      by rw [hc367]; simp, fun cl hm => by rw [hc367]; simp [hm], ld41⟩,
      fun hw => ?_, fun he => ?_⟩
    · rcases roleSpecKind_of_roleWalksBound hw with h0 | h2 | h5 <;> omega
    · rcases roleSpecKind_of_roleHasEquations he with h2 | h5 <;> omega
  | n5 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs376
      ev14 ev47 ld41 ev80 ev100 _ ev124 ev378 hc419 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl ev14
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    have hsk : roleSpecKindNat ro = 5 := by
      cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    have hsub_eqns : ∀ cl ∈ cs376, cl ∈ calls := fun cl hm => by rw [hc419]; simp [hm]
    obtain ⟨_, _, _, _, _, _, m101_eq, _, _, m130_eq, _, _, m151_eq, _, _, m182_eq, _,
      v209, m210, cs220, v239, m240, cs250, v280, v281, m283, cs291, m303, cs311, cs326,
      _, sg108, ev140, _, ev192, ev163, ev222, ev252, ev293, ev313, heq322, ev328, hc368⟩ :=
      Obs.«KernelRoles::validate_eqns».obs ev378
    have ext_sg : Heap.Extends m111 m101_eq := by
      cases sg108 with
      | Safe _ _ he63 _ => rw [he63]
      | other _ heq94 _ _ _ => exact absurd (Value.field.inj heq94) zero_ne_one
    have ext_w : Heap.Extends m111 m151_eq :=
      ext_sg.trans (ev140.heap_extends.trans (ev192.heap_extends.trans ev163.heap_extends))
    have hrc_w : RCRep t (some (groupValLimit g)) m151_eq x_rc :=
      hrc.mono (ext_ba.trans (ext_m111.trans ext_w))
    have ha_w : S0.addr m151_eq v1 a := S0.addr_mono (ext_m111.trans ext_w) ha_m2
    have hwalk_a : RunCheckIn calls t (some (groupValLimit g)) a :=
      RunCheckIn.mono hsub_eqns ⟨m151_eq, m210, x_rc, v1, v209, cs220, hrc_w, ha_w, ev222,
        by rw [hc368]; simp, fun cl hm => by rw [hc368]; simp [hm]⟩
    have htbl_m210 : TableRep c₀.t m210 x_tbl :=
      htbl.mono (ext_ba.trans (ext_m111.trans (ext_w.trans ev222.heap_extends)))
    obtain ⟨es, hlist_m240, hes⟩ := role_evidence_step c₀ ev252 x_tbl ro rfl htbl_m210
    obtain ⟨rfl, rfl⟩ := evList_length ev293 hlist_m240
    obtain ⟨rfl, k, hk0, hk10, rfl⟩ := eqns_equation_count_pos hsk ev313
    obtain ⟨arr, hmem_ev, harr_eq, hpos⟩ := nonempty_evidence_of_len_eq hk0 hk10 hes heq322
    have hrc_m303 : RCRep t (some (groupValLimit g)) m303 x_rc :=
      hrc_w.mono (ev222.heap_extends.trans ev252.heap_extends)
    obtain ⟨_, hprfs⟩ := validate_eqns_equations_walks hrc_m303 hlist_m240 ev328
    have hsub_eqs : ∀ cl ∈ cs326, cl ∈ calls := fun cl hm =>
      hsub_eqns cl (by rw [hc368]; simp [hm])
    refine ⟨a, had, ⟨m2, m32, v1, p39, v31, cs45, ha_m2, ev47,
      by rw [hc419]; simp, fun cl hm => by rw [hc419]; simp [hm], ld41⟩,
      fun _ => hwalk_a, fun _ => ⟨arr, hmem_ev, hpos, fun thm hthm => ?_⟩⟩
    rw [harr_eq] at hthm
    obtain ⟨htci, htw⟩ := hprfs thm hthm
    exact ⟨htci.mono hsub_eqs, htw.mono hsub_eqs⟩

theorem validate_role_full_walks {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {g : Nat} {ro : Ix.Kernel.Role}
    {x_rc x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (groupValLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧
    RoleValidatedAt t calls g ro ∧
    ∃ recs : List (Claim.WalkedRec calls bAddr t),
      Claim.RecsClosed recs ∧
      (∀ a, roleWalksBound ro = true → t.addressOf? ro = some a → a ∈ recs.map (·.addr)) ∧
      (∀ arr thm, (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList →
        thm ∈ recs.map (·.addr)) := by
  obtain ⟨ext, hval⟩ := validate_role_walks hrc.toRCRep htbl.toTableRep ev
  have hwf : t.wf = true := htbl.1
  refine ⟨ext, hval, ?_⟩
  by_cases hw : roleWalksBound ro = true
  · let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
    cases Obs.«KernelRoles::validate_role».obs ev with
    | n0 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs140
        ev14 ev47 _ ev80 ev100 _ ev124 ev142 hc183 =>
      obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
      obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
      have hsk : roleSpecKindNat ro = 0 := by
        cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
      have ext_m111 : Heap.Extends m2 m111 :=
        ev47.heap_extends.trans (ev80.heap_extends.trans
          (ev100.heap_extends.trans ev124.heap_extends))
      have hrc_m111 := hrc.mono (ext_ba.trans ext_m111)
      have ha_m111 := S0.addr_mono ext_m111 ha_m2
      have hno_ev : ∀ arr thm, (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → False := by
        intro arr _ hm _
        have hreq := evidence_roleHasEquations_of_wf hwf hm
        rcases roleSpecKind_of_roleHasEquations hreq with h2 | h5 <;> omega
      cases Obs.«KernelRoles::validate_member».obs ev142 with
      | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m198' _ cs221'
          ev14' ev50' ev70' ev36' ev101' _ ev208' _ ev223' hc240' =>
        have ext_w : Heap.Extends m111 m198' :=
          ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
            (ev36'.heap_extends.trans (ev101'.heap_extends.trans ev208'.heap_extends))))
        obtain ⟨_, recs_a, hmem_a, hcl_a, _⟩ :=
          Claim.run_check_transitive_spec (hrc_m111.mono ext_w) (S0.addr_mono ext_w ha_m111) ev223'
        have hsub : ∀ cl ∈ cs221', cl ∈ calls := fun cl hm => by
          rw [hc183]; simp [show cl ∈ cs140 by rw [hc240']; simp [hm]]
        refine ⟨recs_a.map (Claim.WalkedRec.mono hsub), hcl_a.mono hsub, ?_,
          fun arr thm hm hp => (hno_ev arr thm hm hp).elim⟩
        intro a' _ had'
        rw [had] at had'; injection had' with ha_eq; subst ha_eq
        rw [Claim.map_addr_walkedRec_mono]
        exact hmem_a
      | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m472' _ cs623'
          ev14' ev50' ev70' ev36' ev101' _ ev319' ev389' ev376' _ ev482' _ _ _ _ _ ev625' hc642' =>
        have ext_w : Heap.Extends m111 m472' :=
          ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
            (ev36'.heap_extends.trans (ev101'.heap_extends.trans (ev319'.heap_extends.trans
              (ev389'.heap_extends.trans (ev376'.heap_extends.trans ev482'.heap_extends)))))))
        obtain ⟨_, recs_a, hmem_a, hcl_a, _⟩ :=
          Claim.run_check_transitive_spec (hrc_m111.mono ext_w) (S0.addr_mono ext_w ha_m111) ev625'
        have hsub : ∀ cl ∈ cs623', cl ∈ calls := fun cl hm => by
          rw [hc183]; simp [show cl ∈ cs140 by rw [hc642']; simp [hm]]
        refine ⟨recs_a.map (Claim.WalkedRec.mono hsub), hcl_a.mono hsub, ?_,
          fun arr thm hm hp => (hno_ev arr thm hm hp).elim⟩
        intro a' _ had'
        rw [had] at had'; injection had' with ha_eq; subst ha_eq
        rw [Claim.map_addr_walkedRec_mono]
        exact hmem_a
      | n2 _ _ _ _ _ _ _ _ _ _ _ _ m88' _ _ _ _ _ _ _ _ _ _ _ _ cs735'
          ev14' ev50' ev70' ev36' ev101' _ ev737' hc754' =>
        have ext_w : Heap.Extends m111 m88' :=
          ev14'.heap_extends.trans (ev50'.heap_extends.trans (ev70'.heap_extends.trans
            (ev36'.heap_extends.trans ev101'.heap_extends)))
        obtain ⟨_, recs_a, hmem_a, hcl_a, _⟩ :=
          Claim.run_check_transitive_spec (hrc_m111.mono ext_w) (S0.addr_mono ext_w ha_m111) ev737'
        have hsub : ∀ cl ∈ cs735', cl ∈ calls := fun cl hm => by
          rw [hc183]; simp [show cl ∈ cs140 by rw [hc754']; simp [hm]]
        refine ⟨recs_a.map (Claim.WalkedRec.mono hsub), hcl_a.mono hsub, ?_,
          fun arr thm hm hp => (hno_ev arr thm hm hp).elim⟩
        intro a' _ had'
        rw [had] at had'; injection had' with ha_eq; subst ha_eq
        rw [Claim.map_addr_walkedRec_mono]
        exact hmem_a
      | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ _ _ _ _ _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
      | n7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev101' _ _ =>
        obtain ⟨_, hmk⟩ := role_member_kind_lt3_of_walks hsk hw ev101'
        rcases hmk with hmk | hmk | hmk <;> exact absurd (Value.field.inj hmk) (by decide)
    | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
      obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
      have hsk : roleSpecKindNat ro = 1 := by
        cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
      rcases roleSpecKind_of_roleWalksBound hw with h0 | h2 | h5 <;> omega
    | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
        ev14 ev47 _ ev80 ev100 _ ev124 ev238 hc279 =>
      obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
      obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
      have hsk : roleSpecKindNat ro = 2 := by
        cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
      have ext_m111 : Heap.Extends m2 m111 :=
        ev47.heap_extends.trans (ev80.heap_extends.trans
          (ev100.heap_extends.trans ev124.heap_extends))
      obtain ⟨_, _, _, _, _, _, m102_op, _, _, m111_op, _, _, m134_op, _,
        v161, m162, cs172, v191, m192, cs202, v232, v233, m235, cs243, m255, cs263, cs278,
        _, sg109, ev144, ev123, ev174, ev204, ev245, ev265, heq274, ev280, hc320⟩ :=
        Obs.«KernelRoles::validate_op».obs ev238
      have ext_sg : Heap.Extends m111 m102_op := by
        cases sg109 with
        | Safe _ _ he64 _ => rw [he64]
        | other _ heq95 _ _ _ => exact absurd (Value.field.inj heq95) zero_ne_one
      have ext_w : Heap.Extends m111 m111_op :=
        ext_sg.trans (ev144.heap_extends.trans ev123.heap_extends)
      have hrc_w := hrc.mono (ext_ba.trans (ext_m111.trans ext_w))
      have ha_w := S0.addr_mono (ext_m111.trans ext_w) ha_m2
      obtain ⟨_, recs_a, hmem_a, hcl_a, _⟩ := Claim.run_check_transitive_spec hrc_w ha_w ev174
      have htbl_m162 : TableRep c₀.t m162 x_tbl :=
        htbl.toTableRep.mono (ext_ba.trans (ext_m111.trans (ext_w.trans ev174.heap_extends)))
      obtain ⟨es, hlist_m192, hes⟩ := role_evidence_step c₀ ev204 x_tbl ro rfl htbl_m162
      obtain ⟨rfl, rfl⟩ := evList_length ev245 hlist_m192
      obtain ⟨rfl, k, hk0, hk10, rfl⟩ := op_equation_count_pos hsk ev265
      obtain ⟨arr₀, hmem_ev₀, harr_eq, _⟩ := nonempty_evidence_of_len_eq hk0 hk10 hes heq274
      have hrc_m255 := hrc_w.mono (ev174.heap_extends.trans ev204.heap_extends)
      obtain ⟨_, recs_ev, hcl_ev, hprfs⟩ :=
        validate_op_equations_full_walks hrc_m255 hlist_m192 ev280
      have hsub_a : ∀ cl ∈ cs172, cl ∈ calls := fun cl hm => by
        rw [hc279]; simp [show cl ∈ cs236 by rw [hc320]; simp [hm]]
      have hsub_ev : ∀ cl ∈ cs278, cl ∈ calls := fun cl hm => by
        rw [hc279]; simp [show cl ∈ cs236 by rw [hc320]; simp [hm]]
      refine ⟨recs_a.map (Claim.WalkedRec.mono hsub_a) ++ recs_ev.map (Claim.WalkedRec.mono hsub_ev),
        (hcl_a.mono hsub_a).append (hcl_ev.mono hsub_ev), ?_, ?_⟩
      · intro a' _ had'
        rw [had] at had'; injection had' with ha_eq; subst ha_eq
        rw [List.map_append, Claim.map_addr_walkedRec_mono]
        exact List.mem_append_left _ hmem_a
      · intro arr thm hm hthm
        have harr : arr = arr₀ := evidence_eq_of_wf hwf hm hmem_ev₀
        subst harr
        rw [harr_eq] at hthm
        rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
        exact List.mem_append_right _ (hprfs thm hthm)
    | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
      obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
      have hsk : roleSpecKindNat ro = 3 := by
        cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
      rcases roleSpecKind_of_roleWalksBound hw with h0 | h2 | h5 <;> omega
    | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
      obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
      have hsk : roleSpecKindNat ro = 4 := by
        cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
      rcases roleSpecKind_of_roleWalksBound hw with h0 | h2 | h5 <;> omega
    | n5 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs376
        ev14 ev47 _ ev80 ev100 _ ev124 ev378 hc419 =>
      obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
      obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
      have hsk : roleSpecKindNat ro = 5 := by
        cases ro <;> first | exact absurd (Value.field.inj hsk_f) (by decide) | rfl
      have ext_m111 : Heap.Extends m2 m111 :=
        ev47.heap_extends.trans (ev80.heap_extends.trans
          (ev100.heap_extends.trans ev124.heap_extends))
      obtain ⟨_, _, _, _, _, _, m101_eq, _, _, m130_eq, _, _, m151_eq, _, _, m182_eq, _,
        v209, m210, cs220, v239, m240, cs250, v280, v281, m283, cs291, m303, cs311, cs326,
        _, sg108, ev140, _, ev192, ev163, ev222, ev252, ev293, ev313, heq322, ev328, hc368⟩ :=
        Obs.«KernelRoles::validate_eqns».obs ev378
      have ext_sg : Heap.Extends m111 m101_eq := by
        cases sg108 with
        | Safe _ _ he63 _ => rw [he63]
        | other _ heq94 _ _ _ => exact absurd (Value.field.inj heq94) zero_ne_one
      have ext_w : Heap.Extends m111 m151_eq :=
        ext_sg.trans (ev140.heap_extends.trans (ev192.heap_extends.trans ev163.heap_extends))
      have hrc_w := hrc.mono (ext_ba.trans (ext_m111.trans ext_w))
      have ha_w := S0.addr_mono (ext_m111.trans ext_w) ha_m2
      obtain ⟨_, recs_a, hmem_a, hcl_a, _⟩ := Claim.run_check_transitive_spec hrc_w ha_w ev222
      have htbl_m210 : TableRep c₀.t m210 x_tbl :=
        htbl.toTableRep.mono (ext_ba.trans (ext_m111.trans (ext_w.trans ev222.heap_extends)))
      obtain ⟨es, hlist_m240, hes⟩ := role_evidence_step c₀ ev252 x_tbl ro rfl htbl_m210
      obtain ⟨rfl, rfl⟩ := evList_length ev293 hlist_m240
      obtain ⟨rfl, k, hk0, hk10, rfl⟩ := eqns_equation_count_pos hsk ev313
      obtain ⟨arr₀, hmem_ev₀, harr_eq, _⟩ := nonempty_evidence_of_len_eq hk0 hk10 hes heq322
      have hrc_m303 := hrc_w.mono (ev222.heap_extends.trans ev252.heap_extends)
      obtain ⟨_, recs_ev, hcl_ev, hprfs⟩ :=
        validate_eqns_equations_full_walks hrc_m303 hlist_m240 ev328
      have hsub_a : ∀ cl ∈ cs220, cl ∈ calls := fun cl hm => by
        rw [hc419]; simp [show cl ∈ cs376 by rw [hc368]; simp [hm]]
      have hsub_ev : ∀ cl ∈ cs326, cl ∈ calls := fun cl hm => by
        rw [hc419]; simp [show cl ∈ cs376 by rw [hc368]; simp [hm]]
      refine ⟨recs_a.map (Claim.WalkedRec.mono hsub_a) ++ recs_ev.map (Claim.WalkedRec.mono hsub_ev),
        (hcl_a.mono hsub_a).append (hcl_ev.mono hsub_ev), ?_, ?_⟩
      · intro a' _ had'
        rw [had] at had'; injection had' with ha_eq; subst ha_eq
        rw [List.map_append, Claim.map_addr_walkedRec_mono]
        exact List.mem_append_left _ hmem_a
      · intro arr thm hm hthm
        have harr : arr = arr₀ := evidence_eq_of_wf hwf hm hmem_ev₀
        subst harr
        rw [harr_eq] at hthm
        rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
        exact List.mem_append_right _ (hprfs thm hthm)
  · refine ⟨[], by simp [Claim.RecsClosed], fun _ hw' _ => absurd hw' hw, ?_⟩
    intro arr _ hm _
    have hreq := evidence_roleHasEquations_of_wf hwf hm
    have hw_true : roleWalksBound ro = true := by
      unfold roleHasEquations at hreq
      unfold roleWalksBound
      cases hsp : ro.spec (md := .anon) <;> rw [hsp] at hreq <;> first | cases hreq | rfl
    exact absurd hw_true hw

private theorem validate_group_roles_walks {t : Ix.Kernel.RoleTable} {g : Nat}
    {rs : List Ix.Kernel.Role} :
    ∀ {x_rc x_tbl x_rs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RCRep t (some (groupValLimit g)) h x_rc →
      TableRep t h x_tbl →
      RepList Obs.Names.«Lists::Node<Field>» repRoleNum h rs x_rs →
      ObsFn W "KernelRoles::validate_group_roles" [x_rc, x_tbl, x_rs] h r h' calls →
      Heap.Extends h h' ∧ ∀ ro ∈ rs, RoleValidatedAt t calls g ro
  | x_rc, x_tbl, x_rs, r, h, h', calls, hrc, htbl, hlist, ev => by
    cases Obs.«KernelRoles::validate_group_roles».obs ev with
    | Nil ld12 _ he23 _ =>
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm)⟩
    | Cons x_r x_rest v42 m43 cs53 cs83 ld12 ev55 ev85 hc110 =>
      obtain ⟨ro₀, rest, rfl, hro, hrest⟩ := Lib.rep_cons_of_load hlist ld12
      rw [hro] at ev55
      obtain ⟨ext1, hval1⟩ := validate_role_walks hrc htbl ev55
      obtain ⟨ext2, hval2⟩ :=
        validate_group_roles_walks (hrc.mono ext1) (htbl.mono ext1)
          (repList_heapMono₂ _ repRoleNum_heapMono₂ ext1 hrest) ev85
      have hsub1 : ∀ cl ∈ cs53, cl ∈ calls := fun cl hm => by rw [hc110]; simp [hm]
      have hsub2 : ∀ cl ∈ cs83, cl ∈ calls := fun cl hm => by rw [hc110]; simp [hm]
      refine ⟨ext1.trans ext2, fun ro hmem => ?_⟩
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact hval1.mono hsub1
      · exact (hval2 ro hmem').mono hsub2

private theorem validate_group_roles_full_walks {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {g : Nat} {rs : List Ix.Kernel.Role} :
    ∀ {x_rc x_tbl x_rs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.RCFullRep t bAddr (groupValLimit g) h x_rc →
      Claim.TableFullRep t bAddr h x_tbl →
      RepList Obs.Names.«Lists::Node<Field>» repRoleNum h rs x_rs →
      ObsFn W "KernelRoles::validate_group_roles" [x_rc, x_tbl, x_rs] h r h' calls →
      Heap.Extends h h' ∧
      (∀ ro ∈ rs, RoleValidatedAt t calls g ro) ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ ro ∈ rs, ∀ a, roleWalksBound ro = true → t.addressOf? ro = some a →
          a ∈ recs.map (·.addr)) ∧
        (∀ ro ∈ rs, ∀ arr thm, (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList →
          thm ∈ recs.map (·.addr))
  | x_rc, x_tbl, x_rs, r, h, h', calls, hrc, htbl, hlist, ev => by
    cases Obs.«KernelRoles::validate_group_roles».obs ev with
    | Nil ld12 _ he23 _ =>
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm), [], by simp [Claim.RecsClosed],
        fun _ hm => (nomatch hm), fun _ hm => (nomatch hm)⟩
    | Cons x_r x_rest v42 m43 cs53 cs83 ld12 ev55 ev85 hc110 =>
      obtain ⟨ro₀, rest, rfl, hro, hrest⟩ := Lib.rep_cons_of_load hlist ld12
      rw [hro] at ev55
      obtain ⟨ext1, hval1, recs₁, hcl₁, ha₁, hev₁⟩ := validate_role_full_walks hrc htbl ev55
      obtain ⟨ext2, hval2, recs₂, hcl₂, ha₂, hev₂⟩ :=
        validate_group_roles_full_walks (hrc.mono ext1) (htbl.mono ext1)
          (repList_heapMono₂ _ repRoleNum_heapMono₂ ext1 hrest) ev85
      have hsub1 : ∀ cl ∈ cs53, cl ∈ calls := fun cl hm => by rw [hc110]; simp [hm]
      have hsub2 : ∀ cl ∈ cs83, cl ∈ calls := fun cl hm => by rw [hc110]; simp [hm]
      refine ⟨ext1.trans ext2, ?_,
        recs₁.map (Claim.WalkedRec.mono hsub1) ++ recs₂.map (Claim.WalkedRec.mono hsub2),
        (hcl₁.mono hsub1).append (hcl₂.mono hsub2), ?_, ?_⟩
      · intro ro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact hval1.mono hsub1
        · exact (hval2 ro hmem').mono hsub2
      · intro ro hmem a hw had
        rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact List.mem_append_left _ (ha₁ a hw had)
        · exact List.mem_append_right _ (ha₂ ro hmem' a hw had)
      · intro ro hmem arr thm hm hthm
        rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact List.mem_append_left _ (hev₁ arr thm hm hthm)
        · exact List.mem_append_right _ (hev₂ ro hmem' arr thm hm hthm)

/-! ## `group_admit` and `group_admit_needs` -/

private theorem group_admit_needs_walks {t : Ix.Kernel.RoleTable} {g : Nat}
    (ih_g : ∀ g' < g, ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      TableRep t h x_tbl →
      ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g' : F)] h r h' calls →
      Heap.Extends h h' ∧
      ∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', RoleValidatedAt t calls g'' ro)
    {needs : List Ix.Kernel.Role} (hsub_needs : ∀ ro ∈ needs, ro ∈ groupNeededRoles g) :
    ∀ {x_tbl x_needs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      TableRep t h x_tbl →
      RepList Obs.Names.«Lists::Node<Field>» repRoleNum h needs x_needs →
      ObsFn W "KernelRoles::group_admit_needs" [x_tbl, x_needs] h r h' calls →
      Heap.Extends h h' ∧
      ∀ ro₀ ∈ needs, ∀ g'', GroupReachable (Ix.SpecDigest.groupOf ro₀) g'' →
        ∀ ro ∈ groupRoles g'', RoleValidatedAt t calls g'' ro
  | x_tbl, x_needs, r, h, h', calls, htbl, hlist, ev => by
    cases Obs.«KernelRoles::group_admit_needs».obs ev with
    | Nil ld12 _ he23 _ =>
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm)⟩
    | Cons x_r x_rest v42 m43 cs53 v57 m66 cs74 cs88 ld12 ev76 ev55 ev90 hc107 =>
      obtain ⟨ro_h, rest, rfl, hro, hrest⟩ := Lib.rep_cons_of_load hlist ld12
      rw [hro] at ev76
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev76
      have hlt_g : Ix.SpecDigest.groupOf ro_h < g :=
        groupNeeds_groupOf_lt (hsub_needs ro_h (List.mem_cons_self ..))
      obtain ⟨ext1, hval1⟩ := ih_g (Ix.SpecDigest.groupOf ro_h) hlt_g htbl ev55
      obtain ⟨ext2, hval2⟩ :=
        group_admit_needs_walks ih_g
          (fun ro hm => hsub_needs ro (List.mem_cons_of_mem _ hm))
          (htbl.mono ext1)
          (repList_heapMono₂ _ repRoleNum_heapMono₂ ext1 hrest) ev90
      have hsub1 : ∀ cl ∈ cs53, cl ∈ calls := fun cl hm => by rw [hc107]; simp [hm]
      have hsub2 : ∀ cl ∈ cs88, cl ∈ calls := fun cl hm => by rw [hc107]; simp [hm]
      refine ⟨ext1.trans ext2, fun ro₀ hmem g'' hr ro hro_in => ?_⟩
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact (hval1 g'' hr ro hro_in).mono hsub1
      · exact (hval2 ro₀ hmem' g'' hr ro hro_in).mono hsub2

/-- **`KernelRoles::group_admit(tbl, .field (g : F))` (`g < 2^32`) under `TableRep`**:
validates every role in `groupRoles g` and in every transitively needed group
`GroupReachable g g'`. -/
theorem group_admit_nat_spec {t : Ix.Kernel.RoleTable} :
    ∀ (g : Nat), g < 4294967296 →
      ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        TableRep t h x_tbl →
        ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g : F)] h r h' calls →
        Heap.Extends h h' ∧
        ∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', RoleValidatedAt t calls g' ro := by
  intro g
  refine Nat.strongRecOn g fun g ih hg x_tbl r h h' calls htbl ev => ?_
  obtain ⟨v1, m2, cs12, v16, m25, cs33, m45, v60, m70, cs78, cs101, v106, m122, cs130,
    ev35, ev14, hm55, ev80, ev132, ev103, hc141⟩ :=
    Obs.«KernelRoles::group_admit».obs ev
  obtain ⟨rfl, rfl⟩ := group_validation_limit_of_nat hg ev80
  obtain ⟨ext_gn, hneeds_rep⟩ := group_needs_spec hg ev35
  have ih_lt : ∀ g' < g, ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      TableRep t h x_tbl →
      ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g' : F)] h r h' calls →
      Heap.Extends h h' ∧
      ∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', RoleValidatedAt t calls g'' ro :=
    fun g' hlt => ih g' hlt (Nat.lt_trans hlt hg)
  obtain ⟨ext_gan, hval_needs⟩ :=
    group_admit_needs_walks ih_lt (fun _ hm => hm) (htbl.mono ext_gn) hneeds_rep ev14
  let rcNode := Value.construct rcEnum "Mk"
    [x_tbl, .field (groupValLimit g : F), .construct addrMapEnum "Nil" []]
  have ext_m45 : Heap.Extends h m45 :=
    ext_gn.trans (ext_gan.trans (by rw [hm55]; exact Heap.Extends.snoc m70 rcNode))
  have hld_rc : loadValue m45 (.ptr (.enum rcEnum) m70.length) = .ok rcNode := by
    rw [hm55]
    exact Claim.loadValue_snoc_construct m70 rcEnum "Mk"
      [x_tbl, .field (groupValLimit g : F), .construct addrMapEnum "Nil" []]
  have hrc_m45 : RCRep t (some (groupValLimit g)) m45 (.ptr (.enum rcEnum) m70.length) :=
    ⟨x_tbl, .construct addrMapEnum "Nil" [], _, hld_rc,
      .inl ⟨groupValLimit g, rfl, groupValLimit_lt_u32 g, rfl⟩, htbl.mono ext_m45⟩
  obtain ⟨ext_gr, hroles_rep⟩ := group_roles_spec hg ev132
  obtain ⟨ext_vgr, hval_here⟩ :=
    validate_group_roles_walks (hrc_m45.mono ext_gr) ((htbl.mono ext_m45).mono ext_gr)
      hroles_rep ev103
  have hsub_needs_cs : ∀ cl ∈ cs12, cl ∈ calls := fun cl hm => by rw [hc141]; simp [hm]
  have hsub_here_cs : ∀ cl ∈ cs101, cl ∈ calls := fun cl hm => by rw [hc141]; simp [hm]
  refine ⟨ext_m45.trans (ext_gr.trans ext_vgr), fun g' hr ro hro => ?_⟩
  cases hr with
  | refl => exact (hval_here ro hro).mono hsub_here_cs
  | step hm hr' => exact (hval_needs _ hm g' hr' ro hro).mono hsub_needs_cs

/-- **`KernelRoles::group_admit(tbl, x_g)` under `TableRep`**: forces `x_g = .field (g : F)` with
`g < 2^32` and extracts `RoleValidatedAt` across all `GroupReachable g g'`. -/
theorem group_admit_spec {t : Ix.Kernel.RoleTable}
    {x_tbl x_g r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (htbl : TableRep t h x_tbl)
    (ev : ObsFn W "KernelRoles::group_admit" [x_tbl, x_g] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ g : Nat, g < 4294967296 ∧ x_g = .field (g : F) ∧
      ∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', RoleValidatedAt t calls g' ro := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev80, _, _, _⟩ :=
    Obs.«KernelRoles::group_admit».obs ev
  obtain ⟨_, g, hg, rfl, _⟩ := group_validation_limit_exact ev80
  obtain ⟨ext, hval⟩ := group_admit_nat_spec g hg htbl ev
  exact ⟨ext, g, hg, rfl, hval⟩

private theorem group_admit_needs_full_walks {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {g : Nat}
    (ih_g : ∀ g' < g, ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.TableFullRep t bAddr h x_tbl →
      ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g' : F)] h r h' calls →
      Heap.Extends h h' ∧
      (∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', RoleValidatedAt t calls g'' ro) ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', ∀ a,
          roleWalksBound ro = true → t.addressOf? ro = some a → a ∈ recs.map (·.addr)) ∧
        (∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', ∀ arr thm,
          (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr)))
    {needs : List Ix.Kernel.Role} (hsub_needs : ∀ ro ∈ needs, ro ∈ groupNeededRoles g) :
    ∀ {x_tbl x_needs r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.TableFullRep t bAddr h x_tbl →
      RepList Obs.Names.«Lists::Node<Field>» repRoleNum h needs x_needs →
      ObsFn W "KernelRoles::group_admit_needs" [x_tbl, x_needs] h r h' calls →
      Heap.Extends h h' ∧
      (∀ ro₀ ∈ needs, ∀ g'', GroupReachable (Ix.SpecDigest.groupOf ro₀) g'' →
        ∀ ro ∈ groupRoles g'', RoleValidatedAt t calls g'' ro) ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ ro₀ ∈ needs, ∀ g'', GroupReachable (Ix.SpecDigest.groupOf ro₀) g'' →
          ∀ ro ∈ groupRoles g'', ∀ a,
            roleWalksBound ro = true → t.addressOf? ro = some a → a ∈ recs.map (·.addr)) ∧
        (∀ ro₀ ∈ needs, ∀ g'', GroupReachable (Ix.SpecDigest.groupOf ro₀) g'' →
          ∀ ro ∈ groupRoles g'', ∀ arr thm,
            (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr))
  | x_tbl, x_needs, r, h, h', calls, htbl, hlist, ev => by
    cases Obs.«KernelRoles::group_admit_needs».obs ev with
    | Nil ld12 _ he23 _ =>
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm), [], by simp [Claim.RecsClosed],
        fun _ hm => (nomatch hm), fun _ hm => (nomatch hm)⟩
    | Cons x_r x_rest v42 m43 cs53 v57 m66 cs74 cs88 ld12 ev76 ev55 ev90 hc107 =>
      obtain ⟨ro_h, rest, rfl, hro, hrest⟩ := Lib.rep_cons_of_load hlist ld12
      rw [hro] at ev76
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev76
      have hlt_g : Ix.SpecDigest.groupOf ro_h < g :=
        groupNeeds_groupOf_lt (hsub_needs ro_h (List.mem_cons_self ..))
      obtain ⟨ext1, hval1, recs₁, hcl₁, ha₁, hev₁⟩ :=
        ih_g (Ix.SpecDigest.groupOf ro_h) hlt_g htbl ev55
      obtain ⟨ext2, hval2, recs₂, hcl₂, ha₂, hev₂⟩ :=
        group_admit_needs_full_walks ih_g
          (fun ro hm => hsub_needs ro (List.mem_cons_of_mem _ hm))
          (htbl.mono ext1)
          (repList_heapMono₂ _ repRoleNum_heapMono₂ ext1 hrest) ev90
      have hsub1 : ∀ cl ∈ cs53, cl ∈ calls := fun cl hm => by rw [hc107]; simp [hm]
      have hsub2 : ∀ cl ∈ cs88, cl ∈ calls := fun cl hm => by rw [hc107]; simp [hm]
      refine ⟨ext1.trans ext2, ?_,
        recs₁.map (Claim.WalkedRec.mono hsub1) ++ recs₂.map (Claim.WalkedRec.mono hsub2),
        (hcl₁.mono hsub1).append (hcl₂.mono hsub2), ?_, ?_⟩
      · intro ro₀ hmem g'' hr ro hro_in
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact (hval1 g'' hr ro hro_in).mono hsub1
        · exact (hval2 ro₀ hmem' g'' hr ro hro_in).mono hsub2
      · intro ro₀ hmem g'' hr ro hro_in a hw had
        rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact List.mem_append_left _ (ha₁ g'' hr ro hro_in a hw had)
        · exact List.mem_append_right _ (ha₂ ro₀ hmem' g'' hr ro hro_in a hw had)
      · intro ro₀ hmem g'' hr ro hro_in arr thm hm hthm
        rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact List.mem_append_left _ (hev₁ g'' hr ro hro_in arr thm hm hthm)
        · exact List.mem_append_right _ (hev₂ ro₀ hmem' g'' hr ro hro_in arr thm hm hthm)

/-- **`KernelRoles::group_admit(tbl, .field (g : F))` (`g < 2^32`) under `Claim.TableFullRep`**:
extracts both `RoleValidatedAt` and a closed list of `Claim.WalkedRec`s covering every walked bound
address and every `.proof thm` evidence entry across all `GroupReachable g g'`. -/
theorem group_admit_full_nat_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} :
    ∀ (g : Nat), g < 4294967296 →
      ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        Claim.TableFullRep t bAddr h x_tbl →
        ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g : F)] h r h' calls →
        Heap.Extends h h' ∧
        (∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', RoleValidatedAt t calls g' ro) ∧
        ∃ recs : List (Claim.WalkedRec calls bAddr t),
          Claim.RecsClosed recs ∧
          (∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', ∀ a,
            roleWalksBound ro = true → t.addressOf? ro = some a → a ∈ recs.map (·.addr)) ∧
          (∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', ∀ arr thm,
            (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr)) := by
  intro g
  refine Nat.strongRecOn g fun g ih hg x_tbl r h h' calls htbl ev => ?_
  obtain ⟨v1, m2, cs12, v16, m25, cs33, m45, v60, m70, cs78, cs101, v106, m122, cs130,
    ev35, ev14, hm55, ev80, ev132, ev103, hc141⟩ :=
    Obs.«KernelRoles::group_admit».obs ev
  obtain ⟨rfl, rfl⟩ := group_validation_limit_of_nat hg ev80
  obtain ⟨ext_gn, hneeds_rep⟩ := group_needs_spec hg ev35
  have ih_lt : ∀ g' < g, ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      Claim.TableFullRep t bAddr h x_tbl →
      ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g' : F)] h r h' calls →
      Heap.Extends h h' ∧
      (∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', RoleValidatedAt t calls g'' ro) ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', ∀ a,
          roleWalksBound ro = true → t.addressOf? ro = some a → a ∈ recs.map (·.addr)) ∧
        (∀ g'', GroupReachable g' g'' → ∀ ro ∈ groupRoles g'', ∀ arr thm,
          (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr)) :=
    fun g' hlt => ih g' hlt (Nat.lt_trans hlt hg)
  obtain ⟨ext_gan, hval_needs, recs_n, hcl_n, ha_n, hev_n⟩ :=
    group_admit_needs_full_walks ih_lt (fun _ hm => hm) (htbl.mono ext_gn) hneeds_rep ev14
  let rcNode := Value.construct rcEnum "Mk"
    [x_tbl, .field (groupValLimit g : F), .construct addrMapEnum "Nil" []]
  have ext_m45 : Heap.Extends h m45 :=
    ext_gn.trans (ext_gan.trans (by rw [hm55]; exact Heap.Extends.snoc m70 rcNode))
  have hld_rc : loadValue m45 (.ptr (.enum rcEnum) m70.length) = .ok rcNode := by
    rw [hm55]
    exact Claim.loadValue_snoc_construct m70 rcEnum "Mk"
      [x_tbl, .field (groupValLimit g : F), .construct addrMapEnum "Nil" []]
  have hrc_m45 : Claim.RCFullRep t bAddr (groupValLimit g) m45 (.ptr (.enum rcEnum) m70.length) :=
    ⟨groupValLimit_lt_u32 g, x_tbl, hld_rc, htbl.mono ext_m45⟩
  obtain ⟨ext_gr, hroles_rep⟩ := group_roles_spec hg ev132
  obtain ⟨ext_vgr, hval_here, recs_h, hcl_h, ha_h, hev_h⟩ :=
    validate_group_roles_full_walks (hrc_m45.mono ext_gr) ((htbl.mono ext_m45).mono ext_gr)
      hroles_rep ev103
  have hsub_n : ∀ cl ∈ cs12, cl ∈ calls := fun cl hm => by rw [hc141]; simp [hm]
  have hsub_h : ∀ cl ∈ cs101, cl ∈ calls := fun cl hm => by rw [hc141]; simp [hm]
  refine ⟨ext_m45.trans (ext_gr.trans ext_vgr), ?_,
    recs_n.map (Claim.WalkedRec.mono hsub_n) ++ recs_h.map (Claim.WalkedRec.mono hsub_h),
    (hcl_n.mono hsub_n).append (hcl_h.mono hsub_h), ?_, ?_⟩
  · intro g' hr ro hro
    cases hr with
    | refl => exact (hval_here ro hro).mono hsub_h
    | step hm hr' => exact (hval_needs _ hm g' hr' ro hro).mono hsub_n
  · intro g' hr ro hro a hw had
    rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
    cases hr with
    | refl => exact List.mem_append_right _ (ha_h ro hro a hw had)
    | step hm hr' => exact List.mem_append_left _ (ha_n _ hm g' hr' ro hro a hw had)
  · intro g' hr ro hro arr thm hm_ev hthm
    rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
    cases hr with
    | refl => exact List.mem_append_right _ (hev_h ro hro arr thm hm_ev hthm)
    | step hm hr' => exact List.mem_append_left _ (hev_n _ hm g' hr' ro hro arr thm hm_ev hthm)

/-- **`KernelRoles::group_admit(tbl, x_g)` under `Claim.TableFullRep`**. -/
theorem group_admit_full_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {x_tbl x_g r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::group_admit" [x_tbl, x_g] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ g : Nat, g < 4294967296 ∧ x_g = .field (g : F) ∧
      (∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', RoleValidatedAt t calls g' ro) ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', ∀ a,
          roleWalksBound ro = true → t.addressOf? ro = some a → a ∈ recs.map (·.addr)) ∧
        (∀ g', GroupReachable g g' → ∀ ro ∈ groupRoles g', ∀ arr thm,
          (ro, arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev80, _, _, _⟩ :=
    Obs.«KernelRoles::group_admit».obs ev
  obtain ⟨_, g, hg, rfl, _⟩ := group_validation_limit_exact ev80
  obtain ⟨ext, hval, recs, hcl, ha, hev⟩ := group_admit_full_nat_spec g hg htbl ev
  exact ⟨ext, g, hg, rfl, hval, recs, hcl, ha, hev⟩

/-! ## `role_addr`, `role_used_implicitly`, and `role_of` -/

/-- **`KernelRoles::role_addr(rc, .field (roleNum ro))` under `RCRep`**:
extracts the bound address `a` (`t.addressOf? ro = some a`, `S0.addr h' r a`), and when `rc` is a
validating `Mk` context (`lim = some n`), extracts `groupOf ro < n`, `GroupAdmitIn`, and
`RoleValidatedAt` across all `GroupReachable (groupOf ro) g'`. -/
theorem role_addr_admit_spec {t : Ix.Kernel.RoleTable} {lim : Option Nat} {ro : Ix.Kernel.Role}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCRep t lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_addr" [x_rc, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ a : _root_.Address, S0.addr h' r a ∧ t.addressOf? ro = some a ∧
      (∀ n, lim = some n →
        Ix.SpecDigest.groupOf ro < n ∧
        GroupAdmitIn calls t (Ix.SpecDigest.groupOf ro) ∧
        ∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' →
          ∀ ro' ∈ groupRoles g', RoleValidatedAt t calls g' ro') := by
  obtain ⟨tbl, ax, node, hload, hnode, htbl⟩ := hrc
  cases Obs.«KernelRoles::role_addr».obs ev with
  | Mk x_tbl x_limit w20 v47 m50 cs58 v61 m64 cs72 v97 m98 cs108 v127 m128 cs138
      v142 m151 cs159 ld12 ev74 ev60 heq96 ev110 ev161 ev140 he171 he172 hc173 =>
    rw [hload] at ld12
    rcases hnode with ⟨n, hlim, hn_lt, rfl⟩ | ⟨_, rfl⟩
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt hxs1
      injection hxs1 with hxl
      subst hxt hxl
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev74
      subst heq96
      obtain ⟨_, _, hlt_iff, _, rfl⟩ := Lib.less_than_fields_field ev60
      have hlt_val : ZMod.val (Ix.SpecDigest.groupOf ro : F) < ZMod.val (n : F) := hlt_iff.mp rfl
      rw [RolesAux.val_groupOf, RolesAux.val_natCast (Nat.lt_trans hn_lt (by decide))] at hlt_val
      obtain ⟨ext_ba, a, ha_m98, had⟩ := role_bound_addr_uncond htbl ev110
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev161
      have hg_lt : Ix.SpecDigest.groupOf ro < 4294967296 :=
        Nat.lt_trans (groupOf_lt_77 ro) (by decide)
      obtain ⟨ext_ga, hval_ga⟩ := group_admit_nat_spec _ hg_lt (htbl.mono ext_ba) ev140
      have hsub_ga : ∀ cl ∈ cs138, cl ∈ calls := fun cl hm => by rw [hc173]; simp [hm]
      subst he171 he172
      refine ⟨ext_ba.trans ext_ga, a, S0.addr_mono ext_ga ha_m98, had, fun n' hn' => ?_⟩
      rw [hlim] at hn'
      injection hn' with hnn
      subst hnn
      exact ⟨hlt_val, ⟨_, _, tbl, v127, cs138, htbl.mono ext_ba, ev140,
        by rw [hc173]; simp, hsub_ga⟩, fun g' hr ro' hro' => (hval_ga g' hr ro' hro').mono hsub_ga⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
  | Assumed x_tbl w181 cs195 ld12 ev197 _ =>
    rw [hload] at ld12
    rcases hnode with ⟨_, _, _, rfl⟩ | ⟨hlim, rfl⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt
      subst hxt
      obtain ⟨ext_ba, a, ha_h', had⟩ := role_bound_addr_uncond htbl ev197
      exact ⟨ext_ba, a, ha_h', had, fun n hn => by rw [hlim] at hn; cases hn⟩

/-- **`KernelRoles::role_addr(rc, .field (roleNum ro))` under `Claim.RCFullRep`**. -/
theorem role_addr_full_admit_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Nat} {ro : Ix.Kernel.Role}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_addr" [x_rc, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧
    Ix.SpecDigest.groupOf ro < lim ∧
    GroupAdmitIn calls t (Ix.SpecDigest.groupOf ro) ∧
    (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' →
      ∀ ro' ∈ groupRoles g', RoleValidatedAt t calls g' ro') ∧
    ∃ a : _root_.Address, S0.addr h' r a ∧ t.addressOf? ro = some a ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' → ∀ ro' ∈ groupRoles g', ∀ a',
          roleWalksBound ro' = true → t.addressOf? ro' = some a' → a' ∈ recs.map (·.addr)) ∧
        (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' → ∀ ro' ∈ groupRoles g', ∀ arr thm,
          (ro', arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr)) := by
  obtain ⟨ext, a, ha, had, hmk⟩ := role_addr_admit_spec hrc.toRCRep ev
  obtain ⟨hlt, hga, hval⟩ := hmk lim rfl
  obtain ⟨_, tbl, hload, htbl⟩ := hrc
  cases Obs.«KernelRoles::role_addr».obs ev with
  | Assumed _ _ _ ld12 _ _ =>
    rw [hload] at ld12
    exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
  | Mk x_tbl _ _ _ m50 _ _ m64 _ _ m98 _ _ m128 cs138 _ m151 _
      ld12 ev74 ev60 _ ev110 ev161 ev140 _ _ hc173 =>
    rw [hload] at ld12
    injection ld12 with hv
    injection hv with _ _ hxs
    injection hxs with hxt _
    subst hxt
    obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev161
    have ext_m151 := ev74.heap_extends.trans (ev60.heap_extends.trans ev110.heap_extends)
    have hg_lt : Ix.SpecDigest.groupOf ro < 4294967296 :=
      Nat.lt_trans (groupOf_lt_77 ro) (by decide)
    obtain ⟨_, _, recs_ga, hcl_ga, ha_ga, hev_ga⟩ :=
      group_admit_full_nat_spec _ hg_lt (htbl.mono ext_m151) ev140
    have hsub_ga : ∀ cl ∈ cs138, cl ∈ calls := fun cl hm => by rw [hc173]; simp [hm]
    refine ⟨ext, hlt, hga, hval, a, ha, had, recs_ga.map (Claim.WalkedRec.mono hsub_ga),
      hcl_ga.mono hsub_ga, ?_, ?_⟩
    · intro g' hr ro' hro' a' hw had'
      rw [Claim.map_addr_walkedRec_mono]
      exact ha_ga g' hr ro' hro' a' hw had'
    · intro g' hr ro' hro' arr thm hm hthm
      rw [Claim.map_addr_walkedRec_mono]
      exact hev_ga g' hr ro' hro' arr thm hm hthm

/-- **`KernelRoles::role_used_implicitly(rc, .field (roleNum ro))` under `RCRep`**:
extracts the bound address `a` (`t.addressOf? ro = some a`, `S0.addr h' r a`), the direct
`RunCheckIn calls t lim a` walk of `a` (present in both `Mk` and `Assumed` contexts), and when
`rc` is `Mk(tbl, n, ax)` (`lim = some n`), also `groupOf ro < n`, `GroupAdmitIn`, and
`RoleValidatedAt` across all `GroupReachable (groupOf ro) g'`. -/
theorem role_used_implicitly_spec {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {ro : Ix.Kernel.Role}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCRep t lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_used_implicitly" [x_rc, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ a : _root_.Address, S0.addr h' r a ∧ t.addressOf? ro = some a ∧
      RunCheckIn calls t lim a ∧
      (∀ n, lim = some n →
        Ix.SpecDigest.groupOf ro < n ∧
        GroupAdmitIn calls t (Ix.SpecDigest.groupOf ro) ∧
        ∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' →
          ∀ ro' ∈ groupRoles g', RoleValidatedAt t calls g' ro') := by
  obtain ⟨v1, m2, cs12, v31, m32, cs42, ev14, ev44, rfl, rfl, hc64⟩ :=
    Obs.«KernelRoles::role_used_implicitly».obs ev
  obtain ⟨ext1, a, ha_m2, had, hmk⟩ := role_addr_admit_spec hrc ev14
  have hsub1 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hm => by rw [hc64]; simp [hm]
  have hwalk_a : RunCheckIn calls t lim a :=
    ⟨_, _, x_rc, _, v31, cs42, hrc.mono ext1, ha_m2, ev44,
      by rw [hc64]; simp, fun cl hm => by rw [hc64]; simp [hm]⟩
  refine ⟨ext1.trans ev44.heap_extends, a, S0.addr_mono ev44.heap_extends ha_m2, had, hwalk_a,
    fun n hn => ?_⟩
  obtain ⟨hlt, hga, hval⟩ := hmk n hn
  exact ⟨hlt, hga.mono hsub1, fun g' hr ro' hro' => (hval g' hr ro' hro').mono hsub1⟩

/-- **`KernelRoles::role_used_implicitly(rc, .field (roleNum ro))` under `Claim.RCFullRep`**:
extracts `groupOf ro < lim`, `GroupAdmitIn`, `RoleValidatedAt`, and a single closed list of
`Claim.WalkedRec`s covering `a` itself as well as every walked bound role and `.proof thm`
evidence entry of `GroupReachable (groupOf ro) g'`. -/
theorem role_used_implicitly_full_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Nat} {ro : Ix.Kernel.Role}
    {x_rc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr lim h x_rc)
    (ev : ObsFn W "KernelRoles::role_used_implicitly" [x_rc, .field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧
    Ix.SpecDigest.groupOf ro < lim ∧
    GroupAdmitIn calls t (Ix.SpecDigest.groupOf ro) ∧
    (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' →
      ∀ ro' ∈ groupRoles g', RoleValidatedAt t calls g' ro') ∧
    ∃ a : _root_.Address, S0.addr h' r a ∧ t.addressOf? ro = some a ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        a ∈ recs.map (·.addr) ∧
        (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' → ∀ ro' ∈ groupRoles g', ∀ a',
          roleWalksBound ro' = true → t.addressOf? ro' = some a' → a' ∈ recs.map (·.addr)) ∧
        (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' → ∀ ro' ∈ groupRoles g', ∀ arr thm,
          (ro', arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr)) := by
  obtain ⟨v1, m2, cs12, v31, m32, cs42, ev14, ev44, rfl, rfl, hc64⟩ :=
    Obs.«KernelRoles::role_used_implicitly».obs ev
  obtain ⟨ext1, hlt, hga, hval, a, ha_m2, had, recs_ga, hcl_ga, ha_ga, hev_ga⟩ :=
    role_addr_full_admit_spec hrc ev14
  obtain ⟨ext2, recs_a, hmem_a, hcl_a, _⟩ :=
    Claim.run_check_transitive_spec (hrc.mono ext1) ha_m2 ev44
  have hsub1 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hm => by rw [hc64]; simp [hm]
  have hsub2 : ∀ cl ∈ cs42, cl ∈ calls := fun cl hm => by rw [hc64]; simp [hm]
  refine ⟨ext1.trans ext2, hlt, hga.mono hsub1,
    fun g' hr ro' hro' => (hval g' hr ro' hro').mono hsub1,
    a, S0.addr_mono ext2 ha_m2, had,
    recs_ga.map (Claim.WalkedRec.mono hsub1) ++ recs_a.map (Claim.WalkedRec.mono hsub2),
    (hcl_ga.mono hsub1).append (hcl_a.mono hsub2), ?_, ?_, ?_⟩
  · rw [List.map_append, Claim.map_addr_walkedRec_mono, Claim.map_addr_walkedRec_mono]
    exact List.mem_append_right _ hmem_a
  · intro g' hr ro' hro' a' hw had'
    rw [List.map_append, Claim.map_addr_walkedRec_mono]
    exact List.mem_append_left _ (ha_ga g' hr ro' hro' a' hw had')
  · intro g' hr ro' hro' arr thm hm hthm
    rw [List.map_append, Claim.map_addr_walkedRec_mono]
    exact List.mem_append_left _ (hev_ga g' hr ro' hro' arr thm hm hthm)

/-- **`KernelRoles::role_of(rc, ap)` under `RCRep`**: either returns `0`, or returns
`roleNum ro + 1` with `t.addressOf? ro = some addr`, and when `lim = some n`, `groupOf ro < n`,
`GroupAdmitIn`, and `RoleValidatedAt` across all `GroupReachable (groupOf ro) g'`. -/
theorem role_of_admit_spec {t : Ix.Kernel.RoleTable} {lim : Option Nat} {addr : _root_.Address}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCRep t lim h x_rc) (ha : S0.addr h x_a addr)
    (ev : ObsFn W "KernelRoles::role_of" [x_rc, x_a] h r h' calls) :
    Heap.Extends h h' ∧
    (r = .field 0 ∨
      ∃ ro : Ix.Kernel.Role,
        r = .field (roleNum ro + 1) ∧
        t.addressOf? ro = some addr ∧
        (∀ n, lim = some n →
          Ix.SpecDigest.groupOf ro < n ∧
          GroupAdmitIn calls t (Ix.SpecDigest.groupOf ro) ∧
          ∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' →
            ∀ ro' ∈ groupRoles g', RoleValidatedAt t calls g' ro')) := by
  let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
  obtain ⟨a_bytes, ha_rep, rfl⟩ := ha
  obtain ⟨tbl, ax, node, hload, hnode, htbl⟩ := hrc
  refine ⟨ev.heap_extends, ?_⟩
  cases Obs.«KernelRoles::role_of».obs ev with
  | Mk_n0 _ _ _ _ _ _ _ _ _ _ _ he100 _ _ =>
    exact .inl he100
  | Mk_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he222 _ _ =>
    exact .inl he222
  | Mk_other_n1 x_tbl x_limit w20 v36 m37 cs47 v51 m61 cs69 m108 cs119 v122 m125 cs133 v136
      v163 m164 cs174 v178 m187 cs195 v198
      ld12 ev71 ev49 hne103 op150 ev135 ev121 op212 ev197 ev176 he215 _ hc217 =>
    rw [hload] at ld12
    rcases hnode with ⟨n, hlim, hn_lt, rfl⟩ | ⟨_, rfl⟩
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt hxs1
      injection hxs1 with hxl
      subst hxt hxl
      obtain ⟨rfl, hIdx⟩ := role_addr_index_step c₀ ev71 tbl rfl htbl
      have hlookup :=
        rbtree_map_lookup_or_default_field_step c₀ ev49
          x_a v51 (.field 0) rfl a_bytes ha_rep (IndexEntry c₀.t) hIdx
      rcases hlookup with hv0 | ⟨ro, hv36, had⟩
      · exact absurd hv0 hne103
      · subst hv36
        obtain ⟨y, hy1, rfl⟩ := RolesAux.evalBinOp_sub_field_left_inv op150
        injection hy1 with hy
        subst hy
        have hsub : roleNum ro + 1 - 1 = roleNum ro := add_sub_cancel_right _ _
        rw [hsub] at ev135
        obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev135
        obtain ⟨_, _, hlt_iff, _, rfl⟩ := Lib.less_than_fields_field ev121
        have hlt_val : ZMod.val (Ix.SpecDigest.groupOf ro : F) < ZMod.val (n : F) := hlt_iff.mp rfl
        rw [RolesAux.val_groupOf, RolesAux.val_natCast (Nat.lt_trans hn_lt (by decide))] at hlt_val
        obtain ⟨y2, hy2, rfl⟩ := RolesAux.evalBinOp_sub_field_left_inv op212
        injection hy2 with hy2_eq
        subst hy2_eq
        rw [hsub] at ev197
        obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev197
        have ext_m := ev71.heap_extends.trans ev49.heap_extends
        have hg_lt : Ix.SpecDigest.groupOf ro < 4294967296 :=
          Nat.lt_trans (groupOf_lt_77 ro) (by decide)
        obtain ⟨_, hval_ga⟩ := group_admit_nat_spec _ hg_lt (htbl.mono ext_m) ev176
        have hsub_ga : ∀ cl ∈ cs174, cl ∈ calls := fun cl hm => by rw [hc217]; simp [hm]
        refine .inr ⟨ro, he215, had, fun n' hn' => ?_⟩
        rw [hlim] at hn'
        injection hn' with hnn
        subst hnn
        exact ⟨hlt_val, ⟨_, _, tbl, v163, cs174, htbl.mono ext_m, ev176,
          by rw [hc217]; simp, hsub_ga⟩,
          fun g' hr ro' hro' => (hval_ga g' hr ro' hro').mono hsub_ga⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
  | Assumed x_tbl w232 cs246 v250 m260 cs268 ld12 ev270 ev248 _ =>
    rw [hload] at ld12
    rcases hnode with ⟨_, _, _, rfl⟩ | ⟨hlim, rfl⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt
      subst hxt
      obtain ⟨rfl, hIdx⟩ := role_addr_index_step c₀ ev270 tbl rfl htbl
      have hlookup :=
        rbtree_map_lookup_or_default_field_step c₀ ev248
          x_a v250 (.field 0) rfl a_bytes ha_rep (IndexEntry c₀.t) hIdx
      rcases hlookup with hr0 | ⟨ro, hr_eq, had⟩
      · exact .inl hr0
      · exact .inr ⟨ro, hr_eq, had, fun n hn => by rw [hlim] at hn; cases hn⟩

/-- **`KernelRoles::role_of(rc, ap)` under `Claim.RCFullRep`**. -/
theorem role_of_full_admit_spec {t : Ix.Kernel.RoleTable} {bAddr addr : _root_.Address}
    {lim : Nat}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr lim h x_rc) (ha : S0.addr h x_a addr)
    (ev : ObsFn W "KernelRoles::role_of" [x_rc, x_a] h r h' calls) :
    Heap.Extends h h' ∧
    (r = .field 0 ∨
      ∃ ro : Ix.Kernel.Role,
        r = .field (roleNum ro + 1) ∧
        t.addressOf? ro = some addr ∧
        Ix.SpecDigest.groupOf ro < lim ∧
        GroupAdmitIn calls t (Ix.SpecDigest.groupOf ro) ∧
        (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' →
          ∀ ro' ∈ groupRoles g', RoleValidatedAt t calls g' ro') ∧
        ∃ recs : List (Claim.WalkedRec calls bAddr t),
          Claim.RecsClosed recs ∧
          (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' → ∀ ro' ∈ groupRoles g', ∀ a',
            roleWalksBound ro' = true → t.addressOf? ro' = some a' → a' ∈ recs.map (·.addr)) ∧
          (∀ g', GroupReachable (Ix.SpecDigest.groupOf ro) g' → ∀ ro' ∈ groupRoles g', ∀ arr thm,
            (ro', arr) ∈ t.evidence.toList → .proof thm ∈ arr.toList → thm ∈ recs.map (·.addr))) := by
  obtain ⟨ext, hres⟩ := role_of_admit_spec hrc.toRCRep ha ev
  refine ⟨ext, ?_⟩
  rcases hres with hr0 | ⟨ro, hr_eq, had, hmk⟩
  · exact .inl hr0
  · obtain ⟨hlt, hga, hval⟩ := hmk lim rfl
    obtain ⟨_, tbl, hload, htbl⟩ := hrc
    cases Obs.«KernelRoles::role_of».obs ev with
    | Mk_n0 _ _ _ _ _ _ _ _ _ _ _ he100 _ _ =>
      exfalso
      exact RolesAux.roleNum_add_one_ne_zero ro (Value.field.inj (hr_eq.symm.trans he100))
    | Mk_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he222 _ _ =>
      exfalso
      exact RolesAux.roleNum_add_one_ne_zero ro (Value.field.inj (hr_eq.symm.trans he222))
    | Assumed _ _ _ _ _ _ ld12 _ _ _ =>
      rw [hload] at ld12
      exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
    | Mk_other_n1 x_tbl _ _ v36 m37 _ _ m61 _ m108 _ _ m125 _ _
        _ m164 cs174 v178 m187 _ v198
        ld12 ev71 ev49 _ _ ev135 ev121 op212 ev197 ev176 he215 _ hc217 =>
      rw [hload] at ld12
      injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt _
      subst hxt
      have hv36 : v36 = .field (roleNum ro + 1) := he215.symm.trans hr_eq
      subst hv36
      obtain ⟨y2, hy2, rfl⟩ := RolesAux.evalBinOp_sub_field_left_inv op212
      injection hy2 with hy2_eq
      subst hy2_eq
      have hsub : roleNum ro + 1 - 1 = roleNum ro := add_sub_cancel_right _ _
      rw [hsub] at ev197
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev197
      have ext_m187 :=
        ev71.heap_extends.trans (ev49.heap_extends.trans
          (ev135.heap_extends.trans ev121.heap_extends))
      have hg_lt : Ix.SpecDigest.groupOf ro < 4294967296 :=
        Nat.lt_trans (groupOf_lt_77 ro) (by decide)
      obtain ⟨_, _, recs_ga, hcl_ga, ha_ga, hev_ga⟩ :=
        group_admit_full_nat_spec _ hg_lt (htbl.mono ext_m187) ev176
      have hsub_ga : ∀ cl ∈ cs174, cl ∈ calls := fun cl hm => by rw [hc217]; simp [hm]
      refine .inr ⟨ro, hr_eq, had, hlt, hga, hval,
        recs_ga.map (Claim.WalkedRec.mono hsub_ga), hcl_ga.mono hsub_ga, ?_, ?_⟩
      · intro g' hr ro' hro' a' hw had'
        rw [Claim.map_addr_walkedRec_mono]
        exact ha_ga g' hr ro' hro' a' hw had'
      · intro g' hr ro' hro' arr thm hm hthm
        rw [Claim.map_addr_walkedRec_mono]
        exact hev_ga g' hr ro' hro' arr thm hm hthm

end GroupAdmit

end IxVM.Refinement.RoleVal
