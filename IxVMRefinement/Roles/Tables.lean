import IxVMRefinement.Core.Registry

/-! # `KernelRoleSpec`: role numbers, validation groups, and native operation dispatch tables

Step lemmas for the constant role-number functions (`role_nat` … `role_quot_ind`) and the
role-indexed dispatch tables (`role_group` and `role_prim_family`) of `KernelRoleSpec`, together
with basic arithmetic facts on `roleNum` (`Role.idx` in `F`).

The two match tables (`role_group` and `role_prim_family`) are evaluated directly over their source
arm lists (`evalLitTable`, `evalLitPairTable`) via `selectArm_cons_inv`, avoiding unfolding 100+
match arms in proof contexts. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

set_option linter.unusedVariables false

namespace RolesAux

/-- The Goldilocks modulus, as a literal for `omega`. -/
scoped notation "PF" => (18446744069414584321 : Nat)

theorem val_natCast {n : Nat} (hn : n < PF) : ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt hn

theorem role_groupOf_lt (r : Ix.Kernel.Role) : Ix.SpecDigest.groupOf r < 108 := by
  cases r <;> decide

theorem val_roleNum (r : Ix.Kernel.Role) : ZMod.val (roleNum r) = r.idx :=
  val_natCast (Nat.lt_trans r.idx_lt (by decide))

theorem val_groupOf (r : Ix.Kernel.Role) :
    ZMod.val (Ix.SpecDigest.groupOf r : F) = Ix.SpecDigest.groupOf r :=
  val_natCast (Nat.lt_trans (role_groupOf_lt r) (by decide))

theorem roleNum_inj {r s : Ix.Kernel.Role} (h : roleNum r = roleNum s) : r = s := by
  have hv := congrArg ZMod.val h
  rw [val_roleNum, val_roleNum] at hv
  exact Ix.Kernel.Role.idx_inj hv

theorem roleNum_add_one_inj {r s : Ix.Kernel.Role} (h : roleNum r + 1 = roleNum s + 1) : r = s :=
  roleNum_inj (add_right_cancel h)

theorem roleNum_add_one_ne_zero (r : Ix.Kernel.Role) : roleNum r + 1 ≠ 0 := by
  have hlt := r.idx_lt
  have hcast : roleNum r + 1 = ((r.idx + 1 : Nat) : F) := by
    unfold roleNum
    push_cast
    rfl
  intro hz
  rw [hcast] at hz
  have hv := congrArg ZMod.val hz
  rw [val_natCast (by omega), ZMod.val_zero] at hv
  omega

/-- Extract the arms of a top-level `match` expression. -/
def matchArms : Generic.Expr F → List (Generic.Pattern F × Generic.Expr F)
  | .matchValue _ arms => arms
  | _ => []

/-- Pure evaluator for a literal/wildcard → literal match table. -/
def evalLitTable : List (Generic.Pattern F × Generic.Expr F) → F → Option F
  | [], _ => none
  | (.literal c, .literal g) :: rest, x => if x = c then some g else evalLitTable rest x
  | (.wildcard, .literal g) :: _, _ => some g
  | _ :: _, _ => none

/-- Pure evaluator for a literal/wildcard → literal-pair match table. -/
def evalLitPairTable : List (Generic.Pattern F × Generic.Expr F) → F → Option (F × F)
  | [], _ => none
  | (.literal c, .tuple [.literal a, .literal b]) :: rest, x =>
    if x = c then some (a, b) else evalLitPairTable rest x
  | (.wildcard, .tuple [.literal a, .literal b]) :: _, _ => some (a, b)
  | _ :: _, _ => none

theorem selectArm_litTable {arms : List (Generic.Pattern F × Generic.Expr F)} {x g : F}
    {heap : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (ht : evalLitTable arms x = some g)
    (hsel : selectArm W [] heap (.field x) arms = Except.ok (some (bs, body))) :
    bs = [] ∧ body = .literal g := by
  induction arms with
  | nil => simp [evalLitTable] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, expr⟩
    cases pat with
    | literal c =>
      cases expr with
      | literal g' =>
        simp only [evalLitTable] at ht
        rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, hsel'⟩
        · obtain ⟨hvx, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal c) mt
          have hxc : x = c := Value.field.inj hvx
          rw [if_pos hxc] at ht
          injection ht with hg
          exact ⟨rfl, congrArg Expr.literal hg.symm⟩
        · have hne : (Value.field x : SourceValue F) ≠ .field c :=
            MatchesConst.none_inv (MatchesConst.literal c) nm
          have hxc : x ≠ c := fun e => hne (congrArg Value.field e)
          rw [if_neg hxc] at ht
          exact ih ht hsel'
      | _ => simp [evalLitTable] at ht
    | wildcard =>
      cases expr with
      | literal g' =>
        simp only [evalLitTable, Option.some.injEq] at ht
        subst ht
        rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, _⟩
        · exact ⟨matchPattern_wildcard_inv mt, rfl⟩
        · exact (matchPattern_wildcard_none nm).elim
      | _ => simp [evalLitTable] at ht
    | _ => simp [evalLitTable] at ht

theorem selectArm_litPairTable {arms : List (Generic.Pattern F × Generic.Expr F)} {x a b : F}
    {heap : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (ht : evalLitPairTable arms x = some (a, b))
    (hsel : selectArm W [] heap (.field x) arms = Except.ok (some (bs, body))) :
    bs = [] ∧ body = .tuple [.literal a, .literal b] := by
  induction arms with
  | nil => simp [evalLitPairTable] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, expr⟩
    cases pat with
    | literal c =>
      cases expr with
      | tuple es =>
        cases es with
        | nil => simp [evalLitPairTable] at ht
        | cons e1 es1 =>
          cases e1 with
          | literal a' =>
            cases es1 with
            | nil => simp [evalLitPairTable] at ht
            | cons e2 es2 =>
              cases e2 with
              | literal b' =>
                cases es2 with
                | nil =>
                  simp only [evalLitPairTable] at ht
                  rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, hsel'⟩
                  · obtain ⟨hvx, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal c) mt
                    have hxc : x = c := Value.field.inj hvx
                    rw [if_pos hxc] at ht
                    injection ht with hp
                    injection hp with ha hb
                    subst ha hb
                    exact ⟨rfl, rfl⟩
                  · have hne : (Value.field x : SourceValue F) ≠ .field c :=
                      MatchesConst.none_inv (MatchesConst.literal c) nm
                    have hxc : x ≠ c := fun e => hne (congrArg Value.field e)
                    rw [if_neg hxc] at ht
                    exact ih ht hsel'
                | cons _ _ => simp [evalLitPairTable] at ht
              | _ => simp [evalLitPairTable] at ht
          | _ => simp [evalLitPairTable] at ht
      | _ => simp [evalLitPairTable] at ht
    | wildcard =>
      cases expr with
      | tuple es =>
        cases es with
        | nil => simp [evalLitPairTable] at ht
        | cons e1 es1 =>
          cases e1 with
          | literal a' =>
            cases es1 with
            | nil => simp [evalLitPairTable] at ht
            | cons e2 es2 =>
              cases e2 with
              | literal b' =>
                cases es2 with
                | nil =>
                  simp only [evalLitPairTable, Option.some.injEq, Prod.mk.injEq] at ht
                  obtain ⟨rfl, rfl⟩ := ht
                  rcases selectArm_cons_inv hsel with ⟨mt, rfl⟩ | ⟨nm, _⟩
                  · exact ⟨matchPattern_wildcard_inv mt, rfl⟩
                  · exact (matchPattern_wildcard_none nm).elim
                | cons _ _ => simp [evalLitPairTable] at ht
              | _ => simp [evalLitPairTable] at ht
          | _ => simp [evalLitPairTable] at ht
      | _ => simp [evalLitPairTable] at ht
    | _ => simp [evalLitPairTable] at ht

set_option maxRecDepth 100000 in
theorem role_group_table (ro : Ix.Kernel.Role) :
    evalLitTable (matchArms IxVM.KernelRoleSpec.role_group.body) (roleNum ro) =
      some (Ix.SpecDigest.groupOf ro : F) := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
theorem role_prim_family_table (ro : Ix.Kernel.Role) :
    evalLitPairTable (matchArms IxVM.KernelRoleSpec.role_prim_family.body) (roleNum ro) =
      some (((Ix.SpecDigest.nativeOp ro).1 : F), ((Ix.SpecDigest.nativeOp ro).2 : F)) := by
  cases ro <;> decide

/-- **`KernelRoleSpec::role_group(roleNum ro)`** evaluates to `(Ix.SpecDigest.groupOf ro : F)`
without allocating on the heap. -/
theorem role_group_spec {ro : Ix.Kernel.Role} {h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_group" [.field (roleNum ro)] h r h' calls) :
    r = .field (Ix.SpecDigest.groupOf ro : F) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_group.lookup
    (by simp [IxVM.KernelRoleSpec.role_group, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.role_group.params.map fun (n, t) => (n, (t.subst []).toCore)).map
      Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_group.body =
      .matchValue (.var "r") (matchArms IxVM.KernelRoleSpec.role_group.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨v1, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := selectArm_litTable (role_group_table ro) sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

end RolesAux

/-! ## Step lemmas for `KernelRoleSpec` -/

theorem role_nat_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_nat" args h r h' calls) :
    Specs.Roles.role_nat c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_nat.lookup
    (by simp [IxVM.KernelRoleSpec.role_nat, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_nat] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_nat_zero_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_nat_zero" args h r h' calls) :
    Specs.Roles.role_nat_zero c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_nat_zero.lookup
    (by simp [IxVM.KernelRoleSpec.role_nat_zero, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_nat_zero] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_nat_succ_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_nat_succ" args h r h' calls) :
    Specs.Roles.role_nat_succ c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_nat_succ.lookup
    (by simp [IxVM.KernelRoleSpec.role_nat_succ, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_nat_succ] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_nat_add_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_nat_add" args h r h' calls) :
    Specs.Roles.role_nat_add c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_nat_add.lookup
    (by simp [IxVM.KernelRoleSpec.role_nat_add, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_nat_add] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_bool_true_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_bool_true" args h r h' calls) :
    Specs.Roles.role_bool_true c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_bool_true.lookup
    (by simp [IxVM.KernelRoleSpec.role_bool_true, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_bool_true] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_bool_false_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_bool_false" args h r h' calls) :
    Specs.Roles.role_bool_false c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_bool_false.lookup
    (by simp [IxVM.KernelRoleSpec.role_bool_false, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_bool_false] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_char_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_char" args h r h' calls) :
    Specs.Roles.role_char c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_char.lookup
    (by simp [IxVM.KernelRoleSpec.role_char, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_char] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_char_of_nat_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_char_of_nat" args h r h' calls) :
    Specs.Roles.role_char_of_nat c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_char_of_nat.lookup
    (by simp [IxVM.KernelRoleSpec.role_char_of_nat, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_char_of_nat] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_list_nil_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_list_nil" args h r h' calls) :
    Specs.Roles.role_list_nil c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_list_nil.lookup
    (by simp [IxVM.KernelRoleSpec.role_list_nil, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_list_nil] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_list_cons_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_list_cons" args h r h' calls) :
    Specs.Roles.role_list_cons c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_list_cons.lookup
    (by simp [IxVM.KernelRoleSpec.role_list_cons, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_list_cons] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_string_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_string" args h r h' calls) :
    Specs.Roles.role_string c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_string.lookup
    (by simp [IxVM.KernelRoleSpec.role_string, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_string] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_string_of_list_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_string_of_list" args h r h' calls) :
    Specs.Roles.role_string_of_list c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_string_of_list.lookup
    (by simp [IxVM.KernelRoleSpec.role_string_of_list, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_string_of_list] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_quot_mk_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_quot_mk" args h r h' calls) :
    Specs.Roles.role_quot_mk c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_quot_mk.lookup
    (by simp [IxVM.KernelRoleSpec.role_quot_mk, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_quot_mk] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_quot_lift_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_quot_lift" args h r h' calls) :
    Specs.Roles.role_quot_lift c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_quot_lift.lookup
    (by simp [IxVM.KernelRoleSpec.role_quot_lift, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_quot_lift] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_quot_ind_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_quot_ind" args h r h' calls) :
    Specs.Roles.role_quot_ind c args h r h' calls := by
  intro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_quot_ind.lookup
    (by simp [IxVM.KernelRoleSpec.role_quot_ind, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_quot_ind] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

theorem role_prim_family_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoleSpec::role_prim_family" args h r h' calls) :
    Specs.Roles.role_prim_family c args h r h' calls := by
  intro ro hargs; subst hargs
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_prim_family.lookup
    (by simp [IxVM.KernelRoleSpec.role_prim_family, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.role_prim_family.params.map
      fun (n, t) => (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.role_prim_family.body =
      .matchValue (.var "r") (RolesAux.matchArms IxVM.KernelRoleSpec.role_prim_family.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨v1, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litPairTable (RolesAux.role_prim_family_table ro) sel8
  obtain ⟨vs, a0, rfl⟩ := d9.tuple_inv
  obtain ⟨v1, vs1, m1, _, _, rfl, d1, a1, -⟩ := a0.cons_inv
  obtain ⟨rfl, rfl, -⟩ := d1.literal_inv
  obtain ⟨v2, vs2, m2, _, _, rfl, d2, a2, -⟩ := a1.cons_inv
  obtain ⟨rfl, rfl, -⟩ := d2.literal_inv
  obtain ⟨rfl, rfl, -⟩ := a2.nil_inv
  exact ⟨rfl, rfl⟩

end IxVM.Refinement.Core
