import IxVMRefinement.Binding.TableAdmitsLoad

/-! # The evidence clauses of `RoleTable.check` from the roles' validations

`ValidationsCheckEvidence` (`Binding/TableAdmitsLoad.lean`) for every observed run:

* `admit_all_groups` validates every role (`ValidateRoleRaw`: the observed `validate_role` call
  on the table pointer, with no representation asked of the table: the table's well-formedness
  is what is being established);
* for a role with equations, `validate_role` is `validate_op` (kind 2) or `validate_eqns`
  (kind 5), which read the role's evidence (`role_evidence`, under `Core.TableRep`: the entry or
  nothing), assert its length is the role's equation count (positive, so the entry exists), and
  check each entry's kind (`validate_op_equations`: definitional exactly where
  `op_evidence_is_proof` answers 0; `validate_eqns_equations`: definitional only where
  `eqns_conditional` answers 0);
* the tables of `op_equation_count`, `op_evidence_is_proof`, `eqns_equation_count`,
  `eqns_conditional` agree with `Role.spec`'s `evidenceAllowed` (decided over the 108 roles).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Every role's validation, observed -/

/-- **An observed validation of a role on the table pointer**, from a heap on. -/
def ValidateRoleRaw (h₀ : Heap F) (x_tbl : SourceValue F) (ro : Ix.Kernel.Role) : Prop :=
  ∃ (rc r : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
    Heap.Extends h₀ h ∧
    ObsFn W "KernelRoles::validate_role" [rc, x_tbl, .field (roleNum ro)] h r h' cs

theorem ValidateRoleRaw.mono {h₀ h₁ : Heap F} (ext : Heap.Extends h₀ h₁) {x_tbl : SourceValue F}
    {ro : Ix.Kernel.Role} (hv : ValidateRoleRaw h₁ x_tbl ro) : ValidateRoleRaw h₀ x_tbl ro := by
  obtain ⟨rc, r, h, h', cs, e, ev⟩ := hv
  exact ⟨rc, r, h, h', cs, ext.trans e, ev⟩

theorem validate_group_roles_raw {R : Heap F → Ix.Kernel.Role → SourceValue F → Prop}
    (hR : ∀ h ro v, R h ro v → v = .field (roleNum ro)) (hRm : HeapMono₂ R) :
    ∀ {rs : List Ix.Kernel.Role} {x_rc x_tbl x_rs r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      RepList Obs.Names.«Lists::Node<Field>» R h rs x_rs →
      ObsFn W "KernelRoles::validate_group_roles" [x_rc, x_tbl, x_rs] h r h' calls →
      ∀ ro ∈ rs, ValidateRoleRaw h x_tbl ro
  | rs, x_rc, x_tbl, x_rs, r, h, h', calls, hlist, ev => by
    cases Obs.«KernelRoles::validate_group_roles».obs ev with
    | Nil ld12 _ _ _ =>
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      intro ro hm
      cases hm
    | Cons x_r x_rest v42 m43 cs53 cs83 ld12 ev55 ev85 _ =>
      obtain ⟨ro₀, rest, rfl, hro, hrest⟩ := Lib.rep_cons_of_load hlist ld12
      rw [hR _ _ _ hro] at ev55
      have ext1 := ev55.heap_extends
      intro ro hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ⟨x_rc, v42, h, m43, cs53, Heap.Extends.refl _, ev55⟩
      · exact (validate_group_roles_raw hR hRm (repList_heapMono₂ _ hRm ext1 hrest) ev85 ro
          hmem').mono ext1

theorem group_admit_raw {g : Nat} (hg : g < 4294967296) {x_tbl r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::group_admit" [x_tbl, .field (g : F)] h r h' calls) :
    ∀ ro ∈ RoleVal.groupRoles g, ValidateRoleRaw h x_tbl ro := by
  obtain ⟨v1, m2, cs12, v16, m25, cs33, m45, v60, m70, cs78, cs101, v106, m122, cs130,
    ev35, ev14, hm55, ev80, ev132, ev103, hc141⟩ :=
    Obs.«KernelRoles::group_admit».obs ev
  obtain ⟨rfl, rfl⟩ := RoleVal.group_validation_limit_of_nat hg ev80
  obtain ⟨ext_gn, -⟩ := RoleVal.group_needs_spec hg ev35
  have ext_gan := ev14.heap_extends
  have ext_m45 : Heap.Extends h m45 :=
    ext_gn.trans (ext_gan.trans (by rw [hm55]; exact Heap.Extends.snoc m70 _))
  obtain ⟨ext_gr, hroles_rep⟩ := RoleVal.group_roles_spec hg ev132
  intro ro hro
  exact (validate_group_roles_raw (fun _ _ _ hh => hh) (fun _ _ _ _ _ hh => hh) hroles_rep ev103
    ro hro).mono (ext_m45.trans ext_gr)

theorem admit_all_groups_raw :
    ∀ (n k : Nat), k + n = 77 →
      ∀ {x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
        ObsFn W "KernelRoles::admit_all_groups" [x_tbl, .field ((k : Nat) : F)] h r h' calls →
        ∀ g, k ≤ g → g < 77 → ∀ ro ∈ RoleVal.groupRoles g, ValidateRoleRaw h x_tbl ro := by
  intro n
  induction n with
  | zero =>
    intro k hk x_tbl r h h' calls ev g hkg hg
    omega
  | succ n ih =>
    intro k hk x_tbl r h h' calls ev g hkg hg ro hro
    cases Obs.«KernelRoles::admit_all_groups».obs ev with
    | n0 m2 y11 cs22 ev24 op17 he31 he32 hc33 =>
      obtain ⟨rfl, -, -⟩ := Obs.«KernelRoleSpec::group_count».obs ev24
      obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op17
      have e : ((k : Nat) : F) = ((77 : Nat) : F) := by
        rw [Nat.cast_ofNat]
        exact (Value.field.inj hx1).trans (Value.field.inj hx2).symm
      have := Claim.natCast_inj_of_lt_u32 (by omega) (by omega) e
      omega
    | other v1 m2 y11 cs22 v38 m39 cs49 cs71 v75 ev24 op17 hne34 ev51 op96 ev73 hc98 =>
      obtain ⟨rfl, hm2, -⟩ := Obs.«KernelRoleSpec::group_count».obs ev24
      subst hm2
      obtain rfl := Decl.evalBinOp_add_one k op96
      rcases Nat.eq_or_lt_of_le hkg with heq | hlt
      · subst heq
        exact group_admit_raw (g := k) (by omega) ev51 ro hro
      · exact (ih (k + 1) (by omega) ev73 g (Nat.succ_le_of_lt hlt) hg ro hro).mono
          ev51.heap_extends

/-! ## The tables of the equation counts and kinds -/

theorem op_evidence_is_proof_val {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {g : F}
    (ht : RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
      (roleNum ro) = some g)
    (ev : ObsFn W "KernelRoleSpec::op_evidence_is_proof" [.field (roleNum ro)] h r h' calls) :
    r = .field g ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.op_evidence_is_proof.lookup
    (by simp [IxVM.KernelRoleSpec.op_evidence_is_proof, ControlLower.hasControl]) ev
  have hp : (IxVM.KernelRoleSpec.op_evidence_is_proof.params.map fun (n, t) =>
      (n, (t.subst []).toCore)).map Prod.fst = ["r"] := rfl
  have hb : IxVM.KernelRoleSpec.op_evidence_is_proof.body =
      .matchValue (.var "r")
        (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body) := rfl
  rw [hp, hb] at d0
  obtain ⟨_, _, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
  obtain ⟨l10, rfl, -⟩ := d7.var_inv
  simp at l10
  subst l10
  obtain ⟨rfl, rfl⟩ := RolesAux.selectArm_litTable ht sel8
  obtain ⟨rfl, rfl, -⟩ := d9.literal_inv
  exact ⟨rfl, rfl⟩

/-- The keys `64 * r + k` at which `eqns_conditional` answers 1. -/
def condKeys : List Nat := [4162, 4736, 4737, 5249, 5250, 6400, 6401, 6402, 6403, 6404]

set_option maxRecDepth 100000 in
theorem kind_lt (ro : Ix.Kernel.Role) : RoleVal.roleSpecKindNat ro < 6 := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
theorem kind_of_equations {ro : Ix.Kernel.Role} (he : RoleVal.roleHasEquations ro = true) :
    RoleVal.roleSpecKindNat ro = 2 ∨ RoleVal.roleSpecKindNat ro = 5 := by
  cases ro <;> first | exact absurd he (by decide) | decide

set_option maxRecDepth 100000 in
/-- **An operation's evidence table** (decided): both tables answer, the count is positive, and
the kinds `evidenceAllowed` lists are the count's copies of the one kind `op_evidence_is_proof`
fixes. -/
theorem op_table (ro : Ix.Kernel.Role) :
    (RoleVal.roleSpecKindNat ro != 2 ||
      match RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_equation_count.body)
          (roleNum ro),
        RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
          (roleNum ro) with
      | some n, some p => decide (0 < n.val) &&
          (((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed ==
            List.replicate n.val (some (decide (p = 0))))
      | _, _ => false) = true := by
  cases ro <;> decide +kernel

set_option maxRecDepth 100000 in
/-- **A definition role's evidence table** (decided): the count answers and is positive and the
length of `evidenceAllowed`; at every equation whose key is not a conditional one the kind is
`none`; no kind is `some true`. -/
theorem eqns_table (ro : Ix.Kernel.Role) :
    (RoleVal.roleSpecKindNat ro != 5 ||
      match RolesAux.evalLitTable
          (RolesAux.matchArms IxVM.KernelRoleSpec.eqns_equation_count.body) (roleNum ro) with
      | some n => decide (0 < n.val) &&
          (((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed.length == n.val) &&
          (List.range n.val).all (fun k => condKeys.contains (64 * ro.idx + k) ||
            (((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed[k]? == some none)) &&
          ((Ix.Kernel.Role.spec (md := .anon)) ro).evidenceAllowed.all (· != some true)
      | none => false) = true := by
  cases ro <;> decide +kernel

theorem eqns_conditional_zero {ro : Ix.Kernel.Role} {k : Nat} (hk : k < 1000)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelRoleSpec::eqns_conditional" [.field (roleNum ro), .field (k : F)] h r h'
      cs)
    (hr : r = .field 0) : 64 * ro.idx + k ∉ condKeys := by
  have hv : ∀ x10 v1 : SourceValue F,
      evalBinOp .mul (.field 64) (.field (roleNum ro)) = .ok x10 →
      evalBinOp .add x10 (.field (k : F)) = .ok v1 →
      v1 = .field ((64 * ro.idx + k : Nat) : F) := by
    intro x10 v1 h1 h2
    simp only [evalBinOp, Except.ok.injEq] at h1
    subst h1
    simp only [evalBinOp, Except.ok.injEq] at h2
    subst h2
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have h10 : (Value.field (1 : F) : SourceValue F) ≠ .field 0 := by
    intro e
    exact one_ne_zero (Value.field.inj e)
  cases Obs.«KernelRoleSpec::eqns_conditional».obs ev with
  | n4162 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n4736 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n4737 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n5249 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n5250 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n6400 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n6401 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n6402 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n6403 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | n6404 _ _ _ he _ _ => exact absurd (he.symm.trans hr) h10
  | other v1 x10 op25 op17 h1 h2 h3 h4 h5 h6 h7 h8 h9 h0 _ _ _ =>
    have e := hv x10 v1 op25 op17
    subst e
    intro hmem
    simp only [condKeys, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with e | e | e | e | e | e | e | e | e | e <;>
      rw [e] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h0 <;> simp at h1 h2 h3 h4 h5 h6 h7 h8 h9 h0

/-! ## The loops over an evidence list -/

theorem validate_op_equations_kinds {ro : Ix.Kernel.Role} {p : F}
    (hp : RolesAux.evalLitTable
      (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body) (roleNum ro) = some p) :
    ∀ {es : List (Ix.Kernel.Evidence _root_.Address)}
      {x_rc x_tbl x_a x_val x_ev x_k r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_op_equations"
        [x_rc, x_tbl, .field (roleNum ro), x_a, x_val, x_ev, x_k] h r h' calls →
      ∀ e ∈ es, e.isDefeqKind (decide (p = 0)) = true
  | es, x_rc, x_tbl, x_a, x_val, x_ev, x_k, r, h, h', calls, hlist, ev => by
    cases Obs.«KernelRoles::validate_op_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      intro e he
      cases he
    | Cons x_e x_rest v1048 m1049 cs1051 cs1060 v1069 ld12 sg1056 _ ev1062 hc1127 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have tailMember : (⟨"KernelRoles::validate_op_equations",
          [x_rc, x_tbl, .field (roleNum ro), x_a, x_val, x_rest, v1069], m1049⟩ : Call F) ∈
          calls := by
        rw [hc1127]; simp
      have ext1 : Heap.Extends h m1049 := (ev.call_heap_bounds tailMember).1
      have hhead : e.isDefeqKind (decide (p = 0)) = true := by
        match sg1056 with
        | .n0_Defeq (ev56 := ev56) (hv83 := hv83) .. =>
          obtain ⟨hp0, -⟩ := op_evidence_is_proof_val hp ev56
          have hp0' : p = 0 := (Value.field.inj hp0).symm
          rcases he_rep with ⟨rfl, -⟩ | ⟨_, _, _, hv, _⟩
          · simp [Ix.Kernel.Evidence.isDefeqKind, hp0']
          · rw [hv83] at hv
            exact (RolesAux.construct_ctor_ne (by decide) hv).elim
        | .n0_Proof (heq379 := heq) .. => exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Defeq (heq431 := heq) .. => exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Proof_Defn_other (heq1257 := heq) .. =>
          exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Proof_other (heq1904 := heq) .. =>
          exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Proof_Defn_Theorem (ev56 := ev56) (hne386 := hne) (hv442 := hv442) .. =>
          obtain ⟨hpv, -⟩ := op_evidence_is_proof_val hp ev56
          have hp0' : p ≠ 0 := fun e0 => hne (by rw [hpv, e0])
          rcases he_rep with ⟨rfl, hv⟩ | ⟨a, _, rfl, _, _⟩
          · rw [hv442] at hv
            exact (RolesAux.construct_ctor_ne (by decide) hv).elim
          · simp [Ix.Kernel.Evidence.isDefeqKind, hp0']
      have htail := validate_op_equations_kinds hp
        (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev1062
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hhead
      · exact htail e' he'

theorem validate_eqns_equations_kinds {ro : Ix.Kernel.Role} :
    ∀ {es : List (Ix.Kernel.Evidence _root_.Address)} (k : Nat)
      {x_rc x_tbl x_ev r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      k + es.length < 1000 →
      RepList evListEnum EvRep h es x_ev →
      ObsFn W "KernelRoles::validate_eqns_equations"
        [x_rc, x_tbl, .field (roleNum ro), x_ev, .field (k : F)] h r h' calls →
      ∀ i (hi : i < es.length), es[i] = .defeq → 64 * ro.idx + (k + i) ∉ condKeys
  | es, k, x_rc, x_tbl, x_ev, r, h, h', calls, hk, hlist, ev => by
    cases Obs.«KernelRoles::validate_eqns_equations».obs ev with
    | Nil ld12 _ _ _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      intro i hi
      cases hi
    | Cons x_e x_rest v432 m433 cs435 cs444 v451 ld12 sg440 op493 ev446 hc =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have tailMember : (⟨"KernelRoles::validate_eqns_equations",
          [x_rc, x_tbl, .field (roleNum ro), x_rest, v451], m433⟩ : Call F) ∈ calls := by
        rw [hc]; simp
      have ext1 : Heap.Extends h m433 := (ev.call_heap_bounds tailMember).1
      have hk0 : k < 1000 := by simp at hk; omega
      have hhead : e = .defeq → 64 * ro.idx + k ∉ condKeys := by
        intro hed
        match sg440 with
        | .Defeq (ev82 := ev82) (heq105 := heq105) .. =>
          exact eqns_conditional_zero hk0 ev82 heq105
        | .Proof (hne239 := hne239) .. =>
          subst hed
          rcases he_rep with ⟨-, hv⟩ | ⟨_, _, hpr, _, _⟩
          · exact (hne239 [] rfl hv).elim
          · cases hpr
      obtain rfl := Decl.evalBinOp_add_one k op493
      have htail := validate_eqns_equations_kinds (k + 1) (by simp at hk ⊢; omega)
        (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev446
      intro i hi hdef
      cases i with
      | zero => simpa using hhead hdef
      | succ i =>
        have := htail i (by simp at hi; omega) hdef
        rwa [show k + (i + 1) = k + 1 + i by omega]

end IxVM.Refinement.Binding
