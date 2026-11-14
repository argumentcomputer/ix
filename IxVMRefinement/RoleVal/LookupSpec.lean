import IxVMRefinement.Roles.Steps

/-! # Standalone role-lookup specifications (`RolesSpec`)

Proves `roles_spec : RolesSpec`: for every `c : Ctx` with `c.t.wf = true`, every function
`f : Core.Specs.Roles.Fn` and observed derivation `ObsFn W f.name args h r h' calls` satisfies
`f.spec c args h r h' calls`, without requiring `CoreFacts c`.

Within `Roles/Steps.lean`, 23 of the 30 `Specs.Roles.Fn` constructors already hold unconditionally,
6 (`role_is_bound`, `role_bound_addr`, `role_index_of`, `role_of`, `role_addr`,
`role_used_implicitly`) read only callees within `Specs.Roles.Fn`, and `role_is` additionally reads
only `c.t.wf = true` (`keyOf_of_addressOf`). Restricting strong induction on `calls.length` to
`Specs.Roles.Fn` closes the family unconditionally from `c.t.wf = true`. -/

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core

/-- **Standalone role-lookup family specifications**: for every `c : Ctx` with `c.t.wf = true`,
every `f : Specs.Roles.Fn` satisfies `f.spec` on every observed derivation. -/
def RolesSpec : Prop :=
  ∀ (c : Ctx), c.t.wf = true →
    ∀ (f : Specs.Roles.Fn) (args : List (SourceValue F)) (h : Heap F)
      (r : SourceValue F) (h' : Heap F) (calls : List (Call F)),
      ObsFn W f.name args h r h' calls → f.spec c args h r h' calls

section Steps

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Induction hypothesis restricted to `Specs.Roles.Fn` on derivations with fewer calls. -/
private def RolesIH (c : Ctx) (calls : List (Call F)) : Prop :=
  ∀ (f : Specs.Roles.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
    (h' : Heap F) (cs : List (Call F)),
    cs.length < calls.length → ObsFn W f.name args h r h' cs → f.spec c args h r h' cs

private theorem RolesIH.get {c : Ctx} {calls : List (Call F)} (ih : RolesIH c calls)
    (f : Specs.Roles.Fn) {args : List (SourceValue F)} {h : Heap F} {r : SourceValue F}
    {h' : Heap F} {cs : List (Call F)} (hlt : cs.length < calls.length)
    (ev : ObsFn W f.name args h r h' cs) : f.spec c args h r h' cs :=
  ih f args h r h' cs hlt ev

local macro "roles_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

private theorem role_is_bound_roles_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_is_bound" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_is_bound c args h r h' calls := by
  intro tbl ro hargs good htbl hr_ne byRole hby
  subst hargs
  cases Obs.«KernelRoles::role_is_bound».obs ev with
  | other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he110 _ _ =>
    exact absurd he110 hr_ne
  | n0 v1 m2 cs12 x40 y41 m42 cs51 v55 m65 cs73 ev14 ev75 ev53 op97 op47 _ _ hc105 =>
    obtain ⟨res, hs, hres⟩ :=
      ih.get .role_bound_addr_or_zero (by rw [hc105]; roles_lt_calls) ev14
        tbl (roleNum ro) rfl byRole hby
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
      have htbl_m2 : TableRep c.t m2 tbl := htbl.mono ev14.heap_extends
      obtain ⟨rfl, hIdx⟩ :=
        ih.get .role_addr_index (by rw [hc105]; roles_lt_calls) ev75
          tbl rfl htbl_m2
      have hlookup :=
        ih.get .rbtree_map_lookup_or_default_field (by rw [hc105]; roles_lt_calls)
          ev53 v1 v55 (.field 0) rfl Specs.Roles.zeroAddr ha_zero (IndexEntry c.t) hIdx
      obtain rfl := RolesAux.evalBinOp_add_field_inv op97
      obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op47
      have hx40 : x40 = .field (roleNum ro + 1) := hx1.trans hx2.symm
      rcases hlookup with hx0 | ⟨ro', hxr, haddr⟩
      · exfalso
        have hz : roleNum ro + 1 = 0 := Value.field.inj (hx40.symm.trans hx0)
        exact RolesAux.roleNum_add_one_ne_zero ro hz
      · have hre : roleNum ro + 1 = roleNum ro' + 1 := Value.field.inj (hx40.symm.trans hxr)
        obtain rfl := RolesAux.roleNum_add_one_inj hre
        exact ⟨none, hs, haddr⟩

private theorem role_bound_addr_roles_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_bound_addr" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_bound_addr c args h r h' calls := by
  intro tbl ro hargs good htbl
  subst hargs
  obtain ⟨v12, m15, cs23, cs52, ev25, heq48, ev54, hc71⟩ :=
    Obs.«KernelRoles::role_bound_addr».obs ev
  have htbl' := htbl
  obtain ⟨bp, byRole, byAddr, evMap, hload, _, _, _⟩ := htbl'
  have hby : Specs.Roles.ByRole h tbl byRole := ⟨bp, byAddr, evMap, hload⟩
  have good1 : Good c cs23 := good.sub (by rw [hc71]; intro x hx; simp [hx])
  have hv12_ne : v12 ≠ .field 0 := by
    rw [heq48]
    exact fun e => one_ne_zero (Value.field.inj e)
  obtain ⟨res₁, hs₁, hbound⟩ :=
    ih.get .role_is_bound (by rw [hc71]; roles_lt_calls) ev25
      tbl ro rfl good1 htbl hv12_ne byRole hby
  have ext1 : Heap.Extends h m15 := ev25.heap_extends
  have hby_m15 : Specs.Roles.ByRole m15 tbl byRole :=
    ⟨bp, byAddr, evMap, ext1.loadValue_eq hload⟩
  obtain ⟨res₂, hs₂, hres₂⟩ :=
    ih.get .role_bound_addr_or_zero (by rw [hc71]; roles_lt_calls) ev54
      tbl (roleNum ro) rfl byRole hby_m15
  have hdet : res₁ = res₂ := RolesAux.roleMapSearch_det (RolesAux.roleMapSearch_mono ext1 hs₁) hs₂
  subst hdet
  cases res₁ with
  | some v =>
    rcases hres₂ with hsome | ⟨hnone, _⟩
    · injection hsome with hvr
      subst hvr
      obtain ⟨a, ha, haddr⟩ := hbound
      exact ⟨a, Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans ev54.heap_extends) ha, haddr⟩
    · cases hnone
  | none =>
    rcases hres₂ with hsome | ⟨_, ha_zero⟩
    · cases hsome
    · exact ⟨Specs.Roles.zeroAddr, ha_zero, hbound⟩

private theorem role_index_of_roles_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_index_of" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_index_of c args h r h' calls := by
  intro rc ap a hargs good hrc ha
  subst hargs
  obtain ⟨cs4, v8, m18, cs26, v29, m31, cs39, ev41, ev28, ev6, hc56⟩ :=
    Obs.«KernelRoles::role_index_of».obs ev
  obtain ⟨rfl, htbl⟩ :=
    ih.get .role_ctx_table (by rw [hc56]; roles_lt_calls) ev41 rc rfl hrc
  obtain ⟨rfl, hIdx⟩ :=
    ih.get .role_addr_index (by rw [hc56]; roles_lt_calls) ev28 v29 rfl htbl
  exact ih.get .rbtree_map_lookup_or_default_field
    (by rw [hc56]; roles_lt_calls) ev6 ap v8 (.field 0) rfl a ha (IndexEntry c.t) hIdx

private theorem role_of_roles_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_of" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_of c args h r h' calls := by
  intro rc ap a hargs good hrc ha
  subst hargs
  obtain ⟨tbl, ax, node, hload, hnode, htbl⟩ := hrc
  cases Obs.«KernelRoles::role_of».obs ev with
  | Mk_n0 _ _ _ _ _ _ _ _ _ _ _ he100 _ _ =>
    exact .inl he100
  | Mk_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he222 _ _ =>
    exact .inl he222
  | Mk_other_n1 x_tbl x_limit w20 v36 m37 cs47 v51 m61 cs69 m108 cs119 v122 m125 cs133 v136
      _ _ _ _ _ _ _ ld12 ev71 ev49 hne103 op150 ev135 ev121 _ _ _ he215 _ hc217 =>
    rw [hload] at ld12
    rcases hnode with ⟨n, hlim, hn_lt, rfl⟩ | ⟨_, rfl⟩
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt hxs1
      injection hxs1 with hxl
      subst hxt hxl
      obtain ⟨rfl, hIdx⟩ :=
        ih.get .role_addr_index (by rw [hc217]; roles_lt_calls) ev71 tbl rfl htbl
      have hlookup :=
        ih.get .rbtree_map_lookup_or_default_field
          (by rw [hc217]; roles_lt_calls) ev49 ap v51 (.field 0) rfl a ha (IndexEntry c.t) hIdx
      rcases hlookup with hv0 | ⟨ro, hv36, haddr⟩
      · exact absurd hv0 hne103
      · subst hv36
        obtain ⟨y, hy1, rfl⟩ := RolesAux.evalBinOp_sub_field_left_inv op150
        injection hy1 with hy
        subst hy
        have hsub : roleNum ro + 1 - 1 = roleNum ro := add_sub_cancel_right _ _
        rw [hsub] at ev135
        obtain ⟨rfl, -⟩ := RolesAux.role_group_spec ev135
        obtain ⟨_, _, hlt_iff, _, -⟩ := Lib.less_than_fields_field ev121
        have hlt_val : ZMod.val (Ix.SpecDigest.groupOf ro : F) < ZMod.val (n : F) := hlt_iff.mp rfl
        rw [RolesAux.val_groupOf, RolesAux.val_natCast (Nat.lt_trans hn_lt (by decide))] at hlt_val
        have hbinds : c.binds ro := by simp [Ctx.binds, haddr]
        have hinForce : c.inForce ro := ⟨hbinds, fun m hm => by
          rw [hlim] at hm
          injection hm with hnm
          omega⟩
        exact .inr ⟨ro, he215, haddr, hinForce⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
  | Assumed x_tbl w232 cs246 v250 m260 cs268 ld12 ev270 ev248 hc285 =>
    rw [hload] at ld12
    rcases hnode with ⟨n, _, _, rfl⟩ | ⟨hlim, rfl⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt
      subst hxt
      obtain ⟨rfl, hIdx⟩ :=
        ih.get .role_addr_index (by rw [hc285]; roles_lt_calls) ev270 tbl rfl htbl
      have hlookup :=
        ih.get .rbtree_map_lookup_or_default_field
          (by rw [hc285]; roles_lt_calls) ev248 ap v250 (.field 0) rfl a ha (IndexEntry c.t) hIdx
      rcases hlookup with hr0 | ⟨ro, hr, haddr⟩
      · exact .inl hr0
      · have hbinds : c.binds ro := by simp [Ctx.binds, haddr]
        have hinForce : c.inForce ro := ⟨hbinds, fun m hm => by rw [hlim] at hm; cases hm⟩
        exact .inr ⟨ro, hr, haddr, hinForce⟩

private theorem role_is_roles_step (c : Ctx) (hwf : c.t.wf = true) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_is" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_is c args h r h' calls := by
  intro rc ap a ro hargs good hrc ha hr_ne
  subst hargs
  cases Obs.«KernelRoles::role_is».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ he88 _ _ =>
    exact absurd he88 hr_ne
  | other _ _ _ _ _ _ _ _ _ he102 _ _ =>
    exact absurd he102 hr_ne
  | n0_other x10 y11 m12 cs21 v53 m54 cs65 ev23 op47 op17 ev67 hne91 _ _ hc97 =>
    have good1 : Good c cs21 := good.sub (by rw [hc97]; intro x hx; simp [hx])
    have hidx :=
      ih.get .role_index_of (by rw [hc97]; roles_lt_calls) ev23
        rc ap a rfl good1 hrc ha
    obtain rfl := RolesAux.evalBinOp_add_field_inv op47
    obtain ⟨x, hx1, hx2⟩ := RolesAux.evalBinOp_sub_eq_zero_inv op17
    have hx10 : x10 = .field (roleNum ro + 1) := hx1.trans hx2.symm
    have haddr : c.t.addressOf? ro = some (ixAddr a) := by
      rcases hidx with hx0 | ⟨ro₁, hxr, haddr₁⟩
      · exfalso
        exact RolesAux.roleNum_add_one_ne_zero ro (Value.field.inj (hx10.symm.trans hx0))
      · obtain rfl := RolesAux.roleNum_add_one_inj (Value.field.inj (hx10.symm.trans hxr))
        exact haddr₁
    have ext1 : Heap.Extends h m12 := ev23.heap_extends
    have good2 : Good c cs65 := good.sub (by rw [hc97]; intro x hx; simp [hx])
    have hof :=
      ih.get .role_of (by rw [hc97]; roles_lt_calls) ev67
        rc ap a rfl good2 (hrc.mono ext1) (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha)
    rcases hof with hv0 | ⟨ro₂, _, haddr₂, hinForce₂⟩
    · exact absurd hv0 hne91
    · have hkey₁ := keyOf_of_addressOf hwf haddr
      have hkey₂ := keyOf_of_addressOf hwf haddr₂
      have hre : (Ix.Kernel.Key.role ro : KKey) = .role ro₂ := hkey₁.symm.trans hkey₂
      injection hre with hro
      subst hro
      exact ⟨haddr, hinForce₂⟩

private theorem role_addr_roles_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_addr" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_addr c args h r h' calls := by
  intro rc ro hargs good hrc
  subst hargs
  obtain ⟨tbl, ax, node, hload, hnode, htbl⟩ := hrc
  cases Obs.«KernelRoles::role_addr».obs ev with
  | Mk x_tbl x_limit w20 v47 m50 cs58 v61 m64 cs72 v97 m98 cs108 v127 m128 cs138 v142 m151 cs159
      ld12 ev74 ev60 heq96 ev110 ev161 ev140 he171 he172 hc173 =>
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
      have good_ba : Good c cs108 := good.sub (by rw [hc173]; intro x hx; simp [hx])
      obtain ⟨a, ha_m98, haddr⟩ :=
        ih.get .role_bound_addr (by rw [hc173]; roles_lt_calls) ev110
          tbl ro rfl good_ba htbl
      have ext_tail : Heap.Extends m98 h' := by
        rw [he172]
        exact ev161.heap_extends.trans ev140.heap_extends
      subst he171
      have hbinds : c.binds ro := by simp [Ctx.binds, haddr]
      have hinForce : c.inForce ro := ⟨hbinds, fun m hm => by
        rw [hlim] at hm
        injection hm with hnm
        omega⟩
      exact ⟨a, Bytes.repAddressRef_heapMono₂ addrTy ext_tail ha_m98, haddr, hinForce⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
  | Assumed x_tbl w181 cs195 ld12 ev197 hc214 =>
    rw [hload] at ld12
    rcases hnode with ⟨n, _, _, rfl⟩ | ⟨hlim, rfl⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt
      subst hxt
      have good_ba : Good c cs195 := good.sub (by rw [hc214]; intro x hx; simp [hx])
      obtain ⟨a, ha_h', haddr⟩ :=
        ih.get .role_bound_addr (by rw [hc214]; roles_lt_calls) ev197
          tbl ro rfl good_ba htbl
      have hbinds : c.binds ro := by simp [Ctx.binds, haddr]
      have hinForce : c.inForce ro := ⟨hbinds, fun m hm => by rw [hlim] at hm; cases hm⟩
      exact ⟨a, ha_h', haddr, hinForce⟩

private theorem role_used_implicitly_roles_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_used_implicitly" args h r h' calls) (ih : RolesIH c calls) :
    Specs.Roles.role_used_implicitly c args h r h' calls := by
  intro rc ro hargs good hrc
  subst hargs
  obtain ⟨v1, m2, cs12, v31, m32, cs42, ev14, ev44, rfl, rfl, hc64⟩ :=
    Obs.«KernelRoles::role_used_implicitly».obs ev
  have good1 : Good c cs12 := good.sub (by rw [hc64]; intro x hx; simp [hx])
  obtain ⟨a, ha_m2, haddr, hinForce⟩ :=
    ih.get .role_addr (by rw [hc64]; roles_lt_calls) ev14 rc ro rfl good1 hrc
  exact ⟨a, Bytes.repAddressRef_heapMono₂ addrTy ev44.heap_extends ha_m2, haddr, hinForce⟩

private theorem roles_only_step (c : Ctx) (hwf : c.t.wf = true) :
    ∀ (f : Specs.Roles.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W f.name args h r h' cs → RolesIH c cs →
      f.spec c args h r h' cs
  | .role_map_lookup_or_default_addr, _, _, _, _, _, ev, _ =>
    role_map_lookup_or_default_addr_step c ev
  | .role_map_lookup_or_default_evidence, _, _, _, _, _, ev, _ =>
    role_map_lookup_or_default_evidence_step c ev
  | .rbtree_map_lookup_or_default_field, _, _, _, _, _, ev, _ =>
    rbtree_map_lookup_or_default_field_step c ev
  | .role_ctx_table, _, _, _, _, _, ev, _ => role_ctx_table_step c ev
  | .role_addr_index, _, _, _, _, _, ev, _ => role_addr_index_step c ev
  | .role_bound_addr_or_zero, _, _, _, _, _, ev, _ => role_bound_addr_or_zero_step c ev
  | .role_is_bound, _, _, _, _, _, ev, ih => role_is_bound_roles_step c ev ih
  | .role_bound_addr, _, _, _, _, _, ev, ih => role_bound_addr_roles_step c ev ih
  | .role_index_of, _, _, _, _, _, ev, ih => role_index_of_roles_step c ev ih
  | .role_of, _, _, _, _, _, ev, ih => role_of_roles_step c ev ih
  | .role_is, _, _, _, _, _, ev, ih => role_is_roles_step c hwf ev ih
  | .role_addr, _, _, _, _, _, ev, ih => role_addr_roles_step c ev ih
  | .role_used_implicitly, _, _, _, _, _, ev, ih => role_used_implicitly_roles_step c ev ih
  | .role_evidence, _, _, _, _, _, ev, _ => role_evidence_step c ev
  | .role_nat, _, _, _, _, _, ev, _ => role_nat_step c ev
  | .role_nat_zero, _, _, _, _, _, ev, _ => role_nat_zero_step c ev
  | .role_nat_succ, _, _, _, _, _, ev, _ => role_nat_succ_step c ev
  | .role_nat_add, _, _, _, _, _, ev, _ => role_nat_add_step c ev
  | .role_bool_true, _, _, _, _, _, ev, _ => role_bool_true_step c ev
  | .role_bool_false, _, _, _, _, _, ev, _ => role_bool_false_step c ev
  | .role_char, _, _, _, _, _, ev, _ => role_char_step c ev
  | .role_char_of_nat, _, _, _, _, _, ev, _ => role_char_of_nat_step c ev
  | .role_list_nil, _, _, _, _, _, ev, _ => role_list_nil_step c ev
  | .role_list_cons, _, _, _, _, _, ev, _ => role_list_cons_step c ev
  | .role_string, _, _, _, _, _, ev, _ => role_string_step c ev
  | .role_string_of_list, _, _, _, _, _, ev, _ => role_string_of_list_step c ev
  | .role_quot_mk, _, _, _, _, _, ev, _ => role_quot_mk_step c ev
  | .role_quot_lift, _, _, _, _, _, ev, _ => role_quot_lift_step c ev
  | .role_quot_ind, _, _, _, _, _, ev, _ => role_quot_ind_step c ev
  | .role_prim_family, _, _, _, _, _, ev, _ => role_prim_family_step c ev

end Steps

/-- **Every function in `Specs.Roles.Fn` meets its spec** whenever `c.t.wf = true`. -/
theorem roles_fn_spec (c : Ctx) (hwf : c.t.wf = true) :
    ∀ (f : Specs.Roles.Fn) (args : List (SourceValue F)) (h : Heap F)
      (r : SourceValue F) (h' : Heap F) (calls : List (Call F)),
      ObsFn W f.name args h r h' calls → f.spec c args h r h' calls := by
  have key := ObsFn.strong_induction (world := W)
    (fun n args h r h' cs => ∀ f : Specs.Roles.Fn, f.name = n → f.spec c args h r h' cs)
    (fun n args h r h' cs ev ihn f hf => by
      subst hf
      exact roles_only_step c hwf f args h r h' cs ev
        (fun f' args' h₁ r' h₂ cs' hlt ev' => ihn _ _ _ _ _ _ hlt ev' f' rfl))
  exact fun f args h r h' cs ev => key _ _ _ _ _ _ ev f rfl

/-- **`RolesSpec` holds unconditionally.** -/
theorem roles_spec : RolesSpec :=
  fun c hwf => roles_fn_spec c hwf

end IxVM.Refinement.RoleVal
