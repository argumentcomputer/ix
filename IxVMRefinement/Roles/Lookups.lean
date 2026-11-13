import IxVMRefinement.Roles.Tables
import IxVMRefinement.Core.Roles
import IxVMRefinement.Core.Open
import IxVMRefinement.Lib.Words
import IxVMRefinement.Obs.KernelRoles0
import IxVMRefinement.Obs.KernelRoles1
import IxVMRefinement.Obs.KernelRoles2
import IxVMRefinement.Obs.RBTreeMap0
import Mathlib.Tactic.IntervalCases

/-! # `KernelRoles` and `RBTreeMap`: role-map and address-map lookups, table and context queries

Step lemmas for the fourteen lookup functions of `Specs.Roles.Fn`:
* `role_map_lookup_or_default` (at `&[Field; 32]` and `&Lists::Node<KernelRoles::RoleEvidence>`):
  functional search in a field-keyed red-black tree (`RoleMapSearch`);
* `rbtree_map_lookup_or_default<Field>`: address-keyed red-black tree lookup (`canon_addr_cmp`
  answers `1` only on equal 32-byte addresses);
* `role_ctx_table`, `role_addr_index`, `role_bound_addr_or_zero`, `role_is_bound`,
  `role_bound_addr`, `role_index_of`, `role_of`, `role_is`, `role_addr`,
  `role_used_implicitly`, `role_evidence`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A callee's derivation has fewer calls than its caller's. -/
local macro "roles_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

namespace RolesAux

theorem construct_ctor_ne {en₁ en₂ c₁ c₂ : String} {vs₁ vs₂ : List (SourceValue F)}
    (hne : c₁ ≠ c₂)
    (h : (Value.construct en₁ c₁ vs₁ : SourceValue F) = .construct en₂ c₂ vs₂) : False := by
  injection h with _ hc _
  exact hne hc

theorem ok_construct_ctor_ne {en₁ en₂ c₁ c₂ : String} {vs₁ vs₂ : List (SourceValue F)}
    (hne : c₁ ≠ c₂)
    (h : (Except.ok (Value.construct en₁ c₁ vs₁) : Except EvalError (SourceValue F)) =
      .ok (.construct en₂ c₂ vs₂)) : False := by
  injection h with hv
  exact construct_ctor_ne hne hv

/-! ## Arithmetic and binary-operation inversions -/

theorem evalBinOp_add_field_inv {x y : F} {vr : SourceValue F}
    (h : evalBinOp .add (.field x) (.field y) = .ok vr) :
    vr = .field (x + y) := by
  simp only [evalBinOp, Except.ok.injEq] at h
  exact h.symm

theorem evalBinOp_mul_field_inv {x y : F} {vr : SourceValue F}
    (h : evalBinOp .mul (.field x) (.field y) = .ok vr) :
    vr = .field (x * y) := by
  simp only [evalBinOp, Except.ok.injEq] at h
  exact h.symm

theorem evalBinOp_sub_field_left_inv {x : F} {vy vr : SourceValue F}
    (h : evalBinOp .sub (.field x) vy = .ok vr) :
    ∃ y : F, vy = .field y ∧ vr = .field (x - y) := by
  cases vy with
  | field y =>
    simp only [evalBinOp, Except.ok.injEq] at h
    exact ⟨y, rfl, h.symm⟩
  | _ => simp [evalBinOp] at h

theorem evalBinOp_sub_eq_zero_inv {vx vy : SourceValue F}
    (h : evalBinOp .sub vx vy = .ok (.field 0)) :
    ∃ x : F, vx = .field x ∧ vy = .field x := by
  cases vx with
  | field x =>
    cases vy with
    | field y =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at h
      exact ⟨x, rfl, congrArg Value.field (sub_eq_zero.mp h).symm⟩
    | _ => simp [evalBinOp] at h
  | _ => simp [evalBinOp] at h

/-! ## `RoleMapSearch` properties -/

theorem roleMapSearch_det {en : String} {h : Heap F} {k : F} {tree : SourceValue F}
    {r₁ r₂ : Option (SourceValue F)}
    (h₁ : Specs.Roles.RoleMapSearch en h k tree r₁)
    (h₂ : Specs.Roles.RoleMapSearch en h k tree r₂) : r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | nil =>
    generalize ht : (Value.construct en "Nil" [] : SourceValue F) = t at h₂
    cases h₂ with
    | nil => rfl
    | here => exact (construct_ctor_ne (by decide) ht.symm).elim
    | left => exact (construct_ctor_ne (by decide) ht.symm).elim
    | right => exact (construct_ctor_ne (by decide) ht.symm).elim
  | @here c v lp rp =>
    generalize ht : (Value.construct en "Node" [c, .field k, v, lp, rp] : SourceValue F) = t at h₂
    cases h₂ with
    | nil => exact (construct_ctor_ne (by decide) ht.symm).elim
    | here =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with _ hvs2
      injection hvs2 with hv _
      exact hv
    | left hlt =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk _
      injection hk with hkeq
      subst hkeq
      exact absurd hlt (Nat.lt_irrefl _)
    | right hgt =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk _
      injection hk with hkeq
      subst hkeq
      exact absurd hgt (Nat.lt_irrefl _)
  | @left c v lp rp lv key res hlt hl _ ih =>
    generalize ht : (Value.construct en "Node" [c, .field key, v, lp, rp] : SourceValue F) = t at h₂
    cases h₂ with
    | nil => exact (construct_ctor_ne (by decide) ht.symm).elim
    | here =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk _
      injection hk with hkeq
      subst hkeq
      exact absurd hlt (Nat.lt_irrefl _)
    | left _ hl' hs' =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with _ hvs2
      injection hvs2 with _ hvs3
      injection hvs3 with hlp _
      subst hlp
      rw [hl] at hl'
      injection hl' with hlv
      subst hlv
      exact ih hs'
    | right hgt =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk _
      injection hk with hkeq
      subst hkeq
      omega
  | @right c v lp rp rv key res hgt hr _ ih =>
    generalize ht : (Value.construct en "Node" [c, .field key, v, lp, rp] : SourceValue F) = t at h₂
    cases h₂ with
    | nil => exact (construct_ctor_ne (by decide) ht.symm).elim
    | here =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk _
      injection hk with hkeq
      subst hkeq
      exact absurd hgt (Nat.lt_irrefl _)
    | left hlt =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk _
      injection hk with hkeq
      subst hkeq
      omega
    | right _ hr' hs' =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with _ hvs2
      injection hvs2 with _ hvs3
      injection hvs3 with _ hvs4
      injection hvs4 with hrp _
      subst hrp
      rw [hr] at hr'
      injection hr' with hrv
      subst hrv
      exact ih hs'

theorem roleMapSearch_mono {en : String} {h₁ h₂ : Heap F} {k : F} {tree : SourceValue F}
    {res : Option (SourceValue F)} (ext : Heap.Extends h₁ h₂)
    (hs : Specs.Roles.RoleMapSearch en h₁ k tree res) :
    Specs.Roles.RoleMapSearch en h₂ k tree res := by
  induction hs with
  | nil => exact .nil
  | here => exact .here
  | left hlt hl _ ih => exact .left hlt (ext.loadValue_eq hl) ih
  | right hgt hr _ ih => exact .right hgt (ext.loadValue_eq hr) ih

theorem loadValue_unextend_of_ne_construct {en : String} {h : Heap F} {cell lp lv : SourceValue F}
    {k : F} {res : Option (SourceValue F)}
    (hcell : ∀ ctor vs, cell ≠ .construct en ctor vs)
    (hl : loadValue (h ++ [cell]) lp = .ok lv)
    (hs : Specs.Roles.RoleMapSearch en (h ++ [cell]) k lv res) :
    loadValue h lp = .ok lv := by
  cases lp with
  | field | tuple | construct => simp [loadValue] at hl
  | ptr target addr =>
    rcases Nat.lt_trichotomy addr h.length with hlt | rfl | hgt
    · have hget : (h ++ [cell])[addr]? = h[addr]? := List.getElem?_append_left hlt
      simpa [loadValue, hget] using hl
    · have hget : (h ++ [cell])[h.length]? = some cell := by simp
      simp only [loadValue, hget, bind, Except.bind, pure, Except.pure] at hl
      split at hl
      · simp at hl
      · injection hl with hce
        subst hce
        cases hs with
        | nil => exact (hcell _ _ rfl).elim
        | here => exact (hcell _ _ rfl).elim
        | left => exact (hcell _ _ rfl).elim
        | right => exact (hcell _ _ rfl).elim
    · have hget : (h ++ [cell])[addr]? = none := List.getElem?_eq_none (by simp; omega)
      simp [loadValue, hget, bind, Except.bind] at hl

theorem roleMapSearch_unextend_snoc {en : String} {h : Heap F} {cell tree : SourceValue F}
    {k : F} {res : Option (SourceValue F)}
    (hcell : ∀ ctor vs, cell ≠ .construct en ctor vs)
    (hs : Specs.Roles.RoleMapSearch en (h ++ [cell]) k tree res) :
    Specs.Roles.RoleMapSearch en h k tree res := by
  induction hs with
  | nil => exact .nil
  | here => exact .here
  | left hlt hl hs' ih =>
    exact .left hlt (loadValue_unextend_of_ne_construct hcell hl hs') ih
  | right hgt hr hs' ih =>
    exact .right hgt (loadValue_unextend_of_ne_construct hcell hr hs') ih

theorem roleMapSearch_mem_all {en : String} {P : Heap F → F → SourceValue F → Prop}
    {h : Heap F} {k : F} {tree v : SourceValue F}
    (hall : RoleMapAll en P h tree)
    (hs : Specs.Roles.RoleMapSearch en h k tree (some v)) : P h k v := by
  induction hall with
  | nil =>
    generalize ht : (Value.construct en "Nil" [] : SourceValue F) = t at hs
    cases hs with
    | here => exact (construct_ctor_ne (by decide) ht.symm).elim
    | left => exact (construct_ctor_ne (by decide) ht.symm).elim
    | right => exact (construct_ctor_ne (by decide) ht.symm).elim
  | @node c key nv lp rp lv rv hP hl hr _ _ ihl ihr =>
    generalize ht : (Value.construct en "Node" [.field c, .field key, nv, lp, rp] : SourceValue F) = t at hs
    cases hs with
    | here =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with hk hvs2
      injection hk with hkeq
      injection hvs2 with hv _
      subst hkeq hv
      exact hP
    | left _ hl' hs' =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with _ hvs2
      injection hvs2 with _ hvs3
      injection hvs3 with hlp _
      subst hlp
      rw [hl] at hl'
      injection hl' with hlv
      subst hlv
      exact ihl hs'
    | right _ hr' hs' =>
      injection ht with _ _ hvs
      injection hvs with _ hvs1
      injection hvs1 with _ hvs2
      injection hvs2 with _ hvs3
      injection hvs3 with _ hvs4
      injection hvs4 with hrp _
      subst hrp
      rw [hr] at hr'
      injection hr' with hrv
      subst hrv
      exact ihr hs'

/-! ## Generic `role_map_lookup_or_default` -/

theorem role_map_lookup_generic (t_V : Generic.Ty) :
    ∀ {k : F} {tree dflt r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      ObsFn W (Instance.mk "KernelRoles::role_map_lookup_or_default" [t_V]).symbol
        [.field k, tree, dflt] h r h' calls →
      h' = h ∧
        ∃ res, Specs.Roles.RoleMapSearch (Instance.mk "KernelRoles::RoleMap" [t_V]).symbol h k tree res ∧
          r = res.getD dflt := by
  have go : ∀ (N : Nat) {k : F} {tree dflt r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ N →
      ObsFn W (Instance.mk "KernelRoles::role_map_lookup_or_default" [t_V]).symbol
        [.field k, tree, dflt] h r h' calls →
      h' = h ∧
        ∃ res, Specs.Roles.RoleMapSearch (Instance.mk "KernelRoles::RoleMap" [t_V]).symbol h k tree res ∧
          r = res.getD dflt := by
    intro N
    induction N with
    | zero =>
      intro k tree dflt r h h' calls hle ev
      cases Obs.«KernelRoles::role_map_lookup_or_default».obs ev with
      | Nil hv15 he18 he19 _ =>
        subst hv15 he18 he19
        exact ⟨rfl, none, .nil, rfl⟩
      | Node_n0 w28 x_k x_v x_left x_right _ hv26 op69 he87 he88 _ =>
        obtain ⟨k', rfl, heq⟩ := evalBinOp_sub_field_left_inv op69
        have hk : k' = k := (sub_eq_zero.mp (Value.field.inj heq).symm).symm
        rw [hv26, hk, he87, he88]
        exact ⟨rfl, some x_v, .here, rfl⟩
      | Node_other_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc162 =>
        rw [hc162] at hle; simp at hle
      | Node_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc200 =>
        rw [hc200] at hle; simp at hle
    | succ N ih =>
      intro k tree dflt r h h' calls hle ev
      cases Obs.«KernelRoles::role_map_lookup_or_default».obs ev with
      | Nil hv15 he18 he19 _ =>
        subst hv15 he18 he19
        exact ⟨rfl, none, .nil, rfl⟩
      | Node_n0 w28 x_k x_v x_left x_right _ hv26 op69 he87 he88 _ =>
        obtain ⟨k', rfl, heq⟩ := evalBinOp_sub_field_left_inv op69
        have hk : k' = k := (sub_eq_zero.mp (Value.field.inj heq).symm).symm
        rw [hv26, hk, he87, he88]
        exact ⟨rfl, some x_v, .here, rfl⟩
      | Node_other_n1 w28 x_k x_v x_left x_right v54 m95 cs106 cs132 v136 _ hv26 op69 hne90 ev108 ld153 ev134 hc162 =>
        obtain ⟨k', rfl, rfl⟩ := evalBinOp_sub_field_left_inv op69
        obtain ⟨_, _, hlt_iff, _, rfl⟩ := Lib.less_than_fields_field ev108
        have hlt : ZMod.val k < ZMod.val k' := hlt_iff.mp rfl
        have hcs : cs132.length ≤ N := by rw [hc162] at hle; simp at hle; omega
        obtain ⟨rfl, res, hs, hr⟩ := ih hcs ev134
        subst hv26
        exact ⟨rfl, res, .left hlt ld153 hs, hr⟩
      | Node_other_other w28 x_k x_v x_left x_right v54 v94 m95 cs106 cs170 v174 _ hv26 op69 hne90 ev108 hne163 ld191 ev172 hc200 =>
        obtain ⟨k', rfl, rfl⟩ := evalBinOp_sub_field_left_inv op69
        have hkne : k ≠ k' := fun e => hne90 (by rw [e, sub_self])
        have hvne : ZMod.val k ≠ ZMod.val k' := fun e => hkne (ZMod.val_injective PF e)
        obtain ⟨_, _, hlt_iff, _, rfl⟩ := Lib.less_than_fields_field ev108
        have hnlt : ¬ ZMod.val k < ZMod.val k' := fun h1 => hne163 (hlt_iff.mpr h1)
        have hgt : ZMod.val k' < ZMod.val k := by omega
        have hcs : cs170.length ≤ N := by rw [hc200] at hle; simp at hle; omega
        obtain ⟨rfl, res, hs, hr⟩ := ih hcs ev172
        subst hv26
        exact ⟨rfl, res, .right hgt ld191 hs, hr⟩
  intro k tree dflt r h h' calls ev
  exact go calls.length (Nat.le_refl _) ev

/-! ## Zero-address allocation -/

theorem repAddr_zeroAddr_snoc (h : Heap F) :
    RepAddr (h ++ [.tuple (List.replicate 32 (.field 0))]) Specs.Roles.zeroAddr
      (.ptr (.tuple (List.map Value.type (List.replicate 32 ((.field 0) : SourceValue F)))) h.length) := by
  have hty : (List.map Value.type (List.replicate 32 ((.field 0) : SourceValue F))) =
      List.replicate 32 .field := by simp [Value.type]
  rw [hty]
  refine ⟨h.length, .tuple (List.replicate 32 (.field 0)), rfl, by simp, ?_⟩
  unfold Bytes.RepAddress Specs.Roles.zeroAddr
  apply congrArg Value.tuple
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 32 := by simpa using h1
  simp [List.getElem_replicate, Vector.getElem_toList, hi]

/-! ## `RBTreeMap::canon_addr_cmp` and `rbtree_map_lookup_or_default` -/

theorem canon_ord_cmp_g_spec {x_a x_b r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "RBTreeMap::canon_ord_cmp_g" [x_a, x_b] h r h' calls) :
    h' = h ∧ (r = .field 1 → x_a = x_b) := by
  cases Obs.«RBTreeMap::canon_ord_cmp_g».obs ev with
  | n0 op17 _ he25 _ =>
    obtain ⟨x, rfl, rfl⟩ := evalBinOp_sub_eq_zero_inv op17
    exact ⟨he25, fun _ => rfl⟩
  | other_n1 _ m32 _ _ _ ev45 he66 he67 _ =>
    obtain ⟨_, _, _, _, _, _, _, hm⟩ := Lib.less_than_fields_spec ev45
    refine ⟨he67.trans hm, fun hr => ?_⟩
    exact absurd (Value.field.inj (he66.symm.trans hr)) zero_ne_one
  | other_n0 _ m32 _ _ _ ev45 he74 he75 _ =>
    obtain ⟨_, _, _, _, _, _, _, hm⟩ := Lib.less_than_fields_spec ev45
    refine ⟨he75.trans hm, fun hr => ?_⟩
    have h21 : (2 : F) = 1 := Value.field.inj (he74.symm.trans hr)
    exact absurd h21 (by decide)

theorem canon_ord_then_spec {x_a x_b r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "RBTreeMap::canon_ord_then" [x_a, x_b] h r h' calls) :
    h' = h ∧ (r = .field 1 → x_a = .field 1 ∧ x_b = .field 1) := by
  cases Obs.«RBTreeMap::canon_ord_then».obs ev with
  | n1 hv14 he16 he17 _ =>
    exact ⟨he17, fun hr => ⟨hv14, he16.symm.trans hr⟩⟩
  | other hne19 he24 he25 _ =>
    exact ⟨he25, fun hr => absurd (he24.symm.trans hr) hne19⟩

theorem u8_eq_of_toNat {b c : UInt8} (h : b.toNat = c.toNat) : b = c :=
  congrArg UInt8.ofBitVec (BitVec.eq_of_toNat_eq h)

theorem canon_addr_chunk_spec {b0 b1 b2 b3 c0 c1 c2 c3 : UInt8}
    {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "RBTreeMap::canon_addr_chunk"
      [.field (b0.toNat : F), .field (b1.toNat : F), .field (b2.toNat : F), .field (b3.toNat : F),
       .field (c0.toNat : F), .field (c1.toNat : F), .field (c2.toNat : F), .field (c3.toNat : F)]
      h r h' calls) :
    h' = h ∧ (r = .field 1 → b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3) := by
  obtain ⟨v1, x9, x17, y18, x25, y26, v61, x69, x77, y78, x85, y86, cs124,
    op40, op49, op32, op58, op24, op16, op100, op109, op92, op118, op84, op76, ev126, -⟩ :=
    Obs.«RBTreeMap::canon_addr_chunk».obs ev
  obtain rfl := evalBinOp_mul_field_inv op40
  obtain rfl := evalBinOp_mul_field_inv op49
  obtain rfl := evalBinOp_add_field_inv op32
  obtain rfl := evalBinOp_mul_field_inv op58
  obtain rfl := evalBinOp_add_field_inv op24
  obtain rfl := evalBinOp_add_field_inv op16
  obtain rfl := evalBinOp_mul_field_inv op100
  obtain rfl := evalBinOp_mul_field_inv op109
  obtain rfl := evalBinOp_add_field_inv op92
  obtain rfl := evalBinOp_mul_field_inv op118
  obtain rfl := evalBinOp_add_field_inv op84
  obtain rfl := evalBinOp_add_field_inv op76
  obtain ⟨hh, hcmp⟩ := canon_ord_cmp_g_spec ev126
  refine ⟨hh, fun hr => ?_⟩
  have hf := Value.field.inj (hcmp hr)
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  have hc0 := c0.toNat_lt; have hc1 := c1.toNat_lt; have hc2 := c2.toNat_lt; have hc3 := c3.toNat_lt
  have hcastL :
      (b0.toNat : F) * 16777216 + (b1.toNat : F) * 65536 + (b2.toNat : F) * 256 + (b3.toNat : F) =
      ((b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat : Nat) : F) := by
    push_cast; ring
  have hcastR :
      (c0.toNat : F) * 16777216 + (c1.toNat : F) * 65536 + (c2.toNat : F) * 256 + (c3.toNat : F) =
      ((c0.toNat * 16777216 + c1.toNat * 65536 + c2.toNat * 256 + c3.toNat : Nat) : F) := by
    push_cast; ring
  rw [hcastL, hcastR] at hf
  have hnat := congrArg ZMod.val hf
  rw [val_natCast (by omega), val_natCast (by omega)] at hnat
  exact ⟨u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega),
    u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega)⟩

theorem loadValue_of_repAddr {h : Heap F} {a : Bytes.Address} {p : SourceValue F}
    (ha : RepAddr h a p) :
    loadValue h p = .ok (.tuple (a.toList.map fun b => .field (b.toNat : F))) := by
  obtain ⟨addr, v, rfl, hcell, rfl⟩ := ha
  have hty : (Value.tuple (a.toList.map fun b => (Value.field (b.toNat : F) : SourceValue F))).type =
      addrTy := by
    simp [Value.type, addrTy, Function.comp_def]
  simp [loadValue, hcell, hty, bind, Except.bind, pure, Except.pure]

theorem proj_addrTuple (a : Bytes.Address) (i : Nat) (hi : i < 32) :
    projectValue (.tuple (a.toList.map fun b => (Value.field (b.toNat : F) : SourceValue F))) i =
      .ok (.field (a[i].toNat : F)) := by
  have hl : i < a.toList.length := by simpa using hi
  simp [projectValue, List.getElem?_eq_getElem hl, bind, Except.bind, pure, Except.pure]

theorem proj_addrTuple_eq {a : Bytes.Address} {v : SourceValue F} (i : Nat) (hi : i < 32)
    (hp : projectValue (.tuple (a.toList.map fun b => (Value.field (b.toNat : F) : SourceValue F))) i =
      .ok v) :
    v = .field (a[i].toNat : F) := by
  rw [proj_addrTuple a i hi] at hp
  exact (Except.ok.inj hp).symm

set_option maxHeartbeats 1600000 in
/-- **`RBTreeMap::canon_addr_cmp(x, y)`** on two represented addresses leaves the heap unchanged,
and answers `1` only when the addresses are equal. -/
theorem canon_addr_cmp_spec {a₁ a₂ : Bytes.Address} {px py r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ha₁ : RepAddr h a₁ px) (ha₂ : RepAddr h a₂ py)
    (ev : ObsFn W "RBTreeMap::canon_addr_cmp" [px, py] h r h' calls) :
    h' = h ∧ (r = .field 1 → a₁ = a₂) := by
  rcases Obs.«RBTreeMap::canon_addr_cmp».obs ev with
    ⟨v1, v13, cs28, v31, v32, m34, cs42, v45, v46, v47, v48, v49, v50, v51, v52,
     m54, cs62, v65, m77, cs85, v88, m100, cs108, v111, m123, cs131, v134, m146, cs154, v157,
     m169, cs177, v180, m192, cs200, v203, m215, cs223, v226, m238, cs246, v249, v250, m252,
     cs260, v263, v264, v265, v266, v267, v268, v269, v270, m272, cs280, v283, m295, cs303,
     v306, m318, cs326, v329, m341, cs349, v352, m364, cs372, v375, m387, cs395, v398, m410,
     cs418, v421, m433, cs441, v444, m456, cs464, v467, v468, m470, cs478, v481, v482, v483,
     v484, v485, v486, v487, v488, m490, cs498, v501, m513, cs521, v524, m536, cs544, v547,
     m559, cs567, v570, m582, cs590, v593, m605, cs613, v616, m628, cs636, v639, m651, cs659,
     v662, m674, cs682, v685, v686, m688, cs696, v699, v700, v701, v702, v703, v704, v705,
     v706, m708, cs716, v719, m731, cs739, v742, m754, cs762, v765, m777, cs785, v788, m800,
     cs808, v811, m823, cs831, v834, m846, cs854, v857, m869, cs877, v880, m892, cs900, v903,
     v904, m906, cs914, v917, v918, v919, v920, v921, v922, v923, v924, m926, cs934, v937,
     m949, cs957, v960, m972, cs980, v983, m995, cs1003, v1006, m1018, cs1026, v1029, m1041,
     cs1049, v1052, m1064, cs1072, v1075, m1087, cs1095, v1098, m1110, cs1118, v1121, v1122,
     m1124, cs1132, v1135, v1136, v1137, v1138, v1139, v1140, v1141, v1142, m1144, cs1152,
     v1155, m1167, cs1175, v1178, m1190, cs1198, v1201, m1213, cs1221, v1224, m1236, cs1244,
     v1247, m1259, cs1267, v1270, m1282, cs1290, v1293, m1305, cs1313, v1316, m1328, cs1336,
     v1339, v1340, m1342, cs1350, v1353, v1354, v1355, v1356, v1357, v1358, v1359, v1360,
     m1362, cs1370, v1373, m1385, cs1393, v1396, m1408, cs1416, v1419, m1431, cs1439, v1442,
     m1454, cs1462, v1465, m1477, cs1485, v1488, m1500, cs1508, v1511, m1523, cs1531, v1534,
     m1546, cs1554, v1557, v1558, v1559, v1560, v1561, v1562, v1563, v1564, m1566, cs1574,
     v1577, m1589, cs1597, v1600, m1612, cs1620, v1623, m1635, cs1643, v1646, m1658, cs1666,
     v1669, m1681, cs1689, v1692, m1704, cs1712, v1715, m1727, cs1735, v1738,
     ld11, ld23,
     pr74, ev64, pr97, ev87, pr120, ev110, pr143, ev133,
     pr166, ev156, pr189, ev179, pr212, ev202, pr235, ev225, ev44,
     pr292, ev282, pr315, ev305, pr338, ev328, pr361, ev351,
     pr384, ev374, pr407, ev397, pr430, ev420, pr453, ev443, ev262,
     pr510, ev500, pr533, ev523, pr556, ev546, pr579, ev569,
     pr602, ev592, pr625, ev615, pr648, ev638, pr671, ev661, ev480,
     pr728, ev718, pr751, ev741, pr774, ev764, pr797, ev787,
     pr820, ev810, pr843, ev833, pr866, ev856, pr889, ev879, ev698,
     pr946, ev936, pr969, ev959, pr992, ev982, pr1015, ev1005,
     pr1038, ev1028, pr1061, ev1051, pr1084, ev1074, pr1107, ev1097, ev916,
     pr1164, ev1154, pr1187, ev1177, pr1210, ev1200, pr1233, ev1223,
     pr1256, ev1246, pr1279, ev1269, pr1302, ev1292, pr1325, ev1315, ev1134,
     pr1382, ev1372, pr1405, ev1395, pr1428, ev1418, pr1451, ev1441,
     pr1474, ev1464, pr1497, ev1487, pr1520, ev1510, pr1543, ev1533, ev1352,
     pr1586, ev1576, pr1609, ev1599, pr1632, ev1622, pr1655, ev1645,
     pr1678, ev1668, pr1701, ev1691, pr1724, ev1714, pr1747, ev1737, ev1556,
     ev1338, ev1120, ev902, ev684, ev466, ev248, ev30, -⟩
  rw [loadValue_of_repAddr ha₁] at ld11; injection ld11 with hv1; subst hv1
  rw [loadValue_of_repAddr ha₂] at ld23; injection ld23 with hv13; subst hv13
  obtain rfl := proj_addrTuple_eq 0 (by decide) pr74
  obtain rfl := proj_addrTuple_eq 1 (by decide) pr97
  obtain rfl := proj_addrTuple_eq 2 (by decide) pr120
  obtain rfl := proj_addrTuple_eq 3 (by decide) pr143
  obtain rfl := proj_addrTuple_eq 0 (by decide) pr166
  obtain rfl := proj_addrTuple_eq 1 (by decide) pr189
  obtain rfl := proj_addrTuple_eq 2 (by decide) pr212
  obtain rfl := proj_addrTuple_eq 3 (by decide) pr235
  obtain rfl := proj_addrTuple_eq 4 (by decide) pr292
  obtain rfl := proj_addrTuple_eq 5 (by decide) pr315
  obtain rfl := proj_addrTuple_eq 6 (by decide) pr338
  obtain rfl := proj_addrTuple_eq 7 (by decide) pr361
  obtain rfl := proj_addrTuple_eq 4 (by decide) pr384
  obtain rfl := proj_addrTuple_eq 5 (by decide) pr407
  obtain rfl := proj_addrTuple_eq 6 (by decide) pr430
  obtain rfl := proj_addrTuple_eq 7 (by decide) pr453
  obtain rfl := proj_addrTuple_eq 8 (by decide) pr510
  obtain rfl := proj_addrTuple_eq 9 (by decide) pr533
  obtain rfl := proj_addrTuple_eq 10 (by decide) pr556
  obtain rfl := proj_addrTuple_eq 11 (by decide) pr579
  obtain rfl := proj_addrTuple_eq 8 (by decide) pr602
  obtain rfl := proj_addrTuple_eq 9 (by decide) pr625
  obtain rfl := proj_addrTuple_eq 10 (by decide) pr648
  obtain rfl := proj_addrTuple_eq 11 (by decide) pr671
  obtain rfl := proj_addrTuple_eq 12 (by decide) pr728
  obtain rfl := proj_addrTuple_eq 13 (by decide) pr751
  obtain rfl := proj_addrTuple_eq 14 (by decide) pr774
  obtain rfl := proj_addrTuple_eq 15 (by decide) pr797
  obtain rfl := proj_addrTuple_eq 12 (by decide) pr820
  obtain rfl := proj_addrTuple_eq 13 (by decide) pr843
  obtain rfl := proj_addrTuple_eq 14 (by decide) pr866
  obtain rfl := proj_addrTuple_eq 15 (by decide) pr889
  obtain rfl := proj_addrTuple_eq 16 (by decide) pr946
  obtain rfl := proj_addrTuple_eq 17 (by decide) pr969
  obtain rfl := proj_addrTuple_eq 18 (by decide) pr992
  obtain rfl := proj_addrTuple_eq 19 (by decide) pr1015
  obtain rfl := proj_addrTuple_eq 16 (by decide) pr1038
  obtain rfl := proj_addrTuple_eq 17 (by decide) pr1061
  obtain rfl := proj_addrTuple_eq 18 (by decide) pr1084
  obtain rfl := proj_addrTuple_eq 19 (by decide) pr1107
  obtain rfl := proj_addrTuple_eq 20 (by decide) pr1164
  obtain rfl := proj_addrTuple_eq 21 (by decide) pr1187
  obtain rfl := proj_addrTuple_eq 22 (by decide) pr1210
  obtain rfl := proj_addrTuple_eq 23 (by decide) pr1233
  obtain rfl := proj_addrTuple_eq 20 (by decide) pr1256
  obtain rfl := proj_addrTuple_eq 21 (by decide) pr1279
  obtain rfl := proj_addrTuple_eq 22 (by decide) pr1302
  obtain rfl := proj_addrTuple_eq 23 (by decide) pr1325
  obtain rfl := proj_addrTuple_eq 24 (by decide) pr1382
  obtain rfl := proj_addrTuple_eq 25 (by decide) pr1405
  obtain rfl := proj_addrTuple_eq 26 (by decide) pr1428
  obtain rfl := proj_addrTuple_eq 27 (by decide) pr1451
  obtain rfl := proj_addrTuple_eq 24 (by decide) pr1474
  obtain rfl := proj_addrTuple_eq 25 (by decide) pr1497
  obtain rfl := proj_addrTuple_eq 26 (by decide) pr1520
  obtain rfl := proj_addrTuple_eq 27 (by decide) pr1543
  obtain rfl := proj_addrTuple_eq 28 (by decide) pr1586
  obtain rfl := proj_addrTuple_eq 29 (by decide) pr1609
  obtain rfl := proj_addrTuple_eq 30 (by decide) pr1632
  obtain rfl := proj_addrTuple_eq 31 (by decide) pr1655
  obtain rfl := proj_addrTuple_eq 28 (by decide) pr1678
  obtain rfl := proj_addrTuple_eq 29 (by decide) pr1701
  obtain rfl := proj_addrTuple_eq 30 (by decide) pr1724
  obtain rfl := proj_addrTuple_eq 31 (by decide) pr1747
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev64
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev87
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev110
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev133
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev156
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev179
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev202
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev225
  obtain ⟨rfl, hc0⟩ := canon_addr_chunk_spec ev44
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev282
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev305
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev328
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev351
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev374
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev397
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev420
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev443
  obtain ⟨rfl, hc1⟩ := canon_addr_chunk_spec ev262
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev500
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev523
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev546
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev569
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev592
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev615
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev638
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev661
  obtain ⟨rfl, hc2⟩ := canon_addr_chunk_spec ev480
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev718
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev741
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev764
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev787
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev810
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev833
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev856
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev879
  obtain ⟨rfl, hc3⟩ := canon_addr_chunk_spec ev698
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev936
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev959
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev982
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1005
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1028
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1051
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1074
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1097
  obtain ⟨rfl, hc4⟩ := canon_addr_chunk_spec ev916
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1154
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1177
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1200
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1223
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1246
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1269
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1292
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1315
  obtain ⟨rfl, hc5⟩ := canon_addr_chunk_spec ev1134
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1372
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1395
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1418
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1441
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1464
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1487
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1510
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1533
  obtain ⟨rfl, hc6⟩ := canon_addr_chunk_spec ev1352
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1576
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1599
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1622
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1645
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1668
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1691
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1714
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev1737
  obtain ⟨rfl, hc7⟩ := canon_addr_chunk_spec ev1556
  obtain ⟨rfl, ht6⟩ := canon_ord_then_spec ev1338
  obtain ⟨rfl, ht5⟩ := canon_ord_then_spec ev1120
  obtain ⟨rfl, ht4⟩ := canon_ord_then_spec ev902
  obtain ⟨rfl, ht3⟩ := canon_ord_then_spec ev684
  obtain ⟨rfl, ht2⟩ := canon_ord_then_spec ev466
  obtain ⟨rfl, ht1⟩ := canon_ord_then_spec ev248
  obtain ⟨rfl, ht0⟩ := canon_ord_then_spec ev30
  refine ⟨rfl, fun hr => ?_⟩
  obtain ⟨hq0, hr1⟩ := ht0 hr
  obtain ⟨hq1, hr2⟩ := ht1 hr1
  obtain ⟨hq2, hr3⟩ := ht2 hr2
  obtain ⟨hq3, hr4⟩ := ht3 hr3
  obtain ⟨hq4, hr5⟩ := ht4 hr4
  obtain ⟨hq5, hr6⟩ := ht5 hr5
  obtain ⟨hq6, hq7⟩ := ht6 hr6
  obtain ⟨e0, e1, e2, e3⟩ := hc0 hq0
  obtain ⟨e4, e5, e6, e7⟩ := hc1 hq1
  obtain ⟨e8, e9, e10, e11⟩ := hc2 hq2
  obtain ⟨e12, e13, e14, e15⟩ := hc3 hq3
  obtain ⟨e16, e17, e18, e19⟩ := hc4 hq4
  obtain ⟨e20, e21, e22, e23⟩ := hc5 hq5
  obtain ⟨e24, e25, e26, e27⟩ := hc6 hq6
  obtain ⟨e28, e29, e30, e31⟩ := hc7 hq7
  apply Vector.ext
  intro i hi
  interval_cases i
  all_goals assumption

theorem rbtree_map_lookup_generic :
    ∀ {kp tree dflt r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {a : Bytes.Address} {P : Heap F → Bytes.Address → SourceValue F → Prop},
      RepAddr h a kp →
      AddrMapAll addrMapEnum P h tree →
      ObsFn W Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>» [kp, tree, dflt] h r h' calls →
      h' = h ∧ (r = dflt ∨ P h a r) := by
  have go : ∀ (N : Nat) {kp tree dflt r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {a : Bytes.Address} {P : Heap F → Bytes.Address → SourceValue F → Prop},
      calls.length ≤ N →
      RepAddr h a kp →
      AddrMapAll addrMapEnum P h tree →
      ObsFn W (Instance.mk "RBTreeMap::rbtree_map_lookup_or_default" [.field]).symbol
        [kp, tree, dflt] h r h' calls →
      h' = h ∧ (r = dflt ∨ P h a r) := by
    intro N
    induction N with
    | zero =>
      intro kp tree dflt r h h' calls a P hle ha hall ev
      cases Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev with
      | Nil _ he18 he19 _ => exact ⟨he19, .inl he18⟩
      | Node_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc149 =>
        rw [hc149] at hle; simp at hle
      | Node_other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc209 =>
        rw [hc209] at hle; simp at hle
      | Node_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc244 =>
        rw [hc244] at hle; simp at hle
    | succ N ih =>
      intro kp tree dflt r h h' calls a P hle ha hall ev
      cases Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev with
      | Nil _ he18 he19 _ => exact ⟨he19, .inl he18⟩
      | Node_n1 w28 x_k x_v w29 w30 y51 y59 m63 cs73 v76 m78 cs86 cs122 _ hv26 ld52 _ ev88 ev75 ev124 hc149 =>
        rw [Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol] at hv26
        subst hv26
        generalize ht : (Value.construct addrMapEnum "Node" [w28, x_k, x_v, w29, w30] : SourceValue F) = t at hall
        cases hall with
        | nil => exact (construct_ctor_ne (by decide) ht.symm).elim
        | node hk _ hl _ rl _ =>
          injection ht with _ _ hvs
          injection hvs with _ hvs1
          injection hvs1 with hxk hvs2
          injection hvs2 with _ hvs3
          injection hvs3 with hw29 _
          subst hxk hw29
          rw [hl] at ld52; injection ld52 with hy51; subst hy51
          obtain ⟨rfl, -⟩ := canon_addr_cmp_spec ha hk ev88
          obtain ⟨-, rfl⟩ := Lib.is_zero_spec ev75
          have hcs : cs122.length ≤ N := by rw [hc149] at hle; simp at hle; omega
          exact ih hcs ha rl ev124
      | Node_other_n0 w28 x_k x_v w29 w30 y51 y59 v62 m63 cs73 v76 m78 cs86 x162 m164 cs173 _ hv26 _ _ ev88 ev75 _ ev175 op169 he207 he208 _ =>
        rw [Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol] at hv26
        subst hv26
        generalize ht : (Value.construct addrMapEnum "Node" [w28, x_k, x_v, w29, w30] : SourceValue F) = t at hall
        cases hall with
        | nil => exact (construct_ctor_ne (by decide) ht.symm).elim
        | node hk hP _ _ _ _ =>
          injection ht with _ _ hvs
          injection hvs with _ hvs1
          injection hvs1 with hxk hvs2
          injection hvs2 with hxv _
          subst hxk hxv
          obtain ⟨rfl, -⟩ := canon_addr_cmp_spec ha hk ev88
          obtain ⟨-, rfl⟩ := Lib.is_zero_spec ev75
          obtain ⟨x, hx1, hx2⟩ := evalBinOp_sub_eq_zero_inv op169
          have hx162 : x162 = .field 1 := hx1.trans hx2.symm
          obtain ⟨rfl, heqa⟩ := canon_addr_cmp_spec ha hk ev175
          obtain rfl := heqa hx162
          rw [he207, he208]
          exact ⟨rfl, .inr hP⟩
      | Node_other_other w28 x_k x_v w29 w30 y51 y59 v62 m63 cs73 v76 m78 cs86 v154 x162 m164 cs173 cs217 _ hv26 _ ld60 ev88 ev75 _ ev175 _ _ ev219 hc244 =>
        rw [Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol] at hv26
        subst hv26
        generalize ht : (Value.construct addrMapEnum "Node" [w28, x_k, x_v, w29, w30] : SourceValue F) = t at hall
        cases hall with
        | nil => exact (construct_ctor_ne (by decide) ht.symm).elim
        | node hk _ _ hr _ rr =>
          injection ht with _ _ hvs
          injection hvs with _ hvs1
          injection hvs1 with hxk hvs2
          injection hvs2 with _ hvs3
          injection hvs3 with _ hvs4
          injection hvs4 with hw30 _
          subst hxk hw30
          rw [hr] at ld60; injection ld60 with hy59; subst hy59
          obtain ⟨rfl, -⟩ := canon_addr_cmp_spec ha hk ev88
          obtain ⟨-, rfl⟩ := Lib.is_zero_spec ev75
          obtain ⟨rfl, -⟩ := canon_addr_cmp_spec ha hk ev175
          have hcs : cs217.length ≤ N := by rw [hc244] at hle; simp at hle; omega
          exact ih hcs ha rr ev219
  intro kp tree dflt r h h' calls a P ha hall ev
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev
  exact go calls.length (Nat.le_refl _) ha hall ev

end RolesAux

/-! ## Exported step lemmas for `Specs.Roles` -/

theorem role_map_lookup_or_default_addr_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W Obs.Names.«KernelRoles::role_map_lookup_or_default<&[Field; 32]>» args h r h' calls) :
    Specs.Roles.role_map_lookup_or_default_addr c args h r h' calls := by
  intro kv tree dflt hargs k hk
  subst hk hargs
  rw [← Obs.Names.«KernelRoles::role_map_lookup_or_default<&[Field; 32]>».symbol] at ev
  obtain ⟨-, res, hs, hr⟩ := RolesAux.role_map_lookup_generic (.ptr (.array .field 32)) ev
  rw [Obs.Names.«KernelRoles::RoleMap<&[Field; 32]>».symbol] at hs
  exact ⟨res, hs, hr⟩

theorem role_map_lookup_or_default_evidence_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W Obs.Names.«KernelRoles::role_map_lookup_or_default<&Lists::Node<KernelRoles::RoleEvidence>>»
      args h r h' calls) :
    Specs.Roles.role_map_lookup_or_default_evidence c args h r h' calls := by
  intro kv tree dflt hargs k hk
  subst hk hargs
  rw [← Obs.Names.«KernelRoles::role_map_lookup_or_default<&Lists::Node<KernelRoles::RoleEvidence>>».symbol] at ev
  obtain ⟨-, res, hs, hr⟩ := RolesAux.role_map_lookup_generic
    (.ptr (.named "Lists::Node" [.named "KernelRoles::RoleEvidence" []])) ev
  rw [Obs.Names.«KernelRoles::RoleMap<&Lists::Node<KernelRoles::RoleEvidence>>».symbol] at hs
  exact ⟨res, hs, hr⟩

theorem rbtree_map_lookup_or_default_field_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>» args h r h' calls) :
    Specs.Roles.rbtree_map_lookup_or_default_field c args h r h' calls := by
  intro kp tree dflt hargs a ha P hall
  subst hargs
  exact (RolesAux.rbtree_map_lookup_generic ha hall ev).2

theorem role_ctx_table_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_ctx_table" args h r h' calls) :
    Specs.Roles.role_ctx_table c args h r h' calls := by
  intro rc hargs hrc
  subst hargs
  obtain ⟨tbl, ax, node, hload, hnode, htbl⟩ := hrc
  cases Obs.«KernelRoles::role_ctx_table».obs ev with
  | Mk x_tbl w20 w21 ld12 he38 he39 _ =>
    rw [hload] at ld12
    rcases hnode with ⟨n, _, _, rfl⟩ | ⟨_, rfl⟩
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt
      subst hxt he38 he39
      exact ⟨rfl, htbl⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
  | Assumed x_tbl w48 ld12 he60 he61 _ =>
    rw [hload] at ld12
    rcases hnode with ⟨n, _, _, rfl⟩ | ⟨_, rfl⟩
    · exact (RolesAux.ok_construct_ctor_ne (by decide) ld12).elim
    · injection ld12 with hv
      injection hv with _ _ hxs
      injection hxs with hxt
      subst hxt he60 he61
      exact ⟨rfl, htbl⟩

theorem role_addr_index_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_addr_index" args h r h' calls) :
    Specs.Roles.role_addr_index c args h r h' calls := by
  intro tbl hargs htbl
  subst hargs
  obtain ⟨bp, byRole, byAddr, evMap, hload, _, hbyAddr, _⟩ := htbl
  obtain ⟨w20, w21, x_by_addr, w22, ld12, rfl, rfl, -⟩ :=
    Obs.«KernelRoles::role_addr_index».obs ev
  rw [hload] at ld12
  injection ld12 with hv
  injection hv with _ _ hxs
  injection hxs with _ hxs1
  injection hxs1 with _ hxs2
  injection hxs2 with hba
  subst hba
  exact ⟨rfl, hbyAddr⟩

theorem role_bound_addr_or_zero_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_bound_addr_or_zero" args h r h' calls) :
    Specs.Roles.role_bound_addr_or_zero c args h r h' calls := by
  intro tbl k hargs byRole hby
  subst hargs
  obtain ⟨bp, byAddr, evMap, hload⟩ := hby
  obtain ⟨w20, x_by_role, w21, w22, cs46, m67, ld12, hm75, ev48, -⟩ :=
    Obs.«KernelRoles::role_bound_addr_or_zero».obs ev
  rw [hload] at ld12
  injection ld12 with hv
  injection hv with _ _ hxs
  injection hxs with _ hxs1
  injection hxs1 with hbr
  subst hbr hm75
  rw [← Obs.Names.«KernelRoles::role_map_lookup_or_default<&[Field; 32]>».symbol] at ev48
  obtain ⟨rfl, res, hs_ext, hr⟩ := RolesAux.role_map_lookup_generic (.ptr (.array .field 32)) ev48
  rw [Obs.Names.«KernelRoles::RoleMap<&[Field; 32]>».symbol] at hs_ext
  have hs : Specs.Roles.RoleMapSearch roleAddrMapEnum h k byRole res :=
    RolesAux.roleMapSearch_unextend_snoc (fun _ _ e => by cases e) hs_ext
  cases res with
  | some v =>
    simp only [Option.getD_some] at hr
    subst hr
    exact ⟨some v, hs, .inl rfl⟩
  | none =>
    simp only [Option.getD_none] at hr
    subst hr
    exact ⟨none, hs, .inr ⟨rfl, RolesAux.repAddr_zeroAddr_snoc h⟩⟩

theorem role_is_bound_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_is_bound" args h r h' calls) (ih : IH c calls) :
    Specs.Roles.role_is_bound c args h r h' calls := by
  intro tbl ro hargs good htbl hr_ne byRole hby
  subst hargs
  cases Obs.«KernelRoles::role_is_bound».obs ev with
  | other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he110 _ _ =>
    exact absurd he110 hr_ne
  | n0 v1 m2 cs12 x40 y41 m42 cs51 v55 m65 cs73 ev14 ev75 ev53 op97 op47 _ _ hc105 =>
    obtain ⟨res, hs, hres⟩ :=
      ih.get (.roles .role_bound_addr_or_zero) (by rw [hc105]; roles_lt_calls) ev14
        tbl (roleNum ro) rfl byRole hby
    obtain ⟨bp, byRole', byAddr, evMap, hload, hbyRoleAll, _, _⟩ := htbl
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
        ih.get (.roles .role_addr_index) (by rw [hc105]; roles_lt_calls) ev75
          tbl rfl htbl_m2
      have hlookup :=
        ih.get (.roles .rbtree_map_lookup_or_default_field) (by rw [hc105]; roles_lt_calls)
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

theorem role_bound_addr_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_bound_addr" args h r h' calls) (ih : IH c calls) :
    Specs.Roles.role_bound_addr c args h r h' calls := by
  intro tbl ro hargs good htbl
  subst hargs
  obtain ⟨v12, m15, cs23, cs52, ev25, heq48, ev54, hc71⟩ :=
    Obs.«KernelRoles::role_bound_addr».obs ev
  obtain ⟨bp, byRole, byAddr, evMap, hload, _, _, _⟩ := htbl
  have hby : Specs.Roles.ByRole h tbl byRole := ⟨bp, byAddr, evMap, hload⟩
  have good1 : Good c cs23 := good.sub (by rw [hc71]; intro x hx; simp [hx])
  have hv12_ne : v12 ≠ .field 0 := by
    rw [heq48]
    exact fun e => one_ne_zero (Value.field.inj e)
  obtain ⟨res₁, hs₁, hbound⟩ :=
    ih.get (.roles .role_is_bound) (by rw [hc71]; roles_lt_calls) ev25
      tbl ro rfl good1 htbl hv12_ne byRole hby
  have ext1 : Heap.Extends h m15 := ev25.heap_extends
  have hby_m15 : Specs.Roles.ByRole m15 tbl byRole :=
    ⟨bp, byAddr, evMap, ext1.loadValue_eq hload⟩
  obtain ⟨res₂, hs₂, hres₂⟩ :=
    ih.get (.roles .role_bound_addr_or_zero) (by rw [hc71]; roles_lt_calls) ev54
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

theorem role_index_of_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_index_of" args h r h' calls) (ih : IH c calls) :
    Specs.Roles.role_index_of c args h r h' calls := by
  intro rc ap a hargs good hrc ha
  subst hargs
  obtain ⟨cs4, v8, m18, cs26, v29, m31, cs39, ev41, ev28, ev6, hc56⟩ :=
    Obs.«KernelRoles::role_index_of».obs ev
  obtain ⟨rfl, htbl⟩ :=
    ih.get (.roles .role_ctx_table) (by rw [hc56]; roles_lt_calls) ev41 rc rfl hrc
  obtain ⟨rfl, hIdx⟩ :=
    ih.get (.roles .role_addr_index) (by rw [hc56]; roles_lt_calls) ev28 v29 rfl htbl
  exact ih.get (.roles .rbtree_map_lookup_or_default_field)
    (by rw [hc56]; roles_lt_calls) ev6 ap v8 (.field 0) rfl a ha (IndexEntry c.t) hIdx

theorem role_of_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_of" args h r h' calls) (ih : IH c calls) :
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
        ih.get (.roles .role_addr_index) (by rw [hc217]; roles_lt_calls) ev71 tbl rfl htbl
      have hlookup :=
        ih.get (.roles .rbtree_map_lookup_or_default_field)
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
        ih.get (.roles .role_addr_index) (by rw [hc285]; roles_lt_calls) ev270 tbl rfl htbl
      have hlookup :=
        ih.get (.roles .rbtree_map_lookup_or_default_field)
          (by rw [hc285]; roles_lt_calls) ev248 ap v250 (.field 0) rfl a ha (IndexEntry c.t) hIdx
      rcases hlookup with hr0 | ⟨ro, hr, haddr⟩
      · exact .inl hr0
      · have hbinds : c.binds ro := by simp [Ctx.binds, haddr]
        have hinForce : c.inForce ro := ⟨hbinds, fun m hm => by rw [hlim] at hm; cases hm⟩
        exact .inr ⟨ro, hr, haddr, hinForce⟩

theorem role_is_step (c : Ctx) (hc : CoreFacts c) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_is" args h r h' calls) (ih : IH c calls) :
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
      ih.get (.roles .role_index_of) (by rw [hc97]; roles_lt_calls) ev23
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
      ih.get (.roles .role_of) (by rw [hc97]; roles_lt_calls) ev67
        rc ap a rfl good2 (hrc.mono ext1) (Bytes.repAddressRef_heapMono₂ addrTy ext1 ha)
    rcases hof with hv0 | ⟨ro₂, _, haddr₂, hinForce₂⟩
    · exact absurd hv0 hne91
    · have hkey₁ := keyOf_of_addressOf hc.env.tableWf haddr
      have hkey₂ := keyOf_of_addressOf hc.env.tableWf haddr₂
      have hre : (Ix.Kernel.Key.role ro : KKey) = .role ro₂ := hkey₁.symm.trans hkey₂
      injection hre with hro
      subst hro
      exact ⟨haddr, hinForce₂⟩

theorem role_addr_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_addr" args h r h' calls) (ih : IH c calls) :
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
        ih.get (.roles .role_bound_addr) (by rw [hc173]; roles_lt_calls) ev110
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
        ih.get (.roles .role_bound_addr) (by rw [hc214]; roles_lt_calls) ev197
          tbl ro rfl good_ba htbl
      have hbinds : c.binds ro := by simp [Ctx.binds, haddr]
      have hinForce : c.inForce ro := ⟨hbinds, fun m hm => by rw [hlim] at hm; cases hm⟩
      exact ⟨a, ha_h', haddr, hinForce⟩

theorem role_used_implicitly_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_used_implicitly" args h r h' calls) (ih : IH c calls) :
    Specs.Roles.role_used_implicitly c args h r h' calls := by
  intro rc ro hargs good hrc
  subst hargs
  obtain ⟨v1, m2, cs12, v31, m32, cs42, ev14, ev44, rfl, rfl, hc64⟩ :=
    Obs.«KernelRoles::role_used_implicitly».obs ev
  have good1 : Good c cs12 := good.sub (by rw [hc64]; intro x hx; simp [hx])
  obtain ⟨a, ha_m2, haddr, hinForce⟩ :=
    ih.get (.roles .role_addr) (by rw [hc64]; roles_lt_calls) ev14 rc ro rfl good1 hrc
  exact ⟨a, Bytes.repAddressRef_heapMono₂ addrTy ev44.heap_extends ha_m2, haddr, hinForce⟩

theorem role_evidence_step (c : Ctx) {args h r h' calls}
    (ev : ObsFn W "KernelRoles::role_evidence" args h r h' calls) :
    Specs.Roles.role_evidence c args h r h' calls := by
  intro tbl ro hargs htbl
  subst hargs
  obtain ⟨bp, byRole, byAddr, evMap, hload, _, _, hevAll⟩ := htbl
  obtain ⟨w20, w21, w22, x_evidence, cs46, m67, ld12, hm75, ev48, -⟩ :=
    Obs.«KernelRoles::role_evidence».obs ev
  rw [hload] at ld12
  injection ld12 with hv
  injection hv with _ _ hxs
  injection hxs with _ hxs1
  injection hxs1 with _ hxs2
  injection hxs2 with _ hxs3
  injection hxs3 with hev
  subst hev hm75
  rw [← Obs.Names.«KernelRoles::role_map_lookup_or_default<&Lists::Node<KernelRoles::RoleEvidence>>».symbol] at ev48
  obtain ⟨rfl, res, hs_ext, hr⟩ := RolesAux.role_map_lookup_generic
    (.ptr (.named "Lists::Node" [.named "KernelRoles::RoleEvidence" []])) ev48
  rw [Obs.Names.«KernelRoles::RoleMap<&Lists::Node<KernelRoles::RoleEvidence>>».symbol] at hs_ext
  have hcell_ne : ∀ ctor vs,
      (Value.construct evListEnum "Nil" [] : SourceValue F) ≠ .construct roleEvMapEnum ctor vs := by
    intro ctor vs e
    have hne : evListEnum ≠ roleEvMapEnum := by decide +kernel
    injection e with he
    exact hne he
  have hs : Specs.Roles.RoleMapSearch roleEvMapEnum h (roleNum ro) evMap res :=
    RolesAux.roleMapSearch_unextend_snoc hcell_ne hs_ext
  cases res with
  | some v =>
    simp only [Option.getD_some] at hr
    subst hr
    obtain ⟨ro', arr, hk, hmem, hlist⟩ := RolesAux.roleMapSearch_mem_all hevAll hs
    obtain rfl := RolesAux.roleNum_inj hk.symm
    have ext : Heap.Extends h (h ++ [.construct evListEnum "Nil" []]) := Heap.Extends.snoc h _
    exact ⟨arr.toList, repList_heapMono₂ evListEnum evRep_heapMono₂ ext hlist, .inr ⟨arr, hmem, rfl⟩⟩
  | none =>
    simp only [Option.getD_none] at hr
    subst hr
    exact ⟨[], .nil (by simp), .inl rfl⟩

end IxVM.Refinement.Core
