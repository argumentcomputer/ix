import IxVMRefinement.Core.CallHeaps
import IxVMRefinement.Decl.ModeledInstall
import IxVMRefinement.Obs.RBTreeMap
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.Obs.KernelModeled

/-! # Modeled Inductive Block Dispatch & Top-Level Declaration Assembly (`Modeled.lean`)

Completes the modeled-inductive slice and joins it with standalone value declarations (`Value.lean`,
`ModeledInstall.lean`) and the native-inductive seam (`NativeIndStep`) to discharge
`IxVM.Consistency.Decls.{u} baseSeams` and `IxVM.Consistency.DeclsObligation.{u} baseSeams`:

1. **`AddrMapAll` & `RBTreeMap` insertion (`rbtree_map_insert_field_addrMapAll`)**: proves from
   the generated path lemmas for `rbtree_map_balance_fix`, `rbtree_map_balance`, `rbtree_map_ins`,
   and `rbtree_map_insert<Field>` that inserting `(a, 1)` into an `AddrMapAll` address set extends
   its membership predicate to `S · ∨ · = a`.
2. **Payload address streams, list operations, & `RenameMap` construction**: refines
   `KernelModeled::get_addrs`, `Lists::length<&[Field; 32]>`, `Lists::concat<&[Field; 32]>`,
   proves `ixAddr_injective` and `keyOf_injective`, and builds `RenameMap` for the 3-way
   concatenated `(types ++ ctors ++ recs) → (type_models ++ ctor_models ++ rec_models)` table.
3. **`KernelCheck::check_const` & `KernelModeled::check_family` component specs**:
   - `check_const_ind_inv`, `check_const_ctor_inv`, `check_const_rec_inv` (splitting safe unpinned
     inductive members cleanly into native `block_is_modeled = 0` vs modeled `block_is_modeled ≠ 0`),
   - `check_modeled_block_inv`, `check_family_seg1_inv`,
   - `check_advice_records_spec` (stepping `(env, seen)` along `advice` via `AdviceStepOracle` +
     `rbtree_map_insert_field_addrMapAll`),
   - `ci_lvls_type_spec`, `member_val_spec`, `members_val_spec` (matching every block member's
     signature against its advice `Defn` model via `ExactGetCI` + `rename_exact` +
     `kexpr_struct_eq_one`),
4. **`NativeIndStep`**, the native-inductive seam. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Library.List Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule
  RecRuleFire IndCaps BasisKind Declaration LevelParam EnvExt ReducibilityHint Derived
  auxKey projTableName recRuleBits hasFvar_renameConsts)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "decl_lt_calls" : tactic =>
  `(tactic| simp +arith [Call.sizeOf_spec, List.sizeOf_append])

universe u

private abbrev zg : Nat → KExpr := fun _ => .sort .zero

/-! ## Section 1: `AddrMapAll` & `RBTreeMap::rbtree_map_insert<Field>` Refinement -/

theorem AddrMapAll.valueType_eq {en : String}
    {P : Heap F → Bytes.Address → SourceValue F → Prop}
    {h : Heap F} {t : SourceValue F} (ht : AddrMapAll en P h t) :
    Value.type t = .enum en := by
  cases ht <;> simp [Value.type]

private theorem addrMapAll_mono_pred {en : String}
    {P₁ P₂ : Heap F → Bytes.Address → SourceValue F → Prop}
    {h₁ h₂ : Heap F} {t : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (himp : ∀ {h a v}, P₁ h a v → P₂ h₂ a v)
    (ht : AddrMapAll en P₁ h₁ t) : AddrMapAll en P₂ h₂ t := by
  induction ht with
  | nil => exact .nil
  | node hk hP hl hr _ _ ihl ihr =>
    exact .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk) (himp hP)
      (ext.loadValue_eq hl) (ext.loadValue_eq hr) ihl ihr

private theorem addrSet_mono {S : Bytes.Address → Prop}
    {h₁ h₂ : Heap F} {t : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (ht : AddrMapAll addrMapEnum (fun _ a _ => S a) h₁ t) :
    AddrMapAll addrMapEnum (fun _ a _ => S a) h₂ t :=
  addrMapAll_mono_pred (P₂ := fun _ a _ => S a) ext (fun hp => hp) ht

private theorem load_stored_addrMapAll_enum {en : String}
    {P : Heap F → Bytes.Address → SourceValue F → Prop}
    {h₀ h' : Heap F} {t : SourceValue F}
    (ht : AddrMapAll en P h₀ t)
    (ext : Heap.Extends (h₀ ++ [t]) h') :
    loadValue h' (.ptr (.enum en) h₀.length) = .ok t := by
  have hcell : (h₀ ++ [t])[h₀.length]? = some t := by simp
  have hcell' : h'[h₀.length]? = some t := ext.getElem?_eq hcell
  cases ht with
  | nil => exact Lib.load_enum_cell hcell'
  | node _ _ _ _ _ _ => exact Lib.load_enum_cell hcell'

private theorem load_stored_addrMapAll_type {en : String}
    {P : Heap F → Bytes.Address → SourceValue F → Prop}
    {h₀ h' : Heap F} {t : SourceValue F}
    (ht : AddrMapAll en P h₀ t)
    (ext : Heap.Extends (h₀ ++ [t]) h') :
    loadValue h' (.ptr (Value.type t) h₀.length) = .ok t := by
  rw [AddrMapAll.valueType_eq ht]
  exact load_stored_addrMapAll_enum ht ext

private theorem addrMapAll_node_inv {en : String}
    {P : Heap F → Bytes.Address → SourceValue F → Prop}
    {h : Heap F} {x_c x_k x_v x_l x_r : SourceValue F}
    (ht : AddrMapAll en P h (.construct en "Node" [x_c, x_k, x_v, x_l, x_r])) :
    ∃ (c : F) (a : Bytes.Address) (lv rv : SourceValue F),
      x_c = .field c ∧
      Bytes.RepAddressRef addrTy h a x_k ∧
      P h a x_v ∧
      loadValue h x_l = .ok lv ∧
      loadValue h x_r = .ok rv ∧
      AddrMapAll en P h lv ∧
      AddrMapAll en P h rv := by
  generalize hv : Value.construct en "Node" [x_c, x_k, x_v, x_l, x_r] = t at ht
  cases ht with
  | nil =>
    injection hv with _ htag _
    exact absurd htag (by decide)
  | @node c _ _ _ _ lv rv a hk hP hl hr rl rr =>
    injection hv with _ _ hargs
    injection hargs with h1 h2
    injection h2 with h3 h4
    injection h4 with h5 h6
    injection h6 with h7 h8
    injection h8 with h9 _
    subst h1 h3 h5 h7 h9
    exact ⟨c, a, lv, rv, rfl, hk, hP, hl, hr, rl, rr⟩

private theorem rbtree_map_balance_fix_addrMapAll {t_V : Generic.Ty}
    {P : Bytes.Address → SourceValue F → Prop}
    {a_key : Bytes.Address} {x_key x_value x_left x_right r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hk : Bytes.RepAddressRef addrTy h a_key x_key)
    (hv : P a_key x_value)
    (hl : AddrMapAll (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol (fun _ a v => P a v) h x_left)
    (hr : AddrMapAll (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol (fun _ a v => P a v) h x_right)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_balance_fix" [t_V]).symbol
      [x_key, x_value, x_left, x_right] h r h' cs) :
    let en := (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
    AddrMapAll en (fun _ a v => P a v) h' r ∧
    (∃ (c_out : F) (k_out v_out l_out r_out : SourceValue F),
      r = .construct en "Node" [.field c_out, k_out, v_out, l_out, r_out]) ∧
    Heap.Extends h h' := by
  let en := (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
  let Pm : Heap F → Bytes.Address → SourceValue F → Prop := fun _ a v => P a v
  cases Obs.«RBTreeMap::rbtree_map_balance_fix».obs ev with
  | Node_bind x_yk x_yv w40 x_c x_xk x_xv x_a x_b m134 m186 m231
      hv37 ld63 he112 hm142 hm194 hm239 he241 _ =>
    rw [hv37] at hl
    obtain ⟨_, a_y, lv_w40, rv_c, _, hyk, hyv, ld_w40, ld_c, hw40, hc_map⟩ := addrMapAll_node_inv hl
    rw [ld63] at ld_w40
    injection ld_w40 with hlv_eq
    rw [← hlv_eq] at hw40
    obtain ⟨_, a_x, lv_a, rv_b, _, hxk, hxv, ld_a, ld_b, ha_map, hb_map⟩ := addrMapAll_node_inv hw40
    let nodeL : SourceValue F := .construct en "Node" [.field 1, x_xk, x_xv, x_a, x_b]
    let nodeR : SourceValue F := .construct en "Node"
      [.field 1, x_key, x_value, x_c, .ptr (Value.type x_right) m134.length]
    have ext_134 : Heap.Extends h m134 := hm142 ▸ heap_extends_append h [nodeL]
    have ext_231 : Heap.Extends m134 m231 := hm239 ▸ heap_extends_append m134 [x_right]
    have ext_186 : Heap.Extends m231 m186 := hm194 ▸ heap_extends_append m231 [nodeR]
    have ext_all : Heap.Extends h h' := he241 ▸ ext_134.trans (ext_231.trans ext_186)
    have hnodeL_h : AddrMapAll en Pm h nodeL :=
      .node hxk hxv ld_a ld_b ha_map hb_map
    have hnodeL_h' : AddrMapAll en Pm h' nodeL :=
      addrMapAll_mono_pred ext_all (fun hp => hp) hnodeL_h
    have ld_nodeL : loadValue h' (.ptr (.enum en) h.length) = .ok nodeL :=
      load_stored_addrMapAll_enum hnodeL_h (hm142 ▸ he241 ▸ ext_231.trans ext_186)
    have hright_134 : AddrMapAll en Pm m134 x_right :=
      addrMapAll_mono_pred ext_134 (fun hp => hp) hr
    have hright_231 : AddrMapAll en Pm m231 x_right :=
      addrMapAll_mono_pred (ext_134.trans ext_231) (fun hp => hp) hr
    have ld_right_231 : loadValue m231 (.ptr (Value.type x_right) m134.length) = .ok x_right :=
      load_stored_addrMapAll_type hright_134 (hm239 ▸ Heap.Extends.refl _)
    have hnodeR_231 : AddrMapAll en Pm m231 nodeR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy (ext_134.trans ext_231) hk) hv
        ((ext_134.trans ext_231).loadValue_eq ld_c) ld_right_231
        (addrMapAll_mono_pred (ext_134.trans ext_231) (fun hp => hp) hc_map) hright_231
    have hnodeR_h' : AddrMapAll en Pm h' nodeR :=
      addrMapAll_mono_pred (he241 ▸ ext_186) (fun hp => hp) hnodeR_231
    have ld_nodeR : loadValue h' (.ptr (.enum en) m231.length) = .ok nodeR :=
      load_stored_addrMapAll_enum hnodeR_231 (hm194 ▸ he241 ▸ Heap.Extends.refl _)
    rw [he112]
    exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hyk) hyv
      ld_nodeL ld_nodeR hnodeL_h' hnodeR_h',
      ⟨0, x_yk, x_yv, _, _, rfl⟩, ext_all⟩
  | Node_bind_1 x_xk x_xv x_a w255 x_yk x_yv x_b x_c m349 m401 m446
      hv252 ld283 he327 hm357 hm409 hm454 he456 _ =>
    rw [hv252] at hl
    obtain ⟨_, a_x, lv_a, rv_w255, _, hxk, hxv, ld_a, ld_w255, ha_map, hw255⟩ :=
      addrMapAll_node_inv hl
    rw [ld283] at ld_w255
    injection ld_w255 with hrv_eq
    rw [← hrv_eq] at hw255
    obtain ⟨_, a_y, lv_b, rv_c, _, hyk, hyv, ld_b, ld_c, hb_map, hc_map⟩ :=
      addrMapAll_node_inv hw255
    let nodeL : SourceValue F := .construct en "Node" [.field 1, x_xk, x_xv, x_a, x_b]
    let nodeR : SourceValue F := .construct en "Node"
      [.field 1, x_key, x_value, x_c, .ptr (Value.type x_right) m349.length]
    have ext_349 : Heap.Extends h m349 := hm357 ▸ heap_extends_append h [nodeL]
    have ext_446 : Heap.Extends m349 m446 := hm454 ▸ heap_extends_append m349 [x_right]
    have ext_401 : Heap.Extends m446 m401 := hm409 ▸ heap_extends_append m446 [nodeR]
    have ext_all : Heap.Extends h h' := he456 ▸ ext_349.trans (ext_446.trans ext_401)
    have hnodeL_h : AddrMapAll en Pm h nodeL :=
      .node hxk hxv ld_a ld_b ha_map hb_map
    have hnodeL_h' : AddrMapAll en Pm h' nodeL :=
      addrMapAll_mono_pred ext_all (fun hp => hp) hnodeL_h
    have ld_nodeL : loadValue h' (.ptr (.enum en) h.length) = .ok nodeL :=
      load_stored_addrMapAll_enum hnodeL_h (hm357 ▸ he456 ▸ ext_446.trans ext_401)
    have hright_349 : AddrMapAll en Pm m349 x_right :=
      addrMapAll_mono_pred ext_349 (fun hp => hp) hr
    have hright_446 : AddrMapAll en Pm m446 x_right :=
      addrMapAll_mono_pred (ext_349.trans ext_446) (fun hp => hp) hr
    have ld_right_446 : loadValue m446 (.ptr (Value.type x_right) m349.length) = .ok x_right :=
      load_stored_addrMapAll_type hright_349 (hm454 ▸ Heap.Extends.refl _)
    have hnodeR_446 : AddrMapAll en Pm m446 nodeR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy (ext_349.trans ext_446) hk) hv
        ((ext_349.trans ext_446).loadValue_eq ld_c) ld_right_446
        (addrMapAll_mono_pred (ext_349.trans ext_446) (fun hp => hp) hc_map) hright_446
    have hnodeR_h' : AddrMapAll en Pm h' nodeR :=
      addrMapAll_mono_pred (he456 ▸ ext_401) (fun hp => hp) hnodeR_446
    have ld_nodeR : loadValue h' (.ptr (.enum en) m446.length) = .ok nodeR :=
      load_stored_addrMapAll_enum hnodeR_446 (hm409 ▸ he456 ▸ Heap.Extends.refl _)
    rw [he327]
    exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hyk) hyv
      ld_nodeL ld_nodeR hnodeL_h' hnodeR_h',
      ⟨0, x_yk, x_yv, _, _, rfl⟩, ext_all⟩
  | bind_Node x_zk x_zv w474 x_d x_yk x_yv x_b x_c m564 m602 m620
      hv471 ld497 he542 hm572 hm610 hm628 he671 _ =>
    rw [hv471] at hr
    obtain ⟨_, a_z, lv_w474, rv_d, _, hzk, hzv, ld_w474, ld_d, hw474, hd_map⟩ :=
      addrMapAll_node_inv hr
    rw [ld497] at ld_w474
    injection ld_w474 with hlv_eq
    rw [← hlv_eq] at hw474
    obtain ⟨_, a_y, lv_b, rv_c, _, hyk, hyv, ld_b, ld_c, hb_map, hc_map⟩ :=
      addrMapAll_node_inv hw474
    let nodeL : SourceValue F := .construct en "Node"
      [.field 1, x_key, x_value, .ptr (Value.type x_left) h.length, x_b]
    let nodeR : SourceValue F := .construct en "Node" [.field 1, x_zk, x_zv, x_c, x_d]
    have ext_602 : Heap.Extends h m602 := hm610 ▸ heap_extends_append h [x_left]
    have ext_564 : Heap.Extends m602 m564 := hm572 ▸ heap_extends_append m602 [nodeL]
    have ext_620 : Heap.Extends m564 m620 := hm628 ▸ heap_extends_append m564 [nodeR]
    have ext_all : Heap.Extends h h' := he671 ▸ ext_602.trans (ext_564.trans ext_620)
    have hleft_602 : AddrMapAll en Pm m602 x_left :=
      addrMapAll_mono_pred ext_602 (fun hp => hp) hl
    have ld_left_602 : loadValue m602 (.ptr (Value.type x_left) h.length) = .ok x_left :=
      load_stored_addrMapAll_type hl (hm610 ▸ Heap.Extends.refl _)
    have hnodeL_602 : AddrMapAll en Pm m602 nodeL :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext_602 hk) hv
        ld_left_602 (ext_602.loadValue_eq ld_b)
        hleft_602 (addrMapAll_mono_pred ext_602 (fun hp => hp) hb_map)
    have hnodeL_h' : AddrMapAll en Pm h' nodeL :=
      addrMapAll_mono_pred (he671 ▸ ext_564.trans ext_620) (fun hp => hp) hnodeL_602
    have ld_nodeL : loadValue h' (.ptr (.enum en) m602.length) = .ok nodeL :=
      load_stored_addrMapAll_enum hnodeL_602 (hm572 ▸ he671 ▸ ext_620)
    have hnodeR_564 : AddrMapAll en Pm m564 nodeR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy (ext_602.trans ext_564) hzk) hzv
        ((ext_602.trans ext_564).loadValue_eq ld_c) ((ext_602.trans ext_564).loadValue_eq ld_d)
        (addrMapAll_mono_pred (ext_602.trans ext_564) (fun hp => hp) hc_map)
        (addrMapAll_mono_pred (ext_602.trans ext_564) (fun hp => hp) hd_map)
    have hnodeR_h' : AddrMapAll en Pm h' nodeR :=
      addrMapAll_mono_pred (he671 ▸ ext_620) (fun hp => hp) hnodeR_564
    have ld_nodeR : loadValue h' (.ptr (.enum en) m564.length) = .ok nodeR :=
      load_stored_addrMapAll_enum hnodeR_564 (hm628 ▸ he671 ▸ Heap.Extends.refl _)
    rw [he542]
    exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hyk) hyv
      ld_nodeL ld_nodeR hnodeL_h' hnodeR_h',
      ⟨0, x_yk, x_yv, _, _, rfl⟩, ext_all⟩
  | bind_Node_1 x_yk x_yv x_b w689 x_zk x_zv x_c x_d m779 m817 m835
      hv686 ld717 he757 hm787 hm825 hm843 he886 _ =>
    rw [hv686] at hr
    obtain ⟨_, a_y, lv_b, rv_w689, _, hyk, hyv, ld_b, ld_w689, hb_map, hw689⟩ :=
      addrMapAll_node_inv hr
    rw [ld717] at ld_w689
    injection ld_w689 with hrv_eq
    rw [← hrv_eq] at hw689
    obtain ⟨_, a_z, lv_c, rv_d, _, hzk, hzv, ld_c, ld_d, hc_map, hd_map⟩ :=
      addrMapAll_node_inv hw689
    let nodeL : SourceValue F := .construct en "Node"
      [.field 1, x_key, x_value, .ptr (Value.type x_left) h.length, x_b]
    let nodeR : SourceValue F := .construct en "Node" [.field 1, x_zk, x_zv, x_c, x_d]
    have ext_817 : Heap.Extends h m817 := hm825 ▸ heap_extends_append h [x_left]
    have ext_779 : Heap.Extends m817 m779 := hm787 ▸ heap_extends_append m817 [nodeL]
    have ext_835 : Heap.Extends m779 m835 := hm843 ▸ heap_extends_append m779 [nodeR]
    have ext_all : Heap.Extends h h' := he886 ▸ ext_817.trans (ext_779.trans ext_835)
    have hleft_817 : AddrMapAll en Pm m817 x_left :=
      addrMapAll_mono_pred ext_817 (fun hp => hp) hl
    have ld_left_817 : loadValue m817 (.ptr (Value.type x_left) h.length) = .ok x_left :=
      load_stored_addrMapAll_type hl (hm825 ▸ Heap.Extends.refl _)
    have hnodeL_817 : AddrMapAll en Pm m817 nodeL :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy ext_817 hk) hv
        ld_left_817 (ext_817.loadValue_eq ld_b)
        hleft_817 (addrMapAll_mono_pred ext_817 (fun hp => hp) hb_map)
    have hnodeL_h' : AddrMapAll en Pm h' nodeL :=
      addrMapAll_mono_pred (he886 ▸ ext_779.trans ext_835) (fun hp => hp) hnodeL_817
    have ld_nodeL : loadValue h' (.ptr (.enum en) m817.length) = .ok nodeL :=
      load_stored_addrMapAll_enum hnodeL_817 (hm787 ▸ he886 ▸ ext_835)
    have hnodeR_779 : AddrMapAll en Pm m779 nodeR :=
      .node (Bytes.repAddressRef_heapMono₂ addrTy (ext_817.trans ext_779) hzk) hzv
        ((ext_817.trans ext_779).loadValue_eq ld_c) ((ext_817.trans ext_779).loadValue_eq ld_d)
        (addrMapAll_mono_pred (ext_817.trans ext_779) (fun hp => hp) hc_map)
        (addrMapAll_mono_pred (ext_817.trans ext_779) (fun hp => hp) hd_map)
    have hnodeR_h' : AddrMapAll en Pm h' nodeR :=
      addrMapAll_mono_pred (he886 ▸ ext_835) (fun hp => hp) hnodeR_779
    have ld_nodeR : loadValue h' (.ptr (.enum en) m779.length) = .ok nodeR :=
      load_stored_addrMapAll_enum hnodeR_779 (hm843 ▸ he886 ▸ Heap.Extends.refl _)
    rw [he757]
    exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hyk) hyv
      ld_nodeL ld_nodeR hnodeL_h' hnodeR_h',
      ⟨0, x_yk, x_yv, _, _, rfl⟩, ext_all⟩
  | other m921 m932 he899 hm929 hm940 he942 _ =>
    have ext_921 : Heap.Extends h m921 := hm929 ▸ heap_extends_append h [x_left]
    have ext_932 : Heap.Extends m921 m932 := hm940 ▸ heap_extends_append m921 [x_right]
    have ext_all : Heap.Extends h h' := he942 ▸ ext_921.trans ext_932
    have hright_921 : AddrMapAll en Pm m921 x_right :=
      addrMapAll_mono_pred ext_921 (fun hp => hp) hr
    have ld_left : loadValue h' (.ptr (Value.type x_left) h.length) = .ok x_left :=
      load_stored_addrMapAll_type hl (hm929 ▸ he942 ▸ ext_932)
    have ld_right : loadValue h' (.ptr (Value.type x_right) m921.length) = .ok x_right :=
      load_stored_addrMapAll_type hright_921 (hm940 ▸ he942 ▸ Heap.Extends.refl _)
    rw [he899]
    exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hk) hv ld_left ld_right
      (addrMapAll_mono_pred ext_all (fun hp => hp) hl)
      (addrMapAll_mono_pred ext_all (fun hp => hp) hr),
      ⟨1, x_key, x_value, _, _, rfl⟩, ext_all⟩

private theorem rbtree_map_balance_addrMapAll {t_V : Generic.Ty}
    {P : Bytes.Address → SourceValue F → Prop}
    {c_in : F} {a_key : Bytes.Address} {x_key x_value x_left x_right r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hk : Bytes.RepAddressRef addrTy h a_key x_key)
    (hv : P a_key x_value)
    (hl : AddrMapAll (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol (fun _ a v => P a v) h x_left)
    (hr : AddrMapAll (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol (fun _ a v => P a v) h x_right)
    (ev : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_balance" [t_V]).symbol
      [.field c_in, x_key, x_value, x_left, x_right] h r h' cs) :
    let en := (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
    AddrMapAll en (fun _ a v => P a v) h' r ∧
    (∃ (c_out : F) (k_out v_out l_out r_out : SourceValue F),
      r = .construct en "Node" [.field c_out, k_out, v_out, l_out, r_out]) ∧
    Heap.Extends h h' := by
  let en := (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
  let Pm : Heap F → Bytes.Address → SourceValue F → Prop := fun _ a v => P a v
  cases Obs.«RBTreeMap::rbtree_map_balance».obs ev with
  | n1 _ _ ev20 _ =>
    exact rbtree_map_balance_fix_addrMapAll hk hv hl hr ev20
  | other m89 m100 _ he66 hm97 hm108 he110 _ =>
    have ext_89 : Heap.Extends h m89 := hm97 ▸ heap_extends_append h [x_left]
    have ext_100 : Heap.Extends m89 m100 := hm108 ▸ heap_extends_append m89 [x_right]
    have ext_all : Heap.Extends h h' := he110 ▸ ext_89.trans ext_100
    have hright_89 : AddrMapAll en Pm m89 x_right :=
      addrMapAll_mono_pred ext_89 (fun hp => hp) hr
    have ld_left : loadValue h' (.ptr (Value.type x_left) h.length) = .ok x_left :=
      load_stored_addrMapAll_type hl (hm97 ▸ he110 ▸ ext_100)
    have ld_right : loadValue h' (.ptr (Value.type x_right) m89.length) = .ok x_right :=
      load_stored_addrMapAll_type hright_89 (hm108 ▸ he110 ▸ Heap.Extends.refl _)
    rw [he66]
    exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hk) hv ld_left ld_right
      (addrMapAll_mono_pred ext_all (fun hp => hp) hl)
      (addrMapAll_mono_pred ext_all (fun hp => hp) hr),
      ⟨c_in, x_key, x_value, _, _, rfl⟩, ext_all⟩

private theorem rbtree_map_ins_addrMapAll {t_V : Generic.Ty}
    {P : Bytes.Address → SourceValue F → Prop}
    {h₀ : Heap F} {x_tree : SourceValue F}
    (ht0 : AddrMapAll (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
      (fun _ a v => P a v) h₀ x_tree) :
    ∀ {a_key : Bytes.Address} {x_key x_value r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Heap.Extends h₀ h →
      Bytes.RepAddressRef addrTy h a_key x_key →
      P a_key x_value →
      ObsFn W (Instance.mk "RBTreeMap::rbtree_map_ins" [t_V]).symbol
        [x_key, x_value, x_tree] h r h' cs →
      let en := (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
      AddrMapAll en (fun _ a v => P a v) h' r ∧
      (∃ (c_out : F) (k_out v_out l_out r_out : SourceValue F),
        r = .construct en "Node" [.field c_out, k_out, v_out, l_out, r_out]) ∧
      Heap.Extends h h' := by
  let en := (Instance.mk "RBTreeMap::RBTreeMap" [t_V]).symbol
  let Pm : Heap F → Bytes.Address → SourceValue F → Prop := fun _ a v => P a v
  induction ht0 with
  | nil =>
    intro a_key x_key x_value r h h' cs _ hk hv ev
    match Obs.«RBTreeMap::rbtree_map_ins».obs ev with
    | .Nil (m47 := m47) (m60 := m60) (he25 := he25) (hm55 := hm55) (hm68 := hm68) (he72 := he72) .. =>
      let nilVal : SourceValue F := .construct en "Nil" []
      have ext_47 : Heap.Extends h m47 := hm55 ▸ heap_extends_append h [nilVal]
      have ext_60 : Heap.Extends m47 m60 := hm68 ▸ heap_extends_append m47 [nilVal]
      have ext_all : Heap.Extends h h' := he72 ▸ ext_47.trans ext_60
      have ld_l : loadValue h' (.ptr (.enum en) h.length) = .ok nilVal :=
        load_stored_addrMapAll_enum (.nil (P := Pm)) (hm55 ▸ he72 ▸ ext_60)
      have ld_r : loadValue h' (.ptr (.enum en) m47.length) = .ok nilVal :=
        load_stored_addrMapAll_enum (.nil (P := Pm)) (hm68 ▸ he72 ▸ Heap.Extends.refl _)
      rw [he25]
      exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hk) hv ld_l ld_r .nil .nil,
        ⟨0, x_key, x_value, _, _, rfl⟩, ext_all⟩
    | .Node_n0 (hv_yxogouup := hv79) .. =>
      injection hv79 with _ htag _; exact absurd htag (by decide)
    | .Node_n1 (hv_yxogouup := hv79) .. =>
      injection hv79 with _ htag _; exact absurd htag (by decide)
    | .Node_other (hv_yxogouup := hv79) .. =>
      injection hv79 with _ htag _; exact absurd htag (by decide)
  | @node c_t kp vp lp rp lv rv _ hk_t hP_t hl_t hr_t rl_t rr_t ihl ihr =>
    intro a_key x_key x_value r h h' cs ext0 hk hv ev
    match Obs.«RBTreeMap::rbtree_map_ins».obs ev with
    | .Nil (hv15 := hv15) .. =>
      injection hv15 with _ htag _; exact absurd htag (by decide)
    | .Node_n0 (x_color := x_color) (x_k := x_k) (x_v := x_v) (x_left_ptr := x_left_ptr)
        (x_right_ptr := x_right_ptr) (m_iczzthhe := m_cmp) (v_xkvkfotc := v_ins)
        (v_wltcltau := v_r) (m_mfdajbya := m_ins) (v_yeofoqcl := v_l)
        (hv_yxogouup := hv79) (ev_khiwzwox := ev_cmp) (ld_ntcpyjql := ld_l)
        (ev_yrqpzaso := ev_ins) (ld_gfopccso := ld_r) (ev_ueayrilk := ev_bal) .. =>
      injection hv79 with _ _ hargs
      injection hargs with hc_eq h1
      injection h1 with hk_eq h2
      injection h2 with hv_eq h3
      injection h3 with hl_eq h4
      injection h4 with hr_eq _
      subst hc_eq hk_eq hv_eq hl_eq hr_eq
      have ext_cmp : Heap.Extends h m_cmp := ObsFn.heap_extends ev_cmp
      have hld_l : loadValue m_cmp lp = .ok lv := (ext0.trans ext_cmp).loadValue_eq hl_t
      rw [hld_l] at ld_l; injection ld_l with hv_l; subst hv_l
      obtain ⟨hv_ins, _, ext_ins⟩ :=
        ihl (ext0.trans ext_cmp) (Bytes.repAddressRef_heapMono₂ addrTy ext_cmp hk) hv ev_ins
      have ext_h_ins : Heap.Extends h m_ins := ext_cmp.trans ext_ins
      have ext_b_ins : Heap.Extends h₀ m_ins := ext0.trans ext_h_ins
      have hld_r : loadValue m_ins rp = .ok rv := ext_b_ins.loadValue_eq hr_t
      rw [hld_r] at ld_r; injection ld_r with hv_r; subst hv_r
      obtain ⟨hout, hshape, ext_bal⟩ :=
        rbtree_map_balance_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_b_ins hk_t) hP_t
          hv_ins (addrMapAll_mono_pred (P₂ := Pm) ext_b_ins (fun hp => hp) rr_t) ev_bal
      exact ⟨hout, hshape, ext_h_ins.trans ext_bal⟩
    | .Node_n1 (x_color := x_color) (x_k := x_k) (x_v := x_v) (x_left_ptr := x_left_ptr)
        (x_right_ptr := x_right_ptr) (m_iczzthhe := m_cmp) (hv_yxogouup := hv79)
        (ev_khiwzwox := ev_cmp) (he_pjwpkiht := he_r) (he_zhcposei := he_h) .. =>
      injection hv79 with _ _ hargs
      injection hargs with hc_eq h1
      injection h1 with hk_eq h2
      injection h2 with hv_eq h3
      injection h3 with hl_eq h4
      injection h4 with hr_eq _
      subst hc_eq hk_eq hv_eq hl_eq hr_eq
      have ext_all : Heap.Extends h h' := he_h ▸ ObsFn.heap_extends ev_cmp
      have ext_b : Heap.Extends h₀ h' := ext0.trans ext_all
      rw [he_r]
      exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hk) hv
        (ext_b.loadValue_eq hl_t) (ext_b.loadValue_eq hr_t)
        (addrMapAll_mono_pred (P₂ := Pm) ext_b (fun hp => hp) rl_t)
        (addrMapAll_mono_pred (P₂ := Pm) ext_b (fun hp => hp) rr_t),
        ⟨c_t, x_key, x_value, _, _, rfl⟩, ext_all⟩
    | .Node_other (x_color := x_color) (x_k := x_k) (x_v := x_v) (x_left_ptr := x_left_ptr)
        (x_right_ptr := x_right_ptr) (m_iczzthhe := m_cmp) (v_gnsaykcn := v_l)
        (v_wkuqfaty := v_ins) (m_zxtzwonh := m_ins) (v_oxqmdgey := v_r)
        (hv_yxogouup := hv79) (ev_khiwzwox := ev_cmp) (ld_soaidfau := ld_l)
        (ld_ihxnivmy := ld_r) (ev_avtjegwj := ev_ins) (ev_kdezdqmp := ev_bal) .. =>
      injection hv79 with _ _ hargs
      injection hargs with hc_eq h1
      injection h1 with hk_eq h2
      injection h2 with hv_eq h3
      injection h3 with hl_eq h4
      injection h4 with hr_eq _
      subst hc_eq hk_eq hv_eq hl_eq hr_eq
      have ext_cmp : Heap.Extends h m_cmp := ObsFn.heap_extends ev_cmp
      have hld_l : loadValue m_cmp lp = .ok lv := (ext0.trans ext_cmp).loadValue_eq hl_t
      have hld_r : loadValue m_cmp rp = .ok rv := (ext0.trans ext_cmp).loadValue_eq hr_t
      rw [hld_l] at ld_l; injection ld_l with hv_l; subst hv_l
      rw [hld_r] at ld_r; injection ld_r with hv_r; subst hv_r
      obtain ⟨hv_ins, _, ext_ins⟩ :=
        ihr (ext0.trans ext_cmp) (Bytes.repAddressRef_heapMono₂ addrTy ext_cmp hk) hv ev_ins
      have ext_h_ins : Heap.Extends h m_ins := ext_cmp.trans ext_ins
      have ext_b_ins : Heap.Extends h₀ m_ins := ext0.trans ext_h_ins
      obtain ⟨hout, hshape, ext_bal⟩ :=
        rbtree_map_balance_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_b_ins hk_t) hP_t
          (addrMapAll_mono_pred (P₂ := Pm) ext_b_ins (fun hp => hp) rl_t) hv_ins ev_bal
      exact ⟨hout, hshape, ext_h_ins.trans ext_bal⟩

/-- Inserting `(x_key, .field 1)` into an `AddrMapAll addrMapEnum` set extends its membership
predicate from `S` to `fun a => S a ∨ a = a_key`. -/
theorem rbtree_map_insert_field_addrMapAll
    {S : Bytes.Address → Prop} {a_key : Bytes.Address}
    {x_key x_tree r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hk : Bytes.RepAddressRef addrTy h a_key x_key)
    (ht : AddrMapAll addrMapEnum (fun _ a _ => S a) h x_tree)
    (ev : ObsFn W Obs.Names.«RBTreeMap::rbtree_map_insert<Field>»
      [x_key, .field 1, x_tree] h r h' cs) :
    AddrMapAll addrMapEnum (fun _ a _ => S a ∨ a = a_key) h' r := by
  have ev' : ObsFn W (Instance.mk "RBTreeMap::rbtree_map_insert" [.field]).symbol
      [x_key, .field 1, x_tree] h r h' cs := by
    rw [Obs.Names.«RBTreeMap::rbtree_map_insert<Field>».symbol]
    exact ev
  cases Obs.«RBTreeMap::rbtree_map_insert».obs ev' with
  | run m2 cs12 w55 x_k x_v x_left x_right ev14 he89 he124 _ =>
    have ht_w : AddrMapAll (Instance.mk "RBTreeMap::RBTreeMap" [.field]).symbol
        (fun _ a _ => S a ∨ a = a_key) h x_tree := by
      rw [Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol]
      exact addrMapAll_mono_pred (Heap.Extends.refl h) (fun hp => Or.inl hp) ht
    obtain ⟨hins, _, _⟩ :=
      rbtree_map_ins_addrMapAll ht_w (Heap.Extends.refl h) hk (Or.inr rfl) ev14
    rw [Obs.Names.«RBTreeMap::RBTreeMap<Field>».symbol] at hins he89
    obtain ⟨_, a_root, lv, rv, _, hkr, hPr, hlr, hrr, rlr, rrr⟩ := addrMapAll_node_inv hins
    rw [he89, he124]
    exact .node hkr hPr hlr hrr rlr rrr

/-! ## Section 2: Address Deserialization, Lists, Key Injectivity, & `RenameMap` -/

private theorem field_of_get_addrs {x_s x_n r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelModeled::get_addrs" [x_s, x_n] h r h' cs) :
    ∃ n_f : F, x_n = .field n_f := by
  cases Obs.«KernelModeled::get_addrs».obs ev with
  | n0 _ hv14 _ _ _ _ => exact ⟨0, hv14⟩
  | other _ _ _ _ _ _ v96 _ _ _ _ _ op117 _ _ _ _ _ =>
    cases x_n <;> simp [evalBinOp] at op117
    exact ⟨_, rfl⟩

private theorem get_addrs_go :
    ∀ (cnt : Nat) {n_f : F} {x_s r : SourceValue F} {bytes_in : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n_f = cnt →
      Ingress.Stream h bytes_in x_s →
      ObsFn W "KernelModeled::get_addrs" [x_s, .field n_f] h r h' cs →
      ∃ (as_ : List Bytes.Address) (bytes_out : List UInt8) (x_as x_s' : SourceValue F),
        r = .tuple [x_as, x_s'] ∧
        as_.length = cnt ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as_ x_as ∧
        Ingress.Stream h' bytes_out x_s' ∧
        Heap.Extends h h'
  | 0, n_f, x_s, r, bytes_in, h, h', cs, hcnt, hs, ev => by
    cases Obs.«KernelModeled::get_addrs».obs ev with
    | n0 m21 _ he19 hm29 he40 _ =>
      have ext : Heap.Extends h h' := he40 ▸ hm29 ▸ heap_extends_append h _
      refine ⟨[], bytes_in, .ptr (.enum addrListEnum) h.length, x_s, he19, rfl, ?_, hs.mono ext, ext⟩
      rw [he40, hm29]
      exact Lib.rep_store_nil h
    | other _ _ _ _ _ _ _ _ _ _ hne42 _ _ _ _ _ _ _ =>
      have hn0 : n_f = 0 := by rwa [ZMod.val_eq_zero] at hcnt
      exact absurd (congrArg Value.field hn0) hne42
  | cnt + 1, n_f, x_s, r, bytes_in, h, h', cs, hcnt, hs, ev => by
    cases Obs.«KernelModeled::get_addrs».obs ev with
    | n0 _ hv14 _ _ _ _ =>
      injection hv14 with hn0
      subst hn0
      simp at hcnt
    | other m47 cs57 x_a x_s2 m82 cs92 v96 x_rest x_s3 m138
        hne42 ev59 op117 ev94 he136 hm146 he173 _ =>
      have hn_ne : n_f ≠ 0 := fun e => hne42 (congrArg Value.field e)
      obtain rfl := Lib.sub_one_inv op117
      have hpred : ZMod.val (n_f - 1) = cnt := by
        have hv := Lib.val_sub_one hn_ne
        omega
      obtain ⟨a, rem, x_t, x_s2', _, htup1, ha_rep, hs_rem, ext1, _⟩ := get_address_spec hs ev59
      injection htup1 with hargs1
      injection hargs1 with hxa h1
      injection h1 with hxs2 _
      subst hxa hxs2
      obtain ⟨as_rest, bytes_out, x_as_rest, x_s_out, htup2, hlen_rest, hrest_rep, hs_out, ext2⟩ :=
        get_addrs_go cnt hpred hs_rem ev94
      injection htup2 with hargs2
      injection hargs2 with hxrest h2
      injection h2 with hxs3 _
      subst hxrest hxs3
      have ext3 : Heap.Extends m82 h' := he173 ▸ hm146 ▸ heap_extends_append m82 _
      refine ⟨a :: as_rest, bytes_out, .ptr (.enum addrListEnum) m82.length, x_s3,
        he136, by simp [hlen_rest], ?_, hs_out.mono ext3, ext1.trans (ext2.trans ext3)⟩
      rw [he173, hm146]
      exact Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
        (Bytes.repAddressRef_heapMono₂ addrTy ext2 ha_rep) hrest_rep

/-- **`KernelModeled::get_addrs`**: peels `n` addresses off an `Ingress.Stream`, returning a
`RepList addrListEnum` of length `ZMod.val n` and the remaining stream. -/
theorem get_addrs_spec {x_s x_n x_as x_s' : SourceValue F} {bytes_in : List UInt8}
    {h h' : Heap F} {cs : List (Call F)}
    (hs : Ingress.Stream h bytes_in x_s)
    (ev : ObsFn W "KernelModeled::get_addrs" [x_s, x_n] h (.tuple [x_as, x_s']) h' cs) :
    ∃ (n_f : F) (as_ : List Bytes.Address) (bytes_out : List UInt8),
      x_n = .field n_f ∧
      as_.length = ZMod.val n_f ∧
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as_ x_as ∧
      Ingress.Stream h' bytes_out x_s' ∧
      Heap.Extends h h' := by
  obtain ⟨n_f, rfl⟩ := field_of_get_addrs ev
  obtain ⟨as_, bytes_out, x_as', x_s'', htup, hlen, hrep, hs', ext⟩ :=
    get_addrs_go (ZMod.val n_f) rfl hs ev
  injection htup with hargs
  injection hargs with h1 h2
  injection h2 with h3 _
  subst h1 h3
  exact ⟨n_f, as_, bytes_out, rfl, hlen, hrep, hs', ext⟩

/-- **`Lists::length<&[Field; 32]>`** over `RepList addrListEnum`. -/
theorem addrList_length_spec {as_ : List Bytes.Address} {l r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hl : RepList addrListEnum (Bytes.RepAddressRef addrTy) h as_ l)
    (ev : ObsFn W Obs.Names.«Lists::length<&[Field; 32]>» [l] h r h' cs) :
    r = .field (as_.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [.ptr (.array .field 32)]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<&[Field; 32]>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      (Bytes.RepAddressRef addrTy) h as_ l := by
    rw [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

/-- **`Lists::concat<&[Field; 32]>`** over `RepList addrListEnum`. -/
theorem addrList_concat_spec {xs ys : List Bytes.Address} {a b r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ha : RepList addrListEnum (Bytes.RepAddressRef addrTy) h xs a)
    (hb : RepList addrListEnum (Bytes.RepAddressRef addrTy) h ys b)
    (ev : ObsFn W Obs.Names.«Lists::concat<&[Field; 32]>» [a, b] h r h' cs) :
    RepList addrListEnum (Bytes.RepAddressRef addrTy) h' (xs ++ ys) r := by
  have ev' : ObsFn W (Instance.mk "Lists::concat" [.ptr (.array .field 32)]).symbol
      [a, b] h r h' cs := by
    rw [Obs.Names.«Lists::concat<&[Field; 32]>».symbol]; exact ev
  have ha' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      (Bytes.RepAddressRef addrTy) h xs a := by
    rw [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]; exact ha
  have hb' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      (Bytes.RepAddressRef addrTy) h ys b := by
    rw [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]; exact hb
  have hout := Lib.Lists.concat_spec (Bytes.repAddressRef_heapMono₂ addrTy) ev' ha' hb'
  rwa [Obs.Names.«Lists::Node<&[Field; 32]>».symbol] at hout

theorem ixAddr_injective {a₁ a₂ : Bytes.Address} (h : ixAddr a₁ = ixAddr a₂) : a₁ = a₂ := by
  cases a₁ with
  | mk arr₁ sz₁ =>
    cases a₂ with
    | mk arr₂ sz₂ =>
      unfold ixAddr at h
      injection h with hb
      injection hb with ha
      subst ha
      rfl

theorem keyOf_injective {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {a₁ a₂ : _root_.Address} (h : keyOf t a₁ = keyOf t a₂) : a₁ = a₂ := by
  cases hq₁ : t.bound.find? (·.2 == a₁) with
  | some p =>
    have hk₁ : keyOf t a₁ = .role p.1 := by simp [keyOf, hq₁]
    have h₁ := addressOf_of_keyOf hwf hk₁
    have h₂ := addressOf_of_keyOf hwf (h.symm.trans hk₁)
    exact Option.some.inj (h₁.symm.trans h₂)
  | none =>
    cases hq₂ : t.bound.find? (·.2 == a₂) with
    | some q =>
      simp [keyOf, hq₁, hq₂] at h
    | none =>
      simp [keyOf, hq₁, hq₂] at h
      exact h

/-- Key-level parallel list renaming induced by `(srcKeys, dstKeys)`. -/
def renameKeyList (k : KKey) : List KKey → List KKey → KKey
  | s :: ss, d :: ds => if k = s then d else renameKeyList k ss ds
  | _, _ => k

theorem renameKeyList_eq_map_renameBytesAddr {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) :
    ∀ (srcAs dstAs : List Bytes.Address) (a : Bytes.Address),
      srcAs.length = dstAs.length →
      keyOf t (ixAddr (renameBytesAddr a srcAs dstAs)) =
        renameKeyList (keyOf t (ixAddr a))
          (srcAs.map fun b => keyOf t (ixAddr b))
          (dstAs.map fun b => keyOf t (ixAddr b))
  | [], [], a, _ => rfl
  | [], _ :: _, _, hlen => nomatch hlen
  | _ :: _, [], _, hlen => nomatch hlen
  | s :: ss, d :: ds, a, hlen => by
    simp only [renameBytesAddr, List.map_cons, renameKeyList]
    by_cases has : a = s
    · subst has
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · have hks : keyOf t (ixAddr a) ≠ keyOf t (ixAddr s) := fun hk =>
        has (ixAddr_injective (keyOf_injective hwf hk))
      rw [ite_eq_right has, ite_eq_right hks]
      exact renameKeyList_eq_map_renameBytesAddr hwf ss ds a (Nat.succ.inj hlen)

/-- Build `RenameMap (keyOf t) (keyOf t)` directly from equal-length `RepList`s of addresses. -/
theorem renameMap_of_lists {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {srcAs dstAs : List Bytes.Address} {src dst : SourceValue F} {h : Heap F}
    (hlen : srcAs.length = dstAs.length)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst) :
    RenameMap (keyOf t) (keyOf t)
      (fun k => renameKeyList k
        (srcAs.map fun b => keyOf t (ixAddr b))
        (dstAs.map fun b => keyOf t (ixAddr b)))
      h src dst :=
  ⟨srcAs, dstAs, hsrc, hdst, hlen, fun a =>
    renameKeyList_eq_map_renameBytesAddr hwf srcAs dstAs a hlen⟩

theorem renameKeyList_out (k : KKey) :
    ∀ (ks ds : List KKey), ks.contains k = false → renameKeyList k ks ds = k
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | s :: ss, d :: ds, h => by
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [renameKeyList, ite_eq_right h.1]
    exact renameKeyList_out k ss ds h.2

theorem renameKeyList_append_left {k : KKey} :
    ∀ {ks₁ ds₁ : List KKey} (ks₂ ds₂ : List KKey),
      ks₁.length = ds₁.length →
      k ∈ ks₁ →
      renameKeyList k (ks₁ ++ ks₂) (ds₁ ++ ds₂) = renameKeyList k ks₁ ds₁
  | [], [], _, _, _, hmem => nomatch hmem
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | s :: ss, d :: ds, ks₂, ds₂, hlen, hmem => by
    simp only [List.cons_append, renameKeyList]
    by_cases hks : k = s
    · rw [ite_eq_left hks, ite_eq_left hks]
    · rw [ite_eq_right hks, ite_eq_right hks]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact absurd rfl hks
      · exact renameKeyList_append_left ks₂ ds₂ (Nat.succ.inj hlen) hmem'

theorem renameKeyList_append_right {k : KKey} :
    ∀ {ks₁ ds₁ : List KKey} (ks₂ ds₂ : List KKey),
      ks₁.length = ds₁.length →
      k ∉ ks₁ →
      renameKeyList k (ks₁ ++ ks₂) (ds₁ ++ ds₂) = renameKeyList k ks₂ ds₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => nomatch hlen
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | s :: ss, d :: ds, ks₂, ds₂, hlen, hnin => by
    have hks : k ≠ s := fun he => hnin (he ▸ List.mem_cons_self)
    have hnin' : k ∉ ss := fun hm => hnin (List.mem_cons_of_mem s hm)
    simp only [List.cons_append, renameKeyList, ite_eq_right hks]
    exact renameKeyList_append_right ks₂ ds₂ (Nat.succ.inj hlen) hnin'

theorem renameKeyList_getElem_of_nodup :
    ∀ {ks ds : List KKey} {i : Nat} (hnd : ks.Nodup) (hlen : ks.length = ds.length)
      (hi : i < ks.length),
      renameKeyList ks[i] ks ds = ds[i]'(hlen ▸ hi)
  | [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, hlen, _ => nomatch hlen
  | s :: ss, d :: ds, 0, _, _, _ => by
    simp [renameKeyList]
  | s :: ss, d :: ds, i + 1, hnd, hlen, hi => by
    obtain ⟨hsin, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ss.length := Nat.lt_of_succ_lt_succ hi
    have hne : ss[i] ≠ s := fun he => hsin (he ▸ List.getElem_mem hi')
    simp only [List.getElem_cons_succ, renameKeyList, ite_eq_right hne]
    exact renameKeyList_getElem_of_nodup hnd' (Nat.succ.inj hlen) hi'

/-! ## Section 3: VM Specs for `check_const`, `check_advice_records`, `members_val`, & `check_recs` -/

/-- Inversion of `KernelCheck::check_const` on a safe `"Induct"` constant: the native route
(`block_is_modeled = 0`) or the modeled route (`block_is_modeled ≠ 0`, after which the arm also
runs `check_modeled_block`). -/
theorem check_const_ind_inv {rc nl ty np ni nct iblk iidx ap r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Induct" [nl, ty, np, ni, nct, .field 0, iblk, iidx], ap]
      h r h' calls) :
    ((∃ (v_sc v_sort : SourceValue F) (m_sc m_sort m_nil : Heap F) (cs_sc cs_sort : List (Call F)),
      ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h v_sc m_sc cs_sc ∧
      Heap.Extends m_sc m_nil ∧
      TypesRep (fun _ => .role .nat) zg m_nil 0
        (.ptr (.enum kexprListEnum) (m_nil.length - 1))) ∨ True) ∧
    ((∃ (m_bm1 m_bm2 : Heap F) (cs_bm : List (Call F)),
        Heap.Extends h m_bm1 ∧
        ObsFn W "KernelModeled::block_is_modeled" [iblk] m_bm1 (.field 0) m_bm2 cs_bm ∧
        (∀ x ∈ cs_bm, x ∈ calls)) ∨
      (∃ (m_bm1 m_bm2 : Heap F) (v_bm : SourceValue F) (cs_bm : List (Call F)),
        Heap.Extends h m_bm1 ∧
        ObsFn W "KernelModeled::block_is_modeled" [iblk] m_bm1 v_bm m_bm2 cs_bm ∧
        v_bm ≠ .field 0 ∧
        (∀ x ∈ cs_bm, x ∈ calls))) := by
  refine ⟨Or.inr trivial, ?_⟩
  match Obs.«KernelCheck::check_const».obs ev with
  | .Induct_n0 (x_ind_block := block) (m1470 := before) (m1492 := after)
      (cs1503 := children) (hv1240 := shape) (ev1505 := check) (hc1634 := events) .. =>
    have hb : iblk = block := by
      have hx := congrArg (fun xs : List (SourceValue F) => xs[6]?)
        (Value.construct.inj shape).2.2
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx
      exact hx
    subst block
    have hm : (⟨"KernelModeled::block_is_modeled", [iblk], before⟩ : Call F) ∈ calls := by
      rw [events]; simp
    exact Or.inl ⟨before, after, children, (ev.call_heap_bounds hm).1, check,
      fun cl hc => by rw [events]; simp [hc]⟩
  | .Induct_other_n0 (x_ind_block := block) (m1470 := before) (m1492 := after)
      (v1491 := result) (cs1503 := children) (hv1240 := shape) (ev1505 := check)
      (hne1635 := nonnative) (hc1974 := events) .. =>
    have hb : iblk = block := by
      have hx := congrArg (fun xs : List (SourceValue F) => xs[6]?)
        (Value.construct.inj shape).2.2
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx
      exact hx
    subst block
    have hm : (⟨"KernelModeled::block_is_modeled", [iblk], before⟩ : Call F) ∈ calls := by
      rw [events]; simp
    exact Or.inr ⟨before, after, result, children, (ev.call_heap_bounds hm).1, check,
      nonnative, fun cl hc => by rw [events]; simp [hc]⟩
  | .Induct_other_other (hv1240 := shape) (hne1975 := unsafeFlag) .. =>
    have hu := congrArg (fun xs : List (SourceValue F) => xs[5]?)
      (Value.construct.inj shape).2.2
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hu
    exact (unsafeFlag hu.symm).elim
  | .Axiom_n1 (hv37 := shape) .. | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) .. | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) .. | .Quot (hv1076 := shape) ..
  | .Ctor_n0_n0 (hv1989 := shape) .. | .Ctor_n0_other (hv1989 := shape) ..
  | .Ctor_other_n0 (hv1989 := shape) .. | .Ctor_other_other (hv1989 := shape) ..
  | .Rec_n0 (hv2727 := shape) .. | .Rec_other (hv2727 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)

/-- Inversion of `KernelModeled::check_modeled_block`: extracts `read_payload`, `get_address`, and
`KernelModeled::check_family`. -/
theorem check_modeled_block_inv {rc iblk r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::check_modeled_block" [rc, iblk] h r h' calls) :
    ∃ (v_pay x_rb w_rem : SourceValue F) (m_pay m_ga : Heap F)
      (cs_pay cs_ga cs_fam : List (Call F)),
      ObsFn W "KernelModeled::read_payload" [iblk] h v_pay m_pay cs_pay ∧
      ObsFn W "IxonDeserialize::get_address" [v_pay] m_pay (.tuple [x_rb, w_rem]) m_ga cs_ga ∧
      ObsFn W "KernelModeled::check_family" [rc, iblk, x_rb] m_ga r h' cs_fam ∧
      Heap.Extends h m_ga ∧
      (∀ x ∈ cs_fam, x ∈ calls) := by
  cases Obs.«KernelModeled::check_modeled_block».obs ev with
  | run m2 cs12 v15 m17 cs25 x_rb w39 cs53 ev27 ev14 ev55 hc80 =>
    subst hc80
    exact ⟨v15, x_rb, w39, m17, m2, cs25, cs12, cs53, ev27, ev14, ev55,
      (ObsFn.heap_extends ev27).trans (ObsFn.heap_extends ev14),
      fun x hx => by simp [hx]⟩

/-- Inversion of `KernelModeled::check_family`'s initial segment `Seg_krruczny` (stripping user
axioms from `rc` for `check_advice_records`). -/
theorem check_family_seg1_inv {rc iblk rblk v104 : SourceValue F} {h m105 : Heap F}
    {cs107 : List (Call F)}
    (sg : Obs.«KernelModeled::check_family».Seg_krruczny rc iblk rblk h v104 m105 cs107) :
    Heap.Extends h m105 := by
  cases sg with
  | Nil _ _ ev15 _ he33 _ => exact he33 ▸ ObsFn.heap_extends ev15
  | Node _ _ _ _ _ _ _ _ ev15 ev_wo _ =>
    exact (ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev_wo)

/-- When `rc` already has an empty user-axiom map (`RCAxiomsNil`), `check_family`'s initial
segment takes the `.Nil` arm and leaves `rc` and the heap unchanged. -/
theorem check_family_seg_nil_of_rc {rc iblk rblk v104 : SourceValue F} {h m105 : Heap F}
    {cs107 : List (Call F)} (hnil : RCAxiomsNil h rc)
    (sg : Obs.«KernelModeled::check_family».Seg_krruczny rc iblk rblk h v104 m105 cs107) :
    v104 = rc ∧ m105 = h := by
  cases sg with
  | Nil _ _ ev15 hr hm _ =>
    obtain ⟨_, hm0, _⟩ := role_ctx_axioms_nil hnil ev15
    exact ⟨hr, hm.trans hm0⟩
  | Node _ _ _ _ _ _ _ _ ev15 _ _ =>
    obtain ⟨hax, _, _⟩ := role_ctx_axioms_nil hnil ev15
    injection hax with _ htag _
    exact absurd htag (by decide)

/-- Assembly step oracle for `KernelModeled::check_advice_records`: given the current validated advice
prefix `(seenSet, c_cur)`, an unvisited advice address `a` (`addr_set_member(a, seen) = 0`), and
an observed `check_advice_record(rc, a, seen, wset)` sub-derivation, advances `c_cur` to `c_next`
via `ModelExtStep` and installs `a` as a `.defnInfo` in `c_next.env`. -/
def AdviceStepOracle (calls : List (Call F)) (blockNames : List KKey)
    (rc wset : SourceValue F) : Prop :=
  ∀ (c_cur : Ctx) (seenSet : Bytes.Address → Prop) (a : Bytes.Address)
    (x_a x_seen v89 : SourceValue F) (h₀ m55s m55 m90 : Heap F) (cs63 cs63w cs100 : List (Call F)),
    DeclStoreInv c_cur.env →
    AuxRootSynced c_cur.env →
    (∀ k ∈ blockNames, c_cur.env.find? k = none) →
    RCRep c_cur.t c_cur.lim h₀ rc →
    EnvFacts c_cur → LoadFacts c_cur → ExactGetCI c_cur → Good c_cur calls →
    Bytes.RepAddressRef addrTy h₀ a x_a →
    AddrMapAll addrMapEnum (fun _ k _ => seenSet k) h₀ x_seen →
    ObsFn W "KernelClaim::addr_set_member" [x_a, x_seen] h₀ (.field 0) m55s cs63 →
    ObsFn W "KernelClaim::addr_set_member" [x_a, wset] m55s (.field 0) m55 cs63w →
    ObsFn W "KernelModeled::check_advice_record" [rc, x_a, x_seen, wset] m55 v89 m90 cs100 →
    (∀ x ∈ cs63, x ∈ calls) →
    (∀ x ∈ cs63w, x ∈ calls) →
    (∀ x ∈ cs100, x ∈ calls) →
    ∃ c_next : Ctx,
      c_next.E = c_cur.E ∧ c_next.t = c_cur.t ∧ c_next.lim = c_cur.lim ∧
      ModelExtStep.{u} c_cur.env c_next.env ∧
      (∀ k ∈ blockNames, c_next.env.find? k = none) ∧
      EnvFacts c_next ∧ LoadFacts c_next ∧ ExactGetCI c_next ∧ Good c_next calls ∧
      ∃ cvm mval hint,
        c_next.env.find? (c_next.κ (ixAddr a)) = some (.defnInfo cvm mval hint)

/-- **`KernelModeled::check_advice_records`** refines an advice address list `advAs` from an
initial `(seenSet, c₀)` to `(fun b => seenSet b ∨ b ∈ advAs, c_adv)` via `AdviceStepOracle` and
`rbtree_map_insert_field_addrMapAll`. -/
theorem check_advice_records_spec {calls : List (Call F)} {blockNames : List KKey}
    {rc wset : SourceValue F}
    (horacle : AdviceStepOracle.{u} calls blockNames rc wset) :
    ∀ (advAs : List Bytes.Address) (seenSet : Bytes.Address → Prop) (c_cur : Ctx)
      {x_advice x_seen r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      DeclStoreInv c_cur.env →
      AuxRootSynced c_cur.env →
      (∀ k ∈ blockNames, c_cur.env.find? k = none) →
      (∀ b, seenSet b → ∃ cvm mval hint,
        c_cur.env.find? (c_cur.κ (ixAddr b)) = some (.defnInfo cvm mval hint)) →
      RCRep c_cur.t c_cur.lim h rc →
      EnvFacts c_cur → LoadFacts c_cur → ExactGetCI c_cur → Good c_cur calls →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs x_advice →
      AddrMapAll addrMapEnum (fun _ b _ => seenSet b) h x_seen →
      ObsFn W "KernelModeled::check_advice_records" [rc, x_advice, x_seen, wset] h r h' cs →
      (∀ x ∈ cs, x ∈ calls) →
      ∃ c_adv : Ctx,
        c_adv.E = c_cur.E ∧ c_adv.t = c_cur.t ∧ c_adv.lim = c_cur.lim ∧
        ModelExtStep.{u} c_cur.env c_adv.env ∧
        DeclStoreInv c_adv.env ∧ AuxRootSynced c_adv.env ∧
        (∀ k ∈ blockNames, c_adv.env.find? k = none) ∧
        EnvFacts c_adv ∧ LoadFacts c_adv ∧ ExactGetCI c_adv ∧ Good c_adv calls ∧
        AddrMapAll addrMapEnum (fun _ b _ => seenSet b ∨ b ∈ advAs) h' r ∧
        (∀ b, seenSet b ∨ b ∈ advAs → ∃ cvm mval hint,
          c_adv.env.find? (c_adv.κ (ixAddr b)) = some (.defnInfo cvm mval hint)) ∧
        Heap.Extends h h'
  | [], seenSet, c_cur, x_advice, x_seen, r, h, h', cs,
      hS, hAux, hfr, hdefs, _, hef, hlf, hex, hg, hadv_rep, hseen, ev, _ => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (he21 := he21) (he22 := he22) .. =>
      rw [he21, he22]
      refine ⟨c_cur, rfl, rfl, rfl, ModelExtStep.refl c_cur.env, hS, hAux, hfr,
        hef, hlf, hex, hg, ?_, ?_, Heap.Extends.refl h⟩
      · exact addrMapAll_mono_pred (Heap.Extends.refl h) (fun hp => Or.inl hp) hseen
      · intro b hb
        rcases hb with hs | hmem
        · exact hdefs b hs
        · exact nomatch hmem
    | .Cons (ld12 := ld12) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hadv_rep ld12
      cases he
  | a :: rest, seenSet, c_cur, x_advice, x_seen, r, h, h', cs,
      hS, hAux, hfr, hdefs, hrc, hef, hlf, hex, hg, hadv_rep, hseen, ev, hsub => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (ld12 := ld12) .. =>
      cases Lib.rep_nil_of_load hadv_rep ld12
    | .Cons (x_a := x_a) (m_cnmrgvie := m55s) (cs_jxqtckhn := cs63) (cs_eiizeeve := cs63w)
        (m_aiikskik := m55) (v89 := v89) (m90 := m90) (cs100 := cs100) (v143 := v143)
        (m160 := m160) (ld12 := ld12) (ev_mfihupbr := ev65) (heq_sefkntmx := heq88)
        (ev_xzbngsxs := ev65w) (heq_xyxoxrbw := heq88w) (ev102 := ev102) (ev170 := ev170)
        (ev140 := ev140) (hc201 := hc201) .. =>
      subst heq88 heq88w hc201
      obtain ⟨a', rest', heq_cons, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hadv_rep ld12
      injection heq_cons with ha_eq hrest_eq
      subst ha_eq hrest_eq
      obtain ⟨c_next, hE_eq, ht_eq, hlim_eq, hstep1, hfr1, hef1, hlf1, hex1, hg1,
          cvm_a, mval_a, hint_a, hdef_a⟩ :=
        horacle c_cur seenSet a x_a x_seen v89 h m55s m55 m90 cs63 cs63w cs100
          hS hAux hfr hrc hef hlf hex hg ha_rep hseen ev65 ev65w ev102
          (fun x hx => hsub x (by simp [hx]))
          (fun x hx => hsub x (by simp [hx]))
          (fun x hx => hsub x (by simp [hx]))
      have hS1 : DeclStoreInv c_next.env := hstep1.storeStep hS
      have hAux1 : AuxRootSynced c_next.env := hstep1.auxStep hAux
      have hκ_eq : c_next.κ = c_cur.κ := by simp [Ctx.κ, ht_eq]
      have ext_90 : Heap.Extends h m90 :=
        (ObsFn.heap_extends ev65).trans ((ObsFn.heap_extends ev65w).trans
          (ObsFn.heap_extends ev102))
      have ext_160 : Heap.Extends m90 m160 := ObsFn.heap_extends ev170
      have ext_h_160 : Heap.Extends h m160 := ext_90.trans ext_160
      have hseen1 : AddrMapAll addrMapEnum (fun _ b _ => seenSet b ∨ b = a) m160 v143 :=
        rbtree_map_insert_field_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_90 ha_rep)
          (addrSet_mono ext_90 hseen) ev170
      have hdefs1 : ∀ b, seenSet b ∨ b = a → ∃ cvm mval hint,
          c_next.env.find? (c_next.κ (ixAddr b)) = some (.defnInfo cvm mval hint) := by
        intro b hb
        rcases hb with hs | rfl
        · obtain ⟨cvm, mval, hint, hf⟩ := hdefs b hs
          rw [hκ_eq]
          exact ⟨cvm, mval, hint, hstep1.ext.find hf⟩
        · exact ⟨cvm_a, mval_a, hint_a, hdef_a⟩
      have hrc1 : RCRep c_next.t c_next.lim m160 rc := by
        rw [ht_eq, hlim_eq]; exact hrc.mono ext_h_160
      obtain ⟨c_adv, hE2, ht2, hlim2, hstep2, hS2, hAux2, hfr2, hef2, hlf2, hex2, hg2,
          haset_out, hdefs_out, ext_rest⟩ :=
        check_advice_records_spec horacle rest (fun b => seenSet b ∨ b = a) c_next
          hS1 hAux1 hfr1 hdefs1 hrc1 hef1 hlf1 hex1 hg1
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_160 hrest_rep)
          hseen1 ev140 (fun x hx => hsub x (by simp [hx]))
      refine ⟨c_adv, hE2.trans hE_eq, ht2.trans ht_eq, hlim2.trans hlim_eq,
        hstep1.trans hstep2, hS2, hAux2, hfr2, hef2, hlf2, hex2, hg2, ?_, ?_,
        ext_h_160.trans ext_rest⟩
      · refine addrMapAll_mono_pred (Heap.Extends.refl h') ?_ haset_out
        intro _ b _ hb
        rcases hb with (hs | rfl) | hrm
        · exact Or.inl hs
        · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem a hrm)
      · intro b hb
        refine hdefs_out b ?_
        rcases hb with hs | hmem
        · exact Or.inl (Or.inl hs)
        · rcases List.mem_cons.mp hmem with rfl | hrm
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr hrm

/-- **`KernelModeled::ci_lvls_type`** extracts `ValRepExact` on `(nl, ty)` from `CIRepExact`. -/
theorem ci_lvls_type_spec {κ : _root_.Address → KKey} {v_ci x_nl x_ty : SourceValue F}
    {ci : ConstantInfo .anon} {h h' : Heap F} {cs : List (Call F)}
    (hci : CIRepExact κ h v_ci ci)
    (ev : ObsFn W "KernelModeled::ci_lvls_type" [v_ci] h (.tuple [x_nl, x_ty]) h' cs) :
    ValRepExact κ h x_nl x_ty ci.toConstantVal ∧ h' = h := by
  cases Obs.«KernelModeled::ci_lvls_type».obs ev with
  | Induct nl' ty' _ _ _ _ _ _ hv15 he67 he82 _ =>
    injection he67 with hargs; injection hargs with h1 h2; injection h2 with h3 _
    subst h1 h3 he82
    cases hci with
    | induct hv _ _ =>
      injection hv15 with _ _ hc; injection hc with hnl h4; injection h4 with hty _
      subst hnl hty; exact ⟨hv, rfl⟩
    | _ => injection hv15 with _ htag _; exact absurd htag (by decide)
  | Ctor nl' ty' _ _ _ _ _ _ _ hv89 he141 he156 _ =>
    injection he141 with hargs; injection hargs with h1 h2; injection h2 with h3 _
    subst h1 h3 he156
    cases hci with
    | ctor hv _ _ _ _ =>
      injection hv89 with _ _ hc; injection hc with hnl h4; injection h4 with hty _
      subst hnl hty; exact ⟨hv, rfl⟩
    | _ => injection hv89 with _ htag _; exact absurd htag (by decide)
  | Rec nl' ty' _ _ _ _ _ _ _ _ _ _ _ hv163 he233 he248 _ =>
    injection he233 with hargs; injection hargs with h1 h2; injection h2 with h3 _
    subst h1 h3 he248
    cases hci with
    | recr hv _ _ _ _ _ _ _ _ _ _ =>
      injection hv163 with _ _ hc; injection hc with hnl h4; injection h4 with hty _
      subst hnl hty; exact ⟨hv, rfl⟩
    | _ => injection hv163 with _ htag _; exact absurd htag (by decide)

/-- **`KernelModeled::member_val`** verifies that `a_md` is in `advSet`, loads `ci_m` at `a_m`,
loads a `.defnInfo cvm_f mval_f hint_f` at `a_md` in `c_adv.env`, and checks syntactic equality of
their level-parameter counts and `f_id`-renamed positional types. -/
theorem member_val_spec (hroles : RolesSpec) {c_adv : Ctx}
    (hwf : c_adv.t.wf = true) (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    {a_m a_md : Bytes.Address} {ci_m : ConstantInfo .anon}
    {x_member x_model x_src x_dst x_aset x_later r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hg_adv : Good c_adv calls)
    (hm_rep : Bytes.RepAddressRef addrTy h a_m x_member)
    (hmd_rep : Bytes.RepAddressRef addrTy h a_md x_model)
    (hf_key : c_adv.κ (ixAddr a_md) = f_id ci_m.name)
    (hnp_m : NoProjIn blockNames ci_m.toConstantVal.type = true)
    (haset : AddrMapAll addrMapEnum (fun _ k _ => advSet k) h x_aset)
    (hren : RenameMap c_adv.κ c_adv.κ f_id h x_src x_dst)
    (hmem_ci : ∀ {p_ci : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
      Heap.Extends h h₁ →
      (∀ x ∈ cs_ci, x ∈ calls) →
      Bytes.RepAddressRef addrTy h₁ a_m x_member →
      ObsFn W "Ingress::get_ci" [x_member] h₁ p_ci h₂ cs_ci →
      CIPtrRepExact c_adv.κ h₂ p_ci ci_m)
    (ev : ObsFn W "KernelModeled::member_val"
      [x_member, x_model, x_src, x_dst, x_aset, x_later] h r h' calls) :
    advSet a_md ∧
    ci_m.toConstantVal.levelParams.Perm (List.range ci_m.toConstantVal.levelParams.length) ∧
    (∃ cvm_f mval_f hint_f,
      c_adv.env.find? (f_id ci_m.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
      cvm_f.levelParams = List.range ci_m.toConstantVal.levelParams.length ∧
      cvm_f.type =
        (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type).renameConsts f_id) ∧
    Heap.Extends h h' := by
  cases Obs.«KernelModeled::member_val».obs ev with
  | run v12 m15 cs23 m50 cs60 v63 m65 p70 cs76 x_nl x_ty vL mL csL m101 p109 cs115
      x_nlm x_mty w132 w133 w134 v199 m202 cs210 v213 m216 cs224
      ev25 heq48 ev78 ld72 ev62 evL _ ev117 ld111 heq187 ev226 ev212 heq264 _ he268 hc269 =>
    subst heq48 heq264 he268 hc269
    have hadv_md : advSet a_md :=
      addr_set_member_one hroles hwf hmd_rep haset ev25
    have e25 := ObsFn.heap_extends ev25
    have hptr_m : CIPtrRepExact c_adv.κ m65 p70 ci_m :=
      hmem_ci e25 (fun x hx => by simp [hx])
        (Bytes.repAddressRef_heapMono₂ addrTy e25 hm_rep) ev78
    obtain ⟨v_m, hld_m, hci_m⟩ := hptr_m
    rw [ld72] at hld_m; injection hld_m with hv_m; subst hv_m
    obtain ⟨hval_m, hm50_eq⟩ := ci_lvls_type_spec hci_m ev62
    rw [hm50_eq] at evL
    obtain ⟨hnl_m, hlps_lt_m, hperm_m, hty_m_rep⟩ := hval_m
    have e78 := ObsFn.heap_extends ev78
    have e_h_65 : Heap.Extends h m65 := e25.trans e78
    have eL : Heap.Extends m65 mL := ObsFn.heap_extends evL
    have e_h_L : Heap.Extends h mL := e_h_65.trans eL
    have hnot_rq : ∀ tag xs, (tag = "Rec" ∨ tag = "Quot") →
        loadValue m101 p109 ≠ .ok (.construct kciEnum tag xs) := by
      intro tag xs htag hld_bad
      rw [ld111] at hld_bad
      injection hld_bad with hcon
      injection hcon with _ htag_eq _
      rcases htag with rfl | rfl <;> exact absurd htag_eq (by decide)
    obtain ⟨ci_md, hfind_md, hnr_md, _, hptr_md⟩ :=
      hexact_adv a_md x_model p109 mL m101 cs115 ev117
        (hg_adv.sub fun x hx => by simp [hx])
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_L hmd_rep) hnot_rq
    obtain ⟨v_md, hld_md, hci_md⟩ := hptr_md
    rw [ld111] at hld_md; injection hld_md with hv_md
    cases hci_md with
    | @defn nl_d ty_d _ _ _ cvm_f mval_f hint_f hval_md _ =>
      injection hv_md with _ _ hdef_args
      injection hdef_args with h1_d h2_d
      injection h2_d with h3_d _
      subst h1_d h3_d
      have hlps_md_range : cvm_f.levelParams = List.range cvm_f.levelParams.length :=
        hnr_md rfl
      obtain ⟨hnl_md, hlps_lt_md, _, hty_md_rep⟩ := hval_md
      have hlen_eq : cvm_f.levelParams.length = ci_m.toConstantVal.levelParams.length := by
        have hfeq : (ci_m.toConstantVal.levelParams.length : F) =
            (cvm_f.levelParams.length : F) := by
          have h1 := hnl_m.symm.trans (heq187.trans hnl_md)
          injection h1
        have hv1 : ZMod.val (ci_m.toConstantVal.levelParams.length : F) =
            ci_m.toConstantVal.levelParams.length :=
          SubstAux.val_natCast (Nat.lt_trans hlps_lt_m (by decide))
        have hv2 : ZMod.val (cvm_f.levelParams.length : F) = cvm_f.levelParams.length :=
          SubstAux.val_natCast (Nat.lt_trans hlps_lt_md (by decide))
        rw [← hv2, ← hfeq, hv1]
      have hlps_f : cvm_f.levelParams = List.range ci_m.toConstantVal.levelParams.length := by
        rw [hlps_md_range, hlen_eq]
      have hpos_md : posOf cvm_f.levelParams cvm_f.type = cvm_f.type := by
        conv => lhs; rw [hlps_md_range]
        exact posOf_range cvm_f.levelParams.length cvm_f.type
      rw [hpos_md] at hty_md_rep
      have e117 := ObsFn.heap_extends ev117
      have e_h_101 : Heap.Extends h m101 := e_h_L.trans e117
      have hren_101 : RenameMap c_adv.κ c_adv.κ f_id m101 x_src x_dst := by
        obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
        exact ⟨sAs, dAs,
          RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_101 hs,
          RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_101 hd, hl, hm⟩
      have hren_tm : TmExact c_adv.κ 0 zg m216 0
          (renameAll f_id (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type)) v213 :=
        rename_exact ev226 ((hty_m_rep 0 zg).mono (eL.trans e117)) hren_101
      have e226 := ObsFn.heap_extends ev226
      have hstruct_eq :
          renameAll f_id (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type) =
            cvm_f.type :=
        kexpr_struct_eq_one hren_tm ((hty_md_rep 0 zg).mono e226) ev212
      have hnp_pos :
          NoProjIn blockNames
            (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type) = true := by
        unfold posOf
        rw [noProjIn_instantiateLevelParams]
        exact hnp_m
      have hren_eq :
          renameAll f_id (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type) =
            (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type).renameConsts f_id :=
        renameAll_eq_renameConsts_of_noProjIn hf_out hnp_pos
      rw [hf_key] at hfind_md
      have e212 := ObsFn.heap_extends ev212
      exact ⟨hadv_md, hperm_m,
        ⟨cvm_f, mval_f, hint_f, hfind_md, hlps_f, hstruct_eq.symm.trans hren_eq⟩,
        e_h_101.trans (e226.trans e212)⟩
    | _ =>
      injection hv_md with _ htag _
      exact absurd htag (by decide)

/-- **`KernelModeled::members_val`** lifts `member_val_spec` pairwise across equal-length lists of
member addresses, model addresses, and member `ConstantInfo`s. -/
theorem members_val_spec (hroles : RolesSpec) {c_adv : Ctx}
    (hwf : c_adv.t.wf = true) (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k) {x_later : SourceValue F} :
    ∀ (memAs mdAs : List Bytes.Address) (cis : List (ConstantInfo .anon))
      {x_members x_models x_src x_dst x_aset r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      (hlen1 : memAs.length = mdAs.length) →
      (hlen2 : memAs.length = cis.length) →
      Good c_adv calls →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h memAs x_members →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h mdAs x_models →
      (∀ i (hi : i < memAs.length),
        c_adv.κ (ixAddr (mdAs[i]'(by omega))) = f_id (cis[i]'(by omega)).name ∧
        NoProjIn blockNames (cis[i]'(by omega)).toConstantVal.type = true ∧
        ∀ {p_ci : SourceValue F} {x_m : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
          Heap.Extends h h₁ →
          (∀ x ∈ cs_ci, x ∈ calls) →
          Bytes.RepAddressRef addrTy h₁ memAs[i] x_m →
          ObsFn W "Ingress::get_ci" [x_m] h₁ p_ci h₂ cs_ci →
          CIPtrRepExact c_adv.κ h₂ p_ci (cis[i]'(by omega))) →
      AddrMapAll addrMapEnum (fun _ k _ => advSet k) h x_aset →
      RenameMap c_adv.κ c_adv.κ f_id h x_src x_dst →
      ObsFn W "KernelModeled::members_val"
        [x_members, x_models, x_src, x_dst, x_aset, x_later] h r h' calls →
      (∀ ci ∈ cis,
        ci.toConstantVal.levelParams.Perm (List.range ci.toConstantVal.levelParams.length) ∧
        ∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id ci.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range ci.toConstantVal.levelParams.length ∧
          cvm_f.type =
            (posOf ci.toConstantVal.levelParams ci.toConstantVal.type).renameConsts f_id) ∧
      Heap.Extends h h'
  | [], [], [], _, _, _, _, _, _, h, h', calls, _, _, _, hmem_rep, _, _, _, _, ev => by
    cases Obs.«KernelModeled::members_val».obs ev with
    | Nil _ _ he23 _ =>
      rw [he23]
      exact ⟨(fun _ hm => nomatch hm), Heap.Extends.refl h⟩
    | Cons _ _ _ _ _ _ _ _ ld12 _ _ _ _ =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hmem_rep ld12
      cases he
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, hlen1, _, _, _, _, _, _, _, _ => nomatch hlen1
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hlen1, _, _, _, _, _, _, _, _ => nomatch hlen1
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, hlen2, _, _, _, _, _, _, _ => nomatch hlen2
  | a_m :: memRest, a_md :: mdRest, ci_m :: ciRest,
      x_members, x_models, x_src, x_dst, x_aset, r, h, h', calls,
      hlen1, hlen2, hg_adv, hmem_rep, hmd_rep, hidx, haset, hren, ev => by
    cases Obs.«KernelModeled::members_val».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hmem_rep ld12
    | Cons x_m x_rest x_md x_mrest v67 m68 cs78 cs124 ld12 ld52 ev80 ev126 hc167 =>
      subst hc167
      obtain ⟨a_m', memRest', hm_eq, hm_head, hm_tail⟩ := Lib.rep_cons_of_load hmem_rep ld12
      obtain ⟨a_md', mdRest', hmd_eq, hmd_head, hmd_tail⟩ := Lib.rep_cons_of_load hmd_rep ld52
      injection hm_eq with h1 h2; subst h1 h2
      injection hmd_eq with h1 h2; subst h1 h2
      obtain ⟨hf0, hnp0, hci0⟩ := hidx 0 (Nat.zero_lt_succ _)
      obtain ⟨_, hperm0, hdef0, ext68⟩ :=
        member_val_spec hroles hwf hexact_adv hf_out
          (hg_adv.sub fun x hx => by simp [hx])
          hm_head hmd_head hf0 hnp0 haset hren
          (fun ext1 hsub1 hrep1 ev1 =>
            hci0 ext1 (fun x hx => by simp [hsub1 x hx]) hrep1 ev1)
          ev80
      have hren68 : RenameMap c_adv.κ c_adv.κ f_id m68 x_src x_dst := by
        obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
        exact ⟨sAs, dAs,
          RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext68 hs,
          RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext68 hd, hl, hm⟩
      obtain ⟨hrest_all, ext_rest⟩ :=
        members_val_spec hroles hwf hexact_adv hf_out memRest mdRest ciRest
          (Nat.succ.inj hlen1) (Nat.succ.inj hlen2)
          (hg_adv.sub fun x hx => by simp [hx])
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext68 hm_tail)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext68 hmd_tail)
          (fun i hi => by
            obtain ⟨hfi, hnpi, hcii⟩ := hidx (i + 1) (Nat.succ_lt_succ hi)
            exact ⟨hfi, hnpi, fun ext1 hsub1 hrep1 ev1 =>
              hcii (ext68.trans ext1) (fun x hx => by simp [hsub1 x hx]) hrep1 ev1⟩)
          (addrSet_mono ext68 haset)
          hren68 ev126
      refine ⟨?_, ext68.trans ext_rest⟩
      intro ci hci
      rcases List.mem_cons.mp hci with rfl | htl
      · exact ⟨hperm0, hdef0⟩
      · exact hrest_all ci htl

private theorem rulesRepExact_noLet {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List LevelParam} {v : SourceValue F} {rls : List (RecRule .anon)} :
    ∀ {j : Nat}, RulesRepExact κ h ps j v rls → ∀ r ∈ rls, noLetExpr (posOf ps r.rhs) = true
  | _, .nil _, _, hr => nomatch hr
  | _, .cons _ ⟨_, _, _, htm⟩ htail, r, hr => by
    rcases List.mem_cons.mp hr with rfl | htl
    · exact htm.noLet
    · exact rulesRepExact_noLet htail r htl

/-- Raw recursor entry prior to running `check_recs` (carrying the member address, model address,
and raw `ConstantInfo.recInfo cv mI rP rawRules`). -/
structure RawRecEntry where
  a_rec : Bytes.Address
  a_rm : Bytes.Address
  cv : ConstantVal .anon
  mI : Nat
  rP : Nat
  rawRules : List (RecRule .anon)

def RawRecEntry.prov_r (e : RawRecEntry) : ConstantInfo .anon :=
  .recInfo e.cv e.mI e.rP []

def RawRecEntry.prov_p (e : RawRecEntry) : ConstantInfo .anon :=
  .recInfo (posCV e.cv) e.mI e.rP []

def RawRecEntry.toCI (e : RawRecEntry) : ConstantInfo .anon :=
  .recInfo e.cv e.mI e.rP e.rawRules

private theorem mem_tail_step {α : Type _} {a b : List α} {c x : α} (h : x ∈ b) :
    x ∈ a ++ (c :: b) :=
  List.mem_append_right a (List.mem_cons_of_mem c h)

private theorem mem_head_step {α : Type _} {a b : List α} {x : α} (h : x ∈ a) :
    x ∈ a ++ b :=
  List.mem_append_left b h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-! ## Section 4: `ModeledFamilyBridge`, `ModeledBlockWitness` Construction, & `modeledIndDecl_step` -/

private theorem storedAs_checked_r {find? : KKey → Option (ConstantInfo .anon)}
    {w : RecInstallEntry} {ci₀ : ConstantInfo .anon}
    (hs : IxVM.Consistency.StoredAs (.recInfo w.cv w.mI w.rP w.rawRules) ci₀) :
    IxVM.Consistency.StoredAs (w.checked_r find?) ci₀ := by
  cases ci₀ with
  | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _
  | indInfo _ _ | ctorInfo _ _ _ | projInfo _ => cases hs.2
  | recInfo cv₀ mI₀ rP₀ rules₀ =>
    obtain ⟨hval, hmI, hrP, hrules⟩ := hs
    refine ⟨hval, hmI, hrP, ?_⟩
    dsimp only [RecInstallEntry.checked_r, RecInstallEntry.rules_r]
    clear hval hmI hrP
    generalize w.rawRules = rls at hrules ⊢
    induction hrules with
    | nil => exact .nil
    | cons hhd _ ih =>
      exact .cons hhd ih

private theorem envExt_pushList_shared :
    ∀ (cs : List (ConstantInfo .anon)) {E₁ E₂ : Env .anon},
      EnvExt E₁ E₂ →
      (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, E₁.find? c.name = none) →
      (∀ c ∈ cs, E₂.find? c.name = none) →
      (∀ c ∈ cs, ∀ T, c.name ≠ projTableName T) →
      (∀ c ∈ cs, (∀ cv caps, c ≠ .indInfo cv caps) ∨
        (E₁.find? (projTableName c.name) = none ∧ E₂.find? (projTableName c.name) = none)) →
      (∀ k ci, (pushList cs E₁).find? k = some ci → (pushList cs E₂).find? k = some ci) ∧
      EnvExt (pushList cs E₁) (pushList cs E₂)
  | [], _, _, hext, _, _, _, _, _ => ⟨fun _ _ hf => hext.find hf, hext⟩
  | c :: rest, E₁, E₂, hext, hnd, hfr₁, hfr₂, hnpt, hpt => by
    obtain ⟨hcnin, hnd'⟩ := List.nodup_cons.mp hnd
    have hc_ne_rest : ∀ c' ∈ rest, c.name ≠ c'.name :=
      fun c' hc' heq => hcnin (List.mem_map.mpr ⟨c', hc', heq.symm⟩)
    have hext₁ : EnvExt ⟨c :: E₁.consts⟩ ⟨c :: E₂.consts⟩ := by
      refine { find := ?_, tables := ?_ }
      · intro k ci hf
        rw [Env.find?_cons] at hf ⊢
        by_cases hk : c.name = k
        · rw [ite_eq_left hk] at hf ⊢; exact hf
        · rw [ite_eq_right hk] at hf ⊢; exact hext.find hf
      · intro T cv caps hf
        have hne : c.name ≠ projTableName T := hnpt c List.mem_cons_self T
        rw [EnvExt.find?_cons_ne hne, EnvExt.find?_cons_ne hne]
        rw [Env.find?_cons] at hf
        by_cases hk : c.name = T
        · rw [ite_eq_left hk] at hf
          injection hf with hc_ind
          rcases hpt c List.mem_cons_self with hno_ind | ⟨h1, h2⟩
          · exact absurd hc_ind (hno_ind cv caps)
          · rw [← hk, h1, h2]
        · rw [ite_eq_right hk] at hf
          exact hext.tables hf
    refine envExt_pushList_shared rest hext₁ hnd' ?_ ?_
      (fun c' hc' => hnpt c' (List.mem_cons_of_mem c hc')) ?_
    · intro c' hc'
      rw [EnvExt.find?_cons_ne (hc_ne_rest c' hc')]
      exact hfr₁ c' (List.mem_cons_of_mem c hc')
    · intro c' hc'
      rw [EnvExt.find?_cons_ne (hc_ne_rest c' hc')]
      exact hfr₂ c' (List.mem_cons_of_mem c hc')
    · intro c' hc'
      rcases hpt c' (List.mem_cons_of_mem c hc') with hno_ind | ⟨h1, h2⟩
      · exact Or.inl hno_ind
      · have hne' : c.name ≠ projTableName c'.name := hnpt c List.mem_cons_self c'.name
        exact Or.inr ⟨by rw [EnvExt.find?_cons_ne hne']; exact h1,
          by rw [EnvExt.find?_cons_ne hne']; exact h2⟩

private theorem envExt_pushList_fresh_base :
    ∀ (cs : List (ConstantInfo .anon)) {E : Env .anon},
      (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, E.find? c.name = none) →
      (∀ c ∈ cs, ∀ T, c.name ≠ projTableName T) →
      EnvExt E (pushList cs E)
  | [], E, _, _, _ => EnvExt.refl E
  | c :: rest, E, hnd, hfr, hnpt => by
    obtain ⟨hcnin, hnd'⟩ := List.nodup_cons.mp hnd
    have hext₁ : EnvExt E ⟨c :: E.consts⟩ :=
      envExt_cons_fresh (hfr c List.mem_cons_self) (hnpt c List.mem_cons_self)
    have hfr' : ∀ c' ∈ rest, (⟨c :: E.consts⟩ : Env .anon).find? c'.name = none := by
      intro c' hc'
      have hne : c.name ≠ c'.name :=
        fun heq => hcnin (List.mem_map.mpr ⟨c', hc', heq.symm⟩)
      rw [EnvExt.find?_cons_ne hne]
      exact hfr c' (List.mem_cons_of_mem c hc')
    exact hext₁.trans
      (envExt_pushList_fresh_base rest hnd' hfr' fun c' hc' => hnpt c' (List.mem_cons_of_mem c hc'))

private theorem findProj_pushList_base :
    ∀ (cs : List (ConstantInfo .anon)) (E : Env .anon) (sn : KKey) (i : Nat),
      (∀ c ∈ cs, isBaseKey c.name = true) →
      (pushList cs E).findProj? sn i = E.findProj? sn i
  | [], _, _, _, _ => rfl
  | c :: rest, E, sn, i, hbase => by
    dsimp only [pushList]
    rw [findProj_pushList_base rest ⟨c :: E.consts⟩ sn i
      (fun c' hc' => hbase c' (List.mem_cons_of_mem c hc'))]
    unfold Env.findProj?
    rw [EnvExt.find?_cons_ne (ne_projTableName_of_isBaseKey (hbase c List.mem_cons_self))]

private theorem constsResolve_congr_isSome {E₁ E₂ : Env .anon}
    (hsome : ∀ k, (E₁.find? k).isSome = true → (E₂.find? k).isSome = true) :
    ∀ e : KExpr, e.constsResolve E₁ = true → e.constsResolve E₂ = true
  | .bvar _ | .sort _ => fun _ => rfl
  | .const n _ => fun h => hsome n h
  | .lit (.natVal _) => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hsome _ h.1.1, hsome _ h.1.2⟩, hsome _ h.2⟩
  | .lit (.strVal _) => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsome _ h.1.1.1.1.1.1.1.1.1, hsome _ h.1.1.1.1.1.1.1.1.2⟩,
      hsome _ h.1.1.1.1.1.1.1.2⟩, hsome _ h.1.1.1.1.1.1.2⟩, hsome _ h.1.1.1.1.1.2⟩,
      hsome _ h.1.1.1.1.2⟩, hsome _ h.1.1.1.2⟩, hsome _ h.1.1.2⟩, hsome _ h.1.2⟩, hsome _ h.2⟩
  | .fvar _ ty => constsResolve_congr_isSome hsome ty
  | .app f a => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_congr_isSome hsome f h.1, constsResolve_congr_isSome hsome a h.2⟩
  | .lam ty b _ | .forallE ty b _ => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_congr_isSome hsome ty h.1, constsResolve_congr_isSome hsome b h.2⟩
  | .letE ty v b _ => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨constsResolve_congr_isSome hsome ty h.1.1,
      constsResolve_congr_isSome hsome v h.1.2⟩,
      constsResolve_congr_isSome hsome b h.2⟩
  | .proj s _ sub => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hsome s h.1, constsResolve_congr_isSome hsome sub h.2⟩

private theorem isSome_pushList_posCI_iff :
    ∀ (cs : List (ConstantInfo .anon)) (E : Env .anon) (k : KKey),
      (∀ c ∈ cs, (posCI c).name = c.name) →
      ((pushList (cs.map posCI) E).find? k).isSome = ((pushList cs E).find? k).isSome
  | [], _, _, _ => rfl
  | c :: rest, E, k, hnm => by
    simp only [List.map_cons, pushList]
    have hrec := isSome_pushList_posCI_iff rest ⟨c :: E.consts⟩ k
      (fun c' hc' => hnm c' (List.mem_cons_of_mem c hc'))
    have hstep : ∀ (rs : List (ConstantInfo .anon)) (E₁ E₂ : Env .anon),
        (∀ x, (E₁.find? x).isSome = (E₂.find? x).isSome) →
        ((pushList rs E₁).find? k).isSome = ((pushList rs E₂).find? k).isSome := by
      intro rs
      induction rs with
      | nil => intro E₁ E₂ heq; exact heq k
      | cons r rt ih =>
        intro E₁ E₂ heq
        exact ih ⟨r :: E₁.consts⟩ ⟨r :: E₂.consts⟩ fun x => by
          rw [Env.find?_cons, Env.find?_cons]
          by_cases hx : r.name = x
          · rw [ite_eq_left hx, ite_eq_left hx]
          · rw [ite_eq_right hx, ite_eq_right hx]; exact heq x
    refine (hstep (rest.map posCI) ⟨posCI c :: E.consts⟩ ⟨c :: E.consts⟩ ?_).trans hrec
    intro x
    rw [Env.find?_cons, Env.find?_cons, hnm c List.mem_cons_self]
    by_cases hx : c.name = x
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]

private theorem isSome_pushList_prov_iff :
    ∀ (ws : List RecInstallEntry) (E₁ E₂ : Env .anon) (k : KKey),
      (∀ x, (E₁.find? x).isSome = (E₂.find? x).isSome) →
      ((pushList (ws.map (·.prov_p)) E₁).find? k).isSome =
        ((pushList (ws.map (·.prov_r)) E₂).find? k).isSome
  | [], _, _, k, heq => heq k
  | w :: rest, E₁, E₂, k, heq => by
    simp only [List.map_cons, pushList]
    refine isSome_pushList_prov_iff rest ⟨w.prov_p :: E₁.consts⟩ ⟨w.prov_r :: E₂.consts⟩ k ?_
    intro x
    rw [Env.find?_cons, Env.find?_cons]
    have hnm : w.prov_p.name = w.prov_r.name := rfl
    rw [hnm]
    by_cases hx : w.prov_r.name = x
    · rw [ite_eq_left hx, ite_eq_left hx]; rfl
    · rw [ite_eq_right hx, ite_eq_right hx]; exact heq x

private theorem build_nonRecChain {c_adv : Ctx} (hS_adv : DeclStoreInv c_adv.env)
    {f_id : KKey → KKey} :
    ∀ (nonrecs : List (ConstantInfo .anon)) (E_r E_p₀ : Env .anon),
      (nonrecs.map (·.name)).Nodup →
      (∀ c ∈ nonrecs, E_r.find? c.name = none) →
      (∀ c ∈ nonrecs, E_p₀.find? c.name = none) →
      (∀ c ∈ nonrecs,
        isBaseKey c.name = true ∧
        Ix.Kernel.reservedBasisNames.contains c.name = false ∧
        ((∃ cv, c = .indInfo cv {}) ∨ ∃ cv nP nF, c = .ctorInfo cv nP nF) ∧
        c.toConstantVal.levelParams.Perm (List.range c.toConstantVal.levelParams.length) ∧
        (∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id c.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          E_p₀.find? (f_id c.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range c.toConstantVal.levelParams.length ∧
          cvm_f.type = (posOf c.toConstantVal.levelParams c.toConstantVal.type).renameConsts f_id)) →
      (∀ pre suff c, nonrecs = pre ++ c :: suff →
        c.toConstantVal.type.constsResolve (pushList pre E_r) = true) →
      NonRecChain E_r E_p₀ f_id nonrecs
  | [], _, _, _, _, _, _, _ => trivial
  | c :: rest, E_r, E_p₀, hnd, hfr_r, hfr_p, hinfo, hcr => by
    obtain ⟨hcnin, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hbase, hnres, hknd, hperm, cvm_f, mval_f, hint_f,
        hf_adv, hf_p, hlps_f, hty_f⟩ := hinfo c List.mem_cons_self
    have hname_p : (posCI c).name = c.name := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hpos_ty_eq :
        (posCI c).toConstantVal.type = posOf c.toConstantVal.levelParams c.toConstantVal.type := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hmem_f : ConstantInfo.defnInfo cvm_f mval_f hint_f ∈ c_adv.env.consts :=
      Ix.Kernel.Semantics.Env.find?_mem hf_adv
    have hwf_f := hS_adv.store.wf _ hmem_f
    have htf : c.toConstantVal.type.hasFvar = false := by
      have h1 : ((posOf c.toConstantVal.levelParams c.toConstantVal.type).renameConsts f_id).hasFvar =
          false := hty_f ▸ hwf_f.1
      unfold posOf at h1
      rwa [hasFvar_renameConsts, hasFvar_instantiateLevelParams] at h1
    have htp : c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true := by
      have h1 :
          ((posOf c.toConstantVal.levelParams c.toConstantVal.type).renameConsts f_id).allLevelParamsDefined
            (List.range c.toConstantVal.levelParams.length) = true :=
        hlps_f ▸ hty_f ▸ hwf_f.2.1
      rw [allLevelParamsDefined_renameConsts] at h1
      exact allLevelParamsDefined_of_posOf_perm hperm h1
    have htb : c.toConstantVal.type.looseBVarsBounded 0 = true := by
      have h1 :
          ((posOf c.toConstantVal.levelParams c.toConstantVal.type).renameConsts f_id).looseBVarsBounded 0 =
            true := hty_f ▸ hwf_f.2.2.2.1
      unfold posOf at h1
      rwa [looseBVarsBounded_renameConsts, Expr.looseBVarsBounded_instantiateLevelParams] at h1
    have htr : c.toConstantVal.type.constsResolve E_r = true := hcr [] rest c rfl
    have hc_ne_rest : ∀ c' ∈ rest, c.name ≠ c'.name :=
      fun c' hc' heq => hcnin (List.mem_map.mpr ⟨c', hc', heq.symm⟩)
    refine ⟨hfr_r c List.mem_cons_self, hfr_p c List.mem_cons_self,
      hbase, hnres, hperm, hknd, htf, htp, htr, htb,
      ⟨cvm_f, mval_f, hint_f, hf_p, hlps_f, by rw [hpos_ty_eq]; exact hty_f⟩, ?_⟩
    refine build_nonRecChain hS_adv rest ⟨c :: E_r.consts⟩ ⟨posCI c :: E_p₀.consts⟩ hnd' ?_ ?_ ?_ ?_
    · intro c' hc'
      rw [EnvExt.find?_cons_ne (hc_ne_rest c' hc')]
      exact hfr_r c' (List.mem_cons_of_mem c hc')
    · intro c' hc'
      rw [EnvExt.find?_cons_ne (hname_p ▸ hc_ne_rest c' hc')]
      exact hfr_p c' (List.mem_cons_of_mem c hc')
    · intro c' hc'
      obtain ⟨hb', hnr', hk', hp', cvm', mval', hint', hfa', hfp', hl', ht'⟩ :=
        hinfo c' (List.mem_cons_of_mem c hc')
      have hne_f : (posCI c).name ≠ f_id c'.name := by
        intro heq
        rw [hname_p] at heq
        rw [← heq, hfr_p c List.mem_cons_self] at hfp'
        exact nomatch hfp'
      exact ⟨hb', hnr', hk', hp', cvm', mval', hint', hfa',
        by rw [EnvExt.find?_cons_ne hne_f]; exact hfp', hl', ht'⟩
    · intro pre suff c' hsplit
      simpa [pushList] using hcr (c :: pre) suff c' (by simp [hsplit])

private theorem build_recProvChain {c_adv : Ctx} (hS_adv : DeclStoreInv c_adv.env)
    {f_id : KKey → KKey} :
    ∀ (recs : List RecInstallEntry) (E_r E_p₀ : Env .anon),
      (recs.map (·.cv.name)).Nodup →
      (∀ w ∈ recs, E_r.find? w.cv.name = none) →
      (∀ w ∈ recs, E_p₀.find? w.cv.name = none) →
      (∀ w ∈ recs,
        isBaseKey w.cv.name = true ∧
        Ix.Kernel.reservedBasisNames.contains w.cv.name = false ∧
        w.cv.levelParams.Perm (List.range w.cv.levelParams.length) ∧
        w.cv.type.constsResolve E_r = true ∧
        (∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id w.cv.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          E_p₀.find? (f_id w.cv.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range w.cv.levelParams.length ∧
          cvm_f.type = (posOf w.cv.levelParams w.cv.type).renameConsts f_id)) →
      RecProvChain E_r E_p₀ f_id recs
  | [], _, _, _, _, _, _ => trivial
  | w :: rest, E_r, E_p₀, hnd, hfr_r, hfr_p, hinfo => by
    obtain ⟨hwnin, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hbase, hnres, hperm, htr, cvm_f, mval_f, hint_f,
        hf_adv, hf_p, hlps_f, hty_f⟩ := hinfo w List.mem_cons_self
    have hmem_f : ConstantInfo.defnInfo cvm_f mval_f hint_f ∈ c_adv.env.consts :=
      Ix.Kernel.Semantics.Env.find?_mem hf_adv
    have hwf_f := hS_adv.store.wf _ hmem_f
    have htf : w.cv.type.hasFvar = false := by
      have h1 : ((posOf w.cv.levelParams w.cv.type).renameConsts f_id).hasFvar = false :=
        hty_f ▸ hwf_f.1
      unfold posOf at h1
      rwa [hasFvar_renameConsts, hasFvar_instantiateLevelParams] at h1
    have htp : w.cv.type.allLevelParamsDefined w.cv.levelParams = true := by
      have h1 :
          ((posOf w.cv.levelParams w.cv.type).renameConsts f_id).allLevelParamsDefined
            (List.range w.cv.levelParams.length) = true :=
        hlps_f ▸ hty_f ▸ hwf_f.2.1
      rw [allLevelParamsDefined_renameConsts] at h1
      exact allLevelParamsDefined_of_posOf_perm hperm h1
    have htb : w.cv.type.looseBVarsBounded 0 = true := by
      have h1 :
          ((posOf w.cv.levelParams w.cv.type).renameConsts f_id).looseBVarsBounded 0 = true :=
        hty_f ▸ hwf_f.2.2.2.1
      unfold posOf at h1
      rwa [looseBVarsBounded_renameConsts, Expr.looseBVarsBounded_instantiateLevelParams] at h1
    have hw_ne_rest : ∀ w' ∈ rest, w.cv.name ≠ w'.cv.name :=
      fun w' hw' heq => hwnin (List.mem_map.mpr ⟨w', hw', heq.symm⟩)
    refine ⟨hfr_r w List.mem_cons_self, hfr_p w List.mem_cons_self,
      hbase, hnres, hperm, htf, htp, htr, htb,
      ⟨cvm_f, mval_f, hint_f, hf_p, hlps_f, hty_f⟩, ?_⟩
    refine build_recProvChain hS_adv rest ⟨w.prov_r :: E_r.consts⟩ ⟨w.prov_p :: E_p₀.consts⟩
      hnd' ?_ ?_ ?_
    · intro w' hw'
      rw [EnvExt.find?_cons_ne (show w.prov_r.name ≠ w'.cv.name from hw_ne_rest w' hw')]
      exact hfr_r w' (List.mem_cons_of_mem w hw')
    · intro w' hw'
      rw [EnvExt.find?_cons_ne (show w.prov_p.name ≠ w'.cv.name from hw_ne_rest w' hw')]
      exact hfr_p w' (List.mem_cons_of_mem w hw')
    · intro w' hw'
      obtain ⟨hb', hnr', hp', htr', cvm', mval', hint', hfa', hfp', hl', ht'⟩ :=
        hinfo w' (List.mem_cons_of_mem w hw')
      have hne_f : w.prov_p.name ≠ f_id w'.cv.name := by
        intro heq
        change w.cv.name = f_id w'.cv.name at heq
        rw [← heq, hfr_p w List.mem_cons_self] at hfp'
        exact nomatch hfp'
      exact ⟨hb', hnr', hp', Ix.Kernel.Expr.constsResolve_mono htr',
        cvm', mval', hint', hfa',
        by rw [EnvExt.find?_cons_ne hne_f]; exact hfp', hl', ht'⟩

private theorem ne_auxKey_of_isBaseKey {k m : KKey} {d : Derived} (hk : isBaseKey k = true) :
    k ≠ auxKey m d := by
  intro heq
  rw [heq] at hk
  exact nomatch hk

private theorem find?_pushList_of_ne :
    ∀ (cs : List (ConstantInfo .anon)) (E : Env .anon) (k : KKey),
      (∀ c ∈ cs, c.name ≠ k) →
      (pushList cs E).find? k = E.find? k
  | [], _, _, _ => rfl
  | c :: rest, E, k, hne => by
    dsimp only [pushList]
    rw [find?_pushList_of_ne rest ⟨c :: E.consts⟩ k
      (fun c' hc' => hne c' (List.mem_cons_of_mem c hc'))]
    exact EnvExt.find?_cons_ne (hne c List.mem_cons_self)

private theorem declStoreInv_push_pos_nonrecs :
    ∀ (nonrecs : List (ConstantInfo .anon)) {E_r E_p : Env .anon}
      {E_adv : Env .anon} {f_id : KKey → KKey},
      (nonrecs.map (·.name)).Nodup →
      DeclStoreInv E_p →
      (∀ k, (E_r.find? k).isSome = (E_p.find? k).isSome) →
      (∀ c ∈ nonrecs, E_p.find? c.name = none) →
      NonRecChain E_r E_adv f_id nonrecs →
      DeclStoreInv (pushList (nonrecs.map posCI) E_p)
  | [], _, _, _, _, _, hSp, _, _, _ => hSp
  | c :: rest, E_r, E_p, E_adv, f_id, hnd, hSp, hsome, hfr_p,
      ⟨_, _, hbase, _, _, hknd, htf, htp, htr, htb, _, hrest⟩ => by
    obtain ⟨hcnin, hnd'⟩ := List.nodup_cons.mp hnd
    have hname_p : (posCI c).name = c.name := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hknd_p : (∃ cv, posCI c = .indInfo cv {}) ∨ ∃ cv nP nF, posCI c = .ctorInfo cv nP nF := by
      rcases hknd with ⟨cv, rfl⟩ | ⟨cv, nP, nF, rfl⟩
      · exact Or.inl ⟨posCV cv, rfl⟩
      · exact Or.inr ⟨posCV cv, nP, nF, rfl⟩
    have hty_p : (posCI c).toConstantVal.type =
        posOf c.toConstantVal.levelParams c.toConstantVal.type := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hlps_p : (posCI c).toConstantVal.levelParams =
        List.range c.toConstantVal.levelParams.length := by
      rcases hknd with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have htf_p : (posCI c).toConstantVal.type.hasFvar = false := by
      rw [hty_p]; unfold posOf; rw [hasFvar_instantiateLevelParams]; exact htf
    have htp_p : (posCI c).toConstantVal.type.allLevelParamsDefined
        (posCI c).toConstantVal.levelParams = true := by
      rw [hty_p, hlps_p]; exact allLevelParamsDefined_posOf htp
    have htr_p : (posCI c).toConstantVal.type.constsResolve E_p = true := by
      rw [hty_p]
      have hcr1 : (posOf c.toConstantVal.levelParams c.toConstantVal.type).constsResolve E_r = true := by
        rw [constsResolve_posOf]; exact htr
      exact constsResolve_congr_isSome (fun k hk => hsome k ▸ hk) _ hcr1
    have htb_p : (posCI c).toConstantVal.type.looseBVarsBounded 0 = true := by
      rw [hty_p]; unfold posOf; rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact htb
    have hSp₁ : DeclStoreInv ⟨posCI c :: E_p.consts⟩ :=
      hSp.cons_nonrec (hname_p ▸ hfr_p c List.mem_cons_self)
        (fun T => hname_p ▸ ne_projTableName_of_isBaseKey hbase)
        hknd_p htf_p htp_p htr_p htb_p
    have hsome₁ : ∀ k, ((⟨c :: E_r.consts⟩ : Env .anon).find? k).isSome =
        ((⟨posCI c :: E_p.consts⟩ : Env .anon).find? k).isSome := by
      intro k
      rw [Env.find?_cons, Env.find?_cons, hname_p]
      by_cases hk : c.name = k
      · rw [ite_eq_left hk, ite_eq_left hk]; rfl
      · rw [ite_eq_right hk, ite_eq_right hk]; exact hsome k
    have hfr_rest : ∀ c' ∈ rest, (⟨posCI c :: E_p.consts⟩ : Env .anon).find? c'.name = none := by
      intro c' hc'
      have hne : (posCI c).name ≠ c'.name :=
        fun heq => hcnin (List.mem_map.mpr ⟨c', hc', heq.symm.trans hname_p⟩)
      rw [EnvExt.find?_cons_ne hne]
      exact hfr_p c' (List.mem_cons_of_mem c hc')
    exact declStoreInv_push_pos_nonrecs rest hnd' hSp₁ hsome₁ hfr_rest hrest

/-- Block-side raw recursor specification prior to pairing with its deserialized advice model
address `a_rm`. -/
structure RawRecSpec where
  a_rec : Bytes.Address
  cv : ConstantVal .anon
  mI : Nat
  rP : Nat
  rawRules : List (RecRule .anon)

def RawRecSpec.toEntry (s : RawRecSpec) (a_rm : Bytes.Address) : RawRecEntry :=
  { a_rec := s.a_rec, a_rm := a_rm, cv := s.cv, mI := s.mI, rP := s.rP, rawRules := s.rawRules }

def RawRecSpec.prov_r (s : RawRecSpec) : ConstantInfo .anon :=
  .recInfo s.cv s.mI s.rP []

def RawRecSpec.prov_p (s : RawRecSpec) : ConstantInfo .anon :=
  .recInfo (posCV s.cv) s.mI s.rP []

def RawRecSpec.toCI (s : RawRecSpec) : ConstantInfo .anon :=
  .recInfo s.cv s.mI s.rP s.rawRules

def zipRawSpecs : List RawRecSpec → List Bytes.Address → List RawRecEntry
  | s :: ss, m :: ms => s.toEntry m :: zipRawSpecs ss ms
  | _, _ => []

private theorem zipRawSpecs_length :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address),
      ms.length = ss.length → (zipRawSpecs ss ms).length = ss.length
  | [], [], _ => rfl
  | _ :: ss, _ :: ms, h => congrArg Nat.succ (zipRawSpecs_length ss ms (Nat.succ.inj h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem zipRawSpecs_map_a_rec :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address),
      ms.length = ss.length → (zipRawSpecs ss ms).map (·.a_rec) = ss.map (·.a_rec)
  | [], [], _ => rfl
  | s :: ss, m :: ms, h =>
    congrArg (s.a_rec :: ·) (zipRawSpecs_map_a_rec ss ms (Nat.succ.inj h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem zipRawSpecs_map_a_rm :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address),
      ms.length = ss.length → (zipRawSpecs ss ms).map (·.a_rm) = ms
  | [], [], _ => rfl
  | _ :: ss, m :: ms, h =>
    congrArg (m :: ·) (zipRawSpecs_map_a_rm ss ms (Nat.succ.inj h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem zipRawSpecs_map_cv :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address),
      ms.length = ss.length → (zipRawSpecs ss ms).map (·.cv) = ss.map (·.cv)
  | [], [], _ => rfl
  | s :: ss, _ :: ms, h =>
    congrArg (s.cv :: ·) (zipRawSpecs_map_cv ss ms (Nat.succ.inj h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem zipRawSpecs_map_prov_r :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address),
      ms.length = ss.length →
      (zipRawSpecs ss ms).map RawRecEntry.prov_r = ss.map RawRecSpec.prov_r
  | [], [], _ => rfl
  | s :: ss, _ :: ms, h =>
    congrArg (s.prov_r :: ·) (zipRawSpecs_map_prov_r ss ms (Nat.succ.inj h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem zipRawSpecs_map_prov_p :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address),
      ms.length = ss.length →
      (zipRawSpecs ss ms).map RawRecEntry.prov_p = ss.map RawRecSpec.prov_p
  | [], [], _ => rfl
  | s :: ss, _ :: ms, h =>
    congrArg (s.prov_p :: ·) (zipRawSpecs_map_prov_p ss ms (Nat.succ.inj h))
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

private theorem zipRawSpecs_getElem :
    ∀ (ss : List RawRecSpec) (ms : List Bytes.Address) (hlen : ms.length = ss.length)
      (i : Nat) (hi : i < ss.length),
      (zipRawSpecs ss ms)[i]'(by rw [zipRawSpecs_length ss ms hlen]; exact hi) =
        ss[i].toEntry (ms[i]'(hlen ▸ hi))
  | [], _, _, _, hi => nomatch hi
  | _ :: _, [], hlen, _, _ => nomatch hlen
  | _ :: _, _ :: _, _, 0, _ => rfl
  | _ :: ss, _ :: ms, hlen, i + 1, hi =>
    zipRawSpecs_getElem ss ms (Nat.succ.inj hlen) i (Nat.lt_of_succ_lt_succ hi)

private theorem declStoreInv_push_pos_specs_prov :
    ∀ (ss : List RawRecSpec) {E_p : Env .anon},
      (ss.map (·.cv.name)).Nodup →
      DeclStoreInv E_p →
      (∀ s ∈ ss, E_p.find? s.cv.name = none) →
      (∀ s ∈ ss,
        isBaseKey s.cv.name = true ∧
        (posCV s.cv).type.hasFvar = false ∧
        (posCV s.cv).type.allLevelParamsDefined (posCV s.cv).levelParams = true ∧
        (posCV s.cv).type.constsResolve E_p = true ∧
        (posCV s.cv).type.looseBVarsBounded 0 = true) →
      DeclStoreInv (pushList (ss.map RawRecSpec.prov_p) E_p)
  | [], _, _, hSp, _, _ => hSp
  | s :: rest, E_p, hnd, hSp, hfr, hwf => by
    obtain ⟨hsnin, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨hbase, htf, htp, htr, htb⟩ := hwf s List.mem_cons_self
    have hSp₁ : DeclStoreInv ⟨s.prov_p :: E_p.consts⟩ :=
      hSp.cons_rec_prov (hfr s List.mem_cons_self)
        (fun T => ne_projTableName_of_isBaseKey hbase) htf htp htr htb
    have hfr_rest : ∀ s' ∈ rest, (⟨s.prov_p :: E_p.consts⟩ : Env .anon).find? s'.cv.name = none := by
      intro s' hs'
      have hne : s.prov_p.name ≠ s'.cv.name :=
        fun heq => hsnin (List.mem_map.mpr ⟨s', hs', heq.symm⟩)
      rw [EnvExt.find?_cons_ne hne]
      exact hfr s' (List.mem_cons_of_mem s hs')
    refine declStoreInv_push_pos_specs_prov rest hnd' hSp₁ hfr_rest ?_
    intro s' hs'
    obtain ⟨hb', htf', htp', htr', htb'⟩ := hwf s' (List.mem_cons_of_mem s hs')
    exact ⟨hb', htf', htp', Ix.Kernel.Expr.constsResolve_mono htr', htb'⟩

/-- Parallel native-inductive seam (`block_is_modeled = 0`). -/
def NativeIndStep (calls : List (Call F)) (env : Env .anon)
    (block₀ : List (ConstantInfo .anon)) (nP : Nat) : Prop :=
  ∃ env₂, CleanInstallStep env (.indDecl block₀ nP) env₂ ∧
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂

end IxVM.Refinement.Decl
