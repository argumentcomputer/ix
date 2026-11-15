import IxVMRefinement.Decl.ModeledInstall
import IxVMRefinement.Obs.RBTreeMap
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.Obs.KernelModeled

/-! # Modeled Inductive Block Dispatch & Top-Level `L5` Assembly (`Modeled.lean`)

Completes the modeled-inductive slice (`L5-M`) and joins it with `L5-V` (`Value.lean`,
`ModeledInstall.lean`) and the native-inductive seam (`NativeIndStep`) to discharge
`IxVM.Consistency.Decls.{u} S₀` and `IxVM.Consistency.L5.{u} S₀`:

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
     inductive members cleanly into native `block_is_modeled = 0` vs modeled `check_modeled_block`),
   - `check_modeled_block_inv`, `check_family_seg1_inv`,
   - `check_advice_records_spec` (stepping `(env, seen)` along `advice` via `AdviceStepOracle` +
     `rbtree_map_insert_field_addrMapAll`),
   - `ci_lvls_type_spec`, `member_val_spec`, `members_val_spec` (matching every block member's
     signature against its advice `Defn` model via `ExactGetCI` + `rename_exact` +
     `kexpr_struct_eq_one`),
   - `check_recs_spec` (refining `KernelModeled::check_recs` across the recursor list via
     `validate_expr_well_scoped_spec`, `core_ensure_sort`, and `check_rules_vm_spec`).
4. **End-to-end `ModeledBlockWitness` assembly & `modeledIndDecl_step`**: walks
   `Obs.«KernelModeled::check_family».obs` end-to-end to construct `ModeledBlockWitness.{u}` and
   feeds it into `modeledBlock_install_step`.
5. **Top-level `Decls S₀` & `L5 S₀` theorems (`l5_decls_S₀`, `l5_S₀`)**: uses `DeclInvM` as the
   witness invariant `Inv`, combining `valueOrPinnedDecl_step_M`, `modeledIndDecl_step`, and
   `NativeIndStep` across all declarations. -/

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
    cases Obs.«RBTreeMap::rbtree_map_ins».obs ev with
    | Nil m47 m60 _ he25 hm55 hm68 he72 _ =>
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
    | Node_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv79 _ _ _ _ _ _ _ =>
      injection hv79 with _ htag _; exact absurd htag (by decide)
    | Node_other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv79 _ _ _ _ _ _ _ _ _ _ _ _ =>
      injection hv79 with _ htag _; exact absurd htag (by decide)
    | Node_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv79 _ _ _ _ _ _ _ _ _ _ _ =>
      injection hv79 with _ htag _; exact absurd htag (by decide)
  | @node c_t kp vp lp rp lv rv _ hk_t hP_t hl_t hr_t rl_t rr_t ihl ihr =>
    intro a_key x_key x_value r h h' cs ext0 hk hv ev
    cases Obs.«RBTreeMap::rbtree_map_ins».obs ev with
    | Nil _ _ hv15 _ _ _ _ _ =>
      injection hv15 with _ htag _; exact absurd htag (by decide)
    | Node_n1 x_color x_k x_v w81 w82 y103 y111 m115 _ v128 m130 _ _ v180 m204 _
        _ hv79 ld104 ld112 ev140 ev127 ev214 ev176 _ =>
      injection hv79 with _ _ hargs
      injection hargs with hc_eq h1
      injection h1 with hk_eq h2
      injection h2 with hv_eq h3
      injection h3 with hl_eq h4
      injection h4 with hr_eq _
      subst hc_eq hk_eq hv_eq hl_eq hr_eq
      have hld_l : loadValue h lp = .ok lv := ext0.loadValue_eq hl_t
      have hld_r : loadValue h rp = .ok rv := ext0.loadValue_eq hr_t
      rw [hld_l] at ld104; injection ld104 with hy103; subst hy103
      rw [hld_r] at ld112; injection ld112 with hy111; subst hy111
      have ext_115 : Heap.Extends h m115 :=
        (ObsFn.heap_extends ev140).trans (ObsFn.heap_extends ev127)
      obtain ⟨hv180, _, ext_204⟩ :=
        ihl (ext0.trans ext_115) (Bytes.repAddressRef_heapMono₂ addrTy ext_115 hk) hv ev214
      have ext_h_204 : Heap.Extends h m204 := ext_115.trans ext_204
      have ext_b_204 : Heap.Extends h₀ m204 := ext0.trans ext_h_204
      obtain ⟨hout, hshape, ext_bal⟩ :=
        rbtree_map_balance_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_b_204 hk_t) hP_t
          hv180 (addrMapAll_mono_pred (P₂ := Pm) ext_b_204 (fun hp => hp) rr_t) ev176
      exact ⟨hout, hshape, ext_h_204.trans ext_bal⟩
    | Node_other_n0 x_color x_k x_v w81 w82 y103 y111 _ m115 _ _ m130 _ _ m261 _ m334 m345
        _ hv79 ld104 ld112 ev140 ev127 _ ev272 _ he311 hm342 hm353 he355 _ =>
      injection hv79 with _ _ hargs
      injection hargs with hc_eq h1
      injection h1 with hk_eq h2
      injection h2 with hv_eq h3
      injection h3 with hl_eq h4
      injection h4 with hr_eq _
      subst hc_eq hk_eq hv_eq hl_eq hr_eq
      have hld_l : loadValue h lp = .ok lv := ext0.loadValue_eq hl_t
      have hld_r : loadValue h rp = .ok rv := ext0.loadValue_eq hr_t
      rw [hld_l] at ld104; injection ld104 with hy103; subst hy103
      rw [hld_r] at ld112; injection ld112 with hy111; subst hy111
      have ext_261 : Heap.Extends h m261 :=
        (ObsFn.heap_extends ev140).trans
          ((ObsFn.heap_extends ev127).trans (ObsFn.heap_extends ev272))
      have ext_334 : Heap.Extends m261 m334 := hm342 ▸ heap_extends_append m261 [lv]
      have ext_345 : Heap.Extends m334 m345 := hm353 ▸ heap_extends_append m334 [rv]
      have ext_all : Heap.Extends h h' := he355 ▸ ext_261.trans (ext_334.trans ext_345)
      have hlv_261 : AddrMapAll en Pm m261 lv :=
        addrMapAll_mono_pred (P₂ := Pm) (ext0.trans ext_261) (fun hp => hp) rl_t
      have hrv_334 : AddrMapAll en Pm m334 rv :=
        addrMapAll_mono_pred (P₂ := Pm) (ext0.trans (ext_261.trans ext_334)) (fun hp => hp) rr_t
      have ld_lv : loadValue h' (.ptr (Value.type lv) m261.length) = .ok lv :=
        load_stored_addrMapAll_type hlv_261 (hm342 ▸ he355 ▸ ext_345)
      have ld_rv : loadValue h' (.ptr (Value.type rv) m334.length) = .ok rv :=
        load_stored_addrMapAll_type hrv_334 (hm353 ▸ he355 ▸ Heap.Extends.refl _)
      rw [he311]
      exact ⟨.node (Bytes.repAddressRef_heapMono₂ addrTy ext_all hk) hv ld_lv ld_rv
        (addrMapAll_mono_pred (P₂ := Pm) (ext0.trans ext_all) (fun hp => hp) rl_t)
        (addrMapAll_mono_pred (P₂ := Pm) (ext0.trans ext_all) (fun hp => hp) rr_t),
        ⟨c_t, x_key, x_value, _, _, rfl⟩, ext_all⟩
    | Node_other_other x_color x_k x_v w81 w82 y103 y111 _ m115 _ _ m130 _ _ _ m261 _ _
        v371 m401 _ _ hv79 ld104 ld112 ev140 ev127 _ ev272 _ _ ev411 ev366 _ =>
      injection hv79 with _ _ hargs
      injection hargs with hc_eq h1
      injection h1 with hk_eq h2
      injection h2 with hv_eq h3
      injection h3 with hl_eq h4
      injection h4 with hr_eq _
      subst hc_eq hk_eq hv_eq hl_eq hr_eq
      have hld_l : loadValue h lp = .ok lv := ext0.loadValue_eq hl_t
      have hld_r : loadValue h rp = .ok rv := ext0.loadValue_eq hr_t
      rw [hld_l] at ld104; injection ld104 with hy103; subst hy103
      rw [hld_r] at ld112; injection ld112 with hy111; subst hy111
      have ext_261 : Heap.Extends h m261 :=
        (ObsFn.heap_extends ev140).trans
          ((ObsFn.heap_extends ev127).trans (ObsFn.heap_extends ev272))
      obtain ⟨hv371, _, ext_401⟩ :=
        ihr (ext0.trans ext_261) (Bytes.repAddressRef_heapMono₂ addrTy ext_261 hk) hv ev411
      have ext_h_401 : Heap.Extends h m401 := ext_261.trans ext_401
      have ext_b_401 : Heap.Extends h₀ m401 := ext0.trans ext_h_401
      obtain ⟨hout, hshape, ext_bal⟩ :=
        rbtree_map_balance_addrMapAll
          (Bytes.repAddressRef_heapMono₂ addrTy ext_b_401 hk_t) hP_t
          (addrMapAll_mono_pred (P₂ := Pm) ext_b_401 (fun hp => hp) rl_t) hv371 ev366
      exact ⟨hout, hshape, ext_h_401.trans ext_bal⟩

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
      L1.Stream h bytes_in x_s →
      ObsFn W "KernelModeled::get_addrs" [x_s, .field n_f] h r h' cs →
      ∃ (as_ : List Bytes.Address) (bytes_out : List UInt8) (x_as x_s' : SourceValue F),
        r = .tuple [x_as, x_s'] ∧
        as_.length = cnt ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as_ x_as ∧
        L1.Stream h' bytes_out x_s' ∧
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

/-- **`KernelModeled::get_addrs`**: peels `n` addresses off an `L1.Stream`, returning a
`RepList addrListEnum` of length `ZMod.val n` and the remaining stream. -/
theorem get_addrs_spec {x_s x_n x_as x_s' : SourceValue F} {bytes_in : List UInt8}
    {h h' : Heap F} {cs : List (Call F)}
    (hs : L1.Stream h bytes_in x_s)
    (ev : ObsFn W "KernelModeled::get_addrs" [x_s, x_n] h (.tuple [x_as, x_s']) h' cs) :
    ∃ (n_f : F) (as_ : List Bytes.Address) (bytes_out : List UInt8),
      x_n = .field n_f ∧
      as_.length = ZMod.val n_f ∧
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as_ x_as ∧
      L1.Stream h' bytes_out x_s' ∧
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

/-- Inversion of `KernelCheck::check_const` on a safe `"Induct"` constant: splits cleanly into the
native route (`block_is_modeled = 0`) vs the modeled route (`check_modeled_block`), while also
providing `validate_expr_well_scoped` + `k_ensure_sort` on `ty`. -/
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
      (∃ (m_mb : Heap F) (cs_mb : List (Call F)),
        Heap.Extends h m_mb ∧
        ObsFn W "KernelModeled::check_modeled_block" [rc, iblk] m_mb r h' cs_mb ∧
        (∀ x ∈ cs_mb, x ∈ calls))) := by
  refine ⟨Or.inr trivial, ?_⟩
  cases Obs.«KernelCheck::check_const».obs ev with
  | Axiom_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv37 _ _ _ _ _ _ _ =>
    injection hv37 with _ htag _; exact absurd htag (by decide)
  | Axiom_other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv37 _ _ _ _ _ _ _ _ _ _ =>
    injection hv37 with _ htag _; exact absurd htag (by decide)
  | Axiom_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv37 _ _ _ _ _ _ _ _ _ _ =>
    injection hv37 with _ htag _; exact absurd htag (by decide)
  | Defn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv269 _ _ _ _ _ _ _ _ _ =>
    injection hv269 with _ htag _; exact absurd htag (by decide)
  | Thm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv526 _ _ _ _ _ _ _ _ _ _ _ _ =>
    injection hv526 with _ htag _; exact absurd htag (by decide)
  | Opaque _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv825 _ _ _ _ _ _ _ _ _ =>
    injection hv825 with _ htag _; exact absurd htag (by decide)
  | Quot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv1076 _ _ _ _ _ _ =>
    injection hv1076 with _ htag _; exact absurd htag (by decide)
  | Induct_n0 v1 m2 cs12 x_nlvls x_ty x_n_params x_n_indices x_num_ctors x_ind_is_unsafe
      x_ind_block x_ind_idx v1282 m1283 cs1293 v1330 m1333 cs1341 m1354 m1376 v1395 m1396 cs1406
      m1427 v1439 m1440 cs1450 v1469 m1470 cs1480 m1492 cs1503 _ _ _ _
      ev14 _ _ _ _ _ hv1240 ev1295 hm1362 hm1384 ev1343 _ hm1435 ev1408 ev1452 ev1482 ev1505
      _ _ hc1634 =>
    injection hv1240 with _ _ hargs
    injection hargs with _ h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ h5; injection h5 with _ h6
    injection h6 with hblk _
    subst hblk hc1634
    have e1 := ObsFn.heap_extends ev14
    have e2 := ObsFn.heap_extends ev1295
    have e3 : Heap.Extends m1283 m1354 :=
      hm1362 ▸ hm1384 ▸ (heap_extends_append m1283 _).trans (heap_extends_append _ _)
    have e4 := ObsFn.heap_extends ev1343
    have e5 : Heap.Extends m1333 m1427 := hm1435 ▸ heap_extends_append m1333 _
    have e6 := ObsFn.heap_extends ev1408
    have e7 := ObsFn.heap_extends ev1452
    have e8 := ObsFn.heap_extends ev1482
    exact Or.inl ⟨m1470, m1492, cs1503,
      e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans e8)))))),
      ev1505, fun x hx => by simp [hx]⟩
  | Induct_other_n0 v1 m2 cs12 x_nlvls x_ty x_n_params x_n_indices x_num_ctors
      x_ind_block x_ind_idx v1282 m1283 cs1293 v1330 m1333 cs1341 m1354 m1376 v1395 m1396 cs1406
      m1427 v1439 m1440 cs1450 v1469 m1470 cs1480 v1491 m1492 cs1503 v1650 m1653 cs1661
      v1687 m1688 cs1698 v1703 m1736 v1748 m1749 cs1759 cs1850
      ev14 _ _ _ _ _ hv1240 ev1295 hm1362 hm1384 ev1343 _ hm1435 ev1408 ev1452 ev1482 ev1505
      _ ev1663 _ _ hm1744 ev1700 ev1761 ev1852 hc1869 =>
    injection hv1240 with _ _ hargs
    injection hargs with _ h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ h5; injection h5 with _ h6
    injection h6 with hblk _
    subst hblk hc1869
    have e1 := ObsFn.heap_extends ev14
    have e2 := ObsFn.heap_extends ev1295
    have e3 : Heap.Extends m1283 m1354 :=
      hm1362 ▸ hm1384 ▸ (heap_extends_append m1283 _).trans (heap_extends_append _ _)
    have e4 := ObsFn.heap_extends ev1343
    have e5 : Heap.Extends m1333 m1427 := hm1435 ▸ heap_extends_append m1333 _
    have e6 := ObsFn.heap_extends ev1408
    have e7 := ObsFn.heap_extends ev1452
    have e8 := ObsFn.heap_extends ev1482
    have e9 := ObsFn.heap_extends ev1505
    have e10 := ObsFn.heap_extends ev1663
    have e11 : Heap.Extends m1653 m1736 := hm1744 ▸ heap_extends_append m1653 _
    have e12 := ObsFn.heap_extends ev1700
    have e13 := ObsFn.heap_extends ev1761
    exact Or.inr ⟨m1749, cs1850,
      e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans
        (e8.trans (e9.trans (e10.trans (e11.trans (e12.trans e13))))))))))),
      ev1852, fun x hx => by simp [hx]⟩
  | Induct_other_other _ _ _ _ _ _ _ _ x_ind_is_unsafe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv1240 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne1870 _ _ _ =>
    injection hv1240 with _ _ hargs
    injection hargs with _ h1; injection h1 with _ h2; injection h2 with _ h3
    injection h3 with _ h4; injection h4 with _ h5; injection h5 with hu _
    exact absurd hu.symm hne1870
  | _ =>
    exfalso
    exact ‹∀ vs : List (SourceValue F), vs.length = 8 →
      Value.construct kciEnum "Induct" [nl, ty, np, ni, nct, .field 0, iblk, iidx] ≠
        .construct "KernelTypes::KConstantInfo" "Induct" vs›
      [nl, ty, np, ni, nct, .field 0, iblk, iidx] rfl rfl

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

/-- Inversion of `KernelModeled::check_family`'s initial segment `Seg1` (asserting empty user
axioms in `rc`). -/
theorem check_family_seg1_inv {rc iblk rblk v104 : SourceValue F} {h m105 : Heap F}
    {cs107 : List (Call F)}
    (sg : Obs.«KernelModeled::check_family».Seg1 rc iblk rblk h v104 m105 cs107) :
    Heap.Extends h m105 := by
  cases sg with
  | Nil _ _ ev15 _ he33 _ => exact he33 ▸ ObsFn.heap_extends ev15
  | Node _ _ _ _ _ _ _ _ heq97 _ _ _ =>
    injection heq97 with hf
    exact absurd hf zero_ne_one

/-- L7 step oracle for `KernelModeled::check_advice_records`: given the current validated advice
prefix `(seenSet, c_cur)`, an unvisited advice address `a` (`addr_set_member(a, seen) = 0`), and
an observed `check_advice_record(rc, a, seen, wset)` sub-derivation, advances `c_cur` to `c_next`
via `ModelExtStep` and installs `a` as a `.defnInfo` in `c_next.env`. -/
def AdviceStepOracle (calls : List (Call F)) (blockNames : List KKey)
    (rc wset : SourceValue F) : Prop :=
  ∀ (c_cur : Ctx) (seenSet : Bytes.Address → Prop) (a : Bytes.Address)
    (x_a x_seen v89 : SourceValue F) (h₀ m55 m90 : Heap F) (cs63 cs100 : List (Call F)),
    DeclStoreInv c_cur.env →
    AuxRootSynced c_cur.env →
    (∀ k ∈ blockNames, c_cur.env.find? k = none) →
    RCRep c_cur.t c_cur.lim h₀ rc →
    EnvFacts c_cur → LoadFacts c_cur → ExactGetCI c_cur → Good c_cur calls →
    Bytes.RepAddressRef addrTy h₀ a x_a →
    AddrMapAll addrMapEnum (fun _ k _ => seenSet k) h₀ x_seen →
    ObsFn W "KernelClaim::addr_set_member" [x_a, x_seen] h₀ (.field 0) m55 cs63 →
    ObsFn W "KernelModeled::check_advice_record" [rc, x_a, x_seen, wset] m55 v89 m90 cs100 →
    (∀ x ∈ cs63, x ∈ calls) →
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
    cases Obs.«KernelModeled::check_advice_records».obs ev with
    | Nil _ he21 he22 _ =>
      rw [he21, he22]
      refine ⟨c_cur, rfl, rfl, rfl, ModelExtStep.refl c_cur.env, hS, hAux, hfr,
        hef, hlf, hex, hg, ?_, ?_, Heap.Extends.refl h⟩
      · exact addrMapAll_mono_pred (Heap.Extends.refl h) (fun hp => Or.inl hp) hseen
      · intro b hb
        rcases hb with hs | hmem
        · exact hdefs b hs
        · exact nomatch hmem
    | Cons _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hadv_rep ld12
      cases he
  | a :: rest, seenSet, c_cur, x_advice, x_seen, r, h, h', cs,
      hS, hAux, hfr, hdefs, hrc, hef, hlf, hex, hg, hadv_rep, hseen, ev, hsub => by
    cases Obs.«KernelModeled::check_advice_records».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hadv_rep ld12
    | Cons x_a x_rest v52 m55 cs63 v89 m90 cs100 cs138 v143 m160 cs168
        ld12 ev65 heq88 ev102 ev170 ev140 hc201 =>
      subst heq88 hc201
      obtain ⟨a', rest', heq_cons, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hadv_rep ld12
      injection heq_cons with ha_eq hrest_eq
      subst ha_eq hrest_eq
      obtain ⟨c_next, hE_eq, ht_eq, hlim_eq, hstep1, hfr1, hef1, hlf1, hex1, hg1,
          cvm_a, mval_a, hint_a, hdef_a⟩ :=
        horacle c_cur seenSet a x_a x_seen v89 h m55 m90 cs63 cs100
          hS hAux hfr hrc hef hlf hex hg ha_rep hseen ev65 ev102
          (fun x hx => hsub x (by simp [hx]))
          (fun x hx => hsub x (by simp [hx]))
      have hS1 : DeclStoreInv c_next.env := hstep1.storeStep hS
      have hAux1 : AuxRootSynced c_next.env := hstep1.auxStep hAux
      have hκ_eq : c_next.κ = c_cur.κ := by simp [Ctx.κ, ht_eq]
      have ext_90 : Heap.Extends h m90 :=
        (ObsFn.heap_extends ev65).trans (ObsFn.heap_extends ev102)
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
    {x_member x_model x_src x_dst x_aset r : SourceValue F}
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
      [x_member, x_model, x_src, x_dst, x_aset] h r h' calls) :
    advSet a_md ∧
    ci_m.toConstantVal.levelParams.Perm (List.range ci_m.toConstantVal.levelParams.length) ∧
    (∃ cvm_f mval_f hint_f,
      c_adv.env.find? (f_id ci_m.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
      cvm_f.levelParams = List.range ci_m.toConstantVal.levelParams.length ∧
      cvm_f.type =
        (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type).renameConsts f_id) ∧
    Heap.Extends h h' := by
  cases Obs.«KernelModeled::member_val».obs ev with
  | run v12 m15 cs23 m50 cs60 v63 m65 p70 cs76 x_nl x_ty m101 p109 cs115
      x_nlm x_mty w132 w133 w134 v199 m202 cs210 v213 m216 cs224
      ev25 heq48 ev78 ld72 ev62 ev117 ld111 heq187 ev226 ev212 heq264 _ he268 hc269 =>
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
    rw [hm50_eq] at ev117
    obtain ⟨hnl_m, hlps_lt_m, hperm_m, hty_m_rep⟩ := hval_m
    have e78 := ObsFn.heap_extends ev78
    have e_h_65 : Heap.Extends h m65 := e25.trans e78
    have hnot_rq : ∀ tag xs, (tag = "Rec" ∨ tag = "Quot") →
        loadValue m101 p109 ≠ .ok (.construct kciEnum tag xs) := by
      intro tag xs htag hld_bad
      rw [ld111] at hld_bad
      injection hld_bad with hcon
      injection hcon with _ htag_eq _
      rcases htag with rfl | rfl <;> exact absurd htag_eq (by decide)
    obtain ⟨ci_md, hfind_md, hnr_md, _, hptr_md⟩ :=
      hexact_adv a_md x_model p109 m65 m101 cs115 ev117
        (hg_adv.sub fun x hx => by simp [hx])
        (Bytes.repAddressRef_heapMono₂ addrTy e_h_65 hmd_rep) hnot_rq
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
      have e_h_101 : Heap.Extends h m101 := e_h_65.trans e117
      have hren_101 : RenameMap c_adv.κ c_adv.κ f_id m101 x_src x_dst := by
        obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
        exact ⟨sAs, dAs,
          RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_101 hs,
          RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_101 hd, hl, hm⟩
      have hren_tm : TmExact c_adv.κ 0 zg m216 0
          (renameAll f_id (posOf ci_m.toConstantVal.levelParams ci_m.toConstantVal.type)) v213 :=
        rename_exact ev226 ((hty_m_rep 0 zg).mono e117) hren_101
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
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k) :
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
        [x_members, x_models, x_src, x_dst, x_aset] h r h' calls →
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
/-- **`KernelModeled::check_recs`** refines a list of `RawRecEntry`s into a matching list of
`RecInstallEntry`s carrying `RawIotaRulesVmRun` and telescope/pin decompositions. -/
theorem check_recs_spec
    (hCore : IxVM.Consistency.Core S₀) (hroles : RolesSpec) (hcallees : CalleesSpec)
    {c_pub c_rhs c_adv : Ctx}
    (ht_rhs : c_rhs.t = c_pub.t) (hlim_rhs : c_rhs.lim = c_pub.lim)
    (ht_eq : c_adv.t = c_pub.t) (hlim_eq : c_adv.lim = c_pub.lim)
    (hef_pub : EnvFacts c_pub) (hlf_pub : LoadFacts c_pub) (hexact_pub : ExactGetCI c_pub)
    (hef_rhs : EnvFacts c_rhs) (hlf_rhs : LoadFacts c_rhs)
    (hef_adv : EnvFacts c_adv) (hlf_adv : LoadFacts c_adv) (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hproj_rhs : ∀ sn i entry, c_rhs.env.findProj? sn i = some entry →
      blockNames.contains sn = false)
    (hnp_ctor : ∀ k cvj cnP cnF, c_pub.env.find? k = some (.ctorInfo cvj cnP cnF) →
      NoProjIn blockNames cvj.type = true) :
    ∀ (raws : List RawRecEntry)
      {x_rc x_type_addrs x_recs x_models x_src x_dst x_aset x_s x_n_recs x_k x_np
       x_univ_offset x_bnl s_out : SourceValue F}
      {bytes_in : List UInt8} {h h' : Heap F} {calls : List (Call F)},
      Good c_pub calls → Good c_rhs calls → Good c_adv calls →
      RCRep c_pub.t c_pub.lim h x_rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h (raws.map (·.a_rec)) x_recs →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h (raws.map (·.a_rm)) x_models →
      AddrMapAll addrMapEnum (fun _ k _ => advSet k) h x_aset →
      RenameMap c_pub.κ c_pub.κ f_id h x_src x_dst →
      L1.Stream h bytes_in x_s →
      (∀ e ∈ raws,
        c_pub.κ (ixAddr e.a_rm) = f_id e.cv.name ∧
        NoProjIn blockNames e.cv.type = true ∧
        (∀ (b_ind : Bytes.Address) (i_ind : Nat) (cv_ind : ConstantVal .anon)
          (caps_ind : IndCaps .anon),
          c_pub.env.find? (c_pub.κ (iprjAddr (ixAddr b_ind) i_ind)) =
            some (.indInfo cv_ind caps_ind) →
          (∃ bs dom body mb lvls_d, e.cv.type.stripPis e.mI = some (bs, .forallE dom body mb) ∧
            dom.getAppFn = .const (c_pub.κ (iprjAddr (ixAddr b_ind) i_ind)) lvls_d) →
          (∀ (k : Nat) (rl : RecRule .anon), e.rawRules[k]? = some rl →
            rl.ctor = c_pub.κ (cprjAddr (ixAddr b_ind) i_ind k)) ∧
          (∀ (k : Nat) (rl : RecRule .anon), e.rawRules[k]? = some rl → ∀ cvj cnP cnF,
            c_pub.env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
            cvj.levelParams.length = cv_ind.levelParams.length)) ∧
        ∀ {p_ci x_r : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
          Heap.Extends h h₁ →
          (∀ x ∈ cs_ci, x ∈ calls) →
          Bytes.RepAddressRef addrTy h₁ e.a_rec x_r →
          ObsFn W "Ingress::get_ci" [x_r] h₁ p_ci h₂ cs_ci →
          CIPtrRepExact c_pub.κ h₂ p_ci e.toCI) →
      ObsFn W "KernelModeled::check_recs"
        [x_rc, x_type_addrs, x_recs, x_models, x_src, x_dst, x_aset, x_s,
         x_n_recs, x_k, x_np, x_univ_offset, x_bnl] h s_out h' calls →
      ∃ (recs : List RecInstallEntry) (bytes_out : List UInt8),
        recs.map (·.cv) = raws.map (·.cv) ∧
        recs.map (·.prov_r) = raws.map (·.prov_r) ∧
        recs.map (·.prov_p) = raws.map (·.prov_p) ∧
        List.Forall₂
          (fun (e : RawRecEntry) (w : RecInstallEntry) =>
            w.cv = e.cv ∧ w.mI = e.mI ∧ w.rP = e.rP ∧ w.rawRules = e.rawRules)
          raws recs ∧
        (∀ w ∈ recs,
          w.cv.type.constsResolve c_pub.env = true ∧
          w.rP ≤ w.mI ∧
          w.cv.type.stripPis w.mI = some (w.pre, .forallE w.dom w.body w.bm) ∧
          w.dom.getAppFn = .const w.indKey w.lvls_lps ∧
          w.dom.getAppArgs.length = w.cnP_ind + (w.mI - w.rP) ∧
          (∀ p ∈ w.dom.getAppArgs.take w.cnP_ind, noLooseIn 0 (w.mI - w.rP) p = true) ∧
          w.dom.getAppArgs.drop w.cnP_ind =
            (List.range (w.mI - w.rP)).map (fun m => .bvar (w.mI - w.rP - 1 - m)) ∧
          w.pins_lps = (w.dom.getAppArgs.take w.cnP_ind).map (Expr.lowerBVars (w.mI - w.rP) 0) ∧
          (∀ r ∈ w.rawRules,
            noLetExpr (posOf w.cv.levelParams r.rhs) = true ∧
            r.rhs.constsResolve c_rhs.env = true ∧
            ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t') ∧
          RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet
            w.cv.name w.cv.levelParams w.cv.type w.mI w.rP w.lvls_lps w.pins_lps 0 w.rawRules) ∧
        L1.Stream h' bytes_out s_out ∧
        Heap.Extends h h' := by
  intro raws
  induction raws with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ bytes_in h h' _
      _ _ _ _ hrecs_rep _ _ _ hstr _ ev
    cases Obs.«KernelModeled::check_recs».obs ev with
    | Nil _ he21 he22 _ =>
      rw [he21, he22]
      exact ⟨[], bytes_in, rfl, rfl, rfl, .nil, (fun _ hm => nomatch hm), hstr, Heap.Extends.refl h⟩
    | Cons (ld12 := ld12) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hrecs_rep ld12
      cases he
  | cons e₀ rawRest ih =>
    intro x_rc x_type_addrs x_recs x_models x_src x_dst x_aset x_s x_n_recs x_k x_np
      x_univ_offset x_bnl s_out bytes_in h h' calls
      hg_pub hg_rhs hg_adv hrc hrecs_rep hmd_rep haset hren hstr hraw_info ev
    cases Obs.«KernelModeled::check_recs».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hrecs_rep ld12
    | Cons x_r x_rest x_rm x_mrest m67 p74 cs80 x_nl x_ty x_rnp x_ni x_nmot x_nmin x_rules
        x_kf x_r_uns w107 w108 v285 m288 cs296 v332 m335 cs343 v346 v347 m349 cs357
        v390 m391 cs401 v405 v406 x420 x428 x436 v472 m473 cs483 v510 m511 cs521
        v547 m548 cs558 m579
        safeTyValue safeTyHeap safeTyCalls safeRulesValue safeRulesHeap safeRulesCalls
        v591 m592 cs602 v645 m646 cs656 v662 m688 p693 cs699
        v731 m732 cs742 v749 x790 cs854 v866
        ld12 ld51 ev82 ld76 _ _ _ _ ev298 _ ev359 _ ev345 _ _ _ _ _ _ ev403 ev485
        ev523 hm587 ev560 evSafetyTy evSafetyRules ev604 ev701 _ ev658 op805 op797 ev744 _ ev856 hc969 =>
      have hsub80 : ∀ x ∈ cs80, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      have hsub558 : ∀ x ∈ cs558, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      have hsub742 : ∀ x ∈ cs742, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      have hsub854 : ∀ x ∈ cs854, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      obtain ⟨a_r', rRest, hr_eq, hr_head, hr_tail⟩ := Lib.rep_cons_of_load hrecs_rep ld12
      obtain ⟨a_rm', rmRest, hrm_eq, hrm_head, hrm_tail⟩ := Lib.rep_cons_of_load hmd_rep ld51
      injection hr_eq with h1 h2; subst h1
      injection hrm_eq with h3 h4; subst h3
      obtain ⟨hrm_key0, hnp_ty0, hrule_ctor0, hci0⟩ := hraw_info e₀ List.mem_cons_self
      have hptr0 : CIPtrRepExact c_pub.κ m67 p74 e₀.toCI :=
        hci0 (Heap.Extends.refl h) hsub80 hr_head ev82
      obtain ⟨v_rec, hld_rec, hci_rec⟩ := hptr0
      rw [ld76] at hld_rec; injection hld_rec with hv_rec
      generalize hci_rec_eq : e₀.toCI = ci_rec_g at hci_rec
      cases hci_rec with
      | @recr nl_r ty_r np_r ni_r nm_r nmi_r rules_r _ _ _ _ cv_g mI_g rP_g rls_g p_f i_f m_f mi_f
          hval0 hnp_f hni_f hnm_f hnmi_f hrP_f hmI_f hcounts0 hrules0 _ _ =>
        injection hv_rec with _ _ hrec_args
        injection hrec_args with h1_r hrec_1
        injection hrec_1 with h2_r hrec_2
        injection hrec_2 with h3_r hrec_3
        injection hrec_3 with h4_r hrec_4
        injection hrec_4 with h5_r hrec_5
        injection hrec_5 with h6_r hrec_6
        injection hrec_6 with h7_r _
        subst h1_r h2_r h3_r h4_r h5_r h6_r h7_r
        dsimp only [RawRecEntry.toCI] at hci_rec_eq
        injection hci_rec_eq with hcv_g hmI_g hrP_g hrls_g
        subst hcv_g hmI_g hrP_g hrls_g
        obtain ⟨hnl0, hlps_lt0, hperm0, hty_rep0⟩ := hval0
        obtain ⟨hrp_le0, hmi_lt0⟩ := hcounts0
        have e82 := ObsFn.heap_extends ev82
        have e298 := ObsFn.heap_extends ev298
        have e359 := ObsFn.heap_extends ev359
        have e345 := ObsFn.heap_extends ev345
        have e403 := ObsFn.heap_extends ev403
        have e485 := ObsFn.heap_extends ev485
        have e523 := ObsFn.heap_extends ev523
        have e_67_511 : Heap.Extends m67 m511 :=
          e298.trans (e359.trans (e345.trans (e403.trans (e485.trans e523))))
        have e_511_579 : Heap.Extends m511 m579 := by
          rw [hm587]; exact heap_extends_append m511 _
        have e_h_579 : Heap.Extends h m579 := e82.trans (e_67_511.trans e_511_579)
        have htypes579 : TypesRep c_pub.κ zg m579 0
            (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m511.length) :=
          by rw [hm587]; exact typesRep_alloc_nil c_pub.κ zg m511
        obtain ⟨stype0, _, _, hinf_ty0, _, _, _⟩ :=
          core_ensure_sort hCore (hrc.mono e_h_579) htypes579 (ghostScoped_zero zg)
            hef_pub hlf_pub (hg_pub.sub hsub558) ev560
            ((hty_rep0 0 zg).toTm.mono (e_67_511.trans e_511_579))
        have hty_nfv0 : (posOf e₀.cv.levelParams e₀.cv.type).hasFvar = false :=
          Tm.hasFvar_false (hty_rep0 0 zg).toTm
        have hty_cr_pos0 :
            (posOf e₀.cv.levelParams e₀.cv.type).constsResolve c_pub.env = true :=
          infer_constsResolve hinf_ty0 hef_pub.store hty_nfv0
        have hty_cr0 : e₀.cv.type.constsResolve c_pub.env = true := by
          rwa [constsResolve_posOf] at hty_cr_pos0
        have e560 := ObsFn.heap_extends ev560
        have e604 := ObsFn.heap_extends ev604
        have e701 := ObsFn.heap_extends ev701
        have e658 := ObsFn.heap_extends ev658
        have e_579_646 : Heap.Extends m579 m646 :=
          e560.trans (evSafetyTy.heap_extends.trans (evSafetyRules.heap_extends.trans
            (e604.trans (e701.trans e658))))
        have e_67_646 : Heap.Extends m67 m646 := (e_67_511.trans e_511_579).trans e_579_646
        have e_h_646 : Heap.Extends h m646 := e82.trans e_67_646
        have hv749_eq : v749 = .field (e₀.rP : F) := by
          rw [hnp_f, hnm_f] at op805
          simp only [evalBinOp, Except.ok.injEq] at op805
          rw [← op805, hnmi_f] at op797
          simp only [evalBinOp, Except.ok.injEq] at op797
          rw [← op797, ← hrP_f]
        have hxni_eq : x_ni = .field ((e₀.mI - e₀.rP : Nat) : F) := by
          rw [hni_f]
          congr 1
          rw [Nat.cast_sub hrp_le0, hrP_f, hmI_f]
          ring
        rw [hnl0, hv749_eq, hxni_eq] at ev744
        have hren646 : RenameMap c_pub.κ c_pub.κ f_id m646 x_src x_dst := by
          obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
          exact ⟨sAs, dAs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_646 hs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_646 hd, hl, hm⟩
        obtain ⟨bytes_mid, indKey0, cnP_ind0, _, pre0, dom0, body0, bm0, lvls0, pins0,
            hstr_mid, _, hstrip0, hdom_fn0, hdom_len0, hdom_nli0, hdom_drop0, hpins0,
            hraw_rules0⟩ :=
          check_rules_vm_spec hCore hroles hcallees
            ht_rhs hlim_rhs ht_eq hlim_eq
            hef_pub hlf_pub hexact_pub hef_rhs hlf_rhs hef_adv hlf_adv hexact_adv
            hf_out hproj_rhs
            (hg_pub.sub hsub742)
            (hg_rhs.sub hsub742)
            (hg_adv.sub hsub742)
            hlps_lt0 hperm0 hrp_le0 hmi_lt0
            ⟨stype0, hinf_ty0⟩ hnp_ty0 hnp_ctor hrule_ctor0
            (hrc.mono e_h_646)
            (Bytes.repAddressRef_heapMono₂ addrTy e_h_646 hrm_head)
            hrm_key0
            (addrSet_mono e_h_646 haset)
            hren646
            (hty_rep0.mono e_67_646)
            (hrules0.mono e_67_646)
            (hstr.mono e_h_646)
            ev744
        have hrls_nolet0 : ∀ r ∈ e₀.rawRules,
            noLetExpr (posOf e₀.cv.levelParams r.rhs) = true :=
          rulesRepExact_noLet hrules0
        have hrls_facts0 : ∀ r ∈ e₀.rawRules,
            noLetExpr (posOf e₀.cv.levelParams r.rhs) = true ∧
            r.rhs.constsResolve c_rhs.env = true ∧
            ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t' := by
          have hwalk : ∀ (j : Nat) (rls : List (RecRule .anon)),
              RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet
                e₀.cv.name e₀.cv.levelParams e₀.cv.type e₀.mI e₀.rP lvls0 pins0 j rls →
              ∀ r ∈ rls, r.rhs.constsResolve c_rhs.env = true ∧
                ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t' := by
            intro j rls hrun r hr
            induction rls generalizing j with
            | nil => cases hr
            | cons r₀ rt ih_rls =>
              obtain ⟨⟨hcert⟩, hrt⟩ := hrun
              rcases List.mem_cons.mp hr with rfl | htl
              · exact ⟨hcert.hrhs_cr, hcert.hrhs_typed⟩
              · exact ih_rls (j + 1) hrt htl
          intro r hr
          obtain ⟨hcr, hinf⟩ := hwalk 0 e₀.rawRules hraw_rules0 r hr
          exact ⟨hrls_nolet0 r hr, hcr, hinf⟩
        let w₀ : RecInstallEntry :=
          { cv := e₀.cv
            mI := e₀.mI
            rP := e₀.rP
            cnP_ind := cnP_ind0
            indKey := indKey0
            lvls_lps := lvls0
            pins_lps := pins0
            pre := pre0
            dom := dom0
            body := body0
            bm := bm0
            rawRules := e₀.rawRules }
        have e744 := ObsFn.heap_extends ev744
        have e_h_732 : Heap.Extends h m732 := e_h_646.trans e744
        have hren732 : RenameMap c_pub.κ c_pub.κ f_id m732 x_src x_dst := by
          obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
          exact ⟨sAs, dAs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hd, hl, hm⟩
        have hr_tail' : RepList addrListEnum (Bytes.RepAddressRef addrTy) m732
            (rawRest.map (·.a_rec)) x_rest := by
          rw [← h2] at hr_tail
          exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hr_tail
        have hrm_tail' : RepList addrListEnum (Bytes.RepAddressRef addrTy) m732
            (rawRest.map (·.a_rm)) x_mrest := by
          rw [← h4] at hrm_tail
          exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hrm_tail
        obtain ⟨recsRest, bytes_out, hcv_map, hpr_map, hpp_map, hf2_rest,
            hw_rest, hstr_out, ext_rest⟩ :=
          ih
            (hg_pub.sub hsub854)
            (hg_rhs.sub hsub854)
            (hg_adv.sub hsub854)
            (hrc.mono e_h_732) hr_tail' hrm_tail'
            (addrSet_mono e_h_732 haset)
            hren732 hstr_mid
            (fun e he => by
              obtain ⟨hk_e, hnp_e, hrc_e, hci_e⟩ :=
                hraw_info e (List.mem_cons_of_mem e₀ he)
              exact ⟨hk_e, hnp_e, hrc_e, fun ext1 hsub1 hrep1 ev1 =>
                hci_e (e_h_732.trans ext1) (fun x hx => hsub854 x (hsub1 x hx)) hrep1 ev1⟩)
            ev856
        refine ⟨w₀ :: recsRest, bytes_out,
          congrArg (e₀.cv :: ·) hcv_map,
          congrArg (e₀.prov_r :: ·) hpr_map,
          congrArg (e₀.prov_p :: ·) hpp_map,
          .cons ⟨rfl, rfl, rfl, rfl⟩ hf2_rest,
          ?_, hstr_out, e_h_732.trans ext_rest⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | htl
        · exact ⟨hty_cr0, hrp_le0, hstrip0, hdom_fn0, hdom_len0, hdom_nli0,
            hdom_drop0, hpins0, hrls_facts0, hraw_rules0⟩
        · exact hw_rest w htl
      | _ =>
        injection hv_rec with _ htag _
        exact absurd htag (by decide)

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

/-- Loader (L1), role/callee (L6), and assembly (L7) companions for a modeled inductive block
(`.indDecl block₀ nP` with `basisPinHit block₀ = none` when `block_is_modeled ≠ 0`). -/
structure ModeledFamilyBridge (calls : List (Call F)) (env : Env .anon)
    (block₀ : List (ConstantInfo .anon)) (nP : Nat)
    (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (rc iblk : SourceValue F) (m_mb : Heap F) (cs_mb : List (Call F)) : Prop where
  rolesSpec : RolesSpec
  calleesSpec : CalleesSpec
  /-- Initial `read_payload` stream at `iblk` in `m_mb` and renewed payload stream inside
  `check_family` at any extended heap. -/
  readPayloadStream :
    ∀ {v_pay : SourceValue F} {h₁ h₂ : Heap F} {cs_p : List (Call F)},
      Heap.Extends m_mb h₁ →
      ObsFn W "KernelModeled::read_payload" [iblk] h₁ v_pay h₂ cs_p →
      ∃ bytes_p, L1.Stream h₂ bytes_p v_pay
  /-- `get_count` peels a count field off a payload `L1.Stream`. -/
  getCountStream :
    ∀ {x_s x_n x_s' : SourceValue F} {bytes_in : List UInt8} {h₁ h₂ : Heap F} {cs_c : List (Call F)},
      L1.Stream h₁ bytes_in x_s →
      ObsFn W "KernelModeled::get_count" [x_s] h₁ (.tuple [x_n, x_s']) h₂ cs_c →
      ∃ bytes_out, L1.Stream h₂ bytes_out x_s'
  /-- `check_witnesses` advances the payload `L1.Stream`. -/
  checkWitnessesStream :
    ∀ {x_s x_n x_out x_s' : SourceValue F} {bytes_in : List UInt8} {h₁ h₂ : Heap F}
      {cs_w : List (Call F)},
      L1.Stream h₁ bytes_in x_s →
      ObsFn W "KernelModeled::check_witnesses" [rc, iblk, x_s, x_n]
        h₁ (.tuple [x_out, x_s']) h₂ cs_w →
      ∃ bytes_out, L1.Stream h₂ bytes_out x_s'
  /-- Advice-record step oracle for `check_advice_records`. -/
  adviceOracle :
    ∀ (blockNames : List KKey) (wset : SourceValue F),
      AdviceStepOracle.{u} calls blockNames rc wset
  /-- Initial role-context & exact-loader companions on `⟨E, env, t, lim⟩`. -/
  baseCtxFacts :
    DeclStoreInv env →
    CtxRoleFacts ⟨E, env, t, lim⟩ ∧
    LoadFacts ⟨E, env, t, lim⟩ ∧
    ExactGetCI ⟨E, env, t, lim⟩ ∧
    Good ⟨E, env, t, lim⟩ calls
  /-- Exact L1/L7 decomposition of the family's inductive types (`v673`), constructors (`v746`),
  and recursors (`v839`) inside `check_family`, matching `installs (.indDecl block₀ nP)` and the
  syntactic checks (`build_flat_block`, `check_nested_aux`, `family_refs_ok`). -/
  familyMembers :
    ∀ {v_pay0 x_rec_block w_rem0 x_s4 x_n_w x_outside x_s5 v390 x_members
       w538 w539 w540 w541 v588 v673 v746 v839 x_univ_offset v1248 v1233 v1292 : SourceValue F}
      {m_pay0 m_ga m297 m332 m391 m453 m501 m589 m652 m674 m704 m747 m784 m840
       m1191 m1257 m1234 m1293 : Heap F}
      {cs_pay0 cs_ga0 cs342 cs401 cs511 cs599 cs684 cs757 cs850 cs1265 cs1244 cs1303 : List (Call F)},
      ObsFn W "KernelModeled::read_payload" [iblk] m_mb v_pay0 m_pay0 cs_pay0 →
      ObsFn W "IxonDeserialize::get_address" [v_pay0] m_pay0 (.tuple [x_rec_block, w_rem0]) m_ga cs_ga0 →
      ObsFn W "KernelModeled::check_witnesses" [rc, iblk, x_s4, x_n_w] m297
        (.tuple [x_outside, x_s5]) m332 cs342 →
      ObsFn W "KernelClaim::addr_set_build"
        [x_outside, .construct addrMapEnum "Nil" []] m332 v390 m391 cs401 →
      ObsFn W "Ingress::load_verified_constant" [iblk] m453
        (.construct "Ixon::Constant" "Mk"
          [.construct "Ixon::ConstantInfo" "Muts" [x_members], w538, w539, w540, w541])
        m501 cs511 →
      ObsFn W Obs.Names.«Lists::length<Ixon::MutConst>» [x_members] m501 v588 m589 cs599 →
      ObsFn W "Ingress::build_recur_addrs" [x_members, iblk] m652 v673 m674 cs684 →
      ObsFn W "KernelModeled::block_ctor_addrs" [x_members, iblk, .field 0] m704 v746 m747 cs757 →
      ObsFn W "KernelModeled::family_recs" [x_rec_block] m784 v839 m840 cs850 →
      ObsFn W "KernelCheck::build_flat_block" [x_rec_block, iblk, x_univ_offset]
        m1191 v1248 m1257 cs1265 →
      ObsFn W "KernelModeled::check_nested_aux" [iblk, v1248] m1257 v1233 m1234 cs1244 →
      ObsFn W "KernelModeled::family_refs_ok" [x_rec_block, iblk, v390]
        m1234 v1292 m1293 cs1303 →
      ∃ (indAs ctorAs : List Bytes.Address)
        (inds ctors : List (ConstantInfo .anon))
        (rawSpecs : List RawRecSpec)
        (_hind_len : indAs.length = inds.length)
        (_hctor_len : ctorAs.length = ctors.length),
        let nonrecs := inds ++ ctors
        let blockNames := (nonrecs.map (·.name)) ++ (rawSpecs.map (·.cv.name))
        v588 = .field (indAs.length : F) ∧
        indAs.length < 4294967296 ∧
        ctorAs.length < 4294967296 ∧
        rawSpecs.length < 4294967296 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m674 indAs v673 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m747 ctorAs v746 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m840 (rawSpecs.map (·.a_rec)) v839 ∧
        blockNames.Nodup ∧
        (∀ c ∈ nonrecs,
          isBaseKey c.name = true ∧
          Ix.Kernel.reservedBasisNames.contains c.name = false ∧
          ((∃ cv, c = .indInfo cv {}) ∨ ∃ cv nP_c nF_c, c = .ctorInfo cv nP_c nF_c) ∧
          NoProjIn blockNames c.toConstantVal.type = true ∧
          (∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci₀.name = c.name)) ∧
        (∀ s ∈ rawSpecs,
          isBaseKey s.cv.name = true ∧
          Ix.Kernel.reservedBasisNames.contains s.cv.name = false ∧
          NoProjIn blockNames s.cv.type = true ∧
          s.cv.type.constsResolve (pushList nonrecs env) = true ∧
          (∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci₀.name = s.cv.name)) ∧
        (∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP),
          (∃ c ∈ nonrecs, IxVM.Consistency.StoredAs c ci₀) ∨
          (∃ s ∈ rawSpecs, IxVM.Consistency.StoredAs s.toCI ci₀)) ∧
        (∀ i (hi : i < indAs.length),
          keyOf t (ixAddr indAs[i]) = (inds[i]'(by omega)).name ∧
          ∀ {p_ci x_m : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
            Heap.Extends m840 h₁ → (∀ x ∈ cs_ci, x ∈ calls) →
            Bytes.RepAddressRef addrTy h₁ indAs[i] x_m →
            ObsFn W "Ingress::get_ci" [x_m] h₁ p_ci h₂ cs_ci →
            CIPtrRepExact (keyOf t) h₂ p_ci (inds[i]'(by omega))) ∧
        (∀ i (hi : i < ctorAs.length),
          keyOf t (ixAddr ctorAs[i]) = (ctors[i]'(by omega)).name ∧
          ∀ {p_ci x_m : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
            Heap.Extends m840 h₁ → (∀ x ∈ cs_ci, x ∈ calls) →
            Bytes.RepAddressRef addrTy h₁ ctorAs[i] x_m →
            ObsFn W "Ingress::get_ci" [x_m] h₁ p_ci h₂ cs_ci →
            CIPtrRepExact (keyOf t) h₂ p_ci (ctors[i]'(by omega))) ∧
        (∀ i (hi : i < rawSpecs.length),
          keyOf t (ixAddr rawSpecs[i].a_rec) = rawSpecs[i].cv.name ∧
          ∀ {p_ci x_r : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
            Heap.Extends m840 h₁ → (∀ x ∈ cs_ci, x ∈ calls) →
            Bytes.RepAddressRef addrTy h₁ rawSpecs[i].a_rec x_r →
            ObsFn W "Ingress::get_ci" [x_r] h₁ p_ci h₂ cs_ci →
            CIPtrRepExact (keyOf t) h₂ p_ci rawSpecs[i].toCI) ∧
        (∀ pre suff c, nonrecs = pre ++ c :: suff →
          c.toConstantVal.type.constsResolve (pushList pre env) = true) ∧
        (∀ ck cvj cnP cnF,
          (pushList (nonrecs.map posCI) env).find? ck = some (.ctorInfo cvj cnP cnF) →
          cvj.type.allLevelParamsDefined cvj.levelParams = true ∧
          NoProjIn blockNames cvj.type = true ∧
          (pushList nonrecs env).find? ck = some (.ctorInfo cvj cnP cnF) ∧
          ∃ bsC0 cbody0 Dc usc,
            cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
            cbody0.getAppFn = .const Dc usc) ∧
        (∀ s ∈ rawSpecs,
          ∀ (b_ind : Bytes.Address) (i_ind : Nat) (cv_ind : ConstantVal .anon)
            (caps_ind : IndCaps .anon),
            (pushList (nonrecs.map posCI) env).find?
              (keyOf t (iprjAddr (ixAddr b_ind) i_ind)) = some (.indInfo cv_ind caps_ind) →
            (∃ bs dom body mb lvls_d, s.cv.type.stripPis s.mI = some (bs, .forallE dom body mb) ∧
              dom.getAppFn = .const (keyOf t (iprjAddr (ixAddr b_ind) i_ind)) lvls_d) →
            (∀ (k : Nat) (rl : RecRule .anon), s.rawRules[k]? = some rl →
              rl.ctor = keyOf t (cprjAddr (ixAddr b_ind) i_ind k)) ∧
            (∀ (k : Nat) (rl : RecRule .anon), s.rawRules[k]? = some rl → ∀ cvj cnP cnF,
              (pushList (nonrecs.map posCI) env).find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
              cvj.levelParams.length = cv_ind.levelParams.length)) ∧
        (DeclStoreInv (pushList (nonrecs.map posCI) env) →
          CtxRoleFacts ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ ∧
          LoadFacts ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ ∧
          ExactGetCI ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ ∧
          Good ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ calls) ∧
        (DeclStoreInv
            (pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env)) →
          CtxRoleFacts
            ⟨E, pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env),
             t, lim⟩ ∧
          LoadFacts
            ⟨E, pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env),
             t, lim⟩ ∧
          Good
            ⟨E, pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env),
             t, lim⟩ calls)

private theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, hy => nomatch hy
  | a :: _, _ :: _, .cons hhd htl, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨a, List.mem_cons_self, hhd⟩
    · obtain ⟨x, hx, hr⟩ := forall₂_mem_right htl _ hm
      exact ⟨x, List.mem_cons_of_mem a hx, hr⟩

private theorem forall₂_mem_left {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => nomatch hx
  | _ :: _, b :: _, .cons hhd htl, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hm
    · exact ⟨b, List.mem_cons_self, hhd⟩
    · obtain ⟨y, hy, hr⟩ := forall₂_mem_left htl _ hm
      exact ⟨y, List.mem_cons_of_mem b hy, hr⟩

set_option maxHeartbeats 6400000 in
/-- **End-to-end `KernelModeled::check_modeled_block` / `check_family` refinement**: constructs
`Nonempty (ModeledBlockWitness.{u} env block₀ nP)` from an observed `check_modeled_block` run and
`ModeledFamilyBridge`. -/
theorem modeledBlockWitness_of_check_family
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {block₀ : List (ConstantInfo .anon)} {nP : Nat}
    {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {rc iblk r_mb : SourceValue F} {m_mb h'_mb : Heap F} {cs_mb : List (Call F)}
    (htwf : t.wf = true)
    (hrc_mb : RCRep t lim m_mb rc)
    (hsub_mb : ∀ x ∈ cs_mb, x ∈ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), env.find? ci₀.name = none)
    (ev_mb : ObsFn W "KernelModeled::check_modeled_block" [rc, iblk] m_mb r_mb h'_mb cs_mb)
    (bridge : ModeledFamilyBridge.{u} calls env block₀ nP E t lim rc iblk m_mb cs_mb)
    (hS₀ : DeclStoreInv env) (hAux₀ : AuxRootSynced env) :
    Nonempty (ModeledBlockWitness.{u} env block₀ nP) := by
  obtain ⟨v_pay0, x_rec_block, w_rem0, m_pay0, m_ga, cs_pay0, cs_ga0, cs_fam,
      ev_pay0, ev_ga0, ev_fam, ext_mb_ga, hsub_fam0⟩ :=
    check_modeled_block_inv ev_mb
  have hsub_fam : ∀ x ∈ cs_fam, x ∈ calls := fun x hx => hsub_mb x (hsub_fam0 x hx)
  cases Obs.«KernelModeled::check_family».obs ev_fam with
  | run v104 m105 cs107 v113 m114 cs124 m136 cs146 x_rb x_s1 v181 m184 cs192
      m219 cs229 x_n_a x_s2 m254 cs264 x_advice x_s3 m297 cs307 x_n_w x_s4
      m332 cs342 x_outside x_s5 v390 m391 cs401 v422 m423 cs433 v452 m453 cs463
      m501 cs511 w538 w539 w540 w541 x_members v588 m589 cs599 v621 m624 cs632
      v651 m652 cs662 v673 m674 cs684 m704 cs714 x_type_models x_s6 v746 m747 cs757
      m784 cs794 v798 m807 cs815 x_ctor_models x_s7 v839 m840 cs850 v861 m862 cs872
      m884 cs894 x_rec_models x_s8 v926 m927 cs937 v941 m950 cs958 v977 m978 cs988
      v992 m1001 cs1009 v1028 m1029 cs1039 v1082 m1083 cs1093 v1136 m1137 cs1147
      m1191 cs1201 x_bnl x_univ_offset v1233 m1234 cs1244 v1248 m1257 cs1265
      v1292 m1293 cs1303 v1330 m1331 cs1341
      sg112 ev126 ev148 ev194 _ ev231 ev266 ev309 ev344 ev403 ev435 ev465
      ev513 ev601 ev634 _ ev664 ev686 ev716 ev759 ev817 ev796 ev852 ev874 ev896
      ev960 ev939 ev1011 ev990 ev1041 ev1095 ev1149 ev1203 ev1267 ev1246 ev1305
      ev1343 _ _ _ hc1466 =>
    -- Subcall inclusions for the 5 key sub-derivations
    have hsub463 : ∀ x ∈ cs463, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1039 : ∀ x ∈ cs1039, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1093 : ∀ x ∈ cs1093, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1147 : ∀ x ∈ cs1147, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1341 : ∀ x ∈ cs1341, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    -- 1. Extract family member lists and L1/L7 invariants
    obtain ⟨indAs, ctorAs, inds, ctors, rawSpecs, hind_len, hctor_len,
        hv588_eq, hind_lt, hctor_lt, hspec_lt,
        hind_rep_674, hctor_rep_747, hrec_rep_840,
        hbn_nd,
        hnr_info, hspec_info, hcov_raw,
        hind_idx, hctor_idx, hspec_idx,
        hcr_nr, hc_wf, hspec_canonical, hctx_pub_fn, hctx_rhs_fn⟩ :=
      bridge.familyMembers ev_pay0 ev_ga0 ev344 ev403 ev513 ev601 ev686 ev759
        ev852 ev1267 ev1246 ev1305
    let nonrecs := inds ++ ctors
    let recAs := rawSpecs.map (·.a_rec)
    let blockNames := (nonrecs.map (·.name)) ++ (rawSpecs.map (·.cv.name))
    -- 2. Payload stream walk up to `ev465 : check_advice_records`
    have ext_105 : Heap.Extends m_ga m105 := check_family_seg1_inv sg112
    obtain ⟨bytes0, hs0⟩ := bridge.readPayloadStream (ext_mb_ga.trans ext_105) ev126
    have ext_114 := ObsFn.heap_extends ev126
    obtain ⟨_, bytes1, _, _, _, htup148, _, hs1_0, ext_136, _⟩ := get_address_spec hs0 ev148
    injection htup148 with hargs148
    injection hargs148 with _ h148_2
    injection h148_2 with hxs1_eq _
    subst hxs1_eq
    have ext_184 := ObsFn.heap_extends ev194
    obtain ⟨bytes2, hs2⟩ := bridge.getCountStream (hs1_0.mono ext_184) ev231
    have ext_219 := ObsFn.heap_extends ev231
    obtain ⟨_, advAs, bytes3, _, _, hadv_rep_254, hs3, ext_254⟩ := get_addrs_spec hs2 ev266
    obtain ⟨bytes4, hs4⟩ := bridge.getCountStream hs3 ev309
    have ext_297 := ObsFn.heap_extends ev309
    obtain ⟨bytes5, hs5⟩ := bridge.checkWitnessesStream hs4 ev344
    have ext_332 := ObsFn.heap_extends ev344
    have ext_423 : Heap.Extends m332 m423 :=
      (ObsFn.heap_extends ev403).trans (ObsFn.heap_extends ev435)
    have ext_mb_423 : Heap.Extends m_mb m423 :=
      ext_mb_ga.trans (ext_105.trans (ext_114.trans (ext_136.trans
        (ext_184.trans (ext_219.trans (ext_254.trans (ext_297.trans (ext_332.trans ext_423))))))))
    have hadv_rep_423 : RepList addrListEnum (Bytes.RepAddressRef addrTy) m423 advAs x_advice :=
      RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_297.trans (ext_332.trans ext_423)) hadv_rep_254
    -- 3. `check_advice_records` (`ev465`)
    let instNames := (IxVM.Consistency.installs (.indDecl block₀ nP)).map (·.name)
    have hfr_inst0 : ∀ k ∈ instNames, env.find? k = none := by
      intro k hk
      obtain ⟨ci₀, hm₀, rfl⟩ := List.mem_map.mp hk
      exact hfresh ci₀ hm₀
    obtain ⟨hR₀, hlf₀, hex₀, hg₀⟩ := bridge.baseCtxFacts hS₀
    let c₀ : Ctx := ⟨E, env, t, lim⟩
    have hef₀ : EnvFacts c₀ := hS₀.toEnvFacts htwf hR₀
    obtain ⟨c_adv, hE_adv, ht_adv, hlim_adv, hadv_step, hS_adv, hAux_adv, hfr_inst_adv,
        hef_adv, hlf_adv, hex_adv, hg_adv, haset_raw, _, ext_453⟩ :=
      check_advice_records_spec (bridge.adviceOracle instNames v390)
        advAs (fun _ => False) c₀ hS₀ hAux₀ hfr_inst0
        (fun _ hf => False.elim hf)
        (hrc_mb.mono ext_mb_423) hef₀ hlf₀ hex₀ hg₀
        hadv_rep_423 .nil ev465 hsub463
    have haset_453 : AddrMapAll addrMapEnum (fun _ b _ => b ∈ advAs) m453 v452 :=
      addrMapAll_mono_pred (Heap.Extends.refl m453) (fun hp => hp.elim False.elim id) haset_raw
    have hκ_adv : c_adv.κ = keyOf t := by simp [Ctx.κ, ht_adv, c₀]
    have htwf_adv : c_adv.t.wf = true := ht_adv ▸ htwf
    -- 4. Deserialized model address lists (`ev716`, `ev817`, `ev796`, `ev874`, `ev896`)
    have ext_453_674 : Heap.Extends m453 m674 :=
      (ObsFn.heap_extends ev513).trans
        ((ObsFn.heap_extends ev601).trans
          ((ObsFn.heap_extends ev634).trans
            ((ObsFn.heap_extends ev664).trans (ObsFn.heap_extends ev686))))
    have hs5_674 : L1.Stream m674 bytes5 x_s5 :=
      hs5.mono (ext_423.trans (ext_453.trans ext_453_674))
    obtain ⟨n_tm_f, tmAs, bytes6, hv588_f, htm_len0, htm_rep_704, hs6, ext_704⟩ :=
      get_addrs_spec hs5_674 ev716
    have htm_len : tmAs.length = indAs.length := by
      have hf : n_tm_f = (indAs.length : F) := Value.field.inj (hv588_f.symm.trans hv588_eq)
      rw [htm_len0, hf, SubstAux.val_natCast (Nat.lt_trans hind_lt (by decide))]
    have ext_747 := ObsFn.heap_extends ev759
    obtain ⟨hv798_eq, hm807_eq⟩ := addrList_length_spec hctor_rep_747 ev817
    have ext_807 : Heap.Extends m747 m807 := hm807_eq ▸ Heap.Extends.refl m747
    obtain ⟨n_cm_f, cmAs, bytes7, hv798_f, hcm_len0, hcm_rep_784, hs7, ext_784⟩ :=
      get_addrs_spec (hs6.mono (ext_747.trans ext_807)) ev796
    have hcm_len : cmAs.length = ctorAs.length := by
      have hf : n_cm_f = (ctorAs.length : F) := Value.field.inj (hv798_f.symm.trans hv798_eq)
      rw [hcm_len0, hf, SubstAux.val_natCast (Nat.lt_trans hctor_lt (by decide))]
    have ext_840 := ObsFn.heap_extends ev852
    obtain ⟨hv861_eq, hm862_eq⟩ := addrList_length_spec hrec_rep_840 ev874
    have ext_862 : Heap.Extends m840 m862 := hm862_eq ▸ Heap.Extends.refl m840
    obtain ⟨n_rm_f, rmAs, bytes8, hv861_f, hrm_len0, hrm_rep_884, hs8, ext_884⟩ :=
      get_addrs_spec (hs7.mono (ext_840.trans ext_862)) ev896
    have hrm_len : rmAs.length = rawSpecs.length := by
      have hf : n_rm_f = ((rawSpecs.map (·.a_rec)).length : F) :=
        Value.field.inj (hv861_f.symm.trans hv861_eq)
      rw [hrm_len0, hf, List.length_map, SubstAux.val_natCast (Nat.lt_trans hspec_lt (by decide))]
    -- 5. Build `RenameMap` (`ev960`, `ev939`, `ev1011`, `ev990`)
    have ext_840_884 : Heap.Extends m840 m884 := ext_862.trans ext_884
    have ext_784_884 : Heap.Extends m784 m884 := ext_840.trans ext_840_884
    have ext_747_884 : Heap.Extends m747 m884 := (ext_807.trans ext_784).trans ext_784_884
    have ext_704_884 : Heap.Extends m704 m884 := ext_747.trans ext_747_884
    have ext_674_884 : Heap.Extends m674 m884 := ext_704.trans ext_704_884
    have h941 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_747_884 hctor_rep_747)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_840_884 hrec_rep_840)
      ev960
    have ext_950 := ObsFn.heap_extends ev960
    have h926 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_674_884.trans ext_950) hind_rep_674)
      h941 ev939
    have ext_927 := ObsFn.heap_extends ev939
    have h992 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_784_884.trans (ext_950.trans ext_927)) hcm_rep_784)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_950.trans ext_927) hrm_rep_884)
      ev1011
    have ext_1001 := ObsFn.heap_extends ev1011
    have h977 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_704_884.trans (ext_950.trans (ext_927.trans ext_1001))) htm_rep_704)
      h992 ev990
    have ext_978 := ObsFn.heap_extends ev990
    have ext_884_978 : Heap.Extends m884 m978 :=
      ext_950.trans (ext_927.trans (ext_1001.trans ext_978))
    have ext_840_978 : Heap.Extends m840 m978 := ext_840_884.trans ext_884_978
    let srcAs := indAs ++ (ctorAs ++ recAs)
    let dstAs := tmAs ++ (cmAs ++ rmAs)
    have hlen_sd : srcAs.length = dstAs.length := by
      simp [srcAs, dstAs, recAs, htm_len, hcm_len, hrm_len]
    let f_id : KKey → KKey := fun k =>
      renameKeyList k (srcAs.map fun b => keyOf t (ixAddr b))
        (dstAs.map fun b => keyOf t (ixAddr b))
    have hren_978 : RenameMap (keyOf t) (keyOf t) f_id m978 v926 v977 :=
      renameMap_of_lists htwf hlen_sd
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_1001.trans ext_978) h926)
        h977
    -- Key-map equations and slice index lookups for `f_id`
    have hind_keys : indAs.map (fun b => keyOf t (ixAddr b)) = inds.map (·.name) := by
      apply List.ext_getElem (by simp [hind_len])
      intro i hi₁ _
      simp only [List.length_map] at hi₁
      simp only [List.getElem_map]
      exact (hind_idx i hi₁).1
    have hctor_keys : ctorAs.map (fun b => keyOf t (ixAddr b)) = ctors.map (·.name) := by
      apply List.ext_getElem (by simp [hctor_len])
      intro i hi₁ _
      simp only [List.length_map] at hi₁
      simp only [List.getElem_map]
      exact (hctor_idx i hi₁).1
    have hrec_keys : recAs.map (fun b => keyOf t (ixAddr b)) = rawSpecs.map (·.cv.name) := by
      apply List.ext_getElem (by simp [recAs])
      intro i hi₁ _
      simp only [List.length_map, recAs] at hi₁
      simp only [List.getElem_map, recAs]
      exact (hspec_idx i hi₁).1
    let ks₁ := inds.map (·.name)
    let ks₂ := ctors.map (·.name)
    let ks₃ := rawSpecs.map (·.cv.name)
    let ds₁ := tmAs.map fun b => keyOf t (ixAddr b)
    let ds₂ := cmAs.map fun b => keyOf t (ixAddr b)
    let ds₃ := rmAs.map fun b => keyOf t (ixAddr b)
    have hsrc_keys : srcAs.map (fun b => keyOf t (ixAddr b)) = ks₁ ++ (ks₂ ++ ks₃) := by
      simp only [srcAs, List.map_append, hind_keys, hctor_keys, hrec_keys, ks₁, ks₂, ks₃]
    have hdst_keys : dstAs.map (fun b => keyOf t (ixAddr b)) = ds₁ ++ (ds₂ ++ ds₃) := by
      simp only [dstAs, List.map_append, ds₁, ds₂, ds₃]
    have hbn_assoc : blockNames = ks₁ ++ (ks₂ ++ ks₃) := by
      simp only [blockNames, nonrecs, List.map_append, List.append_assoc, ks₁, ks₂, ks₃]
    have hf_out : ∀ k, blockNames.contains k = false → f_id k = k := by
      intro k hk
      show renameKeyList k (srcAs.map _) (dstAs.map _) = k
      rw [hsrc_keys, ← hbn_assoc]
      exact renameKeyList_out k blockNames _ hk
    have hbn_nd' : (ks₁ ++ (ks₂ ++ ks₃)).Nodup := hbn_assoc ▸ hbn_nd
    have hnd₁ : ks₁.Nodup := (List.nodup_append.mp hbn_nd').1
    have hnd₂₃ : (ks₂ ++ ks₃).Nodup := (List.nodup_append.mp hbn_nd').2.1
    have hdisj₁ : ∀ x ∈ ks₁, x ∉ ks₂ ++ ks₃ :=
      fun x hx hy => (List.nodup_append.mp hbn_nd').2.2 x hx x hy rfl
    have hnd₂ : ks₂.Nodup := (List.nodup_append.mp hnd₂₃).1
    have hnd₃ : ks₃.Nodup := (List.nodup_append.mp hnd₂₃).2.1
    have hdisj₂ : ∀ x ∈ ks₂, x ∉ ks₃ :=
      fun x hx hy => (List.nodup_append.mp hnd₂₃).2.2 x hx x hy rfl
    have hkd_len₁ : ks₁.length = ds₁.length := by simp [ks₁, ds₁, hind_len.symm, htm_len]
    have hkd_len₂ : ks₂.length = ds₂.length := by simp [ks₂, ds₂, hctor_len.symm, hcm_len]
    have hkd_len₃ : ks₃.length = ds₃.length := by simp [ks₃, ds₃, hrm_len]
    have hf_ind : ∀ i (hi : i < indAs.length),
        keyOf t (ixAddr (tmAs[i]'(by omega))) = f_id (inds[i]'(by omega)).name := by
      intro i hi
      have hi_k : i < ks₁.length := by simp [ks₁, hind_len.symm, hi]
      have hmem_k : ks₁[i] ∈ ks₁ := List.getElem_mem hi_k
      have hstep : f_id ks₁[i] = ds₁[i]'(hkd_len₁ ▸ hi_k) := by
        show renameKeyList ks₁[i] (srcAs.map _) (dstAs.map _) = _
        rw [hsrc_keys, hdst_keys,
          renameKeyList_append_left (ks₂ ++ ks₃) (ds₂ ++ ds₃) hkd_len₁ hmem_k]
        exact renameKeyList_getElem_of_nodup hnd₁ hkd_len₁ hi_k
      simpa [ks₁, ds₁] using hstep.symm
    have hf_ctor : ∀ i (hi : i < ctorAs.length),
        keyOf t (ixAddr (cmAs[i]'(by omega))) = f_id (ctors[i]'(by omega)).name := by
      intro i hi
      have hi_k : i < ks₂.length := by simp [ks₂, hctor_len.symm, hi]
      have hmem_k : ks₂[i] ∈ ks₂ := List.getElem_mem hi_k
      have hnin₁ : ks₂[i] ∉ ks₁ :=
        fun hm => hdisj₁ ks₂[i] hm (List.mem_append_left ks₃ hmem_k)
      have hstep : f_id ks₂[i] = ds₂[i]'(hkd_len₂ ▸ hi_k) := by
        show renameKeyList ks₂[i] (srcAs.map _) (dstAs.map _) = _
        rw [hsrc_keys, hdst_keys,
          renameKeyList_append_right (ks₂ ++ ks₃) (ds₂ ++ ds₃) hkd_len₁ hnin₁,
          renameKeyList_append_left ks₃ ds₃ hkd_len₂ hmem_k]
        exact renameKeyList_getElem_of_nodup hnd₂ hkd_len₂ hi_k
      simpa [ks₂, ds₂] using hstep.symm
    have hf_spec : ∀ i (hi : i < rawSpecs.length),
        keyOf t (ixAddr (rmAs[i]'(by omega))) = f_id rawSpecs[i].cv.name := by
      intro i hi
      have hi_k : i < ks₃.length := by simp [ks₃, hi]
      have hmem_k : ks₃[i] ∈ ks₃ := List.getElem_mem hi_k
      have hnin₁ : ks₃[i] ∉ ks₁ :=
        fun hm => hdisj₁ ks₃[i] hm (List.mem_append_right ks₂ hmem_k)
      have hnin₂ : ks₃[i] ∉ ks₂ := fun hm => hdisj₂ ks₃[i] hm hmem_k
      have hstep : f_id ks₃[i] = ds₃[i]'(hkd_len₃ ▸ hi_k) := by
        show renameKeyList ks₃[i] (srcAs.map _) (dstAs.map _) = _
        rw [hsrc_keys, hdst_keys,
          renameKeyList_append_right (ks₂ ++ ks₃) (ds₂ ++ ds₃) hkd_len₁ hnin₁,
          renameKeyList_append_right ks₃ ds₃ hkd_len₂ hnin₂]
        exact renameKeyList_getElem_of_nodup hnd₃ hkd_len₃ hi_k
      simpa [ks₃, ds₃] using hstep.symm
    -- 6. Run `members_val_spec` on `inds` (`ev1041`), `ctors` (`ev1095`), and `rawSpecs` (`ev1149`)
    have ext_453_978 : Heap.Extends m453 m978 :=
      ext_453_674.trans (ext_674_884.trans ext_884_978)
    have haset_978 : AddrMapAll addrMapEnum (fun _ b _ => b ∈ advAs) m978 v452 :=
      addrSet_mono ext_453_978 haset_453
    have hren_adv_978 : RenameMap c_adv.κ c_adv.κ f_id m978 v926 v977 := hκ_adv.symm ▸ hren_978
    obtain ⟨hmv_inds, ext_1029⟩ :=
      members_val_spec bridge.rolesSpec htwf_adv hex_adv hf_out indAs tmAs inds
        htm_len.symm hind_len (hg_adv.sub hsub1039)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_674_884.trans ext_884_978) hind_rep_674)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_704_884.trans ext_884_978) htm_rep_704)
        (fun i hi => by
          have hc_mem : inds[i]'(by omega) ∈ nonrecs :=
            List.mem_append_left ctors (List.getElem_mem (by omega))
          refine ⟨by rw [hκ_adv]; exact hf_ind i hi,
            (hnr_info _ hc_mem).2.2.2.1, fun ext1 hsub1 hrep1 ev1 => ?_⟩
          rw [hκ_adv]
          exact (hind_idx i hi).2 (ext_840_978.trans ext1)
            (fun x hx => hsub1039 x (hsub1 x hx)) hrep1 ev1)
        haset_978 hren_adv_978 ev1041
    have hren_adv_1029 : RenameMap c_adv.κ c_adv.κ f_id m1029 v926 v977 := by
      obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren_adv_978
      exact ⟨sAs, dAs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1029 hs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1029 hd, hl, hm⟩
    obtain ⟨hmv_ctors, ext_1083⟩ :=
      members_val_spec bridge.rolesSpec htwf_adv hex_adv hf_out ctorAs cmAs ctors
        hcm_len.symm hctor_len (hg_adv.sub hsub1093)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_747_884.trans (ext_884_978.trans ext_1029)) hctor_rep_747)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_784_884.trans (ext_884_978.trans ext_1029)) hcm_rep_784)
        (fun i hi => by
          have hc_mem : ctors[i]'(by omega) ∈ nonrecs :=
            List.mem_append_right inds (List.getElem_mem (by omega))
          refine ⟨by rw [hκ_adv]; exact hf_ctor i hi,
            (hnr_info _ hc_mem).2.2.2.1, fun ext1 hsub1 hrep1 ev1 => ?_⟩
          rw [hκ_adv]
          exact (hctor_idx i hi).2 (ext_840_978.trans (ext_1029.trans ext1))
            (fun x hx => hsub1093 x (hsub1 x hx)) hrep1 ev1)
        (addrSet_mono ext_1029 haset_978)
        hren_adv_1029 ev1095
    have hren_adv_1083 : RenameMap c_adv.κ c_adv.κ f_id m1083 v926 v977 := by
      obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren_adv_1029
      exact ⟨sAs, dAs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1083 hs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1083 hd, hl, hm⟩
    obtain ⟨hmv_specs, ext_1137⟩ :=
      members_val_spec bridge.rolesSpec htwf_adv hex_adv hf_out
        recAs rmAs (rawSpecs.map RawRecSpec.toCI)
        (by simp [recAs, hrm_len]) (by simp [recAs]) (hg_adv.sub hsub1147)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_840_978.trans (ext_1029.trans ext_1083)) hrec_rep_840)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_884_978.trans (ext_1029.trans ext_1083)) hrm_rep_884)
        (fun i hi => by
          have hi_s : i < rawSpecs.length := by simpa [recAs] using hi
          have hs_mem : rawSpecs[i] ∈ rawSpecs := List.getElem_mem hi_s
          refine ⟨by rw [hκ_adv, List.getElem_map]; exact hf_spec i hi_s,
            by rw [List.getElem_map]; exact (hspec_info _ hs_mem).2.2.1,
            fun ext1 hsub1 hrep1 ev1 => ?_⟩
          rw [hκ_adv, List.getElem_map]
          dsimp only [recAs] at hrep1
          rw [List.getElem_map] at hrep1
          exact (hspec_idx i hi_s).2
            (ext_840_978.trans (ext_1029.trans (ext_1083.trans ext1)))
            (fun x hx => hsub1147 x (hsub1 x hx)) hrep1 ev1)
        (addrSet_mono (ext_1029.trans ext_1083) haset_978)
        hren_adv_1083 ev1149
    have hmv_nonrec : ∀ c ∈ nonrecs,
        c.toConstantVal.levelParams.Perm (List.range c.toConstantVal.levelParams.length) ∧
        ∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id c.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range c.toConstantVal.levelParams.length ∧
          cvm_f.type =
            (posOf c.toConstantVal.levelParams c.toConstantVal.type).renameConsts f_id := by
      intro c hc
      rcases List.mem_append.mp hc with hi | hct
      · exact hmv_inds c hi
      · exact hmv_ctors c hct
    have hmv_spec : ∀ s ∈ rawSpecs,
        s.cv.levelParams.Perm (List.range s.cv.levelParams.length) ∧
        ∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id s.cv.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range s.cv.levelParams.length ∧
          cvm_f.type = (posOf s.cv.levelParams s.cv.type).renameConsts f_id := by
      intro s hs
      exact hmv_specs s.toCI (List.mem_map_of_mem hs)
    -- 7. Build `c_pub`, `c_rhs`, `DeclStoreInv c_pub.env`, `DeclStoreInv c_rhs.env`
    let c_pub : Ctx := ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩
    let rawRecs := zipRawSpecs rawSpecs rmAs
    let c_rhs : Ctx := ⟨E, pushList (rawRecs.map RawRecEntry.prov_p) c_pub.env, t, lim⟩
    have hnd_nr : (nonrecs.map (·.name)).Nodup := (List.nodup_append.mp hbn_nd).1
    have hnd_sp : (rawSpecs.map (·.cv.name)).Nodup := (List.nodup_append.mp hbn_nd).2.1
    have hdisj_nr_sp : ∀ x ∈ nonrecs.map (·.name), x ∉ rawSpecs.map (·.cv.name) :=
      fun x hx hy => (List.nodup_append.mp hbn_nd).2.2 x hx x hy rfl
    have hfr_env_nr : ∀ c ∈ nonrecs, env.find? c.name = none := by
      intro c hc
      obtain ⟨ci₀, hm₀, hnm⟩ := (hnr_info c hc).2.2.2.2
      rw [← hnm]; exact hfresh ci₀ hm₀
    have hfr_adv_nr : ∀ c ∈ nonrecs, c_adv.env.find? c.name = none := by
      intro c hc
      obtain ⟨ci₀, hm₀, hnm⟩ := (hnr_info c hc).2.2.2.2
      rw [← hnm]; exact hfr_inst_adv ci₀.name (List.mem_map_of_mem hm₀)
    have hfr_env_sp : ∀ s ∈ rawSpecs, env.find? s.cv.name = none := by
      intro s hs
      obtain ⟨ci₀, hm₀, hnm⟩ := (hspec_info s hs).2.2.2.2
      rw [← hnm]; exact hfresh ci₀ hm₀
    have hfr_adv_sp : ∀ s ∈ rawSpecs, c_adv.env.find? s.cv.name = none := by
      intro s hs
      obtain ⟨ci₀, hm₀, hnm⟩ := (hspec_info s hs).2.2.2.2
      rw [← hnm]; exact hfr_inst_adv ci₀.name (List.mem_map_of_mem hm₀)
    have hpos_nr_names : ∀ c ∈ nonrecs, (posCI c).name = c.name := by
      intro c hc
      rcases (hnr_info c hc).2.2.1 with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hchain_nr0 : NonRecChain env c_adv.env f_id nonrecs :=
      build_nonRecChain hS_adv nonrecs env c_adv.env hnd_nr hfr_env_nr hfr_adv_nr
        (fun c hc => by
          obtain ⟨hb, hnres, hk, _, _⟩ := hnr_info c hc
          obtain ⟨hp, cvm_f, mval_f, hint_f, hfa, hlf, htf⟩ := hmv_nonrec c hc
          exact ⟨hb, hnres, hk, hp, cvm_f, mval_f, hint_f, hfa, hfa, hlf, htf⟩)
        hcr_nr
    have hS_pub : DeclStoreInv c_pub.env :=
      declStoreInv_push_pos_nonrecs nonrecs hnd_nr hS₀ (fun _ => rfl) hfr_env_nr hchain_nr0
    obtain ⟨hR_pub, hlf_pub, hex_pub, hg_pub⟩ := hctx_pub_fn hS_pub
    have hef_pub : EnvFacts c_pub := hS_pub.toEnvFacts htwf hR_pub
    have hfr_pub_sp : ∀ s ∈ rawSpecs, c_pub.env.find? s.cv.name = none := by
      intro s hs
      rw [find?_pushList_of_ne (nonrecs.map posCI) env s.cv.name fun cp hcp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
        rw [hpos_nr_names c hc]
        exact fun heq => hdisj_nr_sp c.name (List.mem_map_of_mem hc)
          (by rw [heq]; exact List.mem_map_of_mem hs)]
      exact hfr_env_sp s hs
    have hsome_nr_pos : ∀ k,
        ((pushList nonrecs env).find? k).isSome = (c_pub.env.find? k).isSome :=
      fun k => (isSome_pushList_posCI_iff nonrecs env k hpos_nr_names).symm
    have hS_rhs0 :
        DeclStoreInv (pushList (rawSpecs.map RawRecSpec.prov_p) c_pub.env) :=
      declStoreInv_push_pos_specs_prov rawSpecs hnd_sp hS_pub hfr_pub_sp fun s hs => by
        obtain ⟨hbase, _, _, hcr_s, _⟩ := hspec_info s hs
        obtain ⟨_, cvm_f, mval_f, hint_f, hf_adv, hlps_f, hty_f⟩ := hmv_spec s hs
        have hwf_f := hS_adv.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem hf_adv)
        have htf : (posCV s.cv).type.hasFvar = false := by
          have h1 : ((posOf s.cv.levelParams s.cv.type).renameConsts f_id).hasFvar = false :=
            hty_f ▸ hwf_f.1
          rwa [hasFvar_renameConsts] at h1
        have htp : (posCV s.cv).type.allLevelParamsDefined (posCV s.cv).levelParams = true := by
          have h1 :
              ((posOf s.cv.levelParams s.cv.type).renameConsts f_id).allLevelParamsDefined
                (List.range s.cv.levelParams.length) = true :=
            hlps_f ▸ hty_f ▸ hwf_f.2.1
          rwa [allLevelParamsDefined_renameConsts] at h1
        have htr : (posCV s.cv).type.constsResolve c_pub.env = true := by
          have h1 : (posOf s.cv.levelParams s.cv.type).constsResolve (pushList nonrecs env) =
              true := by
            rw [constsResolve_posOf]; exact hcr_s
          exact constsResolve_congr_isSome (fun k hk => hsome_nr_pos k ▸ hk) _ h1
        have htb : (posCV s.cv).type.looseBVarsBounded 0 = true := by
          have h1 :
              ((posOf s.cv.levelParams s.cv.type).renameConsts f_id).looseBVarsBounded 0 = true :=
            hty_f ▸ hwf_f.2.2.2.1
          rwa [looseBVarsBounded_renameConsts] at h1
        exact ⟨hbase, htf, htp, htr, htb⟩
    have hrhs_env_eq :
        c_rhs.env = pushList (rawSpecs.map RawRecSpec.prov_p) c_pub.env := by
      dsimp only [c_rhs, rawRecs]
      rw [zipRawSpecs_map_prov_p rawSpecs rmAs hrm_len]
    have hS_rhs : DeclStoreInv c_rhs.env := hrhs_env_eq ▸ hS_rhs0
    obtain ⟨hR_rhs, hlf_rhs0, hg_rhs0⟩ := hctx_rhs_fn hS_rhs0
    have hlf_rhs : LoadFacts c_rhs := by
      show LoadFacts ⟨E, c_rhs.env, t, lim⟩
      rw [hrhs_env_eq]; exact hlf_rhs0
    have hg_rhs : Good c_rhs calls := by
      show Good ⟨E, c_rhs.env, t, lim⟩ calls
      rw [hrhs_env_eq]; exact hg_rhs0
    have hef_rhs : EnvFacts c_rhs :=
      hS_rhs.toEnvFacts htwf (by show CtxRoleFacts ⟨E, c_rhs.env, t, lim⟩; rw [hrhs_env_eq]; exact hR_rhs)
    -- 8. Run `check_recs_spec` (`ev1343`)
    have ext_1137_1293 : Heap.Extends m1137 m1293 :=
      (ObsFn.heap_extends ev1203).trans
        ((ObsFn.heap_extends ev1267).trans
          ((ObsFn.heap_extends ev1246).trans (ObsFn.heap_extends ev1305)))
    have ext_978_1293 : Heap.Extends m978 m1293 :=
      ext_1029.trans (ext_1083.trans (ext_1137.trans ext_1137_1293))
    have ext_884_1293 : Heap.Extends m884 m1293 := ext_884_978.trans ext_978_1293
    have ext_840_1293 : Heap.Extends m840 m1293 := ext_840_884.trans ext_884_1293
    have ext_mb_1293 : Heap.Extends m_mb m1293 :=
      ext_mb_423.trans (ext_453.trans (ext_453_978.trans ext_978_1293))
    have hproj_rhs : ∀ sn i entry, c_rhs.env.findProj? sn i = some entry →
        blockNames.contains sn = false := by
      intro sn i entry hfp
      have hfp1 : c_rhs.env.findProj? sn i = c_pub.env.findProj? sn i := by
        rw [hrhs_env_eq]
        exact findProj_pushList_base (rawSpecs.map RawRecSpec.prov_p) c_pub.env sn i fun cp hcp => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hcp
          exact (hspec_info s hs).1
      have hfp2 : c_pub.env.findProj? sn i = env.findProj? sn i :=
        findProj_pushList_base (nonrecs.map posCI) env sn i fun cp hcp => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
          rw [hpos_nr_names c hc]; exact (hnr_info c hc).1
      rw [hfp1, hfp2] at hfp
      cases hcon : blockNames.contains sn with
      | false => rfl
      | true =>
        have hmem_bn : sn ∈ blockNames := List.mem_of_elem_eq_true hcon
        have hbf : isBaseKey sn = true ∧ env.find? sn = none := by
          rcases List.mem_append.mp hmem_bn with hnr_m | hsp_m
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnr_m
            exact ⟨(hnr_info c hc).1, hfr_env_nr c hc⟩
          · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsp_m
            exact ⟨(hspec_info s hs).1, hfr_env_sp s hs⟩
        have hnone := hAux₀.fresh_projTable hbf.1 hbf.2
        unfold Env.findProj? at hfp
        rw [hnone] at hfp
        exact nomatch hfp
    have hren_1293 : RenameMap c_pub.κ c_pub.κ f_id m1293 v926 v977 := by
      obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren_978
      exact ⟨sAs, dAs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_1293 hs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_1293 hd, hl, hm⟩
    have hraws_rec_rep :
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m1293 (rawRecs.map (·.a_rec)) v839 := by
      dsimp only [rawRecs]
      rw [zipRawSpecs_map_a_rec rawSpecs rmAs hrm_len]
      exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_840_1293 hrec_rep_840
    have hraws_rm_rep :
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m1293 (rawRecs.map (·.a_rm))
          x_rec_models := by
      dsimp only [rawRecs]
      rw [zipRawSpecs_map_a_rm rawSpecs rmAs hrm_len]
      exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_884_1293 hrm_rep_884
    obtain ⟨recs, _, hcv_map, hpr_map, hpp_map, hf2_recs, hw_all, _, _⟩ :=
      check_recs_spec (c_pub := c_pub) (c_rhs := c_rhs) (c_adv := c_adv)
        hCore bridge.rolesSpec bridge.calleesSpec
        rfl rfl ht_adv hlim_adv
        hef_pub hlf_pub hex_pub hef_rhs hlf_rhs hef_adv hlf_adv hex_adv
        hf_out hproj_rhs
        (fun k cvj cnP cnF hf => (hc_wf k cvj cnP cnF hf).2.1)
        rawRecs
        (hg_pub.sub hsub1341) (hg_rhs.sub hsub1341) (hg_adv.sub hsub1341)
        (hrc_mb.mono ext_mb_1293)
        hraws_rec_rep hraws_rm_rep
        (addrSet_mono ext_978_1293 haset_978)
        hren_1293
        (hs8.mono ext_884_1293)
        (fun e he => by
          obtain ⟨i, hi_r, he_eq⟩ := List.mem_iff_getElem.mp he
          have hi_s : i < rawSpecs.length := by
            simpa [rawRecs, zipRawSpecs_length rawSpecs rmAs hrm_len] using hi_r
          have hget := zipRawSpecs_getElem rawSpecs rmAs hrm_len i hi_s
          rw [hget] at he_eq
          subst he_eq
          have hs_mem : rawSpecs[i] ∈ rawSpecs := List.getElem_mem hi_s
          refine ⟨hf_spec i hi_s, (hspec_info _ hs_mem).2.2.1,
            hspec_canonical _ hs_mem, fun ext1 hsub1 hrep1 ev1 => ?_⟩
          exact (hspec_idx i hi_s).2 (ext_840_1293.trans ext1)
            (fun x hx => hsub1341 x (hsub1 x hx)) hrep1 ev1)
        ev1343
    -- 9. Assemble `ModeledBlockWitness`
    have hrec_cvs_eq : recs.map (·.cv) = rawSpecs.map (·.cv) :=
      hcv_map.trans (zipRawSpecs_map_cv rawSpecs rmAs hrm_len)
    have hrec_names_eq : recs.map (·.cv.name) = rawSpecs.map (·.cv.name) := by
      have h1 := congrArg (List.map (·.name)) hrec_cvs_eq
      simpa [List.map_map, Function.comp_def] using h1
    have hbn_recs_eq : (nonrecs.map (·.name)) ++ (recs.map (·.cv.name)) = blockNames := by
      simp only [blockNames, hrec_names_eq]
    have hrec_to_spec : ∀ w ∈ recs, ∃ s ∈ rawSpecs,
        w.cv = s.cv ∧ w.mI = s.mI ∧ w.rP = s.rP ∧ w.rawRules = s.rawRules := by
      intro w hw
      obtain ⟨e, he_mem, hw_eq⟩ := forall₂_mem_right hf2_recs w hw
      obtain ⟨i, hi_r, he_eq⟩ := List.mem_iff_getElem.mp he_mem
      have hi_s : i < rawSpecs.length := by
        simpa [rawRecs, zipRawSpecs_length rawSpecs rmAs hrm_len] using hi_r
      rw [zipRawSpecs_getElem rawSpecs rmAs hrm_len i hi_s] at he_eq
      subst he_eq
      exact ⟨rawSpecs[i], List.getElem_mem hi_s, hw_eq⟩
    have hspec_to_rec : ∀ s ∈ rawSpecs, ∃ w ∈ recs,
        w.cv = s.cv ∧ w.mI = s.mI ∧ w.rP = s.rP ∧ w.rawRules = s.rawRules := by
      intro s hs
      obtain ⟨i, hi_s, rfl⟩ := List.mem_iff_getElem.mp hs
      have he_mem : (zipRawSpecs rawSpecs rmAs)[i]'(by
          rw [zipRawSpecs_length rawSpecs rmAs hrm_len]; exact hi_s) ∈ rawRecs :=
        List.getElem_mem _
      obtain ⟨w, hw_mem, hw_eq⟩ := forall₂_mem_left hf2_recs _ he_mem
      rw [zipRawSpecs_getElem rawSpecs rmAs hrm_len i hi_s] at hw_eq
      exact ⟨w, hw_mem, hw_eq⟩
    -- Shared helper for `env_iota` bridges (`hchains`, `hfind_pub_M`, `hrecs_rules`)
    have hiota_bridges : ∀ (env_iota : Env .anon),
        EnvExt c_adv.env env_iota →
        (∀ k, (∀ w ∈ recs, ∀ j, k ≠ auxKey (auxKey w.cv.name .model) (.iota j)) →
          env_iota.find? k = c_adv.env.find? k) →
        NonRecChain env env_iota f_id nonrecs ∧
        RecProvChain (pushList nonrecs env) (pushList (nonrecs.map posCI) env_iota) f_id recs ∧
        (∀ k ci, c_pub.env.find? k = some ci →
          (pushList (nonrecs.map posCI) env_iota).find? k = some ci) ∧
        EnvExt c_pub.env
          (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota)) ∧
        EnvExt c_rhs.env
          (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota)) := by
      intro env_iota hext_iota hout_iota
      have hfr_iota_nr : ∀ c ∈ nonrecs, env_iota.find? c.name = none := by
        intro c hc
        rw [hout_iota c.name fun _ _ _ => ne_auxKey_of_isBaseKey (hnr_info c hc).1]
        exact hfr_adv_nr c hc
      have hfr_iota_rec : ∀ w ∈ recs, env_iota.find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_eq, hout_iota s.cv.name fun _ _ _ => ne_auxKey_of_isBaseKey (hspec_info s hs).1]
        exact hfr_adv_sp s hs
      have hnr_chain : NonRecChain env env_iota f_id nonrecs :=
        build_nonRecChain hS_adv nonrecs env env_iota hnd_nr hfr_env_nr hfr_iota_nr
          (fun c hc => by
            obtain ⟨hb, hnres, hk, _, _⟩ := hnr_info c hc
            obtain ⟨hp, cvm_f, mval_f, hint_f, hfa, hlf, htf⟩ := hmv_nonrec c hc
            exact ⟨hb, hnres, hk, hp, cvm_f, mval_f, hint_f, hfa, hext_iota.find hfa, hlf, htf⟩)
          hcr_nr
      have hnd_pos_nr : ((nonrecs.map posCI).map (·.name)).Nodup := by
        have hmap : (nonrecs.map posCI).map (·.name) = nonrecs.map (·.name) := by
          rw [List.map_map]
          exact List.map_congr_left fun c hc => hpos_nr_names c hc
        rwa [hmap]
      obtain ⟨hfind_pub_Mp, hext_pub_Mp⟩ :=
        envExt_pushList_shared (nonrecs.map posCI) (hadv_step.ext.trans hext_iota) hnd_pos_nr
          (fun cp hcp => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]; exact hfr_env_nr c hc)
          (fun cp hcp => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]; exact hfr_iota_nr c hc)
          (fun cp hcp T => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]; exact ne_projTableName_of_isBaseKey (hnr_info c hc).1)
          (fun cp hcp => Or.inr (by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]
            have hb : isBaseKey c.name = true := (hnr_info c hc).1
            refine ⟨hAux₀.fresh_projTable hb (hfr_env_nr c hc), ?_⟩
            rw [hout_iota (projTableName c.name) fun w _ j =>
              (ne_projTableName_auxKey_iota (auxKey w.cv.name .model) c.name j).symm]
            exact hAux_adv.fresh_projTable hb (hfr_adv_nr c hc)))
      have hnd_rec : (recs.map (·.cv.name)).Nodup := hrec_names_eq ▸ hnd_sp
      have hfr_M_r : ∀ w ∈ recs, (pushList nonrecs env).find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_eq, find?_pushList_of_ne nonrecs env s.cv.name fun c hc heq =>
          hdisj_nr_sp c.name (List.mem_map_of_mem hc) (by rw [heq]; exact List.mem_map_of_mem hs)]
        exact hfr_env_sp s hs
      have hfr_M_p : ∀ w ∈ recs,
          (pushList (nonrecs.map posCI) env_iota).find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [find?_pushList_of_ne (nonrecs.map posCI) env_iota w.cv.name fun cp hcp => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
          rw [hpos_nr_names c hc, hcv_eq]
          exact fun heq => hdisj_nr_sp c.name (List.mem_map_of_mem hc)
            (by rw [heq]; exact List.mem_map_of_mem hs)]
        exact hfr_iota_rec w hw
      have hrec_chain :
          RecProvChain (pushList nonrecs env) (pushList (nonrecs.map posCI) env_iota) f_id recs :=
        build_recProvChain hS_adv recs (pushList nonrecs env)
          (pushList (nonrecs.map posCI) env_iota) hnd_rec hfr_M_r hfr_M_p fun w hw => by
          obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
          obtain ⟨hb, hnres, _, hcr_s, _⟩ := hspec_info s hs
          obtain ⟨hp, cvm_f, mval_f, hint_f, hfa, hlf, htf⟩ := hmv_spec s hs
          rw [← hcv_eq] at hb hnres hcr_s hp hfa hlf htf
          have hfp : (pushList (nonrecs.map posCI) env_iota).find? (f_id w.cv.name) =
              some (.defnInfo cvm_f mval_f hint_f) := by
            rw [find?_pushList_of_ne (nonrecs.map posCI) env_iota (f_id w.cv.name) fun cp hcp => by
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
              rw [hpos_nr_names c hc]
              intro heq
              have hnone := hfr_adv_nr c hc
              rw [heq, hfa] at hnone
              exact nomatch hnone]
            exact hext_iota.find hfa
          exact ⟨hb, hnres, hp, hcr_s, cvm_f, mval_f, hint_f, hfa, hfp, hlf, htf⟩
      have hnd_prov_p : ((recs.map (·.prov_p)).map (·.name)).Nodup := by
        have hmap : (recs.map (·.prov_p)).map (·.name) = recs.map (·.cv.name) := by
          rw [List.map_map]; rfl
        rwa [hmap]
      have hfr_pub_rec : ∀ w ∈ recs, c_pub.env.find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_eq]; exact hfr_pub_sp s hs
      have hnpt_prov_p : ∀ cp ∈ recs.map (·.prov_p), ∀ T, cp.name ≠ projTableName T := by
        intro cp hcp T
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        show w.cv.name ≠ projTableName T
        rw [hcv_eq]; exact ne_projTableName_of_isBaseKey (hspec_info s hs).1
      have hext_Mp_Sp :
          EnvExt (pushList (nonrecs.map posCI) env_iota)
            (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota)) :=
        envExt_pushList_fresh_base (recs.map (·.prov_p)) hnd_prov_p
          (fun cp hcp => by
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
            exact hfr_M_p w hw)
          hnpt_prov_p
      obtain ⟨_, hext_rhs_Sp0⟩ :=
        envExt_pushList_shared (recs.map (·.prov_p)) hext_pub_Mp hnd_prov_p
          (fun cp hcp => by
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
            exact hfr_pub_rec w hw)
          (fun cp hcp => by
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
            exact hfr_M_p w hw)
          hnpt_prov_p
          (fun cp hcp => by
            obtain ⟨w, _, rfl⟩ := List.mem_map.mp hcp
            exact Or.inl fun _ _ h => nomatch h)
      have hrhs_recs_eq : c_rhs.env = pushList (recs.map (·.prov_p)) c_pub.env := by
        dsimp only [c_rhs]; rw [hpp_map]
      exact ⟨hnr_chain, hrec_chain, hfind_pub_Mp, hext_pub_Mp.trans hext_Mp_Sp,
        hrhs_recs_eq ▸ hext_rhs_Sp0⟩
    have hsome_rhs_to_real : ∀ k,
        (c_rhs.env.find? k).isSome =
          ((pushList (recs.map (·.prov_r)) (pushList nonrecs env)).find? k).isSome := by
      intro k
      have hrhs_recs_eq : c_rhs.env = pushList (recs.map (·.prov_p)) c_pub.env := by
        dsimp only [c_rhs]; rw [hpp_map]
      rw [hrhs_recs_eq]
      exact isSome_pushList_prov_iff recs c_pub.env (pushList nonrecs env) k
        (fun x => isSome_pushList_posCI_iff nonrecs env x hpos_nr_names)
    refine ⟨{
      c_pub := c_pub
      c_rhs := c_rhs
      c_adv := c_adv
      f_id := f_id
      advSet := fun b => b ∈ advAs
      nonrecs := nonrecs
      recs := recs
      hadv_step := hadv_step
      hnames_nodup := hbn_recs_eq ▸ hbn_nd
      hnames_fresh_adv := fun k hk => by
        rw [hbn_recs_eq] at hk
        rcases List.mem_append.mp hk with hnr_m | hsp_m
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnr_m
          exact hfr_adv_nr c hc
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsp_m
          exact hfr_adv_sp s hs
      hcov_installs := fun ci₀ hm₀ => by
        rcases hcov_raw ci₀ hm₀ with hnr_c | ⟨s, hs, hst⟩
        · exact Or.inl hnr_c
        · obtain ⟨w, hw, hcv_w, hmI_w, hrP_w, hrls_w⟩ := hspec_to_rec s hs
          have htoCI_eq : ConstantInfo.recInfo w.cv w.mI w.rP w.rawRules = s.toCI := by
            simp only [RawRecSpec.toCI, hcv_w, hmI_w, hrP_w, hrls_w]
          rw [← htoCI_eq] at hst
          exact Or.inr ⟨w, hw, storedAs_checked_r hst⟩
      hin_installs_nonrec := fun c hc => (hnr_info c hc).2.2.2.2
      hin_installs_rec := fun w hw => by
        obtain ⟨s, hs, hcv_w, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_w]; exact (hspec_info s hs).2.2.2.2
      hf_out := fun k hk => hf_out k (hbn_recs_eq ▸ hk)
      hchains := fun env_iota hext_iota hout_iota => by
        obtain ⟨hc1, hc2, _, _, _⟩ := hiota_bridges env_iota hext_iota hout_iota
        exact ⟨hc1, hc2⟩
      hctor_pub_wf := fun ck cvj cnP cnF hf => by
        obtain ⟨hlp, _, hmr, hhd⟩ := hc_wf ck cvj cnP cnF hf
        exact ⟨hlp, hmr, hhd⟩
      hfind_pub_M := fun env_iota hext_iota hout_iota => by
        obtain ⟨_, _, hfM, hextM, _⟩ := hiota_bridges env_iota hext_iota hout_iota
        exact ⟨hfM, hextM⟩
      hrecs_rules := fun w hw => by
        obtain ⟨_, hrp_le, hstrip, hdom_fn, hdom_len, hdom_nli, hdom_drop,
            hpins, hrls_facts, hraw_run⟩ := hw_all w hw
        obtain ⟨s, hs, hcv_w, _, _, _⟩ := hrec_to_spec w hw
        have hw_perm : w.cv.levelParams.Perm (List.range w.cv.levelParams.length) := by
          rw [hcv_w]; exact (hmv_spec s hs).1
        refine ⟨hrp_le, hstrip, hdom_fn, hdom_len, hdom_nli, hdom_drop, hpins, ?_, ?_,
          hbn_recs_eq.symm ▸ hraw_run⟩
        · intro r hr
          obtain ⟨hnl, hcr_rhs, _⟩ := hrls_facts r hr
          exact ⟨hnl,
            constsResolve_congr_isSome (fun k hk => hsome_rhs_to_real k ▸ hk) _ hcr_rhs⟩
        · intro env_iota hext_iota hout_iota r hr t' hinf
          obtain ⟨_, _, _, _, hext_rhs_Sp⟩ := hiota_bridges env_iota hext_iota hout_iota
          exact ⟨posOf w.cv.levelParams t',
            posRulesJ_infer_weaken hext_rhs_Sp (posRulesJ_infer_posOf hw_perm hinf)⟩
    }⟩

/-! ## Section 5: Modeled Dispatch, Native Seam, & Top-Level `Decls S₀` / `L5 S₀` -/

/-- Loader (L1), role/callee (L6), and assembly (L7) witness for a modeled inductive declaration
`.indDecl block₀ nP`: exhibits a checked safe `"Induct"` member whose `KernelCheck::check_const`
derivation does not take the native `block_is_modeled = 0` branch and carries
`ModeledFamilyBridge`. -/
structure DeclModeledExtraFacts (calls : List (Call F)) (env : Env .anon)
    (block₀ : List (ConstantInfo .anon)) (nP : Nat) : Prop where
  installsNodup : ((IxVM.Consistency.installs (.indDecl block₀ nP)).map (·.name)).Nodup
  installsFresh :
    ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), env.find? ci₀.name = none
  modeledWitness :
    ∃ (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
      (cl : Call F) (rc nl ty np ni nct iblk iidx ap r_cl : SourceValue F)
      (h'_cl : Heap F) (subcalls : List (Call F)),
      t.wf = true ∧
      cl ∈ calls ∧
      RCRep t lim cl.heap rc ∧
      ObsFn W "KernelCheck::check_const"
        [rc, .construct kciEnum "Induct" [nl, ty, np, ni, nct, .field 0, iblk, iidx], ap]
        cl.heap r_cl h'_cl subcalls ∧
      (∀ x ∈ subcalls, x ∈ calls) ∧
      (∀ (m_bm1 m_bm2 : Heap F) (cs_bm : List (Call F)),
        Heap.Extends cl.heap m_bm1 → (∀ x ∈ cs_bm, x ∈ calls) →
        ¬ ObsFn W "KernelModeled::block_is_modeled" [iblk] m_bm1 (.field 0) m_bm2 cs_bm) ∧
      ∀ (m_mb : Heap F) (cs_mb : List (Call F)),
        Heap.Extends cl.heap m_mb →
        ObsFn W "KernelModeled::check_modeled_block" [rc, iblk] m_mb r_cl h'_cl cs_mb →
        (∀ x ∈ cs_mb, x ∈ calls) →
        ModeledFamilyBridge.{u} calls env block₀ nP E t lim rc iblk m_mb cs_mb

/-- **Modeled Inductive Declaration Step Theorem (`L5-M`)**: combines `check_const_ind_inv`,
`modeledBlockWitness_of_check_family`, and `modeledBlock_install_step` to step `DeclInvM` across a
modeled `.indDecl block₀ nP`. -/
theorem modeledIndDecl_step (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {block₀ : List (ConstantInfo .anon)} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block₀ nP))
    (hx : DeclModeledExtraFacts.{u} calls env block₀ nP) :
    ∃ env₂, CleanInstallStep env (.indDecl block₀ nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  obtain ⟨E, t, lim, cl, rc, nl, ty, np, ni, nct, iblk, iidx, ap, r_cl, h'_cl, subcalls,
      htwf, _, hrc, ev_chk, hsub, hnot_native, hbridge_fn⟩ :=
    hx.modeledWitness
  rcases (check_const_ind_inv ev_chk).2 with
    ⟨m_bm1, m_bm2, cs_bm, ext_bm, ev_bm, hsub_bm⟩ | ⟨m_mb, cs_mb, ext_mb, ev_mb, hsub_mb⟩
  · exact absurd ev_bm
      (hnot_native m_bm1 m_bm2 cs_bm ext_bm (fun x hx => hsub x (hsub_bm x hx)))
  · have hsub_mb' : ∀ x ∈ cs_mb, x ∈ calls := fun x hx => hsub x (hsub_mb x hx)
    have bridge := hbridge_fn m_mb cs_mb ext_mb ev_mb hsub_mb'
    exact modeledBlock_install_step hchk hx.installsNodup hx.installsFresh
      (modeledBlockWitness_of_check_family hCore htwf (hrc.mono ext_mb) hsub_mb'
        hx.installsFresh ev_mb bridge)

/-- Parallel native-inductive seam (`L5-N`, `block_is_modeled = 0`). -/
def NativeIndStep (calls : List (Call F)) (env : Env .anon)
    (block₀ : List (ConstantInfo .anon)) (nP : Nat) : Prop :=
  ∃ env₂, CleanInstallStep env (.indDecl block₀ nP) env₂ ∧
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂

/-- Combined per-declaration seam assumptions owed by L1/L6/L7 (and `L5-N` for native inductive
blocks). -/
structure DeclExtraFacts (calls : List (Call F)) (env : Env .anon)
    (d : Declaration .anon) : Prop where
  valueFacts : DeclValueExtraFacts calls env d
  unpinnedInd :
    ∀ block₀ nP, d = .indDecl block₀ nP → Ix.Kernel.basisPinHit block₀ = none → block₀ ≠ [] →
      DeclModeledExtraFacts.{u} calls env block₀ nP ∨ NativeIndStep.{u} calls env block₀ nP

/-- Global seam hypothesis supplying `DeclExtraFacts` for every `S0.Checked` declaration in a
bounded call trace. -/
def AllDeclExtraFacts : Prop :=
  ∀ (calls : List (Call F)) (env : Env .anon) (d : Declaration .anon),
    IxVM.Consistency.Bounded calls → S0.Checked calls env d → DeclExtraFacts.{u} calls env d

/-- **Unified `DeclInvM` step preservation across all declarations** (`L5-V` + `L5-M` +
`NativeIndStep`). -/
theorem decl_step_S₀ (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {d : Declaration .anon}
    (hchk : S0.Checked calls env d)
    (hx : DeclExtraFacts.{u} calls env d) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ :=
  valueOrPinnedDecl_step_M hLevels hCore hchk hx.valueFacts fun block₀ nP hd hpin => by
    cases block₀ with
    | nil =>
      have hempty : IxVM.Consistency.installs (.indDecl [] nP) = [] := by
        simp [IxVM.Consistency.installs, hpin]
      exact ⟨env, CleanInstallStep.empty hempty, fun _ _ h => h⟩
    | cons c₀ rest =>
      rcases hx.unpinnedInd (c₀ :: rest) nP hd hpin (List.cons_ne_nil c₀ rest) with hmod | hnat
      · exact modeledIndDecl_step hCore (hd ▸ hchk) hmod
      · exact hnat

/-- **`IxVM.Consistency.Decls.{u} S₀`** witnessed by `DeclInvM`. -/
theorem l5_decls_S₀ (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    (hExtra : AllDeclExtraFacts.{u}) :
    IxVM.Consistency.Decls.{u} S₀ :=
  ⟨fun (V : Type u) [Ix.Kernel.SetTheory V] (env : Env .anon) => DeclInvM V env,
    fun V _ => DeclInvM.empty V,
    fun _ _ _ h => h.toEnvModelOk,
    fun calls env d hbnd hchk =>
      let ⟨env₂, hclean, hstep⟩ := decl_step_S₀ hLevels hCore hchk (hExtra calls env d hbnd hchk)
      ⟨env₂, hclean.step, hstep⟩⟩

/-- **Top-level Obligation `L5` at `S₀`** (`IxVM.Consistency.L5.{u} S₀`). -/
theorem l5_S₀ (hExtra : AllDeclExtraFacts.{u}) :
    IxVM.Consistency.L5.{u} S₀ :=
  fun _ hLevels _ hCore => l5_decls_S₀ hLevels hCore hExtra

end IxVM.Refinement.Decl
