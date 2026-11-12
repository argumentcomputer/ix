import IxVMRefinement.Nat.Basic
import IxVMRefinement.Nat.Utf8
import IxVMRefinement.Core.Steps.Whnf

/-! # `KernelNatPrim`: constructions, the `u32` split, and the string-literal expansion

Step lemmas of the `KernelNatPrim` functions that build terms, split a field element into bytes,
and expand a string literal, against their registered specs:

* **Constructions.** `mk_bool` builds the closed `Bool.false` or `Bool.true`: the address
  `role_addr` returns is bound to the role, so its key is the role (`keyOf_of_addressOf`), at an
  empty level list. `mk_nat_lit` stores a literal node of canonical limbs, `np_apply_spine`
  folds a spine into applications, and `lvls_empty` tests a level list for emptiness (a list
  semantically equal to the empty one is empty).
* **The `u32` split.** `split_u32` takes four base-256 digits off a field element with
  `divmod_256` (whose derivation exists only below `2^32`), so the quotients are the natural
  ones; `klimbs_from_g` stores the four digits as the low bytes of one limb, which is the word
  of the value (`TagN.u64Value` below `2^32`), and normalizes it. The recomposition check the
  circuit makes afterwards is redundant.
* **String literals.** `str_lit_to_ctor` stores the constants of the five roles
  `role_used_implicitly` returns (keyed by their roles), at the level `0` where
  `strLitToConstructor` writes one, and the character list `build_char_list` builds; the string
  the bytes decode to is `String.ofList` of those characters, and `String.ofList` in force brings
  `String` into force, hence the string support (`EnvFacts.strLit`). `str_lit_delta_step`
  unfolds `String.ofList` (`Red.delta`: its stored definition, level-free by
  `strLitSupported`, so the circuit's instantiation at no levels is the identity), takes a β
  step at a binder whose level the never-zero test accepts (`Red.betaGate`), and continues with
  `whnf_nd`'s reduct; `str_lit_to_ctor_app_or_self` composes `Red.strLit` with it. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open NatAux

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PrimStrAux

/-! ## Heaps and stored nodes -/

/-- A heap that is another one with a cell appended extends it. -/
theorem ext_of_eq_snoc {h m : Heap F} {v : SourceValue F} (hm : m = h ++ [v]) :
    Heap.Extends h m := by
  rw [hm]; exact Heap.Extends.snoc h v

/-- A stored `App` node of two represented terms, at the heap the store produced. -/
theorem tm_store_app' {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h m : Heap F}
    {k : Nat} {Ef Ea : KExpr} {fp ap : SourceValue F}
    (hm : m = h ++ [.construct kexprEnum "App" [fp, ap]])
    (rf : Tm κ d Γ h k Ef fp) (ra : Tm κ d Γ h k Ea ap) :
    Tm κ d Γ m k (.app Ef Ea) (.ptr (.enum kexprEnum) h.length) := by
  subst hm; exact Tm.store_app rf ra

/-- A stored `Nil` level list represents the empty list. -/
theorem repKLevelList_nil_of {m m₁ : Heap F}
    (hm₁ : m₁ = m ++ [.construct klevelListEnum "Nil" []]) :
    RepKLevelList m₁ [] (.ptr (.enum klevelListEnum) m.length) := by
  subst hm₁
  rw [klevelListEnum_eq]
  exact .nil List.getElem?_concat_length

/-- A stored `Nil` level list, up to semantic equality. -/
theorem lvListRep_nil_of {m m₁ : Heap F}
    (hm₁ : m₁ = m ++ [.construct klevelListEnum "Nil" []]) :
    LvListRep m₁ [] (.ptr (.enum klevelListEnum) m.length) :=
  ⟨[], repKLevelList_nil_of hm₁, LvEqList.refl []⟩

/-- The level list `[zero]` as the circuit stores it: a `Zero` node, a `Nil` list, then the
`Cons` cell. -/
theorem repKLevelList_zero_of {h m2 m41 m17 : Heap F}
    (hm12 : m2 = h ++ [.construct klevelEnum "Zero" []])
    (hm49 : m41 = m2 ++ [.construct klevelListEnum "Nil" []])
    (hm27 : m17 = m41 ++ [.construct klevelListEnum "Cons"
      [.ptr (.enum klevelEnum) h.length, .ptr (.enum klevelListEnum) m2.length]]) :
    RepKLevelList m17 [.zero] (.ptr (.enum klevelListEnum) m41.length) := by
  have hz : RepKLevel m41 .zero (.ptr (.enum klevelEnum) h.length) := by
    have z : RepKLevel m2 .zero (.ptr (.enum klevelEnum) h.length) := by
      rw [hm12]; exact (IxVM.Refinement.KernelLevels.RepKLevel.allocZero h).1
    exact z.mono (ext_of_eq_snoc hm49)
  have hn := repKLevelList_nil_of hm49
  have ext := ext_of_eq_snoc hm27
  subst hm27
  rw [klevelListEnum_eq] at hn ext ⊢
  exact .cons List.getElem?_concat_length (hz.mono ext) (hn.mono ext)

/-- **A role's constant**, stored as a `Const` node of the address a role lookup returned: closed,
keyed by the role (the address is bound to it, and the table binds no address twice). -/
theorem tmc_role_const {c : Ctx} (hc : CoreFacts c) {ro : Ix.Kernel.Role} {m h₂ : Heap F}
    {ap lsp : SourceValue F} {a : Bytes.Address} {ls : List KLevel}
    (ra : RepAddr m a ap) (hb : c.t.addressOf? ro = some (ixAddr a))
    (rls : RepKLevelList m ls lsp)
    (hm₂ : h₂ = m ++ [.construct kexprEnum "Const" [ap, lsp]]) :
    c.tmc h₂ (.const (.role ro) ls) (.ptr (.enum kexprEnum) m.length) := by
  subst hm₂
  intro d Γ
  have ext := Heap.Extends.snoc m (.construct kexprEnum "Const" [ap, lsp])
  have hk : c.κ (ixAddr a) = .role ro := keyOf_of_addressOf hc.env.tableWf hb
  rw [← hk]
  exact .const List.getElem?_concat_length (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
    (rls.mono ext) (LvEqList.refl ls)

/-- **A role's constant at the empty level list**: a stored `Nil` level list, then the `Const`
node. -/
theorem tmc_role_const_nil {c : Ctx} (hc : CoreFacts c) {ro : Ix.Kernel.Role} {m m₁ h₂ : Heap F}
    {ap : SourceValue F} {a : Bytes.Address}
    (ra : RepAddr m a ap) (hb : c.t.addressOf? ro = some (ixAddr a))
    (hm₁ : m₁ = m ++ [.construct klevelListEnum "Nil" []])
    (hm₂ : h₂ = m₁ ++ [.construct kexprEnum "Const" [ap, .ptr (.enum klevelListEnum) m.length]]) :
    c.tmc h₂ (.const (.role ro) []) (.ptr (.enum kexprEnum) m₁.length) :=
  tmc_role_const hc (Bytes.repAddressRef_heapMono₂ addrTy (ext_of_eq_snoc hm₁) ra) hb
    (repKLevelList_nil_of hm₁) hm₂

/-! ## Fields and words -/

theorem val_zero_add {n : Nat} (hn : n < PF) : ZMod.val ((0 : F) + (n : F)) = n := by
  rw [zero_add]; exact val_natCast hn

/-- **A word below `2^32`**: its four low bytes, then four zero bytes. -/
theorem u64Value_lt32 {n : Nat} (hn : n < 4294967296) :
    TagN.u64Value n = (.tuple [.field ((n % 256 : Nat) : F), .field ((n / 256 % 256 : Nat) : F),
      .field ((n / 65536 % 256 : Nat) : F), .field ((n / 16777216 % 256 : Nat) : F), .field 0,
      .field 0, .field 0, .field 0] : SourceValue F) := by
  have e4 : n / 4294967296 = 0 := by omega
  have e5 : n / 1099511627776 = 0 := by omega
  have e6 : n / 281474976710656 = 0 := by omega
  have e7 : n / 72057594037927936 = 0 := by omega
  simp only [TagN.u64Value, e4, e5, e6, e7, Nat.zero_mod, Nat.cast_zero]

/-! ## The string support -/

/-- **`String.ofList` is level-free under the string support** (`stringOfListTyOk`). -/
theorem levelParams_of_strLit {env : Ix.Kernel.Env .anon} {cv : Ix.Kernel.ConstantVal .anon}
    {V : KExpr} {hn : Ix.Kernel.ReducibilityHint}
    (hsup : Ix.Kernel.strLitSupported env = true)
    (hfind : env.find? Ix.Kernel.stringOfListName = some (.defnInfo cv V hn)) :
    cv.levelParams = [] := by
  have h4 : Ix.Kernel.stringOfListTyOk (env.find? Ix.Kernel.stringOfListName) = true := by
    unfold Ix.Kernel.strLitSupported at hsup
    simp only [Bool.and_eq_true] at hsup
    first
      | exact hsup.1.1.1.1.1.2
      | tauto
  rw [hfind] at h4
  simp only [Ix.Kernel.stringOfListTyOk, Bool.and_eq_true] at h4
  have h5 : cv.levelParams.isEmpty = true := h4.1
  exact List.isEmpty_iff.mp h5

/-- The node a represented `String.ofList` application loads to: an `App` of a `Const` node, the
constant's address keyed as `String.ofList`, and the argument. -/
theorem app_const_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {L : KExpr} {n : KKey} {e x_f x_list_arg x_caddr w49 : SourceValue F}
    (hE : Tm κ d Γ h 0 (.app (.const n []) L) e)
    (ld12 : loadValue h e = .ok (.construct kexprEnum "App" [x_f, x_list_arg]))
    (ld41 : loadValue h x_f = .ok (.construct kexprEnum "Const" [x_caddr, w49])) :
    ∃ a, n = κ (ixAddr a) ∧ RepAddr h a x_caddr ∧ Tm κ d Γ h 0 L x_list_arg := by
  obtain ⟨Ef, Ea, hEq, hEf, hEa⟩ := hE.app_of_load ld12
  injection hEq with hEf' hEa'
  subst hEf' hEa'
  obtain ⟨a, us, hEq2, ha, -⟩ := hEf.const_of_load ld41
  injection hEq2 with hk hus
  exact ⟨a, hk, ha, hEa⟩

/-- **δ at `String.ofList`**: the constant `get_ci` loads at its key is its stored definition, its
value instantiated at no levels is the value itself (it is level-free under the string support),
and `String.ofList L` unfolds to the value applied to `L`. -/
theorem delta_prefix (c : Ctx) {calls : List (Call F)} (ih : IH c calls)
    (hsup : Ix.Kernel.strLitSupported c.env = true)
    {h m61 m154 m131 : Heap F} {ap p68 x_value v130 w101 w102 w103 w104 : SourceValue F}
    {a : Bytes.Address} {cs74 cs141 : List (Call F)}
    (hlt1 : cs74.length < calls.length) (hlt2 : cs141.length < calls.length)
    (g1 : Good c cs74) (g2 : Good c cs141)
    (hkey : Ix.Kernel.stringOfListName = c.κ (ixAddr a)) (ha : RepAddr h a ap)
    (ev76 : ObsFn W "Ingress::get_ci" [ap] h p68 m61 cs74)
    (ld70 : loadValue m61 p68 = .ok (.construct kciEnum "Defn" [w101, w102, x_value, w103, w104]))
    (hm162 : m154 = m61 ++ [.construct klevelListEnum "Nil" []])
    (ev143 : ObsFn W "KernelLevels::expr_inst_levels"
      [x_value, .ptr (.enum klevelListEnum) m61.length] m154 v130 m131 cs141) :
    ∃ V : KExpr, (∀ Γ, Tm c.κ 0 Γ m131 0 V v130) ∧
      ∀ d L, Red c.env d (.app (.const Ix.Kernel.stringOfListName []) L) (.app V L) := by
  obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) hlt1 ev76 ap a rfl g1 ha
  rw [ld70] at hld
  injection hld with hv
  subst hv
  obtain ⟨cv, V, hn, rfl, -, hV⟩ := CIRep.defn_inv hci
  rw [← hkey] at hfind
  have hlp : cv.levelParams = [] := levelParams_of_strLit hsup hfind
  have hself : V.instantiateLevelParams [] [] = V := by
    have := Ix.Kernel.Expr.instantiateLevelParams_self [] V
    simp only [List.map_nil] at this
    exact this
  have hpos : posOf cv.levelParams V = V := by
    simp only [posOf, posLevels, hlp, List.length_nil, List.range_zero, List.map_nil]
    exact hself
  rw [hpos] at hV
  have e1 := ext_of_eq_snoc hm162
  refine ⟨V, fun Γ => ?_, fun d L => ?_⟩
  · have := ih.get (.subst .expr_inst_levels) hlt2 ev143 x_value _ rfl g2 Γ 0 V []
      (Tm.mono e1 (hV 0 Γ)) (lvListRep_nil_of hm162)
    simp only [List.length_nil, List.range_zero, hself] at this
    exact this
  · have hunf := unfold_const_mkAppN (us := []) [L] hfind (by simp [hlp])
    rw [hlp, hself] at hunf
    exact .delta hunf

end PrimStrAux

/-! ## Constructions -/

/-- `KernelNatPrim::mk_bool`: the constant of `Bool.false` at `g = 0`, else of `Bool.true`, at
the address `role_addr` returns (keyed by the role), at an empty level list. -/
theorem mk_bool_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::mk_bool" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.mk_bool c args h r h' calls := by
  intro rc g hargs good hrc
  subst hargs
  rcases Obs.«KernelNatPrim::mk_bool».obs ev with
    ⟨v23, m26, cs34, v38, m47, cs55, m59, hv14, he19, hm18, ev57, ev36, hm67, hc71⟩ |
    ⟨v84, m87, cs95, v99, m108, cs116, m120, hne72, he80, hm79, ev118, ev97, hm128, hc132⟩
  · -- `0 => Bool.false`
    have hg : g = 0 := Value.field.inj hv14
    subst hc71
    obtain ⟨rfl, hm47⟩ := ih.get (.roles .role_bool_false) (by nat_lt_calls) ev57 rfl
    subst m47
    obtain ⟨a, ha, hb, -⟩ := ih.get (.roles .role_addr) (by nat_lt_calls) ev36 rc .boolFalse rfl
      (good.sub fun x hx => by simp [hx]) hrc
    rw [he19, ite_eq_left hg]
    exact PrimStrAux.tmc_role_const_nil hc ha hb hm67 hm18
  · -- `_ => Bool.true`
    have hg : g ≠ 0 := fun h0 => hne72 (by rw [h0])
    subst hc132
    obtain ⟨rfl, hm108⟩ := ih.get (.roles .role_bool_true) (by nat_lt_calls) ev118 rfl
    subst m108
    obtain ⟨a, ha, hb, -⟩ := ih.get (.roles .role_addr) (by nat_lt_calls) ev97 rc .boolTrue rfl
      (good.sub fun x hx => by simp [hx]) hrc
    rw [he80, ite_eq_right hg]
    exact PrimStrAux.tmc_role_const_nil hc ha hb hm128 hm79

/-- `KernelNatPrim::mk_nat_lit`: a literal node of the (canonical) limbs. -/
theorem mk_nat_lit_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::mk_nat_lit" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.mk_nat_lit c args h r h' calls := by
  intro a hargs good n hn
  subst hargs
  obtain ⟨he5, hm4, -⟩ := Obs.«KernelNatPrim::mk_nat_lit».obs ev
  obtain ⟨limbs, hl, rfl, hcan⟩ := hn
  subst he5 hm4
  intro d Γ
  exact .litNat List.getElem?_concat_length
    (repList_heapMono₂ _ repU64_heapMono₂ (Heap.Extends.snoc _ _) hl) hcan

/-- `KernelNatPrim::np_apply_spine`: the head applied to the spine, one `App` node per
argument. -/
theorem np_apply_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::np_apply_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.np_apply_spine c args h r h' calls := by
  intro hd sp hargs good d Γ H As hH hAs
  subst hargs
  rcases Obs.«KernelNatPrim::np_apply_spine».obs ev with
    ⟨ld12, he21, he22, hc23⟩ | ⟨x_a, x_rest, cs44, m50, ld12, hm58, ev46, hc85⟩
  · -- `Nil`: the head
    obtain rfl := RepList.nil_of_load hAs ld12
    rw [he21, he22]
    exact hH
  · -- `Cons`: apply the head to the first argument, then the rest
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    subst hc85 hm58
    exact ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev46 _ x_rest rfl
      (good.sub fun x hx => by simp [hx]) d Γ (.app H A) As' (Tm.store_app hH hA)
      (TmL.mono (Heap.Extends.snoc _ _) hAs')

/-- `KernelNatPrim::lvls_empty`: `1` exactly at the empty level list (a list semantically equal
to the empty one is empty); nothing allocated. -/
theorem lvls_empty_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::lvls_empty" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.lvls_empty c args h r h' calls := by
  intro lp hargs good us hus
  subst hargs
  obtain ⟨ls, hls, hEq⟩ := hus
  rcases Obs.«KernelNatPrim::lvls_empty».obs ev with
    ⟨ld12, he20, he21, hc22⟩ | ⟨v1, ld12, hne23, he27, he28, hc29⟩
  · -- `Nil`
    have ld' : loadValue h lp =
        .ok (.construct IxVM.Refinement.KernelLevels.klevelListEnum "Nil" []) := by
      rw [← klevelListEnum_eq]; exact ld12
    obtain rfl := RepList.nil_of_load hls ld'
    obtain rfl : us = [] := by
      cases us with
      | nil => rfl
      | cons u us =>
        have h0 := hEq (fun _ => 0)
        simp [Ix.Kernel.Level.EvalEqList] at h0
    exact ⟨by rw [he20, ite_eq_left (rfl : ([] : List KLevel) = [])], he21⟩
  · -- a `Cons` cell
    have hne' : ∀ vs : List (SourceValue F), vs.length = 0 →
        v1 ≠ .construct IxVM.Refinement.KernelLevels.klevelListEnum "Nil" vs := by
      rw [← klevelListEnum_eq]; exact hne23
    have hne := rep_cons_of_not_nil hls ld12 hne'
    have hus : us ≠ [] := by
      rintro rfl
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
      have h0 := hEq (fun _ => 0)
      simp [Ix.Kernel.Level.EvalEqList] at h0
    exact ⟨by rw [he27, ite_eq_right hus], he28⟩

/-! ## The `u32` split -/

/-- `KernelNatPrim::split_u32`: the four base-256 digits, least significant first (a derivation
exists only below `2^32`, by the first `divmod_256`); nothing allocated. -/
theorem split_u32_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::split_u32" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.split_u32 c args h r h' calls := by
  intro x hargs good
  subst hargs
  obtain ⟨m2, cs13, x_b0, x_q1, m48, cs59, x_b1, x_q2, m94, cs105, x_b2, x_q3, m140, cs151, x_b3,
    w175, ev15, ev61, ev107, ev153, he192, he221, hc222⟩ := Obs.«KernelNatPrim::split_u32».obs ev
  subst hc222
  obtain ⟨hx, hr0, hm2⟩ := ih.get (.nat .divmod_256) (by nat_lt_calls) ev15 x 0 rfl
    (good.sub fun y hy => by simp [hy])
  have hxv : ZMod.val x < 4294967296 := by simpa using hx
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr0
  obtain ⟨rfl, rfl⟩ := hr0
  obtain ⟨-, hr1, hm48⟩ := ih.get (.nat .divmod_256) (by nat_lt_calls) ev61 _ 0 rfl
    (good.sub fun y hy => by simp [hy])
  rw [PrimStrAux.val_zero_add (n := ZMod.val x / 256) (by omega)] at hr1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr1
  obtain ⟨rfl, rfl⟩ := hr1
  obtain ⟨-, hr2, hm94⟩ := ih.get (.nat .divmod_256) (by nat_lt_calls) ev107 _ 0 rfl
    (good.sub fun y hy => by simp [hy])
  rw [PrimStrAux.val_zero_add (n := ZMod.val x / 256 / 256) (by omega)] at hr2
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr2
  obtain ⟨rfl, rfl⟩ := hr2
  obtain ⟨-, hr3, hm140⟩ := ih.get (.nat .divmod_256) (by nat_lt_calls) ev153 _ 0 rfl
    (good.sub fun y hy => by simp [hy])
  rw [PrimStrAux.val_zero_add (n := ZMod.val x / 256 / 256 / 256) (by omega)] at hr3
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr3
  obtain ⟨rfl, -⟩ := hr3
  refine ⟨hx, ?_, he221.trans (hm140.trans (hm94.trans (hm48.trans hm2)))⟩
  rw [he192, show ZMod.val x / 256 / 256 / 256 = ZMod.val x / 16777216 by omega,
    show ZMod.val x / 256 / 256 = ZMod.val x / 65536 by omega]

/-- `KernelNatPrim::klimbs_from_g`: the canonical limbs of the value (below `2^32`): the four
digits are the low bytes of one limb holding the value, normalized. -/
theorem klimbs_from_g_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::klimbs_from_g" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.klimbs_from_g c args h r h' calls := by
  intro x hargs good
  subst hargs
  obtain ⟨m2, cs13, x_rb0, x_rb1, x_rb2, x_rb3, v50, m51, cs61, v72, m73, cs83, v94, m95, cs105,
    v116, m117, cs127, v150, m159, x164, y165, m166, x172, y173, m174, x180, y181, m182, cs191,
    y203, cs213, y225, cs235, y247, cs257, cs272, m277, m360, ev15, ev63, ev85, ev107, ev129,
    ev193, ev215, op209, op187, ev237, op231, op179, ev259, op253, op171, heq268, hm285, hm368,
    ev274, hc372⟩ := Obs.«KernelNatPrim::klimbs_from_g».obs ev
  subst hc372
  obtain ⟨hx, hr, -⟩ := ih.get (.nat .split_u32) (by nat_lt_calls) ev15 x rfl
    (good.sub fun y hy => by simp [hy])
  have hxv : ZMod.val x < 4294967296 := by simpa using hx
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
  obtain ⟨rfl, -, -⟩ := from_field ev63
  obtain ⟨rfl, -, -⟩ := from_field ev85
  obtain ⟨rfl, -, -⟩ := from_field ev107
  obtain ⟨rfl, -, -⟩ := from_field ev129
  subst hm285 hm368
  have hw := Lib.repU64_ofNatLT m159 (m := ZMod.val x) (by omega)
  rw [PrimStrAux.u64Value_lt32 hxv] at hw
  have hl := lrep_store_cons hw (lrep_store_nil m159)
  refine ⟨hx, ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev274 _ rfl
    (good.sub fun y hy => by simp [hy]) _ ⟨_, hl, ?_⟩⟩
  rw [limbsVal_cons, limbsVal_nil, UInt64.toNat_ofNatLT]
  omega

/-! ## String literals -/

/-- `KernelNatPrim::str_lit_to_ctor`: the closed constructor form of the string the bytes decode
to, over the constants of the roles `role_used_implicitly` returns; `String.ofList` in force
brings `String` into force, hence the string support. -/
theorem str_lit_to_ctor_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::str_lit_to_ctor" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.str_lit_to_ctor c args h r h' calls := by
  intro rc bp hargs good hrc bs s hbs hs
  subst hargs
  obtain ⟨m2, m17, m41, m54, v68, m71, cs79, v83, m92, cs100, m111, v125, m128, cs136, v140,
    m149, cs157, m168, v182, m185, cs193, v197, m206, cs214, m218, m231, v245, m248, cs256, v260,
    m269, cs277, m281, m294, v308, m311, cs319, v323, m332, cs340, m344, m357, m388, v418, m419,
    cs429, hm12, hm27, hm49, hm64, ev102, ev81, hm121, ev159, ev138, hm178, ev216, ev195, hm226,
    hm241, ev279, ev258, hm289, hm304, ev342, ev321, hm352, hm367, hm398, ev431, he468, hm467,
    hc488⟩ := Obs.«KernelNatPrim::str_lit_to_ctor».obs ev
  subst hc488
  -- `List.nil`, at the level list `[zero]`
  have e1 := PrimStrAux.ext_of_eq_snoc hm12
  have e2 := PrimStrAux.ext_of_eq_snoc hm49
  have e3 := PrimStrAux.ext_of_eq_snoc hm27
  obtain ⟨rfl, hm92⟩ := ih.get (.roles .role_list_nil) (by nat_lt_calls) ev102 rfl
  subst m92
  have E17 : Heap.Extends h m17 := e1.trans (e2.trans e3)
  obtain ⟨aN, haN, hbN, -⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev81 rc
    .listNil rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E17 hrc)
  have e4 := ObsFn.heap_extends ev81
  have e5 := PrimStrAux.ext_of_eq_snoc hm64
  -- `List.cons`, at the same level list
  obtain ⟨rfl, hm149⟩ := ih.get (.roles .role_list_cons) (by nat_lt_calls) ev159 rfl
  subst m149
  have E54 : Heap.Extends h m54 := E17.trans (e4.trans e5)
  obtain ⟨aC, haC, hbC, -⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev138 rc
    .listCons rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E54 hrc)
  have e6 := ObsFn.heap_extends ev138
  have e7 := PrimStrAux.ext_of_eq_snoc hm121
  -- `Char`
  obtain ⟨rfl, hm206⟩ := ih.get (.roles .role_char) (by nat_lt_calls) ev216 rfl
  subst m206
  have E111 : Heap.Extends h m111 := E54.trans (e6.trans e7)
  obtain ⟨aCh, haCh, hbCh, -⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev195 rc
    .char rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E111 hrc)
  have e8 := ObsFn.heap_extends ev195
  have e9 := PrimStrAux.ext_of_eq_snoc hm226
  have e10 := PrimStrAux.ext_of_eq_snoc hm178
  -- `Char.ofNat`
  obtain ⟨rfl, hm269⟩ := ih.get (.roles .role_char_of_nat) (by nat_lt_calls) ev279 rfl
  subst m269
  have E168 : Heap.Extends h m168 := E111.trans (e8.trans (e9.trans e10))
  obtain ⟨aK, haK, hbK, -⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev258 rc
    .charOfNat rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E168 hrc)
  have e11 := ObsFn.heap_extends ev258
  have e12 := PrimStrAux.ext_of_eq_snoc hm289
  have e13 := PrimStrAux.ext_of_eq_snoc hm241
  -- `String.ofList`
  obtain ⟨rfl, hm332⟩ := ih.get (.roles .role_string_of_list) (by nat_lt_calls) ev342 rfl
  subst m332
  have E231 : Heap.Extends h m231 := E168.trans (e11.trans (e12.trans e13))
  obtain ⟨aS, haS, hbS, hfS⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev321 rc
    .stringOfList rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E231 hrc)
  have e14 := ObsFn.heap_extends ev321
  have e15 := PrimStrAux.ext_of_eq_snoc hm352
  have e16 := PrimStrAux.ext_of_eq_snoc hm304
  have e17 := PrimStrAux.ext_of_eq_snoc hm367
  have e18 := PrimStrAux.ext_of_eq_snoc hm398
  have E388 : Heap.Extends h m388 :=
    E231.trans (e14.trans (e15.trans (e16.trans (e17.trans e18))))
  -- the five constants
  have hls := PrimStrAux.repKLevelList_zero_of hm12 hm49 hm27
  have nilC := PrimStrAux.tmc_role_const hc haN hbN (hls.mono e4) hm64
  have consC := PrimStrAux.tmc_role_const hc haC hbC (hls.mono (e4.trans (e5.trans e6))) hm121
  have charC := PrimStrAux.tmc_role_const_nil hc haCh hbCh hm226 hm178
  have conC := PrimStrAux.tmc_role_const_nil hc haK hbK hm289 hm241
  have strC := PrimStrAux.tmc_role_const_nil hc haS hbS hm352 hm304
  -- the characters
  obtain ⟨cs, hcs, hlist⟩ := ih.get (.nat .build_char_list) (by nat_lt_calls) ev431 bp _ _ _ rfl
    (good.sub fun x hx => by simp [hx]) bs (Bytes.repByteStream_heapMono₂ _ E388 hbs)
  have e19 := ObsFn.heap_extends ev431
  obtain rfl := Utf8Aux.strBytes_eq_ofList hs hcs
  refine ⟨hc.env.strLit (Ctx.inForce_of_block_or_dep hc.env.tableWf hfS (.inr (by decide))), ?_⟩
  rw [Utf8Aux.strLitToConstructor_ofList, he468]
  intro d Γ
  have X168 : Heap.Extends m168 m294 :=
    e11.trans (e12.trans (e13.trans (e14.trans (e15.trans e16))))
  have hnil : c.tm d Γ m357 (.app (.const (.role .listNil) [.zero]) (.const (.role .char) []))
      (.ptr (.enum kexprEnum) m294.length) :=
    PrimStrAux.tm_store_app' hm367
      (Tm.mono (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans X168))))) (nilC d Γ))
      (Tm.mono X168 (charC d Γ))
  have hcons : c.tm d Γ m388 (.app (.const (.role .listCons) [.zero]) (.const (.role .char) []))
      (.ptr (.enum kexprEnum) m357.length) :=
    PrimStrAux.tm_store_app' hm398
      (Tm.mono (e8.trans (e9.trans (e10.trans (X168.trans e17)))) (consC d Γ))
      (Tm.mono (X168.trans e17) (charC d Γ))
  exact PrimStrAux.tm_store_app' hm467 (Tm.mono (e17.trans (e18.trans e19)) (strC d Γ))
    (hlist d Γ _ _ _ (Tm.mono e18 hnil) hcons
      (Tm.mono (e14.trans (e15.trans (e16.trans (e17.trans e18)))) (conC d Γ)))

/-- `KernelNatPrim::str_lit_delta_step` on `String.ofList L`: δ at its stored definition, a β
step at a binder whose level the never-zero test accepts (or none), then `whnf_nd`'s reduct. -/
theorem str_lit_delta_step_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::str_lit_delta_step" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.str_lit_delta_step c args h r h' calls := by
  intro rc e types hargs good hrc hsup d Γ htypes L hE
  subst hargs
  rcases Obs.«KernelNatPrim::str_lit_delta_step».obs ev with
    ⟨x_f, x_list_arg, x_caddr, w49, m61, p68, cs74, w101, w102, x_value, w103, w104, v130, m131,
      cs141, m154, w185, x_lam_body, x_bl, m202, cs213, cs231, v235, m245, cs253, ld12, ld41,
      ev76, ld70, hm162, ev143, ld177, ev215, ev255, ev233, hc286⟩ |
    ⟨x_f, x_list_arg, x_caddr, w49, m61, p68, cs74, w101, w102, x_value, w103, w104, v130, m131,
      cs141, m154, w185, x_lam_body, x_bl, v201, m202, cs213, cs294, m308, ld12, ld41, ev76, ld70,
      hm162, ev143, ld177, ev215, hne287, hm316, ev296, hc343⟩ |
    ⟨x_f, x_list_arg, x_caddr, w49, m61, p68, cs74, w101, w102, x_value, w103, w104, v130, m131,
      cs141, m154, v166, cs351, m365, ld12, ld41, ev76, ld70, hm162, ev143, ld177, hne344, hm373,
      ev353, hc400⟩ |
    ⟨x_f, x_list_arg, x_caddr, w49, v60, m61, p68, cs74, ld12, ld41, ev76, ld70, hne401, he406,
      he407, hc408⟩ |
    ⟨x_f, x_list_arg, v30, ld12, ld41, hne409, he414, he415, hc416⟩ |
    ⟨v1, ld12, hne417, he422, he423, hc424⟩
  · -- a definition whose value is a `λ` at a never-zero level: δ, β, `whnf_nd`
    subst hc286
    obtain ⟨a, hk, ha, hL⟩ := PrimStrAux.app_const_of_load hE ld12 ld41
    obtain ⟨V, hV, hred⟩ := PrimStrAux.delta_prefix c ih hsup (by nat_lt_calls) (by nat_lt_calls)
      (good.sub fun x hx => by simp [hx]) (good.sub fun x hx => by simp [hx]) hk ha ev76 ld70
      hm162 ev143
    obtain ⟨T, B, ℓ, rfl, -, hB, hℓ⟩ := (hV Γ).lam_of_load ld177
    obtain ⟨hr1, hm202⟩ := ih.get (.levelOps .level_is_not_zero) (by nat_lt_calls) ev215 x_bl rfl
      ℓ hℓ
    subst m202
    have hnz : ℓ.isNeverZero = true := by
      by_contra hn
      rw [ite_eq_right hn] at hr1
      exact NatAux.field_one_ne_zero hr1
    have hnever : (bmeta ℓ).pw.isNever = true := by
      rw [bmeta_of_isNeverZero hnz]; exact nbMeta_isNever
    have ext : Heap.Extends h m131 := (ObsFn.heap_extends ev76).trans
      ((PrimStrAux.ext_of_eq_snoc hm162).trans (ObsFn.heap_extends ev143))
    have hB' : c.tmk d Γ (ZMod.val (0 : F) + 1) m131 B x_lam_body := by
      simp only [ZMod.val_zero]; exact Tm.of_depth_zero hB d
    have hinst := ih.get (.subst .expr_inst1) (by nat_lt_calls) ev255 x_lam_body x_list_arg 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B L hB' (Tm.mono ext hL)
    simp only [ZMod.val_zero] at hinst
    have ext' := ext.trans (ObsFn.heap_extends ev255)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by nat_lt_calls) ev233 rc v235 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) _
      hinst
    exact ⟨E', hE', .trans (hred d L) (.trans (.betaGate hnever) hred')⟩
  · -- a `λ` at a level the test does not accept: δ, then `whnf_nd` of the application
    subst hc343
    obtain ⟨a, hk, ha, hL⟩ := PrimStrAux.app_const_of_load hE ld12 ld41
    obtain ⟨V, hV, hred⟩ := PrimStrAux.delta_prefix c ih hsup (by nat_lt_calls) (by nat_lt_calls)
      (good.sub fun x hx => by simp [hx]) (good.sub fun x hx => by simp [hx]) hk ha ev76 ld70
      hm162 ev143
    have e3 := ObsFn.heap_extends ev215
    have ext : Heap.Extends h m202 := (ObsFn.heap_extends ev76).trans
      ((PrimStrAux.ext_of_eq_snoc hm162).trans ((ObsFn.heap_extends ev143).trans e3))
    have happ : c.tm d Γ m308 (.app V L) (.ptr (.enum kexprEnum) m202.length) :=
      PrimStrAux.tm_store_app' hm316 (Tm.mono e3 ((hV Γ).of_depth_zero d)) (Tm.mono ext hL)
    have ext' := ext.trans (PrimStrAux.ext_of_eq_snoc hm316)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by nat_lt_calls) ev296 rc _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) _
      happ
    exact ⟨E', hE', .trans (hred d L) hred'⟩
  · -- a value that is not a `λ`: δ, then `whnf_nd` of the application
    subst hc400
    obtain ⟨a, hk, ha, hL⟩ := PrimStrAux.app_const_of_load hE ld12 ld41
    obtain ⟨V, hV, hred⟩ := PrimStrAux.delta_prefix c ih hsup (by nat_lt_calls) (by nat_lt_calls)
      (good.sub fun x hx => by simp [hx]) (good.sub fun x hx => by simp [hx]) hk ha ev76 ld70
      hm162 ev143
    have ext : Heap.Extends h m131 := (ObsFn.heap_extends ev76).trans
      ((PrimStrAux.ext_of_eq_snoc hm162).trans (ObsFn.heap_extends ev143))
    have happ : c.tm d Γ m365 (.app V L) (.ptr (.enum kexprEnum) m131.length) :=
      PrimStrAux.tm_store_app' hm373 ((hV Γ).of_depth_zero d) (Tm.mono ext hL)
    have ext' := ext.trans (PrimStrAux.ext_of_eq_snoc hm373)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd) (by nat_lt_calls) ev353 rc _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) _
      happ
    exact ⟨E', hE', .trans (hred d L) hred'⟩
  · -- not a definition: the term itself
    rw [he406, he407]
    exact ⟨_, Tm.mono (ObsFn.heap_extends ev76) hE, .refl⟩
  · -- the function is not a constant: the term itself
    rw [he414, he415]
    exact ⟨_, hE, .refl⟩
  · -- not an application: the term itself
    rw [he422, he423]
    exact ⟨_, hE, .refl⟩

/-- `KernelNatPrim::str_lit_to_ctor_app_or_self`: a string literal expands to its constructor form
(`Red.strLit`, under the support `str_lit_to_ctor` gives), then `str_lit_delta_step`'s reduct;
any other term is itself. -/
theorem str_lit_to_ctor_app_or_self_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::str_lit_to_ctor_app_or_self" args h r h' calls)
    (ih : IH c calls) :
    Specs.Nat.str_lit_to_ctor_app_or_self c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelNatPrim::str_lit_to_ctor_app_or_self».obs ev with
    ⟨x_bs, cs49, v53, m63, cs71, ld12, ev73, ev51, hc97⟩ |
    ⟨x_lit, ld12, hne98, he103, he104, hc105⟩ |
    ⟨v1, ld12, hne106, he111, he112, hc113⟩
  · -- a string literal
    subst hc97
    rcases hE.lit_of_load ld12 with ⟨lp, limbs, hx, -⟩ | ⟨bp, bytes, s, hx, hbs, hs, rfl⟩
    · injection hx with h1 h2 h3
      exact absurd h2 (by decide)
    · injection hx with h1 h2 h3
      injection h3 with h4 h5
      subst h4
      obtain ⟨hsup, hctor⟩ := ih.get (.nat .str_lit_to_ctor) (by nat_lt_calls) ev73 rc x_bs rfl
        (good.sub fun x hx => by simp [hx]) hrc bytes s hbs hs
      obtain ⟨L, hL⟩ : ∃ L : KExpr, Ix.Kernel.strLitToConstructor (md := .anon) s =
          .app (.const Ix.Kernel.stringOfListName []) L := ⟨_, rfl⟩
      rw [hL] at hctor
      have e1 := ObsFn.heap_extends ev73
      obtain ⟨E', hE', hred⟩ := ih.get (.nat .str_lit_delta_step) (by nat_lt_calls) ev51 rc v53
        types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hsup d Γ
        (types_mono e1 htypes) L (hctor d Γ)
      have h1 : Ix.Kernel.Rules.Red c.env d (.lit (.strVal s))
          (.app (.const Ix.Kernel.stringOfListName []) L) := by
        rw [← hL]; exact .strLit hsup
      exact ⟨E', hE', .trans h1 hred⟩
  · -- another literal: itself
    rw [he103, he104]
    exact ⟨E, hE, .refl⟩
  · -- not a literal: itself
    rw [he111, he112]
    exact ⟨E, hE, .refl⟩

end IxVM.Refinement.Core
