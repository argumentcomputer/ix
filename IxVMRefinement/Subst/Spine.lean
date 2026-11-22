import IxVMRefinement.Subst.Ctx
import IxVMRefinement.Levels.Smart
import IxVMRefinement.Core.SpineChain
import IxVMRefinement.Obs.KernelLevels

/-! # Spines and level instantiation: `collect_spine`, `expr_inst_levels(_walk)`

`collect_spine` splits an application into its head and its arguments (`mkAppN`).
`expr_inst_levels` substitutes the list's levels for the positional level parameters, through
`level_inst_params` and `level_list_inst` (whose results the level slice proves:
`levelInstParams_obs`, `levelListInst_obs`). Levels are related up to semantic equality
(`lvEq_subst`); a binder's datum is the zero-ness of its stored level, and zero-ness commutes
with substitution (`zeronessOf_subst`), so the image's binder data are exactly the kernel's. The
term is read at opening depth `0`, where it has no opened variable. -/

namespace IxVM.Refinement.Core.SubstAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency (Bounded)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList substLevel substLevelList)

set_option linter.unusedVariables false

local macro "lt_calls" : term => `(by simp <;> omega)
local macro "sub_calls" : term => `(fun _ hx => by simp [hx])

/-! ## `collect_spine` -/

theorem ksnoc {α : Type} {R : Heap F → α → SourceValue F → Prop} (hR : HeapMono₂ R)
    {xs : List α} {x : α} {l v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>» [l, v] h r h' cs)
    (hl : RepList kexprListEnum R h xs l) (hx : R h x v) :
    RepList kexprListEnum R h' (xs ++ [x]) r := by
  have ev' : ObsFn W (Instance.mk "Lists::snoc" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l, v] h r h' cs := by
    rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      R h xs l := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl
  have := Lib.Lists.snoc_spec hR ev' hl' hx
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at this
  exact this

private theorem spineChain_tm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat}
    {h : Heap F} {e hd : SourceValue F} {ps : List (SourceValue F)}
    (sc : SpineChain h e hd ps) :
    ∀ {E : KExpr}, Tm κ d Γ h k E e →
      ∃ H As, Tm κ d Γ h k H hd ∧
        List.Forall₂ (fun A p => Tm κ d Γ h k A p) As ps ∧
        E = Ix.Kernel.Expr.mkAppN H As := by
  induction sc with
  | head _ _ =>
    intro E hE
    exact ⟨E, [], hE, .nil, rfl⟩
  | app ld _ ih =>
    intro E hE
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    obtain ⟨H, As, hH, hAs, rfl⟩ := ih hf
    exact ⟨H, As ++ [Ea], hH, forall₂_append hAs (.cons ha .nil), (mkAppN_snoc As H Ea).symm⟩

theorem g_collect_spine (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" args h r h' calls) (ih : GIH κ calls) :
    G.collect_spine κ args h r h' calls := by
  intro e hargs bd d Γ k E hE
  subst hargs
  obtain ⟨hd, sp, ps, rfl, hch, -, hrep⟩ := collect_spine_chain ev
  obtain ⟨H, As, hH, hAs, hmk⟩ := spineChain_tm (hch.mono ev.heap_extends) (hE.mono ev.heap_extends)
  exact ⟨hd, sp, H, As, rfl, hH, repList_of_eq_forall₂ hrep hAs, hmk⟩

/-! ## Level arithmetic -/

theorem evalEqList_length {φ : Ix.Kernel.LevelParam → Nat} :
    ∀ {us ls : List KLevel}, Ix.Kernel.Level.EvalEqList φ us ls → us.length = ls.length
  | [], [], _ => rfl
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, _ :: _, h => by simp [evalEqList_length h.2]

theorem substFn_congr {φ : Ix.Kernel.LevelParam → Nat} :
    ∀ {us ls : List KLevel}, Ix.Kernel.Level.EvalEqList φ us ls →
      ∀ (ks : List Ix.Kernel.LevelParam) (n : Ix.Kernel.LevelParam),
        Ix.Kernel.Level.substFn φ ks us n = Ix.Kernel.Level.substFn φ ks ls n
  | [], [], _, ks, n => rfl
  | [], _ :: _, h, _, _ => False.elim h
  | _ :: _, [], h, _, _ => False.elim h
  | u :: us, l :: ls, h, ks, n => by
    cases ks with
    | nil => rfl
    | cons k ks =>
      simp only [Ix.Kernel.Level.substFn, h.1, substFn_congr h.2 ks n]

/-- **Substitution respects semantic equality**, and IxVM's `substLevel` is the kernel's
substitution at the positional parameters. -/
theorem lvEq_subst {u l : KLevel} {us ls : List KLevel} (hu : LvEq u l) (hus : LvEqList us ls) :
    LvEq (Ix.Kernel.Level.subst (List.range us.length) us u) (substLevel l ls) := by
  intro φ
  have hlen : us.length = ls.length := evalEqList_length (hus φ)
  rw [KernelLevels.eval_substLevel_eq_subst, Ix.Kernel.Level.eval_subst,
    Ix.Kernel.Level.eval_subst, hlen, hu (Ix.Kernel.Level.substFn φ (List.range ls.length) us)]
  congr 1
  funext n
  exact substFn_congr (hus φ) _ n

theorem lvEqList_subst : ∀ {us' ls' : List KLevel}, LvEqList us' ls' →
    ∀ {us ls : List KLevel}, LvEqList us ls →
      LvEqList (us'.map (Ix.Kernel.Level.subst (List.range us.length) us))
        (substLevelList ls' ls)
  | [], [], _, _, _, _ => fun _ => trivial
  | [], _ :: _, h', _, _, _ => False.elim (h' (fun _ => 0))
  | _ :: _, [], h', _, _, _ => False.elim (h' (fun _ => 0))
  | u :: us', l :: ls', h', us, ls, hus => fun φ =>
    ⟨lvEq_subst (fun ψ => (h' ψ).1) hus φ, lvEqList_subst (fun ψ => (h' ψ).2) hus φ⟩

theorem level_subst_nil : ∀ u : KLevel, Ix.Kernel.Level.subst [] [] u = u := by
  intro u
  induction u <;> simp_all [Ix.Kernel.Level.subst, Ix.Kernel.Level.subst.go]

/-- A binder's datum after substitution. -/
theorem bmeta_subst {ℓ : KLevel} {us ls : List KLevel} (hul : LvEqList us ls) :
    ({ bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw } :
      Ix.Kernel.BinderMeta) = bmeta (substLevel ℓ ls) := by
  have hz : (substLevel ℓ ls).zeronessOf =
      Ix.Kernel.Level.substPW (List.range us.length) us ℓ.zeronessOf := by
    rw [← Ix.Kernel.Level.zeronessOf_subst]
    exact (zeronessOf_congr (lvEq_subst (LvEq.refl ℓ) hul)).symm
  show ({ bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us ℓ.zeronessOf } :
      Ix.Kernel.BinderMeta) = { pw := (substLevel ℓ ls).zeronessOf }
  rw [hz]; rfl

theorem bmeta_subst_nil {ℓ : KLevel} :
    ({ bmeta ℓ with pw := Ix.Kernel.Level.substPW [] [] (bmeta ℓ).pw } : Ix.Kernel.BinderMeta) =
      bmeta ℓ := by
  have hz : Ix.Kernel.Level.substPW [] [] ℓ.zeronessOf = ℓ.zeronessOf := by
    rw [← Ix.Kernel.Level.zeronessOf_subst, level_subst_nil]
  show ({ bmeta ℓ with pw := Ix.Kernel.Level.substPW [] [] ℓ.zeronessOf } :
      Ix.Kernel.BinderMeta) = { pw := ℓ.zeronessOf }
  rw [hz]; rfl

/-- **Instantiating no parameter changes no image at opening depth `0`.** -/
theorem tm_ilp_nil {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h k E p) :
    E.instantiateLevelParams [] [] = E := by
  induction rep with
  | bvarLocal => rfl
  | bvarFree _ _ _ hd => omega
  | sort => simp [Ix.Kernel.Expr.instantiateLevelParams, level_subst_nil]
  | const =>
    have hid : Ix.Kernel.Level.subst [] [] = id := funext level_subst_nil
    simp [Ix.Kernel.Expr.instantiateLevelParams, hid]
  | app _ _ _ ihf iha => simp [Ix.Kernel.Expr.instantiateLevelParams, ihf, iha]
  | lam _ _ _ _ iht ihb =>
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht, ihb, bmeta_subst_nil]
  | forallE _ _ _ _ iht ihb =>
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht, ihb, bmeta_subst_nil]
  | letE _ _ _ _ _ ihv ihb => rw [ilp_instShift, ihv, ihb]
  | litNat => rfl
  | litStr => rfl
  | proj _ _ _ ihe => simp [Ix.Kernel.Expr.instantiateLevelParams, ihe]

/-! ## `expr_has_level_param` and `expr_inst_levels` -/

/-- **`expr_has_level_param` never allocates, returns `0` or `1`, and `0` guarantees `Tm` is
preserved under arbitrary level parameter instantiation without modifying the heap node.** -/
theorem exprHasLevelParam_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {E : KExpr} {e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelLevels::expr_has_level_param" [e] h r h' cs)
    (hE : Tm κ 0 Γ h k E e) :
    h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 0 → ∀ us, Tm κ 0 Γ h k (E.instantiateLevelParams (List.range us.length) us) e) := by
  cases Obs.«KernelLevels::expr_has_level_param».obs ev with
  | BVar w ld hr hm hc =>
    subst hr hm
    obtain ⟨i, rfl, -, hcase⟩ := Tm.bvar_of_load hE ld
    rcases hcase with ⟨_, rfl⟩ | ⟨_, hd, _⟩
    · exact ⟨rfl, .inl rfl, fun _ _ => hE⟩
    · omega
  | Lit w ld hr hm hc =>
    subst hr hm
    rcases Tm.lit_of_load hE ld with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
      exact ⟨rfl, .inl rfl, fun _ _ => hE⟩
  | Srt x_l cs1 ld ev1 hc =>
    cases hE with
    | sort cell rl hu =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs; injection hxs with h1 _; subst h1
      obtain ⟨hh', h01, h0⟩ := IxVM.Refinement.Levels.levelHasParam_obs ev1 rl
      refine ⟨hh', h01, fun hr us => ?_⟩
      obtain ⟨-, hsub⟩ := h0 hr us
      have hlv := lvEq_subst hu (LvEqList.refl us)
      rw [hsub] at hlv
      exact .sort cell rl hlv
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | const cell _ _ _ | app cell _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | Const w x_lvls cs1 ld ev1 hc =>
    cases hE with
    | const cell ra rls hus =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs
      injection hxs with _ hxs; injection hxs with h2 _; subst h2
      obtain ⟨hh', h01, h0⟩ := IxVM.Refinement.Levels.levelListHasParam_obs ev1 rls
      refine ⟨hh', h01, fun hr us => ?_⟩
      obtain ⟨-, hsub⟩ := h0 hr us
      have hlv := lvEqList_subst hus (LvEqList.refl us)
      rw [hsub] at hlv
      exact .const cell ra rls hlv
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | App_n1 x_f x_a m1 cs1 ld ev1 hr hm hc =>
    cases hE with
    | app cell hf ha =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs
      injection hxs with h1 hxs; injection hxs with h2 _; subst h1 h2
      obtain ⟨hm1, -, -⟩ := exprHasLevelParam_tm ev1 hf
      subst hm1 hr hm
      exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | App_other x_f x_a v1 m1 cs1 cs2 ld ev1 hne1 ev2 hc =>
    cases hE with
    | app cell hf ha =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs
      injection hxs with h1 hxs; injection hxs with h2 _; subst h1 h2
      obtain ⟨hm1, h01f, h0f⟩ := exprHasLevelParam_tm ev1 hf
      subst hm1
      have hv1 : v1 = .field 0 := h01f.resolve_right hne1
      obtain ⟨hh', h01a, h0a⟩ := exprHasLevelParam_tm ev2 ha
      refine ⟨hh', h01a, fun hr us => ?_⟩
      exact .app cell (h0f hv1 us) (h0a hr us)
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | Lam x_ty x_body x_bl cs1 ld evb hc =>
    cases hE with
    | lam cell ht hb hl =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs
      injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
      cases Obs.«KernelLevels::expr_has_level_param_binder».obs evb with
      | n1 m1 csb evl hr hm hcb =>
        obtain ⟨hm1, -, -⟩ := IxVM.Refinement.Levels.levelHasParam_obs evl hl
        subst hm1 hr hm
        exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
      | other_n1 v1 m1 csb m2 cst evl hne1 evt hr hm hcb =>
        obtain ⟨hm1, -, -⟩ := IxVM.Refinement.Levels.levelHasParam_obs evl hl
        subst hm1
        obtain ⟨hm2, -, -⟩ := exprHasLevelParam_tm evt ht
        subst hm2 hr hm
        exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
      | other_other v1 m1 csb v2 m2 cst cs3 evl hne1 evt hne2 evbd hcb =>
        obtain ⟨hm1, h01l, h0l⟩ := IxVM.Refinement.Levels.levelHasParam_obs evl hl
        subst hm1
        have hv1 : v1 = .field 0 := h01l.resolve_right hne1
        obtain ⟨hm2, h01t, h0t⟩ := exprHasLevelParam_tm evt ht
        subst hm2
        have hv2 : v2 = .field 0 := h01t.resolve_right hne2
        obtain ⟨hh', h01b, h0b⟩ := exprHasLevelParam_tm evbd hb
        refine ⟨hh', h01b, fun hr us => ?_⟩
        obtain ⟨-, hsubl⟩ := h0l hv1 us
        show Tm κ 0 Γ _ k (.lam (_ ) (_)
          { bmeta _ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta _).pw }) _
        rw [bmeta_subst (LvEqList.refl us), hsubl]
        exact .lam cell (h0t hv2 us) (h0b hr us) hl
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | Forall x_ty x_body x_bl cs1 ld evb hc =>
    cases hE with
    | forallE cell ht hb hl =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs
      injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
      cases Obs.«KernelLevels::expr_has_level_param_binder».obs evb with
      | n1 m1 csb evl hr hm hcb =>
        obtain ⟨hm1, -, -⟩ := IxVM.Refinement.Levels.levelHasParam_obs evl hl
        subst hm1 hr hm
        exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
      | other_n1 v1 m1 csb m2 cst evl hne1 evt hr hm hcb =>
        obtain ⟨hm1, -, -⟩ := IxVM.Refinement.Levels.levelHasParam_obs evl hl
        subst hm1
        obtain ⟨hm2, -, -⟩ := exprHasLevelParam_tm evt ht
        subst hm2 hr hm
        exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
      | other_other v1 m1 csb v2 m2 cst cs3 evl hne1 evt hne2 evbd hcb =>
        obtain ⟨hm1, h01l, h0l⟩ := IxVM.Refinement.Levels.levelHasParam_obs evl hl
        subst hm1
        have hv1 : v1 = .field 0 := h01l.resolve_right hne1
        obtain ⟨hm2, h01t, h0t⟩ := exprHasLevelParam_tm evt ht
        subst hm2
        have hv2 : v2 = .field 0 := h01t.resolve_right hne2
        obtain ⟨hh', h01b, h0b⟩ := exprHasLevelParam_tm evbd hb
        refine ⟨hh', h01b, fun hr us => ?_⟩
        obtain ⟨-, hsubl⟩ := h0l hv1 us
        show Tm κ 0 Γ _ k (.forallE (_ ) (_)
          { bmeta _ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta _).pw }) _
        rw [bmeta_subst (LvEqList.refl us), hsubl]
        exact .forallE cell (h0t hv2 us) (h0b hr us) hl
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | Let x_ty x_val x_body cs1 ld evl hc =>
    cases hE with
    | letE cell ht hv hb =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv'; injection hv' with _ _ hxs
      injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
      cases Obs.«KernelLevels::expr_has_level_param_let».obs evl with
      | n1 m1 cst evt hr hm hcl =>
        obtain ⟨hm1, -, -⟩ := exprHasLevelParam_tm evt ht
        subst hm1 hr hm
        exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
      | other_n1 v1 m1 cst m2 csv evt hne1 evv hr hm hcl =>
        obtain ⟨hm1, -, -⟩ := exprHasLevelParam_tm evt ht
        subst hm1
        obtain ⟨hm2, -, -⟩ := exprHasLevelParam_tm evv hv
        subst hm2 hr hm
        exact ⟨rfl, .inr rfl, fun h10 => absurd (Value.field.inj h10) one_ne_zero⟩
      | other_other v1 m1 cst v2 m2 csv cs3 evt hne1 evv hne2 evbd hcl =>
        obtain ⟨hm1, h01t, h0t⟩ := exprHasLevelParam_tm evt ht
        subst hm1
        have hv1 : v1 = .field 0 := h01t.resolve_right hne1
        obtain ⟨hm2, h01v, h0v⟩ := exprHasLevelParam_tm evv hv
        subst hm2
        have hv2 : v2 = .field 0 := h01v.resolve_right hne2
        obtain ⟨hh', h01b, h0b⟩ := exprHasLevelParam_tm evbd hb
        refine ⟨hh', h01b, fun hr us => ?_⟩
        rw [ilp_instShift]
        exact .letE cell (h0t hv1 us) (h0v hv2 us) (h0b hr us)
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
  | Proj w1 w2 x_e1 cs1 ld ev1 hc =>
    cases hE with
    | proj cell ra hes =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hxs
      injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with h3 _; subst h3
      obtain ⟨hh', h01, h0⟩ := exprHasLevelParam_tm ev1 hes
      refine ⟨hh', h01, fun hr us => ?_⟩
      exact .proj cell ra (h0 hr us)
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
    | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
    | litNat cell _ _ | litStr cell _ _ =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc' _; exact absurd hc' (by decide)
termination_by cs.length
decreasing_by
  all_goals
    try subst hc
    try subst hcb
    try subst hcl
    simp only [List.length_cons, List.length_append]
    omega

theorem g_expr_inst_levels_walk (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::expr_inst_levels_walk" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_levels_walk κ args h r h' calls := by
  intro e params hargs bd Γ k E us hE hus
  subst hargs
  obtain ⟨ls, hls, hul⟩ := hus
  match Obs.«KernelLevels::expr_inst_levels_walk».obs ev with
  | .BVar (ld12 := ld) (he_wafvjlei := hr) (he_iewaezri := hm) .. =>
    subst hr hm
    obtain ⟨i, rfl, hsm, hcase⟩ := Tm.bvar_of_load hE ld
    rcases hcase with ⟨_, rfl⟩ | ⟨_, hd, _⟩
    · exact hE
    · omega
  | .Srt (ld12 := ld) (ev74 := e1) (he58 := hr) (hm57 := hm) (hc91 := hc) .. =>
    subst hc hr hm
    obtain ⟨u, rfl, l, rl, hu⟩ := Tm.sort_of_load hE ld
    obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e1 (bounded_sub sub_calls bd) rl hls
    exact tm_store_sort rl' (lvEq_subst hu hul)
  | .Const (ld12 := ld) (ev137 := e1) (he113 := hr) (hm112 := hm) (hc154 := hc) .. =>
    subst hc hr hm
    obtain ⟨a, us', rfl, ra, ls', rls, hus'⟩ := Tm.const_of_load hE ld
    have : Resolved _ := ⟨hE.const_key_ne⟩
    obtain ⟨-, rls'', ext⟩ := IxVM.Refinement.Levels.levelListInst_obs e1 (bounded_sub sub_calls bd) rls hls
    exact tm_store_const (Bytes.repAddressRef_heapMono₂ addrTy ext ra) rls''
      (lvEqList_subst hus' hul)
  | .App (ld12 := ld) (he176 := hr) (hm175 := hm) (ev193 := e1) (ev221 := e2) (hc238 := hc) .. =>
    subst hc hr hm
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld
    have sf := ih.get .expr_inst_levels lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) Γ k Ef us hf
      ⟨ls, hls, hul⟩
    have sa := ih.get .expr_inst_levels lt_calls e2 _ _ rfl (bounded_sub sub_calls bd) Γ k Ea us
      (ha.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
    exact Tm.store_app (sf.mono e2.heap_extends) sa
  | .Lam (ld12 := ld) (he265 := hr) (hm264 := hm) (ev283 := e1) (ev311 := e2) (ev339 := e3)
      (hc356 := hc) .. =>
    subst hc hr hm
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.lam_of_load hE ld
    have st := ih.get .expr_inst_levels lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) Γ k T us ht
      ⟨ls, hls, hul⟩
    have sb := ih.get .expr_inst_levels lt_calls e2 _ _ rfl (bounded_sub sub_calls bd) Γ (k + 1) B us
      (hb.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
    have ext12 := e1.heap_extends.trans e2.heap_extends
    obtain ⟨-, rl', -⟩ :=
      IxVM.Refinement.Levels.levelInstParams_obs e3 (bounded_sub sub_calls bd) (hl.mono ext12) (hls.mono ext12)
    show Tm κ 0 Γ _ k (.lam (T.instantiateLevelParams (List.range us.length) us)
      (B.instantiateLevelParams (List.range us.length) us)
      { bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw }) _
    rw [bmeta_subst hul]
    exact tm_store_lam (st.mono (e2.heap_extends.trans e3.heap_extends)) (sb.mono e3.heap_extends) rl'
  | .Forall (ld12 := ld) (he383 := hr) (hm382 := hm) (ev401 := e1) (ev429 := e2) (ev457 := e3)
      (hc474 := hc) .. =>
    subst hc hr hm
    obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := Tm.forallE_of_load hE ld
    have st := ih.get .expr_inst_levels lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) Γ k T us ht
      ⟨ls, hls, hul⟩
    have sb := ih.get .expr_inst_levels lt_calls e2 _ _ rfl (bounded_sub sub_calls bd) Γ (k + 1) B us
      (hb.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
    have ext12 := e1.heap_extends.trans e2.heap_extends
    obtain ⟨-, rl', -⟩ :=
      IxVM.Refinement.Levels.levelInstParams_obs e3 (bounded_sub sub_calls bd) (hl.mono ext12) (hls.mono ext12)
    show Tm κ 0 Γ _ k (.forallE (T.instantiateLevelParams (List.range us.length) us)
      (B.instantiateLevelParams (List.range us.length) us)
      { bmeta ℓ with pw := Ix.Kernel.Level.substPW (List.range us.length) us (bmeta ℓ).pw }) _
    rw [bmeta_subst hul]
    exact tm_store_forallE (st.mono (e2.heap_extends.trans e3.heap_extends))
      (sb.mono e3.heap_extends) rl'
  | .Let (ld12 := ld) (he501 := hr) (hm500 := hm) (ev519 := e1) (ev547 := e2) (ev575 := e3)
      (hc592 := hc) .. =>
    subst hc hr hm
    obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := Tm.letE_of_load hE ld
    have st := ih.get .expr_inst_levels lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) Γ k T us ht
      ⟨ls, hls, hul⟩
    have sv := ih.get .expr_inst_levels lt_calls e2 _ _ rfl (bounded_sub sub_calls bd) Γ k V us
      (hv.mono e1.heap_extends) ⟨ls, hls.mono e1.heap_extends, hul⟩
    have ext12 := e1.heap_extends.trans e2.heap_extends
    have sb := ih.get .expr_inst_levels lt_calls e3 _ _ rfl (bounded_sub sub_calls bd) Γ (k + 1) B us
      (hb.mono ext12) ⟨ls, hls.mono ext12, hul⟩
    rw [ilp_instShift]
    exact tm_store_letE ((st.mono e2.heap_extends).mono e3.heap_extends) (sv.mono e3.heap_extends) sb
  | .Lit (ld12 := ld) (he_jqvjdxzf := hr) (he_vxvydceu := hm) .. =>
    subst hr hm
    rcases Tm.lit_of_load hE ld with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;>
      exact hE
  | .Proj (ld12 := ld) (he648 := hr) (hm647 := hm) (ev680 := e1) (hc697 := hc) .. =>
    subst hc hr hm
    obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := Tm.proj_of_load hE ld
    have : Resolved _ := ⟨hE.proj_key_ne⟩
    have : ProjPermitted _ _ := hE.proj_permitted ld ra
    exact tm_store_proj (Bytes.repAddressRef_heapMono₂ addrTy e1.heap_extends ra)
      (ih.get .expr_inst_levels lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) Γ k Es us hes
        ⟨ls, hls, hul⟩)

theorem g_expr_inst_levels (κ : _root_.Address → KKey) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::expr_inst_levels" args h r h' calls) (ih : GIH κ calls) :
    G.expr_inst_levels κ args h r h' calls := by
  intro e params hargs bd Γ k E us hE hus
  subst hargs
  match Obs.«KernelLevels::expr_inst_levels».obs ev with
  | .Nil (ld12 := ld) (he21 := hr) (he22 := he) .. =>
    subst hr he
    obtain ⟨ls, hls, hul⟩ := hus
    have e' : (Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» : String) =
        KernelLevels.klevelListEnum := klevelListEnum_eq
    rw [e'] at ld
    obtain rfl := RepList.nil_of_load hls ld
    obtain rfl : us = [] := by
      cases us with
      | nil => rfl
      | cons u us => exact False.elim (hul (fun _ => 0))
    simp only [List.length_nil, List.range_zero]
    rw [tm_ilp_nil hE]
    exact hE
  | .other_n0 (ev_ogebasxu := ehp) (he_yyggzpmq := hr) (he_krlanrqd := hm) .. =>
    subst hr hm
    obtain ⟨hm1, -, h0⟩ := exprHasLevelParam_tm ehp hE
    subst hm1
    exact h0 rfl us
  | .other_other (ev_ogebasxu := ehp) (ev_nzgqgvgw := e1) (hc_bmwtsztg := hc) .. =>
    subst hc
    obtain ⟨hm1, -, -⟩ := exprHasLevelParam_tm ehp hE
    subst hm1
    exact ih.get .expr_inst_levels_walk lt_calls e1 _ _ rfl (bounded_sub sub_calls bd) Γ k E us hE hus

end IxVM.Refinement.Core.SubstAux
