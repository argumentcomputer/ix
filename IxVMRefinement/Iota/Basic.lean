import IxVMRefinement.Core.Steps.Whnf
import IxVMRefinement.Core.Certs
import IxVMRefinement.Core.Det
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Nat.Basic

/-! # Step lemmas of `KernelWhnf`'s ι helpers: rule lookup, telescope peeling, the parent scan

The rule lookup by position (`find_rule`), the binder domain and the codomain of a telescope
under the arguments of a spine (`pi_peel`, `pi_residual`), the address of the head of a
telescope's binder domain (`se_parent_addr`) and exact address membership (`se_addr_in`). Each
lemma inverts the derivation with the generated path lemma and reads its callees' specs from the
induction hypothesis. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

/-! ## Helpers -/

/-- Two tagged results with the tags `0` and `1` differ. -/
theorem tag_zero_ne_one {xs ys : List (SourceValue F)}
    (h : (Value.tuple (.field 0 :: xs) : SourceValue F) = .tuple (.field 1 :: ys)) : False := by
  injection h with h1
  injection h1 with h2 _
  injection h2 with h3
  exact zero_ne_one h3

/-- A tagged pair's tag and payload, from two descriptions of one result. -/
theorem tuple2_inj {a b x y : SourceValue F}
    (h : (Value.tuple [a, x] : SourceValue F) = .tuple [b, y]) : a = b ∧ x = y := by
  injection h with h1
  simp only [List.cons.injEq, and_true] at h1
  exact h1

/-- A tagged triple's parts, from two descriptions of one result. -/
theorem tuple3_inj {a b x y u v : SourceValue F}
    (h : (Value.tuple [a, x, u] : SourceValue F) = .tuple [b, y, v]) : a = b ∧ x = y ∧ u = v := by
  injection h with h1
  simp only [List.cons.injEq, and_true] at h1
  exact h1

theorem field_ne_of_ne {n : F} (h : (Value.field n : SourceValue F) ≠ .field 0) : n ≠ 0 :=
  fun e => h (by rw [e])

theorem RulesRep.nil_of_load {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List Ix.Kernel.LevelParam} {j : Nat} {p : SourceValue F}
    {rls : List (Ix.Kernel.RecRule .anon)} (rep : RulesRep κ h ps j p rls)
    (hl : loadValue h p = .ok (.construct krrListEnum "Nil" [])) : rls = [] := by
  cases rep with
  | nil _ => rfl
  | cons cell _ _ => exact (load_cell_ne cell hl (by decide)).elim

theorem RulesRep.cons_of_load {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List Ix.Kernel.LevelParam} {j : Nat} {p x y : SourceValue F}
    {rls : List (Ix.Kernel.RecRule .anon)} (rep : RulesRep κ h ps j p rls)
    (hl : loadValue h p = .ok (.construct krrListEnum "Cons" [x, y])) :
    ∃ rl rls', rls = rl :: rls' ∧ RuleRep κ h ps j x rl ∧ RulesRep κ h ps (j + 1) y rls' := by
  cases rep with
  | nil cell => exact (load_cell_ne cell hl (by decide)).elim
  | cons cell hr rs =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx hrest
    injection hrest with hy
    subst hx hy
    exact ⟨_, _, rfl, hr, rs⟩

/-! ## `find_rule` -/

/-- `KernelWhnf::find_rule` walks the rule list until the rule's index is the one sought. -/
theorem find_rule_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::find_rule" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.find_rule c args h r h' calls := by
  intro rules cidx hargs good ps j rls hrep nf rhs hr
  subst hargs
  rcases Obs.«KernelWhnf::find_rule».obs ev with
    ⟨m39, ld12, he25, hm47, he58, hc59⟩ |
    ⟨x_rest, x_rcidx, x_nfields, x_rhs, ld12, op124, he136, he157, hc158⟩ |
    ⟨x_rest, x_rcidx, x_nfields, x_rhs, v108, cs166, ld12, op124, hne159, ev168, hc185⟩
  · exact (tag_zero_ne_one (he25.symm.trans hr)).elim
  · obtain ⟨rl, rls', rfl, ⟨rhs', hv, hn, hrhs⟩, -⟩ := RulesRep.cons_of_load hrep ld12
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    obtain ⟨x, y, hx, rfl⟩ := NatAux.binop_fields op124
    injection hx with hx
    subst hx
    have hxy : ((j : Nat) : F) - y = 0 := NatAux.field_inj (NatAux.sub_ok op124).symm
    obtain ⟨-, rfl, rfl⟩ := tuple3_inj (hr.symm.trans he136)
    subst he157
    refine ⟨0, rl, rfl, ?_, rfl, hrhs⟩
    rw [Nat.add_zero, (sub_eq_zero.mp hxy).symm]
  · obtain ⟨rl, rls', rfl, -, hrest⟩ := RulesRep.cons_of_load hrep ld12
    subst hc185
    obtain ⟨i, rl', hi, hc, hnf, hrh⟩ := ih.get (.whnf .find_rule) (by lt_calls) ev168 x_rest cidx
      rfl (good.sub fun z hz => by simp [hz]) ps (j + 1) rls' hrest nf rhs hr
    refine ⟨i + 1, rl', by simpa using hi, ?_, hnf, hrh⟩
    rw [hc, show j + 1 + i = j + (i + 1) by omega]

/-! ## `pi_peel`, `pi_residual` -/

/-- `KernelWhnf::pi_peel` walks the telescope to binder `n`, pushing the arguments it passes onto
the substitution. -/
theorem pi_peel_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::pi_peel" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.pi_peel c args h r h' calls := by
  intro t zs subs n hargs good d Γ T Cs As m hT hCs hAs hn x hr
  subst hargs hn
  rcases Obs.«KernelWhnf::pi_peel».obs ev with
    ⟨x_dom, x_body, w20, v53, m62, cs70, ld12, hv49, he54, ev72, he89, hc90⟩ |
    ⟨x_dom, x_body, w20, x_a, x_rest, cs127, v133, m149, ld12, hne91, ld106, hm157, op190, ev129,
      hc192⟩ |
    ⟨x_dom, x_body, w20, ld12, hne91, ld106, he204, he218, hc219⟩ |
    ⟨v1, ld12, hne221, he229, he243, hc244⟩
  · obtain ⟨T0, B, ℓ, rfl, hT0, -, -⟩ := hT.forallE_of_load ld12
    injection hv49 with hm
    subst hm he89 hc90
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he54)
    refine ⟨_, ih.get (.infer .inst_subs) (by lt_calls) ev72 x_dom subs rfl
      (good.sub fun z hz => by simp [hz]) d Γ Cs T0 hCs hT0, ?_⟩
    simp [Ix.Kernel.Expr.instantiateList, Specs.Whnf.piDomInst]
  · obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hT.forallE_of_load ld12
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld106
    have hm0 : m ≠ 0 := fun e => hne91 (by rw [e])
    have hv := NatAux.sub_ok op190
    subst hv hm157 hc192
    have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [x_a, subs]]) :=
      Heap.Extends.snoc _ _
    obtain ⟨D, hD, hpi⟩ := ih.get (.whnf .pi_peel) (by lt_calls) ev129 x_body x_rest _ _ rfl
      (good.sub fun z hz => by simp [hz]) d Γ B (A :: Cs) As' (m - 1)
      (by rw [List.length_cons]; exact Tm.mono ext hB) (TmL.store_cons hA hCs)
      (tml_mono ext hAs') rfl x hr
    refine ⟨D, hD, ?_⟩
    rw [← Lib.val_sub_one hm0]
    rw [Ix.Kernel.Expr.instantiateList_cons] at hpi
    simpa [Ix.Kernel.Expr.instantiateList, Specs.Whnf.piDomInst] using hpi
  · exact (tag_zero_ne_one (he204.symm.trans hr)).elim
  · exact (tag_zero_ne_one (he229.symm.trans hr)).elim

/-- `KernelWhnf::pi_residual` walks the telescope along all the arguments, pushing each onto the
substitution, and instantiates what is left. -/
theorem pi_residual_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::pi_residual" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.pi_residual c args h r h' calls := by
  intro t zs subs hargs good d Γ T Cs As hT hCs hAs x hr
  subst hargs
  rcases Obs.«KernelWhnf::pi_residual».obs ev with
    ⟨v23, m32, cs40, ld12, he24, ev42, he59, hc60⟩ |
    ⟨x_a, x_rest, w97, x_body, w98, cs117, m138, ld12, ld89, hm146, ev119, hc166⟩ |
    ⟨x_a, x_rest, v78, ld12, ld89, hne167, he175, he189, hc190⟩
  · obtain rfl := RepList.nil_of_load hAs ld12
    subst he59 hc60
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he24)
    refine ⟨_, ih.get (.infer .inst_subs) (by lt_calls) ev42 t subs rfl
      (good.sub fun z hz => by simp [hz]) d Γ Cs T hCs hT, ?_⟩
    simp [Ix.Kernel.piResidual]
  · obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hT.forallE_of_load ld89
    subst hm146 hc166
    have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [x_a, subs]]) :=
      Heap.Extends.snoc _ _
    obtain ⟨R, hR, hres⟩ := ih.get (.whnf .pi_residual) (by lt_calls) ev119 x_body x_rest _ rfl
      (good.sub fun z hz => by simp [hz]) d Γ B (A :: Cs) As'
      (by rw [List.length_cons]; exact Tm.mono ext hB) (TmL.store_cons hA hCs)
      (tml_mono ext hAs') x hr
    refine ⟨R, hR, ?_⟩
    rw [Ix.Kernel.Expr.instantiateList_cons] at hres
    simpa [Ix.Kernel.Expr.instantiateList, Ix.Kernel.piResidual] using hres
  · exact (tag_zero_ne_one (he175.symm.trans hr)).elim

/-! ## `se_addr_in`, `se_parent_addr` -/

/-- `KernelWhnf::se_addr_in` compares the address with each entry (`Bytes::address_eq`). -/
theorem se_addr_in_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::se_addr_in" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.se_addr_in c args h r h' calls := by
  intro ap xs hargs good a ms ha hms
  subst hargs
  rcases Obs.«KernelWhnf::se_addr_in».obs ev with
    ⟨ld12, he20, he21, hc22⟩ |
    ⟨x_x, x_rest, m41, cs52, ld12, ev54, he75, he76, hc77⟩ |
    ⟨x_x, x_rest, v40, m41, cs52, cs85, ld12, ev54, hne78, ev87, hc104⟩
  · obtain rfl := RepList.nil_of_load hms ld12
    exact ⟨by simp [he20], he21⟩
  · obtain ⟨b, ms', rfl, hb, -⟩ := RepList.cons_of_load hms ld12
    obtain ⟨hr1, rfl⟩ := Lib.address_eq_spec ev54 ha hb
    have hab : a = b := by
      by_contra hne
      rw [ite_eq_right hne] at hr1
      exact NatAux.field_one_ne_zero hr1
    subst hab
    exact ⟨by simp [he75], he76⟩
  · obtain ⟨b, ms', rfl, hb, hms'⟩ := RepList.cons_of_load hms ld12
    obtain ⟨hr1, rfl⟩ := Lib.address_eq_spec ev54 ha hb
    have hab : a ≠ b := by
      intro e
      rw [ite_eq_left e] at hr1
      exact hne78 hr1
    subst hc104
    obtain ⟨hr, hh⟩ := ih.get (.whnf .se_addr_in) (by lt_calls) ev87 ap x_rest rfl
      (good.sub fun z hz => by simp [hz]) a ms' ha hms'
    refine ⟨?_, hh⟩
    rw [hr]
    simp [hab]

/-- `KernelWhnf::se_parent_addr` walks `skip` binders down the telescope and reads the head
constant of the next binder's domain. -/
theorem se_parent_addr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::se_parent_addr" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.se_parent_addr c args h r h' calls := by
  intro rt skip hargs good d Γ k RT n hRT hn t pa hr ht
  subst hargs hn
  rcases Obs.«KernelWhnf::se_parent_addr».obs ev with
    ⟨x_dom, w34, w35, m52, cs63, x_h, w80, x_a, w110, hv14, ld26, ev65, ld102, he125, he139,
      hc140⟩ |
    ⟨x_dom, w34, w35, m52, cs63, x_h, w80, v91, m157, hv14, ld26, ev65, ld102, hne141, he149,
      hm165, he168, hc169⟩ |
    ⟨v15, m187, hv14, ld26, hne171, he179, hm195, he198, hc199⟩ |
    ⟨w223, x_body, w224, cs243, v247, hne200, ld215, op268, ev245, hc270⟩ |
    ⟨v204, m287, hne200, ld215, hne271, he279, hm295, he298, hc299⟩
  · injection hv14 with hn0
    subst hn0 he139 hc140
    obtain ⟨T0, B, ℓ, rfl, hT0, -, -⟩ := hRT.forallE_of_load ld26
    obtain ⟨hd, sp, H, As, he, hH, -, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls) ev65
      x_dom rfl (good.sub fun z hz => by simp [hz]) d Γ k T0 hT0
    obtain ⟨rfl, rfl⟩ := tuple2_inj he
    obtain ⟨a, us, rfl, ha, -⟩ := hH.const_of_load ld102
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he125)
    refine ⟨a, us, ha, ?_⟩
    simp [piDomAt, getAppFn_mkAppN, Ix.Kernel.Expr.getAppFn]
  · obtain ⟨ht0, -⟩ := tuple2_inj (hr.symm.trans he149)
    injection ht0 with ht0
    exact (ht ht0).elim
  · obtain ⟨ht0, -⟩ := tuple2_inj (hr.symm.trans he179)
    injection ht0 with ht0
    exact (ht ht0).elim
  · have hn0 : n ≠ 0 := fun e => hne200 (by rw [e])
    have hv := NatAux.sub_ok op268
    subst hv hc270
    obtain ⟨T0, B, ℓ, rfl, -, hB, -⟩ := hRT.forallE_of_load ld215
    obtain ⟨p, us, hp, hpi⟩ := ih.get (.whnf .se_parent_addr) (by lt_calls) ev245 x_body _ rfl
      (good.sub fun z hz => by simp [hz]) d Γ (k + 1) B (n - 1) hB rfl t pa hr ht
    refine ⟨p, us, hp, ?_⟩
    rw [← Lib.val_sub_one hn0]
    simpa [piDomAt] using hpi
  · obtain ⟨ht0, -⟩ := tuple2_inj (hr.symm.trans he279)
    injection ht0 with ht0
    exact (ht ht0).elim

end IxVM.Refinement.Core
