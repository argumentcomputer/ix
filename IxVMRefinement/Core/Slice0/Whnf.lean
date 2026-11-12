import IxVMRefinement.Core.Slice0.Specs
import IxVMRefinement.Core.Slice0.Bound
import IxVMRefinement.Obs.KernelWhnf
import IxVMRefinement.Obs.KernelTypes
import IxVMRefinement.Obs.KernelLevels
import IxC.Kernel.Verify.PropWhen

/-! # The step lemmas of the whnf slice, and the induction

One lemma per function: from the induction hypothesis at strictly
fewer calls (`IH`) and an observed derivation of the function, its spec. Each
proof takes the derivation's path from the generated path lemma
(`IxVMRefinement.Obs`, `«f».obs`: the inversion of the body, with every
variable replaced by its value) and applies the callees' specs (the part that
is reasoning). `core_sound` is the induction: every observed derivation of a
function of the slice satisfies its spec. -/

namespace IxVM.Refinement.Core.Slice0

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.IxVMRep Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Lengths of concatenated call lists. -/
macro "lenlt" : tactic =>
  `(tactic| (simp only [List.length_append, List.length_cons, List.length_nil]; omega))

/-- Membership in concatenated call lists. -/
macro "memsub" : tactic => `(tactic| (intro x hx; simp [hx]))

/-! ## `level_is_not_zero`: the binder datum `never` -/

/-- `level_is_not_zero` at a stored level answers `1` exactly when the level's
image is never zero (`Level.isNeverZero`), and allocates nothing. -/
theorem levelIsNotZero_eval {h h' : Heap F} {ℓ : IxVMKUniv F} {ptr r : SourceValue F}
    (rep : RepIxVMKUniv h ℓ ptr)
    (ev : EvalFn W "KernelLevels::level_is_not_zero" [ptr] h r h') :
    r = .field (if (trLevel ℓ).isNeverZero then 1 else 0) ∧ h' = h := by
  induction rep generalizing r h' with
  | zero cell =>
    have ev := ev.function_inv (IxVM.KernelLevels.level_is_not_zero.lookup)
      (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl])
    simp only [IxVM.KernelLevels.level_is_not_zero] at ev
    obtain ⟨bs, body, sel, dArm⟩ :=
      IxVM.Refinement.KernelLevels.evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      SourceSemantics.matchListWith, bind, Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [trLevel, Ix.Kernel.Level.isNeverZero]
  | succ cell _ _ =>
    have ev := ev.function_inv (IxVM.KernelLevels.level_is_not_zero.lookup)
      (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl])
    simp only [IxVM.KernelLevels.level_is_not_zero] at ev
    obtain ⟨bs, body, sel, dArm⟩ :=
      IxVM.Refinement.KernelLevels.evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      matchPattern_wildcard, SourceSemantics.matchListWith, bind, Except.bind, pure,
      Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [trLevel, Ix.Kernel.Level.isNeverZero]
  | max cell repA repB iha ihb =>
    have ev := ev.function_inv (IxVM.KernelLevels.level_is_not_zero.lookup)
      (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl])
    simp only [IxVM.KernelLevels.level_is_not_zero] at ev
    obtain ⟨bs, body, sel, dArm⟩ :=
      IxVM.Refinement.KernelLevels.evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      matchPattern_bind, SourceSemantics.matchListWith, bind, Except.bind, pure,
      Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, bs2, body2, dTuple, sel2, dArm2⟩ := dArm.matchValue_inv
    obtain ⟨_, _, _, dCallA, dCallB, rfl⟩ :=
      IxVM.Refinement.KernelLevels.evalExpr_tuple2_inv dTuple
    obtain ⟨_, _, dVarA, dFnA⟩ := IxVM.Refinement.KernelLevels.evalExpr_call1_inv dCallA
    obtain ⟨⟨⟩, rfl⟩ := dVarA.var_inv'
    simp only [instanceName] at dFnA
    obtain ⟨rfl, rfl⟩ := iha dFnA
    obtain ⟨_, _, dVarB, dFnB⟩ := IxVM.Refinement.KernelLevels.evalExpr_call1_inv dCallB
    obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
    simp only [instanceName] at dFnB
    obtain ⟨rfl, rfl⟩ := ihb dFnB
    rcases IxVM.Refinement.KernelLevels.selectArm_bool_pair_zero_zero _ _ sel2 with
      ⟨hor, rfl, rfl⟩ | ⟨hor, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [trLevel, Ix.Kernel.Level.isNeverZero, hor]
    · obtain ⟨rfl, rfl⟩ := dArm2.literal_inv
      simp [trLevel, Ix.Kernel.Level.isNeverZero, hor]
  | imax cell _ repB _ ihb =>
    have ev := ev.function_inv (IxVM.KernelLevels.level_is_not_zero.lookup)
      (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl])
    simp only [IxVM.KernelLevels.level_is_not_zero] at ev
    obtain ⟨bs, body, sel, dArm⟩ :=
      IxVM.Refinement.KernelLevels.evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      matchPattern_wildcard, matchPattern_bind, SourceSemantics.matchListWith, bind,
      Except.bind, pure, Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨_, _, dVarB, dFnB⟩ := IxVM.Refinement.KernelLevels.evalExpr_call1_inv dArm
    obtain ⟨⟨⟩, rfl⟩ := dVarB.var_inv'
    simp only [instanceName] at dFnB
    dsimp only [trLevel, Ix.Kernel.Level.isNeverZero]
    exact ihb dFnB
  | param cell =>
    have ev := ev.function_inv (IxVM.KernelLevels.level_is_not_zero.lookup)
      (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl])
    simp only [IxVM.KernelLevels.level_is_not_zero] at ev
    obtain ⟨bs, body, sel, dArm⟩ :=
      IxVM.Refinement.KernelLevels.evalExpr_match_load_var_enum rfl cell ev
    simp (config := { decide := true }) [SourceSemantics.selectArm, matchPattern_construct,
      matchPattern_wildcard, SourceSemantics.matchListWith, bind, Except.bind, pure,
      Except.pure] at sel
    obtain ⟨rfl, rfl⟩ := sel
    obtain ⟨rfl, rfl⟩ := dArm.literal_inv
    simp [trLevel, Ix.Kernel.Level.isNeverZero]

/-- **A binder `level_is_not_zero` passes has the datum `never`**: the stored level's
zero-ness (`bmeta`) is `never` (`Level.isNeverZero_eq_isNever`). -/
theorem bmeta_nb_of_obs {h h' : Heap F} {ℓ : IxVMKUniv F} {ptr : SourceValue F}
    {cs : List (Call F)} (rep : RepIxVMKUniv h ℓ ptr)
    (ev : ObsFn W "KernelLevels::level_is_not_zero" [ptr] h (.field 1) h' cs) :
    bmeta ℓ = nb ∧ h' = h := by
  obtain ⟨hr, rfl⟩ := levelIsNotZero_eval rep ev.erase
  refine ⟨?_, rfl⟩
  cases hz : (trLevel ℓ).isNeverZero
  · simp [hz] at hr
  · have hnv : (trLevel ℓ).zeronessOf = .never :=
      Ix.Kernel.PropWhen.isNever_iff.mp
        ((Ix.Kernel.Level.isNeverZero_eq_isNever (trLevel ℓ)).symm.trans hz)
    show ({ pw := (trLevel ℓ).zeronessOf } : Ix.Kernel.BinderMeta) = { pw := .never }
    rw [hnv]

/-! ## `apply_spine` -/

theorem applySpine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::apply_spine" args h r h' calls) (ih : IH c calls) :
    ApplySpineSpec c args h r h' := by
  intro hd sp hargs d Γ H As hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::apply_spine».obs ev with ⟨ld, rfl, rfl, -⟩ |
    ⟨a, rest, cs, m, ld, rfl, ev', rfl⟩
  · -- `Nil => head`
    obtain rfl := RepList.nil_of_load hAs ld
    exact hH
  · -- `Cons(a, rest) => apply_spine(&App(head, a), rest)`
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld
    exact (ih _ _ _ _ _ _ (by lenlt) ev').applySpine rfl _ _ rfl d Γ (.app H A) As'
      (RepE.store_app hH hA) (RepSpine.mono (Heap.Extends.snoc _ _) hAs')

/-! ## `collect_spine` -/

theorem collect_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" args h r h' calls) (ih : IH c calls) :
    CollectSpec c args h r h' := by
  intro e hargs d Γ E hE
  subst hargs
  rcases Obs.«KernelTypes::collect_spine».obs ev with
    ⟨f, a, m, cs, hd, sa, v, m', cs', ld, ev1, rfl, ev2, rfl, rfl⟩ |
    ⟨v, m, ld, -, rfl, rfl, rfl, -⟩
  · -- `App(f, a) => let (head, args) = collect_spine(f); (head, snoc(args, a))`
    obtain ⟨te, rte, tte⟩ := hE
    obtain ⟨f', a', rfl, rf, ra⟩ := RepK.app_of_load rte ld
    obtain ⟨Ef, Ea, rfl, tf, ta⟩ := Tr.app_inv tte
    have extm := ev1.heap_extends
    obtain ⟨hdp, sp, Hh, As, hpair, hHh, hAs, rfl⟩ :=
      (ih _ _ _ _ _ _ (by lenlt) ev1).collect rfl _ rfl d Γ Ef ⟨f', rf, tf⟩
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hEa := RepEk.mono extm (show RepE c.κ d Γ _ Ea a from ⟨a', ra, ta⟩)
    have hsn := hA.snoc _ _ _ _ _ _ ev2 d Γ As Ea hAs hEa
    exact ⟨_, _, Hh, As ++ [Ea], rfl, RepEk.mono ev2.heap_extends hHh, hsn,
      (K.mkAppN_snoc Hh Ea As).symm⟩
  · -- `_ => (e, &Nil)`
    exact ⟨_, _, E, [], rfl, RepEk.mono (Heap.Extends.snoc _ _) hE, RepSpine.store_nil _, rfl⟩

/-! ## `expr_inst_levels` at an empty level list -/

theorem instLevels_step {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::expr_inst_levels" args h r h' calls) :
    InstLevelsSpec args h r h' := by
  intro e ps hargs hps
  subst hargs
  rcases Obs.«KernelLevels::expr_inst_levels».obs ev with ⟨ld, rfl, rfl, -⟩ | ⟨v, cs, ld, hne, -, -⟩
  · exact ⟨rfl, rfl⟩
  · cases hps with
    | nil cell =>
      rw [loadValue_enum_cell cell] at ld
      cases ld
      exact (hne [] rfl rfl).elim

/-! ## `whnf_core` and `whnf` -/

theorem whnfCore_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_core" args h r h' calls) (ih : IH c calls) :
    WhnfSpec c args h r h' calls := by
  intro rc e types hargs good d Γ E hE
  subst hargs
  obtain ⟨cs, m, rfl, ev', rfl⟩ := Obs.«KernelWhnf::whnf_core».obs ev
  exact (ih _ _ _ _ _ _ (by lenlt) ev').withSpine rfl _ _ _ _ rfl (good.sub (by memsub) (by lenlt))
    d Γ E [] (RepEk.mono (Heap.Extends.snoc _ _) hE) (RepSpine.store_nil _)

theorem whnf_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf" args h r h' calls) (ih : IH c calls) :
    WhnfSpec c args h r h' calls := by
  intro rc e types hargs good d Γ E hE
  subst hargs
  rcases Obs.«KernelWhnf::whnf».obs ev with
    ⟨_, -, rfl, rfl, -⟩ | ⟨_, -, rfl, rfl, -⟩ | ⟨_, _, _, -, rfl, rfl, -⟩ | ⟨_, _, _, -, rfl, rfl, -⟩ |
    ⟨_, -, rfl, rfl, -⟩ | ⟨v, cs, v', m, cs', v'', m', cs'', -, -, -, -, -, -, ev1, ev2, ev3, rfl⟩
  -- `Srt`, `Lit`, `Lam`, `Forall`, `BVar`: already weak head normal
  all_goals first | exact ⟨E, hE, .refl⟩ | skip
  -- `_ => whnf_core(rc, e, ctx_trim(types, expr_lbr(e)))`
  exact (ih _ _ _ _ _ _ (by lenlt) ev3).whnfCore rfl _ _ _ rfl (good.sub (by memsub) (by lenlt))
    d Γ E (RepEk.mono (ev1.heap_extends.trans ev2.heap_extends) hE)

/-! ## `whnf_with_spine` -/

theorem withSpine_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_with_spine" args h r h' calls) (ih : IH c calls) :
    WithSpineSpec c args h r h' calls := by
  intro rc hd sp types hargs good d Γ H As hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_with_spine».obs ev with
    ⟨f, a, m, cs, ih', is, cs', v, m', cs'', ld, ev1, ev2, ev3, rfl⟩ |
    ⟨ty, b, w, m, cs, red, rest, cs', ld, ev1, ev2, rfl⟩ |
    ⟨ty, b, w, v, m, cs, cs', ld, ev1, ev2, rfl⟩ |
    ⟨ad, lv, cs, ld, ev1, rfl⟩ |
    ⟨_, _, _, _, _, _, _, ld, -, -, -⟩ |
    ⟨_, _, _, _, ld, -, -⟩ |
    ⟨v, cs, ld, -, -, -, -, -, ev1, rfl⟩
  · -- `App(f, a) => match collect_spine(head) { (ih, is) => whnf_with_spine(rc, ih, concat(is, spine), types) }`
    have extc := ev1.heap_extends
    obtain ⟨hdp, sp0, Hh, Is, hpair, hHh, hIs, rfl⟩ :=
      (ih _ _ _ _ _ _ (by lenlt) ev1).collect rfl _ rfl d Γ H hH
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    have hcat := hA.concat _ _ _ _ _ _ ev2 d Γ Is As hIs (RepSpine.mono extc hAs)
    obtain ⟨E', hE', hred⟩ := (ih _ _ _ _ _ _ (by lenlt) ev3).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ Hh (Is ++ As) (RepEk.mono ev2.heap_extends hHh) hcat
    refine ⟨E', hE', ?_⟩
    rw [← K.mkAppN_append]
    exact hred
  · -- `Lam`, `red_beta(rc, head, spine, types)`, `(1, reduct, rest) => whnf_with_spine(rc, reduct, rest, types)`
    obtain ⟨E, Bs, hE, hBs, hred1⟩ := (ih _ _ _ _ _ _ (by lenlt) ev1).redBeta rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ H As hH hAs _ _ rfl
    obtain ⟨E', hE', hred2⟩ := (ih _ _ _ _ _ _ (by lenlt) ev2).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ E Bs hE hBs
    exact ⟨E', hE', .trans hred1 hred2⟩
  · -- `Lam`, `_ => apply_spine(head, spine)`
    have ext := ev1.heap_extends
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) ev2).applySpine rfl _ _ rfl d Γ H As
      (RepEk.mono ext hH) (RepSpine.mono ext hAs), .refl⟩
  · -- `Const(addr, lvls) => whnf_const_head(rc, addr, lvls, head, spine, types)`
    obtain ⟨t, rt, tt⟩ := hH
    obtain ⟨a, ls, rfl, ha, hls⟩ := RepK.const_of_load rt ld
    obtain ⟨rfl, rfl⟩ := Tr.const_inv tt
    exact (ih _ _ _ _ _ _ (by lenlt) ev1).constHead rfl _ _ _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ a As ha hls ⟨_, rt, .const⟩ hAs
  · -- `Let` has no image
    obtain ⟨t, rt, tt⟩ := hH
    obtain ⟨_, _, _, rfl⟩ := RepK.let_of_load rt ld
    exact (Tr.let_inv tt).elim
  · -- `Proj` has no image
    obtain ⟨t, rt, tt⟩ := hH
    obtain ⟨_, _, _, rfl⟩ := RepK.proj_of_load rt ld
    exact (Tr.proj_inv tt).elim
  · -- `_ => apply_spine(head, spine)`
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) ev1).applySpine rfl _ _ rfl d Γ H As hH hAs, .refl⟩

/-! ## `peel_beta` -/

theorem peel_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::peel_beta" args h r h' calls) (ih : IH c calls) :
    PeelSpec c args h r h' calls := by
  intro lam sp acc hargs d Γ k L As Cs hL hAs hCs
  subst hargs
  rcases Obs.«KernelWhnf::peel_beta».obs ev with
    ⟨w, b, bl, a, rest, m, csz, cs, m', ld, ld', evz, rfl, ev1, rfl⟩ |
    ⟨w, b, bl, a, rest, v, m, csz, ld, ld', evz, hne, rfl, rfl, rfl⟩ |
    ⟨w, b, bl, ld, ld', rfl, rfl, -⟩ |
    ⟨v, ld, -, rfl, rfl, -⟩
  · -- `Lam(_, body, bl)`, `Cons(a, rest)`, `level_is_not_zero(bl)` is `1` (the binder's
    -- datum is `never`) `=> peel_beta(body, rest, &Cons(a, acc))`
    obtain ⟨t, rt, tt⟩ := hL
    obtain ⟨ty, b', ℓ, rfl, rty, rb, rl⟩ := RepK.lam_of_load rt ld
    obtain ⟨T, B, rfl, tty, tb⟩ := Tr.lam_inv tt
    obtain ⟨hnb, rfl⟩ := bmeta_nb_of_obs rl evz
    obtain ⟨A, As', rfl, hA1, hAs'⟩ := RepList.cons_of_load hAs ld'
    obtain ⟨deep, cons, rest', Ts, D, rfl, rfl, hlenA, hlenC, hD, hcons, hrest⟩ :=
      (ih _ _ _ _ _ _ (by lenlt) ev1).peel rfl _ _ _ rfl d Γ (k + 1) B As' (A :: Cs)
        (RepEk.mono (Heap.Extends.snoc _ _) ⟨b', rb, tb⟩)
        (RepSpine.mono (Heap.Extends.snoc _ _) hAs')
        (.cons (by simp) (RepEk.mono (Heap.Extends.snoc _ _) hA1)
          (RepSpine.mono (Heap.Extends.snoc _ _) hCs))
    refine ⟨deep, cons, rest', T :: Ts, D, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show _ = Ix.Kernel.Expr.lam T (K.lams Ts D) nb
      rw [hnb]
    · simp only [List.length_cons]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · have hk : k + (T :: Ts).length = k + 1 + Ts.length := by simp; omega
      rw [hk]; exact hD
    · simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hcons
    · simpa [List.drop_succ_cons] using hrest
  · -- `Lam(_, body, bl)`, `Cons(a, rest)`, `_ => (lam, acc, spine)`: the datum may be zero
    have ext := evz.heap_extends
    exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using RepEk.mono ext hL,
      by simpa using RepSpine.mono ext hCs, by simpa using RepSpine.mono ext hAs⟩
  · -- `Lam(_, body, bl)`, `Nil => (lam, acc, spine)`
    exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using hL, by simpa using hCs,
      by simpa using hAs⟩
  · -- `_ => (lam, acc, spine)`
    exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using hL, by simpa using hCs,
      by simpa using hAs⟩

/-! ## `red_beta` -/

/-- **`peel_beta(lam, spine, &Nil)`**, which opens `red_beta`: a `λ`-telescope `Ts`
of the head, its body at depth `|Ts|`, the consumed arguments reversed, and the rest
of the spine. -/
theorem peel_nil (c : Ctx) {calls : List (Call F)} (ih : IH c calls)
    {lam sp deep cons rest : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelWhnf::peel_beta" [lam, sp, .ptr (.enum kexprListEnum) h.length]
      (h ++ [.construct kexprListEnum "Nil" []]) (.tuple [deep, cons, rest]) m2 cs)
    (hlt : cs.length < calls.length)
    {d : Nat} {Γ : Nat → KExpr} {L : KExpr} {As : List KExpr}
    (hL : RepE c.κ d Γ h L lam) (hAs : RepSpine c.κ d Γ h As sp) :
    ∃ Ts D, L = K.lams Ts D ∧ Ts.length ≤ As.length ∧
      RepEk c.κ d Γ Ts.length m2 D deep ∧
      RepSpine c.κ d Γ m2 (As.take Ts.length).reverse cons ∧
      RepSpine c.κ d Γ m2 (As.drop Ts.length) rest := by
  obtain ⟨deep', cons', rest', Ts, D, hres, rfl, hlenA, -, hD, hcons, hrest⟩ :=
    (ih _ _ _ _ _ _ hlt ev).peel rfl _ _ _ rfl d Γ 0 L As []
      (RepEk.mono (Heap.Extends.snoc _ _) hL) (RepSpine.mono (Heap.Extends.snoc _ _) hAs)
      (RepSpine.store_nil _)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hres
  obtain ⟨rfl, rfl, rfl⟩ := hres
  rw [Nat.zero_add] at hD
  rw [List.append_nil] at hcons
  exact ⟨Ts, D, rfl, hlenA, hD, hcons, hrest⟩

/-- **`beta_more` in the fragment returns its arguments**: it calls `peel_beta_cert`
(certified β, outside the fragment) or returns `(deep, consumed, rest)`. -/
theorem betaMore_frag {c : Ctx} {calls : List (Call F)} (good : Good c calls)
    {rc deep rest cons types deep2 cons2 rest2 : SourceValue F} {m m' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelWhnf::beta_more" [rc, deep, rest, cons, types] m
      (.tuple [deep2, cons2, rest2]) m' cs)
    (hsub : ∀ x ∈ cs, x ∈ calls) :
    deep2 = deep ∧ cons2 = cons ∧ rest2 = rest ∧ m' = m := by
  rcases Obs.«KernelWhnf::beta_more».obs ev with
    ⟨ld, hr, rfl, -⟩ | ⟨_, _, _, _, _, cs', ld, ld', ev', rfl⟩ | ⟨_, _, _, ld, ld', -, hr, rfl, -⟩
  · -- `Nil => (deep, consumed, rest)`
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- `Cons(_, _)`, `Lam(_, _, _) => peel_beta_cert(…)`: outside the fragment
    exact (good.2.2.1 _ (hsub _ (List.mem_cons_self ..)) (by simp [nativeNames])).elim
  · -- `Cons(_, _)`, `_ => (deep, consumed, rest)`
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- `red_beta`: the consumed arguments are matched structurally, so no
count is read as a field element. In the fragment `beta_more` returns `peel_beta`'s
result (`betaMore_frag`), so every consumed binder has the datum `never`. -/
theorem redBeta_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_beta" args h r h' calls) (ih : IH c calls) :
    RedBetaSpec c args h r h' calls := by
  intro rc lam sp types hargs good d Γ L As hL hAs x y hr
  subst hargs
  rcases Obs.«KernelWhnf::red_beta».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, -, -, -, -, rfl, -, -⟩ |
    ⟨m2, cs13, m34, deep, cons, rest, m68, cs79, deep2, cons2, rest2, a, more, v, m239, cs247,
      rfl, ev15, ev81, ld154, ld218, rfl, ev249, rfl, rfl⟩ |
    ⟨m2, cs13, m34, deep, cons, rest, m68, cs79, deep2, cons2, rest2, a, more, w1, w2, v, m314,
      cs322, rfl, ev15, ev81, ld154, ld218, rfl, ev324, rfl, rfl⟩
  · -- `Nil => (0, lam, spine)`: not tag `1`
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hr
    exact absurd hr.1 (by decide)
  · -- `Cons(a, more)`, `Nil => (1, expr_inst1(deep, a, 0), rest)`: one `Red.betaGate`
    cases hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := betaMore_frag good ev81 (by memsub)
    obtain ⟨Ts, D, rfl, hlenA, hD, hcons, hrest⟩ := peel_nil c ih ev15 (by lenlt) hL hAs
    obtain ⟨A1, Cs, hc, hA1, hCs⟩ := RepList.cons_of_load hcons ld154
    obtain rfl := RepList.nil_of_load hCs ld218
    have hn : Ts.length = 1 := by
      have := congrArg List.length hc
      simp only [List.length_reverse, List.length_take, List.length_cons, List.length_nil] at this
      omega
    obtain ⟨T1, rfl⟩ : ∃ T1, Ts = [T1] := by
      rcases Ts with _ | ⟨T1, _ | ⟨_, _⟩⟩
      · simp at hn
      · exact ⟨T1, rfl⟩
      · simp at hn
    obtain ⟨A0, As', rfl⟩ : ∃ A0 As', As = A0 :: As' := by
      rcases As with _ | ⟨A0, As'⟩
      · simp at hlenA
      · exact ⟨A0, As', rfl⟩
    have hAeq : A0 = A1 := by simpa using hc
    rw [← hAeq] at hA1
    simp at hD hrest
    refine ⟨_, _, hA.inst1 _ _ _ _ _ _ ev249 d Γ D A0 hD hA1,
      RepSpine.mono ev249.heap_extends hrest, ?_⟩
    show Red c.env d (K.mkAppN (.app (.lam T1 D nb) A0) As') (K.mkAppN (D.instantiate1 A0) As')
    exact K.red_mkAppN As' (.betaGate nb_isNever)
  · -- `Cons(a, more)`, `Cons(_, _) => (1, expr_inst_many(deep, consumed, 0), rest)`: the chain
    cases hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := betaMore_frag good ev81 (by memsub)
    obtain ⟨Ts, D, rfl, hlenA, hD, hcons, hrest⟩ := peel_nil c ih ev15 (by lenlt) hL hAs
    have hclen : (As.take Ts.length).reverse.length = Ts.length := by simp; omega
    rw [← hclen] at hD
    refine ⟨_, _, hA.instMany _ _ _ _ _ _ ev324 d Γ D _ hD hcons,
      RepSpine.mono ev324.heap_extends hrest, ?_⟩
    have hchain := K.red_beta_chain (env := c.env) (d := d) (As.take Ts.length) Ts D
      (As.drop Ts.length) (by simp; omega)
    rwa [List.take_append_drop] at hchain

/-! ## `whnf_const_head` -/

/-- **A record load in the fragment represents the environment's constant**:
`get_ci` called with a represented address, by a run that hashed no collision
and loads only records of the fragment. -/
theorem ci_rep {c : Ctx} (hA : Assumed c) {calls cs : List (Call F)} (good : Good c calls)
    {addr ci : SourceValue F} {m m' : Heap F}
    (ev : ObsFn W "Ingress::get_ci" [addr] m ci m' cs)
    (hmem : (⟨"Ingress::get_ci", [addr], m⟩ : Call F) ∈ calls)
    (hsub : ∀ x ∈ cs, x ∈ calls) (hlen : cs.length ≤ calls.length)
    {a : Bytes.Address} (ha : Bytes.RepAddressRef addrTy m a addr) :
    CIRep c m' ci (c.env.find? (c.κ a)) := by
  obtain ⟨⟨lc, hst⟩, hfrag⟩ := good.2.1 _ hmem rfl addr a rfl ha
  exact hA.getCI _ _ _ _ _ ev a ha hfrag (load_escape hst (good.sub hsub hlen).1)

/-- `Lists::length` of the empty level list is `0`, and allocates nothing. -/
theorem length_levels_nil {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepList klevelListEnum RepIxVMKUniv h [] l) : r = .field 0 ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [klevelTy]).symbol [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev
  have henum : (Instance.mk "Lists::Node" [klevelTy]).symbol = klevelListEnum :=
    Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol
  cases hl with
  | nil cell =>
    rcases Obs.«Lists::length».obs ev' with ⟨ld, hr, hh, -⟩ | ⟨w, rest, x, m, cs', ld, -, -, -, -⟩
    · exact ⟨hr, hh⟩
    · rw [henum, loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc _
      exact absurd hc (by decide)

theorem constHead_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_const_head" args h r h' calls) (ih : IH c calls) :
    ConstHeadSpec c args h r h' calls := by
  intro rc addr lvls hd sp types hargs good d Γ a As ha hls hhd hAs
  subst hargs
  cases Obs.«KernelWhnf::whnf_const_head».obs ev with
  | n1_bind m2 cs12 x cs86 ev14 ev88 hc =>
    -- `(1, reduced) => whnf(rc, reduced, types)`: not taken, no native fires
    subst hc
    obtain ⟨y, hy⟩ := hA.tryPrim _ _ _ _ _ _ _ _ _ ev14 (good.sub (by memsub) (by lenlt)).2.2.1
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hy
    exact absurd hy.1 (by decide)
  | n2_bind m2 cs12 x ev14 he1 he2 hc =>
    -- `(2, stuck) => stuck`: not taken
    subst hc
    obtain ⟨y, hy⟩ := hA.tryPrim _ _ _ _ _ _ _ _ _ ev14 (good.sub (by memsub) (by lenlt)).2.2.1
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hy
    exact absurd hy.1 (by decide)
  | other_Defn_n1_bind v1 m2 cs12 m140 p cs153 nl w2 value w3 w4 m210 cs220 x cs270 ev14 ev155
      ld ev222 ev272 hc =>
    -- `Defn`, `(1, reduced) => whnf(rc, reduced, types)`: not taken on a represented value
    subst hc
    have ha1 := Bytes.repAddressRef_heapMono₂ addrTy ev14.heap_extends ha
    have hci := ci_rep hA good ev155 (by simp) (by memsub) (by lenlt) ha1
    obtain ⟨cvv, V, hn, hfind, hlp, hV⟩ := hci.defn _ _ _ _ _ ld
    obtain ⟨y, hy⟩ := hA.tryProjDef _ _ _ _ _ _ _ _ ev222 d Γ V (hV d Γ)
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hy
    exact absurd hy.1 (by decide)
  | other_Defn_other_n1_bind v1 m2 cs12 m140 p cs153 nl w2 value w3 w4 v209 m210 cs220 m302 cs313
      body cs353 ev14 ev155 ld ev222 ev315 ev355 hc =>
    -- `Defn(nl, _, value, _, _)`, `_`, `red_unfold(ci, lvls)`, `(1, body) =>
    -- whnf_with_spine(rc, body, spine, types)`; `red_unfold`'s `Defn` arm checks the level
    -- count, `Lists::length(lvls) - nl` (`0` here: `(1, expr_inst_levels(value, lvls))`)
    subst hc
    rcases Obs.«KernelWhnf::red_unfold».obs ev315 with
      ⟨_, _, _, _, _, x54, m56, cs65, v84, m93, cs101, hv, evL, -, he, ev314, rfl, rfl⟩ |
      ⟨_, _, _, _, _, _, _, _, _, -, -, -, -, he, -, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, hne, -, -, -, -, -, -, -⟩ |
      ⟨_, _, _, _, _, _, _, hne, -, -, -, -, -, -, -⟩ | ⟨_, hne, -, -, -, -, -⟩
    rotate_left
    · -- the count differs: `(0, value)`, not tag `1`
      simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at he
      exact absurd he.1 (by decide)
    all_goals first | exact (hne _ (by rfl) rfl).elim | skip
    cases hv
    cases he
    have extp := ev14.heap_extends
    have ha1 := Bytes.repAddressRef_heapMono₂ addrTy extp ha
    have hci := ci_rep hA good ev155 (by simp) (by memsub) (by lenlt) ha1
    have extg := ev155.heap_extends
    obtain ⟨cvv, V, hn, hfind, hlp, hV⟩ := hci.defn _ _ _ _ _ ld
    have hδ : Red c.env d (K.mkAppN (.const (c.κ a) []) As) (K.mkAppN V As) :=
      .delta (K.unfold_const_head As hfind hlp)
    have extj := ev222.heap_extends
    have ext3 := extp.trans (extg.trans extj)
    have hls3 := repList_heapMono₂ klevelListEnum repIxVMKUniv_heapMono₂ ext3 hls
    obtain ⟨-, rfl⟩ := length_levels_nil evL hls3
    obtain ⟨rfl, rfl⟩ := (ih _ _ _ _ _ _ (by lenlt) ev314).instLevels rfl _ _ rfl hls3
    obtain ⟨E', hE', hred2⟩ := (ih _ _ _ _ _ _ (by lenlt) ev355).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ V As (RepEc.mono extj hV d Γ)
      (RepSpine.mono ext3 hAs)
    exact ⟨E', hE', .trans hδ hred2⟩
  | other_Defn_other_other v1 m2 cs12 m140 p cs153 w1 w2 value w3 w4 v209 m210 cs220 v301 m302
      cs313 cs395 ev14 ev155 ld ev222 ev315 ev397 hc =>
    -- `Defn`, `_`, `_ => apply_spine(head, spine)`: the stuck form is a reduct too
    subst hc
    have ext := ev14.heap_extends.trans
      (ev155.heap_extends.trans (ev222.heap_extends.trans ev315.heap_extends))
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) ev397).applySpine rfl _ _ rfl d Γ _ As
      (RepEk.mono ext hhd) (RepSpine.mono ext hAs), .refl⟩
  | other_Thm v1 m2 cs12 m140 p cs153 w1 w2 w3 cs398 ev14 ev155 ld ev400 hc =>
    -- `Thm(_, _, _) => apply_spine(head, spine)`
    subst hc
    have ext := ev14.heap_extends.trans ev155.heap_extends
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) ev400).applySpine rfl _ _ rfl d Γ _ As
      (RepEk.mono ext hhd) (RepSpine.mono ext hAs), .refl⟩
  | other_other v1 m2 cs12 v139 m140 p cs153 cs1760 ev14 ev155 ld hn1 hn2 hn3 hn4 ev1762 hc =>
    -- `_ => apply_spine(head, spine)`
    subst hc
    have ext := ev14.heap_extends.trans ev155.heap_extends
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) ev1762).applySpine rfl _ _ rfl d Γ _ As
      (RepEk.mono ext hhd) (RepSpine.mono ext hAs), .refl⟩
  | _ =>
    -- `Quot` and `Rec` (every path through their arms) are outside the slice
    rename_i hc
    subst hc
    have ev14 := ‹ObsFn W "KernelWhnf::try_prim_dispatch" _ _ _ _ _›
    have ev155 := ‹ObsFn W "Ingress::get_ci" _ _ _ _ _›
    have hci := ci_rep hA good ev155 (by simp) (by memsub) (by lenlt)
      (Bytes.repAddressRef_heapMono₂ addrTy ev14.heap_extends ha)
    first
      | exact (hci.quot _ ‹loadValue _ _ = .ok (.construct _ "Quot" _)›).elim
      | exact (hci.recr _ ‹loadValue _ _ = .ok (.construct _ "Rec" _)›).elim

end IxVM.Refinement.Core.Slice0
