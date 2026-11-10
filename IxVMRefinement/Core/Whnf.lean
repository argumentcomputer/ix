import IxVMRefinement.Core.Specs
import IxVMRefinement.Core.Bound
import IxVMRefinement.Obs.KernelWhnf
import IxVMRefinement.Obs.KernelTypes
import IxVMRefinement.Obs.KernelLevels

/-! # The step lemmas of the whnf slice, and the induction

Spike S3. One lemma per function: from the induction hypothesis at strictly
fewer calls (`IH`) and an observed derivation of the function, its spec. Each
proof takes the derivation's path from the generated path lemma
(`IxVMRefinement.Obs`, `«f».obs`: the inversion of the body, with every
variable replaced by its value) and applies the callees' specs (the part that
is reasoning). `core_sound` is the induction: every observed derivation of a
function of the slice satisfies its spec. -/

namespace IxVM.Refinement.Core

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
    ⟨_, -, rfl, rfl, -⟩ | ⟨_, -, rfl, rfl, -⟩ | ⟨_, _, -, rfl, rfl, -⟩ | ⟨_, _, -, rfl, rfl, -⟩ |
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
    ⟨ty, b, cs, ld, ev1, rfl⟩ |
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
  · -- `Lam(ty, body) => whnf_apply_beta(rc, spine, head, types)`
    exact (ih _ _ _ _ _ _ (by lenlt) ev1).applyBeta rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ H As hH hAs
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
    ⟨w, b, a, rest, cs, m, ld, ld', rfl, ev1, rfl⟩ | ⟨w, b, ld, ld', rfl, rfl, -⟩ |
    ⟨v, ld, -, rfl, rfl, -⟩
  · -- `Lam(_, body)`, `Cons(a, rest) => peel_beta(body, rest, &Cons(a, acc))`
    obtain ⟨t, rt, tt⟩ := hL
    obtain ⟨ty, b', rfl, rty, rb⟩ := RepK.lam_of_load rt ld
    obtain ⟨T, B, rfl, tty, tb⟩ := Tr.lam_inv tt
    obtain ⟨A, As', rfl, hA1, hAs'⟩ := RepList.cons_of_load hAs ld'
    obtain ⟨deep, cons, rest', Ts, D, rfl, rfl, hlenA, hlenC, hD, hcons, hrest⟩ :=
      (ih _ _ _ _ _ _ (by lenlt) ev1).peel rfl _ _ _ rfl d Γ (k + 1) B As' (A :: Cs)
        (RepEk.mono (Heap.Extends.snoc _ _) ⟨b', rb, tb⟩)
        (RepSpine.mono (Heap.Extends.snoc _ _) hAs')
        (.cons (by simp) (RepEk.mono (Heap.Extends.snoc _ _) hA1)
          (RepSpine.mono (Heap.Extends.snoc _ _) hCs))
    refine ⟨deep, cons, rest', T :: Ts, D, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons, List.length_nil]; omega
    · have hk : k + (T :: Ts).length = k + 1 + Ts.length := by simp; omega
      rw [hk]; exact hD
    · simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hcons
    · simpa [List.drop_succ_cons] using hrest
  · -- `Lam(_, body)`, `Nil => (lam, acc, spine)`
    exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using hL, by simpa using hCs,
      by simpa using hAs⟩
  · -- `_ => (lam, acc, spine)`
    exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using hL, by simpa using hCs,
      by simpa using hAs⟩

/-! ## `whnf_apply_beta` -/

theorem field_lit_eq {n m : Nat} {x : F} (hn : n < 2 ^ 39) (hm : m < 2 ^ 39)
    (h1 : ((n : F)) = x) (h2 : x = (m : F)) : n = m :=
  natCast_lt_inj hn hm (h1.trans h2)

/-- **The common prefix of `whnf_apply_beta`**: `peel_beta(lam, spine, &Nil)`
gives a `λ`-telescope `Ts` of the head and the consumed arguments, and
`Lists::length` of them is `|Ts|`. -/
theorem applyBeta_prefix (c : Ctx) (hA : Assumed c) {calls : List (Call F)} (ih : IH c calls)
    {lam sp deep cons rest n : SourceValue F} {h m2 m68 : Heap F} {cs13 cs79 : List (Call F)}
    (ev15 : ObsFn W "KernelWhnf::peel_beta" [lam, sp, .ptr (.enum kexprListEnum) h.length]
      (h ++ [.construct kexprListEnum "Nil" []]) (.tuple [deep, cons, rest]) m2 cs13)
    (hlt : cs13.length < calls.length) (ev81 : ObsFn W lengthName [cons] m2 n m68 cs79)
    {d : Nat} {Γ : Nat → KExpr} {L : KExpr} {As : List KExpr}
    (hL : RepE c.κ d Γ h L lam) (hAs : RepSpine c.κ d Γ h As sp) :
    ∃ Ts D, L = K.lams Ts D ∧ Ts.length ≤ As.length ∧ Ts.length ≤ cs13.length ∧
      RepEk c.κ d Γ (0 + Ts.length) m2 D deep ∧
      RepSpine c.κ d Γ m2 ((As.take Ts.length).reverse ++ []) cons ∧
      RepSpine c.κ d Γ m2 (As.drop Ts.length) rest ∧ n = .field (Ts.length : F) := by
  obtain ⟨deep', cons', rest', Ts, D, hres, rfl, hlenA, hlenC, hD, hcons, hrest⟩ :=
    (ih _ _ _ _ _ _ hlt ev15).peel rfl _ _ _ rfl d Γ 0 L As []
      (RepEk.mono (Heap.Extends.snoc _ _) hL) (RepSpine.mono (Heap.Extends.snoc _ _) hAs)
      (RepSpine.store_nil _)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hres
  obtain ⟨rfl, rfl, rfl⟩ := hres
  have hlv := hA.length _ _ _ _ _ ev81 d Γ _ hcons
  have hclen : ((As.take Ts.length).reverse ++ []).length = Ts.length := by simp; omega
  rw [hclen] at hlv
  exact ⟨Ts, D, rfl, hlenA, hlenC, hD, hcons, hrest, hlv⟩

theorem applyBeta_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_apply_beta" args h r h' calls) (ih : IH c calls) :
    ApplyBetaSpec c args h r h' calls := by
  intro rc sp lam types hargs good d Γ L As hL hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_apply_beta».obs ev with
    ⟨m2, cs13, m34, deep, cons, rest, m68, cs79, cs97, rfl, ev15, ev81, ev99, rfl⟩ |
    ⟨m2, cs13, m34, deep, cons, rest, m68, cs79, v122, m123, cs133, v137, m147, cs155, cs182, rfl,
      ev15, ev81, ev157, ev135, ev184, rfl⟩ |
    ⟨m2, cs13, m34, deep, cons, rest, v67, m68, cs79, v222, m223, cs233, cs262, rfl, ev15, ev81,
      -, -, ev235, ev264, rfl⟩
  · -- `0 => apply_spine(lam, spine)`
    obtain ⟨Ts, D, rfl, hlenA, hlenC, hD, hcons, hrest, hlv⟩ :=
      applyBeta_prefix c hA ih ev15 (by lenlt) ev81 hL hAs
    have ext := (Heap.Extends.snoc _ _).trans (ev15.heap_extends.trans ev81.heap_extends)
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) ev99).applySpine rfl _ _ rfl d Γ _ As
      (RepEk.mono ext hL) (RepSpine.mono ext hAs), .refl⟩
  · -- `1 => whnf_with_spine(rc, expr_inst1(deep, lookup(consumed, 0), 0), rest, types)`
    obtain ⟨Ts, D, rfl, hlenA, hlenC, hD, hcons, hrest, hlit⟩ :=
      applyBeta_prefix c hA ih ev15 (by lenlt) ev81 hL hAs
    -- the consumed list is short: L0's bound, through `Lists::length`'s own calls
    obtain ⟨rom, hrv, hmemo⟩ := good.2.2.2
    have hlt := length_lt hrv hmemo ev81
      (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exacts [by simp, by simp [hx]]) hcons
    have hclen : ((As.take Ts.length).reverse ++ []).length = Ts.length := by simp; omega
    rw [hclen] at hlt
    have hn : Ts.length = 1 := by
      injection hlit with hlit
      exact field_lit_eq (m := 1) hlt (by norm_num) hlit.symm (by decide)
    obtain ⟨T1, rfl⟩ : ∃ T1, Ts = [T1] := by
      rcases Ts with _ | ⟨T1, _ | ⟨_, _⟩⟩
      · simp at hn
      · exact ⟨T1, rfl⟩
      · simp at hn
    obtain ⟨A1, As'', rfl⟩ : ∃ A1 As'', As = A1 :: As'' := by
      rcases As with _ | ⟨A1, As''⟩
      · simp at hlenA
      · exact ⟨A1, As'', rfl⟩
    have extg := ev81.heap_extends
    have hcons1 := hcons
    simp at hcons1
    have hA1 := hA.lookup0 _ _ _ _ _ ev157 d Γ A1 [] (RepSpine.mono extg hcons1)
    have extk := ev157.heap_extends
    have hD1 := hD
    simp at hD1
    have hbody := hA.inst1 _ _ _ _ _ _ ev135 d Γ D A1 (RepEk.mono (extg.trans extk) hD1) hA1
    have hrest1 := hrest
    simp at hrest1
    obtain ⟨E', hE', hred⟩ := (ih _ _ _ _ _ _ (by lenlt) ev184).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ _ As'' hbody
      (RepSpine.mono (extg.trans (extk.trans ev135.heap_extends)) hrest1)
    refine ⟨E', hE', ?_⟩
    show Red c.env d (K.mkAppN (.app (.lam T1 D nb) A1) As'') E'
    exact .trans (K.red_mkAppN As'' (.betaGate nb_isNever)) hred
  · -- `_ => whnf_with_spine(rc, expr_inst_many(deep, consumed, 0), rest, types)`
    obtain ⟨Ts, D, rfl, hlenA, hlenC, hD, hcons, hrest, hlv⟩ :=
      applyBeta_prefix c hA ih ev15 (by lenlt) ev81 hL hAs
    have extg := ev81.heap_extends
    have hclen : ((As.take Ts.length).reverse ++ []).length = Ts.length := by simp; omega
    have hDn := hD
    rw [show 0 + Ts.length = ((As.take Ts.length).reverse ++ []).length by rw [hclen]; simp]
      at hDn
    have hbody := hA.instMany _ _ _ _ _ _ ev235 d Γ D _ (RepEk.mono extg hDn)
      (RepSpine.mono extg hcons)
    obtain ⟨E', hE', hred⟩ := (ih _ _ _ _ _ _ (by lenlt) ev264).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ _ _ hbody
      (RepSpine.mono (extg.trans ev235.heap_extends) hrest)
    refine ⟨E', hE', ?_⟩
    have hchain := K.red_beta_chain (env := c.env) (d := d) (As.take Ts.length) Ts D
      (As.drop Ts.length) (by simp; omega)
    rw [List.take_append_drop] at hchain
    simp only [List.append_nil] at hred
    exact .trans hchain hred

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
  | other_Defn_n1_bind v1 m2 cs12 m140 p cs153 w1 w2 value w3 w4 m210 cs220 x cs270 ev14 ev155
      ld ev222 ev272 hc =>
    -- `Defn`, `(1, reduced) => whnf(rc, reduced, types)`: not taken on a represented value
    subst hc
    have ha1 := Bytes.repAddressRef_heapMono₂ addrTy ev14.heap_extends ha
    have hci := ci_rep hA good ev155 (by simp) (by memsub) (by lenlt) ha1
    obtain ⟨cvv, V, hn, hfind, hlp, hV⟩ := hci.defn _ _ _ _ _ ld
    obtain ⟨y, hy⟩ := hA.tryProjDef _ _ _ _ _ _ ev222 d Γ V (hV d Γ)
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hy
    exact absurd hy.1 (by decide)
  | other_Defn_other v1 m2 cs12 m140 p cs153 w1 w2 value w3 w4 v209 m210 cs220 v301 m302 cs312
      cs334 ev14 ev155 ld ev222 ev314 ev336 hc =>
    -- `Defn(_, _, value, _, _)`, `_ => whnf_with_spine(rc, expr_inst_levels(value, lvls), spine, types)`
    subst hc
    have extp := ev14.heap_extends
    have ha1 := Bytes.repAddressRef_heapMono₂ addrTy extp ha
    have hci := ci_rep hA good ev155 (by simp) (by memsub) (by lenlt) ha1
    have extg := ev155.heap_extends
    obtain ⟨cvv, V, hn, hfind, hlp, hV⟩ := hci.defn _ _ _ _ _ ld
    have hδ : Red c.env d (K.mkAppN (.const (c.κ a) []) As) (K.mkAppN V As) :=
      .delta (K.unfold_const_head As hfind hlp)
    have extj := ev222.heap_extends
    have ext3 := extp.trans (extg.trans extj)
    obtain ⟨rfl, rfl⟩ := (ih _ _ _ _ _ _ (by lenlt) ev314).instLevels rfl _ _ rfl
      (repList_heapMono₂ klevelListEnum repIxVMKUniv_heapMono₂ ext3 hls)
    obtain ⟨E', hE', hred2⟩ := (ih _ _ _ _ _ _ (by lenlt) ev336).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ V As (RepEc.mono extj hV d Γ)
      (RepSpine.mono ext3 hAs)
    exact ⟨E', hE', .trans hδ hred2⟩
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

end IxVM.Refinement.Core
