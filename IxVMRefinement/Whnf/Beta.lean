import IxVMRefinement.Whnf.Basic

/-! # Step lemmas of `KernelWhnf`: certified β and the telescope certificate

`peel_beta_cert` consumes an argument at a `λ` whose level the never-zero test accepts
(`Red.betaGate`) or whose argument's io-grade type (`k_infer_only`) is definitionally equal
(`k_is_def_eq`) to the domain under the arguments consumed so far (`inst_subs`): `Red.beta`.
The consumed arguments stand for the body's bound variables (`instantiateList`, the newest
innermost: `instantiateList_cons`). `beta_more` calls it where arguments remain and the body is a
`λ`. `certs_all` builds `CertsR … false`: a certificate per `∀` slot, and a `Red` step
(`whnf`) where the telescope is not syntactically a `∀`. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

namespace WhnfAux

/-- **No argument consumed**: the walk's claim at `m = 0`, returning its inputs. -/
theorem cert_stop {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {lam acc sp : SourceValue F}
    {L : KExpr} {Cs As : List KExpr} (hL : c.tmk d Γ Cs.length h L lam)
    (hCs : c.tml d Γ h Cs acc) (hAs : c.tml d Γ h As sp) :
    ∃ deep cons rest m D, (Value.tuple [lam, acc, sp] : SourceValue F) = .tuple [deep, cons, rest] ∧
      m ≤ As.length ∧ c.tmk d Γ (Cs.length + m) h D deep ∧
      c.tml d Γ h ((As.take m).reverse ++ Cs) cons ∧ c.tml d Γ h (As.drop m) rest ∧
      Red c.env d (Specs.Whnf.mkAppN (L.instantiateList Cs 0) (As.take m))
        (D.instantiateList ((As.take m).reverse ++ Cs) 0) := by
  refine ⟨lam, acc, sp, 0, L, rfl, Nat.zero_le _, hL, ?_, ?_, ?_⟩
  · simpa using hCs
  · simpa using hAs
  · simp only [List.take_zero, List.reverse_nil, List.nil_append]
    exact .refl

/-- The heap the certificate test of `peel_beta_cert` ends in extends the one it starts in. -/
theorem cert_seg_ext {a rest ty body bl rc lam sp acc types : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {cs : List (Call F)}
    (sg : Obs.«KernelWhnf::peel_beta_cert».Seg1 a rest ty body bl rc lam sp acc types h r h' cs) :
    Heap.Extends h h' := by
  rcases sg with ⟨m65, cs76, ev78, he91, he92, hc93⟩ |
    ⟨v64, m65, cs76, v98, m99, cs109, cs139, v144, m161, cs169, ev78, hne94, ev111, ev171, ev141,
      hc195⟩
  · subst he92; exact ObsFn.heap_extends ev78
  · exact (ObsFn.heap_extends ev78).trans ((ObsFn.heap_extends ev111).trans
      ((ObsFn.heap_extends ev171).trans (ObsFn.heap_extends ev141)))

end WhnfAux

/-- `KernelWhnf::peel_beta_cert`: the certified β walk (`Red.betaGate` at a `never` level,
`Red.beta` with the argument's io-grade type definitionally equal to the domain otherwise); it
stops at the first certificate that fails. -/
theorem peel_beta_cert_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::peel_beta_cert" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.peel_beta_cert c args h r h' calls := by
  intro rc lam sp acc types hargs good hrc d Γ htypes L Cs As hL hCs hAs
  subst hargs
  rcases Obs.«KernelWhnf::peel_beta_cert».obs ev with
    ⟨x_ty, x_body, x_bl, x_a, x_rest, m197, cs199, cs222, m252, ld12, ld46, sg204, hm260, ev224,
      hc287⟩ |
    ⟨x_ty, x_body, x_bl, x_a, x_rest, v196, m197, cs199, ld12, ld46, sg204, hne288, he297, he319,
      hc320⟩ |
    ⟨x_ty, x_body, x_bl, ld12, ld46, he333, he355, hc356⟩ |
    ⟨v1, ld12, hne358, he367, he389, hc390⟩
  · subst hm260 hc287
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hL.lam_of_load ld12
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld46
    have e0 := WhnfAux.cert_seg_ext sg204
    -- the step at this binder
    have hstep : Red c.env d (.app ((Ix.Kernel.Expr.lam T B (bmeta ℓ)).instantiateList Cs 0) A)
        (B.instantiateList (A :: Cs) 0) := by
      rw [WhnfAux.instantiateList_lam, Ix.Kernel.Expr.instantiateList_cons]
      rcases sg204 with ⟨m65, cs76, ev78, he91, he92, hc93⟩ |
        ⟨v64, m65, cs76, v98, m99, cs109, cs139, v144, m161, cs169, ev78, hne94, ev111, ev171,
          ev141, hc195⟩
      · subst hc93
        obtain ⟨hr1, -⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev78 x_bl rfl ℓ hℓ
        have hnz := WhnfAux.isNeverZero_of_answer hr1
        exact .betaGate (by rw [bmeta_of_isNeverZero hnz]; exact nbMeta_isNever)
      · subst hc195
        have e1 := ObsFn.heap_extends ev78
        have e2 := ObsFn.heap_extends ev111
        have e3 := ObsFn.heap_extends ev171
        obtain ⟨TA, hTA, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev111 rc x_a types rfl
          (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) A
          (Tm.mono e1 hA)
        have hdom := ih.get (.infer .inst_subs) (by lt_calls) ev171 x_ty acc rfl
          (good.sub fun x hx => by simp [hx]) d Γ Cs T (tml_mono (e1.trans e2) hCs)
          (Tm.mono (e1.trans e2) hT)
        have ext := e1.trans (e2.trans e3)
        have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev141 rc v98 v144 types rfl
          (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) TA
          _ (Tm.mono e3 hTA) hdom field_one_ne_zero
        exact .beta hinf hde
    -- the rest of the walk
    have ext0 : Heap.Extends h (m197 ++ [.construct kexprListEnum "Cons" [x_a, acc]]) :=
      e0.trans (Heap.Extends.snoc _ _)
    have hacc : c.tml d Γ (m197 ++ [.construct kexprListEnum "Cons" [x_a, acc]]) (A :: Cs)
        (.ptr (.enum kexprListEnum) m197.length) :=
      TmL.store_cons (Tm.mono e0 hA) (tml_mono e0 hCs)
    obtain ⟨deep, cons, rest, m, D, hr, hm, hD, hcons, hrest, hred⟩ :=
      ih.get (.whnf .peel_beta_cert) (by lt_calls) ev224 rc x_body x_rest _ types rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono ext0 hrc) d Γ (types_mono ext0 htypes)
        B (A :: Cs) As' (Tm.mono ext0 hB) hacc (tml_mono ext0 hAs')
    refine ⟨deep, cons, rest, m + 1, D, hr, by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_⟩
    · have e : (A :: Cs).length + m = Cs.length + (m + 1) := by
        simp only [List.length_cons]; omega
      rw [← e]; exact hD
    · simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hcons
    · simpa using hrest
    · have hlist : ((A :: As').take (m + 1)).reverse ++ Cs = (As'.take m).reverse ++ A :: Cs := by
        simp [List.take_succ_cons, List.reverse_cons, List.append_assoc]
      rw [hlist, List.take_succ_cons]
      show Red c.env d (Ix.Kernel.Expr.mkAppN
        (.app ((Ix.Kernel.Expr.lam T B (bmeta ℓ)).instantiateList Cs 0) A) (As'.take m)) _
      exact .trans (red_mkAppN (As'.take m) hstep) hred
  · subst he297 he319 hc320
    have e0 := WhnfAux.cert_seg_ext sg204
    exact WhnfAux.cert_stop (Tm.mono e0 hL) (tml_mono e0 hCs) (tml_mono e0 hAs)
  · subst he333 he355
    exact WhnfAux.cert_stop hL hCs hAs
  · subst he367 he389
    exact WhnfAux.cert_stop hL hCs hAs

/-- `KernelWhnf::beta_more`: `peel_beta_cert` where arguments remain and the body is a `λ`;
otherwise no argument is consumed. -/
theorem beta_more_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::beta_more" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.beta_more c args h r h' calls := by
  intro rc deep rest cons types hargs good hrc d Γ htypes L Cs As hL hCs hAs
  subst hargs
  rcases Obs.«KernelWhnf::beta_more».obs ev with
    ⟨ld12, he25, he47, hc48⟩ |
    ⟨w56, w57, w87, w88, w89, cs108, ld12, ld79, ev110, hc151⟩ |
    ⟨w56, w57, v68, ld12, ld79, hne152, he161, he183, hc184⟩
  · subst he25 he47
    exact WhnfAux.cert_stop hL hCs hAs
  · subst hc151
    exact ih.get (.whnf .peel_beta_cert) (by lt_calls) ev110 rc deep rest cons types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes L Cs As hL hCs hAs
  · subst he161 he183
    exact WhnfAux.cert_stop hL hCs hAs

/-- `KernelWhnf::certs_all`: a nonzero answer is the unlicensed telescope certificate, up to
reduction of the telescope (`CertsR … false`). -/
theorem certs_all_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::certs_all" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.certs_all c args h r h' calls := by
  intro rc t zs subs types hargs good hrc d Γ htypes T Cs As hT hCs hAs hr
  subst hargs
  rcases Obs.«KernelWhnf::certs_all».obs ev with
    ⟨ld12, he20, he21, hc22⟩ |
    ⟨x_a, x_rest, x_dom, x_cod, w59, v75, m76, cs86, m114, cs125, v130, m147, cs155, cs188, m218,
      ld12, ld51, ev88, ev157, ev127, hm226, ev190, hc253⟩ |
    ⟨x_a, x_rest, x_dom, x_cod, w59, v75, m76, cs86, v113, m114, cs125, v130, m147, cs155, ld12,
      ld51, ev88, ev157, ev127, hne254, he258, he259, hc260⟩ |
    ⟨x_a, x_rest, v40, v265, m266, cs276, v280, m290, cs298, w343, w344, w345, cs364, m394, ld12,
      ld51, hne261, ev300, ev278, ld335, hm402, ev366, hc413⟩ |
    ⟨x_a, x_rest, v40, v265, m266, cs276, v280, m290, cs298, v324, ld12, ld51, hne261, ev300,
      ev278, ld335, hne414, he418, he419, hc420⟩
  · obtain rfl := RepList.nil_of_load hAs ld12
    exact .nil
  · subst hm226 hc253
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hT.forallE_of_load ld51
    obtain ⟨TA, hTA, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev88 rc x_a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e1 := ObsFn.heap_extends ev88
    have e2 := ObsFn.heap_extends ev157
    have e3 := ObsFn.heap_extends ev127
    have hdom := ih.get (.infer .inst_subs) (by lt_calls) ev157 x_dom subs rfl
      (good.sub fun x hx => by simp [hx]) d Γ Cs D (tml_mono e1 hCs) (Tm.mono e1 hD)
    have ext := e1.trans e2
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev127 rc v75 v130 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) TA _
      (Tm.mono e2 hTA) hdom field_one_ne_zero
    have ext3 := ext.trans e3
    have ext0 : Heap.Extends h (m114 ++ [.construct kexprListEnum "Cons" [x_a, subs]]) :=
      ext3.trans (Heap.Extends.snoc _ _)
    have hsubs : c.tml d Γ (m114 ++ [.construct kexprListEnum "Cons" [x_a, subs]]) (A :: Cs)
        (.ptr (.enum kexprListEnum) m114.length) :=
      TmL.store_cons (Tm.mono ext3 hA) (tml_mono ext3 hCs)
    have hrec := ih.get (.whnf .certs_all) (by lt_calls) ev190 rc x_cod x_rest _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext0 hrc) d Γ (types_mono ext0 htypes) B
      (A :: Cs) As' (Tm.mono ext0 hB) hsubs (tml_mono ext0 hAs') hr
    have hrec' : Specs.Whnf.CertsR c.env d false
        ((B.instantiateList Cs (0 + 1)).instantiate1 A 0) As' := by
      rw [← Ix.Kernel.Expr.instantiateList_cons]; exact hrec
    rw [WhnfAux.instantiateList_forallE]
    exact .cert hinf hde hrec'
  · exact (hr he258).elim
  · subst hm402 hc413
    have e1 := ObsFn.heap_extends ev300
    have e2 := ObsFn.heap_extends ev278
    have hinst := ih.get (.infer .inst_subs) (by lt_calls) ev300 t subs rfl
      (good.sub fun x hx => by simp [hx]) d Γ Cs T hCs hT
    obtain ⟨TW, hTW, hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev278 rc v280 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) _ hinst
    have ext := e1.trans e2
    have ext0 : Heap.Extends h (m266 ++ [.construct kexprListEnum "Nil" []]) :=
      ext.trans (Heap.Extends.snoc _ _)
    have hrec := ih.get (.whnf .certs_all) (by lt_calls) ev366 rc v265 zs _ types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext0 hrc) d Γ (types_mono ext0 htypes) TW
      [] As (Tm.mono (Heap.Extends.snoc _ _) hTW) (TmL.store_nil m266) (tml_mono ext0 hAs) hr
    rw [Ix.Kernel.Expr.instantiateList_nil] at hrec
    exact .red hred hrec
  · exact (hr he418).elim

end IxVM.Refinement.Core
