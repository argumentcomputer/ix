import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Open
import IxVMRefinement.Obs.KernelWhnf
import IxVMRefinement.Obs.KernelTypes
import IxVMRefinement.Obs.KernelLevels
import IxC.Kernel.Verify.InstLevels
import IxVMRefinement.Lib.Lists
import IxC.Kernel.Verify.InstList

/-! # Step lemmas of `KernelWhnf`, on the registry

Each lemma takes the derivation's path from the generated path lemma, reads its callees' specs
from the induction hypothesis (`IH.get`), and concludes the function's registered spec. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

/-! ## Helpers -/

/-- A callee's derivation has fewer calls than its caller's. -/
macro "lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

theorem types_mono {c : Ctx} {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {d : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : c.types Γ h₁ d p) : c.types Γ h₂ d p :=
  ⟨r.1.mono ext, r.2⟩

theorem tml_mono {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {Es : List KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : c.tml d Γ h₁ Es p) : c.tml d Γ h₂ Es p :=
  TmL.mono ext r

/-- A level the never-zero test accepts has the datum `never`. -/
theorem bmeta_of_isNeverZero {ℓ : KLevel} (h : ℓ.isNeverZero = true) :
    bmeta ℓ = Specs.Whnf.nbMeta := by
  have e := Ix.Kernel.Level.isNeverZero_eq_isNever ℓ
  rw [h] at e
  have := Ix.Kernel.PropWhen.isNever_iff.mp e.symm
  simp [bmeta, Specs.Whnf.nbMeta, this]

theorem field_one_ne_zero : (Value.field (1 : F) : SourceValue F) ≠ .field 0 := by
  intro h
  injection h with h
  exact one_ne_zero h

/-! ## `peel_beta` -/

/-- `KernelWhnf::peel_beta` consumes the arguments of the `λ`s whose level the never-zero test
accepts. -/
theorem peel_beta_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::peel_beta" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.peel_beta c args h r h' calls := by
  intro lam sp acc hargs good d Γ k L As Cs hL hAs hCs
  subst hargs
  rcases Obs.«KernelWhnf::peel_beta».obs ev with
    ⟨w20, x_body, x_bl, x_a, x_rest, m66, cs77, cs95, m116, ld12, ld47, ev79, hm124, ev97,
      hc144⟩ |
    ⟨w20, x_body, x_bl, x_a, x_rest, v65, m66, cs77, ld12, ld47, ev79, hne145, he154, he176,
      hc177⟩ |
    ⟨w20, x_body, x_bl, ld12, ld47, he190, he212, hc213⟩ |
    ⟨v1, ld12, hne215, he224, he246, hc247⟩
  · -- a `λ` with an argument, the level never zero: consume it
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hL.lam_of_load ld12
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld47
    subst hc144 hm124
    obtain ⟨hr1, -⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev79 x_bl rfl ℓ hℓ
    have hnz : ℓ.isNeverZero = true := by
      by_contra hn
      have h10 : (Value.field (1 : F) : SourceValue F) = .field 0 := by rw [hr1, ite_eq_right hn]
      exact field_one_ne_zero h10
    have e1 := ObsFn.heap_extends ev79
    have ext : Heap.Extends h (m66 ++ [.construct kexprListEnum "Cons" [x_a, acc]]) :=
      e1.trans (Heap.Extends.snoc _ _)
    have hacc : c.tml d Γ (m66 ++ [.construct kexprListEnum "Cons" [x_a, acc]]) (A :: Cs)
        (.ptr (.enum kexprListEnum) m66.length) :=
      TmL.store_cons (Tm.mono e1 hA) (TmL.mono e1 hCs)
    obtain ⟨deep, cons, rest, Ts, D, hr, hBD, hlen, hD, hcons, hrest⟩ :=
      ih.get (.whnf .peel_beta) (by lt_calls) ev97 x_body x_rest _ rfl
        (good.sub fun x hx => by simp [hx]) d Γ (k + 1) B As' (A :: Cs)
        (Tm.mono ext hB) (tml_mono ext hAs') hacc
    refine ⟨deep, cons, rest, T :: Ts, D, hr, ?_, by simp; omega, ?_, ?_, ?_⟩
    · rw [bmeta_of_isNeverZero hnz, hBD]; rfl
    · have e : k + (T :: Ts).length = k + 1 + Ts.length := by
        simp only [List.length_cons]; omega
      rw [e]; exact hD
    · simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hcons
    · simpa using hrest
  · -- the level may be zero: stop
    obtain ⟨T, B, ℓ, rfl, -, -, hℓ⟩ := hL.lam_of_load ld12
    subst hc177
    have e1 := ObsFn.heap_extends ev79
    subst he154 he176
    exact ⟨lam, acc, sp, [], _, rfl, rfl, by simp, Tm.mono e1 hL, by simpa using TmL.mono e1 hCs,
      by simpa using TmL.mono e1 hAs⟩
  · -- no argument left: stop
    subst he190 he212
    exact ⟨lam, acc, sp, [], _, rfl, rfl, by simp, hL, by simpa using hCs, by simpa using hAs⟩
  · -- not a `λ`: stop
    subst he224 he246
    exact ⟨lam, acc, sp, [], _, rfl, rfl, by simp, hL, by simpa using hCs, by simpa using hAs⟩

/-! ## The normalizers -/

/-- `KernelWhnf::whnf_core` is `whnf_with_spine` at the empty spine. -/
theorem whnf_core_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_core" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨cs4, m26, hm34, ev6, hc45⟩ := Obs.«KernelWhnf::whnf_core».obs ev
  subst hc45 hm34
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
  obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_with_spine) (by lt_calls) ev6 rc e _ types rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) E []
    (Tm.mono ext hE) (TmL.store_nil h)
  exact ⟨E', hE', hred⟩

/-- `KernelWhnf::whnf`: a value form is its own normal form; any other term is head-normalized
under the context cut to its loose bound variables (`ctx_trim`), which keeps the depth and the
ghost context. -/
theorem whnf_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelWhnf::whnf».obs ev with
    ⟨w20, ld12, he27, he28, hc29⟩ | ⟨w37, ld12, he44, he45, hc46⟩ |
    ⟨w54, w55, w56, ld12, he73, he74, hc75⟩ | ⟨w83, w84, w85, ld12, he102, he103, hc104⟩ |
    ⟨w112, ld12, he119, he120, hc121⟩ |
    ⟨v1, cs129, v134, m150, cs158, v162, m171, cs179, ld12, hne30, hne47, hne76, hne105, hne122,
      ev181, ev160, ev131, hc190⟩
  · subst he27 he28; exact ⟨E, hE, .refl⟩
  · subst he44 he45; exact ⟨E, hE, .refl⟩
  · subst he73 he74; exact ⟨E, hE, .refl⟩
  · subst he102 he103; exact ⟨E, hE, .refl⟩
  · subst he119 he120; exact ⟨E, hE, .refl⟩
  · subst hc190
    have g1 : Good c cs179 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs158 := good.sub fun x hx => by simp [hx]
    have g3 : Good c cs129 := good.sub fun x hx => by simp [hx]
    obtain ⟨hm171, -⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev181 e rfl g1
    subst m171
    have htr := ih.get (.subst .ctx_trim) (by lt_calls) ev160 types v162 rfl g2 Γ d htypes
    have ext := ObsFn.heap_extends ev160
    exact ih.get (.whnf .whnf_core) (by lt_calls) ev131 rc e v134 rfl g3 (RCRep.mono ext hrc) d Γ
      htr E (Tm.mono ext hE)

/-- `KernelWhnf::whnf_spine` head-normalizes each argument. -/
theorem whnf_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_spine c args h r h' calls := by
  intro rc sp types hargs good hrc d Γ htypes As hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_spine».obs ev with
    ⟨ld12, he24, hm23, hc28⟩ |
    ⟨x_a, x_rest, v46, m47, cs57, v93, m102, cs110, ld12, ev59, he88, hm87, ev112, hc137⟩
  · obtain rfl := RepList.nil_of_load hAs ld12
    subst he24 hm23
    exact ⟨[], TmL.store_nil h, .nil⟩
  · obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    subst hc137 he88 hm87
    have g1 : Good c cs57 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs110 := good.sub fun x hx => by simp [hx]
    obtain ⟨A', hA', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev59 rc x_a types rfl g1 hrc d Γ
      htypes A hA
    have ext1 := ObsFn.heap_extends ev59
    obtain ⟨Bs, hBs, hreds⟩ := ih.get (.whnf .whnf_spine) (by lt_calls) ev112 rc x_rest types rfl g2
      (RCRep.mono ext1 hrc) d Γ (types_mono ext1 htypes) As' (tml_mono ext1 hAs')
    have ext2 := ObsFn.heap_extends ev112
    exact ⟨A' :: Bs, TmL.store_cons (Tm.mono ext2 hA') hBs, .cons hred hreds⟩

/-! ## The spine normalizer -/

theorem mkAppN_mkAppN (H : KExpr) :
    ∀ (xs ys : List KExpr),
      Ix.Kernel.Expr.mkAppN (Ix.Kernel.Expr.mkAppN H xs) ys = Ix.Kernel.Expr.mkAppN H (xs ++ ys)
  | [], _ => rfl
  | x :: xs, ys => mkAppN_mkAppN (.app H x) xs ys

/-- `KernelWhnf::whnf_with_spine`: an application's spine is collected and appended; a `λ` head
takes a β step (`red_beta`); a constant head goes to `whnf_const_head`; a `let` head is
replaced by its instantiation, which is its image; a projection head goes to `whnf_proj_head`;
any other head is stuck. `Red` of the applied head throughout. -/
theorem whnf_with_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_with_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_with_spine c args h r h' calls := by
  intro rc hd sp types hargs good hrc d Γ htypes H As hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_with_spine».obs ev with
    ⟨x_f, x_a, m31, cs42, x_ih, x_is, cs72, v77, m94, cs102, ld12, ev44, ev104, ev74, hc128⟩ |
    ⟨x_ty, x_body, w137, m154, cs165, x_reduct, x_rest, cs226, ld12, ev167, ev228, hc261⟩ |
    ⟨x_ty, x_body, w137, v153, m154, cs165, cs268, ld12, ev167, ev270, hc287⟩ |
    ⟨x_addr, x_lvls, cs308, ld12, ev310, hc359⟩ |
    ⟨w367, x_val, x_body, v383, m384, cs394, cs423, ld12, ev396, ev425, hc458⟩ |
    ⟨x_sa, x_fidx, x_inner, cs484, ld12, ev486, hc535⟩ |
    ⟨v1, cs543, ld12, hne130, hne288, hne360, hne459, hne536, ev545, hc562⟩
  · -- an application: collect its spine and go on with the appended spine
    subst hc128
    have e0 := ObsFn.heap_extends ev44
    have e1 := ObsFn.heap_extends ev104
    obtain ⟨ih', is', H', As', he, hH', hAs', rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev44 hd rfl
        (good.sub fun x hx => by simp [hx]) d Γ 0 H hH
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    have hcat := Lib.Lists.concat_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
      (R := TmE c.κ d Γ) tmE_heapMono₂ (xs := As') (ys := As)
      (by rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev104)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs')
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono e0 hAs)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hcat
    have ext := e0.trans e1
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_with_spine) (by lt_calls) ev74 rc _ v77 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      H' (As' ++ As) (Tm.mono e1 hH') hcat
    refine ⟨E', hE', ?_⟩
    rw [show Specs.Whnf.mkAppN (Ix.Kernel.Expr.mkAppN H' As') As = Specs.Whnf.mkAppN H' (As' ++ As)
      from mkAppN_mkAppN H' As' As]
    exact hred
  · -- a `λ` head that takes a β step
    subst hc261
    obtain ⟨E, Bs, hE, hBs, hred⟩ := ih.get (.whnf .red_beta) (by lt_calls) ev167 rc hd sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes H As hH hAs x_reduct x_rest rfl
    have ext := ObsFn.heap_extends ev167
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_with_spine) (by lt_calls) ev228 rc x_reduct
      x_rest types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) E Bs hE hBs
    exact ⟨E', hE', .trans hred hred'⟩
  · -- a `λ` head that takes no step: stuck
    subst hc287
    have ext := ObsFn.heap_extends ev167
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev270 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 H As (Tm.mono ext hH) (tml_mono ext hAs)
    exact ⟨_, happ, .refl⟩
  · -- a constant head
    subst hc359
    obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld12
    exact ih.get (.whnf .whnf_const_head) (by lt_calls) ev310 rc x_addr x_lvls hd sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a us As ha hus hH hAs
  · -- a `let` head: its instantiation is its image
    subst hc458
    obtain ⟨T, V, B, rfl, hT, hV, hB⟩ := hH.letE_of_load ld12
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev396 x_body x_val 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B V (by simpa using hB) hV
    simp only [ZMod.val_zero] at hinst
    rw [← instShift_eq_instantiate1 (Tm.looseBVarsBounded hV)] at hinst
    have ext := ObsFn.heap_extends ev396
    exact ih.get (.whnf .whnf_with_spine) (by lt_calls) ev425 rc v383 sp types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      (instShift V 0 B) As hinst (tml_mono ext hAs)
  · -- a projection head
    subst hc535
    obtain ⟨s, i, S, rfl, rfl, hs, hS⟩ := hH.proj_of_load ld12
    exact ih.get (.whnf .whnf_proj_head) (by lt_calls) ev486 rc x_sa (.field i) x_inner sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes s i S As hs rfl hS hAs
  · -- any other head: stuck
    subst hc562
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev545 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 H As hH hAs
    exact ⟨_, happ, .refl⟩

/-! ## β -/

theorem red_mkAppN {env : Ix.Kernel.Env .anon} {d : Nat} : ∀ (As : List KExpr) {f f' : KExpr},
    Red env d f f' → Red env d (Ix.Kernel.Expr.mkAppN f As) (Ix.Kernel.Expr.mkAppN f' As)
  | [], _, _, h => h
  | _ :: As, _, _, h => red_mkAppN As (.appFn h)

theorem lamsNb_instantiate1 : ∀ (Ts : List KExpr) (D v : KExpr) (k : Nat),
    ∃ Ts' : List KExpr, Ts'.length = Ts.length ∧
      (Specs.Whnf.lamsNb Ts D).instantiate1 v k =
        Specs.Whnf.lamsNb Ts' (D.instantiate1 v (k + Ts.length))
  | [], D, v, k => ⟨[], rfl, by simp [Specs.Whnf.lamsNb]⟩
  | T :: Ts, D, v, k => by
    obtain ⟨Ts', hlen, heq⟩ := lamsNb_instantiate1 Ts D v (k + 1)
    refine ⟨T.instantiate1 v k :: Ts', by simp [hlen], ?_⟩
    have hk : k + 1 + Ts.length = k + (T :: Ts).length := by simp only [List.length_cons]; omega
    show Ix.Kernel.Expr.instantiate1 (.lam T (Specs.Whnf.lamsNb Ts D) Specs.Whnf.nbMeta) v k = _
    rw [Ix.Kernel.Expr.instantiate1, heq, hk]
    rfl

theorem nbMeta_isNever : Specs.Whnf.nbMeta.pw.isNever = true := Ix.Kernel.PropWhen.isNever_never

/-- **The β chain**: a `never`-datum `λ`-telescope applied to as many arguments as it has
binders, then to `rest`, reduces to its body under the reversed arguments, applied to `rest`
(`Red.betaGate` along the spine). -/
theorem red_beta_chain {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (Ts : List KExpr) (D : KExpr) (rest : List KExpr),
      Ts.length = As.length →
      Red env d (Ix.Kernel.Expr.mkAppN (Specs.Whnf.lamsNb Ts D) (As ++ rest))
        (Ix.Kernel.Expr.mkAppN (D.instantiateList As.reverse 0) rest)
  | [], Ts, D, rest, hlen => by
    match Ts, hlen with
    | [], _ =>
      show Red env d (Ix.Kernel.Expr.mkAppN D rest)
        (Ix.Kernel.Expr.mkAppN (D.instantiateList [] 0) rest)
      rw [Ix.Kernel.Expr.instantiateList_nil]
      exact .refl
    | _ :: _, hlen => simp at hlen
  | A :: As, Ts, D, rest, hlen => by
    match Ts, hlen with
    | [], hlen => simp at hlen
    | T :: Ts, hlen =>
      have hlen' : Ts.length = As.length := by simpa using hlen
      obtain ⟨Ts', hlen'', heq⟩ := lamsNb_instantiate1 Ts D A 0
      have hstep : Red env d
          (Ix.Kernel.Expr.mkAppN (Specs.Whnf.lamsNb (T :: Ts) D) ((A :: As) ++ rest))
          (Ix.Kernel.Expr.mkAppN (Specs.Whnf.lamsNb Ts' (D.instantiate1 A (0 + Ts.length)))
            (As ++ rest)) := by
        show Red env d (Ix.Kernel.Expr.mkAppN
          (.app (.lam T (Specs.Whnf.lamsNb Ts D) Specs.Whnf.nbMeta) A) (As ++ rest)) _
        rw [← heq]
        exact red_mkAppN _ (.betaGate nbMeta_isNever)
      have hrest := red_beta_chain (env := env) (d := d) As Ts' (D.instantiate1 A (0 + Ts.length))
        rest (by rw [hlen'', hlen'])
      have hfold : (D.instantiate1 A (0 + Ts.length)).instantiateList As.reverse 0 =
          D.instantiateList (A :: As).reverse 0 := by
        rw [List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one, List.length_reverse,
          hlen']
      rw [hfold] at hrest
      exact .trans hstep hrest

/-- The common prefix of `red_beta`'s paths: `peel_beta` from the empty accumulator, then
`beta_more`; the reduct to substitute, the consumed arguments (innermost first) and the rest
of the spine, with the `Red` chain from the applied `λ` to the substituted body applied to the
rest. -/
theorem red_beta_common (c : Ctx) {calls : List (Call F)} (ih : IH c calls) (good : Good c calls)
    {rc lam sp types deep cons rest deep2 cons2 rest2 : SourceValue F} {h m2 m68 : Heap F}
    {cs13 cs79 : List (Call F)}
    (ev15 : ObsFn W "KernelWhnf::peel_beta" [lam, sp, .ptr (.enum kexprListEnum) h.length]
      (h ++ [.construct kexprListEnum "Nil" []]) (.tuple [deep, cons, rest]) m2 cs13)
    (ev81 : ObsFn W "KernelWhnf::beta_more" [rc, deep, rest, cons, types] m2
      (.tuple [deep2, cons2, rest2]) m68 cs79)
    (hlt1 : cs13.length < calls.length) (hlt2 : cs79.length < calls.length)
    (hsub1 : ∀ x ∈ cs13, x ∈ calls) (hsub2 : ∀ x ∈ cs79, x ∈ calls)
    (hrc : c.rc h rc) {d : Nat} {Γ : Nat → KExpr} (htypes : c.types Γ h d types)
    {L : KExpr} {As : List KExpr} (hL : c.tm d Γ h L lam) (hAs : c.tml d Γ h As sp) :
    ∃ D2 Cs2 Bs, c.tmk d Γ Cs2.length m68 D2 deep2 ∧ c.tml d Γ m68 Cs2 cons2 ∧
      c.tml d Γ m68 Bs rest2 ∧
      Red c.env d (Ix.Kernel.Expr.mkAppN L As)
        (Ix.Kernel.Expr.mkAppN (D2.instantiateList Cs2 0) Bs) := by
  have e00 : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
  have e0 := ObsFn.heap_extends ev15
  obtain ⟨deep', cons', rest', Ts, D, hres, rfl, hlen, hD, hcons, hrest⟩ :=
    ih.get (.whnf .peel_beta) hlt1 ev15 lam sp _ rfl (good.sub hsub1) d Γ 0 L As []
      (Tm.mono e00 hL) (tml_mono e00 hAs) (TmL.store_nil h)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hres
  obtain ⟨rfl, rfl, rfl⟩ := hres
  rw [Nat.zero_add] at hD
  rw [List.append_nil] at hcons
  have hclen : ((As.take Ts.length).reverse).length = Ts.length := by
    simp only [List.length_reverse, List.length_take]; omega
  have ext0 := e00.trans e0
  obtain ⟨deep'', cons'', rest'', m, D', hres', hm, hD', hcons', hrest', hred'⟩ :=
    ih.get (.whnf .beta_more) hlt2 ev81 rc _ _ _ types rfl (good.sub hsub2)
      (RCRep.mono ext0 hrc) d Γ (types_mono ext0 htypes)
      D (As.take Ts.length).reverse (As.drop Ts.length) (by rw [hclen]; exact hD) hcons hrest
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hres'
  obtain ⟨rfl, rfl, rfl⟩ := hres'
  refine ⟨D', ((As.drop Ts.length).take m).reverse ++ (As.take Ts.length).reverse,
    (As.drop Ts.length).drop m, ?_, hcons', hrest', ?_⟩
  · have e : (((As.drop Ts.length).take m).reverse ++ (As.take Ts.length).reverse).length =
        (As.take Ts.length).reverse.length + m := by
      simp only [List.length_drop] at hm
      simp only [List.length_append, List.length_reverse, List.length_take, List.length_drop]
      omega
    rw [e]; exact hD'
  · have h1 := red_beta_chain (env := c.env) (d := d) (As.take Ts.length) Ts D
      (As.drop Ts.length) (by simp only [List.length_take]; omega)
    rw [List.take_append_drop] at h1
    have h2 : Red c.env d
        (Ix.Kernel.Expr.mkAppN
          (Ix.Kernel.Expr.mkAppN (D.instantiateList (As.take Ts.length).reverse 0)
            ((As.drop Ts.length).take m)) ((As.drop Ts.length).drop m))
        (Ix.Kernel.Expr.mkAppN (D'.instantiateList (((As.drop Ts.length).take m).reverse ++
          (As.take Ts.length).reverse) 0) ((As.drop Ts.length).drop m)) :=
      red_mkAppN _ hred'
    rw [mkAppN_mkAppN, List.take_append_drop] at h2
    exact .trans h1 h2

/-- `KernelWhnf::red_beta`: the `never`-datum binders (`peel_beta`), then the certified ones
(`beta_more`), the consumed arguments substituted at once; tag `1` is a `Red` of the applied
`λ` to the applied reduct. -/
theorem red_beta_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_beta" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.red_beta c args h r h' calls := by
  intro rc lam sp types hargs good hrc d Γ htypes L As hL hAs x y hr
  subst hargs
  rcases Obs.«KernelWhnf::red_beta».obs ev with
    ⟨m2, cs13, m34, x_deep, x_cons, x_rest, m68, cs79, x_deep2, x_cons2, x_rest2, hm42, ev15,
      ev81, ld154, he167, he188, hc189⟩ |
    ⟨m2, cs13, m34, x_deep, x_cons, x_rest, m68, cs79, x_deep2, x_cons2, x_rest2, x_a, x_more,
      v229, m239, cs247, hm42, ev15, ev81, ld154, ld218, he231, ev249, he280, hc281⟩ |
    ⟨m2, cs13, m34, x_deep, x_cons, x_rest, m68, cs79, x_deep2, x_cons2, x_rest2, x_a, x_more,
      w289, w290, v304, m314, cs322, hm42, ev15, ev81, ld154, ld218, he306, ev324, he355, hc356⟩
  · -- nothing consumed: tag `0`
    rw [hr] at he167
    injection he167 with he
    injection he with he1 _
    injection he1 with he2
    exact (one_ne_zero he2).elim
  · -- one argument consumed: `expr_inst1`
    subst hm42 hc281 he280
    obtain ⟨D2, Cs2, Bs, hD2, hCs2, hBs, hred⟩ := red_beta_common c ih good ev15 ev81
      (by lt_calls) (by lt_calls) (fun x hx => by simp [hx]) (fun x hx => by simp [hx]) hrc
      htypes hL hAs
    obtain ⟨A, Cs2', rfl, hA, hCs2'⟩ := RepList.cons_of_load hCs2 ld154
    obtain rfl := RepList.nil_of_load hCs2' ld218
    rw [hr] at he231
    injection he231 with he
    injection he with _ he
    injection he with hx he
    injection he with hy _
    subst hx hy
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev249 _ _ 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ D2 A (by simpa using hD2) hA
    simp only [ZMod.val_zero] at hinst
    have e := ObsFn.heap_extends ev249
    refine ⟨D2.instantiate1 A 0, Bs, hinst, tml_mono e hBs, ?_⟩
    have hone : D2.instantiateList [A] 0 = D2.instantiate1 A 0 := by
      have := Ix.Kernel.Expr.instantiateList_append_one [] D2 A 0
      simpa [Ix.Kernel.Expr.instantiateList_nil] using this
    rw [← hone]
    exact hred
  · -- several arguments consumed: `expr_inst_many`
    subst hm42 hc356 he355
    obtain ⟨D2, Cs2, Bs, hD2, hCs2, hBs, hred⟩ := red_beta_common c ih good ev15 ev81
      (by lt_calls) (by lt_calls) (fun x hx => by simp [hx]) (fun x hx => by simp [hx]) hrc
      htypes hL hAs
    rw [hr] at he306
    injection he306 with he
    injection he with _ he
    injection he with hx he
    injection he with hy _
    subst hx hy
    have hinst := ih.get (.subst .expr_inst_many) (by lt_calls) ev324 _ _ 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ D2 Cs2 (by simpa using hD2) hCs2
    simp only [ZMod.val_zero] at hinst
    have e := ObsFn.heap_extends ev324
    exact ⟨_, Bs, hinst, tml_mono e hBs, hred⟩


/-! ## Spines -/

/-- `KernelTypes::collect_spine`: the head and the arguments of an application, under any number
of local binders. -/
theorem collect_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.collect_spine c args h r h' calls := by
  intro e hargs good d Γ k E hE
  subst hargs
  rcases Obs.«KernelTypes::collect_spine».obs ev with
    ⟨x_f, x_a, m31, cs41, x_head, x_args, v68, m78, cs86, ld12, ev43, he69, ev88, he105, hc106⟩ |
    ⟨v1, m124, ld12, hne107, he115, hm132, he136, hc137⟩
  · subst hc106 he69 he105
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld12
    obtain ⟨hd, sp, H, As, hres, hH, hAs, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev43 x_f rfl (good.sub fun x hx => by simp [hx]) d Γ k Ef hf
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hres
    obtain ⟨rfl, rfl⟩ := hres
    have e0 := ObsFn.heap_extends ev43
    have e1 := ObsFn.heap_extends ev88
    have hR : HeapMono₂ (fun h E p => Tm c.κ d Γ h k E p) := fun _ _ _ _ ext r => Tm.mono ext r
    have hsnoc := Lib.Lists.snoc_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) hR
      (xs := As) (x := Ea)
      (by rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev88)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs)
      (Tm.mono e0 ha)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hsnoc
    refine ⟨_, _, H, As ++ [Ea], rfl, Tm.mono e1 hH, hsnoc, ?_⟩
    rw [← mkAppN_mkAppN]
    rfl
  · subst he115 hm132 he136
    have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
    exact ⟨_, _, E, [], rfl, Tm.mono ext hE, .nil (by simp), rfl⟩

/-! ## Level instantiation -/

/-- `KernelLevels::expr_inst_levels`: the identity at the empty level list, the walk
otherwise. -/
theorem expr_inst_levels_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::expr_inst_levels" args h r h' calls) (ih : IH c calls) :
    Specs.Subst.expr_inst_levels c args h r h' calls := by
  intro e params hargs good Γ k E us hE hus
  subst hargs
  rcases Obs.«KernelLevels::expr_inst_levels».obs ev with
    ⟨ld12, he21, he22, hc23⟩ | ⟨v1, cs31, ld12, hne24, ev33, hc50⟩
  · subst he21
    subst h'
    obtain ⟨ls, hls, hEq⟩ := hus
    have ld' : loadValue h params =
        .ok (.construct IxVM.Refinement.KernelLevels.klevelListEnum "Nil" []) := by
      rw [← klevelListEnum_eq]; exact ld12
    obtain rfl := RepList.nil_of_load hls ld'
    obtain rfl : us = [] := by
      cases us with
      | nil => rfl
      | cons u us =>
        have h0 := hEq (fun _ => 0)
        simp [Ix.Kernel.Level.EvalEqList] at h0
    have hself := Ix.Kernel.Expr.instantiateLevelParams_self [] E
    simp only [List.map_nil] at hself
    simp only [List.length_nil, List.range_zero, hself]
    exact hE
  · subst hc50
    exact ih.get (.subst .expr_inst_levels_walk) (by lt_calls) ev33 e params rfl
      (good.sub fun x hx => by simp [hx]) Γ k E us hE hus

/-! ## Constant heads -/

theorem getAppFn_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (Ix.Kernel.Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Ix.Kernel.Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [getAppFn_mkAppN As (.app f a)]
    rfl

theorem getAppArgs_mkAppN : ∀ (As : List KExpr) (f : KExpr),
    (Ix.Kernel.Expr.mkAppN f As).getAppArgs = f.getAppArgs ++ As
  | [], f => by simp [Ix.Kernel.Expr.mkAppN]
  | a :: As, f => by
    show (Ix.Kernel.Expr.mkAppN (.app f a) As).getAppArgs = f.getAppArgs ++ a :: As
    rw [getAppArgs_mkAppN As (.app f a)]
    simp [Ix.Kernel.Expr.getAppArgs]

/-- **δ at a constant head**: the unfolding of a stored definition applied to a spine, at a level
list of its parameter count, is its value at those levels applied to the spine. -/
theorem unfold_const_mkAppN {env : Ix.Kernel.Env .anon} {n : Ix.Kernel.Key .anon}
    {us : List KLevel} {cv : Ix.Kernel.ConstantVal .anon} {V : KExpr}
    {hint : Ix.Kernel.ReducibilityHint} (As : List KExpr)
    (hfind : env.find? n = some (.defnInfo cv V hint)) (hlen : us.length = cv.levelParams.length) :
    Ix.Kernel.unfoldDefinition env (Ix.Kernel.Expr.mkAppN (.const n us) As) =
      some (Ix.Kernel.Expr.mkAppN (V.instantiateLevelParams cv.levelParams us) As) := by
  have hfn : (Ix.Kernel.Expr.mkAppN (.const n us) As).getAppFn = .const n us := by
    rw [getAppFn_mkAppN]; rfl
  have hargs : (Ix.Kernel.Expr.mkAppN (.const n us) As).getAppArgs = As := by
    rw [getAppArgs_mkAppN]; rfl
  simp [Ix.Kernel.unfoldDefinition, hfn, hfind, hargs, hlen]

/-- A loaded `Defn` represents a stored definition. -/
theorem CIRep.defn_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty val sf hint : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Defn" [nl, ty, val, sf, hint]) ci) :
    ∃ cv V hn, ci = .defnInfo cv V hn ∧ ValRep κ h nl ty cv ∧
      TmC κ h (posOf cv.levelParams V) val := by
  generalize hv : (Value.construct kciEnum "Defn" [nl, ty, val, sf, hint] : SourceValue F) = v at r
  cases r
  case defn hvr hV =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, _, rfl, hvr, hV⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-- A loaded `Rec` represents a stored recursor. -/
theorem CIRep.recr_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nm nmi rules k u blk idx : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx]) ci) :
    ∃ cv mI rP rls, ci = .recInfo cv mI rP rls := by
  generalize hv : (Value.construct kciEnum "Rec" [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx] :
    SourceValue F) = v at r
  cases r
  case recr => exact ⟨_, _, _, _, rfl⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))


theorem field_one_ne_two : (1 : F) ≠ 2 := by
  intro h
  have h2 : (1 : F) + 1 = 2 := one_add_one_eq_two
  rw [← h] at h2
  have h3 : (1 : F) + 1 = 1 + 0 := by rw [add_zero]; exact h2
  exact one_ne_zero (add_left_cancel h3)

/-- `KernelWhnf::whnf_const_head`: the natives (`try_prim_dispatch`), then by the loaded
constant: a definition's projection shortcut, then δ (`Red.delta`, continued by
`whnf_with_spine`); quotient ι; the recursor dispatch; any other head is stuck. -/
theorem whnf_const_head_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_const_head" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_const_head c args h r h' calls := by
  intro rc addr lvls hd sp types hargs good hrc d Γ htypes a us As ha hus hH hAs
  subst hargs
  have p := Obs.«KernelWhnf::whnf_const_head».obs ev
  cases p
  case n1_bind m2 cs12 x_reduced cs86 ev14 ev88 hc =>
    subst hc
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .try_prim_dispatch) (by lt_calls) ev14 rc addr lvls sp
      types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a us As ha hus hAs 1 x_reduced
      rfl (.inl rfl)
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf) (by lt_calls) ev88 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case n2_bind m2 cs12 x_stuck ev14 he133 he134 hc =>
    subst hc he133 he134
    exact ih.get (.whnf .try_prim_dispatch) (by lt_calls) ev14 rc addr lvls sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a us As ha hus hAs 2 _ rfl (.inr rfl)
  case other_Defn_n1_bind v1 m2 cs12 m140 p147 cs153 x_nl w180 x_value w181 w182 m209 cs219
      x_reduced cs285 ev14 ev155 ld149 ev221 ev287 hc =>
    subst hc
    have e0 := ObsFn.heap_extends ev14
    have e1 := ObsFn.heap_extends ev155
    have e2 := ObsFn.heap_extends ev221
    have ext := e0.trans e1
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev155 addr a rfl
      (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy e0 ha)
    rw [ld149] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, V, hn, rfl, ⟨hnl, -, hnd, -⟩, hV⟩ := CIRep.defn_inv hci
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .try_reduce_projection_definition) (by lt_calls) ev221
      x_value x_nl lvls sp rfl (good.sub fun x hx => by simp [hx]) d Γ _ cv V hn us As hfind hV
      hnd hnl (LvListRep.mono ext hus) (tml_mono ext hAs) x_reduced rfl
    have ext' := ext.trans e2
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf) (by lt_calls) ev287 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Defn_other_n1_bind v1 m2 cs12 m140 p147 cs153 x_nl w180 x_value w181 w182 v208 m209
      cs219 m317 cs328 x_body cs368 ev14 ev155 ld149 ev221 ev330 ev370 hc =>
    subst hc
    have e0 := ObsFn.heap_extends ev14
    have e1 := ObsFn.heap_extends ev155
    have e2 := ObsFn.heap_extends ev221
    have e3 := ObsFn.heap_extends ev330
    have ext := e0.trans e1
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev155 addr a rfl
      (good.sub fun x hx => by simp [hx]) (Bytes.repAddressRef_heapMono₂ addrTy e0 ha)
    rw [ld149] at hld
    injection hld with hv
    subst hv
    have hci2 := CIRep.mono e2 hci
    obtain ⟨cv, V, hn, rfl, -, -⟩ := CIRep.defn_inv hci
    have hu := ih.get (.whnf .red_unfold) (by lt_calls) ev330 _ lvls rfl
      (good.sub fun x hx => by simp [hx]) _ us hci2 (LvListRep.mono (ext.trans e2) hus) 1 x_body
      rfl one_ne_zero
    rcases hu with ⟨-, cv', V', hn', hci', hlen, hbody⟩ | ⟨h12, -⟩
    · injection hci' with hcv hV' hhn
      subst hcv hV'
      have ext' := ext.trans (e2.trans e3)
      obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_with_spine) (by lt_calls) ev370 rc x_body sp
        types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ
        (types_mono ext' htypes) _ As (hbody d Γ) (tml_mono ext' hAs)
      exact ⟨E', hE', .trans (.delta (unfold_const_mkAppN As hfind hlen)) hred'⟩
    · exact (field_one_ne_two h12).elim
  case other_Defn_other_other v1 m2 cs12 m140 p147 cs153 x_nl w180 x_value w181 w182 v208 m209
      cs219 v316 m317 cs328 cs410 ev14 ev155 ld149 ev221 ev330 ev412 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((ObsFn.heap_extends ev155).trans
      ((ObsFn.heap_extends ev221).trans (ObsFn.heap_extends ev330)))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev412 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_Thm v1 m2 cs12 m140 p147 cs153 w437 w438 w439 cs458 ev14 ev155 ld149 ev460 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev155)
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev460 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_Quot_n1_bind v1 m2 cs12 m140 p147 cs153 w485 w486 w487 m504 cs514 x_reduced cs588
      ev14 ev155 ld149 ev516 ev590 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev155)
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .try_quot_iota) (by lt_calls) ev516 rc addr lvls sp types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) a
      us As (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (LvListRep.mono ext hus)
      (tml_mono ext hAs) x_reduced rfl
    have ext' := ext.trans (ObsFn.heap_extends ev516)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf) (by lt_calls) ev590 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Quot_other v1 m2 cs12 m140 p147 cs153 w485 w486 w487 v503 m504 cs514 cs622 ev14
      ev155 ld149 ev516 ev624 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((ObsFn.heap_extends ev155).trans
      (ObsFn.heap_extends ev516))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev624 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_Rec_n1_bind v1 m2 cs12 m140 p147 cs153 x_rnl x_rec_ty x_nparams x_nindices
      x_nmotives x_nminors x_rules x_k_flag w649 w650 w651 m708 cs719 x_reduced cs847 ev14 ev155
      ld149 ev721 ev849 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev155)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev155 addr a rfl
      (good.sub fun x hx => by simp [hx])
      (Bytes.repAddressRef_heapMono₂ addrTy (ObsFn.heap_extends ev14) ha)
    rw [ld149] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, rfl⟩ := CIRep.recr_inv hci
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .red_rec) (by lt_calls) ev721 rc _ _ lvls hd sp _ _ _ _ _
      _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us cv mI rP rls As
      ⟨⟨hfind, _, _, _, hci⟩, LvListRep.mono ext hus⟩ (Tm.mono ext hH) (tml_mono ext hAs) 1
      x_reduced rfl (.inl rfl)
    have ext' := ext.trans (ObsFn.heap_extends ev721)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf) (by lt_calls) ev849 rc x_reduced types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Rec_n2_bind v1 m2 cs12 m140 p147 cs153 x_rnl x_rec_ty x_nparams x_nindices
      x_nmotives x_nminors x_rules x_k_flag w649 w650 w651 m708 cs719 x_stuck ev14 ev155 ld149
      ev721 he894 he895 hc =>
    subst hc he894 he895
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev155)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev155 addr a rfl
      (good.sub fun x hx => by simp [hx])
      (Bytes.repAddressRef_heapMono₂ addrTy (ObsFn.heap_extends ev14) ha)
    rw [ld149] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, rfl⟩ := CIRep.recr_inv hci
    exact ih.get (.whnf .red_rec) (by lt_calls) ev721 rc _ _ lvls hd sp _ _ _ _ _
      _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us cv mI rP rls As
      ⟨⟨hfind, _, _, _, hci⟩, LvListRep.mono ext hus⟩ (Tm.mono ext hH) (tml_mono ext hAs) 2
      _ rfl (.inr (.inl rfl))
  case other_Rec_n3_bind v1 m2 cs12 m140 p147 cs153 x_rnl x_rec_ty x_nparams x_nindices
      x_nmotives x_nminors x_rules x_k_flag w649 w650 w651 m708 cs719 x_k_reduct cs918 ev14 ev155
      ld149 ev721 ev920 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev155)
    obtain ⟨ci, hfind, v, hld, hci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev155 addr a rfl
      (good.sub fun x hx => by simp [hx])
      (Bytes.repAddressRef_heapMono₂ addrTy (ObsFn.heap_extends ev14) ha)
    rw [ld149] at hld
    injection hld with hv
    subst hv
    obtain ⟨cv, mI, rP, rls, rfl⟩ := CIRep.recr_inv hci
    obtain ⟨E, hE, hred⟩ := ih.get (.whnf .red_rec) (by lt_calls) ev721 rc _ _ lvls hd sp _ _ _ _ _
      _ types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) _ us cv mI rP rls As
      ⟨⟨hfind, _, _, _, hci⟩, LvListRep.mono ext hus⟩ (Tm.mono ext hH) (tml_mono ext hAs) 3
      x_k_reduct rfl (.inr (.inr rfl))
    have ext' := ext.trans (ObsFn.heap_extends ev721)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf) (by lt_calls) ev920 rc x_k_reduct types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext' hrc) d Γ (types_mono ext' htypes) E hE
    exact ⟨E', hE', .trans hred hred'⟩
  case other_Rec_other v1 m2 cs12 m140 p147 cs153 x_rnl x_rec_ty x_nparams x_nindices
      x_nmotives x_nminors x_rules x_k_flag w649 w650 w651 v707 m708 cs719 cs952 ev14 ev155 ld149
      ev721 ev954 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans ((ObsFn.heap_extends ev155).trans
      (ObsFn.heap_extends ev721))
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev954 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩
  case other_other v1 m2 cs12 v139 m140 p147 cs153 cs979 ev14 ev155 ld149 hne430 hne478 hne642
      hne972 ev981 hc =>
    subst hc
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev155)
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev981 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext hH) (tml_mono ext hAs), .refl⟩


end IxVM.Refinement.Core
