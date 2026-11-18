import IxVMRefinement.Assembly.NativeBlockGuardWalk
import IxVMRefinement.Guard.FieldTraces

/-! # The projection guard at a use, with the raw walk it made

`peel_open`, `walk_open_checked` and `proj_guard_open` (`NativeBlockGuardWalk.lean`) read a
`KernelInfer::proj_guard` run at the term seam: the guard level as the fold of the field levels
under the flags, typed sorts, and the flags against the stored constructor type. They keep no
fact of the classifier calls the checked walk makes.

The twins here follow the same observations and keep the raw data, as `Guard/FieldTraces.lean`
does for the install's loop:

* `peel_traces`: the parameter peel moves each parameter domain of the raw telescope into the
  raw context.
* `walk_open_traced`: the checked walk classifies each of the fields `0..K` of the raw
  telescope in the raw context of the binders before it, and the level it joins for a field
  has the zero-set of that field's signature.
* `proj_guard_traced`: a `proj_guard` run either took the unchecked walk, after its own
  `is_inductive_prop` call answered something other than `1` (the call and the inductive's
  load are returned), or its level is the fold of levels `lus` under `flags`, the flags cover
  `structUsedLater` of the stored constructor type, and the raw telescope `S` behind the type
  pointer of the constructor it loaded has field traces of its fields `0..f` whose signatures
  have the zero-sets of `lus`.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Core.GuardWalk

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red Infer)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Decl (RawExprRep RawContext RawTypeAt RawDeltaAt RawSignatureTrace
  RawDomainTraces RawFieldTraces)

private theorem klevel_node_enum :
    Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» =
      IxVM.Refinement.KernelLevels.klevelListEnum := by decide +kernel

/-- **The parameter peel, with its raw walk**: `peel_open`, and the raw context and raw
remainder after the peel, from which the field traces of the remainder are the field traces of
the telescope after the peeled parameters. -/
theorem peel_traces (rawKey : _root_.Address → KKey) (c : ScopedCtx) (Γ0 : Nat → KExpr) :
    ∀ (m : Nat) {x_e x_types x_after x_ctx : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} (n : F), ZMod.val n = m →
      ObsFn W "KernelCheck::peel_n_foralls_with_types" [x_e, .field n, x_types] h
        (.tuple [x_after, x_ctx]) h' calls →
      ∀ (d : Nat) (Γ : Nat → KExpr) (E : KExpr) (kr : Nat) (R : KExpr)
        (context : List KExpr) (kraw : Nat) (S : KExpr),
        c.types Γ h d x_types → c.tm d Γ h E x_e → Tm c.κ 0 Γ0 h kr R x_e →
        RawContext rawKey h context x_types → RawExprRep rawKey h kraw S x_e →
        ∃ (m' : Nat) (Γ' : Nat → KExpr) (E' R' : KExpr) (fvs : List KExpr)
          (bs : List (KExpr × Ix.Kernel.BinderMeta)) (context' : List KExpr) (S' : KExpr),
          m' ≤ m ∧ c.types Γ' h' (d + m') x_ctx ∧ c.tm (d + m') Γ' h' E' x_after ∧
          Tm c.κ 0 Γ0 h' (kr + m') R' x_after ∧
          Ix.Kernel.openPisAtFvars m' E d = some (fvs, E') ∧ R.stripPis m' = some (bs, R') ∧
          (m' < m → ∃ v, loadValue h' x_after = .ok v ∧
            ∀ vs : List (SourceValue F), vs.length = 3 →
              v ≠ .construct "KernelTypes::KExprNode" "Forall" vs) ∧
          RawContext rawKey h' context' x_ctx ∧ RawExprRep rawKey h' (kraw + m') S' x_after ∧
          ∀ (types delta : KKey → List KLevel → KExpr → Prop) (count : Nat)
            (sigs : List KLevel),
            RawDomainTraces types delta count context' S' sigs →
            RawFieldTraces types delta m' count context S sigs := by
  intro m
  induction m with
  | zero =>
    intro x_e x_types x_after x_ctx h h' calls n hn ev d Γ E kr R context kraw S htypes hE hR
      rawCtx rawS
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hn
    subst hn0
    rcases Obs.«KernelCheck::peel_n_foralls_with_types».obs ev with
      ⟨_, he19, he34, _⟩ |
      ⟨x_dom, x_body, w59, m76, cs109, v113, hne36, ld51, hm86, op135, ev111, hc144⟩ |
      ⟨v40, hne36, ld51, hne145, he153, he168, _⟩
    · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he19
      obtain ⟨rfl, rfl⟩ := he19
      subst he34
      exact ⟨0, Γ, E, R, [], [], context, S, Nat.le_refl 0, htypes, hE, hR, rfl, rfl,
        fun hlt => absurd hlt (Nat.lt_irrefl 0), rawCtx, rawS,
        fun _ _ _ _ domains => .fields domains⟩
    · exact absurd rfl hne36
    · exact absurd rfl hne36
  | succ m ih =>
    intro x_e x_types x_after x_ctx h h' calls n hn ev d Γ E kr R context kraw S htypes hE hR
      rawCtx rawS
    have hn0 : n ≠ 0 := by
      intro e
      rw [e, ZMod.val_zero] at hn
      omega
    rcases Obs.«KernelCheck::peel_n_foralls_with_types».obs ev with
      ⟨hv14, _, _, _⟩ |
      ⟨x_dom, x_body, w59, m76, cs109, v113, _, ld51, hm86, op135, ev111, hc144⟩ |
      ⟨v40, _, ld51, hne145, he153, he168, _⟩
    · exact absurd (Value.field.inj hv14) hn0
    · subst hm86
      have hv113 : v113 = .field (n - 1) := NatAux.sub_ok op135
      subst hv113
      have hnv : ZMod.val (n - 1) = m := by
        have := NatAux.val_sub_one hn0
        omega
      obtain ⟨image, raw⟩ := rawS
      obtain ⟨D, B, ℓ, rfl, hD, hB, -⟩ := hE.forallE_of_load ld51
      obtain ⟨RD, RB, ℓr, rfl, -, hRB, -⟩ := hR.forallE_of_load ld51
      obtain ⟨SD, SB, ED, EB, binderLevel, rfl, rfl, rawDom, rawBody, -⟩ :=
        raw.raw_forallE_view ld51
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [x_dom, x_types])
      have htypes' := ProjAux.types_extend htypes hD
      have hbody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
        (Tm.mono ext hB)
      obtain ⟨m', Γ', E', R', fvs, bs, context', S', hm', ht', hE', hR', hop, hst, hstop,
        hctx', hS', hstep⟩ :=
        ih (n - 1) hnv ev111 (d + 1) _ _ (kr + 1) RB (SD :: context) (kraw + 1) SB htypes'
          hbody (Tm.mono ext hRB)
          (.cons List.getElem?_concat_length ⟨kraw, ⟨_, rawDom.mono ext⟩⟩ (rawCtx.mono ext))
          ⟨_, rawBody.mono ext⟩
      refine ⟨m' + 1, Γ', E', R', .fvar d D :: fvs, (RD, bmeta ℓr) :: bs, context', S',
        by omega, ?_, ?_, ?_, openPisAtFvars_succ_forallE_of hop, stripPis_succ_forallE_of hst,
        fun hlt => hstop (by omega), hctx', ?_,
        fun types delta count sigs domains => .parameter (hstep types delta count sigs domains)⟩
      · rw [show d + (m' + 1) = d + 1 + m' by omega]
        exact ht'
      · rw [show d + (m' + 1) = d + 1 + m' by omega]
        exact hE'
      · rw [show kr + (m' + 1) = kr + 1 + m' by omega]
        exact hR'
      · rw [show kraw + (m' + 1) = kraw + 1 + m' by omega]
        exact hS'
    · simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he153
      obtain ⟨rfl, rfl⟩ := he153
      subst he168
      exact ⟨0, Γ, E, R, [], [], context, S, Nat.zero_le _, htypes, hE, hR, rfl, rfl,
        fun _ => ⟨v40, ld51, hne145⟩, rawCtx, rawS, fun _ _ _ _ domains => .fields domains⟩

/-- **The checked walk, with its raw walk**: the fold and the flags of `walk_open_checked`, and
for the same levels `lus` the signature traces of the raw telescope's fields `0..K` over the
run's loads, with the zero-set agreement of each level with its field's signature. -/
theorem walk_open_traced (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    (c : ScopedCtx) (hc : ScopedCoreFacts c) (Γ0 : Nat → KExpr) (rootCalls : List (Call F)) :
    ∀ (K : Nat) {x_rc x_ty x_ctx x_deps r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} (k : F), ZMod.val k = K → CoreGood c calls →
      (∀ cl ∈ calls, cl ∈ rootCalls) →
      ObsFn W "KernelGuard::proj_walk_checked" [x_rc, x_ty, x_ctx, .field k, x_deps] h r h'
        calls →
      ∀ (d : Nat) (Γ : Nat → KExpr) (E : KExpr) (kr : Nat) (R : KExpr) (ls : List KLevel)
        (context : List KExpr) (kraw : Nat) (S : KExpr),
        c.rc h x_rc → c.types Γ h d x_ctx → c.tm d Γ h E x_ty → Tm c.κ 0 Γ0 h kr R x_ty →
        RepKLevelList h ls x_deps →
        RawContext rawKey h context x_ctx → RawExprRep rawKey h kraw S x_ty →
        (∃ x y z, loadValue h x_ty = .ok (.construct "KernelTypes::KExprNode" "Forall" [x, y, z])) ∧
        ∃ (lus : List KLevel) (flags : List Bool) (sigs : List KLevel),
          lus.length = K + 1 ∧ flags.length = K ∧
          RepKLevel h' ((ls ++ selDeps lus flags).foldl (fun a b => Ix.Kernel.Level.max a b)
            (lus.getD K .zero)) r ∧
          (∀ j, j < K → flags.getD j false = false →
            ∀ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (rest : KExpr),
              R.stripPis (j + 1) = some (bs, rest) → rest.hasLooseBVar 0 = false) ∧
          RawDomainTraces (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls)
            (K + 1) context S sigs ∧
          ∀ j, j ≤ K → ∀ φ : Ix.Kernel.LevelParam → Nat,
            Ix.Kernel.Level.eval φ (lus.getD j .zero) = 0 ↔
              Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0 := by
  intro K
  induction K with
  | zero =>
    intro x_rc x_ty x_ctx x_deps r h h' calls k hk good subset ev d Γ E kr R ls context kraw S
      hrc htypes hE hR hls rawCtx rawS
    have hk0 : k = 0 := (ZMod.val_eq_zero k).mp hk
    subst hk0
    obtain ⟨image, raw⟩ := rawS
    rcases Obs.«KernelGuard::proj_walk_checked».obs ev with
      ⟨x_dom, x_body, w16, v32, m33, cs43, cs87, ld11, ev45, _, ev89, hc106⟩ |
      ⟨x_dom, x_body, w16, v32, m33, cs43, v176, m177, cs179, cs188, v194, m211,
        ld11, ev45, hne107, sg184, hm219, op252, ev190, hc261⟩
    · have s43 : ∀ cl ∈ cs43, cl ∈ rootCalls := fun cl hx => subset cl (by rw [hc106]; simp [hx])
      subst hc106
      obtain ⟨D, B, ℓ0, rfl, hD, -, -⟩ := hE.forallE_of_load ld11
      obtain ⟨SD, SB, ED, EB, binderLevel, rfl, rfl, rawDom, -, -⟩ := raw.raw_forallE_view ld11
      have g43 : CoreGood c cs43 := good.sub fun x hx => by simp [hx]
      obtain ⟨stype, u, ℓ, signature, predicted, before, after, inner, hinf, hred, hℓ, heq,
        visited, observed, level, members, zero⟩ :=
          GuardData.checked_sort_zero_iff hc g43 hrc htypes hD ev45
      obtain ⟨rawSignature, rawLevel, trace⟩ := GuardData.sort_signature_raw_trace rawKey hc
        (g43.sub members) (fun cl hm => s43 cl (members cl hm)) (types_mono visited htypes)
        (Tm.mono visited hD) (rawCtx.mono visited)
        (⟨_, rawDom.mono visited⟩ : RawExprRep rawKey before kraw SD x_dom) observed
      have same := level.det rawLevel
      subst same
      have e45 := ObsFn.heap_extends ev45
      refine ⟨⟨_, _, _, ld11⟩, [ℓ], [], [signature], rfl, rfl, ?_, ?_,
        .step trace (.done _ _), ?_⟩
      · have hf := fold_eq ev89 hℓ (RepKLevelList.mono hls e45)
        have e1 : selDeps [ℓ] [] = [] := rfl
        have e2 : ([ℓ] : List KLevel).getD 0 .zero = ℓ := rfl
        rw [e1, e2, List.append_nil]
        exact hf
      · intro j hj
        exact absurd hj (Nat.not_lt_zero j)
      · intro j hj φ
        have hj0 : j = 0 := by omega
        subst hj0
        have key : Ix.Kernel.Level.eval φ ℓ = 0 ↔ Ix.Kernel.Level.eval φ signature = 0 := by
          rw [← heq φ]
          exact zero φ
        simpa only [List.getD_cons_zero] using key
    · exact absurd rfl hne107
  | succ K ih =>
    intro x_rc x_ty x_ctx x_deps r h h' calls k hk good subset ev d Γ E kr R ls context kraw S
      hrc htypes hE hR hls rawCtx rawS
    have hk0 : k ≠ 0 := by
      intro e
      rw [e, ZMod.val_zero] at hk
      omega
    obtain ⟨image, raw⟩ := rawS
    rcases Obs.«KernelGuard::proj_walk_checked».obs ev with
      ⟨x_dom, x_body, w16, v32, m33, cs43, cs87, ld11, ev45, hv83, ev89, hc106⟩ |
      ⟨x_dom, x_body, w16, v32, m33, cs43, v176, m177, cs179, cs188, v194, m211,
        ld11, ev45, hne107, sg184, hm219, op252, ev190, hc261⟩
    · exact absurd (Value.field.inj hv83) hk0
    · have s43 : ∀ cl ∈ cs43, cl ∈ rootCalls := fun cl hx => subset cl (by rw [hc261]; simp [hx])
      have s188 : ∀ cl ∈ cs188, cl ∈ rootCalls :=
        fun cl hx => subset cl (by rw [hc261]; simp [hx])
      subst hc261
      obtain ⟨D, B, ℓ0, rfl, hD, hB, -⟩ := hE.forallE_of_load ld11
      obtain ⟨RD, RB, ℓr, rfl, -, hRB, -⟩ := hR.forallE_of_load ld11
      obtain ⟨SD, SB, ED, EB, binderLevel, rfl, rfl, rawDom, rawBody, -⟩ :=
        raw.raw_forallE_view ld11
      have g43 : CoreGood c cs43 := good.sub fun x hx => by simp [hx]
      obtain ⟨stype, u, ℓ, signature, predicted, before, after, inner, hinf, hred, hℓ, heq,
        visited, observed, level, members, zero⟩ :=
          GuardData.checked_sort_zero_iff hc g43 hrc htypes hD ev45
      obtain ⟨rawSignature, rawLevel, trace⟩ := GuardData.sort_signature_raw_trace rawKey hc
        (g43.sub members) (fun cl hm => s43 cl (members cl hm)) (types_mono visited htypes)
        (Tm.mono visited hD) (rawCtx.mono visited)
        (⟨_, rawDom.mono visited⟩ : RawExprRep rawKey before kraw SD x_dom) observed
      have same := level.det rawLevel
      subst same
      have e45 := ObsFn.heap_extends ev45
      -- the flag of this field and the levels kept so far
      obtain ⟨b, ls', hls177, e33_177, hb, hbflag⟩ : ∃ (b : Bool) (ls' : List KLevel),
          RepKLevelList m177 ls' v176 ∧ Heap.Extends m33 m177 ∧
          ls' = ls ++ (if b then [ℓ] else []) ∧ (b = false → RB.hasLooseBVar 0 = false) := by
        rcases sg184 with
          ⟨m112, cs123, cs148, ev125, ev150, hc167⟩ |
          ⟨v111, m112, cs123, ev125, hne168, he173, he174, hc175⟩
        · have e125 := ObsFn.heap_extends ev125
          have e150 := ObsFn.heap_extends ev150
          refine ⟨true, ls ++ [ℓ],
            ProjAux.lv_snoc ev150 (RepKLevelList.mono (RepKLevelList.mono hls e45) e125)
              (hℓ.mono e125),
            e125.trans e150, ?_, fun hf => by cases hf⟩
          first | rfl | simp
        · subst he173 he174 hc175
          have e125 := ObsFn.heap_extends ev125
          have g123 : CoreGood c cs123 := good.sub fun x hx => by simp [hx]
          obtain ⟨-, h01, -⟩ := SubstAux.gall c.κ .expr_has_bvar_at _ _ _ _ _ ev125 x_body 0 rfl
            g123.bounded
          have hv0 : v111 = .field 0 := h01.resolve_right hne168
          subst hv0
          have hno := (Decl.expr_has_bvar_at_zero_spec (k := kr + 1) (j := 0) (by omega)
            (by decide) g123.bounded (Tm.mono e45 hRB) (by rw [Nat.cast_zero]; exact ev125)).1
          refine ⟨false, ls, RepKLevelList.mono (RepKLevelList.mono hls e45) e125, e125, ?_,
            fun _ => hno⟩
          first | rfl | simp
      subst hm219
      have hv194 : v194 = .field (k - 1) := NatAux.sub_ok op252
      subst hv194
      have hkv : ZMod.val (k - 1) = K := by
        have := NatAux.val_sub_one hk0
        omega
      have e211 := Heap.Extends.snoc m177 (.construct kexprListEnum "Cons" [x_dom, x_ctx])
      have E177 : Heap.Extends h m177 := e45.trans e33_177
      have E211 : Heap.Extends h _ := E177.trans e211
      have htypes211 := ProjAux.types_extend (types_mono E177 htypes) (Tm.mono E177 hD)
      have hbody211 := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
        (Tm.mono E211 hB)
      have g188 : CoreGood c cs188 := good.sub fun x hx => by simp [hx]
      obtain ⟨-, lus', flags', sigs', hlen1, hlen2, hfold, hflag, traces, zeros⟩ :=
        ih (k - 1) hkv g188 s188 ev190 (d + 1) _ _ (kr + 1) RB ls' (SD :: context) (kraw + 1) SB
          (RCRep.mono E211 hrc) htypes211 hbody211 (Tm.mono E211 hRB)
          (RepKLevelList.mono hls177 e211)
          (.cons List.getElem?_concat_length ⟨kraw, ⟨_, rawDom.mono E211⟩⟩ (rawCtx.mono E211))
          ⟨_, rawBody.mono E211⟩
      refine ⟨⟨_, _, _, ld11⟩, ℓ :: lus', b :: flags', signature :: sigs', by simp [hlen1],
        by simp [hlen2], ?_, ?_, .step trace traces, ?_⟩
      · have e1 : ls ++ selDeps (ℓ :: lus') (b :: flags') = ls' ++ selDeps lus' flags' := by
          show ls ++ ((if b then [ℓ] else []) ++ selDeps lus' flags') = ls' ++ selDeps lus' flags'
          rw [hb, List.append_assoc]
        rw [e1]
        exact hfold
      · intro j hj hfl bs rest hst
        obtain ⟨bs', hst'⟩ := stripPis_succ_forallE hst
        cases j with
        | zero =>
          have h0 : (some ([], RB) : Option (List (KExpr × Ix.Kernel.BinderMeta) × KExpr)) =
              some (bs', rest) := hst'
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h0)
          exact hbflag hfl
        | succ j => exact hflag j (by omega) hfl bs' rest hst'
      · intro j hj φ
        cases j with
        | zero =>
          have key : Ix.Kernel.Level.eval φ ℓ = 0 ↔ Ix.Kernel.Level.eval φ signature = 0 := by
            rw [← heq φ]
            exact zero φ
          simpa only [List.getD_cons_zero] using key
        | succ j => simpa only [List.getD_cons_succ] using zeros j (by omega) φ

/-- **The projection guard at a use, with its raw walk** (module docstring). The constructor
load is the run's own `get_ci_cprj`; `S` is the raw telescope its type pointer reads as. -/
theorem proj_guard_traced (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    (c : ScopedCtx) (hc : ScopedCoreFacts c)
    {x_rc bp r : SourceValue F} {i f : F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, bp, .field i, .field f] h r h' calls)
    (hrc : c.rc h x_rc)
    {nm : KKey} {k : Nat} {T : KExpr} {nP nF : Nat}
    (hload : ∀ (ptr : SourceValue F) (m : Heap F) (cs : List (Call F)),
      ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      CIPtrRep c.κ m ptr (.ctorInfo ⟨nm, List.range k, T⟩ nP nF))
    (hf : ZMod.val f < nF)
    {g : KLevel} (hg : RepKLevel h' g r) :
    (∃ (ptr ity np ni n v w₁ w₅ w₆ w₇ w₈ : SourceValue F) (m₀ m₁ m₂ : Heap F)
        (cs₁ cs₂ : List (Call F)),
      Heap.Extends h m₀ ∧
      ObsFn W "Ingress::get_ci_iprj" [bp, .field i] m₀ ptr m₁ cs₁ ∧ (∀ cl ∈ cs₁, cl ∈ calls) ∧
      loadValue m₁ ptr = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [w₁, ity, np, ni, w₅, w₆, w₇, w₈]) ∧
      evalBinOp .add np ni = .ok n ∧
      ObsFn W "KernelInfer::is_inductive_prop" [x_rc, ity, n] m₁ v m₂ cs₂ ∧
      (∀ cl ∈ cs₂, cl ∈ calls) ∧ v ≠ .field 1) ∨
    ∃ (lus : List KLevel) (flags : List Bool) (sigs : List KLevel) (S : KExpr)
      (ptr x_cty w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F) (m : Heap F) (cs₀ : List (Call F)),
      g = (List.range (ZMod.val f)).foldl
          (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
            else acc) (lus.getD (ZMod.val f) .zero) ∧
      (∀ j, j < ZMod.val f → Ix.Kernel.structUsedLater T nP j = true →
        flags.getD j false = true) ∧
      ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs₀ ∧
      (∀ cl ∈ cs₀, cl ∈ calls) ∧
      loadValue m ptr = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
        [w₁, x_cty, w₃, w₄, w₅, w₆, w₇, w₈]) ∧
      RawExprRep rawKey m 0 S x_cty ∧
      RawFieldTraces (RawTypeAt c rawKey calls) (RawDeltaAt c rawKey calls)
        nP (ZMod.val f + 1) [] S sigs ∧
      ∀ j, j ≤ ZMod.val f → ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (lus.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0 := by
  rcases Obs.«KernelInfer::proj_guard».obs ev with
    ⟨m2, p9, cs15, w44, x_cty, w45, w46, w47, x_np, w48, w49, m91, cs101, m122,
      x_after, x_ctx, m148, p155, cs161, w183, x_ind_ty, x_ind_np, x_ind_ni, w184, w185,
      w186, w187, m229, cs240, v245, csTail, mFinal, ev17, ld11, hm130, ev103, ev163,
      ld157, op273, ev242, hmFinal, evTail, hcs⟩ |
    ⟨m2, p9, cs15, w44, x_cty, w45, w46, w47, x_np, w48, w49, m91, cs101, m122,
      x_after, x_ctx, m148, p155, cs161, w183, x_ind_ty, x_ind_np, x_ind_ni, w184, w185,
      w186, w187, v228, m229, cs240, v245, csTail, mFinal, ev17, ld11, hm130, ev103,
      ev163, ld157, op273, ev242, hne, hmFinal, evTail, hcs⟩
  · have s15 : ∀ cl ∈ cs15, cl ∈ calls := fun cl hx => by rw [hcs]; simp [hx]
    have sTail : ∀ cl ∈ csTail, cl ∈ calls := fun cl hx => by rw [hcs]; simp [hx]
    subst hm130 hmFinal
    -- the loaded constructor
    obtain ⟨v, hldv, hci⟩ := hload p9 m2 cs15 ev17 s15
    rw [ld11] at hldv
    injection hldv with hv
    subst hv
    obtain ⟨cv, nP', nF', hci_eq, hval, hnp_eq, -, hnP_lt, -, -⟩ := WhnfAux.ctor_inv hci
    injection hci_eq with hcv hnP hnF
    subst hcv hnP hnF hnp_eq
    let Γ0 : Nat → KExpr := fun _ => .sort .zero
    have hT0 : Tm c.κ 0 Γ0 m2 0 T x_cty := by
      have h1 : Tm c.κ 0 Γ0 m2 0 (posOf (List.range k) T) x_cty := hval.2.2.2 0 Γ0
      rwa [Decl.posOf_range] at h1
    obtain ⟨S, (rawT : RawExprRep rawKey m2 0 S x_cty)⟩ :=
      RawExprRep.ofOpenTm_keyed rawKey hT0
    -- the parameter peel
    have e17 := ObsFn.heap_extends ev17
    have e122 := Heap.Extends.snoc m2 (.construct kexprListEnum "Nil" [])
    have hnil_ctx : c.types Γ0 (m2 ++ [.construct kexprListEnum "Nil" []]) 0
        (.ptr (.enum kexprListEnum) m2.length) :=
      ⟨.nil List.getElem?_concat_length, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have hT122 := Tm.mono e122 hT0
    have hnPv : ZMod.val (nP : F) = nP := ZMod.val_natCast_of_lt (Nat.lt_trans hnP_lt (by decide))
    obtain ⟨m', Γ', E', R', fvs, bs, context', S', hm'le, htypesP, hEP, hRP, hopP, hstP, hstop,
      rawCtxP, rawSP, hparams⟩ :=
      peel_traces rawKey c Γ0 nP (nP : F) hnPv ev103 0 Γ0 T 0 T [] 0 S hnil_ctx hT122 hT122
        (.nil List.getElem?_concat_length) (rawT.mono e122)
    rw [Nat.zero_add] at htypesP hEP hRP rawSP
    -- the field walk
    have e103 := ObsFn.heap_extends ev103
    have eRest := ev163.heap_extends.trans ev242.heap_extends
    have e187 := Heap.Extends.snoc m229
      (.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" [])
    have hnil_deps : RepKLevelList
        (m229 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Nil" []]) []
        (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>») m229.length) := by
      rw [klevel_node_enum]
      exact .nil List.getElem?_concat_length
    have E187 : Heap.Extends h _ := e17.trans (e122.trans (e103.trans (eRest.trans e187)))
    have g150 : CoreGood c csTail := good.sub sTail
    obtain ⟨⟨xa, ya, za, hldF⟩, lus, flags, sigs, hlen1, hlen2, hfold, hflag, traces, zeros⟩ :=
      walk_open_traced rawKey c hc Γ0 calls (ZMod.val f) f rfl g150 sTail evTail m' Γ' E' m' R'
        [] context' m' S' (RCRep.mono E187 hrc) (types_mono (eRest.trans e187) htypesP)
        (Tm.mono (eRest.trans e187) hEP) (Tm.mono (eRest.trans e187) hRP) hnil_deps
        (rawCtxP.mono (eRest.trans e187)) (rawSP.mono (eRest.trans e187))
    -- the peel passed every parameter: the walk starts at a `Forall` cell
    have hm'eq : nP = m' := by
      by_contra hne
      obtain ⟨vv, hldv', hnf⟩ := hstop (by omega)
      have hl := L1.loadValue_extend (eRest.trans e187) hldv'
      rw [hl] at hldF
      injection hldF with hvv
      exact hnf [xa, ya, za] rfl hvv
    subst hm'eq
    have hgEq : g = ([] ++ selDeps lus flags).foldl (fun a b => Ix.Kernel.Level.max a b)
        (lus.getD (ZMod.val f) .zero) := hg.det hfold
    refine Or.inr ⟨lus, flags, sigs, S, p9, x_cty, _, _, _, _, _, _, _, m2, cs15, ?_, ?_, ev17,
      s15, ld11, rawT, hparams _ _ _ _ traces, zeros⟩
    · rw [hgEq, List.nil_append]
      have hfr := foldl_range_selDeps flags lus (lus.getD (ZMod.val f) .zero)
      rw [hlen2] at hfr
      exact hfr.symm
    · intro j hj
      cases hfl : flags.getD j false with
      | true => intro _; rfl
      | false =>
        intro hU
        exfalso
        have hno : Ix.Kernel.structUsedLater T nP j = false := by
          cases hs : T.stripPis (nP + j + 1) with
          | none => simp only [Ix.Kernel.structUsedLater, hs]
          | some p =>
            obtain ⟨bsU, rest⟩ := p
            simp only [Ix.Kernel.structUsedLater, hs]
            rw [show nP + j + 1 = nP + (j + 1) by omega] at hs
            obtain ⟨bU₁, midU, bU₂, hUP, hUmid, -, -⟩ := Decl.stripPis_split nP (j + 1) hs
            have hmid : midU = R' := (Prod.mk.inj (Option.some.inj (hUP.symm.trans hstP))).2
            subst hmid
            rw [Ix.Kernel.Expr.hasLooseBVarB_eq]
            exact hflag j hj hfl bU₂ rest hUmid
        rw [hno] at hU
        exact Bool.false_ne_true hU
  · have s161 : ∀ cl ∈ cs161, cl ∈ calls := fun cl hx => by rw [hcs]; simp [hx]
    have s240 : ∀ cl ∈ cs240, cl ∈ calls := fun cl hx => by rw [hcs]; simp [hx]
    subst hm130
    exact Or.inl ⟨p155, x_ind_ty, x_ind_np, x_ind_ni, v245, v228, w183, w184, w185, w186, w187,
      m91, m148, m229, cs161, cs240,
      (ObsFn.heap_extends ev17).trans
        ((Heap.Extends.snoc m2 (.construct kexprListEnum "Nil" [])).trans
          (ObsFn.heap_extends ev103)),
      ev163, s161, ld157, op273, ev242, s240, hne⟩

end IxVM.Refinement.Core.GuardWalk
