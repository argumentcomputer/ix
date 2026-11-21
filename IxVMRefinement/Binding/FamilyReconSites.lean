import IxVMRefinement.Binding.FamilyReconWhnf

/-! # The four head-normalizing sites of the reconstruction on `TmOExact`

The reconstruction head-normalizes (`recon_whnf`) at four functions; each refines the model's
function at every large enough fuel (`Eventually`), from the five elementary store-read predicates
(`AddrOf`, `DefnAnswers`, `IndAnswers`, `CtorOfAnswers`, `ModeledAnswers`):

* `whnf_tele_spec` (`whnfTele`);
* `collect_n_doms_whnf_spec` (`collectDoms`), `collect_index_doms_spec` (its domains);
* `peel_ctor_params_subst_spec` (`peelCtorParams`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum)
open IxVM.Refinement.Decl (TmExact)
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Fuel -/

/-- **From some fuel on.** -/
def Eventually (P : Nat → Prop) : Prop := ∃ a, ∀ f, a ≤ f → P f

theorem Eventually.and {P Q : Nat → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually fun f => P f ∧ Q f :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun f hf => ⟨ha f (by omega), hb f (by omega)⟩⟩

theorem Eventually.mono {P Q : Nat → Prop} (hP : Eventually P) (h : ∀ f, P f → Q f) :
    Eventually Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun f hf => h f (ha f hf)⟩

theorem Eventually.always {P : Nat → Prop} (h : ∀ f, P f) : Eventually P := ⟨0, fun f _ => h f⟩

section

variable {κ : _root_.Address → KKey}

/-- A `NotLet` node that is not a `Forall` cell has `isForall E = none`. -/
theorem isForall_of_notLet {h : Heap F} {E : KExpr} {p v : SourceValue F} (hE : TmOExact κ h E p)
    (hl : loadValue h p = .ok v)
    (hf : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs)
    (hn : NotLet h p) : isForall E = none := by
  cases hE' : E with
  | forallE D B m => exact (tmOExact_not_forall hE hn hl hf D B m hE').elim
  | _ => rfl

/-- **The model's binder on a term whose head normal form is `W`**: from some fuel on, the
binder `W` exposes. -/
theorem binderOf_whnf {V : ReconView} {E W : KExpr} (hto : HnfTo V E [] W) :
    Eventually fun f => binderOf V f E = some (isForall W) := by
  obtain ⟨n₀, hn⟩ := hto
  refine ⟨n₀, fun f hf => ?_⟩
  cases E
  case forallE T B m =>
    have h1 := hn (n₀ + 1) (by omega)
    simp only [hnfSpine, Ix.Kernel.Expr.mkAppN, Option.some.injEq] at h1
    subst h1
    rfl
  all_goals simp [binderOf, isForall, hnf, hn f hf]

theorem binderOf_forallE {V : ReconView} {f : Nat} {T B : KExpr} {m : Ix.Kernel.BinderMeta} :
    binderOf V f (.forallE T B m) = some (some (T, B, m)) := rfl

end

/-! ## The sites -/

section Sites

variable {κ : _root_.Address → KKey}

/-- **`KernelCheck::whnf_tele(rc, ty, types)`** is `whnfTele` (at every large enough fuel of head
normalization and of binders) on `TmOExact`, preserving `AddrIn S κ`. -/
theorem whnf_tele_spec {rootCalls : List (Call F)} {S : _root_.Address → Prop} {V : ReconView}
    (hA : AddrOf κ V) (hD : DefnAnswers rootCalls S κ V) (hI : IndAnswers rootCalls S κ V)
    (hC : CtorOfAnswers rootCalls S V) (hM : ModeledAnswers rootCalls S V) :
    ∀ (N : Nat) {xrc xty xtys r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {E : KExpr}, cs.length < N →
      ObsFn W "KernelCheck::whnf_tele" [xrc, xty, xtys] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact κ h E xty → AddrIn S κ E →
      Heap.Extends h h' ∧ ∃ E', (∃ a, ∀ f n, a ≤ f → a ≤ n →
        whnfTele V f n E = some E') ∧ TmOExact κ h' E' r ∧ AddrIn S κ E' := by
  intro N
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ hlen; exact absurd hlen (Nat.not_lt_zero _)
  | succ N ih =>
    intro xrc xty xtys r h h' cs E hlen ev hbnd hsub hE hEin
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    rcases Obs.«KernelCheck::whnf_tele».obs ev with
      ⟨v₁, m₂, cs_b, x_dom, x_body, x_bl, v₈, m₉, cs₁, m₁₂, evw, ld, rfl, rfl, hm, ev₁, hc⟩ |
      ⟨v₁, m₂, cs_b, v₃, evw, ld, hne, rfl, rfl, hc⟩
    · subst hm
      obtain ⟨ext₁, W0, htoW, hW, -, hWin⟩ := recon_whnf_spec hA hD hI hC hM evw
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin
      obtain ⟨kW, rW⟩ := hW
      obtain ⟨D, B, ℓ, rfl, rD, rB, rl⟩ := rW.forallE_of_load ld
      have ext₂ : Heap.Extends m₂
          (m₂ ++ [.construct kexprListEnum "Cons" [x_dom, xtys]]) := Heap.Extends.snoc _ _
      obtain ⟨ext₃, B', ⟨a, ha⟩, hB', hB'in⟩ := ih (by rw [hc] at hlen; simp at hlen; omega) ev₁
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        ((TmOExact.ofTmExact rB).mono ext₂) hWin.2
      have ext₄ : Heap.Extends m₉
          (m₉ ++ [.construct "KernelTypes::KExprNode" "Forall" [x_dom, v₈, x_bl]]) :=
        Heap.Extends.snoc _ _
      have ext₅ := (ext₂.trans ext₃).trans ext₄
      obtain ⟨kB, rB'⟩ := hB'
      refine ⟨hext, .forallE D B' (bmeta ℓ), ?_,
        ⟨max kW kB, .forallE (by simp)
          (tmExact_depth_le (rD.mono ext₅) _ (Nat.le_max_left _ _))
          (tmExact_depth_le (rB'.mono ext₄) _ (by omega)) (rl.mono ext₅)⟩,
        ⟨hWin.1, hB'in⟩⟩
      obtain ⟨n₀, hn₀⟩ := htoW
      refine ⟨max n₀ a + 1, fun f n hf hn => ?_⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [whnfTele, hnf, hn₀ f (by omega), isForall, ha f n' (by omega) (by omega),
        Option.map_some]
    · obtain ⟨ext₁, W0, htoW, hW, hnl, hWin⟩ := recon_whnf_spec hA hD hI hC hM evw
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin
      have hiW := isForall_of_notLet hW ld hne hnl
      refine ⟨hext, W0, ?_, hW, hWin⟩
      obtain ⟨n₀, hn₀⟩ := htoW
      refine ⟨n₀ + 1, fun f n hf hn => ?_⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [whnfTele, hnf, hn₀ f (by omega), hiW]

/-- **`KernelCheck::collect_n_doms_whnf(rc, ty, n, types)`** is `collectDoms` on `TmOExact`,
preserving `AddrIn S κ`. -/
theorem collect_n_doms_whnf_spec {rootCalls : List (Call F)} {S : _root_.Address → Prop}
    {V : ReconView}
    (hA : AddrOf κ V) (hD : DefnAnswers rootCalls S κ V) (hI : IndAnswers rootCalls S κ V)
    (hC : CtorOfAnswers rootCalls S V) (hM : ModeledAnswers rootCalls S V) :
    ∀ (n : Nat) {xrc xty xtys r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {E : KExpr}, n < 9223372036854775808 →
      ObsFn W "KernelCheck::collect_n_doms_whnf" [xrc, xty, .field (n : F), xtys] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact κ h E xty → AddrIn S κ E →
      Heap.Extends h h' ∧ ∃ xl xa Ds A, r = .tuple [xl, xa] ∧
        RepList kexprListEnum (TmOExact κ) h' Ds xl ∧ TmOExact κ h' A xa ∧
        (∀ D ∈ Ds, AddrIn S κ D) ∧ AddrIn S κ A ∧
        Eventually fun f => collectDoms V f n E = some (Ds, A) := by
  intro n
  induction n with
  | zero =>
    intro xrc xty xtys r h h' cs E hn ev hbnd hsub hE hEin
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    rcases Obs.«KernelCheck::collect_n_doms_whnf».obs ev with
      ⟨m₁, hv, rfl, hm, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hne, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hne, -⟩ | ⟨_, _, _, _, _, _, hne, -⟩
    · subst hm
      exact ⟨hext, _, _, [], E, rfl, Lib.rep_store_nil h, hE.mono hext,
        (fun _ hm => nomatch hm), hEin, Eventually.always fun _ => rfl⟩
    all_goals exact (hne (by simp)).elim
  | succ n ih =>
    intro xrc xty xtys r h h' cs E hn ev hbnd hsub hE hEin
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    rcases Obs.«KernelCheck::collect_n_doms_whnf».obs ev with
      ⟨m₁, hv, -, -, -, -⟩ |
      ⟨x_dom, x_body, w₁, m₈, cs₉, v₉, m₁₃, x_rest, x_after, m₁₈, hne, ld, op, hm₁, ev₁, rfl, hm₂,
        rfl, hc⟩ |
      ⟨v₄, m₂, p₂, cs_w, x_dom, x_body, w₂, m₂₈, cs₂₉, v₃₀, m₃₃, x_rest, x_after, m₃₈, hne, ld,
        hne', evw, ld', op, hm₁, ev₁, rfl, hm₂, rfl, hc⟩ |
      ⟨v₄, v₂, m₂, p₂, cs_w, m₄, hne, ld, hne', evw, ld', hne'', rfl, hm, rfl, hc⟩
    · exact absurd (field_natCast_eq_zero (by omega) hv) (by omega)
    · subst hm₁ hm₂
      obtain rfl := binop_sub_one_nat (by omega) op
      obtain ⟨T, B, ℓ, rfl, hT, hB, -⟩ := TmOExact.forallE_of_load hE ld
      have ext₁ : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [x_dom, xtys]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨ext₂, xl, xa, Ds, A, he, hDs, hA1, hDsIn, hAin, hev⟩ := ih (by omega)
        (by simpa using ev₁)
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (hB.mono ext₁) hEin.2
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨hext, _, _, T :: Ds, A, rfl,
        Lib.rep_store_cons tmOExact_heapMono₂ (hT.mono (ext₁.trans ext₂)) hDs,
        hA1.mono (Heap.Extends.snoc _ _),
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hEin.1; exact hDsIn X hm),
        hAin, hev.mono fun f hf => ?_⟩
      simp only [collectDoms, binderOf_forallE, hf, Option.map_some]
    · subst hm₁ hm₂
      obtain rfl := binop_sub_one_nat (by omega) op
      obtain ⟨ext₁, W0, htoW, hW, -, hWin⟩ := recon_whnf_spec hA hD hI hC hM evw
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin
      obtain ⟨D, B, ℓ, rfl, hD1, hB, -⟩ := TmOExact.forallE_of_load hW ld'
      have ext₂ : Heap.Extends m₂ (m₂ ++ [.construct kexprListEnum "Cons" [x_dom, xtys]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨ext₃, xl, xa, Ds, A, he, hDs, hA1, hDsIn, hAin, hev⟩ := ih (by omega)
        (by simpa using ev₁)
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (hB.mono ext₂) hWin.2
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨hext, _, _, D :: Ds, A, rfl,
        Lib.rep_store_cons tmOExact_heapMono₂ (hD1.mono (ext₂.trans ext₃)) hDs,
        hA1.mono (Heap.Extends.snoc _ _),
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hWin.1; exact hDsIn X hm),
        hAin, ((binderOf_whnf htoW).and hev).mono fun f ⟨hb, hf⟩ => ?_⟩
      simp only [collectDoms, hb, isForall, hf, Option.map_some]
    · subst hm
      obtain ⟨ext₁, W0, htoW, hW, hnl, -⟩ := recon_whnf_spec hA hD hI hC hM evw
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin
      have hiW := isForall_of_notLet hW ld' hne'' hnl
      refine ⟨hext, _, _, [], E, rfl, Lib.rep_store_nil m₂,
        hE.mono (ext₁.trans (Heap.Extends.snoc _ _)), (fun _ hm => nomatch hm), hEin,
        (binderOf_whnf htoW).mono fun f hb => ?_⟩
      simp only [collectDoms, hb, hiW]

/-- **`KernelCheck::collect_index_doms(rc, ty, n, types)`** is `collectDoms`'s domains on
`TmOExact`, preserving `AddrIn S κ`. -/
theorem collect_index_doms_spec {rootCalls : List (Call F)} {S : _root_.Address → Prop}
    {V : ReconView}
    (hA : AddrOf κ V) (hD : DefnAnswers rootCalls S κ V) (hI : IndAnswers rootCalls S κ V)
    (hC : CtorOfAnswers rootCalls S V) (hM : ModeledAnswers rootCalls S V) :
    ∀ (n : Nat) {xrc xty xtys r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {E : KExpr}, n < 9223372036854775808 →
      ObsFn W "KernelCheck::collect_index_doms" [xrc, xty, .field (n : F), xtys] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact κ h E xty → AddrIn S κ E →
      Heap.Extends h h' ∧ ∃ Ds, RepList kexprListEnum (TmOExact κ) h' Ds r ∧
        (∀ D ∈ Ds, AddrIn S κ D) ∧
        Eventually fun f => (collectDoms V f n E).map Prod.fst = some Ds := by
  intro n
  induction n with
  | zero =>
    intro xrc xty xtys r h h' cs E hn ev hbnd hsub hE hEin
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    rcases Obs.«KernelCheck::collect_index_doms».obs ev with
      ⟨hv, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, hne, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hne, -⟩ | ⟨_, _, _, _, _, hne, -⟩
    · exact ⟨hext, [], Lib.rep_store_nil h, (fun _ hm => nomatch hm),
        Eventually.always fun _ => rfl⟩
    all_goals exact (hne (by simp)).elim
  | succ n ih =>
    intro xrc xty xtys r h h' cs E hn ev hbnd hsub hE hEin
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    rcases Obs.«KernelCheck::collect_index_doms».obs ev with
      ⟨hv, -, -, -⟩ |
      ⟨x_dom, x_body, w₁, v₇, m₈, cs₉, v₉, m₁₂, hne, ld, rfl, rfl, op, hm, ev₁, hc⟩ |
      ⟨v₂, m₁, p₁, cs_w, x_dom, x_body, w₂, v₂₃, m₂₄, cs₂₄, v₂₅, m₂₈, hne, ld, hne', evw, ld',
        rfl, rfl, op, hm, ev₁, hc⟩ |
      ⟨v₂, v₁, m₁, p₁, cs_w, hne, ld, hne', evw, ld', hne'', rfl, rfl, hc⟩
    · exact absurd (field_natCast_eq_zero (by omega) hv) (by omega)
    · subst hm
      obtain rfl := binop_sub_one_nat (by omega) op
      obtain ⟨T, B, ℓ, rfl, hT, hB, -⟩ := TmOExact.forallE_of_load hE ld
      have ext₁ : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [x_dom, xtys]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨ext₂, Ds, hDs, hDsIn, hev⟩ := ih (by omega) (by simpa using ev₁)
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (hB.mono ext₁) hEin.2
      refine ⟨hext, T :: Ds,
        Lib.rep_store_cons tmOExact_heapMono₂ (hT.mono (ext₁.trans ext₂)) hDs,
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hEin.1; exact hDsIn X hm),
        hev.mono fun f hf => ?_⟩
      cases hc' : collectDoms V f n B with
      | none => rw [hc'] at hf; cases hf
      | some p =>
        rw [hc'] at hf
        simp only [Option.map_some, Option.some.injEq] at hf
        simp only [collectDoms, binderOf_forallE, hc', Option.map_some, hf]
    · subst hm
      obtain rfl := binop_sub_one_nat (by omega) op
      obtain ⟨ext₁, W0, htoW, hW, -, hWin⟩ := recon_whnf_spec hA hD hI hC hM evw
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin
      obtain ⟨D, B, ℓ, rfl, hD1, hB, -⟩ := TmOExact.forallE_of_load hW ld'
      have ext₂ : Heap.Extends m₁ (m₁ ++ [.construct kexprListEnum "Cons" [x_dom, xtys]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨ext₃, Ds, hDs, hDsIn, hev⟩ := ih (by omega) (by simpa using ev₁)
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        (hB.mono ext₂) hWin.2
      refine ⟨hext, D :: Ds,
        Lib.rep_store_cons tmOExact_heapMono₂ (hD1.mono (ext₂.trans ext₃)) hDs,
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hWin.1; exact hDsIn X hm),
        ((binderOf_whnf htoW).and hev).mono fun f ⟨hb, hf⟩ => ?_⟩
      cases hc' : collectDoms V f n B with
      | none => rw [hc'] at hf; cases hf
      | some p =>
        rw [hc'] at hf
        simp only [Option.map_some, Option.some.injEq] at hf
        simp only [collectDoms, hb, isForall, hc', Option.map_some, hf]
    · obtain ⟨ext₁, W0, htoW, hW, hnl, -⟩ := recon_whnf_spec hA hD hI hC hM evw
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hE hEin
      have hiW := isForall_of_notLet hW ld' hne'' hnl
      refine ⟨hext, [], Lib.rep_store_nil m₁, (fun _ hm => nomatch hm),
        (binderOf_whnf htoW).mono fun f hb => ?_⟩
      simp only [collectDoms, hb, hiW, Option.map_some]

/-- **`KernelCheck::peel_ctor_params_subst`** is `peelCtorParams` on `TmOExact`, preserving
`AddrIn S κ`. -/
theorem peel_ctor_params_subst_spec {rootCalls : List (Call F)} {S : _root_.Address → Prop}
    {V : ReconView}
    (hA : AddrOf κ V) (hD : DefnAnswers rootCalls S κ V) (hI : IndAnswers rootCalls S κ V)
    (hC : CtorOfAnswers rootCalls S V) (hM : ModeledAnswers rootCalls S V)
    {depth lift : Nat} {aux : Bool} {Ps : List KExpr}
    (hdepth : depth < 9223372036854775808) (hlift : lift < 4611686018427387904)
    (hPs : Ps.length < 9223372036854775808) (hPsIn : ∀ P ∈ Ps, AddrIn S κ P) :
    ∀ (n j : Nat), n + j < 9223372036854775808 →
      (∀ i, j ≤ i → i < j + n → ¬ (aux = true ∧ i < Ps.length) → i < depth) →
      ∀ {xrc xty xps xtys r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr},
      ObsFn W "KernelCheck::peel_ctor_params_subst"
        [xrc, xty, .field (n : F), .field (depth : F), .field (lift : F), auxVal aux, xps,
          .field (j : F), xtys] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact κ h E xty → AddrIn S κ E →
      RepList kexprListEnum (TmOExact κ) h Ps xps →
      Heap.Extends h h' ∧ ∃ E', TmOExact κ h' E' r ∧ AddrIn S κ E' ∧
        Eventually fun f => peelCtorParams V f depth lift aux Ps n j E = some E' := by
  intro n
  induction n with
  | zero =>
    intro j hb hj xrc xty xps xtys r h h' cs E ev hbnd hsub hE hEin hPs'
    rcases Obs.«KernelCheck::peel_ctor_params_subst».obs ev with
      ⟨hv, rfl, rfl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hne, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hne, -⟩
    · exact ⟨Heap.Extends.refl _, E, hE, hEin, Eventually.always fun _ => rfl⟩
    all_goals exact (hne (by simp)).elim
  | succ n ih =>
    intro j hb hj xrc xty xps xtys r h h' cs E ev hbnd hsub hE hEin hPs'
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    have rsub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
      fun hs c hc => hsub c (hs c hc)
    rcases Obs.«KernelCheck::peel_ctor_params_subst».obs ev with
      ⟨hv, -, -, -⟩ |
      ⟨w₁, x_body, w₂, v₅, m₆, cs₇, v₁₁, m₁₁, cs₁₂, cs₁₅, v₁₅, v₁₆, hne, ld, evp, evi, op₁, op₂,
        ev₁, hc⟩ |
      ⟨v₂, m₂, p₂, cs_w, w₁, x_body, w₂, v₃, m₃, cs₃, v₃₆, m₃₆, cs₃₇, cs₄₀, v₄₁, v₄₂, hne, ld,
        hne', evw, ld', evp, evi, op₁, op₂, ev₁, hc⟩
    · exact absurd (field_natCast_eq_zero (by omega) hv) (by omega)
    · obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
      obtain ⟨ext₁, hp⟩ := ctor_subst_param_for_spec (κ := κ) hdepth (by omega) hlift hPs
        (hj j le_rfl (by omega)) evp (sub fun c hc' => by rw [hc]; simp [hc']) hPs'
      have hinst := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc'])
        (hB.mono ext₁) hp evi
      have hinstIn : AddrIn S κ (B.instantiate1Lift (ctorSubstParamFor j depth lift aux Ps) 0) :=
        addrIn_instantiate1Lift (addrIn_ctorSubstParamFor hPsIn) hEin.2
      have ext₂ : Heap.Extends m₆ m₁₁ := ObsFn.heap_extends evi
      obtain rfl := binop_sub_one_nat (by omega) op₁
      obtain rfl := binop_add_one_nat op₂
      simp only [Nat.add_sub_cancel] at ev₁
      obtain ⟨-, E', hE', hE'in, hev⟩ := ih (j + 1) (by omega)
        (fun i hi1 hi2 hni => hj i (by omega) (by omega) hni) ev₁
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (rsub fun c hc' => by rw [hc]; simp [hc'])
        hinst hinstIn (tmOExactList_mono (ext₁.trans ext₂) hPs')
      exact ⟨hext, E', hE', hE'in, hev.mono fun f hf => by
        simp only [peelCtorParams, binderOf_forallE, hf]⟩
    · obtain ⟨ext₀, W0, htoW, hW, -, hWin⟩ := recon_whnf_spec hA hD hI hC hM evw
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (rsub fun c hc' => by rw [hc]; simp [hc']) hE hEin
      obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hW ld'
      obtain ⟨ext₁, hp⟩ := ctor_subst_param_for_spec (κ := κ) hdepth (by omega) hlift hPs
        (hj j le_rfl (by omega)) evp (sub fun c hc' => by rw [hc]; simp [hc'])
        (tmOExactList_mono ext₀ hPs')
      have hinst := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc'])
        (hB.mono ext₁) hp evi
      have hinstIn : AddrIn S κ (B.instantiate1Lift (ctorSubstParamFor j depth lift aux Ps) 0) :=
        addrIn_instantiate1Lift (addrIn_ctorSubstParamFor hPsIn) hWin.2
      have ext₂ : Heap.Extends m₃ m₃₆ := ObsFn.heap_extends evi
      obtain rfl := binop_sub_one_nat (by omega) op₁
      obtain rfl := binop_add_one_nat op₂
      simp only [Nat.add_sub_cancel] at ev₁
      obtain ⟨-, E', hE', hE'in, hev⟩ := ih (j + 1) (by omega)
        (fun i hi1 hi2 hni => hj i (by omega) (by omega) hni) ev₁
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (rsub fun c hc' => by rw [hc]; simp [hc'])
        hinst hinstIn (tmOExactList_mono ((ext₀.trans ext₁).trans ext₂) hPs')
      exact ⟨hext, E', hE', hE'in, ((binderOf_whnf htoW).and hev).mono fun f ⟨hb, hf⟩ => by
        simp only [peelCtorParams, hb, isForall, hf]⟩

end Sites

end IxVM.Refinement.Binding.FamilyRecon
