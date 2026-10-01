module

public import ConLeche.Model.Inductives.DeclSum
public section

/-!
# The constructors' loop, over any former leaf (task #188)

`ctorsLoopGen`: `sumCtorsLoop` (`ConLeche/Model/Inductives/DeclSum.lean`)
with the former's leaf abstract — any closed reading `leafT` — and,
per constructor, the fibre fold `stageCtorGen` consumes: the leaf at
the parameter variables and the constructor's index readings, under a
fitting field spine, is the indexed sum route's restricted tagged
union at the index values.  The recursive route provides the fold from
the fixed-point leaf (`fixLeafApp`, `fixFamI_app_eq_sum`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

set_option maxHeartbeats 6400000 in
/-- **The constructors' conses, in order.** -/
theorem ctorsLoopGen (hμ : μ.verifiedChecks = true)
    {F : Nat} {p : InductiveShape} {env₀ envI : Env} {cvTa : ConstantVal}
    {ctors ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hCtors : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ envI p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa ctors = .ok (ctorsA, sortss))
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      fssOf p.nP (ctorDataList dsF esF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF esF ψ₂ ctorsA 0))
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0),
      FieldsBelow p.nP Fs)
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
      SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))
    (hIdx : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (cA : ConstantVal × Nat)
      (A : (Name → Nat) → AnnotTerm)
      (mC : EnvModel V ⟨.ctorInfo cA.1 p.nP cA.2 :: env'.consts⟩),
      cA ∈ ctorsA → env'.find? cA.1.name = none →
      mC.acval = acvalWith m'.acval cA.1.name A → Inv m' → Inv mC)
    -- the block's capability record and its laws at every carrier the
    -- invariant reaches (task #210 Part A)
    (caps : IndCaps)
    (leafT : (Name → Nat) → AnnotTerm)
    (hTlawsOf : ∀ {env' : Env} (m' : EnvModel V env') (k : Nat) (cA : ConstantVal × Nat),
      ctorsA[k]? = some cA → Inv m' →
      FormerData m' cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m'.acval p.cvT.name ψ = leafT ψ) →
      (∀ ψ, m'.acval cA.1.name ψ
        = sumMkAV (p.resSort.eval ψ) k (dsF k ψ) (((dsF k ψ).drop p.nP).map (·.2.2))
            (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))) →
      CapsLawsAt m' p.cvT.name cvTa caps)
    (hfold : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
        interp V (consList bs ρ)
            (AnnotTerm.mkAppN (leafT ψ) (paramBvars p.nP cA.2 ++ esF j ψ))
          = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ)
              (consList (idxValsAt ρ (esF j ψ) bs) ρ)
              (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                (essOf (ctorDataList dsF esF ψ ctorsA 0))))) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ i, rest[i]? = ctorsA[k + i]?) → k + rest.length = ctorsA.length →
      ConLeche.EtaFamiliesClosedExcept env p.cvT.name →
      env.find? p.cvT.name = some (.indInfo cvTa caps) →
      FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, mp.base2.acval p.cvT.name ψ = leafT ψ) →
      ConsedAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      PendingAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      Inv mp.base2 →
      ∃ mp' : EnvModelM V μ (ConLeche.consSumCtors p.nP rest env),
        ConLeche.EtaFamiliesClosedExcept (ConLeche.consSumCtors p.nP rest env) p.cvT.name ∧
        (ConLeche.consSumCtors p.nP rest env).find? p.cvT.name
          = some (.indInfo cvTa caps) ∧
        FormerData mp'.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll ∧
        (∀ ψ, mp'.base2.acval p.cvT.name ψ = leafT ψ) ∧
        ConsedAt mp'.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
          idxF dsF esF srcsF ctorsA ctorsA.length ∧
        Inv mp'.base2
  | [], k, env, mp, _, hk, hE, hfT, hFD, hleafT, hcons, _, hinv => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    exact ⟨mp, hE, hfT, hFD, hleafT, hcons, hinv⟩
  | cA :: rest, k, env, mp, hrest, hk, hE, hfT, hFD, hleafT, hcons, hpend, hinv => by
    have hcAk : ctorsA[k]? = some cA := by
      have := hrest 0; simpa using this.symm
    obtain ⟨hlen, -, hall⟩ := ConLeche.checkSumCtors_inv hCtors
    have hkl : k < ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hcAk).1; omega
    obtain ⟨hnF, _, -, hCtor⟩ := hall k (ctors[k]) cA (List.getElem?_eq_getElem hkl) hcAk
    rw [← hnF] at hCtor
    obtain ⟨hfresh, htr, hidxRes, hCD⟩ := hpend k cA (Nat.le_refl _) hcAk
    have hlpsC : cA.1.levelParams = p.cvT.levelParams := hlpsA cA (List.mem_of_getElem? hcAk)
    have hTC : p.cvT.name ≠ cA.1.name := by
      intro h; rw [h, hfresh] at hfT; exact nomatch hfT
    have hFsj : ∀ ψ, (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))[k]?
        = some (((dsF k ψ).drop p.nP).map (·.2.2)) := by
      intro ψ
      rw [fssOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl
    have hEsj : ∀ ψ, (essOf (ctorDataList dsF esF ψ ctorsA 0))[k]? = some (esF k ψ) := by
      intro ψ
      rw [essOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl
    -- the stage
    have hfoldC : ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
        ∀ bs : List V, SpineFit ρ (((dsF k ψ).drop p.nP).map (·.2.2)) bs →
          interp V (consList bs ρ) (ctorBodyAVI mp.base2 p.cvT.name p.nP cA.2 ψ (esF k ψ))
            = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ)
                (consList (idxValsAt ρ (esF k ψ) bs) ρ)
                (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                  (essOf (ctorDataList dsF esF ψ ctorsA 0)))) := by
      intro ψ ρ hρ bs hsp
      unfold ctorBodyAVI
      rw [hleafT ψ]
      exact hfold k cA hcAk ψ ρ hρ bs hsp
    have hcbT : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1
    have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 p.nP cA.2) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    obtain ⟨mpC, hacC⟩ := stageCtorGen (j := k) hE mp hCtor hfresh htr hfT hlpsT hlpsC
      (fun m₂ hag hleafC₂ => by
        have hac : m₂.acval = acvalWith mp.base2.acval cA.1.name
            (fun ψ => m₂.acval cA.1.name ψ) := by
          funext n ψ
          by_cases hn : n = cA.1.name
          · subst hn; exact (congrFun acvalWith_self ψ).symm
          · rw [hag n hn]; exact (congrFun (acvalWith_ne hn) ψ).symm
        exact hTlawsOf m₂ k cA hcAk (hInv mp.base2 cA (fun ψ => m₂.acval cA.1.name ψ) m₂
            (List.mem_of_getElem? hcAk) hfresh hac hinv)
          (hFD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh (hcross _) hcbT m₂ hac)
          (fun ψ => by rw [hag _ hTC]; exact hleafT ψ) hleafC₂)
      hFD hCD
      hfoldC hFsj hEsj hFssParams hFssBelow (hiff k cA hcAk)
      (fun ψ ρ hρ => hFssOkP ψ ρ ((hiff k cA hcAk ψ ρ).mpr hρ)) (hIdx k cA hcAk)
    -- the invariants at the extension
    have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ htr
    have hE' : ConLeche.EtaFamiliesClosedExcept ⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts⟩
        p.cvT.name :=
      hE.cons hfresh (fun _ _ heq => nomatch heq)
    have hfT' : (⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts⟩ : Env).find? p.cvT.name
        = some (.indInfo cvTa caps) := ConLeche.Env.find?_cons_of_fresh hfresh hfT
    have hFD' : FormerData mpC.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
      hFD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh (hcross _) hcbT mpC.base2 hacC
    have hleafT' : ∀ ψ, mpC.base2.acval p.cvT.name ψ = leafT ψ := by
      intro ψ
      rw [hacC]
      show acvalWith mp.base2.acval cA.1.name _ p.cvT.name ψ = _
      rw [acvalWith_ne hTC]
      exact hleafT ψ
    have hcons' : ConsedAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      rcases Nat.lt_or_ge i k with hlt | hge
      · obtain ⟨⟨hfi, hlpsi, hCDi⟩, hresi, hleaf⟩ := hcons i cAi hlt hcAi
        have hne : cAi.1.name ≠ cA.1.name := names_ne_of_nodup hnd hcAi hcAk (by omega)
        have hcbi : ConstsBound env cAi.1.type :=
          constsBound_of_constsResolve _
            (mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfi)).2.2.1
        refine ⟨⟨ConLeche.Env.find?_cons_of_fresh hfresh hfi, hlpsi,
          hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross hcbi
            (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hresi e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cAi.1.name ψ = _
        rw [acvalWith_ne hne]
        exact hleaf ψ
      · have hik : i = k := by omega
        subst hik
        obtain rfl := Option.some.inj (hcAk.symm.trans hcAi)
        refine ⟨⟨ConLeche.Env.find?_cons_self (.ctorInfo cA.1 p.nP cA.2) env, hlpsC,
          hCD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross hcbC
            (fun e he => constsBound_of_constsResolve _ (hidxRes e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hidxRes e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cA.1.name ψ = _
        rw [acvalWith_self]
    have hpend' : PendingAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      obtain ⟨hfreshi, htri, hresi, hCDi⟩ := hpend i cAi (by omega) hcAi
      have hne : cA.1.name ≠ cAi.1.name := names_ne_of_nodup hnd hcAk hcAi (by omega)
      refine ⟨?_, Expr.constsResolve_mono htri, fun e he => Expr.constsResolve_mono (hresi e he),
        hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross
          (constsBound_of_constsResolve _ htri)
          (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩
      rw [ConLeche.Env.find?_cons]
      split
      · next h => exact absurd h hne
      · exact hfreshi
    have hrest' : ∀ i, rest[i]? = ctorsA[k + 1 + i]? := by
      intro i
      have := hrest (i + 1)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    have hinv' : Inv mpC.base2 :=
      hInv mp.base2 cA _ mpC.base2 (List.mem_of_getElem? hcAk) hfresh hacC hinv
    exact ctorsLoopGen hμ hCtors hnd hlpsT hlpsA hFssParams hFssBelow hiff hFssOkP hIdx Inv hInv
      caps leafT hTlawsOf hfold rest (k + 1) _ mpC hrest' (by simp at hk; omega) hE' hfT' hFD'
      hleafT' hcons' hpend' hinv'


end ConLeche.Model
