module

public import ConLeche.Model.Inductives.FixLeafOk
public section

/-!
# The recursive former's cons (task #188)

`stageFixFormer`: the P step at the recursive family's type former,
for given block data — the X-chain sources `Fss`, the index-expression
readings `Eiss`, the residual index readings `Ess`, the recursive
positions `rss` — `stageSumFormer` with the fixed-point leaf
`nativeTyAVI`.  The leaf's hereditary premises (`ParamsOkXI`, the
tower's validity) are walked from the former's data down to the frame
below the parameters and the index variables, where the functor's
premise (`XChainsOk`) and the index telescope's grading, both at the
parameter frame, are the base (`fixLeafWalks`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

omit [SetTheory V] in
theorem frameIdx_eq_reverse_map (n : Nat) (σ : Nat → V) :
    frameIdx n σ = (List.range n).reverse.map σ := by
  apply List.ext_getElem
  · simp [frameIdx]
  · intro l h1 h2
    simp only [frameIdx, List.getElem_map, List.getElem_reverse, List.getElem_range]
    simp only [List.length_range]

/-- **The fixed-point leaf's two hereditary premises**, from the
former's data and the base facts at the parameter frame. -/
theorem fixLeafWalks {m : EnvModel V env} {cvT : ConstantVal} {nP nIdx : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps)
    {u : (Name → Nat) → Nat} {rss : List (List Bool)}
    {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : (Name → Nat) → List (List (List AnnotTerm))} {Fss Ess : (Name → Nat) → List (List AnnotTerm)}
    (hIdx : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρp →
      IdxOk (u ψ) ρp (((pps ψ).drop nP).map (·.2.2)) ∧ FieldsValid ρp (((pps ψ).drop nP).map (·.2.2)))
    (hX : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρp →
      XChainsOk (u ψ) (resSort.eval ψ) ρp (((pps ψ).drop nP).map (·.2.2)) rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ))
    (hXV : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρp →
      ∀ X, X ∈ˢ lfpFamSpace V (resSort.eval ψ) (idxSet (u ψ) ρp (((pps ψ).drop nP).map (·.2.2))) →
      ∀ t, t ∈ˢ idxSet (u ψ) ρp (((pps ψ).drop nP).map (·.2.2)) →
      SumFieldsValid (cons t (cons X ρp))
        (chainsXI (u ψ) (((pps ψ).drop nP).map (·.2.2)) (((pps ψ).drop nP).map (·.2.2)).length
          rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkXI (u ψ) (resSort.eval ψ) ρ (((pps ψ).drop nP).map (·.2.2)) rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)
        (pps ψ) ∧
      UnderTowerValid ρ
        (.app ((fixBodyAVI (u ψ) (resSort.eval ψ) (((pps ψ).drop nP).map (·.2.2))
            (((pps ψ).drop nP).map (·.2.2)).length rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)).liftN
              (((pps ψ).drop nP).map (·.2.2)).length 0)
          (mkTowerGo (u ψ) (((pps ψ).drop nP).map (·.2.2))))
        (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  have hent : ∀ i, i < nP + nIdx → ∃ p, (pps ψ)[i]? = some p ∧
      p.2.2 = (((pps ψ).map (·.2.2)).reverse).getD (nP + nIdx - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ).map (·.2.2)).reverse).drop (nP + nIdx - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  have hIdsLen : ((((pps ψ).drop nP).map (·.2.2))).length = nIdx := by simp [hFD.len ψ]
  -- the base facts at a frame satisfying the whole telescope
  have hbase : ∀ ρ : Nat → V, Sat V (((pps ψ).map (·.2.2)).reverse) ρ →
      FixBaseI (u ψ) (resSort.eval ψ) ρ (((pps ψ).drop nP).map (·.2.2)) rss (tlss ψ) (Eiss ψ) (Fss ψ)
        (Ess ψ) ∧
      AnnotValid V ρ
        (.app ((fixBodyAVI (u ψ) (resSort.eval ψ) (((pps ψ).drop nP).map (·.2.2))
            (((pps ψ).drop nP).map (·.2.2)).length rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)).liftN
              (((pps ψ).drop nP).map (·.2.2)).length 0)
          (mkTowerGo (u ψ) (((pps ψ).drop nP).map (·.2.2)))) := by
    intro ρ hρ
    rw [reverse_map_take_drop (pps ψ) nP] at hρ
    -- the parameter frame
    have hρp : Sat V (((pps ψ).take nP).map (·.2.2)).reverse (fun j => ρ (j + nIdx)) := by
      have := Sat_drop hρ nIdx
      rwa [List.drop_append_of_le_length (by rw [List.length_reverse, hIdsLen]; exact Nat.le_refl _),
        List.drop_eq_nil_of_le (by rw [List.length_reverse, hIdsLen]; exact Nat.le_refl _),
        List.nil_append] at this
    have hsh : shiftE (((pps ψ).drop nP).map (·.2.2)).length 0 ρ = fun j => ρ (j + nIdx) := by
      rw [shiftE_zero, hIdsLen]
    -- the index spine
    have hspI := spineFit_of_sat (Δ₀ := (((pps ψ).take nP).map (·.2.2)).reverse)
      (Ds := ((pps ψ).drop nP).map (·.2.2)) hρ
    rw [hIdsLen, ← frameIdx_eq_reverse_map] at hspI
    obtain ⟨hI, hIV⟩ := hIdx ψ _ hρp
    have hXρ := hX ψ _ hρp
    refine ⟨⟨by rw [hsh]; exact hI, by rw [hsh]; exact hXρ.hok, by rw [hsh, hIdsLen]; exact hspI⟩, ?_⟩
    have hfr : consList (frameIdx nIdx ρ) (fun j => ρ (j + nIdx)) = ρ := by
      have := consList_frameIdx nIdx ρ
      rwa [shiftE_zero] at this
    have hv := fixBody_validV (w := resSort.eval ψ) hI hIV (hXV ψ _ hρp) hspI
    rw [hfr] at hv
    exact hv
  generalize hIdsE : (((pps ψ).drop nP).map (·.2.2)) = Ids at hbase ⊢
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkXI (u ψ) (resSort.eval ψ) ρ Ids rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hbase ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hFD.bits ψ d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ
        (.app ((fixBodyAVI (u ψ) (resSort.eval ψ) Ids Ids.length rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)).liftN
              Ids.length 0)
          (mkTowerGo (u ψ) Ids)) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hbase ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw

/-- **The P step at the recursive former's cons**, for given block
data. -/
theorem stageFixFormer (mp : EnvModelM V μ env)
    (hE₀ : ConLeche.EtaFamiliesClosed env)
    {F : Nat} {p : InductiveShape} {cvT cvTa : ConstantVal}
    -- the former's `checkConstantVal` run at the block's header (as at
    -- `stageSumFormer`)
    (hccv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cvT = .ok cvTa)
    (hname₀ : cvT.name = p.cvT.name)
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort pps)
    (u : (Name → Nat) → Nat) (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : (Name → Nat) → List (List (List AnnotTerm))) (Fss Ess : (Name → Nat) → List (List AnnotTerm))
    (hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) →
      u ψ₁ = u ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss ψ₁ = Eiss ψ₂ ∧ Fss ψ₁ = Fss ψ₂ ∧ Ess ψ₁ = Ess ψ₂)
    (hbelow : ∀ ψ, ∀ chain ∈ chainsXI (u ψ) (((pps ψ).drop p.nP).map (·.2.2)) p.nIdx rss (tlss ψ) (Eiss ψ)
      (Fss ψ) (Ess ψ), FieldsBelow (p.nP + 2) chain)
    (hIdx : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρp →
      IdxOk (u ψ) ρp (((pps ψ).drop p.nP).map (·.2.2)) ∧
      FieldsValid ρp (((pps ψ).drop p.nP).map (·.2.2)))
    (hX : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (u ψ) (p.resSort.eval ψ) ρp (((pps ψ).drop p.nP).map (·.2.2)) rss (tlss ψ) (Eiss ψ) (Fss ψ)
        (Ess ψ))
    (hXV : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρp →
      ∀ X, X ∈ˢ lfpFamSpace V (p.resSort.eval ψ)
        (idxSet (u ψ) ρp (((pps ψ).drop p.nP).map (·.2.2))) →
      ∀ t, t ∈ˢ idxSet (u ψ) ρp (((pps ψ).drop p.nP).map (·.2.2)) →
      SumFieldsValid (cons t (cons X ρp))
        (chainsXI (u ψ) (((pps ψ).drop p.nP).map (·.2.2)) (((pps ψ).drop p.nP).map (·.2.2)).length
          rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)))
    -- the block's capability record and its laws at the cons (task #210
    -- Part A)
    (caps : IndCaps)
    -- the record's arities, from the install's telescope pin
    (hicw : ConLeche.IndCapsWF (.indInfo cvTa caps))
    (hTlaws : ∀ m₂ : EnvModel V ⟨.indInfo cvTa caps :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => nativeTyAVI (u ψ) (p.resSort.eval ψ) (pps ψ) (((pps ψ).drop p.nP).map (·.2.2))
          rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)) →
      CapsLawsAt m₂ cvTa.name cvTa caps) :
    ∃ mp' : EnvModelM V μ ⟨.indInfo cvTa caps :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => nativeTyAVI (u ψ) (p.resSort.eval ψ) (pps ψ) (((pps ψ).drop p.nP).map (·.2.2))
          rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)) := by
  obtain ⟨hfind, hnres, hpshape, -, -, -, type', -, -, -, -, htr', -, -, hty⟩ :=
    ConLeche.checkConstantVal_inv hccv
  have hname : cvTa.name = p.cvT.name := by rw [hty]; exact hname₀
  have hfresh : env.find? cvTa.name = none := by
    rw [hname, ← hname₀]; exact hfind
  have htr : cvTa.type.constsResolve env = true := by rw [hty]; exact htr'
  have hcb : ConstsBound env cvTa.type := constsBound_of_constsResolve _ htr
  have hwfI : ConLeche.EnvWF ⟨.indInfo cvTa caps :: env.consts⟩ :=
    ConLeche.envWF_cons_ind mp.base2.wf hccv hicw
  have hIdsLen : ∀ ψ, ((((pps ψ).drop p.nP).map (·.2.2))).length = p.nIdx := by
    intro ψ; simp [hFD.len ψ]
  let A : (Name → Nat) → AnnotTerm :=
    fun ψ => nativeTyAVI (u ψ) (p.resSort.eval ψ) (pps ψ) (((pps ψ).drop p.nP).map (·.2.2))
      rss (tlss ψ) (Eiss ψ) (Fss ψ) (Ess ψ)
  have hAbelow : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := fun ψ =>
    nativeTyAVI_below (hFD.below ψ) (hFD.len ψ) (hIdsLen ψ) (hbelow ψ) rfl
  have hwalks := fixLeafWalks hFD hIdx hX hXV
  have hreadI : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa caps :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (p.resSort.eval ψ))) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .indInfo cvTa caps) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : ConLeche.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa caps).name = false := by
    show ConLeche.reservedBasisNames.contains cvTa.name = false
    rw [hname, ← hname₀]; exact hnres
  have hpshapeI : (ConstantInfo.indInfo cvTa caps).name.isProjFnShape = false := by
    show cvTa.name.isProjFnShape = false
    rw [hname, ← hname₀]; exact hpshape
  refine declStep_preserves_of_ind_member_cons mp (c₀ := .indInfo cvTa caps)
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHead.ofFresh hwfI (fun ψ => hAbelow ψ) hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    obtain ⟨hp, hw⟩ := hFD.params ψ₁ ψ₂ hφ
    obtain ⟨hu, htlss, hEiss, hFss, hEss⟩ := hParams ψ₁ ψ₂ hφ
    show nativeTyAVI _ _ _ _ _ _ _ _ _ = nativeTyAVI _ _ _ _ _ _ _ _ _
    rw [hp, hw, hu, htlss, hEiss, hFss, hEss]
  · exact fun ψ ρ => nativeTyAVI_wellDenoted (hwalks ψ ρ).1
  · exact fun ψ ρ => (nativeTyAVI_wellDenotedV (hwalks ψ ρ).1 (hwalks ψ ρ).2).2
  · exact fun ψ => ⟨_, hreadI ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact nativeTyAVI_mem (hwalks ψ ρ).1
  · intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .indInfo cvTa caps)
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeI
      (Or.inl ⟨cvTa, caps, rfl, rfl⟩)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.indInfo cvTa caps) env
    obtain ⟨rfl, rfl⟩ :=
      ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
    exact hTlaws m₂ hac

end ConLeche.Model
