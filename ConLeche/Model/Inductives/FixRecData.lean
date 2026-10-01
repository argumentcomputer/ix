module

public import ConLeche.Model.Inductives.FixRecRead
public import ConLeche.Model.Inductives.FixCtorReads
import ConLeche.Verify.Inductives.FixInv
import ConLeche.Verify.Inductives.FixWF
public import ConLeche.Model.Inductives.SumStageRec
import ConLeche.Model.Annot.BitLevels
public section

/-!
# The recursive recursor's data (task #188)

The generated recursive recursor type's data (`SumRecData` — the same
record as the sum route's, read off the generated type by
`denoteMeta_structRecTyR`), its universe (the kernel's own sort
inference at the pre-recursor environment, through the claims'
sort row), its opening at every assignment, and the readings'
insensitivity to the recursor's own valuation (the binder data
mention the former and the constructors only).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  NativeParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The data, per block -/

/-- The recursive recursor's binder data at the block. -/
@[expose] def fixRdsAV {env : Env} (m : EnvModel V env) (p : NativeParts)
    (ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (ctorsA : List (ConstantVal × Nat)) (ψ : Name → Nat) : List (Nat × Nat × AnnotTerm) :=
  fixRecDataAV m p.cvT.name ψ p.nP p.nIdx (ConLeche.structElimLevel p.elim p.large)
    ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP) (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)

theorem fixRdsAV_length {m : EnvModel V env} {p : NativeParts}
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ctorsA : List (ConstantVal × Nat)}
    {cvTa : ConstantVal} (hFD : FormerData m cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    (ψ : Name → Nat) :
    (fixRdsAV m p ppsAll dsF esF ksF eissF tssF ctorsA ψ).length = p.nP + ctorsA.length + p.nIdx + 2 := by
  unfold fixRdsAV
  rw [fixRecDataAV_length (by rw [List.length_take, hFD.len ψ]; omega)
    (by rw [List.length_drop, hFD.len ψ]; omega), fixCtorDataList_length]

/-! ## Insensitivity to the recursor's valuation -/

section Congr

variable {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂} {ψ : Name → Nat}
  {T : Name} {nP nIdx : Nat}

theorem minorAVAtR_congr {C : Name} {nF b o : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {Es : List AnnotTerm} {recIdx : List Nat} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))}
    (hC : m₁.acval C ψ = m₂.acval C ψ) :
    minorAVAtR m₁ C ψ nP nF b o ds Es recIdx tls Eiss
      = minorAVAtR m₂ C ψ nP nF b o ds Es recIdx tls Eiss := by
  unfold minorAVAtR
  rw [hC]

theorem fixMinorsData_congr {b : Nat} :
    ∀ (cds : List CtorDatumR) (o : Nat), (∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) →
      fixMinorsData m₁ ψ nP b cds o = fixMinorsData m₂ ψ nP b cds o
  | [], _, _ => rfl
  | (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, o, h => by
    simp only [fixMinorsData]
    rw [minorAVAtR_congr (h _ List.mem_cons_self),
      fixMinorsData_congr cs (o + 1) fun cd hcd => h cd (List.mem_cons_of_mem _ hcd)]

theorem fixRuleDataAV_congr {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List CtorDatumR}
    {ds : List (Nat × Nat × AnnotTerm)}
    (hT : m₁.acval T ψ = m₂.acval T ψ) (hC : ∀ cd ∈ cds, m₁.acval cd.1 ψ = m₂.acval cd.1 ψ) :
    fixRuleDataAV m₁ T ψ nP nIdx ℓ pps ips cds ds = fixRuleDataAV m₂ T ψ nP nIdx ℓ pps ips cds ds := by
  unfold fixRuleDataAV motiveAVI
  rw [hT, fixMinorsData_congr cds 1 hC]

end Congr

/-! ## The data, read off the generated type -/

/-- **The recursor's data**, read off the generated type, and its
universe: the kernel's sort inference, through the claims' sort row. -/
theorem fixRecData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {p : NativeParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {caps : IndCaps}
    (hRec : ConLeche.checkNativeRec (ConLeche.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {bsT : List (Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env} {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF i cA) :
    SumRecData mp.base2 cvRa p.nP ctorsA.length p.nIdx (ConLeche.structElimLevel p.elim p.large)
        (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA) ∧
      ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
        interp V ρ (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
          (recConcAV ctorsA.length p.nIdx)) ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨cvRi, recTy, sty, u, -, hgen, htp, -, hbt, hRf, hsty, hens, -, -, rfl⟩ :=
    ConLeche.checkNativeRec_shape hRec
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  have hcr : ∀ ψ, CtorReadsR mp.base2 ψ p.cvT.name p.cvT.levelParams p.nP p.nIdx
      (ConLeche.nativeCtors4 ctorsA p.kinds) (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) :=
    fun ψ => fixCtorReadsR_of ψ hlenK hks hcf
  have hread : ∀ ψ : Name → Nat, denoteMeta mp.base2.acval env ψ 0 recTy
      = some (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
          (recConcAV ctorsA.length p.nIdx)) := fun ψ => by
    have := denoteMeta_structRecTyR hfT (show (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
        = p.cvT.levelParams from hlpsT) (hcr ψ) hgen hTf hTb
      (by rw [hstripT]; rfl) hopT (hFD.read ψ) (hFD.len ψ)
    rwa [fixCtorDataList_length] at this
  have hw : Expr.WScoped 0 recTy := Expr.WScoped.of_not_hasFvar hRf
  have hL : Expr.LeavesBounded recTy := Expr.LeavesBounded.of_not_hasFvar hRf
  have hnil : recTy.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf
  refine ⟨⟨hread, fun ψ => fixRdsAV_length hFD ψ, ?_, ?_, ?_, ?_⟩, u, fun ψ ρ => ?_⟩
  · intro ψ d hd
    unfold fixRdsAV at hd
    rw [mem_fixRecDataAV hd, pwBit_eq_zero_iff, ConLeche.PropWhen.zeronessOf_sound, beq_iff_eq]
  · intro ψ ρ
    have hc := claimsAt_of hμ mp ψ F
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hsty hw hbt hL (CtxOk.nil hnil) (hread ψ)
    exact hokT ρ (Sat_nil V ρ)
  · intro ψ
    have hst := stripPisAV_mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
      (recConcAV ctorsA.length p.nIdx)
    exact (stripPisAV_below hst (bvarsBelow_of_reading hw hbt (hread ψ))).1
  · intro ψ₁ ψ₂ hφ
    have h2 := hread ψ₂
    have h1 : denoteMeta mp.base2.acval env ψ₂ 0 recTy
        = some (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ₁)
            (recConcAV ctorsA.length p.nIdx)) := by
      rw [← denoteMeta_params_ext mp.base2 hφ 0 recTy htp]
      exact hread ψ₁
    exact (mkPisAV_inj (by rw [fixRdsAV_length hFD ψ₁, fixRdsAV_length hFD ψ₂])
      (Option.some.inj (h1.symm.trans h2))).1
  · have hc := claimsAt_of hμ mp ψ F
    exact (hc.sortRow hsty hens hw hbt hL (CtxOk.nil hnil) (hread ψ) ρ (Sat_nil V ρ)).2

/-! ## The opening -/

/-- The generated recursive recursor type's opening, at every
assignment. -/
theorem fixRecOpenedAll (mp : EnvModelM V μ env)
    {F : Nat} {p : NativeParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr}
    (hRec : ConLeche.checkNativeRec (ConLeche.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    {bsT : List (Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    (hlenK : p.kinds.length = ctorsA.length)
    {rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length p.nIdx (ConLeche.structElimLevel p.elim p.large)
      rds) :
    ∃ (fvsR : List Expr) (oR : Expr), ∀ ψ : Name → Nat,
      Opened mp.base2 ψ (p.nP + ctorsA.length + p.nIdx + 2) cvRa.type fvsR oR
        (((rds ψ).map (·.2.2)).reverse) (recConcAV ctorsA.length p.nIdx) := by
  obtain ⟨cvRi, recTy, sty, u, -, hgen, -, -, hbt, hRf, -, -, -, -, rfl⟩ :=
    ConLeche.checkNativeRec_shape hRec
  obtain ⟨tbs, itele, motiveTy, major, minors, hsT, -, hmaj, hmin, hrec⟩ :=
    ConLeche.structRecTyR_unfold hgen
  generalize hctors : ConLeche.nativeCtors4 ctorsA p.kinds = ctors at hmaj hmin
  have hlenC : ctors.length = ctorsA.length := by
    rw [← hctors]; exact ConLeche.nativeCtors4_length hlenK.symm
  -- the former's index telescope strips
  have hstripI : (itele.stripPis p.nIdx).isSome = true :=
    stripPis_isSome_drop p.nP (by rw [hstripT]; rfl) hsT
  obtain ⟨⟨ibs, ibody⟩, hsI⟩ := Option.isSome_iff_exists.mp hstripI
  obtain ⟨ibs', hsI'⟩ := stripPis_liftLooseBVars p.nIdx ctors.length.succ 0 hsI
  -- the major's telescope: the index binders then the major binder
  have hs3 := ConLeche.replacePisPw_stripPis p.nIdx hmaj hsI'
  have hs4 : ∃ bs, (Expr.forallE
      (ConLeche.structFamI p.cvT.name p.cvT.levelParams p.nP p.nIdx (ctors.length + 1) 0)
      (Expr.mkAppN (.bvar (p.nIdx + ctors.length + 1)) (ConLeche.structPsAt 1 p.nIdx ++ [.bvar 0]))
      ⟨Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)⟩).stripPis 1
      = some (bs, Expr.mkAppN (.bvar (p.nIdx + ctors.length + 1))
        (ConLeche.structPsAt 1 p.nIdx ++ [.bvar 0])) :=
    ⟨_, rfl⟩
  obtain ⟨bs4, hs4⟩ := hs4
  have hs34 := ConLeche.stripPis_append p.nIdx hs3 hs4
  -- the minors' telescope strips its `n` binders
  have hsmin : ∀ (cs : List (Name × Nat × Expr × List Nat)) (o : Nat) (body mins : Expr),
      ConLeche.structMinorsPisR p.cvT.levelParams p.nP
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) cs o body = some mins →
      ∃ bs, mins.stripPis cs.length = some (bs, body) := by
    intro cs
    induction cs with
    | nil => intro o body mins h; rw [ConLeche.structMinorsPisR_nil h]; exact ⟨[], rfl⟩
    | cons c cs ih =>
      intro o body mins h
      obtain ⟨C, nF, cty, recIdx⟩ := c
      obtain ⟨mty, rest, -, hrest, rfl⟩ := ConLeche.structMinorsPisR_cons h
      obtain ⟨bs, hbs⟩ := ih (o + 1) body rest hrest
      exact ⟨((mty : Expr),
        ⟨Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)⟩) :: bs,
        by simp [Expr.stripPis, hbs]⟩
  obtain ⟨bsm, hbsm⟩ := hsmin _ _ _ _ hmin
  have h23 := ConLeche.stripPis_append _ hbsm hs34
  have hs2 := ConLeche.stripPis_append 1 (e := Expr.forallE motiveTy minors
      ⟨Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)⟩)
    (bs := [((motiveTy : Expr),
      ⟨Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)⟩)])
    (by simp [Expr.stripPis]) h23
  have hs1 := ConLeche.replacePisPw_stripPis p.nP hrec hsT
  have hs := ConLeche.stripPis_append p.nP hs1 hs2
  rw [hlenC] at hs
  rw [show p.nP + (1 + (ctorsA.length + (p.nIdx + 1))) = p.nP + ctorsA.length + p.nIdx + 2 from by
    omega] at hs
  obtain ⟨fvsR, oR, hop⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + ctorsA.length + p.nIdx + 2) 0
    (by rw [hs]; rfl)
  exact ⟨fvsR, oR, fun ψ =>
    opened_of_peel hop hRf hbt (hRD.read ψ) (hRD.len ψ) (hRD.okTy ψ)⟩

end ConLeche.Model
