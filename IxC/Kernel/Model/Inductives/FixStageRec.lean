module

public import IxC.Kernel.Model.Inductives.NativeJudge
public import IxC.Kernel.Model.Inductives.FixRuleData
public import IxC.Kernel.Model.Inductives.FixRuleOk
import IxC.Kernel.Model.Inductives.FixLeafOk
import IxC.Kernel.Model.Inductives.FixRuleKit
import IxC.Kernel.Model.Inductives.FixRecLeaf
import IxC.Kernel.Semantics.Tower.FixWire
public section

/-!
# The recursive recursor's stage, part 1: the rule law (task #188)

The semantic data of a recursive block at an assignment (`fssOfR`,
`essOfR`, `eissOfR`, `rssOfK`), the recursor leaf (`fixLeafAV`), the
rule's binder data as domains (`fixRuleDataAV_map_dom`), and **the
rule law** at the recursor's cons (`fixRecRuleLaw`): the sum route's
`sumRecRuleLaw` with the rule read at the cons (`fixRuleData_of`),
its gradedness from the model (`fixRuleOk`, supplied), and the
recursor's iota (`fixRecLawCore`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory Ix.Kernel.SetTheory.Tower
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  NativeParts RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env md}

/-! ## The semantic data of a block -/

/-- The constructors' field lists. -/
@[expose] def fssOfR (nP : Nat) (cds : List (CtorDatumR md)) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The constructors' index readings. -/
@[expose] def essOfR (cds : List (CtorDatumR md)) : List (List AnnotTerm) := cds.map fun cd => cd.2.2.2.1

/-- The constructors' per-field index expressions. -/
@[expose] def eissOfR (cds : List (CtorDatumR md)) : List (List (List AnnotTerm)) := cds.map fun cd => cd.2.2.2.2.2.1

/-- The per-constructor telescopes (task #202). -/
@[expose] def tlssOfR (cds : List (CtorDatumR md)) : List (List (List (Nat × Nat × AnnotTerm))) :=
  cds.map fun cd => cd.2.2.2.2.2.2

/-- The recursive flags of the first `n` constructors. -/
@[expose] def rssOfK (ksF : Nat → List RecFieldKind) (n : Nat) : List (List Bool) :=
  (List.range n).map fun j => rsOf (ksF j)

omit [SetTheory V] in
theorem fssOfR_getElem? (nP : Nat) (cds : List (CtorDatumR md)) (j : Nat) :
    (fssOfR nP cds)[j]? = (cds[j]?).map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_getElem? (cds : List (CtorDatumR md)) (j : Nat) :
    (essOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.1 := by simp [essOfR]

omit [SetTheory V] in
theorem eissOfR_getElem? (cds : List (CtorDatumR md)) (j : Nat) :
    (eissOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.2.2.1 := by simp [eissOfR]

theorem tlssOfR_getElem? (cds : List (CtorDatumR md)) (j : Nat) :
    (tlssOfR cds)[j]? = (cds[j]?).map fun cd => cd.2.2.2.2.2.2 := by simp [tlssOfR]

theorem tlssOfR_length (cds : List (CtorDatumR md)) : (tlssOfR cds).length = cds.length := by
  simp [tlssOfR]

omit [SetTheory V] in
theorem fssOfR_length (nP : Nat) (cds : List (CtorDatumR md)) : (fssOfR nP cds).length = cds.length := by
  simp [fssOfR]

omit [SetTheory V] in
theorem essOfR_length (cds : List (CtorDatumR md)) : (essOfR cds).length = cds.length := by simp [essOfR]

omit [SetTheory V] in
theorem eissOfR_length (cds : List (CtorDatumR md)) : (eissOfR cds).length = cds.length := by
  simp [eissOfR]

omit [SetTheory V] in
theorem rssOfK_getD {ksF : Nat → List RecFieldKind} {n j : Nat} (hj : j < n) :
    (rssOfK ksF n).getD j [] = rsOf (ksF j) := by
  simp [rssOfK, List.getD_eq_getElem?_getD, List.getElem?_range hj]

/-! ## The rule's binder data as domains -/

theorem fixRuleDataAV_map_dom {m : EnvModel V env} {T : Key md} {ψ : LevelParam → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List (CtorDatumR md)}
    {ds : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP) (hlenI : ips.length = nIdx) :
    (fixRuleDataAV m T ψ nP nIdx ℓ pps ips cds ds).map (·.2)
      = ((fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).take (nP + 1 + cds.length)).map (·.2.2) ++
        (liftDoms (cds.length + 1) 0 (ds.drop nP)).map (·.2.2) := by
  have hlenX : (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
      [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
      fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1).length = nP + 1 + cds.length := by
    simp only [List.length_append, rebit_length, hlenP, List.length_singleton, fixMinorsData_length]
  generalize hX : rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
      [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
      fixMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 = X at hlenX
  have hlenXD : (X ++ rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips)).length
      = nP + 1 + cds.length + nIdx := by
    rw [List.length_append, hlenX, rebit_length, liftDoms_length, hlenI]
  unfold fixRuleDataAV fixRecDataAV
  rw [hX, List.take_append_of_le_length (by omega :
      nP + 1 + cds.length ≤ (X ++ rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips)).length),
    List.take_append_of_le_length (by omega : nP + 1 + cds.length ≤ X.length),
    List.take_of_length_le (by omega : X.length ≤ nP + 1 + cds.length)]
  simp only [List.map_append, List.map_map, rebit]
  rfl

/-! ## The recursor leaf -/

/-- The restriction of an assignment to a level-parameter list. -/
@[expose] def restrictΨ (lps : List LevelParam) (ψ : LevelParam → Nat) : LevelParam → Nat :=
  fun q => if q ∈ lps then ψ q else 0

omit [SetTheory V] in
theorem restrictΨ_agree (lps : List LevelParam) (ψ : LevelParam → Nat) :
    ∀ q ∈ lps, restrictΨ lps ψ q = ψ q := by
  intro q hq
  simp [restrictΨ, hq]

omit [SetTheory V] in
theorem restrictΨ_congr {lps : List LevelParam} {ψ₁ ψ₂ : LevelParam → Nat}
    (h : ∀ q ∈ lps, ψ₁ q = ψ₂ q) : restrictΨ lps ψ₁ = restrictΨ lps ψ₂ := by
  funext q
  unfold restrictΨ
  split
  · next hq => exact h q hq
  · rfl

/-- The recursor leaf's sort: the kernel's inferred sort at the
restricted assignment, floored at one at a nonzero elimination level,
zero at a zero one. -/
@[expose] def fixSortAV (elimL : Level) (u : Level) (lps : List LevelParam) (ψ : LevelParam → Nat) : Nat :=
  if elimL.eval ψ = 0 then 0 else max 1 (u.eval (restrictΨ lps ψ))

omit [SetTheory V] in
theorem fixSortAV_zero_iff (elimL u : Level) (lps : List LevelParam) (ψ : LevelParam → Nat) :
    fixSortAV elimL u lps ψ = 0 ↔ elimL.eval ψ = 0 := by
  unfold fixSortAV
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h =>
    exact ⟨fun h' => absurd h' (by have := Nat.le_max_left 1 (u.eval (restrictΨ lps ψ)); omega),
      fun h' => absurd h' h⟩


/-! ## The data at the parameters -/

theorem fixRecDataAV_take_nP {m : EnvModel V env} {T : Key md} {ψ : LevelParam → Nat} {nP nIdx : Nat}
    {ℓ : Level} {pps ips : List (Nat × Nat × AnnotTerm)} {cds : List (CtorDatumR md)}
    (hlenP : pps.length = nP) :
    ((fixRecDataAV m T ψ nP nIdx ℓ pps ips cds).take nP).map (·.2.2) = pps.map (·.2.2) := by
  unfold fixRecDataAV
  rw [List.take_append_of_le_length (by simp [hlenP]),
    List.take_append_of_le_length (by simp [hlenP]),
    List.take_append_of_le_length (by simp [hlenP]),
    List.take_append_of_le_length (by simp [hlenP]),
    List.take_of_length_le (by simp [hlenP]), rebit_map_dom]

omit [SetTheory V] in
/-- The constructor data at two assignments agreeing on the data. -/
theorem fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF₁ esF₂ : Nat → (LevelParam → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF₁ tssF₂ : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ₁ ψ₂ : LevelParam → Nat} :
    ∀ (cs : List (ConstantVal md × Nat)) (j : Nat),
      (∀ i, i < cs.length → dsF₁ (j + i) ψ₁ = dsF₂ (j + i) ψ₂ ∧ esF₁ (j + i) ψ₁ = esF₂ (j + i) ψ₂ ∧
        eissF₁ (j + i) ψ₁ = eissF₂ (j + i) ψ₂ ∧ tssF₁ (j + i) ψ₁ = tssF₂ (j + i) ψ₂) →
      fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ₁ cs j = fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ₂ cs j
  | [], _, _ => rfl
  | c :: cs, j, h => by
    simp only [fixCtorDataList]
    obtain ⟨h1, h2, h3, h4⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h1 h2 h3 h4
    rw [h1, h2, h3, h4, fixCtorDataList_congr cs (j + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      rwa [show j + (i + 1) = j + 1 + i from by omega] at this]

/-! ## The rule law -/

set_option maxHeartbeats 6400000 in
/-- **The recursive recursor rule's law** at the recursor's cons. -/
theorem fixRecRuleLaw (mp : EnvModelM V μ env)
    {J : Judgements md} {p : NativeParts md} {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hRec : NativeRecRunJ J env p cvTa ctorsA cvRa rhss)
    {caps : IndCaps md} {cvS : ConstantVal md}
    (hfT : env.find? p.cvT.name = some (.indInfo cvS caps))
    (hlpsS : cvS.levelParams = p.cvT.levelParams)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {bsT : List (Expr md × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {tfvs : List (Expr md)} {trest : Expr md}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env md} {idxF : Nat → List (Expr md)} {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List (Expr md)} {xrestF : Nat → Expr md}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF i cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    (hRD : SumRecData mp.base2 cvRa p.nP ctorsA.length p.nIdx (Ix.Kernel.structElimLevel p.elim p.large)
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA))
    -- the leaf and its facts
    {A : (LevelParam → Nat) → AnnotTerm} {sAV : (LevelParam → Nat) → Nat} {uAV : (LevelParam → Nat) → Nat}
    {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    (hA : ∀ ψ, A ψ = nativeRecAVI ((Ix.Kernel.structElimLevel p.elim p.large).eval ψ) (p.resSort.eval ψ)
      p.nP (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (((ppsAll ψ).drop p.nP).map (·.2.2))
      (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ) (sAV ψ))
    (hpre : ∀ ψ, FixPre V ((Ix.Kernel.structElimLevel p.elim p.large).eval ψ) (p.resSort.eval ψ) (uAV ψ)
      p.nP (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssZ ψ)
      (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ) (sAV ψ))
    (hAcl : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase)
    (hokFssH : ∀ (ψ : LevelParam → Nat) (ρp : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      SumFieldsOkB (p.resSort.eval ψ) ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = sumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))))
    -- a constructor's parameter domains and the former's are the same
    -- `Sat`, so the law needs no comparison of the two parameter spines
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    -- the subsingleton criterion at the former's parameter frame
    (hsrcH : ∀ ψ : LevelParam → Nat, p.resSort.eval ψ = 0 →
      (Ix.Kernel.structElimLevel p.elim p.large).eval ψ ≠ 0 → ∀ ρp : Nat → V,
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      ∀ k, k < ctorsA.length →
      ∀ i, i < ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD k []).length →
      srcOfEs ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD k [])
        ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD k []).length i = none →
      ∀ fs : List V,
        SpineFit ρp (((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD k []).take i) fs →
        interp V (consList fs ρp)
            (((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD k []).getD i default)
          ∈ˢ (univZero : V))
    -- the rule
    {j : Nat} {cA : ConstantVal md × Nat} (hj : ctorsA[j]? = some cA) {rhs : Expr md}
    (hrhs : rhss[j]? = some rhs)
    (hRuleOk : ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx
          (Ix.Kernel.structElimLevel p.elim p.large) ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) (dsF j ψ))
        (fixRuleCoreAV (pwBit ψ (Level.zeronessOf (Ix.Kernel.structElimLevel p.elim p.large))) (A ψ) p.nP
          cA.2 ctorsA.length j (Ix.Kernel.recIdxOf (ksF j)) (tssF j ψ) (eissF j ψ))))
    (hfresh : env.find? cvRa.name = none)
    {rule : RecRule md} {kb eb : Bool}
    (hrule : rule = ⟨cA.1.name, cA.2, p.nP, .plain, rhs, kb, eb, true⟩)
    {rules : List (RecRule md)}
    (m₂ : EnvModel V ⟨.recInfo cvRa mI rP rules :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name A)
    (φ : LevelParam → Nat) :
    RecRuleLaw m₂ φ cvRa.name cvRa mI rP rule := by
  subst hrule
  obtain ⟨hfC, hlpsC, hD⟩ := hcf j cA hj
  have hCD := hD.toCtorDataI
  have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  -- the constructor's stored type
  obtain ⟨-, -, hCres, -, -⟩ := mp.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCres
  have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ hCres
  have hRC : cA.1.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfC; exact nomatch hfC
  have hRT : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  have hcbT : ConstsBound env cvRa.type := by
    obtain ⟨-, -, cvRi, recTy, -, -, -, htrR, -, -, -, -, hcvRa⟩ :=
      id hRec
    have hcvRa : cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := hcvRa
    have : cvRa.type = recTy := by rw [hcvRa]
    rw [this]
    exact constsBound_of_constsResolve _ htrR
  -- the cons crossing
  have hcross : ∀ e : Expr md, ConsCrossAt (.recInfo cvRa mI rP rules) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hfindC : (⟨.recInfo cvRa mI rP rules :: env.consts⟩ : Env md).find? cA.1.name
      = some (.ctorInfo cA.1 p.nP cA.2) := by
    rw [Ix.Kernel.Env.find?_cons, if_neg (fun h => hRC h.symm)]
    exact hfC
  -- the readings at `m₂` are the readings at `mp`
  have hTac : ∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ := by
    intro ψ; rw [hac, acvalWith_ne hRT]
  have hCac : ∀ ψ, ∀ cd ∈ fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0,
      m₂.acval cd.1 ψ = mp.base2.acval cd.1 ψ := by
    intro ψ cd hcd
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcd
    rw [fixCtorDataList_getElem?, Nat.zero_add] at hi
    cases hA' : ctorsA[i]? with
    | none => rw [hA'] at hi; exact nomatch hi
    | some cAi =>
      rw [hA'] at hi
      obtain rfl := Option.some.inj hi
      obtain ⟨hfi, -, -⟩ := hcf i cAi hA'
      have hne : cAi.1.name ≠ cvRa.name := by
        intro h; rw [h, hfresh] at hfi; exact nomatch hfi
      show m₂.acval cAi.1.name ψ = _
      rw [hac, acvalWith_ne hne]
  -- the law
  refine ⟨by omega, fun us hus => ?_⟩
  dsimp only
  have hinstR : ∀ (d : Nat) (e : Expr md),
      denoteMeta m₂.acval _ φ d (e.instantiateLevelParams cvRa.levelParams us)
        = denoteMeta m₂.acval _ (Level.substFn φ cvRa.levelParams us) d e :=
    fun d e => denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ d e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  -- the right-hand side's reading, at the extension
  obtain ⟨rhs', hrhs', -, -, -, hread⟩ := fixRuleData_of mp hRec hfT hlpsS hstripT hopT hFD hlenK hks
    hcf (mI := mI) (rP := rP) (rules := rules) hfresh hRT m₂ hac hj
  obtain rfl := Option.some.inj (hrhs.symm.trans hrhs')
  have hRa₂ : denoteMeta m₂.acval ⟨.recInfo cvRa mI rP rules :: env.consts⟩ φ 0
      (rhs.instantiateLevelParams cvRa.levelParams us)
      = some (mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx
          (Ix.Kernel.structElimLevel p.elim p.large) ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0) (dsF j ψR))
        (fixRuleCoreAV (pwBit ψR (Level.zeronessOf (Ix.Kernel.structElimLevel p.elim p.large))) (A ψR) p.nP
          cA.2 ctorsA.length j (Ix.Kernel.recIdxOf (ksF j)) (tssF j ψR) (eissF j ψR))) := by
    rw [hinstR, hread ψR, fixRuleDataAV_congr (hTac ψR) (hCac ψR)]
  refine ⟨_, hRa₂, hRuleOk ψR, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ _ _ hidx hTVa
    hTVja hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfindC.symm.trans hfcj))
  -- the level assignments
  have hagree : ∀ q ∈ p.cvT.levelParams,
      Level.substFn φ cA.1.levelParams usj q = ψR q := by
    have h := hψ
    simp only [Ix.Kernel.recFireComparands] at h
    rw [hlpsC] at h
    rw [hlpsC, ← hψR]
    exact substFn_agree_of_comparand h
  generalize hψC : Level.substFn φ cA.1.levelParams usj = ψC at hagree hTVja hfitR hfitC ⊢
  have hdsEq : ∀ i, i < ctorsA.length →
      dsF i ψC = dsF i ψR ∧ esF i ψC = esF i ψR ∧ eissF i ψC = eissF i ψR ∧
        tssF i ψC = tssF i ψR := by
    intro i hi
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨-, hlpsi, hDi⟩ := hcf i cAi hi'
    exact ⟨(hDi.params ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))).1,
      (hDi.params ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))).2,
      hDi.eissParams ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq)),
      hDi.tssParams ψC ψR (fun q hq => hagree q (by rw [← hlpsi]; exact hq))⟩
  have hcdsEq : fixCtorDataList dsF esF ksF eissF tssF ψC ctorsA 0
      = fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0 :=
    fixCtorDataList_congr ctorsA 0 fun i hi => by rw [Nat.zero_add]; exact hdsEq i hi
  have hdsjEq : dsF j ψC = dsF j ψR := (hdsEq j hjn).1
  have hesjEq : esF j ψC = esF j ψR := (hdsEq j hjn).2.1
  have hwEq : p.resSort.eval ψC = p.resSort.eval ψR :=
    (hFD.params ψC ψR (fun q hq => hagree q (by rw [← hlpsT]; exact hq))).2
  -- the recursor and constructor types' readings, at the extension
  have hRD₂ := hRD.cross (c₀ := .recInfo cvRa mI rP rules) hfresh (hcross _) hcbT m₂ hac
  have hCD₂ := hCD.cross (c₀ := .recInfo cvRa mI rP rules) hfresh hRT hcross hcbC
    (fun e he => constsBound_of_constsResolve _ (hidxRes j cA hj e he)) m₂ hac
  have hTVa' : TVa = mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψR)
      (recConcAV ctorsA.length p.nIdx) := by
    have h := hTVa
    rw [hinstR] at h
    exact Option.some.inj (h.symm.trans (hRD₂.read ψR))
  have hTVja' : TVja = mkPisAV (dsF j ψR) (ctorBodyAVI m₂ p.cvT.name p.nP cA.2 ψC (esF j ψR)) := by
    have h := hTVja
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m₂) φ 0 cA.1.type, hψC] at h
    have := Option.some.inj (h.symm.trans (hCD₂.read ψC))
    rw [this, hdsjEq, hesjEq]
  -- the constructor's leaf at the extension
  have hleafC₂ : m₂.acval cA.1.name ψC
      = sumMkAV (p.resSort.eval ψR) j (dsF j ψR) (((dsF j ψR).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0))) := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cA.1.name ψC = _
    rw [acvalWith_ne hRC, hleafC j cA hj ψC, hdsjEq, hwEq, hcdsEq]
  have hleafR₂ : m₂.acval cvRa.name ψR = A ψR := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cvRa.name ψR = _
    rw [acvalWith_self]
  -- the fits, as spines
  have hspR : SpineFit ρ ((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψR).map (·.2.2))
      ((xs ++ [AnnotTerm.mkAppN (sumMkAV (p.resSort.eval ψR) j (dsF j ψR)
        (((dsF j ψR).drop p.nP).map (·.2.2))
        (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)))) ys]).map
        (interp V ρ)) := by
    have hst := stripPisAV_mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψR)
      (recConcAV ctorsA.length p.nIdx)
    rw [hRD.len ψR] at hst
    have htele := piTeleAV_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    rw [hleafC₂] at hfit
    have hchain := teleFitPA_to_chain (p.nP + ctorsA.length + p.nIdx + 2) htele
      (by simp [hxl, hmI]; omega) hfit
    refine spineFit_of_chain (by simp [hxl, hRD.len ψR, hmI]; omega) ?_
    intro n hn
    have := hchain n (by simpa [hRD.len ψR] using hn)
    simpa [hRD.len ψR] using this
  have hstC := stripPisAV_mkPisAV (dsF j ψR) (ctorBodyAVI m₂ p.cvT.name p.nP cA.2 ψC (esF j ψR))
  rw [hCD.len ψR] at hstC
  have hteleC := piTeleAV_of_stripPisAV hstC
  have hspC : SpineFit ρ ((dsF j ψR).map (·.2.2)) (ys.map (interp V ρ)) := by
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (p.nP + cA.2) hteleC (by simpa using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hCD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hCD.len ψR] using hn)
    simpa [hCD.len ψR] using this
  -- the index pin: the constructor's index values at the fields are the
  -- application's index arguments
  have hpin : ∀ i, i < p.nIdx →
      interp V (consList (ys.map (interp V ρ)) ρ) ((esF j ψR).getD i default)
        = interp V ρ (xs.getD (p.nP + 1 + ctorsA.length + i) default) := by
    intro i hi
    obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcarInterp⟩ := hidx
    rcases hcarLen with hcase | hcarLen
    · omega
    have hrest : restC = Ix.Kernel.Model.AnnotTerm.instSeq ys (p.nP + cA.2 - 1)
        (ctorBodyAVI m₂ p.cvT.name p.nP cA.2 ψC (esF j ψR)) := by
      have hfit := hfitC
      rw [hTVja'] at hfit
      exact teleFitPA_rest_eq (p.nP + cA.2) hteleC (by simpa using hyl) hfit
    have hrest2 : AnnotTerm.mkAppN Ha cargsa
        = AnnotTerm.mkAppN (Ix.Kernel.Model.AnnotTerm.instSeq ys (p.nP + cA.2 - 1) (m₂.acval p.cvT.name ψC))
            ((paramBvars p.nP cA.2 ++ esF j ψR).map (Ix.Kernel.Model.AnnotTerm.instSeq ys (p.nP + cA.2 - 1))) := by
      rw [← hrestEq, hrest]
      unfold ctorBodyAVI
      rw [instSeqAV_mkAppN]
    have hlenE := hCD.lenE ψR
    obtain ⟨-, hcargs⟩ := AnnotTerm.mkAppN_inj hrest2
      (by simp [hcarLen, paramBvars, hlenE]; omega)
    have hcel : cargsa.getD (p.nP + i) default
        = Ix.Kernel.Model.AnnotTerm.instSeq ys (p.nP + cA.2 - 1) ((esF j ψR).getD i default) := by
      have h1 := congrArg (fun l => l[p.nP + i]?) hcargs
      simp only [List.getElem?_map, List.getElem?_append_right (show (paramBvars p.nP cA.2).length ≤ p.nP + i
        by simp [paramBvars]), show (paramBvars p.nP cA.2).length = p.nP by simp [paramBvars],
        Nat.add_sub_cancel_left] at h1
      rw [List.getD_eq_getElem?_getD, h1, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some, Option.getD_some]
    have hcar := hcarInterp i (by omega)
    rw [hcel, show p.nP + cA.2 - 1 = ys.length - 1 from by rw [hyl], interp_instSeq, hrP] at hcar
    rw [← hcar]
    unfold chain
    rw [consN_eq_consList]
  -- the law's two halves
  have hlenCds : (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0).length = ctorsA.length :=
    fixCtorDataList_length _ _ _ _ _ _ _ _
  have hjd : (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)[j]?
      = some (cA.1.name, cA.2, dsF j ψR, esF j ψR, Ix.Kernel.recIdxOf (ksF j), eissF j ψR, tssF j ψR) := by
    rw [fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl
  have hFsj : (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0))[j]?
      = some (((dsF j ψR).drop p.nP).map (·.2.2)) := by
    rw [fssOfR_getElem?, hjd]; rfl
  have hEsj : (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0))[j]? = some (esF j ψR) := by
    rw [essOfR_getElem?, hjd]; rfl
  have hEisj : (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD j [] = eissF j ψR := by
    rw [List.getD_eq_getElem?_getD, eissOfR_getElem?, hjd]; rfl
  have hTlsj : (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD j [] = tssF j ψR := by
    rw [List.getD_eq_getElem?_getD, tlssOfR_getElem?, hjd]; rfl
  have hrssj : (rssOfK ksF ctorsA.length).getD j [] = rsOf (ksF j) := rssOfK_getD hjn
  have hlenPps : ((ppsAll ψR).take p.nP).length = p.nP := by
    rw [List.length_take, hFD.len ψR]; omega
  have hlenIps : ((ppsAll ψR).drop p.nP).length = p.nIdx := by
    rw [List.length_drop, hFD.len ψR]; omega
  have hokFss : ∀ ρp : Nat → V,
      Sat V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψR).take p.nP).map (·.2.2)).reverse) ρp →
      SumFieldsOkB (p.resSort.eval ψR) ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)) := by
    intro ρp hρ
    unfold fixRdsAV at hρ
    rw [fixRecDataAV_take_nP hlenPps] at hρ
    exact hokFssH ψR ρp hρ
  -- the two parameter frames coincide, so the law compares neither
  -- spine with the other
  have hsatIffR : ∀ ρp : Nat → V,
      Sat V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψR).take p.nP).map (·.2.2)).reverse) ρp ↔
        Sat V ((((dsF j ψR).take p.nP).map (·.2.2)).reverse) ρp := by
    intro ρp
    unfold fixRdsAV
    rw [fixRecDataAV_take_nP hlenPps]
    exact hiff j cA hj ψR ρp
  have hsrcR : p.resSort.eval ψR = 0 →
      (Ix.Kernel.structElimLevel p.elim p.large).eval ψR ≠ 0 → ∀ ρp : Nat → V,
      Sat V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψR).take p.nP).map (·.2.2)).reverse) ρp →
      ∀ i, i < ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD 0 []).length →
      srcOfEs ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD 0 [])
        ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD 0 []).length i = none →
      ∀ fs : List V,
        SpineFit ρp (((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD 0 []).take i) fs →
        interp V (consList fs ρp)
            (((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)).getD 0 []).getD i default)
          ∈ˢ (univZero : V) := by
    intro hw0 hl0 ρp hρ
    unfold fixRdsAV at hρ
    rw [fixRecDataAV_take_nP hlenPps] at hρ
    exact hsrcH ψR hw0 hl0 ρp hρ 0 (by omega)
  -- every rule binder carries the elimination level's bit
  have hldsBits : ∀ d ∈ fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx
      (Ix.Kernel.structElimLevel p.elim p.large) ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP)
      (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0) (dsF j ψR),
      d.1 = pwBit ψR (Level.zeronessOf (Ix.Kernel.structElimLevel p.elim p.large)) :=
    fun _ hd => mem_fixRuleDataAV hd
  have hbzR : (Ix.Kernel.structElimLevel p.elim p.large).eval ψR = 0 ↔
      pwBit ψR (Level.zeronessOf (Ix.Kernel.structElimLevel p.elim p.large)) = 0 := by
    rw [pwBit_eq_zero_iff, Ix.Kernel.PropWhen.zeronessOf_sound, beq_iff_eq]
  have hcore := fixRecLawCore hbzR (hpre ψR) (n := ctorsA.length) (nF := cA.2) (nIdx := p.nIdx) (j := j)
    (by rw [fssOfR_length, hlenCds]) (by rw [List.length_map, hlenIps]) (hCD.len ψR) hjn hFsj hEsj
    (hCD.lenE ψR) (R := A ψR) (by rw [hA ψR]) (hAcl ψR) hokFss hsatIffR hsrcR
    (lds := fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx (Ix.Kernel.structElimLevel p.elim p.large)
      ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP) (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0)
      (dsF j ψR))
    (by rw [fixRuleDataAV_map_dom hlenPps hlenIps, hlenCds]; rfl) hldsBits
    (Ra := mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψR p.nP p.nIdx
        (Ix.Kernel.structElimLevel p.elim p.large) ((ppsAll ψR).take p.nP) ((ppsAll ψR).drop p.nP)
        (fixCtorDataList dsF esF ksF eissF tssF ψR ctorsA 0) (dsF j ψR))
      (fixRuleCoreAV (pwBit ψR (Level.zeronessOf (Ix.Kernel.structElimLevel p.elim p.large))) (A ψR) p.nP
        cA.2 ctorsA.length j (Ix.Kernel.recIdxOf (ksF j)) (tssF j ψR) (eissF j ψR)))
    (by rw [hEisj, hTlsj, hrssj, ← recIdx_rsOf, hD.ksLen]) (hRuleOk ψR) (by rw [hxl, hmI])
    (by simpa using hyl) hspR hspC hpin
  try simp only [RecRule.ctor, RecRule.ctorParams] at hcore ⊢
  rw [hleafR₂, hleafC₂, hrP]
  exact hcore


/-! ## The subsingleton criterion at a field (task #202 A2) -/

/-- An unsourced field of a source-bounded chain is a truth value at
every fitting prefix spine. -/
theorem fieldsBoundSrc_at {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {srcs : List (Option Nat)} {i : Nat} {fs : List V},
      FieldsBoundSrc ρ Fs srcs → srcs[i]? = some none → SpineFit ρ (Fs.take i) fs → i < Fs.length →
      interp V (consList fs ρ) (Fs.getD i default) ∈ˢ (univ 0 : V)
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, hs, _, _ => by simp at hs
  | F :: Fs, s :: srcs, 0, fs, hb, hs, hsp, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    cases fs with
    | nil => exact hb.1 hs
    | cons a fs' => exact hsp.elim
  | F :: Fs, s :: srcs, i + 1, fs, hb, hs, hsp, hi => by
    cases fs with
    | nil => exact hsp.elim
    | cons a fs' =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons, List.getD_cons_succ]
      exact fieldsBoundSrc_at (hb.2 a ha) (by simpa using hs) hsp' (by simpa using hi)

/-! ## The stage -/

/-- The recursor leaf of a recursive block at an assignment. -/
@[expose] def fixLeafAV {env : Env md} (m : EnvModel V env) (p : NativeParts md)
    (ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm))
    (dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (LevelParam → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm))
    (tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))) (ctorsA : List (ConstantVal md × Nat))
    (sAV : (LevelParam → Nat) → Nat) (ψ : LevelParam → Nat) : AnnotTerm :=
  nativeRecAVI ((Ix.Kernel.structElimLevel p.elim p.large).eval ψ) (p.resSort.eval ψ) p.nP
    (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
    (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (((ppsAll ψ).drop p.nP).map (·.2.2))
    (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
    (fixRdsAV m p ppsAll dsF esF ksF eissF tssF ctorsA ψ) (sAV ψ)

private theorem WellDenoted_mkPisAV_of {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      DomsWalk σ gds →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → WellDenoted V (consList as σ) R) →
      WellDenoted V σ (mkPisAV gds R)
  | [], _, _, hR => by simpa [mkPisAV, consList] using hR [] trivial
  | _ :: _, _, ⟨hd, hrest⟩, hR => by
    simp only [mkPisAV, WellDenoted_pi]
    refine ⟨hd, fun x hx => WellDenoted_mkPisAV_of (hrest x hx) fun as hsp => ?_⟩
    have := hR (x :: as) ⟨hx, hsp⟩
    rwa [consList_cons] at this

omit [SetTheory V] in
private theorem mkPisAV_append' (xs ys : List (Nat × Nat × AnnotTerm)) (R : AnnotTerm) :
    mkPisAV (xs ++ ys) R = mkPisAV xs (mkPisAV ys R) := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [mkPisAV, ih]

private theorem fieldsOkB_append_inv {w : Nat} :
    ∀ {xs ys : List AnnotTerm} {σ : Nat → V},
      FieldsOkB w σ (xs ++ ys) →
      FieldsOkB w σ xs ∧ ∀ as, SpineFit σ xs as → FieldsOkB w (consList as σ) ys
  | [], _, _, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [consList] using h
      | cons _ _ => exact hsp.elim⟩
  | _ :: _, _, _, ⟨hw, h0, hrest⟩ =>
    ⟨⟨hw, h0, fun a ha => (fieldsOkB_append_inv (hrest a ha)).1⟩, fun as hsp => by
      cases as with
      | nil => exact hsp.elim
      | cons a as =>
        rw [consList_cons]
        exact (fieldsOkB_append_inv (hrest a hsp.1)).2 as hsp.2⟩

private theorem fieldsValid_append_inv :
    ∀ {xs ys : List AnnotTerm} {σ : Nat → V},
      FieldsValid σ (xs ++ ys) →
      FieldsValid σ xs ∧ ∀ as, SpineFit σ xs as → FieldsValid (consList as σ) ys
  | [], _, _, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [consList] using h
      | cons _ _ => exact hsp.elim⟩
  | _ :: _, _, _, ⟨hv, hrest⟩ =>
    ⟨⟨hv, fun a ha => (fieldsValid_append_inv (hrest a ha)).1⟩, fun as hsp => by
      cases as with
      | nil => exact hsp.elim
      | cons a as =>
        rw [consList_cons]
        exact (fieldsValid_append_inv (hrest a hsp.1)).2 as hsp.2⟩

private theorem fieldsValid_append :
    ∀ {xs ys : List AnnotTerm} {σ : Nat → V},
      FieldsValid σ xs →
      (∀ as, SpineFit σ xs as → FieldsValid (consList as σ) ys) →
      FieldsValid σ (xs ++ ys)
  | [], _, _, _, hys => by simpa [consList] using hys [] trivial
  | _ :: _, _, _, ⟨hv, hxs⟩, hys => by
    refine ⟨hv, fun a ha => fieldsValid_append (hxs a ha) fun as hsp => ?_⟩
    have := hys (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

private theorem fieldsValid_liftDoms {n : Nat} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat) (σ : Nat → V),
      FieldsValid (shiftE n k σ) (ds.map (·.2.2)) →
      FieldsValid σ ((liftDoms n k ds).map (·.2.2))
  | [], _, _, _ => trivial
  | d :: ds, k, σ, ⟨hv, hrest⟩ => by
    refine ⟨?_, fun a ha => ?_⟩
    · show AnnotValid V σ (d.2.2.liftN n k)
      rw [AnnotValid_liftN]; exact hv
    · have ha' : a ∈ˢ interp V (shiftE n k σ) d.2.2 := by
        rwa [show interp V σ (d.2.2.liftN n k) = interp V (shiftE n k σ) d.2.2 from
          interp_liftN V n d.2.2 k σ] at ha
      refine fieldsValid_liftDoms ds (k + 1) (cons a σ) ?_
      rw [shiftE_succ_cons']
      exact hrest a ha'

omit [SetTheory V] in
private theorem ihTeleAtGo_rebit_map_dom (nF o i l b : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      (ihTeleAtGo nF o i l k (rebit b tl)).map (·.2.2) = (ihTeleAtGo nF o i l k tl).map (·.2.2)
  | _, [] => rfl
  | k, _ :: tl => by simp only [rebit_cons, ihTeleAtGo, List.map_cons, ihTeleAtGo_rebit_map_dom nF o i l b (k + 1) tl]

omit [SetTheory V] in
private theorem map_pair_dom (w : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (ds.map fun d => (w, d.2.2)).map (·.2) = ds.map (·.2.2) := by
  induction ds with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

private theorem famSpine_wellDenotedV (mp : EnvModelM V μ env) {T : Key md} {ψ : LevelParam → Nat}
    {nP nIdx D w : Nat} {pps ips ppsAll : List (Nat × Nat × AnnotTerm)}
    (hppsAll : ppsAll = pps ++ ips) (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hleafT : ∃ B, mp.base2.acval T ψ = mkLamsAV (ppsAll.map fun d => (w, d.2.2)) B)
    {extras is : List V} (hspI : SpineFit ρp (ips.map (·.2.2)) is)
    (hD : D = nP + extras.length + nIdx) :
    WellDenotedV V (consList is (consList extras ρp))
      (AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP D ++ fieldBvars nIdx)) := by
  obtain ⟨B, hB⟩ := hleafT
  let σ : Nat → V := consList is (consList extras ρp)
  let ρ' : Nat → V := fun k => ρp (k + nP)
  have hlenIs : is.length = nIdx := by rw [hspI.length_eq, List.length_map, hlenI]
  have hσ : ∀ k, σ (k + (extras.length + nIdx)) = ρp k := fun k => by
    dsimp only [σ]
    rw [show k + (extras.length + nIdx) = (k + extras.length) + is.length from by omega,
      consList_apply_add, consList_apply_add]
  have hargs : ∀ a ∈ paramBvarsAt nP D ++ fieldBvars nIdx, WellDenotedV V σ a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; exact ⟨trivial, trivial⟩
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; exact ⟨trivial, trivial⟩
  have hokL : WellDenoted V ρ' (mkLamsAV (ppsAll.map fun d => (w, d.2.2)) B) := by
    rw [← hB]; exact mp.base2.acval_wellDenoted T ψ ρ'
  have hval : interp V σ (mp.base2.acval T ψ) = (pt : V) ∨
      interp V σ (mp.base2.acval T ψ) = interp V ρ' (mkLamsAV (ppsAll.map fun d => (w, d.2.2)) B) := by
    right; rw [← hB]; exact interp_closed (V := V) (mp.base2.cval_closedL T ψ) σ ρ'
  have hlenP' : (pps.map (·.2.2)).length = nP := by rw [List.length_map, hlenP]
  have hsp₁ := spineFit_of_sat (Δ₀ := []) (Ds := pps.map (·.2.2))
    (by rw [List.append_nil]; exact hsatP)
  rw [hlenP'] at hsp₁
  refine mkAppN_wellDenotedV_of_lam ⟨mp.base2.acval_wellDenoted T ψ σ, mp.acval_validV T ψ σ⟩
    hargs hokL hval ?_
  rw [map_pair_dom,
    hppsAll, List.map_append, List.map_append, hD,
    show nP + extras.length + nIdx = nP + (extras.length + nIdx) from by omega,
    map_paramBvarsAt_interp hσ,
    show fieldBvars nIdx = (List.range nIdx).map (fun k => AnnotTerm.bvar (nIdx - 1 - k)) from rfl,
    map_fieldBvars_interp hlenIs]
  exact SpineFit.append hsp₁ (by rwa [consList_range_reverse])

private theorem motiveAVI_wellDenotedV (mp : EnvModelM V μ env) {T : Key md} {ψ : LevelParam → Nat}
    {nP nIdx w : Nat} {elimL : Level} {pps ips ppsAll : List (Nat × Nat × AnnotTerm)}
    (hppsAll : ppsAll = pps ++ ips) (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hleafT : ∃ B, mp.base2.acval T ψ = mkLamsAV (ppsAll.map fun d => (w, d.2.2)) B)
    (hIpsOk : FieldsOkB 0 ρp (ips.map (·.2.2)))
    (hIpsVal : FieldsValid ρp (ips.map (·.2.2))) :
    WellDenotedV V ρp (motiveAVI mp.base2 T ψ nP nIdx elimL ips) := by
  let domT := AnnotTerm.mkAppN (mp.base2.acval T ψ) (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx)
  let mds := rebit (pwBit ψ Ix.Kernel.PropWhen.never) ips ++ [(0, pwBit ψ Ix.Kernel.PropWhen.never, domT)]
  have hmEq : motiveAVI mp.base2 T ψ nP nIdx elimL ips = mkPisAV mds (.sort (elimL.eval ψ)) := by
    unfold motiveAVI; rw [mkPisAV_append']; rfl
  rw [hmEq]
  have hfam : ∀ is', SpineFit ρp (ips.map (·.2.2)) is' → WellDenotedV V (consList is' ρp) domT := by
    intro is' hspI
    have := famSpine_wellDenotedV (D := nP + nIdx) mp hppsAll hlenP hlenI hsatP hleafT (extras := []) hspI (by simp)
    rwa [consList_nil] at this
  refine ⟨WellDenoted_mkPisAV_of ?_ (fun _ _ => trivial),
    AnnotValid_mkPisAV_of (w := 1) ?_ ?_ (fun _ _ => trivial) (fun h => nomatch h)⟩
  · refine domsWalk_append (domsWalk_rebit _ (domsWalk_of_fieldsOkB hIpsOk)) fun is' hspI => ?_
    rw [rebit_map_dom] at hspI
    exact ⟨(hfam is' hspI).1, fun _ _ => trivial⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · rw [mem_rebit hd]
      exact Iff.intro (fun h => absurd h (pwBit_ne_zero_of_isNever Ix.Kernel.PropWhen.isNever_never ψ)) (fun h => nomatch h)
    · rw [List.mem_singleton] at hd; subst hd
      exact Iff.intro (fun h => absurd h (pwBit_ne_zero_of_isNever Ix.Kernel.PropWhen.isNever_never ψ)) (fun h => nomatch h)
  · rw [List.map_append, rebit_map_dom, List.map_cons, List.map_nil]
    exact fieldsValid_append hIpsVal fun is' hspI => ⟨(hfam is' hspI).2, fun _ _ => trivial⟩

private theorem motive_app_facts {m : EnvModel V env} {ψ : LevelParam → Nat} {T : Key md}
    {nP nIdx u w : Nat} {elimL : Level} {pps ips : List (Nat × Nat × AnnotTerm)}
    (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    {Fss₀ Ess : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {ρp : Nat → V} (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hX : XChainsOk u w ρp (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess)
    (hleafT_val : ∀ σ : Nat → V, interp V σ (m.acval T ψ)
      = interp V (fun k => ρp (k + nP))
          (nativeTyAVI u w (pps ++ ips) (ips.map (·.2.2)) rss tlss Eiss Fss₀ Ess))
    {M : V} (hM : M ∈ˢ interp V ρp (motiveAVI m T ψ nP nIdx elimL ips))
    {is' : List V} (hspIs : SpineFit ρp (ips.map (·.2.2)) is')
    {x : V} (hx : x ∈ˢ SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) (tupW u is')) :
    AppChainOk M (is' ++ [x]) ∧ (is' ++ [x]).foldl SetTheory.app M ∈ˢ (univ (elimL.eval ψ) : V) := by
  let domT := AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx)
  let mds := rebit (pwBit ψ Ix.Kernel.PropWhen.never) ips ++ [(0, pwBit ψ Ix.Kernel.PropWhen.never, domT)]
  have hmEq : motiveAVI m T ψ nP nIdx elimL ips = mkPisAV mds (.sort (elimL.eval ψ)) := by
    unfold motiveAVI; rw [mkPisAV_append']; rfl
  rw [hmEq] at hM
  have hz : ∀ d ∈ mds, (1 = 0 ↔ d.2.1 = 0) := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · rw [mem_rebit hd]
      exact Iff.intro (fun h => nomatch h) (fun h => absurd h (pwBit_ne_zero_of_isNever Ix.Kernel.PropWhen.isNever_never ψ))
    · rw [List.mem_singleton] at hd; subst hd
      exact Iff.intro (fun h => nomatch h) (fun h => absurd h (pwBit_ne_zero_of_isNever Ix.Kernel.PropWhen.isNever_never ψ))
  have hlenIs' : is'.length = nIdx := by rw [hspIs.length_eq, List.length_map, hlenI]
  have hdomVal : interp V (consList is' ρp) domT
      = SetTheory.app (fixFamI u w ρp (ips.map (·.2.2)) nIdx rss tlss Eiss Fss₀ Ess) (tupW u is') := by
    have h := fixFamAt_of hlenP hlenI hsatP hX hleafT_val hlenIs' [] hspIs
    simpa [domT, consList] using h
  have hspM : SpineFit ρp (mds.map (·.2.2)) (is' ++ [x]) := by
    simp only [mds, List.map_append, rebit_map_dom, List.map_cons, List.map_nil]
    exact SpineFit.append hspIs ⟨by rwa [hdomVal], trivial⟩
  exact ⟨appChainOk_of_mkPisAV' (m := 1) hz (fun h => nomatch h) hM hspM,
    mkPisAV_fold_mem (m := 1) hz (fun h => nomatch h) hM hspM⟩

private theorem ctorVal_mem_fixFam {u w nIdx j : Nat} {ρp : Nat → V} {Ids Fs Es : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss₀ Fss Ess : List (List AnnotTerm)}
    (hX : XChainsOk u w ρp Ids rss tlss Eiss Fss₀ Ess)
    (hReal : ChainsRealI (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess) u w ρp Ids rss tlss Eiss Fss₀ Fss Ess)
    (hlenIds : Ids.length = nIdx) (hFsj : Fss[j]? = some Fs) (hEsj : Ess[j]? = some Es)
    (hlenEs : Es.length = nIdx) {fs : List V} (hspF : SpineFit ρp Fs fs)
    (hspIdx : SpineFit ρp Ids (idxValsAt ρp Es fs)) :
    ctorValI w j fs ∈ˢ SetTheory.app (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess)
      (tupW u (idxValsAt ρp Es fs)) := by
  have hReal' : ChainsRealI (fixFamI u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess)
      u w ρp Ids rss tlss Eiss Fss₀ Fss Ess := by rwa [hlenIds]
  rw [← hlenIds, fixFamI_app_eq_sum hX hReal' hspIdx, hlenIds]
  have hcEq : ctorValI w j fs = injW w j (if w = 0 then pt else mkTower (fs ++ [pt])) := by
    unfold ctorValI
    by_cases hw : w = 0 <;> simp [hw, injW_zero, injW_pos]
  rw [hcEq]
  apply injW_mem
  have hRj : (rChains nIdx nIdx Fss Ess)[j]? = some (rChain nIdx nIdx Fs Es) := by
    rw [rChains_getElem?, hFsj, hEsj]
  rw [sumFibre_of_getElem? hRj]
  have hlenIv : (idxValsAt ρp Es fs).length = nIdx := by simp [idxValsAt, hlenEs]
  have hsh : shiftE nIdx 0 (consList (idxValsAt ρp Es fs) ρp) = ρp := by
    rw [← hlenIv]; exact shiftE_consList _ _
  refine restricted_member_intro (Fs := liftFields nIdx 0 Fs) ?_ ?_
  · rw [spineFit_liftFields, hsh]; exact hspF
  · rw [EqAll_idxEqsAt hlenEs hspF.length_eq, hsh, frameIdx_consList hlenIv]

private theorem ihDomAV_wellDenotedV {u w nIdx nF o i l b ℓ : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {ρp : Nat → V} {M : V} {ms fs ihs : List V}
    (hms : ms.length + 1 = o) (hfs : fs.length = nF) (hihs : ihs.length = l) (hik : i < nF)
    {Ids Eis : List AnnotTerm} {tl : List (Nat × Nat × AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss₀ Ess : List (List AnnotTerm)}
    (hfitS : SlotFit u w ρp Ids tl Eis (fs.take i))
    (hfamU : ∀ t, SetTheory.app (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess) t ∈ˢ (univ w : V))
    (hfield : fs.getD i pt ∈ˢ slotSet w u (consList (fs.take i) ρp) tl Eis
      (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess))
    (hTlVal : FieldsValid (consList (fs.take i) ρp) (tl.map (·.2.2)))
    (hEisVal : ∀ bs, SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs →
      ∀ E ∈ Eis, AnnotValid V (consList bs (consList (fs.take i) ρp)) E)
    (hMapp : ∀ is' x, SpineFit ρp Ids is' →
      x ∈ˢ SetTheory.app (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess) (tupW u is') →
      AppChainOk M (is' ++ [x]) ∧ (is' ++ [x]).foldl SetTheory.app M ∈ˢ (univ ℓ : V)) :
    WellDenotedV V (consList ihs (consList fs (consList ms (cons M ρp))))
      (ihDomAV nF o i l (rebit b tl) Eis) := by
  let σ_ih := consList ihs (consList fs (consList ms (cons M ρp)))
  unfold ihDomAV
  have hwalk : DomsWalk σ_ih (ihTeleAtR nF o i l (rebit b tl)) := by
    apply domsWalk_of_fieldsOkB (w := w)
    rw [ihTeleAtR, ihTeleAtGo_rebit_map_dom]
    have := fieldsOkB_ihTeleAtGo (M := M) hms hfs hihs (Nat.le_of_lt hik) tl []
      (by rw [consList_nil]; exact hfitS.1)
    simpa [σ_ih, consList] using this
  have hfv : FieldsValid σ_ih ((ihTeleAtR nF o i l (rebit b tl)).map (·.2.2)) := by
    rw [ihTeleAtR, ihTeleAtGo_rebit_map_dom]
    have := fieldsValid_ihTeleAtGo (M := M) hms hfs hihs (Nat.le_of_lt hik) tl []
      (by rw [consList_nil]; exact hTlVal)
    simpa [σ_ih, consList] using this
  have hbits : ∀ d ∈ ihTeleAtR nF o i l (rebit b tl), d.2.1 = 0 ↔ ℓ = 0 := by
    intro d hd
    obtain ⟨d', hd', heq⟩ := mem_ihTeleAtGo hd
    rw [heq, mem_rebit hd']
    exact hbz.symm
  have hbody : ∀ bs, SpineFit σ_ih ((ihTeleAtR nF o i l (rebit b tl)).map (·.2.2)) bs →
      WellDenotedV V (consList bs σ_ih)
        (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + (rebit b tl).length))
          (Eis.map (ihIdxAtM nF o i l (rebit b tl).length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + (rebit b tl).length))
              (teleVarsAV (rebit b tl).length)])) ∧
      (ℓ = 0 → interp V (consList bs σ_ih)
        (AnnotTerm.mkAppN (.bvar (nF + o - 1 + l + (rebit b tl).length))
          (Eis.map (ihIdxAtM nF o i l (rebit b tl).length) ++
            [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + (rebit b tl).length))
              (teleVarsAV (rebit b tl).length)])) ∈ˢ (univZero : V)) := by
    intro bs hsp'
    rw [ihTeleAtR, ihTeleAtGo_rebit_map_dom] at hsp'
    have hsp : SpineFit (consList (fs.take i) ρp) (tl.map (·.2.2)) bs := by
      have := (spineFit_ihTeleAtGo (M := M) hms hfs hihs (Nat.le_of_lt hik) tl [] bs).mp
        (by simpa [σ_ih, consList] using hsp')
      simpa [consList] using this
    have hlenBs : (rebit b tl).length = bs.length := by
      rw [rebit_length, hsp.length_eq, List.length_map]
    rw [hlenBs]
    let σ_b := consList bs σ_ih
    have hMval : interp V σ_b (.bvar (nF + o - 1 + l + bs.length)) = M := by
      dsimp only [σ_b, σ_ih]
      rw [interp_bvar, consList_apply_add,
        show nF + o - 1 + l = (nF + o - 1) + ihs.length from by omega, consList_apply_add,
        show nF + o - 1 = (o - 1) + fs.length from by omega, consList_apply_add,
        show o - 1 = 0 + ms.length from by omega, consList_apply_add]
      rfl
    have hFval : interp V σ_b (.bvar (nF - 1 - i + l + bs.length)) = fs.getD i pt := by
      dsimp only [σ_b, σ_ih]
      rw [interp_bvar, consList_apply_add,
        show nF - 1 - i + l = (nF - 1 - i) + ihs.length from by omega, consList_apply_add,
        consList_apply_lt' fs _ (by omega), show fs.length - 1 - (nF - 1 - i) = i from by omega]
    have hvars : (teleVarsAV bs.length).map (interp V σ_b) = bs := map_fieldBvars_interp rfl _
    have hlastCh := mkAppN_wellDenoted_of_chain (f := .bvar (nF - 1 - i + l + bs.length))
      (args := teleVarsAV bs.length) (σ := σ_b) trivial
      (fun a ha => by obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial)
      (by rw [hFval, hvars]; exact slotSet_chainOk hfamU hfield hsp)
    have hlastV : AnnotValid V σ_b
        (AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + bs.length)) (teleVarsAV bs.length)) :=
      mkAppN_validV trivial fun a ha => by obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; trivial
    obtain ⟨hEok, hvsp⟩ := hfitS.2.2 bs hsp
    rw [consList_append] at hEok hvsp
    have hmem := slotSet_fold_mem hfamU hfield hsp
    let vals := Eis.map (interp V (consList bs (consList (fs.take i) ρp)))
    have hargsEq : (Eis.map (ihIdxAtM nF o i l bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + bs.length)) (teleVarsAV bs.length)]).map
          (interp V σ_b) = vals ++ [bs.foldl SetTheory.app (fs.getD i pt)] := by
      rw [List.map_append, List.map_map]
      simp only [List.map_cons, List.map_nil]
      rw [hlastCh.2, hFval, hvars]
      congr 1
      apply List.map_congr_left
      intro E _
      simp only [Function.comp]
      exact interp_ihIdxAtM hms hfs hihs (Nat.le_of_lt hik) bs E
    have hargsOk : ∀ a ∈ Eis.map (ihIdxAtM nF o i l bs.length) ++
        [AnnotTerm.mkAppN (.bvar (nF - 1 - i + l + bs.length)) (teleVarsAV bs.length)],
        WellDenotedV V σ_b a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
        exact ⟨(WellDenoted_ihIdxAtM hms hfs hihs (Nat.le_of_lt hik) bs E).mpr (hEok E hE),
          (AnnotValid_ihIdxAtM hms hfs hihs (Nat.le_of_lt hik) bs E).mpr (hEisVal bs hsp E hE)⟩
      · rw [List.mem_singleton] at ha; subst ha
        exact ⟨hlastCh.1, hlastV⟩
    obtain ⟨hMch, hMmem⟩ := hMapp vals _ hvsp hmem
    obtain ⟨hokB, hvB⟩ := mkAppN_wellDenoted_of_chain
      (f := .bvar (nF + o - 1 + l + bs.length)) (σ := σ_b) trivial
      (fun a ha => (hargsOk a ha).1) (by rw [hMval, hargsEq]; exact hMch)
    refine ⟨⟨hokB, mkAppN_validV trivial fun a ha => (hargsOk a ha).2⟩, fun hℓ0 => ?_⟩
    rw [hvB, hMval, hargsEq, ← univ_zero, ← hℓ0]
    exact hMmem
  exact ⟨WellDenoted_mkPisAV_of hwalk (fun bs hsp => (hbody bs hsp).1.1),
    AnnotValid_mkPisAV_of hbits hfv (fun bs hsp => (hbody bs hsp).1.2)
      (fun h0 bs hsp => (hbody bs hsp).2 h0)⟩

private theorem ihPisAV_wellDenotedV {nF o b ℓ tot : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    {σ_f : Nat → V} {body_conc : AnnotTerm}
    (hbody : WellDenotedV V σ_f body_conc ∧ (ℓ = 0 → interp V σ_f body_conc ∈ˢ (univZero : V))) :
    ∀ (is_rec : List Nat) (l : Nat) (ihs : List V),
      ihs.length = l → l + is_rec.length = tot →
      (∀ i ∈ is_rec, ∀ l' (ihs' : List V), ihs'.length = l' →
        WellDenotedV V (consList ihs' σ_f) (ihDomAV nF o i l' (rebit b (tls.getD i [])) (Eiss.getD i []))) →
      WellDenotedV V (consList ihs σ_f) (ihPisAV nF o b tls Eiss is_rec l (body_conc.liftN tot 0)) ∧
      (ℓ = 0 → interp V (consList ihs σ_f)
        (ihPisAV nF o b tls Eiss is_rec l (body_conc.liftN tot 0)) ∈ˢ (univZero : V))
  | [], l, ihs, hihs, htot, _ => by
    have htot' : tot = ihs.length := by simp at htot; omega
    have hsh : shiftE tot 0 (consList ihs σ_f) = σ_f := by rw [htot']; exact shiftE_consList _ _
    simp only [ihPisAV]
    refine ⟨⟨by rw [WellDenoted_liftN, hsh]; exact hbody.1.1,
      by rw [AnnotValid_liftN, hsh]; exact hbody.1.2⟩, fun hℓ0 => ?_⟩
    rw [interp_liftN, hsh]
    exact hbody.2 hℓ0
  | i :: is_rec, l, ihs, hihs, htot, hdom => by
    have hdom0 := hdom i List.mem_cons_self l ihs hihs
    have hstep : ∀ x, x ∈ˢ interp V (consList ihs σ_f)
        (ihDomAV nF o i l (rebit b (tls.getD i [])) (Eiss.getD i [])) →
        WellDenotedV V (cons x (consList ihs σ_f))
          (ihPisAV nF o b tls Eiss is_rec (l + 1) (body_conc.liftN tot 0)) ∧
        (ℓ = 0 → interp V (cons x (consList ihs σ_f))
          (ihPisAV nF o b tls Eiss is_rec (l + 1) (body_conc.liftN tot 0)) ∈ˢ (univZero : V)) := by
      intro x _
      rw [consList_snoc']
      exact ihPisAV_wellDenotedV hbz hbody is_rec (l + 1) (ihs ++ [x])
        (by rw [length_snoc', hihs]) (by simp at htot; omega)
        (fun i' hi' l' ihs' hl' => hdom i' (List.mem_cons_of_mem _ hi') l' ihs' hl')
    simp only [WellDenotedV, ihPisAV, WellDenoted_pi, AnnotValid_pi, interp_pi]
    exact ⟨⟨⟨hdom0.1, fun x hx => (hstep x hx).1.1⟩,
      ⟨hdom0.2, fun x hx => (hstep x hx).1.2, fun hb0 x hx => (hstep x hx).2 (hbz.mpr hb0)⟩⟩,
      fun hℓ0 => by rw [hbz.mp hℓ0]; exact piR_zero_mem_univZero⟩

private theorem fixMinorsData_walk {m : EnvModel V env} {ψ : LevelParam → Nat} {nP b : Nat}
    {ρp : Nat → V} {M : V} :
    ∀ (cds : List (CtorDatumR md)) (ms : List V) (o : Nat),
      ms.length + 1 = o →
      (∀ (j : Nat) (cd : CtorDatumR md) (ms' : List V),
        cds[j]? = some cd → ms'.length = ms.length + j →
        WellDenotedV V (consList ms' (cons M ρp))
          (minorAVAtR m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2.1
            cd.2.2.2.2.1 cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)) →
      DomsWalk (consList ms (cons M ρp)) (fixMinorsData m ψ nP b cds o) ∧
      FieldsValid (consList ms (cons M ρp)) ((fixMinorsData m ψ nP b cds o).map (·.2.2))
  | [], _, _, _, _ => ⟨trivial, trivial⟩
  | (C, nF, ds, Es, recIdx, Eiss, tls) :: cs, ms, o, hms, h => by
    have h0 := h 0 (C, nF, ds, Es, recIdx, Eiss, tls) ms rfl (Nat.add_zero _)
    rw [Nat.add_zero] at h0
    have hstep : ∀ x, x ∈ˢ interp V (consList ms (cons M ρp))
        (minorAVAtR m C ψ nP nF b o ds Es recIdx tls Eiss) →
        DomsWalk (cons x (consList ms (cons M ρp))) (fixMinorsData m ψ nP b cs (o + 1)) ∧
        FieldsValid (cons x (consList ms (cons M ρp)))
          ((fixMinorsData m ψ nP b cs (o + 1)).map (·.2.2)) := by
      intro x _
      rw [consList_snoc']
      refine fixMinorsData_walk cs (ms ++ [x]) (o + 1) (by rw [length_snoc']; omega)
        fun j cd ms' hcd hms' => ?_
      rw [show o + 1 + j = o + (j + 1) from by omega]
      exact h (j + 1) cd ms' (by simpa using hcd) (by rw [length_snoc'] at hms'; omega)
    exact ⟨⟨h0.1, fun x hx => (hstep x hx).1⟩, ⟨h0.2, fun x hx => (hstep x hx).2⟩⟩

private theorem minorAVAtR_wellDenotedV (mp : EnvModelM V μ env) {C : Key md} {ψ : LevelParam → Nat}
    {u w nP nF nIdx b ℓ j : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length = j)
    {ds : List (Nat × Nat × AnnotTerm)} (hlenDs : ds.length = nP + nF)
    {Ids Es : List AnnotTerm} (hlenIds : Ids.length = nIdx) (hlenEs : Es.length = nIdx)
    {recIdx_j : List Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss₀ Fss Ess : List (List AnnotTerm)}
    (hjF : j < Fss.length)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hEsj : Ess[j]? = some Es)
    (hleafC : mp.base2.acval C ψ = sumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss))
    (hokB : SumFieldsOkB w ρp Fss)
    (hFsOk : FieldsOkB w ρp ((ds.drop nP).map (·.2.2)))
    (hFsVal : FieldsValid ρp ((ds.drop nP).map (·.2.2)))
    (hEsOk : ∀ bs, SpineFit ρp ((ds.drop nP).map (·.2.2)) bs →
      (∀ E ∈ Es, WellDenoted V (consList bs ρp) E) ∧ SpineFit ρp Ids (idxValsAt ρp Es bs))
    (hEsVal : ∀ bs, SpineFit ρp ((ds.drop nP).map (·.2.2)) bs →
      ∀ E ∈ Es, AnnotValid V (consList bs ρp) E)
    (hsatC : Sat V (((ds.take nP).map (·.2.2)).reverse) ρp)
    (hX : XChainsOk u w ρp Ids rss tlss Eiss Fss₀ Ess)
    (hReal : ChainsRealI (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess)
      u w ρp Ids rss tlss Eiss Fss₀ Fss Ess)
    (hrss : recIdx_j = recIdx (rss.getD j []) nF)
    (hTlVal : ∀ i ∈ recIdx (rss.getD j []) nF, ∀ fs, SpineFit ρp ((ds.drop nP).map (·.2.2)) fs →
      FieldsValid (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) ∧
      ∀ bs, SpineFit (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) bs →
        ∀ E ∈ (Eiss.getD j []).getD i [], AnnotValid V (consList bs (consList (fs.take i) ρp)) E)
    (hMapp : ∀ is' x, SpineFit ρp Ids is' →
      x ∈ˢ SetTheory.app (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess) (tupW u is') →
      AppChainOk M (is' ++ [x]) ∧ (is' ++ [x]).foldl SetTheory.app M ∈ˢ (univ ℓ : V)) :
    WellDenotedV V (consList ms (cons M ρp))
      (minorAVAtR mp.base2 C ψ nP nF b (1 + j) ds Es recIdx_j (tlss.getD j []) (Eiss.getD j [])) := by
  let σ₀ := consList ms (cons M ρp)
  have hsh : shiftE (1 + j) 0 σ₀ = ρp := by
    dsimp only [σ₀]
    rw [show 1 + j = ms.length + 1 from by omega, shiftE_consList_add ms 1 (cons M ρp),
      shiftE_succ_cons, shiftE_zero_zero]
  unfold minorAVAtR
  have hwalk : DomsWalk σ₀ (rebit b (liftDoms (1 + j) 0 (ds.drop nP))) :=
    domsWalk_rebit b (domsWalk_liftDoms (ds.drop nP) 0 σ₀ (by rwa [hsh]))
  have hfv : FieldsValid σ₀ ((rebit b (liftDoms (1 + j) 0 (ds.drop nP))).map (·.2.2)) := by
    rw [rebit_map_dom]; exact fieldsValid_liftDoms (ds.drop nP) 0 σ₀ (by rwa [hsh])
  have hbits : ∀ d ∈ rebit b (liftDoms (1 + j) 0 (ds.drop nP)), d.2.1 = 0 ↔ ℓ = 0 := by
    intro d hd; rw [mem_rebit hd]; exact hbz.symm
  have hlenFs : ((ds.drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
  have hbody : ∀ fs, SpineFit σ₀ ((rebit b (liftDoms (1 + j) 0 (ds.drop nP))).map (·.2.2)) fs →
      WellDenotedV V (consList fs σ₀)
        (ihPisAV nF (1 + j) b (tlss.getD j []) (Eiss.getD j []) recIdx_j 0
          ((AnnotTerm.mkAppN (.bvar (nF + (1 + j) - 1))
            ((Es.map fun E => E.liftN (1 + j) nF) ++
              [AnnotTerm.mkAppN (mp.base2.acval C ψ)
                (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF)])).liftN
            recIdx_j.length 0)) ∧
      (ℓ = 0 → interp V (consList fs σ₀)
        (ihPisAV nF (1 + j) b (tlss.getD j []) (Eiss.getD j []) recIdx_j 0
          ((AnnotTerm.mkAppN (.bvar (nF + (1 + j) - 1))
            ((Es.map fun E => E.liftN (1 + j) nF) ++
              [AnnotTerm.mkAppN (mp.base2.acval C ψ)
                (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF)])).liftN
            recIdx_j.length 0)) ∈ˢ (univZero : V)) := by
    intro fs hsp'
    rw [rebit_map_dom, spineFit_liftDoms_iff, hsh] at hsp'
    have hlenAs : fs.length = nF := by rw [hsp'.length_eq, hlenFs]
    let σ_f := consList fs σ₀
    let C_spine := AnnotTerm.mkAppN (mp.base2.acval C ψ)
      (paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF)
    let body_conc := AnnotTerm.mkAppN (.bvar (nF + (1 + j) - 1))
      ((Es.map fun E => E.liftN (1 + j) nF) ++ [C_spine])
    let ρ' : Nat → V := fun k => ρp (k + nP)
    have hσ : ∀ k, σ_f (k + ((1 + j) + nF)) = ρp k := fun k => by
      dsimp only [σ_f, σ₀]
      rw [show k + ((1 + j) + nF) = (k + (1 + j)) + fs.length from by omega, consList_apply_add,
        show k + (1 + j) = (k + 1) + ms.length from by omega, consList_apply_add]
      rfl
    have hlenP' : (((ds.take nP).map (·.2.2))).length = nP := by simp [hlenDs]
    have hsp₁ := spineFit_of_sat (Δ₀ := []) (Ds := (ds.take nP).map (·.2.2))
      (by rw [List.append_nil]; exact hsatC)
    rw [hlenP'] at hsp₁
    have hCok : WellDenotedV V σ_f C_spine := by
      have hargsC : ∀ a ∈ paramBvarsAt nP (nP + (1 + j) + nF) ++ fieldBvars nF,
          WellDenotedV V σ_f a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; exact ⟨trivial, trivial⟩
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; exact ⟨trivial, trivial⟩
      have hlamEq : mp.base2.acval C ψ = mkLamsAV (ds.map fun d => (w, d.2.2))
          (sumInjAtAV w (uChains Fss) ((ds.drop nP).map (·.2.2)).length (numeralAV j)
            (mkTowerGoU w ((ds.drop nP).map (·.2.2)) (idxEqAV []))) := hleafC
      have hokL : WellDenoted V ρ' (mkLamsAV (ds.map fun d => (w, d.2.2))
          (sumInjAtAV w (uChains Fss) ((ds.drop nP).map (·.2.2)).length (numeralAV j)
            (mkTowerGoU w ((ds.drop nP).map (·.2.2)) (idxEqAV [])))) := by
        rw [← hlamEq]; exact mp.base2.acval_wellDenoted C ψ ρ'
      have hvalC : interp V σ_f (mp.base2.acval C ψ) = (pt : V) ∨
          interp V σ_f (mp.base2.acval C ψ) = interp V ρ'
            (mkLamsAV (ds.map fun d => (w, d.2.2))
              (sumInjAtAV w (uChains Fss) ((ds.drop nP).map (·.2.2)).length (numeralAV j)
                (mkTowerGoU w ((ds.drop nP).map (·.2.2)) (idxEqAV [])))) := by
        right; rw [← hlamEq]; exact interp_closed (V := V) (mp.base2.cval_closedL C ψ) σ_f ρ'
      refine mkAppN_wellDenotedV_of_lam
        ⟨mp.base2.acval_wellDenoted C ψ σ_f, mp.acval_validV C ψ σ_f⟩ hargsC hokL hvalC ?_
      rw [map_pair_dom,
        ← List.take_append_drop nP ds, List.map_append, List.map_append,
        show nP + (1 + j) + nF = nP + ((1 + j) + nF) from by omega, map_paramBvarsAt_interp hσ,
        show fieldBvars nF = (List.range nF).map (fun k => AnnotTerm.bvar (nF - 1 - k)) from rfl,
        map_fieldBvars_interp hlenAs]
      exact SpineFit.append hsp₁ (by rwa [consList_range_reverse])
    have hCval : interp V σ_f C_spine = ctorValI w j fs := by
      have hleafC' : mp.base2.acval C ψ
          = sumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) (uChains Fss) := by
        rw [hleafC, List.take_append_drop]
      dsimp only [C_spine]
      rw [interp_mkAppN, ← List.foldl_map (f := interp V σ_f) (g := SetTheory.app),
        List.map_append, show nP + (1 + j) + nF = nP + ((1 + j) + nF) from by omega,
        map_paramBvarsAt_interp hσ,
        show fieldBvars nF = (List.range nF).map (fun k => AnnotTerm.bvar (nF - 1 - k)) from rfl,
        map_fieldBvars_interp hlenAs, interp_closed (V := V) (mp.base2.cval_closedL C ψ) _ ρ',
        hleafC']
      unfold ctorValI
      rcases Nat.eq_zero_or_pos w with hw0 | hwpos
      · rw [hw0, sumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
      · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
        rw [sumMkAV_fold hw' hsp₁ (by rw [consList_range_reverse]; exact hsp')
          (by rw [consList_range_reverse]; exact SumFieldsOkB_uChains hokB)
          (by rw [uChains_getElem?, hFsj]; rfl), if_neg hw']
    have hshF : shiftE (1 + j) nF σ_f = consList fs ρp := by
      dsimp only [σ_f]; rw [← hlenAs, shiftE_consList_len, hsh]
    have hMval : interp V σ_f (.bvar (nF + (1 + j) - 1)) = M := by
      dsimp only [σ_f, σ₀]
      rw [interp_bvar, show nF + (1 + j) - 1 = j + fs.length from by omega, consList_apply_add,
        show j = 0 + ms.length from by omega, consList_apply_add]
      rfl
    have hconc : WellDenotedV V σ_f body_conc ∧ (ℓ = 0 → interp V σ_f body_conc ∈ˢ (univZero : V)) := by
      have hargsEq : ((Es.map fun E => E.liftN (1 + j) nF) ++ [C_spine]).map (interp V σ_f)
          = idxValsAt ρp Es fs ++ [ctorValI w j fs] := by
        rw [List.map_append, List.map_map]
        simp only [List.map_cons, List.map_nil]
        rw [hCval]
        congr 1
        unfold idxValsAt
        apply List.map_congr_left
        intro E _
        simp only [Function.comp]
        rw [interp_liftN, hshF]
      have hargsOk : ∀ a ∈ (Es.map fun E => E.liftN (1 + j) nF) ++ [C_spine],
          WellDenotedV V σ_f a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          exact ⟨by rw [WellDenoted_liftN, hshF]; exact (hEsOk fs hsp').1 E hE,
            by rw [AnnotValid_liftN, hshF]; exact hEsVal fs hsp' E hE⟩
        · rw [List.mem_singleton] at ha; subst ha
          exact hCok
      have hcMem := ctorVal_mem_fixFam hX hReal hlenIds hFsj hEsj hlenEs hsp' (hEsOk fs hsp').2
      obtain ⟨hMch, hMmem⟩ := hMapp (idxValsAt ρp Es fs) (ctorValI w j fs) (hEsOk fs hsp').2 hcMem
      obtain ⟨hokB', hvB'⟩ := mkAppN_wellDenoted_of_chain
        (f := .bvar (nF + (1 + j) - 1)) (σ := σ_f) trivial
        (fun a ha => (hargsOk a ha).1) (by rw [hMval, hargsEq]; exact hMch)
      refine ⟨⟨hokB', mkAppN_validV trivial fun a ha => (hargsOk a ha).2⟩, fun hℓ0 => ?_⟩
      dsimp only [body_conc] at hvB' ⊢
      rw [hvB', hMval, hargsEq, ← univ_zero, ← hℓ0]
      exact hMmem
    have hih := ihPisAV_wellDenotedV hbz hconc recIdx_j 0 [] rfl (Nat.zero_add _)
      fun i hi l' ihs' hl' => by
        rw [hrss] at hi
        obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
        have hFsD : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
          rw [List.getD_eq_getElem?_getD, hFsj]; rfl
        have hc := chainRealI_at (Fss₀.getD j []) ((ds.drop nP).map (·.2.2)) 0 [] fs rfl
          (by rw [← hFsD]; exact hReal.2.2.2.2 j hjF) (by simpa using hsp') i
          (by rw [hlenFs]; exact hik) (by rw [Nat.zero_add]; exact hri)
        rw [Nat.zero_add, List.nil_append] at hc
        obtain ⟨hfitS, heq⟩ := hc
        have hfamU : ∀ t, SetTheory.app (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess) t
            ∈ˢ (univ w : V) := fun t => by
          rw [← hlenIds]; exact famApp_mem_univ (fixFamI_mem _ _ _ _ _ _ _ _ _) t
        have hfield : fs.getD i pt ∈ˢ slotSet w u (consList (fs.take i) ρp)
            ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])
            (fixFamI u w ρp Ids nIdx rss tlss Eiss Fss₀ Ess) := by
          have := FixKI.spineFit_getD_mem' hsp' (by rw [hlenFs]; exact hik)
          rwa [heq] at this
        obtain ⟨hTv, hEv⟩ := hTlVal i hi fs hsp'
        dsimp only [σ_f, σ₀]
        exact ihDomAV_wellDenotedV (o := 1 + j) (ms := ms) hbz (by rw [hms]; omega) hlenAs hl' hik hfitS hfamU hfield hTv hEv hMapp
    simpa [consList, body_conc, C_spine] using hih
  exact ⟨WellDenoted_mkPisAV_of hwalk (fun fs hsp => (hbody fs hsp).1.1),
    AnnotValid_mkPisAV_of hbits hfv (fun fs hsp => (hbody fs hsp).1.2)
      (fun h0 fs hsp => (hbody fs hsp).2 h0)⟩

set_option maxHeartbeats 12800000 in
/-- **The P step at the recursive recursor's cons.** -/
theorem stageFixRecJ {p : NativeParts md} (hE : Ix.Kernel.EtaFamiliesClosedExcept env p.cvT.name)
    (mp : EnvModelM V μ env) {J : Judgements md} (hJ : JudgeSound J mp.base2)
    (hS : ∀ ψ, SortClaimJ J mp.base2 ψ)
    {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hmIp : p.majorIdx = mI) (hrPp : p.rulePrefix = rP)
    (hRec : NativeRecRunJ J env p cvTa ctorsA cvRa rhss)
    (hplAll : ctorsA.all (fun c => Expr.recRulePlain cvRa.type mI rP p.nP c.1.levelParams) = true)
    {bsT : List (Expr md × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {caps : IndCaps md} {cvS : ConstantVal md}
    (hfT : env.find? p.cvT.name = some (.indInfo cvS caps))
    -- the block's own capability laws at the cons (task #210 Part A),
    -- at any carrier agreeing with this one off the recursor's name
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    (hTlaws : ∀ m₂ : EnvModel V ⟨.recInfo cvRa mI rP
        (Ix.Kernel.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss) :: env.consts⟩,
      (∀ n, n ≠ cvRa.name → m₂.acval n = mp.base2.acval n) →
      FormerData m₂ cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ) →
      (∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
        ∀ ψ, m₂.acval cA.1.name ψ = mp.base2.acval cA.1.name ψ) →
      CapsLawsAt m₂ p.cvT.name cvS caps)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsS : cvS.levelParams = p.cvT.levelParams)
    {tfvs : List (Expr md)} {trest : Expr md}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (helim : p.large = true → p.elim ∈ p.cvR.levelParams)
    (hRlps' : ∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams)
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env md} {idxF : Nat → List (Expr md)} {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List (Expr md)} {xrestF : Nat → Expr md}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF i cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    (_hUparams : ∀ ψ₁ ψ₂ : LevelParam → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) → uAV ψ₁ = uAV ψ₂)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = sumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hframes : ∀ (ψ : LevelParam → Nat) (ρp : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
        (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
        (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
          (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
            WellDenoted V (consList bs ρp) E) ∧
          SpineFit ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
            (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs)) ∧
      SumFieldsValid ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) fs →
        FieldsValid (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map (·.2.2)) bs →
        ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i [],
          AnnotValid V (consList bs (consList (fs.take i) ρp)) E) ∧
      (∀ j, j < ctorsA.length →
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
          AnnotValid V (consList bs ρp) E))
    (hwl : p.large = true → (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ ctorsA.length < 2) :
    ∃ (sAV : (LevelParam → Nat) → Nat)
      (mp' : EnvModelM V μ ⟨.recInfo cvRa mI rP (Ix.Kernel.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss)
        :: env.consts⟩),
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA sAV) := by
  -- the constant's facts
  obtain ⟨-, -, cvRi, recTy, hccv, -, htp, htrR, -, -, -, -, hcvRa⟩ :=
    id hRec
  have hcvRa : cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := hcvRa
  obtain ⟨-, ⟨hfind', hnres, hpshape, -, -, -, -, -, -, -⟩, -⟩ :=
    hccv
  have hfind := Option.isNone_iff_eq_none.mp hfind'
  have hRname : cvRa.name = p.cvR.name := by rw [hcvRa]
  have hRlps : cvRa.levelParams = p.cvR.levelParams := by rw [hcvRa]
  have hRtype : cvRa.type = recTy := by rw [hcvRa]
  have hfresh : env.find? cvRa.name = none := by rw [hRname]; exact hfind
  have htrR' : cvRa.type.constsResolve env = true := by rw [hRtype]; exact htrR
  have hcbR : ConstsBound env cvRa.type := constsBound_of_constsResolve _ htrR'
  have hwf := hRec.recWF mp.base2.wf
  rw [hmIp, hrPp] at hwf
  have hTR : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- names
  generalize hElimL : Ix.Kernel.structElimLevel p.elim p.large = elimL at hleafC ⊢
  have hrdsE : ∀ ψ, fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ
      = fixRecDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ((ppsAll ψ).take p.nP)
          ((ppsAll ψ).drop p.nP) (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) := by
    intro ψ; unfold fixRdsAV; rw [hElimL]
  -- the block's lengths and the per-constructor pins
  have hn : ∀ ψ, (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0).length = ctorsA.length :=
    fun ψ => fixCtorDataList_length _ _ _ _ _ _ _ _
  have hlenPps : ∀ ψ, ((ppsAll ψ).take p.nP).length = p.nP := fun ψ => by
    rw [List.length_take, hFD.len ψ]; omega
  have hlenIps : ∀ ψ, ((ppsAll ψ).drop p.nP).length = p.nIdx := fun ψ => by
    rw [List.length_drop, hFD.len ψ]; omega
  have hlenIds : ∀ ψ, ((((ppsAll ψ).drop p.nP).map (·.2.2))).length = p.nIdx := fun ψ => by
    rw [List.length_map, hlenIps]
  have hlenFs : ∀ ψ, (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).length = ctorsA.length :=
    fun ψ => by rw [fssOfR_length, hn]
  have hlenEs : ∀ ψ, (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).length = ctorsA.length :=
    fun ψ => by rw [essOfR_length, hn]
  have hjd : ∀ ψ j cA, ctorsA[j]? = some cA →
      (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)[j]?
        = some (cA.1.name, cA.2, dsF j ψ, esF j ψ, Ix.Kernel.recIdxOf (ksF j), eissF j ψ, tssF j ψ) := by
    intro ψ j cA hj
    rw [fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl
  have hFsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []
        = ((dsF j ψ).drop p.nP).map (·.2.2) := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, fssOfR_getElem?, hjd ψ j cA hj]; rfl
  have hEsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = esF j ψ := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, essOfR_getElem?, hjd ψ j cA hj]; rfl
  have hEisjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = eissF j ψ := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, eissOfR_getElem?, hjd ψ j cA hj]; rfl
  have hcAof : ∀ j, j < ctorsA.length → ∃ cA, ctorsA[j]? = some cA :=
    fun j hj => ⟨_, List.getElem?_eq_getElem hj⟩
  have hTlsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = tssF j ψ := by
    intro ψ j cA hj
    rw [List.getD_eq_getElem?_getD, tlssOfR_getElem?, hjd ψ j cA hj]; rfl
  have hTlsNone : ∀ ψ j, ¬ j < ctorsA.length →
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = [] := by
    intro ψ j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [tlssOfR_length, hn]; omega)]; rfl
  -- the elimination level's bit and zeroness
  have hbz : ∀ ψ, elimL.eval ψ = 0 ↔ pwBit ψ (Level.zeronessOf elimL) = 0 := by
    intro ψ
    rw [pwBit_eq_zero_iff, Ix.Kernel.PropWhen.zeronessOf_sound, beq_iff_eq]
  have hlarge_of : ∀ ψ, elimL.eval ψ ≠ 0 → p.large = true := by
    intro ψ hl0
    cases hpl : p.large
    · exfalso; apply hl0; rw [← hElimL]; simp [Ix.Kernel.structElimLevel, hpl, Level.eval]
    · rfl
  -- the squash regime (task #202 A2): a large eliminator at a `Prop`
  -- instance has at most one constructor (none since task #210 Part B)
  have hsingle : ∀ ψ, p.resSort.eval ψ = 0 → elimL.eval ψ ≠ 0 → ctorsA.length ≤ 1 := by
    intro ψ hw0 hl0
    rcases hwl (hlarge_of ψ hl0) with hnz | hlt
    · exact absurd hw0 (hnz ψ)
    · omega
  -- the subsingleton criterion (task #202 A2): at a `Prop` instance
  -- with a large eliminator, a field not sourced by an index
  -- expression is a proposition (the kernel's `checkStructFieldSortsI`)
  have hprop : ∀ ψ, p.resSort.eval ψ = 0 → elimL.eval ψ ≠ 0 → ∀ ρp : Nat → V,
      Sat V ((((ppsAll ψ).take p.nP).map (·.2.2)).reverse) ρp →
      ∀ j, j < ctorsA.length →
      ∀ i, i < ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length →
      srcOfEs ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [])
        ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length i = none →
      ∀ fs : List V,
        SpineFit ρp (((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).take i) fs →
        interp V (consList fs ρp)
            (((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i default)
          ∈ˢ (univZero : V) := by
    intro ψ hw0 hℓ0 ρp hρp j hj i hi hsrc fs hfs
    obtain ⟨cA, hjA⟩ := hcAof j hj
    obtain ⟨-, -, hCD⟩ := hcf j cA hjA
    rw [hFsjD ψ j cA hjA] at hi hfs hsrc ⊢
    rw [hEsjD ψ j cA hjA] at hsrc
    have hsatC := (hiff j cA hjA ψ ρp).mp hρp
    have hbnd := hCD.srcProp (hlarge_of ψ hℓ0) ψ hw0 ρp hsatC
    have hlenF : (((dsF j ψ).drop p.nP).map (·.2.2)).length = cA.2 := by simp [hCD.len ψ]
    rw [hlenF] at hi hsrc
    obtain ⟨s', hs⟩ : ∃ s', (srcsF j)[i]? = some s' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hCD.srcLen]; exact hi)⟩
    have hsn : s' = none := by
      cases s' with
      | none => rfl
      | some l => exact absurd (hCD.srcIdx i l hs ψ) fun h => srcOfEs_none hsrc h
    subst hsn
    rw [← univ_zero]
    exact fieldsBoundSrc_at hbnd hs hfs (by rw [hlenF]; exact hi)
  -- the frames at a parameter valuation, in `fixPre_of`'s shape
  have hframes' : ∀ (ψ : LevelParam → Nat) (ρp : Nat → V),
      Sat V ((((ppsAll ψ).take p.nP).map (·.2.2)).reverse) ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
        (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
        (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
          (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
            WellDenoted V (consList bs ρp) E) ∧
          SpineFit ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
            (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs)) ∧
      (∀ σ : Nat → V, interp V σ (mp.base2.acval p.cvT.name ψ)
        = interp V (fun k => ρp (k + p.nP))
            (nativeTyAVI (uAV ψ) (p.resSort.eval ψ) ((ppsAll ψ).take p.nP ++ (ppsAll ψ).drop p.nP)
              (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
              (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
              (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
              (fssZ ψ)
              (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))) ∧
      (∀ j cd, (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)[j]? = some cd →
        ∀ (M : V) (ms : List V), ms.length = j →
        interp V (consList ms (cons M ρp))
            (minorAVAtR mp.base2 cd.1 ψ p.nP cd.2.1 (pwBit ψ (Level.zeronessOf elimL)) (1 + j)
              cd.2.2.1 cd.2.2.2.1 cd.2.2.2.2.1
              cd.2.2.2.2.2.2 cd.2.2.2.2.2.1)
          = minorSpI (elimL.eval ψ) (fun fs => ihSpL (elimL.eval ψ)
              (concI (p.resSort.eval ψ) ρp M ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) j fs)
              (ihDomsI (elimL.eval ψ) ρp M (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
                (fun j' => ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j' []).length) j fs))
            ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) ρp []) := by
    intro ψ ρp hρp
    obtain ⟨hX, hreal, hfields, hv, hEisV, hEsV⟩ := hframes ψ ρp hρp
    have hokB : SumFieldsOkB (p.resSort.eval ψ) ρp
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) := by
      intro Fs hFs
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
      have hjn : j < ctorsA.length := by
        rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj).1
      have := (hfields j hjn).1
      rwa [List.getD_eq_getElem?_getD, hj] at this
    refine ⟨hX, hreal, hfields, ?_, ?_⟩
    · intro σ
      rw [List.take_append_drop, interp_closed (V := V) (mp.base2.cval_closedL p.cvT.name ψ) σ
        (fun k => ρp (k + p.nP)), hleafT ψ]
    · intro j cd hcd M ms hlenM
      have hjn : j < ctorsA.length := by
        rw [← hn ψ]; exact (List.getElem?_eq_some_iff.mp hcd).1
      obtain ⟨cA, hj⟩ := hcAof j hjn
      obtain rfl := Option.some.inj ((hjd ψ j cA hj).symm.trans hcd)
      obtain ⟨-, -, hD⟩ := hcf j cA hj
      have hrss : Ix.Kernel.recIdxOf (ksF j) = recIdx ((rssOfK ksF ctorsA.length).getD j []) cA.2 := by
        rw [rssOfK_getD hjn, ← hD.ksLen, recIdx_rsOf]
      show interp V (consList ms (cons M ρp))
        (minorAVAtR mp.base2 cA.1.name ψ p.nP cA.2 _ (1 + j) (dsF j ψ) (esF j ψ)
          (Ix.Kernel.recIdxOf (ksF j)) (tssF j ψ) (eissF j ψ)) = _
      rw [hrss, ← hEisjD ψ j cA hj, ← hTlsjD ψ j cA hj, hEsjD ψ j cA hj, hFsjD ψ j cA hj]
      exact interp_minorAVAtR (hbz ψ) hlenM (hD.len ψ) (hleafC j cA hj ψ)
        (mp.base2.cval_closedL cA.1.name ψ) (by rw [fssOfR_getElem?, hjd ψ j cA hj]; rfl) hokB
        ((hiff j cA hj ψ ρp).mp hρp)
  -- the per-field data's pins
  have hEs : ∀ ψ j, j < ctorsA.length →
      ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length = p.nIdx := by
    intro ψ j hj
    obtain ⟨cA, hjA⟩ := hcAof j hj
    rw [hEsjD ψ j cA hjA]
    exact (hcf j cA hjA).2.2.lenE ψ
  have hEisLen : ∀ ψ j i, i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
      ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length →
      (((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).length = p.nIdx := by
    intro ψ j i hi
    by_cases hj : j < ctorsA.length
    · obtain ⟨cA, hjA⟩ := hcAof j hj
      obtain ⟨-, -, hD⟩ := hcf j cA hjA
      rw [rssOfK_getD hj, hFsjD ψ j cA hjA, List.length_map, List.length_drop, hD.len ψ,
        Nat.add_sub_cancel_left, ← hD.ksLen, recIdx_rsOf, mem_recIdxOf] at hi
      rw [hEisjD ψ j cA hjA]
      rcases hi.2 with hk | hk
      · exact hD.eisLen ψ i hk (by rw [← hD.ksLen]; exact hi.1)
      · exact hD.eisLenRefl ψ i hk (by rw [← hD.ksLen]; exact hi.1)
    · exfalso
      have h0 : (rssOfK ksF ctorsA.length).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [rssOfK]; omega)]; rfl
      rw [h0] at hi
      obtain ⟨-, hr⟩ := mem_recIdx.mp hi
      simp at hr
  have hEbelow : ∀ ψ j i, ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i [],
      Term.bvarsBelow (p.nP + i +
        (((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).length)
        E.erase := by
    intro ψ j i E hE
    by_cases hj : j < ctorsA.length
    · obtain ⟨cA, hjA⟩ := hcAof j hj
      rw [hEisjD ψ j cA hjA] at hE
      rw [hTlsjD ψ j cA hjA]
      exact (hcf j cA hjA).2.2.eissBelow ψ i E hE
    · exfalso
      have h0 : (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [eissOfR_length, hn]; omega)]; rfl
      rw [h0] at hE
      simp at hE
  have hTlsBelow : ∀ ψ j i, DomsBelow (p.nP + i)
      (((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []) := by
    intro ψ j i
    by_cases hj : j < ctorsA.length
    · obtain ⟨cA, hjA⟩ := hcAof j hj
      rw [hTlsjD ψ j cA hjA]
      exact (hcf j cA hjA).2.2.tssBelow ψ i
    · rw [hTlsNone ψ j hj]; trivial
  -- the generated recursor type's grading and bit-validity
  have hokTy : ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
        (recConcAV ctorsA.length p.nIdx)) := by
    intro ψ ρ
    rw [hrdsE ψ]
    let b := pwBit ψ (Level.zeronessOf elimL)
    let pps := (ppsAll ψ).take p.nP
    let ips := (ppsAll ψ).drop p.nP
    let cds := fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0
    have hppsAll : ppsAll ψ = pps ++ ips := (List.take_append_drop p.nP (ppsAll ψ)).symm
    have hFDok := (WellDenoted_mkPisAV_inv (hFD.okTy ψ ρ).1).1
    have hFDval := (AnnotValid_mkPisAV_inv (hFD.okTy ψ ρ).2).1
    rw [hppsAll, List.map_append] at hFDok hFDval
    obtain ⟨hppsOk, hipsOk⟩ := fieldsOkB_append_inv hFDok
    obtain ⟨hppsVal, hipsVal⟩ := fieldsValid_append_inv hFDval
    have hleafT_lam : ∃ B, mp.base2.acval p.cvT.name ψ
        = mkLamsAV ((ppsAll ψ).map fun d => (p.resSort.eval ψ + 1, d.2.2)) B := ⟨_, hleafT ψ⟩
    have hbits : ∀ d ∈ fixRecDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL pps ips cds,
        d.2.1 = 0 ↔ elimL.eval ψ = 0 := by
      intro d hd; rw [mem_fixRecDataAV hd]; exact (hbz ψ).symm
    have hminorOk : ∀ (ps : List V), SpineFit ρ (pps.map (·.2.2)) ps →
        ∀ (M : V), M ∈ˢ interp V (consList ps ρ) (motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips) →
        DomsWalk (cons M (consList ps ρ)) (fixMinorsData mp.base2 ψ p.nP b cds 1) ∧
        FieldsValid (cons M (consList ps ρ)) ((fixMinorsData mp.base2 ψ p.nP b cds 1).map (·.2.2)) := by
      intro ps hspP M hM
      let ρp := consList ps ρ
      have hρp : Sat V ((pps.map (·.2.2)).reverse) ρp := by
        have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspP
        rwa [List.append_nil] at this
      obtain ⟨hX, hreal, hfields, hv, hEisV, hEsV⟩ := hframes ψ ρp hρp
      obtain ⟨-, -, -, hleafT_val, -⟩ := hframes' ψ ρp hρp
      have hokB : SumFieldsOkB (p.resSort.eval ψ) ρp (fssOfR p.nP cds) := by
        intro Fs hFs
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
        have hjn : j < ctorsA.length := by
          rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj).1
        have := (hfields j hjn).1
        rwa [List.getD_eq_getElem?_getD, hj] at this
      have hMapp := fun (is' : List V) (x : V) (hspIs : SpineFit ρp (ips.map (·.2.2)) is') hx =>
        motive_app_facts (x := x) (hlenPps ψ) (hlenIps ψ) hρp hX hleafT_val hM hspIs hx
      have hw := fixMinorsData_walk cds ([] : List V) 1 rfl fun j cd ms' hcd hms' => by
        rw [List.length_nil, Nat.zero_add] at hms'
        have hjn : j < ctorsA.length := by
          rw [← hn ψ]; exact (List.getElem?_eq_some_iff.mp hcd).1
        obtain ⟨cA, hj⟩ := hcAof j hjn
        obtain rfl := Option.some.inj ((hjd ψ j cA hj).symm.trans hcd)
        obtain ⟨-, -, hD⟩ := hcf j cA hj
        have hrss : Ix.Kernel.recIdxOf (ksF j) = recIdx ((rssOfK ksF ctorsA.length).getD j []) cA.2 := by
          rw [rssOfK_getD hjn, ← hD.ksLen, recIdx_rsOf]
        have hFsj : (fssOfR p.nP cds)[j]? = some (((dsF j ψ).drop p.nP).map (·.2.2)) := by
          rw [fssOfR_getElem?, hjd ψ j cA hj]; rfl
        have hEsj : (essOfR cds)[j]? = some (esF j ψ) := by
          rw [essOfR_getElem?, hjd ψ j cA hj]; rfl
        have hFsOk_j : FieldsOkB (p.resSort.eval ψ) ρp (((dsF j ψ).drop p.nP).map (·.2.2)) := by
          have := (hfields j hjn).1; rwa [hFsjD ψ j cA hj] at this
        have hFsVal_j : FieldsValid ρp (((dsF j ψ).drop p.nP).map (·.2.2)) :=
          hv _ (List.mem_of_getElem? hFsj)
        have hEsOk_j : ∀ bs, SpineFit ρp (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
            (∀ E ∈ esF j ψ, WellDenoted V (consList bs ρp) E) ∧
            SpineFit ρp (ips.map (·.2.2)) (idxValsAt ρp (esF j ψ) bs) := by
          intro bs hspB
          have := (hfields j hjn).2 bs (by rwa [hFsjD ψ j cA hj])
          rwa [hEsjD ψ j cA hj] at this
        have hEsVal_j : ∀ bs, SpineFit ρp (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
            ∀ E ∈ esF j ψ, AnnotValid V (consList bs ρp) E := by
          intro bs hspB E hE
          exact hEsV j hjn bs (by rwa [hFsjD ψ j cA hj]) E (by rwa [hEsjD ψ j cA hj])
        have hTlVal_j : ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j []) cA.2,
            ∀ fs, SpineFit ρp (((dsF j ψ).drop p.nP).map (·.2.2)) fs →
            FieldsValid (consList (fs.take i) ρp)
              ((((tlssOfR cds).getD j []).getD i []).map (·.2.2)) ∧
            ∀ bs, SpineFit (consList (fs.take i) ρp)
              ((((tlssOfR cds).getD j []).getD i []).map (·.2.2)) bs →
              ∀ E ∈ ((eissOfR cds).getD j []).getD i [],
                AnnotValid V (consList bs (consList (fs.take i) ρp)) E := by
          intro i hi fs hspF
          have hlenFj : ((fssOfR p.nP cds).getD j []).length = cA.2 := by
            rw [hFsjD ψ j cA hj]; simp [hD.len ψ]
          exact hEisV j hjn i (by rwa [hlenFj]) fs (by rwa [hFsjD ψ j cA hj])
        show WellDenotedV V (consList ms' (cons M ρp))
          (minorAVAtR mp.base2 cA.1.name ψ p.nP cA.2 b (1 + j) (dsF j ψ) (esF j ψ)
            (Ix.Kernel.recIdxOf (ksF j)) (tssF j ψ) (eissF j ψ))
        rw [← hTlsjD ψ j cA hj, ← hEisjD ψ j cA hj]
        exact minorAVAtR_wellDenotedV mp (hbz ψ) hms' (hD.len ψ) (hlenIds ψ) (hD.lenE ψ)
          (by rw [hlenFs ψ]; exact hjn) hFsj hEsj (hleafC j cA hj ψ) hokB hFsOk_j hFsVal_j
          hEsOk_j hEsVal_j ((hiff j cA hj ψ ρp).mp hρp) hX hreal hrss hTlVal_j hMapp
      simpa [consList, ρp] using hw
    have hwalkAll : DomsWalk ρ (fixRecDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL pps ips cds) ∧
        FieldsValid ρ ((fixRecDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL pps ips cds).map (·.2.2)) := by
      unfold fixRecDataAV
      change DomsWalk ρ ((((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ++ rebit b (liftDoms (cds.length + 1) 0 ips)) ++
          [(0, b, majorAVAt mp.base2 p.cvT.name ψ p.nP p.nIdx cds.length)]) ∧
        FieldsValid ρ (((((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ++ rebit b (liftDoms (cds.length + 1) 0 ips)) ++
          [(0, b, majorAVAt mp.base2 p.cvT.name ψ p.nP p.nIdx cds.length)]).map (fun d : Nat × Nat × AnnotTerm => d.2.2))
      have h12 : DomsWalk ρ (rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ∧
          FieldsValid ρ ((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) := by
        have hmot : ∀ ps, SpineFit ρ (pps.map (·.2.2)) ps →
            WellDenotedV V (consList ps ρ) (motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips) := by
          intro ps hspP
          have hρp : Sat V ((pps.map (·.2.2)).reverse) (consList ps ρ) := by
            have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspP
            rwa [List.append_nil] at this
          exact motiveAVI_wellDenotedV mp hppsAll (hlenPps ψ) (hlenIps ψ) hρp hleafT_lam
            (hipsOk ps hspP) (hipsVal ps hspP)
        refine ⟨domsWalk_append (domsWalk_rebit b (domsWalk_of_fieldsOkB hppsOk)) fun ps hspP => ?_,
          by rw [List.map_append, rebit_map_dom, List.map_cons, List.map_nil]
             exact fieldsValid_append hppsVal fun ps hspP => ⟨(hmot ps hspP).2, fun _ _ => trivial⟩⟩
        rw [rebit_map_dom] at hspP
        exact ⟨(hmot ps hspP).1, fun _ _ => trivial⟩
      have h123 : DomsWalk ρ ((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ∧
          FieldsValid ρ (((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) := by
        have hstep3 : ∀ pm, SpineFit ρ ((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) pm →
            DomsWalk (consList pm ρ) (fixMinorsData mp.base2 ψ p.nP b cds 1) ∧
            FieldsValid (consList pm ρ) ((fixMinorsData mp.base2 ψ p.nP b cds 1).map (·.2.2)) := by
          intro pm hspPM
          rw [List.map_append, rebit_map_dom, List.map_cons, List.map_nil] at hspPM
          obtain ⟨ps, m₁, rfl, hspP, hspM⟩ := spineFit_append_inv hspPM
          obtain ⟨M, rfl, hM⟩ := spineFit_singleton hspM
          rw [consList_append, consList_cons, consList_nil]
          exact hminorOk ps hspP M hM
        exact ⟨domsWalk_append h12.1 (fun pm h => (hstep3 pm h).1),
          by rw [List.map_append]; exact fieldsValid_append h12.2 (fun pm h => (hstep3 pm h).2)⟩
      have h1234 : DomsWalk ρ (((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ++ rebit b (liftDoms (cds.length + 1) 0 ips)) ∧
          FieldsValid ρ ((((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ++ rebit b (liftDoms (cds.length + 1) 0 ips)).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) := by
        have hstep4 : ∀ pmm, SpineFit ρ (((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
              fixMinorsData mp.base2 ψ p.nP b cds 1).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) pmm →
            DomsWalk (consList pmm ρ) (rebit b (liftDoms (cds.length + 1) 0 ips)) ∧
            FieldsValid (consList pmm ρ) ((rebit b (liftDoms (cds.length + 1) 0 ips)).map (·.2.2)) := by
          intro pmm hspPMM
          rw [List.map_append, List.map_append, rebit_map_dom, List.map_cons, List.map_nil] at hspPMM
          obtain ⟨pm, ms, rfl, hspPM, hspMs⟩ := spineFit_append_inv hspPMM
          obtain ⟨ps, m₁, rfl, hspP, hspM⟩ := spineFit_append_inv hspPM
          obtain ⟨M, rfl, -⟩ := spineFit_singleton hspM
          have hlenMs : ms.length = cds.length := by
            rw [hspMs.length_eq, List.length_map, fixMinorsData_length]
          have hsh4 : shiftE (cds.length + 1) 0 (consList ((ps ++ [M]) ++ ms) ρ) = consList ps ρ := by
            rw [consList_append, consList_append, consList_cons, consList_nil, shiftE_minors hlenMs]
          exact ⟨domsWalk_rebit b (domsWalk_liftDoms ips 0 _ (by rw [hsh4]; exact hipsOk ps hspP)),
            by rw [rebit_map_dom]; exact fieldsValid_liftDoms ips 0 _ (by rw [hsh4]; exact hipsVal ps hspP)⟩
        exact ⟨domsWalk_append h123.1 (fun pmm h => (hstep4 pmm h).1),
          by rw [List.map_append]; exact fieldsValid_append h123.2 (fun pmm h => (hstep4 pmm h).2)⟩
      have hstep5 : ∀ as, SpineFit ρ ((((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ++ rebit b (liftDoms (cds.length + 1) 0 ips)).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) as →
          WellDenotedV V (consList as ρ) (majorAVAt mp.base2 p.cvT.name ψ p.nP p.nIdx cds.length) := by
        intro as hspAs
        rw [List.map_append, List.map_append, List.map_append, rebit_map_dom, rebit_map_dom,
          List.map_cons, List.map_nil] at hspAs
        obtain ⟨ps, M, ms, is, rfl, -, hlenMs, -, hρp, -, -, hfitI⟩ :=
          fixSpine_split (T := p.cvT.name) (elimL := elimL) (hlenPps ψ) (hlenIps ψ) (rfl : cds.length = cds.length)
            (fun ρp hρp => (hframes' ψ ρp hρp).2.2.2.2) ρ as hspAs
        have hfam := famSpine_wellDenotedV (D := p.nP + 1 + cds.length + p.nIdx) mp hppsAll (hlenPps ψ) (hlenIps ψ) hρp hleafT_lam
          (extras := M :: ms) hfitI (by simp [hlenMs]; omega)
        unfold majorAVAt
        rw [consList_append, consList_append, consList_append, consList_cons, consList_nil]
        rw [consList_cons] at hfam
        exact hfam
      exact ⟨domsWalk_append h1234.1 (fun as h => ⟨(hstep5 as h).1, fun _ _ => trivial⟩),
        by rw [List.map_append, List.map_cons, List.map_nil]
           exact fieldsValid_append h1234.2 (fun as h => ⟨(hstep5 as h).2, fun _ _ => trivial⟩)⟩
    have hbodyAll : ∀ as', SpineFit ρ ((fixRecDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL pps ips cds).map (·.2.2)) as' →
        WellDenotedV V (consList as' ρ) (recConcAV ctorsA.length p.nIdx) ∧
        (elimL.eval ψ = 0 → interp V (consList as' ρ) (recConcAV ctorsA.length p.nIdx) ∈ˢ (univZero : V)) := by
      intro as' hspAll
      unfold fixRecDataAV at hspAll
      change SpineFit ρ (((((rebit b pps ++ [(0, b, motiveAVI mp.base2 p.cvT.name ψ p.nP p.nIdx elimL ips)]) ++
            fixMinorsData mp.base2 ψ p.nP b cds 1) ++ rebit b (liftDoms (cds.length + 1) 0 ips)) ++
          [(0, b, majorAVAt mp.base2 p.cvT.name ψ p.nP p.nIdx cds.length)]).map (fun d : Nat × Nat × AnnotTerm => d.2.2)) as' at hspAll
      rw [List.map_append, List.map_append, List.map_append, List.map_append,
        rebit_map_dom, rebit_map_dom, List.map_cons, List.map_nil, List.map_cons, List.map_nil] at hspAll
      obtain ⟨as, ts, rfl, hspAs, hspT⟩ := spineFit_append_inv hspAll
      obtain ⟨t, rfl, ht⟩ := spineFit_singleton hspT
      obtain ⟨ps, M, ms, is, rfl, -, hlenMs, hlenIs, hρp, hM, -, hfitI⟩ :=
        fixSpine_split (T := p.cvT.name) (elimL := elimL) (hlenPps ψ) (hlenIps ψ) (hn ψ)
          (fun ρp hρp => (hframes' ψ ρp hρp).2.2.2.2) ρ as (by rw [hn ψ] at hspAs; exact hspAs)
      obtain ⟨hX, -, -, hleafT_val, -⟩ := hframes' ψ (consList ps ρ) hρp
      rw [consList_append, consList_append, consList_append, consList_cons, consList_nil, hn ψ] at ht
      rw [interp_majorAVAt (hlenPps ψ) (hlenIps ψ) hρp hX hleafT_val hlenMs hfitI] at ht
      obtain ⟨hMch, hMmem⟩ := motive_app_facts (hlenPps ψ) (hlenIps ψ) hρp hX hleafT_val hM hfitI ht
      let σ_top := cons t (consList is (consList ms (cons M (consList ps ρ))))
      have hσEq : consList ((((ps ++ [M]) ++ ms) ++ is) ++ [t]) ρ = σ_top := by
        simp only [σ_top, consList_append, consList_cons, consList_nil]
      rw [hσEq]
      have hconcEq : recConcAV ctorsA.length p.nIdx
          = AnnotTerm.mkAppN (.bvar (1 + p.nIdx + ctorsA.length)) (idxVarsAV p.nIdx 1 ++ [AnnotTerm.bvar 0]) :=
        (AnnotTerm.mkAppN_append_one _ _ _).symm
      rw [hconcEq]
      have hMval : interp V σ_top (.bvar (1 + p.nIdx + ctorsA.length)) = M := by
        dsimp only [σ_top]
        rw [interp_bvar, show 1 + p.nIdx + ctorsA.length = (p.nIdx + ctorsA.length) + 1 from by omega,
          cons_succ, show p.nIdx + ctorsA.length = ctorsA.length + is.length from by omega,
          consList_apply_add, show ctorsA.length = 0 + ms.length from by omega, consList_apply_add]
        rfl
      have hfr1 : RecFrameS 1 (consList is (consList ms (cons M (consList ps ρ)))) σ_top := by
        unfold RecFrameS
        rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      have hargsEq : (idxVarsAV p.nIdx 1 ++ [AnnotTerm.bvar 0]).map (interp V σ_top) = is ++ [t] := by
        rw [List.map_append, map_idxVarsAV_interp hfr1, frameIdx_consList hlenIs,
          List.map_cons, List.map_nil, interp_bvar]
        rfl
      have hargsOk : ∀ a ∈ idxVarsAV p.nIdx 1 ++ [AnnotTerm.bvar 0], WellDenotedV V σ_top a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; exact ⟨trivial, trivial⟩
        · rw [List.mem_singleton] at ha; subst ha; exact ⟨trivial, trivial⟩
      obtain ⟨hokC, hvC⟩ := mkAppN_wellDenoted_of_chain
        (f := .bvar (1 + p.nIdx + ctorsA.length)) (σ := σ_top) trivial
        (fun a ha => (hargsOk a ha).1) (by rw [hMval, hargsEq]; exact hMch)
      refine ⟨⟨hokC, mkAppN_validV trivial fun a ha => (hargsOk a ha).2⟩, fun hℓ0 => ?_⟩
      rw [hvC, hMval, hargsEq, ← univ_zero, ← hℓ0]
      exact hMmem
    exact ⟨WellDenoted_mkPisAV_of hwalkAll.1 (fun as' hsp => (hbodyAll as' hsp).1.1),
      AnnotValid_mkPisAV_of hbits hwalkAll.2 (fun as' hsp => (hbodyAll as' hsp).1.2)
        (fun h0 as' hsp => (hbodyAll as' hsp).2 h0)⟩
  -- the data, the openings, and the recursor type's universe
  obtain ⟨hRD, u, hsort⟩ := fixRecDataJ hJ hS hRec hfT hlpsS hstripT hopT hFD hlenK hks hcf hokTy
  obtain ⟨fvsR, oR, hR⟩ := fixRecOpenedAll mp hRec hstripT hlenK hRD
  rw [hElimL] at hRD
  let sAV : (LevelParam → Nat) → Nat := fixSortAV elimL u cvRa.levelParams
  let A : (LevelParam → Nat) → AnnotTerm := fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA sAV
  have hA : ∀ ψ, A ψ = nativeRecAVI (elimL.eval ψ) (p.resSort.eval ψ) p.nP
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (((ppsAll ψ).drop p.nP).map (·.2.2))
      (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ) (sAV ψ) := by
    intro ψ
    show fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA sAV ψ = _
    unfold fixLeafAV
    rw [hElimL]
  have hs0 : ∀ ψ, sAV ψ = 0 ↔ elimL.eval ψ = 0 := fun ψ => fixSortAV_zero_iff elimL u _ ψ
  have hunivTy : ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      interp V ρ (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
        (recConcAV ctorsA.length p.nIdx)) ∈ˢ (univ (sAV ψ) : V) := by
    intro ψ ρ
    show _ ∈ˢ (univ (fixSortAV elimL u cvRa.levelParams ψ) : V)
    unfold fixSortAV
    split
    · next h0 =>
      rw [univ_zero]
      have hlen := hRD.len ψ
      cases hrds : fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ with
      | nil => rw [hrds] at hlen; simp at hlen
      | cons d rest =>
        show piR d.2.1 _ _ ∈ˢ _
        have hd0 : d.2.1 = 0 := (hRD.bits ψ d (by rw [hrds]; exact List.mem_cons_self)).mp h0
        rw [hd0]
        exact piR_zero_mem_univZero
    · next h0 =>
      have hagree := restrictΨ_agree cvRa.levelParams ψ
      have hrdsEq := hRD.params (restrictΨ cvRa.levelParams ψ) ψ hagree
      have := hsort (restrictΨ cvRa.levelParams ψ) ρ
      rw [hrdsEq] at this
      exact univ_mono (Nat.le_max_right 1 _) _ this
  -- the premise, the leaf's facts, the leaf's closedness
  have hpre : ∀ ψ, FixPre V (elimL.eval ψ) (p.resSort.eval ψ) (uAV ψ) p.nP
      (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fssZ ψ)
      (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
      (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
      (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ) (sAV ψ) := by
    intro ψ
    rw [hrdsE ψ]
    refine fixPre_of rfl rfl (hbz ψ) (hs0 ψ) (hlenPps ψ) (hlenIps ψ) (hn ψ) (hlenFs ψ)
      (hlenEs ψ) (hEs ψ) (hEisLen ψ) (hEbelow ψ) (hsingle ψ) (hprop ψ) (hTlsBelow ψ)
      ?_ ?_ ?_ ?_ (hframes' ψ)
    · have := hRD.below ψ; rw [hrdsE ψ] at this; exact this
    · have := (hR ψ).okΓ; rw [hrdsE ψ] at this; exact this
    · intro ρ; have := (hRD.okTy ψ ρ).1; rw [hrdsE ψ] at this; exact this
    · intro ρ; have := hunivTy ψ ρ; rw [hrdsE ψ] at this; exact this
  have hokΓ : ∀ ψ, ∀ i, i < p.nP + ctorsA.length + p.nIdx + 2 → ∀ ρ : Nat → V,
      Sat V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ).map (·.2.2)).reverse).drop
        (p.nP + ctorsA.length + p.nIdx + 2 - i)) ρ →
      WellDenotedV V ρ ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ).map (·.2.2)).reverse).getD
        (p.nP + ctorsA.length + p.nIdx + 2 - 1 - i) default) := fun ψ => (hR ψ).okΓ
  have hvFss : ∀ ψ ρp, Sat V ((((fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ).take p.nP).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length → ∀ bs : List V,
        SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
          AnnotValid V (consList bs ρp) E) ∧
      (∀ j, j < ctorsA.length → ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) fs →
        FieldsValid (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map (·.2.2)) bs →
        ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i [],
          AnnotValid V (consList bs (consList (fs.take i) ρp)) E) := by
    intro ψ ρp hρ
    rw [hrdsE ψ, fixRecDataAV_take_nP (hlenPps ψ)] at hρ
    obtain ⟨-, -, -, hv, hEisV, hEsV⟩ := hframes ψ ρp hρ
    exact ⟨hv, hEsV, hEisV⟩
  have hleafF : ∀ (ψ : LevelParam → Nat) (ρ : Nat → V), WellDenotedV V ρ (A ψ) ∧
      interp V ρ (A ψ) ∈ˢ interp V ρ (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
        (recConcAV ctorsA.length p.nIdx)) := by
    intro ψ ρ
    rw [hA ψ]
    exact fixRecLeafFacts (hpre ψ) (hlenFs ψ) (hlenIds ψ) (hokΓ ψ) (fun ρ' => (hRD.okTy ψ ρ').2)
      (hvFss ψ) ρ
  have hAcl : ∀ ψ, Term.bvarsBelow 0 (A ψ).erase := by
    intro ψ
    rw [hA ψ]
    -- the fields are bounded at the parameters
    have hFssB : ∀ Fs ∈ fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0), FieldsBelow (0 + p.nP) Fs := by
      intro Fs hFs
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs
      have hjn : j < ctorsA.length := by rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj).1
      obtain ⟨cA, hjA⟩ := hcAof j hjn
      have hFj := hFsjD ψ j cA hjA
      rw [List.getD_eq_getElem?_getD, hj, Option.getD_some] at hFj
      rw [hFj]
      exact (DomsBelow.drop p.nP ((hcf j cA hjA).2.2.below ψ)).fields
    refine nativeRecAVI_below 0 (hRD.below ψ) (by rw [hRD.len ψ, hlenFs ψ, hlenIds ψ]; omega) rfl ?_
      (fun Fs hFs => by have := hFssB Fs hFs; rwa [Nat.zero_add] at this) (hTlsBelow ψ) (hEbelow ψ)
    -- the restricted chains are bounded
    have hEssB : ∀ j, j < (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).length →
        ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length = p.nIdx ∧
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
          Term.bvarsBelow (0 + p.nP + ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length)
            E.erase := by
      intro j hj
      rw [hlenFs ψ] at hj
      obtain ⟨cA, hjA⟩ := hcAof j hj
      obtain ⟨-, -, hD⟩ := hcf j cA hjA
      rw [hEsjD ψ j cA hjA, hFsjD ψ j cA hjA]
      refine ⟨hD.lenE ψ, fun E hE => ?_⟩
      have := hD.belowE ψ E hE
      rwa [show 0 + p.nP + (((dsF j ψ).drop p.nP).map (·.2.2)).length = p.nP + cA.2 from by
        simp [hD.len ψ]]
    intro Fs' hFs'
    rw [hlenIds ψ, hlenFs ψ] at hFs'
    have := rChains_below (d := p.nIdx + ctorsA.length + 1) (by omega) hFssB
      (fun j hj => hEssB j hj) Fs' hFs'
    refine fieldsBelow_mono (by rw [hlenIds ψ, hlenFs ψ]; omega) this
  -- the rule right-hand sides' gradedness
  have hRuleOk : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkLamsAV (fixRuleDataAV mp.base2 p.cvT.name ψ p.nP p.nIdx elimL
          ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP)
          (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) (dsF j ψ))
        (fixRuleCoreAV (pwBit ψ (Level.zeronessOf elimL)) (A ψ) p.nP cA.2 ctorsA.length j
          (Ix.Kernel.recIdxOf (ksF j)) (tssF j ψ) (eissF j ψ))) := by
    intro j cA hj ψ ρ
    obtain ⟨-, -, hD⟩ := hcf j cA hj
    have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
    have hrss : Ix.Kernel.recIdxOf (ksF j) = recIdx ((rssOfK ksF ctorsA.length).getD j []) cA.2 := by
      rw [rssOfK_getD hjn, ← hD.ksLen, recIdx_rsOf]
    have hpre' := hpre ψ
    rw [hrdsE ψ] at hpre'
    refine fixRuleOk rfl rfl (hbz ψ) (hlenPps ψ) (hlenIps ψ) (hn ψ) (hlenFs ψ) (hlenEs ψ) (hEs ψ)
      (hEisLen ψ) hpre' ?_ (by rw [hA ψ, hrdsE ψ]) (hAcl ψ) (fun ρ' => (hleafF ψ ρ').1) (hframes' ψ)
      (fun ρp hρp => ⟨(hframes ψ ρp hρp).2.2.2.1, (hframes ψ ρp hρp).2.2.2.2.1⟩) (hsingle ψ) (hprop ψ)
      (hjd ψ j cA hj) (hD.len ψ) (by rw [fssOfR_getElem?, hjd ψ j cA hj]; rfl)
      (by rw [essOfR_getElem?, hjd ψ j cA hj]; rfl) hrss (hEisjD ψ j cA hj) (hTlsjD ψ j cA hj)
      (hleafC j cA hj ψ)
      (mp.base2.cval_closedL cA.1.name ψ) (hiff j cA hj ψ) ρ
    have := hokΓ ψ; rw [hrdsE ψ] at this; exact this
  -- the leaf's level dependence
  have hAparams : ∀ ψ₁ ψ₂ : LevelParam → Nat, (∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q) → A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hφ
    have hlpsAll : ∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q :=
      fun q hq => hφ q (by rw [hRlps]; exact hRlps' q hq)
    have hcds : fixCtorDataList dsF esF ksF eissF tssF ψ₁ ctorsA 0
        = fixCtorDataList dsF esF ksF eissF tssF ψ₂ ctorsA 0 := by
      refine fixCtorDataList_congr ctorsA 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ := hcAof i hi
      obtain ⟨-, hlpsi, hDi⟩ := hcf i cAi hi'
      have hag : ∀ q ∈ cAi.1.levelParams, ψ₁ q = ψ₂ q := fun q hq => hlpsAll q (by rw [← hlpsi]; exact hq)
      exact ⟨(hDi.params ψ₁ ψ₂ hag).1, (hDi.params ψ₁ ψ₂ hag).2, hDi.eissParams ψ₁ ψ₂ hag,
        hDi.tssParams ψ₁ ψ₂ hag⟩
    have hpps : ppsAll ψ₁ = ppsAll ψ₂ :=
      (hFD.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsT]; exact hq))).1
    have hw : p.resSort.eval ψ₁ = p.resSort.eval ψ₂ :=
      (hFD.params ψ₁ ψ₂ (fun q hq => hlpsAll q (by rw [← hlpsT]; exact hq))).2
    have hℓ : elimL.eval ψ₁ = elimL.eval ψ₂ := by
      rw [← hElimL]
      cases hpl : p.large
      · simp [Ix.Kernel.structElimLevel, Level.eval]
      · simp only [Ix.Kernel.structElimLevel, if_true, Level.eval]
        exact hφ p.elim (by rw [hRlps]; exact helim hpl)
    have hs : sAV ψ₁ = sAV ψ₂ := by
      show fixSortAV elimL u cvRa.levelParams ψ₁ = fixSortAV elimL u cvRa.levelParams ψ₂
      unfold fixSortAV
      rw [hℓ, restrictΨ_congr hφ]
    rw [hA ψ₁, hA ψ₂, hℓ, hw, hcds, hpps, hRD.params ψ₁ ψ₂ hφ, hs]
  -- the cons head
  let c₀ : ConstantInfo md := .recInfo cvRa mI rP (Ix.Kernel.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss)
  have hcross : ∀ e : Expr md, ConsCrossAt c₀ e := fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hreadR : ∀ ψ : LevelParam → Nat,
      denoteMeta (acvalWith mp.base2.acval cvRa.name A) ⟨c₀ :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (fixRdsAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA ψ)
            (recConcAV ctorsA.length p.nIdx)) := fun ψ =>
    denoteMeta_cons_mono (c₀ := c₀) hfresh (hcross _) ψ 0 hcbR (hRD.read ψ)
  have hnresC : Ix.Kernel.reservedBasisNames.contains c₀.name = false := by
    show Ix.Kernel.reservedBasisNames.contains cvRa.name = false
    rw [hRname]; exact hnres
  have hpshapeC : c₀.name.isProjFnShape = false := by
    show cvRa.name.isProjFnShape = false
    rw [hRname]; exact hpshape
  refine ⟨sAV, ?_⟩
  refine declStep_preserves_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnresC ⟨_, _, _, _, rfl⟩
    (ConsHead.ofFresh hwf (fun ψ => hAcl ψ) hnresC
      (fun _ h => nomatch h)
      (fun cvR' mI' rP' rules heq r hr => by
        injection heq with h1 h2 h3 hrules
        subst h1 h2 h3 hrules
        obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
        obtain ⟨hf, -, hD⟩ := hcf j cA hj
        have hpl := List.all_eq_true.mp hplAll cA (List.mem_of_getElem? hj)
        obtain ⟨cbs, es, hres, -⟩ := hD.resid
        exact ⟨Ix.Kernel.RuleCtorOk.of_plain hf (by simp [Ix.Kernel.recRuleBits, hpl]) hpl
            (Ix.Kernel.Expr.ctorTeleOk_of hres (by rw [Ix.Kernel.Expr.getAppFn_mkAppN]; rfl)),
          fun hb => hb, fun hb => hb⟩))
    (fun ψ k => AnnotTerm.liftN_eq_self _ (Term.bvarsBelow.mono (Nat.zero_le k) (hAcl ψ)) 1)
    hAparams (fun ψ ρ => (hleafF ψ ρ).1.1) (fun ψ ρ => (hleafF ψ ρ).1.2) (fun ψ => ⟨_, hreadR ψ⟩)
    ?_ ?_ ?_ ?_
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact hRD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact (hleafF ψ ρ).2
  · -- `caps_ok`: the block claims no eta or unit law
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := c₀) (A := A) (T := p.cvT.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape
      exact hE T' cvT' caps' hf hne hcape hres
    · intro cvT caps' hf _
      have hfT' : (⟨c₀ :: env.consts⟩ : Env md).find? p.cvT.name = some (.indInfo cvS caps) := by
        rw [Ix.Kernel.Env.find?_cons, if_neg (fun h => hTR h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      have hcbT : ConstsBound env cvTa.type := constsBound_of_constsResolve _ hFD.cr
      refine hTlaws m₂ (fun n hn => ?_)
        (hFD.cross (c₀ := c₀) hfresh (hcross _) hcbT m₂ hac) (fun ψ => ?_) (fun j cA hj ψ => ?_)
      · rw [hac]
        exact acvalWith_ne hn
      · rw [hac]
        exact congrFun (acvalWith_ne hTR) ψ
      · obtain ⟨hf, -, -⟩ := hcf j cA hj
        have hCR : cA.1.name ≠ cvRa.name := by
          intro h; rw [h, hfresh] at hf; exact nomatch hf
        rw [hac]
        exact congrFun (acvalWith_ne hCR) ψ
  · -- `rec_rules`
    intro m₂ hac φ'
    refine recRules_cons_rec mp (c₀ := c₀) (A := A) hfresh rfl m₂ hac φ' ?_
    intro rl hrl hfire
    obtain ⟨j, cA, rhs, hj, hrhs, rfl⟩ := Ix.Kernel.sumRules_getElem? hrl
    by_cases hplain : Expr.recRulePlain cvRa.type mI rP p.nP cA.1.levelParams = true
    · have hrule : (Ix.Kernel.recRuleBits env.find? cvRa.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := p.nP,
              fire := if Expr.recRulePlain cvRa.type mI rP p.nP cA.1.levelParams then .plain
                else .inert,
              rhs := rhs, paramsBlind := true } : RecRule md)
          = ⟨cA.1.name, cA.2, p.nP, .plain, rhs,
             Ix.Kernel.recRuleKOf env.find? cA.1.name,
             Ix.Kernel.recRuleEtaOf env.find? cvRa.name cA.1.name, true⟩ := by
        simp [hplain, Ix.Kernel.recRuleBits]
      subst hElimL
      exact fixRecRuleLaw mp hmI hrP hRec hfT hlpsS hlpsT hstripT hopT hFD hlenK hks hcf hidxRes hRD
        hA hpre hAcl (fun ψ ρp hρp => by
          intro Fs hFs
          obtain ⟨j', hj'⟩ := List.getElem?_of_mem hFs
          have hjn' : j' < ctorsA.length := by
            rw [← hlenFs ψ]; exact (List.getElem?_eq_some_iff.mp hj').1
          have := ((hframes ψ ρp hρp).2.2.1 j' hjn').1
          rwa [List.getD_eq_getElem?_getD, hj'] at this)
        hleafC hiff hprop hj hrhs (hRuleOk j cA hj) hfresh hrule m₂ hac φ'
    · exfalso
      apply hfire
      simp [hplain, Ix.Kernel.recRuleBits]


/-- The P step at the recursor's cons from its stage run: `stageFixRecJ` at the kernel's runs. -/
theorem stageFixRec {p : NativeParts md} (hE : Ix.Kernel.EtaFamiliesClosedExcept env p.cvT.name)
    (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {cvTa cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhss : List (Expr md)} {mI rP : Nat}
    (hmI : mI = p.nP + 1 + ctorsA.length + p.nIdx) (hrP : rP = p.nP + 1 + ctorsA.length)
    (hmIp : p.majorIdx = mI) (hrPp : p.rulePrefix = rP)
    (hRec : Ix.Kernel.checkNativeRec (Ix.Kernel.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    (hplAll : ctorsA.all (fun c => Expr.recRulePlain cvRa.type mI rP p.nP c.1.levelParams) = true)
    {bsT : List (Expr md × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {caps : IndCaps md}
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    -- the block's own capability laws at the cons (task #210 Part A),
    -- at any carrier agreeing with this one off the recursor's name
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    (hTlaws : ∀ m₂ : EnvModel V ⟨.recInfo cvRa mI rP
        (Ix.Kernel.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss) :: env.consts⟩,
      (∀ n, n ≠ cvRa.name → m₂.acval n = mp.base2.acval n) →
      FormerData m₂ cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m₂.acval p.cvT.name ψ = mp.base2.acval p.cvT.name ψ) →
      (∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
        ∀ ψ, m₂.acval cA.1.name ψ = mp.base2.acval cA.1.name ψ) →
      CapsLawsAt m₂ p.cvT.name cvTa caps)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {tfvs : List (Expr md)} {trest : Expr md}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    (helim : p.large = true → p.elim ∈ p.cvR.levelParams)
    (hRlps' : ∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams)
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env md} {idxF : Nat → List (Expr md)} {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List (Expr md)} {xrestF : Nat → Expr md}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF i cA)
    (hidxRes : ∀ j cA, ctorsA[j]? = some cA → ∀ e ∈ idxF j, e.constsResolve env = true)
    {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    (_hUparams : ∀ ψ₁ ψ₂ : LevelParam → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) → uAV ψ₁ = uAV ψ₂)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = nativeTyAVI (uAV ψ) (p.resSort.eval ψ) (ppsAll ψ) (((ppsAll ψ).drop p.nP).map (·.2.2))
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, mp.base2.acval cA.1.name ψ
      = sumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : LevelParam → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hframes : ∀ (ψ : LevelParam → Nat) (ρp : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρp →
      XChainsOk (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
        (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      ChainsRealI (fixFamI (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) p.nIdx
          (rssOfK ksF ctorsA.length) (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
          (fssZ ψ)
          (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)))
        (uAV ψ) (p.resSort.eval ψ) ρp (((ppsAll ψ).drop p.nP).map (·.2.2)) (rssOfK ksF ctorsA.length)
        (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (fssZ ψ)
        (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0))
        (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        FieldsOkB (p.resSort.eval ψ) ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) ∧
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
          (∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
            WellDenoted V (consList bs ρp) E) ∧
          SpineFit ρp (((ppsAll ψ).drop p.nP).map (·.2.2))
            (idxValsAt ρp ((essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs)) ∧
      SumFieldsValid ρp (fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)) ∧
      (∀ j, j < ctorsA.length →
        ∀ i ∈ recIdx ((rssOfK ksF ctorsA.length).getD j [])
          ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).length,
        ∀ fs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) fs →
        FieldsValid (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map (·.2.2)) ∧
        ∀ bs : List V, SpineFit (consList (fs.take i) ρp)
          ((((tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i []).map (·.2.2)) bs →
        ∀ E ∈ ((eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []).getD i [],
          AnnotValid V (consList bs (consList (fs.take i) ρp)) E) ∧
      (∀ j, j < ctorsA.length →
        ∀ bs : List V, SpineFit ρp ((fssOfR p.nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j []) bs →
        ∀ E ∈ (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).getD j [],
          AnnotValid V (consList bs ρp) E))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2) :
    ∃ (sAV : (LevelParam → Nat) → Nat)
      (mp' : EnvModelM V μ ⟨.recInfo cvRa mI rP (Ix.Kernel.sumRules env.find? cvRa.name p.nP mI rP cvRa.type ctorsA rhss)
        :: env.consts⟩),
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fixLeafAV mp.base2 p ppsAll dsF esF ksF eissF tssF ctorsA sAV) :=
  stageFixRecJ hE mp (judgeSound_runJ hμ mp F) (sortClaim_runJ hμ mp F) hmI hrP hmIp hrPp
    (Ix.Kernel.Semantics.nativeRecRunJ_of_run hRec) hplAll hstripT hfT hTlaws hlpsT hlpsT hopT helim hRlps'
    hFD hlenK hks hcf hidxRes _hUparams hleafT hleafC hiff hframes
    (fun hl => (hwl hl).imp_left fun hnz φ => Ix.Kernel.Level.isNeverZero_sound φ _ hnz)

end Ix.Kernel.Model
