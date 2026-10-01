module

public import ConLeche.Model.Inductives.FixStageRec
public import ConLeche.Model.Inductives.FixStageFormer
public import ConLeche.Model.Inductives.FixCtorsLoop
public import ConLeche.Model.Inductives.FixCtorCross
public import ConLeche.Model.Inductives.FixWitness
public section

/-!
# Kit for the direct recursive install's assembly (task #188)

The pieces `declNative` joins: the two routes' data lists
identified (`fssOfR_fixCtorDataList`, `essOfR_fixCtorDataList`), a
read spine transported along pointwise-equal readings
(`DenoteMetaSpine.congr`), the former's index telescope valid at the
parameter frame (`idxValid_of`, beside `idxOk_of`), and the chain
validity facts of a recursive constructor (`fixChainValidFacts_of`,
beside `fixChainFacts_of`: the validity halves of the shadow
gradings).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The two routes' data lists -/

omit [SetTheory V] in
/-- The recursive route's field chains are the sum route's. -/
theorem fssOfR_fixCtorDataList (nP : Nat) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs k) = fssOf nP (ctorDataList dsF esF ψ cs k)
  | [], _ => rfl
  | c :: cs, k => by
    show _ :: fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1))
      = _ :: fssOf nP (ctorDataList dsF esF ψ cs (k + 1))
    rw [fssOfR_fixCtorDataList nP dsF esF ksF eissF tssF ψ cs (k + 1)]

omit [SetTheory V] in
/-- The recursive route's index readings are the sum route's. -/
theorem essOfR_fixCtorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs k) = essOf (ctorDataList dsF esF ψ cs k)
  | [], _ => rfl
  | c :: cs, k => by
    show _ :: essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1))
      = _ :: essOf (ctorDataList dsF esF ψ cs (k + 1))
    rw [essOfR_fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1)]

/-! ## Read spines -/

/-- A read spine transports along pointwise-equal readings. -/
theorem DenoteMetaSpine.congr {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval₁ env φ d as vs →
      (∀ a ∈ as, denoteMeta acval₁ env φ d a = denoteMeta acval₂ env φ d a) →
      DenoteMetaSpine acval₂ env φ d as vs
  | [], _, .nil, _ => .nil
  | a :: as, _ :: vs, .cons ha h, heq =>
    .cons (by rw [← heq a List.mem_cons_self]; exact ha)
      (DenoteMetaSpine.congr h fun a' ha' => heq a' (List.mem_cons_of_mem _ ha'))

/-! ## The index telescope, valid -/

/-- **The former's index telescope**, valid at the parameter frame
(beside `idxOk_of`). -/
theorem idxValid_of (mp : EnvModelM V μ env)
    {nP nIdx : Nat} {resSort : Level} {cvTa : ConstantVal} {T : Name}
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvTa caps))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, trest))
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp) :
    FieldsValid ρp (((ppsAll ψ).drop nP).map (·.2.2)) := by
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  have hT : Opened mp.base2 ψ (nP + nIdx) cvTa.type tfvs trest
      (((ppsAll ψ).map (·.2.2)).reverse) (.sort (resSort.eval ψ)) :=
    opened_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
  have hΓ : (((ppsAll ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  have hρp' : Sat V ((((ppsAll ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_fields_eq (hFD.len ψ) nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
    exact hρp
  have hv := fieldsValid_of_frame rfl hΓ hT.okΓ 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hv
  exact hv

/-! ## The chain validity facts -/

/-- **The walk's validity inputs**, from a recursive constructor's
data at a carrier storing the former as a λ-tower over the parameters
(the validity halves of the shadow gradings). -/
theorem fixChainValidFacts_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp) :
    ChainValidFacts nP nF ρp ks (tss ψ) (((ds ψ).drop nP).map (·.2.2)) (Eiss ψ) (Es ψ) := by
  have hlenDs := hD.len ψ
  -- the parameter frames identified
  have hiff := (ctorFramesGen hμ mp hCtor hfT hProp hFD hD.toCtorDataI hleafT).1 ψ ρp
  have hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp := hiff.mp hρp
  -- the shadow gradings
  obtain ⟨hkey, hkeyR⟩ := fixShadowGrading hμ mp hCtor hProp hD ψ
  refine ⟨?_, ?_⟩
  · intro i hi as' hsp'
    have hsat : Sat V ((shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop
        (nP + nF - (nP + i))) (consList as' ρp) := by
      rw [shadowCtx_drop_fields hlenDs (Nat.le_of_lt hi)]
      exact sat_of_spineFit hρp' hsp'
    obtain ⟨hokP, -⟩ := hkey (nP + i) (by omega) _ hsat
    rw [reverse_getD_field hlenDs hi] at hokP
    refine ⟨hokP.2, fun hr => ?_⟩
    have hk := hr.2
    rw [Nat.add_sub_cancel_left] at hk
    rcases hk with hk | hk
    · -- a finitary field: no telescope, the readings at the spine
      rw [hD.tssNone ψ i (by rw [hk]; intro h; cases h)]
      have hentry := hD.recEntry ψ i hk hi
      rw [drop_map_getD hlenDs hi, hentry] at hokP
      obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hokP.2
      refine ⟨trivial, fun bs hbs E hE => ?_⟩
      cases bs with
      | nil => simpa using hargs E (List.mem_append_right _ hE)
      | cons b bs => exact hbs.elim
    · -- a reflexive field (task #202): the Π-tower's pieces
      have hentry := hD.reflEntry ψ i hk hi
      rw [drop_map_getD hlenDs hi, hentry] at hokP
      obtain ⟨hTV, hB⟩ := AnnotValid_mkPisAV_inv hokP.2
      refine ⟨hTV, fun bs hbs E hE => ?_⟩
      have := hB bs hbs
      rw [← consList_append] at this
      obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv this
      exact hargs E (List.mem_append_right _ hE)
  · intro as' hsp' E hE
    have hsat : Sat V (shadowCtx nP ks (nP + nF) (((ds ψ).map (·.2.2)).reverse))
        (consList as' ρp) := by
      have := shadowCtx_drop_fields (ks := ks) hlenDs (Nat.le_refl nF)
      rw [Nat.sub_self, List.drop_zero,
        List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at this
      rw [this]
      exact sat_of_spineFit hρp' hsp'
    have hokR := hkeyR _ hsat
    unfold ctorBodyAVI at hokR
    obtain ⟨-, hargs⟩ := AnnotValid.mkAppN_inv hokR.2
    exact hargs E (List.mem_append_right _ hE)

/-! ## The data lists, congruent in one component -/

omit [SetTheory V] in
/-- The per-field index expressions depend on the data only through
their own component. -/
theorem eissOfR_fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF₁ esF₂ : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF₁ tssF₂ : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      (∀ i, i < cs.length → eissF₁ (k + i) ψ = eissF₂ (k + i) ψ) →
      eissOfR (fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ cs k)
        = eissOfR (fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ cs k)
  | [], _, _ => rfl
  | c :: cs, k, h => by
    show eissF₁ k ψ :: eissOfR (fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ cs (k + 1))
      = eissF₂ k ψ :: eissOfR (fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ cs (k + 1))
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    congr 1
    exact eissOfR_fixCtorDataList_congr (dsF₁ := dsF₁) (dsF₂ := dsF₂) (esF₁ := esF₁)
      (esF₂ := esF₂) cs (k + 1) fun i hi => by
        rw [Nat.add_right_comm]; exact h (i + 1) (by simp; omega)

omit [SetTheory V] in
/-- The per-field telescopes depend on the data only through their own
component (task #202). -/
theorem tlssOfR_fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF₁ esF₂ : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF₁ tssF₂ : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      (∀ i, i < cs.length → tssF₁ (k + i) ψ = tssF₂ (k + i) ψ) →
      tlssOfR (fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ cs k)
        = tlssOfR (fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ cs k)
  | [], _, _ => rfl
  | c :: cs, k, h => by
    show tssF₁ k ψ :: tlssOfR (fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ cs (k + 1))
      = tssF₂ k ψ :: tlssOfR (fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ cs (k + 1))
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    congr 1
    exact tlssOfR_fixCtorDataList_congr (dsF₁ := dsF₁) (dsF₂ := dsF₂) (esF₁ := esF₁)
      (esF₂ := esF₂) (eissF₁ := eissF₁) (eissF₂ := eissF₂) cs (k + 1) fun i hi => by
        rw [Nat.add_right_comm]; exact h (i + 1) (by simp; omega)

omit [SetTheory V] in
/-- The index readings depend on the data only through their own
component. -/
theorem essOfR_fixCtorDataList_congr {dsF₁ dsF₂ : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF₁ esF₂ : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF₁ eissF₂ : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF₁ tssF₂ : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat} :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      (∀ i, i < cs.length → esF₁ (k + i) ψ = esF₂ (k + i) ψ) →
      essOfR (fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ cs k)
        = essOfR (fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ cs k)
  | [], _, _ => rfl
  | c :: cs, k, h => by
    show esF₁ k ψ :: essOfR (fixCtorDataList dsF₁ esF₁ ksF eissF₁ tssF₁ ψ cs (k + 1))
      = esF₂ k ψ :: essOfR (fixCtorDataList dsF₂ esF₂ ksF eissF₂ tssF₂ ψ cs (k + 1))
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    congr 1
    exact essOfR_fixCtorDataList_congr (dsF₁ := dsF₁) (dsF₂ := dsF₂) (eissF₁ := eissF₁)
      (eissF₂ := eissF₂) cs (k + 1) fun i hi => by
        rw [Nat.add_right_comm]; exact h (i + 1) (by simp; omega)

omit [SetTheory V] in
theorem fssOfR_fixCtorDataList_getD {nP : Nat} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j []
      = ((dsF j ψ).drop nP).map (·.2.2) := by
  rw [List.getD_eq_getElem?_getD, fssOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

omit [SetTheory V] in
theorem essOfR_fixCtorDataList_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j [] = esF j ψ := by
  rw [List.getD_eq_getElem?_getD, essOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

omit [SetTheory V] in
theorem eissOfR_fixCtorDataList_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (eissOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j [] = eissF j ψ := by
  rw [List.getD_eq_getElem?_getD, eissOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

omit [SetTheory V] in
theorem tlssOfR_fixCtorDataList_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j [] = tssF j ψ := by
  rw [List.getD_eq_getElem?_getD, tlssOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

/-! ## The X-chains of all constructors -/

/-- **The functor's premise and the chains' validity**, from the
per-constructor chain facts. -/
theorem xChainsOk_of {u w nP n : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}
    {ksF : Nat → List RecFieldKind} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)}
    (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids) (hlenF : Fss.length = n)
    (hrss : ∀ j, j < n → rss.getD j [] = rsOf (ksF j))
    (hC : ∀ j, j < n → ChainFacts u w nP (Fss.getD j []).length ρp Ids (ksF j) (tlss.getD j [])
      (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
    (hCV : ∀ j, j < n → ChainValidFacts nP (Fss.getD j []).length ρp (ksF j) (tlss.getD j [])
      (Fss.getD j []) (Eiss.getD j []) (Ess.getD j [])) :
    XChainsOk u w ρp Ids rss tlss Eiss Fss Ess ∧
    ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
      SumFieldsValid (cons t (cons X ρp)) (chainsXI u Ids Ids.length rss tlss Eiss Fss Ess) := by
  have hmem : ∀ chain ∈ chainsXI u Ids Ids.length rss tlss Eiss Fss Ess, ∃ j, j < n ∧
      chain = chainXI u Ids Ids.length (rsOf (ksF j)) (tlss.getD j []) (Eiss.getD j [])
        (Fss.getD j []) (Ess.getD j []) := by
    intro chain hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    rw [chainsXI_getElem?] at hj
    split at hj
    · next hjF =>
      refine ⟨j, by omega, ?_⟩
      rw [← hrss j (by omega)]
      exact (Option.some.inj hj).symm
    · exact nomatch hj
  have hok : FixChainsOkI u w ρp Ids Ids.length rss tlss Eiss Fss Ess := by
    intro X hX t ht chain hc
    obtain ⟨j, hj, rfl⟩ := hmem chain hc
    exact (fixChain_of hI hX ht (hC j hj)).1
  -- the closure witness: the container instance, or the top family at `w = 0`
  have hclosed : ∃ L, IsClosedFam w (idxSet u ρp Ids)
      (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss Ess) L := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · exact fixFunVI_closed_zero hok
    · exact fixClosed_of (Nat.pos_iff_ne_zero.mp hw) hI (fun j hj => hrss j (by omega))
        (fun j hj => hC j (by omega))
  refine ⟨⟨hI, hok, fun X hX t ht j hj => ?_, hclosed⟩,
    fun X hX t ht chain hc => ?_⟩
  · rw [hrss j (by omega)]
    exact (fixChain_of hI hX ht (hC j (by omega))).2
  · obtain ⟨j, hj, rfl⟩ := hmem chain hc
    exact fixChainValid_of hI hIV hX (hC j hj) (hCV j hj)

/-- The X-chains are closed under the parameters, the family and the
tuple. -/
theorem chainsXI_below_of {u nP nIdx n : Nat} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}
    (hIds : FieldsBelow nP Ids) (hlenF : Fss.length = n)
    (hTls : ∀ j, j < n → ∀ i, DomsBelow (nP + i) ((tlss.getD j []).getD i []))
    (hEis : ∀ j, j < n → ∀ i, ∀ E ∈ (Eiss.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase)
    (hFs : ∀ j, j < n → FieldsBelow nP (Fss.getD j []))
    (hEsLen : ∀ j, j < n → (Ess.getD j []).length = nIdx)
    (hEs : ∀ j, j < n → ∀ E ∈ Ess.getD j [],
      Term.bvarsBelow (nP + (Fss.getD j []).length) E.erase) :
    ∀ chain ∈ chainsXI u Ids nIdx rss tlss Eiss Fss Ess, FieldsBelow (nP + 2) chain := by
  intro chain hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  rw [chainsXI_getElem?] at hj
  split at hj
  · next hjF =>
    obtain rfl := Option.some.inj hj
    have hjn : j < n := by omega
    exact chainXI_below hIds (hTls j hjn) (hEis j hjn) (hFs j hjn) (hEsLen j hjn) (hEs j hjn)
  · exact nomatch hj

/-! ## The constructors' data, picked -/

/-- A recursive constructor's data, bundled for the choice. -/
structure FixCtorPick where
  idxArgs : List Expr
  ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)
  Es : (Name → Nat) → List AnnotTerm
  srcs : List (Option Nat)
  fvsP : List Expr
  xFvs : List Expr
  xrest : Expr
  Eiss : (Name → Nat) → List (List AnnotTerm)
  tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))

/-- `fixCtorData_of`, its witnesses bundled. -/
theorem fixCtorPick_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {ks : List RecFieldKind}
    {sorts : List Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hks : ks.length = nF)
    (hopened : ConLeche.nativeOpenedOk env₀ T lps nP nIdx cvCa.type nF ks = true) :
    ∃ q : FixCtorPick, FixCtorDataI mp.base2 env₀ T lps cvCa nP nF nIdx resSort isProp large
      q.idxArgs q.ds q.Es q.srcs ks q.fvsP q.xFvs q.xrest q.Eiss q.tss := by
  obtain ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, tss, hD⟩ :=
    fixCtorData_of hμ mp hCtor hfT hlpsT hstripT hks hopened
  exact ⟨⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, Eiss, tss⟩, hD⟩

/-- **The constructors' data functions** at a carrier storing the
former: every constructor's recursive data, its kind list the guard's. -/
theorem fixCtorFuns_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvTa : ConstantVal} {env₀ env₁ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List RecFieldKind)}
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort))
    (hFOk : ConLeche.nativeFieldsOk env₀ T lps nP nIdx ctorsA kinds = true)
    (hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx
          resSort isProp large c.1 cA.2 cvTa = .ok (cA.1, sorts)) :
    ∃ (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        FixCtorDataI mp.base2 env₀ T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j)
          (esF j) (srcsF j) (kinds.getD j []) (fvsPF j) (xFvsF j) (xrestF j) (eissF j) (tssF j) := by
  have hex : ∀ j : Nat, ∃ q : FixCtorPick, ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      FixCtorDataI mp.base2 env₀ T lps cA.1 nP cA.2 nIdx resSort isProp large q.idxArgs q.ds
        q.Es q.srcs (kinds.getD j []) q.fvsP q.xFvs q.xrest q.Eiss q.tss := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨⟨[], fun _ => [], fun _ => [], [], [], [], .bvar 0, fun _ => [], fun _ => []⟩,
        fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, sorts, hCtor⟩ := hrunOf j cA hj
      obtain ⟨ks, hks, hksLen, hopened⟩ := ConLeche.nativeFieldsOk_inv hFOk hj
      have hksD : kinds.getD j [] = ks := by rw [List.getD_eq_getElem?_getD, hks]; rfl
      obtain ⟨q, hq⟩ := fixCtorPick_of hμ mp hCtor hfT hlpsT hstripT hksLen hopened
      refine ⟨q, fun cA' h => ?_⟩
      obtain rfl := Option.some.inj h
      rw [hksD]
      exact hq
  let q : Nat → FixCtorPick := fun j => Classical.choose (hex j)
  exact ⟨fun j => (q j).idxArgs, fun j => (q j).ds, fun j => (q j).Es, fun j => (q j).srcs,
    fun j => (q j).fvsP, fun j => (q j).xFvs, fun j => (q j).xrest, fun j => (q j).Eiss,
    fun j => (q j).tss, fun j => Classical.choose_spec (hex j)⟩

/-! ## The data at two carriers -/

/-- **A recursive constructor's data at two carriers** differing only
at the former: the openings and the residual's index arguments are
syntactic, the index readings, the recursive slots' index expressions
and the ordinary fields' domains read the same (none mentions the
former). -/
theorem fixCtorDataI_ident {acval : Name → (Name → Nat) → AnnotTerm} {T : Name}
    {A₁ A₂ : (Name → Nat) → AnnotTerm} {env₀ : Env}
    {m₁ m₂ : EnvModel V env} (hac₁ : m₁.acval = acvalWith acval T A₁)
    (hac₂ : m₂.acval = acvalWith acval T A₂) (hfresh : env₀.find? T = none)
    {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idx₁ idx₂ : List Expr}
    {ds₁ ds₂ : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es₁ Es₂ : (Name → Nat) → List AnnotTerm}
    {srcs₁ srcs₂ : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP₁ fvsP₂ xFvs₁ xFvs₂ : List Expr} {xrest₁ xrest₂ : Expr}
    {Eiss₁ Eiss₂ : (Name → Nat) → List (List AnnotTerm)}
    {tss₁ tss₂ : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h₁ : FixCtorDataI m₁ env₀ T lps cvC nP nF nIdx resSort isProp large idx₁ ds₁ Es₁ srcs₁ ks
      fvsP₁ xFvs₁ xrest₁ Eiss₁ tss₁)
    (h₂ : FixCtorDataI m₂ env₀ T lps cvC nP nF nIdx resSort isProp large idx₂ ds₂ Es₂ srcs₂ ks
      fvsP₂ xFvs₂ xrest₂ Eiss₂ tss₂) :
    idx₁ = idx₂ ∧ fvsP₁ = fvsP₂ ∧ xFvs₁ = xFvs₂ ∧ xrest₁ = xrest₂ ∧
    (∀ ψ, Es₁ ψ = Es₂ ψ) ∧ (∀ ψ, Eiss₁ ψ = Eiss₂ ψ) ∧ (∀ ψ, tss₁ ψ = tss₂ ψ) ∧
    ∀ ψ i, i < nF → ks.getD i .ordinary ≠ .recursive → ks.getD i .ordinary ≠ .reflexive →
      ((ds₁ ψ).getD (nP + i) default).2.2 = ((ds₂ ψ).getD (nP + i) default).2.2 := by
  obtain ⟨crest₁, hopP₁, hopX₁⟩ := h₁.opens
  obtain ⟨crest₂, hopP₂, hopX₂⟩ := h₂.opens
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP₁.symm.trans hopP₂))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopX₁.symm.trans hopX₂))
  have hidx : idx₁ = idx₂ := by rw [h₁.idxEq, h₂.idxEq]
  subst hidx
  -- a reflexive field's opening at the two carriers is the same, its
  -- telescope domains and index expressions resolving before the block
  have hrefl : ∀ ψ i x, xFvs₁[i]? = some x → ks.getD i .ordinary = .reflexive →
      ((tss₁ ψ).getD i []).length = ((tss₂ ψ).getD i []).length ∧
      ∃ afvs body,
        openPisAtFvars ((tss₁ ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a →
          ((tss₁ ψ).getD i []).getD k default = ((tss₂ ψ).getD i []).getD k default) ∧
        DenoteMetaSpine m₁.acval env ψ (nP + i + ((tss₁ ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss₁ ψ).getD i []) ∧
        DenoteMetaSpine m₂.acval env ψ (nP + i + ((tss₁ ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss₂ ψ).getD i []) ∧
        (∀ e ∈ body.getAppArgs.drop nP, e.constsResolve env₀ = true) := by
    intro ψ i x hx hk
    obtain ⟨afvs, body, hop₁, hlen₁, hdoms₁, hsp₁⟩ := h₁.reflOpen ψ i x hx hk
    obtain ⟨afvs₂, body₂, hop₂, hlen₂, hdoms₂, hsp₂⟩ := h₂.reflOpen ψ i x hx hk
    have hlen : ((tss₁ ψ).getD i []).length = ((tss₂ ψ).getD i []).length := by
      rw [hlen₁, hlen₂]
    rw [← hlen] at hop₂ hsp₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop₁.symm.trans hop₂))
    obtain ⟨afvs', body', hop', -, hresA, -, -, -, hresB, -, -⟩ := h₁.opened.reflF i x hx hk
    rw [← hlen₁] at hop'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop₁.symm.trans hop'))
    refine ⟨hlen, afvs, body, hop₁, fun k a hka => ?_, hsp₁, hsp₂, hresB⟩
    have hd₁ := hdoms₁ k a hka
    have hd₂ := hdoms₂ k a hka
    rw [hac₁] at hd₁
    rw [hac₂] at hd₂
    rw [denoteMeta_acvalWith_unmentioned₂ (A₂ := A₂) hfresh (nP + i + k) _
      (hresA a (List.mem_of_getElem? hka))] at hd₁
    have h22 := Option.some.inj (hd₁.symm.trans hd₂)
    have hlenA := openPisAtFvars_length _ hop₁
    have hkA : k < afvs.length := (List.getElem?_eq_some_iff.mp hka).1
    have hB₁ := h₁.tssBits ψ i
    have hB₂ := h₂.tssBits ψ i
    have hP₁ := h₁.tssPiBits ψ i
    have hP₂ := h₂.tssPiBits ψ i
    generalize hL₁ : (tss₁ ψ).getD i [] = L₁ at hlen hlenA hB₁ hP₁ h22 ⊢
    generalize hL₂ : (tss₂ ψ).getD i [] = L₂ at hlen hB₂ hP₂ h22 ⊢
    have hk₁ : k < L₁.length := by rw [← hlenA]; exact hkA
    have hk₂ : k < L₂.length := by rw [← hlen]; exact hk₁
    have hm₁ : L₁.getD k default ∈ L₁ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₁]; exact List.getElem_mem hk₁
    have hm₂ : L₂.getD k default ∈ L₂ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk₂]; exact List.getElem_mem hk₂
    obtain ⟨hb₁, hle₁⟩ := hP₁ _ hm₁
    obtain ⟨hb₂, hle₂⟩ := hP₂ _ hm₂
    have hz := (hB₁ _ hm₁).trans (hB₂ _ hm₂).symm
    have h21 : (L₁.getD k default).2.1 = (L₂.getD k default).2.1 := by
      rcases Nat.lt_or_ge (L₁.getD k default).2.1 1 with hlt | hge
      · have h0 : (L₁.getD k default).2.1 = 0 := by omega
        rw [h0, (hz.mp h0).symm]
      · have h1 : (L₁.getD k default).2.1 = 1 := by omega
        have hne : (L₂.getD k default).2.1 ≠ 0 := fun h0 => by
          have := hz.mpr h0; omega
        omega
    exact Prod.ext (hb₁.trans hb₂.symm) (Prod.ext h21 h22)
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro ψ
    refine CtorDataI.Es_eq hac₁ hac₂ hfresh h₁.toCtorDataI h₂.toCtorDataI ?_ ψ
    rw [h₁.idxEq]
    exact h₁.opened.residRes
  · intro ψ
    have hl₁ := h₁.eissLen ψ
    have hl₂ := h₂.eissLen ψ
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i nF with hi | hi
    · have hx : xFvs₁[i]? = some (xFvs₁[i]'(by rw [h₁.xLen]; exact hi)) :=
        List.getElem?_eq_getElem _
      have hD : (Eiss₁ ψ).getD i [] = (Eiss₂ ψ).getD i [] := by
        rcases h₁.opened.kinds i hi with hk | hk | hk
        · rw [h₁.ordNone ψ i (by rw [hk]; exact nofun) (by rw [hk]; exact nofun),
            h₂.ordNone ψ i (by rw [hk]; exact nofun) (by rw [hk]; exact nofun)]
        · have hr₁ := h₁.eisRead ψ i _ hx hk
          have hr₂ := h₂.eisRead ψ i _ hx hk
          obtain ⟨-, -, -, hres, -, -⟩ := h₁.opened.recF i _ hx hk
          rw [hac₁] at hr₁
          rw [hac₂] at hr₂
          have hr₁' := DenoteMetaSpine.congr hr₁ fun a ha =>
            denoteMeta_acvalWith_unmentioned₂ (A₂ := A₂) hfresh (nP + i) a (hres a ha)
          exact DenoteMetaSpine.unique hr₁' hr₂
        · obtain ⟨-, afvs, body, -, -, hr₁, hr₂, hres⟩ := hrefl ψ i _ hx hk
          rw [hac₁] at hr₁
          rw [hac₂] at hr₂
          have hr₁' := DenoteMetaSpine.congr hr₁ fun a ha =>
            denoteMeta_acvalWith_unmentioned₂ (A₂ := A₂) hfresh _ a (hres a ha)
          exact DenoteMetaSpine.unique hr₁' hr₂
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hD
      exact hD
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro ψ
    have hl₁ := h₁.tssLen ψ
    have hl₂ := h₂.tssLen ψ
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i nF with hi | hi
    · have hx : xFvs₁[i]? = some (xFvs₁[i]'(by rw [h₁.xLen]; exact hi)) :=
        List.getElem?_eq_getElem _
      have hD : (tss₁ ψ).getD i [] = (tss₂ ψ).getD i [] := by
        by_cases hk : ks.getD i .ordinary = .reflexive
        · obtain ⟨hlen, afvs, body, hop, hdoms, -, -, -⟩ := hrefl ψ i _ hx hk
          have hlenA := openPisAtFvars_length _ hop
          generalize hL₁ : (tss₁ ψ).getD i [] = L₁ at hlen hlenA hdoms ⊢
          generalize hL₂ : (tss₂ ψ).getD i [] = L₂ at hlen hdoms ⊢
          apply List.ext_getElem
          · exact hlen
          · intro k hk₁ hk₂
            obtain ⟨a, ha⟩ : ∃ a, afvs[k]? = some a :=
              ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; exact hk₁)⟩
            have := hdoms k a ha
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hk₁, List.getElem?_eq_getElem hk₂, Option.getD_some,
              Option.getD_some] at this
            exact this
        · rw [h₁.tssNone ψ i hk, h₂.tssNone ψ i hk]
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hD
      exact hD
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro ψ i hi hnr hnf
    have hx : xFvs₁[i]? = some (xFvs₁[i]'(by rw [h₁.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hk : ks.getD i .ordinary = .ordinary := by
      rcases h₁.opened.kinds i hi with hk | hk | hk
      · exact hk
      · exact absurd hk hnr
      · exact absurd hk hnf
    have hd₁ := h₁.domRead ψ i _ hx
    have hd₂ := h₂.domRead ψ i _ hx
    rw [hac₁] at hd₁
    rw [hac₂] at hd₂
    rw [denoteMeta_acvalWith_unmentioned₂ (A₂ := A₂) hfresh (nP + i) _ (h₁.opened.ord i _ hx hk)] at hd₁
    exact Option.some.inj (hd₁.symm.trans hd₂)

end ConLeche.Model
