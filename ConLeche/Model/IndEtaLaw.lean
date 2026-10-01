module

public import ConLeche.Model.IndUnitLaw
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.VClosed
import ConLeche.Model.Annot.BitLevels
public section

/-!
# The η key, P tier (task #161, IND TIER part 2, item 1a)

`etaLawKeyS`'s transpose (`Install/EtaLawS.lean:108`): the checked
`T._model.eta` theorem, fired at a fitting parameter spine and a member
of the family, yields the stored family's `EtaLaw`.

The skeleton is `memberUnitLaw`'s — the same four moves, one member
binder instead of two — and the two deltas are exactly v1's:

* **`etaFields = 0`.** `capsOk_cons_member` only ever leaves the η row
  open at a block former with no projection slots (part 1's finding 5),
  so `etaFabArgsV val T ts x 0 = ts ++ [] = ts` and the fabricated
  spine *is* the parameter spine.  No projection leaf is read, and
  `etaLawKeyS`'s whole `hvP`/`projSpinesV` half evaporates.
* **The fabricated side is typed by no check.**  This is v1's finding 4,
  and it transposes verbatim: `checkEtaThm` is a pure `Bool` shape
  match with no side certification, so nothing says the constructor
  application inhabits the type slot.  v1 recovers it from `Eq`-slot
  rigidity (`EqLawV.dom`) against the statement's own truthfulness;
  `eqThird_mem` below is that argument one currency over, and it is the
  P tier's second and last use of rigidity (the first, `eqSlot_univ`,
  every `Eq` statement needs).

**The valuation identifications are premises, as in v1.**  `etaLawKeyS`
takes `hvT`/`hvC`/`hvP` — "the public/model valuation identifications
(install-supplied)".  At the P tier they are *derived* here from
`BlockAcvalInstalled` plus the two block-membership facts the η split
now carries, which is why those were added to `MemberEtaLaw`: the law's
subject is the *public* leaf and every pin names the `_model` one, and
`BlockAcvalInstalled` is the only bridge between them.  The cons's own
former is the case where the bridge is the install itself
(`acvalWith_self`), and a stored block former is the case where it is
the invariant (`hIA`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps ReducibilityHint BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## `Eq`-slot rigidity, second use -/

/-- **The `Eq` spine's third slot inhabits the type slot** —
`EqLawV.dom`'s P counterpart, and v1's finding-4 repair one currency
over.  The fabricated constructor application is typed by no
`--verified` check; what types it is the *pinned* `Eq` former's own
graph, against the statement's grading. -/
theorem eqThird_mem (mp : EnvModelM V μ env)
    (heqfE : env.find? eqName = some eqA) (χ : Name → Nat)
    {σ : Nat → V} {Sa la ra : AnnotTerm}
    (hok : WellDenotedV V σ
      (.app (.app (.app (mp.base2.acval eqName χ) Sa) la) ra))
    (hS : interp V σ Sa ∈ˢ (univ (χ uN) : V))
    (hl : interp V σ la ∈ˢ interp V σ Sa) :
    interp V σ ra ∈ˢ interp V σ Sa := by
  obtain ⟨ea, hea, -, hmem⟩ := mp.acval_memType heqfE χ
  rw [show (eqA : ConstantInfo).toConstantVal.type
      = eqA.toConstantVal.type from rfl, denoteMeta_eqA_type_gen] at hea
  obtain rfl : ea = eqTy χ := (Option.some.inj hea).symm
  have hpin : interp V σ (mp.base2.acval eqName χ)
      ∈ˢ piR 1 (univ (χ uN) : V)
        (fun A => piR 1 A fun _ => piR 1 A fun _ => (univ 0 : V)) := by
    have h := hmem σ
    rw [show interp V σ (eqTy χ)
        = piR 1 (univ (χ uN) : V)
          (fun A => piR 1 A fun _ => piR 1 A fun _ => (univ 0 : V))
      from rfl] at h
    exact h
  have h1 := app_mem_piR_pos (V := V) Nat.one_ne_zero hpin hS
  have h2 := app_mem_piR_pos (V := V) Nat.one_ne_zero h1 hl
  have h3 : WellDenoted V σ
      (.app (.app (.app (mp.base2.acval eqName χ) Sa) la) ra) := hok.1
  rw [WellDenoted_app] at h3
  obtain ⟨-, -, v, A, B, hIn, hrIn, -⟩ := h3
  have hIn' : SetTheory.app
      (SetTheory.app (interp V σ (mp.base2.acval eqName χ))
        (interp V σ Sa)) (interp V σ la) ∈ˢ piR v A B := by
    rw [← interp_app, ← interp_app]; exact hIn
  have hv : v ≠ 0 := by
    intro hv0
    subst hv0
    exact not_pt_mem_piR_pos (V := V) Nat.one_ne_zero
      (eq_pt_of_mem_piR_zero hIn' ▸ h2)
  rw [piR_dom_unique hv Nat.one_ne_zero hIn' h2] at hrIn
  exact hrIn

/-! ## The key -/

set_option maxHeartbeats 3200000 in
/-- **The member cons's η key, P tier** — `etaLawKeyS`'s transpose, and
the campaign's first `EtaLaw` producer. -/
theorem memberEtaLaw : MemberEtaLaw V := by
  intro μ F blockNames env mp cv cvA c₀ hmv hIB hIA hc₀cv hc₀name
    hntc T cvT caps hfT hcape hnresT hp h0 hbT hbC hfam m₂ hac φ'
  -- `MemberValR`'s data
  obtain ⟨type', hcv, hcvAeq, hms, cvm₀, mval₀, hint₀, hfm₀, hlpm₀,
    hren₀⟩ := id hmv
  obtain ⟨hfind, -, -, -, -, -, -, -, htr0, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvAeq]
  have htypeA : cvA.type = type' := by rw [hcvAeq]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hms0 : c₀.name.isModelSuffix = false := by
    rw [hc₀name]; exact hms
  -- the kernel's η-capability pins
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps, hCmE, hprojE,
    heqfE, hSstrip, hTstrip, hsdoms, hxdom, hsbody, htySlot, -⟩ :=
    hp.1 hcape
  obtain ⟨cvmC, mvalC, hmC, hCmE', hCmlps⟩ := hCmE
  -- ===== the two valuation identifications (v1's `hvT`/`hvC`) =====
  have hvT : ∀ ψ : Name → Nat,
      m₂.acval T ψ = mp.base2.acval (T.str "_model") ψ := by
    intro ψ
    by_cases hT0 : T = c₀.name
    · subst hT0
      rw [hac, acvalWith_self, hc₀name]
    · rw [hac, acvalWith_ne hT0]
      have hfE : env.find? T = some (.indInfo cvT caps) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun hh => hT0 hh.symm)] at hfT
        exact hfT
      exact (hIA T hbT _ hfE ψ).symm
  have hvC : ∀ ψ : Name → Nat,
      m₂.acval caps.etaCtor ψ
        = mp.base2.acval (caps.etaCtor.str "_model") ψ := by
    intro ψ
    by_cases hC0 : caps.etaCtor = c₀.name
    · rw [hac, hC0, acvalWith_self, hc₀name]
    · rw [hac, acvalWith_ne hC0]
      obtain ⟨cvC, cnP, cnF, hfC⟩ := hfam.2.1
      have hfCe : env.find? caps.etaCtor
          = some (.ctorInfo cvC cnP cnF) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun hh => hC0 hh.symm)] at hfC
        exact hfC
      exact (hIA caps.etaCtor hbC _ hfCe ψ).symm
  -- ===== the former's type reads as its model's =====
  have hEqTy : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 cvT.type
        = denoteMeta mp.base2.acval env ψ 0 cvmT.type := by
    intro ψ
    by_cases hT0 : T = c₀.name
    · have hc₀ : c₀ = .indInfo cvT caps := by
        rw [hT0, ConLeche.Env.find?_cons_self] at hfT
        exact Option.some.inj hfT
      have hcvT : cvT = cvA := by rw [hc₀] at hc₀cv; exact hc₀cv
      have hcvm : cvm₀ = cvmT := by
        have h := hTmE
        rw [hT0, hc₀name, hfm₀] at h
        exact (ConLeche.ConstantInfo.defnInfo.inj (Option.some.inj h)).1
      rw [hcvT, ← hcvm]
      exact memberTypeReadEq mp hmv hIB hIA hfm₀ ψ
    · have hfE : env.find? T = some (.indInfo cvT caps) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun hh => hT0 hh.symm)] at hfT
        exact hfT
      obtain ⟨cvm, mval, hm, hfm, hlps, hren, hval⟩ := hIB T hbT _ hfE
      obtain rfl : cvm = cvmT := by
        have h := hTmE; rw [hfm] at h
        exact (ConLeche.ConstantInfo.defnInfo.inj (Option.some.inj h)).1
      obtain ⟨-, -, hty, -⟩ :=
        mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfE)
      exact blockTypeReadEq mp hIB hIA hty hren ψ
  have hcbT : ConstsBound env cvT.type := by
    by_cases hT0 : T = c₀.name
    · have hc₀ : c₀ = .indInfo cvT caps := by
        rw [hT0, ConLeche.Env.find?_cons_self] at hfT
        exact Option.some.inj hfT
      have hcvT : cvT = cvA := by rw [hc₀] at hc₀cv; exact hc₀cv
      exact constsBound_of_constsResolve _ (by rw [hcvT, htypeA]; exact htr0)
    · have hfE : env.find? T = some (.indInfo cvT caps) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun hh => hT0 hh.symm)] at hfT
        exact hfT
      obtain ⟨-, -, hty, -⟩ :=
        mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfE)
      exact constsBound_of_constsResolve _ hty
  intro us hus
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ' cvT.levelParams us := ⟨_, rfl⟩
  obtain ⟨ta, htaM, hokta, -⟩ := mp.acval_memType hTmE ψ
  have htaM' : denoteMeta mp.base2.acval env ψ 0 cvmT.type = some ta := htaM
  have hta : denoteMeta mp.base2.acval env ψ 0 cvT.type = some ta := by
    rw [hEqTy]; exact htaM'
  refine ⟨ta, ?_, hokta, ?_⟩
  · rw [denotePInstLevels m₂ φ' cvT.levelParams us 0 cvT.type, ← hψ, hac]
    exact denoteMeta_cons_fresh_mono hfresh0 hntc ψ 0 cvT.type hcbT hta
  intro ρ ts rest x hlents hfit hmx
  rw [← hψ, hvT] at hmx
  rw [← hψ, h0, hvC,
    show etaFabArgsV (fun n => interp V ρ (m₂.acval n ψ)) T ts x 0
      = ts from by unfold etaFabArgsV projSpines; simp]
  -- ===== the two telescopes =====
  obtain ⟨Γm, Cm, hteleM, hΓmlen, hbodyM, hdomsM⟩ :=
    stripPis_denotePTele caps.etaParams hTstrip htaM'
  obtain ⟨ua, hua, hokua, hmemua⟩ := mp.acval_memType hthmE ψ
  have hua' : denoteMeta mp.base2.acval env ψ 0 tcv.type = some ua := hua
  obtain ⟨Γs, Cs, hteleS, hΓslen, hbodyS, hdomsS⟩ :=
    stripPis_denotePTele (caps.etaParams + 1) hSstrip hua'
  obtain ⟨Γ₁, Γ₂, M, hΓsplit, hΓ₂len, hΓ₁len, hteleS2, hteleS1⟩ :=
    PiTeleAV.split caps.etaParams 1 hteleS
  obtain ⟨ux, vx, Ax, Bx, Γ₁', rfl, hΓ₁eq, hS0⟩ := hteleS1.succ_inv
  cases hS0
  have hsblen : sbinders.length = caps.etaParams + 1 :=
    ConLeche.Expr.stripPis_length _ hSstrip
  have htblen : tbindersM.length = caps.etaParams :=
    ConLeche.Expr.stripPis_length _ hTstrip
  have hΓ₁ : Γ₁ = [Ax] := by rw [hΓ₁eq]; rfl
  -- ===== the parameter domains agree =====
  have hdomEq : ∀ i, i < ts.length →
      Γm.getD i default = Γ₂.getD i default := by
    intro i hi
    rw [hlents] at hi
    have hi0 : caps.etaParams - 1 - i < caps.etaParams := by omega
    have hb : sbinders[caps.etaParams - 1 - i]?
        = some (sbinders[caps.etaParams - 1 - i]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hb' : tbindersM[caps.etaParams - 1 - i]?
        = some (tbindersM[caps.etaParams - 1 - i]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hEq := hsdoms (caps.etaParams - 1 - i) _ _ hi0 hb hb'
    have h1 := hdomsS (caps.etaParams - 1 - i) _ hb
    have h2 := hdomsM (caps.etaParams - 1 - i) _ hb'
    rw [hEq, h2] at h1
    rw [show caps.etaParams - 1 - (caps.etaParams - 1 - i) = i from by
      omega] at h1
    rw [hΓsplit, List.getD, List.getD,
      List.getElem?_append_right (by rw [hΓ₁len]; omega), hΓ₁len,
      show caps.etaParams + 1 - 1 - (caps.etaParams - 1 - i) - 1 = i
        from by omega] at h1
    exact Option.some.inj h1
  -- ===== the opened slot, read and evaluated =====
  have hKle : ∀ (K : Name) (ci : ConstantInfo),
      env.find? K = some ci →
      ci.toConstantVal.levelParams = cvT.levelParams →
      ∀ d : Nat, caps.etaParams ≤ d →
      denoteMeta mp.base2.acval env ψ d
        (Expr.mkAppN (.const K (cvT.levelParams.map .param))
          (openFvars 0 caps.etaParams))
      = some (AnnotTerm.mkAppN (mp.base2.acval K ψ)
          ((List.range caps.etaParams).map fun q =>
            AnnotTerm.bvar (d - 1 - (0 + q)))) :=
    fun K ci hf hlps d hd => denoteMeta_openSpine hf hlps _ d hd
  have hspineVal : ∀ (K : Name) (d : Nat) (σ : Nat → V),
      (∀ q, q < ts.length →
        σ (d - 1 - (0 + q)) = consN ts ρ (ts.length - 1 - q)) →
      interp V σ (AnnotTerm.mkAppN (mp.base2.acval K ψ)
          ((List.range caps.etaParams).map fun q =>
            AnnotTerm.bvar (d - 1 - (0 + q))))
        = ts.foldl SetTheory.app (interp V ρ (mp.base2.acval K ψ)) := by
    intro K d σ hσ
    rw [← hlents]
    exact interp_bvarSpine (V := V) ts (ρ := ρ) (σ := σ)
      (K := mp.base2.acval K ψ) (fun q => d - 1 - (0 + q)) hσ
      (acval_interp_closedC mp.base2 _ ψ σ ρ)
  -- the major's slot
  obtain ⟨mx, hxb⟩ := hxdom
  have hAx : Ax = AnnotTerm.mkAppN (mp.base2.acval (T.str "_model") ψ)
      ((List.range caps.etaParams).map fun q =>
        AnnotTerm.bvar (caps.etaParams - 1 - (0 + q))) := by
    have h := hdomsS caps.etaParams _ hxb
    rw [instSeq_openSpine _ _ caps.etaParams caps.etaParams
        (caps.etaParams - 1) (Nat.le_refl _) (by omega),
      Nat.zero_add,
      hKle _ _ hTmE hTmlps caps.etaParams (Nat.le_refl _)] at h
    rw [hΓsplit, hΓ₁, List.getD,
      List.getElem?_append_left (by simp),
      show caps.etaParams + 1 - 1 - caps.etaParams = 0 from by omega]
      at h
    exact (Option.some.inj h).symm
  have hx' : x ∈ˢ interp V (consN ts ρ) Ax := by
    rw [hAx, hspineVal _ caps.etaParams (consN ts ρ)
      (fun q hq => congrArg (consN ts ρ) (by omega))]
    exact hmx
  -- ===== the fit, moved and continued =====
  have hteleM' : PiTeleAV ts.length ta Γm Cm := by rw [hlents]; exact hteleM
  have hteleS2' : PiTeleAV ts.length ua Γ₂ (.pi ux vx Ax Cs) := by
    rw [hlents]; exact hteleS2
  have hfitFull : TeleFit V ρ ua (ts ++ [x])
      (interp V (cons x (consN ts ρ)) Cs) :=
    teleFit_congr_ext ts hteleM' hteleS2' hdomEq hfit
      (TeleFit.cons hx' TeleFit.nil)
  have hteleFull : PiTeleAV (ts ++ [x]).length ua Γs Cs := by
    rw [List.length_append, hlents]; exact hteleS
  have hconsApp : consN (ts ++ [x]) ρ = cons x (consN ts ρ) := by
    rw [consN_append]; rfl
  -- ===== the opened body is the pinned `Eq` spine =====
  rw [h0] at hsbody
  simp only [List.range_zero, List.map_nil, List.append_nil] at hsbody
  have hCs : Cs = .app (.app (.app
      (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams [ℓA]))
      (AnnotTerm.mkAppN (mp.base2.acval (T.str "_model") ψ)
        ((List.range caps.etaParams).map fun q =>
          AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q)))))
      (.bvar 0))
      (AnnotTerm.mkAppN (mp.base2.acval (caps.etaCtor.str "_model") ψ)
        ((List.range caps.etaParams).map fun q =>
          AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q)))) := by
    have h := hbodyS
    rw [show caps.etaParams + 1 - 1 = caps.etaParams from by omega,
      hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl,
      Nat.zero_add] at h
    simp only [List.map_cons, List.map_nil] at h
    rw [htySlot, instSeq_openSpine _ _ caps.etaParams
      (caps.etaParams + 1) caps.etaParams (by omega) (by omega),
      instSeq_openSpine _ _ caps.etaParams (caps.etaParams + 1)
        caps.etaParams (by omega) (by omega)] at h
    have hb0 : Expr.instSeq (openFvars 0 (caps.etaParams + 1))
        caps.etaParams (Expr.bvar 0)
        = Expr.fvar caps.etaParams (.sort .zero) := by
      have hhit := Expr.instSeq_bvar (openFvars 0 (caps.etaParams + 1))
        caps.etaParams 0 (openFvars_bounded 0 (caps.etaParams + 1))
        (by omega) (by rw [openFvars_length]; omega)
      rw [openFvars_getElem? (d := 0) (k := caps.etaParams + 1)
        (i := caps.etaParams - 0) (by omega),
        show (0 : Nat) + (caps.etaParams - 0) = caps.etaParams from by
          omega] at hhit
      exact (Option.some.inj hhit).symm
    rw [hb0] at h
    rw [denoteMeta_mkAppN
      (DenoteMetaSpine.cons
        (hKle _ _ hTmE hTmlps (caps.etaParams + 1) (by omega))
        (DenoteMetaSpine.cons
          (denoteMeta_fvar mp.base2.acval (caps.etaParams + 1)
            caps.etaParams (.sort .zero))
          (DenoteMetaSpine.cons
            (hKle _ _ hCmE' hCmlps (caps.etaParams + 1) (by omega))
            DenoteMetaSpine.nil)))
      (denoteMeta_const heqfE rfl)] at h
    rw [show caps.etaParams + 1 - 1 - caps.etaParams = 0 from by omega]
      at h
    exact (Option.some.inj h).symm
  -- ===== fire =====
  have hokCs : WellDenotedV V (cons x (consN ts ρ)) Cs := by
    have h := teleFit_wellDenotedV_residual (ts ++ [x]) hteleFull (hokua ρ)
      hfitFull
    rwa [hconsApp] at h
  have hSval : ∀ K : Name, interp V (cons x (consN ts ρ))
      (AnnotTerm.mkAppN (mp.base2.acval K ψ)
        ((List.range caps.etaParams).map fun q =>
          AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q))))
      = ts.foldl SetTheory.app (interp V ρ (mp.base2.acval K ψ)) :=
    fun K => hspineVal K (caps.etaParams + 1) (cons x (consN ts ρ))
      (fun q hq => by
        rw [show caps.etaParams + 1 - 1 - (0 + q)
          = (ts.length - 1 - q) + 1 from by omega]
        rfl)
  have hSuniv := eqSlot_univ mp heqfE _ (hCs ▸ hokCs)
  rw [hSval] at hSuniv
  have hxS : x ∈ˢ ts.foldl SetTheory.app
      (interp V ρ (mp.base2.acval (T.str "_model") ψ)) := hmx
  have hRS := eqThird_mem mp heqfE _ (hCs ▸ hokCs)
    (by rw [hSval]; exact hSuniv)
    (by rw [hSval]; exact hxS)
  rw [hSval, hSval] at hRS
  have hlanded := memFoldl_of_teleFit (ts ++ [x]) (hokua ρ)
    (hmemua ρ) hfitFull
  rw [hCs] at hlanded
  have hc0 : (cons x (consN ts ρ)) 0 = x := rfl
  simp only [interp_app, interp_bvar, hSval, hc0] at hlanded
  rw [(mp.eq_law heqfE _).1 (cons x (consN ts ρ)) _ x _
    hSuniv hxS hRS] at hlanded
  exact eq_of_mem_eqv hlanded

end ConLeche.Model
