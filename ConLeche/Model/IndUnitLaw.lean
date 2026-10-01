module

import ConLeche.Semantics.IndBlockRun
public import ConLeche.Model.IndTele
public import ConLeche.Model.BasisEq
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLevels

public section

/-!
# The unit-like key, P tier (task #161, IND TIER part 2, item 1b)

`unitLawKeyS`'s transpose (`Install/EtaLawS.lean:618`): the checked
`T._model.unitlike` theorem, fired at a fitting parameter spine and two
members of the family, yields the stored family's `UnitLaw`.

**The P route is not v1's, and it is shorter.**  v1 fires through
`fireS`, which needs the whole tower/`Sat`/`chainE` apparatus and an
`EqFormerKeyV` narrowed out of the bundle.  At the P currency none of
that exists (the survey confirmed it), and none of it is needed: the
reading of a `∀` *is* a `.pi`, `TeleFit` peels `.pi`s under `cons`,
and `interp` of a `.pi` *is* a `piR`.  So the firing is four moves:

1. the statement's type reads to a `PiTeleAV` of length `nP + 2`
   (`stripPis_denotePTele`) and the stored theorem inhabits it
   (`EnvModelM.acval_memType` — the P twin of `mem_type_step`);
2. the *given* fit is at the family former's type, and the pins'
   domain equalities move it to the statement's (`teleFit_congr_ext`)
   and continue it at the two member slots, whose domains both
   evaluate to the family at the parameters;
3. `memFoldl_of_teleFit` applies the theorem's inhabitant along the
   whole spine, landing it in the opened body's reading;
4. that body is the pinned `Eq` spine, which `eq_law` computes to
   `eqv x y` — and `eq_of_mem_eqv` reads the equation off.

**Where the type slot's universe membership comes from.**  `EqLaw`,
like `EqLawV`, needs `⟦α⟧ ∈ univ (χ uN)` before it will compute; v1
gets it inside `fireS` by graph rigidity of the pinned `Eq` former
against the statement's own truthfulness, and the P tier does exactly
the same with `piR_dom_unique` — the statement's *grading*
(`teleFit_wellDenotedV_residual`, then `WellDenoted_app` twice) exhibits the `Eq`
leaf in some `piR v A B` with the slot in `A`, `acval_memType` at
`eqName` exhibits it in `piR 1 (univ (χ uN)) _` (the pinned type's
reading, `eqTy`), and the two domains coincide.  The regime side
condition `v ≠ 0` is not an assumption: a squash-regime member is `pt`
(`eq_pt_of_mem_piR_zero`) and `pt` is in no graph-regime product
(`not_pt_mem_piR_pos`), so `v = 0` is refuted outright.

The unit half's split is **two-way** where the η half's is four-way,
and it needs no `Eq`-slot rigidity for its *sides*: both are telescope
slots, so the fit supplies their memberships directly.  Rigidity
appears here only for the type slot, which every `Eq` statement needs.
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
variable {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}

/-! ## The capability statements' type slot, opened

All three occurrences — the η/unit member binders and the equation's
type slot — open to the *same* expression, the model former applied to
the canonical opener; only the depth they are read at differs.  One
lemma, parameterised by the cut. -/

theorem instSeq_openSpine (K : Name) (lvls : List Level)
    (nP L t : Nat) (hnL : nP ≤ L) (hnP : nP ≤ t + 1) :
    Expr.instSeq (openFvars 0 L) t
        (Expr.mkAppN (.const K lvls)
          ((List.range nP).map fun k => Expr.bvar (t - k)))
      = Expr.mkAppN (.const K lvls) (openFvars 0 nP) := by
  rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl, List.map_map]
  refine congrArg _ (List.ext_getElem (by simp) fun q h1 h2 => ?_)
  have hq : q < nP := by simpa using h1
  rw [List.getElem_map, List.getElem_range]
  show Expr.instSeq (openFvars 0 L) t (Expr.bvar (t - q))
    = (openFvars 0 nP)[q]
  have hbnd := openFvars_getElem? (d := 0) (k := nP) (i := q) hq
  rw [List.getElem?_eq_getElem h2] at hbnd
  rw [Option.some.inj hbnd]
  have hhit := Expr.instSeq_bvar (openFvars 0 L) t (t - q)
    (openFvars_bounded 0 L) (by omega)
    (by rw [openFvars_length]; omega)
  rw [show t - (t - q) = q from by omega,
    openFvars_getElem? (d := 0) (k := L) (i := q) (by omega)] at hhit
  exact (Option.some.inj hhit).symm

/-- The opened slot, read: the model former's leaf applied to the
descending bound variables at whatever depth the slot sits. -/
theorem denoteMeta_openSpine {K : Name} {ci : ConstantInfo}
    {lps : List Name} (hf : env.find? K = some ci)
    (hlps : ci.toConstantVal.levelParams = lps)
    (nP d : Nat) (hd : nP ≤ d) :
    denoteMeta acval env φ d
        (Expr.mkAppN (.const K (lps.map .param)) (openFvars 0 nP))
      = some (AnnotTerm.mkAppN (acval K φ)
          ((List.range nP).map fun q => AnnotTerm.bvar (d - 1 - (0 + q)))) := by
  refine denoteMeta_mkAppN (denoteMetaSpine_openFvars nP 0 d (by omega)) ?_
  rw [denoteMeta_const hf (by rw [hlps, List.length_map]), hlps,
    show Level.substFn φ lps (lps.map .param) = φ from
      funext fun _ => Level.substFn_map_param]

/-! ## The member type's reading, and the model's

`memberKey` proves the two types read the same but returns only the
member's reading; the keys need the *model's*, because that is the
type whose telescope the pins speak about.  Same two-move argument
(`denoteMeta_renameConsts_resolve` past `denoteMeta_erasedEq`), stated as
the equality. -/

theorem blockTypeReadEq (mp : EnvModelM V μ env) {blockNames : List Name}
    (hIB : BlockInstalledTT blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env mp.base2.acval)
    {ty : Expr} (htr : ty.constsResolve env = true)
    {cvm : ConstantVal}
    (hren : ((ty.renameConsts (fun n' =>
      if blockNames.contains n' then n'.str "_model" else n')) == cvm.type)
      = true)
    (ψ : Name → Nat) :
    denoteMeta mp.base2.acval env ψ 0 ty
      = denoteMeta mp.base2.acval env ψ 0 cvm.type := by
  have hup : ∀ n ci, env.find? n = some ci →
      ∃ ci', env.find? ((fun n =>
          if blockNames.contains n then n.str "_model" else n) n)
        = some ci' ∧
        ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams := by
    intro n ci hfn
    dsimp only
    by_cases hb : blockNames.contains n = true
    · obtain ⟨cvm₂, mval₂, hint₂, hfm₂, hlp₂, -, -⟩ := hIB n hb ci hfn
      exact ⟨.defnInfo cvm₂ mval₂ hint₂, by rw [if_pos hb]; exact hfm₂,
        hlp₂⟩
    · exact ⟨ci, by rw [if_neg hb]; exact hfn, rfl⟩
  have hval : ∀ (n : Name) (ci : ConstantInfo),
      env.find? n = some ci → ∀ ψ' : Name → Nat,
      mp.base2.acval ((fun n =>
        if blockNames.contains n then n.str "_model" else n) n) ψ'
        = mp.base2.acval n ψ' := by
    intro n ci hfn ψ'
    dsimp only
    by_cases hb : blockNames.contains n = true
    · rw [if_pos hb]; exact hIA n hb ci hfn ψ'
    · rw [if_neg hb]
  rw [← denoteMeta_erasedEq (Expr.ErasedEq.of_eq (eq_of_beq hren)) 0]
  exact (denoteMeta_renameConsts_resolve hup hval ty 0 htr).symm

/-- The member cons's instance: `MemberValR` supplies both data. -/
theorem memberTypeReadEq (mp : EnvModelM V μ env) {blockNames : List Name}
    {cv cvA : ConstantVal}
    (hmv : MemberValRun μ F env blockNames cv cvA)
    (hIB : BlockInstalledTT blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env mp.base2.acval)
    {cvm : ConstantVal} {mval : Expr} {hint : ReducibilityHint}
    (hfm : env.find? (cvA.name.str "_model")
      = some (.defnInfo cvm mval hint))
    (ψ : Name → Nat) :
    denoteMeta mp.base2.acval env ψ 0 cvA.type
      = denoteMeta mp.base2.acval env ψ 0 cvm.type := by
  obtain ⟨type', hcv, rfl, -, cvm', mval', hint', hfm', hlpm, hren⟩ := hmv
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hcv
  obtain rfl : cvm' = cvm := by
    rw [hfm'] at hfm
    exact (ConLeche.ConstantInfo.defnInfo.inj (Option.some.inj hfm)).1
  exact blockTypeReadEq mp hIB hIA htr hren ψ

/-! ## `Eq`'s pinned type, at any environment storing it -/

/-- `denoteMeta_eqA_type` at an arbitrary environment: `Eq`'s type has no
`const` leaf, so its reading does not consult the environment. -/
theorem denoteMeta_eqA_type_gen (ψ : Name → Nat) :
    denoteMeta acval env ψ 0 eqA.toConstantVal.type = some (eqTy ψ) := by
  simp [eqA, ConstantInfo.toConstantVal, denoteMeta_forallE, denoteMeta_sort,
    denoteMeta_fvar, Expr.instantiate1, eqTy, pwBit_never, Level.eval, uN]

/-- **The `Eq` type slot's universe membership, by graph rigidity.**
`EqLawV.dom`'s P counterpart, and the only place the unit key needs
rigidity at all. -/
theorem eqSlot_univ (mp : EnvModelM V μ env)
    (heqfE : env.find? eqName = some eqA) (χ : Name → Nat)
    {σ : Nat → V} {Sa la ra : AnnotTerm}
    (hok : WellDenotedV V σ
      (.app (.app (.app (mp.base2.acval eqName χ) Sa) la) ra)) :
    interp V σ Sa ∈ˢ (univ (χ uN) : V) := by
  -- the statement's own grading exhibits the leaf in *some* product
  have h2 : WellDenoted V σ (.app (mp.base2.acval eqName χ) Sa) := by
    have h1 := hok.1
    rw [WellDenoted_app] at h1
    have h1' := h1.1
    rw [WellDenoted_app] at h1'
    exact h1'.1
  rw [WellDenoted_app] at h2
  obtain ⟨-, -, v, A, B, hEqIn, hSIn, -⟩ := h2
  -- the pinned type exhibits it in the graph-regime product
  obtain ⟨ea, hea, -, hmem⟩ := mp.acval_memType heqfE χ
  rw [show (eqA : ConstantInfo).toConstantVal.type
      = eqA.toConstantVal.type from rfl, denoteMeta_eqA_type_gen] at hea
  obtain rfl : ea = eqTy χ := (Option.some.inj hea).symm
  have hpin : interp V σ (mp.base2.acval eqName χ)
      ∈ˢ piR 1 (univ (χ uN) : V)
        (fun A => piR 1 A fun _ => piR 1 A fun _ => (univ 0 : V)) := by
    have := hmem σ
    rw [show interp V σ (eqTy χ)
        = piR 1 (univ (χ uN) : V)
          (fun A => piR 1 A fun _ => piR 1 A fun _ => (univ 0 : V)) from rfl]
      at this
    exact this
  -- the regime is graph: a squash member is `pt`, which no graph
  -- product contains
  have hv : v ≠ 0 := by
    intro hv0
    subst hv0
    exact not_pt_mem_piR_pos (V := V) Nat.one_ne_zero
      (eq_pt_of_mem_piR_zero hEqIn ▸ hpin)
  rw [piR_dom_unique hv Nat.one_ne_zero hEqIn hpin] at hSIn
  exact hSIn

/-! ## The key -/

set_option maxHeartbeats 1600000 in
/-- **The member cons's unit-like key, P tier** — `unitLawKeyS`'s
transpose, and the campaign's first `UnitLaw` producer. -/
theorem memberUnitLaw : MemberUnitLaw V := by
  intro μ F blockNames env mp cv cvA c₀ hmv hIB hIA hc₀cv hc₀name
    cvT caps hceq hcapu hnres hp m₂ hac φ'
  have hcvT : cvT = cvA := by
    have h := hc₀cv; rw [hceq] at h; exact h
  rw [hcvT]
  -- `MemberValR`'s data
  obtain ⟨type', hcv, hcvAeq, hms, cvm₀, mval₀, hint₀, hfm₀, hlpm₀,
    hren₀⟩ := id hmv
  obtain ⟨hfind, -, -, -, -, -, -, -, htr, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvAeq]
  have htypeA : cvA.type = type' := by rw [hcvAeq]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hcb : ConstsBound env cvA.type :=
    constsBound_of_constsResolve _ (by rw [htypeA]; exact htr)
  intro us hus
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ' cvA.levelParams us := ⟨_, rfl⟩
  -- the member's type reading, and its crossing to the extension
  obtain ⟨ta, hta, hokta, -⟩ := memberKey mp hmv hIB hIA ψ
  refine ⟨ta, ?_, hokta, ?_⟩
  · rw [denotePInstLevels m₂ φ' cvA.levelParams us 0 cvA.type, ← hψ, hac]
    exact denoteMeta_cons_fresh_mono hfresh0
      (fun _ h => by rw [hceq] at h; exact nomatch h)
      ψ 0 cvA.type hcb hta
  intro ρ ts rest x y hlents hfit hmx hmy
  -- the family's leaf at the extension is the model's
  have hleaf : m₂.acval c₀.name ψ
      = mp.base2.acval (cvA.name.str "_model") ψ := by
    rw [hac, acvalWith_self]
  rw [← hψ, hleaf] at hmx hmy
  -- the kernel's unit-capability pins
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps, heqfE, hSstrip,
    hTstrip, hsdoms, hxdom, hydom, hsbody, htySlot, -⟩ := hp.2 hcapu
  have hcvmEq : cvm₀ = cvmT := by
    have h := hTmE; rw [hfm₀] at h
    exact (ConLeche.ConstantInfo.defnInfo.inj (Option.some.inj h)).1
  -- the model former's type reads to the member's reading
  have htaM : denoteMeta mp.base2.acval env ψ 0 cvmT.type = some ta := by
    rw [← hcvmEq, ← memberTypeReadEq mp hmv hIB hIA hfm₀ ψ]; exact hta
  -- the two telescopes
  obtain ⟨Γm, Cm, hteleM, hΓmlen, hbodyM, hdomsM⟩ :=
    stripPis_denotePTele caps.unitParams hTstrip htaM
  obtain ⟨ua, hua, hokua, hmemua⟩ := mp.acval_memType hthmE ψ
  have hua' : denoteMeta mp.base2.acval env ψ 0 tcv.type = some ua := hua
  obtain ⟨Γs, Cs, hteleS, hΓslen, hbodyS, hdomsS⟩ :=
    stripPis_denotePTele (caps.unitParams + 2) hSstrip hua'
  obtain ⟨Γ₁, Γ₂, M, hΓsplit, hΓ₂len, hΓ₁len, hteleS2, hteleS1⟩ :=
    PiTeleAV.split caps.unitParams 2 hteleS
  obtain ⟨ux, vx, Ax, Bx, Γ₁', rfl, hΓ₁eq, hS1⟩ := hteleS1.succ_inv
  obtain ⟨uy, vy, Ay, By, Γ₁'', rfl, hΓ₁'eq, hS0⟩ := hS1.succ_inv
  cases hS0
  -- the binder lists' lengths
  have hsblen : sbinders.length = caps.unitParams + 2 :=
    ConLeche.Expr.stripPis_length _ hSstrip
  have htblen : tbindersM.length = caps.unitParams :=
    ConLeche.Expr.stripPis_length _ hTstrip
  -- Γ₁ = [Ay, Ax]
  have hΓ₁ : Γ₁ = [Ay, Ax] := by
    rw [hΓ₁eq, hΓ₁'eq]; rfl
  -- ===== the parameter domains agree =====
  have hdomEq : ∀ i, i < ts.length →
      Γm.getD i default = Γ₂.getD i default := by
    intro i hi
    rw [hlents] at hi
    have hi0 : caps.unitParams - 1 - i < caps.unitParams := by omega
    have hb : sbinders[caps.unitParams - 1 - i]?
        = some (sbinders[caps.unitParams - 1 - i]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hb' : tbindersM[caps.unitParams - 1 - i]?
        = some (tbindersM[caps.unitParams - 1 - i]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hEq := hsdoms (caps.unitParams - 1 - i) _ _ hi0 hb hb'
    have h1 := hdomsS (caps.unitParams - 1 - i) _ hb
    have h2 := hdomsM (caps.unitParams - 1 - i) _ hb'
    rw [hEq, h2] at h1
    -- `Γs.getD (nP + 1 - i0) = Γ₂.getD i`, `Γm.getD (nP - 1 - i0) = Γm.getD i`
    rw [show caps.unitParams - 1 - (caps.unitParams - 1 - i) = i from by
      omega] at h1
    rw [hΓsplit, List.getD, List.getD,
      List.getElem?_append_right (by rw [hΓ₁len]; omega), hΓ₁len,
      show caps.unitParams + 2 - 1 - (caps.unitParams - 1 - i) - 2 = i
        from by omega] at h1
    exact Option.some.inj h1
  -- ===== the two member slots =====
  have hKle : ∀ d : Nat, caps.unitParams ≤ d →
      denoteMeta mp.base2.acval env ψ d
        (Expr.mkAppN (.const (cvA.name.str "_model")
          (cvA.levelParams.map .param)) (openFvars 0 caps.unitParams))
      = some (AnnotTerm.mkAppN
          (mp.base2.acval (cvA.name.str "_model") ψ)
          ((List.range caps.unitParams).map fun q =>
            AnnotTerm.bvar (d - 1 - (0 + q)))) :=
    fun d hd => denoteMeta_openSpine hTmE hTmlps _ d hd
  -- the spine's value at any environment agreeing with the fit
  have hspineVal : ∀ (d : Nat) (σ : Nat → V),
      (∀ q, q < ts.length →
        σ (d - 1 - (0 + q)) = consN ts ρ (ts.length - 1 - q)) →
      interp V σ (AnnotTerm.mkAppN
          (mp.base2.acval (cvA.name.str "_model") ψ)
          ((List.range caps.unitParams).map fun q =>
            AnnotTerm.bvar (d - 1 - (0 + q))))
        = ts.foldl SetTheory.app
            (interp V ρ (mp.base2.acval (cvA.name.str "_model") ψ)) := by
    intro d σ hσ
    rw [← hlents]
    exact interp_bvarSpine (V := V) ts (ρ := ρ) (σ := σ)
      (K := mp.base2.acval (cvA.name.str "_model") ψ)
      (fun q => d - 1 - (0 + q)) hσ
      (acval_interp_closedC mp.base2 _ ψ σ ρ)
  -- the x-slot
  obtain ⟨mx, hxb⟩ := hxdom
  have hAx : Ax = AnnotTerm.mkAppN
      (mp.base2.acval (cvA.name.str "_model") ψ)
      ((List.range caps.unitParams).map fun q =>
        AnnotTerm.bvar (caps.unitParams - 1 - (0 + q))) := by
    have h := hdomsS caps.unitParams _ hxb
    rw [instSeq_openSpine _ _ caps.unitParams caps.unitParams
        (caps.unitParams - 1) (Nat.le_refl _) (by omega),
      Nat.zero_add, hKle caps.unitParams (Nat.le_refl _)] at h
    rw [hΓsplit, hΓ₁, List.getD,
      List.getElem?_append_left (by simp),
      show caps.unitParams + 2 - 1 - caps.unitParams = 1 from by omega]
      at h
    exact (Option.some.inj h).symm
  -- the y-slot
  obtain ⟨my, hyb⟩ := hydom
  have hAy : Ay = AnnotTerm.mkAppN
      (mp.base2.acval (cvA.name.str "_model") ψ)
      ((List.range caps.unitParams).map fun q =>
        AnnotTerm.bvar (caps.unitParams + 1 - 1 - (0 + q))) := by
    have h := hdomsS (caps.unitParams + 1) _ hyb
    rw [show caps.unitParams + 1 - 1 = caps.unitParams from by omega,
      instSeq_openSpine _ _ caps.unitParams (caps.unitParams + 1)
        caps.unitParams (by omega) (by omega),
      Nat.zero_add, hKle (caps.unitParams + 1) (by omega)] at h
    rw [hΓsplit, hΓ₁, List.getD,
      List.getElem?_append_left (by simp),
      show caps.unitParams + 2 - 1 - (caps.unitParams + 1) = 0 from by
        omega] at h
    exact (Option.some.inj h).symm
  -- the memberships, at the fit's environments
  have hx' : x ∈ˢ interp V (consN ts ρ) Ax := by
    rw [hAx, hspineVal caps.unitParams (consN ts ρ)
      (fun q hq => congrArg (consN ts ρ) (by omega))]
    exact hmx
  have hy' : y ∈ˢ interp V (cons x (consN ts ρ)) Ay := by
    rw [hAy, hspineVal (caps.unitParams + 1) (cons x (consN ts ρ))
      (fun q hq => by
        rw [show caps.unitParams + 1 - 1 - (0 + q)
          = (ts.length - 1 - q) + 1 from by omega]
        rfl)]
    exact hmy
  -- ===== the fit, moved and continued =====
  have hteleM' : PiTeleAV ts.length ta Γm Cm := by rw [hlents]; exact hteleM
  have hteleS2' : PiTeleAV ts.length ua Γ₂ (.pi ux vx Ax (.pi uy vy Ay Cs)) := by
    rw [hlents]; exact hteleS2
  have hfitFull : TeleFit V ρ ua (ts ++ [x, y])
      (interp V (cons y (cons x (consN ts ρ))) Cs) :=
    teleFit_congr_ext ts hteleM' hteleS2' hdomEq hfit
      (TeleFit.cons hx' (TeleFit.cons hy' TeleFit.nil))
  have hteleFull : PiTeleAV (ts ++ [x, y]).length ua Γs Cs := by
    rw [List.length_append, hlents]; exact hteleS
  have hconsApp : consN (ts ++ [x, y]) ρ
      = cons y (cons x (consN ts ρ)) := by
    rw [consN_append]; rfl
  -- ===== the opened body is the pinned `Eq` spine =====
  have hCs : Cs = .app (.app (.app
      (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams [ℓA]))
      (AnnotTerm.mkAppN (mp.base2.acval (cvA.name.str "_model") ψ)
        ((List.range caps.unitParams).map fun q =>
          AnnotTerm.bvar (caps.unitParams + 2 - 1 - (0 + q)))))
      (.bvar 1)) (.bvar 0) := by
    have h := hbodyS
    rw [show caps.unitParams + 2 - 1 = caps.unitParams + 1 from by omega,
      hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl,
      Nat.zero_add] at h
    simp only [List.map_cons, List.map_nil] at h
    rw [htySlot, instSeq_openSpine _ _ caps.unitParams
      (caps.unitParams + 2) (caps.unitParams + 1) (by omega)
      (by omega)] at h
    -- the two member variables, opened
    have hb1 : Expr.instSeq (openFvars 0 (caps.unitParams + 2))
        (caps.unitParams + 1) (Expr.bvar 1)
        = Expr.fvar caps.unitParams (.sort .zero) := by
      have hhit := Expr.instSeq_bvar (openFvars 0 (caps.unitParams + 2))
        (caps.unitParams + 1) 1
        (openFvars_bounded 0 (caps.unitParams + 2)) (by omega)
        (by rw [openFvars_length]; omega)
      rw [openFvars_getElem? (d := 0) (k := caps.unitParams + 2)
        (i := caps.unitParams + 1 - 1) (by omega),
        show (0 : Nat) + (caps.unitParams + 1 - 1)
          = caps.unitParams from by omega] at hhit
      exact (Option.some.inj hhit).symm
    have hb0 : Expr.instSeq (openFvars 0 (caps.unitParams + 2))
        (caps.unitParams + 1) (Expr.bvar 0)
        = Expr.fvar (caps.unitParams + 1) (.sort .zero) := by
      have hhit := Expr.instSeq_bvar (openFvars 0 (caps.unitParams + 2))
        (caps.unitParams + 1) 0
        (openFvars_bounded 0 (caps.unitParams + 2)) (by omega)
        (by rw [openFvars_length]; omega)
      rw [openFvars_getElem? (d := 0) (k := caps.unitParams + 2)
        (i := caps.unitParams + 1 - 0) (by omega),
        show (0 : Nat) + (caps.unitParams + 1 - 0)
          = caps.unitParams + 1 from by omega] at hhit
      exact (Option.some.inj hhit).symm
    rw [hb1, hb0] at h
    rw [denoteMeta_mkAppN
      (DenoteMetaSpine.cons (hKle (caps.unitParams + 2) (by omega))
        (DenoteMetaSpine.cons
          (denoteMeta_fvar mp.base2.acval (caps.unitParams + 2)
            caps.unitParams (.sort .zero))
          (DenoteMetaSpine.cons
            (denoteMeta_fvar mp.base2.acval (caps.unitParams + 2)
              (caps.unitParams + 1) (.sort .zero))
            DenoteMetaSpine.nil)))
      (denoteMeta_const heqfE rfl)] at h
    rw [show caps.unitParams + 2 - 1 - caps.unitParams = 1 from by omega,
      show caps.unitParams + 2 - 1 - (caps.unitParams + 1) = 0 from by
        omega] at h
    exact (Option.some.inj h).symm
  -- ===== fire =====
  have hokCs : WellDenotedV V (cons y (cons x (consN ts ρ))) Cs := by
    have h := teleFit_wellDenotedV_residual (ts ++ [x, y]) hteleFull
      (hokua ρ) hfitFull
    rwa [hconsApp] at h
  have hSval : interp V (cons y (cons x (consN ts ρ)))
      (AnnotTerm.mkAppN (mp.base2.acval (cvA.name.str "_model") ψ)
        ((List.range caps.unitParams).map fun q =>
          AnnotTerm.bvar (caps.unitParams + 2 - 1 - (0 + q))))
      = ts.foldl SetTheory.app
          (interp V ρ (mp.base2.acval (cvA.name.str "_model") ψ)) :=
    hspineVal (caps.unitParams + 2) (cons y (cons x (consN ts ρ)))
      (fun q hq => by
        rw [show caps.unitParams + 2 - 1 - (0 + q)
          = (ts.length - 1 - q) + 1 + 1 from by omega]
        rfl)
  have hSuniv := eqSlot_univ mp heqfE _ (hCs ▸ hokCs)
  rw [hSval] at hSuniv
  have hlanded := memFoldl_of_teleFit (ts ++ [x, y]) (hokua ρ)
    (hmemua ρ) hfitFull
  rw [hCs] at hlanded
  have hc1 : (cons y (cons x (consN ts ρ))) 1 = x := rfl
  have hc0 : (cons y (cons x (consN ts ρ))) 0 = y := rfl
  simp only [interp_app, interp_bvar, hSval, hc1, hc0] at hlanded
  rw [(mp.eq_law heqfE _).1 (cons y (cons x (consN ts ρ))) _ x y
    hSuniv hmx hmy] at hlanded
  exact eq_of_mem_eqv hlanded

end ConLeche.Model
