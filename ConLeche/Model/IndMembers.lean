module

import ConLeche.Semantics.IndBlockRun
public import ConLeche.Model.IndCaps
import ConLeche.Semantics.EnvFactsCons
public section

/-!
# The member phase, P tier (task #161, IND TIER)

`memberInstallS` is v1's shared step of both block folds; this is its
joint twin — one step that installs a member **at both tiers at
once**, so that the P side always has the v1 carrier its
`declStep_preserves_of_cons` premise names.  That pairing is forced: the P
step needs `EnvS V ⟨c₀ :: env.consts⟩` *constructively*, and only the
v1 install produces it.

Carried across the step, and the reason each is here:

| carried | why |
| --- | --- |
| `BlockInstalledTT` | the member key's `hup` clause (V-free, v1's) |
| `BlockAcvalInstalled` | the member key's `hval` clause (H's §1 shape) |
| `EtaFamiliesClosedO` / `BlockEtaPinned` | the η split's side facts |

The two capability laws enter as named obligations —
`MemberEtaLaw` / `MemberUnitLaw`, `MemberKeyS`'s siblings — because
`capsOk_cons_member` has already reduced `caps_ok` at a member cons
to exactly them.  They are the inductive tier's remaining semantic
content on the caps side, and nothing else about a member cons is
open.

`BlockAcvalInstalled`'s step is the one new argument: the member's
leaf *is* the model's, so the fresh entry satisfies the predicate by
`acvalWith_self`, and every earlier entry survives because neither
`n` nor `n ++ "_model"` can be the member's name —
`Name.str_model_ne` against `MemberValR`'s `isModelSuffix = false`
conjunct, which is exactly the conjunct v1's `BlockInstalledTT.step`
consumes for the same purpose.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-- **The member cons's live η law** (`MemberKeyS`'s sibling): the row
`capsOk_cons_member` leaves open — a block former at
`etaFields = 0`.  v1's counterpart is `etaLawKeyS`, reached through
`memberEtaS`. -/
@[expose] def MemberEtaLaw (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {blockNames : List Name} {env : Env}
    (mp : EnvModelM V μ env) {cv cvA : ConstantVal} {c₀ : ConstantInfo},
    MemberValRun μ F env blockNames cv cvA →
    BlockInstalledTT blockNames env mp.base2.cvalE →
    BlockAcvalInstalled blockNames env mp.base2.acval →
    c₀.toConstantVal = cvA → c₀.name = cvA.name →
    (∀ entry, c₀ ≠ .projInfo entry) →
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → ConLeche.reservedBasisNames.contains T = false →
      ConLeche.EtaPins μ env T cvT.levelParams caps →
      caps.etaFields = 0 →
      -- the block-membership facts, v1's `hvT`/`hvC` in P form: they
      -- are what turns `acval T` into `acval (T ++ "_model")` through
      -- `BlockAcvalInstalled`, which is the only bridge between the
      -- law's *subject* and the model artifacts the pins name
      blockNames.contains T = true →
      blockNames.contains caps.etaCtor = true →
      ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
        m₂.acval = acvalWith mp.base2.acval c₀.name
          (fun ψ => mp.base2.acval (cvA.name.str "_model") ψ) →
        ∀ φ' : Name → Nat, EtaLaw m₂ φ' T cvT caps

/-- **The member cons's live unit-like law** (`unitLawKeyS`'s
transpose's obligation): the cons's own former.

**The pins are a premise** (task #161 IND TIER part 2, a repair of
part 1's landing).  `capsOk_cons_member`'s unit row carries no family
premise — the ratified deletion — and part 1 read that as "no premise
at all", but the *pins* are a different datum: `MemberValR` records
`checkMemberVal`'s output and says nothing about `checkUnitThm`, so
without `EtaPins` the law's own statement (`T._model.unitlike` is
stored, its telescope is pinned) is unreachable.  The caller has them
— `memberInstallPM`'s `hpins`, at exactly this `cvA` and these `caps`
— so this is a threading fix, not a strengthening of what the fold
must prove. -/
@[expose] def MemberUnitLaw (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {blockNames : List Name} {env : Env}
    (mp : EnvModelM V μ env) {cv cvA : ConstantVal} {c₀ : ConstantInfo},
    MemberValRun μ F env blockNames cv cvA →
    BlockInstalledTT blockNames env mp.base2.cvalE →
    BlockAcvalInstalled blockNames env mp.base2.acval →
    c₀.toConstantVal = cvA → c₀.name = cvA.name →
    ∀ (cvT : ConstantVal) (caps : IndCaps),
      c₀ = .indInfo cvT caps → caps.unitlike = true →
      ConLeche.reservedBasisNames.contains c₀.name = false →
      ConLeche.EtaPins μ env cvA.name cvA.levelParams caps →
      ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
        m₂.acval = acvalWith mp.base2.acval c₀.name
          (fun ψ => mp.base2.acval (cvA.name.str "_model") ψ) →
        ∀ φ' : Name → Nat, UnitLaw m₂ φ' c₀.name cvT caps

/-- **One member installed at both tiers**, with every carried
invariant stepped — `memberInstallS`'s joint twin. -/
theorem memberInstallPM (hetaP : MemberEtaLaw V)
    (hunitP : MemberUnitLaw V)
    {blockNames : List Name} (mp : EnvModelM V μ env)
    {cv cvA : ConstantVal} {c₀ : ConstantInfo}
    (hmv : MemberValRun μ F env blockNames cv cvA)
    (hI : BlockInstalledTT blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env mp.base2.acval)
    (hbn : blockNames.contains cvA.name = true)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      ConLeche.EtaPins μ env cv.name cv.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (ConLeche.projFnName cv.name 0) = none))
    (hEC : ConLeche.EtaFamiliesClosedO blockNames env)
    (hBP : ConLeche.BlockEtaPinned μ blockNames env)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
      (∃ mI rP, c₀ = .recInfo cvA mI rP []))
    -- the capability arities of an inductive member
    (hicw : ConLeche.IndCapsWF c₀) :
    ∃ mp₁ : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp₁.base2.cvalE = cvalModeled mp.base2.cvalE cvA.name ∧
      mp₁.base2.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => mp.base2.acval (cvA.name.str "_model") ψ) ∧
      BlockInstalledTT blockNames ⟨c₀ :: env.consts⟩
        mp₁.base2.cvalE ∧
      BlockAcvalInstalled blockNames ⟨c₀ :: env.consts⟩
        mp₁.base2.acval ∧
      ConLeche.EtaFamiliesClosedO blockNames ⟨c₀ :: env.consts⟩ ∧
      ConLeche.BlockEtaPinned μ blockNames ⟨c₀ :: env.consts⟩ := by
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, hnres, hpshape, -, -, -, -, -, htr, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have hlpsA : cvA.levelParams = cv.levelParams := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  have hnresA : ConLeche.reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres
  have hpshapeA : cvA.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape
  have hmsA : cvA.name.isModelSuffix = false := hms
  -- the `cvA`-form pins the P row wants
  have hpinsA : ∀ caps, c₀ = .indInfo cvA caps →
      ConLeche.EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (ConLeche.projFnName cvA.name 0) = none) := by
    intro caps2 hceq
    exact ⟨by rw [hnameA, hlpsA]; exact (hpins caps2 hceq).1,
      (hpins caps2 hceq).2.1,
      by rw [hnameA]; exact (hpins caps2 hceq).2.2⟩
  -- **the install's model-free half** (task #161 S7, Wall C): the
  -- extended store's `EnvWF` and the three block invariants are
  -- `memberInstallInv`'s (`SetBase/EnvRCons.lean`), so the P member
  -- cons consults no v1 install at all.
  obtain ⟨hwf₁, hI₁, hEC₁, hBP₁⟩ :=
    memberInstallInv mp.base2.wf hmv hI hbn hpins hEC hBP hc₀cv
      hc₀name hkind hicw
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hpshape0 : c₀.name.isProjFnShape = false := by
    rw [hc₀name]; exact hpshapeA
  -- the P install
  obtain ⟨mp₁, hmp₁ac⟩ :=
    indMember mp hkind hfreshA hnresA hmE hmlps
      (by rw [htypeA]; exact htr) hwf₁
      (memberKey mp hmv hI hIA)
      (fun m₂ hac => capsOk_cons_member mp hfresh0
        (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
              intro _ h <;> exact nomatch h)
        hc₀cv hc₀name
        hpshape0 hbn hpinsA hEC hBP
        (fun T cvT caps hfT hcape hresT hp h0 hbT hbC hfamT m₃ hac₃ φ' =>
          hetaP mp hmv hI hIA hc₀cv hc₀name
            (by rcases hkind with ⟨caps2, rfl⟩ | ⟨nP2, nF2, rfl⟩
                  | ⟨mI2, rP2, rfl⟩ <;>
                intro _ h <;> exact nomatch h)
            T cvT caps hfT hcape hresT
            hp h0 hbT hbC hfamT m₃ hac₃ φ')
        (fun cvT caps hceq hcapu hresT hpT m₃ hac₃ φ' =>
          hunitP mp hmv hI hIA hc₀cv hc₀name cvT caps hceq hcapu hresT
            hpT m₃ hac₃ φ')
        m₂ (by rw [hac, hc₀name]))
  -- the v1 valuation at the extension, read off the leaf equation
  -- through `acval_erase` (no install-API change: the *base* carrier
  -- stays hidden, and only its valuation is ever consumed)
  have hcval₁ : mp₁.base2.cvalE
      = cvalModeled mp.base2.cvalE cvA.name := by
    funext n ψ
    rw [← mp₁.base2.acval_erase n ψ, hmp₁ac]
    by_cases hn : n = cvA.name
    · subst hn
      rw [acvalWith_self]
      show (mp.base2.acval (cvA.name.str "_model") ψ).erase = _
      rw [mp.base2.acval_erase]
      exact (congrFun cvalWith_self ψ).symm
    · rw [acvalWith_ne hn, mp.base2.acval_erase]
      exact (congrFun (cvalWith_ne hn) ψ).symm
  refine ⟨mp₁, hcval₁, hmp₁ac,
    by rw [hcval₁]; exact hI₁, ?_, hEC₁,
    hBP₁⟩
  -- `BlockAcvalInstalled` steps
  intro n hbnn ci hfn ψ
  rw [hmp₁ac]
  by_cases hn : n = cvA.name
  · subst hn
    rw [acvalWith_ne (ConLeche.Name.str_model_ne hmsA), acvalWith_self]
  · rw [acvalWith_ne (ConLeche.Name.str_model_ne hmsA), acvalWith_ne hn]
    refine hIA n hbnn ci ?_ ψ
    rw [ConLeche.Env.find?_cons,
      if_neg (fun hh => hn (by rw [← hh, hc₀name]))] at hfn
    exact hfn

/-- **The member fold, both tiers** — `indMembersS`'s joint twin.  The
non-recursor block members install, the running v1 valuation ends at
the fold's, and the four carried invariants hold of the result.

The same induction serves the *provisioning* fold (`ProvisionRecsR`'s
rule-less recursors), exactly as `memberInstallS` serves both of v1's:
the step's `hkind` disjunct covers all three shapes. -/
theorem indMembersPM (hetaP : MemberEtaLaw V)
    (hunitP : MemberUnitLaw V)
    {μ : CheckMode} {F : Nat} {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} (mp : EnvModelM V μ env)
      {env₂ : Env},
      (∀ ci ∈ members, blockNames.contains ci.name = true) →
      (∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        ConLeche.EtaPins μ env cv.name cv.levelParams caps ∧
          (caps.eta = true →
            blockNames.contains caps.etaCtor = true) ∧
          (caps.eta = true → 0 < caps.etaFields →
            env.find? (ConLeche.projFnName cv.name 0) = none)) →
      IndMembersRun μ F blockNames caps env members env₂ →
      BlockInstalledTT blockNames env mp.base2.cvalE →
      BlockAcvalInstalled blockNames env mp.base2.acval →
      ConLeche.EtaFamiliesClosedO blockNames env →
      ConLeche.BlockEtaPinned μ blockNames env →
      ∃ mp₂ : EnvModelM V μ env₂,
        BlockInstalledTT blockNames env₂ mp₂.base2.cvalE ∧
        BlockAcvalInstalled blockNames env₂ mp₂.base2.acval ∧
        ConLeche.EtaFamiliesClosedO blockNames env₂ ∧
        ConLeche.BlockEtaPinned μ blockNames env₂ := by
  intro members
  induction members with
  | nil =>
    intro env mp env₂ hbn hp h hI hIA hEC hBP
    subst h
    exact ⟨mp, hI, hIA, hEC, hBP⟩
  | cons ci rest ih =>
    intro env mp env₂ hbn hp h hI hIA hEC hBP
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, hms, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    have hfreshA : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci List.mem_cons_self
    have hpshapeA : cvA.name.isProjFnShape = false := by
      rw [hnameA]; exact hcv.2.2.1
    cases ci with
    | indInfo cv caps' =>
      -- the capability arities: the block's pins read the model
      -- former's telescope, and the stored type is the model's under
      -- the block renaming
      have hicw : ConLeche.IndCapsWF (.indInfo cvA caps) := by
        obtain ⟨type', -, hcvA', -, cvm, mval, hint, hfm, -, hty⟩ := id hmv
        refine ConLeche.indCapsWF_of_pins (μ := μ) ?_ hfm hty
        rw [hcvA']
        exact (hp cv caps' List.mem_cons_self).1
      obtain ⟨mp₁, -, -, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
        memberInstallPM hetaP hunitP mp hmv hI hIA hbnA
          (fun caps₃ heq => by
            obtain ⟨-, -, -, rfl⟩ := ConstantInfo.indInfo.inj heq
            exact hp cv caps' List.mem_cons_self)
          hEC hBP rfl rfl (Or.inl ⟨caps, rfl⟩) hicw
      exact ih mp₁
        (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        (fun cv₂ caps₂ hmem => etaMemberData_step hfreshA
          hpshapeA (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)))
        hmatch
        hI₁ hIA₁ hEC₁ hBP₁
    | ctorInfo cv nP nF =>
      obtain ⟨mp₁, -, -, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
        memberInstallPM hetaP hunitP mp hmv hI hIA hbnA
          (fun _ heq => ConstantInfo.noConfusion heq)
          hEC hBP rfl rfl (Or.inr (Or.inl ⟨nP, nF, rfl⟩))
          (fun _ _ heq => ConstantInfo.noConfusion heq)
      exact ih mp₁
        (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        (fun cv₂ caps₂ hmem => etaMemberData_step hfreshA
          hpshapeA (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)))
        hmatch
        hI₁ hIA₁ hEC₁ hBP₁
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- **The recursor provisioning fold, both tiers** —
`provisionRecsS`'s joint twin.  The group's recursors install
rule-less, giving the **self** environment the rule certificates were
checked against *together with a `EnvModelM` at it* — which is what the
iota phase's run-certificate route needs, since `checkSoundAt` runs
at `Rules.RulesInputs.ofSem` and there is no other way to get one at
`envSelf`. -/
theorem provisionRecsPM (hetaP : MemberEtaLaw V)
    (hunitP : MemberUnitLaw V)
    {μ : CheckMode} {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env}
      (mp : EnvModelM V μ envAcc)
      {envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ConLeche.Semantics.ProvisionRecsRun μ F blockNames envAcc
        recs envSelf checked →
      BlockInstalledTT blockNames envAcc mp.base2.cvalE →
      BlockAcvalInstalled blockNames envAcc mp.base2.acval →
      ConLeche.EtaFamiliesClosedO blockNames envAcc →
      ConLeche.BlockEtaPinned μ blockNames envAcc →
      ∃ mS : EnvModelM V μ envSelf,
        BlockInstalledTT blockNames envSelf mS.base2.cvalE ∧
        BlockAcvalInstalled blockNames envSelf mS.base2.acval ∧
        ConLeche.EtaFamiliesClosedO blockNames envSelf ∧
        ConLeche.BlockEtaPinned μ blockNames envSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc mp envSelf checked hbn h hI hIA hEC hBP
    obtain ⟨rfl, -⟩ := h
    exact ⟨mp, hI, hIA, hEC, hBP⟩
  | cons ci rest ih =>
    intro envAcc mp envSelf checked hbn h hI hIA hEC hBP
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hrec, -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    obtain ⟨mp₁, -, -, hI₁, hIA₁, hEC₁, hBP₁⟩ :=
      memberInstallPM hetaP hunitP mp hmv hI hIA
        (by rw [hnameA]; exact hbn ci List.mem_cons_self)
        (fun _ heq => ConstantInfo.noConfusion heq)
        hEC hBP rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
        (fun _ _ heq => ConstantInfo.noConfusion heq)
    exact ih mp₁
      (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
      hrec hI₁ hIA₁ hEC₁ hBP₁

end ConLeche.Model
