module

public import IxC.Kernel.Model.IndRenAt
public import IxC.Kernel.Model.IndBlockRunAt
public import IxC.Kernel.Model.IndMember
public import IxC.Kernel.Model.IndMembers
public import IxC.Kernel.Model.IndCaps
public import IxC.Kernel.Model.IndRename
import IxC.Kernel.Model.IndCons
import IxC.Kernel.Model.Annot.BitRename
import IxC.Kernel.Verify.Extend.Block
import IxC.Kernel.Verify.Extend.Ind
import IxC.Kernel.Verify.Extend.Iota
import IxC.Kernel.Semantics.EnvFactsCons
import IxC.Kernel.Semantics.IndBlockRun

public section

/-!
# The member phase, at a given model key

`Model/IndMember.lean` and `Model/IndMembers.lean` over the members' record at the model key
`g` (`MemberValRunJAt`, `Model/IndRenAt.lean`): the block invariants (`BlockInstalledTTAt`,
`BlockAcvalInstalledAt`), the member's key (`memberKeyAt`), one install (`indMemberAt`,
`memberInstallPMAt`) and the two folds (`indMembersPMAt`, `provisionRecsPMAt`), and the block
renaming's soundness (`blockRenameOkAt`).

Where the originals use a member's `isModelSuffix` guard (a model key is no block name), these
take `hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false`.

The modeled route installs every member at the empty capability record, so the folds here are
stated at that record. They carry `BlockNoEta` (no stored block former has η) in place of
`BlockEtaPinned`, and the member cons's two capability laws (`MemberEtaLaw`, `MemberUnitLaw`)
are vacuous: no premise replaces them.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal
  IndCaps ReducibilityHint RecRule)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env md} {J : Judgements md} {g : Key md → Key md}

/-! ## The block invariants at a model key -/

/-- `BlockInstalledTT` at the model key `g`: every installed block member has its model stored at
`g n` (a definition with the same level parameters), its type is the model's under
`blockRenAt g`, and it is valued by the model. -/
@[expose] def BlockInstalledTTAt (g : Key md → Key md) (blockNames : List (Key md))
    (env' : Env md) (cval : TConstVal md) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci, env'.find? n = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (g n) = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ((ci.toConstantVal.type.renameConsts (blockRenAt g blockNames)) == cvm.type) = true ∧
      ∀ ψ : LevelParam → Nat, cval n ψ = cval (g n) ψ

/-- `BlockAcvalInstalled` at the model key `g`: an installed block member's leaf is its
model's. -/
@[expose] def BlockAcvalInstalledAt (g : Key md → Key md) (blockNames : List (Key md))
    (env : Env md) (acval : Key md → (LevelParam → Nat) → AnnotTerm) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci : ConstantInfo md,
    env.find? n = some ci →
    ∀ ψ : LevelParam → Nat, acval (g n) ψ = acval n ψ

/-- No stored block former has the η capability. -/
@[expose] def BlockNoEta (blockNames : List (Key md)) (env : Env md) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ (cv : ConstantVal md) (caps : IndCaps md),
    env.find? n = some (.indInfo cv caps) → caps.eta = false

/-- `cvalModeled` at the model key `g`. -/
@[expose] def cvalModeledAt (g : Key md → Key md) (cval : TConstVal md) (n : Key md) :
    TConstVal md :=
  cvalWith cval n (fun ψ => cval (g n) ψ)

theorem indCaps_empty_eta : ({} : IndCaps md).eta = false := rfl

theorem indCaps_empty_unitlike : ({} : IndCaps md).unitlike = false := rfl

/-- No model key is a block name, when `g` maps block names outside the block. -/
theorem modelKey_ne_of_out {blockNames : List (Key md)}
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false)
    {m : Key md} (hm : blockNames.contains m = true) :
    ∀ n, blockNames.contains n = true → g n ≠ m := by
  intro n hn h
  have := hout n hn
  rw [h, hm] at this
  exact nomatch this

/-- Installing one member valued by its model preserves the fold invariant
(`BlockInstalledTT.step` at the model key `g`). -/
theorem BlockInstalledTTAt.step {blockNames : List (Key md)} {env' : Env md}
    {cval cval₁ : TConstVal md} {ci₁ : ConstantInfo md} {cvm : ConstantVal md}
    {mval : Expr md} {hmcvm : ReducibilityHint}
    (hI : BlockInstalledTTAt g blockNames env' cval)
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false)
    (hbn₁ : blockNames.contains ci₁.name = true)
    (hfm : env'.find? (g ci₁.name) = some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci₁.toConstantVal.levelParams)
    (hren : ((ci₁.toConstantVal.type.renameConsts (blockRenAt g blockNames))
      == cvm.type) = true)
    (hval₁ : ∀ ψ, cval₁ ci₁.name ψ = cval (g ci₁.name) ψ)
    (hpres₁ : ∀ n ψ, n ≠ ci₁.name → cval₁ n ψ = cval n ψ) :
    BlockInstalledTTAt g blockNames ⟨ci₁ :: env'.consts⟩ cval₁ := by
  have hgne := modelKey_ne_of_out hout hbn₁
  intro n hbn ci₂ hf₂
  rw [Ix.Kernel.Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    obtain rfl := Option.some.inj hf₂
    obtain rfl : ci₁.name = n := hh
    refine ⟨cvm, mval, hmcvm, ?_, hlps, hren, ?_⟩
    · rw [Ix.Kernel.Env.find?_cons, if_neg (fun h => hgne _ hbn h.symm)]
      exact hfm
    · intro ψ
      rw [hval₁ ψ, hpres₁ _ ψ (hgne _ hbn)]
  · next hh =>
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hI n hbn ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · rw [Ix.Kernel.Env.find?_cons, if_neg (fun h => hgne _ hbn h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁ _ ψ (fun h => hh h.symm), hpres₁ _ ψ (hgne _ hbn), hv₂ ψ]

/-- **The block renaming at the reading** (`blockRenameOk` at the model key `g`). -/
theorem blockRenameOkAt {blockNames : List (Key md)} {cval : TConstVal md}
    {acval : Key md → (LevelParam → Nat) → AnnotTerm}
    (hIS : BlockInstalledTTAt g blockNames env cval)
    (hIA : BlockAcvalInstalledAt g blockNames env acval)
    (hnames : ∀ n, blockNames.contains n = true →
      (env.find? n).isSome = true) :
    RenameOk acval env (blockRenAt g blockNames) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ciS hfS
    by_cases hc : blockNames.contains n = true
    · rw [blockRenAt_pos hc]
      obtain ⟨cvmS, mvalS, hmS, hfmS, hlpsS, -, -⟩ := hIS n hc ciS hfS
      exact ⟨.defnInfo cvmS mvalS hmS, hfmS, hlpsS⟩
    · rw [blockRenAt_neg hc]
      exact ⟨ciS, hfS, rfl⟩
  · intro n hfS
    by_cases hc : blockNames.contains n = true
    · have := hnames n hc
      rw [hfS] at this
      exact nomatch this
    · rw [blockRenAt_neg hc]
      exact hfS
  · intro n ψ
    by_cases hc : blockNames.contains n = true
    · rw [blockRenAt_pos hc]
      rcases hfS : env.find? n with _ | ciS
      · have := hnames n hc
        rw [hfS] at this
        exact nomatch this
      · exact hIA n hc ciS hfS ψ
    · rw [blockRenAt_neg hc]

/-- `BlockAcvalInstalledAt` crosses the swap. -/
theorem blockAcvalInstalledAt_swap {blockNames : List (Key md)}
    {env₀ env₃ : Env md} {acval : Key md → (LevelParam → Nat) → AnnotTerm}
    (hcg : Ix.Kernel.SwapCongr env₀ env₃)
    (h : BlockAcvalInstalledAt g blockNames env₀ acval) :
    BlockAcvalInstalledAt g blockNames env₃ acval := by
  intro n hbn ci hf ψ
  have hs := hcg.isSomeEq n
  rw [hf] at hs
  rcases hf₀ : env₀.find? n with _ | ci₀
  · rw [hf₀] at hs; exact nomatch hs.symm
  · exact h n hbn ci₀ hf₀ ψ

/-! ## The member's key -/

/-- **The block member's key** (`memberKey` at the model key `g`): the model's leaf inhabits
the checked member's type's reading, graded, at every assignment. -/
theorem memberKeyAt (mp : EnvModelM V μ env) {blockNames : List (Key md)}
    {cv cvA : ConstantVal md}
    (hmv : MemberValRunJAt J g env blockNames cv cvA)
    (hIB : BlockInstalledTTAt g blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalledAt g blockNames env mp.base2.acval)
    (ψ : LevelParam → Nat) :
    ∃ ta, denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.acval (g cvA.name) ψ)
          ∈ˢ interp V ρ ta := by
  obtain ⟨type', hcv, rfl, cvm, mval, hint, hfm, hlpm, hren⟩ := hmv
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hcv
  have hup : ∀ n ci, env.find? n = some ci →
      ∃ ci', env.find? (blockRenAt g blockNames n) = some ci' ∧
        ci'.toConstantVal.levelParams
          = ci.toConstantVal.levelParams := by
    intro n ci hfn
    by_cases hb : blockNames.contains n = true
    · obtain ⟨cvm', mval', hint', hfm', hlp', -, -⟩ := hIB n hb ci hfn
      exact ⟨.defnInfo cvm' mval' hint', by rw [blockRenAt_pos hb]; exact hfm', hlp'⟩
    · exact ⟨ci, by rw [blockRenAt_neg hb]; exact hfn, rfl⟩
  have hval : ∀ (n : Key md) (ci : ConstantInfo md),
      env.find? n = some ci → ∀ ψ' : LevelParam → Nat,
      mp.base2.acval (blockRenAt g blockNames n) ψ' = mp.base2.acval n ψ' := by
    intro n ci hfn ψ'
    by_cases hb : blockNames.contains n = true
    · rw [blockRenAt_pos hb]; exact hIA n hb ci hfn ψ'
    · rw [blockRenAt_neg hb]
  obtain ⟨ta, hta, hokta, hmem⟩ :=
    mp.acval_memType (n := g cv.name) hfm ψ
  refine ⟨ta, ?_, hokta, hmem⟩
  show denoteMeta mp.base2.acval env ψ 0 type' = some ta
  rw [← hta]
  show denoteMeta mp.base2.acval env ψ 0 type'
    = denoteMeta mp.base2.acval env ψ 0 cvm.type
  rw [← denoteMeta_erasedEq (Expr.ErasedEq.of_eq (eq_of_beq hren)) 0]
  exact (denoteMeta_renameConsts_resolve hup hval type' 0 htr).symm

/-! ## The member install -/

/-- **One block member, installed at its model's leaf** (`indMember` with the model at the key
`mk`). -/
theorem indMemberAt (mp : EnvModelM V μ env) {c₀ : ConstantInfo md}
    {cvA : ConstantVal md} {mk : Key md}
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
      (∃ mI rP, c₀ = .recInfo cvA mI rP []))
    (hfresh : env.find? cvA.name = none)
    (hnres : Ix.Kernel.reservedBasisNames.contains cvA.name = false)
    -- the model artifact whose leaf the member takes
    {cvm : ConstantVal md} {mval : Expr md} {hint : ReducibilityHint}
    (hmE : env.find? mk
      = some (.defnInfo cvm mval hint))
    (hmlps : cvm.levelParams = cvA.levelParams)
    -- the member's type resolves in the prefix (`ConstantValR`)
    (hres : cvA.type.constsResolve env = true)
    -- the extended store's well-formedness (`memberInstallInv`'s
    -- first conclusion; task #161 S7 — this is all the v1 install
    -- ever supplied here)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    -- the member's key at the prefix (`memberKey`)
    (hkeyP : ∀ ψ : LevelParam → Nat, ∃ ta,
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.acval mk ψ)
          ∈ˢ interp V ρ ta)
    -- the block fold's row
    (hcaps : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => mp.base2.acval mk ψ) →
      CapsOk m₂) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => mp.base2.acval mk ψ) := by
  -- the three kinds share a constant value and a name
  have hcvA : c₀.toConstantVal = cvA := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;> rfl
  have hname : c₀.name = cvA.name := congrArg ConstantVal.name hcvA
  have hfresh' : env.find? c₀.name = none := by rw [hname]; exact hfresh
  have hnres' : Ix.Kernel.reservedBasisNames.contains c₀.name = false := by
    rw [hname]; exact hnres
  -- provisioning's recursor is rule-less, so `rec_rules` transports
  have hnorules : ∀ cv2 mI2 rP2 rules2,
      c₀ = .recInfo cv2 mI2 rP2 rules2 → rules2 = [] := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro cv2 mI2 rP2 rules2 heq
    · exact nomatch heq
    · exact nomatch heq
    · injection heq with _ _ _ h4
      exact h4.symm
  have hcb : ConstsBound env cvA.type :=
    constsBound_of_constsResolve _ hres
  -- the crossing, forward
  have hcross : ∀ (ψ : LevelParam → Nat) {ta : AnnotTerm},
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta →
      denoteMeta (acvalWith mp.base2.acval c₀.name
          (fun ψ => mp.base2.acval mk ψ))
        ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta := by
    intro ψ ta h
    rw [hcvA]
    exact denoteMeta_cons_fresh_mono hfresh'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro _ h <;> exact nomatch h)
      ψ 0 cvA.type hcb h
  have hgoal := declStep_preserves_of_ind_cons mp (c₀ := c₀)
    (A := fun ψ => mp.base2.acval mk ψ)
    hfresh' hnres'
    (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
          intro _ _ _ h <;> exact nomatch h)
    (ConsHead.ofFresh hwf
      (fun ψ => mp.base2.cval_closedL _ ψ) hnres'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
            intro _ h <;> exact nomatch h)
      (fun cv2 mI2 rP2 rules2 heq r hr => by
        rw [hnorules cv2 mI2 rP2 rules2 heq] at hr
        exact nomatch hr))
    -- the tower: the invariant's own leaf laws, at the model's name
    (fun ψ k => mp.base2.acval_closed _ ψ k)
    (fun ψ₁ ψ₂ hps =>
      mp.base2.acval_params _ _ hmE ψ₁ ψ₂ (by
        intro p hp
        have hp' : p ∈ cvm.levelParams := hp
        rw [hmlps] at hp'
        exact hps p (by rw [hcvA]; exact hp')))
    (fun ψ ρ => mp.base2.acval_wellDenoted _ ψ ρ)
    (fun ψ ρ => mp.acval_validV _ ψ ρ)
    -- the type's reading, crossed
    (fun ψ => by
      obtain ⟨ta, hta, -, -⟩ := hkeyP ψ
      exact ⟨ta, hcross ψ hta⟩)
    (fun ψ ta hta ρ => by
      obtain ⟨ta₀, hta₀, hok, -⟩ := hkeyP ψ
      obtain rfl : ta₀ = ta := Option.some.inj ((hcross ψ hta₀).symm.trans hta)
      exact hok ρ)
    (fun ψ ta hta ρ => by
      obtain ⟨ta₀, hta₀, -, hmem⟩ := hkeyP ψ
      obtain rfl : ta₀ = ta := Option.some.inj ((hcross ψ hta₀).symm.trans hta)
      exact hmem ρ)
    (fun m₂ hac => hcaps m₂ (by rw [hac, hname]))
    (fun m₂ hac φ => recRules_cons_fresh mp hfresh'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro _ h <;> exact nomatch h)
      hnorules m₂ hac φ)
    (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro _ h <;> exact nomatch h)
  rw [hname] at hgoal
  exact hgoal

/-- **The model-free conclusions of a block-member install** (`memberInstallInv` at the model
key `g`, at the empty capability record): the extended store's `EnvWF`, the block invariant, the
η-family closure off the block, and `BlockNoEta`. -/
theorem memberInstallInvAt {μ : CheckMode} {J : Judgements md}
    {blockNames : List (Key md)} {env : Env md} {cval : TConstVal md}
    (hwfE : EnvWF env)
    {cv cvA : ConstantVal md} {c₀ : ConstantInfo md}
    (hmv : MemberValRunJAt J g env blockNames cv cvA)
    -- an annotation of a closed, bounded type is closed and bounded
    (hsyn : ∀ {e e' : Expr md}, J.annot env 0 e e' → e.hasFvar = false →
      e.looseBVarsBounded 0 = true → e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true)
    (hI : BlockInstalledTTAt g blockNames env cval)
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false)
    (hbn : blockNames.contains cvA.name = true)
    (hEC : Ix.Kernel.EtaFamiliesClosedO blockNames env)
    (hNE : BlockNoEta blockNames env)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : BlockMemberKind c₀ cvA)
    -- the member is installed at the empty capability record
    (hcaps : ∀ cv' caps, c₀ = .indInfo cv' caps → caps = {}) :
    EnvWF ⟨c₀ :: env.consts⟩ ∧
      BlockInstalledTTAt g blockNames ⟨c₀ :: env.consts⟩
        (cvalModeledAt g cval cvA.name) ∧
      Ix.Kernel.EtaFamiliesClosedO blockNames ⟨c₀ :: env.consts⟩ ∧
      BlockNoEta blockNames ⟨c₀ :: env.consts⟩ := by
  obtain ⟨type', hcv, hcvA, cvm, mval, hint, hmE, hmlps, hren⟩ := id hmv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, -⟩ := hcv
  obtain ⟨htf', hbt'⟩ := hsyn hann hitf hlbt
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have hlpsA : cvA.levelParams = cv.levelParams := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]
    exact Option.isNone_iff_eq_none.mp hfind
  have hicw : Ix.Kernel.IndCapsWF c₀ := by
    intro cv' caps heq
    rw [hcaps cv' caps heq, indCaps_empty_eta, indCaps_empty_unitlike]
    exact ⟨fun h => nomatch h, fun h => nomatch h⟩
  have hwf : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons hwfE ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hicw⟩
    · rw [hc₀cv, htypeA]; exact htf'
    · rw [hc₀cv, htypeA, hlpsA]; exact htp
    · rw [hc₀cv, htypeA]; exact Expr.constsResolve_mono htr
    · rw [hc₀cv, htypeA]; exact hbt'
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 v2 h2 heq <;> exact nomatch heq
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 mI2 rP2 rules2 heq
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with _ _ _ h4
        intro r hr
        rw [← h4] at hr
        exact nomatch hr
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro tbl heq <;> exact nomatch heq
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hbn0 : blockNames.contains c₀.name = true := by
    rw [hc₀name]; exact hbn
  refine ⟨hwf, ?_, Ix.Kernel.EtaFamiliesClosedO.cons hEC hfresh0 hbn0, ?_⟩
  · refine BlockInstalledTTAt.step hI hout hbn0
      (by rw [hc₀name]; exact hmE)
      (by rw [hc₀cv]; exact hmlps)
      (by rw [hc₀cv]; exact hren)
      (fun ψ => by
        rw [hc₀name]
        exact congrFun cvalWith_self ψ)
      (fun n ψ hn => by
        rw [hc₀name] at hn
        exact congrFun (cvalWith_ne hn) ψ)
  · intro n hn cv' caps hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · rw [hcaps cv' caps (Option.some.inj hf), indCaps_empty_eta]
    · exact hNE n hn cv' caps hf

/-- **One member installed at both tiers** (`memberInstallPM` at the model key `g`, at the empty
capability record), with every carried invariant stepped. -/
theorem memberInstallPMAt {blockNames : List (Key md)} (mp : EnvModelM V μ env)
    {cv cvA : ConstantVal md} {c₀ : ConstantInfo md}
    (hmv : MemberValRunJAt J g env blockNames cv cvA) (hfr : JudgeFrames J env)
    (hI : BlockInstalledTTAt g blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalledAt g blockNames env mp.base2.acval)
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false)
    (hbn : blockNames.contains cvA.name = true)
    (hEC : Ix.Kernel.EtaFamiliesClosedO blockNames env)
    (hNE : BlockNoEta blockNames env)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
      (∃ mI rP, c₀ = .recInfo cvA mI rP []))
    (hcaps : ∀ cv' caps, c₀ = .indInfo cv' caps → caps = {}) :
    ∃ mp₁ : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp₁.base2.cvalE = cvalModeledAt g mp.base2.cvalE cvA.name ∧
      mp₁.base2.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => mp.base2.acval (g cvA.name) ψ) ∧
      BlockInstalledTTAt g blockNames ⟨c₀ :: env.consts⟩ mp₁.base2.cvalE ∧
      BlockAcvalInstalledAt g blockNames ⟨c₀ :: env.consts⟩ mp₁.base2.acval ∧
      Ix.Kernel.EtaFamiliesClosedO blockNames ⟨c₀ :: env.consts⟩ ∧
      BlockNoEta blockNames ⟨c₀ :: env.consts⟩ := by
  obtain ⟨type', hcv, hcvA, cvm, mval, hint, hmE, hmlps, hren⟩ := id hmv
  obtain ⟨hfind, hnres, hpshape, -, -, -, -, -, htr, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  have hnresA : Ix.Kernel.reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres
  have hpshapeA : cvA.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape
  have hgne := modelKey_ne_of_out hout hbn
  -- the empty capability record pins nothing
  have hpinsA : ∀ caps, c₀ = .indInfo cvA caps →
      Ix.Kernel.EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → ∀ C, caps.etaCtor = some C → blockNames.contains C = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (Ix.Kernel.projFnName cvA.name 0) = none) := by
    intro caps heq
    rw [hcaps cvA caps heq, indCaps_empty_eta]
    exact ⟨etaPins_empty, fun h => nomatch h, fun h => nomatch h⟩
  obtain ⟨hwf₁, hI₁, hEC₁, hNE₁⟩ :=
    memberInstallInvAt mp.base2.wf hmv hfr.annot_syntax hI hout hbn hEC hNE hc₀cv
      hc₀name hkind hcaps
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hpshape0 : c₀.name.isProjFnShape = false := by
    rw [hc₀name]; exact hpshapeA
  -- no stored block former has η, so the block is η-pinned vacuously
  have hBP : Ix.Kernel.BlockEtaPinned μ blockNames env := by
    intro n cvS capsS hnb hf he
    rw [hNE n hnb cvS capsS hf] at he
    exact nomatch he
  -- the P install
  obtain ⟨mp₁, hmp₁ac⟩ :=
    indMemberAt mp hkind hfreshA hnresA hmE hmlps
      (by rw [htypeA]; exact htr) hwf₁
      (memberKeyAt mp hmv hI hIA)
      (fun m₂ hac => capsOk_cons_member mp hfresh0
        (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
              intro _ h <;> exact nomatch h)
        hc₀cv hc₀name
        hpshape0 hbn hpinsA hEC hBP
        (fun T cvT caps hfT hcape _ _ _ hbT _ _ _ _ _ => by
          rw [hNE₁ T hbT cvT caps hfT] at hcape
          exact nomatch hcape)
        (fun cvT caps hceq hcapu _ _ _ _ _ => by
          rw [hcaps cvT caps hceq, indCaps_empty_unitlike] at hcapu
          exact nomatch hcapu)
        m₂ (by rw [hac, hc₀name]))
  -- the v1 valuation at the extension, read off the leaf equation
  have hcval₁ : mp₁.base2.cvalE
      = cvalModeledAt g mp.base2.cvalE cvA.name := by
    funext n ψ
    rw [← mp₁.base2.acval_erase n ψ, hmp₁ac]
    by_cases hn : n = cvA.name
    · subst hn
      rw [acvalWith_self]
      show (mp.base2.acval (g cvA.name) ψ).erase = _
      rw [mp.base2.acval_erase]
      exact (congrFun cvalWith_self ψ).symm
    · rw [acvalWith_ne hn, mp.base2.acval_erase]
      exact (congrFun (cvalWith_ne hn) ψ).symm
  refine ⟨mp₁, hcval₁, hmp₁ac,
    by rw [hcval₁]; exact hI₁, ?_, hEC₁, hNE₁⟩
  -- `BlockAcvalInstalledAt` steps
  intro n hbnn ci hfn ψ
  rw [hmp₁ac]
  by_cases hn : n = cvA.name
  · subst hn
    rw [acvalWith_ne (hgne _ hbnn), acvalWith_self]
  · rw [acvalWith_ne (hgne _ hbnn), acvalWith_ne hn]
    refine hIA n hbnn ci ?_ ψ
    rw [Ix.Kernel.Env.find?_cons,
      if_neg (fun hh => hn (by rw [← hh, hc₀name]))] at hfn
    exact hfn

/-- **The member fold, both tiers** (`indMembersPM` at the model key `g`, at the empty
capability record). -/
theorem indMembersPMAt {μ : CheckMode} {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e) {blockNames : List (Key md)}
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false) :
    ∀ (members : List (ConstantInfo md)) {env : Env md} (mp : EnvModelM V μ env)
      {env₂ : Env md},
      (∀ ci ∈ members, blockNames.contains ci.name = true) →
      IndMembersRunJAt J g blockNames {} env members env₂ →
      BlockInstalledTTAt g blockNames env mp.base2.cvalE →
      BlockAcvalInstalledAt g blockNames env mp.base2.acval →
      Ix.Kernel.EtaFamiliesClosedO blockNames env →
      BlockNoEta blockNames env →
      ∃ mp₂ : EnvModelM V μ env₂,
        BlockInstalledTTAt g blockNames env₂ mp₂.base2.cvalE ∧
        BlockAcvalInstalledAt g blockNames env₂ mp₂.base2.acval ∧
        Ix.Kernel.EtaFamiliesClosedO blockNames env₂ ∧
        BlockNoEta blockNames env₂ ∧
        ModelExt mp mp₂ := by
  intro members
  induction members with
  | nil =>
    intro env mp env₂ hbn h hI hIA hEC hNE
    subst h
    exact ⟨mp, hI, hIA, hEC, hNE, .refl⟩
  | cons ci rest ih =>
    intro env mp env₂ hbn h hI hIA hEC hNE
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    have hfreshA : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci List.mem_cons_self
    cases ci with
    | indInfo cv caps' =>
      obtain ⟨mp₁, -, hac₁, hI₁, hIA₁, hEC₁, hNE₁⟩ :=
        memberInstallPMAt mp hmv (hfr _) hI hIA hout hbnA hEC hNE rfl rfl
          (Or.inl ⟨{}, rfl⟩)
          (fun _ _ heq => (ConstantInfo.indInfo.inj heq).2.symm)
      obtain ⟨mp₂, hI₂, hIA₂, hEC₂, hNE₂, hext₂⟩ := ih mp₁
        (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        hmatch hI₁ hIA₁ hEC₁ hNE₁
      exact ⟨mp₂, hI₂, hIA₂, hEC₂, hNE₂,
        ((ModelExt.refl (mp₁ := mp)).plain hac₁ hfreshA).trans hext₂⟩
    | ctorInfo cv nP nF =>
      obtain ⟨mp₁, -, hac₁, hI₁, hIA₁, hEC₁, hNE₁⟩ :=
        memberInstallPMAt mp hmv (hfr _) hI hIA hout hbnA hEC hNE rfl rfl
          (Or.inr (Or.inl ⟨nP, nF, rfl⟩))
          (fun _ _ heq => nomatch heq)
      obtain ⟨mp₂, hI₂, hIA₂, hEC₂, hNE₂, hext₂⟩ := ih mp₁
        (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        hmatch hI₁ hIA₁ hEC₁ hNE₁
      exact ⟨mp₂, hI₂, hIA₂, hEC₂, hNE₂,
        ((ModelExt.refl (mp₁ := mp)).plain hac₁ hfreshA).trans hext₂⟩
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- **The recursor provisioning fold, both tiers** (`provisionRecsPM` at the model key `g`). -/
theorem provisionRecsPMAt {μ : CheckMode} {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e) {blockNames : List (Key md)}
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false) :
    ∀ (recs : List (ConstantInfo md)) {envAcc : Env md}
      (mp : EnvModelM V μ envAcc)
      {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsRunJAt J g blockNames envAcc recs envSelf checked →
      BlockInstalledTTAt g blockNames envAcc mp.base2.cvalE →
      BlockAcvalInstalledAt g blockNames envAcc mp.base2.acval →
      Ix.Kernel.EtaFamiliesClosedO blockNames envAcc →
      BlockNoEta blockNames envAcc →
      ∃ mS : EnvModelM V μ envSelf,
        BlockInstalledTTAt g blockNames envSelf mS.base2.cvalE ∧
        BlockAcvalInstalledAt g blockNames envSelf mS.base2.acval ∧
        Ix.Kernel.EtaFamiliesClosedO blockNames envSelf ∧
        BlockNoEta blockNames envSelf ∧
        ModelExt mp mS := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc mp envSelf checked hbn h hI hIA hEC hNE
    obtain ⟨rfl, -⟩ := h
    exact ⟨mp, hI, hIA, hEC, hNE, .refl⟩
  | cons ci rest ih =>
    intro envAcc mp envSelf checked hbn h hI hIA hEC hNE
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hrec, -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    have hfreshA : envAcc.find? cvA.name = none := by
      rw [hnameA]; exact Option.isNone_iff_eq_none.mp hcv.1
    obtain ⟨mp₁, -, hac₁, hI₁, hIA₁, hEC₁, hNE₁⟩ :=
      memberInstallPMAt mp hmv (hfr _) hI hIA hout
        (by rw [hnameA]; exact hbn ci List.mem_cons_self)
        hEC hNE rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
        (fun _ _ heq => nomatch heq)
    obtain ⟨mS, hIS, hIAS, hECS, hNES, hextS⟩ := ih mp₁
      (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
      hrec hI₁ hIA₁ hEC₁ hNE₁
    exact ⟨mS, hIS, hIAS, hECS, hNES,
      ((ModelExt.refl (mp₁ := mp)).plain hac₁ hfreshA).trans hextS⟩

end Ix.Kernel.Model
