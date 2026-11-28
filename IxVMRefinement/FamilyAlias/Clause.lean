import IxVMRefinement.FamilyAlias.Roots
import IxCK.Kernel.Model.FoldLate
import IxCK.Kernel.Model.ThmLevels
import IxCK.Kernel.Model.StoreArKeep

/-! # What the family step keeps of IxCK's half of the carried clause

The carried clause's IxCK half is IxCK's fold invariant with the native families registered so far
(`EnvModelN`) and IxCK's store facts. From the family step's conclusion (an alias group over the
prefix and the renamed record over the family package), across the aliases and the block:

* `envModelN_famStep`: `EnvModelN` at any registry, in every set theory. Each alias extends the
  model it is given (`installAliasPos`), and so does the block (`declIndStepRenJ`), so the generic
  step `EnvModelN.step` applies and the registry is kept as it is: the step registers nothing.
* `foldStoreInv_famStep`: the store invariant, the recursor shape and `K` facts, the typed
  theorems, the eta towers and the table bodies (`FoldStoreInv`).
* `thmLevels_famStep`: the theorems' level parameters. The step stores no theorem: an alias is a
  definition.

The one store fact not proved here is the arity of the stored terms (`StoreArR`). It is stated
as `FamilyKeepsStoreAr`. IxCK has no lemma of this kind for its modeled route. -/

universe u

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal LevelParam EnvExt
  ReducibilityHint Derived auxKey)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The fold invariant with a registry -/

/-- IxCK's fold invariant with a registry across one installed alias: the alias extends the model
it is given. -/
theorem envModelN_installAliasPos {V : Type u} [Ix.Kernel.SetTheory V] {E : Env .anon}
    {R : NativeFam .anon → Prop} (hE : EnvModelN V .verified E R)
    {n : KKey} {d : Derived} {lps : List LevelParam} {ty : KExpr} {tgt : KKey}
    {ci : ConstantInfo .anon} {h : KKey → KKey}
    (hperm : lps.Perm (List.range lps.length))
    (hfresh : E.find? (auxKey n d) = none)
    (hnpt : ∀ T, auxKey n d ≠ Ix.Kernel.projTableName T)
    (hsrc : E.find? tgt = some ci)
    (hlps : ci.toConstantVal.levelParams.Perm (List.range lps.length))
    (htf : ty.hasFvar = false)
    (htp : ty.allLevelParamsDefined lps = true)
    (htr : ty.constsResolve E = true)
    (htb : ty.looseBVarsBounded 0 = true)
    (hA : AliasEnv E h)
    (hty : ExprLvEq (posOf lps (ty.renameConsts h))
      (posOf ci.toConstantVal.levelParams ci.toConstantVal.type)) :
    EnvModelN V .verified
      ⟨.defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev :: E.consts⟩ R :=
  EnvModelN.step V hE (fun mp _ hEE => by
    obtain ⟨mp', -, hext, hEE', -⟩ := installAliasPos mp hEE hperm hfresh hnpt hsrc hlps htf htp
      htr htb (fun ψ => aliasType_reads mp.base2 (renameOkPos_of_aliasEnv mp hA) hperm hlps hty ψ)
    exact ⟨hEE', mp', hext⟩)

/-- IxCK's fold invariant with a registry across an alias group. -/
theorem envModelN_aliasGroup {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    {R : NativeFam .anon → Prop} {h : KKey → KKey} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) (hE : EnvModelN V .verified env R) :
    EnvModelN V .verified ⟨as ++ env.consts⟩ R ∧ AliasEnv ⟨as ++ env.consts⟩ h := by
  induction hg with
  | nil hid => exact ⟨hE, fun k hk => absurd (hid k) hk⟩
  | cons hg' hperm hfresh hnpt hsrc hlps htf htp htr htb hty hk' hrest ih =>
    obtain ⟨hF, hA⟩ := ih
    exact ⟨envModelN_installAliasPos hF hperm hfresh hnpt hsrc hlps htf htp htr htb hA hty,
      aliasEnv_cons hA hperm hfresh hsrc hlps hk' hrest⟩

/-- **IxCK's fold invariant with a registry across the family step**: from an alias group over
the prefix and the renamed record over the family package, `EnvModelN` at the same registry after
the block, in every set theory. -/
theorem envModelN_famStep {env env₂ : Env .anon} {h : KKey → KKey}
    {aliases block : List (ConstantInfo .anon)} {R : NativeFam .anon → Prop}
    (hg : AliasGroup env h aliases)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      EnvModelN V .verified env R → EnvModelN V .verified env₂ R :=
  fun V _ hE =>
    EnvModelN.step V (envModelN_aliasGroup hg hE).1 (fun mp _ hEE =>
      Ix.Kernel.Model.declIndStepRenJ (judgeFrames_famJ h) (fun m => judgeSound_famJ_of m h) mp
        hEE hd)

/-! ## The store facts -/

/-- The store invariant across one installed alias. -/
theorem foldStoreInv_installAlias {E : Env .anon} (hE : FoldStoreInv E)
    {n : KKey} {d : Derived} {lps : List LevelParam} {ty : KExpr} {tgt : KKey}
    {ci : ConstantInfo .anon}
    (hfresh : E.find? (auxKey n d) = none)
    (hnpt : ∀ T, auxKey n d ≠ Ix.Kernel.projTableName T)
    (hsrc : E.find? tgt = some ci)
    (htf : ty.hasFvar = false)
    (htp : ty.allLevelParamsDefined lps = true)
    (htr : ty.constsResolve E = true)
    (htb : ty.looseBVarsBounded 0 = true) :
    FoldStoreInv
      ⟨.defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev :: E.consts⟩ := by
  refine foldStoreInv_cons_defn hE (fun hna => hna n d rfl) hfresh hnpt ⟨htf, htp, htr, htb⟩ ⟨rfl, ?_, ?_, rfl⟩
  · show Expr.allLevelParamsDefined lps (Expr.const tgt (lps.map Level.param)) = true
    simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    simpa [Level.allParamsDefined] using hp
  · show Expr.constsResolve E (Expr.const tgt (lps.map Level.param)) = true
    simp only [Expr.constsResolve, hsrc]
    rfl

/-- The store invariant across an alias group. -/
theorem foldStoreInv_aliasGroup {env : Env .anon} {h : KKey → KKey}
    {as : List (ConstantInfo .anon)} (hg : AliasGroup env h as) (hE : FoldStoreInv env) :
    FoldStoreInv ⟨as ++ env.consts⟩ := by
  induction hg with
  | nil hid => exact hE
  | cons hg' hperm hfresh hnpt hsrc hlps htf htp htr htb hty hk' hrest ih =>
    exact foldStoreInv_installAlias ih hfresh hnpt hsrc htf htp htr htb

/-- **The store invariant across the family step.** -/
theorem foldStoreInv_famStep {env env₂ : Env .anon} {h : KKey → KKey}
    {aliases block : List (ConstantInfo .anon)}
    (hg : AliasGroup env h aliases)
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ block env₂)
    (hE : FoldStoreInv env) : FoldStoreInv env₂ :=
  foldStoreInv_step_declIndRenJ (nP := 0) (judgeFrames_famJ h) (foldStoreInv_aliasGroup hg hE)
    hpin hna hd

/-- The theorems' level parameters across an alias group: an alias is no theorem. -/
theorem thmLevels_aliasGroup {env : Env .anon} {h : KKey → KKey}
    {as : List (ConstantInfo .anon)} (hg : AliasGroup env h as)
    (hT : Ix.Kernel.ThmLevels env) : Ix.Kernel.ThmLevels ⟨as ++ env.consts⟩ := by
  induction hg with
  | nil hid => exact hT
  | cons hg' hperm hfresh hnpt hsrc hlps htf htp htr htb hty hk' hrest ih =>
    exact Ix.Kernel.Model.ThmLevels.step_noThm ih (NewSat.cons (fun _ _ heq => nomatch heq))

/-- **The theorems' level parameters across the family step**: the step stores no theorem. -/
theorem thmLevels_famStep {env env₂ : Env .anon} {h : KKey → KKey}
    {aliases block : List (ConstantInfo .anon)}
    (hg : AliasGroup env h aliases)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ block env₂)
    (hT : Ix.Kernel.ThmLevels env) : Ix.Kernel.ThmLevels env₂ :=
  Ix.Kernel.Model.ThmLevels.step_noThm (thmLevels_aliasGroup hg hT)
    (Ix.Kernel.Model.modeled_newSat (fun _ _ _ heq => nomatch heq)
      (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hd.shape)

/-- **The arity of the stored terms across the family step** (a statement; not proved here):
from an alias group over the prefix and the renamed record over the family package, the stored
terms after the block are arity-correct and resolve when the prefix's are. -/
def FamilyKeepsStoreAr : Prop :=
  ∀ (env env₂ : Env .anon) (h : KKey → KKey) (aliases block : List (ConstantInfo .anon)),
    AliasGroup env h aliases →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ block env₂ →
    StoreArR env → StoreArR env₂

end IxVM.Refinement.Decl.FamilyAlias
