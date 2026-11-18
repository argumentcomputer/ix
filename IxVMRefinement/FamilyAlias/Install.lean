import IxVMRefinement.FamilyAlias.Package
import IxVMRefinement.Decl.ModeledInstall
import IxVMRefinement.Decl.FamilyDeclInv

/-! # Installing a model alias with the member's own level parameters

`installModelAlias` (`IxVMRefinement/Decl/ModeledAux.lean`) installs an alias at positional level
parameters, with the target's leaf at the same assignment. Here the alias keeps the member's own
parameters `lps` (a permutation of the positions) and its leaf at `ψ` is the target's at
`posVal lps ψ`. The target may be any stored constant with positional parameters (an advice model
or an advice `iota` theorem); the alias is a definition whose value is the target at
`lps.map .param`, and whose declared type only has to read as the target's type does. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule
  RecRuleFire IndCaps BasisKind Declaration LevelParam EnvExt ReducibilityHint Derived SwapShList
  openPisAtFvars eqName eqA auxKey projTableName nestedRuleShape recRuleBits recRuleKOf
  recRuleEtaOf isEqHead hasFvar_renameConsts swapSh_find?_corr)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-- **The alias's declared type reads as the target's**, when it is the target's type with the
positions renamed back to the member's parameters, up to a renaming invisible to the reading. -/
theorem aliasType_reads {V : Type u} [Ix.Kernel.SetTheory V] {E : Env .anon}
    (m : EnvModel V E) {h : KKey → KKey} (hro : RenameOkPos m.acval E h)
    {lps : List LevelParam} (hperm : lps.Perm (List.range lps.length))
    {ty tyT : KExpr} (hty : posOf lps (ty.renameConsts h) = tyT) (ψ : LevelParam → Nat) :
    denoteMeta m.acval E ψ 0 ty = denoteMeta m.acval E (posVal lps ψ) 0 tyT := by
  rw [← hty, denoteMeta_posOf m hperm ψ 0, denoteMeta_renameConsts_pos hro]

/-- **Install a model alias with the member's own level parameters**: a definition at a fresh
derived key, with parameters `lps`, value the target at `lps.map .param` and a declared type that
reads as the target's type at the positional valuation. The model extends with the alias's leaf at
`ψ` the target's at `posVal lps ψ`. -/
theorem installAliasPos {V : Type u} [Ix.Kernel.SetTheory V] {μ : CheckMode} {E : Env .anon}
    (mpE : EnvModelM V μ E) (hEE : Ix.Kernel.EtaFamiliesClosed E)
    {n : KKey} {d : Derived} {lps : List LevelParam} {ty : KExpr} {tgt : KKey}
    {ci : ConstantInfo .anon}
    (hperm : lps.Perm (List.range lps.length))
    (hfresh : E.find? (auxKey n d) = none)
    (hnpt : ∀ T, auxKey n d ≠ Ix.Kernel.projTableName T)
    (hsrc : E.find? tgt = some ci)
    (hlps : ci.toConstantVal.levelParams = List.range lps.length)
    (htf : ty.hasFvar = false)
    (htp : ty.allLevelParamsDefined lps = true)
    (htr : ty.constsResolve E = true)
    (htb : ty.looseBVarsBounded 0 = true)
    (hty : ∀ ψ : LevelParam → Nat,
      denoteMeta mpE.base2.acval E ψ 0 ty =
        denoteMeta mpE.base2.acval E (posVal lps ψ) 0 ci.toConstantVal.type) :
    let c₀ : ConstantInfo .anon :=
      .defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev
    ∃ mp' : EnvModelM V μ ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name
        (fun ψ => mpE.base2.acval tgt (posVal lps ψ)) ∧
      ModelExt mpE mp' ∧
      Ix.Kernel.EtaFamiliesClosed ⟨c₀ :: E.consts⟩ ∧
      EnvExt E ⟨c₀ :: E.consts⟩ := by
  let mval_new : KExpr := .const tgt (lps.map .param)
  let c₀ : ConstantInfo .anon := .defnInfo ⟨auxKey n d, lps, ty⟩ mval_new .abbrev
  let A : (LevelParam → Nat) → AnnotTerm := fun ψ => mpE.base2.acval tgt (posVal lps ψ)
  have hnres : Ix.Kernel.reservedBasisNames.contains c₀.name = false :=
    Ix.Kernel.reservedBasisNames_contains_auxKey n d
  have hmem : ci ∈ E.consts := Ix.Kernel.Semantics.Env.find?_mem hsrc
  have hnm : ci.name = tgt := Ix.Kernel.Semantics.Env.find?_name hsrc
  have hvf : mval_new.hasFvar = false := rfl
  have hvp : mval_new.allLevelParamsDefined lps = true := by
    simp only [mval_new, Expr.allLevelParamsDefined, List.all_eq_true]
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    simpa [Level.allParamsDefined] using hp
  have hvr : mval_new.constsResolve E = true := by
    simp only [mval_new, Expr.constsResolve, hsrc]
    rfl
  have hvb : mval_new.looseBVarsBounded 0 = true := rfl
  have hcbT : ConstsBound E ty := constsBound_of_constsResolve _ htr
  have hcomp : ∀ (ψ : LevelParam → Nat) (e : KExpr), ConstsBound E e →
      ∀ {ea : AnnotTerm}, denoteMeta mpE.base2.acval E ψ 0 e = some ea →
      denoteMeta (acvalWith mpE.base2.acval c₀.name A) ⟨c₀ :: E.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 e hcb h
  have hne_tgt : tgt ≠ auxKey n d := fun heq => by
    rw [heq, hfresh] at hsrc; exact nomatch hsrc
  have hstep : ∃ mp' : EnvModelM V μ ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name A := by
    refine declStep_preserves_of_cons mpE (c₀ := c₀) (A := A) hfresh
      (ConsHead.ofFresh
        (Ix.Kernel.EnvWF.cons mpE.base2.wf (Ix.Kernel.structConstWF htf htp
          (Ix.Kernel.Expr.constsResolve_mono htr) htb
          (fun _ _ _ heq => by
            obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
            exact ⟨hvf, hvp, Ix.Kernel.Expr.constsResolve_mono hvr, hvb⟩)
          (fun _ _ _ _ heq => nomatch heq)
          (fun _ heq => nomatch heq)
          (fun _ _ heq => nomatch heq)))
        (fun ψ => mpE.base2.cval_closedL tgt (posVal lps ψ))
        hnres
        (fun _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
      (fun ψ k => mpE.base2.acval_closed tgt (posVal lps ψ) k)
      (fun ψ₁ ψ₂ hp => mpE.base2.acval_params tgt _ hsrc _ _
        (fun p hpm => posVal_congr hp p (hlps ▸ hpm)))
      (fun ψ ρ => mpE.base2.acval_wellDenoted tgt (posVal lps ψ) ρ)
      (fun ψ ρ => mpE.acval_validV tgt (posVal lps ψ) ρ)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta⟩ := mpE.type_reads _ hmem (posVal lps ψ)
      rw [← hty ψ] at hta
      exact ⟨ta, hcomp ψ ty hcbT hta⟩
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem (posVal lps ψ)
      have hta₀' : denoteMeta mpE.base2.acval E ψ 0 ty = some ta₀ := by
        rw [hty ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj
        (hta.symm.trans (hcomp ψ ty hcbT hta₀'))
      rw [htaEq]
      exact mpE.type_wellDenotedV _ hmem (posVal lps ψ) ta₀ hta₀ ρ
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem (posVal lps ψ)
      have hta₀' : denoteMeta mpE.base2.acval E ψ 0 ty = some ta₀ := by
        rw [hty ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj
        (hta.symm.trans (hcomp ψ ty hcbT hta₀'))
      have hm := mpE.mem_type _ hmem (posVal lps ψ) ta₀ hta₀ ρ
      rw [hnm] at hm
      rw [htaEq]
      exact hm
    · intro ψ cv2 value2 ⟨hint2, hdt⟩
      obtain ⟨_, rfl, _⟩ := ConstantInfo.defnInfo.inj hdt
      have hfind_t : (⟨c₀ :: E.consts⟩ : Env .anon).find? tgt = some ci :=
        Env.find?_cons_of_fresh hfresh hsrc
      have hlen_p : (lps.map Level.param).length = ci.toConstantVal.levelParams.length := by
        rw [hlps]; simp
      simp only [mval_new]
      rw [denoteMeta, hfind_t]
      dsimp only
      rw [ite_eq_left hlen_p, show c₀.name = auxKey n d from rfl, acvalWith_ne hne_tgt]
      have hgoal : some (mpE.base2.acval tgt
          (Level.substFn ψ (List.range lps.length) (lps.map Level.param))) = some (A ψ) := rfl
      first
        | (rw [hlps]; done)
        | (rw [hlps]; exact hgoal)
    · exact fun φ => natHeads_cons_offNat mpE
        (ne_of_notReserved hnres reserved_natName)
        (ne_of_notReserved hnres reserved_natZeroName)
        (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
    · exact fun φ => natOps_cons_fresh mpE (mpE.nat_ops φ) (c₀ := c₀) (A := A) hfresh
        (hntc := fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (Or.inr (auxKey_not_mem_natOpNames n d)) _ rfl
    · exact fun φ => divMod_cons_fresh (mpE.div_mod φ) (c₀ := c₀) (A := A) hfresh
        (Or.inr (auxKey_not_mem_natDivModNames n d)) _ rfl
    · exact eqLaw_cons_valueKind mpE.eq_law (c₀ := c₀) (A := A)
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact capsOk_cons_fresh mpE mpE.caps_ok (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact fun φ => recRules_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
    · exact fun φ => towerOk_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
  obtain ⟨mp', hac⟩ := hstep
  refine ⟨mp', hac, ?_,
    Ix.Kernel.EtaFamiliesClosed.cons_nonind hEE hfresh (fun _ _ h => nomatch h),
    envExt_cons_fresh hfresh hnpt⟩
  exact ModelExt.step (c₀ := c₀) (A := A) ModelExt.refl hfresh
    (fun _ _ _ => ConsCrossAt.ofNtc (fun _ heq => nomatch heq))
    (fun _ _ heq => nomatch heq) hac

/-- **An installed alias is an alias of the extended environment**: a renaming that moves the
new key to its target, and otherwise agrees with a renaming of aliases the prefix stores, moves
stored aliases only. -/
theorem aliasEnv_cons {E : Env .anon} {h h' : KKey → KKey} (hA : AliasEnv E h)
    {k tgt : KKey} {lps : List LevelParam} {ty : KExpr} {hint : ReducibilityHint}
    {ci : ConstantInfo .anon}
    (hperm : lps.Perm (List.range lps.length))
    (hfresh : E.find? k = none) (hsrc : E.find? tgt = some ci)
    (hlps : ci.toConstantVal.levelParams = List.range lps.length)
    (hk' : h' k = tgt) (hrest : ∀ x, x ≠ k → h' x = h x) :
    AliasEnv ⟨.defnInfo ⟨k, lps, ty⟩ (.const tgt (lps.map .param)) hint :: E.consts⟩ h' := by
  have hfresh0 : E.find? (ConstantInfo.defnInfo ⟨k, lps, ty⟩ (.const tgt (lps.map .param)) hint :
      ConstantInfo .anon).name = none := hfresh
  intro x hx
  by_cases hxk : x = k
  · subst hxk
    refine ⟨lps, ty, hint, ci, ?_, hperm, ?_, hlps⟩
    · rw [hk']
      exact Ix.Kernel.Env.find?_cons_self _ _
    · rw [hk']
      exact Env.find?_cons_of_fresh hfresh0 hsrc
  · rw [hrest x hxk] at hx
    obtain ⟨lps', ty', hint', ci', hfx, hperm', hft', hlt'⟩ := hA x hx
    refine ⟨lps', ty', hint', ci', ?_, hperm', ?_, hlt'⟩
    · rw [hrest x hxk]
      exact Env.find?_cons_of_fresh hfresh0 hfx
    · rw [hrest x hxk]
      exact Env.find?_cons_of_fresh hfresh0 hft'

/-- **The store invariant across a fresh definition at a derived key** (an alias): every field by
its one-step lemma. -/
theorem foldStoreInv_cons_defn {env : Env .anon} (h : FoldStoreInv env)
    {cv : ConstantVal .anon} {value : KExpr} {hint : ReducibilityHint}
    (hfresh : env.find? cv.name = none)
    (hnpt : ∀ T, cv.name ≠ Ix.Kernel.projTableName T)
    (hty : cv.type.hasFvar = false ∧
      cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env = true ∧ cv.type.looseBVarsBounded 0 = true)
    (hval : value.hasFvar = false ∧ value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧ value.looseBVarsBounded 0 = true) :
    FoldStoreInv ⟨.defnInfo cv value hint :: env.consts⟩ := by
  have hfresh0 : env.find? (ConstantInfo.defnInfo cv value hint).name = none := hfresh
  have hext : EnvExt env ⟨.defnInfo cv value hint :: env.consts⟩ :=
    envExt_cons_fresh hfresh0 hnpt
  have hnew : ∀ (Q : ConstantInfo .anon → Prop), Q (.defnInfo cv value hint) →
      NewSat env ⟨.defnInfo cv value hint :: env.consts⟩ Q := fun Q hQ => NewSat.cons hQ
  have hnorec : ∀ n cv' mI rP rules,
      (⟨.defnInfo cv value hint :: env.consts⟩ : Env .anon).find? n =
        some (.recInfo cv' mI rP rules) → env.find? n = none → False := by
    intro n cv' mI rP rules hf hn
    rcases hnew (fun x => ∀ cv' mI rP rules, x ≠ .recInfo cv' mI rP rules)
      (fun _ _ _ _ heq => nomatch heq) n _ hf with hold | hq
    · rw [hold] at hn; exact nomatch hn
    · exact hq cv' mI rP rules rfl
  have heta := etaShape_step_noEta hext h.etaCtorStored h.etaShape
    (hnew NoEtaInd (fun _ _ heq => nomatch heq))
  exact
    { store := Ix.Kernel.Model.storeInv_consTyped h.store hfresh0 hty
        (fun cv' value' hint' heq => by
          obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
          exact hval)
        (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
        (fun _ _ heq => nomatch heq)
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (hnew Ix.Kernel.Model.NotThm (fun _ _ heq => nomatch heq))
      recK := Ix.Kernel.Model.recK_step h.store h.recK hext.find
        (fun n cv' mI rP rules hf hn => (hnorec n cv' mI rP rules hf hn).elim)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (hnew Ix.Kernel.Model.TowerFree (fun _ _ heq => nomatch heq))
      strongProps := strongEnvProps_step_noProj hext.find h.strongProps
        (hnew Ix.Kernel.Model.NotProj (fun _ heq => nomatch heq))
      recShape := Ix.Kernel.Model.recShape_step h.store h.recShape hext.find
        (fun n cv' mI rP rules hf hn => (hnorec n cv' mI rP rules hf hn).elim)
      etaCtorStored := heta.1
      etaShape := heta.2 }

/-- **The fold invariant across an installed alias.** -/
theorem foldInv_installAliasPos {V : Type u} [Ix.Kernel.SetTheory V] {E : Env .anon}
    (hE : FoldInv V E)
    {n : KKey} {d : Derived} {lps : List LevelParam} {ty : KExpr} {tgt : KKey}
    {ci : ConstantInfo .anon} {h : KKey → KKey}
    (hperm : lps.Perm (List.range lps.length))
    (hfresh : E.find? (auxKey n d) = none)
    (hnpt : ∀ T, auxKey n d ≠ Ix.Kernel.projTableName T)
    (hsrc : E.find? tgt = some ci)
    (hlps : ci.toConstantVal.levelParams = List.range lps.length)
    (htf : ty.hasFvar = false)
    (htp : ty.allLevelParamsDefined lps = true)
    (htr : ty.constsResolve E = true)
    (htb : ty.looseBVarsBounded 0 = true)
    (hA : AliasEnv E h)
    (hty : posOf lps (ty.renameConsts h) = ci.toConstantVal.type) :
    FoldInv V ⟨.defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev ::
      E.consts⟩ := by
  obtain ⟨⟨mp, hT⟩, hEE⟩ := hE.model
  obtain ⟨mp', -, hext, hEE', -⟩ := installAliasPos mp hEE hperm hfresh hnpt hsrc hlps htf htp
    htr htb (fun ψ => aliasType_reads mp.base2 (renameOkPos_of_aliasEnv mp hA) hperm hty ψ)
  refine ⟨⟨⟨mp', hT.of_ext hext⟩, hEE'⟩, ?_⟩
  refine foldStoreInv_cons_defn hE.store hfresh hnpt ⟨htf, htp, htr, htb⟩ ⟨rfl, ?_, ?_, rfl⟩
  · show Expr.allLevelParamsDefined lps (Expr.const tgt (lps.map Level.param)) = true
    simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    simpa [Level.allParamsDefined] using hp
  · show Expr.constsResolve E (Expr.const tgt (lps.map Level.param)) = true
    simp only [Expr.constsResolve, hsrc]
    rfl

/-! ## A group of aliases -/

/-- **An alias group for `h` over `env`**: the listed constants, newest first, are definitions at
fresh derived keys. Each is the alias of a constant stored before it with positional level
parameters, at its own parameters `lps` (a permutation of the positions); its declared type, with
the earlier aliases renamed to their targets and its parameters renamed to positions, is the
target's type. `h` moves the group's keys, each to its target, and nothing else. -/
inductive AliasGroup (env : Env .anon) : (KKey → KKey) → List (ConstantInfo .anon) → Prop where
  | nil {h : KKey → KKey} : (∀ x, h x = x) → AliasGroup env h []
  | cons {h h' : KKey → KKey} {as : List (ConstantInfo .anon)} {n : KKey} {d : Derived}
      {lps : List LevelParam} {ty : KExpr} {tgt : KKey} {ci : ConstantInfo .anon} :
      AliasGroup env h as →
      lps.Perm (List.range lps.length) →
      (⟨as ++ env.consts⟩ : Env .anon).find? (auxKey n d) = none →
      (∀ T, auxKey n d ≠ Ix.Kernel.projTableName T) →
      (⟨as ++ env.consts⟩ : Env .anon).find? tgt = some ci →
      ci.toConstantVal.levelParams = List.range lps.length →
      ty.hasFvar = false →
      ty.allLevelParamsDefined lps = true →
      ty.constsResolve (⟨as ++ env.consts⟩ : Env .anon) = true →
      ty.looseBVarsBounded 0 = true →
      posOf lps (ty.renameConsts h) = ci.toConstantVal.type →
      h' (auxKey n d) = tgt →
      (∀ x, x ≠ auxKey n d → h' x = h x) →
      AliasGroup env h'
        (.defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev :: as)

/-- **The fold invariant across an alias group**, and the group's renaming moves stored aliases
only. -/
theorem foldInv_aliasGroup {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    {h : KKey → KKey} {as : List (ConstantInfo .anon)} (hg : AliasGroup env h as)
    (hE : FoldInv V env) :
    FoldInv V ⟨as ++ env.consts⟩ ∧ AliasEnv ⟨as ++ env.consts⟩ h := by
  induction hg with
  | nil hid => exact ⟨hE, fun k hk => absurd (hid k) hk⟩
  | cons hg' hperm hfresh hnpt hsrc hlps htf htp htr htb hty hk' hrest ih =>
    obtain ⟨hF, hA⟩ := ih
    exact ⟨foldInv_installAliasPos hF hperm hfresh hnpt hsrc hlps htf htp htr htb hA hty,
      aliasEnv_cons hA hperm hfresh hsrc hlps hk' hrest⟩

end IxVM.Refinement.Decl.FamilyAlias
