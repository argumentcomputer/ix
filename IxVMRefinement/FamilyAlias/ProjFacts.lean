import IxVMRefinement.FamilyAlias.Assembly
import IxVMRefinement.FamilyAlias.ProjEligible
import IxVMRefinement.Assembly.RecRhsPw
import IxVMRefinement.Decl.NativeCommon
import IxVMRefinement.Decl.ModeledTele
import IxVMRefinement.Levels.Spec

/-! # Projection check witness structures for modeled inductive blocks

Defines the semantic witness structures produced by inverting `KernelModeled::check_projs`
(`CallProjs.lean`) and consumed by projection-table installation (`ProjTableInstall.lean`) and
block load refinement (`BlockLoads.lean`):

* pure telescope helpers (`openDummiesP`, `StripPisZeta`, `stripPis_instantiate1`,
  `stripPisZeta_eq_of_stripPis`, `StripPisZetaSort`, `stripPisZetaSort_eq_of_stripPis`);
* `NativeIndWitness`, `NativeCtorWitness`, `AuxCtorTagWitness`, `UnpackRebuildArgWitness`,
  `UnpackMinorWitness`, `ProjMinorWitness`, `ProjPureBodyWitness`, `ProjPureWitness`;
* `FieldProjFacts`, `projFieldTeleAt`, `MemberProjFacts`, and `BlockProjFacts`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (substLevel)
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam)

set_option linter.unusedVariables false

/-! ## Pure telescope and ζ-stripping helpers -/

/-- Open `m` outer bvars `(c + m - 1, ..., c)` into dummy fvars `(d, ..., d + m - 1)`. -/
def openDummiesP : Nat → Nat → Nat → KExpr → KExpr
  | 0, _, _, e => e
  | m + 1, d, c, e => openDummiesP m (d + 1) c (e.instantiate1 (.fvar d (.sort .zero)) (c + m))

/-- Strip `n` leading `Forall` binders (stepping through any `Let` binders while `n > 0`),
opening each `Forall` with dummy `.fvar d (.sort .zero)`. -/
inductive StripPisZeta : Nat → Nat → KExpr → KExpr → Prop where
  | zero (d : Nat) (e : KExpr) : StripPisZeta 0 d e e
  | forallE (n d : Nat) (ty b : KExpr) (m : Ix.Kernel.BinderMeta) (rem : KExpr) :
      StripPisZeta n (d + 1) (b.instantiate1 (.fvar d (.sort .zero)) 0) rem →
      StripPisZeta (n + 1) d (.forallE ty b m) rem
  | letE (n d : Nat) (ty v b : KExpr) (l : Ix.Kernel.LetMeta) (rem : KExpr) :
      StripPisZeta (n + 1) d (b.instantiate1 v 0) rem →
      StripPisZeta (n + 1) d (.letE ty v b l) rem

theorem stripPis_instantiate1 (v : KExpr) :
    ∀ (n c : Nat) {e rem : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis n = some (bs, rem) →
      ∃ bs', (e.instantiate1 v c).stripPis n = some (bs', rem.instantiate1 v (c + n))
  | 0, c, e, rem, bs, h => by
    injection h with hp; injection hp with _ hr; subst hr
    exact ⟨[], by simp [Expr.stripPis]⟩
  | n + 1, c, .forallE ty b m, rem, bs, h => by
    simp only [Expr.stripPis] at h
    cases hsb : b.stripPis n with
    | none => simp [hsb] at h
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at h; injection h with hp; injection hp with _ hr
      dsimp only at hr; subst hr
      obtain ⟨bs', hbs'⟩ := stripPis_instantiate1 v n (c + 1) hsb
      refine ⟨(ty.instantiate1 v c, m) :: bs', ?_⟩
      simp only [Expr.instantiate1, Expr.stripPis, hbs', Option.map_some]
      rw [show c + 1 + n = c + (n + 1) by omega]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _ _, _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const _ _, _, _, h | _ + 1, _, .app _ _, _, _, h | _ + 1, _, .lam _ _ _, _, _, h
  | _ + 1, _, .letE _ _ _ _, _, _, h | _ + 1, _, .lit _, _, _, h | _ + 1, _, .proj _ _ _, _, _, h =>
    nomatch h

theorem stripPisZeta_eq_of_stripPis :
    ∀ {n d : Nat} {e rem1 rem2 : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis n = some (bs, rem1) → StripPisZeta n d e rem2 →
      rem2 = openDummiesP n d 0 rem1
  | 0, d, e, rem1, rem2, bs, hs, hz => by
    injection hs with hp; injection hp with _ hr; subst hr
    cases hz; rfl
  | n + 1, d, .forallE ty b m, rem1, rem2, bs, hs, hz => by
    simp only [Expr.stripPis] at hs
    cases hsb : b.stripPis n with
    | none => simp [hsb] at hs
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at hs; injection hs with hp; injection hp with _ hr
      dsimp only at hr; subst hr
      cases hz with
      | forallE _ _ _ _ _ _ hz' =>
        obtain ⟨bs', hbs'⟩ := stripPis_instantiate1 (.fvar d (.sort .zero)) n 0 hsb
        simp only [Nat.zero_add] at hbs'
        simp only [openDummiesP, Nat.zero_add]
        exact stripPisZeta_eq_of_stripPis hbs' hz'
  | _ + 1, _, .bvar _, _, _, _, hs, _ | _ + 1, _, .fvar _ _, _, _, _, hs, _
  | _ + 1, _, .sort _, _, _, _, hs, _ | _ + 1, _, .const _ _, _, _, _, hs, _
  | _ + 1, _, .app _ _, _, _, _, hs, _ | _ + 1, _, .lam _ _ _, _, _, _, hs, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, hs, _ | _ + 1, _, .lit _, _, _, _, hs, _
  | _ + 1, _, .proj _ _ _, _, _, _, hs, _ => nomatch hs

/-- Strip `n` leading `Forall` binders (stepping through any `Let` binders, including at `n = 0`)
into `.sort l`. -/
inductive StripPisZetaSort : Nat → Nat → KExpr → KLevel → Prop where
  | srt (d : Nat) (l : KLevel) : StripPisZetaSort 0 d (.sort l) l
  | forallE (n d : Nat) (ty b : KExpr) (m : Ix.Kernel.BinderMeta) (l : KLevel) :
      StripPisZetaSort n (d + 1) (b.instantiate1 (.fvar d (.sort .zero)) 0) l →
      StripPisZetaSort (n + 1) d (.forallE ty b m) l
  | letE (n d : Nat) (ty v b : KExpr) (lM : Ix.Kernel.LetMeta) (l : KLevel) :
      StripPisZetaSort n d (b.instantiate1 v 0) l →
      StripPisZetaSort n d (.letE ty v b lM) l

theorem stripPisZetaSort_eq_of_stripPis :
    ∀ {n d : Nat} {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {l1 l2 : KLevel},
      e.stripPis n = some (bs, .sort l1) → StripPisZetaSort n d e l2 → l2 = l1
  | 0, _, e, _, l1, _, hs, hz => by
    injection hs with hp; injection hp with _ hr; subst hr
    cases hz; rfl
  | n + 1, d, .forallE ty b m, bs, l1, l2, hs, hz => by
    simp only [Expr.stripPis] at hs
    cases hsb : b.stripPis n with
    | none => simp [hsb] at hs
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at hs; injection hs with hp; injection hp with _ hr
      dsimp only at hr; rw [hr] at hsb
      cases hz with
      | forallE _ _ _ _ _ _ hz' =>
        obtain ⟨bs', hbs'⟩ := stripPis_instantiate1 (.fvar d (.sort .zero)) n 0 hsb
        simp only [Expr.instantiate1] at hbs'
        exact stripPisZetaSort_eq_of_stripPis hbs' hz'
  | _ + 1, _, .bvar _, _, _, _, hs, _ | _ + 1, _, .fvar _ _, _, _, _, hs, _
  | _ + 1, _, .sort _, _, _, _, hs, _ | _ + 1, _, .const _ _, _, _, _, hs, _
  | _ + 1, _, .app _ _, _, _, _, hs, _ | _ + 1, _, .lam _ _ _, _, _, _, hs, _
  | _ + 1, _, .letE _ _ _ _, _, _, _, hs, _ | _ + 1, _, .lit _, _, _, _, hs, _
  | _ + 1, _, .proj _ _ _, _, _, _, hs, _ => nomatch hs

/-! ## Witness structures for `check_projs` -/

/-- A native inductive stored in `env` whose record is an `.iPrj` of a native block at `E`. -/
structure NativeIndWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (key : KKey) where
  addr : _root_.Address
  cm : Ixon.Constant
  ip : Ixon.InductiveProj
  cv : ConstantVal .anon
  caps : Ix.Kernel.IndCaps .anon
  hkey : Core.keyOf t addr = key
  hfind : env.find? key = some (.indInfo cv caps)
  hnotRes : Ix.Kernel.reservedBasisNames.contains key = false
  hrec : Ix.Cert.recordAt E addr = some cm
  hinfo : cm.info = .iPrj ip
  hnat : NativeAt E ip.block

/-- A native constructor stored in `env` whose record is a `.cPrj` of a native block at `E`. -/
structure NativeCtorWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (cKey iKey : KKey) (cidx : Nat) where
  addr : _root_.Address
  cm : Ixon.Constant
  cp : Ixon.ConstructorProj
  cv : ConstantVal .anon
  nP : Nat
  nF : Nat
  hkey : Core.keyOf t addr = cKey
  hfind : env.find? cKey = some (.ctorInfo cv nP nF)
  hnotRes : Ix.Kernel.reservedBasisNames.contains cKey = false
  hrec : Ix.Cert.recordAt E addr = some cm
  hinfo : cm.info = .cPrj cp
  hnat : NativeAt E cp.block
  hindKey : Core.keyOf t (Core.iprjAddr cp.block cp.idx.toNat) = iKey
  hcidx : cp.cidx.toNat = cidx

/-- Witness for one constructor `k` of `aux` inside `find_aux_ctor_for_tag`. -/
structure AuxCtorTagWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (auxKey tagKey : KKey) (nP bnl : Nat) (k : Nat) where
  ctorKey : KKey
  cv : ConstantVal .anon
  knf : Nat
  hfind : env.find? ctorKey = some (.ctorInfo cv nP knf)
  hlvls : cv.levelParams.length = bnl
  hperm : cv.levelParams.Perm (List.range bnl)
  kres : KExpr
  kargs : List KExpr
  auxLvls : List KLevel
  hstrip : StripPisZeta (nP + knf) 0 (Core.posOf cv.levelParams cv.type) kres
  hkres : kres = Expr.mkAppN (.const auxKey auxLvls) kargs
  hkargs_len : kargs.length = nP + 1
  ktcKey : KKey
  ktLvls : List KLevel
  ktArgs : List KExpr
  ktcCidx : Nat
  hkidx : kargs[nP]? = some (Expr.mkAppN (.const ktcKey ktLvls) ktArgs)
  hktc : NativeCtorWitness t E env ktcKey tagKey ktcCidx
  hktLvls_len : ktLvls.length = hktc.cv.levelParams.length
  hktArgs_len : ktArgs.length = hktc.nP + hktc.nF

/-- Witness for one field `l < rnf` inside `check_unpack_rebuild_args`. -/
inductive UnpackRebuildArgWitness (auxKey auxRecKey : KKey) (nP bnl anc rnf nIh : Nat)
    (ihArgs : List KExpr) (l : Nat) (arg kfdom : KExpr) : Prop where
  | nonRec
      (harg : arg = .bvar (nIh + rnf - 1 - l)) :
      UnpackRebuildArgWitness auxKey auxRecKey nP bnl anc rnf nIh ihArgs l arg kfdom
  | recField
      (bv : Nat) (ihLvls : List KLevel) (ihSargs : List KExpr) (kfLvls : List KLevel)
      (kfArgs : List KExpr)
      (harg : arg = .bvar bv)
      (hbv_lt : bv < nIh)
      (hih_get : ihArgs[nIh - 1 - bv]? = some (Expr.mkAppN (.const auxRecKey ihLvls) ihSargs))
      (hih_lvls : LvEqList ihLvls ((List.range (bnl + 1)).map .param))
      (hih_len : ihSargs.length = nP + 1 + anc + 2)
      (hih_pref : List.Forall₂ ExprSemEq (ihSargs.take (nP + 1 + anc))
        ((List.range (nP + 1 + anc)).map fun m => .bvar (nP + 1 + anc + rnf - 1 - m)))
      (hih_maj : ihSargs[nP + 1 + anc + 1]? = some (.bvar (rnf - 1 - l)))
      (hkfdom : kfdom = Expr.mkAppN (.const auxKey kfLvls) kfArgs) :
      UnpackRebuildArgWitness auxKey auxRecKey nP bnl anc rnf nIh ihArgs l arg kfdom

/-- Witness for one constructor `k < anc` inside `check_unpack_minors`. -/
structure UnpackMinorWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (auxKey auxRecKey : KKey) (auxRecLps : List LevelParam) (auxCtorKey : KKey)
    (nP bnl anc k : Nat) (minor : KExpr) (rl : RecRule .anon) where
  rnf : Nat
  hrnf : rl.nfields = rnf
  rbs : List (KExpr × Ix.Kernel.BinderMeta)
  rargs : List KExpr
  hr_strip : (Core.posOf auxRecLps rl.rhs).stripLams (nP + 1 + anc + rnf) =
    some (rbs, Expr.mkAppN (.bvar (rnf + anc - 1 - k)) rargs)
  hrargs_ge : rnf ≤ rargs.length
  hrargs_fields : List.Forall₂ ExprSemEq (rargs.take rnf)
    ((List.range rnf).map fun m => .bvar (rnf - 1 - m))
  mbs : List (KExpr × Ix.Kernel.BinderMeta)
  mcKey : KKey
  mcLvls : List KLevel
  margs : List KExpr
  hmin_strip : minor.stripLams (rnf + (rargs.length - rnf)) =
    some (mbs, Expr.mkAppN (.const mcKey mcLvls) margs)
  hbranch :
    -- Passthrough: rebuilds `aux.c_k` unchanged
    (mcKey = auxCtorKey ∧
      (∀ bm ∈ mbs, bm.2.pw = .never) ∧
      LvEqList mcLvls ((List.range bnl).map .param) ∧
      margs.length = nP + rnf ∧
      List.Forall₂ ExprSemEq (margs.take nP)
        ((List.range nP).map fun m => .bvar (nP + rnf + (rargs.length - rnf) - 1 - m)) ∧
      List.Forall₂ ExprSemEq (margs.drop nP)
        ((List.range rnf).map fun m => .bvar (rnf + (rargs.length - rnf) - 1 - m))) ∨
    -- Rebuild: maps to container constructor `mcKey`
    (∃ (cvMC : ConstantVal .anon) (cnp : Nat)
        (mcIndKey : KKey) (cvMCI : ConstantVal .anon) (capsMCI : Ix.Kernel.IndCaps .anon)
        (ini : Nat) (sortL : KLevel)
        (cvAuxC : ConstantVal .anon) (bsP bsF : List (KExpr × Ix.Kernel.BinderMeta))
        (remP remF : KExpr),
      mcKey ≠ auxCtorKey ∧
      env.find? mcKey = some (.ctorInfo cvMC cnp rnf) ∧
      0 < cnp ∧
      mcLvls.length = cvMC.levelParams.length ∧
      margs.length = cnp + rnf ∧
      env.find? mcIndKey = some (.indInfo cvMCI capsMCI) ∧
      cvMCI.levelParams.length = cvMC.levelParams.length ∧
      ((mcKey = Ix.Kernel.eqReflName ∧ rnf = 0 ∧
          env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA ∧
          env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA) ∨
        ∃ cidx, Nonempty (NativeCtorWitness t E env mcKey mcIndKey cidx)) ∧
      StripPisZetaSort (cnp + ini) 0 (Core.posOf cvMCI.levelParams cvMCI.type) sortL ∧
      (((∀ φ, (substLevel sortL mcLvls).eval φ > 0) ∧ ∀ bm ∈ mbs, bm.2.pw = .never) ∨
        ((∀ φ, (substLevel sortL mcLvls).eval φ = 0) ∧ ∀ bm ∈ mbs, bm.2.pw = .ifAllZero [])) ∧
      env.find? auxCtorKey = some (.ctorInfo cvAuxC nP rnf) ∧
      (Core.posOf cvAuxC.levelParams cvAuxC.type).stripPis nP = some (bsP, remP) ∧
      remP.stripPis rnf = some (bsF, remF) ∧
      ∀ l (hl : l < rnf),
        UnpackRebuildArgWitness auxKey auxRecKey nP bnl anc rnf (rargs.length - rnf)
          (rargs.drop rnf) l (margs.drop cnp |>.getD l default) (bsF.map Prod.fst |>.getD l default))

/-- Witness for `check_proj_nested_minor` on `mbody`. -/
inductive ProjMinorWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (auxKey auxRecKey : KKey) (auxRecLps : List LevelParam)
    (arules : List (RecRule .anon)) (auxCtorKeyAt : Nat → KKey) (sbmPw : Ix.Kernel.PropWhen)
    (nP bnl anc nF nIhJ fidx : Nat) (mbody : KExpr) : Prop where
  | bvar
      (hmbody : mbody = .bvar (nIhJ + nF - 1 - fidx)) :
      ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc nF nIhJ
        fidx mbody
  | unpack
      (hsbl_nz : ∀ φ, Ix.Kernel.Model.pwBit φ sbmPw > 0)
      (uKey : KKey) (cvU : ConstantVal .anon) (uval : KExpr) (uHint : Ix.Kernel.ReducibilityHint)
      (uLvls : List KLevel) (uargs : List KExpr)
      (uaKey : KKey) (cvUA : ConstantVal .anon) (uaval : KExpr) (uaHint : Ix.Kernel.ReducibilityHint)
      (ubs : List (KExpr × Ix.Kernel.BinderMeta)) (uaLvls : List KLevel) (uaArgs : List KExpr)
      (uabs : List (KExpr × Ix.Kernel.BinderMeta)) (uarLvls : List KLevel) (uarArgs : List KExpr)
      (hmbody : mbody = Expr.mkAppN (.const uKey uLvls) uargs)
      (hU_nonAux : Decl.NonAuxKey uKey)
      (hfindU : env.find? uKey = some (.defnInfo cvU uval uHint))
      (hU_lvls : cvU.levelParams.length = bnl)
      (hU_perm : cvU.levelParams.Perm (List.range bnl))
      (huLvls : LvEqList uLvls ((List.range bnl).map .param))
      (huargs_gt : nP < uargs.length)
      (huargs_pref : List.Forall₂ ExprSemEq (uargs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 + nF + nIhJ - 1 - m)))
      (huargs_last : uargs[uargs.length - 1]? = some (.bvar (nIhJ + nF - 1 - fidx)))
      (hu_strip : (Core.posOf cvU.levelParams uval).stripLams uargs.length =
        some (ubs, Expr.mkAppN (.const uaKey uaLvls) uaArgs))
      (hu_pw : ∀ bm ∈ ubs, bm.2.pw = .never)
      (hUA_nonAux : Decl.NonAuxKey uaKey)
      (hfindUA : env.find? uaKey = some (.defnInfo cvUA uaval uaHint))
      (hUA_lvls : cvUA.levelParams.length = bnl)
      (hUA_perm : cvUA.levelParams.Perm (List.range bnl))
      (huaLvls : LvEqList uaLvls ((List.range bnl).map .param))
      (hua_len : uaArgs.length = nP + 2)
      (hua_pref : List.Forall₂ ExprSemEq (uaArgs.take nP)
        ((List.range nP).map fun m => .bvar (uargs.length - 1 - m)))
      (hua_last : uaArgs[nP + 1]? = some (.bvar 0))
      (hua_strip : (Core.posOf cvUA.levelParams uaval).stripLams nP =
        some (uabs, Expr.mkAppN (.const auxRecKey uarLvls) uarArgs))
      (hua_pw : ∀ bm ∈ uabs, bm.2.pw = .never)
      (huar_lvls_len : uarLvls.length = bnl + 1)
      (huar_elim_nz : ∀ φ, (uarLvls.getD 0 .zero).eval φ > 0)
      (huar_lvls_drop : LvEqList (uarLvls.drop 1) ((List.range bnl).map .param))
      (huar_len : uarArgs.length = nP + 1 + anc)
      (huar_pref : List.Forall₂ ExprSemEq (uarArgs.take nP)
        ((List.range nP).map fun m => .bvar (nP - 1 - m)))
      (hminors : ∀ k (hk : k < anc),
        ∃ rl, arules[k]? = some rl ∧
          Nonempty (UnpackMinorWitness t E env auxKey auxRecKey auxRecLps (auxCtorKeyAt k) nP bnl anc k
            (uarArgs.drop (nP + 1) |>.getD k default) rl)) :
      ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc nF nIhJ
        fidx mbody

/-- How `pval` reaches `aux.rec` inside `check_proj_pure_body` (directly or via a mutual recursor
model definition). -/
inductive ProjPureBodyWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (auxKey tagCKey auxRecKey : KKey) (auxRecLps : List LevelParam)
    (arules : List (RecRule .anon)) (auxCtorKeyAt : Nat → KKey) (sbmPw : Ix.Kernel.PropWhen)
    (nP bnl anc nF fidx jIdx : Nat) (pvalPos : KExpr) : Prop where
  | direct
      (pbs : List (KExpr × Ix.Kernel.BinderMeta)) (pheadLvls : List KLevel) (pargs : List KExpr)
      (rbsJ : List (KExpr × Ix.Kernel.BinderMeta)) (rargsJ : List KExpr)
      (mbsJ : List (KExpr × Ix.Kernel.BinderMeta)) (mbody : KExpr) (rlJ : RecRule .anon)
      (hp_strip : pvalPos.stripLams (nP + 1) =
        some (pbs, Expr.mkAppN (.const auxRecKey pheadLvls) pargs))
      (hp_pw : ∀ bm ∈ pbs, bm.2.pw = sbmPw)
      (hplvls_len : pheadLvls.length = bnl + 1)
      (hplvls_elim : ∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ sbmPw = 0)
      (hplvls_drop : LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param))
      (hpargs_len : pargs.length = nP + 1 + anc + 2)
      (hpargs_pref : List.Forall₂ ExprSemEq (pargs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 - 1 - m)))
      (hpargs_tag : ∃ tArg, pargs[nP + 1 + anc]? = some tArg ∧
        ExprSemEq tArg (Expr.mkAppN (.const tagCKey ((List.range bnl).map .param))
          ((List.range nP).map fun m => .bvar (nP + 1 - 1 - m))))
      (hpargs_subj : pargs[nP + 1 + anc + 1]? = some (.bvar 0))
      (hrlJ : arules[jIdx]? = some rlJ)
      (hrlJ_nf : rlJ.nfields = nF)
      (hrlJ_strip : (Core.posOf auxRecLps rlJ.rhs).stripLams (nP + 1 + anc + nF) =
        some (rbsJ, Expr.mkAppN (.bvar (nF + anc - 1 - jIdx)) rargsJ))
      (hrargsJ_ge : nF ≤ rargsJ.length)
      (hrargsJ_fields : List.Forall₂ ExprSemEq (rargsJ.take nF)
        ((List.range nF).map fun m => .bvar (nF - 1 - m)))
      (hminJ_strip : (pargs.getD (nP + 1 + jIdx) default).stripLams (nF + (rargsJ.length - nF)) =
        some (mbsJ, mbody))
      (hminJ_pw : ∀ bm ∈ mbsJ, bm.2.pw = sbmPw)
      (hminor : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc
        nF (rargsJ.length - nF) fidx mbody) :
      ProjPureBodyWitness t E env auxKey tagCKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc
        nF fidx jIdx pvalPos
  | viaDefn
      (pheadKey : KKey) (cvR : ConstantVal .anon) (rval : KExpr) (rHint : Ix.Kernel.ReducibilityHint)
      (pbs : List (KExpr × Ix.Kernel.BinderMeta)) (pheadLvls : List KLevel) (pargs : List KExpr)
      (rbs : List (KExpr × Ix.Kernel.BinderMeta)) (arLvls : List KLevel) (rargs : List KExpr)
      (rbsJ : List (KExpr × Ix.Kernel.BinderMeta)) (rargsJ : List KExpr)
      (mbsJ : List (KExpr × Ix.Kernel.BinderMeta)) (mbody : KExpr) (rlJ : RecRule .anon)
      (hp_strip : pvalPos.stripLams (nP + 1) =
        some (pbs, Expr.mkAppN (.const pheadKey pheadLvls) pargs))
      (hp_pw : ∀ bm ∈ pbs, bm.2.pw = sbmPw)
      (hplvls_len : pheadLvls.length = bnl + 1)
      (hplvls_elim : ∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ sbmPw = 0)
      (hplvls_drop : LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param))
      (hR_nonAux : Decl.NonAuxKey pheadKey)
      (hfindR : env.find? pheadKey = some (.defnInfo cvR rval rHint))
      (hR_lvls : cvR.levelParams.length = bnl + 1)
      (hR_perm : cvR.levelParams.Perm (List.range (bnl + 1)))
      (hplen_gt : nP + anc + 1 < pargs.length)
      (hpargs_pref : List.Forall₂ ExprSemEq (pargs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 - 1 - m)))
      (hpargs_subj : pargs[pargs.length - 1]? = some (.bvar 0))
      (hr_strip : (Core.posOf cvR.levelParams rval).stripLams pargs.length =
        some (rbs, Expr.mkAppN (.const auxRecKey arLvls) rargs))
      (hr_pw : ∀ bm ∈ rbs, bm.2.pw = .ifAllZero [0])
      (harLvls : LvEqList arLvls ((List.range (bnl + 1)).map .param))
      (hrargs_len : rargs.length = nP + 1 + anc + 2)
      (hrargs_pref : List.Forall₂ ExprSemEq (rargs.take nP)
        ((List.range nP).map fun m => .bvar (pargs.length - 1 - m)))
      (hrargs_minors : List.Forall₂ ExprSemEq ((rargs.drop (nP + 1)).take anc)
        ((List.range anc).map fun m => .bvar (anc + 1 - 1 - m)))
      (hrargs_tag : ∃ rtArg, rargs[nP + 1 + anc]? = some rtArg ∧
        ExprSemEq rtArg (Expr.mkAppN (.const tagCKey ((List.range bnl).map fun m => .param (1 + m)))
          ((List.range nP).map fun m => .bvar (pargs.length - 1 - m))))
      (hrargs_subj : rargs[nP + 1 + anc + 1]? = some (.bvar 0))
      (hrlJ : arules[jIdx]? = some rlJ)
      (hrlJ_nf : rlJ.nfields = nF)
      (hrlJ_strip : (Core.posOf auxRecLps rlJ.rhs).stripLams (nP + 1 + anc + nF) =
        some (rbsJ, Expr.mkAppN (.bvar (nF + anc - 1 - jIdx)) rargsJ))
      (hrargsJ_ge : nF ≤ rargsJ.length)
      (hrargsJ_fields : List.Forall₂ ExprSemEq (rargsJ.take nF)
        ((List.range nF).map fun m => .bvar (nF - 1 - m)))
      (hminJ_strip : (pargs.getD (nP + (pargs.length - nP - (anc + 1)) + jIdx) default).stripLams
        (nF + (rargsJ.length - nF)) = some (mbsJ, mbody))
      (hminJ_pw : ∀ bm ∈ mbsJ, bm.2.pw = sbmPw)
      (hminor : ProjMinorWitness t E env auxKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc
        nF (rargsJ.length - nF) fidx mbody) :
      ProjPureBodyWitness t E env auxKey tagCKey auxRecKey auxRecLps arules auxCtorKeyAt sbmPw nP bnl anc
        nF fidx jIdx pvalPos

/-- Complete coherence witness produced by `KernelModeled::check_proj_pure` when `nP > 0 ∨ bnl > 0`
and the field is not unconditionally `Prop`. -/
structure ProjPureWitness (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (tModelKey : KKey) (pvalPos ctyMPos rawDom : KExpr) (sbmPw : Ix.Kernel.PropWhen)
    (nP bnl nF fidx : Nat) where
  cvmT : ConstantVal .anon
  mvalT : KExpr
  hintT : Ix.Kernel.ReducibilityHint
  hTM_nonAux : Decl.NonAuxKey tModelKey
  hfindTM : env.find? tModelKey = some (.defnInfo cvmT mvalT hintT)
  hTM_lvls : cvmT.levelParams.length = bnl
  hTM_perm : cvmT.levelParams.Perm (List.range bnl)
  auxKey : KKey
  tagKey : KKey
  tagCKey : KKey
  tagCidx : Nat
  tmbs : List (KExpr × Ix.Kernel.BinderMeta)
  auxLvls : List KLevel
  auxArgs : List KExpr
  tcLvls : List KLevel
  tcArgs : List KExpr
  hTM_strip : (Core.posOf cvmT.levelParams mvalT).stripLams nP =
    some (tmbs, Expr.mkAppN (.const auxKey auxLvls) auxArgs)
  hTM_pw : ∀ bm ∈ tmbs, bm.2.pw = .never
  hauxLvls : LvEqList auxLvls ((List.range bnl).map .param)
  hauxArgs_len : auxArgs.length = nP + 1
  hauxArgs_pref : List.Forall₂ ExprSemEq (auxArgs.take nP)
    ((List.range nP).map fun m => .bvar (nP - 1 - m))
  hauxArgs_tag : auxArgs[nP]? = some (Expr.mkAppN (.const tagCKey tcLvls) tcArgs)
  htcLvls : LvEqList tcLvls ((List.range bnl).map .param)
  htcArgs : List.Forall₂ ExprSemEq tcArgs ((List.range nP).map fun m => .bvar (nP - 1 - m))
  tagCWit : NativeCtorWitness t E env tagCKey tagKey tagCidx
  htagC_lvls : tagCWit.cv.levelParams.length = bnl
  htagC_nP : tagCWit.nP = nP
  htagC_nF : tagCWit.nF = 0
  tagIndWit : NativeIndWitness t E env tagKey
  htagInd_lvls : tagIndWit.cv.levelParams.length = bnl
  htagInd_neNat : tagKey ≠ Ix.Kernel.natName
  htagInd_idx : tagIndWit.ip.idx.toNat = 0
  htagInd_rec : ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
    Ix.Cert.recordAt E tagIndWit.ip.block = some cb ∧ cb.info = .muts ms ∧
    ms[0]? = some (.indc ind) ∧ ind.params.toNat = nP ∧ ind.indices.toNat = 0 ∧
    1 < ind.ctors.size
  tagSortBs : List (KExpr × Ix.Kernel.BinderMeta)
  tagSortU : KLevel
  htagInd_sort : (Core.posOf tagIndWit.cv.levelParams tagIndWit.cv.type).stripPis nP =
    some (tagSortBs, .sort tagSortU)
  htagInd_nz : ∀ φ, (substLevel tagSortU ((List.range bnl).map .param)).eval φ > 0
  auxIndWit : NativeIndWitness t E env auxKey
  hauxInd_lvls : auxIndWit.cv.levelParams.length = bnl
  hauxInd_idx : auxIndWit.ip.idx.toNat = 0
  auxSortBs : List (KExpr × Ix.Kernel.BinderMeta)
  auxSortU : KLevel
  hauxInd_sort : (Core.posOf auxIndWit.cv.levelParams auxIndWit.cv.type).stripPis (nP + 1) =
    some (auxSortBs, .sort auxSortU)
  hauxInd_nz : ∀ φ, (substLevel auxSortU ((List.range bnl).map .param)).eval φ > 0
  anc : Nat
  hauxInd_rec : ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
    Ix.Cert.recordAt E auxIndWit.ip.block = some cb ∧ cb.info = .muts ms ∧
    ms[0]? = some (.indc ind) ∧ ind.params.toNat = nP ∧ ind.indices.toNat = 1 ∧
    ind.ctors.size = anc
  jIdx : Nat
  hjIdx_lt : jIdx < anc
  auxCtorKeyAt : Nat → KKey
  hauxCtorKeyAt : ∀ k, auxCtorKeyAt k = Core.keyOf t (Core.cprjAddr auxIndWit.ip.block 0 k)
  hauxCtors : ∀ k < anc, ∃ w : AuxCtorTagWitness t E env auxKey tagKey nP bnl k,
    w.ctorKey = auxCtorKeyAt k ∧
    (k = jIdx → w.ktcCidx = tagCidx ∧ w.knf = nF) ∧
    (k ≠ jIdx → w.ktcCidx ≠ tagCidx)
  auxRecKey : KKey
  cvAuxRec : ConstantVal .anon
  arules : List (RecRule .anon)
  hfindAuxRec : env.find? auxRecKey =
    some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules)
  hAuxRec_lvls : cvAuxRec.levelParams.length = bnl + 1
  hAuxRec_perm : cvAuxRec.levelParams.Perm (List.range (bnl + 1))
  hrecCtor : ∀ j rl, arules[j]? = some rl → rl.ctor = auxCtorKeyAt j
  hauxRec_famBlk : ∃ (aR : _root_.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
      (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
    Core.keyOf t aR = auxRecKey ∧ RecHostAt E aR cHost rcR ∧
    recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
    Ix.Cert.recordAt E p0 = some cm0 ∧ cm0.info = .iPrj ip0 ∧ ip0.block = auxIndWit.ip.block
  majBs : List (KExpr × Ix.Kernel.BinderMeta)
  majDom : KExpr
  majBody : KExpr
  majBm : Ix.Kernel.BinderMeta
  majLvls : List KLevel
  majArgs : List KExpr
  hAuxRec_maj : (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
    some (majBs, .forallE majDom majBody majBm)
  hmajDom : majDom = Expr.mkAppN (.const auxKey majLvls) majArgs
  hmajLvls : LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m))
  hmajArgs_len : majArgs.length = nP + 1
  hmajArgs_pref : List.Forall₂ ExprSemEq (majArgs.take nP)
    ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m))
  hmajArgs_idx : majArgs[nP]? = some (.bvar 0)
  hsort_poly : (∀ φ, Ix.Kernel.Model.pwBit φ sbmPw > 0) ∨
    ((∀ i < fidx, rawDom.hasLooseBVar i = false) ∧
      ∃ (cvAuxC : ConstantVal .anon) (kbs : List (KExpr × Ix.Kernel.BinderMeta)) (krest : KExpr)
        (cbs : List (KExpr × Ix.Kernel.BinderMeta)) (crest : KExpr)
        (kfbs : List (KExpr × Ix.Kernel.BinderMeta)) (kfdom kfrest : KExpr)
        (kfbm : Ix.Kernel.BinderMeta),
      env.find? (auxCtorKeyAt jIdx) = some (.ctorInfo cvAuxC nP nF) ∧
      (Core.posOf cvAuxC.levelParams cvAuxC.type).stripPis nP = some (kbs, krest) ∧
      ctyMPos.stripPis nP = some (cbs, crest) ∧
      List.Forall₂ ExprSemEq (kbs.map Prod.fst) (cbs.map Prod.fst) ∧
      krest.stripPis fidx = some (kfbs, .forallE kfdom kfrest kfbm) ∧
      ExprSemEq kfdom rawDom)
  hbody : ProjPureBodyWitness t E env auxKey tagCKey auxRecKey cvAuxRec.levelParams arules
    auxCtorKeyAt sbmPw nP bnl anc nF fidx jIdx pvalPos

/-- One field `fidx < nF` of an eligible modeled inductive member checked by `check_member_projs`. -/
structure FieldProjFacts (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (tModelKey cModelKey : KKey) (tyTPos ctyMPos : KExpr) (nP bnl nF fidx : Nat)
    (fdom rawDom : KExpr) where
  projKey : KKey
  cvProj : ConstantVal .anon
  projVal : KExpr
  projHint : Ix.Kernel.ReducibilityHint
  hProj_nonAux : Decl.NonAuxKey projKey
  hfindProj : env.find? projKey = some (.defnInfo cvProj projVal projHint)
  hProj_lvls : cvProj.levelParams.length = bnl
  hProj_perm : cvProj.levelParams.Perm (List.range bnl)
  iotaKey : KKey
  cvIota : ConstantVal .anon
  iotaVal : KExpr
  hfindIota : env.find? iotaKey = some (.thmInfo cvIota iotaVal)
  hIota_lvls : cvIota.levelParams.length = bnl
  hIota_perm : cvIota.levelParams.Perm (List.range bnl)
  -- Type of `proj_i`
  pbsP : List (KExpr × Ix.Kernel.BinderMeta)
  tbsP : List (KExpr × Ix.Kernel.BinderMeta)
  tremP : KExpr
  sdom : KExpr
  rdom : KExpr
  sbm : Ix.Kernel.BinderMeta
  hProj_strip : (Core.posOf cvProj.levelParams cvProj.type).stripPis nP =
    some (pbsP, .forallE sdom rdom sbm)
  hT_strip : tyTPos.stripPis nP = some (tbsP, tremP)
  hProj_pdoms : List.Forall₂ ExprSemEq (pbsP.map Prod.fst) (tbsP.map Prod.fst)
  hProj_sdom : ExprSemEq sdom
    (Expr.mkAppN (.const tModelKey ((List.range bnl).map .param))
      ((List.range nP).map fun m => .bvar (nP - 1 - m)))
  hProj_rdom : ExprSemEq (openDummiesP (nP + 1) 0 0 rdom) fdom
  -- Type of `iota_i`
  ibsI : List (KExpr × Ix.Kernel.BinderMeta)
  cbsI : List (KExpr × Ix.Kernel.BinderMeta)
  cremI : KExpr
  uEq : KLevel
  alpha : KExpr
  lhs : KExpr
  hIota_strip : (Core.posOf cvIota.levelParams cvIota.type).stripPis (nP + nF) =
    some (ibsI, Expr.mkAppN (.const Ix.Kernel.eqName [uEq]) [alpha, lhs, .bvar (nF - 1 - fidx)])
  hC_strip : ctyMPos.stripPis (nP + nF) = some (cbsI, cremI)
  hIota_doms : List.Forall₂ ExprSemEq (ibsI.map Prod.fst) (cbsI.map Prod.fst)
  hIota_alpha : ExprSemEq alpha (rawDom.liftLooseBVars (nF - fidx) 0)
  hIota_lhs : ExprSemEq lhs
    (Expr.mkAppN (.const projKey ((List.range bnl).map .param))
      (((List.range nP).map fun m => .bvar (nP + nF - 1 - m)) ++
        [Expr.mkAppN (.const cModelKey ((List.range bnl).map .param))
          (((List.range nP).map fun m => .bvar (nP + nF - 1 - m)) ++
            ((List.range nF).map fun m => .bvar (nF - 1 - m)))]))
  -- Purity coherence gate (when `nP > 0 ∨ bnl > 0` and field is not unconditionally `Prop`)
  hpure : (nP = 0 ∧ bnl = 0) ∨
    (∀ φ, Ix.Kernel.Model.pwBit φ sbm.pw = 0) ∨
    Nonempty (ProjPureWitness t E env tModelKey (Core.posOf cvProj.levelParams projVal)
      ctyMPos rawDom sbm.pw nP bnl nF fidx)

/-- Folded telescope state after `k` fields of `check_member_projs`: instantiates `ctyMPos`'s
`nP` parameters with `.fvar 0 .. .fvar (nP - 1)` and each field `j < k` with
`projKey j param_lvls (.fvar 0) ... (.fvar (nP - 1)) (.fvar nP)`. -/
def projFieldTeleAt (ctyMPos : KExpr) (nP bnl : Nat) (projKeyAt : Nat → KKey) :
    Nat → Option KExpr
  | 0 => (Expr.instPisAt ((List.range nP).map fun m => .fvar m (.sort .zero)) ctyMPos).map Prod.snd
  | k + 1 =>
    match projFieldTeleAt ctyMPos nP bnl projKeyAt k with
    | some (.forallE _ frest _) =>
      let projApp := Expr.mkAppN (.const (projKeyAt k) ((List.range bnl).map .param))
        (((List.range nP).map fun m => .fvar m (.sort .zero)) ++ [.fvar nP (.sort .zero)])
      some (frest.instantiate1 projApp 0)
    | _ => none

/-- Full projection check facts for one eligible member `pos` of a modeled block. -/
structure MemberProjFacts (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (B : _root_.Address) (ms : Array Ixon.MutConst) (g : KKey → KKey)
    (pos : Nat) (tyA_T tyA_C : KExpr) where
  ind : Ixon.Inductive
  ct : Ixon.Constructor
  hms : ms[pos]? = some (.indc ind)
  hct : ind.ctors[0]? = some ct
  hni0 : ind.indices.toNat = 0
  hnc1 : ind.ctors.size = 1
  hcnl : ct.lvls.toNat = ind.lvls.toNat
  hcnp : ct.params.toNat = ind.params.toNat
  hnf_pos : 0 < ct.fields.toNat
  -- Result sort of `tyA_T`
  bsT : List (KExpr × Ix.Kernel.BinderMeta)
  structSort : KLevel
  hT_sort : tyA_T.stripPis ind.params.toNat = some (bsT, .sort structSort)
  hT_sort_nz : structSort.isNeverZero = true
  -- Return type of `tyA_C`
  bsC : List (KExpr × Ix.Kernel.BinderMeta)
  cret : KExpr
  hC_ret : (Core.posOf (List.range ct.lvls.toNat) tyA_C).stripPis (ind.params.toNat + ct.fields.toNat) =
    some (bsC, cret)
  hC_ret_eq : cret = Expr.mkAppN
    (.const (Core.keyOf t (Core.iprjAddr B pos)) ((List.range ind.lvls.toNat).map .param))
    ((List.range ind.params.toNat).map fun m =>
      .bvar (ind.params.toNat + ct.fields.toNat - 1 - m))
  -- Per-field projection models, iota theorems, and coherence witnesses
  projKeyAt : Nat → KKey
  hfields : ∀ fidx (hf : fidx < ct.fields.toNat),
    ∃ (fdom frest rawDom : KExpr) (fbm : Ix.Kernel.BinderMeta)
      (bsRaw : List (KExpr × Ix.Kernel.BinderMeta)) (remRaw : KExpr),
      projFieldTeleAt (Decl.renameAll g (Core.posOf (List.range ct.lvls.toNat) tyA_C))
        ind.params.toNat ind.lvls.toNat projKeyAt fidx = some (.forallE fdom frest fbm) ∧
      (Decl.renameAll g (Core.posOf (List.range ct.lvls.toNat) tyA_C)).stripPis
        (ind.params.toNat + ct.fields.toNat) = some (bsRaw, remRaw) ∧
      (bsRaw.map Prod.fst)[ind.params.toNat + fidx]? = some rawDom ∧
      ∃ fp : FieldProjFacts t E env
          (g (Core.keyOf t (Core.iprjAddr B pos)))
          (g (Core.keyOf t (Core.cprjAddr B pos 0)))
          (Core.posOf (List.range ind.lvls.toNat) tyA_T)
          (Decl.renameAll g (Core.posOf (List.range ct.lvls.toNat) tyA_C))
          ind.params.toNat ind.lvls.toNat ct.fields.toNat fidx fdom rawDom,
        fp.projKey = projKeyAt fidx

/-- Whole-block projection facts returned by `check_projs_facts` alongside `SelectedForms`. -/
structure BlockProjFacts (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) (g : KKey → KKey) where
  hms_size : ms.size < UInt64.size
  elig : Nat → Bool
  indTy₀ : Nat → KExpr
  ctorTy₀ : Nat → Nat → KExpr
  canonE₀ : BlockCanonReadings t E₀ B cb ms indTy₀ ctorTy₀
  eligDet : ∀ {E₂ : Ixon.Env},
    BlockCanonReadings t E₂ B cb ms indTy₀ ctorTy₀ →
    ∀ {b₂ : Bytes.Address} {bp₂ r₂ : SourceValue F} {pos : Nat},
      pos < ms.size →
      ∀ {h₂ h₂' : Heap F} {cs₂ : List (Call F)},
        Bytes.RepAddressRef addrTy h₂ b₂ bp₂ → ixAddr b₂ = B →
        ¬ View.HashedCollision { env := E₂ } [] cs₂ → Bounded cs₂ →
        ObsFn Obs.W "KernelModeled::modeled_proj_eligible"
          [bp₂, .field (pos : F)] h₂ r₂ h₂' cs₂ →
        r₂ = .field (if elig pos then 1 else 0)
  atPos : ∀ pos < ms.size, elig pos = true →
    ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor)
      (kT kC : Nat) (ciT ciC : ConstantInfo .anon) (tyA_T tyA_C : KExpr),
      ms[pos]? = some (.indc ind) ∧ ind.ctors[0]? = some ct ∧
      (Decl.FamilyAlias.nonrecsOf blk)[kT]? = some ciT ∧
      ciT.name = Core.keyOf t (Core.iprjAddr B pos) ∧
      tys[kT]? = some tyA_T ∧
      (Decl.FamilyAlias.nonrecsOf blk)[kC]? = some ciC ∧
      ciC.name = Core.keyOf t (Core.cprjAddr B pos 0) ∧
      tys[kC]? = some tyA_C ∧
      Nonempty (MemberProjFacts t E env B ms g pos tyA_T tyA_C)

end IxVM.Refinement.Typing.FamilyAlias
