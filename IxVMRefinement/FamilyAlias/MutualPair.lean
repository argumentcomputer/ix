import IxVMRefinement.FamilyAlias.Package
import IxC.Kernel.Model.IndRenRecord

/-! # A mutual pair `A B : Type u` with large recursors, at IxC's own record

Explicit kernel data for

    mutual
      inductive A : Type u | mk : A
      inductive B : Type u | mk : B
    end

with level parameters `[0]` for the types and constructors (`u` is `0`) and `[1, 0]` for the
recursors (`n :: range n` at `n = 1`: the motive universe `v` is `1`). The keys of the block, of
the advice models and the block renaming `f` are arbitrary.

* `memberValRunJ_of_alias` (any member of any block): with the alias at `auxKey X .model` stated
  at the member's own level parameters, the member record's lookup, its level-list conjunct and
  its type conjunct hold by construction.
* `iotaThm_recA`: the canonical rule's theorem record `IotaThmRunJ` of `A.rec` at the real frame
  `[1, 0]`, for a theorem copy stated at `[1, 0]` with head `f A.rec` and major `f A.mk`. Every
  literal conjunct holds by computation; the package's judgements are the hypothesis `hJ`.
* `recA_plain`, `recA_pos_not_plain`: the rule is canonical in the real frame and not in the
  positional one. -/

namespace IxVM.Refinement.Decl.FamilyAlias.MutualPair

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  LevelParam EnvExt ReducibilityHint Derived openPisAtFvars eqName eqA auxKey nestedRuleShape
  recRuleBits isEqHead hasFvar_renameConsts)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## Helpers -/

theorem beq_of_eq {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a = b) : (a == b) = true :=
  beq_iff_eq.mpr h

theorem isEqHead_eq (u : KLevel) : isEqHead (Expr.const eqName [u] : KExpr) = true := by
  show ((eqName : KKey) == eqName) = true
  exact beq_iff_eq.mpr rfl

/-! ## The member record, for any member -/

/-- **The member record holds by construction at an alias with the member's own parameters**:
the lookup at `auxKey X .model`, the level-list conjunct `cvm.levelParams = cvA.levelParams` and
the type conjunct, for every member, a recursor with parameters `n :: range n` included. The
front door (`ConstantValRunJ`) is the hypothesis. -/
theorem memberValRunJ_of_alias {J : Judgements .anon} {env' : Env .anon}
    {blockNames : List KKey} {cv : ConstantVal .anon} {type' mval : KExpr}
    {hint : ReducibilityHint}
    (hcv : ConstantValRunJ J env' cv type') (hsuf : cv.name.isModelSuffix = false)
    (hfind : env'.find? (auxKey cv.name .model) = some (.defnInfo
      ⟨auxKey cv.name .model, cv.levelParams,
        type'.renameConsts (fun n => if blockNames.contains n then auxKey n .model else n)⟩
      mval hint)) :
    MemberValRunJ J env' blockNames cv ⟨cv.name, cv.levelParams, type'⟩ :=
  ⟨type', hcv, rfl, hsuf, _, mval, hint, hfind, rfl, beq_iff_eq.mpr rfl⟩

/-! ## The family's data -/

/-- The binder metadata used throughout. -/
def bm : BinderMeta := default

/-- `X.{u} → Sort v`, a motive's type. -/
def motiveTy (kX : KKey) : KExpr :=
  .forallE (.const kX [.param 0]) (.sort (.param 1)) bm

/-- The level parameters of the large recursors: `n :: range n` at `n = 1`. -/
def lpsR : List LevelParam := [1, 0]

theorem lpsR_perm : lpsR.Perm (List.range lpsR.length) := by decide

section Family

variable (kA kB kMkA kMkB kRecA : KKey) (mA mB mMkA mMkB : KKey) (f : KKey → KKey)

/-- `A.rec.{v, u} : {motive_1 : A → Sort v} → {motive_2 : B → Sort v} → motive_1 A.mk →
motive_2 B.mk → (t : A) → motive_1 t`. -/
def tyRecA : KExpr :=
  .forallE (motiveTy kA) (
  .forallE (motiveTy kB) (
  .forallE (.app (.bvar 1) (.const kMkA [.param 0])) (
  .forallE (.app (.bvar 1) (.const kMkB [.param 0])) (
  .forallE (.const kA [.param 0]) (.app (.bvar 4) (.bvar 0)) bm) bm) bm) bm) bm

/-- The rule of `A.rec` at `A.mk`: `fun motive_1 motive_2 hA hB => hA`. -/
def rhsA : KExpr :=
  .lam (motiveTy kA) (
  .lam (motiveTy kB) (
  .lam (.app (.bvar 1) (.const kMkA [.param 0])) (
  .lam (.app (.bvar 1) (.const kMkB [.param 0])) (.bvar 1) bm) bm) bm) bm

/-- **The theorem copy**, stated at the recursor's own parameters `[1, 0]`: the binder types are
over the advice models, the left side is headed by the recursor's alias `f A.rec` at
`[param 1, param 0]`, and its major premise is the constructor's alias `f A.mk` at `[param 0]`:

    ∀ m1 m2 hA hB, @Eq.{v} (m1 mk') (f A.rec).{v, u} m1 m2 hA hB (f A.mk).{u}) hA -/
def thmTyA : KExpr :=
  .forallE (motiveTy mA) (
  .forallE (motiveTy mB) (
  .forallE (.app (.bvar 1) (.const mMkA [.param 0])) (
  .forallE (.app (.bvar 1) (.const mMkB [.param 0])) (
    .app (.app (.app (.const eqName [.param 1])
      (.app (.bvar 3) (.const mMkA [.param 0])))
      (.app (.app (.app (.app (.app (.const (f kRecA) [.param 1, .param 0])
        (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.const (f kMkA) [.param 0])))
      (.bvar 1)) bm) bm) bm) bm

/-- The rule is canonical in the real frame: the major premise is at the constructor's own
level parameters. -/
theorem recA_plain : Expr.recRulePlain (tyRecA kA kB kMkA kMkB) 4 4 0 [0] = true := by
  rfl

/-- In the positional frame the rule is not canonical: the major premise is at `param 1`. -/
theorem recA_pos_not_plain :
    Expr.recRulePlain (posOf lpsR (tyRecA kA kB kMkA kMkB)) 4 4 0 [0] = false := by
  rfl

/-- **The canonical rule's theorem record of the large recursor, in the real frame.** The theorem
copy is stored at the `iota` key with the recursor's parameters `[1, 0]`; the record's literal
conjuncts (the level list, the head at `lps.map .param`, the major premise at the constructor's
parameters, the telescopes of the recursor's and the constructor's types renamed by `f`) hold by
computation. The package's judgements on the opened terms are `hJ`. -/
theorem iotaThm_recA {J : Judgements .anon} {env' envSelf : Env .anon} (r₀ : RecRule .anon)
    (hfind : env'.findCV? (auxKey (auxKey kRecA .model) (.iota 0)) =
      some ⟨auxKey (auxKey kRecA .model) (.iota 0), lpsR,
        thmTyA kMkA kRecA mA mB mMkA mMkB f⟩)
    (hJ : ∀ fvs tbody rdoms lrest fvsP crest2 ldomsL lrest2,
      openPisAtFvars 4 (thmTyA kMkA kRecA mA mB mMkA mMkB f) 0 = some (fvs, tbody) →
      Expr.instPisAt fvs ((tyRecA kA kB kMkA kMkB).renameConsts f) = some (rdoms, lrest) →
      openPisAtFvars 4 (tyRecA kA kB kMkA kMkB) 0 = some (fvsP, crest2) →
      Expr.instLamsAt fvsP (rhsA kA kB kMkA kMkB) = some (ldomsL, lrest2) →
      IotaRunsJ J envSelf 4 [] [] [] []
        (fvs.map Expr.fvarTypeD) rdoms (fvsP.map Expr.fvarTypeD) ldomsL
        (tbody.getAppArgs.getD 2 (.bvar 0))
        (Expr.mkAppN ((rhsA kA kB kMkA kMkB).renameConsts f) fvs)
        (tbody.getAppArgs.getD 0 (.bvar 0)) (tbody.getAppArgs.getD 1 (.bvar 0))) :
    IotaThmRunJ J env' envSelf f kRecA lpsR (tyRecA kA kB kMkA kMkB) 4 4 0
      { r₀ with ctor := kMkA } ⟨kMkA, [0], .const kA [.param 0]⟩ 0 0
      (rhsA kA kB kMkA kMkB) := by
  refine ⟨_, _, _, hfind, rfl, rfl, isEqHead_eq _, rfl, ?_⟩
  dsimp only
  refine ⟨beq_of_eq rfl, rfl, beq_of_eq rfl, beq_of_eq rfl, rfl,
    _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, _, _, rfl, trivial, ?_⟩
  exact hJ _ _ _ _ _ _ _ _ rfl rfl rfl rfl

end Family

end IxVM.Refinement.Decl.FamilyAlias.MutualPair
