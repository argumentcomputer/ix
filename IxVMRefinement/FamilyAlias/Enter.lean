import IxVMRefinement.FamilyAlias.Package
import IxC.Kernel.Model.IndRenRecord

/-! # Entering the family package from positional derivations

What a producer of `DeclIndRenRunJ (famJ h)` supplies for each judgement of the record: a
derivation, at the record's environment, on the subject renamed by the block renaming `f` (block
names to aux keys) and then by `h` (aliases to their targets), with its level parameters at
positions. For a public term these two renamings compose to the advice renaming, so the subject is
the positional term the circuit checks. -/

namespace IxVM.Refinement.Decl.FamilyAlias

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

/-- A positional conversion of the renamed terms is a conversion of the record's package. -/
theorem famJ_defeq_of_pos {h f : KKey → KKey} {env : Env .anon} {d : Nat} {a b : KExpr}
    {ps : List LevelParam} (hA : AliasEnv env h) (hperm : ps.Perm (List.range ps.length))
    (hd : DefEq env d (posOf ps ((a.renameConsts f).renameConsts h))
      (posOf ps ((b.renameConsts f).renameConsts h))) :
    (renameJ f (famJ h)).defeq env d a b :=
  Or.inr ⟨hA, Or.inl ⟨ps, hperm, hd⟩⟩

/-- A positional conversion of terms that are already over the aux keys. -/
theorem famJ_defeq_of_pos' {h f : KKey → KKey} {env : Env .anon} {d : Nat} {a b : KExpr}
    {ps : List LevelParam} (hA : AliasEnv env h) (hperm : ps.Perm (List.range ps.length))
    (hd : DefEq env d (posOf ps (a.renameConsts h)) (posOf ps (b.renameConsts h))) :
    (renameJ f (famJ h)).defeq env d a b :=
  Or.inl ⟨hA, Or.inl ⟨ps, hperm, hd⟩⟩

/-- A positional typing of a closed renamed subject is a typing of the record's package, at the
inferred type with the positions renamed back. -/
theorem famJ_infer_closed_of_pos {h f : KKey → KKey} {env : Env .anon} {d : Nat}
    {e tpos : KExpr} {ps : List LevelParam} (hA : AliasEnv env h)
    (hperm : ps.Perm (List.range ps.length)) (hc : e.hasFvar = false)
    (hi : Infer env .full d (posOf ps ((e.renameConsts f).renameConsts h)) tpos) :
    (renameJ f (famJ h)).infer env d e (invPosOf ps tpos) :=
  Or.inr ⟨hc, hA, LeavesFixed.of_closed ((hasFvar_renameConsts f e).trans hc), ps, hperm,
    by rw [posOf_invPosOf hperm]; exact hi⟩

/-- A positional typing of an open subject whose leaf annotations the renaming fixes. -/
theorem famJ_infer_of_pos {h : KKey → KKey} {env : Env .anon} {d : Nat} {e tpos : KExpr}
    {ps : List LevelParam} (hA : AliasEnv env h) (hperm : ps.Perm (List.range ps.length))
    (hfix : LeavesFixed h e)
    (hi : Infer env .full d (posOf ps (e.renameConsts h)) tpos) :
    (famJ h).infer env d e (invPosOf ps tpos) :=
  ⟨hA, hfix, ps, hperm, by rw [posOf_invPosOf hperm]; exact hi⟩

/-- A positional sort reduction is a sort of the record's package. -/
theorem famJ_sort_of_pos {h f : KKey → KKey} {env : Env .anon} {d : Nat} {tpos : KExpr}
    {upos : KLevel} {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (hr : Red env d tpos (.sort upos)) :
    (renameJ f (famJ h)).sort env d (invPosOf ps tpos) (invPosLevel ps upos) :=
  posRulesJ_sort_of_pos hperm hr

end IxVM.Refinement.Decl.FamilyAlias
