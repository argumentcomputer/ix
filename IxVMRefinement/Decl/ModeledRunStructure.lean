import IxVMRefinement.Decl.ModeledRunModel
import IxC.Kernel.Semantics.Bridge.DeclIndRun
import IxC.Kernel.Model.StoreCompanions

/-! # Structural extension through the complete modeled route

The actual projection-function tail adds recursors at derived function keys. It preserves
previous lookups and projection tables and introduces no theorem entries. Thus already
checked theorem rows remain typed throughout this route.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

private theorem projection_structure {md : Mode} {mode : CheckMode} {fuel : Nat}
    {T ctor : Key md} {lps : List LevelParam} {nP nF : Nat} :
    ∀ {env out : Env md} {fields : List Nat},
      ProjInstallRun mode fuel T ctor lps nP nF env fields out →
      EnvExt env out ∧ NewSat env out NotThm := by
  intro env out fields run
  induction fields generalizing env with
  | nil =>
    change out = env at run
    subst out
    exact ⟨EnvExt.refl env, NewSat.refl env NotThm⟩
  | cons i fields ih =>
    obtain ⟨next, step, tail⟩ := run
    rcases step with checked | ⟨_, rfl⟩
    · obtain ⟨cvj, mcv, mval, mhint, pty, rhs, _, _, _, fresh,
        _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := checked
      have extension : EnvExt env
          ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
            [projFnRule env.find? T ctor pty nP nF i rhs] :: env.consts⟩ :=
        EnvExt.cons (Option.isNone_iff_eq_none.mp fresh) (by
          intro T' _ _ _
          change projFnName T i ≠ projTableName T'
          simp [projFnName, projTableName, auxKey])
      obtain ⟨restExt, restNew⟩ := ih tail
      exact ⟨extension.trans restExt,
        (NewSat.cons (by intro cv value impossible; cases impossible)).trans restNew⟩
    · exact ih tail

private theorem phases_structure {md : Mode} {J : Judgements md}
    {env middle out : Env md} {names : List (Key md)} {caps : IndCaps md}
    {members recs : List (ConstantInfo md)}
    (memberRun : IndMembersRunJ J names caps env members middle)
    (recRun : IndRecsRunJ J names middle recs out) :
    EnvExt env out ∧ NewSat env out NotThm := by
  have memberExt := indMembersRunJ_envExt memberRun
  have memberNew := indMembersRunJ_newSat (Q := NotThm)
    (fun _ _ _ impossible => nomatch impossible)
    (fun _ _ _ _ _ impossible => nomatch impossible) memberRun
  rcases recRun with ⟨_, rfl⟩ | ⟨_, _, envSelf, checked, provisioned, folded⟩
  · exact ⟨memberExt, memberNew⟩
  · exact ⟨indRecsFoldRunJ_envExt provisioned folded (fun _ => rfl) memberExt,
      memberNew.trans (indRecsFoldRunJ_newSat (Q := NotThm)
        (fun _ _ _ _ _ _ impossible => nomatch impossible) folded)⟩

/-- Both modeled branches extend lookups and tables and store no new theorems. -/
theorem modeledRun_structure {md : Mode} {mode : CheckMode} {fuel : Nat}
    {env out : Env md} {block : List (ConstantInfo md)}
    (run : DeclIndRun mode fuel env block out) :
    EnvExt env out ∧ NewSat env out NotThm := by
  obtain ⟨_, branch⟩ := run
  rcases branch with ⟨cvT, capsT, cvC, cnP, cnF, _, _, middle, beforeProjections,
    members, recs, _, _, projections⟩ | ⟨_, middle, members, recs⟩
  · obtain ⟨phasesExt, phasesNew⟩ :=
      phases_structure (indMembersRun_runJ members) (indRecsRun_runJ recs)
    obtain ⟨projectionsExt, projectionsNew⟩ := projection_structure projections
    exact ⟨phasesExt.trans projectionsExt, phasesNew.trans projectionsNew⟩
  · exact phases_structure (indMembersRun_runJ members) (indRecsRun_runJ recs)

/-- The complete legacy modeled route preserves actual typed theorem rows. -/
theorem modeledRun_thmTyped {md : Mode} {mode : CheckMode} {fuel : Nat}
    {env out : Env md} {block : List (ConstantInfo md)}
    (run : DeclIndRun mode fuel env block out) (typed : ThmTyped env) :
    ThmTyped out :=
  thmTyped_step_noThm (modeledRun_structure run).1 typed (modeledRun_structure run).2

end IxVM.Refinement.Decl
