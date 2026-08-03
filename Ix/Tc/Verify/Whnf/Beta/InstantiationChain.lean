import Ix.Tc.Verify.Whnf.Beta.DependentContexts

/-!
# The peeled telescope induces a dependent instantiation chain

The translated lambda peel and the typed suffix determine exactly how the
endpoint mixed context is reduced back to the caller context.  This theorem
is purely structural: typing is used later for beta equality, while the
context chain itself follows from the recovered lambda declarations and the
exact Theory argument values.
-/

namespace Ix.Tc

open Lean4Lean

namespace RecM.BetaPeel.Tr

/-- Every translated peel plus its exact Theory argument list induces the
dependent context-instantiation chain used by one-pass simultaneous
substitution. -/
theorem contextInsts
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} {start : KExpr .anon} {startV : VExpr}
    {consumed : List (KExpr .anon)} {body : KExpr .anon}
    {bodyDelta : KVLCtx} {bodyV : VExpr}
    {argValues : List VExpr} {appliedV : VExpr}
    (h : BetaPeel.Tr world.venv uvars world.nameOf trProj Delta start startV
      consumed body bodyDelta bodyV)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (happs : TrAppSuffix.Values world.venv uvars world.nameOf trProj Delta
      startV consumed argValues appliedV) :
    KVLCtx.KInsts world.venv uvars Delta argValues 0 0 bodyDelta Delta := by
  induction h generalizing argValues appliedV with
  | nil hstart =>
      obtain ⟨rfl, rfl⟩ := happs.nil_inv
      exact .nil Delta 0 0
  | @snoc consumed name bi ty body info arg currentDelta A bodyV hprefix
      hA hty hbody ih =>
      obtain ⟨priorValues, currentV, argV, domain, codomain, rfl,
        hpriorApps, hfun, harg, hargTr, rfl⟩ := happs.unsnoc
      have hprefixInsts := ih hpriorApps
      have hprefixEq := hprefix.theoryMeaning theory hDelta hpriorApps
      rw [VExpr.instBetaArgs_lam] at hprefixEq
      let A' := VExpr.instBetaArgs A priorValues 0
      let bodyV' := VExpr.instBetaArgs bodyV priorValues 1
      have hfun' : world.venv.HasType uvars Delta.toCtx
          (.lam A' bodyV') (.forallE domain codomain) :=
        hfun.defeqU_l world.venvWF hDelta.toCtx hprefixEq
      obtain ⟨⟨level, hA'⟩, B', hbodyV'⟩ :=
        hfun'.lam_inv world.venvWF.ordered hDelta.toCtx
      have hlam' : world.venv.HasType uvars Delta.toCtx
          (.lam A' bodyV') (.forallE A' B') :=
        Lean4Lean.VEnv.HasType.lam hA' hbodyV'
      have hforallEq : world.venv.IsDefEqU uvars Delta.toCtx
          (.forallE domain codomain) (.forallE A' B') :=
        hfun'.uniqU world.venvWF hDelta.toCtx hlam'
      have hdomainEq : world.venv.IsDefEqU uvars Delta.toCtx domain A' :=
        let ⟨uDomain, hdomain⟩ :=
          (hforallEq.forallE_inv world.venvWF hDelta.toCtx).1
        ⟨.sort uDomain, hdomain⟩
      have harg' : world.venv.HasType uvars Delta.toCtx argV A' :=
        harg.defeqU_r world.venvWF hDelta.toCtx hdomainEq
      have hlifted := hprefixInsts.succ (.vlam A)
      have hlifted' : KVLCtx.KInsts world.venv uvars Delta
          priorValues 1 1
          ((none, .vlam A) :: currentDelta)
          ((none, .vlam (VExpr.instBetaArgs A priorValues 0)) :: Delta) := by
        simpa [VLocalDecl.instBetaArgs, VLocalDecl.depth] using hlifted
      have hfinal : KVLCtx.KInsts world.venv uvars Delta [argV] 0 0
          ((none, .vlam (VExpr.instBetaArgs A priorValues 0)) :: Delta)
          Delta :=
        .cons (.zero) harg' (.nil Delta 0 0)
      exact hlifted'.append hfinal

end RecM.BetaPeel.Tr
end Ix.Tc
