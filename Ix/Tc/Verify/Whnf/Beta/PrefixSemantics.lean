import Ix.Tc.Verify.Whnf.Beta.LambdaInstantiation

/-!
# Theory semantics of a peeled beta prefix

This slice records the Theory expression obtained by instantiating a lambda
telescope in production order.  It proves the list algebra and the exact
typed `TrAppSuffix` unsnoc view needed to reduce a `BetaPeel.Tr` one argument
at a time.  The concrete simultaneous-substitution translation is kept as a
separate one-pass theorem so it need not pretend that sequential intermediate
terms satisfy production's size bound.
-/

namespace Ix.Tc

open Lean4Lean

end Ix.Tc

namespace Lean4Lean.VExpr

/-- Instantiate outer-to-inner beta arguments.  The first argument removes
the outermost remaining binder; the final argument removes the binder at
`depth`. -/
def instBetaArgs (e : VExpr) : List VExpr → (depth : Nat) → VExpr
  | [], _ => e
  | arg :: args, depth =>
      instBetaArgs (e.inst arg (depth + args.length)) args depth

@[simp] theorem instBetaArgs_nil (e : VExpr) (depth : Nat) :
    instBetaArgs e [] depth = e := rfl

@[simp] theorem instBetaArgs_sort (level : VLevel) (args : List VExpr)
    (depth : Nat) :
    instBetaArgs (.sort level) args depth = .sort level := by
  induction args generalizing depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, VExpr.inst, ih]

@[simp] theorem instBetaArgs_const (name : Lean.Name) (levels : List VLevel)
    (args : List VExpr) (depth : Nat) :
    instBetaArgs (.const name levels) args depth = .const name levels := by
  induction args generalizing depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, VExpr.inst, ih]

theorem instBetaArgs_app (fn arg : VExpr) (args : List VExpr)
    (depth : Nat) :
    instBetaArgs (.app fn arg) args depth =
      .app (instBetaArgs fn args depth) (instBetaArgs arg args depth) := by
  induction args generalizing fn arg depth with
  | nil => rfl
  | cons replacement args ih =>
      rw [instBetaArgs, VExpr.inst, ih]
      simp only [instBetaArgs]

/-- Beta-prefix instantiation distributes through a lambda, incrementing the
body cutoff exactly once. -/
theorem instBetaArgs_lam (A body : VExpr) (args : List VExpr)
    (depth : Nat) :
    instBetaArgs (.lam A body) args depth =
      .lam (instBetaArgs A args depth)
        (instBetaArgs body args (depth + 1)) := by
  induction args generalizing A body depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, VExpr.inst, ih]
      simp only [instBetaArgs]
      have hpos : depth + args.length + 1 = depth + 1 + args.length := by
        omega
      rw [hpos]

theorem instBetaArgs_forallE (A body : VExpr) (args : List VExpr)
    (depth : Nat) :
    instBetaArgs (.forallE A body) args depth =
      .forallE (instBetaArgs A args depth)
        (instBetaArgs body args (depth + 1)) := by
  induction args generalizing A body depth with
  | nil => rfl
  | cons arg args ih =>
      rw [instBetaArgs, VExpr.inst, ih]
      simp only [instBetaArgs]
      have hpos : depth + args.length + 1 = depth + 1 + args.length := by
        omega
      rw [hpos]

/-- Appending the innermost argument is one final instantiation after the
older prefix has been processed one binder deeper. -/
theorem instBetaArgs_append_singleton (e arg : VExpr)
    (args : List VExpr) (depth : Nat) :
    instBetaArgs e (args ++ [arg]) depth =
      (instBetaArgs e args (depth + 1)).inst arg depth := by
  induction args generalizing e depth with
  | nil => rfl
  | cons first rest ih =>
      rw [List.cons_append, instBetaArgs, List.length_append,
        List.length_singleton, instBetaArgs]
      have hpos : depth + (rest.length + 1) = depth + 1 + rest.length := by
        omega
      rw [hpos, ih]

private theorem inst_liftN_total (e replacement : VExpr) (amount : Nat) :
    (e.liftN (amount + 1)).inst replacement amount = e.liftN amount := by
  have hcompose :
      (e.liftN amount).liftN 1 amount = e.liftN (amount + 1) :=
    VExpr.liftN'_liftN' (e := e) (n1 := amount) (n2 := 1)
      (k1 := 0) (k2 := amount) (Nat.zero_le _) (Nat.le_refl _)
  rw [← hcompose]
  exact VExpr.inst_liftN _ _

/-- Removing every beta binder from an expression lifted across the whole
telescope leaves exactly the syntax-local lift below that telescope. -/
theorem instBetaArgs_liftN (e : VExpr) (args : List VExpr) (depth : Nat) :
    instBetaArgs (e.liftN (depth + args.length)) args depth =
      e.liftN depth := by
  induction args generalizing e depth with
  | nil => simp
  | cons arg args ih =>
      rw [instBetaArgs]
      simp only [List.length_cons]
      have hamount : depth + (args.length + 1) =
          (depth + args.length) + 1 := by omega
      rw [hamount, inst_liftN_total, ih]

end Lean4Lean.VExpr

namespace Ix.Tc

open Lean4Lean

namespace RecM.TrAppSuffix

/-- A typed suffix together with the exact Theory argument values in the same
production order as its concrete arguments. -/
inductive Values (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) (start : VExpr) :
    List (KExpr .anon) → List VExpr → VExpr → Prop
  | nil : Values env uvars nameOf trProj Delta start [] [] start
  | app {args : List (KExpr .anon)} {argValues : List VExpr}
      {current argV A B : VExpr} {arg : KExpr .anon} :
      Values env uvars nameOf trProj Delta start args argValues current →
      env.HasType uvars Delta.toCtx current (.forallE A B) →
      env.HasType uvars Delta.toCtx argV A →
      TrKExprS env uvars nameOf trProj Delta arg argV →
      Values env uvars nameOf trProj Delta start (args ++ [arg])
        (argValues ++ [argV]) (.app current argV)

namespace Values

/-- Every typed suffix exposes its exact Theory argument list. -/
theorem ofSuffix
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {resultV : VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV) :
    ∃ argValues,
      Values env uvars nameOf trProj Delta start args argValues resultV := by
  induction h with
  | nil => exact ⟨[], .nil⟩
  | app hprefix hfun harg hargTr ih =>
      obtain ⟨argValues, hvalues⟩ := ih
      exact ⟨argValues ++ [_], .app hvalues hfun harg hargTr⟩

/-- The empty concrete suffix has no Theory arguments and leaves its start
expression unchanged. -/
theorem nil_inv
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start resultV : VExpr} {argValues : List VExpr}
    (h : Values env uvars nameOf trProj Delta start [] argValues resultV) :
    argValues = [] ∧ resultV = start := by
  generalize heq : ([] : List (KExpr .anon)) = args at h
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | app => simp at heq

/-- Exact last-argument view, retaining the Theory-value list. -/
theorem unsnoc
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {arg : KExpr .anon}
    {argValues : List VExpr} {resultV : VExpr}
    (h : Values env uvars nameOf trProj Delta start (args ++ [arg])
      argValues resultV) :
    ∃ priorValues currentV argV A B,
      argValues = priorValues ++ [argV] ∧
        Values env uvars nameOf trProj Delta start args priorValues currentV ∧
        env.HasType uvars Delta.toCtx currentV (.forallE A B) ∧
        env.HasType uvars Delta.toCtx argV A ∧
        TrKExprS env uvars nameOf trProj Delta arg argV ∧
        resultV = .app currentV argV := by
  generalize heq : args ++ [arg] = allArgs at h
  induction h with
  | nil => simp at heq
  | @app priorArgs priorValues currentV argV A B concreteArg hprefix hfun
      harg hargTr ih =>
      obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp heq
      exact ⟨priorValues, currentV, argV, A, B, rfl, hprefix, hfun,
        harg, hargTr, rfl⟩

end Values

/-- Exact last-argument view of a typed suffix. -/
theorem unsnoc
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {arg : KExpr .anon} {resultV : VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start
      (args ++ [arg]) resultV) :
    ∃ currentV argV A B,
      TrAppSuffix env uvars nameOf trProj Delta start args currentV ∧
        env.HasType uvars Delta.toCtx currentV (.forallE A B) ∧
        env.HasType uvars Delta.toCtx argV A ∧
        TrKExprS env uvars nameOf trProj Delta arg argV ∧
        resultV = .app currentV argV := by
  generalize heq : args ++ [arg] = allArgs at h
  induction h with
  | nil => simp at heq
  | @app priorArgs current lastArg argV A B hprefix hfun hargTy hargTr ih =>
      obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp heq
      exact ⟨_, _, _, _, hprefix, hfun, hargTy, hargTr, rfl⟩

end RecM.TrAppSuffix

namespace RecM.BetaPeel.Tr

/-- The endpoint context of a translated lambda peel is well formed. -/
theorem endpointWF
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {start : KExpr .anon} {startV : VExpr}
    {consumed : List (KExpr .anon)} {body : KExpr .anon}
    {bodyDelta : KVLCtx} {bodyV : VExpr}
    (h : BetaPeel.Tr world.venv uvars world.nameOf trProj Delta start startV
      consumed body bodyDelta bodyV)
    (hDelta : KVLCtx.WF world.venv uvars Delta) :
    KVLCtx.WF world.venv uvars bodyDelta := by
  induction h with
  | nil => exact hDelta
  | snoc hprefix hA hty hbody ih => exact ⟨ih, nofun, hA⟩

/-- A typed application of every peeled lambda is definitionally equal to
the endpoint Theory body instantiated by the same argument values. -/
theorem theoryMeaning
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
    world.venv.IsDefEqU uvars Delta.toCtx appliedV
      (VExpr.instBetaArgs bodyV argValues 0) := by
  induction h generalizing argValues appliedV with
  | nil hstart =>
      obtain ⟨rfl, rfl⟩ := happs.nil_inv
      exact Lean4Lean.VEnv.IsDefEqU.refl
        (hstart.wf world.venvWF.ordered theory.literalWF
          theory.projections.wf hDelta)
  | @snoc consumed name bi ty body info arg currentDelta A bodyV hprefix
      hA hty hbody ih =>
      obtain ⟨priorValues, currentV, argV, domain, codomain, rfl,
        hpriorApps, hfun, harg, hargTr, rfl⟩ := happs.unsnoc
      have hprefixEq := ih hpriorApps
      rw [VExpr.instBetaArgs_lam] at hprefixEq
      let A' := VExpr.instBetaArgs A priorValues 0
      let bodyV' := VExpr.instBetaArgs bodyV priorValues 1
      have hfun' : world.venv.HasType uvars Delta.toCtx
          (.lam A' bodyV') (.forallE domain codomain) :=
        hfun.defeqU_l world.venvWF hDelta.toCtx hprefixEq
      obtain ⟨⟨u, hA'⟩, B', hbodyV'⟩ :=
        hfun'.lam_inv world.venvWF.ordered hDelta.toCtx
      have hlam' : world.venv.HasType uvars Delta.toCtx
          (.lam A' bodyV') (.forallE A' B') :=
        Lean4Lean.VEnv.HasType.lam hA' hbodyV'
      have hforallEq : world.venv.IsDefEqU uvars Delta.toCtx
          (.forallE domain codomain) (.forallE A' B') :=
        hfun'.uniqU world.venvWF hDelta.toCtx hlam'
      have hdomainEq : world.venv.IsDefEqU uvars Delta.toCtx domain A' :=
        let ⟨u, hdomain⟩ :=
          (hforallEq.forallE_inv world.venvWF hDelta.toCtx).1
        ⟨.sort u, hdomain⟩
      have harg' : world.venv.HasType uvars Delta.toCtx argV A' :=
        harg.defeqU_r world.venvWF hDelta.toCtx hdomainEq
      have happCong : world.venv.IsDefEqU uvars Delta.toCtx
          (.app currentV argV) (.app (.lam A' bodyV') argV) :=
        (Lean4Lean.VEnv.IsDefEq.appDF
          (hprefixEq.of_l world.venvWF hDelta.toCtx hfun) harg).toU
      have hbeta : world.venv.IsDefEqU uvars Delta.toCtx
          (.app (.lam A' bodyV') argV) (bodyV'.inst argV) :=
        ⟨_, .beta hbodyV' harg'⟩
      rw [VExpr.instBetaArgs_append_singleton]
      exact happCong.trans world.venvWF hDelta.toCtx hbeta

end RecM.BetaPeel.Tr

end Ix.Tc
