/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.TypeChecker
import Ix.Theory.Named.Reference.Inductive.ValidationTrace

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

/-- Compatibility name for the consumer-neutral reflected-primitive list. -/
@[deprecated Ix.Theory.Named.VEnv.reflectedPrimitiveNames (since := "2026-08-11")]
abbrev reflectedPrimitiveNames : List Name :=
  Ix.Theory.Named.VEnv.reflectedPrimitiveNames

/-- Compatibility shim for the consumer-neutral Theory theorem. -/
@[deprecated Ix.Theory.Named.VEnv.HasPrimitives.of_avoids (since := "2026-08-11")]
theorem VEnv.HasPrimitives.of_avoids
    {env : VEnv}
    (h : ∀ n ∈ reflectedPrimitiveNames, env.constants n = none) :
    env.HasPrimitives :=
  Ix.Theory.Named.VEnv.HasPrimitives.of_avoids h

/-- Compatibility shim for the consumer-neutral Theory theorem. -/
@[deprecated Ix.Theory.Named.VEnv.addConst_other (since := "2026-08-11")]
theorem VEnv.addConst_other
    {env env' : VEnv} {name other : Name} {ci : VConstant}
    (hadd : env.addConst name ci = some env')
    (hne : name ≠ other) :
    env'.constants other = env.constants other :=
  Ix.Theory.Named.VEnv.addConst_other hadd hne

/-- Compatibility shim for the consumer-neutral Theory theorem. -/
@[deprecated Ix.Theory.Named.VEnv.HasPrimitives.addConst (since := "2026-08-11")]
theorem VEnv.HasPrimitives.addConst
    {env env' : VEnv} {name : Name} {ci : VConstant}
    (H : env.HasPrimitives)
    (hname : name ∉ reflectedPrimitiveNames)
    (hadd : env.addConst name ci = some env') :
    env'.HasPrimitives :=
  Ix.Theory.Named.VEnv.HasPrimitives.addConst H hname hadd

/-- A verified implementation local context remains verified when the Theory
environment grows.  Kernel local declarations and their free-variable names
are unchanged; only their translations and typing derivations are transported
monotonically. -/
theorem MLCtx.WF.mono
    {env env' : VEnv} (henv : env ≤ env') :
    ∀ {context : MLCtx} {Us : List Name},
      context.WF env Us → context.WF env' Us
  | .nil, _, _ => trivial
  | .vlam _ _ _ _ _ _, _,
      ⟨tailWF, fresh, type_tr, typeWF⟩ =>
    ⟨tailWF.mono henv, fresh, type_tr.mono henv, typeWF.mono henv⟩
  | .vlet _ _ _ _ _ _ _, _,
      ⟨tailWF, fresh, type_tr, value_tr, valueWF⟩ =>
    ⟨tailWF.mono henv, fresh, type_tr.mono henv,
      value_tr.mono henv, valueWF.mono henv⟩

/-- Kernel-side counterpart of `VEnv.HasPrimitives.of_avoids`: if an isolated
constant map contains no hard-coded primitive name, the safety premise needed
by `VContext` is vacuous. -/
theorem safePrimitives_of_avoids
    {env : Environment} {n : Name} {ci : ConstantInfo}
    (h : ∀ n, Environment.primitives.contains n → env.find? n = none) :
    env.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  rw [h n hprim] at hfind
  contradiction

/-- Staging one fresh non-primitive inductive family preserves the kernel-side
primitive safety contract. All old lookups are inherited from the input map;
the only new lookup cannot be primitive by hypothesis. -/
theorem AddInductConstant.safePrimitives
    {pre post : Environment} {env typeEnv : VEnv} {raw : VConstVal}
    (stage : AddInductConstant .induct pre.constants env raw
      post.constants typeEnv)
    (preMapWF : pre.constants.WF)
    (H : pre.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hname : Environment.primitives.contains raw.name = false) :
    post.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  have postMapWF := stage.map_wf preMapWF
  change post.constants.find?' n = some ci at hfind
  rw [postMapWF.find?'_eq_find?, stage.map_add,
    preMapWF.find?_insert] at hfind
  split at hfind
  · rename_i heq
    have : raw.name = n := by simpa using heq
    subst n
    rw [hname] at hprim
    contradiction
  · apply H
    change pre.constants.find?' n = some ci
    rw [preMapWF.find?'_eq_find?]
    exact hfind
    exact hprim

/-- Evidence that Verify's recursive WHNF procedure returned an exact kernel
expression, together with strict translations of the input and output into one
Theory context.

The result is not trusted merely because it is supplied by a caller:
`run_eq` records the concrete checker execution, while `rhs_tr` identifies its
Theory meaning. -/
structure WhnfRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (lhs rhs : Expr) (lhs' rhs' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  lhs_tr : TrExprS env Us Δ lhs lhs'
  rhs_tr : TrExprS env Us Δ rhs rhs'
  recursionFuel : Nat
  run_eq : ∃ state : State,
    Inner.whnf' lhs (Methods.withFuel recursionFuel)
      context.toContext ({} : State) = .ok (rhs, state)

/-- Turn one operationally certified candidate step into the existing
state-bearing Verify certificate once the caller supplies the strict
kernel/Theory translations and the corresponding verified context.

The adapter recovers the final checker state from the stored `M.run` equality;
it does not rerun normalization, choose a result, or assert a semantic
equality. -/
def WhnfRun.ofCandidateStep
    (step : AddInductive.CandidateWhnfStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq :
      context.toContext = step.context.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (lhs_tr : TrExprS env Us Δ step.source lhs')
    (rhs_tr : TrExprS env Us Δ step.result rhs')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1) :
    WhnfRun env Us Δ step.source step.result lhs' rhs' where
  context := context
  venv_eq := venv_eq
  lparams_eq := lparams_eq
  vlctx_eq := vlctx_eq
  state_wf := state_wf
  lhs_tr := lhs_tr
  rhs_tr := rhs_tr
  recursionFuel := recursionFuel
  run_eq := by
    rw [context_eq]
    exact step.innerRun recursionFuel hdepth hvalid

/-- The strict input translation already supplies the Theory well-formedness
needed to type an exact WHNF equality. In particular, a certificate producer
does not need to borrow a typing fact from the normalized declaration it is
trying to construct. -/
theorem WhnfRun.lhs_wf
    (run : WhnfRun env Us Δ lhs rhs lhs' rhs') :
    lhs'.WF env Us.length Δ.toCtx := by
  have hlhs : run.context.TrExprS lhs lhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.lhs_tr
  have hwf := hlhs.wf run.context.Ewf.ordered run.context.Δwf
  simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using hwf

/-- An exact successful verified WHNF execution is an ordinary Theory
definitional equality. The proof consumes the existing checker-refinement
contract and uses representation uniqueness to identify the translated
result. -/
theorem WhnfRun.isDefEqU
    (run : WhnfRun env Us Δ lhs rhs lhs' rhs') :
    env.IsDefEqU Us.length Δ.toCtx lhs' rhs' := by
  have hlhs : run.context.TrExprS lhs lhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.lhs_tr
  have hrhs : run.context.TrExpr rhs rhs' := by
    have strict : run.context.TrExprS rhs rhs' := by
      simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
        run.vlctx_eq] using run.rhs_tr
    exact strict.trExpr run.context.Ewf run.context.Δwf
  obtain ⟨state, hrun⟩ := run.run_eq
  obtain ⟨_, _, _, _, _, htr⟩ :=
    (TypeChecker.Inner.whnf'.WF hlhs
      (Methods.withFuel run.recursionFuel) Methods.withFuel.WF)
      run.state_wf rhs state hrun
  have hdefeq :=
    htr.uniq run.context.Ewf
      (.refl run.context.Ewf run.context.Δwf) hrhs
  simpa only [VContext.IsDefEqU, run.venv_eq, run.lparams_eq,
    run.vlctx_eq] using hdefeq

/-- Typed form of `WhnfRun.isDefEqU`. A known type for the input fixes the
otherwise existential type in the WHNF refinement result. -/
theorem WhnfRun.isDefEq
    (run : WhnfRun env Us Δ lhs rhs lhs' rhs')
    (hlhs : env.HasType Us.length Δ.toCtx lhs' A) :
    env.IsDefEq Us.length Δ.toCtx lhs' rhs' A := by
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.context.Ewf
  have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      run.context.Δwf.toCtx
  exact run.isDefEqU.of_l henv hΔ hlhs

/-- Evidence that Verify's full type-checking path inferred an exact kernel
type, with strict Theory translations of both the checked expression and the
returned type.

`inferOnly := false` is important here: the recorded run checks the expression
rather than trusting a caller-provided `TrExprS` derivation as an inference
cache hit. -/
structure CheckTypeRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (expr inferred : Expr) (expr' inferred' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  expr_tr : TrExprS env Us Δ expr expr'
  inferred_tr : TrExprS env Us Δ inferred inferred'
  recursionFuel : Nat
  run_eq : ∃ state : State,
    Inner.inferType expr false (Methods.withFuel recursionFuel)
      context.toContext ({} : State) = .ok (inferred, state)

/-- Candidate-step adapter for full checking. As with
`WhnfRun.ofCandidateStep`, the operational result and final state come from
the producer; this boundary only attaches an already verified context and
strict translations. -/
def CheckTypeRun.ofCandidateStep
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq :
      context.toContext = step.context.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (expr_tr : TrExprS env Us Δ step.source expr')
    (inferred_tr : TrExprS env Us Δ step.inferred inferred')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel) :
    CheckTypeRun env Us Δ step.source step.inferred expr' inferred' where
  context := context
  venv_eq := venv_eq
  lparams_eq := lparams_eq
  vlctx_eq := vlctx_eq
  state_wf := state_wf
  expr_tr := expr_tr
  inferred_tr := inferred_tr
  recursionFuel := recursionFuel
  run_eq := by
    rw [context_eq]
    exact step.innerRun recursionFuel hdepth hvalid

/-- Recover the strict Theory translations and typing judgment supplied by an
exact retained full-check observation.

This is the proof-producing counterpart of `CheckTypeRun.ofCandidateStep` for
callers that do not yet have named translations.  The only source-side premise
is the free-variable condition required by the verified checker refinement. -/
theorem candidateCheckTypeStep_exists_translation
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq : context.toContext = step.context.toTypeChecker)
    (state_wf : VState.WF context {})
    (source_fvars :
      step.source.FVarsIn (· ∈ context.vlctx.fvars))
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel) :
    ∃ source' inferred',
      context.TrExprS step.source source' ∧
      context.TrExprS step.inferred inferred' ∧
      context.HasType source' inferred' := by
  obtain ⟨state, run⟩ :=
    step.innerRun recursionFuel hdepth hvalid
  rw [← context_eq] at run
  obtain ⟨_, _, _, _, source', inferred', typing⟩ :=
    (Inner.checkType.WF source_fvars
      (Methods.withFuel recursionFuel) Methods.withFuel.WF)
      state_wf step.inferred state run
  exact ⟨source', inferred', typing.2.1, typing.2.2.1,
    typing.2.2.2⟩

/-- An exact successful `checkType` execution supplies the corresponding
Theory typing judgment. Translation uniqueness transports the verifier's
existential result to the precise translations named by the certificate. -/
theorem CheckTypeRun.hasType
    (run : CheckTypeRun env Us Δ expr inferred expr' inferred') :
    env.HasType Us.length Δ.toCtx expr' inferred' := by
  have hexpr : run.context.TrExprS expr expr' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.expr_tr
  have hinferred : run.context.TrExprS inferred inferred' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.inferred_tr
  obtain ⟨state, hrun⟩ := run.run_eq
  obtain ⟨_, _, _, _, e, ty, htyping⟩ :=
    (TypeChecker.Inner.checkType.WF hexpr.fvarsIn
      (Methods.withFuel run.recursionFuel) Methods.withFuel.WF)
      run.state_wf inferred state hrun
  rcases htyping with ⟨_, he, hty, hhasType⟩
  have heq :=
    he.uniq run.context.Ewf
      (.refl run.context.Ewf run.context.Δwf) hexpr
  have htyeq :=
    hty.uniq run.context.Ewf
      (.refl run.context.Ewf run.context.Δwf) hinferred
  have hout :=
    (hhasType.defeqU_l run.context.Ewf run.context.Δwf heq).defeqU_r
      run.context.Ewf run.context.Δwf htyeq
  simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using hout

/-- A checked expression whose inferred type translates to a sort is a Theory
type. This is the insertion premise needed for raw family and constructor
constants. -/
theorem CheckTypeRun.isType
    (run : CheckTypeRun env Us Δ expr inferred expr' (.sort u)) :
    env.IsType Us.length Δ.toCtx expr' :=
  ⟨u, run.hasType⟩

/-- If `checkType` returns a type expression whose own verified WHNF is a
sort, the checked expression is a Theory type. This is the common alias case:
the checker may infer a reducible type constant before `ensureSort` exposes its
sort WHNF. -/
theorem CheckTypeRun.isType_of_whnf
    (run : CheckTypeRun env Us Δ expr inferred expr' inferred')
    (typeRun : WhnfRun env Us Δ inferred reduced inferred' (.sort u)) :
    env.IsType Us.length Δ.toCtx expr' := by
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.context.Ewf
  have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      run.context.Δwf.toCtx
  exact ⟨u, run.hasType.defeqU_r henv hΔ typeRun.isDefEqU⟩

/-- Evidence for one exact successful checker definitional-equality run, with
strict translations of both kernel endpoints in the same Theory context. -/
structure IsDefEqRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (lhs rhs : Expr) (lhs' rhs' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  lhs_tr : TrExprS env Us Δ lhs lhs'
  rhs_tr : TrExprS env Us Δ rhs rhs'
  recursionFuel : Nat
  run_eq : ∃ state : State,
    Inner.isDefEq lhs rhs (Methods.withFuel recursionFuel)
      context.toContext ({} : State) = .ok (true, state)

/-- Convert the retained candidate equality observation to a state-bearing
Verify certificate. -/
def IsDefEqRun.ofCandidateStep
    (step : AddInductive.CandidateIsDefEqStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq : context.toContext = step.context.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (lhs_tr : TrExprS env Us Δ step.lhs lhs')
    (rhs_tr : TrExprS env Us Δ step.rhs rhs')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel) :
    IsDefEqRun env Us Δ step.lhs step.rhs lhs' rhs' where
  context := context
  venv_eq := venv_eq
  lparams_eq := lparams_eq
  vlctx_eq := vlctx_eq
  state_wf := state_wf
  lhs_tr := lhs_tr
  rhs_tr := rhs_tr
  recursionFuel := recursionFuel
  run_eq := by
    rw [context_eq]
    exact step.innerRun recursionFuel hdepth hvalid

/-- A successful verified equality run supplies ordinary Theory
definitional equality. -/
theorem IsDefEqRun.isDefEqU
    (run : IsDefEqRun env Us Δ lhs rhs lhs' rhs') :
    env.IsDefEqU Us.length Δ.toCtx lhs' rhs' := by
  have hlhs : run.context.TrExprS lhs lhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.lhs_tr
  have hrhs : run.context.TrExprS rhs rhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.rhs_tr
  obtain ⟨state, hrun⟩ := run.run_eq
  obtain ⟨_, _, _, _, hdefeq⟩ :=
    (TypeChecker.Inner.isDefEq.WF hlhs hrhs
      (Methods.withFuel run.recursionFuel) Methods.withFuel.WF)
      run.state_wf true state hrun
  simpa only [VContext.IsDefEqU, run.venv_eq, run.lparams_eq,
    run.vlctx_eq] using hdefeq (by simp)

/-- Consuming a certified annotation path cannot introduce a free variable or
level metavariable. -/
theorem candidateTypeAnnotation_fvarsIn
    (trace : AddInductive.CandidateTypeAnnotationTrace source consumed)
    (h : source.FVarsIn fvars) : consumed.FVarsIn fvars := by
  induction trace with
  | identity => exact h
  | outParam _ _ _ ih => exact ih h.2
  | semiOutParam _ _ _ ih => exact ih h.2
  | optParam _ _ _ _ ih => exact ih h.1.2
  | autoParam _ _ _ _ ih => exact ih h.1.2

/-- Extract a strict translation of the consumed annotation argument from the
strict translation of the raw wrapper application. -/
theorem candidateTypeAnnotation_exists_translation
    (trace : AddInductive.CandidateTypeAnnotationTrace source consumed)
    (source_tr : TrExprS env Us Δ source source') :
    ∃ consumed', TrExprS env Us Δ consumed consumed' := by
  induction trace generalizing source' with
  | identity => exact ⟨source', source_tr⟩
  | outParam _ _ _ ih =>
    let .app _ _ _ type_tr := source_tr
    exact ih type_tr
  | semiOutParam _ _ _ ih =>
    let .app _ _ _ type_tr := source_tr
    exact ih type_tr
  | optParam _ _ _ _ ih =>
    let .app _ _ fn_tr _ := source_tr
    let .app _ _ _ type_tr := fn_tr
    exact ih type_tr
  | autoParam _ _ _ _ ih =>
    let .app _ _ fn_tr _ := source_tr
    let .app _ _ _ type_tr := fn_tr
    exact ih type_tr

/-- The empty executable checker state is well formed for any verified
context whose free-variable names are already reserved by the kernel name
generator.  `VState.WF.empty` is the empty-local-context specialization;
candidate normalization needs this slightly more general form after entering
raw Pi binders. -/
theorem VState.WF.empty_of_reserves
    (context : VContext)
    (reserved : ∀ fv ∈ context.vlctx.fvars,
      (({} : VState).ngen).Reserves fv) :
    VState.WF context {} where
  trctx := context.trlctx
  ngen_wf := reserved
  ectx := ⟨context.vlctx, .refl, context.Δwf, .refl, .empty, reserved⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

/-- Positional verified context for an executable normalization candidate.

The equality pins every checker-visible field (environment, local context,
safety, level parameters, and fuel) to the `AddInductive.Context` retained by
the candidate trace.  The state certificate is kept with it because every
retained full-check and WHNF observation starts from the empty checker state. -/
structure CandidateContextRun
    (candidateContext : AddInductive.Context) where
  context : VContext
  context_eq : context.toContext = candidateContext.toTypeChecker
  state_wf : VState.WF context {}
  namePrefix_ne : candidateContext.ngen.namePrefix ≠
    (({} : VState).ngen).namePrefix

/-- Candidate binders and the kernel checker's own temporary names use
different prefixes, so every candidate binder is reserved by a freshly
initialized kernel checker state. -/
theorem candidateFreshFVarId_reserved
    (candidateContext : AddInductive.Context)
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    (({} : VState).ngen).Reserves candidateContext.freshFVarId := by
  simp [NameGenerator.Reserves, AddInductive.Context.freshFVarId]
  intro i h
  apply namePrefix_ne
  simpa only [NameGenerator.curr, Name.getPrefix] using
    congrArg Name.getPrefix h

/-- Package an already verified checker context at a candidate position. -/
def CandidateContextRun.ofVContext
    (candidateContext : AddInductive.Context)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (state_wf : VState.WF context {})
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    CandidateContextRun candidateContext :=
  ⟨context, context_eq, state_wf, namePrefix_ne⟩

/-- Construct the root certificate used by family and constructor candidates.
Their candidate traversal deliberately resets the local context to empty. -/
def CandidateContextRun.root
    {ves : VEnvs} (wf : ves.WF candidateContext.env)
    (lctx_eq : candidateContext.lctx = {})
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    CandidateContextRun candidateContext := by
  let context := VContext.mk' wf candidateContext.safety
    candidateContext.lparams candidateContext.fuel
  refine ⟨context, ?_, ?_, namePrefix_ne⟩
  · simp [context, VContext.mk', VContext.mk1, MLCtx.lctx,
      AddInductive.Context.toTypeChecker, lctx_eq]
  · exact VState.WF.empty

@[simp] theorem CandidateContextRun.context_env
    (run : CandidateContextRun candidateContext) :
    run.context.env = candidateContext.env := by
  have h := congrArg (fun c : TypeChecker.Context => c.env) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_lctx
    (run : CandidateContextRun candidateContext) :
    run.context.lctx = candidateContext.lctx := by
  have h := congrArg (fun c : TypeChecker.Context => c.lctx) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_safety
    (run : CandidateContextRun candidateContext) :
    run.context.safety = candidateContext.safety := by
  have h := congrArg (fun c : TypeChecker.Context => c.safety) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_lparams
    (run : CandidateContextRun candidateContext) :
    run.context.lparams = candidateContext.lparams := by
  have h := congrArg (fun c : TypeChecker.Context => c.lparams) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_fuel
    (run : CandidateContextRun candidateContext) :
    run.context.fuel = candidateContext.fuel := by
  have h := congrArg (fun c : TypeChecker.Context => c.fuel) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

/-- Reset only the implementation and Theory local contexts while retaining
the exact environment, safety mode, level parameters, fuel, and name
generator owned by a candidate context.  Constructor root `checkType` uses
precisely this context before the validation telescope re-enters the retained
family locals. -/
def CandidateContextRun.withEmptyLocalContext
    (run : CandidateContextRun candidateContext) :
    CandidateContextRun candidateContext.withEmptyLocalContext := by
  let context : VContext :=
    { run.context with
      lctx := {}
      mlctx := .nil
      mlctx_wf := trivial
      lctx_eq := rfl }
  have context_eq : context.toContext =
      candidateContext.withEmptyLocalContext.toTypeChecker := by
    change { run.context.toContext with lctx := {} } =
      candidateContext.withEmptyLocalContext.toTypeChecker
    rw [run.context_eq]
    rfl
  refine ⟨context, context_eq, ?_, run.namePrefix_ne⟩
  exact VState.WF.empty_of_reserves context (by
    intro fv hfv
    change fv ∈ VLCtx.fvars ([] : VLCtx) at hfv
    simp at hfv)

/-- Package a retained full-check observation at an already named strict
Theory source.  The verified execution still chooses the inferred Theory
type; the duplicate source translation returned by refinement is discarded,
not identified by syntactic equality. -/
theorem CheckTypeRun.exists_ofCandidateStep
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS step.source source') :
    ∃ inferred', Nonempty
      (CheckTypeRun contextRun.context.venv contextRun.context.lparams
        contextRun.context.vlctx step.source step.inferred source' inferred') := by
  obtain ⟨_, inferred', _, inferred_tr, _⟩ :=
    candidateCheckTypeStep_exists_translation step hvalid
      contextRun.context contextRun.context_eq contextRun.state_wf
      source_tr.fvarsIn step.context.fuel.recDepth rfl
  exact ⟨inferred', ⟨CheckTypeRun.ofCandidateStep step hvalid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf source_tr inferred_tr
    step.context.fuel.recDepth rfl⟩⟩

/-- Full-check packaging when only the checker's syntactic free-variable
premise is known.  Both strict Theory endpoints are then selected by the
verified refinement of the retained execution. -/
theorem CheckTypeRun.exists_ofCandidateStepFVars
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source_fvars :
      step.source.FVarsIn (· ∈ contextRun.context.vlctx.fvars)) :
    ∃ source' inferred', Nonempty
      (CheckTypeRun contextRun.context.venv contextRun.context.lparams
        contextRun.context.vlctx step.source step.inferred source' inferred') := by
  obtain ⟨source', inferred', source_tr, inferred_tr, _⟩ :=
    candidateCheckTypeStep_exists_translation step hvalid
      contextRun.context contextRun.context_eq contextRun.state_wf
      source_fvars step.context.fuel.recDepth rfl
  exact ⟨source', inferred', ⟨CheckTypeRun.ofCandidateStep step hvalid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf source_tr inferred_tr
    step.context.fuel.recDepth rfl⟩⟩

/-- Package one retained WHNF observation and keep the strict Theory
translation selected for its exact kernel result. -/
theorem WhnfRun.exists_ofCandidateStep
    (step : AddInductive.CandidateWhnfStep)
    (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS step.source source')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1) :
    ∃ result', contextRun.context.TrExprS step.result result' ∧
      Nonempty (WhnfRun contextRun.context.venv
        contextRun.context.lparams contextRun.context.vlctx
        step.source step.result source' result') := by
  obtain ⟨state, run⟩ := step.innerRun recursionFuel hdepth hvalid
  rw [← contextRun.context_eq] at run
  obtain ⟨_, _, _, _, _, resultTranslation⟩ :=
    (Inner.whnf'.WF source_tr
      (Methods.withFuel recursionFuel) Methods.withFuel.WF)
      contextRun.state_wf step.result state run
  obtain ⟨result', result_tr, _⟩ := resultTranslation
  exact ⟨result', result_tr, ⟨WhnfRun.ofCandidateStep step hvalid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf source_tr result_tr
    recursionFuel hdepth⟩⟩

/-- Extend a verified candidate context by precisely the raw local declaration
used by `AddInductive.Context.pushLocalDecl`.

The caller supplies the strict Theory translation and typing of the *stored*
local-domain expression.  Freshness comes from the trace index; reservation is
the independent fact needed to restart each retained checker observation from
the empty kernel checker state. -/
def CandidateContextRun.pushLocalDecl
    (run : CandidateContextRun candidateContext)
    (name : Name) (binderInfo : BinderInfo) (domain : Expr)
    (fresh : candidateContext.lctx.find?
      candidateContext.freshFVarId = none)
    (domain' : VExpr)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    CandidateContextRun
      (candidateContext.pushLocalDecl name binderInfo domain) := by
  let mlctx := run.context.mlctx.vlam candidateContext.freshFVarId
    name domain domain' binderInfo
  have lctx_eq : run.context.mlctx.lctx = candidateContext.lctx := by
    calc
      run.context.mlctx.lctx = run.context.lctx := run.context.lctx_eq
      _ = candidateContext.lctx := by
        simp
  have fresh' : run.context.mlctx.lctx.find?
      candidateContext.freshFVarId = none := by
    rw [lctx_eq]
    exact fresh
  have mlctx_wf : mlctx.WF run.context.venv run.context.lparams :=
    ⟨run.context.mlctx_wf, fresh', domain_tr, domain_type⟩
  let context := run.context.withMLC mlctx (wf := ⟨mlctx_wf⟩)
  have context_eq : context.toContext =
      (candidateContext.pushLocalDecl name binderInfo domain).toTypeChecker := by
    change { run.context.toContext with
        lctx := run.context.mlctx.lctx.mkLocalDecl
          candidateContext.freshFVarId name domain binderInfo } = _
    rw [run.context_eq, lctx_eq]
    rfl
  refine ⟨context, context_eq, VState.WF.empty_of_reserves context ?_, ?_⟩
  intro fv hfv
  change fv ∈ candidateContext.freshFVarId ::
    run.context.vlctx.fvars at hfv
  simp only [List.mem_cons] at hfv
  rcases hfv with rfl | hfv
  · exact candidateFreshFVarId_reserved candidateContext run.namePrefix_ne
  · exact run.state_wf.ngen_wf fv hfv
  simpa [AddInductive.Context.pushLocalDecl, NameGenerator.next] using
    run.namePrefix_ne

@[simp] theorem CandidateContextRun.pushLocalDecl_venv
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.venv = run.context.venv := by
  simp [CandidateContextRun.pushLocalDecl, VContext.withMLC]

@[simp] theorem CandidateContextRun.pushLocalDecl_lparams
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.lparams = run.context.lparams := by
  simp [CandidateContextRun.pushLocalDecl, VContext.withMLC]

@[simp] theorem CandidateContextRun.pushLocalDecl_vlctx
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.vlctx =
      (some (candidateContext.freshFVarId, domain.fvarsList),
        .vlam domain') :: run.context.vlctx := by
  simp [CandidateContextRun.pushLocalDecl, VContext.withMLC]

/-- The two exact verifier runs attached to one retained candidate node.

The indices force both runs to use the node's kernel source and observed
results and to agree on its Theory source.  This is the atomic input to the
recursive candidate interpreter below: a successful full check supplies the
type at which the successful WHNF execution is interpreted. -/
structure CandidateNodeRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (context : AddInductive.Context)
    (source inferred result : Expr)
    (source' result' inferred' : VExpr) where
  check : CheckTypeRun env Us Δ source inferred source' inferred'
  whnf : WhnfRun env Us Δ source result source' result'

/-- Construct an atomic semantic node directly from the two proof-carrying
observations retained by `CandidateExprTrace`.  The caller supplies only the
verified context and translations; the operational equalities and erased
checker states come from the candidate observations themselves. -/
def CandidateNodeRun.ofCandidate
    (candidateContext : AddInductive.Context)
    (source inferred result : Expr)
    (checked : AddInductive.CandidateCheckTypeStep.Valid
      ⟨candidateContext, source, inferred⟩)
    (normalized : AddInductive.CandidateWhnfStep.Valid
      ⟨candidateContext, source, result⟩)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (source_tr : TrExprS env Us Δ source source')
    (inferred_tr : TrExprS env Us Δ inferred inferred')
    (result_tr : TrExprS env Us Δ result result')
    (checkFuel whnfFuel : Nat)
    (checkDepth : candidateContext.fuel.recDepth = checkFuel)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    CandidateNodeRun env Us Δ candidateContext source inferred result
      source' result' inferred' where
  check := CheckTypeRun.ofCandidateStep
    ⟨candidateContext, source, inferred⟩ checked context context_eq
    venv_eq lparams_eq vlctx_eq state_wf source_tr inferred_tr
    checkFuel checkDepth
  whnf := WhnfRun.ofCandidateStep
    ⟨candidateContext, source, result⟩ normalized context context_eq
    venv_eq lparams_eq vlctx_eq state_wf source_tr result_tr
    whnfFuel whnfDepth

/-- Recover all output translations for one retained candidate node from the
verified checker refinements themselves.

Unlike `ofCandidate`, this theorem does not ask the caller to identify the
kernel expressions returned by `checkType` and `whnf` with preselected Theory
terms.  It extracts strict translations of both results from the two exact
executions, then packages those witnesses in the ordinary paired-node API.
Only the root source translation and matching verified context remain input. -/
theorem CandidateNodeRun.exists_ofCandidate
    (candidateContext : AddInductive.Context)
    (source inferred result : Expr)
    (checked : AddInductive.CandidateCheckTypeStep.Valid
      ⟨candidateContext, source, inferred⟩)
    (normalized : AddInductive.CandidateWhnfStep.Valid
      ⟨candidateContext, source, result⟩)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (state_wf : VState.WF context {})
    (source' : VExpr) (source_tr : context.TrExprS source source')
    (checkFuel whnfFuel : Nat)
    (checkDepth : candidateContext.fuel.recDepth = checkFuel)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ inferred' result',
      context.TrExprS inferred inferred' ∧
      context.TrExprS result result' ∧
      Nonempty (CandidateNodeRun context.venv context.lparams context.vlctx
        candidateContext source inferred result source' result' inferred') := by
  obtain ⟨checkState, checkRun⟩ :=
    AddInductive.CandidateCheckTypeStep.innerRun
      ⟨candidateContext, source, inferred⟩ checkFuel checkDepth checked
  rw [← context_eq] at checkRun
  obtain ⟨_, _, _, _, checkedSource', inferred', checkedTyping⟩ :=
    (Inner.checkType.WF source_tr.fvarsIn
      (Methods.withFuel checkFuel) Methods.withFuel.WF)
      state_wf inferred checkState checkRun
  obtain ⟨whnfState, whnfRun⟩ :=
    AddInductive.CandidateWhnfStep.innerRun
      ⟨candidateContext, source, result⟩ whnfFuel whnfDepth normalized
  rw [← context_eq] at whnfRun
  obtain ⟨_, _, _, _, _, resultTranslation⟩ :=
    (Inner.whnf'.WF source_tr
      (Methods.withFuel whnfFuel) Methods.withFuel.WF)
      state_wf result whnfState whnfRun
  obtain ⟨result', result_tr, _⟩ := resultTranslation
  refine ⟨inferred', result', checkedTyping.2.2.1, result_tr, ⟨?_⟩⟩
  exact CandidateNodeRun.ofCandidate
    candidateContext source inferred result checked normalized
    context context_eq rfl rfl rfl state_wf source_tr
    checkedTyping.2.2.1
    result_tr
    checkFuel whnfFuel checkDepth whnfDepth

/-- Construct a paired candidate node with a caller-selected Theory endpoint
for the retained WHNF result. The exact full-check execution still selects
and strictly translates its inferred type; only the already translated WHNF
endpoint is fixed by the caller. -/
theorem CandidateNodeRun.exists_ofCandidateAtResult
    (candidateContext : AddInductive.Context)
    (source inferred result : Expr)
    (checked : AddInductive.CandidateCheckTypeStep.Valid
      ⟨candidateContext, source, inferred⟩)
    (normalized : AddInductive.CandidateWhnfStep.Valid
      ⟨candidateContext, source, result⟩)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (state_wf : VState.WF context {})
    (source' result' : VExpr)
    (source_tr : context.TrExprS source source')
    (result_tr : context.TrExprS result result')
    (checkFuel whnfFuel : Nat)
    (checkDepth : candidateContext.fuel.recDepth = checkFuel)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ inferred', Nonempty
      (CandidateNodeRun context.venv context.lparams context.vlctx
        candidateContext source inferred result source' result' inferred') := by
  obtain ⟨_, inferred', _, inferred_tr, _⟩ :=
    candidateCheckTypeStep_exists_translation
      ⟨candidateContext, source, inferred⟩ checked
      context context_eq state_wf source_tr.fvarsIn checkFuel checkDepth
  exact ⟨inferred', ⟨CandidateNodeRun.ofCandidate
    candidateContext source inferred result checked normalized
    context context_eq rfl rfl rfl state_wf source_tr inferred_tr
    result_tr checkFuel whnfFuel checkDepth whnfDepth⟩⟩

/-- Compositional evidence for a normalization comparison.

Leaves are either reflexive, already typed syntax or exact verified WHNF
executions. `forallE` lifts such evidence through the raw binder context,
which is the constructor-type case needed by the first non-identity replay. -/
inductive DefEqEvidence (env : VEnv) :
    Nat → List VExpr → VExpr → VExpr → VExpr → Prop where
  | refl (h : env.HasType U Γ e A) :
      DefEqEvidence env U Γ e e A
  | whnf (run : WhnfRun env Us Δ lhs rhs lhs' rhs')
      (h : env.HasType Us.length Δ.toCtx lhs' A) :
      DefEqEvidence env Us.length Δ.toCtx lhs' rhs' A
  | app
      (fn : DefEqEvidence env U Γ f f' (.forallE A B))
      (arg : DefEqEvidence env U Γ a a' A) :
      DefEqEvidence env U Γ (.app f a) (.app f' a') (B.inst a)
  | beta
      (body : env.HasType U (A :: Γ) e B)
      (arg : env.HasType U Γ e' A) :
      DefEqEvidence env U Γ
        (.app (.lam A e) e') (e.inst e') (B.inst e')
  | trans
      (left : DefEqEvidence env U Γ lhs mid A)
      (right : DefEqEvidence env U Γ mid rhs A) :
      DefEqEvidence env U Γ lhs rhs A
  | change
      (type : env.IsDefEq U Γ A B (.sort u))
      (term : DefEqEvidence env U Γ lhs rhs A) :
      DefEqEvidence env U Γ lhs rhs B
  | ofDefEq (proof : env.IsDefEq U Γ lhs rhs A) :
      DefEqEvidence env U Γ lhs rhs A
  | forallE
      (domain : DefEqEvidence env U Γ A A' (.sort u))
      (body : DefEqEvidence env U (A :: Γ) B B' (.sort v)) :
      DefEqEvidence env U Γ
        (.forallE A B) (.forallE A' B') (.sort (.imax u v))

/-- Interpret compositional normalization evidence as Theory definitional
equality at its recorded type. -/
theorem DefEqEvidence.isDefEq :
    DefEqEvidence env U Γ lhs rhs A →
      env.IsDefEq U Γ lhs rhs A
  | .refl h => h
  | .whnf run h => run.isDefEq h
  | .app fn arg => .appDF fn.isDefEq arg.isDefEq
  | .beta body arg => .beta body arg
  | .trans left right => .trans left.isDefEq right.isDefEq
  | .change type term => .defeqDF type term.isDefEq
  | .ofDefEq proof => proof
  | .forallE domain body =>
      .forallEDF domain.isDefEq body.isDefEq

/-- Interpret one paired candidate node as typed definitional equality. -/
theorem CandidateNodeRun.evidence
    (run : CandidateNodeRun env Us Δ context source inferred result
      source' result' inferred') :
    DefEqEvidence env Us.length Δ.toCtx source' result' inferred' :=
  .whnf run.whnf run.check.hasType

/-- Recursive semantic interpretation of a source-indexed candidate trace.

At a Pi node the raw domain and the annotation-consumed local domain may have
different strict Theory translations. The retained equality run relates them;
the body is checked in the consumed-domain context and transported back to the
raw Pi context only when forming congruence evidence. -/
inductive CandidateExprRun (env : VEnv) (Us : List Name) :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace candidateContext source →
      (Δ : VLCtx) → VExpr → VExpr → VExpr → Prop where
  | terminal
      (node : CandidateNodeRun env Us Δ context source inferred result
        source' result' inferred') :
      CandidateExprRun env Us
        (.terminal context source inferred result checked normalized)
        Δ source' result' inferred'
  | forallE
      (annotations : AddInductive.CandidateTypeAnnotations domain)
      (annotationsEq : AddInductive.CandidateIsDefEqStep.Valid
        ⟨context, domain, annotations.consumed⟩)
      (domainCandidate : AddInductive.CandidateExprTrace context domain)
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (node : CandidateNodeRun env Us Δ context source inferred
        (.forallE name domain body binderInfo)
        source' (.forallE domain' body') inferred')
      (domainRun : CandidateExprRun env Us domainCandidate Δ
        domain' domainView' domainInferred')
      (annotationsRun : IsDefEqRun env Us Δ
        domain annotations.consumed domain' storedDomain')
      (bodyRun : CandidateExprRun env Us bodyCandidate bodyΔ
        storedBody' bodyView' bodyInferred')
      (domainType : env.HasType Us.length Δ.toCtx domain' (.sort u))
      (bodyType : env.HasType Us.length
        (domain' :: Δ.toCtx) body' (.sort v))
      (bodySource : env.IsDefEq Us.length (domain' :: Δ.toCtx)
        body' storedBody' (.sort v))
      (bodyContext :
        bodyΔ =
          (some (context.freshFVarId, annotations.consumed.fvarsList),
            .vlam storedDomain') :: Δ) :
      CandidateExprRun env Us
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized
          domainCandidate bodyCandidate)
        Δ source' (.forallE domainView' bodyView') inferred'

/-- Structural witness that a retained candidate trace is syntactically
identity-normalizing at every inspected node.

The witness is deliberately recursive rather than a single root equality:
generation consumes the exposed Pi spine positionally. At Pi nodes it also
records that annotation processing kept the binder domain unchanged. -/
inductive CandidateExprIdentity :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace candidateContext source → Prop where
  | terminal
      (result_eq : result = source) :
      CandidateExprIdentity
        (.terminal context source inferred result checked normalized)
  | forallE
      (domainCandidate : AddInductive.CandidateExprTrace context domain)
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (source_eq : source = .forallE name domain body binderInfo)
      (consumed_eq : annotations.consumed = domain)
      (domainIdentity : CandidateExprIdentity domainCandidate)
      (bodyIdentity : CandidateExprIdentity bodyCandidate) :
      CandidateExprIdentity
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized
          domainCandidate bodyCandidate)

private def candidateExprIdentityBinderInfoEq :
    Lean.BinderInfo → Lean.BinderInfo → Bool
  | .default, .default
  | .implicit, .implicit
  | .strictImplicit, .strictImplicit
  | .instImplicit, .instImplicit => true
  | _, _ => false

private theorem candidateExprIdentityBinderInfoEq_sound
    (left right : Lean.BinderInfo)
    (h : candidateExprIdentityBinderInfoEq left right = true) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [candidateExprIdentityBinderInfoEq]

/-- Transparent structural equality sufficient for identity-normalizing
candidate traces.  Metadata nodes are conservatively rejected: the retained
generation spine never needs an opaque metadata equality to justify source
identity. -/
private def candidateExprIdentityExprEq : Lean.Expr → Lean.Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' =>
      candidateExprIdentityExprEq f f' &&
        candidateExprIdentityExprEq a a'
  | .lam n t b bi, .lam n' t' b' bi' =>
      n == n' && candidateExprIdentityExprEq t t' &&
        candidateExprIdentityExprEq b b' &&
          candidateExprIdentityBinderInfoEq bi bi'
  | .forallE n t b bi, .forallE n' t' b' bi' =>
      n == n' && candidateExprIdentityExprEq t t' &&
        candidateExprIdentityExprEq b b' &&
          candidateExprIdentityBinderInfoEq bi bi'
  | .letE n t v b nd, .letE n' t' v' b' nd' =>
      n == n' && candidateExprIdentityExprEq t t' &&
        candidateExprIdentityExprEq v v' &&
          candidateExprIdentityExprEq b b' && nd == nd'
  | .lit a, .lit b => a == b
  | .proj n i s, .proj n' i' s' =>
      n == n' && i == i' && candidateExprIdentityExprEq s s'
  | _, _ => false

private theorem candidateExprIdentityExprEq_sound :
    ∀ (left right : Lean.Expr),
      candidateExprIdentityExprEq left right = true → left = right := by
  intro left right h
  induction left generalizing right with
  | bvar i =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | fvar i =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | mvar i =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | sort u =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | const n us =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | app fn arg fnIH argIH =>
      cases right with
      | app fn' arg' =>
          simp only [candidateExprIdentityExprEq,
            Bool.and_eq_true] at h
          rw [fnIH fn' h.1, argIH arg' h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | lam name type body binderInfo typeIH bodyIH =>
      cases right with
      | lam name' type' body' binderInfo' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1.1, typeIH type' h.1.1.2,
            bodyIH body' h.1.2,
            candidateExprIdentityBinderInfoEq_sound _ _ h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | forallE name type body binderInfo typeIH bodyIH =>
      cases right with
      | forallE name' type' body' binderInfo' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1.1, typeIH type' h.1.1.2,
            bodyIH body' h.1.2,
            candidateExprIdentityBinderInfoEq_sound _ _ h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | letE name type value body nondep typeIH valueIH bodyIH =>
      cases right with
      | letE name' type' value' body' nondep' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1.1.1, typeIH type' h.1.1.1.2,
            valueIH value' h.1.1.2, bodyIH body' h.1.2, h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | lit literal =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | mdata data expr exprIH =>
      cases right <;> simp_all [candidateExprIdentityExprEq]
  | proj typeName idx struct structIH =>
      cases right with
      | proj typeName' idx' struct' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1, h.1.2, structIH struct' h.2]
      | _ => simp_all [candidateExprIdentityExprEq]

/-- Executable sufficient check for the recursive identity witness consumed
by generation.  Unlike a root-only equality, it checks every retained domain,
body, annotation result, and terminal node. -/
def CandidateExprIdentity.check :
    {candidateContext : AddInductive.Context} → {source : Lean.Expr} →
      AddInductive.CandidateExprTrace candidateContext source → Bool
  | _, _, .terminal _ source _ result _ _ =>
      candidateExprIdentityExprEq result source
  | _, _, .forallE _ source _ name domain body binderInfo _ annotations _ _ _
      domainCandidate bodyCandidate =>
    candidateExprIdentityExprEq source
        (.forallE name domain body binderInfo) &&
      candidateExprIdentityExprEq annotations.consumed domain &&
        CandidateExprIdentity.check domainCandidate &&
          CandidateExprIdentity.check bodyCandidate

/-- Executable sufficient equality check for the terminal expression selected
by a candidate trace.  This is useful when the family validator must name its
result universe without unfolding the proof-carrying trace. -/
def CandidateExprIdentity.terminalCheck
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (expected : Lean.Expr) : Bool :=
  candidateExprIdentityExprEq trace.terminalResult expected

theorem CandidateExprIdentity.terminalResult_eq_of_check
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {expected : Lean.Expr}
    (h : CandidateExprIdentity.terminalCheck trace expected = true) :
    trace.terminalResult = expected :=
  candidateExprIdentityExprEq_sound _ _ h

/-- A successful structural check yields the full recursive identity witness;
the Boolean contributes no semantic authority beyond these proved equalities. -/
theorem CandidateExprIdentity.of_check
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (h : CandidateExprIdentity.check trace = true) :
    CandidateExprIdentity trace := by
  induction trace with
  | terminal context source inferred result checked normalized =>
      simp only [CandidateExprIdentity.check] at h
      exact .terminal (candidateExprIdentityExprEq_sound result source h)
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
      simp only [CandidateExprIdentity.check, Bool.and_eq_true] at h
      exact .forallE domainCandidate bodyCandidate
        (candidateExprIdentityExprEq_sound _ _ h.1.1.1)
        (candidateExprIdentityExprEq_sound _ _ h.1.1.2)
        (domainIH h.1.2) (bodyIH h.2)

/-- An identity-normalizing trace necessarily preserves the stored main Pi
spine. This turns the recursive identity witness into the Boolean gate used
by the generation assembler. -/
theorem CandidateExprIdentity.storedSpine
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (identity : CandidateExprIdentity trace) :
    trace.storedSpine = true := by
  induction identity with
  | terminal => rfl
  | forallE _ _ source_eq _ _ _ _ bodyIH =>
    simp [AddInductive.CandidateExprTrace.storedSpine,
      source_eq, Expr.structuralEq_refl, bodyIH]

/-- Exact component inversion for a strict translation of a kernel Pi. -/
theorem TrExprS.forallE_components
    (run : TrExprS env Us Δ (.forallE name domain body binderInfo) source') :
    ∃ domain' body',
      source' = .forallE domain' body' ∧
      env.IsType Us.length Δ.toCtx domain' ∧
      env.IsType Us.length (domain' :: Δ.toCtx) body' ∧
      TrExprS env Us Δ domain domain' ∧
      TrExprS env Us ((none, .vlam domain') :: Δ) body body' := by
  cases run with
  | forallE domainType bodyType domain_tr body_tr =>
    exact ⟨_, _, rfl, domainType, bodyType, domain_tr, body_tr⟩

/-- Recursively turn every retained candidate observation into verified
normalization evidence, constructing and transporting the exact verified
binder context at each Pi node. -/
theorem CandidateExprRun.exists_ofCandidate
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (candidateRun : CandidateContextRun candidateContext)
    (source' : VExpr)
    (source_tr : candidateRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ view' inferred',
      Nonempty (CandidateExprRun candidateRun.context.venv
        candidateRun.context.lparams trace candidateRun.context.vlctx
        source' view' inferred') := by
  induction trace generalizing source' with
  | terminal context source inferred result checked normalized =>
    obtain ⟨inferred', result', _, _, ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidate context source inferred result
        checked normalized candidateRun.context candidateRun.context_eq
        candidateRun.state_wf source' source_tr
        context.fuel.recDepth whnfFuel rfl whnfDepth
    exact ⟨result', inferred', ⟨.terminal node⟩⟩
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized
      domainCandidate bodyCandidate domainIH bodyIH =>
    obtain ⟨inferred', result', _, result_tr, ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidate context source inferred
        (.forallE name domain body binderInfo) checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        source' source_tr context.fuel.recDepth whnfFuel rfl whnfDepth
    let .forallE domainType bodyType domain_tr body_tr := result_tr
    obtain ⟨u, domainTypeHasType⟩ := domainType
    obtain ⟨v, bodyTypeHasType⟩ := bodyType
    obtain ⟨domainView', domainInferred', ⟨domainRun⟩⟩ :=
      domainIH candidateRun _ domain_tr whnfDepth
    obtain ⟨storedDomain', storedDomain_tr⟩ :=
      candidateTypeAnnotation_exists_translation annotations.trace domain_tr
    let annotationsRun := IsDefEqRun.ofCandidateStep
      ⟨context, domain, annotations.consumed⟩ annotationsEq
      candidateRun.context candidateRun.context_eq rfl rfl rfl
      candidateRun.state_wf domain_tr storedDomain_tr
      context.fuel.recDepth rfl
    have henv : VEnv.WF candidateRun.context.venv :=
      candidateRun.context.Ewf
    have hΔ : OnCtx candidateRun.context.vlctx.toCtx
        (candidateRun.context.venv.IsType
          candidateRun.context.lparams.length) :=
      candidateRun.context.Δwf.toCtx
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ domainTypeHasType
    let bodyCandidateRun := candidateRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr
        ⟨u, annotationDef.hasType.2⟩
    have bodyVenv : bodyCandidateRun.context.venv =
        candidateRun.context.venv := rfl
    have bodyLparams : bodyCandidateRun.context.lparams =
        candidateRun.context.lparams := rfl
    have bodyVlctx : bodyCandidateRun.context.vlctx =
        (some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam storedDomain') :: candidateRun.context.vlctx := rfl
    have bodyDepth :
        (context.pushLocalDecl name binderInfo
          annotations.consumed).fuel.recDepth = whnfFuel + 1 := by
      simpa [AddInductive.Context.pushLocalDecl] using whnfDepth
    have domainContext : VLCtx.IsDefEq
        candidateRun.context.venv candidateRun.context.lparams.length
        ((none, .vlam _) :: candidateRun.context.vlctx)
        ((none, .vlam storedDomain') :: candidateRun.context.vlctx) :=
      .cons (.refl henv candidateRun.context.Δwf) (by nofun)
        (.vlam annotationDef)
    obtain ⟨storedBody', storedBody_tr⟩ :=
      body_tr.defeqDFC henv domainContext
    have hRawBody : OnCtx
        (_ :: candidateRun.context.vlctx.toCtx)
        (candidateRun.context.venv.IsType
          candidateRun.context.lparams.length) :=
      ⟨hΔ, ⟨u, domainTypeHasType⟩⟩
    have bodySource :=
      (body_tr.uniq henv domainContext storedBody_tr).of_l
        henv hRawBody bodyTypeHasType
    have bodyΔwf := bodyCandidateRun.context.Δwf
    rw [bodyVenv, bodyLparams, bodyVlctx] at bodyΔwf
    have instantiatedBody_tr :=
      storedBody_tr.inst_fvar henv.ordered bodyΔwf
    obtain ⟨bodyView', bodyInferred', ⟨bodyRun⟩⟩ :=
      bodyIH bodyCandidateRun _ (by
        change TrExprS bodyCandidateRun.context.venv
          bodyCandidateRun.context.lparams bodyCandidateRun.context.vlctx
          (body.instantiate1 context.freshExpr) _
        rw [bodyVenv, bodyLparams, bodyVlctx]
        simpa only [AddInductive.Context.freshExpr,
          Expr.instantiate1_eq] using instantiatedBody_tr)
        bodyDepth
    refine ⟨.forallE domainView' bodyView', inferred', ⟨?_⟩⟩
    exact .forallE annotations annotationsEq domainCandidate bodyCandidate node
      domainRun annotationsRun bodyRun domainTypeHasType bodyTypeHasType
      bodySource bodyVlctx

/-- Interpret a recursively identity-normalizing candidate at the exact
strict Theory translation of its source.

Unlike `exists_ofCandidate`, whose verified executions select an existential
Theory endpoint, this theorem retains `source'` as the endpoint at every
recursive position. That stronger conclusion is what the generation spine
assembler needs for declarations whose executable normalization is
syntactically the identity. -/
theorem CandidateExprRun.exists_ofIdentity
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (identity : CandidateExprIdentity trace)
    (candidateRun : CandidateContextRun candidateContext)
    (source' : VExpr)
    (source_tr : candidateRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ inferred', Nonempty
      (CandidateExprRun candidateRun.context.venv
        candidateRun.context.lparams trace candidateRun.context.vlctx
        source' source' inferred') := by
  induction identity generalizing source' with
  | @terminal result source context inferred checked normalized result_eq =>
    subst result
    obtain ⟨inferred', ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidateAtResult
        context source inferred source checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        source' source' source_tr source_tr
        context.fuel.recDepth whnfFuel rfl whnfDepth
    exact ⟨inferred', ⟨.terminal node⟩⟩
  | @forallE context domain name binderInfo source inferred body fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate source_eq consumed_eq domainIdentity bodyIdentity
      domainIH bodyIH =>
    subst source
    obtain ⟨domain', body', rfl, domainWF, bodyWF, domain_tr, body_tr⟩ :=
      TypeChecker.TrExprS.forallE_components source_tr
    obtain ⟨u, domainType⟩ := domainWF
    obtain ⟨v, bodyType⟩ := bodyWF
    obtain ⟨inferred', ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidateAtResult
        context (.forallE name domain body binderInfo) inferred
        (.forallE name domain body binderInfo) checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        (.forallE domain' body') (.forallE domain' body')
        source_tr source_tr
        context.fuel.recDepth whnfFuel rfl whnfDepth
    obtain ⟨domainInferred', ⟨domainRun⟩⟩ :=
      domainIH candidateRun domain' domain_tr whnfDepth
    have consumed_tr : candidateRun.context.TrExprS
        annotations.consumed domain' := by
      rw [consumed_eq]
      exact domain_tr
    let annotationsRun := IsDefEqRun.ofCandidateStep
      ⟨context, domain, annotations.consumed⟩ annotationsEq
      candidateRun.context candidateRun.context_eq rfl rfl rfl
      candidateRun.state_wf domain_tr consumed_tr
      context.fuel.recDepth rfl
    let bodyCandidateRun := candidateRun.pushLocalDecl name binderInfo
      annotations.consumed fresh domain' consumed_tr ⟨u, domainType⟩
    have bodyVenv : bodyCandidateRun.context.venv =
        candidateRun.context.venv := rfl
    have bodyLparams : bodyCandidateRun.context.lparams =
        candidateRun.context.lparams := rfl
    have bodyVlctx : bodyCandidateRun.context.vlctx =
        (some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam domain') :: candidateRun.context.vlctx := rfl
    have bodyDepth :
        (context.pushLocalDecl name binderInfo
          annotations.consumed).fuel.recDepth =
          whnfFuel + 1 := by
      simpa [AddInductive.Context.pushLocalDecl] using whnfDepth
    have bodyDeltaWF := bodyCandidateRun.context.Δwf
    rw [bodyVenv, bodyLparams, bodyVlctx] at bodyDeltaWF
    have instantiatedBody_tr :=
      body_tr.inst_fvar candidateRun.context.Ewf.ordered
        bodyDeltaWF
    obtain ⟨bodyInferred', ⟨bodyRun⟩⟩ :=
      bodyIH bodyCandidateRun body' (by
        change TrExprS bodyCandidateRun.context.venv
          bodyCandidateRun.context.lparams bodyCandidateRun.context.vlctx
          (body.instantiate1 context.freshExpr) body'
        rw [bodyVenv, bodyLparams, bodyVlctx]
        simpa only [AddInductive.Context.freshExpr,
          Expr.instantiate1_eq] using instantiatedBody_tr)
        bodyDepth
    refine ⟨inferred', ⟨?_⟩⟩
    exact .forallE annotations annotationsEq domainCandidate bodyCandidate
      node domainRun annotationsRun bodyRun domainType bodyType bodyType rfl

/-- Recover a trace root's strict source translation from its retained full
check.  Unlike recursive child nodes, whose source translations are obtained
from the parent Pi translation, a root needs only the checker's syntactic
free-variable premise. -/
theorem candidateExprTrace_exists_source_translation
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (candidateRun : CandidateContextRun candidateContext)
    (source_fvars :
      source.FVarsIn (· ∈ candidateRun.context.vlctx.fvars)) :
    ∃ source', candidateRun.context.TrExprS source source' := by
  let checked := trace.rootCheck
  obtain ⟨source', _, source_tr, _, _⟩ :=
    candidateCheckTypeStep_exists_translation
      ⟨candidateContext, source, checked.inferred⟩ checked.valid
      candidateRun.context candidateRun.context_eq candidateRun.state_wf
      source_fvars candidateContext.fuel.recDepth rfl
  exact ⟨source', source_tr⟩

/-- Recursively certify an annotation-complete candidate trace without asking
the caller for any Theory expression. The retained root full check chooses the
source translation; all output and child translations then come from verified
checker executions, structural annotation traces, and Pi decomposition. -/
theorem CandidateExprRun.exists_ofCandidateFVars
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (candidateRun : CandidateContextRun candidateContext)
    (source_fvars :
      source.FVarsIn (· ∈ candidateRun.context.vlctx.fvars))
    (whnfFuel : Nat)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ source' view' inferred',
      candidateRun.context.TrExprS source source' ∧
      Nonempty (CandidateExprRun candidateRun.context.venv
        candidateRun.context.lparams trace candidateRun.context.vlctx
        source' view' inferred') := by
  obtain ⟨source', source_tr⟩ :=
    candidateExprTrace_exists_source_translation trace candidateRun
      source_fvars
  obtain ⟨view', inferred', run⟩ :=
    CandidateExprRun.exists_ofCandidate trace candidateRun source'
      source_tr whnfFuel whnfDepth
  exact ⟨source', view', inferred', source_tr, run⟩

/-- Fold a complete candidate trace into the compositional equality language
consumed by `NormalizationRun` and `GenerationRun`. -/
theorem CandidateExprRun.evidence
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr} :
    CandidateExprRun env Us trace Δ source' view' inferred' →
      DefEqEvidence env Us.length Δ.toCtx source' view' inferred'
  | .terminal node => node.evidence
  | .forallE _ _ _ _ node domainRun annotationsRun bodyRun domainType
      bodyType bodySource bodyContext => by
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
    have domainEvidence := domainRun.evidence
    obtain ⟨_, domainTypeEq⟩ :=
      domainType.uniq henv hΓ domainEvidence.isDefEq
    have domainAtSort : DefEqEvidence env Us.length Δ.toCtx
        _ _ (.sort _) :=
      .change domainTypeEq.symm domainEvidence
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΓ domainType
    have domainContext : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: Δ) ((none, .vlam _) :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam annotationDef)
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have bodyStoredType :=
      bodySource.hasType.2.defeqDFC henv domainContext.defeqCtx
    have hBodyΓ : OnCtx (_ :: Δ.toCtx) (env.IsType Us.length) :=
      ⟨hΓ, ⟨_, annotationDef.hasType.2⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyStoredType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyAtSortStored : DefEqEvidence env Us.length
        (_ :: Δ.toCtx) _ _ (.sort _) :=
      .change bodyTypeEq.symm bodyEvidence
    have bodyAtSortRaw :=
      bodyAtSortStored.isDefEq.defeqDFC henv
        (domainContext.symm henv).defeqCtx
    have bodyFinal := bodySource.trans bodyAtSortRaw
    have piEvidence := DefEqEvidence.forallE domainAtSort
      (DefEqEvidence.ofDefEq bodyFinal)
    obtain ⟨_, nodeTypeEq⟩ :=
      node.evidence.isDefEq.uniq henv hΓ (domainType.forallE bodyType)
    exact .trans node.evidence (.change nodeTypeEq.symm piEvidence)

/-- The raw root of a recursively interpreted trace has the strict Theory
translation retained by its paired full-check run. -/
theorem CandidateExprRun.source_tr
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    TrExprS env Us Δ source source' := by
  cases run with
  | terminal node => exact node.check.expr_tr
  | forallE _ _ _ _ node => exact node.check.expr_tr

/-- Move a weak expression translation between definitionally equal verified
local contexts while retaining its named Theory meaning. -/
private theorem candidateTrExpr_moveCtx
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExpr env Us Δ₁ e e') :
    TrExpr env Us Δ₂ e e' := by
  obtain ⟨e₂, he₂, hdef⟩ := H
  have moved : TrExpr env Us Δ₂ e e₂ :=
    he₂.defeqDFC' henv hctx
  exact moved.defeq henv (hctx.symm henv).wf.toCtx
    (hdef.defeqDFC henv hctx.defeqCtx)

/-- The recursively reconstructed kernel candidate view translates to the
Theory view named by `CandidateExprRun`.

At Pi nodes the instantiated child body is first abstracted from its exact
free-variable context and then transported from the raw-domain context to the
definitionally equal normalized-domain context.  This closes the provenance
loop: the emitted Theory equality is not only between two well-typed terms;
both endpoints are translations of the source-indexed candidate syntax. -/
theorem CandidateExprRun.view_tr
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    TrExpr env Us Δ trace.view view' := by
  induction run with
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
      have henv : VEnv.WF env := by
        simpa only [node.whnf.venv_eq] using node.whnf.context.Ewf
      have hΔ : VLCtx.WF env Us.length Δ := by
        simpa only [node.whnf.venv_eq, node.whnf.lparams_eq,
          node.whnf.vlctx_eq] using node.whnf.context.Δwf
      simpa only [AddInductive.CandidateExprTrace.view] using
        node.whnf.rhs_tr.trExpr henv hΔ
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    obtain ⟨_, domainTypeEq⟩ :=
      domainType.uniq henv hΔ.toCtx domainRun.evidence.isDefEq
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      (DefEqEvidence.change domainTypeEq.symm domainRun.evidence).isDefEq
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    have bodyIH' : TrExpr env Us
        ((some (context.freshFVarId,
          annotations.consumed.fvarsList), .vlam storedDomain') :: Δ)
        bodyCandidate.view bodyView' := by
      simpa only [bodyContext] using bodyIH
    have bodyAbstract := bodyIH'.abstract VLCtx.Abstract.zero
    have hctx : VLCtx.IsDefEq env Us.length
        ((none, .vlam storedDomain') :: Δ)
        ((none, .vlam domainView') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun)
        (.vlam storedToView)
    have bodyMoved := candidateTrExpr_moveCtx henv hctx bodyAbstract
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have annotationContext : VLCtx.IsDefEq env Us.length
        ((none, .vlam domain') :: Δ)
        ((none, .vlam storedDomain') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam annotationDef)
    have bodyStoredType :=
      bodySource.hasType.2.defeqDFC henv annotationContext.defeqCtx
    have hBodyΓ : OnCtx (storedDomain' :: Δ.toCtx)
        (env.IsType Us.length) :=
      ⟨hΔ.toCtx, ⟨_, annotationDef.hasType.2⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyStoredType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyDefStored : env.IsDefEq Us.length
        (storedDomain' :: Δ.toCtx) storedBody' bodyView' (.sort v) :=
      (DefEqEvidence.change bodyTypeEq.symm bodyEvidence).isDefEq
    have bodyDefMoved :=
      bodyDefStored.defeqDFC henv hctx.defeqCtx
    have habstract :
        bodyCandidate.view.abstract #[context.freshExpr] =
          Expr.abstract1 context.freshFVarId bodyCandidate.view := by
      rw [show #[context.freshExpr] =
        ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
      simp only [Expr.abstract_eq, Expr.abstractList]
    apply TrExpr.forallE henv hΔ
    · exact ⟨_, domainDef.hasType.2⟩
    · exact ⟨_, bodyDefMoved.hasType.2⟩
    · exact domainIH
    · simpa only [AddInductive.CandidateExprTrace.view,
        habstract] using bodyMoved

/-- Exact-translation uniqueness for every expression that contributes to a
candidate view.  The abstracted-body clause names the syntax stored by
`CandidateExprTrace.view`, while the recursive body clause supports the next
candidate node.  Projections are intentionally excluded: their verified
Theory relation is only unique up to definitional equality. -/
def CandidateExprTraceViewIsUnique :
    {context : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace context source → Prop
  | _, _, .terminal _ _ _ result _ _ => TrExprS.IsUnique result
  | _, _, .forallE context _ _ _ _ _ _ _ _ _ _ _ domain body =>
      CandidateExprTraceViewIsUnique domain ∧
        CandidateExprTraceViewIsUnique body ∧
        TrExprS.IsUnique (body.view.abstract #[context.freshExpr])

/-- The recursive uniqueness certificate in particular covers the complete
view reconstructed at this candidate node. -/
theorem CandidateExprTraceViewIsUnique.view
    {context : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace context source}
    (unique : CandidateExprTraceViewIsUnique trace) :
    TrExprS.IsUnique trace.view := by
  induction trace with
  | terminal => exact unique
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate bodyCandidate
      domainIH bodyIH =>
    exact ⟨domainIH unique.1, unique.2.2⟩

/-- A projection-free candidate view retains the strict Theory translation
selected componentwise by its recursive semantic run.

The ordinary `view_tr` theorem must use weak translation because a projection
endpoint is only definitionally determined.  Under the explicit uniqueness
condition, recursive abstraction and context transport select the exact
analyzer-owned expression instead. -/
theorem CandidateExprRun.view_tr_strict
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (unique : CandidateExprTraceViewIsUnique trace) :
    TrExprS env Us Δ trace.view view' := by
  induction run with
  | terminal node =>
      simpa only [AddInductive.CandidateExprTrace.view] using
        node.whnf.rhs_tr
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    rcases unique with ⟨domainUnique, bodyUnique, abstractUnique⟩
    have domainStrict := domainIH domainUnique
    have bodyStrict : TrExprS env Us
        ((some (context.freshFVarId,
          annotations.consumed.fvarsList), .vlam storedDomain') :: Δ)
        bodyCandidate.view bodyView' := by
      simpa only [bodyContext] using bodyIH bodyUnique
    have bodyAbstract := bodyStrict.abstract VLCtx.Abstract.zero
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    obtain ⟨_, domainTypeEq⟩ :=
      domainType.uniq henv hΔ.toCtx domainRun.evidence.isDefEq
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      (DefEqEvidence.change domainTypeEq.symm domainRun.evidence).isDefEq
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    have hctx : VLCtx.IsDefEq env Us.length
        ((none, .vlam storedDomain') :: Δ)
        ((none, .vlam domainView') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam storedToView)
    obtain ⟨bodyMoved', bodyMoved⟩ :=
      bodyAbstract.defeqDFC henv hctx
    have habstract :
        bodyCandidate.view.abstract #[context.freshExpr] =
          Expr.abstract1 context.freshFVarId bodyCandidate.view := by
      rw [show #[context.freshExpr] =
        ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
      simp only [Expr.abstract_eq, Expr.abstractList]
    have bodyAbstractArray : TrExprS env Us
        ((none, .vlam storedDomain') :: Δ)
        (bodyCandidate.view.abstract #[context.freshExpr]) bodyView' := by
      simpa only [habstract] using bodyAbstract
    have bodyMovedArray : TrExprS env Us
        ((none, .vlam domainView') :: Δ)
        (bodyCandidate.view.abstract #[context.freshExpr]) bodyMoved' := by
      simpa only [habstract] using bodyMoved
    have bodyMoved_eq : bodyMoved' = bodyView' := by
      exact (bodyAbstractArray.unique'
        (.cons .base .vlam) abstractUnique bodyMovedArray).symm
    subst bodyMoved'
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have annotationContext : VLCtx.IsDefEq env Us.length
        ((none, .vlam domain') :: Δ)
        ((none, .vlam storedDomain') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam annotationDef)
    have bodyStoredType :=
      bodySource.hasType.2.defeqDFC henv annotationContext.defeqCtx
    have hBodyΓ : OnCtx (storedDomain' :: Δ.toCtx)
        (env.IsType Us.length) :=
      ⟨hΔ.toCtx, ⟨_, annotationDef.hasType.2⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyStoredType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyDefStored : env.IsDefEq Us.length
        (storedDomain' :: Δ.toCtx) storedBody' bodyView' (.sort v) :=
      (DefEqEvidence.change bodyTypeEq.symm bodyEvidence).isDefEq
    have bodyDefMoved :=
      bodyDefStored.defeqDFC henv hctx.defeqCtx
    simpa only [AddInductive.CandidateExprTrace.view, habstract] using
      TrExprS.forallE
        (⟨u, domainDef.hasType.2⟩ :
          env.IsType Us.length Δ.toCtx domainView')
        (⟨v, bodyDefMoved.hasType.2⟩ :
          env.IsType Us.length (domainView' :: Δ.toCtx) bodyView')
        domainStrict bodyMoved

/-- Root-level verified context and translations for an exact executable
candidate expression and an explicitly named Theory view.

The raw endpoint is a strict translation of the stored kernel source. The
view endpoint translates the exact reconstructed candidate syntax; allowing
the ordinary `TrExpr` relation here accounts for the definitional transport
performed while recursively rebuilding Pi bodies. -/
structure CandidateExprRootRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' view' : VExpr) where
  contextRun : CandidateContextRun candidate.context
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []
  source_tr : TrExprS env Us [] source source'
  view_tr : TrExpr env Us [] candidate.view view'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1

/-- Interpret a root candidate against its explicitly translated endpoints.
The candidate view is not selected from a proof-only existential: the caller
names it and proves that it translates the exact executable view, while the
verified recursive run supplies the equality to the strict raw endpoint. -/
theorem CandidateExprRootRun.evidence
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source}
    {source' view' : VExpr}
    (run : CandidateExprRootRun env Us candidate source' view') :
    ∃ A, DefEqEvidence env Us.length [] source' view' A := by
  have source_tr : run.contextRun.context.TrExprS source source' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.source_tr
  obtain ⟨candidateView', inferred', ⟨candidateRun⟩⟩ :=
    CandidateExprRun.exists_ofCandidate candidate.trace run.contextRun
      source' source_tr run.whnfFuel run.whnfDepth
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.contextRun.context.Ewf
  have hΔ : VLCtx.WF env Us.length [] := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      run.contextRun.context.Δwf
  have candidateView_tr :
      TrExpr env Us [] candidate.view candidateView' := by
    simpa only [AddInductive.CandidateExpr.view, run.venv_eq,
      run.lparams_eq, run.vlctx_eq] using
      candidateRun.view_tr
  have viewDef : env.IsDefEqU Us.length [] candidateView' view' :=
    candidateView_tr.uniq henv (.refl henv hΔ) run.view_tr
  have sourceDef : env.IsDefEqU Us.length [] source' candidateView' := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq,
      VLCtx.toCtx] using
      candidateRun.evidence.isDefEq.toU
  obtain ⟨A, hfinal⟩ := sourceDef.trans henv hΔ.toCtx viewDef
  exact ⟨A, .ofDefEq hfinal⟩

/-- A root candidate together with the exact recursively interpreted semantic
run selected by its retained checker executions.

Unlike `CandidateExprRootRun`, this bundle does not stop at whole-expression
equality: it retains the exact inferred type and reconstructed Theory view at
every recursive candidate position. Consequently the same value can supply
both normalization evidence and, when the executable trace preserves its main
Pi spine, the positional telescope/result evidence required by generation.
The view is selected by the verified run rather than supplied independently by
a caller. -/
structure CandidateExprSemanticRootRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' : VExpr) where
  contextRun : CandidateContextRun candidate.context
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []
  source_tr : TrExprS env Us [] source source'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1
  view : VExpr
  recursive : ∃ inferred, CandidateExprRun env Us candidate.trace []
    source' view inferred

/-- Forget the retained recursive run and expose the existing root semantic
interface. The reconstructed view translation is derived from that same run,
so it cannot name an unrelated endpoint. -/
def CandidateExprSemanticRootRun.root
    (run : CandidateExprSemanticRootRun env Us candidate source') :
    CandidateExprRootRun env Us candidate source' run.view where
  contextRun := run.contextRun
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq
  vlctx_eq := run.vlctx_eq
  source_tr := run.source_tr
  view_tr := by
    obtain ⟨_, recursive⟩ := run.recursive
    simpa only [AddInductive.CandidateExpr.view] using
      recursive.view_tr
  whnfFuel := run.whnfFuel
  whnfDepth := run.whnfDepth

/-- Automatically construct the retained root semantics from an exact
verified candidate context and strict translation of the stored kernel
source.

The checker run selects the Theory view and inferred type existentially; the
result records those exact selections. No caller-selected normalization view,
erasure equality, or whole-Pi injectivity principle is used. -/
theorem CandidateExprSemanticRootRun.exists_ofCandidate
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (contextRun : CandidateContextRun candidate.context)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = [])
    (source_tr : TrExprS env Us [] source source')
    (whnfFuel : Nat)
    (whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1) :
    Nonempty (CandidateExprSemanticRootRun env Us candidate source') := by
  have contextualSource :
      contextRun.context.TrExprS source source' := by
    simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
      source_tr
  obtain ⟨view, inferred, ⟨recursive⟩⟩ :=
    CandidateExprRun.exists_ofCandidate candidate.trace contextRun source'
      contextualSource whnfFuel whnfDepth
  refine ⟨{
    contextRun := contextRun
    venv_eq := venv_eq
    lparams_eq := lparams_eq
    vlctx_eq := vlctx_eq
    source_tr := source_tr
    whnfFuel := whnfFuel
    whnfDepth := whnfDepth
    view := view
    recursive := ⟨inferred, ?_⟩ }⟩
  simpa only [venv_eq, lparams_eq, vlctx_eq] using recursive

/-- The exact pre-run evidence needed to interpret one candidate root without
asking a caller to choose its normalized Theory view.

This bundle deliberately stops before the recursive semantic run.  It contains
only the verified implementation context, its alignment with the requested
Theory environment, the strict translation of the stored source, and the fuel
relation consumed by `CandidateExprRun.exists_ofCandidate`. -/
structure CandidateExprSemanticRootInput (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' : VExpr) where
  contextRun : CandidateContextRun candidate.context
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []
  source_tr : TrExprS env Us [] source source'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1

/-- Run the retained checker interpreter on an exact root input.  The result is
`Nonempty` because the checker-selected Theory view is semantic evidence rather
than executable metadata; no choice operator or caller-supplied endpoint is
introduced by this boundary. -/
theorem CandidateExprSemanticRootInput.exists
    (input : CandidateExprSemanticRootInput env Us candidate source') :
    Nonempty (CandidateExprSemanticRootRun env Us candidate source') :=
  CandidateExprSemanticRootRun.exists_ofCandidate input.contextRun
    input.venv_eq input.lparams_eq input.vlctx_eq input.source_tr
    input.whnfFuel input.whnfDepth

/-- Interpret an identity-normalizing staged root at the strict Theory
translation already owned by its source input.  This keeps the endpoint
definitionally fixed without caller-supplied WHNF data or a
`Classical.choice` over the general semantic interpreter. -/
def CandidateExprSemanticRootInput.semanticOfIdentity
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (input : CandidateExprSemanticRootInput env Us candidate source')
    (identity : CandidateExprIdentity candidate.trace) :
    CandidateExprSemanticRootRun env Us candidate source' where
  contextRun := input.contextRun
  venv_eq := input.venv_eq
  lparams_eq := input.lparams_eq
  vlctx_eq := input.vlctx_eq
  source_tr := input.source_tr
  whnfFuel := input.whnfFuel
  whnfDepth := input.whnfDepth
  view := source'
  recursive := by
    have source_tr : input.contextRun.context.TrExprS source source' := by
      simpa only [VContext.TrExprS, input.venv_eq, input.lparams_eq,
        input.vlctx_eq] using input.source_tr
    obtain ⟨inferred, ⟨recursive⟩⟩ :=
      CandidateExprRun.exists_ofIdentity candidate.trace identity
        input.contextRun source' source_tr input.whnfFuel input.whnfDepth
    refine ⟨inferred, ?_⟩
    simpa only [input.venv_eq, input.lparams_eq, input.vlctx_eq] using
      recursive

/-- Interpret a staged root at the deterministic translation of its
checker-selected view.  For a projection-free view the recursive semantic
run's endpoint is pinned by strict-translation agreement
(`CandidateExprRun.view_tr_strict` plus `TrExprS.trExprS?_eq`), so the
retained `view` field is computed by `trExprS?` and the `Nonempty`
interpretation is transferred onto it; no choice operator selects data.
Unlike `semanticOfIdentity` this covers non-identity normalizations, at the
cost of the executable view-uniqueness certificate. -/
def CandidateExprSemanticRootInput.semanticOfUnique
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (input : CandidateExprSemanticRootInput env Us candidate source')
    (unique : CandidateExprTraceViewIsUnique candidate.trace) :
    CandidateExprSemanticRootRun env Us candidate source' :=
  match hview : trExprS? Us [] candidate.trace.view with
  | some view =>
    { contextRun := input.contextRun
      venv_eq := input.venv_eq
      lparams_eq := input.lparams_eq
      vlctx_eq := input.vlctx_eq
      source_tr := input.source_tr
      whnfFuel := input.whnfFuel
      whnfDepth := input.whnfDepth
      view := view
      recursive := by
        obtain ⟨w⟩ := input.exists
        obtain ⟨inferred, run⟩ := w.recursive
        cases Option.some.inj
          (((run.view_tr_strict unique).trExprS?_eq unique.view).symm.trans
            hview)
        exact ⟨inferred, run⟩ }
  | none =>
      absurd
        (show (trExprS? Us [] candidate.trace.view).isSome by
          obtain ⟨w⟩ := input.exists
          obtain ⟨inferred, run⟩ := w.recursive
          exact TrExprS.trExprS?_isSome
            ⟨w.view, run.view_tr_strict unique⟩ unique.view)
        (by simp [hview])

/-- One explicitly verified root stage shared by every candidate expression
interpreted before or after family insertion.

The stage owns the implementation/Theory context alignment once. Individual
source positions retain only their strict translation, fuel relation, and the
equality identifying the candidate's stored context with this stage. This is
the reusable boundary between staged environment validation and the retained
recursive candidate interpreter. -/
structure CandidateSemanticStage
    (candidateContext : AddInductive.Context) (env : VEnv) (Us : List Name)
    where
  contextRun : CandidateContextRun candidateContext
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []

/-- Source-position evidence interpreted in one shared candidate stage.

`context_eq` prevents a verified stage for another producer position from
being reused. The normalized Theory endpoint is deliberately absent: it is
selected only by `CandidateExprSemanticRootInput.exists`. -/
structure CandidateExprStagedInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (stage : CandidateSemanticStage candidateContext env Us)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' : VExpr) where
  context_eq : candidateContext = candidate.context
  source_tr : TrExprS env Us [] source source'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1

/-- Specialize a shared verified stage to one exact source-indexed candidate
root. This is a pure dependent transport; it neither runs the checker nor
chooses the semantic view. -/
def CandidateExprStagedInput.rootInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {source : Expr} {candidate : AddInductive.CandidateExpr source}
    {source' : VExpr}
    {stage : CandidateSemanticStage candidateContext env Us}
    (input : CandidateExprStagedInput stage candidate source') :
    CandidateExprSemanticRootInput env Us candidate source' := by
  cases input.context_eq
  exact {
    contextRun := stage.contextRun
    venv_eq := stage.venv_eq
    lparams_eq := stage.lparams_eq
    vlctx_eq := stage.vlctx_eq
    source_tr := input.source_tr
    whnfFuel := input.whnfFuel
    whnfDepth := input.whnfDepth }

/-- Pointwise checker-produced equality for a pair of binder telescopes. The
tail is checked in the context extended by the raw binder, exactly matching
`VEnv.TelDefEq` and the mixed generator's raw-binder discipline. -/
inductive TelDefEqEvidence (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → List VExpr → Prop where
  | nil : TelDefEqEvidence env U Γ [] []
  | cons
      (head : DefEqEvidence env U Γ A A' (.sort u))
      (tail : TelDefEqEvidence env U (A :: Γ) As As') :
      TelDefEqEvidence env U Γ (A :: As) (A' :: As')

/-- Interpret pointwise checker evidence as the Theory telescope equality
consumed by `GenerationChecked.WF`. -/
theorem TelDefEqEvidence.telDefEq :
    TelDefEqEvidence env U Γ As As' →
      env.TelDefEq U Γ As As'
  | .nil => trivial
  | .cons head tail => ⟨⟨_, head.isDefEq⟩, tail.telDefEq⟩

/-- Pointwise telescope equality followed by equality of the terminal result.

Keeping these witnesses in one inductive preserves the raw-binder context at
every recursive step.  In particular, the result is checked in
`rawBinders.reverse ++ Γ`, exactly the context used by mixed generation. -/
inductive TelResultDefEqEvidence (env : VEnv) (U : Nat) :
    (Γ : List VExpr) → (rawBinders viewBinders : List VExpr) →
      (rawResult viewResult resultType : VExpr) → Prop where
  | terminal
      (result : DefEqEvidence env U Γ rawResult viewResult resultType) :
      TelResultDefEqEvidence env U Γ [] [] rawResult viewResult resultType
  | forallE
      (domain : DefEqEvidence env U Γ rawDomain viewDomain (.sort u))
      (tail : TelResultDefEqEvidence env U (rawDomain :: Γ)
        rawBinders viewBinders rawResult viewResult resultType) :
      TelResultDefEqEvidence env U Γ
        (rawDomain :: rawBinders) (viewDomain :: viewBinders)
        rawResult viewResult resultType

/-- Telescope component of a combined spine/result certificate. -/
theorem TelResultDefEqEvidence.telescope :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      TelDefEqEvidence env U Γ rawBinders viewBinders
  | .terminal _ => .nil
  | .forallE domain tail => .cons domain tail.telescope

/-- Terminal component, in the context generated by all raw binders. -/
theorem TelResultDefEqEvidence.result :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      DefEqEvidence env U (rawBinders.reverse ++ Γ)
        rawResult viewResult resultType
  | .terminal result => by simpa using result
  | .forallE _ tail => by
      simpa [List.reverse_cons, List.append_assoc] using tail.result

theorem TelResultDefEqEvidence.length_eq :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      rawBinders.length = viewBinders.length
  | .terminal _ => rfl
  | .forallE _ tail => congrArg Nat.succ tail.length_eq

/-- Reify a Theory telescope equality as explicit checker-produced evidence.
This direction is useful after telescope operations such as `take`, `drop`,
and context transport have rearranged a candidate certificate. -/
theorem TelDefEqEvidence.ofTelDefEq :
    ∀ {Γ As As'}, env.TelDefEq U Γ As As' →
      TelDefEqEvidence env U Γ As As'
  | _, [], [], _ => .nil
  | _, _ :: _, _ :: _, ⟨⟨_, head⟩, tail⟩ =>
    .cons (.ofDefEq head) (TelDefEqEvidence.ofTelDefEq tail)

/-- Retain an exact prefix of a checker-produced telescope certificate. -/
theorem TelDefEqEvidence.take
    (run : TelDefEqEvidence env U Γ As As') (n : Nat) :
    TelDefEqEvidence env U Γ (As.take n) (As'.take n) :=
  .ofTelDefEq (run.telDefEq.take n)

/-- Transport a checker-produced telescope certificate through environment
growth. -/
theorem TelDefEqEvidence.mono
    (run : TelDefEqEvidence env U Γ As As') (henv : env ≤ env') :
    TelDefEqEvidence env' U Γ As As' :=
  .ofTelDefEq (run.telDefEq.mono henv)

/-- Combine an independently transformed telescope certificate with its
terminal result certificate. -/
theorem TelResultDefEqEvidence.ofTelescopeResult
    (tel : TelDefEqEvidence env U Γ rawBinders viewBinders)
    (result : DefEqEvidence env U (rawBinders.reverse ++ Γ)
      rawResult viewResult resultType) :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType := by
  induction tel with
  | nil => exact .terminal (by simpa using result)
  | cons head tail ih =>
    exact .forallE head (ih (by
      simpa [List.reverse_cons, List.append_assoc] using result))

private theorem candidateDefEqCtx_trans (henv : VEnv.WF env) :
    ∀ {Γ₁ Γ₂ Γ₃},
      env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.IsDefEqCtx U [] Γ₂ Γ₃ →
      env.IsDefEqCtx U [] Γ₁ Γ₃
  | _, _, _, .zero, h₂₃ => h₂₃
  | _, _, _, .succ h₁₂ head₁₂, .succ h₂₃ head₂₃ => by
    have tail := candidateDefEqCtx_trans henv h₁₂ h₂₃
    have head₂₃' := head₂₃.defeqDFC henv (h₁₂.symm henv)
    exact .succ tail (VEnv.IsDefEq.trans_l henv h₁₂.isType
      head₁₂ head₂₃')

private theorem candidateTelDefEq_defeqDFC (henv : VEnv.WF env)
    (hctx : env.IsDefEqCtx U [] Γ₁ Γ₂) :
    ∀ {As As'}, env.TelDefEq U Γ₁ As As' →
      env.TelDefEq U Γ₂ As As'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨u, head⟩, tail⟩ =>
    ⟨⟨u, head.defeqDFC henv hctx⟩,
      candidateTelDefEq_defeqDFC henv
        (.succ hctx head.hasType.1) tail⟩

private theorem candidateTelDefEq_append
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As As' Bs Bs'}, env.TelDefEq U Γ As As' →
      env.TelDefEq U (As.reverse ++ Γ) Bs Bs' →
      env.TelDefEq U Γ (As ++ Bs) (As' ++ Bs')
  | [], [], _, _, _, suffix => by simpa using suffix
  | _ :: As, _ :: As', Bs, Bs', ⟨head, tail⟩, suffix => by
    exact ⟨head, candidateTelDefEq_append tail (by
      simpa [List.reverse_cons, List.append_assoc] using suffix)⟩

/-- Replace a constructor candidate's stored parameter prefix by the family's
raw parameter prefix.

The two raw prefixes need not be syntactically equal: both are related to the
same checked view prefix. The field telescope and terminal result are then
transported through the induced context equality, yielding exactly the mixed
raw/view context emitted by generation. -/
theorem TelResultDefEqEvidence.replacePrefix
    (henv : VEnv.WF env)
    (newPrefix : TelDefEqEvidence env U [] newRawPrefix viewPrefix)
    (run : TelResultDefEqEvidence env U []
      (oldRawPrefix ++ rawSuffix) (viewPrefix ++ viewSuffix)
      rawResult viewResult resultType)
    (prefixLength : oldRawPrefix.length = viewPrefix.length) :
    TelResultDefEqEvidence env U []
      (newRawPrefix ++ rawSuffix) (viewPrefix ++ viewSuffix)
      rawResult viewResult resultType := by
  have declaredTel := run.telescope.telDefEq
  have oldPrefix : env.TelDefEq U [] oldRawPrefix viewPrefix := by
    have hprefix := declaredTel.take oldRawPrefix.length
    simpa [prefixLength] using hprefix
  have oldSuffix : env.TelDefEq U oldRawPrefix.reverse
      rawSuffix viewSuffix := by
    have suffix := declaredTel.drop oldRawPrefix.length
    simpa [prefixLength] using suffix
  have newPrefixTheory := newPrefix.telDefEq
  have newPrefixContext : env.IsDefEqCtx U []
      newRawPrefix.reverse viewPrefix.reverse := by
    simpa using newPrefixTheory.ctx
  have oldPrefixContext : env.IsDefEqCtx U []
      oldRawPrefix.reverse viewPrefix.reverse := by
    simpa using oldPrefix.ctx
  have prefixContext : env.IsDefEqCtx U []
      newRawPrefix.reverse oldRawPrefix.reverse :=
    candidateDefEqCtx_trans henv newPrefixContext
      (oldPrefixContext.symm henv)
  have newSuffix : env.TelDefEq U newRawPrefix.reverse
      rawSuffix viewSuffix :=
    candidateTelDefEq_defeqDFC henv (prefixContext.symm henv) oldSuffix
  have emittedTel : env.TelDefEq U []
      (newRawPrefix ++ rawSuffix) (viewPrefix ++ viewSuffix) :=
    candidateTelDefEq_append newPrefixTheory (by simpa using newSuffix)
  have fullContext : env.IsDefEqCtx U []
      ((newRawPrefix ++ rawSuffix).reverse)
      ((oldRawPrefix ++ rawSuffix).reverse) := by
    have extended := newSuffix.raw_onTel.extendDefEqCtx prefixContext
    simpa [List.reverse_append] using extended
  have oldResult : DefEqEvidence env U
      (oldRawPrefix ++ rawSuffix).reverse
      rawResult viewResult resultType := by
    simpa using run.result
  have emittedResult : DefEqEvidence env U
      (newRawPrefix ++ rawSuffix).reverse
      rawResult viewResult resultType :=
    .ofDefEq (oldResult.isDefEq.defeqDFC henv
      (fullContext.symm henv))
  exact TelResultDefEqEvidence.ofTelescopeResult
    (.ofTelDefEq emittedTel) (by simpa using emittedResult)

/-- Every recursive candidate run carries the well-formed local context used
by its root checker observation. -/
theorem CandidateExprRun.context_wf
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    VLCtx.WF env Us.length Δ := by
  cases run with
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
    simpa only [node.check.venv_eq, node.check.lparams_eq,
      node.check.vlctx_eq] using node.check.context.Δwf
  | forallE _ _ _ _ node =>
    simpa only [node.check.venv_eq, node.check.lparams_eq,
      node.check.vlctx_eq] using node.check.context.Δwf

private theorem candidateTelN_forallN_length :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.telN As.length (VExpr.forallN As B) = As
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.telN,
      candidateTelN_forallN_length As B]

private theorem candidateDropN_forallN_length :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.dropN As.length (VExpr.forallN As B) = B
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.dropN,
      candidateDropN_forallN_length As B]

/-- Syntactic terminal marker used only to recover a telescope from a known
`dropN` endpoint. -/
private def CandidateTerminal : VExpr → Prop
  | .forallE _ _ => False
  | _ => True

/-- If dropping `n` binders from a telescope reaches its non-forall terminal,
then taking `n` binders recovers the entire telescope. -/
private theorem candidateTelN_of_dropN_terminal
    {B : VExpr} (hB : CandidateTerminal B) :
    ∀ (As : List VExpr) (n : Nat),
      VExpr.dropN n (VExpr.forallN As B) = B →
      VExpr.telN n (VExpr.forallN As B) = As
  | [], n, _ => by
    cases B <;> cases n <;> simp_all [CandidateTerminal,
      VExpr.forallN, VExpr.dropN, VExpr.telN]
  | A :: As, 0, h => by
    cases B <;> simp_all [CandidateTerminal,
      VExpr.forallN, VExpr.dropN]
  | A :: As, n + 1, h => by
    simp only [VExpr.forallN, VExpr.telN,
      List.cons.injEq, true_and]
    exact candidateTelN_of_dropN_terminal hB As n (by
      simpa only [VExpr.forallN, VExpr.dropN] using h)

private theorem candidateTerminal_appN_app (f a : VExpr) :
    ∀ args, CandidateTerminal (VExpr.appN (.app f a) args)
  | [] => trivial
  | b :: args => candidateTerminal_appN_app (.app f a) b args

private theorem candidateTerminal_appN_const
    (name : Name) (levels : List VLevel) :
    ∀ args, CandidateTerminal (VExpr.appN (.const name levels) args)
  | [] => trivial
  | a :: args => candidateTerminal_appN_app (.const name levels) a args

/-- Recursive worker for candidate spine extraction.

`rawΔ` follows the contexts generated by the stored raw binders, while `Δ`
is the annotation-consumed context in which the candidate body was checked.
The explicit context equality transports each retained checker judgment back
to the raw side before it is added to the telescope certificate. -/
private theorem CandidateExprRun.spineEvidenceAux
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true)
    {rawΔ : VLCtx} {rawSource' : VExpr}
    (contextEq : VLCtx.IsDefEq env Us.length rawΔ Δ)
    (rawSource_tr : TrExprS env Us rawΔ source rawSource') :
    ∃ rawBinders viewBinders rawResult viewResult resultType,
      rawSource' = VExpr.forallN rawBinders rawResult ∧
      view' = VExpr.forallN viewBinders viewResult ∧
      TelResultDefEqEvidence env Us.length rawΔ.toCtx
        rawBinders viewBinders rawResult viewResult resultType ∧
      rawBinders.length = trace.spineLength := by
  induction run generalizing rawΔ rawSource' with
  | terminal node =>
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hRawΔ := contextEq.wf
    have rawToSource : env.IsDefEqU Us.length rawΔ.toCtx
        rawSource' _ :=
      rawSource_tr.uniq henv contextEq node.check.expr_tr
    have sourceToView :=
      node.evidence.isDefEq.defeqDFC henv
        (contextEq.symm henv).defeqCtx
    have final := VEnv.IsDefEq.transU_r henv hRawΔ.toCtx
      rawToSource sourceToView
    exact ⟨[], [], rawSource', _, _, rfl, rfl,
      .terminal (.ofDefEq final), rfl⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.storedSpine,
      Bool.and_eq_true] at aligned
    obtain ⟨sourceEq, bodyAligned⟩ := aligned
    have alignedSource_tr : TrExprS env Us rawΔ
        (.forallE name domain body binderInfo) rawSource' :=
      rawSource_tr.eqv (Expr.structuralEq_eqv sourceEq)
    let @TrExprS.forallE _ _ rawDomain rawBody _ _ _ _ _
        rawDomainType rawBodyType rawDomain_tr rawBody_tr := alignedSource_tr
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have hRawΔ := contextEq.wf
    have rawToDomainU :=
      rawDomain_tr.uniq henv contextEq domainRun.source_tr
    have domainTypeRaw :=
      domainType.defeqDFC henv (contextEq.symm henv).defeqCtx
    have rawToDomain :=
      rawToDomainU.of_r henv hRawΔ.toCtx domainTypeRaw
    have domainToView :=
      domainRun.evidence.isDefEq.toU.of_l henv hΔ.toCtx domainType
    have domainToViewRaw :=
      domainToView.defeqDFC henv (contextEq.symm henv).defeqCtx
    have head : DefEqEvidence env Us.length rawΔ.toCtx
        _ domainView' (.sort u) :=
      .ofDefEq (rawToDomain.trans domainToViewRaw)
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have annotationDefRaw :=
      annotationDef.defeqDFC henv (contextEq.symm henv).defeqCtx
    have rawToStored := rawToDomain.trans annotationDefRaw
    have bodyWF := bodyRun.context_wf
    rw [bodyContext] at bodyWF
    have rawFresh :
        ∀ fv deps,
          some (context.freshFVarId, annotations.consumed.fvarsList) =
              some (fv, deps) →
            fv ∉ rawΔ.fvars ∧ deps ⊆ rawΔ.fvars := by
      intro fv deps heq
      cases heq
      have hfresh := bodyWF.2.1 _ _ rfl
      simpa only [contextEq.fvars] using hfresh
    let rawBodyΔ : VLCtx :=
      (some (context.freshFVarId, annotations.consumed.fvarsList),
        .vlam rawDomain) :: rawΔ
    have bodyContextEqConcrete : VLCtx.IsDefEq env Us.length rawBodyΔ
        ((some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam storedDomain') :: Δ) :=
      .cons contextEq rawFresh (.vlam rawToStored)
    have bodyContextEq : VLCtx.IsDefEq env Us.length rawBodyΔ bodyΔ := by
      simpa only [bodyContext] using bodyContextEqConcrete
    have rawBodyΔwf := bodyContextEq.wf
    have rawBodyInst_tr : TrExprS env Us rawBodyΔ
        (body.instantiate1 context.freshExpr) rawBody := by
      simpa only [AddInductive.Context.freshExpr,
        Expr.instantiate1_eq] using
        rawBody_tr.inst_fvar henv.ordered rawBodyΔwf
    obtain ⟨rawBinders, viewBinders, rawResult, viewResult,
        resultType, rawBodyEq, viewBodyEq, tail, tailLength⟩ :=
      bodyIH bodyAligned bodyContextEq rawBodyInst_tr
    refine ⟨rawDomain :: rawBinders,
      domainView' :: viewBinders, rawResult, viewResult, resultType,
      ?_, ?_, ?_, ?_⟩
    · simp only [VExpr.forallN, rawBodyEq]
    · simp only [VExpr.forallN, viewBodyEq]
    · exact .forallE head (by
        simpa only [rawBodyΔ, VLCtx.toCtx] using tail)
    · simpa only [List.length_cons,
        AddInductive.CandidateExprTrace.spineLength] using
        congrArg Nat.succ tailLength

/-- Extract exact raw/view telescopes and terminal results from a recursive
candidate run whose WHNF traversal preserved the stored Pi spine.

The binder count is computed from the source-indexed trace, and `telN`/
`dropN` name the exact stored raw and reconstructed-view components.  This
avoids recovering binder equality from whole-Pi definitional equality and so
does not use the unfinished forall-injectivity theorem. -/
theorem CandidateExprRun.spineEvidence
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true) :
    ∃ resultType,
      TelResultDefEqEvidence env Us.length Δ.toCtx
        (VExpr.telN trace.spineLength source')
        (VExpr.telN trace.spineLength view')
        (VExpr.dropN trace.spineLength source')
        (VExpr.dropN trace.spineLength view') resultType := by
  have henv : VEnv.WF env := by
    cases run with
    | terminal node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    | forallE _ _ _ _ node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
  obtain ⟨rawBinders, viewBinders, rawResult, viewResult,
      resultType, rawEq, viewEq, evidence, rawLength⟩ :=
    run.spineEvidenceAux aligned
      (.refl henv run.context_wf) run.source_tr
  have viewLength : viewBinders.length = trace.spineLength :=
    evidence.length_eq ▸ rawLength
  have rawTel : VExpr.telN trace.spineLength source' = rawBinders := by
    rw [rawEq, ← rawLength]
    exact candidateTelN_forallN_length rawBinders rawResult
  have viewTel : VExpr.telN trace.spineLength view' = viewBinders := by
    rw [viewEq, ← viewLength]
    exact candidateTelN_forallN_length viewBinders viewResult
  have rawResultEq :
      VExpr.dropN trace.spineLength source' = rawResult := by
    rw [rawEq, ← rawLength]
    exact candidateDropN_forallN_length rawBinders rawResult
  have viewResultEq :
      VExpr.dropN trace.spineLength view' = viewResult := by
    rw [viewEq, ← viewLength]
    exact candidateDropN_forallN_length viewBinders viewResult
  simpa only [rawTel, viewTel, rawResultEq, viewResultEq] using
    ⟨resultType, evidence⟩

/-- Replace only the terminal typing index of a combined certificate. The
telescope and both result endpoints remain definitionally unchanged. -/
theorem TelResultDefEqEvidence.withResult
    (run : TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType)
    (result : DefEqEvidence env U (rawBinders.reverse ++ Γ)
      rawResult viewResult resultType') :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType' := by
  induction run with
  | terminal _ => exact .terminal (by simpa using result)
  | forallE domain tail ih =>
    exact .forallE domain (ih (by
      simpa [List.reverse_cons, List.append_assoc] using result))

/-- Fix a candidate terminal equality at a known type of its right endpoint.
This is the bridge from the candidate's checker-inferred type to the precise
sort required by dependent inductive analysis. -/
theorem TelResultDefEqEvidence.ofRightType
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (run : TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType)
    (rightType : env.HasType U (rawBinders.reverse ++ Γ)
      viewResult expectedType) :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult expectedType := by
  have hctx : OnCtx (rawBinders.reverse ++ Γ) (env.IsType U) :=
    (run.telescope.telDefEq.extendCtx (.refl hΓ)).isType
  exact run.withResult (.ofDefEq
    (run.result.isDefEq.toU.of_r henv hctx rightType))

theorem CandidateExprRun.env_wf
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    VEnv.WF env := by
  cases run with
  | terminal node =>
    simpa only [node.check.venv_eq] using node.check.context.Ewf
  | forallE _ _ _ _ node =>
    simpa only [node.check.venv_eq] using node.check.context.Ewf

/-- Recover the exact verified candidate context reached at the end of the
main Pi spine.

`CandidateExprRun` retains the semantic context at every recursive node, but
its public indices deliberately mention only the translated local context.
Constructor validation, on the other hand, resumes in the implementation
`Context` returned by the family traversal.  This projection reconnects the
two without reconstructing a local context from names: starting from the
root `CandidateContextRun`, each Pi case repeats the already-certified
annotation equality and the exact `pushLocalDecl` used by the candidate. -/
theorem CandidateExprRun.terminalContextRun
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ) :
    ∃ terminalRun : CandidateContextRun trace.terminalContext,
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us := by
  induction run with
  | terminal node =>
      exact ⟨by
          simpa only [AddInductive.CandidateExprTrace.terminalContext] using
            contextRun,
        venv_eq, lparams_eq⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have storedDomain_tr : contextRun.context.TrExprS
        annotations.consumed storedDomain' := by
      simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
        annotationsRun.rhs_tr
    have henv : VEnv.WF env := by
      simpa only [venv_eq] using contextRun.context.Ewf
    have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
      simpa only [venv_eq, lparams_eq, vlctx_eq] using
        contextRun.context.Δwf.toCtx
    have storedDomain_type : env.IsType Us.length Δ.toCtx storedDomain' := by
      have annotationDef := annotationsRun.isDefEqU.of_l henv hΔ domainType
      exact ⟨u, annotationDef.hasType.2⟩
    let nextContextRun := contextRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr (by
        change contextRun.context.venv.IsType
          contextRun.context.lparams.length
          contextRun.context.vlctx.toCtx storedDomain'
        rw [venv_eq, lparams_eq, vlctx_eq]
        exact storedDomain_type)
    have nextVenv : nextContextRun.context.venv = env := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_venv,
        venv_eq]
    have nextLparams : nextContextRun.context.lparams = Us := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_lparams,
        lparams_eq]
    have nextVlctx : nextContextRun.context.vlctx = bodyΔ := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_vlctx]
      rw [vlctx_eq, bodyContext]
    obtain ⟨terminalRun, terminalVenv, terminalLparams⟩ :=
      bodyIH nextContextRun nextVenv nextLparams nextVlctx
    exact ⟨by
        simpa only [AddInductive.CandidateExprTrace.terminalContext] using
          terminalRun,
      terminalVenv, terminalLparams⟩

private theorem candidateFVLift'_comp
    (left : VLCtx.FVLift' Δ₁ Δ₂ 0 (.skipN .refl n₁) 0)
    (right : VLCtx.FVLift' Δ₂ Δ₃ 0 (.skipN .refl n₂) 0) :
    VLCtx.FVLift' Δ₁ Δ₃ 0 (.skipN .refl (n₁ + n₂)) 0 := by
  simpa only [Lift.comp_skipN, Lift.comp, Lift.skipN_skipN] using
    left.comp right

/-- Recover the terminal implementation context together with the exact
candidate-view telescope occupying the same local positions.

The two `VLCtx`s keep the identical free-variable metadata and declaration
kinds.  Their declaration types may differ, but strict translation uniqueness
only needs this positional relation.  The view-side `toCtx` is definitionally
the reversed telescope selected by the recursive semantic run, followed by
the caller's view-side base context. -/
theorem CandidateExprRun.terminalContextRunView
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ)
    {viewΔ : VLCtx}
    (viewDefEq : VLCtx.IsDefEq env Us.length Δ viewΔ)
    (viewContext : TrExprS.IsUniqueCtx Δ viewΔ) :
    ∃ (terminalRun : CandidateContextRun trace.terminalContext)
        (viewTerminal : VLCtx),
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      VLCtx.IsDefEq env Us.length terminalRun.context.vlctx viewTerminal ∧
      TrExprS.IsUniqueCtx terminalRun.context.vlctx viewTerminal ∧
      VLCtx.FVLift' viewΔ viewTerminal 0
        (.skipN .refl trace.spineLength) 0 ∧
      viewTerminal.toCtx =
        (VExpr.telN trace.spineLength view').reverse ++ viewΔ.toCtx := by
  induction run generalizing viewΔ with
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
      let terminalRun : CandidateContextRun
          (AddInductive.CandidateExprTrace.terminal
            context source inferred result checked normalized).terminalContext := by
        simpa only [AddInductive.CandidateExprTrace.terminalContext] using
          contextRun
      refine ⟨terminalRun, viewΔ, venv_eq, lparams_eq, ?_, ?_, .refl, ?_⟩
      · change VLCtx.IsDefEq env Us.length contextRun.context.vlctx viewΔ
        rw [vlctx_eq]
        exact viewDefEq
      · change TrExprS.IsUniqueCtx contextRun.context.vlctx viewΔ
        rw [vlctx_eq]
        exact viewContext
      · simp only [AddInductive.CandidateExprTrace.spineLength,
          VExpr.telN, List.reverse_nil, List.nil_append]
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have storedDomain_tr : contextRun.context.TrExprS
        annotations.consumed storedDomain' := by
      simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
        annotationsRun.rhs_tr
    have henv : VEnv.WF env := by
      simpa only [venv_eq] using contextRun.context.Ewf
    have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
      simpa only [venv_eq, lparams_eq, vlctx_eq] using
        contextRun.context.Δwf.toCtx
    have storedDomain_type : env.IsType Us.length Δ.toCtx storedDomain' := by
      have annotationDef := annotationsRun.isDefEqU.of_l henv hΔ domainType
      exact ⟨u, annotationDef.hasType.2⟩
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      domainRun.evidence.isDefEq.toU.of_l henv hΔ domainType
    have annotationDef : env.IsDefEq Us.length Δ.toCtx
        domain' storedDomain' (.sort u) :=
      annotationsRun.isDefEqU.of_l henv hΔ domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    let nextContextRun := contextRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr (by
        change contextRun.context.venv.IsType
          contextRun.context.lparams.length
          contextRun.context.vlctx.toCtx storedDomain'
        rw [venv_eq, lparams_eq, vlctx_eq]
        exact storedDomain_type)
    have nextVenv : nextContextRun.context.venv = env := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_venv,
        venv_eq]
    have nextLparams : nextContextRun.context.lparams = Us := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_lparams,
        lparams_eq]
    have nextVlctx : nextContextRun.context.vlctx = bodyΔ := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_vlctx]
      rw [vlctx_eq, bodyContext]
    let viewBodyΔ : VLCtx :=
      (some (context.freshFVarId, annotations.consumed.fvarsList),
        .vlam domainView') :: viewΔ
    have bodyWF := bodyRun.context_wf
    rw [bodyContext] at bodyWF
    have bodyViewDefEq : VLCtx.IsDefEq env Us.length bodyΔ viewBodyΔ := by
      rw [bodyContext]
      exact .cons viewDefEq bodyWF.2.1 (.vlam storedToView)
    have bodyViewContext : TrExprS.IsUniqueCtx bodyΔ viewBodyΔ := by
      rw [bodyContext]
      exact viewContext.cons .vlam
    obtain ⟨terminalRun, viewTerminal, terminalVenv, terminalLparams,
        terminalViewDefEq, terminalViewContext, terminalViewLift,
        terminalViewEq⟩ :=
      bodyIH nextContextRun nextVenv nextLparams nextVlctx bodyViewDefEq
        bodyViewContext
    refine ⟨by
        simpa only [AddInductive.CandidateExprTrace.terminalContext] using
          terminalRun,
      viewTerminal, terminalVenv, terminalLparams, terminalViewDefEq,
      terminalViewContext, ?_, ?_⟩
    · have headLift : VLCtx.FVLift' viewΔ viewBodyΔ 0
          (.skipN .refl 1) 0 := by
        exact VLCtx.FVLift'.skip_fvar
          (context.freshFVarId, annotations.consumed.fvarsList)
          (.vlam domainView') (.refl :
            VLCtx.FVLift' viewΔ viewΔ 0 .refl 0)
      simpa only [AddInductive.CandidateExprTrace.spineLength,
        Nat.add_comm 1] using
        candidateFVLift'_comp headLift terminalViewLift
    simpa only [AddInductive.CandidateExprTrace.spineLength,
      VExpr.telN, List.reverse_cons, List.singleton_append,
      List.append_assoc, viewBodyΔ, VLCtx.toCtx] using terminalViewEq

/-- Interpret the terminal-sort fact retained by family validation.

At a terminal node the verified WHNF result translates the exact kernel sort.
At a Pi node the recursively interpreted body is transported from the
annotation-consumed binder context to the candidate-view binder context. Thus
the complete checker-selected candidate view is a Theory type without using a
checked inductive declaration or a caller-supplied view-WF proof. -/
theorem CandidateExprRun.view_isType_of_terminalSort
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (terminal : trace.terminalResult = .sort resultLevel) :
    env.IsType Us.length Δ.toCtx view' := by
  induction run with
  | terminal node =>
    simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
    rw [terminal] at node
    cases node.whnf.rhs_tr with
    | sort level_tr =>
      exact ⟨_, .sort (VLevel.WF.of_ofLevel level_tr)⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      domainRun.evidence.isDefEq.toU.of_l henv hΔ.toCtx domainType
    have domainViewType : env.IsType Us.length Δ.toCtx domainView' :=
      ⟨u, domainDef.hasType.2⟩
    have annotationDef : env.IsDefEq Us.length Δ.toCtx
        domain' storedDomain' (.sort u) :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    have bodyContextEq : env.IsDefEqCtx Us.length []
        (storedDomain' :: Δ.toCtx) (domainView' :: Δ.toCtx) :=
      (VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none)
        (by nofun) (.vlam storedToView)).defeqCtx
    have bodyViewTypeStored : env.IsType Us.length
        (storedDomain' :: Δ.toCtx) bodyView' := by
      simpa only [bodyContext, VLCtx.toCtx] using bodyIH terminal
    have bodyViewType : env.IsType Us.length
        (domainView' :: Δ.toCtx) bodyView' := by
      exact bodyViewTypeStored.defeqDFC henv.ordered bodyContextEq
    exact domainViewType.forallE bodyViewType

/-- Family validation types the checker-selected view first; the retained
candidate equality then transports that fact back to the exact raw Theory
source. This is the declaration-WF fact needed before raw-family insertion. -/
theorem CandidateExprSemanticRootRun.source_isType_of_terminalSort
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (terminal : candidate.trace.terminalResult = .sort resultLevel) :
    env.IsType Us.length [] source' := by
  obtain ⟨_, recursive⟩ := run.recursive
  have hview := recursive.view_isType_of_terminalSort terminal
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.contextRun.context.Ewf
  exact hview.defeqU_l henv trivial recursive.evidence.isDefEq.toU.symm

/-- Candidate-view parameter binders selected by an exact singleton family
validation run. The split is computed from the retained candidate spine. -/
def CandidateExprSemanticRootRun.viewParameters
    {indType : InductiveType}
    {candidate : AddInductive.CandidateExpr indType.type}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (validation : AddInductive.CandidateExprTrace.FamilyValidationRun
      indType candidate.trace) : List VExpr :=
  (VExpr.telN candidate.trace.spineLength run.view).take
    validation.nparams

/-- Candidate-view index binders following the validator-selected parameter
prefix. -/
def CandidateExprSemanticRootRun.viewIndices
    {indType : InductiveType}
    {candidate : AddInductive.CandidateExpr indType.type}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (validation : AddInductive.CandidateExprTrace.FamilyValidationRun
      indType candidate.trace) : List VExpr :=
  (VExpr.telN candidate.trace.spineLength run.view).drop
    validation.nparams

/-- An exact recursive run whose executable main spine preserves the stored
binders. Unlike a whole-expression root equality, this package is strong
enough to expose generation's pointwise binder and terminal-result evidence. -/
def CandidateExprSpineRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (raw view : VExpr) : Prop :=
  candidate.trace.storedSpine = true ∧
    ∃ inferred, CandidateExprRun env Us candidate.trace [] raw view inferred

/-- Retaining the recursive semantic root makes the generation spine a direct
projection once the executable structural gate has succeeded. -/
theorem CandidateExprSemanticRootRun.spine
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (storedSpine : candidate.trace.storedSpine = true) :
    CandidateExprSpineRun env Us candidate source' run.view :=
  ⟨storedSpine, run.recursive⟩

/-- Turn an exact root translation and a recursive identity witness into the
generation-ready spine package. The root equalities transport the recursive
run out of the verifier's reconstructed context without choosing a different
semantic endpoint. -/
theorem CandidateExprRootRun.spineOfIdentity
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprRootRun env Us candidate source' source')
    (identity : CandidateExprIdentity candidate.trace) :
    CandidateExprSpineRun env Us candidate source' source' := by
  refine ⟨identity.storedSpine, ?_⟩
  have source_tr : run.contextRun.context.TrExprS source source' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.source_tr
  obtain ⟨inferred', ⟨recursive⟩⟩ :=
    CandidateExprRun.exists_ofIdentity candidate.trace identity
      run.contextRun source' source_tr run.whnfFuel run.whnfDepth
  refine ⟨inferred', ?_⟩
  simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using recursive

/-- Retain the exact recursive run selected by an identity-normalizing root.

All data fields are inherited from the named root and its fixed Theory
endpoint. The existential inferred type remains proof-only, so this constructor
does not use classical choice and does not turn identity into an executable or
semantic oracle. -/
def CandidateExprRootRun.semanticOfIdentity
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprRootRun env Us candidate source' source')
    (identity : CandidateExprIdentity candidate.trace) :
    CandidateExprSemanticRootRun env Us candidate source' where
  contextRun := run.contextRun
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq
  vlctx_eq := run.vlctx_eq
  source_tr := run.source_tr
  whnfFuel := run.whnfFuel
  whnfDepth := run.whnfDepth
  view := source'
  recursive := by
    have source_tr : run.contextRun.context.TrExprS source source' := by
      simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
        run.vlctx_eq] using run.source_tr
    obtain ⟨inferred, ⟨recursive⟩⟩ :=
      CandidateExprRun.exists_ofIdentity candidate.trace identity
        run.contextRun source' source_tr run.whnfFuel run.whnfDepth
    refine ⟨inferred, ?_⟩
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using recursive

theorem CandidateExprSpineRun.evidence
    (run : CandidateExprSpineRun env Us candidate raw view) :
    ∃ resultType,
      TelResultDefEqEvidence env Us.length []
        (VExpr.telN candidate.trace.spineLength raw)
        (VExpr.telN candidate.trace.spineLength view)
        (VExpr.dropN candidate.trace.spineLength raw)
        (VExpr.dropN candidate.trace.spineLength view) resultType := by
  obtain ⟨aligned, _, recursive⟩ := run
  exact recursive.spineEvidence aligned

/-- Align extracted candidate components with named raw/view telescope and
result data, then fix the terminal type from a checked right-endpoint typing
judgment. All four alignment premises are syntactic equations. -/
theorem CandidateExprSpineRun.evidenceAt
    (run : CandidateExprSpineRun env Us candidate raw view)
    (rawTel : VExpr.telN candidate.trace.spineLength raw = rawBinders)
    (viewTel : VExpr.telN candidate.trace.spineLength view = viewBinders)
    (rawResult_eq :
      VExpr.dropN candidate.trace.spineLength raw = rawResult)
    (viewResult_eq :
      VExpr.dropN candidate.trace.spineLength view = viewResult)
    (rightType : env.HasType Us.length rawBinders.reverse
      viewResult expectedType) :
    TelResultDefEqEvidence env Us.length [] rawBinders viewBinders
      rawResult viewResult expectedType := by
  obtain ⟨aligned, _, recursive⟩ := run
  obtain ⟨resultType, evidence⟩ := recursive.spineEvidence aligned
  have exactEvidence : TelResultDefEqEvidence env Us.length []
      rawBinders viewBinders rawResult viewResult resultType := by
    simpa only [rawTel, viewTel, rawResult_eq, viewResult_eq,
      VLCtx.toCtx] using evidence
  exact exactEvidence.ofRightType recursive.env_wf trivial (by
    simpa using rightType)

end TypeChecker

namespace VInductDecl

/-- A one-family normalization candidate validated by compositional verified
normalization evidence at the kernel's two declaration stages.

The family comparison runs in `env`. Constructor comparisons run in the exact
`typeEnv` obtained by inserting the raw family constant. The positional
`Forall₂` prevents a shorter checker-result list from certifying a declaration.
-/
structure NormalizationRun {source : VInductDecl}
    (norm : Normalization source) (env : VEnv) where
  raw : VInductiveType
  view : VInductiveType
  source_types_eq : source.types = [raw]
  view_types_eq : norm.view.types = [view]
  family : ∃ A,
    TypeChecker.DefEqEvidence env source.uvars []
      raw.type view.type A
  typeEnv : VEnv
  addType :
    env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : List.Forall₂
    (fun rawCtor viewCtor =>
      ∃ A, TypeChecker.DefEqEvidence typeEnv source.uvars []
        rawCtor.type viewCtor.type A)
    raw.ctors view.ctors

/-- Checker-validated family and constructor comparisons establish the
semantic part of the raw/view normalization boundary. -/
theorem NormalizationRun.wf
    (run : NormalizationRun norm env) : norm.WF env := by
  refine ⟨run.raw, run.view, run.source_types_eq, run.view_types_eq, ?_, ?_⟩
  · obtain ⟨_, hfamily⟩ := run.family
    exact hfamily.isDefEq.toU
  · intro envT hadd
    have henv : envT = run.typeEnv := by
      have : some envT = some run.typeEnv := hadd.symm.trans run.addType
      exact Option.some.inj this
    subst envT
    exact Ix.Theory.Named.List.Forall₂.imp (h := run.constructors) fun _ _ h => by
      obtain ⟨_, hctor⟩ := h
      exact hctor.isDefEq.toU

/-- Checker-validated normalization for an arbitrary mutual block.

Family equalities are interpreted in the common pre-family environment.  The
raw family constants are then staged as one exact source-ordered fold, and
all constructor equalities are interpreted in the resulting shared block
environment. -/
structure NormalizationBlockRun {source : VInductDecl}
    (norm : Normalization source) (env blockEnv : VEnv) where
  stage : env.stageInductiveTypes source.types = some blockEnv
  families : List.Forall₂
    (fun raw view =>
      (∃ A, TypeChecker.DefEqEvidence env source.uvars []
        raw.type view.type A) ∧
      List.Forall₂
        (fun rawCtor viewCtor =>
          ∃ A, TypeChecker.DefEqEvidence blockEnv source.uvars []
            rawCtor.type viewCtor.type A)
        raw.ctors view.ctors)
    source.types norm.view.types

/-- The verified checker interpretation discharges the complete Theory
mutual-normalization contract without a singleton projection. -/
theorem NormalizationBlockRun.wf
    (run : NormalizationBlockRun norm env blockEnv) :
    norm.BlockWF env blockEnv := by
  refine ⟨run.stage, ?_⟩
  exact Ix.Theory.Named.List.Forall₂.imp (h := run.families) fun _ _ h => by
    refine ⟨h.1.choose_spec.isDefEq.toU, ?_⟩
    exact Ix.Theory.Named.List.Forall₂.imp (h := h.2) fun _ _ hctor =>
      hctor.choose_spec.isDefEq.toU

/-- One constructor candidate tied to the corresponding raw Theory constant.
Its expression payload may normalize, but its name, universe arity, and exact
source position remain fixed. -/
structure CandidateConstructorRun (env : VEnv) (Us : List Name)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  viewType : VExpr
  typeRun : TypeChecker.CandidateExprRootRun env Us candidate.type
    raw.type viewType

/-- Replace only the expression payload certified by the constructor run. -/
def CandidateConstructorRun.view
    (run : CandidateConstructorRun env Us candidate raw) : VConstVal :=
  { raw with type := run.viewType }

/-- Exact positional certification for a source-indexed constructor list and
the raw Theory constructor list. Unlike `zip`, this type cannot truncate a
longer side or reuse evidence at a different source position. -/
inductive CandidateConstructorListRun (env : VEnv) (Us : List Name) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorListRun env Us .nil []
  | cons
      (head : CandidateConstructorRun env Us candidate raw)
      (tail : CandidateConstructorListRun env Us candidates raws) :
      CandidateConstructorListRun env Us
        (.cons candidate candidates) (raw :: raws)

/-- The exact normalized constructor list retained by a positional run. -/
def CandidateConstructorListRun.views :
    CandidateConstructorListRun env Us candidates raws → List VConstVal
  | .nil => []
  | .cons head tail => head.view :: tail.views

/-- Positional certification preserves every constructor header. -/
theorem CandidateConstructorListRun.sameHeaders
    (run : CandidateConstructorListRun env Us candidates raws) :
    sameCtorHeaders raws run.views = true := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    simp [CandidateConstructorListRun.views,
      CandidateConstructorRun.view, sameCtorHeaders, ih]

/-- Collect the exact checker-produced equality for every positional raw/view
constructor pair. -/
theorem CandidateConstructorListRun.evidence
    (run : CandidateConstructorListRun env Us candidates raws) :
    List.Forall₂
      (fun raw view => ∃ A,
        TypeChecker.DefEqEvidence env Us.length []
          raw.type view.type A)
      raws run.views := by
  induction run with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons head.typeRun.evidence ih

/-- One family candidate certified in the input environment, together with
all of its constructors certified in the exact environment obtained by
inserting the raw family constant. -/
structure CandidateFamilyRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  viewType : VExpr
  typeRun : TypeChecker.CandidateExprRootRun env Us
    candidate.familyType.type raw.type viewType
  typeEnv : VEnv
  addType : env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : CandidateConstructorListRun typeEnv Us
    candidate.constructors raw.ctors

/-- Replace only the family and constructor expression payloads named by the
certified candidate runs. -/
def CandidateFamilyRun.view
    (run : CandidateFamilyRun env Us candidate raw) : VInductiveType :=
  { raw with
    type := run.viewType
    ctors := run.constructors.views }

/-- Exact singleton candidate-list certification against one raw Theory
declaration. The singleton kernel-source index rules out partial selection of
a family candidate, and `raw_types_eq` rules out partial selection of a Theory
family. Mutual blocks remain an explicit later generalization. -/
structure NormalizationCandidateRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  uvars_eq : rawDecl.uvars = Us.length
  family : CandidateFamilyRun env Us candidate.families.singleton raw

/-- The Theory declaration obtained from the exact singleton candidate. -/
def NormalizationCandidateRun.viewDecl
    (run : NormalizationCandidateRun env Us candidate rawDecl) :
    VInductDecl :=
  { rawDecl with types := [run.family.view] }

/-- Candidate-list shape evidence is sufficient to construct the Theory
normalization boundary without `head!`, unchecked `zip`, or an arbitrary view
declaration supplied separately from the candidate. -/
def NormalizationCandidateRun.normalization
    (run : NormalizationCandidateRun env Us candidate rawDecl) :
    Normalization rawDecl where
  view := run.viewDecl
  shape_eq := by
    simp only [normalizationShape, NormalizationCandidateRun.viewDecl,
      run.raw_types_eq, beq_self_eq_true, Bool.true_and, sameTypeHeaders,
      CandidateFamilyRun.view]
    simp [run.family.constructors.sameHeaders]

/-- Assemble the existing semantic normalization certificate from the exact
family and constructor candidate runs. -/
def NormalizationCandidateRun.normalizationRun
    (run : NormalizationCandidateRun env Us candidate rawDecl) :
    NormalizationRun run.normalization env where
  raw := run.raw
  view := run.family.view
  source_types_eq := run.raw_types_eq
  view_types_eq := rfl
  family := by
    simpa only [run.uvars_eq, CandidateFamilyRun.view] using
      run.family.typeRun.evidence
  typeEnv := run.family.typeEnv
  addType := run.family.addType
  constructors := by
    simpa only [run.uvars_eq, CandidateFamilyRun.view] using
      run.family.constructors.evidence

/-- One constructor whose exact recursive candidate semantics are retained,
rather than reconstructed separately for normalization and generation.

The header remains indexed by the kernel source and raw Theory constant. The
semantic root owns the checker-selected view, its inferred type, and the
recursive run used by both downstream phases. -/
structure CandidateConstructorSemanticRun (env : VEnv) (Us : List Name)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootRun env Us candidate.type
    raw.type

/-- Project the normalization-facing constructor root without losing its
source or position indices. -/
def CandidateConstructorSemanticRun.root
    (run : CandidateConstructorSemanticRun env Us candidate raw) :
    CandidateConstructorRun env Us candidate raw where
  name_eq := run.name_eq
  uvars_eq := run.uvars_eq
  viewType := run.type.view
  typeRun := run.type.root

/-- Exact positional semantic ownership for an arbitrary constructor list.
Every element retains the recursive run selected at that source position; the
list cannot truncate, reorder, or reuse a run for another constructor. -/
inductive CandidateConstructorSemanticListRun
    (env : VEnv) (Us : List Name) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorSemanticListRun env Us .nil []
  | cons
      (head : CandidateConstructorSemanticRun env Us candidate raw)
      (tail : CandidateConstructorSemanticListRun env Us candidates raws) :
      CandidateConstructorSemanticListRun env Us
        (.cons candidate candidates) (raw :: raws)

/-- Forget only the retained recursive-run payload and recover the existing
normalization-facing positional list. -/
def CandidateConstructorSemanticListRun.roots :
    CandidateConstructorSemanticListRun env Us candidates raws →
      CandidateConstructorListRun env Us candidates raws
  | .nil => .nil
  | .cons head tail => .cons head.root tail.roots

/-- One family in a mutual normalization candidate.  Its type is interpreted
in the common pre-family environment, while every constructor is interpreted
in the single environment obtained after staging the complete raw family
block. -/
structure CandidateBlockFamilySemanticRun
    (env blockEnv : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootRun env Us
    candidate.familyType.type raw.type
  constructors : CandidateConstructorSemanticListRun blockEnv Us
    candidate.constructors raw.ctors

/-- Replace only the expression payloads selected by the retained checker
runs; all family and constructor headers remain raw and source-indexed. -/
def CandidateBlockFamilySemanticRun.view
    (run : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw) :
    VInductiveType :=
  { raw with
    type := run.type.view
    ctors := run.constructors.roots.views }

/-- Exact source-order semantic ownership for every family in an arbitrary
block.  Both the kernel candidate list and raw Theory list are indices, so
family reordering and truncation are unrepresentable. -/
inductive CandidateBlockFamilySemanticListRun
    (env blockEnv : VEnv) (Us : List Name) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      List VInductiveType → Type where
  | nil : CandidateBlockFamilySemanticListRun env blockEnv Us .nil []
  | cons
      (head : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
      (tail : CandidateBlockFamilySemanticListRun env blockEnv Us
        candidates raws) :
      CandidateBlockFamilySemanticListRun env blockEnv Us
        (.cons candidate candidates) (raw :: raws)

/-- Exact normalized family views in source order. -/
def CandidateBlockFamilySemanticListRun.views :
    CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws →
      List VInductiveType
  | .nil => []
  | .cons head tail => head.view :: tail.views

/-- Block semantic runs preserve every family and constructor header. -/
theorem CandidateBlockFamilySemanticListRun.sameHeaders
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    sameTypeHeaders raws run.views = true := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    simp [CandidateBlockFamilySemanticListRun.views,
      CandidateBlockFamilySemanticRun.view, sameTypeHeaders,
      head.constructors.roots.sameHeaders, ih]

/-- Collect the exact family/constructor definitional equalities selected by
the retained semantic checker hierarchy. -/
theorem CandidateBlockFamilySemanticListRun.evidence
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    List.Forall₂
      (fun raw view =>
        (∃ A, TypeChecker.DefEqEvidence env Us.length []
          raw.type view.type A) ∧
        List.Forall₂
          (fun rawCtor viewCtor =>
            ∃ A, TypeChecker.DefEqEvidence blockEnv Us.length []
              rawCtor.type viewCtor.type A)
          raw.ctors view.ctors)
      raws run.views := by
  induction run with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons
      ⟨head.type.root.evidence, head.constructors.roots.evidence⟩ ih

/-- Complete semantic ownership for an arbitrary normalization candidate.
The raw staging equation and dependent family list share the same exact raw
declaration; no independently supplied normalized declaration is accepted. -/
structure NormalizationCandidateBlockSemanticRun
    (env blockEnv : VEnv) (Us : List Name)
    {sources : List InductiveType}
    (candidate : AddInductive.NormalizationCandidate sources)
    (rawDecl : VInductDecl) where
  uvars_eq : rawDecl.uvars = Us.length
  stage : env.stageInductiveTypes rawDecl.types = some blockEnv
  families : CandidateBlockFamilySemanticListRun env blockEnv Us
    candidate.families rawDecl.types

/-- Theory declaration selected by the exact block semantic hierarchy. -/
def NormalizationCandidateBlockSemanticRun.viewDecl
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) : VInductDecl :=
  { rawDecl with types := run.families.views }

/-- Construct the header-preserving Theory normalization boundary selected by
the candidate semantic hierarchy. -/
def NormalizationCandidateBlockSemanticRun.normalization
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) : Normalization rawDecl where
  view := run.viewDecl
  shape_eq := by
    simp only [normalizationShape,
      NormalizationCandidateBlockSemanticRun.viewDecl,
      beq_self_eq_true, Bool.true_and]
    exact run.families.sameHeaders

/-- Project the generic verified normalization run for the same raw block and
shared staged environment. -/
theorem NormalizationCandidateBlockSemanticRun.normalizationRun
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) :
    NormalizationBlockRun run.normalization env blockEnv where
  stage := run.stage
  families := by
    simpa only [run.uvars_eq,
      NormalizationCandidateBlockSemanticRun.normalization,
      NormalizationCandidateBlockSemanticRun.viewDecl] using
      run.families.evidence

/-- A singleton-family semantic hierarchy spanning the pre-family candidate,
the exact raw-family insertion, and every post-family constructor candidate.
The normalized expression payloads are selected by retained recursive checker
runs, not by a parallel caller-supplied declaration. -/
structure CandidateFamilySemanticRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootRun env Us
    candidate.familyType.type raw.type
  typeEnv : VEnv
  addType : env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : CandidateConstructorSemanticListRun typeEnv Us
    candidate.constructors raw.ctors

/-- Project the existing normalization-facing family run from the retained
semantic hierarchy. -/
def CandidateFamilySemanticRun.root
    (run : CandidateFamilySemanticRun env Us candidate raw) :
    CandidateFamilyRun env Us candidate raw where
  name_eq := run.name_eq
  uvars_eq := run.uvars_eq
  viewType := run.type.view
  typeRun := run.type.root
  typeEnv := run.typeEnv
  addType := run.addType
  constructors := run.constructors.roots

/-- Complete retained semantic ownership for one source-indexed singleton
normalization candidate. This is the generic bridge from translated family and
constructor candidates to `NormalizationCandidateRun`; mutual blocks remain a
later indexed generalization. -/
structure NormalizationCandidateSemanticRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  uvars_eq : rawDecl.uvars = Us.length
  family : CandidateFamilySemanticRun env Us candidate.families.singleton raw

/-- Recover the existing normalization candidate from the retained semantic
hierarchy. -/
def NormalizationCandidateSemanticRun.root
    (run : NormalizationCandidateSemanticRun env Us candidate rawDecl) :
    NormalizationCandidateRun env Us candidate rawDecl where
  raw := run.raw
  raw_types_eq := run.raw_types_eq
  uvars_eq := run.uvars_eq
  family := run.family.root

/-- Pre-run semantic evidence for one source-indexed constructor.  Its header
is aligned with the raw Theory constant, while the expression input contains
only the verified context and strict source translation needed to let the
retained checker choose the view. -/
structure CandidateConstructorSemanticInput (env : VEnv) (Us : List Name)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootInput env Us candidate.type
    raw.type

/-- Interpret one constructor input without selecting its view at the call
site. -/
theorem CandidateConstructorSemanticInput.exists
    (input : CandidateConstructorSemanticInput env Us candidate raw) :
    Nonempty (CandidateConstructorSemanticRun env Us candidate raw) := by
  obtain ⟨type⟩ := input.type.exists
  exact ⟨{
    name_eq := input.name_eq
    uvars_eq := input.uvars_eq
    type := type }⟩

/-- Exact source-order semantic inputs for an arbitrary constructor list.
Unlike a pointwise predicate over erased lists, these indices prevent an input
from being reused at another constructor or from silently truncating either
side. -/
inductive CandidateConstructorSemanticListInput
    (env : VEnv) (Us : List Name) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorSemanticListInput env Us .nil []
  | cons
      (head : CandidateConstructorSemanticInput env Us candidate raw)
      (tail : CandidateConstructorSemanticListInput env Us candidates raws) :
      CandidateConstructorSemanticListInput env Us
        (.cons candidate candidates) (raw :: raws)

/-- Recursively interpret every source-indexed constructor input. -/
theorem CandidateConstructorSemanticListInput.exists
    (input : CandidateConstructorSemanticListInput env Us candidates raws) :
    Nonempty (CandidateConstructorSemanticListRun env Us candidates raws) := by
  induction input with
  | nil => exact ⟨.nil⟩
  | cons head tail ih =>
    obtain ⟨headRun⟩ := head.exists
    obtain ⟨tailRun⟩ := ih
    exact ⟨.cons headRun tailRun⟩

/-- Pre-run semantic evidence for one family in a shared mutual stage.
Family types use `env`; all constructor types use the same `blockEnv` after
every raw family has been staged. -/
structure CandidateBlockFamilySemanticInput
    (env blockEnv : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootInput env Us
    candidate.familyType.type raw.type
  constructors : CandidateConstructorSemanticListInput blockEnv Us
    candidate.constructors raw.ctors

/-- Interpret one family and its complete constructor list without selecting
a normalized expression at the call site. -/
theorem CandidateBlockFamilySemanticInput.exists
    (input : CandidateBlockFamilySemanticInput env blockEnv Us
      candidate raw) :
    Nonempty (CandidateBlockFamilySemanticRun env blockEnv Us
      candidate raw) := by
  obtain ⟨type⟩ := input.type.exists
  obtain ⟨constructors⟩ := input.constructors.exists
  exact ⟨{
    name_eq := input.name_eq
    uvars_eq := input.uvars_eq
    type
    constructors }⟩

/-- Exact source-order semantic inputs for every family in a mutual block. -/
inductive CandidateBlockFamilySemanticListInput
    (env blockEnv : VEnv) (Us : List Name) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      List VInductiveType → Type where
  | nil : CandidateBlockFamilySemanticListInput env blockEnv Us .nil []
  | cons
      (head : CandidateBlockFamilySemanticInput env blockEnv Us candidate raw)
      (tail : CandidateBlockFamilySemanticListInput env blockEnv Us
        candidates raws) :
      CandidateBlockFamilySemanticListInput env blockEnv Us
        (.cons candidate candidates) (raw :: raws)

/-- Interpret every family and constructor input in lockstep. -/
theorem CandidateBlockFamilySemanticListInput.exists
    (input : CandidateBlockFamilySemanticListInput env blockEnv Us
      candidates raws) :
    Nonempty (CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) := by
  induction input with
  | nil => exact ⟨.nil⟩
  | cons head tail ih =>
    obtain ⟨headRun⟩ := head.exists
    obtain ⟨tailRun⟩ := ih
    exact ⟨.cons headRun tailRun⟩

/-- Complete verified semantic input for an arbitrary normalization
candidate.  The exact raw family list owns both the all-family staging fold and
the dependent family interpretation, ruling out a reordered staging witness. -/
structure NormalizationCandidateBlockSemanticInput
    (env blockEnv : VEnv) (Us : List Name)
    {sources : List InductiveType}
    (candidate : AddInductive.NormalizationCandidate sources)
    (rawDecl : VInductDecl) where
  uvars_eq : rawDecl.uvars = Us.length
  stage : env.stageInductiveTypes rawDecl.types = some blockEnv
  families : CandidateBlockFamilySemanticListInput env blockEnv Us
    candidate.families rawDecl.types

/-- Automatically interpret the complete mutual semantic hierarchy. -/
theorem NormalizationCandidateBlockSemanticInput.exists
    (input : NormalizationCandidateBlockSemanticInput env blockEnv Us
      candidate rawDecl) :
    Nonempty (NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) := by
  obtain ⟨families⟩ := input.families.exists
  exact ⟨{
    uvars_eq := input.uvars_eq
    stage := input.stage
    families }⟩

/-- A mutual semantic hierarchy paired with the exact arbitrary-length
producer traversals that selected the same dependent candidate. -/
structure ProducedNormalizationCandidateBlockSemanticRun
    (familyContext constructorContext : AddInductive.Context)
    (env blockEnv : VEnv) (Us : List Name)
    {sources : List InductiveType}
    (candidate : AddInductive.NormalizationCandidate sources)
    (rawDecl : VInductDecl) where
  semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
    candidate rawDecl
  familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
    familyContext candidate.families.familyTypes
  familiesProduced : AddInductive.CandidateFamilyListProduced
    constructorContext candidate.families.familyTypes candidate.families

/-- Combine verified semantic inputs with exact producer provenance for the
same source-indexed mutual candidate. -/
theorem NormalizationCandidateBlockSemanticInput.exists_ofProduced
    (input : NormalizationCandidateBlockSemanticInput env blockEnv Us
      candidate rawDecl)
    (familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
      familyContext candidate.families.familyTypes)
    (familiesProduced : AddInductive.CandidateFamilyListProduced
      constructorContext candidate.families.familyTypes candidate.families) :
    Nonempty (ProducedNormalizationCandidateBlockSemanticRun
      familyContext constructorContext env blockEnv Us candidate rawDecl) := by
  obtain ⟨semantic⟩ := input.exists
  exact ⟨{
    semantic
    familyTypesProduced
    familiesProduced }⟩

/-- One validated singleton family stage derived from a verified entry
candidate context and the exact kernel/Theory family insertion.

The family validator selects the parameter/index split and terminal sort. The
retained candidate semantics then prove the raw family constant well formed;
that proof extends the entry `TrEnv` and constructs the post-family verifier
context. No independently verified post-family `VEnvs` is an input. -/
structure CandidateFamilyStagedInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamilyType source)
    (raw : VInductiveType)
    (preFamily : TypeChecker.CandidateSemanticStage familyContext env Us)
    where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprStagedInput preFamily
    candidate.type raw.type
  validation : AddInductive.CandidateExprTrace.FamilyValidationRun
    source candidate.type.trace
  typeEnv : VEnv
  addInduct : AddInductConstant .induct familyContext.env.constants env
    raw.toVConstVal constructorContext.env.constants typeEnv
  /-- The staged family environment has not yet completed a new projection
  artifact; any already-complete host structure remains backed by a registered
  Theory view. -/
  projectionReady : ProjectionReady constructorContext.env typeEnv
  structureEtaReady : StructureEtaReady constructorContext.env typeEnv
  family_lctx_eq : familyContext.lctx = {}
  constructorContext_eq : constructorContext =
    { familyContext with env := constructorContext.env }
  quotInit_eq : constructorContext.env.quotInit =
    familyContext.env.quotInit
  name_not_reflected : raw.name ∉ VEnv.reflectedPrimitiveNames
  name_not_primitive :
    Environment.primitives.contains raw.name = false

/-- Family validation plus retained candidate semantics prove the exact raw
Theory constant suitable for insertion. The semantic view remains hidden
under `Nonempty`; elimination is only into this proposition. -/
theorem CandidateFamilyStagedInput.rawWF
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) :
    raw.toVConstant.WF env := by
  obtain ⟨semantic⟩ := input.type.rootInput.exists
  show env.IsType raw.uvars [] raw.type
  simpa only [input.uvars_eq] using
    semantic.source_isType_of_terminalSort input.validation.terminal_eq

/-- The verifier context after inserting the validated raw family constant.
Primitive reflection and safety are preserved because the new family name is
not a kernel or reflected primitive. -/
def CandidateFamilyStagedInput.postContext
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) : TypeChecker.VContext where
  env := constructorContext.env
  lctx := constructorContext.lctx
  lparams := constructorContext.lparams
  safety := constructorContext.safety
  fuel := constructorContext.fuel
  venv := input.typeEnv
  hasPrimitives := by
    have H : env.HasPrimitives := by
      simpa only [preFamily.venv_eq] using
        preFamily.contextRun.context.hasPrimitives
    exact VEnv.HasPrimitives.addConst H
      input.name_not_reflected input.addInduct.env_add
  safePrimitives := by
    intro n ci
    have preMapWF : familyContext.env.constants.WF := by
      simpa only [preFamily.contextRun.context_env] using
        preFamily.contextRun.context.trenv.map_wf
    exact TypeChecker.AddInductConstant.safePrimitives input.addInduct
      (n := n) (ci := ci) preMapWF (fun hfind hprim => by
        apply preFamily.contextRun.context.safePrimitives
        · simpa only [preFamily.contextRun.context_env] using hfind
        · exact hprim)
      input.name_not_primitive
  trenv := by
    have preTr : TrEnv' familyContext.safety familyContext.env.constants
        familyContext.env.quotInit env := by
      simpa only [TrEnv, preFamily.contextRun.context_safety,
        preFamily.contextRun.context_env, preFamily.venv_eq] using
        preFamily.contextRun.context.trenv
    have postTr := TrEnv'.inductStaging input.addInduct input.rawWF preTr
    change TrEnv' constructorContext.safety constructorContext.env.constants
      constructorContext.env.quotInit input.typeEnv
    rw [show constructorContext.safety = familyContext.safety by
      rw [input.constructorContext_eq]]
    rw [input.quotInit_eq]
    exact postTr
  projectionReady := input.projectionReady
  structureEtaReady := input.structureEtaReady
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := by
    change ({} : LocalContext) = constructorContext.lctx
    rw [input.constructorContext_eq, input.family_lctx_eq]

/-- The exact post-family candidate context constructed from family
validation, rather than supplied by a second verifier setup. -/
def CandidateFamilyStagedInput.postContextRun
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) :
    TypeChecker.CandidateContextRun constructorContext :=
  TypeChecker.CandidateContextRun.ofVContext constructorContext
    input.postContext (by rfl)
    (TypeChecker.VState.WF.empty_of_reserves input.postContext (by
      intro fv hfv
      change fv ∈ VLCtx.fvars ([] : VLCtx) at hfv
      simp at hfv))
    (by
      rw [input.constructorContext_eq]
      exact preFamily.contextRun.namePrefix_ne)

/-- Shared post-family semantic stage consumed by every constructor position.
Its implementation and Theory environments are fixed by the exact family
insertion above. -/
def CandidateFamilyStagedInput.postFamily
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) :
    TypeChecker.CandidateSemanticStage constructorContext input.typeEnv Us where
  contextRun := input.postContextRun
  venv_eq := rfl
  lparams_eq := by
    rw [TypeChecker.CandidateContextRun.context_lparams]
    calc
      constructorContext.lparams = familyContext.lparams := by
        rw [input.constructorContext_eq]
      _ = preFamily.contextRun.context.lparams :=
        preFamily.contextRun.context_lparams.symm
      _ = Us := preFamily.lparams_eq
  vlctx_eq := rfl

/-- Recover the exact verified pre-family context at the end of the family
telescope.

Constructor validation starts from this local telescope after changing only
the kernel/Theory environment to the staged post-family pair.  D3 reuses the
pre-change context to replay family-free constructor checks; no local
declaration or fresh identifier is reconstructed. -/
theorem CandidateFamilyStagedInput.preValidationContextRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamilyType source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (_input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily)
    (semantic : TypeChecker.CandidateExprSemanticRootRun env Us
      candidate.type raw.type) :
    ∃ preRun : TypeChecker.CandidateContextRun
        candidate.type.trace.terminalContext,
      preRun.context.venv = env ∧
      preRun.context.lparams = Us := by
  obtain ⟨inferred, recursive⟩ := semantic.recursive
  exact recursive.terminalContextRun semantic.contextRun semantic.venv_eq
    semantic.lparams_eq semantic.vlctx_eq

/-- Rebuild the verified constructor-validation context from the exact
pre-family terminal context run.

The returned run preserves the implementation local context definitionally;
only the kernel/Theory environment and the primitive evidence are changed to
the staged post-family pair. -/
theorem CandidateFamilyStagedInput.validationContextRunFromPre
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamilyType source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily)
    (terminalRun : TypeChecker.CandidateContextRun
      candidate.type.trace.terminalContext)
    (terminalVenv : terminalRun.context.venv = env)
    (terminalLparams : terminalRun.context.lparams = Us) :
    ∃ validationRun : TypeChecker.CandidateContextRun
        { candidate.type.trace.terminalContext with
          env := constructorContext.env },
      validationRun.context.venv = input.typeEnv ∧
      validationRun.context.lparams = Us ∧
      validationRun.context.vlctx = terminalRun.context.vlctx := by
  have terminalMLWF : terminalRun.context.mlctx.WF env Us := by
    simpa only [terminalVenv, terminalLparams] using
      terminalRun.context.mlctx_wf
  have postMLWF : terminalRun.context.mlctx.WF input.typeEnv Us :=
    terminalMLWF.mono (VEnv.addConst_le input.addInduct.env_add)
  have validationSafety : terminalRun.context.safety =
      input.postContext.safety := by
    calc
      terminalRun.context.safety =
          candidate.type.trace.terminalContext.safety :=
        terminalRun.context_safety
      _ = candidate.type.context.safety :=
        candidate.type.trace.terminalContext_safety
      _ = familyContext.safety := by rw [input.type.context_eq]
      _ = constructorContext.safety := by rw [input.constructorContext_eq]
      _ = input.postContext.safety := rfl
  let validationContext : TypeChecker.VContext :=
    { terminalRun.context with
      env := constructorContext.env
      venv := input.typeEnv
      hasPrimitives := input.postContext.hasPrimitives
      safePrimitives := input.postContext.safePrimitives
      trenv := by
        have postEnv : input.postContext.env = constructorContext.env := rfl
        have postVenv : input.postContext.venv = input.typeEnv := rfl
        simpa only [validationSafety, postEnv, postVenv] using
          input.postContext.trenv
      projectionReady := input.postContext.projectionReady
      structureEtaReady := input.postContext.structureEtaReady
      mlctx_wf := by
        simpa only [terminalLparams] using postMLWF }
  have validationContextEq : validationContext.toContext =
      ({ candidate.type.trace.terminalContext with
        env := constructorContext.env } : AddInductive.Context).toTypeChecker := by
    calc
      validationContext.toContext =
          { terminalRun.context.toContext with
            env := constructorContext.env } := rfl
      _ = { candidate.type.trace.terminalContext.toTypeChecker with
            env := constructorContext.env } :=
        congrArg (fun c : TypeChecker.Context =>
          { c with env := constructorContext.env }) terminalRun.context_eq
      _ = ({ candidate.type.trace.terminalContext with
          env := constructorContext.env } : AddInductive.Context).toTypeChecker :=
        rfl
  let validationRun : TypeChecker.CandidateContextRun
      { candidate.type.trace.terminalContext with
        env := constructorContext.env } :=
    TypeChecker.CandidateContextRun.ofVContext _ validationContext
      validationContextEq
      (TypeChecker.VState.WF.empty_of_reserves validationContext (by
        intro fv hfv
        exact terminalRun.state_wf.ngen_wf fv (by
          simpa only [validationContext] using hfv)))
      terminalRun.namePrefix_ne
  exact ⟨validationRun, rfl, terminalLparams, rfl⟩

/-- Rebuild the verified context in which constructor validation actually
runs.

Family candidates are interpreted before the raw family is inserted, so the
recursive run reaches the correct local telescope in the pre-family Theory
environment.  Constructor validation keeps that exact implementation local
context while replacing only the kernel/Theory environment with the staged
post-family pair.  Monotonicity of local-context verification justifies that
replacement; no local declaration, free-variable identifier, or binder order
is regenerated. -/
theorem CandidateFamilyStagedInput.validationContextRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamilyType source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily)
    (semantic : TypeChecker.CandidateExprSemanticRootRun env Us
      candidate.type raw.type) :
    ∃ validationRun : TypeChecker.CandidateContextRun
        { candidate.type.trace.terminalContext with
          env := constructorContext.env },
      validationRun.context.venv = input.typeEnv ∧
      validationRun.context.lparams = Us := by
  obtain ⟨terminalRun, terminalVenv, terminalLparams⟩ :=
    input.preValidationContextRun semantic
  obtain ⟨validationRun, validationVenv, validationLparams, _⟩ :=
    input.validationContextRunFromPre terminalRun terminalVenv terminalLparams
  exact ⟨validationRun, validationVenv, validationLparams⟩

/-- One source-indexed constructor interpreted in the shared post-family
stage. Header equality and universe alignment stay attached to the exact raw
constructor position; the expression payload contains no independently
verified context and no caller-selected semantic view. -/
structure CandidateConstructorStagedInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (stage : TypeChecker.CandidateSemanticStage candidateContext env Us)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprStagedInput stage candidate.type raw.type

/-- Forget only the shared-stage presentation and recover the established
constructor semantic input. -/
def CandidateConstructorStagedInput.semanticInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {source : Constructor}
    {candidate : AddInductive.CandidateConstructor source}
    {raw : VConstVal}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    (input : CandidateConstructorStagedInput stage candidate raw) :
    CandidateConstructorSemanticInput env Us candidate raw where
  name_eq := input.name_eq
  uvars_eq := input.uvars_eq
  type := input.type.rootInput

/-- Exact source-order translations for every constructor in one shared
post-family stage. The dependent indices enforce length, order, source, raw
header, and candidate alignment without `zip` or list lookup. -/
inductive CandidateConstructorStagedListInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (stage : TypeChecker.CandidateSemanticStage candidateContext env Us) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorStagedListInput stage .nil []
  | cons
      (head : CandidateConstructorStagedInput stage candidate raw)
      (tail : CandidateConstructorStagedListInput stage candidates raws) :
      CandidateConstructorStagedListInput stage
        (.cons candidate candidates) (raw :: raws)

/-- Convert the staged, source-indexed constructor translations to the
existing recursive semantic-input representation. -/
def CandidateConstructorStagedListInput.semanticInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal}
    (input : CandidateConstructorStagedListInput stage candidates raws) :
    CandidateConstructorSemanticListInput env Us candidates raws :=
  match input with
  | .nil => CandidateConstructorSemanticListInput.nil
  | .cons head tail =>
    CandidateConstructorSemanticListInput.cons
      head.semanticInput tail.semanticInput

/-- Pre-run semantic evidence for a complete singleton family position.  The
family type is interpreted in the input environment and its constructor list
in the exact environment obtained by inserting the raw family constant. -/
structure CandidateFamilySemanticInput (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootInput env Us
    candidate.familyType.type raw.type
  typeEnv : VEnv
  addType : env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : CandidateConstructorSemanticListInput typeEnv Us
    candidate.constructors raw.ctors

/-- Interpret the family root and all post-insertion constructor roots from
their exact pre-run inputs. -/
theorem CandidateFamilySemanticInput.exists
    (input : CandidateFamilySemanticInput env Us candidate raw) :
    Nonempty (CandidateFamilySemanticRun env Us candidate raw) := by
  obtain ⟨type⟩ := input.type.exists
  obtain ⟨constructors⟩ := input.constructors.exists
  exact ⟨{
    name_eq := input.name_eq
    uvars_eq := input.uvars_eq
    type := type
    typeEnv := input.typeEnv
    addType := input.addType
    constructors := constructors }⟩

/-- Pre-run semantic evidence for one source-indexed singleton normalization
candidate.  The source declaration and candidate list indices rule out an
unrelated raw family or a partial constructor list. -/
structure NormalizationCandidateSemanticInput (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  uvars_eq : rawDecl.uvars = Us.length
  family : CandidateFamilySemanticInput env Us
    candidate.families.singleton raw

/-- Automatically interpret the complete singleton semantic hierarchy from
its verified, source-indexed inputs. -/
theorem NormalizationCandidateSemanticInput.exists
    (input : NormalizationCandidateSemanticInput env Us candidate rawDecl) :
    Nonempty (NormalizationCandidateSemanticRun env Us candidate rawDecl) := by
  obtain ⟨family⟩ := input.family.exists
  exact ⟨{
    raw := input.raw
    raw_types_eq := input.raw_types_eq
    uvars_eq := input.uvars_eq
    family := family }⟩

/-- The automatic semantic hierarchy paired with the exact executable
family-type and constructor-list traversals that selected the same dependent
candidate.  The two producer contexts are explicit because family types are
checked before raw-family insertion and constructors after it. -/
structure ProducedNormalizationCandidateSemanticRun
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  semantic : NormalizationCandidateSemanticRun env Us candidate rawDecl
  familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
    familyContext
    (.cons candidate.families.singleton.familyType .nil)
  familiesProduced : AddInductive.CandidateFamilyListProduced
    constructorContext
    (.cons candidate.families.singleton.familyType .nil)
    candidate.families

/-- Combine exact arbitrary-length producer witnesses with verified semantic
inputs for the same source-indexed singleton candidate.  Operational evidence
selects the candidate; only the retained checker interpreter supplies Theory
meaning. -/
theorem NormalizationCandidateSemanticInput.exists_ofProduced
    (input : NormalizationCandidateSemanticInput env Us candidate rawDecl)
    (familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
      familyContext
      (.cons candidate.families.singleton.familyType .nil))
    (familiesProduced : AddInductive.CandidateFamilyListProduced
      constructorContext
      (.cons candidate.families.singleton.familyType .nil)
      candidate.families) :
    Nonempty (ProducedNormalizationCandidateSemanticRun
      familyContext constructorContext env Us candidate rawDecl) := by
  obtain ⟨semantic⟩ := input.exists
  exact ⟨{
    semantic := semantic
    familyTypesProduced := familyTypesProduced
    familiesProduced := familiesProduced }⟩

/-- The complete family-validated semantic input for a produced singleton
candidate.

Only the entry verifier alignment is supplied. The exact singleton family
validation and raw-family insertion derive the post-family verified stage;
constructor positions then supply strict translations and fuel equalities in
that derived stage. No normalized view, post-family `VEnvs.WF`, semantic run,
declaration-WF proof, or generation package is an input. -/
structure StagedNormalizationCandidateSemanticInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  declaration_uvars_eq : rawDecl.uvars = Us.length
  preFamily : TypeChecker.CandidateSemanticStage familyContext env Us
  family : CandidateFamilyStagedInput familyContext constructorContext env Us
    candidate.families.singleton.familyType raw preFamily
  validation_nparams_eq : family.validation.nparams = rawDecl.nparams
  constructorValidation : AddInductive.ConstructorValidationRun
    source family.validation.stats false
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env }
  constructors : CandidateConstructorStagedListInput family.postFamily
    candidate.families.singleton.constructors raw.ctors
  familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
    familyContext
    (.cons candidate.families.singleton.familyType .nil)
  familiesProduced : AddInductive.CandidateFamilyListProduced
    constructorContext
    (.cons candidate.families.singleton.familyType .nil)
    candidate.families

/-- The staged owner retains exactly the successful executable constructor
validation that selected its source-indexed constructor list. -/
theorem StagedNormalizationCandidateSemanticInput.constructorValidation_run
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateSemanticInput familyContext
      constructorContext env Us candidate rawDecl) :
    AddInductive.checkConstructors #[source] input.family.validation.stats
        false
        { candidate.families.singleton.familyType.type.trace.terminalContext with
          env := constructorContext.env } = .ok () :=
  input.constructorValidation.run

/-- Project the established semantic-input hierarchy from the consolidated
two-stage owner. This projection remains data-free with respect to checker
semantics: it only rearranges verified stage and translation evidence. -/
def StagedNormalizationCandidateSemanticInput.semanticInput
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateSemanticInput familyContext
      constructorContext env Us candidate rawDecl) :
    NormalizationCandidateSemanticInput env Us candidate rawDecl where
  raw := input.raw
  raw_types_eq := input.raw_types_eq
  uvars_eq := input.declaration_uvars_eq
  family := {
    name_eq := input.family.name_eq
    uvars_eq := input.family.uvars_eq
    type := input.family.type.rootInput
    typeEnv := input.family.typeEnv
    addType := input.family.addInduct.env_add
    constructors := input.constructors.semanticInput }

/-- Interpret a complete produced singleton candidate from its entry stage and
derived family-validation stage. The result stays in `Nonempty`; in particular, this theorem
does not use choice to expose a semantic run as executable data. -/
theorem StagedNormalizationCandidateSemanticInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateSemanticInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidateSemanticRun
      familyContext constructorContext env Us candidate rawDecl) :=
  input.semanticInput.exists_ofProduced input.familyTypesProduced
    input.familiesProduced

/-- Forget executable list provenance and expose the existing normalization
root selected by the automatic semantic hierarchy. -/
def ProducedNormalizationCandidateSemanticRun.root
    (run : ProducedNormalizationCandidateSemanticRun
      familyContext constructorContext env Us candidate rawDecl) :
    NormalizationCandidateRun env Us candidate rawDecl :=
  run.semantic.root

/-- Checker-produced semantic evidence for one positional raw/view
constructor pair. This has the same four-way declared/emitted split as
`NormalizedCtor.WF`, but keeps every equality in compositional evidence form
until the final Theory boundary. -/
structure NormalizedCtorRun {source : VInductDecl}
    (block : NormalizedChecked source) (ctor : NormalizedCtor)
    (env : VEnv) where
  declaredTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (ctor.declaredBinders source.nparams) (ctor.viewBinders block)
  declaredResult : TypeChecker.DefEqEvidence env source.uvars
    (ctor.declaredBinders source.nparams).reverse
    (ctor.rawResult source.nparams) (ctor.resultTarget block)
    (.sort block.checked.resultLevel)
  emittedTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (ctor.emittedBinders block) (ctor.viewBinders block)
  emittedResult : TypeChecker.DefEqEvidence env source.uvars
    (ctor.emittedBinders block).reverse
    (ctor.rawResult source.nparams) (ctor.resultTarget block)
    (.sort block.checked.resultLevel)

theorem NormalizedCtorRun.wf
    (run : NormalizedCtorRun block ctor env) :
    ctor.WF block env where
  declaredTel := run.declaredTel.telDefEq
  declaredResult := run.declaredResult.isDefEq
  emittedTel := run.emittedTel.telDefEq
  emittedResult := run.emittedResult.isDefEq

/-- Complete checker-side assembler for a generation-ready candidate.

The exact family insertion state is named once. This lets a producer check
constructor evidence in that state and lets `.wf` discharge the universally
quantified post-family environment in `GenerationChecked.WF` by equality,
without an oracle or an assumed transaction. -/
structure GenerationRun {source : VInductDecl}
    (generation : GenerationChecked source) (env : VEnv) where
  normalization : NormalizationRun generation.block.normalization env
  checked : generation.block.checked.WF env
  familyTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (generation.block.rawParams ++ generation.block.rawIndices)
    (generation.block.checked.params ++ generation.block.checked.indices)
  familyResult : TypeChecker.DefEqEvidence env source.uvars
    (generation.block.rawParams ++ generation.block.rawIndices).reverse
    generation.block.rawResult (.sort generation.block.checked.resultLevel)
    (.sort (.succ generation.block.checked.resultLevel))
  typeEnv : VEnv
  addType : env.addConst generation.block.sourceType.name
    generation.block.sourceType.toVConstant = some typeEnv
  constructors :
    ∀ ctor ∈ generation.block.ctorPairs,
      NormalizedCtorRun generation.block ctor typeEnv

/-- Assemble the complete Theory generation certificate from exact
checker-produced normalization, telescope, result, and constructor evidence. -/
theorem GenerationRun.wf
    (run : GenerationRun generation env) :
    generation.WF env := by
  refine {
    blockWF := ⟨run.normalization.wf, run.checked⟩
    familyTel := run.familyTel.telDefEq
    familyResult := run.familyResult.isDefEq
    ctors := ?_ }
  intro envT hadd ctor hctor
  have henv : envT = run.typeEnv := by
    have : some envT = some run.typeEnv := hadd.symm.trans run.addType
    exact Option.some.inj this
  subst envT
  exact (run.constructors ctor hctor).wf

/-- Exact family-spine evidence extracted from the source-indexed singleton
normalization candidate and aligned with the components retained by dependent
inductive analysis. -/
structure CandidateFamilyGenerationRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) where
  spine : TypeChecker.CandidateExprSpineRun env Us
    candidate.families.singleton.familyType.type
    normalization.raw.type normalization.family.viewType
  rawTel : VExpr.telN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type =
    generation.block.rawParams ++ generation.block.rawIndices
  rawResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type = generation.block.rawResult
  viewResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.family.viewType =
    .sort generation.block.checked.resultLevel

/-- Extract the complete family telescope/result certificate at the exact
components consumed by `GenerationRun`. -/
theorem CandidateFamilyGenerationRun.evidence
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : CandidateFamilyGenerationRun normalization generation)
    (viewType_eq : normalization.family.viewType =
      generation.block.checked.type.type) :
    TypeChecker.TelResultDefEqEvidence env Us.length []
      (generation.block.rawParams ++ generation.block.rawIndices)
      (generation.block.checked.params ++ generation.block.checked.indices)
      generation.block.rawResult
      (.sort generation.block.checked.resultLevel)
      (.sort (.succ generation.block.checked.resultLevel)) :=
  run.spine.evidenceAt run.rawTel (by
    rw [viewType_eq, generation.block.checked.type_eq,
      ← VExpr.forallN_append]
    apply TypeChecker.candidateTelN_of_dropN_terminal (B :=
      .sort generation.block.checked.resultLevel) trivial
    simpa only [viewType_eq, generation.block.checked.type_eq,
      ← VExpr.forallN_append] using run.viewResult)
    run.rawResult run.viewResult (by
      apply VEnv.HasType.sort
      simpa only [← generation.block.uvars_eq,
        normalization.uvars_eq] using
        generation.block.checked.direct_anatomy.2.2.1)

/-- Family generation alignment whose spine is projected directly from the
retained semantic hierarchy.  Callers provide only the executable structural
gate and the component equations required by `GenerationChecked`; they cannot
substitute a second recursive run or a different normalized view. -/
structure CandidateFamilySemanticGenerationRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  storedSpine :
    candidate.families.singleton.familyType.type.trace.storedSpine = true
  rawTel : VExpr.telN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type =
    generation.block.rawParams ++ generation.block.rawIndices
  rawResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type = generation.block.rawResult
  viewResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.family.type.view =
    .sort generation.block.checked.resultLevel

/-- Minimal structural input for family generation.  The retained semantic
root already owns the recursive checker run, while dependent analysis fixes
the raw and checked components.  A caller therefore supplies only the
executable stored-spine gate and the total number of binders traversed by that
spine; all telescope and terminal equations are derived below. -/
structure CandidateFamilySemanticGenerationShape
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  storedSpine :
    candidate.families.singleton.familyType.type.trace.storedSpine = true
  spineLength_eq :
    candidate.families.singleton.familyType.type.trace.spineLength =
      (generation.block.rawParams ++ generation.block.rawIndices).length

/-- Recover the existing family-generation run from the single retained
semantic owner. -/
theorem CandidateFamilySemanticGenerationRun.run
    (run : CandidateFamilySemanticGenerationRun normalization generation) :
    CandidateFamilyGenerationRun normalization.root generation where
  spine := normalization.family.type.spine run.storedSpine
  rawTel := run.rawTel
  rawResult := run.rawResult
  viewResult := run.viewResult

/-- One positional constructor candidate aligned with the raw/view
constructor pair retained by dependent analysis.

The spine certificate covers the exact stored constructor type. Its declared
telescope will later be transformed into the mixed emitted telescope by
replacing only the constructor's parameter prefix. -/
structure CandidateNormalizedCtorRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorRun env Us candidate raw)
    (ctor : NormalizedCtor) where
  raw_eq : ctor.raw = raw
  view_eq : ctor.view.value = root.view
  spine : TypeChecker.CandidateExprSpineRun env Us candidate.type
    raw.type root.viewType
  rawTel : VExpr.telN candidate.type.trace.spineLength raw.type =
    ctor.declaredBinders source.nparams
  rawResult : VExpr.dropN candidate.type.trace.spineLength raw.type =
    ctor.rawResult source.nparams
  viewResult : VExpr.dropN candidate.type.trace.spineLength root.viewType =
    ctor.resultTarget block

/-- Constructor generation alignment owned by the same retained semantic root
used for normalization.  The only spine premise is the Boolean structural gate
computed by the candidate trace; the recursive semantic run and view are
projected from `root`. -/
structure CandidateSemanticNormalizedCtorRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorSemanticRun env Us candidate raw)
    (ctor : NormalizedCtor) where
  raw_eq : ctor.raw = raw
  view_eq : ctor.view.value = root.root.view
  storedSpine : candidate.type.trace.storedSpine = true
  rawTel : VExpr.telN candidate.type.trace.spineLength raw.type =
    ctor.declaredBinders source.nparams
  rawResult : VExpr.dropN candidate.type.trace.spineLength raw.type =
    ctor.rawResult source.nparams
  viewResult : VExpr.dropN candidate.type.trace.spineLength root.type.view =
    ctor.resultTarget block

/-- Minimal structural input for one retained constructor root.  It is
independent of a caller-selected normalized pair: positional raw/view pairing
is recovered from the successful dependent analysis, and the full component
equations follow from this total stored-binder count. -/
structure CandidateConstructorSemanticGenerationShape
    {source : VInductDecl} (env : VEnv) (Us : List Name)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorSemanticRun env Us candidate raw) where
  storedSpine : candidate.type.trace.storedSpine = true
  spineLength_eq : candidate.type.trace.spineLength =
    (VExpr.telN source.nparams raw.type ++
      ctorFields (VExpr.dropN source.nparams raw.type)).length

/-- Project the compatibility constructor run without rebuilding or choosing
semantic evidence. -/
theorem CandidateSemanticNormalizedCtorRun.run
    (run : CandidateSemanticNormalizedCtorRun block env Us root ctor) :
    CandidateNormalizedCtorRun block env Us root.root ctor where
  raw_eq := run.raw_eq
  view_eq := run.view_eq
  spine := root.type.spine run.storedSpine
  rawTel := run.rawTel
  rawResult := run.rawResult
  viewResult := run.viewResult

/-- The terminal alignment and the analyzer's exact constructor shape force
the candidate trace to expose the entire checked binder telescope. -/
theorem CandidateNormalizedCtorRun.viewTel_eq
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (hctor : ctor ∈ generation.block.ctorPairs) :
    VExpr.telN candidate.type.trace.spineLength root.viewType =
      ctor.viewBinders generation.block := by
  have viewType_eq : root.viewType = ctor.view.value.type := by
    simpa only [CandidateConstructorRun.view] using
      (congrArg (fun value : VConstVal => value.type) run.view_eq).symm
  have hterminal :
      TypeChecker.CandidateTerminal (ctor.resultTarget generation.block) := by
    exact TypeChecker.candidateTerminal_appN_const _ _ _
  rw [viewType_eq, generation.viewCtorType_eq hctor]
  apply TypeChecker.candidateTelN_of_dropN_terminal hterminal
  simpa only [viewType_eq, generation.viewCtorType_eq hctor] using
    run.viewResult

/-- Extract the stored constructor's declared telescope/result evidence. -/
theorem CandidateNormalizedCtorRun.declaredEvidence
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (hctor : ctor ∈ generation.block.ctorPairs)
    (rightType : env.HasType Us.length
      (ctor.declaredBinders source.nparams).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel)) :
    TypeChecker.TelResultDefEqEvidence env Us.length []
      (ctor.declaredBinders source.nparams)
      (ctor.viewBinders generation.block)
      (ctor.rawResult source.nparams) (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
  apply run.spine.evidenceAt run.rawTel (run.viewTel_eq hctor)
    run.rawResult run.viewResult rightType

/-- The checked result spine and the candidate-certified binder telescope
determine a constructor's terminal typing judgment.  The family constant is
typed once for the whole block; individual constructor fixtures supply no
additional semantic result oracle. -/
theorem CandidateNormalizedCtorRun.rightType_ofChecked
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (checked : generation.block.checked.WF env)
    (familyConst : env.HasType source.uvars []
      (.const generation.block.sourceType.name
        (VLevel.params source.uvars))
      generation.block.checked.type.type)
    (hctor : ctor ∈ generation.block.ctorPairs) :
    env.HasType Us.length
      (ctor.declaredBinders source.nparams).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
  obtain ⟨_, evidence⟩ := run.spine.evidence
  have telescope : TypeChecker.TelDefEqEvidence env Us.length []
      (ctor.declaredBinders source.nparams)
      (ctor.viewBinders generation.block) := by
    simpa only [run.rawTel, run.viewTel_eq hctor] using evidence.telescope
  have hview := generation.checkedResultTarget_hasType
    henv.ordered checked familyConst hctor
  have hview' : env.HasType Us.length
      (ctor.viewBinders generation.block).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
    simpa only [uvars_eq] using hview
  have hctx : env.IsDefEqCtx Us.length []
      (ctor.declaredBinders source.nparams).reverse
      (ctor.viewBinders generation.block).reverse := by
    simpa using telescope.telDefEq.ctx
  exact hview'.defeqDFC henv.ordered (hctx.symm henv.ordered)

/-- Produce both constructor paths required by `NormalizedCtorRun`.

The declared path comes directly from the constructor candidate. The emitted
path replaces the stored constructor parameter prefix by the checked family
parameter prefix used by Lean's recursor generator, transporting fields and
result through the induced definitionally equal context. -/
theorem CandidateNormalizedCtorRun.normalizedCtorRun
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.rawParams generation.block.checked.params)
    (prefixLength :
      (VExpr.telN source.nparams ctor.raw.type).length =
        generation.block.checked.params.length)
    (hctor : ctor ∈ generation.block.ctorPairs)
    (rightType : env.HasType Us.length
      (ctor.declaredBinders source.nparams).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel)) :
    NormalizedCtorRun generation.block ctor env := by
  have declared := run.declaredEvidence hctor rightType
  have declaredSplit : TypeChecker.TelResultDefEqEvidence env Us.length []
      (VExpr.telN source.nparams ctor.raw.type ++
        ctor.rawFields source.nparams)
      (generation.block.checked.params ++ ctor.view.fields)
      (ctor.rawResult source.nparams) (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
    simpa only [NormalizedCtor.declaredBinders,
      NormalizedCtor.viewBinders] using declared
  have checkedParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.checked.params generation.block.checked.params :=
    .ofTelDefEq <| (familyParams.telDefEq.view_onTel henv.ordered).telDefEq_refl
  have emitted := declaredSplit.replacePrefix henv checkedParams prefixLength
  exact {
    declaredTel := by
      simpa only [uvars_eq] using declared.telescope
    declaredResult := by
      simpa only [uvars_eq, List.append_nil] using declared.result
    emittedTel := by
      simpa only [uvars_eq, NormalizedCtor.emittedBinders,
        NormalizedCtor.viewBinders] using emitted.telescope
    emittedResult := by
      simpa only [uvars_eq, NormalizedCtor.emittedBinders,
        List.append_nil] using emitted.result }

/-- Dependent positional alignment between every constructor candidate run
and every normalized constructor pair. The indices make unequal lengths,
reordering, and evidence reuse at a different source position impossible. -/
inductive CandidateNormalizedCtorListRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name) :
    {kernelSources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources} →
    {raws : List VConstVal} →
    (roots : CandidateConstructorListRun env Us candidates raws) →
    List NormalizedCtor → Type where
  | nil : CandidateNormalizedCtorListRun block env Us .nil []
  | cons
      (head : CandidateNormalizedCtorRun block env Us root ctor)
      (tail : CandidateNormalizedCtorListRun block env Us roots ctors) :
      CandidateNormalizedCtorListRun block env Us
        (.cons root roots) (ctor :: ctors)

/-- Dependent positional generation alignment over the retained constructor
semantic list.  Its projection below is definitionally tied to
`roots.roots`, so source order and the exact normalization views cannot drift
between phases. -/
inductive CandidateSemanticNormalizedCtorListRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name) :
    {kernelSources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources} →
    {raws : List VConstVal} →
    (roots : CandidateConstructorSemanticListRun env Us candidates raws) →
    List NormalizedCtor → Type where
  | nil : CandidateSemanticNormalizedCtorListRun block env Us .nil []
  | cons
      (head : CandidateSemanticNormalizedCtorRun block env Us root ctor)
      (tail : CandidateSemanticNormalizedCtorListRun block env Us roots ctors) :
      CandidateSemanticNormalizedCtorListRun block env Us
        (.cons root roots) (ctor :: ctors)

/-- Source-indexed structural generation inputs for every retained semantic
constructor root.  No normalized constructor list occurs in this type, so a
caller cannot choose, reorder, truncate, or duplicate the analyzer's pairs. -/
inductive CandidateConstructorSemanticGenerationShapeList
    (source : VInductDecl) (env : VEnv) (Us : List Name) :
    {kernelSources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources} →
    {raws : List VConstVal} →
    (roots : CandidateConstructorSemanticListRun env Us candidates raws) →
    Type where
  | nil : CandidateConstructorSemanticGenerationShapeList source env Us .nil
  | cons
      (head : CandidateConstructorSemanticGenerationShape
        (source := source) env Us root)
      (tail : CandidateConstructorSemanticGenerationShapeList
        source env Us roots) :
      CandidateConstructorSemanticGenerationShapeList source env Us
        (.cons root roots)

/-- Executable generation-layout check for a complete source-indexed
constructor candidate list.

The check is intentionally stated against the raw Theory constants retained
by the semantic hierarchy.  It accepts exactly when every candidate WHNF trace
preserves the stored main Pi spine and traverses the complete raw constructor
telescope.  List-length mismatches are rejected explicitly; no `zip` or
positional lookup can silently truncate either side. -/
def candidateConstructorSemanticGenerationShape
    (source : VInductDecl) :
    {kernelSources : List Constructor} →
    AddInductive.CandidateList AddInductive.CandidateConstructor
      kernelSources →
    List VConstVal → Bool
  | _, .nil, [] => true
  | _, .nil, _ :: _ => false
  | _, .cons _ _, [] => false
  | _, .cons candidate candidates, raw :: raws =>
    candidate.type.trace.storedSpine &&
      candidate.type.trace.spineLength ==
        (VExpr.telN source.nparams raw.type ++
          ctorFields (VExpr.dropN source.nparams raw.type)).length &&
      candidateConstructorSemanticGenerationShape source candidates raws

/-- Executable generation-layout check for a complete singleton
normalization candidate and its raw Theory family.

This definition is independent of semantic proofs.  It checks only the
source-indexed candidate traces against the raw family/constructor telescope
layout that generation would emit.  Verify's retained semantic hierarchy
later reindexes the same Boolean onto its exact raw family. -/
def normalizationCandidateGenerationShape
    {kernelSource : InductiveType}
    (source : VInductDecl) (raw : VInductiveType)
    (candidate : AddInductive.NormalizationCandidate [kernelSource]) : Bool :=
  let familyTrace :=
    candidate.families.singleton.familyType.type.trace
  (familyTrace.storedSpine &&
      familyTrace.spineLength ==
        (VExpr.telN source.nparams raw.type ++
          ctorFields (VExpr.dropN source.nparams raw.type)).length) &&
    candidateConstructorSemanticGenerationShape source
      candidate.families.singleton.constructors raw.ctors

/-- One executable constructor-list shape check determines every dependent
per-position shape record required by semantic generation. -/
def CandidateConstructorSemanticGenerationShapeList.ofCheck
    {source : VInductDecl} {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    (roots : CandidateConstructorSemanticListRun env Us candidates raws)
    (shape : candidateConstructorSemanticGenerationShape
      source candidates raws = true) :
    CandidateConstructorSemanticGenerationShapeList source env Us roots :=
  match roots with
  | .nil => .nil
  | .cons head tail => by
      simp only [candidateConstructorSemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq] at shape
      exact .cons {
        storedSpine := shape.1.1
        spineLength_eq := shape.1.2 }
        (CandidateConstructorSemanticGenerationShapeList.ofCheck
          tail shape.2)
termination_by sizeOf roots

/-- Forget only retained semantic ownership and recover the existing
generation-facing positional list. -/
def CandidateSemanticNormalizedCtorListRun.run :
    (semantic : CandidateSemanticNormalizedCtorListRun
      block env Us roots ctors) →
      CandidateNormalizedCtorListRun block env Us roots.roots ctors
  | .nil => .nil
  | .cons head tail => .cons head.run tail.run

/-- Assemble a `NormalizedCtorRun` for every constructor in an exact
dependent positional list. -/
theorem CandidateNormalizedCtorListRun.normalizedCtorRuns
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    {roots : CandidateConstructorListRun env Us candidates raws}
    {ctors : List NormalizedCtor}
    (run : CandidateNormalizedCtorListRun generation.block env Us roots ctors)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.rawParams generation.block.checked.params)
    (checked : generation.block.checked.WF env)
    (familyConst : env.HasType source.uvars []
      (.const generation.block.sourceType.name
        (VLevel.params source.uvars))
      generation.block.checked.type.type)
    (pairMembership : ∀ ctor ∈ ctors,
      ctor ∈ generation.block.ctorPairs)
    (prefixLengths : ∀ ctor ∈ ctors,
      (VExpr.telN source.nparams ctor.raw.type).length =
        generation.block.checked.params.length) :
    ∀ ctor ∈ ctors, NormalizedCtorRun generation.block ctor env := by
  induction run with
  | nil => intro ctor hctor; simp at hctor
  | cons head tail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | hctor
    · exact head.normalizedCtorRun henv uvars_eq familyParams
        (prefixLengths _ (.head _))
        (pairMembership _ (.head _))
        (head.rightType_ofChecked henv uvars_eq checked familyConst
          (pairMembership _ (.head _)))
    · exact ih
        (fun ctor hctor => pairMembership ctor (.tail _ hctor))
        (fun ctor hctor => prefixLengths ctor (.tail _ hctor))
        ctor hctor

/-- Complete source-indexed candidate certificate for one generation-ready
singleton inductive declaration.

`analysis` records that the candidate-derived normalization produced this exact
dependent generation result. `constructors` then aligns every post-family
candidate run with the corresponding dependent analyzer pair. -/
structure GenerationCandidateRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) where
  analysis : normalization.normalization.generation? = some generation
  checked : generation.block.checked.WF env
  family : CandidateFamilyGenerationRun normalization generation
  constructors : CandidateNormalizedCtorListRun generation.block
    normalization.family.typeEnv Us normalization.family.constructors
    generation.block.ctorPairs

/-- Complete generation assembly owned by one retained semantic hierarchy.

This is the no-parallel-run form of `GenerationCandidateRun`: family and
constructor spines are projections of `normalization`, while `analysis` retains
the exact dependent analyzer result consumed by Theory generation. -/
structure GenerationCandidateSemanticRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  analysis : normalization.root.normalization.generation? = some generation
  checked : generation.block.checked.WF env
  family : CandidateFamilySemanticGenerationRun normalization generation
  constructors : CandidateSemanticNormalizedCtorListRun generation.block
    normalization.family.typeEnv Us normalization.family.constructors
    generation.block.ctorPairs

/-- Complete semantic-generation input with all analyzer-determined component
equations erased.  Compared with `GenerationCandidateSemanticRun`, this form
retains only checked semantics plus the executable stored-spine/length shape
for each source-indexed root.  Its projection below reconstructs the exact
family and dependent constructor alignment from `analysis`. -/
structure GenerationCandidateSemanticShapeRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  analysis : normalization.root.normalization.generation? = some generation
  checked : generation.block.checked.WF env
  family : CandidateFamilySemanticGenerationShape normalization generation
  constructors : CandidateConstructorSemanticGenerationShapeList source
    normalization.family.typeEnv Us normalization.family.constructors

/-- One executable structural gate for the complete retained singleton
candidate hierarchy.

The family check uses the complete raw parameter/index telescope.  The
constructor check traverses the source-indexed candidate and raw lists
dependently.  This consolidates the former per-fixture family and constructor
proof records into one computation while remaining separate from semantic
authority and dependent analysis. -/
def NormalizationCandidateSemanticRun.generationShape
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source) :
    Bool :=
  normalizationCandidateGenerationShape source normalization.raw candidate

/-- One successful outer candidate together with the executable structural
gate required before mixed raw/view generation.

The record carries the exact ordinary producer equation, so the shape check
cannot be reused for a different candidate.  It remains operational evidence:
semantic authority is supplied only after Verify interprets the retained
checker executions. -/
structure ProducedGenerationShapeCandidate
    (source : VInductDecl) (raw : VInductiveType)
    (kernelSource : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) where
  candidate : AddInductive.NormalizationCandidate [kernelSource]
  produced :
    AddInductive.buildNormalizationCandidate source.nparams
        [kernelSource] numNested isUnsafe context = .ok candidate
  shape : normalizationCandidateGenerationShape source raw candidate = true

/-- Run the ordinary outer producer and immediately reject candidates whose
retained traces cannot support mixed generation of the supplied raw Theory
family.  The successful result retains both exact producer provenance and the
single complete shape proof. -/
def produceGenerationShapeCandidate
    (source : VInductDecl) (raw : VInductiveType)
    (kernelSource : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) :
    Except Exception (ProducedGenerationShapeCandidate source raw kernelSource
      numNested isUnsafe context) :=
  match produced : AddInductive.buildNormalizationCandidate source.nparams
      [kernelSource] numNested isUnsafe context with
  | .error error => .error error
  | .ok candidate =>
    if shape : normalizationCandidateGenerationShape source raw candidate then
      .ok { candidate, produced, shape }
    else
      .error (.other
        "normalization candidate does not preserve the generation spine")

private theorem produceGenerationShapeCandidate_match_ok
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (result : Except Exception
      (AddInductive.NormalizationCandidate [kernelSource]))
    (toProduced : ∀ actual, result = .ok actual →
      AddInductive.buildNormalizationCandidate source.nparams
          [kernelSource] numNested isUnsafe context = .ok actual)
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (result_ok : result = .ok candidate)
    (shape : normalizationCandidateGenerationShape source raw candidate = true) :
    (match result_eq : result with
    | .error error => Except.error error
    | .ok actual =>
      if actualShape : normalizationCandidateGenerationShape source raw actual then
        Except.ok (show ProducedGenerationShapeCandidate source raw kernelSource
            numNested isUnsafe context from {
          candidate := actual
          produced := toProduced actual result_eq
          shape := actualShape })
      else
        Except.error (.other
          "normalization candidate does not preserve the generation spine")) =
      Except.ok (show ProducedGenerationShapeCandidate source raw kernelSource
          numNested isUnsafe context from {
        candidate
        produced := toProduced candidate result_ok
        shape }) := by
  subst result
  simp [shape]

/-- A successful ordinary producer equation and successful hierarchy-shape
check determine the exact successful result of the strengthened producer.

Keeping this dependent-match elimination here avoids repeating proof-carrying
`Except` reasoning in clients. -/
theorem produceGenerationShapeCandidate_eq_ok
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (produced :
      AddInductive.buildNormalizationCandidate source.nparams
          [kernelSource] numNested isUnsafe context = .ok candidate)
    (shape : normalizationCandidateGenerationShape source raw candidate = true) :
    produceGenerationShapeCandidate source raw kernelSource numNested isUnsafe
        context =
      .ok { candidate, produced, shape } := by
  unfold produceGenerationShapeCandidate
  exact produceGenerationShapeCandidate_match_ok
    (result := AddInductive.buildNormalizationCandidate source.nparams
      [kernelSource] numNested isUnsafe context)
    (toProduced := fun _ result_eq => result_eq) produced shape

/-- Project the established generation assembler.  Every normalization root,
view, and recursive spine remains definitionally tied to the semantic owner. -/
def GenerationCandidateSemanticRun.run
    (run : GenerationCandidateSemanticRun normalization generation) :
    GenerationCandidateRun normalization.root generation where
  analysis := run.analysis
  checked := run.checked
  family := run.family.run
  constructors := run.constructors.run

/-- A retained analyzer result necessarily contains the normalization that was
analyzed.  This is derived from `analysis`, rather than supplied by fixtures. -/
theorem GenerationCandidateRun.normalization_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    generation.block.normalization = normalization.normalization :=
  Normalization.generation?_normalization run.analysis

/-- The source-indexed singleton declarations force the analyzer's raw family
to be the exact family retained by a normalization candidate. -/
theorem NormalizationCandidateRun.sourceType_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) :
    generation.block.sourceType = normalization.raw := by
  have h : [generation.block.sourceType] = [normalization.raw] :=
    generation.block.source_types_eq.symm.trans normalization.raw_types_eq
  injection h

/-- Exact dependent analysis selects the reconstructed family view, including
its constructor list, not merely an expression payload with the same type. -/
theorem NormalizationCandidateRun.familyViewType_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (analysis : normalization.normalization.generation? = some generation) :
    generation.block.checked.type = normalization.family.view := by
  have normalization_eq : generation.block.normalization =
      normalization.normalization :=
    Normalization.generation?_normalization analysis
  have hviews := congrArg (fun norm : Normalization source => norm.view.types)
    normalization_eq
  have htypes : [generation.block.checked.type] =
      [normalization.family.view] := by
    calc
      [generation.block.checked.type] =
          generation.block.normalization.view.types :=
        generation.block.checked.types_eq.symm
      _ = normalization.normalization.view.types := hviews
      _ = [normalization.family.view] := rfl
  injection htypes

/-- The retained dependent analysis necessarily checks the exact family view
selected by the normalization candidate.  This equation is a consequence of
the two singleton declaration indices and `normalization_eq`, not a separate
fixture alignment premise. -/
theorem GenerationCandidateRun.familyView_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    normalization.family.viewType = generation.block.checked.type.type := by
  exact (congrArg (fun ty : VInductiveType => ty.type)
    (normalization.familyViewType_eq run.analysis)).symm

/-- Taking the exact length of the complete stored telescope recovers both
its binder list and its non-forall result.  This is the structural bridge from
one numeric trace invariant to generation's named raw components. -/
private theorem generationTelNForallNLength :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.telN As.length (VExpr.forallN As B) = As
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.telN,
      generationTelNForallNLength As B]

private theorem generationDropNForallNLength :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.dropN As.length (VExpr.forallN As B) = B
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.dropN,
      generationDropNForallNLength As B]

private theorem candidateFullTelComponents (np n : Nat) (e : VExpr)
    (h : n =
      (VExpr.telN np e ++ ctorFields (VExpr.dropN np e)).length) :
    VExpr.telN n e =
        VExpr.telN np e ++ ctorFields (VExpr.dropN np e) ∧
      VExpr.dropN n e = VExpr.resultOf (VExpr.dropN np e) := by
  let As := VExpr.telN np e ++ ctorFields (VExpr.dropN np e)
  have he :
      VExpr.forallN As (VExpr.resultOf (VExpr.dropN np e)) = e := by
    simp only [As, VExpr.forallN_append,
      forallN_ctorFields_resultOf, VExpr.forallN_telN_dropN]
  let B := VExpr.resultOf (VExpr.dropN np e)
  have hAs : n = As.length := h
  change VExpr.telN n e = As ∧ VExpr.dropN n e = B
  rw [hAs, ← he]
  exact ⟨generationTelNForallNLength _ _,
    generationDropNForallNLength _ _⟩

/-- Derive every family component equation from the minimal structural shape
and the exact dependent analyzer result. -/
private theorem CandidateFamilySemanticGenerationShape.generationRun
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (input : CandidateFamilySemanticGenerationShape
      normalization generation)
    (analysis : normalization.root.normalization.generation? =
      some generation) :
    CandidateFamilySemanticGenerationRun normalization generation where
  storedSpine := input.storedSpine
  rawTel := by
    have components := candidateFullTelComponents source.nparams
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type (by
        simpa only [NormalizedChecked.rawParams,
          NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation] using
          input.spineLength_eq)
    simpa only [NormalizedChecked.rawParams,
      NormalizedChecked.rawIndices,
      NormalizationCandidateSemanticRun.root,
      normalization.root.sourceType_eq generation] using components.1
  rawResult := by
    have components := candidateFullTelComponents source.nparams
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type (by
        simpa only [NormalizedChecked.rawParams,
          NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation] using
          input.spineLength_eq)
    simpa only [NormalizedChecked.rawResult,
      NormalizationCandidateSemanticRun.root,
      normalization.root.sourceType_eq generation] using components.2
  viewResult := by
    let As := generation.block.checked.params ++
      generation.block.checked.indices
    have hlength :
        candidate.families.singleton.familyType.type.trace.spineLength =
          As.length := by
      rw [input.spineLength_eq]
      simp only [As, List.length_append]
      rw [generation.shape.2.1, generation.shape.2.2.1]
    have hview : normalization.family.type.view =
        generation.block.checked.type.type := by
      simpa only [NormalizationCandidateSemanticRun.root,
        CandidateFamilySemanticRun.root, CandidateFamilyRun.view] using
        (congrArg (fun ty : VInductiveType => ty.type)
          (normalization.root.familyViewType_eq analysis)).symm
    rw [hview, generation.block.checked.type_eq, hlength]
    simpa only [As, VExpr.forallN_append] using
      generationDropNForallNLength As
        (.sort generation.block.checked.resultLevel)

/-- Derive one normalized constructor alignment after its positional raw/view
equalities have been recovered from the analyzer-owned pair list. -/
private theorem CandidateConstructorSemanticGenerationShape.generationRun
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorSemanticRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (input : CandidateConstructorSemanticGenerationShape
      (source := source) env Us root)
    (raw_eq : ctor.raw = raw)
    (view_eq : ctor.view.value = root.root.view)
    (hctor : ctor ∈ generation.block.ctorPairs) :
    CandidateSemanticNormalizedCtorRun generation.block env Us root ctor where
  raw_eq := raw_eq
  view_eq := view_eq
  storedSpine := input.storedSpine
  rawTel := by
    have components := candidateFullTelComponents source.nparams
      candidate.type.trace.spineLength raw.type input.spineLength_eq
    simpa only [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields, raw_eq] using components.1
  rawResult := by
    have components := candidateFullTelComponents source.nparams
      candidate.type.trace.spineLength raw.type input.spineLength_eq
    simpa only [NormalizedCtor.rawResult, raw_eq] using components.2
  viewResult := by
    let As := generation.block.checked.params ++ ctor.view.fields
    have hlength : candidate.type.trace.spineLength = As.length := by
      rw [input.spineLength_eq]
      simp only [As, List.length_append]
      rw [← raw_eq]
      have hshape := generation.shape.2.2.2.2.2 ctor hctor
      simp only [NormalizedCtor.rawFields] at hshape
      rw [hshape.2.2.1, hshape.2.2.2,
        generation.shape.1.symm.trans generation.shape.2.1]
    have viewType_eq : root.type.view = ctor.view.value.type := by
      exact (congrArg (fun value : VConstVal => value.type) view_eq).symm
    rw [viewType_eq, generation.viewCtorType_eq hctor, hlength]
    exact generationDropNForallNLength As _

/-- Recursively align structural constructor inputs with a pair list whose raw
and checked-value projections are already fixed. -/
private def
    CandidateConstructorSemanticGenerationShapeList.generationRuns
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    {roots : CandidateConstructorSemanticListRun env Us candidates raws} :
    (input : CandidateConstructorSemanticGenerationShapeList
      source env Us roots) →
    (ctors : List NormalizedCtor) →
    (raws_eq : ctors.map (·.raw) = raws) →
    (views_eq : ctors.map (fun ctor => ctor.view.value) =
      roots.roots.views) →
    (membership : ∀ ctor ∈ ctors,
      ctor ∈ generation.block.ctorPairs) →
    CandidateSemanticNormalizedCtorListRun generation.block env Us roots ctors
  | .nil, [], _, _, _ => .nil
  | .nil, _ :: _, raws_eq, _, _ => by simp at raws_eq
  | .cons _ _, [], raws_eq, _, _ => by simp at raws_eq
  | .cons head tail, ctor :: ctors, raws_eq, views_eq, membership => by
      simp only [List.map_cons, List.cons.injEq] at raws_eq
      simp only [List.map_cons,
        CandidateConstructorSemanticListRun.roots,
        CandidateConstructorListRun.views, List.cons.injEq] at views_eq
      exact .cons
        (head.generationRun raws_eq.1 views_eq.1
          (membership ctor (.head _)))
        (tail.generationRuns ctors raws_eq.2 views_eq.2
          (fun ctor hctor => membership ctor (.tail _ hctor)))

/-- Exact analysis determines the complete dependent normalized-constructor
list from source-indexed semantic roots and their minimal structural shapes. -/
private def
    CandidateConstructorSemanticGenerationShapeList.ofAnalysis
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (input : CandidateConstructorSemanticGenerationShapeList source
      normalization.family.typeEnv Us normalization.family.constructors)
    (analysis : normalization.root.normalization.generation? =
      some generation) :
    CandidateSemanticNormalizedCtorListRun generation.block
      normalization.family.typeEnv Us normalization.family.constructors
      generation.block.ctorPairs := by
  apply input.generationRuns
  · simpa only [NormalizationCandidateSemanticRun.root,
      normalization.root.sourceType_eq generation] using
      generation.rawCtors_eq
  · have viewType_eq := normalization.root.familyViewType_eq analysis
    calc
      generation.block.ctorPairs.map (fun ctor => ctor.view.value) =
          generation.block.checked.constructors.map (·.value) := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (·.value)) generation.viewCtors_eq
      _ = generation.block.checked.type.ctors := by
        rw [generation.block.checked.constructors_eq, List.map_map]
        change generation.block.checked.type.ctors.map (fun c => c) = _
        exact List.map_id' generation.block.checked.type.ctors
      _ = normalization.family.root.view.ctors := by
        simpa only [NormalizationCandidateSemanticRun.root] using
          congrArg (fun ty : VInductiveType => ty.ctors) viewType_eq
      _ = normalization.family.constructors.roots.views := rfl
  · exact fun _ hctor => hctor

/-- Recover every analyzer-owned constructor pairing from the retained
semantic hierarchy, dependent analysis, and executable structural gate.

This projection deliberately does not require `Checked.WF`: it exposes only
the exact source/candidate/raw/view alignment needed to derive that semantic
fact in the constructor-validation layer. -/
def NormalizationCandidateSemanticRun.constructorGenerationRuns
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    CandidateSemanticNormalizedCtorListRun generation.block
      normalization.family.typeEnv Us normalization.family.constructors
      generation.block.ctorPairs := by
  simp only [NormalizationCandidateSemanticRun.generationShape,
    normalizationCandidateGenerationShape, Bool.and_eq_true,
    beq_iff_eq] at shape
  exact (CandidateConstructorSemanticGenerationShapeList.ofCheck
    normalization.family.constructors shape.2).ofAnalysis analysis

/-- Reconstruct the established semantic-generation run from the reduced
shape boundary.  No raw/view pair or component equation is supplied here. -/
def GenerationCandidateSemanticShapeRun.run
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (input : GenerationCandidateSemanticShapeRun normalization generation) :
    GenerationCandidateSemanticRun normalization generation where
  analysis := input.analysis
  checked := input.checked
  family := input.family.generationRun input.analysis
  constructors := input.constructors.ofAnalysis input.analysis

/-- Reconstruct well-formedness of the post-family environment from the
retained pre-family context, candidate raw/view equality, checked family view,
and exact raw-family insertion.  Fixtures therefore do not supply this semantic
consequence independently. -/
theorem GenerationCandidateRun.typeEnv_wf
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    VEnv.WF normalization.family.typeEnv := by
  have henv : VEnv.WF env := by
    simpa only [normalization.family.typeRun.venv_eq] using
      normalization.family.typeRun.contextRun.context.Ewf
  obtain ⟨_, hfamily⟩ := normalization.family.typeRun.evidence
  have hview : env.IsType Us.length [] normalization.family.viewType := by
    simpa only [← generation.block.uvars_eq, normalization.uvars_eq,
      run.familyView_eq] using run.checked.family_isType
  have hraw : env.IsType Us.length [] normalization.raw.type :=
    VEnv.IsType.defeqU_l henv trivial hfamily.isDefEq.toU.symm hview
  have hrawWF : normalization.raw.toVConstant.WF env := by
    show env.IsType normalization.raw.uvars [] normalization.raw.type
    simpa only [normalization.family.uvars_eq] using hraw
  obtain ⟨ds, hds⟩ := henv
  exact ⟨.axiom normalization.raw.toVConstVal :: ds,
    .decl (.axiom hrawWF normalization.family.addType) hds⟩

/-- Type the raw family constant at the analyzer-selected family view in the
post-family environment.  The proof combines the exact raw insertion, the
candidate's whole-family equality, and checked family well-formedness once;
constructors can then share this result. -/
theorem GenerationCandidateRun.familyConst_hasType
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    normalization.family.typeEnv.HasType source.uvars []
      (.const generation.block.sourceType.name
        (VLevel.params source.uvars))
      generation.block.checked.type.type := by
  have sourceType_eq : generation.block.sourceType = normalization.raw := by
    have h : [generation.block.sourceType] = [normalization.raw] :=
      generation.block.source_types_eq.symm.trans normalization.raw_types_eq
    injection h
  have hlookup : normalization.family.typeEnv.constants
      normalization.raw.name = some normalization.raw.toVConstant :=
    VEnv.addConst_self normalization.family.addType
  have hconstRaw := VEnv.HasType.const0 hlookup
    (run.typeEnv_wf.ordered.constWF hlookup)
  have hconstRaw' : normalization.family.typeEnv.HasType Us.length []
      (.const normalization.raw.name (VLevel.params Us.length))
      normalization.raw.type := by
    simpa only [normalization.family.uvars_eq] using hconstRaw
  obtain ⟨_, hfamily⟩ := normalization.family.typeRun.evidence
  have hchecked := run.checked.mono
    (VEnv.addConst_le normalization.family.addType)
  have hviewType : normalization.family.typeEnv.IsType Us.length []
      normalization.family.viewType := by
    simpa only [← generation.block.uvars_eq, normalization.uvars_eq,
      run.familyView_eq] using hchecked.family_isType
  obtain ⟨_, hviewType⟩ := hviewType
  have hfamilyExact :=
    (hfamily.isDefEq.toU.mono
      (VEnv.addConst_le normalization.family.addType)).of_r
        run.typeEnv_wf trivial hviewType
  have hconstView : normalization.family.typeEnv.HasType Us.length []
      (.const normalization.raw.name (VLevel.params Us.length))
      normalization.family.viewType :=
    hfamilyExact.defeq hconstRaw'
  simpa only [normalization.uvars_eq, sourceType_eq,
    run.familyView_eq] using hconstView

/-- Assemble the existing checker-side `GenerationRun` entirely from the
source-indexed normalization candidate and its exact spine certificates. -/
def GenerationCandidateRun.generationRun
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    GenerationRun generation env := by
  have familyEvidence := run.family.evidence run.familyView_eq
  have familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.rawParams generation.block.checked.params := by
    apply TypeChecker.TelDefEqEvidence.ofTelDefEq
    simpa [generation.shape.2.1] using
      familyEvidence.telescope.telDefEq.take
        generation.block.rawParams.length
  have familyParamsTypeEnv := familyParams.mono
    (VEnv.addConst_le normalization.family.addType)
  have sourceType_eq : generation.block.sourceType = normalization.raw := by
    have h : [generation.block.sourceType] = [normalization.raw] :=
      generation.block.source_types_eq.symm.trans normalization.raw_types_eq
    injection h
  refine {
    normalization := by
      simpa only [run.normalization_eq] using
        normalization.normalizationRun
    checked := run.checked
    familyTel := by
      simpa only [normalization.uvars_eq] using familyEvidence.telescope
    familyResult := by
      simpa only [normalization.uvars_eq, List.append_nil] using
        familyEvidence.result
    typeEnv := normalization.family.typeEnv
    addType := by
      simpa only [sourceType_eq] using normalization.family.addType
    constructors := ?_ }
  apply run.constructors.normalizedCtorRuns run.typeEnv_wf
    normalization.uvars_eq familyParamsTypeEnv
    (run.checked.mono (VEnv.addConst_le normalization.family.addType))
    run.familyConst_hasType (fun _ hctor => hctor)
  intro ctor hctor
  exact (generation.shape.2.2.2.2.2 ctor hctor).2.2.1.trans
    (generation.shape.1.symm.trans generation.shape.2.1)

/-- Public Theory boundary for a complete source-indexed generation
candidate. -/
theorem GenerationCandidateRun.wf
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    generation.WF env :=
  run.generationRun.wf

/-- Complete dependent semantic package for one Verify-side singleton
candidate.

`kernelSource` and `candidate` retain the exact implementation metadata and
source-indexed operational trace. `normalization` ties that trace to the raw
Theory declaration and its reconstructed view. `generation` is the successful
dependent analysis, and `run` proves that this exact candidate supplies every
semantic obligation consumed by mixed artifact generation. No independently
chosen view can be inserted into this package. -/
structure GenerationCandidatePackage (env : VEnv) (Us : List Name) where
  kernelSource : InductiveType
  source : VInductDecl
  candidate : AddInductive.NormalizationCandidate [kernelSource]
  normalization : NormalizationCandidateRun env Us candidate source
  generation : GenerationChecked source
  run : GenerationCandidateRun normalization generation

/-- Package an already assembled source-indexed candidate run without
repeating any of its dependent indices at a call site. -/
def GenerationCandidateRun.package
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    GenerationCandidatePackage env Us where
  kernelSource := kernelSource
  source := source
  candidate := candidate
  normalization := normalization
  generation := generation
  run := run

/-- Erase checker and candidate provenance at the consumer boundary. The
result contains only the Theory generation value and its ordinary semantic
certificate, which is the complete input of `VEnv.addInductCertified`. -/
def GenerationCandidatePackage.certificate
    (package : GenerationCandidatePackage env Us) :
    package.source.GenerationCertificate env where
  generation := package.generation
  wf := package.run.wf

/-- Build the general Verify metadata replay from a candidate package and the
ordinary implementation-to-Theory insertion witnesses.

The generation value and its semantic proof are not independent inputs: both
are projected from `package`. The remaining arguments concern only constant
map alignment and the exact successful transaction states, so a caller cannot
pair metadata replay with an unrelated normalized view. -/
def GenerationCandidatePackage.addInductTrace
    (package : GenerationCandidatePackage env Us)
    {m₁ m₂ : ConstMap} {env₂ : VEnv}
    (typeMap : ConstMap) (typeEnv : VEnv)
    (ctorMap : ConstMap) (ctorEnv recEnv : VEnv)
    (addType : AddInductConstant .induct m₁ env
      package.generation.block.sourceType.toVConstVal typeMap typeEnv)
    (addCtors : AddInductConstants .ctor typeMap typeEnv
      package.generation.block.sourceType.ctors ctorMap ctorEnv)
    (addRec : AddInductConstant .recursor ctorMap ctorEnv
      (inductGenerationRecVal package.generation) m₂ recEnv)
    (recK : RecursorKMatches addRec.info package.generation.kTarget)
    (addRules : AddDefEqs recEnv
      package.generation.generatedRules env₂) :
    AddInductTrace m₁ env package.source m₂ env₂ where
  generation := package.generation
  generation_wf := package.certificate.wf
  typeMap := typeMap
  typeEnv := typeEnv
  ctorMap := ctorMap
  ctorEnv := ctorEnv
  recEnv := recEnv
  addType := addType
  addCtors := addCtors
  addRec := addRec
  recK := recK
  addRules := addRules

/-- Optional outer provenance for packages obtained by the executable
metadata pass itself. Keeping the exact producer equation separate from the
semantic package makes the trust boundary explicit: computation selects the
candidate, while `GenerationCandidateRun` alone grants it Theory meaning. -/
structure ProducedGenerationCandidatePackage
    (env : VEnv) (Us : List Name) where
  package : GenerationCandidatePackage env Us
  context : AddInductive.Context
  nparams : Nat
  numNested : Nat
  isUnsafe : Bool
  produced :
    AddInductive.buildNormalizationCandidate nparams
        [package.kernelSource] numNested isUnsafe context =
      .ok package.candidate

/-- Attach exact executable provenance to an already verified singleton
generation run.

Both premises are indexed by the same kernel source and dependent candidate:
the executable equation therefore cannot be reused for a different semantic
run, reordered constructor list, or caller-selected view.  Conversely, the
equation supplies no semantic authority by itself; all Theory meaning remains
in `run`. -/
def GenerationCandidateRun.producedPackage
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation)
    (context : AddInductive.Context)
    (nparams numNested : Nat) (isUnsafe : Bool)
    (produced :
      AddInductive.buildNormalizationCandidate nparams
          [kernelSource] numNested isUnsafe context = .ok candidate) :
    ProducedGenerationCandidatePackage env Us where
  package := run.package
  context := context
  nparams := nparams
  numNested := numNested
  isUnsafe := isUnsafe
  produced := produced

/-- Package the no-parallel-run semantic assembler at the existing public
boundary. -/
def GenerationCandidateSemanticRun.package
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateSemanticRun normalization generation) :
    GenerationCandidatePackage env Us :=
  run.run.package

/-- Attach the exact successful outer metadata call directly to a retained
semantic-generation owner. -/
def GenerationCandidateSemanticRun.producedPackage
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateSemanticRun normalization generation)
    (context : AddInductive.Context)
    (nparams numNested : Nat) (isUnsafe : Bool)
    (produced :
      AddInductive.buildNormalizationCandidate nparams
          [kernelSource] numNested isUnsafe context = .ok candidate) :
    ProducedGenerationCandidatePackage env Us :=
  run.run.producedPackage context nparams numNested isUnsafe produced

/-
The evidence types mention exact verifier executions, so the semantic
interpretation roots below intentionally inherit the same transitional Verify
closure as `WhnfRun.isDefEq`. Exact guards ensure that the generic assembler
does not silently widen it. Theory-only helper closures are guarded by
`Tests.TheoryConsumerSurface` without importing Verify.
-/

#guard_named_axioms Ix.Theory.Named.TypeChecker.AddInductConstant.safePrimitives [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.context_env [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.context_lctx [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.context_safety [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.context_lparams [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.context_fuel [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.view_isType_of_terminalSort [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprSemanticRootRun.source_isType_of_terminalSort [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprSemanticRootRun.viewParameters [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprSemanticRootRun.viewIndices [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateFamilyStagedInput [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateFamilyStagedInput.rawWF [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateFamilyStagedInput.postContext [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateFamilyStagedInput.postContextRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateFamilyStagedInput.postFamily [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]


#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprSemanticRootInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateConstructorSemanticListInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateSemanticInput.exists_ofProduced [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidateSemanticInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateFamilySemanticGenerationRun.run [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateSemanticNormalizedCtorListRun.run [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateSemanticRun.run [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateSemanticShapeRun.run [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.candidateConstructorSemanticGenerationShape [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.normalizationCandidateGenerationShape [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateConstructorSemanticGenerationShapeList.ofCheck [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateSemanticRun.generationShape [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.produceGenerationShapeCandidate [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.produceGenerationShapeCandidate_eq_ok [propext, Classical.choice, Quot.sound]
#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateSemanticRun.package [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateSemanticRun.producedPackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.VState.WF.empty_of_reserves [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.candidateFreshFVarId_reserved [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.root [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Syntax.structEq_eq]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateContextRun.pushLocalDecl [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.candidateCheckTypeStep_exists_translation [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.IsDefEqRun.ofCandidateStep [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.IsDefEqRun.isDefEqU [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.candidateTypeAnnotation_fvarsIn []

#guard_named_axioms Ix.Theory.Named.TypeChecker.candidateTypeAnnotation_exists_translation [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.exists_ofCandidate [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.exists_ofCandidateFVars [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.WhnfRun.ofCandidateStep [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CheckTypeRun.ofCandidateStep [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateNodeRun.ofCandidate [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateNodeRun.exists_ofCandidate [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateNodeRun.evidence [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.evidence [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.source_tr [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.view_tr [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRootRun.evidence [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.TelDefEqEvidence.telDefEq [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.TelDefEqEvidence.ofTelDefEq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.TypeChecker.TelResultDefEqEvidence.replacePrefix [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprRun.spineEvidence [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.TypeChecker.CandidateExprSpineRun.evidenceAt [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.normalization_eq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateRun.sourceType_eq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateRun.familyViewType_eq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.familyView_eq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.typeEnv_wf [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.familyConst_hasType [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateNormalizedCtorRun.rightType_ofChecked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateNormalizedCtorRun.viewTel_eq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateNormalizedCtorRun.normalizedCtorRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.wf [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateConstructorListRun.sameHeaders [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateConstructorListRun.evidence [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateRun.normalization [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateRun.normalizationRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizedCtorRun.wf [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationRun.wf [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.package [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidateRun.producedPackage [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidatePackage.certificate [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationCandidatePackage.addInductTrace [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.StagedNormalizationCandidateSemanticInput.constructorValidation_run [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationBlockRun.wf [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateBlockFamilySemanticListRun.sameHeaders [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateBlockFamilySemanticListRun.evidence [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateBlockFamilySemanticInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.CandidateBlockFamilySemanticListInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateBlockSemanticInput.exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizationCandidateBlockSemanticInput.exists_ofProduced [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]


end VInductDecl

end Ix.Theory.Named
