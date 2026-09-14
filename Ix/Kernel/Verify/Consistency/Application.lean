/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BinderOpening
import Ix.Kernel.Knot

/-!
# Production application and dependent substitution

The application result is the actual memoized substitution of its argument
into the inferred Pi codomain. Registered locals remain free in the kernel
tree while their model indices move below each syntactic binder.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

private theorem bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

private theorem depth_succ {depth : UInt64} (bound : depth.toNat + 1 < UInt64.size) :
    (depth + 1).toNat = depth.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt bound]

/-- Lifting a term with no loose legacy variables shifts the reading of its
registered locals beneath the new syntactic binders. -/
theorem readScopedExpr?_liftSpec
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {term : KExpr .anon} {source : VExpr β} {depth shift : UInt64}
    (bound : depth.toNat + term.size < UInt64.size)
    (reading : readScopedExpr? resolve locals term depth.toNat = some source) :
    readScopedExpr? resolve locals (KExpr.liftSpec term shift depth)
      (depth.toNat + shift.toNat) = some (source.liftN shift.toNat depth.toNat) := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at reading
      split at reading
      next inScope =>
        cases reading
        have below : ¬ index ≥ depth := by
          simp only [UInt64.le_iff_toNat_le]; omega
        simp [KExpr.liftSpec, below, readScopedExpr?, show index.toNat <
          depth.toNat + shift.toNat by omega, VExpr.liftN, liftVar, inScope]
      · contradiction
  | fvar id name info =>
      rw [readScopedExpr?] at reading
      obtain ⟨index, found, reading⟩ := Option.map_eq_some_iff.mp reading
      cases reading
      simp only [KExpr.liftSpec, readScopedExpr?, found, Option.map_some, VExpr.liftN, liftVar,
        Nat.not_lt.mpr (Nat.le_add_right depth.toNat index), if_false]
      congr 2
      omega
  | sort _ _ | nat _ _ _ => cases reading; rfl
  | const id levels info =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      cases reading
      simp [KExpr.liftSpec, readScopedExpr?, resolved, VExpr.liftN]
  | str value _ _ =>
      rw [readString?_liftN reading]
      exact reading
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, rfl⟩ := readScopedExpr?_let_parts reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bReads)
      simp only [next] at bodyOut
      simp [KExpr.liftSpec, hA (by omega) aReads, hv (by omega) vReads,
        VExpr.liftN_inst_hi, show depth.toNat + shift.toNat + 1 =
          depth.toNat + 1 + shift.toNat by omega, bodyOut]
  | app fn arg info hf ha =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.liftSpec, hf (by omega) fReads, ha (by omega) aReads, VExpr.liftN]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readScopedExpr?] at reading
      obtain ⟨A, domainReads, reading⟩ := bind_success reading
      obtain ⟨B, bodyReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bodyReads)
      simp only [next] at bodyOut
      simp [KExpr.liftSpec, hd (by omega) domainReads, VExpr.liftN,
        show depth.toNat + shift.toNat + 1 = depth.toNat + 1 + shift.toNat by omega,
        bodyOut]
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.liftSpec, resolved, ih (by omega) valueReads, VExpr.liftN]

/-- Removing one syntactic binder agrees with model substitution, including
arguments that contain registered locals and their own nested binders. -/
theorem readScopedExpr?_substSpec
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body arg : KExpr .anon} {source argument : VExpr β} {depth : UInt64}
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (argBound : arg.size < UInt64.size)
    (bodyReads : readScopedExpr? resolve locals body (depth.toNat + 1) = some source)
    (argReads : readScopedExpr? resolve locals arg = some argument) :
    readScopedExpr? resolve locals (KExpr.substSpec body arg depth) depth.toNat =
      some (source.inst argument depth.toNat) := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at bodyReads
      split at bodyReads
      next inScope =>
        cases bodyReads
        by_cases equal : index = depth
        · subst index
          simp only [KExpr.substSpec, beq_self_eq_true, if_true, VExpr.inst, VExpr.instVar,
            Nat.lt_irrefl, if_false]
          simpa only [UInt64.toNat_zero, Nat.zero_add] using
            (readScopedExpr?_liftSpec (depth := 0) (shift := depth)
              (by simpa using argBound) argReads)
        · have smaller : index.toNat < depth.toNat := by
            have : index.toNat ≠ depth.toNat := fun h => equal (UInt64.toNat_inj.mp h)
            omega
          have below : ¬ index > depth := by
            simp only [UInt64.lt_iff_toNat_lt]; omega
          simp [KExpr.substSpec, equal, below, readScopedExpr?, smaller,
            VExpr.inst, VExpr.instVar]
      · contradiction
  | fvar id name info =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨index, found, bodyReads⟩ := Option.map_eq_some_iff.mp bodyReads
      cases bodyReads
      have greater : depth.toNat < depth.toNat + 1 + index := by omega
      simp [KExpr.substSpec, readScopedExpr?, found, VExpr.inst, VExpr.instVar,
        Nat.not_lt.mpr (by omega : depth.toNat ≤ depth.toNat + 1 + index),
        Nat.ne_of_gt greater, show depth.toNat + 1 + index - 1 = depth.toNat + index by omega]
  | sort _ _ | nat _ _ _ => cases bodyReads; rfl
  | const id levels info =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨ref, resolved, bodyReads⟩ := bind_success bodyReads
      cases bodyReads
      simp [KExpr.substSpec, readScopedExpr?, resolved, VExpr.inst]
  | str value _ _ =>
      rw [readString?_inst bodyReads]
      exact bodyReads
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, rfl⟩ := readScopedExpr?_let_parts bodyReads
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bReads)
      simp only [next] at bodyOut
      simp [KExpr.substSpec, hA (by omega) aReads, hv (by omega) vReads,
        VExpr.inst0_inst_hi, bodyOut]
  | app fn value info hf ha =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨f, fReads, bodyReads⟩ := bind_success bodyReads
      obtain ⟨a, aReads, bodyReads⟩ := bind_success bodyReads
      cases bodyReads
      simp only [KExpr.size] at bound
      simp [KExpr.substSpec, hf (by omega) fReads, ha (by omega) aReads, VExpr.inst]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨A, domainReads, bodyReads⟩ := bind_success bodyReads
      obtain ⟨B, innerReads, reading⟩ := bind_success bodyReads
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using innerReads)
      simp only [next] at bodyOut
      simp [KExpr.substSpec, hd (by omega) domainReads, bodyOut, VExpr.inst]
  | prj id index value info ih =>
      rw [readScopedExpr?] at bodyReads
      obtain ⟨ref, resolved, bodyReads⟩ := bind_success bodyReads
      obtain ⟨value, valueReads, bodyReads⟩ := bind_success bodyReads
      cases bodyReads
      simp only [KExpr.size] at bound
      simp [KExpr.substSpec, resolved, ih (by omega) valueReads, VExpr.inst]

/-- The actual memoized, interned walker inherits the structural substitution
reading under finite collision freedom and bounds excluding index overflow. -/
theorem subst_readScopedExpr?
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body arg : KExpr .anon} {source argument : VExpr β} {table : InternTable .anon}
    (bodyConstructed : body.Constructed) (argConstructed : arg.Constructed)
    (bodyBound : body.size + 1 < UInt64.size) (argBound : arg.size < UInt64.size)
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.SubstReach arg body 0 term)
    (bodyReads : readScopedExpr? resolve locals body 1 = some source)
    (argReads : readScopedExpr? resolve locals arg = some argument) :
    readScopedExpr? resolve locals (subst body arg 0 table).1 = some (source.inst argument) ∧
      (subst body arg 0 table).2.WF := by
  obtain ⟨result, coherent, _⟩ := subst_spec faithful bodyConstructed argConstructed
    (by simpa using (show body.size < UInt64.size by omega)) argBound
    (fun _ h => Or.inr h) coherent (fun _ h => Or.inl h)
  refine ⟨?_, coherent⟩
  rw [result]
  exact readScopedExpr?_substSpec (depth := 0) (by simpa using bodyBound)
    argBound bodyReads argReads

/-- Full-mode application takes a syntactic Pi, infers its argument, and
compares the inferred argument type with the domain. Eager markers are outside
this trace; the comparison and substitution states are the actual ones. -/
structure ApplicationInferenceTrace (fuel : Nat) (before : TcState .anon)
    (fn arg : KExpr .anon) where
  name : Mode.anon.F Name
  bi : Mode.anon.F Lean.BinderInfo
  domain : KExpr .anon
  codomain : KExpr .anon
  info : ExprInfo .anon
  functionState : TcState .anon
  argumentType : KExpr .anon
  argumentState : TcState .anon
  comparedState : TcState .anon
  functionRun : RecM.infer fn (methodsN fuel) before =
    .ok (.all name bi domain codomain info) functionState
  argumentRun : RecM.infer arg (methodsN fuel) functionState = .ok argumentType argumentState
  ordinary : TcM.isEagerReduce arg argumentState = .ok false argumentState
  compareRun : RecM.isDefEq argumentType domain (methodsN fuel) argumentState =
    .ok true comparedState
  contextPreserved : functionState.lctx = before.lctx

/-- Inverting the successful production branch reaches its exact interned
codomain substitution after the real argument check. -/
theorem ApplicationInferenceTrace.output_state {fuel : Nat} {before after : TcState .anon}
    {fn arg result : KExpr .anon} {info : ExprInfo .anon}
    (trace : ApplicationInferenceTrace fuel before fn arg)
    (accepted : RecM.inferUncached RecM.inferCall false (.app fn arg info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (subst trace.codomain arg 0 trace.comparedState.env.intern).1 ∧
      after = {trace.comparedState with env := {trace.comparedState.env with
        intern := (subst trace.codomain arg 0 trace.comparedState.env.intern).2}} := by
  change (RecM.inferUncached RecM.inferCall false (.app fn arg info)).run
    (methodsN (fuel + 1)) before = .ok result after at accepted
  unfold RecM.inferUncached at accepted
  simp only [ReaderT.run_bind] at accepted
  change EStateM.bind (RecM.infer fn (methodsN fuel)) _ before = _ at accepted
  rw [EStateM.bind, trace.functionRun] at accepted
  change EStateM.bind (RecM.infer arg (methodsN fuel)) _ trace.functionState = _ at accepted
  rw [EStateM.bind, trace.argumentRun] at accepted
  change EStateM.bind (TcM.isEagerReduce arg) _ trace.argumentState = _ at accepted
  rw [EStateM.bind, trace.ordinary] at accepted
  change EStateM.bind (RecM.isDefEq trace.argumentType trace.domain (methodsN fuel))
    _ trace.argumentState = _ at accepted
  rw [EStateM.bind, trace.compareRun] at accepted
  cases accepted
  exact ⟨rfl, rfl⟩

theorem ApplicationInferenceTrace.output {fuel : Nat} {before after : TcState .anon}
    {fn arg result : KExpr .anon} {info : ExprInfo .anon}
    (trace : ApplicationInferenceTrace fuel before fn arg)
    (accepted : RecM.inferUncached RecM.inferCall false (.app fn arg info)
      (methodsN (fuel + 1)) before = .ok result after) :
    result = (subst trace.codomain arg 0 trace.comparedState.env.intern).1 :=
  (trace.output_state accepted).1

end Ix.Kernel.Consistency
