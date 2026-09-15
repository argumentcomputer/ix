/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Application
import Ix.Kernel.Verify.Consistency.StructuralWhnfEntry

/-! Explicit-let WHNF uses production substitution. Its scoped reading
is unchanged, so later reductions retain the original annotated term. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

structure LetStepPlan (before : TcState .anon) (source : KExpr .anon) where
  name : Mode.anon.F Name
  domain : KExpr .anon
  value : KExpr .anon
  body : KExpr .anon
  nonDep : Bool
  info : ExprInfo .anon
  sourceEq : source = .letE name domain value body nonDep info
  bodyConstructed : body.Constructed
  valueConstructed : value.Constructed
  bodyBound : body.size + 1 < UInt64.size
  valueBound : value.size < UInt64.size
  faithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
    KExpr.SubstReach value body 0 term

namespace LetStepPlan

variable {before : TcState .anon} {source : KExpr .anon}

def output (plan : LetStepPlan before source) : KExpr .anon × InternTable .anon :=
  subst plan.body plan.value 0 before.env.intern

def result (plan : LetStepPlan before source) : KExpr .anon := plan.output.1

def after (plan : LetStepPlan before source) : TcState .anon :=
  {before with env := {before.env with intern := plan.output.2}}

theorem entry (plan : LetStepPlan before source) : StructuralWhnfEntry source :=
  plan.sourceEq ▸ .letE _ _ _ _ _ _

theorem run (plan : LetStepPlan before source) (methods : Methods .anon) (flags : WhnfFlags) :
    (RecM.whnfCoreWithFlagsStep source flags).run methods before = .ok (.next plan.result) plan.after := by
  simp only [plan.sourceEq]
  rfl

theorem reading {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {term : AExpr β} (plan : LetStepPlan before source)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals plan.result = some term.erase ∧ plan.after.env.intern.WF := by
  rw [plan.sourceEq] at sourceReading
  obtain ⟨_, value, body, _, valueReads, bodyReads, same⟩ := readScopedExpr?_let_parts sourceReading
  obtain ⟨reads, preserved⟩ := subst_readScopedExpr? plan.bodyConstructed plan.valueConstructed
    plan.bodyBound plan.valueBound coherent plan.faithful bodyReads valueReads
  exact ⟨same ▸ reads, preserved⟩

end LetStepPlan

namespace LetStepSource

def selected : KExpr .anon → Bool
  | .letE .. => true
  | _ => false

def parts : KExpr .anon → KExpr .anon × KExpr .anon
  | .letE _ _ value body _ _ => (body, value)
  | source => (source, source)

def output (source : KExpr .anon) (before : TcState .anon) : KExpr .anon × InternTable .anon :=
  subst (parts source).1 (parts source).2 0 before.env.intern

def after (source : KExpr .anon) (before : TcState .anon) : TcState .anon :=
  {before with env := {before.env with intern := (output source before).2}}

structure Resources (source : KExpr .anon) (before : TcState .anon) : Prop where
  bodyConstructed : (parts source).1.Constructed
  valueConstructed : (parts source).2.Constructed
  bodyBound : (parts source).1.size + 1 < UInt64.size
  valueBound : (parts source).2.size < UInt64.size
  faithful : KExpr.CollisionFree fun term => before.env.intern.ExprSupport term ∨
    KExpr.SubstReach (parts source).2 (parts source).1 0 term

theorem selected_entry {source : KExpr .anon} (chosen : selected source = true) : StructuralWhnfEntry source := by
  cases source with
  | letE name domain value body nonDep info => exact .letE name domain value body nonDep info
  | _ => cases chosen

def construct {source : KExpr .anon} {before : TcState .anon}
    (chosen : selected source = true) (resources : Resources source before) :
    {plan : LetStepPlan before source // plan.output = output source before} := by
  cases source with
  | letE name domain value body nonDep info =>
      exact ⟨⟨name, domain, value, body, nonDep, info, rfl, resources.bodyConstructed,
        resources.valueConstructed, resources.bodyBound, resources.valueBound, resources.faithful⟩, rfl⟩
  | _ => cases chosen

theorem construct_result {source : KExpr .anon} {before : TcState .anon}
    (chosen : selected source = true) (resources : Resources source before) :
    (construct chosen resources).1.result = (output source before).1 :=
  congrArg Prod.fst (construct chosen resources).2

theorem construct_after {source : KExpr .anon} {before : TcState .anon}
    (chosen : selected source = true) (resources : Resources source before) :
    (construct chosen resources).1.after = after source before :=
  congrArg (fun result : KExpr .anon × InternTable .anon =>
    {before with env := {before.env with intern := result.2}}) (construct chosen resources).2

end LetStepSource

end Ix.Kernel.Consistency
