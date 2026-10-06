import Ix.CompileCert.DivModValues

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- An executable receipt tree for the binder-free monomorphic recurrence
grammar. Each constant node binds the actual source/target lookup and an
identity or admitted theorem receipt; free-variable types are not erased
from the immutable equation syntax. -/
inductive CheckedNatEquation (source target : Kernel.Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Kernel.Expr → Type
  | constant (name : Kernel.Name)
      (receipt : CheckedCanonicalValue source target names name (certificates name) (levels name)) :
      CheckedNatEquation source target names certificates levels (.const name [])
  | variable (index : Nat) (type : Kernel.Expr) :
      CheckedNatEquation source target names certificates levels (.fvar index type)
  | application {function argument : Kernel.Expr}
      (functionReceipt : CheckedNatEquation source target names certificates levels function)
      (argumentReceipt : CheckedNatEquation source target names certificates levels argument) :
      CheckedNatEquation source target names certificates levels (.app function argument)

def readCheckedNatEquation (source target : Kernel.Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (expression : Kernel.Expr) :
    Option (CheckedNatEquation source target names certificates levels expression) :=
  match expression with
  | .const name [] => (readCheckedCanonicalValue source target names name (certificates name) (levels name)).map
      (CheckedNatEquation.constant name)
  | .fvar index type => some (.variable index type)
  | .app function argument => do
      let functionReceipt ← readCheckedNatEquation source target names certificates levels function
      let argumentReceipt ← readCheckedNatEquation source target names certificates levels argument
      some (.application functionReceipt argumentReceipt)
  | _ => none

/-- Paired actual annotated readings, with equality only at interpretation.
This does not assert syntactic annotation equality or use a public Denotes
equation as a substitute for the strong-model carrier. -/
theorem CheckedNatEquation.readings {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names certificates : Kernel.Name → Kernel.Name}
    {levels : Kernel.Name → Kernel.Level}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {expression : Kernel.Expr} (receipt : CheckedNatEquation source target names certificates levels expression)
    (universes : Kernel.Name → Nat) (depth : Nat) :
    ∃ sourceAnnotation targetAnnotation,
      denoteMeta (association.modelCore sourceModel.internal.base2 targetModel).base.acval source universes depth expression =
        some sourceAnnotation ∧
      denoteMeta targetModel.internal.base2.acval target universes depth expression = some targetAnnotation ∧
      ∀ ρ : Nat → V, interp V ρ sourceAnnotation = interp V ρ targetAnnotation := by
  induction receipt with
  | constant name receipt =>
    have rightParams : receipt.value.endpoints.rightEntry.toConstantVal.levelParams = [] :=
      List.eq_nil_of_length_eq_zero receipt.value.endpoints.rightArity.symm
    have sourceRead := denoteMeta_const
      (acval := (association.modelCore sourceModel.internal.base2 targetModel).base.acval)
      (φ := universes) (d := depth) (us := []) receipt.value.sourceLookup
      (by simp only [receipt.value.sourceMonomorphic, List.length_nil])
    have targetRead := denoteMeta_const (acval := targetModel.internal.base2.acval)
      (φ := universes) (d := depth) (us := []) receipt.value.endpoints.rightLookup
      receipt.value.endpoints.rightArity
    simp only [receipt.value.sourceMonomorphic, rightParams, Kernel.Level.substFn] at sourceRead targetRead
    exact ⟨_, _, sourceRead, targetRead, fun ρ => receipt.value.value_eq association sourceModel.internal.base2 targetModel universes ρ⟩
  | «variable» index type =>
    exact ⟨_, _, denoteMeta_fvar _ depth index type, denoteMeta_fvar _ depth index type, fun _ => rfl⟩
  | application functionReceipt argumentReceipt functionIH argumentIH =>
    obtain ⟨sourceFunction, targetFunction, sourceFunctionRead, targetFunctionRead, functionEq⟩ := functionIH
    obtain ⟨sourceArgument, targetArgument, sourceArgumentRead, targetArgumentRead, argumentEq⟩ := argumentIH
    refine ⟨.app sourceFunction sourceArgument, .app targetFunction targetArgument, ?_, ?_, ?_⟩
    · simp only [denoteMeta_app, sourceFunctionRead, sourceArgumentRead]
      rfl
    · simp only [denoteMeta_app, targetFunctionRead, targetArgumentRead]
      rfl
    · intro ρ
      simp only [interp_app, functionEq ρ, argumentEq ρ]

end Ix.CompileCert
