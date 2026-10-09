import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.CtorAdmission

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt.Proof

theorem envCtorOk_empty (tables : Rt.Lower.Tables) : EnvCtorOk tables .leaf := by
  intro x value lookup
  cases lookup

theorem EnvCtorOk.bind {tables : Rt.Lower.Tables} {env : Own.Env}
    (before : EnvCtorOk tables env) (x : Nat) {value : Own.RVal}
    (compatible : ValueCtorOk tables value) : EnvCtorOk tables (env.insert x value) := by
  intro y actual lookup
  rw [Src.NatMap.get?_insert] at lookup
  split at lookup
  · cases lookup
    exact compatible
  · exact before y actual lookup

theorem EnvCtorOk.arg {tables : Rt.Lower.Tables} {env : Own.Env}
    (before : EnvCtorOk tables env) {arg : Fir.Arg} {value : Own.RVal}
    (evaluation : Own.evalArg env arg = some value) : ValueCtorOk tables value := by
  cases arg with
  | var x => exact before x value evaluation
  | lit l => cases evaluation; trivial
  | erased => cases evaluation; trivial

theorem EnvCtorOk.args {tables : Rt.Lower.Tables} {env : Own.Env}
    (before : EnvCtorOk tables env) :
    ∀ {args : List Fir.Arg} {values : List Own.RVal}, Own.evalArgs env args = some values →
      ∀ value ∈ values, ValueCtorOk tables value
  | [], values, evaluation => by
    cases evaluation
    simp
  | arg :: args, values, evaluation => by
    cases head : Own.evalArg env arg with
    | none => simp [Own.evalArgs, head] at evaluation
    | some first =>
      cases tail : Own.evalArgs env args with
      | none => simp [Own.evalArgs, tail] at evaluation
      | some rest =>
        simp only [Own.evalArgs, head, tail, Option.some.injEq] at evaluation
        subst values
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact before.arg head
        · exact before.args tail value member

theorem EnvCtorOk.bindAll {tables : Rt.Lower.Tables} :
    ∀ {env : Own.Env} (params : List Nat) (values : List Own.RVal),
      EnvCtorOk tables env → (∀ value ∈ values, ValueCtorOk tables value) →
        EnvCtorOk tables (Own.bindAll env params values)
  | _, [], _, before, _ => before
  | _, _ :: _, [], before, _ => before
  | _, x :: params, value :: values, before, compatible =>
    EnvCtorOk.bindAll params values (before.bind x (compatible value (by simp)))
      (fun v member => compatible v (by simp [member]))

theorem HeapCtorOk.field {tables : Rt.Lower.Tables} {heap : Own.Heap}
    (compatible : HeapCtorOk tables heap) {location refs : Nat} {mode : Own.OMode}
    {body : Own.Body} (cell : heap.cell? location = some (.live refs mode body))
    {index : Nat} {value : Own.RVal} (field : body.fields[index]? = some value) :
    ValueCtorOk tables value :=
  (compatible location refs mode body cell).2.2 value (List.mem_of_getElem? field)

/-- Source primitive evaluation produces a scalar or one of the admitted
boolean immediates; it does not manufacture an unchecked constructor row. -/
theorem primitive_ctor_compatible {P : Cfg.Program} {t e : Lir.Word}
    (lowering : (Rt.Lower.tables P).bools = some (t, e))
    {op : Lam.Prim} {values : List Own.RVal} {value : Own.RVal}
    (effect : Own.primResult (ownTables (Rt.Lower.tables P)) op values = .ok value) :
    ValueCtorOk (Rt.Lower.tables P) value := by
  unfold Own.primResult at effect
  split at effect
  · split at effect
    · cases effect
      trivial
    · exact bool_ctor_compatible lowering effect
    · cases effect
  · cases effect








end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
