import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorValues
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedOperands

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt.Proof

/-- Constructor compatibility is required only for values the native code may
read. A fused comparison can produce an omitted Bool even when its word was
not admitted by Lower.tables; its unique switch uses FusedDone instead. -/
def FusedCtorOk (tables : Rt.Lower.Tables) (omitted : Nat → Prop) (env : Own.Env) : Prop :=
  ∀ x value, env.get? x = some value → ¬ omitted x → ValueCtorOk tables value

theorem FusedCtorOk.empty {tables : Rt.Lower.Tables} {omitted : Nat → Prop} :
    FusedCtorOk tables omitted .leaf := by
  intro x value lookup
  cases lookup

theorem FusedCtorOk.of_full {tables : Rt.Lower.Tables} {omitted : Nat → Prop}
    {env : Own.Env} (compatible : EnvCtorOk tables env) : FusedCtorOk tables omitted env :=
  fun x value lookup _ => compatible x value lookup

theorem FusedCtorOk.bind {tables : Rt.Lower.Tables} {omitted : Nat → Prop} {env : Own.Env}
    (before : FusedCtorOk tables omitted env) (x : Nat) {value : Own.RVal}
    (compatible : ValueCtorOk tables value) : FusedCtorOk tables omitted (env.insert x value) := by
  intro y actual lookup live
  rw [Src.NatMap.get?_insert] at lookup
  split at lookup
  · cases lookup
    exact compatible
  · exact before y actual lookup live

theorem FusedCtorOk.bind_omitted {tables : Rt.Lower.Tables} {omitted : Nat → Prop} {env : Own.Env}
    (before : FusedCtorOk tables omitted env) {x : Nat} (omission : omitted x) (value : Own.RVal) :
    FusedCtorOk tables omitted (env.insert x value) := by
  intro y actual lookup live
  by_cases equal : y = x
  · subst y
    exact False.elim (live omission)
  · rw [Src.NatMap.get?_insert_ne _ _ equal] at lookup
    exact before y actual lookup live

theorem FusedCtorOk.arg {tables : Rt.Lower.Tables} {omitted : Nat → Prop} {env : Own.Env}
    (before : FusedCtorOk tables omitted env) {arg : Fir.Arg} {value : Own.RVal}
    (live : LiveArg omitted arg) (evaluation : Own.evalArg env arg = some value) :
    ValueCtorOk tables value := by
  cases arg with
  | var x => exact before x value evaluation (live x rfl)
  | lit l => cases evaluation; trivial
  | erased => cases evaluation; trivial

theorem FusedCtorOk.args {tables : Rt.Lower.Tables} {omitted : Nat → Prop} {env : Own.Env}
    (before : FusedCtorOk tables omitted env) :
    ∀ {args : List Fir.Arg} {values : List Own.RVal},
      (∀ arg ∈ args, LiveArg omitted arg) → Own.evalArgs env args = some values →
        ∀ value ∈ values, ValueCtorOk tables value
  | [], values, _, evaluation => by cases evaluation; simp
  | arg :: args, values, live, evaluation => by
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
        · exact before.arg (live arg (by simp)) head
        · exact before.args (fun a member => live a (by simp [member])) tail value member

theorem FusedCtorOk.bindAll {tables : Rt.Lower.Tables} {omitted : Nat → Prop} :
    ∀ {env : Own.Env} (params : List Nat) (values : List Own.RVal),
      FusedCtorOk tables omitted env → (∀ value ∈ values, ValueCtorOk tables value) →
        FusedCtorOk tables omitted (Own.bindAll env params values)
  | _, [], _, before, _ => before
  | _, _ :: _, [], before, _ => before
  | _, x :: params, value :: values, before, compatible =>
    FusedCtorOk.bindAll params values (before.bind x (compatible value (by simp)))
      (fun v member => compatible v (by simp [member]))

/-- Calls, including emitted RC markers and allocation wrappers, derive the
compatibility of all actual arguments from their real block membership. -/
theorem fused_call_ctor_args {tables : Rt.Lower.Tables} {function : Cfg.Fun} {env : Own.Env}
    (before : FusedCtorOk tables (Fused tables function) env)
    {index : Nat} {block : Cfg.Block} (blockLookup : function.blocks[index]? = some block)
    {x callee : Nat} {args : List Fir.Arg}
    (instruction : Cfg.Instr.bind x (.fir (.call callee args)) ∈ block.body)
    {values : List Own.RVal} (evaluation : Own.evalArgs env args = some values) :
    ∀ value ∈ values, ValueCtorOk tables value :=
  before.args (fused_call_live blockLookup instruction) evaluation









end IxCC.Cfg.Rc.Proof.Physical.Bridge
