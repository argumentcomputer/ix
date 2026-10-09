import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarInstr
import Compilatrix.Cfg.Rc.Proof.Physical.Admission
import Compilatrix.Cfg.Rc.Proof.CallStep

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Cfg.Rc Compilatrix.Cfg.Rc.Native.Spec

theorem pure_unreserved (limit x : Nat) {rhs : Own.Rhs} (pureRhs : PureRhs rhs) :
    reserved limit (.bind x rhs) = false := by
  match rhs, pureRhs with
  | .fir (.arg _), _ | .fir (.prim ..), _ | .alloc .., _ => rfl
  | .fir (.call ..), impossible | .fir (.ctor ..), impossible | .fir (.proj ..), impossible
  | .proj .., impossible => exact False.elim impossible

/-- Both destination and temporary bounds follow from actual checked source
layout and the consuming receipt, including unused original variables. -/
theorem checked_binding_bounds {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    {source : Cfg.Frame} {sourceFd : Fir.Fun} {actualFd : Cfg.Fun}
    (sourceLookup : F.fun? source.fn = some sourceFd)
    (actualLookup : (consumed P pairs).fun? source.fn = some actualFd)
    {env : Own.Env} {joins : List Own.Plain.JEntry} {x : Nat} {rhs : Fir.Rhs}
    {cont : Own.Plain.Code} (atBind : At F P source env joins (.bind x rhs cont))
    (pureRhs : PureRhs (Own.immRhs rhs)) :
    sourceFd.vars ≤ Rt.Proof.supOf actualFd ∧ x < sourceFd.vars := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, range, layout, cursor,
    _, _, _, _⟩ := atBind
  have size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have rangeP : source.fn < P.base.size := by rw [size]; exact range
  obtain ⟨original, actual, lookup', consume, actualLookup'⟩ := consumed_entry consuming rangeP
  have eqOriginal : original = fd := Option.some.inj (lookup'.symm.trans lookup)
  have eqActual : actual = actualFd := Option.some.inj (actualLookup'.symm.trans actualLookup)
  subst original
  subst actual
  refine ⟨checked_consumed_sup checked range sourceLookup lookup consume, ?_⟩
  obtain ⟨term, blockLookup⟩ := Cfg.Proof.impl_head layout
  have bound := functionBounds_block (checked_source_bounds checked range sourceLookup lookup) blockLookup
  have member : Cfg.Instr.bind x (Own.immRhs rhs) ∈
      acc.reverse ++ Cfg.Proof.spine (skeleton P.base.size first (.bind x rhs cont)) := by
    simp [skeleton, Cfg.Proof.spine]
  have binding := List.all_eq_true.mp bound.2.1 _ member
  have ordinary := pure_unreserved P.base.size x pureRhs
  simp only [instrBound, ordinary, Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq] at binding
  exact binding.1



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
