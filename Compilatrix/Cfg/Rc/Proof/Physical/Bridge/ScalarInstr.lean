import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarPrimitives
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarPure
import Compilatrix.Own.Plain.Proof.RhsShape

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

/-- The RHS cases whose native execution leaves physical memory unchanged.
A copy can carry a dynamic address; this predicate is about the operation. -/
def PureRhs : Own.Rhs → Prop
  | .fir (.arg _) | .fir (.prim ..) => True
  | .alloc c _ _ => c.fieldless = true
  | _ => False

theorem pure_effect {T : Tables} {rhs : Own.Rhs} (pureRhs : PureRhs rhs)
    {ρ : Own.Env} {H H' : Own.Heap} {value : Own.RVal} {n : Nat}
    (bounded : Own.Plain.EnvBounded n ρ)
    (effect : Own.evalRhs .rc (ownTables T) ρ H rhs = .ok (value, H')) :
    H' = H ∧ Own.Plain.Bounded n value := by
  match rhs, pureRhs with
  | .fir (.arg a), _ =>
    obtain ⟨same, evaluated⟩ := evalRhs_arg (T := ownTables T) effect
    exact ⟨same, bounded.arg evaluated⟩
  | .fir (.prim op args), _ =>
    obtain ⟨same, values, _, result⟩ := evalRhs_prim effect
    exact ⟨same, Own.Plain.prim_bounded _ n result⟩
  | .alloc c args kind, fieldless =>
    change c.fieldless = true at fieldless
    have oldEffect : Own.evalRhs .immortal (ownTables T) ρ H (.alloc c args kind) =
        .ok (value, H') := by simpa only [Own.evalRhs, fieldless, ↓reduceIte] using effect
    obtain ⟨values, _, _, ⟨_, rfl, rfl⟩ | ⟨notFieldless, _⟩⟩ := evalRhs_alloc oldEffect
    · exact ⟨rfl, trivial⟩
    · simp [fieldless] at notFieldless

  | .fir (.call ..), impossible | .fir (.ctor ..), impossible | .fir (.proj ..), impossible
  | .proj .., impossible => exact False.elim impossible

theorem instr_sim {T : Tables} (hT : BoolsOk T) {f : Fir.FunId} {lp : Lir.Program} {ctx : Word}
    {D : Nat → Prop} {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C)
    (hpow : lp.funcs[T.natPow]? = some Procs.natPow) (hgcd : lp.funcs[T.natGcd]? = some Procs.natGcd)
    {st st' : St} {x : Nat} {r : Own.Rhs} (pureRhs : PureRhs r)
    (hrun : (instr f T (.bind x r)).run st = .ok (true, st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hlive : ∀ y ∈ Cfg.Check.rhsVars r, ¬ D y) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x r := by
  match r, pureRhs, hrun, hlive with
  | .fir (.arg a), _, hrun, hlive =>
    rcases withOperands_run hrun with ⟨las, hops, _, hk⟩ | ⟨_, impossible, _⟩
    · obtain ⟨la, rfl, hop⟩ := operands_one hops
      simp only [assign_run, Except.ok.injEq, Prod.mk.injEq, true_and] at hk
      subst hk
      exact arg_sim hF hH hC ho hx hop (liveArgs_of hlive a (by simp))
    · cases impossible
  | .fir (.prim op args), _, hrun, hlive =>
    rcases withOperands_run hrun with ⟨las, hops, _, hk⟩ | ⟨_, impossible, _⟩
    · exact primitive_sim hT hF hH hpow hgcd hk hC hl ho hsup hx hops (liveArgs_of hlive)
    · cases impossible
  | .alloc c args kind, fieldless, hrun, hlive =>
    rcases withOperands_run hrun with ⟨las, hops, _, hk⟩ | ⟨_, impossible, _⟩
    · exact fieldless_alloc_sim hF hH fieldless hk hC hl ho hsup hx hops (liveArgs_of hlive)
    · cases impossible

  | .fir (.call ..), impossible, _, _ | .fir (.ctor ..), impossible, _, _
  | .fir (.proj ..), impossible, _, _ | .proj .., impossible, _, _ => exact False.elim impossible



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
