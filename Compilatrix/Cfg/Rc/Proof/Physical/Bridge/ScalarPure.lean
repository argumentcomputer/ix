import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarSem
import Compilatrix.Rt.Proof.OpsProj
import Compilatrix.Rt.Proof.OpsAlloc

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

theorem arg_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {x : Nat} {a : Fir.Arg} {la : Lir.Arg}
    (hC : Ext C { st with acc := [Lir.Stmt.assign x (.arg la)].reverse ++ st.acc, fresh := st.fresh }) (ho : Open st)
    (hx : x < sup) (hop : operand f a = .ok (some la)) (hlive : LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur)
      ([Lir.Stmt.assign x (.arg la)].reverse ++ st.acc).length x (.fir (.arg a)) := by
  apply straight_sim hF hH hC ho (by simp [Lir.Stmt.isCall])
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, hv⟩ := evalRhs_arg (T := ownTables T) hr
  obtain ⟨w, hw, hrel, -⟩ := operand_rel hρ hop hlive hv
  exact ⟨rfl, ρl.insert x w, by simp only [lir_eval, hw], hρ.insert hx hrel⟩

theorem fieldless_alloc_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {c : Fir.CtorInfo} {las : List Lir.Arg}
    {as : List Fir.Arg} {κ : Own.Kind}
    (fieldless : c.fieldless = true)
    (hrun : (Lower.alloc f T x c las).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st) (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some las))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x (.alloc c as κ) := by
  obtain ⟨hnat, hlen, hkey, hnx, htag, hcase⟩ := alloc_run hrun
  have hok : CtorOk T c := ⟨hkey, hnat, htag⟩
  rcases hcase with ⟨hfl, rfl⟩ | ⟨hfl, hmax, rfl⟩
  · apply straight_sim hF hH hC ho (by simp [Lir.Stmt.isCall])
    intro P H ρ ρl mem v H' hρ hr
    have pureEffect : Own.evalRhs .immortal (ownTables T) ρ H (.alloc c as κ) = .ok (v, H') := by
      simpa only [Own.evalRhs, fieldless, ↓reduceIte] using hr
    obtain ⟨vs, hvs, hvlen, ⟨-, rfl, rfl⟩ | ⟨hfl', -⟩⟩ := evalRhs_alloc pureEffect
    · refine ⟨rfl, ρl.insert x (ctor0Word c.tag), by simp only [lir_eval], ?_⟩
      exact hρ.insert hx ⟨rfl, hok, hfl⟩
    · rw [hfl] at hfl'; cases hfl'
  · simp [fieldless] at hfl

end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
