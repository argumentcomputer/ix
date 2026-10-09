import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import Compilatrix.Cfg.Rc.Proof.Extend

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt.Rc.Procs

/-- Restrict actual target registers to an independently established lexical
subenvironment. Extra Cfg bindings do not become source-owned roots. -/
theorem FusedWords.restrict {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    {source saved : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses D bound source target)
    (sub : Cfg.Rc.EnvSub saved source) : FusedWords addresses D bound saved target := by
  exact ⟨fun lookup => related.dom (sub _ _ lookup),
    fun lookup live => related.word (sub _ _ lookup) live⟩

/-- The real lowered edge binds parameters over its current Cfg environment;
the lexical join body binds the same values over the selected saved map.
Its saved EnvSub witness, rather than token counts, relates the two maps. -/
theorem FusedWords.saved_bindAll {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    {source saved : Own.Env} {target : Lir.Env}
    (params : List Fir.Var) (values : List Own.RVal)
    (related : FusedWords addresses D bound (Own.bindAll source params values) target)
    (sub : Cfg.Rc.EnvSub saved source) :
    FusedWords addresses D bound (Own.bindAll saved params values) target :=
  related.restrict (Cfg.Proof.Sub.bindAll sub params values)



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
