import Compilatrix.Own.Plain.Proof.Call
import Compilatrix.Own.Plain.Proof.Frames
import Compilatrix.Own.Plain.Proof.TailCall

/-! Concrete non-tail call composition: copy argument tokens, suspend the
caller roots, invoke the smaller-clock hypothesis, and restore the caller
from successful denotation preservation before running its continuation. -/

set_option autoImplicit false
namespace Compilatrix.Own.Plain
open Rc
open Compilatrix.Sem (Result)

theorem call_bind_refines {F : Fir.Program} {k : Nat}
    (domain : programDomain F = true) (smaller : ∀ j, j < k → AtClock F j)
    {H : Heap} {external : Nat → Nat} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {joins : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry}
    (state : State (signatures F) H external live ρf ρo owned joins Jf Jo)
    (x : Fir.Var) (f : Fir.FunId) (args : List Fir.Arg) (c : Fir.Code)
    (fresh : x ∉ live) (scope : args.all (argIn live) = true) (callee : f < F.size)
    (next : ∀ {H' : Heap} {v : RVal} {w : Fir.Val},
      State (signatures F) H' external (live ++ [x]) (ρf.insert x w) (ρo.insert x v)
        (owned ++ [v]) joins Jf Jo →
      ResultRel H' external (Fir.eval F k (ρf.insert x w) Jf c)
        (eval (Program.canonical F) k (ρo.insert x v) Jo H' (lowerCode (live ++ [x]) joins c))) :
    ResultRel H external (Fir.eval F k ρf Jf (.bind x (.call f args) c))
      (eval (Program.canonical F) k ρo Jo H (lowerCode live joins (.bind x (.call f args) c))) := by
  obtain ⟨vs, ws, hvo, hwf, hdargs⟩ := args_den state.env args scope
  obtain ⟨Hcopy, hcopy, hbcopy, hp⟩ := copies_sound ρo H args state.counts
    (argsOwned_of_scope state.env state.roots scope) hvo
  have hcall := call_of_smaller_clocks domain smaller callee
    (dens_transport hdargs (fun root _ => hp root)) (balance_hold.mp hbcopy)
  rw [Fir.eval_bindCall, hwf]
  rw [lowerCode, eval_actionPrefix, hcopy]
  simp only [Result.ofOption, Result.bind_ok]
  rw [eval_bindCall, hvo]
  simp only [Result.ofOption, Result.bind_ok]
  apply ResultRel.bind_frame hcall
  intro w v H' hd hb hext
  obtain ⟨resumed, preserved⟩ := state.resume x fresh hp hd hb hext
  exact (next resumed).preheap preserved

end Compilatrix.Own.Plain
