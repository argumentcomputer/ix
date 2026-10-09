import Compilatrix.Own.Plain.Proof.Admission
import Compilatrix.Own.Plain.Proof.State
import Compilatrix.Own.Plain.Proof.ResultCompose
import Compilatrix.Fir.Proof.Unfold

/-! Smaller-clock call step for the eventual strong induction. Its induction
hypothesis is local proof infrastructure, not a checker acceptance condition. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

def AtClock (F : Fir.Program) (k : Nat) : Prop :=
  ∀ {H : Heap} {external : Nat → Nat} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {joins : Joins}
    {Jf : List Fir.JEntry} {Jo : List JEntry} (c : Fir.Code),
    State (signatures F) H external live ρf ρo owned joins Jf Jo →
    scopeOk (signatures F) live (stackArities Jf) c = true →
    ResultRel H external (Fir.eval F k ρf Jf c)
      (eval (Program.canonical F) k ρo Jo H (lowerCode live joins c))

theorem call_of_smaller_clocks {F : Fir.Program} {k : Nat}
    (domain : programDomain F = true) (ih : ∀ j, j < k → AtClock F j)
    {f : Fir.FunId} (hf : f < F.size) {H : Heap} {external : Nat → Nat}
    {vs : List RVal} {ws : List Fir.Val} (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hb : Balance H external vs) :
    ResultRel H external (Fir.evalCall F k f ws)
      (evalCall (Program.canonical F) k f vs H) := by
  cases hfd : F.fun? f with
  | none =>
    rw [Fir.evalCall_eq, hfd]
    exact .stuck
  | some fd =>
    rw [Fir.evalCall_eq, hfd, canonical_call hfd]
    simp only [Result.ofOption, Result.bind_ok, Fir.callFun, callFun]
    obtain ⟨_, freshParams, scopeBody⟩ := programDomain_function domain hf hfd
    by_cases hl : ws.length = fd.params.length
    · have hl' : vs.length = fd.params.length := hd.length.trans hl
      simp only [hl, hl', ↓reduceIte]
      refine ResultRel.later fun j hj => ?_
      exact ih j hj fd.body
        (state_entry (signatures F) H external (fd.params.map (·.1)) vs ws hd
          (by simpa using hl') freshParams hb) scopeBody
    · have hl' : ¬vs.length = fd.params.length := by rw [hd.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      exact .stuck


end Compilatrix.Own.Plain
