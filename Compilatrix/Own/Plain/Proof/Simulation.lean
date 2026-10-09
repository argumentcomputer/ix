import Compilatrix.Own.Plain.Proof.CallBind
import Compilatrix.Own.Plain.Proof.Jump
import Compilatrix.Own.Plain.Proof.NonCall
import Compilatrix.Own.Plain.Proof.Values
import Compilatrix.Fir.Proof.Mono

/-! Whole-code induction for the canonical counted producer. The only
recursive execution premises are discharged by the lexicographic source
clock/code-and-join measure; heap observations and counts are derived by
the concrete operation lemmas. -/

set_option autoImplicit false
namespace Compilatrix.Own.Plain
open Rc
open Compilatrix.Sem (Result)

section
variable {F : Fir.Program} (domain : programDomain F = true) (pins : BoolPinsOk F)
variable {k : Nat} (smaller : ∀ j, j < k → AtClock F j)
include domain pins smaller

mutual
theorem eval_refines {H : Heap} {external : Nat → Nat} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {joins : Joins}
    (Jf : List Fir.JEntry) {Jo : List JEntry} (c : Fir.Code)
    (state : State (signatures F) H external live ρf ρo owned joins Jf Jo)
    (scope : scopeOk (signatures F) live (stackArities Jf) c = true) :
    ResultRel H external (Fir.eval F k ρf Jf c)
      (eval (Program.canonical F) k ρo Jo H (lowerCode live joins c)) := by
  match c with
  | .bind x r c' =>
    have parts : x ∉ live ∧ rhsIn (signatures F) live r = true ∧
        scopeOk (signatures F) (live ++ [x]) (stackArities Jf) c' = true := by
      simpa [scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨hx, hr, hc⟩ := parts
    by_cases call : ∃ f args, r = .call f args
    · obtain ⟨f, args, rfl⟩ := call
      have hs : (signatures F).lookup f = some args.length ∧ args.all (argIn live) = true := by
        simpa [rhsIn, Bool.and_eq_true] using hr
      obtain ⟨fd, hf, _, _⟩ := signatures_lookup hs.1
      apply call_bind_refines domain smaller state x f args c' hx hs.2 hf
      intro H' v w next
      exact eval_refines Jf c' next hc
    · have noncall : ∀ f args, r ≠ .call f args := fun f args h => call ⟨f, args, h⟩
      apply nonCall_refines state (Program.canonical F) k x r c' pins hx hr noncall
      intro w v H' next
      exact eval_refines Jf c' next hc
  | .jp j ps rec body c' =>
    simp only [scopeOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at scope
    obtain ⟨_, hf, hb, hc⟩ := scope
    rw [Fir.eval_jp, lowerCode, eval_jp]
    apply eval_refines _ c' (state.declare j ps rec body hf hb)
    simpa only [stackArities, List.map_cons] using hc
  | .jmp j args =>
    have hs : args.all (argIn live) = true := by
      have hscope : decide ((stackArities Jf).lookup j = some args.length) = true ∧
          args.all (argIn live) = true := by
        simpa only [scopeOk, Bool.and_eq_true] using scope
      exact hscope.2
    cases hl : Fir.lookupJ j Jf with
    | none => rw [Fir.eval_jmp, hl]; exact .stuck
    | some p =>
      obtain ⟨ef, restf⟩ := p
      obtain ⟨vs₀, ws, _, hw, _⟩ := args_den state.env args hs
      by_cases hlen : ws.length = ef.params.length
      · obtain ⟨captured, older, eo, resto, H', kept, vs, hparams, hcharged, hbody,
          entered, bodyScope, hlen', hsource, htarget, preserved⟩ :=
          jump_progress state hl hs hw hlen
        rw [hsource, htarget]
        unfold Fir.jumpTo jumpTo
        simp only [hlen, hlen', ↓reduceIte, hcharged, hbody]
        apply ResultRel.preheap (hv := preserved)
        cases charged : ef.charged with
        | true =>
          simp only [charged, ↓reduceIte]
          exact ResultRel.later fun j hj => smaller j hj ef.body entered bodyScope
        | false =>
          simp only [charged, Bool.false_eq_true, ↓reduceIte]
          have := Fir.jump_measure hl charged
          exact eval_refines (ef.after restf) ef.body entered bodyScope
      · rw [Fir.eval_jmp_of F k ρf Jf hl hw]
        simp only [Fir.jumpTo, hlen, ↓reduceIte]
        exact .stuck
  | .case x alts d =>
    have parts : x ∈ live ∧ scopeAlts (signatures F) live (stackArities Jf) alts = true ∧
        scopeOpt (signatures F) live (stackArities Jf) d = true := by
      simpa [scopeOk, Bool.and_eq_true, and_assoc] using scope
    obtain ⟨v, w, hvo, hwf, hd⟩ := state.env x parts.1
    rw [Fir.eval_case, hwf, lowerCode, eval_case, hvo]
    simp only [Result.ofOption, Result.bind_ok]
    cases hk : w.asCtor F.known with
    | none => exact .stuck
    | some p =>
      obtain ⟨key, fs⟩ := p
      obtain ⟨fields, hfields, _⟩ := (Values.asCtor_den F.known hd).1 key fs hk
      simp only [Program.canonical, hfields]
      exact evalAlts_refines Jf key alts d state parts.2.1 parts.2.2
  | .ret a =>
    exact return_refines (Program.canonical F) k ρf ρo Jf Jo H live joins a
      state.env state.roots state.counts scope
  | .tcall f args =>
    have hs : (signatures F).lookup f = some args.length ∧ args.all (argIn live) = true := by
      simpa [scopeOk, Bool.and_eq_true] using scope
    obtain ⟨fd, hf, _, _⟩ := signatures_lookup hs.1
    obtain ⟨H', vs, ws, _, _, hfRun, hoRun, hb, hd, hp⟩ :=
      tailCall_transfer (Program.canonical F) k ρf ρo Jf Jo H live joins f args
        state.env state.roots state.counts hs.2
    change Fir.eval F k ρf Jf (.tcall f args) = Fir.evalCall F k f ws at hfRun
    rw [hfRun, hoRun]
    exact (call_of_smaller_clocks domain smaller hf hd hb).preheap (ExternalPreserved.of_values hp)
  | .trap =>
    exact trap_refines (Program.canonical F) k ρf ρo Jf Jo H live joins state.roots state.counts
termination_by c.size + Fir.jweight Jf
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Fir.Code.size]; omega)
    | (simp only [Fir.Code.size, Fir.jweight, Fir.JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Fir.Code.size] at this ⊢; omega)

theorem evalAlts_refines {H : Heap} {external : Nat → Nat} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {joins : Joins}
    (Jf : List Fir.JEntry) {Jo : List JEntry} (key : Key.CtorKey)
    (alts : List Fir.Alt) (d : Option Fir.Code)
    (state : State (signatures F) H external live ρf ρo owned joins Jf Jo)
    (ha : scopeAlts (signatures F) live (stackArities Jf) alts = true)
    (hd : scopeOpt (signatures F) live (stackArities Jf) d = true) :
    ResultRel H external (Fir.evalAlts F k ρf Jf key alts d)
      (evalAlts (Program.canonical F) k ρo Jo H key (lowerAlts live joins alts) (lowerOpt live joins d)) := by
  match alts, d with
  | [], some c =>
    rw [Fir.evalAlts_nil]
    simp only [lowerAlts, lowerOpt]
    rw [evalAlts_nil]
    exact eval_refines Jf c state hd
  | [], none =>
    rw [Fir.evalAlts_nil]
    exact .stuck
  | .mk key' body :: rest, d =>
    have hs : scopeOk (signatures F) live (stackArities Jf) body = true ∧
        scopeAlts (signatures F) live (stackArities Jf) rest = true := by
      simpa only [scopeAlts, Bool.and_eq_true] using ha
    rw [Fir.evalAlts_cons]
    simp only [lowerAlts]
    rw [evalAlts_cons]
    split
    · exact eval_refines Jf body state hs.1
    · exact evalAlts_refines Jf key rest d state hs.2 hd
termination_by Fir.Code.altsSize alts + Fir.Code.optSize d + Fir.jweight Jf + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Fir.Code.altsSize, Fir.Code.optSize]
  all_goals first
    | omega
    | (have := Fir.Code.size_pos body; omega)
end
end

theorem canonical_refines {F : Fir.Program} (domain : programDomain F = true)
    (pins : BoolPinsOk F) : ∀ k, AtClock F k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro H external live ρf ρo owned joins Jf Jo c state scope
    exact eval_refines domain pins ih Jf c state scope

end Compilatrix.Own.Plain
