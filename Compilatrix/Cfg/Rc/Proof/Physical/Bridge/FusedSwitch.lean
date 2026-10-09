import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedCompletion
import Compilatrix.Rt.Proof.StepTerm

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs
open Compilatrix.Lir (Word)
open Compilatrix.Src (NatMap)

/-- The real fusedEnd receipt either branches on the represented comparison
operands or executes its emitted natOverflow failure. The omitted boolean
result is read only in the source; its native register is never assumed. -/
theorem fused_switch
    {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {fn : Nat} {F : Lir.Func} {off : Nat}
    {starts : NatMap Nat} {C : List PBlock}
    (functionLookup : lp.funcs[fn]? = some F) (layout : Holds f F off starts C)
    {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {init : List Cfg.Instr} {cond : Lir.Cond} {a b : Fir.Arg}
    (receipt : fusable T (useCounts function) block = some (init, cond, a, b))
    {frame : Cfg.Frame} (empty : frame.rest = []) (done : FusedDone T function block frame)
    {st st' stF : St} (lowered : (fusedEnd f T index block cond a b).run st = .ok ((), st'))
    (labels : Labels st) (opened : Open st) (growth : Grows st' stF) (complete : Ext C stF)
    {addresses : AddressMap} {bound : Nat} {target : Lir.Env}
    (registers : FusedWords addresses (Fused T function) bound frame.env target)
    {heap : Own.Heap} {mem : X86.Memory} {context : Word} {callers : List Lir.Frame}
    {x : Nat} {value : Own.RVal} {key : Key.CtorKey} {fields : List Own.RVal}
    {alts : List (Key.CtorKey × Cfg.Edge)} {default : Option Cfg.Edge} {edge : Cfg.Edge}
    (terminator : block.term = .switch x alts default)
    (lookup : frame.env.get? x = some value)
    (constructor : value.asCtor T.known heap = some (key, fields))
    (selected : Cfg.selectEdge key alts default = some edge) :
    (∃ pe le target', EdgeOk C f edge pe ∧ edge.back = decide (edge.target ≤ index) ∧
      resolveEdge f off starts pe = .ok le ∧
      ReachesEdge lp fn F mem context callers (off + st.cur)
        (Lir.atState mem context fn (off + st.cur) st.acc.length target callers) le target' ∧
      FusedWords addresses (Fused T function) bound frame.env target') ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context fn (off + st.cur) st.acc.length target callers) := by
  obtain ⟨y, op, actualAlts, actualDefault, body, comparison, actualTerm, _, _⟩ := fusable_some receipt
  have terms := actualTerm.symm.trans terminator
  simp only [Cfg.Term.switch.injEq] at terms
  obtain ⟨rfl, rfl, rfl⟩ := terms
  obtain ⟨y', op', va, vb, result, body', evaluated, resultEffect, resultLookup⟩ :=
    done init cond a b receipt empty
  rw [body] at body'
  simp only [List.append_cancel_left_eq, List.cons.injEq, Cfg.Instr.bind.injEq,
    Own.Rhs.fir.injEq, Fir.Rhs.prim.injEq, and_true] at body'
  obtain ⟨rfl, rfl⟩ := body'
  have resultEqual : result = value := Option.some.inj (resultLookup.symm.trans lookup)
  subst result
  unfold fusedEnd at lowered
  obtain ⟨operands, next, operandLowering, endLowering⟩ := run_bind lowered
  have operandState : next = st ∧ Lower.operands f [a, b] = .ok operands := by
    simp only [StateT.run, MonadLift.monadLift, liftM, monadLift, StateT.lift,
      bind, Except.bind] at operandLowering
    split at operandLowering
    · cases operandLowering
    · rename_i actual actualLowering
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at operandLowering
      obtain ⟨rfl, rfl⟩ := operandLowering
      exact ⟨rfl, actualLowering⟩
  obtain ⟨rfl, operandsReceipt⟩ := operandState
  split at endLowering
  · rename_i left right
    rw [terminator] at endLowering
    simp only at endLowering
    obtain ⟨words, wordEvaluation, represented, _⟩ :=
      fused_compare_operands_words registers blockLookup receipt operandsReceipt evaluated
    obtain ⟨wa, wb, rfl, hva, hvb⟩ : ∃ wa wb, words = [wa, wb] ∧
        valueWord addresses va = some wa ∧ valueWord addresses vb = some wb := by
      rcases represented with _ | ⟨head, rest⟩
      rcases rest with _ | ⟨second, rest⟩
      cases rest
      exact ⟨_, _, rfl, head, second⟩
    obtain ⟨leftEval, rightEval⟩ := lir_evalArgs_two wordEvaluation
    have selectedKey : (if cond.holds .w64 wa wb then T.known.boolTrue else T.known.boolFalse) =
        some key := by
      simp only [Own.primResult] at resultEffect
      cases natural : Own.natArgs [va, vb] with
      | none => simp [natural] at resultEffect
      | some ns =>
        obtain ⟨p, q, rfl, rfl, rfl⟩ := natArgs_two natural
        simp only [natural] at resultEffect
        rw [cmp_sem comparison hva hvb] at resultEffect
        simp only at resultEffect
        exact key_of_bool resultEffect constructor
    obtain ⟨pe, le, edgeOk, back, resolved, reached⟩ := fused_sim
      (mem := mem) (ctx := context) (rest := callers) functionLookup layout endLowering
      labels opened growth complete leftEval rightEval selectedKey selected
    exact .inl ⟨pe, le, target, edgeOk, back, resolved, reached, registers⟩
  · rw [close_run] at endLowering
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at endLowering
    change closeSt _ (.fail .natOverflow) = st' at endLowering
    exact .inr (fails_closed functionLookup
      (closedAt_of (t := .fail .natOverflow) layout
        (by simpa only [endLowering] using growth) complete rfl)
      mem context target callers)


end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
