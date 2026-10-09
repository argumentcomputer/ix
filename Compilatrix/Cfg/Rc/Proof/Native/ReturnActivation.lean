import Compilatrix.Cfg.Rc.Proof.Native.Activation
import Compilatrix.Cfg.Rc.Proof.Native.HeapHistory
import Compilatrix.Cfg.Rc.Proof.Physical.CheckedPrefix
import Compilatrix.Cfg.Rc.Proof.Physical.TransferPrefix
import Compilatrix.Cfg.Rc.Proof.Physical.PrefixHeap
import Compilatrix.Cfg.Rc.Proof.Physical.TokenEnvironments
import Compilatrix.Own.Plain.Proof.Results

/-! Execute the canonical return's copies and cleanup before exposing the
actual native return terminator. The returned value owns exactly one token;
all external caller values and the fixed physical region remain valid. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs Compilatrix.Own.Rc

theorem Activation.return_value
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List Own.RVal}
    {live : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {arg : Fir.Arg} {sourceFunction : Fir.Fun} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins (.ret arg)
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external roots
      context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    (∃ value logical afterMemory afterHeap afterSlots afterLists final cost word,
      Own.evalArg ownedEnv arg = some value ∧ Fir.Arg.eval sourceEnv arg = some logical ∧
      Own.Proof.Den afterHeap value logical ∧ Balance afterHeap external [value] ∧
      HeapState P pairs afterHeap addresses afterMemory external [value]
        context base bump limit regionBytes afterSlots afterLists ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem := memory, ctx := context, stack := target :: callers} cost
        {mem := afterMemory, ctx := context, stack := final :: callers} ∧
      Rt.Proof.RetAt (Public.Spec.sourceStage P functions main) final word ∧
      valueWord addresses value = some word ∧ Own.Plain.Bounded afterHeap.size value ∧
      ValueCtorOk (tablesOf P pairs) value ∧
      Own.Plain.ExternalPreserved H afterHeap external ∧
      HeapHistory H.size addresses afterHeap.size addresses) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem := memory, ctx := context, stack := target :: callers} := by
  have scope : Own.Plain.argIn live arg = true := before.scope
  have scopeArgs : [arg].all (Own.Plain.argIn live) = true := by simpa using scope
  obtain ⟨value, logical, ownValue, sourceValue, originalDen⟩ :=
    Own.Plain.arg_den before.canonical.env scope
  have lexical := before.lexical.1
  have frameValue := Cfg.Proof.evalArg_sub lexical ownValue
  have sourceArgs : Fir.evalArgs sourceEnv [arg] = some [logical] := by
    simp [Fir.evalArgs, sourceValue]
  have frameArgs : Own.evalArgs source.env [arg] = some [value] := by
    simp [Own.evalArgs, frameValue]
  have prefixLayout : At F P source ownedEnv ownedJoins (Own.Plain.actionPrefix
      (Own.Plain.copies [arg] ++ Own.Plain.drops [] live) (.ret arg)) := before.layout
  obtain ⟨first, tail, head, returnLayout, absent⟩ :=
    checked_prefix_cursor checked prefixLayout sourceLookup before.frame.words
  obtain ⟨fd, scopeNames, params, acc, next, supply, lower, lookup, range, layout, cursor,
    sub, below, names, saved⟩ := returnLayout
  have tailEmpty : tail = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  subst tail
  let block : Cfg.Block := {params, body := acc.reverse, term := .ret arg}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  have initialTokens := Tokens.extend
    (Tokens.ofState (external := external) (held := []) before.canonical) lexical
  have initialReady : AllocatorReady H addresses memory (holdRoots external (roots ++ []))
      context base bump limit slots lists := by simpa only [List.append_nil] using heap.ready
  rcases transfer_prefix functions main [arg] [] live before.frame.cursor head before.frame.lookup
      initialTokens scopeArgs initialReady before.frame.words absent before.running callers with success | failure
  · obtain ⟨fields, logicals, kept, afterHeap, afterMemory, afterSlots, afterLists, final, cost,
      actualArgs, actualSourceArgs, actions, tokens, den, ready, trace, afterCursor, words,
      running, subset, preserved, externalPreserved⟩ := success
    have fieldsEqual : fields = [value] := Option.some.inj (actualArgs.symm.trans frameArgs)
    have logicalEqual : logicals = [logical] := Option.some.inj (actualSourceArgs.symm.trans sourceArgs)
    subst fields
    subst logicals
    have keptEmpty : kept = [] := by
      have exactRoots := tokens.exactRoots
      have noRetained : Own.Plain.retained [] live = [] := by simp [Own.Plain.retained]
      simpa only [Own.Plain.EnvRoots, noRetained, List.map_nil, Own.evalArgs,
        Option.some.injEq] using exactRoots.symm
    subst kept
    have denValue : Own.Proof.Den afterHeap value logical := by cases den; assumption
    have balance : Balance afterHeap external [value] := by
      apply balance_unhold
      simpa only [List.append_nil] using tokens.balance
    have size := actions_size actions
    have finalHeap : HeapState P pairs afterHeap addresses afterMemory external [value]
        context base bump limit regionBytes afterSlots afterLists :=
      ⟨by simpa only [List.nil_append, List.append_nil] using ready,
        actions_heapOk heap.ordered actions, heap.compatible.evalActions actions, heap.extent⟩
    obtain ⟨original, actual, originalLookup, receipt, consumedLookup⟩ :=
      consumed_entry consuming nativeRange
    have originalEqual : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
    subst original
    have actualEqual : actual = function := Option.some.inj (consumedLookup.symm.trans before.frame.lookup)
    subst actual
    obtain ⟨consumedBody, consumedBodyEq, consumedBlock⟩ :=
      (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
    have argLive : Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) arg :=
      fused_term_live consumedBlock (args := [arg]) (fun x member => by
        simp only [Rt.Proof.otherUses, List.mem_append]
        exact .inr (by simpa [Cfg.Check.termVars] using Rt.Proof.argVars_of_mem member)) arg (by simp)
    have compatible := before.frame.compatible.arg argLive frameValue
    rcases afterCursor.ret consuming nativeRange lookup before.frame.lookup blockLookup rfl rfl
        words frameValue running afterMemory context callers with returned | failure
    · obtain ⟨word, represented, ret⟩ := returned
      refine .inl ⟨value, logical, afterMemory, afterHeap, afterSlots, afterLists, final, cost, word,
        ownValue, sourceValue, denValue, balance, finalHeap, trace, ret, represented,
        Own.Plain.den_bounded denValue, compatible, ?_, ?_⟩
      · intro root w externalRoot rootDen
        change afterHeap.value? root = some w
        rw [← externalPreserved root externalRoot]
        exact rootDen
      · exact ⟨by omega, fun _ _ => rfl⟩
    · obtain ⟨charges, terminal, resource, restTrace, failed⟩ := failure
      exact .inr ⟨cost + charges, terminal, resource, trace.trans restTrace, failed⟩
  · exact .inr failure


end Compilatrix.Cfg.Rc.Native.Spec
