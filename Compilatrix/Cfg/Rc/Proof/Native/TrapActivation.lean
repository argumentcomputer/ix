import Compilatrix.Cfg.Rc.Proof.Native.ReturnActivation
import Compilatrix.Cfg.Rc.Proof.Native.TrapCursor

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs Compilatrix.Own.Rc

/-- The canonical trap performs its real cleanup before the emitted trap.
An allocation or reference-count resource failure during cleanup remains
the actual resource outcome; no successful prefix is assumed. -/
theorem Activation.trap
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List Own.RVal}
    {live : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {sourceFunction : Fir.Fun} {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins .trap
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {memory : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses memory external roots
      context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    (∃ afterMemory final cost,
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem := memory, ctx := context, stack := target :: callers} cost
        {mem := afterMemory, ctx := context, stack := final :: callers} ∧
      Lir.step (Public.Spec.sourceStage P functions main)
        {mem := afterMemory, ctx := context, stack := final :: callers} = .trap) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem := memory, ctx := context, stack := target :: callers} := by
  have lexical := before.lexical.1
  have prefixLayout : At F P source ownedEnv ownedJoins (Own.Plain.actionPrefix
      (Own.Plain.copies [] ++ Own.Plain.drops [] live) .trap) := before.layout
  obtain ⟨first, tail, head, trapLayout, absent⟩ :=
    checked_prefix_cursor checked prefixLayout sourceLookup before.frame.words
  obtain ⟨fd, scopeNames, params, acc, next, supply, lower, lookup, range, layout, cursor,
    sub, below, names, saved⟩ := trapLayout
  have tailEmpty : tail = [] := by simpa only [skeleton, Cfg.Proof.spine] using cursor
  subst tail
  let block : Cfg.Block := {params, body := acc.reverse, term := .trap}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Cfg.Proof.Impl, Cfg.Fun.block?] using layout
  have programSize : P.base.size = F.size :=
    generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  have initialTokens := Tokens.extend
    (Tokens.ofState (external := external) (held := []) before.canonical) lexical
  have initialReady : AllocatorReady H addresses memory (holdRoots external (roots ++ []))
      context base bump limit slots lists := by simpa only [List.append_nil] using heap.ready
  rcases transfer_prefix functions main [] [] live before.frame.cursor head before.frame.lookup
      initialTokens (by rfl) initialReady before.frame.words absent before.running callers with success | failure
  · obtain ⟨fields, logicals, kept, afterHeap, afterMemory, afterSlots, afterLists, final, cost,
      actualArgs, actualSourceArgs, actions, tokens, den, ready, trace, afterCursor, words,
      running, subset, preserved, externalPreserved⟩ := success
    exact .inl ⟨afterMemory, final, cost, trace,
      afterCursor.trap consuming nativeRange lookup blockLookup rfl rfl running afterMemory context callers⟩
  · exact .inr failure


end Compilatrix.Cfg.Rc.Native.Spec
