import IxCC.Cfg.Rc.Proof.Physical.CopyPrefix

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Lift the physical canonical copy traversal to the full source invariant.
Join denotations, capture views and scope survive each actual count update;
only the copied argument occurrences are added to external held ownership. -/
theorem copy_prefix_state
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {imm : List Fir.Var} (args : List Fir.Arg) {first : Nat} {tail : List Cfg.Instr}
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (head : source.rest = encodePrefix P.base.size first (Own.Plain.copies (Own.Plain.heapArgs imm args)) ++ tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {signatures : Own.Plain.Signatures} {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State signatures H (holdRoots external held) live ρf ρo roots joins Jf Jo imm)
    (scope : args.all (Own.Plain.argIn live) = true)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ∀ dummy, first ≤ dummy → ρo.get? dummy = none)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ fields H' mem' final,
      Own.evalArgs ρo args = some fields ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies (Own.Plain.heapArgs imm args)) = .ok H' ∧
      Own.Plain.State signatures H' (holdRoots external (fields ++ held))
        live ρf ρo roots joins Jf Jo imm ∧
      Gen.AllocatorReady maxClass H' addresses mem' (holdRoots external (roots ++ (fields ++ held)))
        context base bump limit slots lists ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} (2 * (Own.Plain.copies (Own.Plain.heapArgs imm args)).length)
        {mem := mem', ctx := context, stack := final :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail} final ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo final.env ∧
      final.dsts = [] ∧ (∀ root, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  rcases copy_heapArgs_prefix functions main args cursor head sourceLookup (Tokens.ofState before)
      before.immOk scope ready registers absent running callers with success | failure
  · obtain ⟨fields, H', mem', final, arguments, actions, tokens, restored,
      trace, next, words, finished, values⟩ := success
    exact .inl ⟨fields, H', mem', final, arguments, actions,
      ⟨tokens.den, tokens.exactRoots, tokens.balance, tokens.distinct,
        before.stack.transport (fun root _ => values root), before.views, before.scope,
        before.immSub, before.immOk⟩,
      restored, trace, next, words, finished, values⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native
