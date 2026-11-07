import IxCC.Cfg.Rc.Proof.Physical.CopyStep

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

theorem source_stage_decrement_runtime (P : Program) (functions : Nat → Lir.Func) (main : Nat) :
    (Public.Spec.sourceStage P functions main).funcs[P.base.size+1]? =
      some (decrementWrapper (layoutOf P).decProc) ∧
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).decProc]? =
      some Rt.Rc.Procs.dec := by
  have length : ((List.range P.base.size).map functions).length = (layoutOf P).sourceCount := by
    simp [layoutOf]
  exact ⟨raw_public_runtime (raw_dec_wrapper length main),
    raw_public_runtime (raw_dec_proc length main)⟩

/-- An actual source decrement obtains its call and return cursor from
consumed syntax. Reclamation preserves all carried values and allocator
metadata, including the updated free lists, in its actual final memory. -/
theorem drop_marker_step
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    {dummy x : Nat} {tail : List Cfg.Instr}
    (head : source.rest = marker P.base.size dummy (.dec x) :: tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ρo.get? dummy = none) (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ value remaining H' mem' slots' lists' charges,
      ρo.get? x = some value ∧ roots = value :: remaining ∧
      Own.Plain.evalAction ρo H (.dec x) = .ok H' ∧
      Tokens H' external held live ρf ρo remaining ∧
      AllocatorReady H' addresses mem' (holdRoots external (remaining ++ held))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} (2+charges)
        {mem := mem', ctx := context,
          stack := {target with pos := target.pos+1, env := target.env.insert dummy 1, dsts := []} :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert dummy 1, dsts := []} ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo (target.env.insert dummy 1) ∧
      (∀ root ∈ held, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have consuming : consume P (layoutOf P) (marker P.base.size dummy (.dec x)) =
      .ok (.bind dummy (.fir (.call (P.base.size+1) [.var x]))) :=
    IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_decrement P (layoutOf P) dummy x
  have liveOperand : ¬ Rt.Proof.Fused (tablesOf P pairs) function x :=
    consumed_call_live cursor head consuming sourceLookup (.var x) (by simp) x rfl
  rcases cursor.call head consuming mem context callers with success | failure
  · obtain ⟨operands, nativeFunction, block, lowered, functionLookup, blockLookup,
      position, statement, continuation⟩ := success
    have operandsKnown : Rt.Lower.operands source.fn [.var x] = .ok (some [.v x]) := rfl
    rw [operandsKnown] at lowered
    cases lowered
    obtain ⟨wrapperLookup, procedureLookup⟩ := source_stage_decrement_runtime P functions main
    obtain ⟨value, remaining, H', mem', slots', lists', charges, lookup, equal,
        action, tokens, restored, trace, words, preserved⟩ :=
      fused_decrement_ready_instruction_fresh before ready wrapperLookup procedureLookup
        target callers functionLookup blockLookup position statement registers liveOperand absent
    exact .inl ⟨value, remaining, H', mem', slots', lists', charges, lookup, equal,
      action, tokens, restored, trace,
      continuation.withEnvs source.env (target.env.insert dummy 1) [], words, preserved⟩
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failure
    exact failure



end IxCC.Cfg.Rc.Native
