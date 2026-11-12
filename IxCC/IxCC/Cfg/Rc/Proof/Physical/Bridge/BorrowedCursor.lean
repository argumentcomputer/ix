import IxCC.Cfg.Rc.Proof.Physical.CopyStep
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Rt.Rc
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native IxCC.Cfg.Rc.Native.Spec
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Actual consumed inc1 after a borrowed bind. Duplication permission is
supplied by the live parent edge (or immediate), without adding the borrowed
name to lexical ownership before the instruction executes. -/
theorem borrowed_marker_step
    {P : Cfg.Rc.Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    {dummy x : Nat} {tail : List Cfg.Instr}
    (head : source.rest = marker P.base.size dummy (.inc x 1) :: tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {value : RVal} (lookup : ρo.get? x = some value) (permission : CanDup H value)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ρo.get? dummy = none) (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ H' mem',
      Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external (value :: held) live ρf ρo roots ∧
      Gen.AllocatorReady maxClass H' addresses mem' (holdRoots external (roots ++ value :: held))
        context base bump limit slots lists ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} 2
        {mem := mem', ctx := context,
          stack := {target with pos := target.pos+1, env := target.env.insert dummy 1, dsts := []} :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail}
        {target with pos := target.pos+1, env := target.env.insert dummy 1, dsts := []} ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo (target.env.insert dummy 1) ∧
      (∀ root, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have consuming : consume P (layoutOf P) (marker P.base.size dummy (.inc x 1)) =
      .ok (.bind dummy (.fir (.call P.base.size [.var x, .lit (.nat 1)]))) :=
    IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_increment P (layoutOf P) dummy x
  have liveOperand : ¬ Rt.Proof.Fused (tablesOf P pairs) function x :=
    consumed_call_live cursor head consuming sourceLookup (.var x) (by simp) x rfl
  rcases cursor.call head consuming mem context callers with success | failure
  · obtain ⟨operands, nativeFunction, block, lowered, functionLookup, blockLookup,
      position, statement, continuation⟩ := success
    have operandsKnown : Rt.Lower.operands source.fn [.var x, .lit (.nat 1)] =
        .ok (some [.v x, .imm 3]) := rfl
    rw [operandsKnown] at lowered
    cases lowered
    obtain ⟨wrapperLookup, procedureLookup⟩ := source_stage_increment_runtime P functions main
    obtain ⟨H', action, tokens, values, outcome⟩ :=
      fused_increment_ready_instruction_fresh before lookup permission ready
        wrapperLookup procedureLookup target callers functionLookup blockLookup position statement
        registers liveOperand absent
    rcases outcome with ⟨mem', restored, trace, words⟩ | failed
    · exact .inl ⟨H', mem', action, tokens, restored, trace,
        continuation.withEnvs source.env (target.env.insert dummy 1) [], words, values⟩
    · exact .inr (reaches_resource_fails failed)
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failure
    exact failure


end IxCC.Cfg.Rc.Proof.Physical.Bridge
