import IxCC.Cfg.Rc.Proof.Physical.CopyStep
import IxCC.Cfg.Rc.Proof.Prefix

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

theorem Tokens.held_congr {H : Heap} {external : Nat → Nat}
    {held other roots : List RVal} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    (counts : ∀ location, refsIn location held = refsIn location other) :
    Tokens H external other live ρf ρo roots := by
  refine {before with balance := ?_}
  intro location
  simpa only [holdRoots, counts location] using before.balance location

theorem ready_held_congr {H : Heap} {external : Nat → Nat} {held other roots : List RVal}
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (before : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    (counts : ∀ location, refsIn location held = refsIn location other) :
    AllocatorReady H addresses mem (holdRoots external (roots ++ other))
      context base bump limit slots lists := by
  have same : holdRoots external (roots ++ held) = holdRoots external (roots ++ other) := by
    funext location
    simp only [holdRoots, refsIn_append, counts location]
  rw [← same]
  exact before

/-- Traverse the actual canonical copy prefix at its consumed lowering cursor.
Each variable occurrence executes its own inc marker; immediate occurrences
add no instruction or heap count. Aliased fields retain their multiplicity.
A native count failure is an actual finite resource failure from the original
state. All successful copies retain the complete allocator-ready metadata. -/
theorem copy_prefix
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    (args : List Fir.Arg) {first : Nat} {tail : List Cfg.Instr}
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (head : source.rest = encodePrefix P.base.size first (Own.Plain.copies args) ++ tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    (scope : args.all (Own.Plain.argIn live) = true)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ∀ dummy, first ≤ dummy → ρo.get? dummy = none)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ fields H' mem' final,
      Own.evalArgs ρo args = some fields ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies args) = .ok H' ∧
      Tokens H' external (fields ++ held) live ρf ρo roots ∧
      AllocatorReady H' addresses mem' (holdRoots external (roots ++ (fields ++ held)))
        context base bump limit slots lists ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} (2 * (Own.Plain.copies args).length)
        {mem := mem', ctx := context, stack := final :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail} final ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo final.env ∧
      final.dsts = [] ∧ (∀ root, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  induction args generalizing first source target H held mem with
  | nil =>
    have same : {source with rest := tail} = source := by
      have rest : source.rest = tail := by simpa [Own.Plain.copies, encodePrefix] using head
      cases source
      simp_all
    exact .inl ⟨[], H, mem, target, rfl, rfl, before, ready, .refl _,
      by rw [same]; exact cursor, registers, running, fun _ => rfl⟩
  | cons arg args ih =>
    have scopeParts : Own.Plain.argIn live arg = true ∧
        args.all (Own.Plain.argIn live) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using scope
    have scopeTail := scopeParts.2
    cases arg with
    | var x =>
      have member : x ∈ live := by simpa [Own.Plain.argIn] using scopeParts.1
      have markerHead : source.rest = marker P.base.size first (.inc x 1) ::
          (encodePrefix P.base.size (first+1) (Own.Plain.copies args) ++ tail) := by
        simpa only [Own.Plain.copies, encodePrefix, List.cons_append] using head
      rcases copy_marker_step functions main cursor markerHead sourceLookup before member ready
          registers (absent first (by omega)) running callers with success | failed
      · obtain ⟨value, H₁, mem₁, lookup, action, tokens, ready₁, trace₁, next, words, values₁⟩ := success
        rcases ih next rfl sourceLookup tokens scopeTail ready₁ words
            (fun dummy h => absent dummy (by omega)) rfl with success | failed
        · obtain ⟨fields, H₂, mem₂, final, arguments, actions, tokens₂, ready₂, trace₂, cursor₂,
            words₂, running₂, values₂⟩ := success
          have reorder : ∀ location, refsIn location (fields ++ value :: held) =
              refsIn location ((value :: fields) ++ held) := by
            intro location
            simp only [refsIn_append, refsIn, List.cons_append]
            omega
          refine .inl ⟨value :: fields, H₂, mem₂, final, ?_, ?_, Tokens.held_congr tokens₂ reorder,
            ready_held_congr ready₂ reorder, ?_, cursor₂, words₂, running₂,
            fun root => (values₁ root).trans (values₂ root)⟩
          · simp [Own.evalArgs, Own.evalArg, lookup, arguments]
          · simp [Own.Plain.copies, Own.Plain.evalActions, action, actions, Sem.Result.bind]
          · simpa [Own.Plain.copies, Nat.mul_add, Nat.add_comm] using trace₁.trans trace₂
        · obtain ⟨cost, terminal, resource, trace₂, failure⟩ := failed
          exact .inr ⟨2+cost, terminal, resource, trace₁.trans trace₂, failure⟩
      · exact .inr failed
    | lit literal =>
      rcases ih cursor head sourceLookup before scopeTail ready registers absent running with success | failed
      · obtain ⟨fields, H', mem', final, arguments, actions, tokens, restored, trace, next,
          words, finished, values⟩ := success
        have reorder : ∀ location, refsIn location (fields ++ held) =
            refsIn location ((RVal.lit literal :: fields) ++ held) := by
          intro location
          simp [refsIn]
        exact .inl ⟨.lit literal :: fields, H', mem', final,
          by simp [Own.evalArgs, Own.evalArg, arguments], actions,
          Tokens.held_congr tokens reorder, ready_held_congr restored reorder, trace, next,
          words, finished, values⟩
      · exact .inr failed
    | erased =>
      rcases ih cursor head sourceLookup before scopeTail ready registers absent running with success | failed
      · obtain ⟨fields, H', mem', final, arguments, actions, tokens, restored, trace, next,
          words, finished, values⟩ := success
        have reorder : ∀ location, refsIn location (fields ++ held) =
            refsIn location ((RVal.erased :: fields) ++ held) := by
          intro location
          simp [refsIn]
        exact .inl ⟨.erased :: fields, H', mem', final,
          by simp [Own.evalArgs, Own.evalArg, arguments], actions,
          Tokens.held_congr tokens reorder, ready_held_congr restored reorder, trace, next,
          words, finished, values⟩
      · exact .inr failed




end IxCC.Cfg.Rc.Native
