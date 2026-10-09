import Compilatrix.Cfg.Rc.Proof.Physical.DropPreservation
import Compilatrix.Own.Plain.Proof.Transfers
import Compilatrix.Own.Plain.Proof.JumpState
import Compilatrix.Own.Plain.Proof.Scope

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Spec Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs

theorem encodePrefix_append (limit first : Nat) (as bs : List Action) :
    encodePrefix limit first (as ++ bs) =
      encodePrefix limit first as ++ encodePrefix limit (first + as.length) bs := by
  induction as generalizing first with
  | nil => simp [encodePrefix]
  | cons a as ih =>
    simp [encodePrefix, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Execute the actual canonical argument transfer: one copy for each
variable occurrence, then cleanup by lexical identity. This supplies the
physical prefix needed by returns, tail calls and selected join entries.
The argument denotations and surviving capture roots refer to the exact
heap and memory reached by the native trace. -/
theorem transfer_prefix
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    (args : List Fir.Arg) (captured live : List Fir.Var) {first : Nat} {tail : List Cfg.Instr}
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (head : source.rest = encodePrefix P.base.size first
      (Own.Plain.copies args ++ Own.Plain.drops captured live) ++ tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {ρf : Fir.Env} {ρo : Own.Env}
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
    (∃ fields logical kept H' mem' slots' lists' final cost,
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      Own.Plain.evalActions ρo H
        (Own.Plain.copies args ++ Own.Plain.drops captured live) = .ok H' ∧
      Tokens H' external (fields ++ held) (Own.Plain.retained captured live) ρf ρo kept ∧
      Sem.Forall2 (Own.Proof.Den H') fields logical ∧
      AllocatorReady H' addresses mem' (holdRoots external (kept ++ (fields ++ held)))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} cost
        {mem := mem', ctx := context, stack := final :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail} final ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo final.env ∧
      final.dsts = [] ∧
      (∀ root ∈ kept, root ∈ roots) ∧
      (∀ root ∈ (fields ++ held) ++ kept, H.value? root = H'.value? root) ∧
      (∀ root, ExternalRoot external root → H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have copyHead : source.rest = encodePrefix P.base.size first (Own.Plain.copies args) ++
      (encodePrefix P.base.size (first + (Own.Plain.copies args).length)
        (Own.Plain.drops captured live) ++ tail) := by
    simpa only [encodePrefix_append, List.append_assoc] using head
  rcases copy_prefix functions main args cursor copyHead sourceLookup before scope ready
      registers absent running callers with success | failure
  · obtain ⟨fields, copied, mem₁, target₁, arguments, copies, tokens₁, ready₁, trace₁,
      cursor₁, words₁, running₁, values₁⟩ := success
    rcases drop_prefix functions main captured live cursor₁ rfl sourceLookup tokens₁ ready₁
        words₁ (fun dummy h => absent dummy (by omega)) running₁ callers with success | failure
    · obtain ⟨kept, H', mem', slots', lists', final, cost, drops, tokens, restored,
        trace₂, cursor₂, words₂, running₂, heldValues⟩ := success
      obtain ⟨subset, values₂, externalValues⟩ := drop_preservation tokens₁ drops tokens.exactRoots
      obtain ⟨actual, logical, actualArgs, sourceArgs, den⟩ :=
        Own.Plain.args_den before.den args scope
      have same : actual = fields := Option.some.inj (actualArgs.symm.trans arguments)
      subst actual
      have preserved : ∀ root ∈ (fields ++ held) ++ kept, H.value? root = H'.value? root :=
        fun root member => (values₁ root).trans (values₂ root member)
      refine .inl ⟨fields, logical, kept, H', mem', slots', lists', final,
        2 * (Own.Plain.copies args).length + cost, arguments, sourceArgs, ?_, tokens,
        Own.Plain.dens_preserve den (fun root member => preserved root (by simp [member])),
        restored, trace₁.trans trace₂, cursor₂, words₂, running₂, subset, preserved,
        fun root member => (values₁ root).trans (externalValues root member)⟩
      rw [Own.Plain.evalActions_append, copies]
      exact drops
    · obtain ⟨cost, terminal, resource, trace₂, failed⟩ := failure
      exact .inr ⟨2 * (Own.Plain.copies args).length + cost, terminal, resource,
        trace₁.trans trace₂, failed⟩
  · exact .inr failure



end Compilatrix.Cfg.Rc.Native
