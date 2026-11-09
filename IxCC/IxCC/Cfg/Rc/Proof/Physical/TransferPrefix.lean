import IxCC.Cfg.Rc.Proof.Physical.DropPreservation
import IxCC.Own.Plain.Proof.Transfers
import IxCC.Own.Plain.Proof.JumpState
import IxCC.Own.Plain.Proof.Scope

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

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
    (args : List Fir.Arg) (imm captured live : List Fir.Var) {first : Nat} {tail : List Cfg.Instr}
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (head : source.rest = encodePrefix P.base.size first
      (Own.Plain.transferActions imm captured live args) ++ tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    (himm : Own.Plain.ImmEnv ρo imm)
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
        (Own.Plain.transferActions imm captured live args) = .ok H' ∧
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
  have copyHead : source.rest = encodePrefix P.base.size first (Own.Plain.copies (Own.Plain.copiedArgs (captured ++ imm) (Own.Plain.heapArgs imm args))) ++
      (encodePrefix P.base.size (first + (Own.Plain.copies (Own.Plain.copiedArgs (captured ++ imm) (Own.Plain.heapArgs imm args))).length)
        (Own.Plain.drops ((captured ++ imm) ++ Own.Plain.argVars (Own.Plain.heapArgs imm args)) live) ++ tail) := by
    simpa only [Own.Plain.transferActions, Own.Plain.moveCopies_eq_copies, encodePrefix_append, List.append_assoc] using head
  have copyScope := Own.Plain.copiedArgs_scope (captured ++ imm) (Own.Plain.heapArgs_scope imm scope)
  rcases copy_prefix functions main (Own.Plain.copiedArgs (captured ++ imm) (Own.Plain.heapArgs imm args)) cursor copyHead sourceLookup before copyScope ready
      registers absent running callers with success | failure
  · obtain ⟨incFields, copied, mem₁, target₁, incArguments, copies, tokens₁, ready₁, trace₁,
      cursor₁, words₁, running₁, values₁⟩ := success
    rcases drop_prefix functions main ((captured ++ imm) ++ Own.Plain.argVars (Own.Plain.heapArgs imm args)) live cursor₁ rfl sourceLookup tokens₁ ready₁
        words₁ (fun dummy h => absent dummy (by omega)) running₁ callers with success | failure
    · obtain ⟨keptAll, H', mem', slots', lists', final, cost, drops, tokensAll, restoredAll,
        trace₂, cursor₂, words₂, running₂, heldValues⟩ := success
      obtain ⟨_, values₂, externalValues⟩ := drop_preservation tokens₁ drops tokensAll.exactRoots
      obtain ⟨fields, logical, arguments, sourceArgs, den⟩ :=
        Own.Plain.args_den before.den args scope
      obtain ⟨kept, hk, hk_sub⟩ :=
        before.exactRoots.restrict (Own.Plain.retained_sublist captured live)
      obtain ⟨hrefs, hmem⟩ :=
        Own.Plain.moveCopies_transfer_balance before.exactRoots before.distinct himm scope
          arguments incArguments hk tokensAll.exactRoots
      have subset : ∀ root ∈ kept, root ∈ roots := fun _ hm => hk_sub.subset hm
      have preserved : ∀ root ∈ (fields ++ held) ++ kept, H.value? root = H'.value? root := by
        intro root member
        apply (values₁ root).trans
        rcases List.mem_append.mp member with member | member
        · rcases List.mem_append.mp member with member | member
          · rcases hmem root (List.mem_append_left _ member) with hm_raw | himm_root
            · apply values₂ root
              rcases List.mem_append.mp hm_raw with hm | hm
              · exact List.mem_append_left _ (List.mem_append_left _ hm)
              · exact List.mem_append_right _ hm
            · exact Own.Plain.value?_eq_of_immVal copied H' himm_root
          · exact values₂ root (List.mem_append_left _ (List.mem_append_right _ member))
        · rcases hmem root (List.mem_append_right _ member) with hm_raw | himm_root
          · apply values₂ root
            rcases List.mem_append.mp hm_raw with hm | hm
            · exact List.mem_append_left _ (List.mem_append_left _ hm)
            · exact List.mem_append_right _ hm
          · exact Own.Plain.value?_eq_of_immVal copied H' himm_root
      have tokens : Tokens H' external (fields ++ held) (Own.Plain.retained captured live) ρf ρo kept := by
        refine ⟨?_, hk, ?_, (Own.Plain.retained_sublist captured live).nodup before.distinct⟩
        · intro x hx
          have hx_live : x ∈ live := (Own.Plain.retained_sublist captured live).subset hx
          obtain ⟨v, w, hvo, hwf, hd⟩ := before.den x hx_live
          refine ⟨v, w, hvo, hwf, ?_⟩
          change H'.value? v = some w
          have hv_kept : v ∈ kept := hk.member hx hvo
          rw [← preserved v (List.mem_append_right _ hv_kept)]
          exact hd
        · intro location
          have hbAll := tokensAll.balance location
          have hr := hrefs location
          simp only [holdRoots, refsIn_append] at hbAll hr ⊢
          omega
      have hhold : holdRoots external (keptAll ++ (incFields ++ held)) =
          holdRoots external (kept ++ (fields ++ held)) := by
        funext location
        have hr := hrefs location
        simp only [holdRoots, refsIn_append] at hr ⊢
        omega
      have restored : AllocatorReady H' addresses mem' (holdRoots external (kept ++ (fields ++ held)))
          context base bump limit slots' lists' := hhold ▸ restoredAll
      refine .inl ⟨fields, logical, kept, H', mem', slots', lists', final,
        2 * (Own.Plain.copies (Own.Plain.copiedArgs (captured ++ imm) (Own.Plain.heapArgs imm args))).length + cost, arguments, sourceArgs, ?_, tokens,
        Own.Plain.dens_preserve den (fun root member => preserved root (by simp [member])),
        restored, trace₁.trans trace₂, cursor₂, words₂, running₂, subset, preserved,
        fun root member => (values₁ root).trans (externalValues root member)⟩
      unfold Own.Plain.transferActions
      rw [Own.Plain.evalActions_append, Own.Plain.moveCopies_eq_copies, copies]
      exact drops
    · obtain ⟨cost, terminal, resource, trace₂, failed⟩ := failure
      exact .inr ⟨2 * (Own.Plain.copies (Own.Plain.copiedArgs (captured ++ imm) (Own.Plain.heapArgs imm args))).length + cost, terminal, resource,
        trace₁.trans trace₂, failed⟩
  · exact .inr failure



end IxCC.Cfg.Rc.Native
