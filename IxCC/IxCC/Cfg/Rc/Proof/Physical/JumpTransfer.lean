import IxCC.Cfg.Rc.Proof.Physical.TransferPrefix
import IxCC.Own.Plain.Proof.Selected

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- The actual copy/cleanup prefix prepares the selected join's complete
source body state at the physically reached heap. The returned native cursor
is still at the edge; actual edge binding and body entry are separate facts.
Saved joins, lexical captures and checked scope are all reconstructed from
the same selected stack entry. -/
theorem jump_transfer_prefix
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    {signatures : Own.Plain.Signatures} {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State signatures H (holdRoots external held) live ρf ρo roots joins Jf Jo imm)
    (j : Fir.JoinId) (args : List Fir.Arg) {ef : Fir.JEntry} {restf : List Fir.JEntry}
    (lookup : Fir.lookupJ j Jf = some (ef, restf))
    (scope : args.all (Own.Plain.argIn live) = true) (arity : args.length = ef.params.length)
    {first : Nat} {tail : List Cfg.Instr}
    (head : source.rest = encodePrefix P.base.size first
      (Own.Plain.transferActions imm ((joins.lookup j).getD []) live args) ++ tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo target.env)
    (absent : ∀ dummy, first ≤ dummy → ρo.get? dummy = none)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ captured older eo resto fields logical kept H' mem' slots' lists' final cost,
      Own.Plain.lookupJ j Jo = some (eo, resto) ∧ joins.lookup j = some captured ∧
      eo.params = ef.params ∧ eo.charged = ef.charged ∧
      eo.body = Own.Plain.lowerCode (captured ++ ef.params)
        (if ef.isRec then (ef.id, captured) :: older else older) ef.body ∧
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      fields.length = eo.params.length ∧
      Own.Plain.evalActions ρo H
        (Own.Plain.transferActions imm captured live args) = .ok H' ∧
      Own.Plain.State signatures H' (holdRoots external held) (captured ++ ef.params)
        (Fir.bindAll ef.env ef.params logical) (Own.bindAll eo.env eo.params fields) (kept ++ fields)
        (if ef.isRec then (ef.id, captured) :: older else older) (ef.after restf) (eo.after resto) ∧
      Own.Plain.scopeOk signatures (captured ++ ef.params)
        (Own.Plain.stackArities (ef.after restf)) ef.body = true ∧
      AllocatorReady H' addresses mem' (holdRoots external ((kept ++ fields) ++ held))
        context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} cost
        {mem := mem', ctx := context, stack := final :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) {source with rest := tail} final ∧
      FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ρo final.env ∧
      final.dsts = [] ∧
      (∀ root ∈ held, H.value? root = H'.value? root) ∧
      (∀ root, ExternalRoot external root → H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨captured, older, eo, resto, ownedLookup, captureLookup, entryDen, view,
      entryScope, tailDen, tailViews, tailScope⟩ :=
    Own.Plain.lookup_ready before.stack before.views before.scope lookup
  have prefixHead : source.rest = encodePrefix P.base.size first
      (Own.Plain.transferActions imm captured live args) ++ tail := by
    simpa only [captureLookup, Option.getD_some] using head
  rcases transfer_prefix functions main args imm captured live cursor prefixHead sourceLookup
      (Tokens.ofState before) before.immOk scope ready registers absent running callers with success | failure
  · obtain ⟨fields, logical, kept, H', mem', slots', lists', final, cost, arguments,
      sourceArgs, actions, tokens, den, restored, trace, next, words, finished,
      subset, preserved, externalValues⟩ := success
    have length : fields.length = ef.params.length := (Own.evalArgs_length ρo arguments).trans arity
    have balance : Balance H' (holdRoots external held) (fields ++ kept) := by
      intro location
      have counted := tokens.balance location
      simp only [holdRoots, refsIn_append] at counted ⊢
      omega
    have keptArgs : ∀ root ∈ fields ++ kept, H.value? root = H'.value? root := by
      intro root member
      apply preserved root
      simp only [List.mem_append] at member ⊢
      rcases member with member | member
      · exact Or.inl (Or.inl member)
      · exact Or.inr member
    obtain ⟨actual, logical', actualArgs, sourceArgs', originalDen⟩ :=
      Own.Plain.args_den before.env args scope
    have fieldsEqual : actual = fields := Option.some.inj (actualArgs.symm.trans arguments)
    have logicalEqual : logical' = logical := Option.some.inj (sourceArgs'.symm.trans sourceArgs)
    subst actual logical'
    obtain ⟨state, checkedScope⟩ := Own.Plain.jump_state entryDen view entryScope tailDen tailViews
      tailScope tokens.exactRoots balance keptArgs originalDen length
    exact .inl ⟨captured, older, eo, resto, fields, logical, kept, H', mem', slots', lists',
      final, cost, ownedLookup, captureLookup, entryDen.params, entryDen.charged, entryDen.body,
      arguments, sourceArgs, by simpa only [entryDen.params] using length, actions, state, checkedScope,
      by simpa only [List.append_assoc] using restored, trace, next, words, finished,
      fun root member => preserved root (by simp [member]), externalValues⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native
