import IxCC.Cfg.Rc.Proof.Physical.JumpEntry
import IxCC.Cfg.Rc.Proof.Physical.JumpTransfer
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.StateEnvironments
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap
import IxCC.Cfg.Rc.Proof.Native.Activation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- Execute a checked canonical jump through its actual copies, cleanup and
native edge. The same selected join supplies source captures, checked body
scope and physical continuation; all freshness and parameter bounds come
from original source admission. -/
theorem jump_activation
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Heap} {addresses : AddressMap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    {j : Fir.JoinId} {args : List Fir.Arg} {sourceFunction : Fir.Fun}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses
      (holdRoots external held) live ρf ρo roots joins Jf Jo (.jmp j args)
      sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {entry : Fir.JEntry} {rest : List Fir.JEntry}
    (lookup : Fir.lookupJ j Jf = some (entry, rest)) (arity : args.length = entry.params.length)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external (roots ++ held)
      context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    (∃ captured older ownedEntry ownedRest fields logical kept H' mem' slots' lists' after final cost,
      Own.Plain.lookupJ j Jo = some (ownedEntry, ownedRest) ∧ joins.lookup j = some captured ∧
      ownedEntry.params = entry.params ∧ ownedEntry.charged = entry.charged ∧
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      Activation F P pairs (Public.Spec.sourceStage P functions main) H' addresses
        (holdRoots external held) (captured ++ entry.params)
        (Fir.bindAll entry.env entry.params logical) (Own.bindAll ownedEntry.env ownedEntry.params fields)
        (kept ++ fields) (if entry.isRec then (entry.id, captured) :: older else older)
        (entry.after rest) (ownedEntry.after ownedRest) entry.body sourceFunction.vars function after final ∧
      HeapState P pairs H' addresses mem' external ((kept ++ fields) ++ held)
        context base bump limit regionBytes slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} cost
        {mem := mem', ctx := context, stack := final :: callers} ∧
      entry.charged.toNat ≤ cost ∧ H'.size = H.size ∧ after.fn = source.fn ∧
      (∀ root ∈ held, H.value? root = H'.value? root) ∧
      (∀ root, ExternalRoot external root → H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have sourceRange : source.fn < F.size := by
    obtain ⟨_, _, _, _, _, _, _, _, range, _⟩ := before.layout
    exact range
  have programSize : P.base.size = F.size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using sourceRange
  have scope : args.all (Own.Plain.argIn live) = true := by
    have parts : decide ((Own.Plain.stackArities Jf).lookup j = some args.length) = true ∧
        args.all (Own.Plain.argIn live) = true := by
      simpa only [Own.Plain.scopeOk, Bool.and_eq_true] using before.scope
    exact parts.2
  have initialLayout : At F P source ρo Jo (Own.Plain.actionPrefix
      (Own.Plain.copies args ++ Own.Plain.drops ((joins.lookup j).getD []) live) (.jmp j args)) := before.layout
  obtain ⟨first, tail, head, edgeLayout, absent⟩ :=
    checked_prefix_cursor checked initialLayout sourceLookup before.frame.words
  have tailEmpty : tail = [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, cursor, _⟩ := edgeLayout
    simpa only [skeleton, Cfg.Proof.spine] using cursor
  subst tail
  have lexical := before.lexical.1
  have framedState := state_extend before.canonical lexical
  rcases jump_transfer_prefix functions main before.frame.cursor framedState j args lookup scope arity
      head before.frame.lookup heap.ready before.frame.words absent before.running callers with success | failure
  · obtain ⟨captured, older, ownedEntry, ownedRest, fields, logical, kept, H', mem', slots', lists',
      middle, prefixCost, ownedLookup, capturedLookup, params, charged, body, frameArgs, sourceArgs,
      fieldArity, actions, canonical, checkedScope, ready, trace₁, cursor₁, words₁, running₁,
      heldPreserved, externalPreserved⟩ := success
    have size : H'.size = H.size := actions_size actions
    have edgeFrame : FrameState P pairs (Public.Spec.sourceStage P functions main) addresses H'.size
        sourceFunction.vars function {source with rest := []} middle :=
      ⟨before.frame.lookup, cursor₁, words₁, by rw [size]; exact before.frame.bounded,
        before.frame.compatible⟩
    obtain ⟨actualFields, _, originalArgs, _, _⟩ := Own.Plain.args_den before.canonical.env args scope
    have fieldsEqual : actualFields = fields := Option.some.inj
      ((Cfg.Proof.evalArgs_sub lexical originalArgs).symm.trans frameArgs)
    subst actualFields
    have realParams : ∀ fd, P.base.fun? source.fn = some fd →
        ∀ (label : Nat) (block : Cfg.Block), fd.blocks[label]? = some block →
          ∀ x ∈ block.params.map Prod.fst, x < sourceFunction.vars :=
      fun fd fdLookup label block blockLookup =>
        checked_block_params checked sourceRange sourceLookup fdLookup blockLookup
    rcases jump_entry consuming edgeLayout ownedLookup originalArgs fieldArity edgeFrame nativeRange
        realParams running₁ mem' context callers with entered | failure
    · obtain ⟨after, final, edgeCost, afterLayout, afterFrame, trace₂, costBound, running₂, sameFn, fused⟩ := entered
      rw [body] at afterLayout
      have activation : Activation F P pairs (Public.Spec.sourceStage P functions main) H' addresses
          (holdRoots external held) (captured ++ entry.params)
          (Fir.bindAll entry.env entry.params logical) (Own.bindAll ownedEntry.env ownedEntry.params fields)
          (kept ++ fields) (if entry.isRec then (entry.id, captured) :: older else older)
          (entry.after rest) (ownedEntry.after ownedRest) entry.body sourceFunction.vars function after final :=
        ⟨canonical, afterLayout, afterFrame, checkedScope, running₂, fused⟩
      refine .inl ⟨captured, older, ownedEntry, ownedRest, fields, logical, kept, H', mem', slots', lists',
        after, final, prefixCost+edgeCost, ownedLookup, capturedLookup, params, charged, originalArgs,
        sourceArgs, activation, ⟨ready, actions_heapOk heap.ordered actions,
          heap.compatible.evalActions actions, heap.extent⟩,
        trace₁.trans trace₂, ?_, size, sameFn, heldPreserved, externalPreserved⟩
      rw [charged] at costBound
      omega
    · obtain ⟨cost, terminal, resource, trace₂, failed⟩ := failure
      exact .inr ⟨prefixCost+cost, terminal, resource, trace₁.trans trace₂, failed⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native
