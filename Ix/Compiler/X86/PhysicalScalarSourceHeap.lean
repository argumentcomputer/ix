import Ix.Compiler.X86.PhysicalScalarExport
import Ix.Compiler.PipelineApply
import Ix.Compiler.IxIR2.PipelineInvoke

namespace Ix.Compiler.X86.PhysicalScalar

def sourceArgument (word : Word) : Ixon.Eval.Value := .litV (.natL word.toNat)
def rawArgument (word : Word) : IxIR0.Value := .lit (.nat word.toNat)
def sourceArguments (values : Array Word) : List Ixon.Eval.Value := values.toList.map sourceArgument
def rawArguments (values : Array Word) : List IxIR0.Value := values.toList.map rawArgument

theorem sourceArguments.wf (values : Array Word) : Ixon.Eval.ValuesSharingWF (sourceArguments values) := by
  have all : ∀ words : List Word, Ixon.Eval.ValuesSharingWF (words.map sourceArgument) := by
    intro words
    induction words with
    | nil => exact .nil
    | cons word words ih => exact .cons _ _ (.litV _) ih
  exact all values.toList

theorem sourceArguments.related [scope : Ix.Compiler.Sim.MemberScope]
    (context : Ixon.Eval.EvalCtx) (raw : IxIR0.Ctx) (values : Array Word) :
    Ix.Compiler.Sim.ValsRel context.inlineSharing raw
      (Ixon.Eval.valuesInlineSharing (sourceArguments values)) (rawArguments values) := by
  have all : ∀ words : List Word, Ix.Compiler.Sim.ValsRel context.inlineSharing raw
      (Ixon.Eval.valuesInlineSharing (words.map sourceArgument)) (words.map rawArgument) := by
    intro words
    induction words with
    | nil => simpa [Ixon.Eval.valuesInlineSharing] using (Ix.Compiler.Sim.ValsRel.nil
        (ectx := context.inlineSharing) (ictx := raw))
    | cons word words ih =>
      simpa [Ixon.Eval.valuesInlineSharing, sourceArgument, rawArgument, Ixon.Eval.Value.inlineSharing] using
        (Ix.Compiler.Sim.ValsRel.cons (Ix.Compiler.Sim.ValRel.litNat (n := word.toNat)) ih)
  exact all values.toList

theorem rawArguments.renamed (rename : Ixon.Address → Ixon.Address) (values : Array Word) :
    IxIR0.Readdress.ValueList.mapAddresses rename (rawArguments values) = rawArguments values := by
  simp [rawArguments, rawArgument, IxIR0.Readdress.Value.mapAddresses]

theorem rawArguments.graph (relation : IxIR1.Sim.FunctionRel) (store : IxIR1.Store) (values : Array Word) :
    IxIR1.Sim.ValuesGraph relation store (rawArguments values) (values.map rval).toList := by
  have all : ∀ words : List Word, IxIR1.Sim.ValuesGraph relation store (words.map rawArgument) (words.map rval) := by
    intro words
    induction words with
    | nil => exact .nil
    | cons word words ih => exact .cons .lit ih
  simpa [rawArguments] using all values.toList

/-- Module initialization allocates one uncaptured PAP. The saturated scalar
application consumes it before entering the selected function. -/
def invocationHeap : IxIR1.Store := { nodes := #[none], allocs := 1, frees := 1, rcops := 1 }

theorem invocationHeap.get? (location : Nat) : invocationHeap.get? location = none := by
  cases location <;> simp [invocationHeap, IxIR1.Store.get?]

theorem invocationHeap.renamed (rename : Ixon.Address → Ixon.Address) :
    IxIR1.Readdress.Store.mapAddresses rename invocationHeap = invocationHeap := by
  simp [IxIR1.Readdress.Store.mapAddresses, invocationHeap]

theorem invocationHeap.runtime (values : Array Word) :
    IxIR2.Lower.Sim.SourceRuntimeInvariant invocationHeap (values.map rval).toList.reverse := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_⟩⟩
  · intro location box found
    simp [invocationHeap.get?] at found
  · intro parent box child found
    simp [invocationHeap.get?] at found
  · intro value member
    simp only [List.mem_reverse, Array.toList_map, List.mem_map] at member
    obtain ⟨word, _, rfl⟩ := member
    trivial
  · intro location world rc address arity captured found
    simp [invocationHeap.get?] at found

theorem invocationHeap.image {world fuel} (attached : IxIR2.Pipeline.CompiledAttachment world fuel) :
    attached.SourceStoreImage invocationHeap := by
  refine ⟨invocationHeap, invocationHeap.renamed _, ?_⟩
  constructor
  intro location world rc identity fields found
  simp [invocationHeap.get?] at found

theorem scalarArguments_owned {store : IxIR1.Store} {roots : List IxIR1.Sim.Root}
    (owned : IxIR1.Sim.RootOwnership store roots) (values : Array Word) :
    IxIR1.Sim.RootOwnership store (IxIR1.Sim.rootsFor .shared (values.map rval).toList ++ roots) := by
  have all : ∀ words : List Word,
      IxIR1.Sim.RootOwnership store (IxIR1.Sim.rootsFor .shared (words.map rval) ++ roots) := by
    intro words
    induction words with
    | nil => simpa [IxIR1.Sim.rootsFor] using owned
    | cons word words ih =>
      simpa [IxIR1.Sim.rootsFor] using ih.addNoLocation (value := rval word) rfl
  simpa using all values.toList

theorem invocationHeap.owned (values : Array Word) :
    IxIR1.Sim.RootOwnership invocationHeap (IxIR1.Sim.rootsFor .shared (values.map rval).toList) := by
  have empty : IxIR1.Sim.RootOwnership invocationHeap [] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · intro location box found
      simp [invocationHeap.get?] at found
    · intro location box address arity captured found
      simp [invocationHeap.get?] at found
    · intro location box found
      simp [invocationHeap.get?] at found
  simpa using scalarArguments_owned empty values

theorem closureStore.owned (address : Ixon.Address) (target : IxIR2.Function) :
    IxIR1.Sim.RootOwnership (closureStore address target).heap [⟨.shared, .loc 0⟩] := by
  exact IxIR1.Sim.RootOwnership.allocNode (by simpa [IxIR1.Sim.rootsFor, IxIR1.Sim.nodeChildren] using
    IxIR1.Sim.RootOwnership.empty) rfl

theorem closureStore.drop (context : IxIR1.Ctx) (address : Ixon.Address) (target : IxIR2.Function) (fuel : Nat) :
    IxIR1.dropVal context (fuel + 2) (closureStore address target).heap (.loc 0) = .ok invocationHeap := by
  simp [IxIR1.dropVal, IxIR1.dropMany, closureStore, IxIR2.Eval.Store.allocNode,
    IxIR1.Store.allocNode, IxIR1.Store.get?, IxIR1.Store.rcTick, IxIR1.Store.kill, invocationHeap]

/-- Decode the ordinary PAP entry prefix of a successful IxIR₁ application.
The extra evaluator fuel only exposes this fixed, terminating prefix. -/
theorem closureStore.applied {context : IxIR1.Ctx} {address : Ixon.Address} {target : IxIR2.Function}
    {declaration : IxIR1.Decl} (declared : context.decls address = some declaration)
    (safe : IxIR1.declPapSafe declaration = true)
    {values : Array Word} (arity : values.size = target.signature.params.size)
    {fuel : Nat} {output : IxIR1.Store × IxIR1.RVal}
    (applied : IxIR1.applyGo context fuel (closureStore address target).heap (.loc 0)
      (values.map rval).toList = .ok output) :
    ∃ callFuel, IxIR1.invoke context callFuel address (values.map rval).toList invocationHeap = .ok output := by
  have padded := IxIR1.applyGo_mono (larger := fuel + 3) (by omega) applied
  have found : (closureStore address target).heap.get? 0 =
      some ⟨.shared, 1, .papN address target.signature.params.size #[]⟩ := rfl
  refine ⟨fuel + 2, ?_⟩
  simpa [IxIR1.applyGo, found, IxIR1.dupVals, closureStore.drop, declared, safe, arity,
    bind, Except.bind, pure, Except.pure] using padded

end Ix.Compiler.X86.PhysicalScalar
