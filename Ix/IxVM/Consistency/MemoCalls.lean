import Ix.IxVM.Refinement.Statement

/-! # A per-callee count of memoized calls (no longer part of the statement)

The consistency statement once bounded, in `L0`, the distinct calls of each memoized
callee. It now bounds the trace's memory instead (`ROMAddressesAtMost`,
`Ix.IxVM.Consistency.Statement`). These two definitions remain only for the core
slice's size bound (`IxVMRefinement.Core.Bound`, `IxVMRefinement.Core.Specs`), until it
moves to the memory count; nothing in the statement reads them. Delete this module with
their last use. -/

namespace IxVM.Consistency

open Aiur.Generic.SourceSemantics (Call)

/-- **A memoized call**: its callee is a function of the source program that the
compiler does not inline (the negation of `Aiur.Generic.Specialized.inlineNames`'s
test). An inlined call has no memo rows of its own, and a lookup map's callee is not a
function of the program (its table has no trace rows), so neither is counted. -/
def memoCall {G : Type} [DecidableEq G] (s : Aiur.Generic.Source G) (name : String) : Bool :=
  match Aiur.Generic.Instance.ofSymbol name with
  | .error _ => false
  | .ok key => (s.program.findFunction? key.name).any (fun f => !f.isInline)

/-- **At most `n` distinct calls of each memoized callee**, up to representation in the
ROM: for each memoized callee, at most `n` argument lists cover its calls, each one
representing the call's arguments relative to the heap at the call. -/
def MemoCallsAtMost {G : Type} [DecidableEq G] (s : Aiur.Generic.Source G) (rom : Aiur.ROM G)
    (calls : List (Call G)) (n : Nat) : Prop :=
  ∀ name, memoCall s name = true →
    ∃ keys : List (List (Aiur.Value G)), keys.length ≤ n ∧
      ∀ c ∈ calls, c.name = name →
        ∃ k ∈ keys, List.Forall₂ (Aiur.Represents rom c.heap) c.args k

end IxVM.Consistency
