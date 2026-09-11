import Ix.Compiler.IxIR2.EvalCounter

/-!
# Executable IxIR₂ logical/physical witnesses

The fixtures run the same validated programs under both interpretations.  They
pin the intermediate present-credit equation, terminal reuse/discard laws,
hot and cold reset decisions, and the separation of control from recursive
heap-traversal fuel.
-/

namespace Ix.Compiler.IxIR2.Eval.Examples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

private def blockAddress : Address := Address.replicate 0x61
private def layout : LayoutId := Address.replicate 0x62
private def functionAddress : Address := Address.replicate 0x63

private def nodeCtor : CtorId :=
  { block := blockAddress, indIdx := 0, cidx := 0 }

private def schemas : Owned → CtorId → Option CtorSchema
  | .unique, cid =>
      if cid == nodeCtor then
        some { layout, fields := #[.unique] }
      else
        none
  | .shared, cid =>
      if cid == nodeCtor then
        some { layout, fields := #[.shared] }
      else
        none

private def signature (result : Owned) : Signature :=
  { params := #[], result, papSafe := false }

private def validationContext : Validate.Context := { schemas }

private def validates (program : Program) : Bool :=
  match Validate.validate validationContext program with
  | .ok _ => true
  | .error _ => false

private def run (interpretation : Interpretation) (program : Program)
    (controlFuel : Nat := 100) (heapFuel : Nat := 100) : Except Error Result :=
  runMain (Context.ofProgram program schemas) interpretation program
    controlFuel heapFuel

private def lawHolds (logical physical : Store) (presentCredits : Nat) : Bool :=
  let left := logical.counters
  let right := physical.counters
  left.allocs == right.allocs + right.reuses &&
    left.frees == right.frees + right.reuses + presentCredits &&
    left.rcops == right.rcops &&
    logical.live == physical.live &&
    left.resetAttempts == right.resetAttempts &&
    left.hotResets == right.hotResets &&
    left.coldResets == right.coldResets

private def returnedCtor (result : Result) : Option (CtorId × Array RVal) :=
  match result.value with
  | .loc location =>
      match result.store.get? location with
      | some { node := .ctorN cid fields, .. } => some (cid, fields)
      | _ => none
  | _ => none

private def sameCtorResult (left right : Result) : Bool :=
  returnedCtor left == returnedCtor right

/-! ## Unique required-credit reuse -/

private def uniqueReuse : Program :=
  { declarations := []
    main :=
      { signature := signature .unique
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .unique nodeCtor #[.lit (.nat 7)],
              .takeUnique (.reg 0) nodeCtor,
              .allocWith 0 .unique nodeCtor #[.reg 1]]
            terminator := .ret (.reg 2) }] } }

#guard validates uniqueReuse

private def uniqueLogical := run .logical uniqueReuse 4 0
private def uniquePhysical := run .physical uniqueReuse 4 0

#guard match uniqueLogical, uniquePhysical with
  | .ok logical, .ok physical =>
      sameCtorResult logical physical &&
        logical.controlRemaining == 0 && physical.controlRemaining == 0 &&
        logical.heapRemaining == 0 && physical.heapRemaining == 0 &&
        logical.store.counters.allocs == 2 &&
        logical.store.counters.frees == 1 &&
        logical.store.counters.reuses == 0 &&
        physical.store.counters.allocs == 1 &&
        physical.store.counters.frees == 0 &&
        physical.store.counters.reuses == 1 &&
        physical.store.counters.reusedPayloadUnits == 1 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

/-! The state after `takeUnique` has one present credit and already satisfies
the intermediate equation. -/

private def initialMachine (program : Program) : Machine :=
  { heapFuel := 0
    control := .running { definition := program.main } [] }

private def stepToTake (interpretation : Interpretation) : Except Error Machine := do
  let context := Context.ofProgram uniqueReuse schemas
  let first ← step context interpretation (initialMachine uniqueReuse)
  step context interpretation first

private def afterTakeLogical := stepToTake .logical
private def afterTakePhysical := stepToTake .physical

#guard match afterTakeLogical, afterTakePhysical with
  | .ok logical, .ok physical =>
      logical.presentCredits == 1 && physical.presentCredits == 1 &&
        logical.store.live == 0 && physical.store.live == 0 &&
        physical.store.live + physical.store.counters.frees + physical.presentCredits ==
          physical.store.counters.allocs &&
        lawHolds logical.store physical.store physical.presentCredits
  | _, _ => false

/-! ## Credit discard -/

private def uniqueDiscard : Program :=
  { declarations := []
    main :=
      { signature := signature .unique
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .unique nodeCtor #[.lit (.nat 9)],
              .takeUnique (.reg 0) nodeCtor,
              .discardCredit 0]
            terminator := .ret (.reg 1) }] } }

#guard validates uniqueDiscard

#guard match run .logical uniqueDiscard 4 0, run .physical uniqueDiscard 4 0 with
  | .ok logical, .ok physical =>
      logical.value == physical.value &&
        logical.store.counters.allocs == 1 &&
        physical.store.counters.allocs == 1 &&
        logical.store.counters.frees == 1 &&
        physical.store.counters.frees == 1 &&
        logical.store.counters.reuses == 0 &&
        physical.store.counters.reuses == 0 &&
        logical.store.live == 0 && physical.store.live == 0 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

/-! ## Hot shared reset and optional-credit branching -/

private def hotReset : Program :=
  { declarations := []
    main :=
      { signature := signature .shared
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .shared nodeCtor #[.lit (.nat 11)],
              .resetShared (.reg 0) nodeCtor]
            terminator := .branchCredit 0
              { target := 1, values := #[.reg 1], credits := #[0] }
              { target := 2, values := #[.reg 1], credits := #[0] } },
          { valueParams := #[.owned .shared]
            creditParams := #[.required layout]
            instructions := #[.allocWith 0 .shared nodeCtor #[.reg 0]]
            terminator := .ret (.reg 1) },
          { valueParams := #[.owned .shared]
            creditParams := #[.optional layout]
            instructions := #[.allocWith 0 .shared nodeCtor #[.reg 0]]
            terminator := .ret (.reg 1) }] } }

#guard validates hotReset

#guard match run .logical hotReset 5 0, run .physical hotReset 5 0 with
  | .ok logical, .ok physical =>
      sameCtorResult logical physical &&
        logical.store.counters.resetAttempts == 1 &&
        physical.store.counters.resetAttempts == 1 &&
        logical.store.counters.hotResets == 1 &&
        physical.store.counters.hotResets == 1 &&
        logical.store.counters.coldResets == 0 &&
        physical.store.counters.coldResets == 0 &&
        physical.store.counters.reuses == 1 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

/-! ## Cold shared reset -/

private def coldReset : Program :=
  { declarations := []
    main :=
      { signature := signature .shared
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .shared nodeCtor #[.lit (.nat 13)],
              .retainShared (.reg 0),
              .resetShared (.reg 0) nodeCtor]
            terminator := .branchCredit 0
              { target := 1, values := #[.reg 1, .reg 2], credits := #[0] }
              { target := 2, values := #[.reg 1, .reg 2], credits := #[0] } },
          { valueParams := #[.owned .shared, .owned .shared]
            creditParams := #[.required layout]
            instructions := #[
              .allocWith 0 .shared nodeCtor #[.reg 1],
              .releaseShared (.reg 0)]
            terminator := .ret (.reg 2) },
          { valueParams := #[.owned .shared, .owned .shared]
            creditParams := #[.optional layout]
            instructions := #[
              .allocWith 0 .shared nodeCtor #[.reg 1],
              .releaseShared (.reg 0)]
            terminator := .ret (.reg 2) }] } }

#guard validates coldReset

#guard match run .logical coldReset 7 2, run .physical coldReset 7 2 with
  | .ok logical, .ok physical =>
      sameCtorResult logical physical &&
        logical.store.counters.resetAttempts == 1 &&
        physical.store.counters.resetAttempts == 1 &&
        logical.store.counters.hotResets == 0 &&
        physical.store.counters.hotResets == 0 &&
        logical.store.counters.coldResets == 1 &&
        physical.store.counters.coldResets == 1 &&
        logical.store.counters.rcops == 3 &&
        physical.store.counters.rcops == 3 &&
        logical.heapRemaining == 0 && physical.heapRemaining == 0 &&
        physical.store.counters.reuses == 0 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

/-! Heap traversal cannot steal control fuel, and control exhaustion is
reported independently of abundant heap fuel. -/

#guard match run .physical coldReset 7 1 with
  | .error .heapFuel => true
  | _ => false

#guard match run .physical coldReset 6 100 with
  | .error .controlFuel => true
  | _ => false

/-! ## Explicit call-stack/PAP execution -/

private def papIdentity : Function :=
  { signature :=
      { params := #[{ world := .shared, passing := .owned }]
        result := .shared
        papSafe := true }
    blocks := #[
      { valueParams := #[.owned .shared]
        creditParams := #[]
        instructions := #[]
        terminator := .ret (.reg 0) }] }

private def papApply : Program :=
  { declarations := [(functionAddress, .fn papIdentity)]
    main :=
      { signature := signature .shared
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .shared nodeCtor #[.lit (.nat 17)],
              .papp functionAddress #[],
              .apply (.reg 1) #[.reg 0]]
            terminator := .ret (.reg 2) }] } }

#guard validates papApply

#guard match run .logical papApply 5 1, run .physical papApply 5 1 with
  | .ok logical, .ok physical =>
      sameCtorResult logical physical &&
        logical.controlRemaining == 0 && physical.controlRemaining == 0 &&
        logical.heapRemaining == 0 && physical.heapRemaining == 0 &&
        logical.store.counters.allocs == 2 &&
        physical.store.counters.allocs == 2 &&
        logical.store.counters.frees == 1 &&
        physical.store.counters.frees == 1 &&
        logical.store.counters.rcops == 1 &&
        physical.store.counters.rcops == 1 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

private def papFirst : Function :=
  { signature :=
      { params := #[
          { world := .shared, passing := .owned },
          { world := .shared, passing := .owned }]
        result := .shared
        papSafe := true }
    blocks := #[
      { valueParams := #[.owned .shared, .owned .shared]
        creditParams := #[]
        instructions := #[.releaseShared (.reg 1)]
        terminator := .ret (.reg 0) }] }

/-- Applying one argument to an empty binary PAP must take the under-saturated
branch and allocate a longer PAP before the second application saturates it. -/
private def papUnderApply : Program :=
  { declarations := [(functionAddress, .fn papFirst)]
    main :=
      { signature := signature .shared
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .shared nodeCtor #[.lit (.nat 17)],
              .alloc .shared nodeCtor #[.lit (.nat 23)],
              .papp functionAddress #[],
              .apply (.reg 2) #[.reg 0],
              .apply (.reg 3) #[.reg 1]]
            terminator := .ret (.reg 4) }] } }

#guard validates papUnderApply

#guard match run .logical papUnderApply 8 5,
    run .physical papUnderApply 8 5 with
  | .ok logical, .ok physical =>
      sameCtorResult logical physical &&
        returnedCtor logical == some (nodeCtor, #[.lit (.nat 17)]) &&
        logical.controlRemaining == 0 && physical.controlRemaining == 0 &&
        logical.heapRemaining == 0 && physical.heapRemaining == 0 &&
        logical.store.counters.allocs == 4 &&
        physical.store.counters.allocs == 4 &&
        logical.store.counters.frees == 3 &&
        physical.store.counters.frees == 3 &&
        logical.store.counters.rcops == 5 &&
        physical.store.counters.rcops == 5 &&
        logical.store.peakLiveNodes == 3 &&
        physical.store.peakLiveNodes == 3 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

/-- Over-applying an identity PAP to another identity PAP and a constructor
forces the first callee return through `applyMore`, which then saturates the
returned PAP with the residual constructor owner. -/
private def papOverApply : Program :=
  { declarations := [(functionAddress, .fn papIdentity)]
    main :=
      { signature := signature .shared
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .alloc .shared nodeCtor #[.lit (.nat 31)],
              .papp functionAddress #[],
              .papp functionAddress #[],
              .apply (.reg 2) #[.reg 1, .reg 0]]
            terminator := .ret (.reg 3) }] } }

#guard validates papOverApply

#guard match run .logical papOverApply 7 2,
    run .physical papOverApply 7 2 with
  | .ok logical, .ok physical =>
      sameCtorResult logical physical &&
        returnedCtor logical == some (nodeCtor, #[.lit (.nat 31)]) &&
        logical.controlRemaining == 0 && physical.controlRemaining == 0 &&
        logical.heapRemaining == 0 && physical.heapRemaining == 0 &&
        logical.store.counters.allocs == 3 &&
        physical.store.counters.allocs == 3 &&
        logical.store.counters.frees == 2 &&
        physical.store.counters.frees == 2 &&
        logical.store.counters.rcops == 2 &&
        physical.store.counters.rcops == 2 &&
        logical.store.peakLiveNodes == 3 &&
        physical.store.peakLiveNodes == 3 &&
        lawHolds logical.store physical.store 0
  | _, _ => false

end Ix.Compiler.IxIR2.Eval.Examples
