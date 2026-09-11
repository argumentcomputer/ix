import Ix.Compiler.X86.PhysicalScalarCapturedHeap

namespace Ix.Compiler.X86.PhysicalScalar.Captured

/-- These limits bound the closed module initializer, before any runtime
argument exists. They do not bound general allocating native programs. -/
structure Limits where
  control : Nat := 4096
  heap : Nat := 16384
  slots : Nat := 256
  deriving Repr, Inhabited

structure Initialized (program : IxIR2.Program)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema) (limits : Limits) where
  result : IxIR2.Eval.Result
  nullary : program.main.signature.params.size = 0
  nonempty : program.main.blocks.isEmpty = false
  run : IxIR2.Eval.runMain (IxIR2.Eval.Context.ofProgram program schemas (fun _ _ => none))
    .physical program limits.control limits.heap = .ok result
  address : Ixon.Address
  capture : Word
  heap : Heap result.store.heap address capture
  value : result.value = .loc heap.location
  target : IxIR2.Function
  declared : lookup program address = some (.fn target)
  safe : target.signature.papSafe = true
  binary : target.signature.params.size = 2
  allocationSlots : result.store.heap.allocs = result.store.heap.nodes.size
  noReuse : result.store.heap.reuses = 0
  accounted : result.store.heap.frees + 1 = result.store.heap.allocs
  bounded : result.store.heap.nodes.size ≤ limits.slots

/-- A successful check retains the actual initializer execution as a kernel
proof. Only its single live, shared PAP and exact scalar capture are admitted. -/
def checkInitializer (program : IxIR2.Program)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema) (limits : Limits := {}) :
    Except String (Initialized program schemas limits) := do
  if nullary : program.main.signature.params.size = 0 then
    if nonempty : program.main.blocks.isEmpty = false then
      match run : IxIR2.Eval.runMain (IxIR2.Eval.Context.ofProgram program schemas (fun _ _ => none))
          .physical program limits.control limits.heap with
      | .error error => throw s!"captured scalar initializer failed: {reprStr error}"
      | .ok result =>
        match value : result.value with
        | .loc location =>
          match found : result.store.heap.get? location with
          | some ⟨.shared, 1, .papN address 2 #[.lit (.nat number)]⟩ =>
            match encoded : ExactNat.encode number with
            | none => throw "captured scalar initializer capture exceeds Word range"
            | some capture =>
              if sole : exclusive result.store.heap location = true then
                match declared : lookup program address with
                | some (.fn target) =>
                  if safe : target.signature.papSafe = true then
                    if binary : target.signature.params.size = 2 then
                      if allocationSlots : result.store.heap.allocs = result.store.heap.nodes.size then
                        if noReuse : result.store.heap.reuses = 0 then
                          if accounted : result.store.heap.frees + 1 = result.store.heap.allocs then
                            if bounded : result.store.heap.nodes.size ≤ limits.slots then
                              return {
                                result, nullary, nonempty, run, address, capture
                                heap := { location
                                          found := by simpa [rval, ExactNat.encode_some_iff.mp encoded] using found
                                          exclusive := exclusive_sound sole }
                                value, target, declared, safe, binary, allocationSlots, noReuse, accounted, bounded }
                            else throw "captured scalar initializer exceeds the slot limit"
                          else throw "captured scalar initializer has unaccounted allocations"
                        else throw "captured scalar initializer reused storage"
                      else throw "captured scalar initializer allocation count differs from its slots"
                    else throw "captured scalar initializer target must have two parameters"
                  else throw "captured scalar initializer target is not PAP-safe"
                | _ => throw "captured scalar initializer target is missing"
              else throw "captured scalar initializer leaves additional live heap values"
          | _ => throw "captured scalar initializer must return one shared PAP with one Word capture and RC one"
        | _ => throw "captured scalar initializer did not return a closure"
    else throw "captured scalar initializer has no entry block"
  else throw "captured scalar initializer must be nullary"

theorem Initialized.reclaimed {program schemas limits} (source : Initialized program schemas limits) :
    emptyHeap source.heap.spent ∧ source.heap.spent.frees = source.heap.spent.allocs ∧
      source.heap.spent.allocs = source.result.store.heap.allocs ∧
      source.heap.spent.rcops = source.result.store.heap.rcops + 1 ∧
      source.heap.spent.reuses = 0 := by
  exact ⟨source.heap.spent_empty, source.accounted, rfl, rfl, source.noReuse⟩

end Ix.Compiler.X86.PhysicalScalar.Captured
