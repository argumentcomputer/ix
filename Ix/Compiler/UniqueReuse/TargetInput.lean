import Ix.Compiler.UniqueReuse.TargetLoop

namespace Ix.Compiler.UniqueReuse.Target

open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval

def inputPrefix (schema : Schema) (values : List Nat) : Array Instr :=
  #[.alloc .unique (nilId schema) #[]] ++
    (values.reverse.mapIdx fun index value =>
      .alloc .unique (consId schema) #[.lit (.nat value), .reg index]).toArray

@[simp] theorem inputPrefix_size (schema : Schema) (values : List Nat) :
    (inputPrefix schema values).size = values.length + 1 := by
  simp [inputPrefix]

theorem inputPrefix_cons (schema : Schema) (head : Nat) (tail : List Nat) :
    inputPrefix schema (head :: tail) = (inputPrefix schema tail).push
      (.alloc .unique (consId schema) #[.lit (.nat head), .reg tail.length]) := by
  simp [inputPrefix, List.reverse_cons]

theorem inputInstructions_eq (plan : Plan) :
    UniqueLower.inputInstructions plan = inputPrefix plan.schema plan.values ++
      #[.alloc .unique (nilId plan.schema) #[]] := rfl

def inputPoint (definition : Function) (store : Store) (fuel pc : Nat) (values : Array RVal) : Machine :=
  { store, heapFuel := fuel, control := .running { definition, pc, values } [] }

structure InputResult (schema : Schema) (store : Store) (values : List Nat)
    (registers : Array RVal) (value : RVal) : Prop where
  owned : RootOwnership store.heap [⟨.unique, value⟩]
  list : ListAt schema store.heap values value
  size : registers.size = values.length + 1
  last : registers[values.length]? = some value
  allocs : store.heap.allocs = values.length + 1
  frees : store.heap.frees = 0
  reuses : store.heap.reuses = 0
  rcops : store.heap.rcops = 0
  live : store.live = values.length + 1
  peak : store.peakLiveNodes = values.length + 1
  attempts : store.resetAttempts = 0
  hot : store.hotResets = 0
  cold : store.coldResets = 0
  payload : store.reusedPayloadUnits = 0

theorem inputSteps (ctx : Context) (mode : Interpretation) (schema : Schema) (values : List Nat)
    (definition : Function) (block : Block) (suffix : Array Instr) (fuel : Nat)
    (schemas : ctx.schemas = UniqueLower.schemas schema)
    (blockAt : definition.blocks[0]? = some block)
    (instructions : block.instructions = inputPrefix schema values ++ suffix) :
    ∃ store registers value,
      Steps ctx mode (values.length + 1) (inputPoint definition {} fuel 0 #[])
        (inputPoint definition store fuel (values.length + 1) registers) ∧
      InputResult schema store values registers value := by
  induction values generalizing suffix with
  | nil =>
      let allocated := ({} : Store).allocNode .unique (.ctorN (nilId schema) #[])
      have head := Step.alloc (context := ctx) (interpretation := mode)
        (arguments := #[])
        (machine := inputPoint definition {} fuel 0 #[]) rfl blockAt
        (by simp [instructions, inputPrefix]; omega)
        (by simp [instructions, inputPrefix])
        (schemas ▸ nilSchemaAt schema) rfl (nilFields schema {})
      refine ⟨allocated.1, #[.loc allocated.2], .loc allocated.2, head.toSteps rfl,
        ownedNilAllocation RootOwnership.empty schema, nilAllocated {} schema,
        rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · exact Store.live_allocNode {} .unique _
      · rfl
  | cons head tail ih =>
      let operation := Instr.alloc .unique (consId schema) #[.lit (.nat head), .reg tail.length]
      have instructions' : block.instructions = inputPrefix schema tail ++ (#[operation] ++ suffix) := by
        rw [instructions, inputPrefix_cons]
        simp only [Array.push_eq_append, Array.append_assoc, operation]
      obtain ⟨middle, registers, tailValue, first, result⟩ := ih (#[operation] ++ suffix) instructions'
      let allocated := middle.allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), tailValue])
      have bound : tail.length + 1 < block.instructions.size := by
        simp [instructions']; omega
      have step := Step.alloc (context := ctx) (interpretation := mode)
        (arguments := #[.lit (.nat head), .reg tail.length])
        (machine := inputPoint definition middle fuel (tail.length + 1) registers) rfl blockAt
        bound
        (by
          change block.instructions[tail.length + 1] = operation
          simp only [instructions']
          rw [Array.getElem_append_right (by simp)]
          simp)
        (schemas ▸ consSchemaAt schema)
        (by simp [resolveAtoms, resolveAtom, result.last]; rfl)
        (consFields result.list head)
      have ready : RootOwnership middle.heap
          (rootsFor .unique (nodeChildren (.ctorN (consId schema) #[.lit (.nat head), tailValue])) ++ []) :=
        RootOwnership.addNoLocation (value := .lit (.nat head)) rfl result.owned
      refine ⟨allocated.1, registers.push (.loc allocated.2), .loc allocated.2, ?_, ready.allocNode trivial,
        consAllocated result.list head, ?_, ?_, ?_, result.frees, result.reuses, result.rcops,
        ?_, ?_, result.attempts, result.hot, result.cold, result.payload⟩
      · exact first.trans (step.toSteps rfl)
      · simp [result.size]
      · simp [show (head :: tail).length = registers.size by simp [result.size]]
      · simp [allocated, IxIR1.Store.allocNode, result.allocs]
      · simp [allocated, Store.live_allocNode, result.live]
      · rw [Store.peakLive_allocNode, Store.live_allocNode, result.peak, result.live]
        simp [Nat.max_eq_right (show tail.length + 1 ≤ tail.length + 1 + 1 by omega)]

end Ix.Compiler.UniqueReuse.Target
