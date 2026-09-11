import Ix.Compiler.IxIR2.Eval

/-! The small closed application graph emitted by the validated scalar source.
Selection recognizes this exact graph, including both addressed declarations;
it does not prune declarations or rewrite the compiler artifact. -/

namespace Ix.Compiler.X86.Select.ScalarApply

open Ix.Compiler Ix.Compiler.IxIR2 Ix.Compiler.IxIR2.Eval
open Ix.Compiler.Ixon (Address)

def worker (word : UInt64) : Function :=
  { signature := { params := #[{ world := .shared, passing := .owned }]
                   result := .shared, papSafe := true }
    blocks := #[{ valueParams := #[.owned .shared], creditParams := #[]
                  instructions := #[.releaseShared (.reg 0)]
                  terminator := .ret (.lit (.nat word.toNat)) }] }

def entry (workerAddress : Address) : Function :=
  { signature := { params := #[], result := .shared, papSafe := true }
    blocks := #[{ valueParams := #[], creditParams := #[]
                  instructions := #[.papp workerAddress #[], .apply (.reg 0) #[.erased]]
                  terminator := .ret (.reg 1) }] }

def program (word : UInt64) (workerAddress entryAddress : Address) : IxIR2.Program :=
  { declarations := [(workerAddress, .fn (worker word)), (entryAddress, .fn (entry workerAddress))]
    main := { signature := { params := #[], result := .shared, papSafe := false }
              blocks := #[{ valueParams := #[], creditParams := #[], instructions := #[]
                            terminator := .tailCall entryAddress #[] }] } }

def context (word : UInt64) (workerAddress entryAddress : Address)
    (schemas : Ixon.Owned → CtorId → Option CtorSchema := fun _ _ => none)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Context :=
  Context.ofProgram (program word workerAddress entryAddress) schemas oracle

def resultStore : Store :=
  { heap := { nodes := #[none], allocs := 1, frees := 1, rcops := 1 }
    peakLiveNodes := 1 }

private def allocatedStore (workerAddress : Address) : Store :=
  (({} : Store).allocNode .shared (.papN workerAddress 1 #[])).1

private def caller (workerAddress : Address) : Frame :=
  { definition := entry workerAddress, pc := 2, values := #[.loc 0] }

private def machine (word : UInt64) (workerAddress entryAddress : Address)
    (heapRemaining : Nat) : Nat → Machine
  | 0 => initialMachine (program word workerAddress entryAddress).main #[] (heapRemaining + 2)
  | 1 => { heapFuel := heapRemaining + 2, control := .running { definition := entry workerAddress } [] }
  | 2 => { store := allocatedStore workerAddress, heapFuel := heapRemaining + 2
           control := .running { definition := entry workerAddress, pc := 1, values := #[.loc 0] } [] }
  | 3 => { store := resultStore, heapFuel := heapRemaining + 1
           control := .running { definition := worker word, values := #[.erased] } [.resume (caller workerAddress)] }
  | 4 => { store := resultStore, heapFuel := heapRemaining
           control := .running { definition := worker word, pc := 1, values := #[.erased] } [.resume (caller workerAddress)] }
  | 5 => { store := resultStore, heapFuel := heapRemaining
           control := .running { definition := entry workerAddress, pc := 2
                                 values := #[.loc 0, .lit (.nat word.toNat)] } [] }
  | _ => { store := resultStore, heapFuel := heapRemaining, control := .halted (.lit (.nat word.toNat)) }

/-- The actual compiler graph takes six control steps, allocating and
reclaiming one PAP. The proof is uniform in the scalar and both addresses. -/
theorem steps (word : UInt64) (workerAddress entryAddress : Address)
    (distinct : workerAddress ≠ entryAddress) (interpretation : Interpretation)
    (heapRemaining : Nat)
    (schemas : Ixon.Owned → CtorId → Option CtorSchema := fun _ _ => none)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) :
    Steps (context word workerAddress entryAddress schemas oracle) interpretation 6
      (machine word workerAddress entryAddress heapRemaining 0)
      (machine word workerAddress entryAddress heapRemaining 6) := by
  have workerAt : (context word workerAddress entryAddress schemas oracle).declarations workerAddress =
      some (.fn (worker word)) := by simp [context, Context.ofProgram, program]
  have entryAt : (context word workerAddress entryAddress schemas oracle).declarations entryAddress =
      some (.fn (entry workerAddress)) := by simp [context, Context.ofProgram, program, distinct]
  have first : Step (context word workerAddress entryAddress schemas oracle) interpretation
      (machine word workerAddress entryAddress heapRemaining 0)
      (machine word workerAddress entryAddress heapRemaining 1) := by
    apply StepCase.step
    refine .terminator (block := (program word workerAddress entryAddress).main.blocks[0]'(by simp [program]))
      rfl rfl rfl ?_
    exact .tailCallFn (by simp [NoLiveCredits]) rfl entryAt rfl rfl
  have second : Step (context word workerAddress entryAddress schemas oracle) interpretation
      (machine word workerAddress entryAddress heapRemaining 1)
      (machine word workerAddress entryAddress heapRemaining 2) := by
    apply StepCase.step
    refine .instruction (block := (entry workerAddress).blocks[0]'(by simp [entry])) rfl (by simp [entry]) rfl ?_
    exact .pappFn (by simp [NoLiveCredits]) workerAt rfl rfl (by simp [worker])
  have third : Step (context word workerAddress entryAddress schemas oracle) interpretation
      (machine word workerAddress entryAddress heapRemaining 2)
      (machine word workerAddress entryAddress heapRemaining 3) := by
    apply StepCase.step
    refine .instruction (block := (entry workerAddress).blocks[0]'(by simp [entry])) rfl (by simp [entry]) rfl ?_
    refine .apply (by simp [NoLiveCredits]) rfl rfl ?_
    have transfer := ApplyTransferCase.papFn
      (context := context word workerAddress entryAddress schemas oracle) (interpretation := interpretation)
      (store := allocatedStore workerAddress) (heapFuel := heapRemaining + 2)
      (arguments := #[.erased]) (resume := caller workerAddress) (stack := [])
      (location := 0) (box := { world := .shared, rc := 1, node := .papN workerAddress 1 #[] })
      (captured := #[]) (retainedStore := allocatedStore workerAddress)
      (releasedStore := resultStore) (outHeapFuel := heapRemaining + 1)
      rfl rfl rfl (by decide) rfl rfl (by decide) workerAt rfl rfl rfl
    exact transfer.transfer
  have fourth : Step (context word workerAddress entryAddress schemas oracle) interpretation
      (machine word workerAddress entryAddress heapRemaining 3)
      (machine word workerAddress entryAddress heapRemaining 4) := by
    apply StepCase.step
    refine .instruction (block := (worker word).blocks[0]'(by simp [worker])) rfl (by simp [worker]) rfl ?_
    exact .releaseShared rfl (by cases heapRemaining <;> rfl)
  have fifth : Step (context word workerAddress entryAddress schemas oracle) interpretation
      (machine word workerAddress entryAddress heapRemaining 4)
      (machine word workerAddress entryAddress heapRemaining 5) := by
    apply StepCase.step
    refine .terminator (block := (worker word).blocks[0]'(by simp [worker])) rfl rfl rfl ?_
    exact .retResume rfl (by simp [NoLiveCredits]) rfl
  have sixth : Step (context word workerAddress entryAddress schemas oracle) interpretation
      (machine word workerAddress entryAddress heapRemaining 5)
      (machine word workerAddress entryAddress heapRemaining 6) := by
    apply StepCase.step
    refine .terminator (block := (entry workerAddress).blocks[0]'(by simp [entry])) rfl rfl rfl ?_
    exact .retHalt rfl (by simp [NoLiveCredits]) rfl
  exact .cons rfl first (.cons rfl second (.cons rfl third
    (.cons rfl fourth (.cons rfl fifth (.cons rfl sixth (.refl _))))))

theorem runs (word : UInt64) (workerAddress entryAddress : Address)
    (distinct : workerAddress ≠ entryAddress) (interpretation : Interpretation)
    (controlRemaining heapRemaining : Nat)
    (schemas : Ixon.Owned → CtorId → Option CtorSchema := fun _ _ => none)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) :
    runMain (context word workerAddress entryAddress schemas oracle) interpretation
      (program word workerAddress entryAddress) (6 + controlRemaining) (heapRemaining + 2) =
      .ok { store := resultStore, value := .lit (.nat word.toNat)
            controlRemaining, heapRemaining } := by
  rw [runMain_eq_runMachine rfl rfl]
  have run := (steps word workerAddress entryAddress distinct interpretation heapRemaining schemas oracle).runMachine
    (controlFuel := controlRemaining)
  change runMachine _ _ _ (machine word workerAddress entryAddress heapRemaining 0) = _
  rw [run]
  cases controlRemaining <;> rfl

end Ix.Compiler.X86.Select.ScalarApply
