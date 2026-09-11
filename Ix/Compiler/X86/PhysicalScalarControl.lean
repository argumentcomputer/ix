import Ix.Compiler.X86.PhysicalScalarValues

namespace Ix.Compiler.X86.PhysicalScalar
open IxIR2.Eval

inductive Exit where
  | halt
  | resume (caller : Frame) (rest : List Continuation)

def Exit.stack : Exit → List Continuation
  | .halt => []
  | .resume caller rest => .resume caller :: rest

def Exit.result (exit : Exit) (word : Word) : Control :=
  match exit with
  | .halt => .halted (rval word)
  | .resume caller rest => .running { caller with values := caller.values.push (rval word) } rest

def frame (definition : IxIR2.Function) (block pc : Nat) (values : Array Word) : Frame :=
  { definition, block, pc, values := values.map rval }

/-- A function suffix can execute under an arbitrary suspended caller and
arbitrary heap. Scalar releases consume traversal fuel but preserve the whole
store. Both budgets are constructed by the proof; neither is an input-specific
certificate supplied to the selector. -/
def Runs (context : Context) (mode : Interpretation) (start : Frame) (word : Word) : Prop :=
  ∀ (store : Store) (exit : Exit) (suffix : Nat), ∃ controlCost heapCost,
    IxIR2.Eval.Steps context mode controlCost
      { store, heapFuel := heapCost + suffix, control := .running start exit.stack }
      { store, heapFuel := suffix, control := exit.result word }

theorem Runs.prepend {context mode before after word} (rest : Runs context mode after word) (cost : Nat)
    (step : ∀ (store : Store) (exit : Exit) (fuel : Nat), Step context mode
      { store, heapFuel := cost + fuel, control := .running before exit.stack }
      { store, heapFuel := fuel, control := .running after exit.stack }) : Runs context mode before word := by
  intro store exit suffix
  obtain ⟨controls, heap, executed⟩ := rest store exit suffix
  refine ⟨controls + 1, cost + heap, ?_⟩
  simpa [Nat.add_assoc] using IxIR2.Eval.Steps.cons rfl (step store exit (heap + suffix)) executed

theorem Runs.ret {context mode definition block pc values atom body word}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .ret atom) (resolved : resolveAtom (values.map rval) atom = .ok (rval word)) :
    Runs context mode (frame definition block pc values) word := by
  intro store exit suffix
  refine ⟨1, 0, ?_⟩
  cases exit with
  | halt =>
    have step := Step.retHalt (context := context) (interpretation := mode)
      (machine := { store, heapFuel := suffix, control := .running (frame definition block pc values) [] })
      rfl blockAt endAt term resolved rfl rfl
    simpa [Exit.stack, Exit.result] using step.toSteps rfl
  | resume caller rest =>
    have step := Step.retResume (context := context) (interpretation := mode)
      (machine := { store, heapFuel := suffix, control := .running (frame definition block pc values) (.resume caller :: rest) })
      rfl blockAt endAt term resolved rfl rfl
    simpa [Exit.stack, Exit.result] using step.toSteps rfl

theorem Runs.move {context mode definition block pc values atom body word result}
    (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.move atom))
    (resolved : resolveAtom (values.map rval) atom = .ok (rval word))
    (rest : Runs context mode (frame definition block (pc + 1) (values.push word)) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 0
  intro store exit fuel
  obtain ⟨bound, instruction⟩ := Array.getElem?_eq_some_iff.mp instruction
  simpa [frame] using Step.move (context := context) (interpretation := mode)
    (machine := { store, heapFuel := fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt bound instruction resolved

theorem Runs.retain {context mode definition block pc values atom body word result}
    (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.retainShared atom))
    (resolved : resolveAtom (values.map rval) atom = .ok (rval word))
    (rest : Runs context mode (frame definition block (pc + 1) (values.push word)) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 0
  intro store exit fuel
  obtain ⟨bound, instruction⟩ := Array.getElem?_eq_some_iff.mp instruction
  simpa [frame] using Step.retainShared (context := context) (interpretation := mode)
    (machine := { store, heapFuel := fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt bound instruction resolved rfl

theorem Runs.release {context mode definition block pc values atom body word result}
    (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.releaseShared atom))
    (resolved : resolveAtom (values.map rval) atom = .ok (rval word))
    (rest : Runs context mode (frame definition block (pc + 1) values) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 1
  intro store exit fuel
  obtain ⟨bound, instruction⟩ := Array.getElem?_eq_some_iff.mp instruction
  exact Step.releaseShared
    (machine := { store, heapFuel := 1 + fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt bound instruction resolved
    (by simp [releaseShared, releaseSharedWork, rval, Nat.add_comm])

theorem Runs.drop {context mode definition block pc values atom body word result}
    (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.dropUnique atom))
    (resolved : resolveAtom (values.map rval) atom = .ok (rval word))
    (rest : Runs context mode (frame definition block (pc + 1) values) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 1
  intro store exit fuel
  obtain ⟨bound, instruction⟩ := Array.getElem?_eq_some_iff.mp instruction
  exact Step.dropUnique
    (machine := { store, heapFuel := 1 + fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt bound instruction resolved
    (by simp [dropUnique, dropUniqueWork, rval, Nat.add_comm])

theorem edge_transfer {definition block pc values edge arguments implicitWords targets implicitCount}
    (ready : EdgeReady definition edge targets implicitCount)
    (argumentsSize : arguments.size = targets.size) (implicitSize : implicitWords.size = implicitCount)
    (resolved : resolveAtoms (values.map rval) edge.values = .ok (arguments.map rval)) :
    EdgeTransfer (frame definition block pc values) edge (implicitWords.map rval)
      (frame definition edge.target 0 (implicitWords ++ arguments)) := by
  obtain ⟨target, found, arity, credits, targetCredits⟩ := ready
  have step := EdgeTransfer.baseline (frame := frame definition block pc values)
    (implicitValues := implicitWords.map rval) resolved rfl credits found
    (by simpa [argumentsSize, implicitSize] using arity) targetCredits
  simpa [frame] using step

theorem Runs.jump {context mode definition block pc values edge arguments targets body result}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .jump edge) (ready : EdgeReady definition edge targets 0)
    (argumentsSize : arguments.size = targets.size)
    (resolved : resolveAtoms (values.map rval) edge.values = .ok (arguments.map rval))
    (rest : Runs context mode (frame definition edge.target 0 arguments) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 0
  intro store exit fuel
  have transferred := edge_transfer (block := block) (pc := pc) (implicitWords := #[]) ready argumentsSize rfl resolved
  simp only [Array.map_empty, Array.empty_append] at transferred
  simpa using Step.jump (machine := { store, heapFuel := fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt endAt term transferred

theorem Runs.zero {context mode definition block pc values atom peel arguments targets body result}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .switchValue atom #[] (some peel))
    (scrutinee : resolveAtom (values.map rval) atom = .ok (rval 0))
    (ready : EdgeReady definition peel.zero targets 0) (argumentsSize : arguments.size = targets.size)
    (resolved : resolveAtoms (values.map rval) peel.zero.values = .ok (arguments.map rval))
    (rest : Runs context mode (frame definition peel.zero.target 0 arguments) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 0
  intro store exit fuel
  have transferred := edge_transfer (block := block) (pc := pc) (implicitWords := #[]) ready argumentsSize rfl resolved
  simp only [Array.map_empty, Array.empty_append] at transferred
  simpa using Step.switchNatZero (machine := { store, heapFuel := fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt endAt term scrutinee transferred

theorem Runs.successor {context mode definition block pc values atom peel arguments targets body result word}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .switchValue atom #[] (some peel))
    (positive : word ≠ 0) (scrutinee : resolveAtom (values.map rval) atom = .ok (rval word))
    (ready : EdgeReady definition peel.succ targets 1) (argumentsSize : arguments.size = targets.size)
    (resolved : resolveAtoms (values.map rval) peel.succ.values = .ok (arguments.map rval))
    (rest : Runs context mode (frame definition peel.succ.target 0 (#[ExactNat.sub word 1] ++ arguments)) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 0
  intro store exit fuel
  have transferred := edge_transfer (block := block) (pc := pc) (implicitWords := #[ExactNat.sub word 1]) ready argumentsSize rfl resolved
  have nonzero : word.toNat ≠ 0 := by intro eq; exact positive (UInt64.toNat_inj.mp eq)
  have successor : word.toNat - 1 + 1 = word.toNat := by omega
  have scrutinee : resolveAtom (values.map rval) atom = .ok (.lit (.nat (word.toNat - 1 + 1))) := by
    simpa [rval, successor] using scrutinee
  have transferred : EdgeTransfer (frame definition block pc values) peel.succ #[.lit (.nat (word.toNat - 1))]
      (frame definition peel.succ.target 0 (#[ExactNat.sub word 1] ++ arguments)) := by
    simpa [rval, ExactNat.sub_toNat] using transferred
  simpa using Step.switchNatSucc (machine := { store, heapFuel := fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt endAt term scrutinee transferred

theorem Runs.tailCall {context mode definition block pc values address atoms callee arguments body result}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .tailCall address atoms)
    (resolved : resolveAtoms (values.map rval) atoms = .ok (arguments.map rval))
    (declared : context.declarations address = some (.fn callee))
    (arity : arguments.size = callee.signature.params.size) (nonempty : callee.blocks.isEmpty = false)
    (rest : Runs context mode (frame callee 0 0 arguments) result) :
    Runs context mode (frame definition block pc values) result := by
  apply rest.prepend 0
  intro store exit fuel
  simpa [frame] using Step.tailCallFn (context := context) (interpretation := mode)
    (machine := { store, heapFuel := fuel, control := .running (frame definition block pc values) exit.stack })
    rfl blockAt endAt term rfl resolved declared (by simpa using arity) nonempty

theorem Runs.call {context mode definition block pc values address atoms callee arguments body bound result}
    (blockAt : definition.blocks[block]? = some body) (instruction : body.instructions[pc]? = some (.call address atoms))
    (resolved : resolveAtoms (values.map rval) atoms = .ok (arguments.map rval))
    (declared : context.declarations address = some (.fn callee))
    (arity : arguments.size = callee.signature.params.size) (nonempty : callee.blocks.isEmpty = false)
    (called : Runs context mode (frame callee 0 0 arguments) bound)
    (rest : Runs context mode (frame definition block (pc + 1) (values.push bound)) result) :
    Runs context mode (frame definition block pc values) result := by
  intro store exit suffix
  obtain ⟨restControl, restHeap, continuation⟩ := rest store exit suffix
  obtain ⟨callControl, callHeap, executed⟩ := called store (.resume (frame definition block (pc + 1) values) exit.stack) (restHeap + suffix)
  obtain ⟨position, instruction⟩ := Array.getElem?_eq_some_iff.mp instruction
  have entered := Step.callFn (context := context) (interpretation := mode)
    (machine := { store, heapFuel := callHeap + (restHeap + suffix), control := .running (frame definition block pc values) exit.stack })
    rfl blockAt position instruction rfl resolved declared (by simpa using arity) nonempty
  have executed : IxIR2.Eval.Steps context mode callControl
      { store, heapFuel := callHeap + (restHeap + suffix)
        control := .running (frame callee 0 0 arguments) (.resume (frame definition block (pc + 1) values) :: exit.stack) }
      { store, heapFuel := restHeap + suffix, control := .running (frame definition block (pc + 1) (values.push bound)) exit.stack } := by
    simpa [Exit.stack, Exit.result, frame] using executed
  refine ⟨callControl + restControl + 1, callHeap + restHeap, ?_⟩
  simpa [frame, Nat.add_assoc] using IxIR2.Eval.Steps.cons rfl entered (executed.trans continuation)

end Ix.Compiler.X86.PhysicalScalar
