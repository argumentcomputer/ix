import IxCC.X86.SafeControl
import IxCC.X86.Constructors

/-!
# Checked typed steps inside a frame

One `Stream.SafeSteps` step per instruction shape the stacked program runs,
stated on `inFrame` machines (a running PC at a block and offset, with the
active ghost return frames): a table row other than a call or a fused pair
(its footprint must be safe; the mask clears what it writes), a fused pair,
a direct call, `unwind`, and a top-level `ret`.
-/

namespace IxCC.X86

open IxCC.X86.Stream

theorem inFrame_eq {m : Machine} (running : m.status = .running) :
    m = inFrame m.core m.pc.block m.pc.offset.toNat m.returns := by
  obtain ⟨core, ⟨block, offset⟩, returns, status⟩ := m
  simp only at running
  subst running
  simp [inFrame]

/-- An instruction other than a call, a runtime call or a fused pair is
checked by its operation's footprint, and the mask clears what it writes. -/
theorem Straight.Segment.safeAt {checked : Checked} {block : BlockId} {offset : Nat} {ins : Instr}
    (segment : Straight.Segment checked block offset [ins]) (fits : offset < UInt32.size)
    (plain : ∀ t, ins ≠ .call t) (noRuntime : ∀ i, ins ≠ .callRuntime i) (single : ins.single = true)
    {holes : Holes} {returns : List ReturnFrame} {core : Core}
    (safe : OperationSafe holes returns (Encode.instructionOperation ins) core) :
    SafeAt checked.program holes (inFrame core block offset returns) ∧
      holeStep checked.program (inFrame core block offset returns) holes =
        nextHoles holes (Encode.instructionOperation ins) core := by
  obtain ⟨code, found, reads⟩ := segment
  have head := reads 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at head
  have hoff : (UInt32.ofNat offset).toNat = offset := UInt32.toNat_ofNat_of_lt' fits
  constructor
  · simp only [SafeAt, inFrame, hoff, found, head]
    cases ins with
    | call t => exact absurd rfl (plain t)
    | callRuntime i => exact absurd rfl (noRuntime i)
    | fused => simp [Instr.single] at single
    | op o args => exact safe
    | unwind source => exact safe
  · simp only [holeStep, inFrame, hoff, found, head]
    cases ins with
    | call t => exact absurd rfl (plain t)
    | callRuntime i => exact absurd rfl (noRuntime i)
    | fused => simp [Instr.single] at single
    | op o args => rfl
    | unwind source => rfl

/-- A row instruction that runs: one checked step to the next offset. -/
theorem Straight.Segment.safe_op {checked : Checked} {block : BlockId} {offset : Nat} {o : Op} {args : List Arg}
    (segment : Straight.Segment checked block offset [.op o args]) (fits : offset + 1 < UInt32.size)
    (runtime : Runtime) {holes : Holes} {returns : List ReturnFrame} {core core' : Core} {flags : ByteEval.Flags}
    (safe : OperationSafe holes returns (.op o args) core) (runs : o.exec args core {} = .ok (core', flags)) :
    SafeSteps runtime checked 1 holes (inFrame core block offset returns)
      (nextHoles holes (.op o args) core) (inFrame core' block (offset + 1) returns) := by
  obtain ⟨hsafe, hholes⟩ := segment.safeAt (by omega) (fun _ => nofun) (fun _ => nofun) rfl safe
  change _ = nextHoles holes (.op o args) core at hholes
  rw [← hholes]
  refine SafeSteps.single hsafe ?_
  rw [segment.instruction_inFrame (by omega)]
  have hc : (inFrame core block offset returns).core = core := rfl
  simp only [executeInstr, hc, runs, Machine.afterRow]
  exact inFrame_advance _ _ _ _ fits

/-- A fused pair that runs: one checked step to the next offset. -/
theorem Straight.Segment.safe_fused {checked : Checked} {block : BlockId} {offset : Nat} {p c : Op}
    {pargs cargs : List Arg} (segment : Straight.Segment checked block offset [.fused p pargs c cargs])
    (fits : offset + 1 < UInt32.size) (runtime : Runtime) {holes : Holes} {returns : List ReturnFrame}
    {core core₁ core' : Core} {flags flags' : ByteEval.Flags}
    (psafe : OperationSafe holes returns (.op p pargs) core) (csafe : OperationSafe holes returns (.op c cargs) core)
    (prun : p.exec pargs core {} = .ok (core₁, flags)) (crun : c.exec cargs core₁ flags = .ok (core', flags')) :
    SafeSteps runtime checked 1 holes (inFrame core block offset returns)
      (nextHoles holes (.op c cargs) core) (inFrame core' block (offset + 1) returns) := by
  obtain ⟨code, found, reads⟩ := segment
  have head := reads 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero] at head
  have hoff : (UInt32.ofNat offset).toNat = offset := UInt32.toNat_ofNat_of_lt' (by omega)
  have hsafe : SafeAt checked.program holes (inFrame core block offset returns) := by
    simp only [SafeAt, inFrame, hoff, found, head]
    exact ⟨psafe, csafe⟩
  have hholes : holeStep checked.program (inFrame core block offset returns) holes =
      nextHoles holes (.op c cargs) core := by
    simp only [holeStep, inFrame, hoff, found, head]
  rw [← hholes]
  refine SafeSteps.single hsafe ?_
  simp only [step, inFrame, hoff, found, head, executeInstr, prun, crun, Machine.afterRow]
  exact inFrame_advance _ _ _ _ fits

/-- An instruction other than a call, a runtime call or a fused pair whose
execution advances with a new core: one checked step. -/
theorem Straight.Segment.safe_exec {checked : Checked} {block : BlockId} {offset : Nat} {ins : Instr}
    (segment : Straight.Segment checked block offset [ins]) (fits : offset + 1 < UInt32.size)
    (plain : ∀ t, ins ≠ .call t) (noRuntime : ∀ i, ins ≠ .callRuntime i) (single : ins.single = true)
    (runtime : Runtime) {holes holes' : Holes} {returns : List ReturnFrame} {core core' : Core}
    (safe : OperationSafe holes returns (Encode.instructionOperation ins) core)
    (next : nextHoles holes (Encode.instructionOperation ins) core = holes')
    (exec : executeInstr runtime checked ins (inFrame core block offset returns) =
      (inFrame core block offset returns).advanceWith core') :
    SafeSteps runtime checked 1 holes (inFrame core block offset returns) holes'
      (inFrame core' block (offset + 1) returns) := by
  obtain ⟨hsafe, hholes⟩ := segment.safeAt (by omega) plain noRuntime single safe
  rw [← next, ← hholes]
  refine SafeSteps.single hsafe ?_
  rw [segment.instruction_inFrame (by omega), exec]
  exact inFrame_advance _ _ _ _ fits

theorem slotReads_noMem {core : Core} :
    ∀ {slots : List Slot} {args : List Arg}, (∀ a ∈ args, ∀ m, a ≠ .mem m) → slotReads core slots args = []
  | [], _, _ => by cases ‹List Arg› <;> rfl
  | _ :: _, [], _ => rfl
  | s :: ss, a :: as, h => by
      have ha : a.access core s.width = [] := by
        cases a with
        | mem m => exact absurd rfl (h _ (by simp) m)
        | _ => rfl
      have ih := slotReads_noMem (core := core) (slots := ss) (args := as)
        (fun b hb m => h b (by simp [hb]) m)
      simp only [slotReads, ih, List.append_nil]
      split <;> simp [ha]

theorem slotWrites_noMem {core : Core} :
    ∀ {slots : List Slot} {args : List Arg}, (∀ a ∈ args, ∀ m, a ≠ .mem m) → slotWrites core slots args = []
  | [], _, _ => by cases ‹List Arg› <;> rfl
  | _ :: _, [], _ => rfl
  | s :: ss, a :: as, h => by
      have ha : a.access core s.width = [] := by
        cases a with
        | mem m => exact absurd rfl (h _ (by simp) m)
        | _ => rfl
      have ih := slotWrites_noMem (core := core) (slots := ss) (args := as)
        (fun b hb m => h b (by simp [hb]) m)
      simp only [slotWrites, ih, List.append_nil]
      split <;> simp [ha]

/-- A row without memory operands or stack traffic touches no memory. -/
theorem footprint_noMem {o : Op} {args : List Arg} (core : Core) (stack : (desc o).stack = .none)
    (h : ∀ a ∈ args, ∀ m, a ≠ .mem m) :
    Stream.operationReads (.op o args) core = [] ∧ Stream.operationWrites (.op o args) core = [] := by
  simp [Stream.operationReads, Stream.operationWrites, Op.reads, Op.writes, Op.pops, Op.pushes, stack,
    slotReads_noMem h, slotWrites_noMem h]

/-! ## Segments -/

theorem Straight.Segment.of_block {checked : Checked} {block : BlockId} {code : Block}
    (found : checked.program.blocks[block.toNat]? = some code) {pre mid post : List Instr}
    (h : code.instructions.toList = pre ++ mid ++ post) : Straight.Segment checked block pre.length mid := by
  refine ⟨code, found, fun i hi => ?_⟩
  rw [← Array.getElem?_toList, h, List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi]

theorem Straight.Segment.left {checked : Checked} {block : BlockId} {offset : Nat} {xs ys : List Instr}
    (segment : Straight.Segment checked block offset (xs ++ ys)) : Straight.Segment checked block offset xs := by
  obtain ⟨code, found, reads⟩ := segment
  refine ⟨code, found, fun i hi => ?_⟩
  rw [reads i (by simp; omega), List.getElem?_append_left hi]

theorem Straight.Segment.right {checked : Checked} {block : BlockId} {offset : Nat} {xs ys : List Instr}
    (segment : Straight.Segment checked block offset (xs ++ ys)) :
    Straight.Segment checked block (offset + xs.length) ys := by
  obtain ⟨code, found, reads⟩ := segment
  refine ⟨code, found, fun i hi => ?_⟩
  have := reads (xs.length + i) (by simp; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this
  rw [Nat.add_assoc]
  exact this

/-- A footprint with no memory operand is safe and leaves the mask alone. -/
theorem OperationSafe.of_noMemory {holes : Holes} {returns : List ReturnFrame} {o : Op} {args : List Arg}
    {core : Core} (reads : Stream.operationReads (.op o args) core = [])
    (writes : Stream.operationWrites (.op o args) core = []) :
    OperationSafe holes returns (.op o args) core ∧ nextHoles holes (.op o args) core = holes := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [reads]
  · simp [writes]
  · simp [nextHoles, writes, clearAccesses]

/-- A top-level `ret`: the machine halts with `rax`, its core unchanged. -/
theorem BlockCode.safe_ret_top {checked : Checked} {block : BlockId} {instructions : List Instr}
    (code : BlockCode checked block instructions .ret) (runtime : Runtime) (core : Core) (holes : Holes)
    (data : ReadableData holes (core.readReg .rsp) 8) :
    SafeSteps runtime checked 1 holes (inFrame core block instructions.length [])
      holes { inFrame core block instructions.length [] with status := .halted (core.readReg .rax) } := by
  have safe : SafeAt checked.program holes (inFrame core block instructions.length []) := by
    simpa [SafeAt, inFrame, UInt32.toNat_ofNat_of_lt' code.fits, code.found] using data
  have one := SafeSteps.single safe (by
    rw [code.terminator_inFrame]
    rfl : step runtime checked (inFrame core block instructions.length []) =
      { inFrame core block instructions.length [] with status := .halted (core.readReg .rax) })
  simpa only [code.holeStep, terminatorHoles] using one

end IxCC.X86
