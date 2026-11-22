import IxCC.X86.Eval

/-! Executable checks for the local x86-64 v0 target semantics. -/

namespace IxCC.X86.Examples

#guard SysV.functionEntryAligned 0x1008
#guard SysV.callSiteAligned (0x1008 - 8)

def runStatus (program : Program) (runtime : Runtime) (fuel : Nat)
    (core : Core) : Option Status :=
  match program.check with
  | .error _ => none
  | .ok checked => some (runFrom runtime checked fuel core).status

def arithmeticProgram : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[
          .mov .w64 .rax (.imm 40),
          .alu .add .w64 .rax (.imm 2)]
        terminator :=
          .compare
            { width := .w64, left := .rax, right := .imm 42 }
            .eq 1 2 },
      { instructions := #[], terminator := .ret },
      { instructions := #[.mov .w64 .rax (.imm 0)],
        terminator := .ret }] }

def arithmeticBranchAccepted : Bool :=
  runStatus arithmeticProgram Runtime.rejecting 8 (Core.empty 0x1008) ==
    some (.halted 42)

#guard arithmeticBranchAccepted

def stackProgram : Program :=
  let frame : FrameSize := { units16 := 1 }
  let slot : StackSlot := { index := 0 }
  { entry := 0
    blocks := #[
      { instructions := #[
          .push .rbp,
          .mov .w64 .rbp (.reg .rsp),
          .allocFrame frame,
          .mov .w64 .rax (.imm 21),
          .spill slot .rax,
          .mov .w64 .rax (.imm 0),
          .reload .rax slot,
          .alu .add .w64 .rax (.imm 21),
          .freeFrame frame,
          .pop .rbp]
        terminator := .ret }] }

def stackRoundtripAccepted : Bool :=
  match stackProgram.check with
  | .error _ => false
  | .ok checked =>
      let result := runFrom Runtime.rejecting checked 16 (Core.empty 0x1008)
      result.status == .halted 42 &&
        result.core.readReg .rsp == 0x1008 &&
        result.core.readReg .rbp == 0

#guard stackRoundtripAccepted

def callProgram : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[
          .push .rbp,
          .call 1,
          .pop .rbp,
          .alu .add .w64 .rax (.imm 2)]
        terminator := .ret },
      { instructions := #[.mov .w64 .rax (.imm 40)]
        terminator := .ret }] }

def directCallAccepted : Bool :=
  match callProgram.check with
  | .error _ => false
  | .ok checked =>
      let result := runFrom Runtime.rejecting checked 10 (Core.empty 0x1008)
      result.status == .halted 42 &&
        result.core.readReg .rsp == 0x1008 &&
        result.returns.isEmpty

#guard directCallAccepted

def clobberProgram : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[.push .rbp, .call 1, .pop .rbp], terminator := .ret },
      { instructions := #[.mov .w64 .rbx (.imm 1)], terminator := .ret }] }

def calleeSavedViolationTraps : Bool :=
  runStatus clobberProgram Runtime.rejecting 8 (Core.empty 0x1008) ==
    some (.trapped .calleeSavedClobber)

#guard calleeSavedViolationTraps

def fixtureRuntime : Runtime where
  invoke intrinsic arguments memory :=
    match intrinsic with
    | .allocate =>
        if arguments == #[16, 8] then
          .ok
            { memory
              result := 0x2000
              clobber := fun _ => 0 }
        else
          .error 1
    | _ => .error 2

def runtimeProgram : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[
          .push .rbp,
          .mov .w64 .rdi (.imm 16),
          .mov .w64 .rsi (.imm 8),
          .callRuntime .allocate,
          .pop .rbp]
        terminator := .ret }] }

def runtimeCallAccepted : Bool :=
  runStatus runtimeProgram fixtureRuntime 10 (Core.empty 0x1008) ==
    some (.halted 0x2000)

#guard runtimeCallAccepted

def invalidTargetProgram : Program :=
  { entry := 0
    blocks := #[{ instructions := #[], terminator := .jump 1 }] }

def invalidTargetRejected : Bool :=
  match invalidTargetProgram.check with
  | .error .malformedControl => true
  | _ => false

#guard invalidTargetRejected

def littleEndianAccepted : Bool :=
  let memory := Memory.flat.write64 0x100 0x8877665544332211
  memory.bytes 0x100 == 0x11 &&
    memory.bytes 0x107 == 0x88 &&
    memory.read64 0x100 == 0x8877665544332211

#guard littleEndianAccepted

def unmappedLoadProgram : Program :=
  { entry := 0
    blocks := #[
      { instructions := #[
          .load .w64 .rax { base := none, displacement := 0x100 }]
        terminator := .ret }] }

def unmappedLoadTraps : Bool :=
  match unmappedLoadProgram.check with
  | .error _ => false
  | .ok checked =>
      let core : Core :=
        { registers := Registers.zero.set .rsp 0x1000
          memory := Memory.unmapped }
      (runFrom Runtime.rejecting checked 4 core).status ==
        .trapped (.memoryFault
          { access := .read, address := 0x100, bytes := 8 })

#guard unmappedLoadTraps

def misalignedCallTraps : Bool :=
  runStatus callProgram Runtime.rejecting 3 (Core.empty 0x1000) ==
    some (.trapped (.misalignedCall 0x0ff8))

#guard misalignedCallTraps

/-- An export with the failure exit, called as
`ixcc_main(ctx, depth, mode)`. The wrapper saves the callee-saved
registers and its stack pointer at `[ctx]` (`r15 = ctx + 64`) and calls
`f(depth)`. Each level of `f` checks the stack against `stackLimit` at
`[ctx + 8]` (`lea r11, [rsp − 64]; cmp r11, [r15 − 56]; jb fail₂`) and
recurses; at depth 0 it returns 42 (status 0, value 42) when `mode` is 0 and
fails with status 1 otherwise. Failures leave through the exit group's
`unwind [r15 − 64]` with `rax:rdx = status:0`. -/
def unwindProgram : Program :=
  let entrySlot : MemAddr := { base := some .r15, displacement := 0xffffffc0 }
  let stackLimit : MemAddr := { base := some .r15, displacement := 0xffffffc8 }
  { entry := 0
    blocks := #[
      -- 0: the export wrapper.
      { instructions := #[.push .rbx, .push .rbp, .push .r12, .push .r13, .push .r14, .push .r15,
          .alu .sub .w64 .rsp (.imm 8), .lea .r15 { base := some .rdi, displacement := 64 },
          .store .w64 entrySlot .rsp, .call 4, .mov .w64 .rdx (.reg .rax), .alu .xor .w32 .rax (.reg .rax)]
        terminator := .jump 3 },
      -- 1: fail₁ (status 1).
      { instructions := #[.mov .w32 .rax (.imm 1)], terminator := .jump 2 },
      -- 2: the failure exit.
      { instructions := #[.unwind entrySlot, .alu .xor .w32 .rdx (.reg .rdx)], terminator := .jump 3 },
      -- 3: the epilogue.
      { instructions := #[.alu .add .w64 .rsp (.imm 8), .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbp,
          .pop .rbx]
        terminator := .ret },
      -- 4: f's stack check.
      { instructions := #[.lea .r11 { base := some .rsp, displacement := 0xffffffc0 }]
        terminator := .branch { mn := .cmp, w := .w64, form := .RM } [.reg .r11, .mem stackLimit] .unsignedLt 8 5 },
      -- 5: base case or recursion.
      { instructions := #[], terminator := .compare { width := .w64, left := .rsi, right := .imm 0 } .eq 6 7 },
      -- 6: succeed or fail by mode.
      { instructions := #[], terminator := .compare { width := .w64, left := .rdx, right := .imm 0 } .eq 9 1 },
      -- 7: recurse.
      { instructions := #[.alu .sub .w64 .rsi (.imm 1), .push .rbp, .call 4, .pop .rbp], terminator := .ret },
      -- 8: fail₂ (status 2, stack).
      { instructions := #[.mov .w32 .rax (.imm 2)], terminator := .jump 2 },
      -- 9: the base case's result.
      { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }

def unwindCore (depth mode : Word) : Core := ((Core.empty 0x1008).setReg .rsi depth).setReg .rdx mode

def unwindExitAccepted : Bool :=
  match unwindProgram.check with
  | .error _ => false
  | .ok checked =>
      let failed := runFrom Runtime.rejecting checked 64 (unwindCore 3 1)
      let succeeded := runFrom Runtime.rejecting checked 64 (unwindCore 3 0)
      let early := runFrom Runtime.rejecting checked 64 (unwindCore 0 1)
      failed.status == .halted 1 && failed.core.readReg .rdx == 0 && failed.core.readReg .rsp == 0x1008 &&
        failed.returns.isEmpty && succeeded.status == .halted 0 && succeeded.core.readReg .rdx == 42 &&
        early.status == .halted 1

#guard unwindExitAccepted

example : arithmeticProgram.InV0 := arithmeticProgram.inV0
example : callProgram.InV0 := callProgram.inV0

end IxCC.X86.Examples
