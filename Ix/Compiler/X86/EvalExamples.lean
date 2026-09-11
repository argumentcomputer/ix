import Ix.Compiler.X86.Eval

/-! Executable checks for the local x86-64 v0 target semantics. -/

namespace Ix.Compiler.X86.Examples

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
          .branch
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

example : arithmeticProgram.InV0 := arithmeticProgram.inV0
example : callProgram.InV0 := callProgram.inV0

end Ix.Compiler.X86.Examples
