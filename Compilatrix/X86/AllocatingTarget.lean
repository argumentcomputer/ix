import Compilatrix.X86.AllocatingCall

namespace Compilatrix.X86.Allocating
open UniqueABI UniqueTarget UniqueExecution

def policyTag (foldCounters : Bool := false) : String :=
  if foldCounters then "unique-reverse-allocating-call-x86/2" else "unique-reverse-allocating-call-x86/1"
def stackBytes : Nat := 16
def checked (foldCounters : Bool := false) : Checked := RuntimeTarget.checked foldCounters true

def controlCost (length : Nat) (foldCounters : Bool := false) : Nat :=
  RuntimeTarget.controlCost length foldCounters +
    if length = 0 then 5 else if foldCounters then 16 else 4

def afterOutside (layout : Layout) (stack : Stack layout) (values : List Word) (outside : Memory) : Memory :=
  outside.write64 stack.slot (if values.isEmpty then token 26 0 else token 27 10)

theorem hasBlock (foldCounters : Bool) (block : BlockId) (bound : block.toNat < 29) :
    (checked foldCounters).program.hasBlock block = true := by
  simpa [checked, RuntimeTarget.checked, RuntimeTarget.program, Program.hasBlock] using bound

theorem calleeCode (foldCounters : Bool) :
    BlockCode (checked foldCounters) 28 (allocate nilTag 0 (.imm 0) .rsi) .ret := ⟨rfl, by decide⟩
theorem emptyCode (foldCounters : Bool) :
    BlockCode (checked foldCounters) 26 RuntimeTarget.allocatorCall (.jump 3) := ⟨rfl, by decide⟩
theorem firstCode (foldCounters : Bool) :
    BlockCode (checked foldCounters) 27 RuntimeTarget.firstCallInstructions (.jump 3) := ⟨rfl, by decide⟩
theorem dispatchCode (foldCounters : Bool) :
    BlockCode (checked foldCounters) 2 [] (.branch (RuntimeTarget.wordCompare .rsi (.imm 0)) .eq 26 27) := ⟨rfl, by decide⟩

theorem _root_.Compilatrix.X86.Straight.Segment.singleton {checked : Checked} {block : BlockId}
    {offset : Nat} {code : Block} {instruction : Instr}
    (found : checked.program.blocks[block.toNat]? = some code) (atInstruction : code.instructions[offset]? = some instruction) :
    Straight.Segment checked block offset [instruction] := by
  refine ⟨code, found, ?_⟩
  intro index bound
  have zero : index = 0 := by simpa using bound
  simpa [zero] using atInstruction

theorem _root_.Compilatrix.X86.BlockCode.segment_middle {checked : Checked} {block : BlockId}
    {leading body suffix : List Instr} {terminator : Terminator}
    (code : BlockCode checked block (leading ++ body ++ suffix) terminator) :
    Straight.Segment checked block leading.length body := by
  refine ⟨_, code.found, ?_⟩
  intro index bound
  simp only [List.getElem?_toArray, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem?_append_left bound

theorem callSite (foldCounters : Bool) (nonempty : Bool) :
    CallSite (checked foldCounters) (if nonempty then 27 else 26) (if nonempty then 10 else 0) := by
  cases nonempty <;> constructor
  all_goals first
    | exact Straight.Segment.singleton rfl rfl
    | decide

theorem reserveSegment (foldCounters : Bool) :
    Straight.Segment (checked foldCounters) 27 0 reserveCons :=
  (show BlockCode (checked foldCounters) 27
    ([] ++ reserveCons ++ (RuntimeTarget.allocatorCall ++ RuntimeTarget.finishFirstInstructions)) (.jump 3) from firstCode foldCounters).segment_middle

theorem finishSegment (foldCounters : Bool) :
    Straight.Segment (checked foldCounters) 27 13 RuntimeTarget.finishFirstInstructions :=
  (show BlockCode (checked foldCounters) 27
    ((reserveCons ++ RuntimeTarget.allocatorCall) ++ RuntimeTarget.finishFirstInstructions ++ []) (.jump 3) from
      by simpa [RuntimeTarget.firstCallInstructions, List.append_assoc] using firstCode foldCounters).segment_middle

theorem Stack.Available.of_permissions {layout : Layout} {stack : Stack layout} {before after : Memory}
    (available : stack.Available before) (readable : after.readable = before.readable)
    (writable : after.writable = before.writable) : stack.Available after := by
  simpa only [Stack.Available, readable, writable] using available

end Compilatrix.X86.Allocating
