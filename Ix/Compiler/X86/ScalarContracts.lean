import Ix.Compiler.X86.ScalarInstructions

namespace Ix.Compiler.X86.Scalar
open WordRegion

def destination (success failure : BlockId) : Option Word → BlockId
  | some _ => success
  | none => failure

def ResultAt (result : Option Word) (state : State) : Prop :=
  ∀ value, result = some value → state.registers .rax = value

/-- The expression contract preserves existing locals and reaches its exact
success or overflow continuation. All accesses carry E2 safety evidence. -/
structure ExprRun (checked : X86.Checked) (plan : Plan) (success failure : BlockId)
    (layout : Layout) (frame : Frame layout) (values : Array Word)
    (outside initialMemory : Memory) (before : State) (initialHoles : Stream.Holes)
    (rootTop : Nat) (returns : List ReturnFrame) (result : Option Word) where
  count : Nat
  after : State
  memory : Memory
  holes : Stream.Holes
  represented : Realizes layout outside after.words memory
  preserved : Preserves frame values.size before after
  safeHoles : HolesIn layout rootTop holes
  resultAt : ResultAt result after
  steps : Stream.SafeSteps Runtime.rejecting checked count initialHoles
    (inFrame (before.core initialMemory) plan.entry 0 returns)
    holes (inFrame (after.core memory) (destination success failure result) 0 returns)

def returnBlock (plan : FunctionPlan) : Option Word → BlockId
  | some _ => plan.success
  | none => plan.failure

def returnOffset : Option Word → Nat
  | some _ => successInstructions.length
  | none => failureInstructions.length

def returnTag : Option Word → Word
  | some _ => 0
  | none => 1

/-- A complete activation up to its final RET. The caller then composes the
stored-continuation contract; the exported entry composes the external RET. -/
structure FunctionRun (checked : X86.Checked) (plan : FunctionPlan)
    (layout : Layout) (frame : Frame layout) (outside initialMemory : Memory)
    (before : State) (initialHoles : Stream.Holes) (rootTop : Nat)
    (returns : List ReturnFrame) (result : Option Word) where
  count : Nat
  after : State
  memory : Memory
  holes : Stream.Holes
  represented : Realizes layout outside after.words memory
  stable : Stable before after
  preserved : ∀ index, frame.top ≤ index → after.words index = before.words index
  safeHoles : HolesIn layout rootTop holes
  resultValue : after.registers .rax = result.getD 0
  resultTag : after.registers .rdx = returnTag result
  steps : Stream.SafeSteps Runtime.rejecting checked count initialHoles
    (inFrame (before.core initialMemory) plan.entry 0 returns)
    holes (inFrame (after.core memory) (returnBlock plan result) (returnOffset result) returns)

/-- The quantifiers include arbitrary runtime registers, scratch contents,
mapped stack memory, and active callers. -/
def ExprContract (checked : X86.Checked) (plan : Plan) (success failure : BlockId)
    (layout : Layout) (frame : Frame layout) (values : Array Word)
    (rootTop : Nat) (returns : List ReturnFrame) (result : Option Word) : Prop :=
  ∀ outside memory state holes,
    Framed frame state → ValuesAt frame values state → HolesIn layout rootTop holes →
    FramesAbove layout frame.top returns → Realizes layout outside state.words memory →
    Nonempty (ExprRun checked plan success failure layout frame values outside memory state holes rootTop returns result)

def FunctionContract (checked : X86.Checked) (plan : FunctionPlan)
    (layout : Layout) (frame : Frame layout) (values : Array Word)
    (rootTop : Nat) (returns : List ReturnFrame) (result : Option Word) : Prop :=
  ∀ outside memory state holes,
    ArgumentsAt values state → state.registers .rsp = layout.address frame.top →
    HolesIn layout rootTop holes → FramesAbove layout frame.top returns →
    Realizes layout outside state.words memory →
    Nonempty (FunctionRun checked plan layout frame outside memory state holes rootTop returns result)

end Ix.Compiler.X86.Scalar
