import Ix.Compiler.X86.ScalarTarget
import Ix.Compiler.X86.WordRegionExecution
import Ix.Compiler.X86.FrameCalls

namespace Ix.Compiler.X86.Scalar

open WordRegion

@[simp] theorem callerSaved (register : GPR) : SysV.isCallerSaved register =
    (match register with
      | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11 => true
      | _ => false) := by
  cases register <;> simp [SysV.isCallerSaved, SysV.callerSaved]

/-- One activation has a return slot, saved `rbp`, and 32 local words. The
return slot belongs to its caller; the other 264 bytes are this frame. -/
structure Frame (layout : Layout) where
  top : Nat
  enough : 33 ≤ top
  bound : top < layout.slots
  aligned : SysV.functionEntryAligned (layout.address top) = true
  partition : top % frameStride = 33

def Frame.baseIndex {layout : Layout} (frame : Frame layout) : Nat := frame.top - 1
def Frame.stackIndex {layout : Layout} (frame : Frame layout) : Nat := frame.top - 33
def Frame.localIndex {layout : Layout} (frame : Frame layout) (index : Nat) : Nat := frame.top - 2 - index

theorem Frame.base_bound {layout : Layout} (frame : Frame layout) : frame.baseIndex < layout.slots := by
  have := frame.bound
  simp only [Frame.baseIndex]
  omega

theorem Frame.stack_bound {layout : Layout} (frame : Frame layout) : frame.stackIndex < layout.slots := by
  have := frame.bound
  simp only [Frame.stackIndex]
  omega

theorem Frame.local_bound {layout : Layout} (frame : Frame layout) (index : Nat) :
    frame.localIndex index < layout.slots := by
  have := frame.bound
  simp only [Frame.localIndex]
  omega

theorem Frame.local_injective {layout : Layout} (frame : Frame layout) {left right : Nat}
    (leftBound : left < maxLocals) (rightBound : right < maxLocals)
    (equal : frame.localIndex left = frame.localIndex right) : left = right := by
  have := frame.enough
  simp only [Frame.localIndex, maxLocals] at *
  omega

theorem slot_displacement {index : Nat} (bound : index < maxLocals) :
    (slot index).displacement = UInt64.ofNat (8 * (index + 1)) := by
  have small : index < UInt16.size := by simp only [maxLocals, UInt16.size] at *; omega
  have convert : (UInt16.ofNat index).toUInt64 = UInt64.ofNat index := by
    apply UInt64.toNat_inj.mp
    rw [UInt16.toNat_toUInt64, UInt16.toNat_ofNat_of_lt' small,
      UInt64.toNat_ofNat_of_lt' (by simp only [maxLocals, UInt64.size] at *; omega)]
  simp [slot, StackSlot.displacement, convert, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.mul_comm]

theorem Frame.local_address {layout : Layout} (frame : Frame layout) {index : Nat}
    (bound : index < maxLocals) :
    layout.address frame.baseIndex - (slot index).displacement = layout.address (frame.localIndex index) := by
  have enough := frame.enough
  rw [slot_displacement bound, layout.subtract (by
    simp only [Frame.baseIndex, maxLocals] at *
    omega)]
  congr 1
  simp only [Frame.baseIndex, Frame.localIndex]
  omega

theorem Frame.call_aligned {layout : Layout} (frame : Frame layout) :
    SysV.callSiteAligned (layout.address frame.stackIndex) = true := by
  have aligned := frame.aligned
  simp only [SysV.functionEntryAligned, beq_iff_eq] at aligned
  have aligned := congrArg UInt64.toNat aligned
  simp only [UInt64.toNat_mod] at aligned
  change (layout.address frame.top).toNat % 16 = 8 at aligned
  rw [layout.address_toNat frame.bound] at aligned
  simp only [SysV.callSiteAligned, beq_iff_eq]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mod]
  change (layout.address frame.stackIndex).toNat % 16 = 0
  rw [layout.address_toNat frame.stack_bound]
  have enough := frame.enough
  simp only [Frame.stackIndex]
  omega

def Frame.child {layout : Layout} (frame : Frame layout) (enough : 67 ≤ frame.top) : Frame layout where
  top := frame.top - frameStride
  enough := by simp only [frameStride]; omega
  bound := by have := frame.bound; simp only [frameStride]; omega
  aligned := by
    have aligned := frame.aligned
    simp only [SysV.functionEntryAligned, beq_iff_eq] at aligned ⊢
    have aligned := congrArg UInt64.toNat aligned
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod] at aligned ⊢
    change (layout.address (frame.top - frameStride)).toNat % 16 = 8
    change (layout.address frame.top).toNat % 16 = 8 at aligned
    rw [layout.address_toNat frame.bound] at aligned
    rw [layout.address_toNat (by have := frame.bound; simp only [frameStride]; omega)]
    simp only [frameStride]
    omega
  partition := by
    have partition := frame.partition
    simp only [frameStride] at *
    omega

def Framed {layout : Layout} (frame : Frame layout) (state : State) : Prop :=
  state.registers .rbp = layout.address frame.baseIndex ∧
  state.registers .rsp = layout.address frame.stackIndex

def ValuesAt {layout : Layout} (frame : Frame layout) (values : Array Word) (state : State) : Prop :=
  values.size ≤ maxLocals ∧ ∀ index (bound : index < values.size), state.words (frame.localIndex index) = values[index]

/-- The expression compiler may change caller-saved registers. It preserves
`rsp`, `rbp`, and every other System V callee-saved register. -/
def Stable (before after : State) : Prop :=
  ∀ register, SysV.isCallerSaved register = false → after.registers register = before.registers register

theorem Stable.refl (state : State) : Stable state state := fun _ _ => rfl

theorem Stable.trans {before middle after : State} (left : Stable before middle) (right : Stable middle after) :
    Stable before after := fun register safe => (right register safe).trans (left register safe)

theorem Stable.setReg (state : State) (register : GPR) (value : Word)
    (scratch : SysV.isCallerSaved register = true) : Stable state (state.setReg register value) := by
  intro other saved
  have different : other ≠ register := by
    intro equal
    subst other
    exact Bool.noConfusion (saved.symm.trans scratch)
  simp [State.setReg_registers, different]

theorem Stable.setWord (state : State) (slot : Nat) (value : Word) :
    Stable state (state.setWord slot value) := fun _ _ => rfl

theorem Stable.framed {layout : Layout} {frame : Frame layout} {before after : State}
    (stable : Stable before after) (framed : Framed frame before) : Framed frame after :=
  ⟨(stable .rbp (by simp)).trans framed.1, (stable .rsp (by simp)).trans framed.2⟩

theorem Stable.snapshot {before after : State} (stable : Stable before after) (memory nextMemory : Memory) :
    (after.core nextMemory).calleeSavedSnapshot = (before.core memory).calleeSavedSnapshot := by
  simp [Core.calleeSavedSnapshot, SysV.calleeSaved, State.core, Core.readReg,
    stable .rbx (by simp), stable .rbp (by simp), stable .r12 (by simp),
    stable .r13 (by simp), stable .r14 (by simp), stable .r15 (by simp)]

def Preserves {layout : Layout} (frame : Frame layout) (locals : Nat) (before after : State) : Prop :=
  Stable before after ∧
    ∀ index, frame.top - 1 - locals ≤ index → after.words index = before.words index

theorem Preserves.refl {layout : Layout} (frame : Frame layout) (locals : Nat) (state : State) :
    Preserves frame locals state state := ⟨Stable.refl _, fun _ _ => rfl⟩

theorem Preserves.trans {layout : Layout} {frame : Frame layout} {locals : Nat} {before middle after : State}
    (left : Preserves frame locals before middle) (right : Preserves frame locals middle after) :
    Preserves frame locals before after :=
  ⟨left.1.trans right.1, fun index bound => (right.2 index bound).trans (left.2 index bound)⟩

theorem Preserves.values {layout : Layout} {frame : Frame layout} {values : Array Word} {before after : State}
    (preserved : Preserves frame values.size before after) (valuesAt : ValuesAt frame values before) :
    ValuesAt frame values after := by
  refine ⟨valuesAt.1, fun index bound => ?_⟩
  rw [preserved.2]
  · exact valuesAt.2 index bound
  · simp only [Frame.localIndex]
    omega

theorem load_trace {layout : Layout} {frame : Frame layout} {values : Array Word} {state : State}
    (framed : Framed frame state) (valuesAt : ValuesAt frame values state)
    (destination : GPR) {source : Atom} {value : Word} (found : source.eval values = some value) :
    Trace layout [load destination source] state (state.setReg destination value) := by
  cases source with
  | constant number =>
      simp only [Atom.eval, Option.some.injEq] at found
      subst value
      exact .cons (.mov _ _ _) (.nil _)
  | var index =>
      simp only [Atom.eval] at found
      obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
      have loaded : state.words (frame.localIndex index) = value := (valuesAt.2 index bound).trans equal
      have address : state.registers .rbp - (slot index).displacement = layout.address (frame.localIndex index) := by
        rw [framed.1]
        exact frame.local_address (by have := valuesAt.1; omega)
      simpa only [load, loaded] using
        Trace.cons (Effect.reload state destination (slot index) (frame.localIndex index)
          (frame.local_bound index) address) (Trace.nil _)

end Ix.Compiler.X86.Scalar
