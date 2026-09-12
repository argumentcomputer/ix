import Compilatrix.X86.HeapMacros

namespace Compilatrix.X86.HeapPrimitives
open WordRegion PhysicalHeap HeapArena HeapMacros

def save {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (destination : Nat) : State :=
  state.setWord (frame.localIndex destination) (state.registers .rax)

theorem save_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (destination : Nat) :
    Scalar.Stable state (save frame state destination) := Scalar.Stable.setWord _ _ _

def load {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (source : Scalar.Atom) : State :=
  state.setReg .rax (HeapCopies.atomValue frame state source)

theorem load_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (source : Scalar.Atom) :
    Scalar.Stable state (load frame state source) := Scalar.Stable.setReg _ _ _ (by simp)

theorem atom_larger {source : Scalar.Atom} (valid : source.valid maxValues = true) :
    source.valid Scalar.maxLocals = true := by
  cases source with
  | constant word => rfl
  | var index =>
      have small : index < maxValues := of_decide_eq_true valid
      exact decide_eq_true (by simp only [maxValues, Scalar.maxLocals] at *; omega)

theorem load_trace {layout : WordRegion.Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop : Nat} {source : Scalar.Atom}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes)
    (valid : source.valid maxValues = true) :
    SafeTrace layout returns [Scalar.load .rax source] state holes (load frame state source) holes :=
  Scalar.load_safeTrace framed (HeapCopies.slots_at frame state) safe .rax
    (HeapCopies.atom_found frame state (atom_larger valid))

theorem save_trace {layout : WordRegion.Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop destination : Nat}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes)
    (frames : Scalar.FramesAbove layout frame.top returns) (bound : destination < Scalar.maxLocals) :
    SafeTrace layout returns [.spill (Scalar.slot destination) .rax] state holes (save frame state destination) holes :=
  HeapCopies.spill_trace framed safe frames bound rfl

def allocate (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) (state : State)
    (index : Nat) (ctor : Constructor) (arguments : Array Scalar.Atom) (destination : Nat) : State :=
  let state := fields frame state arguments |>.setReg .rax (layout.pointer index)
  let state := writeCell state index ctor
  let state := counter state 0 (· + 32)
  let state := counter state 2 (· + 1)
  save frame state destination

def fetch {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (source : Scalar.Atom) (field destination : Nat) : State :=
  let state := load frame state source
  save frame (state.setReg .rax (state.words (cellSlot index (field + 1)))) destination

def sharedReset (world : Ixon.Owned) (state : State) : State :=
  if world == .shared then counter (counter state 6 (· + 1)) 7 (· + 1) else state

def sharedRelease (world : Ixon.Owned) (state : State) : State :=
  if world == .shared then counter state 5 (· + 1) else state

theorem sharedReset_stable (world : Ixon.Owned) (state : State) : Scalar.Stable state (sharedReset world state) := by
  unfold sharedReset
  split
  · exact (counter_stable _ _ _).trans (counter_stable _ _ _)
  · exact .refl _

theorem sharedRelease_stable (world : Ixon.Owned) (state : State) : Scalar.Stable state (sharedRelease world state) := by
  unfold sharedRelease
  split
  · exact counter_stable _ _ _
  · exact .refl _

@[simp] theorem sharedReset_register {world : Ixon.Owned} {state : State} {register : GPR}
    (different : register ≠ .rcx) : (sharedReset world state).registers register = state.registers register := by
  unfold sharedReset
  split <;> simp [counter_register different]

@[simp] theorem sharedRelease_register {world : Ixon.Owned} {state : State} {register : GPR}
    (different : register ≠ .rcx) : (sharedRelease world state).registers register = state.registers register := by
  unfold sharedRelease
  split <;> simp [counter_register different]

theorem sharedReset_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} (based : Based layout state) (access : Access layout holes returns) (world : Ixon.Owned) :
    SafeTrace layout.region returns
      (if world == .shared then HeapTarget.increment 6 1 ++ HeapTarget.increment 7 1 else [])
      state holes (sharedReset world state) holes := by
  unfold sharedReset
  split
  · have first := increment_trace based access (by decide : 6 < headerWords) (by decide : 1 < 2147483648)
    exact first.append (increment_trace (based.stable (counter_stable _ _ _)) access
      (by decide : 7 < headerWords) (by decide : 1 < 2147483648))
  · exact .nil _ _

theorem sharedRelease_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes}
    {returns : List ReturnFrame} (based : Based layout state) (access : Access layout holes returns) (world : Ixon.Owned) :
    SafeTrace layout.region returns (if world == .shared then HeapTarget.increment 5 1 else [])
      state holes (sharedRelease world state) holes := by
  unfold sharedRelease
  split
  · exact increment_trace based access (by decide : 5 < headerWords) (by decide : 1 < 2147483648)
  · exact .nil _ _

def reserve {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (world : Ixon.Owned) (ctor : Constructor) (source : Scalar.Atom) (destination credit : Nat) : State :=
  let state := load frame state source
  let state := captureFields frame state index ctor.schema.fields.size destination
  let state := tag state index 1
  let state := counter state 9 (· + 1)
  save frame (sharedReset world state) (creditBase + credit)

def creditState {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (credit : Nat) : State :=
  state.setReg .rax (state.words (frame.localIndex (creditBase + credit)))

theorem credit_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (credit : Nat) :
    Scalar.Stable state (creditState frame state credit) := Scalar.Stable.setReg _ _ _ (by simp)

theorem credit_trace {layout : WordRegion.Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop credit : Nat}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes) (bound : credit < maxCredits) :
    SafeTrace layout returns [.reload .rax (Scalar.slot (creditBase + credit))] state holes (creditState frame state credit) holes :=
  Scalar.load_safeTrace framed (HeapCopies.slots_at frame state) safe .rax
    (HeapCopies.atom_found frame state (source := .var (creditBase + credit))
      (decide_eq_true (by simp only [maxCredits, creditBase, Scalar.maxLocals] at *; omega)))

def reuse {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (ctor : Constructor) (credit : Nat) (arguments : Array Scalar.Atom) (destination : Nat) : State :=
  let state := fields frame state arguments
  let state := creditState frame state credit
  let state := writeCell state index ctor
  let state := counter state 4 (· + 1)
  let state := counter state 8 (· + UInt64.ofNat ctor.schema.fields.size)
  let state := counter state 9 (· - 1)
  save frame state destination

def release {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (world : Ixon.Owned) (source : Scalar.Atom) : State :=
  let state := tag (load frame state source) index 0
  sharedRelease world (counter state 3 (· + 1))

def discard {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (index credit : Nat) : State :=
  let state := tag (creditState frame state credit) index 0
  counter (counter state 3 (· + 1)) 9 (· - 1)

theorem allocate_stable (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) (state : State)
    (index : Nat) (ctor : Constructor) (arguments : Array Scalar.Atom) (destination : Nat) :
    Scalar.Stable state (allocate layout frame state index ctor arguments destination) :=
  (((((fields_stable _ _ _).trans (Scalar.Stable.setReg _ _ _ (by simp))).trans
    (writeCell_stable _ _ _)).trans (counter_stable _ _ _)).trans (counter_stable _ _ _)).trans (save_stable _ _ _)

theorem fetch_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (source : Scalar.Atom) (field destination : Nat) :
    Scalar.Stable state (fetch frame state index source field destination) :=
  ((load_stable _ _ _).trans (Scalar.Stable.setReg _ _ _ (by simp))).trans (save_stable _ _ _)

theorem reserve_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (world : Ixon.Owned) (ctor : Constructor) (source : Scalar.Atom) (destination credit : Nat) :
    Scalar.Stable state (reserve frame state index world ctor source destination credit) :=
  (((((load_stable _ _ _).trans (captureFields_stable _ _ _ _ _)).trans (tag_stable _ _ _)).trans
    (counter_stable _ _ _)).trans (sharedReset_stable _ _)).trans (save_stable _ _ _)

theorem reuse_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (ctor : Constructor) (credit : Nat) (arguments : Array Scalar.Atom) (destination : Nat) :
    Scalar.Stable state (reuse frame state index ctor credit arguments destination) :=
  ((((((fields_stable _ _ _).trans (credit_stable _ _ _)).trans (writeCell_stable _ _ _)).trans
    (counter_stable _ _ _)).trans (counter_stable _ _ _)).trans (counter_stable _ _ _)).trans (save_stable _ _ _)

theorem release_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (world : Ixon.Owned) (source : Scalar.Atom) :
    Scalar.Stable state (release frame state index world source) :=
  (((load_stable _ _ _).trans (tag_stable _ _ _)).trans (counter_stable _ _ _)).trans (sharedRelease_stable _ _)

theorem discard_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (index credit : Nat) :
    Scalar.Stable state (discard frame state index credit) := by
  unfold discard
  exact (((credit_stable frame state credit).trans (tag_stable _ index 0)).trans
    (counter_stable _ 3 (· + 1))).trans (counter_stable _ 9 (· - 1))

end Compilatrix.X86.HeapPrimitives
