import Compilatrix.X86.HeapTarget
import Compilatrix.X86.ScalarInstructions

namespace Compilatrix.X86.HeapCopies
open WordRegion PhysicalHeap

def atomValue {layout : Layout} (frame : Scalar.Frame layout) (state : State) : Scalar.Atom → Word
  | .var index => state.words (frame.localIndex index)
  | .constant value => value

def value {layout : Layout} (frame : Scalar.Frame layout) (state : State) : CopySource → Word
  | .atom source => atomValue frame state source
  | .predecessor source => atomValue frame state source - 1

@[simp] theorem atomValue_setReg {layout : Layout} (frame : Scalar.Frame layout) (state : State)
    (register : GPR) (word : Word) (source : Scalar.Atom) :
    atomValue frame (state.setReg register word) source = atomValue frame state source := by
  cases source <;> rfl

def slots {layout : Layout} (frame : Scalar.Frame layout) (state : State) : Array Word :=
  Array.ofFn (fun index : Fin Scalar.maxLocals => state.words (frame.localIndex index.val))

theorem slots_at {layout : Layout} (frame : Scalar.Frame layout) (state : State) :
    Scalar.ValuesAt frame (slots frame state) state := by
  constructor
  · simp [slots]
  · intro index bound
    simp [slots]

theorem atom_found {layout : Layout} (frame : Scalar.Frame layout) (state : State) {source : Scalar.Atom}
    (valid : source.valid Scalar.maxLocals = true) :
    source.eval (slots frame state) = some (atomValue frame state source) := by
  cases source with
  | constant word => rfl
  | var index =>
      simp only [Scalar.Atom.valid, decide_eq_true_eq] at valid
      simp [Scalar.Atom.eval, slots, valid, atomValue]

theorem load_trace {layout : Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop : Nat} {source : CopySource}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes)
    (valid : HeapTarget.copySourceValid source = true) :
    SafeTrace layout returns (HeapTarget.copySourceInstructions source) state holes
      (state.setReg .rax (value frame state source)) holes := by
  have atomTrace (source : Scalar.Atom) (valid : source.valid scratchBase = true) :
      SafeTrace layout returns [Scalar.load .rax source] state holes
        (state.setReg .rax (atomValue frame state source)) holes := by
    have larger : source.valid Scalar.maxLocals = true := by
      cases source with
      | constant word => rfl
      | var index =>
          have small : index < 20 := of_decide_eq_true valid
          exact decide_eq_true (show index < 32 by omega)
    exact Scalar.load_safeTrace framed (slots_at frame state) safe .rax (atom_found frame state larger)
  cases source with
  | atom source => exact atomTrace source valid
  | predecessor source =>
      have sub := SafeTrace.alu layout returns (state.setReg .rax (atomValue frame state source)) holes .sub .rax (.imm 1)
      simpa only [HeapTarget.copySourceInstructions, value, List.singleton_append,
        State.setReg_registers, beq_self_eq_true, if_true, State.alu, AluSource.eval,
        show signExtend32 1 = 1 from by decide,
        AluOp.eval, State.setReg_setReg] using (atomTrace source valid).append sub

def put {layout : Layout} (frame : Scalar.Frame layout) (state : State) (slot : Nat) (word : Word) : State :=
  (state.setReg .rax word).setWord (frame.localIndex slot) word

theorem put_stable {layout : Layout} (frame : Scalar.Frame layout) (state : State) (slot : Nat) (word : Word) :
    Scalar.Stable state (put frame state slot word) :=
  (Scalar.Stable.setReg _ _ _ (by simp)).trans (Scalar.Stable.setWord _ _ _)

theorem put_word {layout : Layout} (frame : Scalar.Frame layout) (state : State) (slot : Nat) (word : Word) :
    (put frame state slot word).words (frame.localIndex slot) = word := by simp [put]

theorem put_other {layout : Layout} (frame : Scalar.Frame layout) (state : State) {slot other : Nat} (word : Word)
    (slotBound : slot < Scalar.maxLocals) (otherBound : other < Scalar.maxLocals) (different : other ≠ slot) :
    (put frame state slot word).words (frame.localIndex other) = state.words (frame.localIndex other) := by
  apply Words.set_other
  exact fun same => different (frame.local_injective otherBound slotBound same)

theorem spill_trace {layout : Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop slot : Nat} {word : Word}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes)
    (frames : Scalar.FramesAbove layout frame.top returns) (bound : slot < Scalar.maxLocals)
    (result : state.registers .rax = word) :
    SafeTrace layout returns [.spill (Scalar.slot slot) .rax] state holes
      (state.setWord (frame.localIndex slot) word) holes := by
  have readable := safe.readable (frame.local_bound slot) (.inl (frame.local_ordinary bound))
  simpa only [result, HeapArena.clear_readable readable] using
    SafeTrace.spill layout returns state holes (Scalar.slot slot) .rax (frame.localIndex slot)
      (frame.local_bound slot) (by rw [framed.1]; exact frame.local_address bound) (frame.local_disjoint frames slot)

def stage {layout : Layout} (frame : Scalar.Frame layout) (original : State) : Nat → List Copy → State → State
  | _, [], state => state
  | start, copy :: rest, state =>
      stage frame original (start + 1) rest (put frame state (scratchBase + start) (value frame original copy.source))

def commit {layout : Layout} (frame : Scalar.Frame layout) (staged : State) : Nat → List Copy → State → State
  | _, [], state => state
  | start, copy :: rest, state =>
      commit frame staged (start + 1) rest (put frame state copy.destination (staged.words (frame.localIndex (scratchBase + start))))

def execute {layout : Layout} (frame : Scalar.Frame layout) (state : State) (transfer : Transfer) : State :=
  let staged := stage frame state 0 transfer.copies.toList state
  commit frame staged 0 transfer.copies.toList staged

def SourcesEqual {layout : Layout} (frame : Scalar.Frame layout) (original state : State) : Prop :=
  ∀ slot < scratchBase, state.words (frame.localIndex slot) = original.words (frame.localIndex slot)

theorem SourcesEqual.value {layout : Layout} {frame : Scalar.Frame layout} {original state : State}
    (same : SourcesEqual frame original state) {source : CopySource} (valid : HeapTarget.copySourceValid source = true) :
    value frame state source = value frame original source := by
  have atoms (source : Scalar.Atom) (valid : source.valid scratchBase = true) :
      atomValue frame state source = atomValue frame original source := by
    cases source with
    | constant word => rfl
    | var index => exact same index (by simpa only [Scalar.Atom.valid, decide_eq_true_eq] using valid)
  cases source with
  | atom source => exact atoms source valid
  | predecessor source => exact congrArg (· - 1) (atoms source valid)

theorem SourcesEqual.put {layout : Layout} {frame : Scalar.Frame layout} {original state : State}
    (same : SourcesEqual frame original state) {start : Nat} (bound : scratchBase + start < Scalar.maxLocals) (word : Word) :
    SourcesEqual frame original (put frame state (scratchBase + start) word) := by
  intro slot small
  rw [put_other frame state word bound (by simp only [scratchBase, Scalar.maxLocals] at *; omega) (by omega)]
  exact same slot small

theorem stage_trace {layout : Layout} {frame : Scalar.Frame layout} (original : State)
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop : Nat}
    (safe : Scalar.HolesIn layout rootTop holes) (frames : Scalar.FramesAbove layout frame.top returns)
    (copies : List Copy) : ∀ (start : Nat) (state : State),
      start + copies.length ≤ maxEdge → (∀ copy ∈ copies, HeapTarget.copySourceValid copy.source = true) →
      Scalar.Framed frame state → SourcesEqual frame original state →
      SafeTrace layout returns (HeapTarget.stageCopies start copies) state holes (stage frame original start copies state) holes := by
  induction copies with
  | nil => intro start state _ _ _ _; exact .nil _ _
  | cons copy copies ih =>
      intro start state bound valid framed same
      have slotBound : scratchBase + start < Scalar.maxLocals := by
        simp only [List.length_cons, maxEdge, scratchBase, Scalar.maxLocals] at *
        omega
      have read := load_trace (returns := returns) framed safe (valid copy (by simp))
      rw [same.value (valid copy (by simp))] at read
      have stored := spill_trace ((Scalar.Stable.setReg _ _ _ (by simp)).framed framed) safe frames slotBound
        (by simp : (state.setReg .rax (value frame original copy.source)).registers .rax = value frame original copy.source)
      have rest := ih (start + 1) (put frame state (scratchBase + start) (value frame original copy.source))
        (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound)
        (fun item member => valid item (by simp [member])) ((put_stable _ _ _ _).framed framed) (same.put slotBound _)
      exact (read.append stored).append rest

theorem stage_stable {layout : Layout} (frame : Scalar.Frame layout) (original state : State) (start : Nat) (copies : List Copy) :
    Scalar.Stable state (stage frame original start copies state) := by
  induction copies generalizing start state with
  | nil => exact .refl _
  | cons copy copies ih => exact (put_stable _ _ _ _).trans (ih _ _)

theorem commit_stable {layout : Layout} (frame : Scalar.Frame layout) (staged state : State) (start : Nat) (copies : List Copy) :
    Scalar.Stable state (commit frame staged start copies state) := by
  induction copies generalizing start state with
  | nil => exact .refl _
  | cons copy copies ih => exact (put_stable _ _ _ _).trans (ih _ _)

def ScratchEqual {layout : Layout} (frame : Scalar.Frame layout) (staged state : State) : Prop :=
  ∀ slot, scratchBase ≤ slot → slot < Scalar.maxLocals → state.words (frame.localIndex slot) = staged.words (frame.localIndex slot)

theorem ScratchEqual.put {layout : Layout} {frame : Scalar.Frame layout} {staged state : State}
    (same : ScratchEqual frame staged state) {destination : Nat} (bound : destination < scratchBase) (word : Word) :
    ScratchEqual frame staged (put frame state destination word) := by
  intro slot low high
  rw [put_other frame state word (by simp only [scratchBase, Scalar.maxLocals] at *; omega) high (by omega)]
  exact same slot low high

theorem commit_trace {layout : Layout} {frame : Scalar.Frame layout} (staged : State)
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop : Nat}
    (safe : Scalar.HolesIn layout rootTop holes) (frames : Scalar.FramesAbove layout frame.top returns)
    (copies : List Copy) : ∀ (start : Nat) (state : State),
      start + copies.length ≤ maxEdge → (∀ copy ∈ copies, copy.destination < scratchBase) →
      Scalar.Framed frame state → ScratchEqual frame staged state →
      SafeTrace layout returns (HeapTarget.commitCopies start copies) state holes (commit frame staged start copies state) holes := by
  induction copies with
  | nil => intro start state _ _ _ _; exact .nil _ _
  | cons copy copies ih =>
      intro start state bound valid framed same
      have sourceBound : scratchBase + start < Scalar.maxLocals := by
        simp only [List.length_cons, maxEdge, scratchBase, Scalar.maxLocals] at *
        omega
      have destBound := valid copy (by simp)
      have loaded := Scalar.load_safeTrace (returns := returns) framed (slots_at frame state) safe .rax
        (atom_found frame state (source := .var (scratchBase + start)) (by simpa only [Scalar.Atom.valid, decide_eq_true_eq] using sourceBound))
      change SafeTrace layout returns [.reload .rax (Scalar.slot (scratchBase + start))] state holes
        (state.setReg .rax (state.words (frame.localIndex (scratchBase + start)))) holes at loaded
      rw [same _ (by omega) sourceBound] at loaded
      have stored := spill_trace ((Scalar.Stable.setReg _ _ _ (by simp)).framed framed) safe frames
        (by simp only [scratchBase, Scalar.maxLocals] at *; omega : copy.destination < Scalar.maxLocals)
        (by simp : (state.setReg .rax (staged.words (frame.localIndex (scratchBase + start)))).registers .rax =
          staged.words (frame.localIndex (scratchBase + start)))
      have rest := ih (start + 1) (put frame state copy.destination (staged.words (frame.localIndex (scratchBase + start))))
        (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound)
        (fun item member => valid item (by simp [member])) ((put_stable _ _ _ _).framed framed) (same.put destBound _)
      exact (loaded.append stored).append rest

theorem execute_trace {layout : Layout} {frame : Scalar.Frame layout} {state : State}
    {holes : Stream.Holes} {returns : List ReturnFrame} {rootTop : Nat} {copies : Transfer}
    (framed : Scalar.Framed frame state) (safe : Scalar.HolesIn layout rootTop holes)
    (frames : Scalar.FramesAbove layout frame.top returns) (valid : HeapTarget.transferValid copies = true) :
    SafeTrace layout returns (HeapTarget.transfer copies) state holes (execute frame state copies) holes := by
  simp only [HeapTarget.transferValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  have members : ∀ copy ∈ copies.copies.toList,
      HeapTarget.copySourceValid copy.source = true ∧ copy.destination < scratchBase := by
    intro copy member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have accepted := Array.all_eq_true.mp valid.1.2 index (by simpa using bound)
    have same : copies.copies[index] = copy := by simpa only [Array.getElem_toList] using equal
    simpa only [same, Bool.and_eq_true, decide_eq_true_eq] using accepted
  have staged := stage_trace state safe frames copies.copies.toList 0 state (by simpa using valid.1.1)
    (fun copy member => (members copy member).1) framed (fun _ _ => rfl)
  have committed := commit_trace (stage frame state 0 copies.copies.toList state) safe frames copies.copies.toList 0 _
    (by simpa using valid.1.1) (fun copy member => (members copy member).2)
    ((stage_stable frame state state 0 copies.copies.toList).framed framed) (fun _ _ _ => rfl)
  exact staged.append committed

theorem stage_other {layout : Layout} (frame : Scalar.Frame layout) (original : State)
    (copies : List Copy) : ∀ (start : Nat) (state : State) (slot : Nat),
      start + copies.length ≤ maxEdge → slot < Scalar.maxLocals →
      (slot < scratchBase + start ∨ scratchBase + start + copies.length ≤ slot) →
      (stage frame original start copies state).words (frame.localIndex slot) = state.words (frame.localIndex slot) := by
  induction copies with
  | nil => intros; rfl
  | cons copy copies ih =>
      intro start state slot bound small outside
      rw [stage, ih (start + 1) _ slot (by simp only [List.length_cons] at bound; omega) small
        (by simp only [List.length_cons] at bound outside; omega)]
      exact put_other frame state (value frame original copy.source)
        (by simp only [List.length_cons, maxEdge, scratchBase, Scalar.maxLocals] at *; omega) small
        (by simp only [List.length_cons] at bound outside; omega)

theorem stage_at {layout : Layout} (frame : Scalar.Frame layout) (original : State)
    (copies : List Copy) : ∀ (start : Nat) (state : State) (index : Nat) (found : index < copies.length),
      start + copies.length ≤ maxEdge →
      (stage frame original start copies state).words (frame.localIndex (scratchBase + start + index)) =
        value frame original copies[index].source := by
  induction copies with
  | nil => intro start state index found; simp at found
  | cons copy copies ih =>
      intro start state index found bound
      cases index with
      | zero =>
          simp only [stage, Nat.add_zero, List.getElem_cons_zero]
          rw [stage_other frame original copies (start + 1) _ (scratchBase + start)
            (by simp only [List.length_cons] at bound; omega)
            (by simp only [List.length_cons, maxEdge, scratchBase, Scalar.maxLocals] at *; omega)
            (Or.inl (by omega))]
          exact put_word _ _ _ _
      | succ index =>
          simpa only [stage, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) (put frame state (scratchBase + start) (value frame original copy.source)) index
              (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using found)
              (by simp only [List.length_cons] at bound; omega)

theorem commit_other {layout : Layout} (frame : Scalar.Frame layout) (staged : State)
    (copies : List Copy) : ∀ (start : Nat) (state : State) (slot : Nat),
      slot < Scalar.maxLocals → (∀ copy ∈ copies, copy.destination < scratchBase) →
      (∀ copy ∈ copies, slot ≠ copy.destination) →
      (commit frame staged start copies state).words (frame.localIndex slot) = state.words (frame.localIndex slot) := by
  induction copies with
  | nil => intros; rfl
  | cons copy copies ih =>
      intro start state slot small valid different
      rw [commit, ih (start + 1) _ slot small (fun copy member => valid copy (by simp [member]))
        (fun copy member => different copy (by simp [member]))]
      exact put_other frame state _
        (by have := valid copy (by simp); simp only [scratchBase, Scalar.maxLocals] at *; omega)
        small (different copy (by simp))

theorem commit_at {layout : Layout} (frame : Scalar.Frame layout) (staged : State)
    (copies : List Copy) : ∀ (start : Nat) (state : State) (index : Nat) (found : index < copies.length),
      (∀ copy ∈ copies, copy.destination < scratchBase) → (copies.map (·.destination)).Nodup →
      (commit frame staged start copies state).words (frame.localIndex copies[index].destination) =
        staged.words (frame.localIndex (scratchBase + start + index)) := by
  induction copies with
  | nil => intro start state index found; simp at found
  | cons copy copies ih =>
      intro start state index found valid distinct
      have distinct := List.nodup_cons.mp distinct
      cases index with
      | zero =>
          simp only [commit, Nat.add_zero, List.getElem_cons_zero]
          rw [commit_other frame staged copies (start + 1) _ copy.destination
            (by have := valid copy (by simp); simp only [scratchBase, Scalar.maxLocals] at *; omega)
            (fun item member => valid item (by simp [member]))
            (fun item member equal => distinct.1 (List.mem_map.mpr ⟨item, member, equal.symm⟩))]
          exact put_word _ _ _ _
      | succ index =>
          simpa only [commit, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) (put frame state copy.destination (staged.words (frame.localIndex (scratchBase + start)))) index
              (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using found)
              (fun item member => valid item (by simp [member])) distinct.2

/-- Every edge operand is read before any destination is overwritten.
This includes permutations of value slots and live reservation slots. -/
theorem execute_at {layout : Layout} (frame : Scalar.Frame layout) (state : State) {copies : Transfer}
    (valid : HeapTarget.transferValid copies = true) (index : Nat) (found : index < copies.copies.size) :
    (execute frame state copies).words (frame.localIndex copies.copies[index].destination) =
      value frame state copies.copies[index].source := by
  simp only [HeapTarget.transferValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  have destinations : ∀ copy ∈ copies.copies.toList, copy.destination < scratchBase := by
    intro copy member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have accepted := Array.all_eq_true.mp valid.1.2 index (by simpa using bound)
    have same : copies.copies[index] = copy := by simpa only [Array.getElem_toList] using equal
    have accepted : HeapTarget.copySourceValid copy.source = true ∧ copy.destination < scratchBase := by
      simpa only [same, Bool.and_eq_true, decide_eq_true_eq] using accepted
    exact accepted.2
  change (commit frame (stage frame state 0 copies.copies.toList state) 0 copies.copies.toList _).words _ = _
  have committed := commit_at frame (stage frame state 0 copies.copies.toList state) copies.copies.toList 0
    (stage frame state 0 copies.copies.toList state) index (by simpa using found) destinations valid.2
  have staged := stage_at frame state copies.copies.toList 0 state index (by simpa using found) (by simpa using valid.1.1)
  simp only [Array.getElem_toList] at committed staged
  exact committed.trans staged

theorem put_preserves {layout : Layout} (frame : Scalar.Frame layout) (state : State)
    (slot : Nat) (word : Word) : Scalar.Preserves frame 0 state (put frame state slot word) := by
  refine ⟨put_stable _ _ _ _, fun index above => ?_⟩
  apply Words.set_other
  have enough := frame.enough
  simp only [Scalar.Frame.localIndex] at *
  omega

theorem stage_preserves {layout : Layout} (frame : Scalar.Frame layout) (original state : State)
    (start : Nat) (copies : List Copy) : Scalar.Preserves frame 0 state (stage frame original start copies state) := by
  induction copies generalizing start state with
  | nil => exact .refl _ _ _
  | cons copy copies ih => exact (put_preserves _ _ _ _).trans (ih _ _)

theorem commit_preserves {layout : Layout} (frame : Scalar.Frame layout) (staged state : State)
    (start : Nat) (copies : List Copy) : Scalar.Preserves frame 0 state (commit frame staged start copies state) := by
  induction copies generalizing start state with
  | nil => exact .refl _ _ _
  | cons copy copies ih => exact (put_preserves _ _ _ _).trans (ih _ _)

theorem execute_preserves {layout : Layout} (frame : Scalar.Frame layout) (state : State) (copies : Transfer) :
    Scalar.Preserves frame 0 state (execute frame state copies) :=
  (stage_preserves _ _ _ _ _).trans (commit_preserves _ _ _ _ _)

end Compilatrix.X86.HeapCopies
