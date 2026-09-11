import Ix.Compiler.IxIR2.Validate

/-!
# Checked block-local liveness for IxIR₂

This is the first liveness artifact consumed by reuse insertion.  A proposal
stores one conservative last-use bound per value register.  Bounds use the
encoding `0 = unused` and `position + 1 = live through position`; therefore a
proposal may safely keep a value live longer than necessary.  The checker
replays every value operand in instructions, terminators, and CFG edges and
rejects any uncovered use under explicit resource limits.

The artifact is deliberately block-local at this stage.  Interprocedural
parameter/result liveness and dead-parameter rewriting remain separate
roadmap work, while reset placement only needs the checked local fact that the
consumed scrutinee has no later use in its block.
-/

namespace Ix.Compiler.IxIR2.Liveness

open Ix.Compiler.IxIR2

/-- One syntactic value-register use at an instruction position.  The block
terminator occupies position `block.instructions.size`. -/
structure Use where
  value : ValueId
  position : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

private def recordAtom (position : Nat) (uses : Array Use) : Atom → Array Use
  | .reg value => uses.push { value, position }
  | .lit _ | .erased => uses

private def recordAtoms (position : Nat) (uses : Array Use)
    (atoms : Array Atom) : Array Use :=
  atoms.foldl (recordAtom position) uses

private def recordEdge (position : Nat) (uses : Array Use)
    (edge : Edge) : Array Use :=
  recordAtoms position uses edge.values

private def recordInstruction (position : Nat) (uses : Array Use) :
    Instr → Array Use
  | .move value => recordAtom position uses value
  | .alloc _ _ arguments | .allocWith _ _ _ arguments =>
      recordAtoms position uses arguments
  | .discardCredit _ => uses
  | .takeUnique target _ | .resetShared target _ |
      .retainShared target | .releaseShared target | .dropUnique target |
      .freeUnique target _ | .fetch target _ _ =>
      recordAtom position uses target
  | .call _ arguments | .callSelf arguments | .papp _ arguments |
      .extern _ arguments =>
      recordAtoms position uses arguments
  | .apply function arguments =>
      recordAtoms position (recordAtom position uses function) arguments

private def recordTerminator (position : Nat) (uses : Array Use) :
    Terminator → Array Use
  | .jump edge => recordEdge position uses edge
  | .switchValue scrutinee constructors natPeel =>
      let uses := recordAtom position uses scrutinee
      let uses := constructors.foldl (fun current alternative =>
        recordEdge position current alternative.edge) uses
      match natPeel with
      | none => uses
      | some peel =>
          recordEdge position (recordEdge position uses peel.zero) peel.succ
  | .branchCredit _ someEdge noneEdge =>
      recordEdge position (recordEdge position uses someEdge) noneEdge
  | .ret value => recordAtom position uses value
  | .tailCall _ arguments | .tailCallSelf arguments =>
      recordAtoms position uses arguments

private def scanInstruction (state : Nat × Array Use)
    (instruction : Instr) : Nat × Array Use :=
  (state.1 + 1, recordInstruction state.1 state.2 instruction)

/-- Complete, deterministic value-use inventory for one block. -/
def blockUses (block : Block) : Array Use :=
  let state := block.instructions.foldl scanInstruction (0, #[])
  recordTerminator state.1 state.2 block.terminator

/-- Declarative membership of an atom among an instruction's runtime value
operands.  This mirrors `recordInstruction` but is proof-facing and does not
expose the accumulator used by the executable inventory. -/
inductive InstrUsesAtom : Instr → Atom → Prop where
  | move {atom} : InstrUsesAtom (.move atom) atom
  | alloc {world cid arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.alloc world cid arguments) atom
  | allocWith {credit world cid arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.allocWith credit world cid arguments) atom
  | takeUnique {target cid} : InstrUsesAtom (.takeUnique target cid) target
  | resetShared {target cid} : InstrUsesAtom (.resetShared target cid) target
  | retainShared {target} : InstrUsesAtom (.retainShared target) target
  | releaseShared {target} : InstrUsesAtom (.releaseShared target) target
  | dropUnique {target} : InstrUsesAtom (.dropUnique target) target
  | freeUnique {target cid} : InstrUsesAtom (.freeUnique target cid) target
  | fetch {target cid field} : InstrUsesAtom (.fetch target cid field) target
  | call {function arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.call function arguments) atom
  | callSelf {arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.callSelf arguments) atom
  | papp {function arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.papp function arguments) atom
  | applyFunction {function arguments} :
      InstrUsesAtom (.apply function arguments) function
  | applyArgument {function arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.apply function arguments) atom
  | extern {function arguments atom} : atom ∈ arguments.toList →
      InstrUsesAtom (.extern function arguments) atom

/-- Declarative membership among an edge's transferred value operands. -/
inductive EdgeUsesAtom (edge : Edge) : Atom → Prop where
  | value {atom} : atom ∈ edge.values.toList → EdgeUsesAtom edge atom

/-- Declarative membership among a terminator's direct and edge value
operands. -/
inductive TerminatorUsesAtom : Terminator → Atom → Prop where
  | jump {edge atom} : EdgeUsesAtom edge atom →
      TerminatorUsesAtom (.jump edge) atom
  | switchScrutinee {scrutinee constructors natPeel} :
      TerminatorUsesAtom (.switchValue scrutinee constructors natPeel)
        scrutinee
  | switchCtor {scrutinee constructors natPeel alternative atom} :
      alternative ∈ constructors.toList → EdgeUsesAtom alternative.edge atom →
      TerminatorUsesAtom (.switchValue scrutinee constructors natPeel) atom
  | switchNatZero {scrutinee constructors peel atom} :
      EdgeUsesAtom peel.zero atom →
      TerminatorUsesAtom (.switchValue scrutinee constructors (some peel)) atom
  | switchNatSucc {scrutinee constructors peel atom} :
      EdgeUsesAtom peel.succ atom →
      TerminatorUsesAtom (.switchValue scrutinee constructors (some peel)) atom
  | branchSome {credit someEdge noneEdge atom} :
      EdgeUsesAtom someEdge atom →
      TerminatorUsesAtom (.branchCredit credit someEdge noneEdge) atom
  | branchNone {credit someEdge noneEdge atom} :
      EdgeUsesAtom noneEdge atom →
      TerminatorUsesAtom (.branchCredit credit someEdge noneEdge) atom
  | ret {atom} : TerminatorUsesAtom (.ret atom) atom
  | tailCall {function arguments atom} : atom ∈ arguments.toList →
      TerminatorUsesAtom (.tailCall function arguments) atom
  | tailCallSelf {arguments atom} : atom ∈ arguments.toList →
      TerminatorUsesAtom (.tailCallSelf arguments) atom

private theorem recordAtom_preserves {position : Nat} {uses : Array Use}
    {atom : Atom} {use : Use} (member : use ∈ uses) :
    use ∈ recordAtom position uses atom := by
  cases atom <;> simp [recordAtom, member]

private theorem foldRecordAtoms_preserves {position : Nat}
    {uses : Array Use} {atoms : List Atom} {use : Use}
    (member : use ∈ uses) :
    use ∈ atoms.foldl (recordAtom position) uses := by
  induction atoms generalizing uses with
  | nil => exact member
  | cons atom rest ih =>
      simp only [List.foldl_cons]
      exact ih (recordAtom_preserves member)

private theorem foldRecordAtoms_reg {position value : Nat}
    {uses : Array Use} {atoms : List Atom} {atom : Atom}
    (member : atom ∈ atoms) (register : atom = .reg value) :
    { value, position } ∈ atoms.foldl (recordAtom position) uses := by
  induction atoms generalizing uses with
  | nil => simp at member
  | cons head rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with same | tail
      · subst head
        subst atom
        apply foldRecordAtoms_preserves
        simp [recordAtom]
      · exact ih tail

private theorem recordAtoms_preserves {position : Nat} {uses : Array Use}
    {atoms : Array Atom} {use : Use} (member : use ∈ uses) :
    use ∈ recordAtoms position uses atoms := by
  unfold recordAtoms
  rw [← Array.foldl_toList]
  exact foldRecordAtoms_preserves member

private theorem recordAtoms_reg {position value : Nat}
    {uses : Array Use} {atoms : Array Atom} {atom : Atom}
    (member : atom ∈ atoms.toList) (register : atom = .reg value) :
    { value, position } ∈ recordAtoms position uses atoms := by
  unfold recordAtoms
  rw [← Array.foldl_toList]
  exact foldRecordAtoms_reg member register

private theorem recordInstruction_preserves {position : Nat}
    {uses : Array Use} {instruction : Instr} {use : Use}
    (member : use ∈ uses) :
    use ∈ recordInstruction position uses instruction := by
  cases instruction with
  | move atom => exact recordAtom_preserves member
  | alloc world cid arguments => exact recordAtoms_preserves member
  | allocWith credit world cid arguments =>
      exact recordAtoms_preserves member
  | discardCredit credit => exact member
  | takeUnique target cid => exact recordAtom_preserves member
  | resetShared target cid => exact recordAtom_preserves member
  | retainShared target => exact recordAtom_preserves member
  | releaseShared target => exact recordAtom_preserves member
  | dropUnique target => exact recordAtom_preserves member
  | freeUnique target cid => exact recordAtom_preserves member
  | fetch target cid field => exact recordAtom_preserves member
  | call function arguments => exact recordAtoms_preserves member
  | callSelf arguments => exact recordAtoms_preserves member
  | papp function arguments => exact recordAtoms_preserves member
  | apply function arguments =>
      exact recordAtoms_preserves (recordAtom_preserves member)
  | extern function arguments => exact recordAtoms_preserves member

private theorem recordInstruction_reg {position value : Nat}
    {uses : Array Use} {instruction : Instr} {atom : Atom}
    (operand : InstrUsesAtom instruction atom)
    (register : atom = .reg value) :
    { value, position } ∈ recordInstruction position uses instruction := by
  cases operand with
  | move =>
      cases register
      simp [recordInstruction, recordAtom]
  | alloc member =>
      exact recordAtoms_reg member register
  | allocWith member =>
      exact recordAtoms_reg member register
  | takeUnique =>
      cases register
      simp [recordInstruction, recordAtom]
  | resetShared =>
      cases register
      simp [recordInstruction, recordAtom]
  | retainShared =>
      cases register
      simp [recordInstruction, recordAtom]
  | releaseShared =>
      cases register
      simp [recordInstruction, recordAtom]
  | dropUnique =>
      cases register
      simp [recordInstruction, recordAtom]
  | freeUnique =>
      cases register
      simp [recordInstruction, recordAtom]
  | fetch =>
      cases register
      simp [recordInstruction, recordAtom]
  | call member =>
      exact recordAtoms_reg member register
  | callSelf member =>
      exact recordAtoms_reg member register
  | papp member =>
      exact recordAtoms_reg member register
  | applyFunction =>
      cases register
      apply recordAtoms_preserves
      simp [recordAtom]
  | applyArgument member =>
      exact recordAtoms_reg member register
  | extern member =>
      exact recordAtoms_reg member register

private theorem recordEdge_preserves {position : Nat} {uses : Array Use}
    {edge : Edge} {use : Use} (member : use ∈ uses) :
    use ∈ recordEdge position uses edge :=
  recordAtoms_preserves member

private theorem recordEdge_reg {position value : Nat} {uses : Array Use}
    {edge : Edge} {atom : Atom} (operand : EdgeUsesAtom edge atom)
    (register : atom = .reg value) :
    { value, position } ∈ recordEdge position uses edge := by
  cases operand with
  | value member => exact recordAtoms_reg member register

private theorem foldCtorEdges_preserves {position : Nat}
    {uses : Array Use} {constructors : List CtorAlt} {use : Use}
    (member : use ∈ uses) :
    use ∈ constructors.foldl
      (fun current alternative => recordEdge position current alternative.edge)
      uses := by
  induction constructors generalizing uses with
  | nil => exact member
  | cons alternative rest ih =>
      simp only [List.foldl_cons]
      exact ih (recordEdge_preserves member)

private theorem foldCtorEdges_reg {position value : Nat}
    {uses : Array Use} {constructors : List CtorAlt}
    {alternative : CtorAlt} {atom : Atom}
    (member : alternative ∈ constructors)
    (operand : EdgeUsesAtom alternative.edge atom)
    (register : atom = .reg value) :
    { value, position } ∈ constructors.foldl
      (fun current candidate => recordEdge position current candidate.edge)
      uses := by
  induction constructors generalizing uses with
  | nil => simp at member
  | cons head rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with same | tail
      · subst head
        apply foldCtorEdges_preserves
        exact recordEdge_reg operand register
      · exact ih tail

private theorem recordTerminator_preserves {position : Nat}
    {uses : Array Use} {terminator : Terminator} {use : Use}
    (member : use ∈ uses) :
    use ∈ recordTerminator position uses terminator := by
  cases terminator with
  | jump edge => exact recordEdge_preserves member
  | switchValue scrutinee constructors natPeel =>
      have afterScrutinee : use ∈ recordAtom position uses scrutinee :=
        recordAtom_preserves member
      have afterConstructors : use ∈ constructors.foldl
          (fun current alternative =>
            recordEdge position current alternative.edge)
          (recordAtom position uses scrutinee) := by
        rw [← Array.foldl_toList]
        exact foldCtorEdges_preserves afterScrutinee
      cases natPeel with
      | none => exact afterConstructors
      | some peel =>
          exact recordEdge_preserves
            (recordEdge_preserves afterConstructors)
  | branchCredit credit someEdge noneEdge =>
      exact recordEdge_preserves (recordEdge_preserves member)
  | ret atom => exact recordAtom_preserves member
  | tailCall function arguments => exact recordAtoms_preserves member
  | tailCallSelf arguments => exact recordAtoms_preserves member

private theorem foldInstructions_preserves {state : Nat × Array Use}
    {instructions : List Instr} {use : Use} (member : use ∈ state.2) :
    use ∈ (instructions.foldl scanInstruction state).2 := by
  induction instructions generalizing state with
  | nil => exact member
  | cons instruction rest ih =>
      simp only [List.foldl_cons]
      apply ih
      exact recordInstruction_preserves member

private theorem foldInstructions_reg (instructions : List Instr) :
    ∀ {start : Nat} {uses : Array Use} {index : Nat}
      {instruction : Instr} {atom : Atom} {value : Nat},
      instructions[index]? = some instruction →
      InstrUsesAtom instruction atom →
      atom = .reg value →
      (⟨value, start + index⟩ : Use) ∈
        (instructions.foldl scanInstruction (start, uses)).2 := by
  induction instructions with
  | nil =>
      intro start uses index instruction atom value found
      simp at found
  | cons head rest ih =>
      intro start uses index instruction atom value found operand register
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst instruction
          simp only [List.foldl_cons, Nat.add_zero]
          apply foldInstructions_preserves
          change (⟨value, start⟩ : Use) ∈
            recordInstruction start uses head
          exact recordInstruction_reg operand register
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          simp only [List.foldl_cons]
          have recorded := ih (start := start + 1)
            (uses := recordInstruction start uses head) found operand register
          simpa [scanInstruction, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using recorded

private theorem foldInstructions_position (instructions : List Instr)
    (start : Nat) (uses : Array Use) :
    (instructions.foldl scanInstruction (start, uses)).1 =
      start + instructions.length := by
  induction instructions generalizing start uses with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [scanInstruction, List.length_cons]
      omega

private theorem recordTerminator_reg {position value : Nat}
    {uses : Array Use} {terminator : Terminator} {atom : Atom}
    (operand : TerminatorUsesAtom terminator atom)
    (register : atom = .reg value) :
    { value, position } ∈ recordTerminator position uses terminator := by
  cases operand with
  | jump edgeOperand => exact recordEdge_reg edgeOperand register
  | @switchScrutinee scrutinee constructors natPeel =>
      cases register
      unfold recordTerminator
      have afterScrutinee : (⟨value, position⟩ : Use) ∈
          recordAtom position uses (.reg value) := by
        simp [recordAtom]
      have afterConstructors : (⟨value, position⟩ : Use) ∈
          constructors.foldl
            (fun current alternative =>
              recordEdge position current alternative.edge)
            (recordAtom position uses (.reg value)) := by
        rw [← Array.foldl_toList]
        exact foldCtorEdges_preserves afterScrutinee
      cases natPeel with
      | none => exact afterConstructors
      | some peel =>
          exact recordEdge_preserves
            (recordEdge_preserves afterConstructors)
  | @switchCtor scrutinee constructors natPeel alternative atom member
      edgeOperand =>
      cases natPeel with
      | none =>
          simp only [recordTerminator]
          rw [← Array.foldl_toList]
          exact foldCtorEdges_reg member edgeOperand register
      | some peel =>
          simp only [recordTerminator]
          apply recordEdge_preserves
          apply recordEdge_preserves
          rw [← Array.foldl_toList]
          exact foldCtorEdges_reg member edgeOperand register
  | switchNatZero edgeOperand =>
      unfold recordTerminator
      apply recordEdge_preserves
      exact recordEdge_reg edgeOperand register
  | switchNatSucc edgeOperand =>
      unfold recordTerminator
      exact recordEdge_reg edgeOperand register
  | branchSome edgeOperand =>
      unfold recordTerminator
      apply recordEdge_preserves
      exact recordEdge_reg edgeOperand register
  | branchNone edgeOperand =>
      unfold recordTerminator
      exact recordEdge_reg edgeOperand register
  | ret =>
      cases register
      simp [recordTerminator, recordAtom]
  | tailCall member =>
      exact recordAtoms_reg member register
  | tailCallSelf member =>
      exact recordAtoms_reg member register

/-- Every declarative register operand of an indexed instruction occurs in
the executable block-use inventory at that instruction's position. -/
theorem instruction_reg_mem_blockUses {block : Block} {position : Nat}
    {instruction : Instr} {atom : Atom} {value : Nat}
    (found : block.instructions[position]? = some instruction)
    (operand : InstrUsesAtom instruction atom)
    (register : atom = .reg value) :
    (⟨value, position⟩ : Use) ∈ blockUses block := by
  unfold blockUses
  rw [← Array.foldl_toList]
  apply recordTerminator_preserves
  have listFound : block.instructions.toList[position]? = some instruction := by
    simpa using found
  have recorded := foldInstructions_reg block.instructions.toList
    (start := 0) (uses := (#[] : Array Use)) listFound operand register
  simpa using recorded

/-- Every declarative direct register operand of a terminator occurs at the
terminator position in the executable block-use inventory. -/
theorem terminator_reg_mem_blockUses {block : Block} {atom : Atom}
    {value : Nat} (operand : TerminatorUsesAtom block.terminator atom)
    (register : atom = .reg value) :
    (⟨value, block.instructions.size⟩ : Use) ∈ blockUses block := by
  unfold blockUses
  rw [← Array.foldl_toList]
  have position :
      (block.instructions.toList.foldl scanInstruction (0, #[])).1 =
        block.instructions.size := by
    simpa using foldInstructions_position block.instructions.toList 0 #[]
  rw [← position]
  exact recordTerminator_reg operand register

private theorem mem_recordAtom {position : Nat} {uses : Array Use}
    {atom : Atom} {use : Use}
    (member : use ∈ recordAtom position uses atom) :
    use ∈ uses ∨
      (use.position = position ∧ atom = .reg use.value) := by
  cases atom with
  | reg value =>
      simp only [recordAtom, Array.mem_push] at member
      cases member with
      | inl member => exact .inl member
      | inr same =>
          subst use
          exact .inr ⟨rfl, rfl⟩
  | lit literal => exact .inl member
  | erased => exact .inl member

private theorem mem_foldRecordAtoms {position : Nat} {uses : Array Use}
    {atoms : List Atom} {use : Use}
    (member : use ∈ atoms.foldl (recordAtom position) uses) :
    use ∈ uses ∨
      ∃ atom ∈ atoms,
        use.position = position ∧ atom = .reg use.value := by
  induction atoms generalizing uses with
  | nil => exact .inl member
  | cons head tail ih =>
      simp only [List.foldl_cons] at member
      cases ih member with
      | inl first =>
          cases mem_recordAtom first with
          | inl previous => exact .inl previous
          | inr added =>
              exact .inr ⟨head, by simp, added⟩
      | inr later =>
          obtain ⟨atom, atomMem, added⟩ := later
          exact .inr ⟨atom, by simp [atomMem], added⟩

private theorem mem_recordAtoms {position : Nat} {uses : Array Use}
    {atoms : Array Atom} {use : Use}
    (member : use ∈ recordAtoms position uses atoms) :
    use ∈ uses ∨
      ∃ atom ∈ atoms.toList,
        use.position = position ∧ atom = .reg use.value := by
  unfold recordAtoms at member
  rw [← Array.foldl_toList] at member
  exact mem_foldRecordAtoms member

private theorem mem_recordInstruction {position : Nat} {uses : Array Use}
    {instruction : Instr} {use : Use}
    (member : use ∈ recordInstruction position uses instruction) :
    use ∈ uses ∨
      (use.position = position ∧
        InstrUsesAtom instruction (.reg use.value)) := by
  cases instruction with
  | move atom =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added =>
          exact .inr ⟨added.1, added.2 ▸ .move⟩
  | alloc world cid arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .alloc atomMem⟩
  | allocWith credit world cid arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .allocWith atomMem⟩
  | discardCredit credit => exact .inl member
  | takeUnique target cid =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .takeUnique⟩
  | resetShared target cid =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .resetShared⟩
  | retainShared target =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .retainShared⟩
  | releaseShared target =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .releaseShared⟩
  | dropUnique target =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .dropUnique⟩
  | freeUnique target cid =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .freeUnique⟩
  | fetch target cid field =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .fetch⟩
  | call function arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .call atomMem⟩
  | callSelf arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .callSelf atomMem⟩
  | papp function arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .papp atomMem⟩
  | apply function arguments =>
      cases mem_recordAtoms member with
      | inl beforeArguments =>
          cases mem_recordAtom beforeArguments with
          | inl previous => exact .inl previous
          | inr added =>
              exact .inr ⟨added.1, added.2 ▸ .applyFunction⟩
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .applyArgument atomMem⟩
  | extern function arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .extern atomMem⟩

private theorem mem_recordEdge {position : Nat} {uses : Array Use}
    {edge : Edge} {use : Use}
    (member : use ∈ recordEdge position uses edge) :
    use ∈ uses ∨
      (use.position = position ∧
        EdgeUsesAtom edge (.reg use.value)) := by
  cases mem_recordAtoms member with
  | inl previous => exact .inl previous
  | inr added =>
      obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
      exact .inr ⟨positionEq, atomEq ▸ .value atomMem⟩

private theorem mem_foldCtorEdges {position : Nat} {uses : Array Use}
    {constructors : List CtorAlt} {use : Use}
    (member : use ∈ constructors.foldl
      (fun current alternative =>
        recordEdge position current alternative.edge) uses) :
    use ∈ uses ∨
      ∃ alternative ∈ constructors,
        use.position = position ∧
          EdgeUsesAtom alternative.edge (.reg use.value) := by
  induction constructors generalizing uses with
  | nil => exact .inl member
  | cons head tail ih =>
      simp only [List.foldl_cons] at member
      cases ih member with
      | inl first =>
          cases mem_recordEdge first with
          | inl previous => exact .inl previous
          | inr added => exact .inr ⟨head, by simp, added⟩
      | inr later =>
          obtain ⟨alternative, alternativeMem, added⟩ := later
          exact .inr ⟨alternative, by simp [alternativeMem], added⟩

private theorem mem_recordTerminator {position : Nat} {uses : Array Use}
    {terminator : Terminator} {use : Use}
    (member : use ∈ recordTerminator position uses terminator) :
    use ∈ uses ∨
      (use.position = position ∧
        TerminatorUsesAtom terminator (.reg use.value)) := by
  cases terminator with
  | jump edge =>
      cases mem_recordEdge member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, .jump added.2⟩
  | switchValue scrutinee constructors natPeel =>
      cases natPeel with
      | none =>
          simp only [recordTerminator] at member
          rw [← Array.foldl_toList] at member
          cases mem_foldCtorEdges member with
          | inl beforeConstructors =>
              cases mem_recordAtom beforeConstructors with
              | inl previous => exact .inl previous
              | inr added =>
                  exact .inr ⟨added.1, added.2 ▸ .switchScrutinee⟩
          | inr added =>
              obtain ⟨alternative, alternativeMem, positionEq, operand⟩ :=
                added
              exact .inr ⟨positionEq,
                .switchCtor (by simpa using alternativeMem) operand⟩
      | some peel =>
          simp only [recordTerminator] at member
          cases mem_recordEdge member with
          | inr added => exact .inr ⟨added.1, .switchNatSucc added.2⟩
          | inl beforeSucc =>
              cases mem_recordEdge beforeSucc with
              | inr added => exact .inr ⟨added.1, .switchNatZero added.2⟩
              | inl beforeNat =>
                  rw [← Array.foldl_toList] at beforeNat
                  cases mem_foldCtorEdges beforeNat with
                  | inl beforeConstructors =>
                      cases mem_recordAtom beforeConstructors with
                      | inl previous => exact .inl previous
                      | inr added =>
                          exact .inr
                            ⟨added.1, added.2 ▸ .switchScrutinee⟩
                  | inr added =>
                      obtain ⟨alternative, alternativeMem, positionEq,
                        operand⟩ := added
                      exact .inr ⟨positionEq,
                        .switchCtor (by simpa using alternativeMem) operand⟩
  | branchCredit credit someEdge noneEdge =>
      cases mem_recordEdge member with
      | inr added => exact .inr ⟨added.1, .branchNone added.2⟩
      | inl beforeNone =>
          cases mem_recordEdge beforeNone with
          | inl previous => exact .inl previous
          | inr added => exact .inr ⟨added.1, .branchSome added.2⟩
  | ret atom =>
      cases mem_recordAtom member with
      | inl previous => exact .inl previous
      | inr added => exact .inr ⟨added.1, added.2 ▸ .ret⟩
  | tailCall function arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .tailCall atomMem⟩
  | tailCallSelf arguments =>
      cases mem_recordAtoms member with
      | inl previous => exact .inl previous
      | inr added =>
          obtain ⟨atom, atomMem, positionEq, atomEq⟩ := added
          exact .inr ⟨positionEq, atomEq ▸ .tailCallSelf atomMem⟩

private theorem mem_foldInstructions (instructions : List Instr) :
    ∀ {start : Nat} {uses : Array Use} {use : Use},
      use ∈ (instructions.foldl scanInstruction (start, uses)).2 →
      use ∈ uses ∨
        ∃ index instruction,
          instructions[index]? = some instruction ∧
            use.position = start + index ∧
            InstrUsesAtom instruction (.reg use.value) := by
  induction instructions with
  | nil =>
      intro start uses use member
      exact .inl member
  | cons head tail ih =>
      intro start uses use member
      simp only [List.foldl_cons] at member
      have classified := ih (start := start + 1)
        (uses := recordInstruction start uses head) (use := use)
        (by simpa [scanInstruction] using member)
      cases classified with
      | inl first =>
          cases mem_recordInstruction first with
          | inl previous => exact .inl previous
          | inr added =>
              exact .inr ⟨0, head, by simp, by simpa using added.1,
                added.2⟩
      | inr later =>
          obtain ⟨index, instruction, found, positionEq, operand⟩ := later
          exact .inr ⟨index + 1, instruction, by simpa using found,
            by omega, operand⟩

/-- Every executable use-inventory entry comes from either the instruction
at its recorded position or the block terminator. Together with the forward
lemmas above, this makes `blockUses` a faithful syntax inventory. -/
theorem mem_blockUses {block : Block} {use : Use}
    (member : use ∈ blockUses block) :
    (∃ instruction,
        block.instructions[use.position]? = some instruction ∧
          InstrUsesAtom instruction (.reg use.value)) ∨
      (use.position = block.instructions.size ∧
        TerminatorUsesAtom block.terminator (.reg use.value)) := by
  unfold blockUses at member
  rw [← Array.foldl_toList] at member
  cases mem_recordTerminator member with
  | inl beforeTerminator =>
      have classified := mem_foldInstructions block.instructions.toList
        (start := 0) (uses := #[]) beforeTerminator
      cases classified with
      | inl empty => simp at empty
      | inr instructionUse =>
          obtain ⟨index, instruction, found, positionEq, operand⟩ :=
            instructionUse
          left
          have positionEq' : use.position = index := by simpa using positionEq
          exact ⟨instruction, by rw [positionEq']; simpa using found,
            operand⟩
  | inr terminatorUse =>
      right
      refine ⟨terminatorUse.1.trans ?_, terminatorUse.2⟩
      simpa using foldInstructions_position block.instructions.toList 0 #[]

/-- Dense conservative last-use vector.  Entry `0` means no claimed use;
entry `position + 1` means live through at least that position. -/
structure BlockSummary where
  lastUses : Array Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

private def growTo (values : Array Nat) (size : Nat) : Array Nat :=
  if size ≤ values.size then values
  else values ++ Array.replicate (size - values.size) 0

private def recordLastUse (values : Array Nat) (use : Use) : Array Nat :=
  let values := growTo values (use.value + 1)
  let previous := (values[use.value]?).getD 0
  values.setIfInBounds use.value (max previous (use.position + 1))

/-- Exact local solution produced by the default planner.  The checker does
not rely on exactness and also accepts conservative larger bounds. -/
def inferBlock (block : Block) : BlockSummary :=
  { lastUses := (blockUses block).foldl recordLastUse
      (Array.replicate block.valueParams.size 0) }

def BlockSummary.lastUse? (summary : BlockSummary)
    (value : ValueId) : Option Nat := do
  let encoded ← summary.lastUses[value]?
  match encoded with
  | 0 => none
  | position + 1 => some position

/-- Does this proposal cover this particular semantic operand use? -/
def coversUse (summary : BlockSummary) (use : Use) : Bool :=
  match summary.lastUses[use.value]? with
  | some bound => use.position < bound
  | none => false

/-- Every syntactic semantic use must be included.  Extra liveness is safe. -/
def covers (block : Block) (summary : BlockSummary) : Bool :=
  (blockUses block).all (coversUse summary)

structure Stats where
  uses : Nat
  valueSlots : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Resource where
  | uses
  | valueSlots
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Error where
  | limit (resource : Resource) (actual maximum : Nat)
  | uncoveredUse
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- A checked conservative local solution.  The retained equation is the
proof-facing reflection boundary for individual-use theorems. -/
structure CheckedBlock (block : Block) where
  summary : BlockSummary
  stats : Stats
  accepted : covers block summary = true

def checkBlockWith (limits : Validate.Limits) (block : Block)
    (summary : BlockSummary) : Except Error (CheckedBlock block) :=
  let uses := blockUses block
  if uses.size > limits.maxFlowWork then
    .error (.limit .uses uses.size limits.maxFlowWork)
  else if summary.lastUses.size > limits.maxValueRegisters then
    .error (.limit .valueSlots summary.lastUses.size limits.maxValueRegisters)
  else if accepted : covers block summary = true then
    .ok { summary
          stats := { uses := uses.size, valueSlots := summary.lastUses.size }
          accepted }
  else
    .error .uncoveredUse

def checkBlock (block : Block) (summary : BlockSummary) :
    Except Error (CheckedBlock block) :=
  checkBlockWith Validate.defaultLimits block summary

/-- Run the default exact planner through the same untrusted-artifact checker
used for externally supplied conservative proposals. -/
def inferCheckedWith (limits : Validate.Limits) (block : Block) :
    Except Error (CheckedBlock block) :=
  let uses := blockUses block
  if uses.size > limits.maxFlowWork then
    .error (.limit .uses uses.size limits.maxFlowWork)
  else
    let requiredSlots := uses.foldl
      (fun size use => max size (use.value + 1)) block.valueParams.size
    if requiredSlots > limits.maxValueRegisters then
      .error (.limit .valueSlots requiredSlots limits.maxValueRegisters)
    else
      checkBlockWith limits block (inferBlock block)

def inferChecked (block : Block) : Except Error (CheckedBlock block) :=
  inferCheckedWith Validate.defaultLimits block

namespace CheckedBlock

/-- Every indexed source use is covered by the retained checked proposal. -/
theorem coversAt {block : Block} (checked : CheckedBlock block)
    (index : Nat) (bound : index < (blockUses block).size) :
    coversUse checked.summary (blockUses block)[index] = true := by
  exact (Array.all_eq_true.mp checked.accepted) index bound

/-- A checked exact bound at `position` excludes every later syntactic use of
that register in the block. -/
theorem no_use_after {block : Block} (checked : CheckedBlock block)
    {value : ValueId} {position : Nat}
    (last : checked.summary.lastUse? value = some position) :
    ∀ index, (bound : index < (blockUses block).size) →
      (blockUses block)[index].value = value →
      (blockUses block)[index].position ≤ position := by
  intro index bound sameValue
  have covered := checked.coversAt index bound
  unfold coversUse at covered
  have encoded : checked.summary.lastUses[value]? = some (position + 1) := by
    cases found : checked.summary.lastUses[value]? with
    | none => simp [BlockSummary.lastUse?, found] at last
    | some valueBound =>
        cases valueBound with
        | zero => simp [BlockSummary.lastUse?, found] at last
        | succ predecessor =>
            simp [BlockSummary.lastUse?, found] at last
            subst predecessor
            rfl
  rw [sameValue, encoded] at covered
  simp only at covered
  exact Nat.le_of_lt_succ (of_decide_eq_true covered)

end CheckedBlock

end Ix.Compiler.IxIR2.Liveness
