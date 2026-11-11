import Aiur.Optimized.PhysicalSemantics
import Mathlib.Data.List.Dedup

/-!
An activation pass for the final physical circuit. It preserves every active
row and makes the all-zero row silent padding, without multiplying every
constraint by another selector. This is separate from the source compiler:
its existing local-rule correctness theorem composes with `active_rule_iff`.
-/

namespace Aiur.Optimized.Activation

open Circuit
variable {F : Type} [Field F] [DecidableEq F]

/-- Replace the constant term by that constant times the row selector. -/
def polynomial (selector : Nat) (p : Polynomial F) : Polynomial F :=
  Polynomial.simplify (.sub p (.mul (.const (p.denote fun _ => 0)) (.sub (.const 1) (.var selector))))

@[simp] theorem polynomial_active (selector : Nat) (p : Polynomial F)
    (a : Nat → F) (active : a selector = 1) :
    (polynomial selector p).denote a = p.denote a := by
  simp [polynomial, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, active]

@[simp] theorem polynomial_zero (selector : Nat) (p : Polynomial F) :
    (polynomial selector p).denote (fun _ => 0) = 0 := by
  simp [polynomial, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote]

def boolean (selector : Nat) : Polynomial F :=
  .mul (.var selector) (.sub (.var selector) (.const 1))

def silent (selector : Nat) (enable : Polynomial F) : Polynomial F :=
  Polynomial.simplify (.mul (.sub (.const 1) (.var selector)) enable)

def send (selector : Nat) (s : Send F) : Send F :=
  { s with enable := polynomial selector s.enable }

def memory (selector : Nat) (m : MemoryLookup F) : MemoryLookup F :=
  { m with enable := polynomial selector m.enable }

/-- Explicit silence constraints cover arbitrary chips, including nonzero
inactive assignments. Repeated enables share a single such constraint. -/
def guards (chip : Chip F) : List (Polynomial F) :=
  ((chip.sends.map fun s => (send chip.numVars s).enable) ++
    (chip.memory.map fun m => (memory chip.numVars m).enable)).dedup

def compile (chip : Chip F) : Chip F :=
  { chip with
    numVars := chip.numVars + 1
    constraints := boolean chip.numVars ::
      chip.constraints.map (polynomial chip.numVars) ++
      (guards chip).map (silent chip.numVars)
    sends := chip.sends.map (send chip.numVars)
    memory := chip.memory.map (memory chip.numVars) }

theorem selector_boolean (chip : Chip F) (a : Nat → F)
    (valid : (compile chip).ValidAssignment rom a) :
    a chip.numVars = 0 ∨ a chip.numVars = 1 := by
  have h := valid.1 (boolean chip.numVars) (by simp [compile])
  simpa [boolean, Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] using h

theorem guard_inactive (chip : Chip F) (a : Nat → F)
    (valid : (compile chip).ValidAssignment rom a) (inactive : a chip.numVars = 0)
    (g : Polynomial F) (member : g ∈ guards chip) : g.denote a = 0 := by
  have h := valid.1 (silent chip.numVars g)
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨g, member, rfl⟩)))
  simpa [silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, inactive] using h

theorem requirements_inactive (chip : Chip F) (a : Nat → F)
    (valid : (compile chip).ValidAssignment rom a) (inactive : a chip.numVars = 0) :
    (compile chip).requirements a = [] := by
  simp only [Chip.requirements, compile, List.filterMap_map]
  apply List.filterMap_eq_nil_iff.mpr
  intro s member
  have h := guard_inactive chip a valid inactive (send chip.numVars s).enable (by
    apply List.mem_dedup.mpr
    exact List.mem_append_left _ (List.mem_map.mpr ⟨s, member, rfl⟩))
  simp [h]

theorem memory_inactive (chip : Chip F) (a : Nat → F)
    (valid : (compile chip).ValidAssignment rom a) (inactive : a chip.numVars = 0)
    (m : MemoryLookup F) (member : m ∈ (compile chip).memory) : m.enable.denote a = 0 := by
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact guard_inactive chip a valid inactive _ (by
    apply List.mem_dedup.mpr
    exact List.mem_append_right _ (List.mem_map.mpr ⟨source, sourceMember, rfl⟩))

theorem valid_active_iff (chip : Chip F) (a : Nat → F) (active : a chip.numVars = 1) :
    (compile chip).ValidAssignment rom a ↔ chip.ValidAssignment rom a := by
  have constraint (p : Polynomial F) :
      (polynomial chip.numVars p).denote a = p.denote a := polynomial_active _ _ _ active
  have silence (p : Polynomial F) : (silent chip.numVars p).denote a = 0 := by
    simp [silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, active]
  constructor
  · intro valid
    refine ⟨fun p member => ?_, fun m member => ?_⟩
    · have h := valid.1 (polynomial chip.numVars p)
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨p, member, rfl⟩)))
      simpa only [constraint] using h
    · have h := valid.2 (memory chip.numVars m) (List.mem_map.mpr ⟨m, member, rfl⟩)
      simpa only [memory, MemoryLookup.Valid, constraint] using h
  · intro valid
    refine ⟨?_, ?_⟩
    · intro p member
      rcases List.mem_cons.mp member with rfl | member
      · simp [boolean, Scalar.Circuit.ArithExpr.denote, active]
      · rcases List.mem_append.mp member with member | member
        · obtain ⟨p, sourceMember, rfl⟩ := List.mem_map.mp member
          simpa only [constraint] using valid.1 p sourceMember
        · obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
          exact silence p
    · intro m member
      obtain ⟨m, sourceMember, rfl⟩ := List.mem_map.mp member
      simpa only [memory, MemoryLookup.Valid, constraint] using valid.2 m sourceMember

theorem requirements_active (chip : Chip F) (a : Nat → F) (active : a chip.numVars = 1) :
    (compile chip).requirements a = chip.requirements a := by
  simp [Chip.requirements, compile, List.filterMap_map, send, Send.message, active]

theorem conclusion_eq (chip : Chip F) (a : Nat → F) :
    (compile chip).conclusion a = chip.conclusion a := rfl

/-- Zero padding needs no source values, hints, ROM membership, or calls. -/
theorem zero_valid (chip : Chip F) (rom : WireROM F) :
    (compile chip).ValidAssignment rom (fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro p member
    rcases List.mem_cons.mp member with rfl | member
    · simp [boolean, Scalar.Circuit.ArithExpr.denote]
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
        exact polynomial_zero _ _
      · obtain ⟨g, guardMember, rfl⟩ := List.mem_map.mp member
        have zero : g.denote (fun _ => 0) = 0 := by
          simp only [guards, List.mem_dedup, List.mem_append, List.mem_map] at guardMember
          rcases guardMember with member | member
          · obtain ⟨s, _, same⟩ := member
            rw [← same]
            exact polynomial_zero _ _
          · obtain ⟨m, _, same⟩ := member
            rw [← same]
            exact polynomial_zero _ _
        simp [silent, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, zero]
  · intro m member
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp member
    simp [memory, MemoryLookup.Valid]

theorem zero_requirements (chip : Chip F) (rom : WireROM F) :
    (compile chip).requirements (fun _ => 0) = [] :=
  requirements_inactive chip _ (zero_valid chip rom) rfl

/-- The active part of the transformed chip has exactly the original local
rule. No source evaluation or compiler theorem is weakened by padding. -/
theorem active_rule_iff (chip : Chip F) (formed : chip.wellFormed = true)
    (paddedFormed : (compile chip).wellFormed = true) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    (∃ row : Row F, row.chip = chip.name ∧ (compile chip).ValidRow rom row ∧
      row.assignment chip.numVars = 1 ∧ (compile chip).receive row = root ∧
      (compile chip).premises row = premises) ↔ chip.LocalRule rom root premises := by
  constructor
  · rintro ⟨row, _, valid, active, rootEq, callsEq⟩
    have sourceValid := (valid_active_iff chip row.assignment active).mp valid.2.2
    have finite := chip.finiteAssignment formed row.assignment rom
    refine ⟨Row.ofAssignment chip.name chip.numVars row.assignment, rfl,
      ⟨formed, Row.ofAssignment_length _ _ _, finite.1.mp sourceValid⟩, ?_, ?_⟩
    · exact finite.2.1.symm.trans rootEq
    · exact finite.2.2.symm.trans ((requirements_active chip row.assignment active).symm.trans callsEq)
  · rintro ⟨row, _, valid, rootEq, callsEq⟩
    let a := Function.update row.assignment chip.numVars 1
    have active : a chip.numVars = 1 := by simp [a]
    have same := chip.agree (a := row.assignment) (b := a) (fun id member => by
      have bound := chip.wellFormed_variables formed id member
      simp [a, Function.update_of_ne (Nat.ne_of_lt bound)]) rom
    have targetValid := (valid_active_iff chip a active).mpr (same.1.mp valid.2.2)
    have finite := (compile chip).finiteAssignment paddedFormed a rom
    refine ⟨Row.ofAssignment chip.name (chip.numVars + 1) a, rfl,
      ⟨paddedFormed, Row.ofAssignment_length _ _ _, finite.1.mp targetValid⟩, ?_, ?_, ?_⟩
    · rw [Row.ofAssignment_agree _ _ _ _ (Nat.lt_succ_self _)]
      exact active
    · exact finite.2.1.symm.trans (same.2.1.symm.trans rootEq)
    · exact finite.2.2.symm.trans ((requirements_active chip a active).trans
        (same.2.2.symm.trans callsEq))

end Aiur.Optimized.Activation
