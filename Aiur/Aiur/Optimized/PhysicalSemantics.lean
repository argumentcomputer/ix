import Aiur.Optimized.PolynomialFacts
import Aiur.Circuit.RowWitness

namespace Aiur.Circuit

open Aiur.Optimized (Polynomial)

variable {F : Type} [Field F] [DecidableEq F]

/-- A physical local rule, retaining the exact ordered list of call slots. -/
def Chip.LocalRule (chip : Chip F) (rom : WireROM F)
    (conclusion : Message F) (premises : List (Message F)) : Prop :=
  ∃ row, row.chip = chip.name ∧ chip.ValidRow rom row ∧
    chip.receive row = conclusion ∧ chip.premises row = premises

def Chip.ValidAssignment (chip : Chip F) (rom : WireROM F) (a : Var → F) : Prop :=
  Satisfies chip.constraints a ∧ ∀ lookup ∈ chip.memory, lookup.Valid rom a

def Chip.conclusion (chip : Chip F) (a : Var → F) : Message F :=
  ⟨chip.name, chip.inputs.map (WireValue.map a), chip.output.map (ArithExpr.denote a)⟩

def Chip.requirements (chip : Chip F) (a : Var → F) : List (Message F) :=
  chip.sends.filterMap fun send =>
    if send.enable.denote a = 1 then some (send.message a) else none

def Chip.Refines (source target : Chip F) : Prop :=
  ∀ rom a, source.ValidAssignment rom a → ∃ b,
    target.ValidAssignment rom b ∧ target.conclusion b = source.conclusion a ∧
      target.requirements b = source.requirements a

def Chip.Equivalent (source target : Chip F) : Prop :=
  source.Refines target ∧ target.Refines source

theorem Chip.Equivalent.refl (chip : Chip F) : chip.Equivalent chip :=
  ⟨fun _ a valid => ⟨a, valid, rfl, rfl⟩, fun _ a valid => ⟨a, valid, rfl, rfl⟩⟩

theorem Chip.Refines.trans {first second third : Chip F}
    (left : first.Refines second) (right : second.Refines third) : first.Refines third := by
  intro rom a valid
  obtain ⟨b, valid, root, calls⟩ := left rom a valid
  obtain ⟨c, valid, root', calls'⟩ := right rom b valid
  exact ⟨c, valid, root'.trans root, calls'.trans calls⟩

theorem Chip.Equivalent.trans {first second third : Chip F}
    (left : first.Equivalent second) (right : second.Equivalent third) : first.Equivalent third :=
  ⟨left.1.trans right.1, right.2.trans left.2⟩

/-- Include guards, interfaces, and inactive lookup slots when finding unused columns. -/
def Chip.expressions (chip : Chip F) : List (ArithExpr F) :=
  (chip.inputs.flatMap WireValue.words).map .var ++ chip.output.words ++ chip.constraints ++
    chip.sends.flatMap (fun send => send.enable ::
      send.args.flatMap WireValue.words ++ send.result.words.map .var) ++
    chip.memory.flatMap (fun lookup => lookup.enable :: lookup.address :: lookup.value.words)

def Chip.variables (chip : Chip F) : List Var := chip.expressions.flatMap Polynomial.vars

theorem Chip.agree {chip : Chip F} {a b : Var → F}
    (agree : ∀ id ∈ chip.variables, a id = b id) (rom : WireROM F) :
    (chip.ValidAssignment rom a ↔ chip.ValidAssignment rom b) ∧
      chip.conclusion a = chip.conclusion b ∧ chip.requirements a = chip.requirements b := by
  have expr (p : ArithExpr F) (member : p ∈ chip.expressions) : p.denote a = p.denote b :=
    Polynomial.denote_congr p (fun id present => agree id (List.mem_flatMap.mpr ⟨p, member, present⟩))
  have inputs (wire : WireValue Var) (member : wire ∈ chip.inputs) : wire.map a = wire.map b := by
    apply WireValue.map_congr
    intro id present
    exact expr (.var id) (by
      simp only [Chip.expressions, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (List.mem_map.mpr ⟨id, List.mem_flatMap.mpr ⟨wire, member, present⟩, rfl⟩)))))
  have output : chip.output.map (ArithExpr.denote a) = chip.output.map (ArithExpr.denote b) := by
    apply WireValue.map_congr
    intro p present
    exact expr p (by simp [Chip.expressions, present])
  have constraints : Satisfies chip.constraints a ↔ Satisfies chip.constraints b := by
    unfold Satisfies Scalar.Circuit.Satisfies
    apply forall_congr'
    intro p
    apply forall_congr'
    intro member
    exact congrArg (· = 0) (expr p (by simp [Chip.expressions, member])) |>.to_iff
  have sends (send : Send F) (member : send ∈ chip.sends) :
      send.enable.denote a = send.enable.denote b ∧ send.message a = send.message b := by
    have present (p : ArithExpr F)
        (h : p ∈ send.enable :: send.args.flatMap WireValue.words ++ send.result.words.map .var) :
        p ∈ chip.expressions := by
      simp only [Chip.expressions, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨send, member, h⟩))
    refine ⟨expr _ (present _ (by simp)), ?_⟩
    have args : send.args.map (WireValue.map (ArithExpr.denote a)) =
        send.args.map (WireValue.map (ArithExpr.denote b)) := by
      apply List.map_congr_left
      intro wire mem
      apply WireValue.map_congr
      intro p h
      exact expr p (present p (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨wire, mem, h⟩))))
    have result : send.result.map a = send.result.map b := by
      apply WireValue.map_congr
      intro id mem
      exact expr (.var id) (present _ (by simp [mem]))
    simp only [Send.message, args, result]
  have memory (lookup : MemoryLookup F) (member : lookup ∈ chip.memory) :
      lookup.Valid rom a ↔ lookup.Valid rom b := by
    have present (p : ArithExpr F) (h : p ∈ lookup.enable :: lookup.address :: lookup.value.words) :
        p ∈ chip.expressions := by
      simp only [Chip.expressions, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨lookup, member, h⟩)
    have value : lookup.value.map (ArithExpr.denote a) = lookup.value.map (ArithExpr.denote b) :=
      WireValue.map_congr _ (fun p h => expr p (present p (by simp [h])))
    simp only [MemoryLookup.Valid, expr lookup.enable (present _ (by simp)),
      expr lookup.address (present _ (by simp)), value]
  refine ⟨and_congr constraints (forall_congr' fun lookup => forall_congr' (memory lookup)), ?_, ?_⟩
  · simp only [Chip.conclusion, List.map_congr_left inputs, output]
  · apply List.filterMap_congr
    intro send member
    simp only [(sends send member).1, (sends send member).2]

omit [Field F] [DecidableEq F] in
theorem Chip.wellFormed_variables {chip : Chip F} (formed : chip.wellFormed = true) :
    ∀ id ∈ chip.variables, id < chip.numVars := by
  have bounded (p : ArithExpr F) (h : p.inBounds chip.numVars = true) :
      ∀ id ∈ Polynomial.vars p, id < chip.numVars := by
    induction p with
    | const value => simp [Polynomial.vars]
    | var id => simpa [Polynomial.vars, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using h
    | add a b ha hb | sub a b ha hb | mul a b ha hb =>
      simp only [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at h
      intro id member
      rcases List.mem_append.mp member with member | member
      · exact ha h.1 id member
      · exact hb h.2 id member
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at formed
  obtain ⟨⟨⟨⟨inputs, output⟩, constraints⟩, sends⟩, memory⟩ := formed
  intro id member
  obtain ⟨p, member, occurs⟩ := List.mem_flatMap.mp member
  apply bounded p ?_ id occurs
  simp only [Chip.expressions, List.mem_append] at member
  rcases member with (((member | member) | member) | member) | member
  · obtain ⟨v, present, equal⟩ := List.mem_map.mp member
    cases equal
    exact decide_eq_true (inputs v present)
  · exact output p member
  · exact constraints p member
  · obtain ⟨send, member, present⟩ := List.mem_flatMap.mp member
    have h := sends send member
    simp only [Send.inBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons, List.mem_append] at present
    rcases present with (rfl | present) | present
    · exact h.1.2
    · exact h.2 p present
    · obtain ⟨v, leaf, equal⟩ := List.mem_map.mp present
      cases equal
      exact decide_eq_true (h.1.1 v leaf)
  · obtain ⟨lookup, member, present⟩ := List.mem_flatMap.mp member
    have h := memory lookup member
    simp only [MemoryLookup.inBounds, Bool.and_eq_true, List.all_eq_true] at h
    simp only [List.mem_cons] at present
    rcases present with rfl | rfl | present
    · exact h.1.2
    · exact h.1.1
    · exact h.2 p present

theorem Chip.finiteAssignment {chip : Chip F} (formed : chip.wellFormed = true)
    (a : Var → F) (rom : WireROM F) :
    let row := Row.ofAssignment chip.name chip.numVars a
    (chip.ValidAssignment rom a ↔ chip.ValidAssignment rom row.assignment) ∧
      chip.conclusion a = chip.receive row ∧ chip.requirements a = chip.premises row := by
  apply chip.agree
  intro id member
  exact (Row.ofAssignment_agree _ _ _ id (chip.wellFormed_variables formed id member)).symm

theorem Chip.Equivalent.localRule {source target : Chip F} (same : source.Equivalent target)
    (sourceFormed : source.wellFormed = true) (targetFormed : target.wellFormed = true)
    (rom : WireROM F) (root : Message F) (premises : List (Message F)) :
    source.LocalRule rom root premises ↔ target.LocalRule rom root premises := by
  have forward {source target : Chip F} (refines : source.Refines target)
      (formed : target.wellFormed = true) :
      source.LocalRule rom root premises → target.LocalRule rom root premises := by
    rintro ⟨row, _, valid, rootEq, callsEq⟩
    obtain ⟨a, valid, root', calls'⟩ := refines rom row.assignment valid.2.2
    have finite := target.finiteAssignment formed a rom
    exact ⟨Row.ofAssignment target.name target.numVars a, rfl,
      ⟨formed, Row.ofAssignment_length _ _ _, finite.1.mp valid⟩,
      finite.2.1.symm.trans (root'.trans rootEq), finite.2.2.symm.trans (calls'.trans callsEq)⟩
  exact ⟨forward same.1 targetFormed, forward same.2 sourceFormed⟩

end Aiur.Circuit
