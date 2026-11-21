import Aiur.Optimized.PhysicalSemantics
import Aiur.Optimized.PolynomialIdentity
import Aiur.Optimized.AffineEquation
import Aiur.Optimized.LinearNormalization

namespace Aiur.Optimized.Propagation

variable {F : Type} [Field F] [DecidableEq F]

/-- Inputs and unknown call results remain witnesses. Provided outputs and ROM
payloads may instead contain expressions. -/
def fixed (chip : Circuit.Chip F) : List Witness :=
  chip.inputs.flatMap WireValue.words ++ chip.sends.flatMap (fun send => send.result.words)

def rewrite (chip : Circuit.Chip F) (column : Witness → Witness)
    (replace : Witness → Polynomial F) : Circuit.Chip F :=
  -- Substitution may duplicate affine expressions exponentially. Collect their
  -- coefficients before the next elimination, including under nonlinear nodes.
  let expr := fun p : Polynomial F => (p.subst replace).simplify.normalizeLinear.simplify
  { chip with
    inputs := chip.inputs.map (WireValue.map column)
    output := chip.output.map expr
    constraints := chip.constraints.filterMap fun p =>
      let p := expr p
      if p == .const 0 then none else some p
    sends := chip.sends.map fun send => { send with
      args := send.args.map (WireValue.map expr)
      result := send.result.map column
      enable := expr send.enable }
    memory := chip.memory.map fun lookup => { lookup with
      address := expr lookup.address, value := lookup.value.map expr, enable := expr lookup.enable } }

theorem rewrite_valid (chip : Circuit.Chip F) (column : Witness → Witness)
    (replace : Witness → Polynomial F) (rom : WireROM F) (a : Witness → F) :
    (rewrite chip column replace).ValidAssignment rom a ↔
      chip.ValidAssignment rom (fun id => (replace id).denote a) := by
  have constraints : Circuit.Satisfies (rewrite chip column replace).constraints a ↔
      Circuit.Satisfies chip.constraints (fun id => (replace id).denote a) := by
    constructor
    · intro valid p member
      let result := (Polynomial.subst replace p).simplify.normalizeLinear.simplify
      have equal : result.denote a = p.denote (fun id => (replace id).denote a) := by
        simp [result]
      by_cases zero : (result == .const 0) = true
      · rw [← equal, (Polynomial.beq_eq _ _).mp zero]
        rfl
      · have found : result ∈ (rewrite chip column replace).constraints :=
          List.mem_filterMap.mpr ⟨p, member, by simp [zero, result]⟩
        exact equal ▸ valid result found
    · intro valid p member
      obtain ⟨old, oldMember, emitted⟩ := List.mem_filterMap.mp member
      dsimp only at emitted
      split at emitted
      · contradiction
      · cases emitted
        simpa only [Polynomial.denote_normalizeLinear, Polynomial.denote_simplify,
          Polynomial.denote_subst] using valid old oldMember
  unfold Circuit.Chip.ValidAssignment
  rw [constraints]
  simp only [rewrite, List.forall_mem_map, Circuit.MemoryLookup.Valid,
    Polynomial.denote_normalizeLinear, Polynomial.denote_simplify, Polynomial.denote_subst,
    WireValue.map_map, Function.comp_def]

theorem rewrite_claims (chip : Circuit.Chip F) (column : Witness → Witness)
    (replace : Witness → Polynomial F)
    (fixed : ∀ id ∈ fixed chip, replace id = .var (column id)) (a : Witness → F) :
    (rewrite chip column replace).conclusion a = chip.conclusion (fun id => (replace id).denote a) ∧
      (rewrite chip column replace).requirements a = chip.requirements (fun id => (replace id).denote a) := by
  have input (wire : WireValue Witness) (member : wire ∈ chip.inputs) :
      wire.map (a ∘ column) = wire.map (fun id => (replace id).denote a) := by
    apply WireValue.map_congr
    intro id present
    rw [fixed id (List.mem_append_left _ (List.mem_flatMap.mpr ⟨wire, member, present⟩))]
    rfl
  constructor
  · simp only [rewrite, Circuit.Chip.conclusion, List.map_map, WireValue.map_map,
      Function.comp_def, Polynomial.denote_normalizeLinear, Polynomial.denote_simplify, Polynomial.denote_subst]
    congr 1
    exact List.map_congr_left input
  · simp only [rewrite, Circuit.Chip.requirements, List.filterMap_map]
    apply List.filterMap_congr
    intro send member
    simp only [Function.comp_def, Polynomial.denote_normalizeLinear, Polynomial.denote_simplify, Polynomial.denote_subst]
    split
    · congr 1
      have result : send.result.map (a ∘ column) = send.result.map (fun id => (replace id).denote a) := by
        apply WireValue.map_congr
        intro id present
        rw [fixed id (List.mem_append_right _ (List.mem_flatMap.mpr ⟨send, member, present⟩))]
        rfl
      simp only [Circuit.Send.message, List.map_map, WireValue.map_map, Function.comp_def,
        Polynomial.denote_normalizeLinear, Polynomial.denote_simplify, Polynomial.denote_subst]
      exact congrArg (Circuit.Message.mk send.channel _) result
    · rfl

structure Candidate (F : Type) where
  id : Witness
  value : Polynomial F

/-- Only actual unconditional equations authorize substitution. In particular,
a guarded equality is not a definition of its value outside the branch. -/
def Candidate.Certificate (chip : Circuit.Chip F) (candidate : Candidate F) : Prop :=
  candidate.id ∉ fixed chip ∧ candidate.id ∉ candidate.value.vars ∧ candidate.value.degree ≤ 1 ∧
    ∃ equation ∈ chip.constraints,
      Polynomial.Identical equation (.sub (.var candidate.id) candidate.value) ∨
      Polynomial.Identical equation (.sub candidate.value (.var candidate.id)) ∨
      Polynomial.solution? equation candidate.id = some candidate.value

instance (chip : Circuit.Chip F) (candidate : Candidate F) : Decidable (candidate.Certificate chip) := by
  unfold Candidate.Certificate
  infer_instance

def Candidate.replace (candidate : Candidate F) (id : Witness) : Polynomial F :=
  if id = candidate.id then candidate.value else .var id

theorem Candidate.equivalent {chip : Circuit.Chip F} {candidate : Candidate F}
    (checked : candidate.Certificate chip) :
    chip.Equivalent (rewrite chip (fun i => i) candidate.replace) := by
  have fixed : ∀ i ∈ fixed chip, candidate.replace i = .var i := by
    intro i member
    have different : i ≠ candidate.id := by rintro rfl; exact checked.1 member
    simp [Candidate.replace, different]
  constructor
  · intro rom a valid
    obtain ⟨polynomial, member, justified⟩ := checked.2.2.2
    have equation : Circuit.ArithExpr.denote a polynomial = 0 := valid.1 polynomial member
    have equal : a candidate.id = candidate.value.denote a := by
      rcases justified with same | same | solved
      · rw [same.denote] at equation
        exact sub_eq_zero.mp equation
      · rw [same.denote] at equation
        exact (sub_eq_zero.mp equation).symm
      · exact Polynomial.solution?_sound solved a equation
    have unchanged : (fun i => (candidate.replace i).denote a) = a := by
      funext i
      by_cases h : i = candidate.id <;> simp [Candidate.replace, h, equal, Scalar.Circuit.ArithExpr.denote]
    refine ⟨a, ?_, ?_, ?_⟩
    · rw [rewrite_valid, unchanged]; exact valid
    · rw [(rewrite_claims chip (fun i => i) candidate.replace fixed a).1, unchanged]
    · rw [(rewrite_claims chip (fun i => i) candidate.replace fixed a).2, unchanged]
  · intro rom a valid
    exact ⟨_, (rewrite_valid chip (fun i => i) candidate.replace rom a).mp valid,
      (rewrite_claims chip (fun i => i) candidate.replace fixed a).1.symm,
      (rewrite_claims chip (fun i => i) candidate.replace fixed a).2.symm⟩

/-- Retain the equation found by the untrusted search so validation does not
repeat an existential search through the entire constraint list. -/
structure Proposal (F : Type) where
  candidate : Candidate F
  equationIndex : Nat

def proposal? (chip : Circuit.Chip F) : Option (Proposal F) := Id.run do
  let fixedIds := (fixed chip).foldl (fun set id => set.insert id) (∅ : Std.HashSet Witness)
  let allowed := fun id value =>
    if !fixedIds.contains id && !(Polynomial.vars value).contains id && value.degree ≤ 1
      then some (Candidate.mk id value) else none
  for (equation, index) in chip.constraints.zipIdx do
    let found := match equation with
      | .sub (.var id) value => (allowed id value).orElse fun _ =>
          match value with | .var other => allowed other (.var id) | _ => none
      | .sub value (.var id) => allowed id value
      | .var id => allowed id (.const 0)
      | _ => none
    if let some candidate := found then return some ⟨candidate, index⟩
    for id in (Polynomial.vars equation).eraseDups do
      if fixedIds.contains id then continue
      -- Failure here is structural, not a zero coefficient for this variable:
      -- `isolate_isSome_eq` shows that trying other variables cannot help.
      let some (coefficient, rest) := Polynomial.isolate id equation | break
      if coefficient ≠ 0 then
        let value := Polynomial.simplify (.mul (.const (-coefficient⁻¹)) rest)
        if let some candidate := allowed id value then return some ⟨candidate, index⟩
  return none

def candidate? (chip : Circuit.Chip F) : Option (Candidate F) :=
  (proposal? chip).map (·.candidate)

/-- The index is only advice: bounds, the actual equation, fixed columns,
occurrence and degree are checked before recovering the original certificate. -/
def Proposal.check (proposal : Proposal F) (chip : Circuit.Chip F) :
    Option {candidate : Candidate F // candidate.Certificate chip} :=
  let candidate := proposal.candidate
  match selected : chip.constraints[proposal.equationIndex]? with
  | none => none
  | some equation =>
      if checked : candidate.id ∉ fixed chip ∧ candidate.id ∉ candidate.value.vars ∧
          candidate.value.degree ≤ 1 ∧
          (Polynomial.Identical equation (.sub (.var candidate.id) candidate.value) ∨
           Polynomial.Identical equation (.sub candidate.value (.var candidate.id)) ∨
           Polynomial.solution? equation candidate.id = some candidate.value) then
        some ⟨candidate, checked.1, checked.2.1, checked.2.2.1,
          equation, List.mem_of_getElem? selected, checked.2.2.2⟩
      else none

structure Checked (source : Circuit.Chip F) where
  chip : Circuit.Chip F
  equivalent : source.Equivalent chip
  name_eq : chip.name = source.name
  inputTypes : chip.inputs.map WireValue.type = source.inputs.map WireValue.type
  outputType : chip.output.type = source.output.type

def Checked.identity (chip : Circuit.Chip F) : Checked chip :=
  ⟨chip, .refl chip, rfl, rfl, rfl⟩

/-- The fuel is an optimization budget, not an evaluation bound. Exhausting it
retains a proved equivalent chip; each successful step removes a variable. -/
def propagate (source : Circuit.Chip F) : Nat → (current : Checked source) → Checked source
  | 0, current => current
  | fuel + 1, current =>
    match (proposal? current.chip).bind (fun proposal => proposal.check current.chip) with
    | none => current
    | some ⟨candidate, checked⟩ =>
        propagate source fuel {
          chip := rewrite current.chip id candidate.replace
          equivalent := current.equivalent.trans (Candidate.equivalent checked)
          name_eq := current.name_eq
          inputTypes := by simpa [rewrite, List.map_map, Function.comp_def] using current.inputTypes
          outputType := current.outputType }

def compact (chip : Circuit.Chip F) (columns : List Witness) : Circuit.Chip F :=
  { rewrite chip columns.idxOf (fun id => .var (columns.idxOf id)) with numVars := columns.length }

theorem compact_equivalent (chip : Circuit.Chip F) (columns : List Witness)
    (inverse : ∀ id ∈ chip.variables, columns[columns.idxOf id]? = some id) :
    chip.Equivalent (compact chip columns) := by
  let replace : Witness → Polynomial F := fun id => Polynomial.var (columns.idxOf id)
  have claims := rewrite_claims chip columns.idxOf replace (fun _ _ => rfl)
  constructor
  · intro rom a valid
    let b : Witness → F := fun column => a (columns[column]?.getD 0)
    have agree : ∀ id ∈ chip.variables, (replace id).denote b = a id := by
      intro id member
      simp [replace, Scalar.Circuit.ArithExpr.denote, b, inverse id member]
    have same := chip.agree agree rom
    refine ⟨b, (rewrite_valid chip columns.idxOf replace rom b).mpr (same.1.mpr valid), ?_, ?_⟩
    · exact (claims b).1.trans same.2.1
    · exact (claims b).2.trans same.2.2
  · intro rom a valid
    exact ⟨_, (rewrite_valid chip columns.idxOf replace rom a).mp valid,
      (claims a).1.symm, (claims a).2.symm⟩

/-- Renumber surviving columns densely after propagation, including columns
made irrelevant by constant-folded equations. -/
def run (source : Circuit.Chip F) : Except String (Checked source) := do
  let current := propagate source source.numVars (.identity source)
  let used := current.chip.variables
  let columns := (List.range current.chip.numVars).filter (used.contains ·)
  if inverse : ∀ id ∈ current.chip.variables, columns[columns.idxOf id]? = some id then
    return {
      chip := compact current.chip columns
      equivalent := current.equivalent.trans (compact_equivalent _ _ inverse)
      name_eq := current.name_eq
      inputTypes := by simpa [compact, rewrite, List.map_map, Function.comp_def] using current.inputTypes
      outputType := current.outputType }
  else throw s!"invalid column compaction in {source.name}"

end Aiur.Optimized.Propagation
