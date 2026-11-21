import Aiur.Optimized.AllocationCertificate
import Aiur.Optimized.ScopedPropagation
import Mathlib.Tactic.Ring

/-! Remove constraints that only define a private auxiliary. Scoped propagation
first substitutes the equalities of the selected arm. A failed earlier pattern
then often has a nonzero constant coefficient on one of its private witnesses.
Solving for that witness makes the entire equation existentially redundant.
No pattern splitting or change to the control tree is involved. -/

namespace Aiur.Optimized.ConstraintElimination

variable {F : Type} [Field F] [DecidableEq F]

/-- Isolate a variable with a constant coefficient, allowing arbitrary products
in the remainder. Unlike affine propagation, the remainder need not be affine. -/
def isolate (id : Witness) : Polynomial F → Option (F × Polynomial F)
  | .const c => some (0, .const c)
  | .var other => if other = id then some (1, .const 0) else some (0, .var other)
  | .add left right => do
      let (a, p) ← isolate id left
      let (b, q) ← isolate id right
      return (a + b, .add p q)
  | .sub left right => do
      let (a, p) ← isolate id left
      let (b, q) ← isolate id right
      return (a - b, .sub p q)
  | .mul left right => do
      let (a, p) ← isolate id left
      let (b, q) ← isolate id right
      if a = 0 then
        if b = 0 then return (0, .mul p q)
        else match p.simplify with
          | .const c => return (c * b, .mul p q)
          | _ => none
      else if b = 0 then
        match q.simplify with
        | .const c => return (a * c, .mul p q)
        | _ => none
      else none

theorem isolate_denote {id : Witness} {expr : Polynomial F} {coefficient : F}
    {rest : Polynomial F} (found : isolate id expr = some (coefficient, rest))
    (assignment : Witness → F) :
    expr.denote assignment = coefficient * assignment id + rest.denote assignment := by
  induction expr generalizing coefficient rest with
  | const c => cases found; simp [Scalar.Circuit.ArithExpr.denote]
  | var other =>
      simp only [isolate] at found
      split at found <;> cases found <;> simp_all [Scalar.Circuit.ArithExpr.denote]
  | add left right ihLeft ihRight | sub left right ihLeft ihRight =>
      simp only [isolate] at found
      cases hl : isolate id left with
      | none => simp [hl] at found
      | some l =>
          cases hr : isolate id right with
          | none => simp [hr] at found
          | some r =>
              simp [hl, hr] at found
              obtain ⟨rfl, rfl⟩ := found
              simp only [Scalar.Circuit.ArithExpr.denote, ihLeft hl, ihRight hr]
              ring
  | mul left right ihLeft ihRight =>
      simp only [isolate] at found
      cases hl : isolate id left with
      | none => simp [hl] at found
      | some l =>
          cases hr : isolate id right with
          | none => simp [hr] at found
          | some r =>
              rcases l with ⟨a, p⟩
              rcases r with ⟨b, q⟩
              simp only [hl, hr, bind, Option.bind] at found
              split at found
              · rename_i ha
                split at found
                · rename_i hb
                  cases found
                  simp [Scalar.Circuit.ArithExpr.denote, ihLeft hl, ihRight hr, ha, hb]
                · split at found <;> try contradiction
                  rename_i c hp
                  cases found
                  have constant := Polynomial.denote_simplify p assignment
                  rw [hp] at constant
                  simp only [Scalar.Circuit.ArithExpr.denote, ihLeft hl, ihRight hr, ha]
                  change c = Scalar.Circuit.ArithExpr.denote assignment p at constant
                  simp only [Circuit.ArithExpr.denote] at *
                  rw [← constant]
                  ring
              · split at found
                · rename_i hb
                  split at found <;> try contradiction
                  rename_i c hq
                  cases found
                  have constant := Polynomial.denote_simplify q assignment
                  rw [hq] at constant
                  simp only [Scalar.Circuit.ArithExpr.denote, ihLeft hl, ihRight hr, hb]
                  change c = Scalar.Circuit.ArithExpr.denote assignment q at constant
                  simp only [Circuit.ArithExpr.denote] at *
                  rw [← constant]
                  ring
                · contradiction

def erase (chip : ScopedChip F) (equation : Equation F) : ScopedChip F :=
  { chip with equations := chip.equations.filter fun other => decide (other ≠ equation) }

def usedVariables (chip : ScopedChip F) : List Witness :=
  (Allocation.occurrences chip).map Prod.fst

theorem relevant_mem {chip : ScopedChip F} {assignment : Witness → F} {id : Witness}
    (relevant : chip.Relevant assignment id) : id ∈ usedVariables chip := by
  obtain ⟨scope, member, _⟩ := Allocation.relevant_site relevant
  exact List.mem_map.mpr ⟨(id, scope), member, rfl⟩

structure Proposal (F : Type) where
  equation : Equation F
  id : Witness
  coefficient : F
  rest : Polynomial F

/-- Privacy is checked against every remaining equation, activation, interface,
call and memory lookup. No witness that affects an observable claim can escape. -/
def Proposal.Certificate (chip : ScopedChip F) (p : Proposal F) : Prop :=
  chip.roles[p.id]? = some (.auxiliary p.equation.scope) ∧
  p.id ∉ usedVariables (erase chip p.equation) ∧
  p.id ∉ p.rest.vars ∧
  isolate p.id p.equation.polynomial = some (p.coefficient, p.rest) ∧
  p.coefficient ≠ 0

instance (chip : ScopedChip F) (p : Proposal F) : Decidable (p.Certificate chip) := by
  unfold Proposal.Certificate
  infer_instance

theorem Proposal.equivalent {chip : ScopedChip F} {p : Proposal F}
    (checked : p.Certificate chip) : chip.Equivalent (erase chip p.equation) := by
  constructor
  · intro rom a valid
    refine ⟨a, ⟨?_, valid.2⟩, rfl, rfl⟩
    intro eq member
    have present : eq ∈ chip.equations.toList ∧ eq ≠ p.equation := by
      simpa [erase] using member
    exact valid.1 eq present.1
  · intro rom a valid
    let target := erase chip p.equation
    let b := Function.update a p.id (-p.rest.denote a / p.coefficient)
    have agree : ∀ id, target.Relevant a id → a id = b id := by
      intro id relevant
      have different : id ≠ p.id := by
        rintro rfl
        exact checked.2.1 (relevant_mem relevant)
      simp [b, Function.update_of_ne different]
    have kept : target.ValidAssignment rom b := target.validAssignment_agree agree valid
    have rest : p.rest.denote b = p.rest.denote a := by
      apply Polynomial.denote_congr
      intro id member
      have different : id ≠ p.id := by rintro rfl; exact checked.2.2.1 member
      simp [b, Function.update_of_ne different]
    have zero : p.equation.polynomial.denote b = 0 := by
      rw [isolate_denote checked.2.2.2.1, rest]
      simp [b, div_eq_mul_inv, mul_comm, checked.2.2.2.2]
    refine ⟨b, ⟨?_, kept.2⟩, (target.conclusion_agree agree).symm,
      (target.premises_agree agree).symm⟩
    intro eq member
    by_cases same : eq = p.equation
    · subst eq
      rw [zero, mul_zero]
    · apply kept.1 eq
      simpa [target, erase] using And.intro member same

/-- Candidate search is untrusted. Occurrence counts only avoid proposing
variables that the certificate would reject. Count once per equation. -/
def proposals (chip : ScopedChip F) : List (Proposal F) := Id.run do
  let protectedIds := (usedVariables { chip with equations := #[] }).foldl
    (fun set id => set.insert id) (∅ : Std.HashSet Witness)
  let mut counts : Std.HashMap Witness Nat := ∅
  for eq in chip.equations do
    for id in eq.polynomial.vars.eraseDups do
      counts := counts.insert id (counts.getD id 0 + 1)
  let mut result := []
  for eq in chip.equations do
    for id in eq.polynomial.vars.eraseDups do
      if counts.getD id 0 != 1 then continue
      if protectedIds.contains id then continue
      if chip.roles[id]? != some (.auxiliary eq.scope) then continue
      if let some (coefficient, rest) := isolate id eq.polynomial then
        if coefficient != 0 then
          result := ⟨eq, id, coefficient, rest⟩ :: result
          break
  return result.reverse

def applyProposals (source : ScopedChip F) : List (Proposal F) →
    Degree.Checked source → Degree.Checked source
  | [], current => current
  | p :: ps, current =>
      if checked : p.Certificate current.chip then
        applyProposals source ps {
          chip := erase current.chip p.equation
          equivalent := current.equivalent.trans (p.equivalent checked)
          name_eq := current.name_eq
          inputs_eq := current.inputs_eq
          output_eq := current.output_eq }
      else applyProposals source ps current

def replacement (id : Witness) (value : Polynomial F) (other : Witness) : Polynomial F :=
  if other = id then value else .var other

structure Reuse (F : Type) where
  equation : Equation F
  id : Witness
  value : Polynomial F
  retained : Equation F

/-- A repeated residual check may reuse a witness from an equation in exactly
the same scope. In particular, neither an inactive sibling nor the equation
being erased can justify the replacement. -/
def Reuse.Certificate (chip : ScopedChip F) (p : Reuse F) : Prop :=
  chip.roles[p.id]? = some (.auxiliary p.equation.scope) ∧
  p.id ∉ usedVariables (erase chip p.equation) ∧
  p.id ∉ p.value.vars ∧
  p.retained ∈ (erase chip p.equation).equations.toList ∧
  p.equation.scope = p.retained.scope ∧
  Polynomial.Identical (p.equation.polynomial.subst (replacement p.id p.value))
    p.retained.polynomial

instance (chip : ScopedChip F) (p : Reuse F) : Decidable (p.Certificate chip) := by
  letI : BEq (Equation F) := instBEqOfDecidableEq
  unfold Reuse.Certificate
  infer_instance

theorem Reuse.equivalent {chip : ScopedChip F} {p : Reuse F}
    (checked : p.Certificate chip) : chip.Equivalent (erase chip p.equation) := by
  constructor
  · intro rom a valid
    refine ⟨a, ⟨?_, valid.2⟩, rfl, rfl⟩
    intro eq member
    have present : eq ∈ chip.equations.toList ∧ eq ≠ p.equation := by
      simpa [erase] using member
    exact valid.1 eq present.1
  · intro rom a valid
    let target := erase chip p.equation
    let b := Function.update a p.id (p.value.denote a)
    have agree : ∀ id, target.Relevant a id → a id = b id := by
      intro id relevant
      have different : id ≠ p.id := by
        rintro rfl
        exact checked.2.1 (relevant_mem relevant)
      simp [b, Function.update_of_ne different]
    have kept : target.ValidAssignment rom b := target.validAssignment_agree agree valid
    have rewritten : p.equation.polynomial.denote b = p.retained.polynomial.denote a := by
      rw [← (Polynomial.alias_extension p.value p.equation.polynomial p.id checked.2.2.1 a).2]
      exact checked.2.2.2.2.2.denote a
    refine ⟨b, ⟨?_, kept.2⟩, (target.conclusion_agree agree).symm,
      (target.premises_agree agree).symm⟩
    intro eq member
    by_cases same : eq = p.equation
    · subst eq
      have activation := target.activation_agree agree p.equation.scope
      change (chip.activation p.equation.scope).denote a =
        (chip.activation p.equation.scope).denote b at activation
      rw [← activation, rewritten, checked.2.2.2.2.1]
      exact valid.1 p.retained checked.2.2.2.1
    · apply kept.1 eq
      simpa [target, erase] using And.intro member same

/-- Recognize identical residual equations modulo one private auxiliary name.
Templates only guide search: the certificate checks the actual substitution. -/
def reuseProposals (chip : ScopedChip F) : List (Reuse F) := Id.run do
  let protectedIds := (usedVariables { chip with equations := #[] }).foldl
    (fun set id => set.insert id) (∅ : Std.HashSet Witness)
  let mut counts : Std.HashMap Witness Nat := ∅
  for eq in chip.equations do
    for id in eq.polynomial.vars.eraseDups do
      counts := counts.insert id (counts.getD id 0 + 1)
  let mut templates : Std.HashMap Nat (List (Polynomial F × Equation F × Witness)) := ∅
  let mut result := []
  for eq in chip.equations do
    for id in eq.polynomial.vars.eraseDups do
      if counts.getD id 0 != 1 || protectedIds.contains id then continue
      if chip.roles[id]? != some (.auxiliary eq.scope) then continue
      let template := (eq.polynomial.subst (replacement id (.var chip.roles.size))).normalForm
      let key := EquationIndex.key (eq.scope, template)
      let bucket := templates.getD key []
      if let some (_, retained, witness) := bucket.find? fun (other, retained, _) =>
          retained.scope == eq.scope && other == template then
        result := ⟨eq, id, .var witness, retained⟩ :: result
      else
        templates := templates.insert key ((template, eq, id) :: bucket)
      break
  return result.reverse

def applyReuse (source : ScopedChip F) : List (Reuse F) →
    Degree.Checked source → Degree.Checked source
  | [], current => current
  | p :: ps, current =>
      if checked : p.Certificate current.chip then
        applyReuse source ps {
          chip := erase current.chip p.equation
          equivalent := current.equivalent.trans (p.equivalent checked)
          name_eq := current.name_eq
          inputs_eq := current.inputs_eq
          output_eq := current.output_eq }
      else applyReuse source ps current

def run (chip : ScopedChip F) : Degree.Checked chip :=
  let privateEquations := applyProposals chip (proposals chip) (ScopedPropagation.identity chip)
  applyReuse chip (reuseProposals privateEquations.chip) privateEquations

end Aiur.Optimized.ConstraintElimination
