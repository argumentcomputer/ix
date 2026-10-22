import Aiur.Optimized.ControlCertificate
import Aiur.Optimized.AffineEquation

namespace Aiur.Optimized.ScopedPropagation

variable {F : Type} [Field F] [DecidableEq F]

/-- Choose a simple affine equality. Search is untrusted: `fact?` checks the
actual equation before constructing a usable fact. -/
def definition? (p : Polynomial F) : Option (Witness × Polynomial F) := Id.run do
  for id in p.vars.eraseDups do
    -- Structural failure is independent of the variable (`isolate_isSome_eq`).
    -- Do not simplify the same nonlinear equation again for every variable.
    let some (coefficient, rest) := p.isolate id | return none
    if coefficient ≠ 0 then
      let value := Polynomial.simplify (.mul (.const (-coefficient⁻¹)) rest)
      if !value.vars.contains id && value.degree ≤ 1 then return some (id, value)
  return none

/-- A scope can use its own facts, root facts, and facts from a branch on its
path. The path is trusted only after checking the actual control equations. -/
def available (chip : ScopedChip F) (owner current : ScopeId) : Bool :=
  owner == 0 || owner == current ||
    match chip.scopes[current]? with
    | none => false
    | some scope => scope.path.any fun tag =>
        ((chip.choices[tag.1]?).bind fun choice => choice.children[tag.2]?) == some owner

/-- Control equations and the equalities used as facts remain unchanged. -/
def keep (chip : ScopedChip F) (eq : Equation F) : Bool :=
  eq.scope == 0 || match definition? eq.polynomial with
    | none => false
    | some (id, _) => !chip.equations.any fun earlier =>
        earlier.scope < eq.scope && available chip earlier.scope eq.scope &&
          (definition? earlier.polynomial).any (fun other => other.1 == id)

/-- Solve each equation once before checking which scope owns its definition. -/
def definitions (chip : ScopedChip F) : Array (Equation F × Option (Witness × Polynomial F)) :=
  chip.equations.map fun eq => (eq, definition? eq.polynomial)

@[noinline] def keepPrepared (chip : ScopedChip F)
    (known : Array (Equation F × Option (Witness × Polynomial F))) (eq : Equation F) : Bool :=
  eq.scope == 0 || match definition? eq.polynomial with
    | none => false
    | some (id, _) => !known.any fun (earlier, definition) =>
        earlier.scope < eq.scope && available chip earlier.scope eq.scope &&
          definition.any (fun other => other.1 == id)

@[simp] theorem keepPrepared_eq (chip : ScopedChip F) (eq : Equation F) :
    keepPrepared chip (definitions chip) eq = keep chip eq := by
  simp [keepPrepared, definitions, keep, Array.any_map, Function.comp_def]

def anchors (chip : ScopedChip F) : ScopedChip F :=
  let known := definitions chip
  { chip with equations := chip.equations.filter (keepPrepared chip known), cells := #[] }

structure Fact (basis : ScopedChip F) where
  scope : ScopeId
  id : Witness
  value : Polynomial F
  sound : ∀ rom a, basis.ValidAssignment rom a →
    (basis.activation scope).denote a ≠ 0 → a id = value.denote a

def fact? (basis : ScopedChip F) (eq : Equation F) (member : eq ∈ basis.equations.toList) :
    Option (Fact basis) := do
  let (id, value) ← definition? eq.polynomial
  if checked : eq.polynomial.solution? id = some value then
    return ⟨eq.scope, id, value, fun _ a valid active =>
      Polynomial.solution?_sound checked a ((mul_eq_zero.mp (valid.1 eq member)).resolve_left active)⟩
  else none

def facts (basis : ScopedChip F) : List (Fact basis) :=
  basis.equations.toList.attach.filterMap fun eq => fact? basis eq.val eq.property

theorem available_active {chip : ScopedChip F} (checked : Control.Certificate chip)
    {rom : WireROM F} {a : Witness → F} (valid : chip.ValidAssignment rom a)
    {owner current : ScopeId} (found : available chip owner current = true)
    (active : (chip.activation current).denote a ≠ 0) : (chip.activation owner).denote a ≠ 0 := by
  simp only [available, Bool.or_eq_true, beq_iff_eq] at found
  rcases found with (root | same) | inherited
  · subst owner
    rw [checked.1.denote]
    exact one_ne_zero
  · simpa [same] using active
  · cases scopeFound : chip.scopes[current]? with
    | none => simp [scopeFound] at inherited
    | some scope =>
        simp only [scopeFound] at inherited
        obtain ⟨tag, member, selected⟩ := List.any_eq_true.mp inherited
        have selected := beq_iff_eq.mp selected
        obtain ⟨choice, choiceFound, child, childFound, childActive⟩ :=
          checked.activePath valid scopeFound active tag member
        simp only [choiceFound, Option.bind_some, childFound, Option.some.injEq] at selected
        simpa [selected] using childActive

def replacement {basis : ScopedChip F} (known : List (Fact basis)) (scope : ScopeId)
    (id : Witness) : Polynomial F :=
  match known.find? (fun fact => fact.id == id && available basis fact.scope scope) with
  | none => .var id
  | some fact => fact.value

theorem replacement_denote {basis : ScopedChip F} (checked : Control.Certificate basis)
    (known : List (Fact basis)) {rom : WireROM F} {a : Witness → F}
    (valid : basis.ValidAssignment rom a) {scope : ScopeId}
    (active : (basis.activation scope).denote a ≠ 0) (id : Witness) :
    (replacement known scope id).denote a = a id := by
  unfold replacement
  cases found : known.find? _ with
  | none => rfl
  | some fact =>
      have selected := List.find?_some found
      obtain ⟨same, available⟩ := Bool.and_eq_true_iff.mp selected
      have same : fact.id = id := beq_iff_eq.mp same
      exact same ▸ (fact.sound rom a valid (available_active checked valid available active)).symm

def expression {basis : ScopedChip F} (known : List (Fact basis)) (scope : ScopeId)
    (p : Polynomial F) : Polynomial F := (p.subst (replacement known scope)).simplify

theorem expression_denote {basis : ScopedChip F} (checked : Control.Certificate basis)
    (known : List (Fact basis)) {rom : WireROM F} {a : Witness → F}
    (valid : basis.ValidAssignment rom a) {scope : ScopeId}
    (active : (basis.activation scope).denote a ≠ 0) (p : Polynomial F) :
    (expression known scope p).denote a = p.denote a := by
  simp only [expression, Polynomial.denote_simplify, Polynomial.denote_subst]
  exact Polynomial.denote_congr p (fun id _ => replacement_denote checked known valid active id)

def transform (chip : ScopedChip F) : ScopedChip F :=
  let known := definitions chip
  let expr := expression (facts (anchors chip))
  { chip with
    equations := chip.equations.map fun eq =>
      { eq with polynomial := if keepPrepared chip known eq then eq.polynomial else expr eq.scope eq.polynomial }
    calls := chip.calls.map fun call =>
      { call with args := call.args.map (WireValue.map (expr call.scope)) }
    cells := chip.cells.map fun cell =>
      { cell with address := expr cell.scope cell.address, value := cell.value.map (expr cell.scope) } }

@[simp] theorem anchors_activation (chip : ScopedChip F) (scope : ScopeId) :
    (anchors chip).activation scope = chip.activation scope := rfl

@[simp] theorem transform_activation (chip : ScopedChip F) (scope : ScopeId) :
    (transform chip).activation scope = chip.activation scope := rfl

theorem anchors_of_source {chip : ScopedChip F} {rom : WireROM F} {a : Witness → F}
    (valid : chip.ValidAssignment rom a) : (anchors chip).ValidAssignment rom a := by
  refine ⟨?_, by simp [anchors]⟩
  intro eq member
  have member : eq ∈ chip.equations.toList ∧ keep chip eq = true := by
    simpa only [anchors, Array.toList_filter, List.mem_filter, keepPrepared_eq] using member
  exact valid.1 eq member.1

theorem anchors_of_target {chip : ScopedChip F} {rom : WireROM F} {a : Witness → F}
    (valid : (transform chip).ValidAssignment rom a) : (anchors chip).ValidAssignment rom a := by
  refine ⟨?_, by simp [anchors]⟩
  intro eq member
  have member : eq ∈ chip.equations.toList ∧ keep chip eq = true := by
    simpa only [anchors, Array.toList_filter, List.mem_filter, keepPrepared_eq] using member
  have present : eq ∈ (transform chip).equations.toList := by
    simp only [transform, Array.toList_map, List.mem_map, keepPrepared_eq]
    exact ⟨eq, member.1, by simp [member.2]⟩
  exact valid.1 eq present

theorem valid_iff {chip : ScopedChip F} (checked : Control.Certificate (anchors chip))
    {rom : WireROM F} {a : Witness → F} (valid : (anchors chip).ValidAssignment rom a) :
    (transform chip).ValidAssignment rom a ↔ chip.ValidAssignment rom a := by
  have expr {scope : ScopeId} (active : (chip.activation scope).denote a ≠ 0) (p : Polynomial F) :=
    expression_denote checked (facts (anchors chip)) valid active p
  unfold ScopedChip.ValidAssignment
  simp only [transform, Array.toList_map, List.forall_mem_map, keepPrepared_eq]
  apply and_congr
  · apply forall_congr'
    intro eq
    apply forall_congr'
    intro member
    change (chip.activation eq.scope).denote a *
        (if keep chip eq then eq.polynomial else
          expression (facts (anchors chip)) eq.scope eq.polynomial).denote a = 0 ↔ _
    by_cases active : (chip.activation eq.scope).denote a = 0
    · simp [active]
    · split
      · rfl
      · rw [expr active]
  · apply forall_congr'
    intro cell
    apply forall_congr'
    intro member
    apply imp_congr_right
    intro active
    change (chip.activation cell.scope).denote a = 1 at active
    have nonzero : (chip.activation cell.scope).denote a ≠ 0 := by rw [active]; exact one_ne_zero
    simp only [WireValue.map_map, Function.comp_def, expr nonzero]

theorem premises_eq {chip : ScopedChip F} (checked : Control.Certificate (anchors chip))
    {rom : WireROM F} {a : Witness → F} (valid : (anchors chip).ValidAssignment rom a) :
    (transform chip).premises a = chip.premises a := by
  simp only [ScopedChip.premises, transform, Array.toList_map, List.filterMap_map]
  apply List.filterMap_congr
  intro call member
  change (if (chip.activation call.scope).denote a = 1 then _ else _) = _
  split
  · rename_i active
    have nonzero : (chip.activation call.scope).denote a ≠ 0 := by rw [active]; exact one_ne_zero
    have args : call.args.map (WireValue.map (fun p =>
        (expression (facts (anchors chip)) call.scope p).denote a)) =
        call.args.map (WireValue.map (Circuit.ArithExpr.denote a)) := by
      apply List.map_congr_left
      intro wire _
      exact WireValue.map_congr wire (fun p _ => expression_denote checked _ valid nonzero p)
    simp only [Call.message, List.map_map, WireValue.map_map, Function.comp_def, args]
  · rfl

theorem equivalent (chip : ScopedChip F) (checked : Control.Certificate (anchors chip)) :
    chip.Equivalent (transform chip) := by
  constructor
  · intro rom a valid
    have basis := anchors_of_source valid
    exact ⟨a, (valid_iff checked basis).mpr valid, rfl, premises_eq checked basis⟩
  · intro rom a valid
    have basis := anchors_of_target valid
    exact ⟨a, (valid_iff checked basis).mp valid, rfl, (premises_eq checked basis).symm⟩

def identity (chip : ScopedChip F) : Degree.Checked chip :=
  ⟨chip, ⟨fun _ a valid => ⟨a, valid, rfl, rfl⟩,
    fun _ a valid => ⟨a, valid, rfl, rfl⟩⟩, rfl, rfl, rfl⟩

def run (chip : ScopedChip F) : Except String (Degree.Checked chip) := do
  if checked : Control.Certificate (anchors chip) then
    return ⟨transform chip, equivalent chip checked, rfl, rfl, rfl⟩
  else throw s!"invalid scoped-propagation control certificate in {chip.name}"

end Aiur.Optimized.ScopedPropagation
