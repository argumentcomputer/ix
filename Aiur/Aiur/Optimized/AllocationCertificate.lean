import Aiur.Optimized.ControlCertificate
import Aiur.Optimized.LayoutWitness
import Aiur.Optimized.Index

namespace Aiur.Optimized.Allocation

variable {F : Type} [Field F] [DecidableEq F]

abbrev Site := Witness × Option ScopeId

def sites (scope : Option ScopeId) (ids : List Witness) : List Site := ids.map (·, scope)

/-- Interfaces and guard variables are live unconditionally; payload variables
are live only in their scope. Repeated occurrences are intentional. -/
def occurrences (chip : ScopedChip F) : List Site :=
  sites none (chip.inputs.flatMap WireValue.words ++ chip.output.words) ++
  chip.scopes.toList.flatMap (fun scope => sites none scope.activation.vars) ++
  chip.equations.toList.flatMap (fun equation => sites (some equation.scope) equation.polynomial.vars) ++
  chip.calls.toList.flatMap (fun call => sites (some call.scope)
    (call.args.flatMap (fun value => value.words.flatMap Polynomial.vars) ++ call.result.words)) ++
  chip.cells.toList.flatMap (fun cell => sites (some cell.scope)
    (cell.address.vars ++ cell.value.words.flatMap Polynomial.vars))

def Live (chip : ScopedChip F) (assignment : Witness → F) : Option ScopeId → Prop
  | none => True
  | some scope => (chip.activation scope).denote assignment ≠ 0

theorem relevant_site {chip : ScopedChip F} {assignment : Witness → F} {id : Witness}
    (relevant : chip.Relevant assignment id) :
    ∃ scope, (id, scope) ∈ occurrences chip ∧ Live chip assignment scope := by
  cases relevant with
  | input member present =>
      refine ⟨none, ?_, trivial⟩
      simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      aesop
  | output present =>
      refine ⟨none, ?_, trivial⟩
      simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      aesop
  | activation present =>
      rename_i scope
      cases found : chip.scopes[scope]? with
      | none => simp [ScopedChip.activation, found, Polynomial.vars] at present
      | some value =>
          simp only [ScopedChip.activation, found, Option.map_some, Option.getD_some] at present
          have member : value ∈ chip.scopes.toList := by simpa using Array.mem_of_getElem? found
          refine ⟨none, ?_, trivial⟩
          simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
          aesop
  | equation member active present =>
      rename_i equation
      refine ⟨some equation.scope, ?_, active⟩
      simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      aesop
  | callArgument member active valueMember polynomialMember used =>
      rename_i call value polynomial
      refine ⟨some call.scope, ?_, ?_⟩
      · simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
        aesop
      · change _ ≠ 0
        rw [active]
        exact one_ne_zero
  | callResult member active present =>
      rename_i call
      refine ⟨some call.scope, ?_, ?_⟩
      · simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
        aesop
      · change _ ≠ 0
        rw [active]
        exact one_ne_zero
  | address member active present =>
      rename_i cell
      refine ⟨some cell.scope, ?_, ?_⟩
      · simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
        aesop
      · change _ ≠ 0
        rw [active]
        exact one_ne_zero
  | payload member active polynomialMember used =>
      rename_i cell polynomial
      refine ⟨some cell.scope, ?_, ?_⟩
      · simp only [occurrences, sites, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
        aesop
      · change _ ≠ 0
        rw [active]
        exact one_ne_zero

def Owned (chip : ScopedChip F) (site : Site) : Prop :=
  match chip.roles[site.1]? with
  | none => False
  | some (.auxiliary owner) =>
    match site.2, chip.scopes[owner]? with
    | some scope, some declared =>
      match chip.scopes[scope]? with
      | some current => declared.path.isPrefixOf current.path = true
      | none => False
    | _, _ => False
  | some _ => True

instance (chip : ScopedChip F) (site : Site) : Decidable (Owned chip site) := by
  unfold Owned
  split <;> (try infer_instance)
  split <;> (try infer_instance)
  split <;> infer_instance

def usedIds (chip : ScopedChip F) : List Witness := ((occurrences chip).map Prod.fst).eraseDups

def Certificate (chip : ScopedChip F) (layout : ColumnLayout) : Prop :=
  Control.Certificate chip ∧
  (∀ site ∈ occurrences chip, layout.column site.1 < layout.occupants.size ∧ Owned chip site) ∧
  ∀ i ∈ usedIds chip, ∀ j ∈ usedIds chip,
    layout.column i = layout.column j → i = j ∨ chip.canShare i j = true

omit [Field F] [DecidableEq F] in
/-- Only witnesses mapped to the same physical column can interfere. The
indexed predicate checks exactly the original all-pairs condition. -/
theorem sharing_iff_indexed (chip : ScopedChip F) (layout : ColumnLayout)
    (ids : List Witness) :
    (∀ i ∈ ids, ∀ j ∈ ids,
      layout.column i = layout.column j → i = j ∨ chip.canShare i j = true) ↔
    (∀ i ∈ ids, ∀ j ∈ (Index.build layout.column ids).getD (layout.column i) [],
      i = j ∨ chip.canShare i j = true) := by
  simp only [Index.getD_build, List.mem_filter, beq_iff_eq]
  constructor
  · intro checked i hi j hj
    exact checked i hi j hj.1 hj.2.symm
  · intro checked i hi j hj same
    exact checked i hi j ⟨hj, same.symm⟩

instance (chip : ScopedChip F) (layout : ColumnLayout) : Decidable (Certificate chip layout) :=
  let sites := occurrences chip
  let ids := usedIds chip
  let buckets := Index.build layout.column ids
  decidable_of_iff
    (Control.Certificate chip ∧
      (∀ site ∈ sites, layout.column site.1 < layout.occupants.size ∧ Owned chip site) ∧
      ∀ i ∈ ids, ∀ j ∈ buckets.getD (layout.column i) [], i = j ∨ chip.canShare i j = true)
    (by unfold Certificate; rw [sharing_iff_indexed])

namespace Certificate

variable {chip : ScopedChip F} {layout : ColumnLayout}
  {rom : WireROM F} {assignment : Witness → F}

theorem bounded (checked : Certificate chip layout) {id : Witness} (relevant : chip.Relevant assignment id) :
    layout.column id < layout.occupants.size := by
  obtain ⟨scope, member, _⟩ := relevant_site relevant
  exact (checked.2.1 _ member).1

theorem activePath (checked : Certificate chip layout) (valid : chip.ValidAssignment rom assignment)
    {id owner : Witness} {scope : Scope F} (relevant : chip.Relevant assignment id)
    (role : chip.roles[id]? = some (.auxiliary owner)) (found : chip.scopes[owner]? = some scope) :
    Control.ActivePath chip assignment scope.path := by
  obtain ⟨site, member, active⟩ := relevant_site relevant
  have owned := (checked.2.1 _ member).2
  unfold Owned at owned
  simp only [role] at owned
  cases site with
  | none => contradiction
  | some useScope =>
    simp only [found] at owned
    cases useFound : chip.scopes[useScope]? with
    | none => simp [useFound] at owned
    | some current =>
      simp only [useFound] at owned
      have activePath := checked.1.activePath valid useFound active
      exact fun tag member => activePath tag ((List.isPrefixOf_iff_prefix.mp owned).subset member)

theorem compatible (checked : Certificate chip layout) (valid : chip.ValidAssignment rom assignment)
    {i j : Witness} (left : chip.Relevant assignment i) (right : chip.Relevant assignment j)
    (column : layout.column i = layout.column j) : assignment i = assignment j := by
  have present {id : Witness} (relevant : chip.Relevant assignment id) : id ∈ usedIds chip := by
    obtain ⟨site, member, _⟩ := relevant_site relevant
    simp only [usedIds, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨(id, site), member, rfl⟩
  rcases checked.2.2 i (present left) j (present right) column with same | shares
  · rw [same]
  · unfold ScopedChip.canShare at shares
    split at shares <;> (try contradiction)
    rename_i a b leftRole rightRole
    split at shares <;> (try contradiction)
    rename_i leftScope rightScope leftFound rightFound
    exact False.elim (checked.1.paths_exclusive valid shares
      (checked.activePath valid left leftRole leftFound) (checked.activePath valid right rightRole rightFound))

theorem complete (checked : Certificate chip layout) (rom : WireROM F) (assignment : Witness → F)
    (formed : (emitChip chip layout).wellFormed = true) (valid : chip.ValidAssignment rom assignment) :
    ∃ row : Circuit.Row F, row.chip = chip.name ∧ (emitChip chip layout).ValidRow rom row ∧
      (emitChip chip layout).receive row = chip.conclusion assignment ∧
      (emitChip chip layout).premises row = chip.premises assignment :=
  emitChip_complete chip layout rom assignment formed valid (fun _ => checked.bounded)
    (fun _ _ => checked.compatible valid)

end Certificate
end Aiur.Optimized.Allocation
