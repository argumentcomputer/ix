import Aiur.Optimized.EndToEnd
import Aiur.Circuit.MemoRows

/-!
# The memo checker over grouped, activated circuits

`Circuit.System.checkMemo` checks rows of the ungrouped circuits. The prover
commits to the grouped, activated circuits of a `Grouping.Plan`: every
ungrouped chip gains a row-activation selector (`Activation.compile`), and
grouped chips share columns behind member selectors (`Grouping.Layout`).
`Plan.checkMemo` checks exactly those rows:

* a row names its physical circuit;
* an ungrouped row must satisfy the activated chip; with selector `1` it
  provides the chip's conclusion and demands its enabled premises;
* a grouped row must have the layout's width and satisfy its constraints; with
  activation `1` the selected member's view supplies the conclusion and
  premises, and the row must be valid (`Layout.ValidRow`, including memory);
* a row whose selector or activation is `0` is padding: it contributes no
  message and must have weight `0`, as `(1 - activation) · m = 0` forces;
* provide weights are arbitrary integers and premises have weight one, as in
  `System.checkMemo`.

`Plan.checkMemo_graph` turns acceptance into a memo graph over the source system
with at most one row node per row. Padding silence (`Activation.zero_requirements`,
`Checked.padding_sound`) is what makes ignoring padding rows faithful to the
deployed circuits; soundness does not need it.
-/

namespace Aiur.Optimized.Grouping

open Circuit

variable {F : Type} [Field F] [DecidableEq F]

instance (constraints : List (Polynomial F)) (a : Nat → F) :
    Decidable (Satisfies constraints a) := by
  unfold Satisfies Scalar.Circuit.Satisfies
  infer_instance

instance (g : Layout F) (rom : WireROM F) (a : Nat → F) : Decidable (g.ValidRow rom a) :=
  decidable_of_iff (Satisfies g.constraints a ∧ g.activation.denote a = 1 ∧
      ∀ m ∈ g.members, a m.selector = 1 → ∀ cell ∈ ((g.view m).denote a).cells, cell.1 = 1 →
        ∃ entry ∈ rom.entries, entry = (cell.2.1, cell.2.2)) (by
    simp only [Layout.ValidRow, Payload.MemoryValid, exists_eq_right])

/-- A grouped row: padding (`none`) when its activation is `0`, otherwise the
selected member's conclusion and premises. -/
def Layout.inspectRow (g : Layout F) (rom : WireROM F) (row : Row F) :
    Except String (Option (RuleClaims (Message F))) :=
  if row.values.length = g.width ∧ Satisfies g.constraints row.assignment then
    if g.activation.denote row.assignment = 0 then .ok none
    else
      match g.members.find? (fun m => decide (row.assignment m.selector = 1)) with
      | none => .error s!"group {g.name}: no selected member"
      | some m =>
          if g.ValidRow rom row.assignment then
            .ok (some (((g.view m).denote row.assignment).root,
              ((g.view m).denote row.assignment).requirements))
          else .error s!"group {g.name}: invalid active row"
  else .error s!"group {g.name}: wrong width or failed constraint"

theorem Layout.inspectRow_some {g : Layout F} {rom : WireROM F} {row : Row F}
    {claims : RuleClaims (Message F)} (inspected : g.inspectRow rom row = .ok (some claims)) :
    ∃ m ∈ g.members, row.values.length = g.width ∧ g.ValidRow rom row.assignment ∧
      row.assignment m.selector = 1 ∧
      claims = (((g.view m).denote row.assignment).root,
        ((g.view m).denote row.assignment).requirements) := by
  unfold Layout.inspectRow at inspected
  by_cases shape : row.values.length = g.width ∧ Satisfies g.constraints row.assignment
  · simp only [shape, and_self, ↓reduceIte] at inspected
    by_cases off : g.activation.denote row.assignment = 0
    · simp [off] at inspected
    · simp only [off, ↓reduceIte] at inspected
      cases found : g.members.find? (fun m => decide (row.assignment m.selector = 1)) with
      | none => simp [found] at inspected
      | some m =>
          simp only [found] at inspected
          by_cases validRow : g.ValidRow rom row.assignment
          · simp only [validRow, ↓reduceIte, Except.ok.injEq, Option.some.injEq] at inspected
            refine ⟨m, List.mem_of_find?_eq_some found, shape.1, validRow, ?_, inspected.symm⟩
            simpa using List.find?_some found
          · simp [validRow] at inspected
  · simp [shape] at inspected

/-- The weighted rules of the active rows. -/
def activeRules (weighed : List (Option α)) : List α := weighed.filterMap fun result => result

@[simp] theorem activeRules_nil : activeRules ([] : List (Option α)) = [] := rfl
@[simp] theorem activeRules_none (rest : List (Option α)) : activeRules (none :: rest) = activeRules rest := rfl
@[simp] theorem activeRules_some (x : α) (rest : List (Option α)) :
    activeRules (some x :: rest) = x :: activeRules rest := rfl

variable {source : Circuit.System F} {id : String → Except String Nat}

/-- A physical row of a plan, named by its circuit. -/
def Plan.inspectRow (plan : Plan source id) (rom : WireROM F) (row : Row F) :
    Except String (Option (RuleClaims (Message F))) :=
  match plan.singles.find? (·.name == row.chip) with
  | some chip =>
      match (Activation.compile chip).checkRow rom row with
      | .error error => .error (reprStr error)
      | .ok claims => .ok (if row.assignment chip.numVars = 1 then some claims else none)
  | none =>
      match plan.groups.find? (·.checked.layout.name == row.chip) with
      | some packed => packed.checked.layout.inspectRow rom row
      | none => .error s!"unknown physical circuit {row.chip}"

/-- An active row is an instance of the plan's activated local rule. -/
theorem Plan.inspectRow_some {plan : Plan source id} {rom : WireROM F} {row : Row F}
    {claims : RuleClaims (Message F)} (inspected : plan.inspectRow rom row = .ok (some claims)) :
    plan.ActivatedLocalRule rom claims.1 claims.2 := by
  unfold Plan.inspectRow at inspected
  cases single : plan.singles.find? (·.name == row.chip) with
  | some chip =>
      simp only [single] at inspected
      cases checked : (Activation.compile chip).checkRow rom row with
      | error error => simp [checked] at inspected
      | ok result =>
          simp only [checked] at inspected
          by_cases active : row.assignment chip.numVars = 1
          · simp only [active, ↓reduceIte, Except.ok.injEq, Option.some.injEq] at inspected
            subst inspected
            obtain ⟨valid, rfl⟩ := Chip.checkRow_iff.mp checked
            have named := List.find?_some single
            simp only [beq_iff_eq] at named
            exact Or.inl ⟨chip, List.mem_of_find?_eq_some single, row,
              named.symm, valid, active, rfl, rfl⟩
          · simp [active] at inspected
  | none =>
      simp only [single] at inspected
      cases group : plan.groups.find? (·.checked.layout.name == row.chip) with
      | none => simp [group] at inspected
      | some packed =>
          simp only [group] at inspected
          obtain ⟨m, member, width, valid, selected, rfl⟩ := Layout.inspectRow_some inspected
          have named := List.find?_some group
          simp only [beq_iff_eq] at named
          exact Or.inr ⟨packed, List.mem_of_find?_eq_some group, row, m,
            named.symm, width, member, valid, selected, rfl, rfl⟩

/-- A weighted row: padding must not provide. -/
def Plan.weigh (plan : Plan source id) (rom : WireROM F) (weighted : WeightedRow F) :
    Except String (Option (RuleClaims (Message F) × Int)) :=
  match plan.inspectRow rom weighted.row with
  | .error error => .error error
  | .ok none => if weighted.multiplicity = 0 then .ok none else .error "a padding row provides a claim"
  | .ok (some claims) => .ok (some (claims, weighted.multiplicity))

theorem Plan.weigh_some {plan : Plan source id} {rom : WireROM F} {weighted : WeightedRow F}
    {rule : RuleClaims (Message F) × Int} (weighed : plan.weigh rom weighted = .ok (some rule)) :
    plan.inspectRow rom weighted.row = .ok (some rule.1) ∧ rule.2 = weighted.multiplicity := by
  unfold Plan.weigh at weighed
  cases inspected : plan.inspectRow rom weighted.row with
  | error error => simp [inspected] at weighed
  | ok result =>
      cases result with
      | none =>
          simp only [inspected] at weighed
          by_cases zero : weighted.multiplicity = 0 <;> simp [zero] at weighed
      | some claims =>
          simp only [inspected, Except.ok.injEq, Option.some.injEq] at weighed
          subst weighed
          exact ⟨rfl, rfl⟩

/-- The LogUp-style abstraction of the deployed grouped, activated circuits:
integer provide weights on active rows, unit premises, silent padding. -/
def Plan.checkMemo (plan : Plan source id) (rom : WireROM F) (root : Message F)
    (rows : List (WeightedRow F)) : Except String Unit :=
  match source.checkContext rom root with
  | .error error => .error (reprStr error)
  | .ok () =>
      match rows.mapM (plan.weigh rom) with
      | .error error => .error error
      | .ok weighed =>
          if (Balance.accumulator (fun c => decide (source.MapClaim c)) root
              (activeRules weighed)).isZero then .ok ()
          else .error "unbalanced lookup messages"

theorem Plan.checkMemo_weighed {plan : Plan source id} {rom : WireROM F} {root : Message F}
    {rows : List (WeightedRow F)} (checked : plan.checkMemo rom root rows = .ok ()) :
    ∃ weighed, rows.mapM (plan.weigh rom) = .ok weighed ∧
      (Balance.accumulator (fun c => decide (source.MapClaim c)) root
        (activeRules weighed)).isZero = true := by
  unfold Plan.checkMemo at checked
  cases context : source.checkContext rom root with
  | error error => simp [context] at checked
  | ok u =>
      cases u
      simp only [context] at checked
      cases mapped : rows.mapM (plan.weigh rom) with
      | error error => simp [mapped] at checked
      | ok weighed =>
          simp only [mapped] at checked
          refine ⟨weighed, rfl, ?_⟩
          by_cases balanced : (Balance.accumulator (fun c => decide (source.MapClaim c)) root
              (activeRules weighed)).isZero = true
          · exact balanced
          · rw [if_neg balanced] at checked
            cases checked

/-- A source chip's local rule is a rule instance of the source system. -/
theorem RuleInstance.ofLocalRule {rom : WireROM F} {chip : Chip F} {root : Message F}
    {premises : List (Message F)} (found : source.findChip? chip.name = some chip)
    (rule : chip.LocalRule rom root premises) :
    ∃ ruleInstance : RuleInstance source rom, ruleInstance.claims = (root, premises) := by
  obtain ⟨row, named, valid, rootEq, premisesEq⟩ := rule
  exact ⟨.node chip row (by rw [named]; exact found) valid, by
    simp [RuleInstance.claims, RuleInstance.conclusion, RuleInstance.premises, rootEq, premisesEq]⟩

/-- Accepted plan rows are, row by row, weighted rule instances of the source
system: the transport through activation and grouping. -/
theorem Plan.checkMemo_rules {plan : Plan source id} (activated : plan.WellFormedActivation)
    {rom : WireROM F} {root : Message F} {rows : List (WeightedRow F)}
    (checked : plan.checkMemo rom root rows = .ok ()) :
    ∃ rules : List (RuleInstance source rom × Int), rules.length ≤ rows.length ∧
      (Balance.accumulator (fun c => decide (source.MapClaim c)) root
        (rules.map fun rule => (rule.1.claims, rule.2))).isZero = true := by
  obtain ⟨weighed, mapped, zero⟩ := Plan.checkMemo_weighed checked
  have each : ∀ {rows : List (WeightedRow F)} {weighed},
      List.Forall₂ (fun row result => plan.weigh rom row = .ok result) rows weighed →
      ∃ rules : List (RuleInstance source rom × Int), rules.length ≤ rows.length ∧
        activeRules weighed = rules.map fun rule => (rule.1.claims, rule.2) := by
    intro rows weighed related
    induction related with
    | nil => exact ⟨[], le_rfl, rfl⟩
    | @cons row result rest results head _ ih =>
        obtain ⟨rules, length, same⟩ := ih
        cases result with
        | none => exact ⟨rules, by simp; omega, by rw [activeRules_none]; exact same⟩
        | some weightedRule =>
            obtain ⟨inspected, weight⟩ := Plan.weigh_some head
            have local_ := (plan.localRule_iff rom _ _).mp
              ((plan.activatedLocalRule_iff activated rom _ _).mp (Plan.inspectRow_some inspected))
            obtain ⟨chip, found, rule⟩ := local_
            obtain ⟨ruleInstance, claims⟩ := RuleInstance.ofLocalRule found rule
            refine ⟨(ruleInstance, weightedRule.2) :: rules, by simp; omega, ?_⟩
            rw [activeRules_some, same, List.map_cons, claims]
  obtain ⟨rules, length, same⟩ := each (mapM_ok_iff.mp mapped)
  rw [same] at zero
  exact ⟨rules, length, zero⟩

/-- Plan-checker acceptance gives a memo graph over the source system with at
most one row node per physical row. -/
theorem Plan.checkMemo_graph {plan : Plan source id} (activated : plan.WellFormedActivation)
    {rom : WireROM F} {root : Message F} {rows : List (WeightedRow F)}
    (checked : plan.checkMemo rom root rows = .ok ()) :
    ∃ graph : MemoDerivation source rom root, graph.rows.card ≤ rows.length := by
  obtain ⟨rules, length, zero⟩ := Plan.checkMemo_rules activated checked
  obtain ⟨graph, card⟩ := MemoDerivation.exists_of_balance rules zero
  exact ⟨graph, card.trans length⟩

end Aiur.Optimized.Grouping
