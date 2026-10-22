import Aiur.Optimized.LookupGuards
import Aiur.Optimized.Propagation

namespace Aiur.Optimized.LookupMerging

variable {F : Type} [Field F] [DecidableEq F]

/-- A guarded output definition. Its expression already includes the guard. -/
structure OutputDefinition (ctx : Context F) (id scope : Witness) where
  expr : Polynomial F
  sound : ∀ a, ctx.Valid a →
    (ctx.guard scope).denote a * a (ctx.layout.column id) = expr.denote a

def outputLeaf (ctx : Context F) (id scope : Witness) (eq : Equation F)
    (member : eq ∈ ctx.logical.equations.toList) (owner : eq.scope = scope)
    (value : Polynomial F) (solved : eq.polynomial.solution? id = some value) : OutputDefinition ctx id scope where
  expr := Polynomial.simplify (.mul (ctx.guard scope) (ctx.layout.expression value))
  sound a valid := by
    have zero := (ctx.logicalValid valid).1 eq member
    rw [owner] at zero
    simp only [Context.guard, ColumnLayout.expression_denote, Polynomial.denote_simplify,
      Scalar.Circuit.ArithExpr.denote]
    rcases mul_eq_zero.mp zero with inactive | equation
    · simp [inactive]
    · exact congrArg (fun x => (ctx.logical.activation scope).denote (a ∘ ctx.layout.column) * x)
        (Polynomial.solution?_sound solved (a ∘ ctx.layout.column) equation)

structure OutputSum (ctx : Context F) (id : Witness) (scopes : List ScopeId) where
  expr : Polynomial F
  sound : ∀ a, ctx.Valid a →
    (scopes.map (fun scope => (ctx.guard scope).denote a)).sum * a (ctx.layout.column id) = expr.denote a

def outputSum (ctx : Context F) (id : Witness)
    (resolve : (scope : ScopeId) → Option (OutputDefinition ctx id scope)) :
    (scopes : List ScopeId) → Option (OutputSum ctx id scopes)
  | [] => some ⟨.const 0, by intros; simp [Scalar.Circuit.ArithExpr.denote]⟩
  | scope :: scopes => do
    let head ← resolve scope
    let tail ← outputSum ctx id resolve scopes
    return ⟨.add head.expr tail.expr, by
      intro a valid
      simp only [List.map_cons, List.sum_cons, add_mul, Scalar.Circuit.ArithExpr.denote]
      rw [head.sound a valid, tail.sound a valid]⟩

theorem Context.coverage (ctx : Context F) (choice : Choice)
    (member : choice ∈ ctx.logical.choices.toList) {a : Witness → F} (valid : ctx.Valid a) :
    (choice.children.map (fun scope => (ctx.guard scope).denote a)).sum =
      (ctx.guard choice.parent).denote a := by
  have zero := ctx.control.zero (ctx.logicalValid valid) (ctx.control.2.1 choice member).1
  have fold (scopes : List ScopeId) (start : Polynomial F) :
      (scopes.foldl (fun sum child => Polynomial.add sum (ctx.logical.activation child)) start).denote
        (a ∘ ctx.layout.column) = start.denote (a ∘ ctx.layout.column) +
          (scopes.map (fun scope => (ctx.guard scope).denote a)).sum := by
    induction scopes generalizing start with
    | nil => simp
    | cons scope scopes ih => simp [ih, Context.guard, Scalar.Circuit.ArithExpr.denote, add_assoc]
  simpa only [Scalar.Circuit.ArithExpr.denote, Control.Choice.total, fold,
    zero_add, sub_eq_zero, Context.guard, ColumnLayout.expression_denote] using zero

/-- Search actual guarded equalities and checked coverage trees. Failure to
find a complete cover retains the existing output witness. -/
def outputDefinition (ctx : Context F) (id : Witness) : Nat →
    (scope : ScopeId) → Option (OutputDefinition ctx id scope)
  | 0, _ => none
  | fuel + 1, scope => do
    for eq in ctx.logical.equations.toList.attach do
      if owner : eq.val.scope = scope then
        match solved : eq.val.polynomial.solution? id with
        | none => pure ()
        | some value =>
          if value.degree ≤ 1 then
            return outputLeaf ctx id scope eq.val eq.property owner value solved
    for choice in ctx.logical.choices.toList.attach do
      if parent : choice.val.parent = scope then
        if let some parts := outputSum ctx id (outputDefinition ctx id fuel) choice.val.children then
          return ⟨parts.expr, by
            intro a valid
            rw [← parent, ← ctx.coverage choice.val choice.property valid]
            exact parts.sound a valid⟩
    none

structure OutputFact (chip : Circuit.Chip F) where
  id : Witness
  value : Polynomial F
  unpinned : id ∉ Propagation.fixed chip
  sound : ∀ a, Circuit.Satisfies chip.constraints a → a id = value.denote a

def outputFacts (ctx : Context F) (chip : Circuit.Chip F)
    (equations : chip.constraints = (emitChip ctx.logical ctx.layout).constraints) : List (OutputFact chip) := Id.run do
  let mut facts := []
  let outputs := ctx.logical.output.words.map ctx.layout.column
  for id in ctx.logical.output.words do
    let column := ctx.layout.column id
    if unpinned : column ∉ Propagation.fixed chip then
      if let some definition := outputDefinition ctx id ctx.logical.scopes.size 0 then
        let value := definition.expr.simplify
        if value.degree ≤ 2 && !value.vars.any (outputs.contains ·) then
          facts := facts ++ [⟨column, value, unpinned, by
            intro a valid
            have ctxValid : ctx.Valid a := by simpa only [Context.Valid, ← equations] using valid
            have defined := definition.sound a ctxValid
            have root : (ctx.guard 0).denote a = 1 := by
              simpa only [Context.guard, ColumnLayout.expression_denote, Scalar.Circuit.ArithExpr.denote]
                using ctx.control.1.denote (a ∘ ctx.layout.column)
            simpa only [root, one_mul, value, Polynomial.denote_simplify] using defined⟩]
  return facts

def outputReplacement {chip : Circuit.Chip F} (facts : List (OutputFact chip)) (id : Witness) : Polynomial F :=
  match facts.find? (fun fact => fact.id == id) with
  | some fact => fact.value
  | none => .var id

omit [DecidableEq F] in
theorem outputReplacement_fixed {chip : Circuit.Chip F} (facts : List (OutputFact chip))
    {id : Witness} (member : id ∈ Propagation.fixed chip) : outputReplacement facts id = .var id := by
  unfold outputReplacement
  cases found : facts.find? _ with
  | none => rfl
  | some fact =>
    have same : fact.id = id := by simpa only [beq_iff_eq] using (List.find?_some found)
    exact False.elim (fact.unpinned (same.symm ▸ member))

omit [DecidableEq F] in
theorem outputReplacement_denote {chip : Circuit.Chip F} (facts : List (OutputFact chip))
    {a : Witness → F} (valid : Circuit.Satisfies chip.constraints a) (id : Witness) :
    (outputReplacement facts id).denote a = a id := by
  unfold outputReplacement
  cases found : facts.find? _ with
  | none => rfl
  | some fact =>
    have same : fact.id = id := by simpa only [beq_iff_eq] using (List.find?_some found)
    exact (fact.sound a valid).symm.trans (congrArg a same)

def replaceOutputs (chip : Circuit.Chip F) (facts : List (OutputFact chip)) : Propagation.Checked chip where
  chip := Propagation.rewrite chip id (outputReplacement facts)
  equivalent := by
    have fixed : ∀ i ∈ Propagation.fixed chip, outputReplacement facts i = .var i :=
      fun _ member => outputReplacement_fixed facts member
    constructor
    · intro rom a valid
      have same : (fun i => (outputReplacement facts i).denote a) = a :=
        funext (outputReplacement_denote facts valid.1)
      refine ⟨a, ?_, ?_, ?_⟩
      · rw [Propagation.rewrite_valid, same]; exact valid
      · rw [(Propagation.rewrite_claims chip id _ fixed a).1, same]
      · rw [(Propagation.rewrite_claims chip id _ fixed a).2, same]
    · intro rom a valid
      exact ⟨_, (Propagation.rewrite_valid chip id _ rom a).mp valid,
        (Propagation.rewrite_claims chip id _ fixed a).1.symm,
        (Propagation.rewrite_claims chip id _ fixed a).2.symm⟩
  name_eq := rfl
  inputTypes := by simp [Propagation.rewrite, List.map_map, Function.comp_def]
  outputType := rfl

end Aiur.Optimized.LookupMerging
