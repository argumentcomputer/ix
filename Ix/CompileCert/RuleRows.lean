import Ix.CompileCert.TypeRows

/-! # Installed firing equations through checked theorem rows

A source recursor may be represented by a target definition. In that case the
target has no installed recursor frame to transport. This module instead reads
an actual target theorem, checks its complete annotated type against a source
equation, and derives the equation at each typed source tuple.

The two endpoints are constructed from the selected *source* rule, using the
same expressions as `UniversalRuleSimulation`. They are not supplied as a
semantic equality premise. The proposal supplies a syntactic instance and its
telescope; the installed row check, not its spelling, supplies the equation.

This is a finite row-soundness slice. Coverage of all accepted source firing
instances, construction of their typed tuples, and the relation to the raw
`leanRuleStatement` export remain separate obligations. In particular, this
does not change or claim the old target-frame-based `UniversalRuleSimulation`,
nor does it certify capabilities, source installation or S+b as a whole.
-/

namespace Ix.CompileCert

/-- An untrusted syntactic presentation of a rule instance. Binder annotations
are retained. There is no independently supplied left or right endpoint. -/
structure FiringRowProposal where
  binders : List (Kernel.Expr × Kernel.BinderMeta)
  level : Kernel.Level
  carrier : Kernel.Expr
  universes : List Kernel.Level
  constructorUniverses : List Kernel.Level
  argumentExpressions : List Kernel.Expr
  fieldExpressions : List Kernel.Expr

/-- The actual source recursor applied to the actual selected constructor. -/
def InstalledRuleFrame.rowLeft {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (proposal : FiringRowProposal) : Kernel.Expr :=
  Kernel.Expr.mkAppN (.const name proposal.universes)
    (proposal.argumentExpressions ++
      [Kernel.Expr.mkAppN (.const frame.rule.ctor proposal.constructorUniverses)
        proposal.fieldExpressions])

/-- The same stored source RHS, universe instance, prefix and field suffix
as the source firing law. No beta reduction or annotation erasure is used. -/
def InstalledRuleFrame.rowRight {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (proposal : FiringRowProposal) : Kernel.Expr :=
  Kernel.Expr.mkAppN
    (frame.rule.rhs.instantiateLevelParams frame.header.levelParams proposal.universes)
    (proposal.argumentExpressions.take frame.rulePrefix ++
      proposal.fieldExpressions.drop frame.rule.ctorParams)

def ruleRowForalls : List (Kernel.Expr × Kernel.BinderMeta) → Kernel.Expr → Kernel.Expr
  | [], body => body
  | (domain, binder) :: rest, body => .forallE domain (ruleRowForalls rest body) binder

def InstalledRuleFrame.rowBody {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (proposal : FiringRowProposal) : Kernel.Expr :=
  kernelEq proposal.level proposal.carrier (frame.rowLeft proposal) (frame.rowRight proposal)

def InstalledRuleFrame.rowStatement {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (proposal : FiringRowProposal) : Kernel.Expr :=
  ruleRowForalls proposal.binders (frame.rowBody proposal)

theorem ruleRowForalls_strip (binders : List (Kernel.Expr × Kernel.BinderMeta))
    (body : Kernel.Expr) :
    (ruleRowForalls binders body).stripPis binders.length = some (binders, body) := by
  induction binders with
  | nil => rfl
  | cons binder rest ih =>
    rcases binder with ⟨domain, binder⟩
    simp only [ruleRowForalls, List.length_cons, Kernel.Expr.stripPis, ih, Option.map_some]

/-- The arity of a tuple ending in the equation follows from its actual
dependent telescope. It is not an additional source-domain hypothesis. -/
theorem InstalledTelescope.ruleRow_arity {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {valuation finalValuation : Nat → V}
    {binders : List (Kernel.Expr × Kernel.BinderMeta)} {arguments : List V}
    {level : Kernel.Level} {carrier left right : Kernel.Expr}
    (typed : InstalledTelescope values env levels valuation
      (ruleRowForalls binders (kernelEq level carrier left right))
      arguments finalValuation (kernelEq level carrier left right)) :
    arguments.length = binders.length := by
  induction binders generalizing valuation arguments with
  | nil =>
    cases typed with
    | nil => rfl
  | cons binder rest ih =>
    rcases binder with ⟨domain, binder⟩
    cases typed with
    | cons domainRead argumentTyped tail =>
      exact congrArg Nat.succ (ih tail)

/-- Inspect the actual installed theorem and compare its *whole* annotated
statement in the source recursor's universe telescope. The final target Eq
shape is checked independently; a target recursor frame is not requested.
`none` preserves an unavailable structural comparison, rather than declaring
the input outside the original compiler domain. -/
def checkInstalledFiringRow (source target : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame source name index) (proposal : FiringRowProposal)
    (rowName : Kernel.Name) : Option Bool :=
  match target.find? rowName with
  | some (.thmInfo row _) =>
    match row.type.stripPis proposal.binders.length with
    | some (_, body) =>
      match eqParts body with
      | some _ => checkInstalledMemberExpr source target names name
          (frame.rowStatement proposal) row.type
      | none => some false
    | none => some false
  | _ => some false

theorem checkInstalledFiringRow_spec {source target : Kernel.Env}
    {names : Kernel.Name → Kernel.Name} {name : Kernel.Name} {index : Nat}
    {frame : InstalledRuleFrame source name index} {proposal : FiringRowProposal}
    {rowName : Kernel.Name}
    (checked : checkInstalledFiringRow source target names frame proposal rowName = some true) :
    ∃ row proof binders level carrier left right,
      target.find? rowName = some (.thmInfo row proof) ∧
      row.type.stripPis proposal.binders.length =
        some (binders, kernelEq level carrier left right) ∧
      checkInstalledMemberExpr source target names name
        (frame.rowStatement proposal) row.type = some true := by
  unfold checkInstalledFiringRow at checked
  cases lookup : target.find? rowName with
  | none => simp [lookup] at checked
  | some entry =>
    cases entry with
    | thmInfo row proof =>
      simp only [lookup] at checked
      cases stripped : row.type.stripPis proposal.binders.length with
      | none => simp [stripped] at checked
      | some result =>
        obtain ⟨binders, body⟩ := result
        simp only [stripped] at checked
        cases parts : eqParts body with
        | none => simp [parts] at checked
        | some result =>
          obtain ⟨level, carrier, left, right⟩ := result
          simp only [parts] at checked
          refine ⟨row, proof, binders, level, carrier, left, right, rfl, ?_, checked⟩
          rw [stripped, eqParts_sound parts]
    | axiomInfo _ | defnInfo _ _ _ | recInfo _ _ _ _ | indInfo _ _
    | ctorInfo _ _ _ | projInfo _ => simp [lookup] at checked

/-- A checked row proves the actual selected source firing equation at each
typed source tuple. Both endpoint readings, the target tuple and its grading
are derived. There is no target rule frame, target tuple-typing premise, source
model choice, assumed equality, representative choice or annotation erasure.

The source tuple belongs to the proposed source equation telescope. Establishing
that all original source firing instances yield such tuples remains the source
coverage obligation; it is not asserted by this finite checker theorem. -/
theorem checkInstalledFiringRow_sound {V : Type u} [Kernel.SetTheory V]
    {source targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name}
    (telescopes : checkTelescopes source targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame source name index)
    (proposal : FiringRowProposal) {rowName : Kernel.Name}
    (checked : checkInstalledFiringRow source targetEnv names frame proposal rowName = some true)
    (levels : Kernel.Name → Nat) {valuation finalValuation : Nat → V} {arguments : List V}
    (typed : InstalledTelescope
      ((PullbackMap.fromEnvs source targetEnv names).values target.public.cval)
      source levels valuation (frame.rowStatement proposal)
      arguments finalValuation (frame.rowBody proposal)) :
    ∃ value,
      Kernel.Denotes ((PullbackMap.fromEnvs source targetEnv names).values target.public.cval)
        source levels finalValuation (frame.rowLeft proposal) value ∧
      Kernel.Denotes ((PullbackMap.fromEnvs source targetEnv names).values target.public.cval)
        source levels finalValuation (frame.rowRight proposal) value := by
  obtain ⟨row, proof, binders, level, carrier, left, right, lookup, stripped, comparison⟩ :=
    checkInstalledFiringRow_spec checked
  have association := checkTelescopes_sound telescopes
  have image := checkInstalledMemberExpr_sound target association frame.recursorLookup comparison levels
  obtain ⟨residual, targetTuple, residualImage⟩ := typed.image image
  have count : arguments.length = proposal.binders.length :=
    InstalledTelescope.ruleRow_arity typed
  have residualEq := targetTuple.result_of_stripPis (by rw [count]; exact stripped)
  subst residual
  change InstalledExprImage _ _ _ _ _ _
    (kernelEq proposal.level proposal.carrier (frame.rowLeft proposal) (frame.rowRight proposal))
    (kernelEq level carrier left right) at residualImage
  unfold kernelEq at residualImage
  cases residualImage with
  | app headImage rightImage =>
    cases headImage with
    | app _ leftImage =>
      have present := Kernel.Semantics.Env.find?_mem lookup
      obtain ⟨_, rowRead, _⟩ := targetTuple.model_apply target.public present
      unfold kernelEq at rowRead
      cases rowRead with
      | app headRead rightRead =>
        cases headRead with
        | app _ leftRead =>
          have same := target.theorem_eq row proof present targetTuple leftRead rightRead
          refine ⟨_, leftImage.symm.denotes leftRead, ?_⟩
          rw [same]
          exact rightImage.symm.denotes rightRead

end Ix.CompileCert
