import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.Trans
import Lean4Lean.Theory.Typing.Pattern

/-!
# Ambient inductive oracle

Lean4Lean currently leaves both `VInductDecl.WF` and `VEnv.addInduct` as
opaque `sorry` definitions.  Requiring an equation involving that operation
here would make the ambient-inductive precondition impossible to instantiate
without adding another axiom.  G2 therefore records the semantic consequences
needed by the checker directly:

* every admitted concrete inductive-family constant has an exact raw Theory
  translation and lookup;
* its Theory constant is well-formed;
* the post-environment is well-formed and extends the prior environment;
* every concrete recursor rule has an explicit, well-formed Theory defeq
  witness headed by that recursor.

`InductiveOracle` is an explicit assumption boundary, not a claim that Ix's
inductive checker has already been verified.  The later inductive milestone
must construct this interface from block checking and a completed
Lean4Lean `addInduct` specification.  Keeping the interface in terms of
semantic consequences permits a closed Nat model with no new Lean axiom now,
while the recursor clause prevents future whnf proofs from treating
computation rules as an unrecorded ambient fact.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VDefEq VEnv VExpr)

/-- Concrete declaration kinds admitted through an ambient inductive block.
Standalone declarations and quotients cannot cross this boundary. -/
def KConst.IsInductiveMember : KConst .anon → Prop
  | .indc .. | .ctor .. | .recr .. => True
  | _ => False

/-- Membership of a concrete rule in a recursor declaration. -/
def KConst.HasRecursorRule (c : KConst .anon) (rule : RecRule .anon) : Prop :=
  match c with
  | .recr (rules := rules) .. => rule ∈ rules
  | _ => False

/-- Major-argument position used by the production iota reducer.  The
`UInt64` additions intentionally occur before `toNat`; recursor validation
must rule out overflow rather than this view silently changing runtime
indexing to mathematical addition. -/
def KConst.RecursorMajorIdx : KConst .anon → Option Nat
  | .recr (params := params) (motives := motives) (minors := minors)
      (indices := indices) .. =>
    some ((params + motives + minors + indices).toNat)
  | _ => none

/-- The descriptor-only Nat fast path and the ordinary iota reducer must
select the same major argument.  The former converts each count to `Nat`
before adding, while the latter performs wrapping `UInt64` additions first.
This predicate is therefore the exact no-overflow obligation needed to move
between those two production computations. -/
def KConst.RecursorMajorIdxCoherent : KConst .anon → Prop
  | .recr (params := params) (motives := motives) (minors := minors)
      (indices := indices) .. =>
    (params + motives + minors + indices).toNat =
      params.toNat + motives.toNat + minors.toNat + indices.toNat
  | _ => False

/-- Exact positional membership of a concrete recursor rule.  Unlike
`HasRecursorRule`, this retains the constructor dispatch index. -/
def KConst.RecursorRuleAt (c : KConst .anon) (index : Nat)
    (rule : RecRule .anon) : Prop :=
  match c with
  | .recr (rules := rules) .. => rules[index]? = some rule
  | _ => False

namespace KConst.RecursorRuleAt

/-- Positional rule evidence implies ordinary array membership while
retaining the stronger dispatch index for consumers that need it. -/
theorem hasRecursorRule {c : KConst .anon} {index : Nat}
    {rule : RecRule .anon} (h : c.RecursorRuleAt index rule) :
    c.HasRecursorRule rule := by
  cases c <;> simp only [KConst.RecursorRuleAt] at h
  case recr rules =>
    exact Array.mem_of_getElem? h

end KConst.RecursorRuleAt

/-- Constructor metadata relevant to iota pattern matching. -/
def KConst.ConstructorAt (c : KConst .anon) (index : Nat)
    (params fields : UInt64) : Prop :=
  match c with
  | .ctor (cidx := cidx) (params := actualParams)
      (fields := actualFields) .. =>
    cidx.toNat = index ∧ actualParams = params ∧ actualFields = fields
  | _ => False

/-- A Theory expression is an application spine headed by `name`. -/
inductive HeadConst (name : Lean.Name) : VExpr → Prop
  | const (levels : List Lean4Lean.VLevel) :
    HeadConst name (.const name levels)
  | app {fn arg : VExpr} : HeadConst name fn → HeadConst name (.app fn arg)

/-- An application spine has exactly `arity` arguments above a constant
head.  This is the counted form needed to distinguish an iota major from an
arbitrary later occurrence of the same constructor. -/
inductive HeadConstN (name : Lean.Name) : Nat → VExpr → Prop
  | const (levels : List Lean4Lean.VLevel) :
    HeadConstN name 0 (.const name levels)
  | app {arity : Nat} {fn arg : VExpr} :
    HeadConstN name arity fn → HeadConstN name (arity + 1) (.app fn arg)

namespace HeadConstN

/-- Matching `varN (const name) arity` exposes exactly that many application
arguments over `name`. -/
theorem of_varN_matches {name : Lean.Name} {arity : Nat} {source : VExpr}
    {levels : List Lean4Lean.VLevel}
    {captures : ((Lean4Lean.Pattern.const name).varN arity).Path → VExpr}
    (h : Lean4Lean.Pattern.Matches
      ((Lean4Lean.Pattern.const name).varN arity)
      source levels captures) :
    HeadConstN name arity source := by
  induction arity generalizing source with
  | zero =>
      change Lean4Lean.Pattern.Matches (.const name)
        source levels captures at h
      cases h
      exact .const levels
  | succ arity ih =>
      change Lean4Lean.Pattern.Matches
        (.var ((Lean4Lean.Pattern.const name).varN arity))
        source levels captures at h
      cases h with
      | var hprefix =>
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            HeadConstN.app (ih hprefix)

end HeadConstN

/-- Exact Theory pattern selected by an ordinary constructor iota rule. -/
def RecursorIotaPattern (recursorName : Lean.Name) (majorIdx : Nat)
    (constructorName : Lean.Name) (constructorArgs : Nat) :
    Lean4Lean.Pattern :=
  (Lean4Lean.SimplePattern.iota recursorName majorIdx constructorName
    constructorArgs).toPattern

namespace RecursorIotaPattern

/-- Invert an iota-pattern match into its exact recursor and constructor
application arities.  The final application is the major: `recursorPrefix`
contains precisely the parameters/motives/minors/indices before it. -/
theorem matches_shape
    {recursorName constructorName : Lean.Name}
    {majorIdx constructorArgs : Nat} {source : VExpr}
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern recursorName majorIdx constructorName
      constructorArgs).Path → VExpr}
    (h : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern recursorName majorIdx constructorName
        constructorArgs) source levels captures) :
    ∃ recursorPrefix major,
      source = .app recursorPrefix major ∧
      HeadConstN recursorName majorIdx recursorPrefix ∧
      HeadConstN constructorName constructorArgs major := by
  simp only [RecursorIotaPattern, Lean4Lean.SimplePattern.toPattern] at h
  cases h with
  | app hrecursor hconstructor =>
      exact ⟨_, _, rfl, HeadConstN.of_varN_matches hrecursor,
        HeadConstN.of_varN_matches hconstructor⟩

end RecursorIotaPattern

/-- Raw translation of one constant supplied by an ambient inductive block.
There is intentionally no block-typing derivation here; that semantic fact is
the oracle boundary. -/
structure RawInductiveConstRel (env : VEnv)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (id : KId .anon) (c : KConst .anon) (name : Lean.Name)
    (ci : VConstant) : Prop where
  kind : c.IsInductiveMember
  nameEq : nameOf id.addr = some name
  uvars : c.lvls.toNat = ci.uvars
  type : RawExprRel env nameOf trProj [] c.ty ci.type

namespace RawInductiveConstRel

theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {c : KConst .anon} {name : Lean.Name}
    {ci : VConstant}
    (h : RawInductiveConstRel env nameOf trProj id c name ci) :
    RawInductiveConstRel env' nameOf trProj id c name ci :=
  ⟨h.kind, h.nameEq, h.uvars, h.type.mono henv⟩

end RawInductiveConstRel

/-- Semantic evidence for one concrete recursor rule and one particular
registered Theory equation.  The raw relation preserves admission syntax;
the structural relation additionally proves that the same closed rule body
is typed at the equation's universe arity.  Keeping both prevents an
untyped/raw translation from being passed to the verified universe
instantiator as though it were `TrKExprS`. -/
def RegisteredRecursorRuleRhsRel (env : VEnv)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (id : KId .anon) (c : KConst .anon) (rule : RecRule .anon)
    (defeq : VDefEq) : Prop :=
  ∃ name constant,
    RawInductiveConstRel env nameOf trProj id c name constant ∧
    env.constants name = some constant ∧
    env.defeqs defeq ∧
    defeq.WF env ∧
    HeadConst name defeq.lhs ∧
    RawExprRel env nameOf trProj [] rule.rhs defeq.rhs ∧
    TrKExprS env defeq.uvars nameOf trProj [] rule.rhs defeq.rhs

/-- Existential rule-level form retained by the inductive oracle and trusted
catalog log. -/
def RawRecursorRuleRel (env : VEnv)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (id : KId .anon) (c : KConst .anon) (rule : RecRule .anon) : Prop :=
  ∃ defeq, RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq

namespace RegisteredRecursorRuleRhsRel

/-- A fixed registered RHS certificate survives trusted-world extension. -/
theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {c : KConst .anon} {rule : RecRule .anon}
    {defeq : VDefEq}
    (h : RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq) :
    RegisteredRecursorRuleRhsRel env' nameOf trProj id c rule defeq := by
  obtain ⟨name, constant, hraw, hlookup, hregistered, hwf, hhead,
    hrhsRaw, hrhsTyped⟩ := h
  exact ⟨name, constant, hraw.mono henv, henv.constants hlookup,
    henv.defeqs hregistered, hwf.mono henv, hhead, hrhsRaw.mono henv,
    hrhsTyped.mono henv⟩

/-- The registered Theory RHS really is typed.  This follows independently
from the new structural translation field, but exposing both facts makes the
remaining concrete-instantiation bridge auditable. -/
theorem rhsTyped
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    (h : RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq) :
    env.HasType defeq.uvars [] defeq.rhs defeq.type := by
  obtain ⟨_, _, _, _, _, hwf, _, _, _⟩ := h
  exact hwf.2

end RegisteredRecursorRuleRhsRel

namespace RawRecursorRuleRel

/-- Select the exact registered equation retained by a rule certificate. -/
theorem registeredRhs
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon}
    (h : RawRecursorRuleRel env nameOf trProj id c rule) :
    ∃ defeq,
      RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq := h

theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {c : KConst .anon} {rule : RecRule .anon}
    (h : RawRecursorRuleRel env nameOf trProj id c rule) :
    RawRecursorRuleRel env' nameOf trProj id c rule := by
  obtain ⟨defeq, hrhs⟩ := h
  exact ⟨defeq, hrhs.mono henv⟩

end RawRecursorRuleRel

/-! ### Exact recursor-pattern provenance -/

/- Semantic pattern evidence for one concrete recursor rule.

`RawRecursorRuleRel` records a registered equation and its translated RHS,
but a recursor-headed expression alone does not determine which argument is
the major or which constructor rule was selected.  This relation retains the
missing data in Lean4Lean's own rewrite vocabulary:

* the rule's exact array index and the production major index;
* the exact catalogued constructor at that index, including parameter and
  field arities;
* a `SimplePattern.iota` RHS/check pair sound for every extension of the
  admission environment.

The final clause mirrors `VEnv.Params.pat_wf` without requiring a global
`Params` instance.  It is a Theory/iota assumption boundary, not a statement
about WHNF execution or the Nat linear fast path. -/
/-- The finite data of one exact Theory iota pattern.  It lives in `Type`
because the dependent RHS/check values are computational data; the semantic
relation below remains proof-irrelevant. -/
structure RecursorRulePattern where
  recursorName : Lean.Name
  constructorId : KId .anon
  constructorName : Lean.Name
  constructorParams : UInt64
  constructorFields : UInt64
  ruleIndex : Nat
  majorIdx : Nat
  rhs : (RecursorIotaPattern recursorName majorIdx constructorName
    (constructorParams.toNat + constructorFields.toNat)).RHS
  checks : (RecursorIotaPattern recursorName majorIdx constructorName
    (constructorParams.toNat + constructorFields.toNat)).Check

/-- Proof-irrelevant semantic realization of exact iota-pattern data for one
concrete rule. -/
def RawRecursorRulePatternRel (env : VEnv) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) (id : KId .anon)
    (c : KConst .anon) (rule : RecRule .anon)
    (pattern : RecursorRulePattern) : Prop :=
  nameOf id.addr = some pattern.recursorName ∧
  c.RecursorMajorIdx = some pattern.majorIdx ∧
  c.RecursorMajorIdxCoherent ∧
  c.RecursorRuleAt pattern.ruleIndex rule ∧
  nameOf pattern.constructorId.addr = some pattern.constructorName ∧
  (∃ ctor,
    catalog pattern.constructorId = some ctor ∧
      ctor.ConstructorAt pattern.ruleIndex pattern.constructorParams
        pattern.constructorFields) ∧
  rule.fields = pattern.constructorFields ∧
  ∀ {env' : VEnv}, env ≤ env' →
    ∀ {uvars : Nat} {Gamma : List VExpr} {source : VExpr}
      {levels : List Lean4Lean.VLevel}
      {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat)).Path → VExpr}
      {A : VExpr},
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern pattern.recursorName pattern.majorIdx
          pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat))
        source levels captures →
      env'.HasType uvars Gamma source A →
      pattern.checks.OK (env'.IsDefEqU uvars Gamma) levels captures →
      env'.IsDefEqU uvars Gamma source
        (pattern.rhs.apply levels captures)

namespace RawRecursorRulePatternRel

/-- Pattern provenance is stable under trusted-world extension.  The sound
law was deliberately quantified over all future environments, so extending
the admission prefix only composes its lower bound. -/
theorem mono {env env' : VEnv} (henv : env ≤ env') {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {id : KId .anon}
    {c : KConst .anon} {rule : RecRule .anon}
    {pattern : RecursorRulePattern}
    (h : RawRecursorRulePatternRel env catalog nameOf id c rule pattern) :
    RawRecursorRulePatternRel env' catalog nameOf id c rule pattern := by
  rcases h with
    ⟨hname, hmajor, hcoherent, hrule, hctorName, hctor, hfields, hsound⟩
  exact ⟨hname, hmajor, hcoherent, hrule, hctorName, hctor, hfields, by
    intro future hfuture uvars Gamma source levels captures A
      hmatches htype hchecks
    exact hsound (henv.trans hfuture) hmatches htype hchecks⟩

end RawRecursorRulePatternRel

/-- One oracle-backed admission of an already-validated ambient inductive
block.  `members` is exact for this admission step; `fresh` prevents the
oracle from re-certifying an existing trusted id.

The oracle records `before ≤ after` rather than an opaque
`before.addInduct = some after` equation.  These are exactly the consequences
used before E2, and unlike the unfinished upstream operation they admit real
models. -/
structure InductiveOracle (trProj : RawProjRel) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) (trusted : KId .anon → Prop)
    (before : VEnv) where
  members : KId .anon → Prop
  nonempty : ∃ id, members id
  fresh : ∀ ⦃id⦄, members id → ¬trusted id
  after : VEnv
  envLE : before ≤ after
  blockWF : after.WF
  translateBlock : ∀ ⦃id⦄, members id →
    ∃ c name ci,
      catalog id = some c ∧
      RawInductiveConstRel after nameOf trProj id c name ci ∧
      after.constants name = some ci ∧
      ci.WF after
  recursorFacts : ∀ ⦃id c rule⦄,
    members id → catalog id = some c → c.HasRecursorRule rule →
      RawRecursorRuleRel after nameOf trProj id c rule
  recursorPatterns : ∀ ⦃id c ruleIndex rule⦄,
    members id → catalog id = some c →
      c.RecursorRuleAt ruleIndex rule →
      ∃ pattern,
        RawRecursorRulePatternRel after catalog nameOf id c rule pattern ∧
          pattern.ruleIndex = ruleIndex

namespace InductiveOracle

/-- Add exactly this oracle block to the trusted predicate. -/
def TrustBlock {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv}
    (oracle : InductiveOracle trProj catalog nameOf trusted before) :
    KId .anon → Prop :=
  fun id => oracle.members id ∨ trusted id

theorem trust_member {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv} (oracle : InductiveOracle trProj catalog nameOf trusted before)
    {id : KId .anon} (h : oracle.members id) : oracle.TrustBlock id :=
  Or.inl h

theorem trust_old {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv} (oracle : InductiveOracle trProj catalog nameOf trusted before)
    {id : KId .anon} (h : trusted id) : oracle.TrustBlock id :=
  Or.inr h

theorem catalogued {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv} (oracle : InductiveOracle trProj catalog nameOf trusted before)
    {id : KId .anon} (h : oracle.members id) : Catalog.Contains catalog id := by
  obtain ⟨c, _, _, hcat, _⟩ := oracle.translateBlock h
  exact ⟨c, hcat⟩

end InductiveOracle

end Ix.Tc
