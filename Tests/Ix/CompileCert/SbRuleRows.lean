import Ix.CompileCert.RuleRowAnnotations
import Ix.CompileCert.Certifier

/-! Focused S+b row controls on independently folded Nat/Eq declarations.
The endpoint mutations are themselves admitted true theorems. The selected
source rule still determines which equation is required, so true but wrong
equations must fail its row check. Separate annotation/kind mutations are
explicit lookup-boundary probes, not admitted environments or S verdicts.
-/

namespace Tests.Ix.CompileCert.SbRuleRows

open _root_.Ix _root_.Ix.CompileCert _root_.Ix.CompileCert.Certifier

def require (label : String) (actual expected : Bool) : IO Unit := do
  IO.println (Lean.Json.mkObj [("name", .str label), ("actual", Lean.toJson actual),
    ("expected", Lean.toJson expected), ("pass", Lean.toJson (actual == expected))]).compress
  unless actual == expected do throw (IO.userError s!"S+b firing-row control failed: {label}")

def folded (declarations : Array Kernel.Declaration) : IO Kernel.Env :=
  match Kernel.Cached.checkDecls .verified [] declarations with
  | .ok env => pure env
  | .error _ => throw (IO.userError "S+b firing-row control fold refused")

/-- This deliberately bounded proposal uses the actual installed zero rule
and its complete annotated prefix. It performs no source annotation erasure. -/
def zeroProposal {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) : Except String FiringRowProposal := do
  unless frame.rule.ctor == Kernel.natZeroName && frame.rule.nfields == 0 &&
      frame.rule.ctorParams == 0 && frame.rulePrefix == frame.major do
    throw "not the expected zero rule"
  let universes := frame.header.levelParams.map Kernel.Level.param
  let [level] := universes | throw "unexpected Nat recursor universe telescope"
  let some (binders, residual) := frame.header.type.stripPis frame.rulePrefix
    | throw "missing actual Nat recursor prefix"
  let major := Kernel.Expr.const frame.rule.ctor []
  let some carrier := Kernel.Expr.instPisAtLift [major] residual
    | throw "missing actual Nat major binder"
  return { binders, level, carrier, universes, constructorUniverses := [],
    argumentExpressions := argumentVariables frame.rulePrefix, fieldExpressions := [] }

/-- The actual Eq reflexivity rule at its dependent prefix. The constructor
parameters and recursor index are the prefix's own alpha/a variables here;
this is one admitted neighbour, not a general parameter-blindness premise. -/
def eqReflProposal {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) : Except String FiringRowProposal := do
  unless frame.rule.ctor == Kernel.eqReflName && frame.rule.nfields == 0 &&
      frame.rule.ctorParams == 2 && frame.rulePrefix == 4 && frame.major == 5 do
    throw "not the expected Eq reflexivity rule"
  let universes := frame.header.levelParams.map Kernel.Level.param
  let [level, _] := universes | throw "unexpected Eq recursor universe telescope"
  let constructorUniverses := frame.universeComparands.map
    (Kernel.Level.subst frame.header.levelParams universes)
  let some (binders, residual) := frame.header.type.stripPis frame.rulePrefix
    | throw "missing actual Eq recursor prefix"
  let fieldExpressions := [Kernel.Expr.bvar 3, .bvar 2]
  let major := Kernel.Expr.mkAppN (.const frame.rule.ctor constructorUniverses) fieldExpressions
  let some carrier := Kernel.Expr.instPisAtLift [.bvar 2, major] residual
    | throw "missing actual Eq index/major binders"
  return { binders, level, carrier, universes, constructorUniverses,
    argumentExpressions := argumentVariables frame.rulePrefix ++ [.bvar 2], fieldExpressions }

def run : IO Unit := do
  let base := #[Kernel.Declaration.basisDecl .eqK, .basisDecl .natK]
  let source ← folded base
  let recursor := Kernel.natName.str "rec"
  let some frame := readInstalledRuleFrame source recursor 0
    | throw (IO.userError "actual Nat zero rule missing")
  let some otherFrame := readInstalledRuleFrame source recursor 1
    | throw (IO.userError "actual Nat successor rule missing")
  let originalProposal ← IO.ofExcept (zeroProposal frame)
  let proposal := originalProposal.forEquation
  let rowName := sourceName `SbRuleRows.honest
  let some row := supportRow rowName frame.header.levelParams (frame.rowStatement proposal)
    | throw (IO.userError "actual firing row is not an equation")
  let target ← folded (base.push row)
  let honest := checkInstalledFiringRow source target id frame proposal rowName == some true
  require "actual-folded-row" honest true
  require "actual-telescope-association" (checkTelescopes source target id) true
  require "equation-regime-valid-neighbour" honest true
  require "unadapted-recursor-prefix-regime"
    (checkInstalledFiringRow source target id frame originalProposal rowName == some true) false
  let left := frame.rowLeft proposal
  let right := frame.rowRight proposal
  for (label, endpoint) in [("wrong-left", right), ("wrong-right", left)] do
    require (label ++ "-valid-neighbour") honest true
    let wrongName := rowName.str label
    let statement := ruleRowForalls proposal.binders
      (kernelEq proposal.level proposal.carrier endpoint endpoint)
    let some wrong := supportRow wrongName frame.header.levelParams statement
      | throw (IO.userError "true wrong-endpoint control is not an equation")
    let wrongTarget ← folded (base.push wrong)
    require label (checkInstalledFiringRow source wrongTarget id frame proposal wrongName == some true) false
  require "wrong-constructor-valid-neighbour" honest true
  require "wrong-selected-source-constructor"
    (checkInstalledFiringRow source target id otherFrame proposal rowName == some true) false
  require "missing-row-valid-neighbour" honest true
  require "missing-installed-row"
    (checkInstalledFiringRow source target id frame proposal (rowName.str "missing") == some true) false
  require "universe-arity-valid-neighbour" honest true
  require "wrong-recursor-universe-arity"
    (checkInstalledFiringRow source target id frame { proposal with universes := [] }
      rowName == some true) false
  let some installed := target.find? rowName
    | throw (IO.userError "admitted honest theorem missing")
  let wrongKind : Kernel.Env := ⟨target.consts.map fun entry =>
    if entry.name == rowName then .axiomInfo entry.toConstantVal else entry⟩
  require "wrong-kind-valid-neighbour" honest true
  require "lookup-boundary-wrong-kind"
    (checkInstalledFiringRow source wrongKind id frame proposal rowName == some true) false
  let .forallE domain body metadata := installed.toConstantVal.type
    | throw (IO.userError "admitted honest theorem lost its prefix")
  let opposite : Kernel.BinderMeta :=
    ⟨if metadata.pw == .never then .ifAllZero [] else .never⟩
  let wrongAnnotations : Kernel.Env := ⟨target.consts.map fun entry =>
    if entry.name == rowName then
      match entry with
      | .thmInfo header proof => .thmInfo { header with type := .forallE domain body opposite } proof
      | other => other
    else entry⟩
  require "annotation-valid-neighbour" honest true
  require "lookup-boundary-binder-annotation"
    (checkInstalledFiringRow source wrongAnnotations id frame proposal rowName == some true) false
  let .forallE innerDomain innerBody innerMetadata := domain
    | throw (IO.userError "actual Nat motive domain lost its dependent binder")
  let innerOpposite : Kernel.BinderMeta :=
    ⟨if innerMetadata.pw == .never then .ifAllZero [] else .never⟩
  let wrongDomainAnnotations : Kernel.Env := ⟨target.consts.map fun entry =>
    if entry.name == rowName then
      match entry with
      | .thmInfo header proof => .thmInfo { header with type :=
          .forallE (.forallE innerDomain innerBody innerOpposite) body metadata } proof
      | other => other
    else entry⟩
  require "domain-annotation-valid-neighbour" honest true
  require "lookup-boundary-dependent-domain-annotation"
    (checkInstalledFiringRow source wrongDomainAnnotations id frame proposal rowName == some true) false
  let extraName := rowName.str "extra"
  let some extra := supportRow extraName frame.header.levelParams (frame.rowStatement proposal)
    | throw (IO.userError "extra honest row lost its equation")
  let extraTarget ← folded ((base.push row).push extra)
  require "extra-admitted-target-support"
    (checkInstalledFiringRow source extraTarget id frame proposal rowName == some true) true
  -- The actual Eq basis rule is parameter-blind and has two constructor
  -- parameters. These are structural witness controls, not assertions that
  -- arbitrary mismatched bvars form a typed semantic firing instance.
  let some blind := readInstalledRuleFrame source (Kernel.eqName.str "rec") 0
    | throw (IO.userError "actual Eq recursor rule missing")
  unless blind.rule.fire == .plain && blind.rule.paramsBlind && blind.rule.ctorParams == 2 do
    throw (IO.userError "independent-parameter control became vacuous")
  let eqOriginal ← IO.ofExcept (eqReflProposal blind)
  let eqProposal := eqOriginal.forEquation
  let eqRowName := sourceName `SbRuleRows.eqRefl
  let some eqRow := supportRow eqRowName blind.header.levelParams (blind.rowStatement eqProposal)
    | throw (IO.userError "actual Eq firing row is not an equation")
  let eqTarget ← folded (base.push eqRow)
  let eqHonest := checkInstalledFiringRow source eqTarget id blind eqProposal eqRowName == some true
  require "eq-actual-folded-row" eqHonest true
  require "eq-actual-telescope-association" (checkTelescopes source eqTarget id) true
  require "eq-equation-regime-valid-neighbour" eqHonest true
  require "eq-unadapted-recursor-prefix-regime"
    (checkInstalledFiringRow source eqTarget id blind eqOriginal eqRowName == some true) false
  let some eqInstalled := eqTarget.find? eqRowName
    | throw (IO.userError "admitted Eq theorem missing")
  let .forallE eqDomain eqBody eqMetadata := eqInstalled.toConstantVal.type
    | throw (IO.userError "admitted Eq theorem lost its prefix")
  let eqOpposite : Kernel.BinderMeta :=
    ⟨if eqMetadata.pw == .never then .ifAllZero [] else .never⟩
  let eqWrongAnnotations : Kernel.Env := ⟨eqTarget.consts.map fun entry =>
    if entry.name == eqRowName then
      match entry with
      | .thmInfo header proof => .thmInfo { header with type :=
          .forallE eqDomain eqBody eqOpposite } proof
      | other => other
    else entry⟩
  require "eq-annotation-valid-neighbour" eqHonest true
  require "eq-lookup-boundary-binder-annotation"
    (checkInstalledFiringRow source eqWrongAnnotations id blind eqProposal eqRowName == some true) false
  let us := blind.header.levelParams.map Kernel.Level.param
  let ctorUs := blind.constructor.levelParams.map Kernel.Level.param
  let ctorType := blind.constructor.type.instantiateLevelParams blind.constructor.levelParams ctorUs
  let arguments := [Kernel.Expr.bvar 7, .bvar 6]
  let fields := [Kernel.Expr.bvar 5, .bvar 4]
  let old := Kernel.Expr.instPisAtLift (blind.openParameterRecipe us arguments) ctorType
  let independent := Kernel.Expr.instPisAtLift (blind.firingParameterRecipe us arguments fields) ctorType
  require "blind-independent-parameter-residual"
    (old.isSome && independent.isSome && decide (old ≠ independent) &&
      decide (blind.firingParameterRecipe us arguments fields = fields)) true
  let neighbour := Kernel.Expr.instPisAtLift (blind.firingParameterRecipe us arguments arguments) ctorType
  require "blind-equal-parameter-neighbour" (old.isSome && decide (old = neighbour)) true
  IO.println "S+b firing rows: 27 row controls and 2 parameter-witness controls passed"

end Tests.Ix.CompileCert.SbRuleRows

def main : IO Unit := Tests.Ix.CompileCert.SbRuleRows.run
