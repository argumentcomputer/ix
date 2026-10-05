import Ix.CompileCert.Entry

namespace Tests.Ix.CompileCert.InstalledRules
open _root_.Ix.CompileCert
open _root_.Ix.Kernel

def require (label : String) (result : Bool) : IO Unit := do
  unless result do throw (IO.userError label)

def alterRules (env : Env) (f : List RecRule → List RecRule) : Env :=
  ⟨env.consts.map fun entry => match entry with
    | .recInfo header major rulePrefix rules => .recInfo header major rulePrefix (f rules)
    | other => other⟩

def run : IO Unit := do
  let source ← match Cached.checkDecls .verified [] #[.basisDecl .natK] with
    | .ok env => pure env
    | .error _ => throw (IO.userError "source Nat fold failed")
  let target ← match Cached.checkDecls .verified [] #[.basisDecl .natK] with
    | .ok env => pure env
    | .error _ => throw (IO.userError "target Nat fold failed")
  let some (.recInfo header _ _ rules) := source.consts.find? (fun entry => match entry with
    | .recInfo _ _ _ rules => rules.length == 2
    | _ => false) | throw (IO.userError "expected actual two-rule Nat recursor")
  require "actual telescope association" (checkTelescopes source target id)
  require "actual installed Nat rules" (checkInstalledRecursors source target id)
  require "actual installed Nat constructors" (checkInstalledConstructors source target id)
  require "missing actual mapped constructors" (!checkInstalledConstructors source Env.empty id)
  let alteredConstructors (f : ConstantVal → Nat → Nat → ConstantInfo) : Env :=
    ⟨target.consts.map fun entry => match entry with
      | .ctorInfo cv params fields => f cv params fields
      | other => other⟩
  require "constructor role mismatch"
    (!checkInstalledConstructors source (alteredConstructors fun cv _ _ => .axiomInfo cv) id)
  require "constructor parameter mismatch"
    (!checkInstalledConstructors source (alteredConstructors fun cv p f => .ctorInfo cv (p + 1) f) id)
  require "constructor field mismatch"
    (!checkInstalledConstructors source (alteredConstructors fun cv p f => .ctorInfo cv p (f + 1)) id)
  let some ctor := source.consts.find? (fun entry => match entry with
    | .ctorInfo .. => true | _ => false) | throw (IO.userError "expected source constructor")
  let shadowed : Env := ⟨.axiomInfo ctor.toConstantVal :: source.consts⟩
  require "shadowed source constructor row" (!checkInstalledConstructors shadowed target id)
  require "missing recursor" (!checkInstalledRecursors source Env.empty id)
  require "missing rule" (!checkInstalledRecursors source (alterRules target (·.drop 1)) id)
  require "extra rule" (!checkInstalledRecursors source (alterRules target (fun rs => rs ++ rs)) id)
  require "reversed positions" (!checkInstalledRecursors source (alterRules target List.reverse) id)
  let mutations : List (String × (RecRule → RecRule)) := [
    ("constructor", fun r => { r with ctor := falseName }),
    ("field count", fun r => { r with nfields := r.nfields + 1 }),
    ("constructor parameter count", fun r => { r with ctorParams := r.ctorParams + 1 }),
    ("K rescue", fun r => { r with k := !r.k }),
    ("eta rescue", fun r => { r with eta := !r.eta }),
    ("parameter comparison", fun r => { r with paramsBlind := !r.paramsBlind }),
    ("firing mode", fun r => { r with fire := .inert }),
    ("RHS", fun r => { r with rhs := .bvar 999 })]
  for (label, mutate) in mutations do
    require label (!checkInstalledRecursors source (alterRules target (List.map mutate)) id)
  let changedIndex : Env := ⟨target.consts.map fun entry => match entry with
    | .recInfo h major rulePrefix rs => .recInfo h (major + 1) rulePrefix rs
    | other => other⟩
  require "major position" (!checkInstalledRecursors source changedIndex id)
  let changedPrefix : Env := ⟨target.consts.map fun entry => match entry with
    | .recInfo h major rulePrefix rs => .recInfo h major (rulePrefix + 1) rs
    | other => other⟩
  require "rule prefix" (!checkInstalledRecursors source changedPrefix id)
  -- Synthetic nested cases exercise the comparison boundary only; the
  -- positive actual-fold control above uses the installed Nat plain rules.
  let compare := checkInstalledFire source target id header.name
  require "semantic nested levels" (compare (.nested [.zero] [.bvar 0])
    (.nested [.max .zero .zero] [.bvar 0]) == some true)
  require "nested level mismatch" (compare (.nested [.zero] [.bvar 0])
    (.nested [.succ .zero] [.bvar 0]) == some false)
  require "nested pin position" (compare (.nested [.zero] [.bvar 0, .bvar 1])
    (.nested [.zero] [.bvar 1, .bvar 0]) == some false)
  require "nested pin omission" (compare (.nested [.zero] [.bvar 0])
    (.nested [.zero] []) == some false)
  require "source actual rules retained" (rules.length == 2)
  require "actual Nat constructor universe selection"
    (checkInstalledRuleUniverses target header.name 0 [.zero] [] == some true)
  require "missing rule ordinal" (checkInstalledRuleUniverses target header.name 2 [.zero] [] != some true)
  require "wrong recursor arity" (checkInstalledRuleUniverses target header.name 0 [] [] != some true)
  require "wrong constructor arity" (checkInstalledRuleUniverses target header.name 0 [.zero] [.zero] != some true)
  require "inert rule cannot supply fired frame"
    (checkInstalledRuleUniverses (alterRules target (List.map fun r => { r with fire := .inert }))
      header.name 0 [.zero] [] != some true)
  let unit ← match Cached.checkDecls .verified [] #[.basisDecl .punitK] with
    | .ok env => pure env
    | .error _ => throw (IO.userError "actual PUnit fold failed")
  let recursor := punitName.str "rec"
  require "reserved PUnit constructor role" (checkInstalledConstructors unit unit id)
  require "actual PUnit constructor universe selection"
    (checkInstalledRuleUniverses unit recursor 0 [.zero, .succ .zero] [.succ .zero] == some true)
  require "semantic constructor level alias"
    (checkInstalledRuleUniverses unit recursor 0 [.zero, .succ .zero] [.max .zero (.succ .zero)] == some true)
  require "wrong concrete constructor universe"
    (checkInstalledRuleUniverses unit recursor 0 [.zero, .succ .zero] [.zero] != some true)
  let withoutConstructor : Env := ⟨unit.consts.filter (fun entry => entry.name != punitUnitName)⟩
  require "missing actual constructor"
    (checkInstalledRuleUniverses withoutConstructor recursor 0 [.zero, .succ .zero] [.succ .zero] != some true)
  let wrongConstructor : Env := ⟨unit.consts.map fun entry =>
    if entry.name = punitUnitName then .axiomInfo entry.toConstantVal else entry⟩
  require "wrong constructor kind"
    (checkInstalledRuleUniverses wrongConstructor recursor 0 [.zero, .succ .zero] [.succ .zero] != some true)
  -- Synthetic firing-mode mutation exercises nested universe substitution;
  -- it is not asserted to be an admitted nested block.
  let nested := alterRules unit (List.map fun r => { r with fire := .nested [.succ (.param uN)] [] })
  require "nested concrete universe substitution"
    (checkInstalledRuleUniverses nested recursor 0 [.zero, .succ .zero] [.succ (.succ .zero)] == some true)
  require "nested universe mismatch"
    (checkInstalledRuleUniverses nested recursor 0 [.zero, .succ .zero] [.succ .zero] != some true)
  require "actual Nat universal rule-level link"
    (checkInstalledRuleLevelLink source target id header.name 0 == some true)
  require "actual PUnit universal rule-level link"
    (checkInstalledRuleLevelLink unit unit id recursor 0 == some true)
  require "missing target level-link owner"
    (checkInstalledRuleLevelLink unit Env.empty id recursor 0 != some true)
  let some frame := readInstalledRuleFrame unit recursor 0 | throw (IO.userError "expected PUnit frame")
  let some otherParameter := frame.header.levelParams.find? (fun p => !frame.constructor.levelParams.contains p)
    | throw (IO.userError "expected recursor-only universe")
  let relinked : Env := ⟨unit.consts.map fun entry => match entry with
    | .ctorInfo cv p f => .ctorInfo { cv with levelParams := [otherParameter] } p f
    | other => other⟩
  require "same-arity wrong recursor-to-constructor level link"
    (checkInstalledRuleLevelLink unit relinked id recursor 0 != some true)
  require "out-of-owner target level rejected"
    (checkInstalledOwnerLevels unit unit id recursor [.param uN] [.param (.str .anonymous "outside")] != some true)
  require "synthetic nested universal level recipe"
    (checkInstalledRuleLevelLink nested nested id recursor 0 == some true)
  let nestedAlias := alterRules unit (List.map fun r => { r with fire := .nested [.max .zero (.succ (.param uN))] [] })
  require "semantic nested level recipe alias"
    (checkInstalledRuleLevelLink nested nestedAlias id recursor 0 == some true)
  let shortNested := alterRules unit (List.map fun r => { r with fire := .nested [] [] })
  require "nested level recipe cannot hide missing constructor universe"
    (checkInstalledRuleLevelLink shortNested shortNested id recursor 0 != some true)
  require "all actual Nat rule level links" (checkInstalledRuleLevelLinks source target id == some true)
  require "all actual PUnit rule level links" (checkInstalledRuleLevelLinks unit unit id == some true)
  require "global wrong formal linkage rejected" (checkInstalledRuleLevelLinks unit relinked id != some true)
  let shadowedRules : Env := ⟨source.consts ++ (alterRules source List.reverse).consts⟩
  require "shadowed source rule row cannot borrow a level link"
    (checkInstalledRuleLevelLinks shadowedRules target id != some true)
  IO.println "installed rules: actual Nat/PUnit folds; 52 rule/universe/constructor controls passed"

end Tests.Ix.CompileCert.InstalledRules

def main : IO Unit := Tests.Ix.CompileCert.InstalledRules.run
