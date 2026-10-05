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
  IO.println "installed rules: independent Nat folds; 21 controls passed"

end Tests.Ix.CompileCert.InstalledRules

def main : IO Unit := Tests.Ix.CompileCert.InstalledRules.run
