import Ix.CompileCert.Entry

namespace Tests.Ix.CompileCert.InstalledCaps
open _root_.Ix.CompileCert
open _root_.Ix.Kernel

def require (label : String) (result : Bool) : IO Unit := do
  unless result do throw (IO.userError label)

/-- Synthetic lookup-boundary controls. The positive result certifies only
stored entry shapes, not admission or capability semantics. -/
def run : IO Unit := do
  let family := sourceName `Family
  let constructor := sourceName `Family.mk
  let header (name : Name) : ConstantVal := ⟨name, [], .sort .zero⟩
  let caps : IndCaps := { eta := true, etaCtor := constructor, etaFields := 2 }
  let ctor := ConstantInfo.ctorInfo (header constructor) 0 2
  let projection (index : Nat) := ConstantInfo.recInfo (header (projFnName family index)) 0 0 []
  let env : Env := ⟨[ctor, projection 0, projection 1]⟩
  require "complete exact stored family" (checkInstalledEtaFamily env family caps)
  require "missing constructor" (!checkInstalledEtaFamily ⟨[projection 0, projection 1]⟩ family caps)
  require "wrong constructor kind" (!checkInstalledEtaFamily
    ⟨[.axiomInfo (header constructor), projection 0, projection 1]⟩ family caps)
  require "missing last projection" (!checkInstalledEtaFamily ⟨[ctor, projection 0]⟩ family caps)
  require "duplicate projection does not fill index" (!checkInstalledEtaFamily
    ⟨[ctor, projection 0, projection 0]⟩ family caps)
  require "wrong projection kind" (!checkInstalledEtaFamily
    ⟨[ctor, projection 0, .axiomInfo (header (projFnName family 1))]⟩ family caps)
  require "reserved constructor refused" (!checkInstalledEtaFamily
    ⟨[.ctorInfo (header natZeroName) 0 0]⟩ family { caps with etaCtor := natZeroName, etaFields := 0 })
  require "zero fields still checks constructor" (checkInstalledEtaFamily ⟨[ctor]⟩ family { caps with etaFields := 0 })
  let source ← match Cached.checkDecls .verified [] #[.basisDecl .natK] with
    | .ok result => pure result
    | .error _ => throw (IO.userError "source Nat fold failed")
  let target ← match Cached.checkDecls .verified [] #[.basisDecl .natK] with
    | .ok result => pure result
    | .error _ => throw (IO.userError "target Nat fold failed")
  require "actual Nat telescope" (checkTelescopes source target id)
  require "actual Nat capability association" (checkInstalledCapabilities source target id)
  require "missing installed family" (!checkInstalledCapabilities source Env.empty id)
  let mutations : List (String × (IndCaps → IndCaps)) := [
    ("eta flag", fun c => { c with eta := !c.eta }),
    ("unit flag", fun c => { c with unitlike := !c.unitlike }),
    ("K flag", fun c => { c with ruleK := !c.ruleK }),
    ("eta parameters", fun c => { c with etaParams := c.etaParams + 1 }),
    ("eta fields", fun c => { c with etaFields := c.etaFields + 1 }),
    ("unit parameters", fun c => { c with unitParams := c.unitParams + 1 }),
    ("sort regime", fun c => { c with sortZ := if c.sortZ = .never then .ifAllZero [] else .never })]
  for (label, mutate) in mutations do
    let changed : Env := ⟨target.consts.map fun entry => match entry with
      | .indInfo h c => .indInfo h (mutate c)
      | other => other⟩
    require label (!checkInstalledCapabilities source changed id)
  let aliasA := sourceName `AliasA
  let aliasB := sourceName `AliasB
  let shared := sourceName `Shared
  let names (name : Name) := if name = aliasA || name = aliasB then shared else name
  let plain : IndCaps := {}
  let aliases : Env := ⟨[.indInfo (header aliasA) plain, .indInfo (header aliasB) plain]⟩
  let sharedEnv : Env := ⟨[.indInfo (header shared) plain]⟩
  require "compatible complete alias fiber" (checkInstalledCapabilities aliases sharedEnv names)
  require "second alias field mismatch" (!checkInstalledCapabilities
    ⟨[.indInfo (header aliasA) plain, .indInfo (header aliasB) { plain with ruleK := true }]⟩ sharedEnv names)
  let etaCaps : IndCaps := { caps with etaFields := 1 }
  require "eta constructor identity" (decide (!InstalledCapsHeader id family etaCaps
    { etaCaps with etaCtor := sourceName `Wrong }))
  let badProjection (name : Name) := if name = projFnName family 0 then sourceName `Wrong else name
  require "eta indexed projection identity" (decide (!InstalledCapsHeader badProjection family etaCaps etaCaps))
  let sourceUnit ← match Cached.checkDecls .verified [] #[.basisDecl .punitK] with
    | .ok result => pure result
    | .error _ => throw (IO.userError "source PUnit fold failed")
  let targetUnit ← match Cached.checkDecls .verified [] #[.basisDecl .punitK] with
    | .ok result => pure result
    | .error _ => throw (IO.userError "target PUnit fold failed")
  require "actual PUnit telescope" (checkTelescopes sourceUnit targetUnit id)
  require "actual PUnit capability association" (checkInstalledCapabilities sourceUnit targetUnit id)
  require "actual PUnit constructor at family levels"
    (checkInstalledFamilyMember sourceUnit targetUnit id punitName punitUnitName == some true)
  let u := sourceName `u
  let v := sourceName `v
  let a := sourceName `a
  let b := sourceName `b
  let extra := sourceName `extra
  let sourceOwner := sourceName `SourceOwner
  let targetOwner := sourceName `TargetOwner
  let sourceHelper := sourceName `SourceHelper
  let targetHelper := sourceName `TargetHelper
  let familyNames (n : Name) := if n = sourceOwner then targetOwner else if n = sourceHelper then targetHelper else n
  let familySource : Env := ⟨[.axiomInfo ⟨sourceOwner, [u, v], .sort .zero⟩,
    .axiomInfo ⟨sourceHelper, [v, u], .sort .zero⟩]⟩
  let familyTarget (parameters : List Name) : Env := ⟨[.axiomInfo ⟨targetOwner, [a, b], .sort .zero⟩,
    .axiomInfo ⟨targetHelper, parameters, .sort .zero⟩]⟩
  require "reordered helper telescope at family levels"
    (checkInstalledFamilyMember familySource (familyTarget [b, a]) familyNames sourceOwner sourceHelper == some true)
  require "same arity wrong family-level order"
    (checkInstalledFamilyMember familySource (familyTarget [a, b]) familyNames sourceOwner sourceHelper != some true)
  require "out-of-family target parameter"
    (checkInstalledFamilyMember familySource (familyTarget [b, extra]) familyNames sourceOwner sourceHelper != some true)
  require "missing mapped family helper"
    (checkInstalledFamilyMember familySource ⟨[.axiomInfo ⟨targetOwner, [a, b], .sort .zero⟩]⟩
      familyNames sourceOwner sourceHelper != some true)
  require "reserved eta selects pinned branch" (checkInstalledEtaAt targetUnit punitName)
  require "ordinary eta selects complete stored family"
    (checkInstalledEtaAt ⟨.indInfo (header family) caps :: env.consts⟩ family)
  require "ordinary eta cannot skip missing projection"
    (!checkInstalledEtaAt ⟨[.indInfo (header family) caps, ctor, projection 0]⟩ family)
  require "eta family must actually be inductive"
    (!checkInstalledEtaAt ⟨.axiomInfo (header family) :: env.consts⟩ family)
  require "complete actual Nat eta associations" (checkInstalledEtaAssociations source target id == some true)
  require "complete actual PUnit eta associations" (checkInstalledEtaAssociations sourceUnit targetUnit id == some true)
  let missingUnitCtor : Env := ⟨targetUnit.consts.filter (fun entry => entry.name != punitUnitName)⟩
  require "reserved eta still needs actual constructor association"
    (checkInstalledEtaAssociations sourceUnit missingUnitCtor id != some true)
  let shadowed : Env := ⟨sourceUnit.consts ++ sourceUnit.consts.map (fun entry => match entry with
    | .indInfo h c => .indInfo h { c with etaFields := c.etaFields + 1 }
    | other => other)⟩
  require "shadowed eta row cannot borrow first source lookup"
    (checkInstalledEtaAssociations shadowed targetUnit id != some true)
  let stream := #[Declaration.basisDecl .falseK, .basisDecl .eqK, .basisDecl .natK, .basisDecl .punitK]
  let combinedSource ← match Cached.checkDecls .verified [] stream with
    | .ok result => pure result
    | .error _ => throw (IO.userError "combined source fold failed")
  let combinedTarget ← match Cached.checkDecls .verified [] stream with
    | .ok result => pure result
    | .error _ => throw (IO.userError "combined target fold failed")
  require "combined stream capability endpoint checks"
    (checkTelescopes combinedSource combinedTarget id && checkInstalledTypes combinedSource combinedTarget id &&
      checkInstalledDefinitions combinedSource combinedTarget id && checkInstalledPin combinedSource id falseName 0 &&
      checkInstalledPin combinedSource id eqName 1 && checkInstalledCapabilities combinedSource combinedTarget id &&
      checkInstalledEtaAssociations combinedSource combinedTarget id == some true)
  require "combined independent streams also satisfy fired-rule endpoint checks"
    (checkInstalledRecursors combinedSource combinedTarget id && checkInstalledConstructors combinedSource combinedTarget id)
  require "combined independent streams satisfy universal level-link checks"
    (checkInstalledRuleLevelLinks combinedSource combinedTarget id == some true)
  require "single aggregate accepts independent combined streams"
    (checkInstalledAssociation combinedSource combinedTarget id == some true)
  require "single aggregate rejects missing target constructor"
    (checkInstalledAssociation combinedSource
      ⟨combinedTarget.consts.filter (fun entry => entry.name != punitUnitName)⟩ id == some false)
  let unknownName := sourceName `UnknownComparison
  let unknownSource : Env := ⟨[.axiomInfo ⟨unknownName, [],
    .letE (.sort .zero) (.sort .zero) (.bvar 0)⟩]⟩
  let unknownTarget : Env := ⟨[.axiomInfo ⟨unknownName, [], .sort .zero⟩]⟩
  require "unavailable comparison survives Boolean projection"
    (checkInstalledAssociation unknownSource unknownTarget id == none)
  require "missing association is definite certificate refusal"
    (checkInstalledAssociation unknownSource ⟨[]⟩ id == some false)
  require "actual checked Eq.refl supplies exact installed equation frame"
    (readInstalledEquationFrame combinedTarget eqReflName 2).isSome
  require "equation frame rejects short argument telescope"
    (readInstalledEquationFrame combinedTarget eqReflName 1).isNone
  require "equation frame rejects excess argument telescope"
    (readInstalledEquationFrame combinedTarget eqReflName 3).isNone
  require "equation frame rejects missing exact identity"
    (readInstalledEquationFrame combinedTarget (sourceName `missingEquation) 2).isNone
  let forgedName := sourceName `forgedEquation
  let forgedType : Expr := .app (.app (.app (.const (sourceName `fakeEq) [.zero])
    (.sort .zero)) (.sort .zero)) (.sort .zero)
  require "equation frame rejects unpinned equality head"
    (readInstalledEquationFrame ⟨[.axiomInfo ⟨forgedName, [], forgedType⟩]⟩ forgedName 0).isNone
  IO.println "installed capabilities: independent Nat/PUnit/combined folds; 49 association controls passed"

end Tests.Ix.CompileCert.InstalledCaps

def main : IO Unit := Tests.Ix.CompileCert.InstalledCaps.run
