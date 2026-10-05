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
  IO.println "installed capabilities: independent Nat/PUnit folds; 24 lookup/field/alias controls passed"

end Tests.Ix.CompileCert.InstalledCaps

def main : IO Unit := Tests.Ix.CompileCert.InstalledCaps.run
