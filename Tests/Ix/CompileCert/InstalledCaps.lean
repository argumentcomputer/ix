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
  IO.println "installed capability lookup: 8 synthetic boundary controls passed"

end Tests.Ix.CompileCert.InstalledCaps

def main : IO Unit := Tests.Ix.CompileCert.InstalledCaps.run
