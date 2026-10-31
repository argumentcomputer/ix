module
public import Ix.Compile.SourceGraph.Prepass

@[expose] public section
namespace Ix.Compile.SourceInput

abbrev Raw := Lean.Name × Lean.ConstantInfo

/-- Only the original winner map is retained. The prepass's thin environment,
label array and transient canonical bodies are not captured here. -/
structure Carrier where
  byName : Ix.Map Ix.Name Raw

/-- One original declaration, canonicalized alone (the singleton-canon
fallback). This lookup does not consult the transformed compile environment. -/
def canonical? (p : Raw) : Option Ix.ConstantInfo :=
  ((Ix.CanonM.canonChunk #[p])[0]?).map (·.2)

/-- A name's original declaration, canonicalized alone (`canonical?`): the
driver's fallback lookup for constants it does not keep. -/
def Carrier.lookup? (s : Carrier) (name : Ix.Name) : Option Ix.ConstantInfo :=
  (s.byName.get? name).bind canonical?

end Ix.Compile.SourceInput

end
