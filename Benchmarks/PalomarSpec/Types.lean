module

public import Lean

@[expose] public section

namespace PalomarSpec

/-- An immutable repository snapshot named by a Palomar record. -/
structure GitSource where
  url : String
  rev : String
  subdir? : Option String := none
deriving Repr, Inhabited, BEq

/-- One current project snapshot from the Palomar registry.

`qualifier` is ix's stable member identity. `packageName` is the package name
declared upstream; the generated wrapper deliberately requires it under the
unique qualifier so repositories that reuse package names remain isolated.
The root is the verified solution closure recorded by Palomar, rather than an
umbrella import invented by this corpus. -/
structure Entry where
  registryId : String
  version : Nat
  qualifier : Lean.Name
  title : String
  source : GitSource
  packageName : String
  upstreamToolchain : String
  license : String
  solutionModule : Lean.Name
  formalizationPath : String
  directDependencies : Array String
deriving Repr, Inhabited, BEq

def Entry.registryPath (entry : Entry) : String :=
  s!"entries/{entry.registryId}-v{entry.version}.json"

def Entry.dataUrl (entry : Entry) : String :=
  s!"https://data.palomar-registry.org/{entry.registryPath}"

end PalomarSpec
