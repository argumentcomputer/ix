module

public import Lean

@[expose] public section

namespace TruthMinesSpec

/-- A reproducible Git source. Revisions are full commit hashes, never moving
branches or tags. -/
structure GitSource where
  url : String
  rev : String
  subdir? : Option String := none
deriving Repr, Inhabited, BEq

/-- Catalog sources include local fixture packages (the RelocFixture collision
pair shared with `Benchmarks/Catalog`); production packages use pinned Git
sources. -/
inductive PackageSource where
  | local (path : String)
  | git (source : GitSource)
deriving Repr, Inhabited, BEq

inductive CatalogDisposition where
  | candidate
  | excluded (reason : String)
deriving Repr, Inhabited, BEq

/-- The sole hand-authored description of a package considered for the corpus.
There is intentionally no topical tier, `heavy` flag, or deferred state; a
candidate is admitted exactly when the frozen admission spec
(`Benchmarks.TruthMinesSpec.Spec`) carries its qualifier. -/
structure PackageSpec where
  lakeName : String
  qualifier : Lean.Name
  source : PackageSource
  upstreamToolchain : String
  directDeps : Array String
  license : String
  lastCommit : String
  rootModules : Array Lean.Name
  /-- Narrow escape hatch for a source file omitted by an upstream LeanLib
  glob. Every use must be explained in `notes`. -/
  moduleIncludes : Array Lean.Name := #[]
  /-- Narrow escape hatch for a module incorrectly claimed by an upstream
  LeanLib glob. Every use must be explained in `notes`. -/
  moduleExcludes : Array Lean.Name := #[]
  hermetic : Bool
  disposition : CatalogDisposition
  notes : String
deriving Repr, Inhabited, BEq

/-- One member of the catalog ix builds: a qualifier and the root modules whose
import closure delivers that package.

Roots are not simply the package's declared entry points. A provider's umbrella
need not import every module a downstream member uses, and ix renames every
module of a cataloged package it meets in any member's environment while
replaying only the closure of the roots it was given. A module reachable from
some consumer and rooted by nobody would therefore be renamed and never
replayed. These roots are closed over cross-package import edges to a global
fixed point so that cannot happen. -/
structure CatalogSpecLib where
  qualifier : Lean.Name
  roots : Array Lean.Name
deriving Repr, Inhabited, BEq

/-- The catalog ix builds, members in dependency order (dependencies first).
`ix catalog` resolves the package-to-qualifier map incrementally as it streams
members, so a provider listed after its consumer is a spec ordering error. -/
structure CatalogSpecProjection where
  catalogPrefix : Lean.Name
  libs : Array CatalogSpecLib
deriving Repr, Inhabited, BEq

/-- Every root module in the spec, in member order. -/
def CatalogSpecProjection.rootModules
    (projection : CatalogSpecProjection) : Array Lean.Name :=
  projection.libs.flatMap (·.roots)

def PackageSpec.isCandidate (spec : PackageSpec) : Bool :=
  match spec.disposition with
  | .candidate => true
  | .excluded _ => false

end TruthMinesSpec
