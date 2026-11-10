import Ix.FormalProver
import Ix.FormalCompiler.Identity
import IxVM.Package
import MultiStark.Package

/-!
The certified Aiur compiler linked into `ix`. On a cache miss a command
compiles the selected program here, in process, with the functions the
standalone exporters run (`IxVM.compilePackage`,
`MultiStark.compilePackage`): the same entries, function groups, parallel
export and package encoding, so the bytes equal the exporter's for the same
program and compiler. The caller caches them like an exported artifact
(`Ix.AiurArtifact.cached`) and hands the file to the prover.

Importing this module registers the compiler with `Ix.FormalProver`, so the
command code, which cannot import the compiler's packages, reaches it
through `FormalProver.compiler?`.
-/

namespace Ix.FormalCompiler
open Lean

/-- The identity of a target's program. -/
def digest : FormalProver.Target → String
  | .ixvm => IxVM.programDigest
  | .verifier => MultiStark.recursionDigest
  | .aggregation => MultiStark.aggregateDigest

/-- Compile `target` into its package bytes, with its circuits. -/
def compile : FormalProver.Target → IO ByteArray
  | .ixvm => IxVM.compilePackage
  | .verifier => MultiStark.compilePackage false
  | .aggregation => MultiStark.compilePackage true

/-- The identity of the compiler code linked here: everything `compile`
reaches, programs and function groups included. -/
def identity : String :=
  compiler_identity% [Ix.FormalCompiler.compile] []

initialize FormalProver.compilerRef.set (some { identity, digest, compile })

end Ix.FormalCompiler
