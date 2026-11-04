import Ix.FormalProver
import Ix.FormalCompiler.Identity
import IxVM
import IxVM.FunctionGroups
import MultiStark
import MultiStark.FunctionGroups
import Aiur.Trace.Export

/-!
The certified Aiur compiler linked into `ix`. On a cache miss a command
compiles the selected program's source bundle here, in process, and hands
the resulting `Aiur.Image.RuntimeImage` to the prover directly: the adapter
reads the Lean objects and copies them once into a Rust-owned program. No
exporter process, JSON or temporary file sits between compilation and
execution.

The compiler is the one the standalone exporters (`IxVM/IxVM/Main.lean`,
`MultiStark/MultiStark/Main.lean`) run, with the same entries and function
groups; the replayed population plans are checked against the certified
layouts before the image is produced (`Aiur.Trace.exportPreparedImage`).

Importing this module registers the compiler with `Ix.FormalProver`, so the
command code, which cannot import the compiler's packages, reaches it
through `FormalProver.compiler`.
-/

namespace Ix.FormalCompiler
open Lean Aiur

/-- The program of a runtime image, registered under its lookup key. -/
@[extern "rs_formal_registry_of_image"]
opaque registryOfImage (registry : @& FormalProver.Registry) (key : @& ByteArray)
  (image : @& Image.RuntimeImage) : IO FormalProver.Program

/-- Make the frontend's syntax available for parsing source bundles: the
inherited `LEAN_PATH`, or the checkout's package build directories. -/
def frontend (root : System.FilePath) : IO Environment := do
  let paths ← match ← IO.getEnv "LEAN_PATH" with
    | some path => pure (System.SearchPath.parse path)
    | none => do
      let mut paths := [root / "Aiur" / ".lake" / "build" / "lib" / "lean"]
      let packages := root / ".lake" / "packages"
      if ← packages.isDir then
        for entry in ← packages.readDir do
          paths := paths ++ [entry.path / ".lake" / "build" / "lib" / "lean"]
      pure paths
  initSearchPath (← findSysroot) paths
  unsafe enableInitializersExecution
  importModules (loadExts := true) #[{ module := `Aiur.Modules.Frontend }] {} 0

/-- Compile the source bundle `text` of `target` into its runtime image. -/
def image (env : Environment) (target : FormalProver.Target) (text : String) :
    IO Image.RuntimeImage := do
  match target with
  | .ixvm =>
    let source ← IO.ofExcept (IxVM.parse env text)
    let prepared ← IO.ofExcept (Modules.prepare source ["IxVM::verify_claim"])
    let exported ← IO.ofExcept prepared.exportExecution
    Trace.modulesImage prepared exported IxVM.modulus ZMod.val IxVM.functionGroups
  | .verifier | .aggregation =>
    let entry := if target == .aggregation then "MultiStark::ix_aggr"
      else "MultiStark::verify_multi_stark_proof"
    let source ← IO.ofExcept (MultiStark.parse env text)
    let prepared ← IO.ofExcept (Modules.prepare source [entry])
    let exported ← IO.ofExcept prepared.exportExecution
    Trace.modulesImage prepared exported MultiStark.modulus ZMod.val MultiStark.functionGroups

/-- The identity of the compiler code linked here: the image producers and
the frontend that parses source bundles. -/
def identity : String :=
  compiler_identity% [Ix.FormalCompiler.image]
    [Aiur.Modules.Frontend, Aiur.Generic.Frontend]

/-- Compile `target` from its source bundle `text` into `registry` under
`key`; the checkout `root` supplies the frontend's build. -/
def compile (registry : FormalProver.Registry) (target : FormalProver.Target) (root text : String)
    (key : ByteArray) : IO FormalProver.Program := do
  let env ← frontend root
  let image ← image env target text
  registryOfImage registry key image

initialize FormalProver.compilerRef.set (some { identity, compile })

end Ix.FormalCompiler
