/-
  compile-ind-flags: both compilers refuse an input inductive whose stored
  flags (`isRec`, `isReflexive`, `numNested`) differ from the recomputed
  ones (Rust `validate_ind_groups`, Lean `Ix.CompileM.validateInductiveFlags`),
  and compile the same closure with the true flags byte-identically.

  The closure is `T` (a recursive inductive) with its recursor and the
  aux-gen seeds; the refused neighbour stores `isRec := false` on `T`. The
  Lean refusal is checked on both Lean drivers: the IO pipeline
  (`compileLeanConsts`, the parallel driver) and the pure compiler
  (`Ix.Cert.compile`, the sequential driver).

  Run with: `lake test -- --ignored compile-ind-flags`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.Cert.Compile
import LSpec

open Lean

namespace Tests.Ix.Compile.IndFlags

namespace Fixture

/-- A recursive inductive: Lean's stored `isRec` is `true`. -/
inductive T where
  | leaf : T
  | node : T → T

end Fixture

def tName : Name := ``Fixture.T

/-- The aux-gen seed names (`Ix.CompileM.auxGenSeedNames`), as Lean names. -/
def auxSeeds : List Name :=
  [``PUnit, ``PProd, ``Eq, ``Eq.refl, ``Eq.symm, ``Eq.ndrec, ``rfl, ``HEq,
    ``HEq.refl, ``eq_of_heq, ``True]

/-- The closure of `T`, with `T`'s stored `isRec` replaced by `isRec`. -/
def closure (env : Environment) (isRec : Bool) :
    Except String (List (Name × ConstantInfo)) := do
  let base := Ix.EnvScope.collectDeps env ([tName, tName ++ `rec] ++ auxSeeds)
  let some (.inductInfo v) := env.find? tName | throw "T missing"
  unless v.isRec do throw "T is not recursive"
  return base.map fun (n, ci) =>
    if n == tName then (n, .inductInfo { v with isRec }) else (n, ci)

/-- The expected refusal's text, without the error-kind prefix. -/
def flagsMessage : String :=
  s!"non-canonical inductive flags for '{tName}': stored isRec=false \
isReflexive=false numNested=0, computed isRec=true isReflexive=false numNested=0"

/-- Rust (`ix compile`, fail-closed): `ok bytes`, or the refusal text. -/
def rust (env : Environment) (cs : List (Name × ConstantInfo)) (out : System.FilePath) :
    IO (Except String ByteArray) := do
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env cs)
  try
    let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared out.toString false
    if let some (n, m) := status.ungrounded[0]? then
      return .error s!"{n}: {m}"
    return .ok (← IO.FS.readBinFile out)
  catch e => return .error (toString e)

/-- The Lean IO pipeline (`compile-lean`): `ok bytes`, or the refusal text. -/
def lean (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Except String ByteArray) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env cs).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := 1) with
  | .error e => return .error e
  | .ok o =>
    if let some (n, m) := o.cenv.ungrounded.toList.head? then
      return .error s!"{n}: {m}"
    return .ok o.bytes

/-- The pure compiler (`Ix.Cert.compile`): `ok bytes`, or the refusal text. -/
def pure (cs : List (Name × ConstantInfo)) : Except String ByteArray := do
  let consts := (Ix.CanonM.canonChunk cs.toArray).foldl (init := {}) fun m (n, c) =>
    m.insert n c
  let ixe ← Ix.Cert.compile { consts }
  Ixon.serEnv ixe

def run : IO UInt32 := do
  let env ← get_env!
  let dir ← IO.FS.createTempDir
  let mut failures := 0
  try
    let good ← IO.ofExcept (closure env true)
    let bad ← IO.ofExcept (closure env false)
    -- valid neighbour: every leg compiles, byte-identically
    match ← rust env good (dir / "good.ixe"), ← lean env good, pure good with
    | .ok r, .ok l, .ok p =>
      if r == l && l == p then
        IO.println s!"[ind-flags] true flags: all three compile, byte-identical ({r.size} bytes)"
      else
        failures := failures + 1
        IO.println s!"[ind-flags] true flags: FAIL: outputs differ \
(rust {r.size}, lean {l.size}, pure {p.size} bytes)"
    | r, l, p =>
      failures := failures + 1
      IO.println s!"[ind-flags] true flags: FAIL: rust {r.isOk}, lean {l.isOk}, pure {p.isOk}"
    -- stored `isRec := false`: every leg refuses with the same message
    let legs := [("rust", ← rust env bad (dir / "bad.ixe")), ("lean", ← lean env bad),
      ("pure", pure bad)]
    for (label, result) in legs do
      match result with
      | .ok _ =>
        failures := failures + 1
        IO.println s!"[ind-flags] stored isRec=false: {label}: FAIL: compiled"
      | .error e =>
        if (e.splitOn flagsMessage).length > 1 then
          IO.println s!"[ind-flags] stored isRec=false: {label} refuses: {flagsMessage}"
        else
          failures := failures + 1
          IO.println s!"[ind-flags] stored isRec=false: {label}: FAIL: other refusal: {e}"
  finally
    IO.FS.removeDirAll dir
  IO.println s!"[ind-flags] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.IndFlags
