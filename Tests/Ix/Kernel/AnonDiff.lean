module

public import LSpec
public import Ix.Kernel
public import Ix.CompileM
public import Ix.KernelCheck
public import Ix.Meta
public import Ix.Common
public import Tests.Ix.Kernel.DefinitionDependencies

/-!
Anon verdict differential (`tc-anon-diff`, ignored suite).

Compiles Lean closures through the Rust compiler, writes the serialized env
to a temp `.ixe`, and compares per-target verdicts: Rust kernel
(`rsCheckAnonFFI`) vs pure-Lean `Ix.Kernel.checkEnvAnon` over the same bytes.

Lean verdicts carrying a "not yet ported" stub message are counted and
skipped — a guard from the incremental port, now expected to count zero
since inductive/recursor validation is in. Every other verdict must agree
(pass/fail; messages are not compared).
-/

namespace Tests.Kernel.AnonDiff

open LSpec
open Ix.Kernel

public section

/-- Skip marker for the not-yet-ported inductive machinery. -/
def isStubErr (msg : String) : Bool :=
  (msg.splitOn "not yet ported").length > 1

def closureOf (env : Lean.Environment) (seeds : List Lean.Name) :
    List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut out : List (Lean.Name × Lean.ConstantInfo) := []
  for seed in seeds do
    if !env.constants.contains seed then
      continue
    for (n, ci) in Lean.collectDependencies seed env.constants do
      if !seen.contains n then
        seen := seen.insert n
        out := (n, ci) :: out
  return out

/-- Run the differential over one seed list. Returns
    `(compared, skippedStubs, firstDiff?)`. -/
def diffOnSeeds (leanEnv : Lean.Environment) (label : String)
    (seeds : List Lean.Name) : IO (Nat × Nat × Option String) := do
  let consts := closureOf leanEnv seeds
  if consts.isEmpty then
    return (0, 0, some s!"empty closure for {seeds}")
  -- The compile FFI streams straight to a file; the Rust check reads the
  -- same path and the Lean side reads the bytes back.
  let dir ← IO.FS.createTempDir
  let path := dir / s!"tc-anon-diff-{label}.ixe"
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString true
  let rustRows ← Ix.KernelCheck.rsCheckAnonFFI path.toString true ""
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  let rust : Std.HashMap String (Option String) :=
    rustRows.foldl (init := {}) fun acc (addr, err?) =>
      acc.insert addr (err?.map (·.message))
  let leanResults ← match checkIxeBytesAnon bytes with
    | .ok rs => pure rs
    | .error e => return (0, 0, some s!"Lean driver failed: {e}")
  let mut compared := 0
  let mut skipped := 0
  let mut firstDiff : Option String := none
  for r in leanResults do
    let addrHex := toString r.addr
    let leanErr? := r.err?
    if let some msg := leanErr? then
      if isStubErr msg then
        skipped := skipped + 1
        continue
    match rust[addrHex]? with
    | none =>
      if firstDiff.isNone then
        firstDiff := some s!"{addrHex}: missing from Rust verdicts"
    | some rustErr? =>
      compared := compared + 1
      match rustErr?, leanErr? with
      | none, none => pure ()
      | some _, some _ => pure ()
      | some re, none =>
        if firstDiff.isNone then
          firstDiff := some s!"{addrHex}: rust FAIL ({re}) but lean PASS"
      | none, some le =>
        if firstDiff.isNone then
          firstDiff := some s!"{addrHex}: rust PASS but lean FAIL ({le})"
  -- The Lean target set must cover the Rust one exactly.
  if leanResults.size != rustRows.size && firstDiff.isNone then
    firstDiff := some s!"target counts differ: rust {rustRows.size} vs lean {leanResults.size}"
  if compared == 0 && firstDiff.isNone then
    firstDiff := some "nothing compared (all skipped?)"
  return (compared, skipped, firstDiff)

def seedSets : List (String × List Lean.Name) :=
  [ ("nat-add", [`Nat.add]),
    ("list-map", [`List.map]),
    ("nat-arith", [`Nat.mul, `Nat.pow, `Nat.ble]),
    ("eq-basics", [`Eq.refl, `Eq.symm, `congrArg]),
    ("bool-decide", [`Bool.rec, `Nat.decEq]),
    -- Formerly the tracked known divergence: `grind`-generated
    -- `Char.Ordinal` proofs (UInt32 arithmetic with 2^32-scale literals)
    -- tripped `maxDefEqDepth` in the pure-Lean kernel — doomed dependent
    -- proof-pair comparisons from the non-short-circuiting
    -- `(← a) && (← b)` port bug. Fixed by the isDefEqWhnf app/letE
    -- short-circuit (commit 891ad556); kept here as a parity guard.
    ("char-ordinal", [`Char.ofOrdinal, `Char.ofOrdinal_le_of_le,
      `Char.succ?_eq, `Char.ordinal_ofOrdinal]) ]

def diffSuite : TestSeq := Id.run do
  let mut ts : TestSeq := .done
  for (label, seeds) in seedSets do
    ts := ts ++ .individualIO s!"anon verdict parity: {label}" none (do
      let env ← get_env!
      let (compared, skipped, diff?) ← diffOnSeeds env label seeds
      let msg := diff?.map (s!"compared {compared}, skipped {skipped} stubs: " ++ ·)
      return (diff?.isNone, compared, skipped, msg)) .done
  return ts

/-- Both checkers process the exact serialized counterexample, with integrity
verification enabled. Matching error counts alone cannot pass: target sets,
per-target verdicts, and the cycle diagnostics must also agree. -/
def dependencyFixtureParity (source : Ixon.Env) (expected failures : Nat) :
    IO (Bool × Option String) := do
  let bytes ← match Ixon.serEnv source with
    | .ok bytes => pure bytes
    | .error error => return (false, some error)
  let directory ← IO.FS.createTempDir
  try
    let path := directory / "definition-dependencies.ixe"
    IO.FS.writeBinFile path bytes
    let rust ← Ix.KernelCheck.rsCheckAnonFFI path.toString true ""
    let lean ← match checkIxeBytesAnon bytes with
      | .ok results => pure results
      | .error error => return (false, some error)
    let cycle := fun message => ("cyclic definition dependency").isPrefixOf message
    let correct := rust.size == expected && lean.size == expected &&
      (lean.filter (·.err?.isSome)).size == failures &&
      lean.all fun row =>
        (row.err?.all cycle) && rust.any fun (address, error) =>
          address == toString row.addr && error.isSome == row.err?.isSome &&
            error.all (fun
              | .kernelException message => cycle message
              | .compileError _ => false)
    let rustMessages := rust.map fun (address, error) =>
      (address, error.map Ix.KernelCheck.CheckError.message)
    return (correct, if correct then none else some s!"expected {expected} targets/{failures} cycle failures; Lean {repr lean}; Rust {repr rustMessages}")
  finally
    IO.FS.removeDirAll directory

def dependencyDiffSuite : TestSeq := Id.run do
  let mut tests : TestSeq := .done
  for (label, source, targets, failures) in DefinitionDependencies.parityFixtures do
    tests := tests ++ .individualIO s!"anon verdict parity: {label}" none (do
      let (passed, message) ← dependencyFixtureParity source targets failures
      return (passed, targets, failures, message)) .done
  return tests

public def suite : List TestSeq := [diffSuite, dependencyDiffSuite]

end

end Tests.Kernel.AnonDiff
