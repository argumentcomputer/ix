module

public import LSpec
public import Ix.Tc
public import Ix.CompileM
public import Ix.KernelCheck
public import Ix.Meta
public import Ix.Common

/-!
Anon verdict differential (`tc-anon-diff`, ignored suite).

Compiles Lean closures through the Rust compiler, writes the serialized env
to a temp `.ixe`, and compares per-target verdicts: Rust kernel
(`rsCheckAnonFFI`) vs pure-Lean `Ix.Tc.checkEnvAnon` over the same bytes.

P7 scope: inductive/recursor validation is not yet ported (P8/P9) — Lean
verdicts carrying the "not yet ported" stub are counted and skipped; every
other verdict must agree (pass/fail; messages are not compared). Once P8/P9
land, the skip set must go to zero and the gate below tightens.
-/

namespace Tests.Tc.AnonDiff

open LSpec
open Ix.Tc

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
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
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
    ("bool-decide", [`Bool.rec, `Nat.decEq]) ]

def diffSuite : TestSeq := Id.run do
  let mut ts : TestSeq := .done
  for (label, seeds) in seedSets do
    ts := ts ++ .individualIO s!"anon verdict parity: {label}" none (do
      let env ← get_env!
      let (compared, skipped, diff?) ← diffOnSeeds env label seeds
      let msg := diff?.map (s!"compared {compared}, skipped {skipped} stubs: " ++ ·)
      return (diff?.isNone, compared, skipped, msg)) .done
  return ts

public def suite : List TestSeq := [diffSuite]

end Tests.Tc.AnonDiff
