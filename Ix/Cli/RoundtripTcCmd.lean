/-
  `ix roundtrip-tc <path.ixe>`: kernel ↔ Ixon structural roundtrip over a
  serialized environment through the pure-Lean `Ix.Tc` kernel.

  For every constant: ingress into a fresh kernel env, egress back to an
  `Ixon.Constant`, and compare canonical forms (sharing expanded, tables
  renumbered, universes reduced — see `Ix.Tc.Egress`); projection constants
  compare byte-exact. Certifies that loading a constant into the kernel
  loses no information.

  "Anon" scope: the v1 Ix.Tc kernel is anon-only — metadata (names, binder
  info, mdata) never enters it, so the roundtrip covers exactly the
  kernel-held, hash-relevant structure. The metadata half of the pipeline
  belongs to the Rust meta-mode `kernel-ixon-roundtrip` test (through
  `decompile` back to Lean) until meta-mode ingress lands here.

  Work items are independent (fresh kernel env per item, immutable
  `Ixon.Env`), so chunks run in parallel on the task pool — bound the
  thread count with `LEAN_NUM_THREADS` if needed. No def-eq is involved,
  so this is much faster than `check-tc`.

  Flags:
  - `--fail-out <path>`: stream failing addresses (one `#<hex> <err>` line
    each).
  - `--max N`: stop after N work items (smoke runs).
  - `--verbose`: log every chunk as it joins (default: every ~20 chunks).
-/
module
public import Cli
public import Ix.Common
public import Ix.Tc

public section

namespace Ix.Cli.RoundtripTcCmd

open Ix.Tc

def runRoundtripTcCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let verbose := p.flag? "verbose" |>.isSome
  let max? := (p.flag? "max").map (·.as! Nat)
  let failOutPath := ((p.flag? "fail-out").map (·.as! String)).getD ""

  IO.println s!"Running Ix.Tc kernel↔Ixon structural roundtrip on {envPath}"
  let bytes ← IO.FS.readBinFile envPath
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .ok env => pure env
    | .error e =>
      IO.eprintln s!"[roundtrip-tc] deserialize failed: {e}"
      return 1
  let work ← match buildAnonWork ixonEnv with
    | .ok work => pure work
    | .error e =>
      IO.eprintln s!"[roundtrip-tc] work discovery failed: {e}"
      return 1
  let workN := match max? with
    | some n => min n work.size
    | none => work.size
  IO.println s!"[roundtrip-tc] {work.size} work item(s) discovered{if workN < work.size then s!", running first {workN}" else ""} ({ixonEnv.consts.size} consts)"

  let failOut? ← if failOutPath.isEmpty then pure none
    else pure (some (← IO.FS.Handle.mk failOutPath .write))

  let start ← IO.monoMsNow
  let chunkSize := 256
  let tasks := roundtripTasks ixonEnv (work.extract 0 workN) chunkSize
  let mut rows := 0
  let mut passed := 0
  let mut itemsDone := 0
  let mut failures : Array (String × String) := #[]
  let mut chunkIdx := 0
  for t in tasks do
    for r in t.get do
      rows := rows + 1
      match r.err? with
      | none => passed := passed + 1
      | some msg =>
        failures := failures.push (s!"#{r.addr}", msg)
        if let some h := failOut? then
          h.putStrLn s!"#{r.addr} {msg}"
          h.flush
    itemsDone := min (itemsDone + chunkSize) workN
    chunkIdx := chunkIdx + 1
    if chunkIdx != tasks.size && (verbose || chunkIdx % 20 == 0) then
      let elapsed := (← IO.monoMsNow) - start
      IO.println s!"[roundtrip-tc] {itemsDone}/{workN} items, {rows} rows, {failures.size} failures, {elapsed}ms"
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"[roundtrip-tc] {rows} constants roundtripped ({workN} work items) in {elapsed}ms"
  IO.println s!"[roundtrip-tc] {passed}/{rows} preserved structure"
  if workN == work.size && rows != ixonEnv.consts.size then
    IO.println s!"[roundtrip-tc] WARNING: coverage gap — {rows} rows vs {ixonEnv.consts.size} env constants"
  if !failures.isEmpty then
    -- Best-effort addr → name labels from the (anon-ignored) meta sections.
    let addrToName : Std.HashMap String String :=
      match Ixon.deEnv bytes with
      | .ok fullEnv => fullEnv.addrToName.fold
          (fun acc addr name => acc.insert (toString addr) (toString name)) {}
      | .error _ => {}
    IO.println s!"[roundtrip-tc] {failures.size} failure(s):"
    let shown := min 30 failures.size
    for (label, msg) in failures.toSubarray 0 shown do
      let named := match addrToName[(label.drop 1).toString]? with
        | some n => s!"{label} ({n})"
        | none => label
      IO.println s!"  ✗ {named}: {msg}"
    if failures.size > shown then
      IO.println s!"  … ({failures.size - shown} more failures suppressed)"
  if !failOutPath.isEmpty then
    IO.println s!"[roundtrip-tc] streamed {failures.size} failure(s) to {failOutPath}"
  IO.println s!"##roundtrip-tc## {elapsed} {passed} {failures.size} {rows}"
  return if failures.isEmpty then 0 else 1

end Ix.Cli.RoundtripTcCmd

open Ix.Cli.RoundtripTcCmd in
def roundtripTcCmd : Cli.Cmd := `[Cli|
  "roundtrip-tc" VIA runRoundtripTcCmd;
  "Kernel↔Ixon structural roundtrip of a `.ixe` through the pure-Lean Ix.Tc kernel (anon: metadata never enters the kernel)"

  FLAGS:
    "fail-out" : String; "Write failing constants to this path"
    max        : Nat;    "Roundtrip only the first N work items"
    verbose;             "Log every chunk as it joins (default: progress every ~20 chunks)"

  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
