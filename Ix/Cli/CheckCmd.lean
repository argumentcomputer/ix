/-
  `ix check`: execute the IxVM Aiur kernel over a Lean or `.ixe`
  environment, one constant at a time.
  The Rust kernel typechecker that used to live under this name is now `ix check-rs`.

  Usage shape:

      ix check Nat.add_comm                            # from compiled-in Lean env
      ix check --ixe arena.ixe foo bar baz             # from .ixe, named targets
      ix check --ixe arena.ixe                         # iterate every named const
      ix check --interp Nat.add_comm                   # Aiur interpreter (richer errors)
      ix check --stats-out STATS Nat.add_comm          # redirect per-circuit stats

  Stats print when exactly one constant is targeted. Multi-target +
  whole-env iteration both suppress stats so the log stays usable.
  `IX_QUIET=1` is set unconditionally; the Rust-side `[compile_env]`
  scheduler noise adds nothing at this layer.
-/
module
public import Cli
public import Std.Internal.UV.System
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Interpret
public import Ix.Aiur.Protocol
public import Ix.Aiur.Statistics
public import Ix.AssumptionTree
public import Ix.Claim
public import Ix.Common
public import Ix.Benchmark.Results
public import Ix.IxVM
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.KernelCheck
public import Ix.TracingTexray
public import Ix.Meta
public import Ix.Store
public import Ix.Cli.NameResolve

public section

open IxVM.ClaimHarness
open Ix.Cli.NameResolve

namespace Ix.Cli.CheckCmd

def addrOfHex! (label : String) (s : String) : IO Address := do
  match Address.fromString s with
  | some a => pure a
  | none =>
    throw <| IO.userError
      s!"error: {label}: expected 64-char hex (32-byte address), got {s.length}-char {s}"

/-- Load a persisted claim from the content-addressed store and resolve
    every tree root it references. Shared between `ix check --claim`
    and `ix prove --claim`. -/
def loadClaimAndTrees (claimHex : String) :
    IO (Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  let claimAddr ← addrOfHex! "claim" claimHex
  let claimBytes ← StoreIO.toIO (Store.read claimAddr)
  let claim ← IO.ofExcept (Ixon.runGet Ix.Claim.get claimBytes)
  let computed := Address.blake3 (Ix.Claim.ser claim)
  if computed != claimAddr then
    throw <| IO.userError
      s!"error: claim bytes at {claimAddr} re-hash to {computed}"
  let treeRoots : Array Address := match claim with
    | .check _ (some r)        => #[r]
    | .eval _ _ (some r)       => #[r]
    | .checkEnv root none     st => #[root] ++ st.toArray
    | .checkEnv root (some r) st => #[root, r] ++ st.toArray
    | .contains tree _         => #[tree]
    | _                        => #[]
  let mut trees : Std.HashMap Address Ix.AssumptionTree := {}
  for r in treeRoots do
    let tbytes ← StoreIO.toIO (Store.read r)
    let tree ← match Ix.AssumptionTree.de tbytes with
      | .error e => throw <| IO.userError s!"error: tree at {r}: deserialize failed: {e}"
      | .ok t => pure t
    if tree.root != r then
      throw <| IO.userError s!"error: tree stored at {r} has merkle root {tree.root}"
    trees := trees.insert r tree
  return (claim, trees)

/-- Build a `ClaimWitness` for the `verify_claim` entrypoint against
    `Ix.Claim.check addr none` (full transitive typecheck of the
    target's closure). -/
def mkWitness (addr : Address) (ixonEnv : Ixon.Env) :
    IO IxVM.ClaimHarness.ClaimWitness := do
  IO.ofExcept <|
    IxVM.ClaimHarness.buildClaimWitness ixonEnv (Ix.Claim.check addr none)

/-- Compute + emit per-circuit stats. With `statsOut = none` prints to
    stdout; with `some path` redirects stdout to the file for the
    duration of `printStats` so the terminal stays clean. -/
def emitStats (compiled : Aiur.CompiledToplevel)
    (queryCounts : Array Aiur.QueryCount)
    (statsOut : Option String) : IO Unit := do
  let stats := Aiur.computeStats compiled queryCounts
  match statsOut with
  | none => Aiur.printStats stats
  | some path => do
    let handle ← IO.FS.Handle.mk path .write
    let stream := IO.FS.Stream.ofHandle handle
    let old ← IO.setStdout stream
    try Aiur.printStats stats
    finally let _ ← IO.setStdout old

/-- What a single `runOne` invocation is targeting.

    * `addr`: full-closure `Claim.check addr none` — dispatch via
      `checkAddrWithEnv` / `proveAddrWithEnv` (handle required).
    * `shard`: `Claim.checkEnv root none` over `owned` blocks —
      dispatch via `shardCheckWithEnv` / `shardProveWithEnv`
      (handle required).
    * `leanW`: a pre-built `ClaimWitness` — used by `--interp`
      mode and by `--claim <hex>` over a non-`check addr none`
      persisted claim. No envHandle needed.

    The env lives once per CLI invocation in a Rust-owned
    `Aiur.EnvHandle`. Lean threads a `@& EnvHandle` reference
    through every per-target FFI call, eliminating per-call env
    re-parse. -/
inductive Target where
  | addr  (a : Address)
  | shard (owned foreign stubbed : Array Address)
  | leanW (w : IxVM.ClaimHarness.ClaimWitness)

/-- Run a single check claim through the codegen'd IxVM Rust kernel.
    The `envHandle?` is `none` only for `.leanW` targets (`--interp`
    fallback); the addr/shard arms require it. -/
def runCompiled (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String) (useBytecode : Bool)
    (envHandle? : Option Aiur.EnvHandle)
    (target : Target) (label : String) : IO UInt32 := do
  IO.println s!"Typechecking {label}"
  (← IO.getStdout).flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let buildBlob (owned : Array Address) : ByteArray := Id.run do
    let mut blob := ByteArray.empty
    for x in owned do blob := blob ++ x.hash
    pure blob
  let res :=
    match target, envHandle? with
    | .addr a, some envHandle =>
      compiled.bytecode.checkAddrWithEnv funIdx envHandle a.hash useBytecode
    | .shard owned foreign stubbed, some envHandle =>
      compiled.bytecode.shardCheckWithEnv funIdx envHandle
        (buildBlob owned) (buildBlob foreign) (buildBlob stubbed) useBytecode
    | .leanW witness, _ =>
      if useBytecode then
        compiled.bytecode.execute funIdx witness.input witness.inputIOBuffer
      else
        compiled.bytecode.executeIxVM funIdx witness.input witness.inputIOBuffer
    | _, none =>
      .error "internal: addr/shard target with no envHandle"
  match res with
  | .error e =>
    IO.eprintln s!"{label}: IxVM-native Aiur execution error: {e}"
    return 1
  | .ok (_output, _ioBuffer, queryCounts) =>
    if printStats then emitStats compiled queryCounts statsOut
    pure 0

/-- Run a single witness through the Aiur interpreter (richer errors). -/
def runInterp (decls : Aiur.Source.Decls)
    (witness : IxVM.ClaimHarness.ClaimWitness) (label : String) : IO UInt32 := do
  IO.println s!"Interpreting {label}"
  (← IO.getStdout).flush
  let funcName := Aiur.Global.mk witness.funcName
  let inputTypes ← match decls.getByKey funcName with
    | some (.function f) => pure $ f.inputs.map (·.2)
    | _ => IO.eprintln s!"{label}: function not found in decls"; return 1
  let inputs := Aiur.unflattenInputs decls witness.input inputTypes
  match Aiur.runFunction decls funcName inputs witness.inputIOBuffer with
  | (.error e, s) =>
    IO.eprintln s!"{label}: interpreter error:\n{e.ppDeref s.store 1 10}"
    return 1
  | (.ok output, _) =>
    IO.println s!"{label}: {output}"
    pure 0

/-- Shared driver for `ix check` / `ix prove`. Loads either a `.ixe`
    env (with optional `--claim` over a persisted claim, or per-name
    iteration) or the compiled-in Lean env (per-name iteration only),
    constructs each `(Claim, WitnessSource, label)` triple, and
    dispatches to `runOne`. Accumulates failures + prints a `[logTag]`
    summary.

    `runOne` ignores `Claim` for `ix check` (the witness encodes the
    claim digest in its IO buffer); `ix prove` uses it to persist
    the claim alongside the proof wrapper.

    The `WitnessSource` is `Native` (Rust-built witness from a
    `.ixe` path + target addr) whenever both are available and the
    claim is the common `Claim.check addr none` shape — avoids the
    per-byte boxing into `Aiur.G` that dominates wall time on heavy
    claims. Falls back to `Lean` when the env is the compiled-in
    Lean env (no `.ixe` to mmap) or when the persisted `--claim`
    variant isn't `check addr none`. -/
def forEachClaim
    (ixePath : Option String) (claimHex : Option String) (names : List String)
    (keepGoing : Bool) (logTag : String) (forceLeanWitness : Bool)
    (runOne : Ix.Claim → Option Aiur.EnvHandle → Target → String → IO UInt32)
    : IO UInt32 := do
  let mut failures : Array String := #[]
  match ixePath with
  | some path =>
    -- Build the env once for the entire batch. The lazy index parse
    -- runs O(num_consts) once at handle construction; all per-name
    -- FFI calls below share the parsed env (no per-call re-mmap).
    let envHandle ← match Aiur.EnvHandle.fromIxe path with
      | .error e =>
        IO.eprintln s!"EnvHandle.fromIxe {path}: {e}"; return 1
      | .ok h => pure h
    -- We still load a Lean-side Ixon.Env for `resolveIxeAddr` (the
    -- name → address resolution used by `--claim` / per-name modes)
    -- and for the rare non-`check addr none` claim-variant Lean
    -- witness builder. Anon load is lazy zero-copy.
    let bytes ← IO.FS.readBinFile path
    let ixonEnv ← match Ixon.deEnvAnon bytes with
      | .error e =>
        IO.eprintln s!"Failed to deserialize {path}: {e}"; return 1
      | .ok env => pure env
    IO.println s!"Loaded {path}: {ixonEnv.namedCount} named, \
      {ixonEnv.constCount} consts, {ixonEnv.blobCount} blobs"
    if let some hex := claimHex then
      let (claim, trees) ← loadClaimAndTrees hex
      let label := s!"claim {hex}"
      -- Persisted `--claim` may be any `Claim` variant; only the
      -- `check addr none` shape has a Rust-witness fast path today.
      -- Other variants (eval/reveal/contains/checkEnv-with-asm)
      -- still build the witness in Lean. `forceLeanWitness` (set by
      -- `--interp source`) always routes through the Lean witness
      -- path even for the fast-path shape — `.addr` targets are
      -- unreachable from `runInterp`.
      let target : Target ← match claim with
        | .check addr none =>
          if forceLeanWitness then
            let witness ← IO.ofExcept <|
              IxVM.ClaimHarness.buildClaimWitness ixonEnv claim trees
            pure (.leanW witness)
          else pure (.addr addr)
        | _ =>
          let witness ← IO.ofExcept <|
            IxVM.ClaimHarness.buildClaimWitness ixonEnv claim trees
          pure (.leanW witness)
      if (← runOne claim (some envHandle) target label) ≠ 0 then
        failures := failures.push label
    else if names.isEmpty then
      let sorted := ixonEnv.named.toArray.qsort
        (fun a b => toString a.1 < toString b.1)
      for (ixName, named) in sorted do
        let leanName := ixNameToLeanName ixName
        let label := toString leanName
        let claim := Ix.Claim.check named.addr none
        let target : Target ←
          if forceLeanWitness then
            let w ← mkWitness named.addr ixonEnv
            pure (.leanW w)
          else pure (.addr named.addr)
        if (← runOne claim (some envHandle) target label) ≠ 0 then
          failures := failures.push label
          if !keepGoing then break
    else
      for arg in names do
        match resolveIxeAddr ixonEnv arg with
        | none =>
          IO.eprintln s!"{arg} not found in {path}"
          failures := failures.push arg
          if !keepGoing then break
        | some addr =>
          let label := arg
          let claim := Ix.Claim.check addr none
          let target : Target ←
            if forceLeanWitness then
              let w ← mkWitness addr ixonEnv
              pure (.leanW w)
            else pure (.addr addr)
          if (← runOne claim (some envHandle) target label) ≠ 0 then
            failures := failures.push label
            if !keepGoing then break
  | none =>
    if claimHex.isSome then
      IO.eprintln "error: --claim requires --ixe <path>"; return 1
    let env ← get_env!
    -- Compiled-Lean-env path. Builds a per-name Ixon env in Lean
    -- memory, serializes to a byte blob, and constructs an
    -- `EnvHandle` from it. Each name has its own closure-rooted
    -- env, so the handle is rebuilt per name. (The `--ixe` arm
    -- can share one handle across many names; this arm cannot
    -- without a shared-env preprocess pass.)
    let runOneByName (name : Lean.Name) (label : String) : IO UInt32 := do
      let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv name env
      let addr ← IxVM.ClaimHarness.lookupAddr ixonEnv name
      let claim := Ix.Claim.check addr none
      if forceLeanWitness then
        let w ← mkWitness addr ixonEnv
        runOne claim none (.leanW w) label
      else
        let envBytes ← match Ixon.serEnv ixonEnv with
          | .error e => throw (IO.userError s!"serEnv failed for {label}: {e}")
          | .ok b => pure b
        let envHandle ← match Aiur.EnvHandle.fromBytes envBytes with
          | .error e => throw (IO.userError s!"EnvHandle.fromBytes failed for {label}: {e}")
          | .ok h => pure h
        runOne claim (some envHandle) (.addr addr) label
    if names.isEmpty then
      let sorted := env.constants.toList.toArray.qsort
        (fun a b => toString a.1 < toString b.1)
      for (name, _) in sorted do
        let label := toString name
        if (← runOneByName name label) ≠ 0 then
          failures := failures.push label
          if !keepGoing then break
    else
      for arg in names do
        match resolveName env arg with
        | none =>
          IO.eprintln s!"{arg} not found"
          failures := failures.push arg
          if !keepGoing then break
          else continue
        | some name =>
          let label := toString name
          if (← runOneByName name label) ≠ 0 then
            failures := failures.push label
            if !keepGoing then break

  if failures.isEmpty then pure 0
  else
    IO.eprintln s!"[{logTag}] {failures.size} failure(s):"
    for n in failures do IO.eprintln s!"  {n}"
    pure 1

-- Bounds-checked little-endian cursor over a `.ixes` byte buffer. Every read
-- verifies the buffer has enough bytes and returns `.error` on underflow — no
-- `b[p]!` panics on a truncated/malformed manifest.
private abbrev IxesP := StateT (ByteArray × Nat) (Except String)

private def ixesU8 : IxesP UInt8 := do
  let (b, p) ← get
  if h : p < b.size then
    modify (fun _ => (b, p + 1))
    pure b[p]
  else throw "ixes: truncated (expected a byte)"

private def ixesU32 : IxesP UInt32 := do
  let a ← ixesU8; let b ← ixesU8; let c ← ixesU8; let d ← ixesU8
  pure (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24))

private def ixesSkip (n : Nat) : IxesP Unit := do
  let (b, p) ← get
  if p + n ≤ b.size then modify (fun _ => (b, p + n)) else throw s!"ixes: truncated (skip {n})"

private def ixesAddr : IxesP Address := do
  let (b, p) ← get
  if p + 32 ≤ b.size then modify (fun _ => (b, p + 32)); pure ⟨b.extract p (p + 32)⟩
  else throw "ixes: truncated (expected a 32-byte address)"

/-- Parse every shard's owned and stubbed block addresses from a serialized
    `.ixes` manifest (`ShardManifest::to_bytes`, `src/ix/shard.rs`):
    magic(8) ‖ total_cross_ingress(u128) ‖ num_shards(u32) ‖ per shard
    { id(u32) ‖ heartbeats(u64) ‖ own_size(u64) ‖ cross_ingress(u64) ‖
      assumption_root(u8 tag + 32?) ‖ blocks(u32 len + 32·len) ‖
      foreign_blocks(u32 len + 32·len) ‖ stubbed_blocks(u32 len + 32·len) }.

    `stubbed_blocks` are the blocks a shard ingresses as type-only axioms.
    Only the partition can identify them — it comes from the profile's delta
    graph — so they travel in the manifest rather than being re-derived here.
    Bounds-checked: a truncated/malformed file yields `.error`, never a panic. -/
def parseIxesAllShards (bytes : ByteArray) :
    Except String (Array (Array Address × Array Address × Array Address)) :=
  let go : IxesP (Array (Array Address × Array Address × Array Address)) := do
    let m0 ← ixesU8; let m1 ← ixesU8; let m2 ← ixesU8; let m3 ← ixesU8
    if !(m0 == 0x49 && m1 == 0x58 && m2 == 0x45 && m3 == 0x53) then
      throw "not an .ixes file (bad magic)"
    ixesSkip 4    -- rest of the 8-byte magic
    ixesSkip 16   -- total_cross_ingress (u128)
    let n ← ixesU32
    let mut shards : Array (Array Address × Array Address × Array Address) := #[]
    for _ in [0:n.toNat] do
      ixesSkip (4 + 8 + 8 + 8)  -- id + heartbeats + own_size + cross_ingress
      if (← ixesU8) == 1 then ixesSkip 32  -- assumption_root present
      let blen ← ixesU32
      let mut blocks : Array Address := #[]
      for _ in [0:blen.toNat] do
        blocks := blocks.push (← ixesAddr)
      let flen ← ixesU32
      let mut foreign : Array Address := #[]
      for _ in [0:flen.toNat] do
        foreign := foreign.push (← ixesAddr)
      let slen ← ixesU32
      let mut stubbed : Array Address := #[]
      for _ in [0:slen.toNat] do
        stubbed := stubbed.push (← ixesAddr)
      shards := shards.push (blocks, foreign, stubbed)
    pure shards
  go.run' (bytes, 0)

/-- The check-schedule block address of a constant: a projection collapses
    to its SCC/Muts wrapper (`p.block`); everything else is its own block.
    Mirrors `check_schedule_block_addr` (`src/ffi/kernel.rs`). -/
private def blockAddrOf (addr : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .iPrj prj => prj.block
  | .cPrj prj => prj.block
  | .rPrj prj => prj.block
  | .dPrj prj => prj.block
  | _ => addr

/-- Owned constants of a shard: every env constant whose check-schedule block
    is in `blocks`. -/
def ownedConstsForBlocks (ixonEnv : Ixon.Env) (blocks : Array Address) : Array Address := Id.run do
  let blockSet : Std.HashSet Address := blocks.foldl (·.insert ·) {}
  let mut o : Array Address := #[]
  for (addr, lc) in ixonEnv.consts do
    let some c := lc.get? | continue
    if blockSet.contains (blockAddrOf addr c) then o := o.push addr
  return o

/-- The `CheckEnv` claim digest a shard's proof commits to — reconstructed
    deterministically from the env + the shard's owned blocks. Matches the
    digest `prove --shard K` produced, so a proof can be bound to its shard. -/
def shardClaimDigest (ixonEnv : Ixon.Env) (blocks foreign stubbed : Array Address) :
    Except String Address := do
  let (claim, _, _) ← IxVM.ClaimHarness.shardCheckEnvClaim ixonEnv
    (ownedConstsForBlocks ixonEnv blocks) (ownedConstsForBlocks ixonEnv foreign)
    (ownedConstsForBlocks ixonEnv stubbed)
  pure (Address.blake3 (Ix.Claim.ser claim))

/-- Load the `.ixe` env and the `.ixes` shard partition together (each file
    read once). Shared by every manifest-driven shard path. -/
def loadEnvAndShards (manifestPath ixePath : String) :
    IO (Except String (Ixon.Env × Array (Array Address × Array Address × Array Address))) := do
  match parseIxesAllShards (← IO.FS.readBinFile manifestPath) with
  | .error e => return .error s!"manifest parse failed: {e}"
  | .ok shards => match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => return .error s!"deserialize {ixePath} failed: {e}"
    | .ok env => return .ok (env, shards)

/-- Run the shard operation for one shard, given the already-loaded env and the
    shard's owned `blocks`: build the `CheckEnv` witness over the owned consts
    (ingress their closure, skip the frontier) and dispatch `runOne`. -/
def runShardOwned (ixonEnv : Ixon.Env) (blocks foreign stubbed : Array Address)
    (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  let foreignConsts := ownedConstsForBlocks ixonEnv foreign
  let stubs := ownedConstsForBlocks ixonEnv stubbed
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts, {stubs.size} stubbed"
  match IxVM.ClaimHarness.buildShardCheckEnvWitness ixonEnv owned foreignConsts
    stubs with
  | .error e => IO.eprintln s!"shard witness build failed: {e}"; return 1
  | .ok (claim, witness) => runOne claim witness s!"shard {shardK}"

/-- IxVM-native fast path: dispatch through `shardCheckWithEnv` (a
    Rust-owned `EnvHandle` reused across calls). Caller threads in
    the pre-built envHandle so all shards in an all-shards run share
    one env parse. Returns the failure message (`none` = passed) so
    the repair driver can read the kernel's wanted-stub report out of
    it; plain check paths wrap it back into an exit code. -/
def runShardOwnedNativeR (envHandle : Aiur.EnvHandle) (compiled : Aiur.CompiledToplevel)
    (printStats : Bool) (statsOut : Option String) (useBytecode : Bool)
    (ixonEnv : Ixon.Env) (blocks foreign stubbed : Array Address) (shardK : Nat) :
    IO (Option String) := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  let foreignConsts := ownedConstsForBlocks ixonEnv foreign
  let stubs := ownedConstsForBlocks ixonEnv stubbed
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts, {stubs.size} stubbed"
  let label := s!"shard {shardK}"
  IO.println s!"Typechecking {label}"
  (← IO.getStdout).flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let mut blob := ByteArray.empty
  for a in owned do
    blob := blob ++ a.hash
  let mut foreignBlob := ByteArray.empty
  for a in foreignConsts do
    foreignBlob := foreignBlob ++ a.hash
  let mut stubBlob := ByteArray.empty
  for a in stubs do
    stubBlob := stubBlob ++ a.hash
  match compiled.bytecode.shardCheckWithEnv funIdx envHandle blob foreignBlob
    stubBlob useBytecode with
  | .error e =>
    IO.eprintln s!"{label}: IxVM-native shard check error: {e}"
    return some e
  | .ok (_output, _ioBuffer, queryCounts) =>
    if printStats then emitStats compiled queryCounts statsOut
    pure none

def runShardOwnedNative (envHandle : Aiur.EnvHandle) (compiled : Aiur.CompiledToplevel)
    (printStats : Bool) (statsOut : Option String) (useBytecode : Bool)
    (ixonEnv : Ixon.Env) (blocks foreign stubbed : Array Address) (shardK : Nat) :
    IO UInt32 := do
  match ← runShardOwnedNativeR envHandle compiled printStats statsOut useBytecode
      ixonEnv blocks foreign stubbed shardK with
  | none => pure 0
  | some _ => pure 1

/-- Manifest-driven check/prove of one shard `shardK` of the partition. -/
def runShardCheckManifest (manifestPath ixePath : String) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some (blocks, foreign, stubbed) =>
      runShardOwned ixonEnv blocks foreign stubbed shardK runOne

/-- IxVM-native shard check, single shard. Builds an `EnvHandle`
    once for this one call.

    `benchJson = (out, rowName)` reports the check as a benchmark row
    (the `aiur-shard` bench backend's per-shard spawn): `execute-time`
    windows the check itself — the env parse and `EnvHandle` build are
    excluded, so the measure tracks the kernel, not the loader — while
    `peak-rss` is the process tree's absolute high-water (the parsed
    env sits in the baseline, matching the ooc rows' semantics). -/
def runShardCheckManifestNative (manifestPath ixePath : String) (shardK : Nat)
    (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String) (useBytecode : Bool)
    (benchJson : Option (String × String) := none) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some (blocks, foreign, stubbed) =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
        | .ok h => pure h
      if benchJson.isSome then
        TracingTexray.startSampler
        TracingTexray.resetPeakTreeRss
      let start ← IO.monoMsNow
      let rc ← runShardOwnedNative envHandle compiled printStats statsOut
        useBytecode ixonEnv blocks foreign stubbed shardK
      if let some (out, rowName) := benchJson then
        if rc == 0 then
          let secs := ((← IO.monoMsNow) - start).toFloat / 1000.0
          let peakRss ← TracingTexray.peakTreeRssBytes
          Ix.Benchmark.Results.writeRow out rowName "ok"
            [ ("execute-time", Ix.Benchmark.Results.jsonRound 3 secs)
            , ("peak-rss", Lean.toJson peakRss) ]
      return rc

/-- Coverage check over already-loaded env + shards: every constant's
    check-schedule block is owned by **exactly one** shard. That is the whole
    soundness condition for the check case — each constant is type-checked
    once, and every shard's frontier (closure minus owned) is therefore owned
    (checked) by some other shard. Prints the per-shard report; returns whether
    the partition is a valid disjoint cover (no block owned by two shards, no
    constant whose block no shard owns). -/
def shardsCover (ixonEnv : Ixon.Env)
    (shards : Array (Array Address × Array Address × Array Address)) : IO Bool := do
  -- block → shard, detecting blocks claimed by more than one shard.
  let mut blockToShard : Std.HashMap Address Nat := {}
  let mut dup : Nat := 0
  for ((blocks, _, _), k) in shards.mapIdx (fun k b => (b, k)) do
    for blk in blocks do
      match blockToShard.get? blk with
      | some _ => dup := dup + 1
      | none => blockToShard := blockToShard.insert blk k
  -- assign every const to a shard via its block; count + detect unowned.
  let mut counts : Array Nat := Array.replicate shards.size 0
  let mut unowned : Nat := 0
  for (addr, lc) in ixonEnv.consts do
    let some c := lc.get? | continue
    match blockToShard.get? (blockAddrOf addr c) with
    | some k => counts := counts.modify k (· + 1)  -- total: no-op if out of range
    | none => unowned := unowned + 1
  IO.println s!"[shards] {shards.size} shards, {ixonEnv.consts.size} consts"
  for ((blocks, _, stubbed), k) in shards.mapIdx (fun k b => (b, k)) do
    IO.println s!"  shard {k}: {blocks.size} blocks ({stubbed.size} stubbed), \
      {(counts[k]?).getD 0} consts"
  if dup != 0 then
    IO.eprintln s!"[shards] FAIL: {dup} block(s) owned by >1 shard (not disjoint)"
  if unowned != 0 then
    IO.eprintln s!"[shards] FAIL: {unowned} const(s) with no owning shard (coverage gap)"
  let ok := dup == 0 && unowned == 0
  if ok then
    IO.println s!"[shards] OK: partition covers all {ixonEnv.consts.size} consts, disjoint"
  pure ok

/-- IxVM-native check over EVERY shard. Builds the `EnvHandle` ONCE
    and shares it across every shard's FFI call (no per-shard
    re-mmap). Coverage-gates the manifest before running any shard —
    exit 0 has to mean "every env const was checked by some shard",
    same soundness contract as `runShardCheckAll`. -/
def runShardManifestAllNative (manifestPath ixePath : String) (jobs? : Option Nat)
    (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String) (useBytecode : Bool) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    if !(← shardsCover ixonEnv shards) then return 1
    let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
      | .ok h => pure h
    let maxJobs := max 1 (jobs?.getD shards.size)
    let mut rc : UInt32 := 0
    for chunk in (shards.mapIdx (fun k b => (b, k))).toList.toChunks maxJobs do
      let tasks ← chunk.mapM fun ((blocks, foreign, stubbed), k) =>
        IO.asTask (prio := .dedicated)
          (runShardOwnedNative envHandle compiled printStats statsOut useBytecode
            ixonEnv blocks foreign stubbed k)
      for t in tasks do
        match t.get with
        | .ok r => if r != 0 then rc := 1
        | .error e => IO.eprintln s!"shard check task failed: {e}"; rc := 1
    pure rc

/-- Extract the kernel's wanted-stub reports from a shard failure message.
    Two forms, possibly both present:
    - `... invalid IO key: channel 98, key <64-hex> ...` — the Proj-site
      abort names exactly one address;
    - `...; wanted stubs: <64-hex>,<64-hex>,...` — the def-eq want log,
      appended by the FFI from IO channel 97 on failure. -/
def extractWantedStubs (msg : String) : List Address :=
  let projSite : List Address :=
    match (msg.splitOn "channel 98, key ")[1]? with
    | none => []
    | some tail => (Address.fromString (tail.take 64).toString).toList
  let defEqLog : List Address :=
    match (msg.splitOn "wanted stubs: ")[1]? with
    | none => []
    | some rest =>
      (rest.splitOn ",").filterMap fun h =>
        Address.fromString (h.take 64).toString
  projSite ++ defEqLog

/-- The escalation retry driver (`ix check --ixes --repair`).

    Replay divergence — the Aiur kernel reducing where the touch-graph
    recording short-circuited, and jamming on a stub — is only
    discoverable by running a shard, so repair is a fixpoint loop:

    1. pack the manifest from the profile at the given budget;
    2. check every shard (concurrently, `--jobs`-capped);
    3. escalate exactly what failed: a failure carrying the kernel's
       wanted-stub report promotes THAT block alone (`K:+HEX`,
       constant-precision, ~KB of extra ingress); one without a report —
       or one that repeats a report already granted — takes a
       whole-frontier promotion round (`K:N`, ~1.5x union bytes);
    4. repack with the accumulated spec and recheck only the escalated
       shards — untouched shards' sets are byte-identical across regens
       (the partition is deterministic in profile + budget);
    5. repeat until green or `maxIters`.

    The ladder's top rung is full closure (the original, known-correct
    semantics), so escalation always terminates; `maxIters` merely caps
    how much of the ladder one run climbs. -/
def runShardRepair (ixprofPath manifestPath ixePath : String)
    (maxRam balancePct : Nat) (jobs? : Option Nat) (maxIters : Nat)
    (compiled : Aiur.CompiledToplevel) (useBytecode : Bool) : IO UInt32 := do
  let regen (spec : String) : IO Unit :=
    Ix.KernelCheck.rsShardEspCapFFI ixprofPath "0" (toString maxRam)
      (toString balancePct) "1" manifestPath "aiur" spec
  IO.println s!"[repair] packing {ixprofPath} at --max-ram {maxRam} → {manifestPath}"
  regen ""
  let ixonEnv ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => IO.eprintln s!"env parse failed: {e}"; return 1
    | .ok env => pure env
  let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
    | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
    | .ok h => pure h
  let mut rounds : Std.HashMap Nat Nat := {}
  let mut adds : Std.HashMap Nat (Array String) := {}
  -- `pending = none` means "check everything" (first iteration).
  let mut pending : Option (List Nat) := none
  for iter in [0:maxIters + 1] do
    let shards ← match parseIxesAllShards (← IO.FS.readBinFile manifestPath) with
      | .error e => IO.eprintln s!"manifest parse failed: {e}"; return 1
      | .ok s => pure s
    if iter == 0 then
      if !(← shardsCover ixonEnv shards) then return 1
    let targets := pending.getD (List.range shards.size)
    let maxJobs := max 1 (jobs?.getD targets.length)
    let mut failures : Array (Nat × String) := #[]
    for chunk in targets.toChunks maxJobs do
      let tasks ← chunk.mapM fun k =>
        IO.asTask (prio := .dedicated) do
          match shards[k]? with
          | none => pure (k, some s!"shard {k} out of range")
          | some (blocks, foreign, stubbed) =>
            pure (k, ← runShardOwnedNativeR envHandle compiled false none
              useBytecode ixonEnv blocks foreign stubbed k)
      for t in tasks do
        match t.get with
        | .ok (k, some e) => failures := failures.push (k, e)
        | .ok (_, none) => pure ()
        | .error e => IO.eprintln s!"shard task failed: {e}"; return 1
    if failures.isEmpty then
      let mut escalated : Array String := #[]
      for (k, n) in rounds.toList do
        escalated := escalated.push s!"{k}:{n}r"
      for (k, hs) in adds.toList do
        escalated := escalated.push s!"{k}:+{hs.size}"
      IO.println s!"[repair] all {shards.size} shards green after {iter} escalation(s); \
        escalated: {if escalated.isEmpty then "none" else String.intercalate ", " escalated.toList}"
      return 0
    if iter == maxIters then
      IO.eprintln s!"[repair] {failures.size} shard(s) still failing after {maxIters} iteration(s): \
        {failures.toList.map (·.1)}"
      return 1
    for (k, msg) in failures do
      -- Wanted-stub reports escalate with constant precision; when every
      -- report is one already granted the precise rung has stalled, so
      -- take the blunt one. Reported addresses are constants; promote
      -- their HOME BLOCKS (projections live in their parent's block).
      let wantedBlocks : List String :=
        ((extractWantedStubs msg).filterMap fun addr => do
          let lc ← ixonEnv.consts.get? addr
          let c ← lc.get?
          pure (toString (blockAddrOf addr c))).eraseDups
      let granted := (adds.get? k).getD #[]
      let fresh := wantedBlocks.filter (fun h => !granted.contains h)
      if fresh.isEmpty then
        rounds := rounds.insert k ((rounds.get? k).getD 0 + 1)
        let why := if wantedBlocks.isEmpty then "no wanted-stub report"
          else "every want already granted"
        IO.println s!"[repair] shard {k}: {why}, \
          promoting whole frontier (round {(rounds.get? k).getD 0})"
      else
        adds := adds.insert k (granted ++ fresh.toArray)
        IO.println s!"[repair] shard {k}: wants \
          {String.intercalate ", " (fresh.map (fun h => (h.take 12).toString))}…, shipping whole"
    let mut parts : Array String := #[]
    for (k, n) in rounds.toList do
      if n > 0 then parts := parts.push s!"{k}:{n}"
    for (k, hs) in adds.toList do
      for h in hs do
        parts := parts.push s!"{k}:+{h}"
    regen (String.intercalate "," parts.toList)
    pending := some (failures.toList.map (·.1))
  return 1

/-- Run the shard operation over EVERY shard — the whole-partition behavior of
    `--ixes` with no `--shard` (used by `prove`). Loads the env once. Returns 1
    if any shard fails, else 0. -/
def runShardManifestAll (manifestPath ixePath : String)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    let mut rc : UInt32 := 0
    for ((blocks, foreign, stubbed), k) in shards.mapIdx (fun k b => (b, k)) do
      if (← runShardOwned ixonEnv blocks foreign stubbed k runOne) != 0 then rc := 1
    pure rc

/-- Check EVERY shard of the partition concurrently (shards are independent
    bytecode runs) after verifying coverage — the whole-partition behavior of
    `check --ixes` with no `--shard`. At most `jobs` shards run at once
    (`none` ⇒ all of them); cap it to bound peak RAM, since each in-flight
    shard's IO buffer re-ingests its whole closure. Returns 1 on a coverage gap
    or any shard failure. -/
def runShardCheckAll (manifestPath ixePath : String) (jobs? : Option Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let (ixonEnv, shards) ← match (← loadEnvAndShards manifestPath ixePath) with
    | .error e => IO.eprintln e; return 1
    | .ok r => pure r
  if !(← shardsCover ixonEnv shards) then return 1
  -- The env + compiled toplevel are read-only, so each shard runs on its own
  -- dedicated task; chunk by `jobs` to cap the number in flight at once.
  let maxJobs := max 1 (jobs?.getD shards.size)
  let mut rc : UInt32 := 0
  for chunk in (shards.mapIdx (fun k b => (b, k))).toList.toChunks maxJobs do
    let tasks ← chunk.mapM fun ((blocks, foreign, stubbed), k) =>
      IO.asTask (prio := .dedicated)
        (runShardOwned ixonEnv blocks foreign stubbed k runOne)
    for t in tasks do
      match t.get with
      | .ok r => if r != 0 then rc := 1
      | .error e => IO.eprintln s!"shard check task failed: {e}"; rc := 1
  pure rc

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  -- Always silence the Rust-side `[compile_env]` progress logs. The
  -- per-name labels + stats are signal enough at this layer.
  Std.Internal.UV.System.osSetenv "IX_QUIET" "1"
  let interpMode : Option String := (p.flag? "interp").map (·.as! String)
  let interpSource := interpMode == some "source"
  let useBytecode := interpMode == some "bytecode"
  match interpMode with
  | none | some "source" | some "bytecode" => pure ()
  | some other =>
    IO.eprintln s!"error: --interp expects \"source\" or \"bytecode\", got \"{other}\""
    return 1
  let keepGoing := p.hasFlag "keep-going"
  let statsOut : Option String :=
    (p.flag? "stats-out").map (·.as! String)
  let ixePath : Option String :=
    (p.flag? "ixe").map (·.as! String)
  let claimHex : Option String :=
    (p.flag? "claim").map (·.as! String)
  let names := (p.variableArgsAs! String).toList
  let ixesPath := (p.flag? "ixes").map (·.as! String)
  let shardK := (p.flag? "shard").map (·.as! Nat)
  -- a single targeted constant, a `--claim`, or a single shard each print
  -- per-circuit stats; whole-env / whole-partition iteration suppresses them.
  let printStats := names.length == 1 || claimHex.isSome || (ixesPath.isSome && shardK.isSome)
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  -- `runOne` consumes `(claim, envHandle?, target, label)`. For the
  -- codegen path it dispatches via `runCompiled`. For `--interp`
  -- it builds a `ClaimWitness` from the target — `.leanW` is
  -- already a witness; `.addr` would require running the Rust
  -- witness builder Lean-side, which `--interp` is meant to
  -- bypass. So `--interp` rejects `.addr`/`.shard` targets here;
  -- the legacy `runShardCheckManifest` path is used for `--interp`
  -- shard mode.
  let runOne : Ix.Claim → Option Aiur.EnvHandle → Target → String → IO UInt32 ←
    if interpSource then do
      let decls ← match toplevel.mkDecls with
        | .error e => IO.eprintln s!"mkDecls failed: {e}"; return 1
        | .ok d => pure d
      let go (_ : Ix.Claim) (_ : Option Aiur.EnvHandle) (target : Target)
          (label : String) : IO UInt32 :=
        match target with
        | .leanW w => runInterp decls w label
        | _ => do
          IO.eprintln s!"{label}: --interp requires a Lean witness; \
            addr/shard targets unreachable here"
          pure 1
      pure go
    else do
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      let go (_ : Ix.Claim) (envHandle? : Option Aiur.EnvHandle) (target : Target)
          (label : String) : IO UInt32 :=
        runCompiled compiled printStats statsOut useBytecode envHandle? target label
      pure go
  -- Repair mode: pack + check + escalate to a green partition. Needs the
  -- profile and budget so manifest regeneration is deterministic.
  if p.hasFlag "repair" then
    match ixePath, ixesPath, (p.flag? "ixprof").map (·.as! String),
          (p.flag? "max-ram").map (·.as! Nat) with
    | some ixe, some manifest, some ixprof, some maxRam =>
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      let balance := ((p.flag? "balance").map (·.as! Nat)).getD 5
      let maxIters := ((p.flag? "max-rounds").map (·.as! Nat)).getD 8
      return (← runShardRepair ixprof manifest ixe maxRam balance
        ((p.flag? "jobs").map (·.as! Nat)) maxIters compiled useBytecode)
    | _, _, _, _ =>
      IO.eprintln "error: --repair needs --ixe, --ixes (output path), --ixprof and --max-ram"
      return 1
  match ixePath, ixesPath, shardK with
  | some ixe, some manifest, some k =>
    if interpSource then
      return (← runShardCheckManifest manifest ixe k
        (fun c w l => runOne c none (.leanW w) l))
    else do
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      let benchJson := (p.flag? "json").map fun f =>
        ((f.as! String),
         ((p.flag? "json-name").map (·.as! String)).getD s!"shard-{k}")
      return (← runShardCheckManifestNative manifest ixe k compiled printStats
        statsOut useBytecode benchJson)
  | some ixe, some manifest, none   =>
    if interpSource then
      return (← runShardCheckAll manifest ixe ((p.flag? "jobs").map (·.as! Nat))
        (fun c w l => runOne c none (.leanW w) l))
    else do
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      return (← runShardManifestAllNative manifest ixe
        ((p.flag? "jobs").map (·.as! Nat)) compiled printStats statsOut useBytecode)
  | _, _, _ =>
    forEachClaim ixePath claimHex names keepGoing "check" interpSource runOne

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Typecheck Lean / `.ixe` constants through the IxVM Aiur kernel"

  FLAGS:
    interp : String;        "Use an interpreter instead of the codegen'd IxVM Rust kernel. Modes: `source` = Aiur source interpreter (richer per-execution error diagnostics, slowest); `bytecode` = generic Aiur bytecode interpreter (skips the regen + cargo rebuild cycle when iterating on `Ix/IxVM/*.lean`). Omit the flag entirely for the native codegen kernel."
    "keep-going";           "Continue past failures and report them at the end instead of halting on the first."
    "ixe"       : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim"     : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, runs the `verify_claim` entrypoint once over the claim's witness against the `--ixe` env (single execution, skips per-const iteration)."
    "stats-out" : String;   "Redirect the per-circuit statistics dump to this file (only used when exactly one constant is targeted)."
    "ixes"      : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: check the constants owned by shard K (ingress their closure, skip the frontier). Without --shard: check every shard of the partition concurrently, after a coverage check."
    "shard"     : Nat;      "0-based shard index K (with --ixe + --ixes): check the constants owned by shard K of the manifest's partition."
    "jobs"      : Nat;      "Max shards to check concurrently when checking a whole partition (--ixes without --shard). Default: all at once. Lower it to bound peak RAM — each in-flight shard re-ingests its closure into its own IO buffer."
    "repair";               "Escalation retry driver: pack --ixprof at --max-ram into --ixes, check every shard, escalate exactly what failed (the kernel's wanted-stub report promotes one named block; otherwise a whole-frontier round), repack and recheck only the escalated shards, until green or --max-rounds."
    "ixprof"    : String;   "Path to the .ixprof (with --repair): the profile the manifest is packed from."
    "max-ram"   : Nat;      "Per-shard host-RAM budget in GiB (with --repair), as in `ix shard --max-ram`."
    balance     : Nat;      "Packing balance tolerance percent (with --repair; default 5)."
    "max-rounds": Nat;      "Escalation iterations before giving up (with --repair; default 8). Divergence is discovered one failure point at a time, so a shard can need several targeted iterations."
    json        : String;   "Benchmark results JSON accumulator (single-shard mode only): append an `execute-time`/`peak-rss` row for the checked shard. Used by `ix bench run --backend aiur-shard`."
    "json-name" : String;   "Row name for --json (default: shard-<K>)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted)."
]

end
