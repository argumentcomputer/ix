/-
  `ix check`: execute the IxVM Aiur kernel over a Lean or `.ixe`
  environment, one constant at a time.
  The Rust kernel typechecker that used to live under this name is now `ix check-rs`.

  Usage shape:

      ix check Nat.add_comm                            # from compiled-in Lean env
      ix check --env arena.ixe foo bar baz             # from .ixe, named targets
      ix check --env arena.ixe                         # iterate every named const
      ix check --interp Nat.add_comm                   # Aiur interpreter (richer errors)
      ix check --stats-out STATS Nat.add_comm          # redirect per-circuit stats

  Stats print when exactly one constant is targeted. Multi-target +
  whole-env iteration both suppress stats so the log stays usable.
  The Rust-side `[compile_env]` / `[Env::put]` progress logs are off
  unless `IX_VERBOSE=1`; they add nothing at this layer.
-/
module
public import Cli
public import Ix.Address
public import Ix.Aiur.Compiler
public import Ix.Aiur.Interpret
public import Ix.Aiur.Protocol
public import Ix.Aiur.Statistics
public import Ix.AssumptionTree
public import Ix.Benchmark.Results
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
public import Ix.Meta
public import Ix.Store
public import Ix.TracingTexray
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
    | .checkEnv root none      => #[root]
    | .checkEnv root (some r)  => #[root, r]
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
    IxVM.ClaimHarness.buildClaimWitness ixonEnv (Ix.Claim.check addr none) {}

/-- Compute + emit per-circuit stats. With `statsOut = none` prints to
    stdout; with `some path` redirects stdout to the file for the
    duration of `printStats` so the terminal stays clean.

    Circuit shapes come from the one-shot FFI (`Aiur.circuitShapes`),
    which builds and drops an `AiurSystem` — the check flow never builds
    one otherwise. That cost is paid only when stats are requested. -/
def emitStats (compiled : Aiur.CompiledToplevel)
    (queryCounts : Array Aiur.QueryCount)
    (statsOut : Option String) : IO Unit := do
  let shapes := Aiur.circuitShapes compiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let stats := Aiur.computeStats compiled queryCounts shapes
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
  | shard (owned : Array Address)
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
    | .shard owned, some envHandle =>
      compiled.bytecode.shardCheckWithEnv funIdx envHandle (buildBlob owned) useBytecode
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
      IO.eprintln "error: --claim requires --env <path>"; return 1
    let env ← get_env!
    -- Compiled-Lean-env path. Builds a per-name Ixon env in Lean
    -- memory, serializes to a byte blob, and constructs an
    -- `EnvHandle` from it. Each name has its own closure-rooted
    -- env, so the handle is rebuilt per name. (The `--env` arm
    -- can share one handle across many names; this arm cannot
    -- without a shared-env preprocess pass.)
    let runOneByName (name : Lean.Name) (label : String) : IO UInt32 := do
      -- the kernel env loader: also seeds the constants the kernel fabricates
      -- during reduction (Bool/Nat ctors, String-literal ctor form),
      -- whose bytes must be in ch 2 even when the target's proof body
      -- never references them.
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

private def ixesU64 : IxesP Nat := do
  let mut v : Nat := 0
  for i in [0:8] do
    v := v ||| ((← ixesU8).toNat <<< (8 * i))
  pure v

/-- One shard row of a parsed `.ixes` manifest: the owned block addresses
    plus the planner cost (`ShardCost` in `crates/kernel/src/shard.rs` —
    `costTag` 0 = unknown, 1 = profile heartbeats, 2 = Zisk cost units,
    3 = Aiur fft; `cost` is the scalar, comparable within one manifest). -/
structure IxesShard where
  blocks : Array Address
  costTag : UInt8
  cost : Nat

/-- Parse every shard of a serialized `.ixes` manifest
    (`ShardManifest::to_bytes`, `crates/kernel/src/shard.rs`, format v2):
    magic("IXES\0\0\0" ++ version) ‖ total_cross_ingress(u128) ‖
    num_shards(u32) ‖ per shard
    { id(u32) ‖ cost_tag(u8) ‖ cost(u64) ‖ own_size(u64) ‖
      cross_ingress(u64) ‖ assumption_root(u8 tag + 32?) ‖
      blocks(u32 len + 32·len) ‖ foreign_blocks(u32 len + 32·len) }.
    Bounds-checked: a truncated/malformed file yields `.error`, never a panic. -/
def parseIxesShards (bytes : ByteArray) : Except String (Array IxesShard) :=
  let go : IxesP (Array IxesShard) := do
    let m0 ← ixesU8; let m1 ← ixesU8; let m2 ← ixesU8; let m3 ← ixesU8
    if !(m0 == 0x49 && m1 == 0x58 && m2 == 0x45 && m3 == 0x53) then
      throw "not an .ixes file (bad magic)"
    ixesSkip 3    -- reserved zero bytes of the 8-byte magic
    let version ← ixesU8
    if version != 2 then
      throw s!"unsupported .ixes format version {version} (expected 2) — \
        regenerate the manifest with the current `ix shard`"
    ixesSkip 16   -- total_cross_ingress (u128)
    let n ← ixesU32
    let mut shards : Array IxesShard := #[]
    for _ in [0:n.toNat] do
      ixesSkip 4  -- id
      let costTag ← ixesU8
      let cost ← ixesU64
      ixesSkip (8 + 8)  -- own_size + cross_ingress
      if (← ixesU8) == 1 then ixesSkip 32  -- assumption_root present
      let blen ← ixesU32
      let mut blocks : Array Address := #[]
      for _ in [0:blen.toNat] do
        blocks := blocks.push (← ixesAddr)
      ixesSkip ((← ixesU32).toNat * 32)  -- skip foreign_blocks
      shards := shards.push { blocks, costTag, cost }
    pure shards
  go.run' (bytes, 0)

/-- The owned block addresses of every shard (cost columns dropped). -/
def parseIxesAllShards (bytes : ByteArray) : Except String (Array (Array Address)) :=
  (parseIxesShards bytes).map (·.map (·.blocks))

/-- The check-schedule block address of a constant: a projection collapses
    to its SCC/Muts wrapper (`p.block`); everything else is its own block.
    Mirrors `check_schedule_block_addr` (`src/ffi/kernel.rs`). Public for
    owning-shard lookups outside this module. -/
def blockAddrOf (addr : Address) (c : Ixon.Constant) : Address :=
  match c.info with
  | .iPrj prj => prj.block
  | .cPrj prj => prj.block
  | .rPrj prj => prj.block
  | .dPrj prj => prj.block
  | _ => addr

/-- Owned constants of a shard: every env constant whose check-schedule block
    is in `blocks`.

    Constants whose bytes do not parse are skipped and therefore owned by
    NOBODY. That is safe only because `shardsCover` fails the run when any
    exist, so this is never reached with one present; without that gate a
    silent skip here means a constant no shard ever checks. -/
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
def shardClaimDigest (ixonEnv : Ixon.Env) (blocks : Array Address) : Except String Address := do
  let (claim, _, _) ← IxVM.ClaimHarness.shardCheckEnvClaim ixonEnv (ownedConstsForBlocks ixonEnv blocks)
  pure (Address.blake3 (Ix.Claim.ser claim))

/-- Load the `.ixe` env and the `.ixes` shard partition together (each file
    read once). Shared by every manifest-driven shard path. -/
def loadEnvAndShards (manifestPath ixePath : String) :
    IO (Except String (Ixon.Env × Array (Array Address))) := do
  match parseIxesAllShards (← IO.FS.readBinFile manifestPath) with
  | .error e => return .error s!"manifest parse failed: {e}"
  | .ok shards => match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => return .error s!"deserialize {ixePath} failed: {e}"
    | .ok env => return .ok (env, shards)

/-- Run the shard operation for one shard, given the already-loaded env and the
    shard's owned `blocks`: build the `CheckEnv` witness over the owned consts
    (ingress their closure, skip the frontier) and dispatch `runOne`. -/
def runShardOwned (ixonEnv : Ixon.Env) (blocks : Array Address) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts"
  match IxVM.ClaimHarness.buildShardCheckEnvWitness ixonEnv owned with
  | .error e => IO.eprintln s!"shard witness build failed: {e}"; return 1
  | .ok (claim, witness) => runOne claim witness s!"shard {shardK}"

/-- IxVM-native fast path: dispatch through `shardCheckWithEnv` (a
    Rust-owned `EnvHandle` reused across calls). Caller threads in
    the pre-built envHandle so all shards in an all-shards run share
    one env parse. -/
def runShardOwnedNative (envHandle : Aiur.EnvHandle) (compiled : Aiur.CompiledToplevel)
    (printStats : Bool) (statsOut : Option String) (useBytecode : Bool)
    (ixonEnv : Ixon.Env) (blocks : Array Address) (shardK : Nat) : IO UInt32 := do
  let owned := ownedConstsForBlocks ixonEnv blocks
  IO.println s!"[shard] shard {shardK}: {blocks.size} owned blocks → \
    {owned.size}/{ixonEnv.consts.size} owned consts"
  let label := s!"shard {shardK}"
  IO.println s!"Typechecking {label}"
  (← IO.getStdout).flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let mut blob := ByteArray.empty
  for a in owned do
    blob := blob ++ a.hash
  match compiled.bytecode.shardCheckWithEnv funIdx envHandle blob useBytecode with
  | .error e =>
    IO.eprintln s!"{label}: IxVM-native shard check error: {e}"
    return 1
  | .ok (_output, _ioBuffer, queryCounts) =>
    if printStats then emitStats compiled queryCounts statsOut
    pure 0

/-- Manifest-driven check/prove of one shard `shardK` of the partition. -/
def runShardCheckManifest (manifestPath ixePath : String) (shardK : Nat)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some blocks => runShardOwned ixonEnv blocks shardK runOne

/-- IxVM-native shard check, single shard. Builds an `EnvHandle`
    once for this one call. -/
def runShardCheckManifestNative (manifestPath ixePath : String) (shardK : Nat)
    (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String) (useBytecode : Bool)
    (benchJson : Option (String × String) := none) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some blocks =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
        | .ok h => pure h
      -- `benchJson = (out, rowName)` reports the check as a benchmark
      -- row: `execute-time` windows the check itself — the env parse and
      -- `EnvHandle` build are excluded, so the measure tracks the
      -- kernel, not the loader — while `peak-rss` is the process tree's
      -- absolute high-water (the parsed env sits in the baseline,
      -- matching the ooc rows' semantics).
      if benchJson.isSome then
        TracingTexray.startSampler
        TracingTexray.resetPeakTreeRss
      let start ← IO.monoMsNow
      let rc ← runShardOwnedNative envHandle compiled printStats statsOut
        useBytecode ixonEnv blocks shardK
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
def shardsCover (ixonEnv : Ixon.Env) (shards : Array (Array Address)) : IO Bool := do
  -- block → shard, detecting blocks claimed by more than one shard.
  let mut blockToShard : Std.HashMap Address Nat := {}
  let mut dup : Nat := 0
  for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
    for blk in blocks do
      match blockToShard.get? blk with
      | some _ => dup := dup + 1
      | none => blockToShard := blockToShard.insert blk k
  -- assign every const to a shard via its block; count + detect unowned.
  let mut counts : Array Nat := Array.replicate shards.size 0
  let mut unowned : Nat := 0
  let mut unparsed : Nat := 0
  for (addr, lc) in ixonEnv.consts do
    -- A constant whose bytes do not parse must FAIL the gate, not be
    -- skipped. `.ixe` loading is lazy and `LazyConstant.get?` discards
    -- the error, so such a constant sits in `consts` with its key
    -- present: skipping it assigned it to no shard, counted it as
    -- neither owned nor unowned, and still included it in the "covers
    -- all N consts" total below. It would also enter a referring
    -- shard's frontier, since that admits an edge on key presence
    -- without parsing — an assumption no shard discharges.
    let some c := lc.get? | unparsed := unparsed + 1; continue
    match blockToShard.get? (blockAddrOf addr c) with
    | some k => counts := counts.modify k (· + 1)  -- total: no-op if out of range
    | none => unowned := unowned + 1
  IO.println s!"[shards] {shards.size} shards, {ixonEnv.consts.size} consts"
  for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
    IO.println s!"  shard {k}: {blocks.size} blocks, {(counts[k]?).getD 0} consts"
  if dup != 0 then
    IO.eprintln s!"[shards] FAIL: {dup} block(s) owned by >1 shard (not disjoint)"
  if unowned != 0 then
    IO.eprintln s!"[shards] FAIL: {unowned} const(s) with no owning shard (coverage gap)"
  if unparsed != 0 then
    IO.eprintln s!"[shards] FAIL: {unparsed} const(s) whose bytes do not parse \
      (cannot be assigned to a shard)"
  let ok := dup == 0 && unowned == 0 && unparsed == 0
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
      let tasks ← chunk.mapM fun (blocks, k) =>
        IO.asTask (prio := .dedicated)
          (runShardOwnedNative envHandle compiled printStats statsOut useBytecode ixonEnv blocks k)
      for t in tasks do
        match t.get with
        | .ok r => if r != 0 then rc := 1
        | .error e => IO.eprintln s!"shard check task failed: {e}"; rc := 1
    pure rc

/-- Run the shard operation over EVERY shard — the whole-partition behavior of
    `--shards` with no `--shard` (used by `prove`). Loads the env once. Returns 1
    if any shard fails, else 0. -/
def runShardManifestAll (manifestPath ixePath : String)
    (runOne : Ix.Claim → IxVM.ClaimHarness.ClaimWitness → String → IO UInt32) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    let mut rc : UInt32 := 0
    for (blocks, k) in shards.mapIdx (fun k b => (b, k)) do
      if (← runShardOwned ixonEnv blocks k runOne) != 0 then rc := 1
    pure rc

/-- Check EVERY shard of the partition concurrently (shards are independent
    bytecode runs) after verifying coverage — the whole-partition behavior of
    `check --shards` with no `--shard`. At most `jobs` shards run at once
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
    let tasks ← chunk.mapM fun (blocks, k) =>
      IO.asTask (prio := .dedicated) (runShardOwned ixonEnv blocks k runOne)
    for t in tasks do
      match t.get with
      | .ok r => if r != 0 then rc := 1
      | .error e => IO.eprintln s!"shard check task failed: {e}"; rc := 1
  pure rc

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let interpMode : Option String := (p.flag? "interp").map (·.as! String)
  let interpSource := interpMode == some "source"
  let useBytecode := interpMode == some "bytecode"
  match interpMode with
  | none | some "source" | some "bytecode" => pure ()
  | some other =>
    IO.eprintln s!"error: --interp expects \"source\" or \"bytecode\", got \"{other}\""
    return 1
  let keepGoing := p.hasFlag "no-fail-fast"
  if keepGoing && p.hasFlag "fail-fast" then
    p.printError "error: --fail-fast and --no-fail-fast are mutually exclusive"
    return 1
  let statsOut : Option String :=
    (p.flag? "stats-out").map (·.as! String)
  let ixePath : Option String :=
    (p.flag? "env").map (·.as! String)
  if p.hasFlag "dry-run" && !p.hasFlag "prove" then
    p.printError "error: --dry-run requires --prove (it is the prove \
      pipeline minus the STARKs)"
    return 1
  if p.hasFlag "execute" && p.hasFlag "prove" then
    p.printError "error: --execute and --prove are mutually exclusive \
      (--execute is execute-ONLY; --prove implies execution)"
    return 1
  if p.hasFlag "execute" || p.hasFlag "prove" then
    -- Whole-env pipelines over the shared record. --execute: parallel
    -- execution of every block's claim, no partition, no manifest, no
    -- prove concerns. --prove: the same execution, cut into prove-sized
    -- segments that each proceed straight to a verified STARK.
    let some ixe := ixePath | do
      let flag := if p.hasFlag "prove" then "prove" else "execute"
      p.printError s!"error: --{flag} requires --env"
      return 1
    let toplevel ← match IxVM.ixVM with
      | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
      | .ok t => pure t
    let compiled ← match toplevel.compile with
      | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
      | .ok c => pure c
    let segFunIdx ← match compiled.getFuncIdx `verify_segment with
      | some i => pure i
      | none => IO.eprintln "error: verify_segment missing"; return 1
    let blockFunIdx ← match compiled.getFuncIdx `verify_block with
      | some i => pure i
      | none => IO.eprintln "error: verify_block missing"; return 1
    let envHandle ← match Aiur.EnvHandle.fromIxe ixe with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixe}: {e}"; return 1
      | .ok h => pure h
    -- Closure roots: with --execute, positional names restrict the run
    -- to their dependency closure (resolved here to hex addresses the
    -- executor filters its schedule by). --prove stays whole-env: its
    -- budget geometry belongs to the env, and partial proving goes
    -- through a manifest (--shards) or an extracted env.
    let rootNames := (p.variableArgsAs! String).toList
    if p.hasFlag "prove" && !rootNames.isEmpty then
      p.printError "error: --prove takes no names (it proves the whole \
        env or a --shards manifest); to prove a closure, extract it first \
        (`ix shard extract`)"
      return 1
    let mut rootsCsv := ""
    if !rootNames.isEmpty then
      let ixonEnv ← match Ixon.deEnvAnon (← IO.FS.readBinFile ixe) with
        | .error e => IO.eprintln s!"Failed to deserialize {ixe}: {e}"; return 1
        | .ok env => pure env
      let mut addrs : List String := []
      for arg in rootNames do
        match resolveIxeAddr ixonEnv arg with
        | none => IO.eprintln s!"{arg} not found in {ixe}"; return 1
        | some addr => addrs := toString addr :: addrs
      rootsCsv := String.intercalate "," addrs.reverse
    -- Determinism debugging: map function indices (as the executor's
    -- per-map count dump prints them) back to kernel names.
    if (← IO.getEnv "IX_DUMP_FUN_NAMES").isSome then
      let reverseMap := compiled.nameMap.fold
        (init := (∅ : Std.HashMap Aiur.Bytecode.FunIdx String))
        fun acc global idx =>
          if !acc.contains idx then acc.insert idx (toString global) else acc
      for i in [:compiled.bytecode.functions.size] do
        IO.println s!"fn {i} {reverseMap[i]?.getD "<anon>"}"
    let workers := (p.flag? "jobs").map (·.as! Nat) |>.getD 0
    -- `--json` reports the run as a benchmark row: `execute-time`
    -- windows the parallel check itself — the kernel compile and
    -- `EnvHandle` build are excluded, so the measure tracks the kernel,
    -- not the loader — while `peak-rss` is the process tree's absolute
    -- high-water (covers the worker pool).
    let benchJson := (p.flag? "json").map fun f =>
      (f.as! String,
       ((p.flag? "json-name").map (·.as! String)).getD "execute")
    if benchJson.isSome then
      TracingTexray.startSampler
      TracingTexray.resetPeakTreeRss
    let start ← IO.monoMsNow
    let run : Except String Unit ← do
      if p.hasFlag "prove" then
        let aiurSystem := Aiur.AiurSystem.build compiled.bytecode
          Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
        -- With a manifest: the plan → exact-measure → fixup → prove
        -- pipeline (shards from the static planner, every prove gated
        -- on the exact post-execution RAM model; --dry-run measures,
        -- optionally rewriting a split/merged manifest to --fixup-out).
        match (p.flag? "shards").map (·.as! String) with
        | some manifest =>
          pure <| aiurSystem.executeManifestProveWithEnv segFunIdx
            blockFunIdx envHandle (toString workers) manifest
            (((p.flag? "shard").map (·.as! Nat)).map toString |>.getD "")
            (if p.hasFlag "dry-run" then "1" else "0")
            (((p.flag? "fixup-out").map (·.as! String)).getD "")
        | none =>
          pure <| aiurSystem.executeEnvProveWithEnv segFunIdx blockFunIdx
            envHandle (toString workers) (if keepGoing then "0" else "1")
            (if p.hasFlag "dry-run" then "1" else "0") ""
      else
        pure <| Aiur.Bytecode.Toplevel.executeEnvWithEnv compiled.bytecode
          segFunIdx blockFunIdx envHandle (toString workers)
          (if keepGoing then "0" else "1") rootsCsv
    match run with
    | .error e => IO.eprintln s!"execute failed: {e}"; return 1
    | .ok () =>
      let ms := (← IO.monoMsNow) - start
      IO.println s!"execute: OK in {ms} ms"
      if let some (out, rowName) := benchJson then
        let peakRss ← TracingTexray.peakTreeRssBytes
        Ix.Benchmark.Results.writeRow out rowName "ok"
          [ ("execute-time",
             Ix.Benchmark.Results.jsonRound 3 (ms.toFloat / 1000.0))
          , ("peak-rss", Lean.toJson peakRss) ]
      return 0
  let claimHex : Option String :=
    (p.flag? "claim").map (·.as! String)
  let names := (p.variableArgsAs! String).toList
  let ixesPath := (p.flag? "shards").map (·.as! String)
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
        (f.as! String,
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
    "fail-fast";            "Halt on the first failure (the default; flag accepted for explicitness)."
    "no-fail-fast";         "Continue past failures and report them at the end instead of halting on the first."
    "env"       : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "prove";                "Full proving (requires --env; mutually exclusive with --execute). Without --shards: execute every block's claim into a shared record, cut prove-sized segments at the RAM model's budget line, and prove+verify each sealed segment directly (multi-claim STARK — the record IS the witness, no re-execution); single claims over the prove budget are executed, measured, and reported UNPROVEN rather than failing the run. With --shards: prove the manifest — each shard executes into its own record, seals, is gated on its EXACT measured peak, and is proven; a shard that measures over budget self-heals (split with the plan's partitioner, halves proven recursively)."
    "dry-run";              "With --prove: the verify-only step — everything except the STARKs. Without --shards: exercise the complete prove-mode geometry (RAM-model cuts, seal acceptance, segment claims) and report every segment's claim count and predicted peak prove RSS. With --shards: re-execute each shard standalone and measure its EXACT peak against the budget — certifies a manifest is provable on this box before committing STARK time (see --fixup-out)."
    "execute";              "Execute-only check (requires --env): run every block's check claim — the whole env, or with positional names their dependency closure — through the codegen'd Aiur kernel in parallel over one shared record; no partition, no manifest, no proving. The record is cut and dropped at a measured RAM threshold purely to bound memory; cuts never change what is checked. Reports blocks checked, kernel rejects (named), and total measured FFT cost. --jobs bounds the worker count (default: autoscale); combine with --no-fail-fast to inventory every reject."
    "claim"     : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, runs the `verify_claim` entrypoint once over the claim's witness against the `--env` env (single execution, skips per-const iteration)."
    "stats-out" : String;   "Redirect the per-circuit statistics dump to this file (only used when exactly one constant is targeted)."
    "shards"    : String;   "Path to a `.ixes` shard manifest (with --env), e.g. from `ix shard`. With --prove: prove the manifest's shards (see --prove). With --shard K: check the constants owned by shard K (ingress their closure, skip the frontier). Without --shard: check every shard of the partition concurrently, after a coverage check."
    "shard"     : Nat;      "0-based shard index K (with --env + --shards): operate on shard K of the manifest's partition only."
    "fixup-out" : String;   "With --prove --shards --dry-run (all shards): after measuring every shard's EXACT prove RAM, write a fixed-up manifest here — shards over budget split in two, consecutive underfilled shards merged while the sum of measured peaks stays under budget."
    "jobs"      : Nat;      "Max shards to check concurrently when checking a whole partition (--shards without --shard). Default: all at once. Lower it to bound peak RAM — each in-flight shard re-ingests its closure into its own IO buffer."
    json        : String;   "Benchmark results JSON accumulator (single-shard and --execute modes): append an `execute-time`/`peak-rss` row for the checked shard or whole-env execute."
    "json-name" : String;   "Row name for --json (default: shard-<K>, or `execute` for --execute)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted). With --execute: execute only the named constants' dependency closure."
]

end
