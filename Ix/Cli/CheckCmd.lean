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
public import Ix.Claim
public import Ix.Common
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.IxVM.ClaimHarness
public import Ix.Ixon
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
    * `leanW`: a pre-built `ClaimWitness` — used by `--interp`
      mode and by `--claim <hex>` over a non-`check addr none`
      persisted claim. No envHandle needed.

    The env lives once per CLI invocation in a Rust-owned
    `Aiur.EnvHandle`. Lean threads a `@& EnvHandle` reference
    through every per-target FFI call, eliminating per-call env
    re-parse. -/
inductive Target where
  | addr  (a : Address)
  | leanW (w : IxVM.ClaimHarness.ClaimWitness)

/-- Run a single check claim through the codegen'd IxVM Rust kernel.
    The `envHandle?` is `none` only for `.leanW` targets (`--interp`
    fallback); the addr arm requires it. -/
def runCompiled (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String) (useBytecode : Bool)
    (envHandle? : Option Aiur.EnvHandle)
    (target : Target) (label : String) : IO UInt32 := do
  IO.println s!"Typechecking {label}"
  (← IO.getStdout).flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let res :=
    match target, envHandle? with
    | .addr a, some envHandle =>
      compiled.bytecode.checkAddrWithEnv funIdx envHandle a.hash useBytecode
    | .leanW witness, _ =>
      if useBytecode then
        compiled.bytecode.execute funIdx witness.input witness.inputIOBuffer
      else
        compiled.bytecode.executeIxVM funIdx witness.input witness.inputIOBuffer
    | _, none =>
      .error "internal: addr target with no envHandle"
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

/-- One shard row of a parsed `.ixes` manifest: the owned block
    addresses plus the planner's `heartbeats` cost scalar (comparable
    within one manifest). Mirrors `Shard` in
    `crates/kernel/src/shard.rs`. -/
structure IxesShard where
  blocks : Array Address
  heartbeats : Nat

/-- Parse every shard of a serialized `.ixes` manifest
    (`ShardManifest::to_bytes`, `crates/kernel/src/shard.rs`):
    magic("IXES\0\0\0\0", 8 bytes) ‖ total_cross_ingress(u128) ‖
    num_shards(u32) ‖ per shard
    { id(u32) ‖ heartbeats(u64) ‖ own_size(u64) ‖
      cross_ingress(u64) ‖ assumption_root(u8 tag + 32?) ‖
      blocks(u32 len + 32·len) ‖ foreign_blocks(u32 len + 32·len) }.
    Bounds-checked: a truncated/malformed file yields `.error`, never a panic. -/
def parseIxesShards (bytes : ByteArray) : Except String (Array IxesShard) :=
  let go : IxesP (Array IxesShard) := do
    -- The whole 8-byte magic identifies the format; there is no
    -- separate version field (`SHARD_MAGIC` in
    -- `crates/kernel/src/shard.rs` is `b"IXES\0\0\0\0"`, and the Rust
    -- reader compares all 8 bytes).
    let m0 ← ixesU8; let m1 ← ixesU8; let m2 ← ixesU8; let m3 ← ixesU8
    let m4 ← ixesU8; let m5 ← ixesU8; let m6 ← ixesU8; let m7 ← ixesU8
    if !(m0 == 0x49 && m1 == 0x58 && m2 == 0x45 && m3 == 0x53
        && m4 == 0 && m5 == 0 && m6 == 0 && m7 == 0) then
      throw "not an .ixes file (bad magic)"
    ixesSkip 16   -- total_cross_ingress (u128)
    let n ← ixesU32
    let mut shards : Array IxesShard := #[]
    for _ in [0:n.toNat] do
      ixesSkip 4  -- id (u32)
      let heartbeats ← ixesU64
      ixesSkip (8 + 8)  -- own_size + cross_ingress
      if (← ixesU8) == 1 then ixesSkip 32  -- assumption_root present
      let blen ← ixesU32
      let mut blocks : Array Address := #[]
      for _ in [0:blen.toNat] do
        blocks := blocks.push (← ixesAddr)
      ixesSkip ((← ixesU32).toNat * 32)  -- skip foreign_blocks
      shards := shards.push { blocks, heartbeats }
    pure shards
  go.run' (bytes, 0)

/-- The owned block addresses of every shard (cost columns dropped). -/
def parseIxesAllShards (bytes : ByteArray) : Except String (Array (Array Address)) :=
  (parseIxesShards bytes).map (·.map (·.blocks))

/-- The check-schedule block address of a constant. A projection
    collapses to its SCC/Muts wrapper ONLY when its coordinates are
    valid there — the block parses as a Muts, the index is in range,
    and the member kind matches the projection variant (plus ctor index
    range for `cPrj`). A projection's serialized content is exactly its
    coordinates, so validity makes it THE canonical wrapper the block's
    check covers; an invalid projection is its own block, so coverage
    demands a shard own (and check, and reject) it individually.
    Mirrors `canonical_prj_fold` (`src/ffi/kernel.rs`). Public for
    owning-shard lookups outside this module. -/
def blockAddrOf (ixonEnv : Ixon.Env) (addr : Address) (c : Ixon.Constant) : Address :=
  let collapse (block : Address) (idx : UInt64)
      (ok : Ixon.MutConst → Bool) : Address :=
    match (ixonEnv.consts.get? block).bind (·.get?) with
    | some bc =>
      match bc.info with
      | .muts members =>
        match members[idx.toNat]? with
        | some m => if ok m then block else addr
        | none => addr
      | _ => addr
    | none => addr
  match c.info with
  | .iPrj p => collapse p.block p.idx fun | .indc _ => true | _ => false
  | .cPrj p =>
    collapse p.block p.idx fun
      | .indc i => p.cidx.toNat < i.ctors.size
      | _ => false
  | .rPrj p => collapse p.block p.idx fun | .recr _ => true | _ => false
  | .dPrj p => collapse p.block p.idx fun | .defn _ => true | _ => false
  | _ => addr

/-- Materialize a lazy environment constant without erasing its parse error.
    Including the address in the error is important for large `.ixe` files:
    otherwise the failing lazy window is impractical to locate. -/
private def materializeEnvConst (addr : Address) (lc : Ixon.LazyConstant) :
    Except String Ixon.Constant :=
  match lc.get with
  | .ok c => .ok c
  | .error e => .error s!"constant {addr} failed to decode: {e}"

/-- Owned constants of a shard: every env constant whose check-schedule block
    is in `blocks`.

    This is deliberately fail-closed. Determining a constant's canonical
    check-schedule block requires decoding it (in particular for projections),
    so an undecodable constant cannot safely be classified as outside the
    selected shard. Manifest blocks that do not name a canonical block in the
    environment are rejected as well; otherwise they would silently contribute
    no constants to the reconstructed claim. -/
def ownedConstsForBlocks (ixonEnv : Ixon.Env) (blocks : Array Address) :
    Except String (Array Address) := do
  let blockSet : Std.HashSet Address := blocks.foldl (·.insert ·) {}
  let mut envBlocks : Std.HashSet Address := {}
  let mut o : Array Address := #[]
  for (addr, lc) in ixonEnv.consts do
    let c ← materializeEnvConst addr lc
    let block := blockAddrOf ixonEnv addr c
    envBlocks := envBlocks.insert block
    if blockSet.contains block then o := o.push addr
  for block in blocks do
    if !envBlocks.contains block then
      throw s!"manifest block {block} is absent from the environment or is not a canonical check block"
  pure o

/-- Owned constants of EVERY shard, in ONE pass over the environment. Same
    fail-closed rule as `ownedConstsForBlocks`, and the same result per shard,
    but the env is decoded once instead of once per shard — the difference
    between linear and `shards × consts` on a whole-env manifest. -/
def ownedConstsPerShard (ixonEnv : Ixon.Env) (shards : Array (Array Address)) :
    Except String (Array (Array Address)) := do
  -- Fail-closed on a non-disjoint partition too: a block owned by two shards
  -- would otherwise silently land in whichever shard is inserted last, and the
  -- other shard's claim would be reconstructed over too few constants.
  let mut blockToShard : Std.HashMap Address Nat := {}
  for (blocks, k) in shards.mapIdx (fun k blocks => (blocks, k)) do
    for block in blocks do
      if let some j := blockToShard.get? block then
        throw s!"manifest block {block} is owned by both shard {j} and shard {k}"
      blockToShard := blockToShard.insert block k
  let mut envBlocks : Std.HashSet Address := {}
  let mut owned : Array (Array Address) := Array.replicate shards.size #[]
  for (addr, lc) in ixonEnv.consts do
    let c ← materializeEnvConst addr lc
    let block := blockAddrOf ixonEnv addr c
    envBlocks := envBlocks.insert block
    if let some k := blockToShard.get? block then
      owned := owned.modify k (·.push addr)
  for (blocks, k) in shards.mapIdx (fun k blocks => (blocks, k)) do
    for block in blocks do
      if !envBlocks.contains block then
        throw s!"shard {k}: manifest block {block} is absent from the environment or is not a canonical check block"
  pure owned

/-- The `CheckEnv` claim digest a proof over `owned` commits to. Only the
    claim is reconstructed: the witness byte scope the prover also builds is
    not part of the digest, so a verifier must not pay for it. -/
def claimDigestOfOwned (ixonEnv : Ixon.Env) (owned : Array Address) :
    Except String Address := do
  let (claim, _) ← IxVM.ClaimHarness.shardCheckEnvClaimOnly ixonEnv owned
  pure (Address.blake3 (Ix.Claim.ser claim))

/-- The `CheckEnv` claim digest a shard's proof commits to — reconstructed
    deterministically from the env + the shard's owned blocks. Matches the
    digest `prove --shard K` produced, so a proof can be bound to its shard. -/
def shardClaimDigest (ixonEnv : Ixon.Env) (blocks : Array Address) : Except String Address := do
  claimDigestOfOwned ixonEnv (← ownedConstsForBlocks ixonEnv blocks)

/-- Every shard's claim digest, from one pass over the environment.
    `none` for a shard that owns no blocks: such a shard has no `CheckEnv`
    claim (the owned set is empty), contributes nothing to coverage, and so
    requires no proof — the planner does emit them (`ShardManifest::summary`
    reports an `empty=` count). -/
def shardClaimDigests (ixonEnv : Ixon.Env) (shards : Array (Array Address)) :
    Except String (Array (Option Address)) := do
  let owned ← ownedConstsPerShard ixonEnv shards
  owned.mapM fun o =>
    if o.isEmpty then pure none else (some <$> claimDigestOfOwned ixonEnv o)

/-- Check the manifest-to-environment direction without scanning the whole
    environment: every owned block listed by the manifest must be an existing
    canonical check block. The reverse direction (every environment constant
    is owned exactly once) remains `shardsCover`'s responsibility. -/
def validateManifestBlocks (ixonEnv : Ixon.Env) (shards : Array (Array Address)) :
    Except String Unit := do
  for (blocks, k) in shards.mapIdx (fun k blocks => (blocks, k)) do
    for block in blocks do
      let some lc := ixonEnv.consts.get? block
        | throw s!"shard {k}: manifest block {block} is absent from the environment"
      let c ← materializeEnvConst block lc
      let canonical := blockAddrOf ixonEnv block c
      if canonical != block then
        throw s!"shard {k}: manifest block {block} is not a canonical check block (canonical block: {canonical})"

/-- Load the `.ixe` env and the `.ixes` shard partition together (each file
    read once), rejecting a manifest that names blocks outside that env. Shared
    by every manifest-driven shard path. -/
def loadEnvAndShards (manifestPath ixePath : String) :
    IO (Except String (Ixon.Env × Array (Array Address))) := do
  match parseIxesAllShards (← IO.FS.readBinFile manifestPath) with
  | .error e => return .error s!"manifest parse failed: {e}"
  | .ok shards => match Ixon.deEnvAnon (← IO.FS.readBinFile ixePath) with
    | .error e => return .error s!"deserialize {ixePath} failed: {e}"
    | .ok env => match validateManifestBlocks env shards with
      | .error e => return .error s!"manifest/environment mismatch: {e}"
      | .ok () => return .ok (env, shards)

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
    match blockToShard.get? (blockAddrOf ixonEnv addr c) with
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
  let claimHex : Option String :=
    (p.flag? "claim").map (·.as! String)
  let names := (p.variableArgsAs! String).toList
  -- a single targeted constant or a `--claim` prints per-circuit
  -- stats; whole-env iteration suppresses them.
  let printStats := names.length == 1 || claimHex.isSome
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  -- `runOne` consumes `(claim, envHandle?, target, label)`. For the
  -- codegen path it dispatches via `runCompiled`. For `--interp`
  -- it builds a `ClaimWitness` from the target — `.leanW` is
  -- already a witness; `.addr` would require running the Rust
  -- witness builder Lean-side, which `--interp` is meant to
  -- bypass, so `--interp` rejects `.addr` targets here.
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
            addr targets unreachable here"
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
  forEachClaim ixePath claimHex names keepGoing "check" interpSource runOne

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Execute and verify `Ix.Claim`s through the IxVM Aiur kernel: one named constant, every constant of an env, or a persisted claim. Proving lives under `ix prove`."

  FLAGS:
    interp : String;        "Use an interpreter instead of the codegen'd IxVM Rust kernel. Modes: `source` = Aiur source interpreter (richer per-execution error diagnostics, slowest); `bytecode` = generic Aiur bytecode interpreter (skips the regen + cargo rebuild cycle when iterating on `Ix/IxVM/*.lean`). Omit the flag entirely for the native codegen kernel."
    "fail-fast";            "Halt on the first failure (the default; flag accepted for explicitness)."
    "no-fail-fast";         "Continue past failures and report them at the end instead of halting on the first."
    "env"       : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim"     : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, runs the `verify_claim` entrypoint once over the claim's witness against the `--env` env (single execution, skips per-const iteration)."
    "stats-out" : String;   "Redirect the per-circuit statistics dump to this file (only used when exactly one constant is targeted)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted)."
]

end
