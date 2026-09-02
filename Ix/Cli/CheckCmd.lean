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
public import Ix.Benchmark.Results
public import Ix.KernelCheck
public import Ix.TracingTexray

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

/-- Append per-constant virtual-gas costs from an execution's
    `QueryRecordHandle` to `out`: one `<addr_hex> <vspan> <mult> [name]`
    line per constrained `check_const` query. The address is recovered by
    dereferencing the `Addr` argument — the LAST input slot, since `ci`
    is passed flattened by value — through `memory[32]`; `vspan` is the
    constant's standalone check cost within its shard (memo hits replay
    the callee's recorded span). Order-independent within a partition,
    but NOT exact across partitions: a callee owned by a foreign shard
    is assumed rather than replayed, so its span drops out of its
    callers' rows (measured: ~10% of a 360-const fixture's rows shift
    between a 1-shard and a 4-shard partition, a few by >2x). Schedule
    off a profile measured under the partition being scheduled.
    Requires the execution to have run with `profile := true`, else
    every span reads 0. -/
def dumpProfile (compiled : Aiur.CompiledToplevel)
    (record : Aiur.QueryRecordHandle) (out : String)
    (nameOf : Address → Option Ix.Name) : IO Unit := do
  let some idx := compiled.getFuncIdx `check_const
    | IO.eprintln "--profile: no `check_const` in compiled toplevel"
  let addrPos := compiled.bytecode.functions[idx]!.layout.inputSize - 1
  let mut block := ""
  for i in [0 : record.fnLen idx] do
    let mult := record.fnMult idx i
    if mult != 0 then
      let key := record.fnKey idx i
      if let some addrG := key[addrPos]? then
        let limbs := record.memKey 32 addrG.val.toNat
        let addr : Address := ⟨.mk <| limbs.map fun g => g.val.toUInt8⟩
        let name := (nameOf addr).map (s!" {·}") |>.getD ""
        block := block ++ s!"{addr} {record.fnVspan idx i} {mult}{name}\n"
  -- One buffered write per execution: concurrent shard tasks (whole
  -- partition mode) append to the same file, and a single O_APPEND
  -- write keeps each shard's block from interleaving mid-line.
  let h ← IO.FS.Handle.mk out .append
  h.putStr block
  h.flush

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

/-- Batch PARALLEL check over one `.ixe`: resolve the targets (explicit
    names, or every named constant when `names` is empty), hand the
    address list to Rust in one call (`checkAddrsWithEnv`), and let a
    rayon pool of `jobs` threads check them — each claim through the
    exact single-claim machinery over task-private data (its own
    witness io and query record), nothing shared between tasks but the
    read-only toplevel and env. Failures come back as batch indices
    and resolve to labels here. -/
def runBatchCheck (ixePath : String) (names : List String) (jobs : Nat)
    (toplevel : Aiur.Source.Toplevel) (useBytecode : Bool) : IO UInt32 := do
  let compiled : Aiur.CompiledToplevel ← match toplevel.compile with
    | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
    | .ok c => pure c
  let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
    | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
    | .ok h => pure h
  let bytes ← IO.FS.readBinFile ixePath
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .error e => IO.eprintln s!"Failed to deserialize {ixePath}: {e}"; return 1
    | .ok env => pure env
  IO.println s!"Loaded {ixePath}: {ixonEnv.namedCount} named, \
    {ixonEnv.constCount} consts, {ixonEnv.blobCount} blobs"
  -- Unresolved names are recorded and reported with the check
  -- failures rather than aborting: the batch is inherently
  -- keep-going (every target's result comes back), so resolution
  -- failures get the same treatment.
  let mut targets : Array (String × Address) := #[]
  let mut unresolved : Array String := #[]
  if names.isEmpty then
    let sorted := ixonEnv.named.toArray.qsort
      (fun a b => toString a.1 < toString b.1)
    for (ixName, named) in sorted do
      targets := targets.push (toString (ixNameToLeanName ixName), named.addr)
  else
    for arg in names do
      match resolveIxeAddr ixonEnv arg with
      | none =>
        IO.eprintln s!"{arg} not found in {ixePath}"
        unresolved := unresolved.push arg
      | some addr => targets := targets.push (arg, addr)
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let mut blob := ByteArray.empty
  for (_, a) in targets do blob := blob ++ a.hash
  IO.println s!"Typechecking {targets.size} constant(s), {jobs} thread(s)"
  (← IO.getStdout).flush
  match compiled.bytecode.checkAddrsWithEnv funIdx envHandle blob
      useBytecode jobs with
  | .error e => IO.eprintln s!"batch check: {e}"; return 1
  | .ok failures =>
    if failures.isEmpty && unresolved.isEmpty then
      IO.println s!"All {targets.size} constant(s) passed"
      return 0
    for (idxStr, err) in failures do
      let label := match idxStr.toNat? with
        | some i =>
          if h : i < targets.size then targets[i].1 else s!"index {idxStr}"
        | none => s!"index {idxStr}"
      IO.eprintln s!"{label}: IxVM-native Aiur execution error: {err}"
    IO.eprintln
      s!"{failures.size} of {targets.size} checked constant(s) FAILED\
        {if unresolved.isEmpty then "" else s!", {unresolved.size} unresolved"}"
    return 1

/-- Run a single check claim through the codegen'd IxVM Rust kernel.
    The `envHandle?` is `none` only for `.leanW` targets (`--interp`
    fallback); the addr/shard arms require it. -/
def runCompiled (compiled : Aiur.CompiledToplevel) (printStats : Bool)
    (statsOut : Option String)
    (profile? : Option (String × (Address → Option Ix.Name)))
    (useBytecode : Bool)
    (envHandle? : Option Aiur.EnvHandle)
    (target : Target) (label : String) : IO UInt32 := do
  IO.println s!"Typechecking {label}"
  (← IO.getStdout).flush
  let funIdx := compiled.getFuncIdx `verify_claim |>.get!
  let buildBlob (owned : Array Address) : ByteArray := Id.run do
    let mut blob := ByteArray.empty
    for x in owned do blob := blob ++ x.hash
    pure blob
  let profile := profile?.isSome
  let res :=
    match target, envHandle? with
    | .addr a, some envHandle =>
      compiled.bytecode.checkAddrWithEnvFull funIdx envHandle a.hash useBytecode profile
    | .shard owned, some envHandle =>
      compiled.bytecode.shardCheckWithEnvFull funIdx envHandle (buildBlob owned) useBytecode profile
    | .leanW witness, _ =>
      if useBytecode then
        compiled.bytecode.executeFull funIdx witness.input witness.inputIOBuffer profile
      else
        compiled.bytecode.executeIxVMFull funIdx witness.input witness.inputIOBuffer profile
    | _, none =>
      .error "internal: addr/shard target with no envHandle"
  match res with
  | .error e =>
    IO.eprintln s!"{label}: IxVM-native Aiur execution error: {e}"
    return 1
  | .ok r =>
    if printStats then emitStats compiled r.queryCounts statsOut
    if let some (out, nameOf) := profile? then
      dumpProfile compiled r.record out nameOf
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

private def ixesU64 : IxesP UInt64 := do
  let lo ← ixesU32; let hi ← ixesU32
  pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32))

private def ixesSkip (n : Nat) : IxesP Unit := do
  let (b, p) ← get
  if p + n ≤ b.size then modify (fun _ => (b, p + n)) else throw s!"ixes: truncated (skip {n})"

private def ixesAddr : IxesP Address := do
  let (b, p) ← get
  if p + 32 ≤ b.size then modify (fun _ => (b, p + 32)); pure ⟨b.extract p (p + 32)⟩
  else throw "ixes: truncated (expected a 32-byte address)"

/-- The binary bisection tree stored at the tail of a `.ixes` manifest. Its
leaves are shard ids; internal nodes prescribe the aggregation order that
minimizes how long cross-shard assumptions remain live. -/
inductive AggregationTree where
  | leaf (shard : Nat)
  | node (left right : AggregationTree)
  deriving BEq, Repr, Inhabited

namespace AggregationTree

partial def leaves : AggregationTree → Array Nat
  | .leaf shard => #[shard]
  | .node left right => left.leaves ++ right.leaves

/-- A legacy fallback for manifests written before the optional bisection-tree
tail existed. Leaves remain in ascending shard order. -/
partial def balancedRange (start count : Nat) : AggregationTree :=
  if count ≤ 1 then .leaf start
  else
    let leftCount := count / 2
    .node (balancedRange start leftCount)
      (balancedRange (start + leftCount) (count - leftCount))

/-- One post-order binary aggregation operation. Join child indices always
refer to earlier plan slots, and the final slot is the root. -/
inductive FoldOp where
  | leaf (shard : Nat)
  | join (left right : Nat)
  deriving BEq, Repr

/-- Lower a bisection tree to the slot plan consumed by the binary join host
driver. -/
partial def foldPlan (tree : AggregationTree) : Array FoldOp :=
  (go tree #[]).2
where
  go (node : AggregationTree) (ops : Array FoldOp) : Nat × Array FoldOp :=
    match node with
    | .leaf shard => (ops.size, ops.push (.leaf shard))
    | .node left right =>
      let (leftIdx, ops) := go left ops
      let (rightIdx, ops) := go right ops
      (ops.size, ops.push (.join leftIdx rightIdx))

/-- Drop removed shard leaves, contract unary nodes, and rewrite retained shard
ids to their dense indices in a pruned manifest view. The input tree has
already passed `validateAggregationTree`, so an out-of-range mapping entry is
an internal inconsistency rather than untrusted manifest input. -/
partial def pruneAndRemap (remap : Array (Option Nat)) :
    AggregationTree → Option AggregationTree
  | .leaf shard => (remap[shard]?).join.map .leaf
  | .node left right =>
    match pruneAndRemap remap left, pruneAndRemap remap right with
    | some left, some right => some (.node left right)
    | some tree, none | none, some tree => some tree
    | none, none => none

end AggregationTree

structure IxesManifestView where
  shards : Array (Array Address)
  /-- Original manifest shard id for each (possibly pruned) dense array slot. -/
  shardIds : Array Nat
  aggregationTree : AggregationTree
  /-- Per dense slot, the analytic prover peak (bytes) a previous run measured
  for that shard's executed record — the manifest's trailing measured-peaks
  section — or `0` when it was never measured (planner output, or a manifest
  written before the section existed). -/
  measuredPeakBytes : Array Nat
  deriving BEq, Repr

private partial def ixesAggregationTree : IxesP AggregationTree := do
  match ← ixesU8 with
  | 0 => pure (.leaf (← ixesU32).toNat)
  | 1 => pure (.node (← ixesAggregationTree) (← ixesAggregationTree))
  | tag => throw s!"ixes: invalid aggregation-tree tag {tag.toNat}"

private def validateAggregationTree (tree : AggregationTree)
    (numShards : Nat) : Except String Unit := do
  let leaves := tree.leaves
  if leaves.size != numShards then
    throw s!"ixes: aggregation tree has {leaves.size} leaves for {numShards} shards"
  let mut seen : Std.HashSet Nat := {}
  for shard in leaves do
    if shard ≥ numShards then
      throw s!"ixes: aggregation tree leaf {shard} is out of range"
    if seen.contains shard then
      throw s!"ixes: aggregation tree repeats shard {shard}"
    seen := seen.insert shard

/-- Parse every shard's owned block addresses and aggregation tree from a
serialized `.ixes`
    manifest (`ShardManifest::to_bytes`, `src/ix/shard.rs`):
    magic(8) ‖ total_cross_ingress(u128) ‖ num_shards(u32) ‖ per shard
    { id(u32) ‖ heartbeats(u64) ‖ own_size(u64) ‖ cross_ingress(u64) ‖
      assumption_root(u8 tag + 32?) ‖ blocks(u32 len + 32·len) ‖
      foreign_blocks(u32 len + 32·len) }.
    The optional trailing tree uses preorder `leaf(0,id:u32)` /
    `node(1,left,right)` encoding. Legacy manifests with no tree (or an explicit
    zero presence byte) receive a balanced ascending-id fallback. After the tree
    an optional measured-peaks section follows: presence byte, then one `u64`
    analytic prover peak per shard in id order (`0` = unmeasured); absent on
    manifests written before it existed. Anything after the last known section
    is an error. Bounds-checked: a truncated/malformed file yields `.error`,
    never a panic. -/
def parseIxesManifest (bytes : ByteArray) : Except String IxesManifestView :=
  let go : IxesP IxesManifestView := do
    let m0 ← ixesU8; let m1 ← ixesU8; let m2 ← ixesU8; let m3 ← ixesU8
    if !(m0 == 0x49 && m1 == 0x58 && m2 == 0x45 && m3 == 0x53) then
      throw "not an .ixes file (bad magic)"
    ixesSkip 4    -- rest of the 8-byte magic
    ixesSkip 16   -- total_cross_ingress (u128)
    let n ← ixesU32
    if n == 0 then throw "ixes: manifest contains no shards"
    let mut shards : Array (Array Address) := #[]
    for shardIdx in [0:n.toNat] do
      let shardId ← ixesU32
      if shardId.toNat != shardIdx then
        throw s!"ixes: shard entry {shardIdx} has id {shardId.toNat}"
      ixesSkip (8 + 8 + 8)  -- heartbeats + own_size + cross_ingress
      match ← ixesU8 with
      | 0 => pure ()
      | 1 => ixesSkip 32  -- assumption_root present
      | tag => throw s!"ixes: invalid assumption-root presence tag {tag.toNat}"
      let blen ← ixesU32
      let mut blocks : Array Address := #[]
      for _ in [0:blen.toNat] do
        blocks := blocks.push (← ixesAddr)
      ixesSkip ((← ixesU32).toNat * 32)  -- skip foreign_blocks
      shards := shards.push blocks
    let (buffer, position) ← get
    let tree ← if position == buffer.size then
        pure (AggregationTree.balancedRange 0 n.toNat)
      else
        match ← ixesU8 with
        | 0 => pure (AggregationTree.balancedRange 0 n.toNat)
        | 1 => ixesAggregationTree
        | tag => throw s!"ixes: invalid aggregation-tree presence tag {tag.toNat}"
    validateAggregationTree tree n.toNat
    let (buffer, position) ← get
    let measuredPeakBytes ← if position == buffer.size then
        pure (Array.replicate n.toNat 0)
      else
        match ← ixesU8 with
        | 0 => pure (Array.replicate n.toNat 0)
        | 1 => do
          let mut peaks : Array Nat := #[]
          for _ in [0:n.toNat] do
            peaks := peaks.push (← ixesU64).toNat
          pure peaks
        | tag => throw s!"ixes: invalid measured-peaks presence tag {tag.toNat}"
    let (buffer, position) ← get
    if position != buffer.size then
      throw s!"ixes: {buffer.size - position} trailing bytes after the measured-peaks section"
    pure { shards, shardIds := Array.range n.toNat, aggregationTree := tree,
           measuredPeakBytes }
  go.run' (bytes, 0)

/-- Backward-compatible shard-only view used by check/prove/verify paths that
do not yet consume the aggregation order. -/
def parseIxesAllShards (bytes : ByteArray) : Except String (Array (Array Address)) :=
  (parseIxesManifest bytes).map (·.shards)

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

/-- Each block address mapped to the index of the list owning it. -/
def blockIndexOf (lists : Array (Array Address)) :
    Std.HashMap Address Nat :=
  (lists.mapIdx fun k l => (k, l)).foldl (init := {}) fun m (k, l) =>
    l.foldl (fun m blk => m.insert blk k) m

/-- Owned constants per entry, in ONE env pass: `result[k]` is every env
    constant whose check-schedule block is in `lists[k]`, in
    env-iteration order (identical to a per-entry filter, so claim
    digests are unchanged). Per-entry filtering rescans all consts each
    call — at env scale (241 shards × 688k consts) that is ~30 min of
    setup, vs seconds here.

    Constants whose bytes do not parse are owned by NOBODY. That is safe
    only because `shardsCover` fails the run when any exist; without
    that gate a silent skip here means a constant no shard ever
    checks. -/
def ownedConstsPer (ixonEnv : Ixon.Env) (lists : Array (Array Address)) :
    Array (Array Address) :=
  let blockTo := blockIndexOf lists
  ixonEnv.consts.fold (init := Array.replicate lists.size #[])
    fun owned addr lc =>
      match lc.get? with
      | none => owned
      | some c =>
        match blockTo.get? (blockAddrOf addr c) with
        | some k => owned.modify k (·.push addr)
        | none => owned

/-- Owned constants of one shard: `ownedConstsPer` over a singleton. -/
def ownedConstsForBlocks (ixonEnv : Ixon.Env) (blocks : Array Address) :
    Array Address :=
  (ownedConstsPer ixonEnv #[blocks])[0]!

/-- Partition a shard's already-known `owned` constants among `parts`
    (block lists) by check-schedule block: one pass over the owned
    consts, none over the env — the split-time companion of
    `ownedConstsPer`, whose full env pass runs once per run. -/
def partitionOwned (ixonEnv : Ixon.Env) (owned : Array Address)
    (parts : Array (Array Address)) : Array (Array Address) :=
  let blockTo := blockIndexOf parts
  owned.foldl (init := Array.replicate parts.size #[]) fun acc a =>
    match (ixonEnv.consts.get? a).bind (·.get?) with
    | none => acc
    | some c =>
      match blockTo.get? (blockAddrOf a c) with
      | some k => acc.modify k (·.push a)
      | none => acc

/-- Count each shard's owned constants in one environment pass. Callers first
run `shardsCover`, so every check-schedule block has exactly one owner. This is
the subject-leaf count used by aggregate structural-threshold scheduling. -/
def ownedConstCountsForShards (ixonEnv : Ixon.Env)
    (shards : Array (Array Address)) : Array Nat := Id.run do
  let mut blockToShard : Std.HashMap Address Nat := {}
  for (blocks, shard) in shards.mapIdx fun shard blocks => (blocks, shard) do
    for block in blocks do
      blockToShard := blockToShard.insert block shard
  let mut counts := Array.replicate shards.size 0
  for (addr, lc) in ixonEnv.consts do
    let some c := lc.get? | continue
    let some shard := blockToShard.get? (blockAddrOf addr c) | continue
    counts := counts.modify shard (· + 1)
  return counts

/-- Remove manifest shards that provably own no environment constants, then
contract and densely reindex the corresponding aggregation-tree leaves.

Callers must run `shardsCover` on the unpruned view first. That gate establishes
that every constant is owned exactly once; the zero counts here therefore prove
that dropping these leaves cannot omit a checked subject. `shardIds` preserves
the original ids for diagnostics and for matching legacy manifests. -/
def IxesManifestView.pruneEmpty (view : IxesManifestView)
    (ixonEnv : Ixon.Env) : Except String (IxesManifestView × Array Nat) := do
  if view.shards.size != view.shardIds.size then
    throw "ixes: internal shard/id cardinality mismatch"
  let counts := ownedConstCountsForShards ixonEnv view.shards
  let mut remap : Array (Option Nat) := Array.replicate view.shards.size none
  let mut shards : Array (Array Address) := #[]
  let mut shardIds : Array Nat := #[]
  let mut measuredPeakBytes : Array Nat := #[]
  let mut keptCounts : Array Nat := #[]
  for (count, oldIdx) in counts.mapIdx fun oldIdx count => (count, oldIdx) do
    if count != 0 then
      let some blocks := view.shards[oldIdx]?
        | throw s!"ixes: internal missing shard {oldIdx}"
      let some originalId := view.shardIds[oldIdx]?
        | throw s!"ixes: internal missing shard id {oldIdx}"
      remap := remap.set! oldIdx (some shards.size)
      shards := shards.push blocks
      shardIds := shardIds.push originalId
      measuredPeakBytes := measuredPeakBytes.push ((view.measuredPeakBytes[oldIdx]?).getD 0)
      keptCounts := keptCounts.push count
  let some aggregationTree := view.aggregationTree.pruneAndRemap remap
    | throw "aggregate: manifest has no shard owning an environment constant"
  pure ({ shards, shardIds, aggregationTree, measuredPeakBytes }, keptCounts)

/-- The `CheckEnv` claim digest a shard's proof commits to — reconstructed
    deterministically from the env + the shard's owned blocks. Matches the
    digest `prove --shard K` produced, so a proof can be bound to its shard. -/
def shardClaimDigest (ixonEnv : Ixon.Env) (blocks : Array Address) : Except String Address := do
  let (claim, _) ← IxVM.ClaimHarness.shardCheckEnvClaimTrees ixonEnv
    (ownedConstsForBlocks ixonEnv blocks)
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
    (printStats : Bool) (statsOut : Option String) (profileOut : Option String)
    (useBytecode : Bool)
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
  match compiled.bytecode.shardCheckWithEnvFull funIdx envHandle blob useBytecode profileOut.isSome with
  | .error e =>
    IO.eprintln s!"{label}: IxVM-native shard check error: {e}"
    return 1
  | .ok r =>
    if printStats then emitStats compiled r.queryCounts statsOut
    if let some out := profileOut then
      dumpProfile compiled r.record out (ixonEnv.addrToName.get? ·)
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
    (statsOut : Option String) (profileOut : Option String)
    (useBytecode : Bool) : IO UInt32 := do
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) => match shards[shardK]? with
    | none => IO.eprintln s!"shard {shardK} out of range ({shards.size} shards)"; return 1
    | some blocks =>
      let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
        | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
        | .ok h => pure h
      runShardOwnedNative envHandle compiled printStats statsOut profileOut
        useBytecode ixonEnv blocks shardK

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

/-- Cut `blocks` into contiguous, nonempty, roughly equal-count parts
    (`p` clamped to `[2, blocks.size]` — a rejection always needs at
    least two parts, and the block list caps how many a cut can
    produce). Rows are what the prover-RAM model responds to, and equal
    block counts are the measured-best proxy for equal rows
    (equal-vspan cuts lost on parts, depth and executions on every env
    tried). Shared by the prove split recursion and the check wave
    loop. -/
def cutBlocks (blocks : Array Address) (p : Nat) : Array (Array Address) :=
  let p := min (max p 2) blocks.size
  (Array.range p).map fun i =>
    blocks.extract (blocks.size * i / p) (blocks.size * (i + 1) / p)

/-- Measured-peaks blob for the manifest emit: one 8-byte LE value per
    shard, in shard order. -/
def peaksBlob (peaks : Array Nat) : ByteArray :=
  peaks.foldl (init := ByteArray.empty) fun blob pk =>
    blob ++ pk.toUInt64.toLEBytes

/-- Wire encoding shared by the shard batch FFI and the manifest emit:
    per entry, a 4-byte LE count followed by the 32-byte addresses. -/
def addrListsBlob (lists : Array (Array Address)) : ByteArray :=
  lists.foldl (init := ByteArray.empty) fun blob l =>
    l.foldl (fun b a => b ++ a.hash) (blob ++ l.size.toUInt32.toLEBytes)

/-- One leaf of a source manifest cut into parts, as the prove and check
    split loops produce it: the parts' block lists in block order, each
    with the analytic prover peak measured on its executed record
    (`0` = unmeasured). -/
structure LeafRefinement where
  shard : Nat
  parts : Array (Array Address × Nat)

/-- Wire encoding of `Aiur.shardManifestRefine`'s refinements argument:
    `count(u32)`, then per refined leaf `id(u32) ‖ nparts(u32)` and per
    part `nblocks(u32) ‖ 32·nblocks ‖ peak(u64)`. -/
def refinementsBlob (rs : Array LeafRefinement) : ByteArray :=
  rs.foldl (init := rs.size.toUInt32.toLEBytes) fun blob r =>
    r.parts.foldl
      (init := blob ++ r.shard.toUInt32.toLEBytes ++ r.parts.size.toUInt32.toLEBytes)
      fun blob (blocks, peak) =>
        (blocks.foldl (fun b a => b ++ a.hash) (blob ++ blocks.size.toUInt32.toLEBytes))
          ++ peak.toUInt64.toLEBytes

/-- Group per-leaf run results `(shard, parts)` over the `n` leaves of a
    source manifest into the leaves that split (≥ 2 parts) and the
    measured peaks of the leaves that did not (`0` where a leaf was not
    run). -/
def refinementsOfRuns (n : Nat)
    (runs : Array (Nat × Array (Array Address × Nat))) :
    Array LeafRefinement × Array Nat :=
  runs.foldl (init := (#[], Array.replicate n 0)) fun (rs, measured) (k, parts) =>
    if parts.size > 1 then (rs.push { shard := k, parts }, measured)
    else match parts[0]? with
      | some (_, peak) => (rs, if k < measured.size then measured.set! k peak else measured)
      | none => (rs, measured)

/-- Decode the new-id table `Aiur.shardManifestRefine` returns:
    `count(u32)`, then per refinement `n(u32) ‖ n × id(u32)`. Malformed
    input yields the ids decoded so far, never a panic. -/
def decodeIdTable (bytes : ByteArray) : Array (Array Nat) := Id.run do
  let u32At (i : Nat) : Option Nat :=
    if i + 4 ≤ bytes.size then
      some (bytes[i]!.toNat ||| (bytes[i+1]!.toNat <<< 8)
        ||| (bytes[i+2]!.toNat <<< 16) ||| (bytes[i+3]!.toNat <<< 24))
    else none
  let some count := u32At 0 | return #[]
  let mut pos := 4
  let mut table : Array (Array Nat) := #[]
  for _ in [0:count] do
    let some n := u32At pos | return table
    pos := pos + 4
    let mut ids : Array Nat := #[]
    for _ in [0:n] do
      let some id := u32At pos | return table
      ids := ids.push id
      pos := pos + 4
    table := table.push ids
  return table

/-- Emit the partition a run actually validated as a refinement of the
    manifest it started from — the shared tail of `ix prove --out-ixes`
    and `ix check --ram-budget --out-ixes`. Untouched leaves keep their
    records, ids and tree positions (`Aiur.shardManifestRefine`); a leaf
    that split becomes a subtree over its parts, part 0 keeping the leaf's
    id and later parts taking fresh ids after the last existing one.
    `measured` carries the peaks of the leaves that ran unsplit. Skipped
    with a note when any shard failed: a refined manifest describes a
    fully-validated partition. Returns the parts' new ids per refinement. -/
def emitRefinedManifest (tag : String) (envHandle : Aiur.EnvHandle)
    (sourcePath out : String) (refinements : Array LeafRefinement)
    (measured : Array Nat) (failures : Nat) : IO (Array (Array Nat)) := do
  if failures == 0 then
    let ids ← Aiur.shardManifestRefine envHandle sourcePath
      (refinementsBlob refinements) (peaksBlob measured) out
    IO.println s!"[{tag}] refined manifest → {out} \
      ({refinements.size} leaf/leaves split)"
    pure (decodeIdTable ids)
  else
    IO.eprintln s!"--out-ixes {out} skipped: {failures} failure(s)"
    pure #[]

/-- Whole-partition check as ONE Rust rayon batch: work-stealing across
    shards, no chunk barriers (measured 2.3–2.5x faster than the
    per-shard Lean-task scheduler it replaced, whose chunk-of-N full
    barrier idled workers on each wave's slowest shard). Each shard
    runs the identical single-shard machinery over its own record; per
    shard the analytic prover RAM peak of the executed record is
    reported — the input to split (over a prover budget) / merge (far
    under it) decisions. Builds the `EnvHandle` ONCE, shared by every
    shard. Coverage-gates the manifest before running any shard — exit
    0 has to mean "every env const was checked by some shard", same
    soundness contract as `runShardCheckAll`. -/
def runShardBatchNative (manifestPath ixePath : String) (jobs? : Option Nat)
    (compiled : Aiur.CompiledToplevel) (useBytecode : Bool)
    (profileOut : Option String)
    (json? : Option (String × String))
    (maxRamBytes : Nat) (outIxes : Option String) :
    IO UInt32 := do
  -- The row's peak-rss needs the process-tree RSS sampler running
  -- (`peakTreeRssBytes` reports 0 otherwise); started before the env
  -- load so the peak covers the whole run, like `check-rs`.
  if json?.isSome then TracingTexray.startSampler
  match (← loadEnvAndShards manifestPath ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    if !(← shardsCover ixonEnv shards) then return 1
    let envHandle ← match Aiur.EnvHandle.fromIxe ixePath with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {ixePath}: {e}"; return 1
      | .ok h => pure h
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    let jobs := jobs?.getD 0
    -- `check_const`'s queries are what the weight rows are read from; a
    -- toplevel without it can still check, just not profile.
    let checkConstIdx := (compiled.getFuncIdx `check_const).getD 0
    if profileOut.isSome && (compiled.getFuncIdx `check_const).isNone then
      IO.eprintln "--profile: no `check_const` in compiled toplevel"
    let cutLabeled (origin : Nat) (label : String) (blocks owned : Array Address)
        (p : Nat) : Array (Nat × String × Array Address × Array Address) :=
      let parts := cutBlocks blocks p
      (parts.zip (partitionOwned ixonEnv owned parts)).mapIdx
        fun i (part, po) => (origin, s!"{label}.{i}", part, po)
    -- One loop over execution waves. Wave 0 is the planned partition;
    -- with `--ram-budget` every over-budget shard is cut into the peak
    -- model's suggested part count and the parts re-batched as the next
    -- wave, until everything fits or is a single block. Without a
    -- budget the FFI answers 1 part everywhere and the loop is a single
    -- wave — the plain batch check. Waves after the first never
    -- profile: wave 0 already carries one row per constant, measured
    -- under the planned partition — the one schedulers consume.
    -- The whole run's ownership assignment: one env pass here, and
    -- every later wave's parts inherit their parent's owned consts via
    -- `partitionOwned` — no wave ever rescans the env.
    let mut wave : Array (Nat × String × Array Address × Array Address) :=
      (shards.zip (ownedConstsPer ixonEnv shards)).mapIdx
        fun k (b, o) => (k, s!"{k}", b, o)
    let mut waveNum := 0
    let mut failed : Array String := #[]
    let mut final : Array (Array Address × Nat) := #[]
    -- Per source leaf, the parts that ended its cascade (fit, or failed)
    -- — the refinement the emitted manifest describes.
    let mut leafParts : Std.HashMap Nat (Array (Array Address × Nat)) := {}
    let mut totalConsts := 0
    let mut elapsedMs := 0
    while wave.size > 0 do
      if waveNum == 0 then
        IO.println s!"Typechecking {wave.size} shard(s) in one rayon \
          batch, {jobs} thread(s) (0 = all)"
      else
        IO.println s!"[wave {waveNum}] re-executing {wave.size} part(s)"
      (← IO.getStdout).flush
      let ownedPer := wave.map (·.2.2.2)
      let start ← IO.monoMsNow
      match compiled.bytecode.shardCheckBatchWithEnv funIdx envHandle
          (addrListsBlob ownedPer) useBytecode jobs
          Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
          (profileOut.isSome && waveNum == 0) checkConstIdx maxRamBytes with
      | .error e => IO.eprintln s!"shard batch (wave {waveNum}): {e}"; return 1
      | .ok rs =>
        if waveNum == 0 then
          -- The bench row's measured window: the planned partition's
          -- batch call, matching `check-rs`. Split waves are audit
          -- extras outside the benchmarked engine window.
          elapsedMs := (← IO.monoMsNow) - start
          totalConsts := ownedPer.foldl (· + ·.size) 0
        let mut next : Array (Nat × String × Array Address × Array Address) := #[]
        for (r, origin, label, blocks, owned) in rs.zip wave do
          let gib := toGib r.peakBytes
          let settled := r.error.isEmpty && r.suggestedParts <= 1
            || !r.error.isEmpty || blocks.size <= 1
          if !r.error.isEmpty then
            IO.eprintln s!"[shard {label}] FAILED: {r.error}"
            failed := failed.push s!"shard {label}: {r.error}"
          else if r.suggestedParts <= 1 then
            IO.println s!"[shard {label}] ok, projected prover peak {gib} GiB"
          else if blocks.size <= 1 then
            IO.eprintln s!"[shard {label}] peak {gib} GiB over budget and a \
              single block — cannot split"
            failed := failed.push s!"shard {label}: single block over budget"
          else
            IO.println s!"[shard {label}] peak {gib} GiB over budget — cut \
              into {r.suggestedParts}"
            next := next ++ cutLabeled origin label blocks owned r.suggestedParts
          if settled then
            final := final.push (blocks, r.peakBytes)
            leafParts := leafParts.insert origin
              ((leafParts.getD origin #[]).push (blocks, r.peakBytes))
        -- Weight rows are appended once, from wave 0: Rust already
        -- reduced each shard's record under its own task, so nothing
        -- here holds a record alive.
        if waveNum == 0 then
          if let some out := profileOut then
            let h ← IO.FS.Handle.mk out .append
            for r in rs do
              h.putStr <| r.foldWeights "" fun acc addrBytes vspan mult =>
                let addr : Address := ⟨addrBytes⟩
                let name := (ixonEnv.addrToName.get? addr).map (s!" {·}") |>.getD ""
                acc ++ s!"{addr} {vspan} {mult}{name}\n"
            h.flush
        wave := next
        waveNum := waveNum + 1
    if maxRamBytes > 0 then
      IO.println s!"[split-audit] {final.size} part(s) from {shards.size} \
        planned shard(s), {waveNum - 1} split wave(s), {failed.size} failure(s)"
      -- Consolidation is arithmetic, never an execution: the measured
      -- sum only shrinks as shards get coarser, so this count is a safe
      -- under-count — and the next run's mandatory executions verify it
      -- inline. 95%: margin for the model's +1.7% under-projection.
      let sum := final.foldl (· + ·.2) 0
      let target := maxRamBytes * 95 / 100
      let n1 := max 1 ((sum + target - 1) / target)
      if failed.isEmpty && n1 < final.size then
        IO.println s!"[split-audit] measured total {toGib sum} GiB — \
          {n1} shard(s) would fit the budget: re-shard with --shards {n1}"
    -- The refined partition — what this run actually validated — written
    -- as a refinement of the manifest it started from: untouched leaves
    -- keep their records, ids and tree positions, and a split leaf's parts
    -- are ordered by their position in the leaf's block list, whatever
    -- wave settled them.
    if let some out := outIxes then
      let runs : Array (Nat × Array (Array Address × Nat)) :=
        (Array.range shards.size).filterMap fun k =>
          (leafParts.get? k).map fun parts =>
            let pos : Std.HashMap Address Nat :=
              ((shards[k]!).mapIdx fun i a => (a, i)).foldl
                (fun m (a, i) => m.insert a i) {}
            let posOf (part : Array Address × Nat) : Nat :=
              ((part.1[0]?).bind pos.get?).getD 0
            (k, parts.qsort fun a b => posOf a < posOf b)
      let (refinements, measured) := refinementsOfRuns shards.size runs
      let _ ← emitRefinedManifest "split-audit" envHandle manifestPath out
        refinements measured failed.size
    -- One env-keyed results row for `ix bench run --backend aiur-sharded-env`:
    -- the measured window is the wave-0 batch FFI call (env load and
    -- blob setup are excluded, matching what the benchmark tracks — the
    -- execution engine, not the loader).
    if let some (path, key) := json? then
      let secs := elapsedMs.toFloat / 1000.0
      let tput := if elapsedMs > 0
        then totalConsts.toFloat * 1000.0 / elapsedMs.toFloat else 0.0
      let peakRss ← TracingTexray.peakTreeRssBytes
      let status := if failed.isEmpty then "ok" else "rejected"
      Ix.Benchmark.Results.writeRow path key status
        [ ("constants", Lean.toJson totalConsts)
        , ("shards", Lean.toJson final.size)
        , ("check-time", Ix.Benchmark.Results.jsonRound 3 secs)
        , ("throughput", Ix.Benchmark.Results.jsonRound 2 tput)
        , ("peak-rss", Lean.toJson peakRss) ]
    if failed.isEmpty then
      IO.println s!"All {final.size} shard(s) passed"
      return 0
    IO.eprintln s!"{failed.size} of {final.size} shard(s) FAILED:"
    for f in failed do IO.eprintln s!"  {f}"
    -- Under `--json` a kernel rejection is the benchmark's `rejected`
    -- exit (the row is already written), same contract as `check-rs`.
    return if json?.isSome then Ix.Benchmark.Results.exitRejected else 1

/-- Run the shard operation over EVERY shard — the whole-partition behavior of
    `--ixes` with no `--shard` (used by `prove`). Loads the env once. Returns 1
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
  let profileOut := (p.flag? "profile").map (·.as! String)
  if profileOut.isSome && interpSource then
    IO.eprintln "error: --profile is not available with --interp source"
    return 1
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
      -- Per-name / per-claim targets carry no addr→name index here (the
      -- ixon env loads later, inside `forEachClaim`), so `--profile`
      -- lines dump address-only on this path; the shard-native paths
      -- below join names via `ixonEnv.addrToName`.
      let profile? := profileOut.map ((·, fun _ => none))
      let go (_ : Ix.Claim) (envHandle? : Option Aiur.EnvHandle) (target : Target)
          (label : String) : IO UInt32 :=
        runCompiled compiled printStats statsOut profile? useBytecode envHandle? target label
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
      return (← runShardCheckManifestNative manifest ixe k compiled printStats statsOut profileOut useBytecode)
  | some ixe, some manifest, none   =>
    if interpSource then
      return (← runShardCheckAll manifest ixe ((p.flag? "jobs").map (·.as! Nat))
        (fun c w l => runOne c none (.leanW w) l))
    else do
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      let json? := (p.flag? "json").map fun f =>
        (f.as! String, ((p.flag? "json-name").map (·.as! String)).getD "env")
      return (← runShardBatchNative manifest ixe
        ((p.flag? "jobs").map (·.as! Nat)) compiled useBytecode profileOut json?
        (((p.flag? "ram-budget").map (·.as! Nat)).getD 0 * gibBytes)
        ((p.flag? "out-ixes").map (·.as! String)))
  | _, _, _ =>
    -- `--jobs N` (N ≠ 1) with an `--ixe` env and no `--claim` takes the
    -- parallel batch path: one FFI call, rayon over the target list,
    -- each claim checked over task-private data. `--jobs 1` (or no
    -- flag) keeps the sequential per-claim loop unchanged.
    match (p.flag? "jobs").map (·.as! Nat), ixePath with
    | some jobs, some ixe =>
      if jobs != 1 && !interpSource && claimHex.isNone then
        runBatchCheck ixe names jobs toplevel useBytecode
      else
        forEachClaim ixePath claimHex names keepGoing "check" interpSource
          runOne
    | _, _ =>
      forEachClaim ixePath claimHex names keepGoing "check" interpSource
        runOne

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
    "profile"   : String;   "Append per-constant virtual-gas costs to this file: one `<addr_hex> <vspan> <mult> [name]` line per `check_const` query, read from the execution's QueryRecordHandle (names joined on the shard paths, where the env's addr→name index is loaded). The vspan is the constant's standalone check cost within its shard — memo hits replay the callee's recorded span. Order-independent within a partition, but spans of constants whose dependency cone crosses an assumption boundary shift between partitions (foreign callees are assumed, not replayed); schedule off a profile measured under the partition being scheduled. Not available with `--interp source`."
    "ixes"      : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: check the constants owned by shard K (ingress their closure, skip the frontier). Without --shard: check every shard of the partition concurrently, after a coverage check."
    "shard"     : Nat;      "0-based shard index K (with --ixe + --ixes): check the constants owned by shard K of the manifest's partition."
    "jobs"      : Nat;      "Parallelism. With --ixes (no --shard): max shards checked concurrently (default: all at once). With --ixe alone and N ≠ 1: check the targeted constants on N Rust threads (0 = all cores), each claim over its own private record — peak RAM is bounded by N in-flight claim closures."
    "json"      : String;   "With --ixes (no --shard): append one env-keyed results row (see Ix.Benchmark.Results) for the batch to this file — check-time, throughput, peak-rss, constants, shards. Used by `ix bench run --backend aiur-sharded-env`."
    "json-name" : String;   "Row key for the --json row (default: `env`)."
    "ram-budget" : Nat;     "The destination prove box's per-shard RAM budget, GiB (with --ixes, no --shard): after the batch, cut every shard whose projected prover peak exceeds the budget into the peak model's suggested part count and re-batch the parts, wave by wave, until everything fits — the exec-only split audit. Under-filled partitions get a printed suggestion (the shard count the measured total says would fit), never an extra execution: re-shard with --shards N and let the next run's mandatory executions verify it inline. Same unit and model as `ix prove --max-ram`, but no auto-detection: the budget describes the prove box the partition is destined for, not the machine running the check. Omit for a plain check."
    "out-ixes"  : String;   "With --ram-budget: write the recalibrated partition — the block lists the wave loop actually validated, splits included — as a `.ixes` manifest to this path. Skipped if any shard failed. The manifest the next run of this env should start from."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted)."
]

end
