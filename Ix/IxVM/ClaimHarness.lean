module
public import Ix.Aiur.Protocol
public import Ix.Ixon
public import Ix.Claim
public import Ix.AssumptionTree
public import Ix.CompileM
public import Ix.Common

public section

/-!
# IxVM Claim harness

Lean-side glue between `Ix.Claim` and the Aiur `verify_claim` /
`dbg_check_const` entrypoints in `Ix/IxVM/Kernel/Claim.lean`.

The harness handles every step the Aiur side cannot:

1. **Lean → Ixon compile**: `loadIxonEnv` / `loadSharedIxonEnv` walk
   the Lean environment, run `Ix.CompileM.rsCompileEnvFFI`, and
   return an `Ixon.Env` representing the constants' transitive
   closure.

2. **Closure layout**: `closureFrom` follows `Constant.refs` (+
   projection block addresses) from a target address. Mirrors the
   Aiur kernel's `load_with_deps` so the IOBuffer carries exactly
   what the kernel will look up.

3. **IOBuffer population**: `addEntries` seeds the constants, blobs,
   and Defn reducibility hints under their content-addressed keys
   (`addr`, `addr ++ [0]`, `addr ++ [1]`). The Aiur kernel reads via
   `io_get_info` + `#read_byte_stream` and blake3-verifies each
   payload against its key.

4. **Witness construction**: `buildClaimWitness` serializes any
   `Ix.Claim`, seeds the bytes at `key = blake3(claim)`, pulls in the
   right closure per variant, and threads any caller-supplied
   `AssumptionTree`s under their merkle roots. The resulting
   `ClaimWitness` packs (a) the entrypoint name (`verify_claim`),
   (b) the 32-G public input (`claim_digest`), and (c) the populated
   IOBuffer.

The serde primitive `buildSerdeIOBuffer` survives here because the
benchmark/test entrypoint `ixon_serde_test` shares the same IOBuffer
plumbing — its inputs are still indexed integers rather than blake3
keys.

## Helpers

* `envCanonicalTree` — convenience that returns the canonical merkle
  tree over an env's const addresses. Hands the caller a tree whose
  root they can plug into a `Claim.checkEnv` claim.
* `hintToG` — `Lean.ReducibilityHints → Aiur.G` encoding shared with
  Aiur's `load_constant_hint`.
-/
namespace IxVM.ClaimHarness

/-- Run the Lean → Ixon FFI pipeline for `name`'s transitive closure. -/
def loadIxonEnv (name : Lean.Name) (leanEnv : Lean.Environment) : IO Ixon.Env := do
  let constList := Lean.collectDependencies name leanEnv.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  pure rawEnv.toEnv

/-- Resolve a Lean name to its `Ixon.Env` `Address`, or fail with a
    descriptive `IO` error. Used by every claim/witness builder that
    starts from a Lean name. -/
def lookupAddr (ixonEnv : Ixon.Env) (name : Lean.Name) : IO Address :=
  match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
  | some addr => pure addr
  | none => throw <| IO.userError s!"{name} not found in Ixon environment"

/-- Compile the union of `names`'s transitive closures into one shared
    Ixon env. Drivers like `KernelArena.lean` use this to pay the
    Lean→Ixon compile cost once and then build per-target IOBuffers via
    `buildClaimWitness` / `buildDbgCheckConst`. -/
def loadSharedIxonEnv (names : Array Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env := do
  let mut seen : Lean.NameSet := {}
  let mut deduped : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for n in names do
    for entry in Lean.collectDependencies n leanEnv.constants do
      if !seen.contains entry.fst then
        seen := seen.insert entry.fst
        deduped := deduped.push entry
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI deduped.toList
  pure rawEnv.toEnv

/-- Walk the Constant ref-graph from `target` to compute the set of
    addresses needed to type-check it. Mirrors Aiur's `load_with_deps`:
    follow `Constant.refs` plus the projection's `block_addr` (the parent
    Muts wrapper) for IPrj/CPrj/RPrj/DPrj. -/
partial def closureFrom (env : Ixon.Env) (target : Address) : Std.HashSet Address := Id.run do
  let mut visited : Std.HashSet Address := {}
  let mut worklist : Array Address := #[target]
  while !worklist.isEmpty do
    let addr := worklist.back!
    worklist := worklist.pop
    if visited.contains addr then continue
    visited := visited.insert addr
    let some c := env.getConst? addr | continue
    for r in c.refs do worklist := worklist.push r
    match c.info with
    | .iPrj p | .cPrj p => worklist := worklist.push p.block
    | _ => pure ()
    match c.info with
    | .rPrj p | .dPrj p => worklist := worklist.push p.block
    | _ => pure ()
  return visited

/-- Build the `ixon_serde_test` / `ixon_serde_blake3_bench` IOBuffer:
    one entry per const, keyed by its index. Returns the buffer and the
    count `n` (which the Aiur entrypoint receives as input). -/
def buildSerdeIOBuffer (ixonEnv : Ixon.Env) : Aiur.IOBuffer × Nat :=
  ixonEnv.consts.valuesIter.fold (init := (default, 0)) fun (ioBuffer, i) lc =>
    -- The lazy entry already holds the serialized bytes; no re-serialization.
    let bytes := lc.rawBytes
    (ioBuffer.extend 0 #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)

/-- Encode a `Lean.ReducibilityHints` as a single `G` per the convention
    Aiur's `load_constant_hint` decodes (opaque → 0, abbrev → 0xFFFFFFFF,
    regular n → clamp(1 + n, 0xFFFFFFFE)). -/
private def hintToG : Lean.ReducibilityHints → Aiur.G
  | .opaque => .ofNat 0
  | .abbrev => .ofNat 0xFFFFFFFF
  | .regular n => .ofNat (min (1 + n.toNat) 0xFFFFFFFE)

/-- Insert all per-address entries for `addr`s satisfying `keep` into
    `ioBuffer`. Each address kind lives on its own channel; the key is
    always the 32-G blake3 hash, with no disambiguating suffix.

    | channel | key (32 G) | value          | meaning |
    |---------|------------|----------------|---------|
    | 0       | `addr`     | const bytes    | constant data (empty marker = `addr` is a blob) |
    | 1       | `addr`     | raw blob bytes | referenced data (verified by Aiur via blake3) |
    | 2       | `addr`     | single G       | Defn `ReducibilityHints` encoding |

    Blob addrs also get an empty entry on channel 0 so the kernel's
    constant-vs-blob detection (`io_get_info(0, addr) ⇒ len=0`) still
    works without a separate query path. -/
def addEntries (ixonEnv : Ixon.Env) (keep : Address → Bool)
    (ioBuffer : Aiur.IOBuffer) : Aiur.IOBuffer := Id.run do
  let mut ioBuffer := ioBuffer
  for (addr, lc) in ixonEnv.consts do
    if !keep addr then continue
    -- The kernel re-hashes these bytes against the key, so feed the exact
    -- serialized form the lazy entry holds — no materialization needed.
    let bytes := lc.rawBytes
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 0 key (bytes.data.map .ofUInt8)
  for (addr, rawBytes) in ixonEnv.blobs do
    if !keep addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 1 key (rawBytes.data.map fun b => .ofNat b.toNat)
    ioBuffer := ioBuffer.extend 0 key #[]
  for (_, named) in ixonEnv.named do
    if !keep named.addr then continue
    match named.constMeta with
    | .defn _ _ hints _ _ _ _ _ =>
      let key : Array Aiur.G := named.addr.hash.data.map .ofUInt8
      ioBuffer := ioBuffer.extend 2 key #[hintToG hints]
    | _ => pure ()
  return ioBuffer

-- ============================================================================
-- Claim witness builders
-- ============================================================================

/-- A ready-to-run Aiur invocation: function name to dispatch, public
    input (`Array G`), and the IOBuffer pre-populated with every
    blake3-keyed witness payload the entrypoint will demand. -/
structure ClaimWitness where
  funcName      : Lean.Name
  input         : Array Aiur.G
  inputIOBuffer : Aiur.IOBuffer
  deriving Inhabited

/-- Convert an `Address` to its `Array G` IOBuffer-key form. -/
@[inline] private def addrKey (a : Address) : Array Aiur.G :=
  a.hash.data.map .ofUInt8

/-- Look up the `AssumptionTree` at `root` in the caller-supplied
    `trees` map and seed its serialized bytes at key=`root` in
    `ioBuffer`. Aiur's `load_assumption_tree` reads bytes by key and
    asserts the merkle fold matches the key. Fails when the caller
    didn't supply a tree the claim references. -/
private def seedTreeAt (root : Address)
    (trees : Std.HashMap Address Ix.AssumptionTree)
    (ioBuffer : Aiur.IOBuffer) : Except String Aiur.IOBuffer :=
  match trees.get? root with
  | some tree =>
    let bytes := Ix.AssumptionTree.ser tree
    .ok (ioBuffer.extend 0 (addrKey tree.root) (bytes.data.map .ofUInt8))
  | none => .error s!"no assumption tree supplied for root {root}"

/-- Build the witness for `verify_claim` against `claim`.

    `trees` is a caller-supplied map of merkle-root → tree; every root
    that appears in the claim (assumption root, env root, contains
    tree root) MUST have an entry. `Ix.AssumptionTree.canonical` builds
    the canonical sorted+padded shape if you start from a leaf list.

    Per-variant IOBuffer payload:
    - `Check addr none`: closure of `addr`.
    - `Check addr (some r)`: closure of `addr` + assumption tree at `r`.
    - `Eval i o asm`: closure of `i ∪ o` (+ optional asm tree).
    - `CheckEnv root asm`: full env entries + env-tree at `root`
      (+ optional asm tree).
    - `Reveal comm info`: closure of `comm`. Info bytes ride inside
      the claim bytes already.
    - `Contains tree target`: tree at `tree`. No const ingest.

    Returns `Except String ClaimWitness`: error message names the
    missing assumption root when applicable.

    Eval-claim invocations currently hit the placeholder
    `assert_eq!(0,1)` arm of `verify_claim` at proving time. -/
def buildClaimWitness (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {}) :
    Except String ClaimWitness := do
  let claimBytes := Ix.Claim.ser claim
  let digestKey := addrKey (Address.blake3 claimBytes)
  let mut ioBuffer : Aiur.IOBuffer := default
  ioBuffer := ioBuffer.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  let seedAsm asm buf := match asm with
    | some r => seedTreeAt r trees buf
    | none => .ok buf
  match claim with
  | .check addr asm =>
    ioBuffer := addEntries env (closureFrom env addr).contains ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .eval input output asm =>
    let inputClosure := closureFrom env input
    let outputClosure := closureFrom env output
    ioBuffer := addEntries env
      (fun a => inputClosure.contains a || outputClosure.contains a) ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .checkEnv root asm =>
    ioBuffer := addEntries env (fun _ => true) ioBuffer
    ioBuffer ← seedTreeAt root trees ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .reveal comm _info =>
    ioBuffer := addEntries env (closureFrom env comm).contains ioBuffer
  | .contains tree _target =>
    ioBuffer ← seedTreeAt tree trees ioBuffer
  return { funcName := `verify_claim
           input := digestKey, inputIOBuffer := ioBuffer }

/-- Reconstruct a shard's `CheckEnv` claim, its reference closure, and the
    assumption trees (env-root + optional frontier) — everything **except** the
    IO buffer. Deterministic in `owned` (canonical trees sort addresses), so the
    claim digest reproduces exactly what `prove`d — used to bind a proof to a
    shard during verification, cheaply (no buffer serialization). -/
def shardCheckEnvClaim (env : Ixon.Env) (owned : Array Address) :
    Except String (Ix.Claim × Std.HashSet Address × Std.HashMap Address Ix.AssumptionTree) := do
  let ownedSet : Std.HashSet Address := owned.foldl (·.insert ·) {}
  let closure : Std.HashSet Address := Id.run do
    let mut s : Std.HashSet Address := {}
    for a in owned do
      for x in (closureFrom env a).toArray do
        s := s.insert x
    return s
  let frontier : Array Address :=
    closure.toArray.filter (fun a => !ownedSet.contains a)
  let some envTree := Ix.AssumptionTree.canonical closure.toArray
    | .error "shardCheckEnvClaim: empty shard closure"
  let asmTree? := Ix.AssumptionTree.canonical frontier
  let claim := Ix.Claim.checkEnv envTree.root (asmTree?.map (·.root))
  let mut trees : Std.HashMap Address Ix.AssumptionTree :=
    ({} : Std.HashMap Address Ix.AssumptionTree).insert envTree.root envTree
  match asmTree? with
  | some asmTree => trees := trees.insert asmTree.root asmTree
  | none => pure ()
  pure (claim, closure, trees)

def buildShardCheckEnvWitness (env : Ixon.Env) (owned : Array Address) :
    Except String (Ix.Claim × ClaimWitness) := do
  let (claim, closure, trees) ← shardCheckEnvClaim env owned
  let claimBytes := Ix.Claim.ser claim
  let digestKey := addrKey (Address.blake3 claimBytes)
  let mut ioBuffer : Aiur.IOBuffer := default
  ioBuffer := ioBuffer.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  -- Ship only the shard closure (consts + blobs + Defn hints).
  ioBuffer := addEntries env closure.contains ioBuffer
  -- Seed the env-root and (when present) frontier assumption trees.
  for (root, _) in trees do
    ioBuffer ← seedTreeAt root trees ioBuffer
  return (claim, { funcName := `verify_claim
                   input := digestKey, inputIOBuffer := ioBuffer })

/-- Canonical merkle tree over every const address in `env`. Returns
    `none` for an empty env. Convenience for callers that want to
    issue a `CheckEnv` claim against the env's canonical merkle root. -/
def envCanonicalTree (env : Ixon.Env) : Option Ix.AssumptionTree :=
  Ix.AssumptionTree.canonical (env.consts.keys.toArray)

/-- Build the witness for the `verify_const` Aiur entrypoint.
    Subject-only typecheck — transitive deps are trusted, not
    re-verified. Not a claim path (no claim-digest discipline). Used
    by `Tests/Ix/Kernel/Arena.lean::arenaTests` where each arena
    fixture's own well-typedness is the only signal needed. -/
def buildVerifyConst (env : Ixon.Env) (target : Address) : ClaimWitness :=
  let closure := closureFrom env target
  let ioBuffer := addEntries env closure.contains default
  { funcName := `verify_const
    input := addrKey target, inputIOBuffer := ioBuffer }

end IxVM.ClaimHarness

end
