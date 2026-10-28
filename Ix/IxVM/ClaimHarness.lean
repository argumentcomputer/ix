module
public import Ix.Aiur.Protocol
public import Ix.Ixon
public import Ix.Claim
public import Ix.AssumptionTree
public import Ix.CompileM
public import Ix.Common
public import Ix.PrimAddrs
public import Ix.ClaimContext

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

2. **Closure layout**: `closureFrom` follows `Constant.refs`,
   projection block addresses, and the derived Muts→wrapper edges from
   a target address, then seeds primitive bytes — the same scope the
   Rust witness builder computes (`witness_scope` over
   `Env::bfs_closure`), so the IOBuffer carries everything the kernel
   can reach.

3. **IOBuffer population**: `addEntries` seeds the constants, blobs, and
   Defn reducibility hints on their own channels, each keyed by the
   address it belongs to. See the "IxVM IOBuffer interface" section
   below for the channel table and the binding argument.

4. **Witness construction**: `buildClaimWitness` serializes any
   `Ix.Claim`, seeds the bytes at `key = blake3(claim)`, pulls in the
   right closure per variant, and threads any caller-supplied
   `AssumptionTree`s under their merkle roots. The resulting
   `ClaimWitness` packs (a) the entrypoint name (`verify_claim`),
   (b) the packed 8-G public input (`claim_digest`), and (c) the populated
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

/-- Resolve a Lean name to its `Ixon.Env` `Address`, or fail with a
    descriptive `IO` error. Used by every claim/witness builder that
    starts from a Lean name. -/
def lookupAddr (ixonEnv : Ixon.Env) (name : Lean.Name) : IO Address :=
  match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
  | some addr => pure addr
  | none => throw <| IO.userError s!"{name} not found in Ixon environment"

/-- Nat / Bool constants the kernel's primitive dispatch synthesizes at
    reduction time (nat literal → succ chain, nat_beq/ble → Bool.true/
    false). Bytes for these MUST live in ch 2 for the kernel's `get_ci` to
    load them — but they may not be dependencies of the target's proof
    body. Seed them into the compile list. -/
def synthesizedPrimNames : Array Lean.Name :=
  #[`Bool.true, `Bool.false, `Nat.zero, `Nat.succ, `Bool,
    -- String-literal ctor expansion (str_lit_to_ctor): the def_eq
    -- Tier 1c / proj-head expansion fabricates Consts of these.
    `String, `String.ofList, `Char, `Char.ofNat, `List.nil, `List.cons]

/-- The Lean names of the roles' constants (`Ix.Kernel.Role.leanName`). Test
    environments compile them with their closures, so a claim finds the record
    of every role the default table binds when it validates the role's group. -/
def roleNames : Array Lean.Name :=
  Ix.Kernel.Role.all.toArray.map fun r => r.leanName.toString.toName

/-- The records, blobs and hints the default role table's roles and evidence
    are validated against (`IxC/Kernel/Ixon/RoleData.lean`): the prelude's
    basis records, the evidence theorems and the well-founded operations'
    dependency closure in the compiled `Init`. -/
def defaultTableSupport : Except String (Array (Address × Ixon.Constant) ×
    Array (Address × ByteArray) × Array (Address × Lean.ReducibilityHints)) := do
  let closure := Ix.Kernel.Reader.RoleData.closure
  let records := (← Ix.Kernel.Reader.preludeRecords) ++ (← Ix.Kernel.Reader.evidenceRecords)
    ++ (← Ix.Kernel.Reader.decodeCommitted "closure" closure)
  let blobs ← (Ix.Kernel.Reader.RoleData.blobs ++ Ix.Kernel.Reader.RoleData.closureBlobs).mapM
    fun (hex, bytes) => do
      let some a := Ix.Kernel.Reader.addressOfHex hex
        | throw s!"default table blob: bad address {hex}"
      let some b := bytesOfHex bytes | throw s!"default table blob: bad bytes at {hex}"
      pure (a, b)
  let hints ← Ix.Kernel.Reader.RoleData.closureHints.mapM fun (hex, h) => do
    let some a := Ix.Kernel.Reader.addressOfHex hex
      | throw s!"default table hint: bad address {hex}"
    let hint : Lean.ReducibilityHints ← match h with
      | "opaque" => pure .opaque
      | "abbrev" => pure .abbrev
      | n => match n.toNat? with
        | some k => pure (.regular k.toUInt32)
        | none => throw s!"default table hint: bad hint {n} at {hex}"
    pure (a, hint)
  pure (records, blobs, hints)

/-- `env` bound to the role table `bytes` (its binding section), together with
    the records the default table's roles and evidence are validated against
    (`defaultTableSupport`, each with the projection records of its blocks)
    wherever `env` lacks them. A table that rebinds roles among those
    constants needs no other support. -/
def withRoleTable (env : Ixon.Env) (bytes : ByteArray) : Except String Ixon.Env := do
  let (records, blobs, hints) ← defaultTableSupport
  let mut env := { env with roleBinding := some { address := Address.blake3 bytes, bytes } }
  let wrapper (info : Ixon.ConstantInfo) : Address × Ixon.Constant :=
    let c : Ixon.Constant := ⟨info, #[], #[], #[]⟩
    (Address.blake3 (Ixon.ser c), c)
  for (a, c) in records do
    let mut entries : Array (Address × Ixon.Constant) := #[(a, c)]
    if let .muts members := c.info then
      for (m, i) in members.zipIdx do
        let i := i.toUInt64
        match m with
        | .defn _ => entries := entries.push (wrapper (.dPrj ⟨i, a⟩))
        | .recr _ => entries := entries.push (wrapper (.rPrj ⟨i, a⟩))
        | .indc ind =>
          entries := entries.push (wrapper (.iPrj ⟨i, a⟩))
          for (_, cidx) in ind.ctors.zipIdx do
            entries := entries.push (wrapper (.cPrj ⟨i, cidx.toUInt64, a⟩))
    for (addr, record) in entries do
      unless env.consts.contains addr do
        env := env.storeConst addr record
  for (a, b) in blobs do
    unless env.blobs.contains a do
      env := { env with blobs := env.blobs.insert a b }
  for (a, h) in hints do
    unless env.anonHints.contains a do
      env := { env with anonHints := env.anonHints.insert a h }
  return env

/-- `env` with the default role table (`Ix.Kernel.Reader.defaultTable`) as its
    role binding when it carries none (`withRoleTable`). A claim is relative
    to its environment's binding (`Ix.ClaimContext.ofEnv`); environments
    compiled here from Lean declarations have none of their own. For tests
    and the command line, like that table. -/
def withDefaultRoleBinding (env : Ixon.Env) : Except String Ixon.Env := do
  if env.roleBinding.isSome then return env
  withRoleTable env (← Ix.Kernel.Reader.defaultTableBytes)

/-- Variant of loadIxonEnv: also seeds the constants the kernel's kernel
    fabricates during reduction (Bool.true/false + Nat.zero/succ), so
    their bytes are always in ch 2 even when the target's proof body
    doesn't textually reference them. -/
def loadIxonEnv (name : Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env := do
  let mut seen : Lean.NameSet := {}
  let mut deduped : Array (Lean.Name × Lean.ConstantInfo) := #[]
  let names : Array Lean.Name := #[name] ++ synthesizedPrimNames ++ roleNames
  for n in names do
    if leanEnv.constants.contains n then
      for entry in Lean.collectDependencies n leanEnv.constants do
        if !seen.contains entry.fst then
          seen := seen.insert entry.fst
          deduped := deduped.push entry
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI deduped.toList
  IO.ofExcept (withDefaultRoleBinding rawEnv.toEnv)

/-- Compile the union of `names`'s transitive closures into one shared
    Ixon env. Drivers like `KernelArena.lean` use this to pay the
    Lean→Ixon compile cost once and then build per-target IOBuffers via
    `buildClaimWitness` / `buildDbgCheckConst`. -/
def loadSharedIxonEnv (names : Array Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env := do
  let mut seen : Lean.NameSet := {}
  let mut deduped : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for n in names ++ roleNames.filter leanEnv.constants.contains do
    for entry in Lean.collectDependencies n leanEnv.constants do
      if !seen.contains entry.fst then
        seen := seen.insert entry.fst
        deduped := deduped.push entry
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI deduped.toList
  IO.ofExcept (withDefaultRoleBinding rawEnv.toEnv)

/-- The `refs` indices `e` uses as a CONSTANT: `Ref i` and the type index
    of `Prj i`. `Str`/`Nat` index blob payloads and `Rec` resolves through
    the block's members, so neither contributes. `Share` is not followed —
    every shared subexpression is itself an entry of `Constant.sharing`,
    walked separately. Mirrors `const_idxs_expr` in `Kernel/Claim.lean`. -/
partial def constIdxsExpr : Ixon.Expr → Std.HashSet UInt64
  | .ref i _ => {i}
  | .prj i _ inner => (constIdxsExpr inner).insert i
  | .app a b | .lam _ a b | .all _ _ a b =>
    (constIdxsExpr a).union (constIdxsExpr b)
  | .letE _ t v b =>
    ((constIdxsExpr t).union (constIdxsExpr v)).union (constIdxsExpr b)
  | _ => {}

/-- The `refs` indices `c` uses as constants, over its `sharing` table and
    every Expr its `ConstantInfo` carries. Mirrors `const_idxs_of` in
    `Kernel/Claim.lean` and `ixon::shard_claim::const_idxs_of`. -/
def constIdxsOf (c : Ixon.Constant) : Std.HashSet UInt64 := Id.run do
  let mut out : Std.HashSet UInt64 := {}
  for e in c.sharing do
    out := out.union (constIdxsExpr e)
  let ofDefn (d : Ixon.Definition) := (constIdxsExpr d.typ).union (constIdxsExpr d.value)
  let ofRecr (r : Ixon.Recursor) := r.rules.foldl
    (fun acc rule => acc.union (constIdxsExpr rule.rhs)) (constIdxsExpr r.typ)
  let ofIndc (i : Ixon.Inductive) := i.ctors.foldl
    (fun acc ctor => acc.union (constIdxsExpr ctor.typ)) (constIdxsExpr i.typ)
  match c.info with
  | .defn d => out := out.union (ofDefn d)
  | .recr r => out := out.union (ofRecr r)
  | .axio a => out := out.union (constIdxsExpr a.typ)
  | .quot q => out := out.union (constIdxsExpr q.typ)
  | .muts members =>
    for m in members do
      out := out.union <| match m with
        | .defn d => ofDefn d
        | .indc i => ofIndc i
        | .recr r => ofRecr r
  -- Projection wrappers carry no Exprs of their own.
  | _ => pure ()
  return out

/-- Content address of a synthesized projection wrapper: a `Constant`
    holding just the proj info with empty sharing/refs/univs tables,
    serialized and blake3-hashed — the same construction compile uses
    (and Rust `ixon::constant::*_proj_address`). -/
def projWrapperAddr (info : Ixon.ConstantInfo) : Address :=
  Address.blake3 (Ixon.ser (⟨info, #[], #[], #[]⟩ : Ixon.Constant))

/-- Walk the Constant ref-graph from `roots` to compute the set of
    addresses needed to type-check them. Mirrors Rust `Env::bfs_closure`:
    follow `Constant.refs`, the projection's `block` pointer
    (IPrj/CPrj/RPrj/DPrj), and — for a `Muts` block — every derived
    member/constructor projection wrapper address. The wrapper edges are
    what the kernel's lazy `get_ci` needs: it synthesizes those addrs via
    kernel-side blake3 and faults their bytes from ch 2, and no
    `Constant.refs` edge names them. -/
partial def closureFromRoots (env : Ixon.Env) (roots : Array Address) :
    Std.HashSet Address := Id.run do
  let mut visited : Std.HashSet Address := {}
  let mut worklist : Array Address := roots
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
    if let .muts members := c.info then
      let mut i : UInt64 := 0
      for m in members do
        let info : Ixon.ConstantInfo := match m with
          | .defn _ => .dPrj ⟨i, addr⟩
          | .indc _ => .iPrj ⟨i, addr⟩
          | .recr _ => .rPrj ⟨i, addr⟩
        worklist := worklist.push (projWrapperAddr info)
        if let .indc ind := m then
          let mut cidx : UInt64 := 0
          for _ in ind.ctors do
            worklist := worklist.push (projWrapperAddr (.cPrj ⟨i, cidx, addr⟩))
            cidx := cidx + 1
        i := i + 1
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

/-! ## IxVM IOBuffer interface

This section is the normative description of the host↔kernel interface.
The host seeds payloads on channels 0–6; the Aiur kernel consumes
them via `io_get_info` + `read_checked_byte_stream`, which range-checks every
byte and proves the list finite before anything hashes or parses it
(channel 3, an advisory value, is read unchecked). Each channel carries one
value shape and each key is the content address of the value it maps to
— no overloading, no in-band discriminators.

| Channel | Purpose                | Key (32 G)            | Value shape  |
|---------|------------------------|-----------------------|--------------|
| 0       | claim wire bytes       | packed `blake3(claim_bytes)` (8 G) | claim bytes  |
| 1       | assumption tree bytes  | `tree.root`           | tree bytes   |
| 2       | constant wire bytes    | const addr            | const bytes  |
| 3       | Defn reducibility hint | Defn addr             | single G     |
| 4       | blob raw bytes         | blob addr             | raw bytes    |
| 5       | resource profile       | profile addr          | profile bytes |
| 6       | role binding section   | binding hash          | `E8 03` bytes |

Channel 6 carries the role table a typing claim's context names, keyed by its
binding hash (`Ix.ClaimContext.binding`); the circuit reads its roles there
(`Ix/IxVM/Kernel/Roles.lean`). Channel 5 reserves the native resource-claim witness layout. IxVM currently
rejects `resource-v1` claims explicitly: a native validation result cannot be
used as a circuit proof. Its `Check` and `CheckEnv` claims assert erased Lean
typing and bind that validator identity in their hashed claim bytes.

An address is seeded on ch 2 iff it is a constant, and on ch 4 iff it is
a blob. The two sets are disjoint and neither carries an entry on the
other's channel.

Access pattern. Channels 0 and 1 are read once per `verify_claim`: the
claim itself, then its assumption tree if the variant carries one.
Channels 2, 3, and 4 are read on demand — `get_ci` faults a constant
the first time the check touches its address, and the reducibility hint
and blob payload follow from that same fault. Nothing is walked up
front, so what actually gets read is a subset of what the host seeds.

Binding. On channels 0, 2, 4, and 6 the kernel re-hashes the bytes it read
and asserts blake3 equality against the key, so the host cannot
substitute a payload. Channel 1 is bound the same way in effect but by a
different derivation: the kernel parses the tree and recomputes its
merkle root, which must equal the key — the tree's serialization is not
itself hashed. Channel 3 is advisory: it selects a WHNF reduction
heuristic and def-eq is sound under any value, so a lying hint costs
performance, never soundness.

`idx` and `len` from `io_get_info` are UNCONSTRAINED prover witness —
`Op::IOGetInfo` emits no constraint and no lookup. They are safe to use
for one thing only: locating bytes that are then bound. Read the wrong
span and the re-hash fails. **Never branch on `idx` or `len`** — a
control-flow decision taken on them is a decision the prover makes, and
it is taken before anything is bound.

Blob-vs-constant is derived from the bytes, not asked of the buffer.
Within a constant's `refs`, an entry is a blob iff some Expr node
references it as one — `Str(i)` / `Nat(i)` index blob payloads,
`Ref(i)` / `Prj(i, ..)` index constants — and `refs` is exactly the
union of those four (`crates/ixon/src/constant.rs`). An address reached
from outside any Expr (a claim target, a block address) is a constant
reference by Ixon convention. The same BYTES may be readable as both a
constant and a Nat or utf-8 string, so this Expr context is the only
correct discriminator; byte inspection cannot replace it. Blob-ness is
therefore a POSITIVE property computed from hash-bound bytes, and every
address lacking it is a constant that must be walked.

Channel numbers MUST stay in sync with the inlined `io_get_info` /
`read_checked_byte_stream` literals in `Ix/IxVM/Ingress.lean` and
`Ix/IxVM/Kernel/Claim.lean`. Channel 0 is reused with a different key
shape by the test and benchmark entrypoints (`blake3_test`,
`ixon_serde_test`, …); those never run in the same execution as
`verify_claim`, so the one-shape-per-channel rule holds for every
production path.
-/

/-- Insert all per-address entries for `addr`s satisfying `keep` into
    `ioBuffer`. See the channel table above. -/
def addEntries (ixonEnv : Ixon.Env) (keep : Address → Bool)
    (ioBuffer : Aiur.IOBuffer) : Aiur.IOBuffer := Id.run do
  let mut ioBuffer := ioBuffer
  for (addr, lc) in ixonEnv.consts do
    if !keep addr then continue
    -- The kernel re-hashes these bytes against the key, so feed the exact
    -- serialized form the lazy entry holds — no materialization needed.
    let bytes := lc.rawBytes
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 2 key (bytes.data.map .ofUInt8)
  for (addr, rawBytes) in ixonEnv.blobs do
    if !keep addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 4 key (rawBytes.data.map fun b => .ofNat b.toNat)
  for (addr, hints) in ixonEnv.anonHints do
    if !keep addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 3 key #[hintToG hints]
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

/-- An `Address` as 8 packed-4-LE-byte field elements: the `verify_claim`
    public-input (and ch-0 key) form. Must match the in-circuit `b3_pack`. -/
@[inline] def packedDigestKey (a : Address) : Array Aiur.G :=
  let h := a.hash.data
  (Array.range 8).map fun i =>
    .ofNat (h[4*i]!.toNat + 256 * h[4*i+1]!.toNat
      + 65536 * h[4*i+2]!.toNat + 16777216 * h[4*i+3]!.toNat)

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
    .ok (ioBuffer.extend 1 (addrKey tree.root) (bytes.data.map .ofUInt8))
  | none => .error s!"no assumption tree supplied for root {root}"

/-- The constants the role binding names: every bound role and every proof
    evidence theorem the environment carries. Role validation reads them, so
    they and their closures are in every witness's byte scope. Mirrors Rust
    `binding_roots`. -/
def bindingRoots (env : Ixon.Env) : Array Address := Id.run do
  let some binding := env.roleBinding | return #[]
  let some table := Ix.Kernel.RoleTable.ofBytes binding.bytes | return #[]
  let mut roots := table.bound.map (·.2)
  for (_, entries) in table.evidence do
    for e in entries do
      if let .proof a := e then roots := roots.push a
  return roots.filter env.consts.contains

/-- Seed the environment's role binding on channel 6, keyed by its hash: the
    circuit reads a claim's roles there. -/
def seedBinding (env : Ixon.Env) (ioBuffer : Aiur.IOBuffer) : Aiur.IOBuffer :=
  match env.roleBinding with
  | some binding =>
    ioBuffer.extend 6 (addrKey binding.address) (binding.bytes.data.map .ofUInt8)
  | none => ioBuffer

/-- The full witness byte scope for `target`: the closure of `target`
    together with every primitive address present in `env` and the role
    binding's constants (`bindingRoots`), all as walk ROOTS. Mirrors Rust
    `witness_scope`.

    Primitives are seeded because the kernel fabricates
    `Const(Std(prim_addr))` refs inline via `mk_prim_const`
    (Whnf/Infer/NatPrim), which triggers a load bypassing the ref walk —
    those addresses need not appear in any `Constant.refs`.

    Their closures are walked, not just their own bytes: def-eq
    delta-unfolds primitive BODIES (the `strAppend*` arena fixtures do
    exactly this), and a body's refs are reachable from nowhere else in
    the scope. Shipping the address alone aborts those with `invalid IO
    key`. -/
def closureFrom (env : Ixon.Env) (target : Address) : Std.HashSet Address :=
  closureFromRoots env
    (#[target] ++ Ix.primAddrSet.toArray.filter env.consts.contains
      ++ bindingRoots env)

/-- Serializes `claim`, seeds its bytes at `key = blake3(claim)`, and
    populates the IOBuffer with the `closureFrom` byte scope of every
    address the claim variant names (plus any caller-supplied
    `AssumptionTree`s under their merkle roots). -/
def buildClaimWitness (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {})
    (profiles : Std.HashMap Address ByteArray := {}) :
    Except String ClaimWitness := do
  let env ← withDefaultRoleBinding env
  let claimBytes := Ix.Claim.ser claim
  let digestKey := packedDigestKey (Address.blake3 claimBytes)
  let mut ioBuffer : Aiur.IOBuffer := seedBinding env default
  ioBuffer := ioBuffer.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  let seedAsm asm buf := match asm with
    | some r => seedTreeAt r trees buf
    | none => .ok buf
  match claim with
  | .check _ addr asm =>
    ioBuffer := addEntries env (closureFrom env addr).contains ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .eval _ input output asm =>
    let inputClosure := closureFrom env input
    let outputClosure := closureFrom env output
    ioBuffer := addEntries env
      (fun a => inputClosure.contains a || outputClosure.contains a) ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .checkEnv _ root asm =>
    ioBuffer := addEntries env (fun _ => true) ioBuffer
    ioBuffer ← seedTreeAt root trees ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .resource root profile =>
    ioBuffer := addEntries env (fun _ => true) ioBuffer
    ioBuffer ← seedTreeAt root trees ioBuffer
    let some bytes := profiles[profile]? <|> env.blobs[profile]?
      | throw s!"no resource profile supplied for {profile}"
    unless Address.blake3 bytes == profile do throw "resource profile hash mismatch"
    ioBuffer := ioBuffer.extend 5 (addrKey profile) (bytes.data.map .ofUInt8)
  | .reveal comm _info =>
    ioBuffer := addEntries env (closureFrom env comm).contains ioBuffer
  | .contains tree _target =>
    ioBuffer ← seedTreeAt tree trees ioBuffer
  | .binding _ bound =>
    -- Every bound role and evidence theorem, with their closures: the
    -- circuit validates every group. The primitives the kernel fabricates
    -- references to are seeded as `closureFrom` seeds them.
    unless env.roleBinding.map (·.address) == some bound do
      throw s!"the environment's role binding is not {bound}"
    let roots := Ix.primAddrSet.toArray.filter env.consts.contains ++ bindingRoots env
    ioBuffer := addEntries env (closureFromRoots env roots).contains ioBuffer
  | .catalog .. =>
    -- A catalog claim collects other claims; it is formed and verified only
    -- by aggregation (`ix_aggr` shape 16), never by one IxVM run.
    throw "catalog claims have no single-run witness; they are formed by \
aggregating their members' check-env claims"
  return { funcName := `verify_claim
           input := digestKey, inputIOBuffer := ioBuffer }

/-- The kernel shard claim and its canonical subject/assumption trees, without
    constructing the witness byte closure. This is the claim-only path used by
    aggregation and verification: those callers need the Merkle trees but do
    not consume the dependency bytes, so walking the full closure would be
    pure discarded work.

    The frontier is THIN: asm = the DIRECT out-of-owned
    walk edges (refs + Prj→block) of the owned constants, not the full
    `closure ∖ owned`. the kernel's env walk exits the shard only through a
    direct external edge and stops there, so everything below the first
    layer is dead weight in the asm tree. Deterministic in
    `(env, owned)` — canonical trees sort addresses — so prove/verify
    digests agree. Every edge — `refs` and the `Prj → block` edge alike —
    is admitted only when it is outside `owned` AND present in
    `env.consts`, matching `ixon::shard_claim::frontier_of`. An edge absent
    from `env.consts` is not something the kernel walk can reach, so
    including it would inflate the asm tree and break digest agreement
    between the Rust prover and this verifier. -/
def shardCheckEnvClaimTrees (env : Ixon.Env) (owned : Array Address) :
    Except String (Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  let env ← withDefaultRoleBinding env
  let ownedSet : Std.HashSet Address := owned.foldl (·.insert ·) {}
  let frontier : Array Address := Id.run do
    let mut fs : Std.HashSet Address := {}
    for o in owned do
      match env.getConst? o with
      | none => pure ()
      | some c =>
        -- Only the indices some Expr uses as a constant are walk edges,
        -- matching the kernel's `env_walk_refs`. A `refs` entry no Expr
        -- names as a constant is never walked in-circuit, so admitting it
        -- would put a phantom member in the frontier.
        let used := constIdxsOf c
        for (r, i) in c.refs.zipIdx do
          if used.contains i.toUInt64 && !ownedSet.contains r
              && env.consts.contains r then
            fs := fs.insert r
        let blockOpt : Option Address := match c.info with
          | .iPrj p => some p.block
          | .cPrj p => some p.block
          | .rPrj p => some p.block
          | .dPrj p => some p.block
          | _ => none
        match blockOpt with
        | some b =>
          if !ownedSet.contains b && env.consts.contains b then
            fs := fs.insert b
        | none => pure ()
    return fs.toArray
  let some ownedTree := Ix.AssumptionTree.canonical owned
    | .error "shardCheckEnvClaim: empty owned set"
  let asmTree? := Ix.AssumptionTree.canonical frontier
  let ctx ← Ix.ClaimContext.ofEnv env
  let claim := Ix.Claim.checkEnv ctx ownedTree.root (asmTree?.map (·.root))
  let mut trees : Std.HashMap Address Ix.AssumptionTree :=
    ({} : Std.HashMap Address Ix.AssumptionTree).insert ownedTree.root ownedTree
  match asmTree? with
  | some asmTree => trees := trees.insert asmTree.root asmTree
  | none => pure ()
  pure (claim, trees)

/-- Claim/tree construction plus the byte closure needed by a Lean-built shard
    witness. Reachability distributes over root union, so one graph walk from
    all owned and primitive roots is exactly the old union of one
    `closureFrom` walk per owned constant, without repeatedly traversing the
    same shared dependency core. -/
def shardCheckEnvClaim (env : Ixon.Env) (owned : Array Address) :
    Except String (Ix.Claim × Std.HashSet Address × Std.HashMap Address Ix.AssumptionTree) := do
  let env ← withDefaultRoleBinding env
  let (claim, trees) ← shardCheckEnvClaimTrees env owned
  let primitiveRoots := Ix.primAddrSet.toArray.filter env.consts.contains
  let closure := closureFromRoots env (owned ++ primitiveRoots ++ bindingRoots env)
  pure (claim, closure, trees)

/-- Variant of `buildShardCheckEnvWitness`: THIN frontier asm (see
    `shardCheckEnvClaimTrees`) with the `closureFrom` byte scope, which
    carries the IPrj/CPrj/RPrj/DPrj wrappers the kernel's `get_ci`
    synthesizes via kernel-side blake3 as forward Muts→wrapper edges. -/
def buildShardCheckEnvWitness (env : Ixon.Env) (owned : Array Address) :
    Except String (Ix.Claim × ClaimWitness) := do
  let env ← withDefaultRoleBinding env
  let (claim, closure, trees) ← shardCheckEnvClaim env owned
  let claimBytes := Ix.Claim.ser claim
  let digestKey := packedDigestKey (Address.blake3 claimBytes)
  let mut ioBuffer : Aiur.IOBuffer := seedBinding env default
  ioBuffer := ioBuffer.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  ioBuffer := addEntries env closure.contains ioBuffer
  for (root, _) in trees do
    ioBuffer ← seedTreeAt root trees ioBuffer
  return (claim, { funcName := `verify_claim
                   input := digestKey, inputIOBuffer := ioBuffer })

/-- Canonical merkle tree over every const address in `env`. Returns
    `none` for an empty env. Convenience for callers that want to
    issue a `CheckEnv` claim against the env's canonical merkle root. -/
def envCanonicalTree (env : Ixon.Env) : Option Ix.AssumptionTree :=
  Ix.AssumptionTree.canonical (env.consts.keys.toArray)

/-- Subject-only `verify_const` witness: the `closureFrom` byte scope
    (which carries the kernel-side blake3-synthesized projection
    wrappers as forward edges) faulted from ch 2, under the environment's
    role binding (seeded on ch 6). -/
def buildVerifyConst (env : Ixon.Env) (target : Address) : Except String ClaimWitness := do
  let env ← withDefaultRoleBinding env
  let some binding := env.roleBinding
    | throw "verify_const: the environment carries no role binding"
  let closure := closureFrom env target
  let ioBuffer := addEntries env closure.contains (seedBinding env default)
  return { funcName := `verify_const
           input := addrKey binding.address ++ addrKey target, inputIOBuffer := ioBuffer }

end IxVM.ClaimHarness

end
