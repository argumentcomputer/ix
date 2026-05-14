module
public import Ix.Aiur.Protocol
public import Ix.Ixon
public import Ix.CompileM
public import Ix.Common

public section

namespace IxVM.CheckHarness

/-- Run the Lean → Ixon FFI pipeline for `name`'s transitive closure. -/
def loadIxonEnv (name : Lean.Name) (leanEnv : Lean.Environment) : IO Ixon.Env := do
  let constList := Lean.collectDependencies name leanEnv.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  pure rawEnv.toEnv

/-- Compile the union of `names`'s transitive closures into one shared
    Ixon env. Drivers like `KernelArena.lean` use this to pay the
    Lean→Ixon compile cost once and then build per-target IOBuffers via
    `buildKernelCheckIOBufferFor`. -/
def loadSharedIxonEnv (names : Array Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env := do
  let constList := names.foldl (init := []) fun acc n =>
    Lean.collectDependencies n leanEnv.constants ++ acc
  let mut seen : Lean.NameSet := {}
  let mut deduped : List (Lean.Name × Lean.ConstantInfo) := []
  for entry in constList do
    if !seen.contains entry.fst then
      seen := seen.insert entry.fst
      deduped := entry :: deduped
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI deduped
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
    match env.consts.get? addr with
    | none => pure ()
    | some c =>
      for r in c.refs do
        if !visited.contains r then worklist := worklist.push r
      let blockAddr? : Option Address := match c.info with
        | .iPrj p => some p.block
        | .cPrj p => some p.block
        | .rPrj p => some p.block
        | .dPrj p => some p.block
        | _ => none
      match blockAddr? with
      | some ba => if !visited.contains ba then worklist := worklist.push ba
      | none => pure ()
  return visited

/-- Build the `ixon_serde_test` / `ixon_serde_blake3_bench` IOBuffer:
    one entry per const, keyed by its index. Returns the buffer and the
    count `n` (which the Aiur entrypoint receives as input). -/
def buildSerdeIOBuffer (ixonEnv : Ixon.Env) : Aiur.IOBuffer × Nat :=
  ixonEnv.consts.valuesIter.fold (init := (default, 0)) fun (ioBuffer, i) c =>
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    (ioBuffer.extend #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)

/-- Encode a `Lean.ReducibilityHints` as a single `G` per the convention
    Aiur's `load_constant_hint` decodes (opaque → 0, abbrev → 0xFFFFFFFF,
    regular n → clamp(1 + n, 0xFFFFFFFE)). -/
private def hintToG : Lean.ReducibilityHints → Aiur.G
  | .opaque => .ofNat 0
  | .abbrev => .ofNat 0xFFFFFFFF
  | .regular n =>
    let v := 1 + n.toNat
    .ofNat (if v > 0xFFFFFFFE then 0xFFFFFFFE else v)

/-- Insert all per-address entries for `addr`s satisfying `keep` into
    `ioBuffer`, following the IOBuffer convention:

    | key                    | value          | meaning |
    |------------------------|----------------|---------|
    | `addr` (32 G)          | const bytes    | primary data; empty value = `addr` is a blob |
    | `addr ++ [0]` (33 G)   | raw blob bytes | referenced data (verified by Aiur via blake3) |
    | `addr ++ [1]` (33 G)   | single G       | Defn `ReducibilityHints` encoding |

    Suffix tags use `Array.push` (O(1) amortized) rather than prefix
    `++ Array` (O(n) allocation). -/
private def addEntries (ixonEnv : Ixon.Env) (keep : Address → Bool)
    (ioBuffer : Aiur.IOBuffer) : Aiur.IOBuffer := Id.run do
  let mut ioBuffer := ioBuffer
  for (addr, c) in ixonEnv.consts do
    if !keep addr then continue
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend key (bytes.data.map .ofUInt8)
  for (addr, rawBytes) in ixonEnv.blobs do
    if !keep addr then continue
    let hashKey : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend (hashKey.push 0)
      (rawBytes.data.map fun b => .ofNat b.toNat)
    ioBuffer := ioBuffer.extend hashKey #[]
  for (_, named) in ixonEnv.named do
    if !keep named.addr then continue
    match named.constMeta with
    | .defn _ _ hints _ _ _ _ _ =>
      let hashKey : Array Aiur.G := named.addr.hash.data.map .ofUInt8
      ioBuffer := ioBuffer.extend (hashKey.push 1) #[hintToG hints]
    | _ => pure ()
  return ioBuffer

/-- Build the full `kernel_check_test` IOBuffer for the entire `ixonEnv`. -/
def buildKernelCheckIOBuffer (ixonEnv : Ixon.Env) : Aiur.IOBuffer :=
  addEntries ixonEnv (fun _ => true) default

/-- Blake3 address bytes of `name` (the target input to `kernel_check_test`). -/
def kernelCheckTarget (name : Lean.Name) (ixonEnv : Ixon.Env) : Array Aiur.G :=
  match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
  | some addr => addr.hash.data.map .ofUInt8
  | none => panic! s!"{name} not found in Ixon environment"

/-- Build a minimal `kernel_check_test` IOBuffer reachable from `target`
    in `ixonEnv`. Used by drivers (e.g. `KernelArena.lean`) that compile
    a single shared env once and then check many targets against it. -/
def buildKernelCheckIOBufferFor (ixonEnv : Ixon.Env) (target : Address) :
    Aiur.IOBuffer :=
  let closure := closureFrom ixonEnv target
  addEntries ixonEnv closure.contains default

end IxVM.CheckHarness

end
