module

public import LSpec
public import Ix.Tc
public import Ix.CompileM
public import Ix.Meta
public import Ix.Common

/-!
Node-address bit-compatibility harness (`tc-node-addr`, ignored suite).

Compiles a Lean closure through the Rust compiler (`rsCompileEnvBytesFFI`),
then ingresses the same serialized env twice: through the Rust kernel's anon
ingress (`rs_kernel_ingress_anon_addrs`, test-ffi) and through the pure-Lean
`Ix.Tc` ingress. Every kernel constant's `(kid, tyAddr, valAddr-or-ruleAddrs)`
row must match byte-for-byte — root-address equality transitively certifies
every child node hash, so a divergence anywhere in the Blake3 preimage chain
localizes here instead of surfacing later as inscrutable def-eq mismatches.
-/

namespace Tests.Tc.NodeAddr

open LSpec
open Ix.Tc

/-- Rust oracle: ingress a serialized env's anon work set into `KEnv<Anon>`
    and dump sorted `(kidHex, tyAddrHex, extraHex)` rows (extra = Defn value
    address, or comma-joined recursor rule-RHS addresses, or empty). -/
@[extern "rs_kernel_ingress_anon_addrs"]
private opaque rsKernelIngressAnonAddrsFFI :
  @& ByteArray → IO (Array (String × String × String))

/-- The same dump for a Lean-side kernel env. -/
def dumpKEnvAddrs (kenv : AnonEnv) : Array (String × String × String) :=
  let rows := kenv.consts.toList.toArray.map fun (id, c) =>
    let extra := match c with
      | .defn (val := val) .. => toString val.addr
      | .recr (rules := rules) .. =>
        String.intercalate "," (rules.toList.map (toString ·.rhs.addr))
      | _ => ""
    (toString id.addr, toString c.ty.addr, extra)
  rows.qsort fun a b => a.1 < b.1

/-- Transitive dependency closure of `seeds` as a `(Name, ConstantInfo)`
    list, deduplicated. -/
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

/-- Run the differential for one seed list. Returns
    `(rustRows, leanRows, firstDiff?)`. -/
def diffOnSeeds (leanEnv : Lean.Environment) (seeds : List Lean.Name) :
    IO (Nat × Nat × Option String) := do
  let consts := closureOf leanEnv seeds
  if consts.isEmpty then
    return (0, 0, some s!"empty closure for {seeds}")
  -- The compile FFI streams to a file (no env-sized ByteArray crosses
  -- the FFI); round-trip through a temp path.
  let dir ← IO.FS.createTempDir
  let path := dir / "tc-node-addr.ixe"
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  let rustRows ← rsKernelIngressAnonAddrsFFI bytes
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .ok env => pure env
    | .error e => return (rustRows.size, 0, some s!"deEnvAnon failed: {e}")
  let leanRows ← match (ingressAll ixonEnv).run {} with
    | .ok _ kenv => pure (dumpKEnvAddrs kenv)
    | .error e _ => return (rustRows.size, 0, some s!"Lean ingress failed: {e}")
  if rustRows.size != leanRows.size then
    -- Report the first key present on one side only.
    let rustKeys := rustRows.map (·.1)
    let leanKeys := leanRows.map (·.1)
    let onlyRust := rustKeys.filter (!leanKeys.contains ·)
    let onlyLean := leanKeys.filter (!rustKeys.contains ·)
    return (rustRows.size, leanRows.size,
      some s!"row count mismatch: rust {rustRows.size} vs lean {leanRows.size}; only-rust {onlyRust.toList.take 3} only-lean {onlyLean.toList.take 3}")
  for (r, l) in rustRows.zip leanRows do
    if r != l then
      return (rustRows.size, leanRows.size,
        some s!"row mismatch:\n  rust {r}\n  lean {l}")
  return (rustRows.size, leanRows.size, none)

def seedSets : List (String × List Lean.Name) :=
  [ ("Nat.add closure", [`Nat.add]),
    ("List.map closure", [`List.map]),
    ("Nat.rec + Eq closure", [`Nat.rec, `Eq.refl]),
    ("decidable/bool closure", [`Nat.decEq, `Bool.rec]),
    ("mixed arithmetic closure", [`Nat.mul, `Nat.pow, `Nat.ble]) ]

def diffSuite : TestSeq := Id.run do
  let mut ts : TestSeq := .done
  for (label, seeds) in seedSets do
    ts := ts ++ .individualIO s!"node-addr parity: {label}" none (do
      let env ← get_env!
      let (nRust, nLean, err?) ← diffOnSeeds env seeds
      return (err?.isNone, nRust, nLean, err?)) .done
  return ts

public def suite : List TestSeq := [diffSuite]

end Tests.Tc.NodeAddr
