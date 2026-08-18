/-
  Dump ORIGINAL (LEON content-hash) primitive addresses for hardcoding
  into the Rust kernel (`crates/common/src/prim_addrs.rs::PrimAddrs::new_orig`).

  Run with: `lake test -- --ignored rust-kernel-build-prim-origs`. The test prints a
  `(lean_name, leon_hash_hex)` line for every primitive the Rust kernel
  expects to find in `PrimAddrs::new_orig`. Each hex is
  `ConstantInfo::get_hash()` (defined in `src/ix/env.rs`) on the
  primitive's declaration in the current Lean environment — a Blake3
  digest over the serialized original `ConstantInfo` (name + level
  params + type expression + variant-specific fields: ctors, rules,
  `all`, value, hints, etc.).

  This is the addressing scheme `orig_kenv` uses: two Lean constants
  with the same name but different content hash to different addresses,
  so a rogue environment can't silently shadow a primitive just by
  naming its own declaration `Nat`.

  Paste the output lines into `PrimAddrs::new_orig` whenever either:
  - a primitive's Lean-side name or content changes upstream, or
  - the `ConstantInfo::get_hash` byte layout is revised.

  The primitive name list itself is shared with
  `Tests.Ix.Kernel.BuildPrimitives.kernelPrimitives` — a single source
  of truth. When upstream Lean renames a primitive, update that list
  once and regenerate BOTH this table AND the canonical one (via
  `rust-kernel-build-primitives`).

  Failure modes:
  - Missing: a primitive name isn't in the Lean env (likely renamed
    upstream). Printed as `// MISSING:` comments so the emitted table is
    still valid as-is for partial regeneration.
  - Address change: the LEON hex for a primitive has changed — paste
    the new hex into `PrimAddrs::new_orig`.
-/
import Ix.Common
import Ix.CompileM            -- rsLeonHashesFFI
import Ix.Environment
import Ix.Address
import Tests.Ix.Kernel.BuildPrimitives
import LSpec

open LSpec

namespace Tests.Ix.Kernel.BuildPrimOrigs

open Tests.Ix.Kernel.BuildPrimitives (kernelPrimitives getConstRefs collectDeps parseNameToLean)

/-- Dump the current `(name, leon_hash_hex)` table for every entry in
    `Tests.Ix.Kernel.BuildPrimitives.kernelPrimitives`. Pass iff every
    entry resolves; missing names are printed as `// MISSING:` comments
    so the output is still valid as-is for partial regeneration.

    Mirrors the structure of `BuildPrimitives.testBuildPrimitives` — the
    only semantic difference is the hash we dump (LEON
    `ConstantInfo::get_hash` vs. the canonical post-compile content
    address). -/
def testBuildPrimOrigs : TestSeq :=
  .individualIO "build prim-origs dump" none (do
    let leanEnv ← get_env!
    let roots := kernelPrimitives.map parseNameToLean
    let needed := collectDeps leanEnv roots
    let filtered := leanEnv.constants.toList.filter fun (name, _) =>
      needed.contains name

    IO.println s!"[build-prim-origs] {filtered.length} constants in transitive closure"

    -- Compute LEON hashes for every constant in the transitive closure.
    let pairs : Array (Ix.Name × Address) ← Ix.CompileM.rsLeonHashesFFI filtered

    IO.println s!"[build-prim-origs] LEON hashes computed: {pairs.size}"

    -- Build Ix.Name → Address lookup.
    let mut byName : Std.HashMap Ix.Name Address := {}
    for p in pairs do
      byName := byName.insert p.1 p.2

    IO.println ""
    IO.println "// === Primitive ORIGINAL (LEON content-hash) addresses ==="
    IO.println "// Format: (\"lean_name\", \"leon_hash_hex\")"
    IO.println "// Hash: ConstantInfo::get_hash (src/ix/env.rs) —"
    IO.println "//       Blake3 over the serialized original ConstantInfo."
    IO.println "// These are the addresses KIds live at in `orig_kenv`."
    IO.println ""

    let mut found : Nat := 0
    let mut missing : Array String := #[]

    for primName in kernelPrimitives do
      let ixName := Ix.Name.fromLeanName (parseNameToLean primName)
      match byName[ixName]? with
      | none =>
        IO.println s!"// MISSING: {primName}"
        missing := missing.push primName
      | some addr =>
        let addrHex := toString addr
        IO.println s!"(\"{primName}\", \"{addrHex}\"),"
        found := found + 1

    IO.println ""
    IO.println s!"// Found: {found}/{kernelPrimitives.size}"
    if !missing.isEmpty then
      IO.println s!"// Missing: {missing}"

    let msg : Option String :=
      if missing.isEmpty then none else some s!"{missing.size} primitives missing from Lean env"
    return (missing.isEmpty, found, missing.size, msg)
  ) .done

@[extern "rs_prim_addrs_orig"]
opaque rsPrimAddrsOrigFFI : IO (Array (String × String))

/-- Every original/LEON primitive address stored in `PrimAddrs::new_orig()`
    must match `ConstantInfo::get_hash()` over the live Lean environment.
    `eagerReduce` is excluded because its original address is a synthetic
    kernel marker rather than the hash of the Lean declaration. -/
def testPrimOrigsParity : TestSeq :=
  .individualIO "original primitive address parity (PrimAddrs vs live LEON hashes)" none (do
    let leanEnv ← get_env!
    let roots := kernelPrimitives.map parseNameToLean
    let needed := collectDeps leanEnv roots
    let filtered := leanEnv.constants.toList.filter fun (name, _) =>
      needed.contains name
    let pairs : Array (Ix.Name × Address) ← Ix.CompileM.rsLeonHashesFFI filtered

    let live : Std.HashMap Ix.Name Address :=
      pairs.foldl (init := {}) fun m (name, addr) => m.insert name addr
    let hardcoded ← rsPrimAddrsOrigFFI
    let lookup : Std.HashMap String String :=
      hardcoded.foldl (init := {}) fun m (name, hex) => m.insert name hex

    let mut mismatches : Array String := #[]
    let mut missing : Array String := #[]
    let hardcodedNames := hardcoded.map fun (name, _) => name
    if hardcodedNames != kernelPrimitives then
      mismatches := mismatches.push
        s!"primitive catalog mismatch: expected {kernelPrimitives}, got {hardcodedNames}"

    for primName in kernelPrimitives do
      if primName == "eagerReduce" then continue
      let ixName := Ix.Name.fromLeanName (parseNameToLean primName)
      match live[ixName]? with
      | none => missing := missing.push primName
      | some liveAddr =>
        match lookup[primName]? with
        | none =>
          mismatches := mismatches.push
            s!"{primName}: missing from PrimAddrs::lean_orig_parity_table"
        | some hardcodedHex =>
          let liveHex := toString liveAddr
          if liveHex != hardcodedHex then
            mismatches := mismatches.push
              s!"{primName}: live={liveHex} PrimAddrs={hardcodedHex}"

    if !missing.isEmpty then
      IO.eprintln s!"original primitive parity: {missing.size} primitive(s) missing from Lean env:"
      for name in missing do IO.eprintln s!"  {name}"
    if !mismatches.isEmpty then
      IO.eprintln s!"original primitive parity: {mismatches.size} mismatch(es):"
      for mismatch in mismatches do IO.eprintln s!"  {mismatch}"
      IO.eprintln "Regenerate via `lake test -- --ignored rust-kernel-build-prim-origs` and paste into PrimAddrs::new_orig in crates/common/src/prim_addrs.rs."

    let totalProblems := missing.size + mismatches.size
    let passed := kernelPrimitives.size - min totalProblems kernelPrimitives.size
    let msg : Option String :=
      if totalProblems == 0 then none
      else some s!"{mismatches.size} mismatch(es), {missing.size} missing"
    return (totalProblems == 0, passed, totalProblems, msg)
  ) .done

def paritySuite : List TestSeq := [testPrimOrigsParity]

def suite : List TestSeq := [testBuildPrimOrigs]

end Tests.Ix.Kernel.BuildPrimOrigs
