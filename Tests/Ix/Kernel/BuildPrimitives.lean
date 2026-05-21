/-
  Dump primitive constant names and content-addresses for hardcoding into the
  Rust kernel (`src/ix/kernel/primitive.rs`).

  Run with: `lake test -- rust-kernel-build-primitives`. The test prints a
  `(lean_name, content_address_hex)` line for every primitive the Rust
  kernel expects to find in `PrimAddrs::new`. Paste the output over the
  corresponding entries whenever Lean's stdlib changes and tests start
  failing with `@<hex>@<hex>` / synthetic-KId fallbacks.

  Failure modes:
  - Missing: a primitive name isn't in the Lean env (likely renamed upstream).
    Fix by updating `kernelPrimitives` below to match the new name.
  - Address change: the address for a primitive has changed — paste the new
    hex into `PrimAddrs::new`.
-/
import Ix.Common
import Ix.CompileM
import Ix.Meta
import Ix.Address
import Ix.Environment
import Ix.Ixon
import LSpec

open LSpec

namespace Tests.Ix.Kernel.BuildPrimitives

/-- The Lean names of every primitive the Rust kernel resolves in
    `PrimAddrs::new`. Keep this in sync with the `Primitives<M>` struct in
    `src/ix/kernel/primitive.rs`. -/
def kernelPrimitives : Array String := #[
  "Nat", "Nat.zero", "Nat.succ",
  "Nat.add", "Nat.pred", "Nat.sub", "Nat.mul", "Nat.pow",
  "Nat.gcd", "Nat.mod", "Nat.div", "Nat.bitwise",
  "Nat.beq", "Nat.ble",
  "Nat.land", "Nat.lor", "Nat.xor",
  "Nat.shiftLeft", "Nat.shiftRight",
  "Bool", "Bool.true", "Bool.false",
  "String", "String.mk",
  "Char", "Char.mk", "Char.ofNat",
  "String.ofList",
  "List", "List.nil", "List.cons",
  "Eq", "Eq.refl",
  "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
  "Lean.reduceBool", "Lean.reduceNat", "eagerReduce",
  "System.Platform.numBits",
  "System.Platform.getNumBits", "Subtype.val",
  "String.toByteArray", "ByteArray.empty",
  "Nat.decLe", "Nat.decEq", "Nat.decLt",
  "Decidable.rec", "Decidable.isTrue", "Decidable.isFalse",
  "Nat.le_of_ble_eq_true", "Nat.not_le_of_not_ble_eq_true",
  "Nat.eq_of_beq_eq_true", "Nat.ne_of_beq_eq_false",
  "Fin",
  "Bool.noConfusion",
  -- Int + ctors + ops. Native reduction for Int operations short-circuits
  -- the symbolic `Int.rec` + `decNonneg` cascade that would otherwise get
  -- stuck at `Decidable.rec (LT.lt Int ...)` inside bodies like `Int.bmod`.
  -- Lean's stdlib uses `Int.ble'` / `Int.blt'` ("for kernel reduction")
  -- for the symbolic path; our kernel takes the native path instead.
  "Int", "Int.ofNat", "Int.negSucc",
  "Int.add", "Int.sub", "Int.mul", "Int.neg",
  "Int.emod", "Int.ediv",
  "Int.bmod", "Int.bdiv",
  "Int.natAbs", "Int.pow",
  "Int.decEq", "Int.decLe", "Int.decLt",
  -- Below/brecOn dependencies — referenced by aux_gen, not Primitives<M>
  -- directly. Kept here so the dump is complete enough to debug drift.
  "PUnit", "PProd", "PProd.mk",
  -- Names previously matched via `is_const_named` (string compare on
  -- `id.name`) in src/ix/kernel/whnf.rs. Under alpha-canonical content
  -- hashing, expressions ingested with one alpha-twin's name (e.g.
  -- `Lean.RBColor.rec`) miss any name-based check that expected the
  -- canonical name (e.g. `Bool.rec`), even though the addresses match.
  -- Hardcoding the address per name flips those callsites to address-only
  -- comparison, which is alpha-stable.
  "Nat.rec", "Nat.casesOn",
  "BitVec", "BitVec.toNat", "BitVec.ofNat", "BitVec.ult",
  "Decidable.decide",
  "LT.lt",
  "OfNat.ofNat",
  "Unit", "PUnit._sizeOf_1",
  "SizeOf.sizeOf",
  "String.back", "String.Legacy.back", "String.utf8ByteSize"
]

/-- Parse a dotted string into a `Lean.Name`, preferring numeric components
    when the part parses as `Nat`. Mirrors the ix_old helper.

    Public so `Tests.Ix.Kernel.BuildPrimOrigs` (the LEON-hash sister test)
    can share the same parse logic. -/
def parseNameToLean (s : String) : Lean.Name := Id.run do
  let mut name := Lean.Name.anonymous
  for part in s.splitOn "." do
    if let some n := part.toNat? then
      name := .num name n
    else
      name := .str name part
  return name

/-- Collect the transitive Const refs of a `ConstantInfo`. Mirrors ix_old. -/
def getConstRefs : Lean.ConstantInfo → Array Lean.Name
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .axiomInfo v  => v.type.getUsedConstants
  | .ctorInfo v   => v.type.getUsedConstants ++ #[v.induct]
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors ++ v.all
  | .recInfo v    => v.type.getUsedConstants ++ v.all
      ++ (v.rules.toArray.flatMap (fun r => r.rhs.getUsedConstants ++ #[r.ctor]))
  | .quotInfo v   => v.type.getUsedConstants

/-- Closure over all constants transitively referenced from `roots`. -/
partial def collectDeps (env : Lean.Environment) (roots : Array Lean.Name)
    : Lean.NameSet := Id.run do
  let mut visited : Lean.NameSet := {}
  let mut queue := roots.toList
  while !queue.isEmpty do
    match queue with
    | [] => break
    | name :: rest =>
      queue := rest
      if visited.contains name then continue
      visited := visited.insert name
      if let some ci := env.find? name then
        for ref in getConstRefs ci do
          if !visited.contains ref then
            queue := ref :: queue
  return visited

/-- Parse a dotted string into an `Ix.Name`. -/
def parseIxName (s : String) : Ix.Name := Id.run do
  let mut name := Ix.Name.mkAnon
  for part in s.splitOn "." do
    name := Ix.Name.mkStr name part
  return name

/-- Dump the current `(name, hex)` table for every entry in `kernelPrimitives`.
    Pass iff every entry resolves; missing names are printed as `// MISSING:`
    comments so the output is still valid as-is for partial regeneration. -/
def testBuildPrimitives : TestSeq :=
  .individualIO "build primitives dump" none (do
    let leanEnv ← get_env!
    let roots := kernelPrimitives.map parseNameToLean
    let needed := collectDeps leanEnv roots
    let filtered := leanEnv.constants.toList.filter fun (name, _) =>
      needed.contains name

    IO.println s!"[build-primitives] {filtered.length} constants in transitive closure"

    let rawEnv ← Ix.CompileM.rsCompileEnvFFI filtered
    let env : Ixon.Env := rawEnv.toEnv

    IO.println s!"[build-primitives] Ixon env: {env.consts.size} consts, {env.named.size} named"
    IO.println ""
    IO.println "// === Primitive content-addresses (for hardcoding in Rust kernel) ==="
    IO.println "// Format: (\"lean_name\", \"content_address_hex\")"
    IO.println ""

    let mut found : Nat := 0
    let mut missing : Array String := #[]

    for primName in kernelPrimitives do
      let ixName := parseIxName primName
      match env.named[ixName]? with
      | none =>
        IO.println s!"// MISSING: {primName}"
        missing := missing.push primName
      | some named =>
        let addrHex := toString named.addr
        IO.println s!"(\"{primName}\", \"{addrHex}\"),"
        found := found + 1

    IO.println ""
    IO.println s!"// Found: {found}/{kernelPrimitives.size}"
    if !missing.isEmpty then
      IO.println s!"// Missing: {missing}"

    let msg : Option String :=
      if missing.isEmpty then none else some s!"{missing.size} primitives missing from Ixon env"
    return (missing.isEmpty, found, missing.size, msg)
  ) .done

/-- FFI: expose `PrimAddrs::new()` from Rust as
    `(lean_name, hex_address)` pairs in the same order as
    `kernelPrimitives` below. Used to detect drift between hardcoded
    addresses and what `rsCompileEnvFFI` would produce today. -/
@[extern "rs_prim_addrs_canonical"]
opaque rsPrimAddrsCanonicalFFI : IO (Array (String × String))

/-- Parity check: every primitive's content address as stored in
    Rust's `PrimAddrs::new()` must match the address produced by
    compiling that primitive's Lean declaration through the live
    `rsCompileEnvFFI` pipeline. A mismatch means someone changed the
    compile/serialize logic in a way that altered a primitive's
    content hash — Aiur and downstream kernel primitive resolution
    will silently break if `PrimAddrs::new()` isn't updated.

    On failure: re-run `lake test --ignored
    rust-kernel-build-primitives` to dump the fresh table, then
    paste over `PrimAddrs::new` in `src/ix/kernel/primitive.rs`
    (plus update `PrimAddrs::lean_parity_table` keeps lock-step).

    Exception: `eagerReduce` is a synthetic kernel marker whose
    PrimAddrs value (`0xff…3`) intentionally diverges from its
    compiled content hash (which collides with `id`). Skip the check
    for it. -/
def testPrimitivesParity : TestSeq :=
  .individualIO "primitive address parity (PrimAddrs vs live compile)" none (do
    -- Reuse the same Lean → Ixon compile pipeline as testBuildPrimitives.
    let leanEnv ← get_env!
    let roots := kernelPrimitives.map parseNameToLean
    let needed := collectDeps leanEnv roots
    let filtered := leanEnv.constants.toList.filter fun (name, _) =>
      needed.contains name
    let rawEnv ← Ix.CompileM.rsCompileEnvFFI filtered
    let env : Ixon.Env := rawEnv.toEnv

    let hardcoded ← rsPrimAddrsCanonicalFFI
    let lookup : Std.HashMap String String :=
      hardcoded.foldl (init := {}) fun m (n, h) => m.insert n h

    let mut mismatches : Array String := #[]
    let mut missing : Array String := #[]
    for primName in kernelPrimitives do
      -- The synthetic eagerReduce marker is intentionally unequal to
      -- the compiled `id` hash; skip parity for it.
      if primName == "eagerReduce" then continue
      let ixName := parseIxName primName
      match env.named[ixName]? with
      | none =>
        missing := missing.push primName
      | some named =>
        let computed := toString named.addr
        match lookup[primName]? with
        | none =>
          mismatches := mismatches.push s!"{primName}: missing from PrimAddrs::lean_parity_table"
        | some hardcoded_hex =>
          if computed != hardcoded_hex then
            mismatches := mismatches.push
              s!"{primName}: live={computed} PrimAddrs={hardcoded_hex}"

    if !missing.isEmpty then
      IO.eprintln s!"primitive parity: {missing.size} primitive(s) missing from compiled env:"
      for n in missing do IO.eprintln s!"  {n}"
    if !mismatches.isEmpty then
      IO.eprintln s!"primitive parity: {mismatches.size} address mismatch(es):"
      for m in mismatches do IO.eprintln s!"  {m}"
      IO.eprintln "Regenerate via `lake test --ignored rust-kernel-build-primitives` and paste into src/ix/kernel/primitive.rs (PrimAddrs::new + lean_parity_table)."

    let total_problems := missing.size + mismatches.size
    let msg : Option String :=
      if total_problems == 0 then none
      else some s!"{mismatches.size} mismatch(es), {missing.size} missing"
    return (total_problems == 0, kernelPrimitives.size - total_problems, total_problems, msg)
  ) .done

def suite : List TestSeq := [testBuildPrimitives, testPrimitivesParity]

end Tests.Ix.Kernel.BuildPrimitives
