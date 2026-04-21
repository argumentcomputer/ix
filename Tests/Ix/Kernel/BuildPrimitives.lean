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
  "Nat.decLe", "Nat.decEq", "Nat.decLt",
  "Decidable.isTrue", "Decidable.isFalse",
  "Nat.le_of_ble_eq_true", "Nat.not_le_of_not_ble_eq_true",
  "Nat.eq_of_beq_eq_true", "Nat.ne_of_beq_eq_false",
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
  "Int.natAbs",
  -- Below/brecOn dependencies — referenced by aux_gen, not Primitives<M>
  -- directly. Kept here so the dump is complete enough to debug drift.
  "PUnit", "PProd", "PProd.mk"
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

def suite : List TestSeq := [testBuildPrimitives]

end Tests.Ix.Kernel.BuildPrimitives
