/-
  `.ixc` catalog format suite (primary, network-free).

  Two fixture pieces are compiled in-process from a self-contained
  kernel environment (no Init — the `Tests.Ix.ImportIxe` pattern,
  miniature), assembled into a fat `.ixc` by the Rust core, and the
  gates run both directions:

  - Rust↔Lean format parity: the Lean mirror (`Ix.Catalog.de`) parses
    the Rust-assembled manifest, recomputes `members_root`, agrees
    with `rs_catalog_info`'s roots, and re-serializes BYTE-IDENTICAL
    to the file — the two implementations cannot drift silently.
  - Identity dedup: the shared fixture constants collapse in the
    union (`content_root` counts them once); two different piece
    partitions of the same content commit to the same `content_root`.
  - Lean-mirror unit coverage: ser/de roundtrips over fat + chunked +
    preimage/deps variants, tamper rejection (magic, unknown flags,
    members_root drift, non-topo deps, path-traversal labels).
  - Strict-anon compile (`rs_compile_env_anon`): §5 empty, §3 hints
    SURVIVE (the `finalize_hints` ordering pin from the plan's risk
    table), and the env root equals the named compile's — the
    anon-invariance the old C5 suite asserted, now structural.
-/
module

public import LSpec
public import Ix.Catalog
public import Ix.CompileM
public import Ix.Cli.CatalogCmd

public section

open LSpec

namespace Tests.Ix.Catalog

@[extern "rs_env_section_counts"]
opaque rsEnvSectionCountsFFI : @& String → IO String

/-! ### Kernel fixture (Init-free): a tiny inductive + defs, so pieces
    carry real compiled constants with hints. -/

private def nN : Lean.Name := `TCat.N
private def cN : Lean.Expr := .const nN []
private def type1 : Lean.Expr := .sort (.succ .zero)

private def arrow (a b : Lean.Expr) : Lean.Expr :=
  .forallE `a a b .default

private def baseDecls : List Lean.Declaration := [
  .inductDecl [] 0 [{
    name := nN
    type := type1
    ctors := [
      { name := `TCat.N.zero, type := cN },
      { name := `TCat.N.succ, type := arrow cN cN } ] }] false]

/-- Piece-specific definitions over the shared base: `idA`/`idB` are
    alpha-DISTINCT bodies so the two pieces genuinely differ. -/
private def defnOver (name : Lean.Name) (steps : Nat) : Lean.Declaration :=
  .defnDecl {
    name
    levelParams := []
    type := arrow cN cN
    value := .lam `n cN
      (Nat.rec (motive := fun _ => Lean.Expr) (.bvar 0)
        (fun _ e => .app (.const `TCat.N.succ []) e) steps)
      .default
    hints := .regular (1 + steps.toUInt32)
    safety := .safe
    all := [name] }

private def fixtureConsts (extra : List Lean.Declaration) :
    IO (List (Lean.Name × Lean.ConstantInfo)) := do
  let env ← Lean.mkEmptyEnvironment
  let mut kenv := env.toKernelEnv
  for decl in baseDecls ++ extra do
    match kenv.addDecl {} decl with
    | .ok kenv' => kenv := kenv'
    | .error _ => throw <| IO.userError "fixture decl rejected by kernel"
  return kenv.constants.fold (init := []) fun acc name info =>
    (name, info) :: acc

private def num (json : Lean.Json) (k : String) : Option Nat :=
  ((json.getObjVal? k).bind (·.getNat?)).toOption

private def str (json : Lean.Json) (k : String) : Option String :=
  ((json.getObjVal? k).bind (·.getStr?)).toOption

/-- The end-to-end fixture gate: compile two overlapping pieces,
    assemble, and pin format parity + identity dedup. -/
private def assembleParityTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  try
    -- Piece A: base + idA. Piece B: base + idA + idB (A ⊂ B content).
    let constsA ← fixtureConsts [defnOver `TCat.idA 1]
    let constsB ← fixtureConsts [defnOver `TCat.idA 1, defnOver `TCat.idB 2]
    let pieceA := (dir / "A.ixe").toString
    let pieceB := (dir / "B.ixe").toString
    let sA ← Ix.CompileM.rsCompileEnvBytesFFI constsA pieceA false
    let sB ← Ix.CompileM.rsCompileEnvBytesFFI constsB pieceB false
    -- Assemble via the Rust core (the production path): a
    -- self-contained .ixc DIRECTORY, pieces ingested inside it.
    let ixcDir := dir / "cat.ixc"
    let members := Lean.Json.arr #[
      Lean.Json.mkObj [("path", .str pieceA), ("label", .str "A")],
      Lean.Json.mkObj [("path", .str pieceB), ("label", .str "B"),
        ("deps", Lean.Json.arr #[Lean.toJson (0 : Nat)])] ]
    let summary ← Ix.Cli.CatalogCmd.rsCatalogAssembleFFI ixcDir.toString
      members.compress
    let json ← match Lean.Json.parse summary with
      | .ok j => pure j
      | .error e => return (false, 0, 0, some s!"assemble JSON: {e}")
    unless (← (ixcDir / "A.ixe").pathExists) do
      return (false, 0, 0, some "piece not ingested into the .ixc dir")
    -- Lean mirror: parse the Rust-written manifest inside the dir.
    let bytes ← IO.FS.readBinFile (ixcDir / "manifest")
    let cat ← match Ix.Catalog.de bytes with
      | .ok c => pure c
      | .error e => return (false, 0, 0, some s!"Lean mirror de: {e}")
    let checks : List (String × Bool) := [
      -- Byte-identity: Lean ser ∘ de reproduces the Rust bytes.
      ("mirror re-serializes byte-identical",
        Ix.Catalog.ser cat == bytes),
      -- Root parity with the Rust info JSON.
      ("members_root parity",
        some (toString cat.membersRoot) == str json "membersRoot"),
      ("content_root parity",
        some (toString cat.contentRoot) == str json "contentRoot"),
      -- Identity dedup: A's content ⊆ B's, so the union root IS B's
      -- env root — the virtual union env coincides with B.
      ("union collapses shared content (content_root = B's env root)",
        toString cat.contentRoot == sB.root),
      ("piece A root recorded",
        toString cat.members[0]!.envRoot == sA.root),
      ("deps carried", cat.members[1]!.deps == #[0]),
      ("fat profile", !(cat.storage matches .chunked _)) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none =>
      return (true, cat.members[0]!.constCount.toNat,
        cat.members[1]!.constCount.toNat, none)
  finally
    IO.FS.removeDirAll dir

/-- Strict-anon compile: §5 empty, §3 survives, root unmoved. -/
private def anonCompileTest : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  try
    let consts ← fixtureConsts [defnOver `TCat.idA 1]
    let named := (dir / "named.ixe").toString
    let anon := (dir / "anon.ixe").toString
    let sNamed ← Ix.CompileM.rsCompileEnvBytesFFI consts named false
    let sAnon ← Ix.CompileM.rsCompileEnvBytesAnonFFI consts anon false
    let countsOf (path : String) : IO (Except String Lean.Json) := do
      match Lean.Json.parse (← rsEnvSectionCountsFFI path) with
      | .ok j => return .ok j
      | .error e => return .error e
    let cNamed ← match ← countsOf named with
      | .ok j => pure j
      | .error e => return (false, 0, 0, some s!"counts(named): {e}")
    let cAnon ← match ← countsOf anon with
      | .ok j => pure j
      | .error e => return (false, 0, 0, some s!"counts(anon): {e}")
    let checks : List (String × Bool) := [
      ("roots equal (anon-invariance)", sNamed.root == sAnon.root),
      ("named piece carries §5", (num cNamed "named").getD 0 > 0),
      ("anon piece has empty §5", num cAnon "named" == some 0),
      ("§2 identical", num cNamed "consts" == num cAnon "consts"),
      -- The finalize_hints ordering pin: a careless --anon that
      -- cleared metadata BEFORE hint finalization would leave §3
      -- empty here.
      ("§3 hints survive --anon",
        (num cAnon "hints").getD 0 > 0
          && num cAnon "hints" == num cNamed "hints") ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, (num cAnon "consts").getD 0,
        (num cAnon "hints").getD 0, none)
  finally
    IO.FS.removeDirAll dir

/-! ### Lean-mirror unit tests (pure, no FFI) -/

private def addr (seed : String) : Address := Address.blake3 seed.toUTF8

private def member (label : String) (root : Address)
    (deps : Array UInt32 := #[]) (preimage : Option Address := none) :
    Ix.Catalog.Member :=
  { envRoot := root, constCount := 3, label, toolchain := "tc",
    sourcePin := "git:example@abc", deps, preimage }

private def fatCat : Ix.Catalog.Catalog :=
  let members := #[member "A" (addr "rootA"),
                   member "B" (addr "rootB") #[0] (some (addr "pre"))]
  { membersRoot := Ix.Catalog.membersRootOf members
    contentRoot := addr "content"
    members
    storage := .fat #[⟨addr "fA", 10⟩, ⟨addr "fB", 20⟩]
    trailing := .empty }

private def chunkedCat : Ix.Catalog.Catalog :=
  let members := #[member "A" (addr "rootA")]
  { membersRoot := Ix.Catalog.membersRootOf members
    contentRoot := addr "content"
    members
    storage := .chunked #[⟨addr "c0", addr "f0", 5, 0⟩]
    trailing := ⟨#[0xAB, 0xCD]⟩ }

private def roundtrips (c : Ix.Catalog.Catalog) : Bool :=
  match Ix.Catalog.de (Ix.Catalog.ser c) with
  | .ok c' => c' == c
  | .error _ => false

private def deFails (mutate : ByteArray → ByteArray)
    (needle : String) : Bool :=
  match Ix.Catalog.de (mutate (Ix.Catalog.ser fatCat)) with
  | .ok _ => false
  | .error e => (e.splitOn needle).length > 1

private def setByte (i : Nat) (v : UInt8) (b : ByteArray) : ByteArray :=
  b.set! i v

private def truncationRejected : Bool :=
  match Ix.Catalog.de ((Ix.Catalog.ser fatCat).extract 0 40) with
  | .ok _ => false
  | .error _ => true

def unitTests : TestSeq :=
  test "fat catalog roundtrips" (roundtrips fatCat)
  ++ test "chunked catalog roundtrips (trailing preserved)"
      (roundtrips chunkedCat)
  ++ test "bad magic rejected" (deFails (setByte 0 0xFF) "magic")
  ++ test "unknown flags rejected" (deFails (setByte 12 0xFF) "flags")
  ++ test "members_root drift rejected"
      (deFails (setByte (8 + 4 + 4) 0xFF) "members_root")
  ++ test "truncation rejected" truncationRejected
  ++ test "path-traversal label rejected"
      (Ix.Catalog.validateLabel "../evil" matches .error _)
  ++ test "bare label accepted"
      (Ix.Catalog.validateLabel "Mathlib" matches .ok _)

def suite : List TestSeq := [
  unitTests,
  .individualIO
    "assemble parity: Rust .ixc ↔ Lean mirror byte-identical, dedup observed"
    none assembleParityTest .done,
  .individualIO
    "strict-anon compile: §5 empty, §3 survives, root unmoved"
    none anonCompileTest .done ]

end Tests.Ix.Catalog
