/-
  Decompilation tests.
  Runs the Rust compilation pipeline, then decompiles back to Ix constants
  and compares via content hashes.
-/

module
public import Ix.Ixon
public import Ix.Environment
public import Ix.Address
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.DecompileM
public import Ix.DecompileDriver
public import Ix.ImportIxe
public import Lean
public import LSpec
public import Tests.Ix.Fixtures
public import Tests.Ix.DecompileOriginals

open LSpec

namespace Tests.Decompile

/-- Decompile roundtrip test: Rust compile → parallel decompile → hash comparison -/
def testDecompile : TestSeq :=
  .individualIO "Decompilation Roundtrip" none (do
    let leanEnv ← get_env!
    let totalConsts := leanEnv.constants.toList.length

    IO.println s!"[Test] Decompilation Roundtrip Test"
    IO.println s!"[Test] Environment has {totalConsts} constants"
    IO.println ""

    -- Step 1: Run Rust compilation pipeline
    IO.println s!"[Step 1] Running Rust compilation pipeline..."
    let rustStart ← IO.monoMsNow
    let phases ← Ix.CompileM.rsCompilePhases leanEnv
    let rustTime := (← IO.monoMsNow) - rustStart
    IO.println s!"[Step 1]   Rust: {phases.compileEnv.constCount} compiled in {rustTime}ms"
    IO.println s!"[Step 1]   names={phases.compileEnv.names.size}, named={phases.compileEnv.named.size}, consts={phases.compileEnv.consts.size}, blobs={phases.compileEnv.blobs.size}"
    IO.println ""

    -- Step 2: Read stored originals and restore inductive flags. The source
    -- view remains a compatibility argument; comparison is below.
    IO.println s!"[Step 2] Decompiling (full driver) to Ix types..."
    let decompStart ← IO.monoMsNow
    let origView : Std.HashMap Ix.Name Ix.ConstantInfo := phases.rawEnv.consts
    -- The limits the Rust compile above read (`IX_SHARING_LIMITS`).
    let sharingLimits ← IO.ofExcept (← Ix.CompileM.compilerSharingLimitsFromEnv)
    let (decompiled, decompErrors, _p2st) ←
      Ix.DecompileM.decompileEnvFullParallel phases.compileEnv (some origView)
        (sharingLimits := sharingLimits)
    IO.println s!"[Step 2]   {decompiled.size} constants, {decompErrors.size} errors in {(← IO.monoMsNow) - decompStart}ms"
    IO.println ""

    -- Report errors
    if !decompErrors.isEmpty then
      IO.println s!"[Errors] First 20 errors:"
      for (name, err) in decompErrors.toList.take 20 do
        IO.println s!"  {name}: {err}"
      IO.println ""

    -- Count by constant type
    let mut nDefn := (0 : Nat); let mut nAxiom := (0 : Nat)
    let mut nInduct := (0 : Nat); let mut nCtor := (0 : Nat)
    let mut nRec := (0 : Nat); let mut nQuot := (0 : Nat)
    let mut nOpaque := (0 : Nat); let mut nThm := (0 : Nat)
    for (_, info) in decompiled do
      match info with
      | .defnInfo _ => nDefn := nDefn + 1
      | .axiomInfo _ => nAxiom := nAxiom + 1
      | .inductInfo _ => nInduct := nInduct + 1
      | .ctorInfo _ => nCtor := nCtor + 1
      | .recInfo _ => nRec := nRec + 1
      | .quotInfo _ => nQuot := nQuot + 1
      | .opaqueInfo _ => nOpaque := nOpaque + 1
      | .thmInfo _ => nThm := nThm + 1
    IO.println s!"[Types] defn={nDefn}, thm={nThm}, opaque={nOpaque}, axiom={nAxiom}, induct={nInduct}, ctor={nCtor}, rec={nRec}, quot={nQuot}"
    IO.println ""

    -- Step 3: Hash-based comparison against original Ix.Environment
    let ixEnv := phases.rawEnv
    IO.println s!"[Step 3] Original Ix.Environment has {ixEnv.consts.size} constants"

    IO.println s!"[Compare] Hash-comparing {decompiled.size} decompiled constants..."
    let compareStart ← IO.monoMsNow

    -- Sequential hash comparison (cheap: just address equality on 32-byte hashes)
    let mut nMatch := (0 : Nat); let mut nMismatch := (0 : Nat); let mut nMissing := (0 : Nat)
    let mut firstMismatches : Array (Ix.Name × String) := #[]
    -- Full structural comparison (`ConstantInfo` BEq — hash-based at
    -- the Name/Level/Expr leaves): every field, not just type/value.
    for (name, decompInfo) in decompiled do
      match ixEnv.consts.get? name with
      | some origInfo =>
        if decompInfo == origInfo then
          nMatch := nMatch + 1
        else
          nMismatch := nMismatch + 1
          if firstMismatches.size < 10 then
            firstMismatches := firstMismatches.push (name, "constant-info mismatch")
      | none =>
        nMissing := nMissing + 1
        if firstMismatches.size < 10 then
          firstMismatches := firstMismatches.push (name, "not in original")
    -- Reverse coverage: source constants never reconstructed.
    let mut nMissingFromDecompile := (0 : Nat)
    for (name, _) in ixEnv.consts do
      if !decompiled.contains name then
        nMissingFromDecompile := nMissingFromDecompile + 1
        if firstMismatches.size < 10 then
          firstMismatches := firstMismatches.push (name, "missing from decompile")
    nMissing := nMissing + nMissingFromDecompile

    let compareTime := (← IO.monoMsNow) - compareStart
    IO.println s!"[Compare] Matched: {nMatch}, Mismatched: {nMismatch}, Missing: {nMissing} ({compareTime}ms)"
    if !firstMismatches.isEmpty then
      IO.println s!"[Compare] First mismatches:"
      for (name, diff) in firstMismatches do
        IO.println s!"  {name}: {diff}"
    IO.println ""

    let success := decompErrors.size == 0 && nMismatch == 0 && nMissing == 0
    if success then
      return (true, 0, 0, none)
    else
      return (false, 0, 0, some s!"{decompErrors.size} decompilation errors")
  ) .done

/-! ## Extension-table append (pure unit)

`mkBlockCtx` extends the primary `refs`/`univs` tables with the
per-constant `ConstantMeta.metaRefs`/`metaUnivs` — the documented
virtual-address contract (Rust `load_meta_extensions`). No compiler
emits extension entries today (stage 1 of canonicity §10.6; stage 2's
`univPatches` spellings will), so this synthetic fixture is the only
thing pinning the Lean side of the contract. -/

section ExtensionAppend

open Ix.DecompileM Ixon

private def nB : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "B"
private def nU : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "u"
private def nX : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "x"

/-- Type `∀ (x : B), Sort (max u 0)` where ref index 1 and univ index 1
    are VIRTUAL — resolvable only through the appended extension
    tables. -/
private def extFixture :
    Ixon.Constant × ConstantMeta × ExprMetaArena × Ixon.Expr := Id.run do
  let ty : Ixon.Expr := .leanAll (.ref 1 #[]) (.sort 1)
  let aAddr := Address.blake3 "ext-fixture-A".toUTF8
  let cnst : Ixon.Constant :=
    ⟨.axio ⟨false, 1, ty⟩, #[], #[aAddr], #[.var 0]⟩
  let bAddr := Address.blake3 "ext-fixture-B".toUTF8
  let cm : ConstantMeta :=
    { metaRefs := #[bAddr], metaUnivs := #[.max (.var 0) .zero] }
  let arena : ExprMetaArena := ⟨#[
    .ref nB.getHash,                  -- 0: domain const name
    .leaf,                            -- 1: codomain sort
    .binder nX.getHash .default 0 1   -- 2: the pi binder
  ]⟩
  return (cnst, cm, arena, ty)

private def extEnv : DecompileEnv := Id.run do
  let base : Ixon.Env := {}
  let names := [nB, nU, nX].foldl (init := base.names)
    Ixon.RawEnv.addNameComponents
  return { ixonEnv := { base with names } }

/-- With extensions installed, the virtual indices resolve and the
    original expression comes back. -/
private def extAppendResolves : Bool := Id.run do
  let (cnst, cm, arena, ty) := extFixture
  let ctx := mkBlockCtx cnst #[] #[nU] arena cm
  match DecompileM.run extEnv ctx {} (decompileExpr ty 2) with
  | .ok (e, _) =>
    let expected := Ix.Expr.mkForallE nX
      (Ix.Expr.mkConst nB #[])
      (Ix.Expr.mkSort (Ix.Level.mkMax (Ix.Level.mkParam nU)
        Ix.Level.mkZero))
      .default
    return e == expected
  | .error _ => return false

/-- Without the metadata wrapper, the same indices are out of bounds —
    proving the append (not table size coincidence) made them resolve. -/
private def extAppendTeeth : Bool := Id.run do
  let (cnst, _, arena, ty) := extFixture
  let ctx := mkBlockCtx cnst #[] #[nU] arena
  match DecompileM.run extEnv ctx {} (decompileExpr ty 2) with
  | .ok _ => return false
  | .error e =>
    return match e with
      | .invalidRefIndex .. | .invalidUnivIndex .. => true
      | _ => false

end ExtensionAppend

/-! ## Metadata `share`: the table check (pure unit)

`share i` inside `metaSharing[j]` denotes primary entry `i` (`i < p`) or
`metaSharing[i - p]` (`p ≤ i < p + j`); anything else is
`invalidMetaShareIndex`. No compiler emits such a share today, so these
hand-built tables are the only thing pinning the table check
(`validateMetaSharing`, which every constant's block setup runs; Rust
mirror: `meta_share_*` tests in `crates/compile/src/decompile.rs`).

Every fixture has one primary entry (`p = 1`), `prim0 = (#1 #2)`. -/

section MetaShare

open Ix.DecompileM Ixon

private def nAx : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "MS.ax"

/-- The names the fixtures read. -/
private def msEnv : DecompileEnv :=
  { ixonEnv := { names := Ixon.RawEnv.addNameComponents {} nAx } }

/-- Primary entry 0. -/
private def prim0 : Ixon.Expr := .app (.var 1) (.var 2)
/-- `metaSharing[0]`, shared: `share 0` is primary entry 0. -/
private def sharedM0 : Ixon.Expr := .app (.share 0) (.var 3)
/-- `metaSharing[1]`, shared: `share 1 = p + 0` is `metaSharing[0]`. -/
private def sharedM1 : Ixon.Expr := .app (.share 1) (.share 0)
/-- The unshared originals of the two entries. -/
private def plainM0 : Ixon.Expr := .app prim0 (.var 3)
private def plainM1 : Ixon.Expr := .app plainM0 prim0

private def isMetaShareErr {α : Type} (idx entry p q : Nat) : Except DecompileError α → Bool
  | .error (.invalidMetaShareIndex i j p' q' _) =>
    i.toNat == idx && j.toNat == entry && p' == p && q' == q
  | _ => false

/-- Forward reference (`metaSharing[0]` → `metaSharing[1]`): rejected. -/
private def msForward : Bool :=
  isMetaShareErr 2 0 1 2 (validateMetaSharing 1 #[.app (.share 2) (.var 3), .var 4])

/-- Self reference (`share p` in `metaSharing[0]`): rejected, not a loop. -/
private def msSelf : Bool :=
  isMetaShareErr 1 0 1 1 (validateMetaSharing 1 #[.app (.share 1) (.var 3)])

/-- `i ≥ p + q`: out of range. -/
private def msOutOfRange : Bool :=
  let r := validateMetaSharing 1 #[.var 0, .app (.share 5) (.var 3)]
  isMetaShareErr 5 1 1 2 r
    && (match r with
        | .error e => (toString e).contains "out of range"
        | .ok _ => false)

/-- Whole-constant path (`decompileAxiom` → `withFreshBlock`): the table
    check rejects a malformed entry that nothing reads, and the error names
    the constant. -/
private def msAxiomUnreadEntryRejected : Bool :=
  let ax : Ixon.Axiom := ⟨false, 0, .sort 0⟩
  let cnst : Ixon.Constant := ⟨.axio ax, #[prim0], #[], #[.zero]⟩
  -- Entry 2 references itself (`share 3 = p + 2`).
  let cm : ConstantMeta :=
    { info := .axio nAx.getHash #[] ⟨#[.leaf]⟩ 0,
      metaSharing := #[sharedM0, sharedM1, .app (.share 3) (.var 0)] }
  let r := (DecompileM.run msEnv default {} (decompileAxiom ax cnst cm)).map (·.1)
  isMetaShareErr 3 2 1 3 r && match r with
    | .error (.invalidMetaShareIndex _ _ _ _ c) => c == nAx.pretty
    | _ => false

/-- Tables without shares pass the check. -/
private def msNoShares : Bool :=
  validateMetaSharing 0 #[plainM0, plainM1] matches .ok ()

/-- A valid shared table passes the check. -/
private def msSharedTable : Bool :=
  validateMetaSharing 1 #[sharedM0, sharedM1] matches .ok ()

/-- The table check visits each shared node once: the chain
    `e(k+1) = app e(k) e(k)` of depth 64 (2^64 nodes as a tree) validates, and
    the first violation inside it is still its leftmost leaf. -/
private def msSharedChain : Bool :=
  let chain := (List.range 64).foldl (fun e _ => Ixon.Expr.app e e)
    (Ixon.Expr.app (.share 0) (.var 0))
  (validateMetaSharing 1 #[chain, chain] matches .ok ()) &&
    isMetaShareErr 0 0 0 1 (validateMetaSharing 0 #[chain])

end MetaShare

public def unitSuite : List TestSeq := [
  test "extension append: virtual ref/univ indices resolve"
      extAppendResolves
    ++ test "extension append: absent metadata leaves indices OOB"
      extAppendTeeth,
  test "metadata share: forward reference rejected" msForward
    ++ test "metadata share: self reference rejected" msSelf
    ++ test "metadata share: i ≥ p + q rejected" msOutOfRange
    ++ test "metadata share: unread malformed entry rejected"
      msAxiomUnreadEntryRejected
    ++ test "metadata share: tables without shares unchanged" msNoShares
    ++ test "metadata share: a valid shared table passes" msSharedTable
    ++ test "metadata share: shared subterms are checked once" msSharedChain,
  Tests.DecompileOriginals.suite
]

/-! ## Test Suite -/

public def decompileSuiteIO : List TestSeq := [
  testDecompile,
]

end Tests.Decompile
