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
public import Ix.DecompileRoundtrip
public import Lean
public import LSpec
public import Tests.Ix.Fixtures

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

    -- Step 2: Full decompile driver (Pass 1 aux-skip → Pass 1.5 flags →
    -- Pass 2 aux regeneration/recovery) with the source env as the
    -- debug-track oracle.
    IO.println s!"[Step 2] Decompiling (full driver) to Ix types..."
    let decompStart ← IO.monoMsNow
    let origView : Std.HashMap Ix.Name Ix.ConstantInfo := phases.rawEnv.consts
    let (decompiled, decompErrors, _p2st) ←
      Ix.DecompileM.decompileEnvFullParallel phases.compileEnv (some origView)
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

public def unitSuite : List TestSeq := [
  test "extension append: virtual ref/univ indices resolve"
      extAppendResolves
    ++ test "extension append: absent metadata leaves indices OOB"
      extAppendTeeth
]

end ExtensionAppend

/-! ## Test Suite -/

public def decompileSuiteIO : List TestSeq := [
  testDecompile,
]

end Tests.Decompile
