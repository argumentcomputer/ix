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
public import Ix.ImportIxe
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

end ExtensionAppend

/-! ## Metadata `share`: the extended index space (pure unit)

`share i` inside `metaSharing[j]` denotes primary entry `i` (`i < p`) or
`metaSharing[i - p]` (`p ≤ i < p + j`); anything else is
`invalidMetaShareIndex`. No compiler emits such a share today, so these
hand-built fixtures are the only thing pinning the reader rule (Rust
mirror: `meta_share_*` tests in `crates/compile/src/decompile.rs`).

Every fixture has one primary entry (`p = 1`), `prim0 = (#1 #2)`, and a
primary root `head #99` whose `callSite` metadata reads one collapsed
argument from `metaSharing` before the kept `#99`. -/

section MetaShare

open Ix.DecompileM Ixon

private def nHead : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "MS.head"
private def nHead2 : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "MS.head2"
private def nAx : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "MS.ax"

private def msEnv : DecompileEnv := Id.run do
  let base : Ixon.Env := {}
  let names := [nHead, nHead2, nAx].foldl (init := base.names)
    Ixon.RawEnv.addNameComponents
  return { ixonEnv := { base with names } }

/-- Primary entry 0. -/
private def prim0 : Ixon.Expr := .app (.var 1) (.var 2)
/-- `metaSharing[0]`, shared: `share 0` is primary entry 0. -/
private def sharedM0 : Ixon.Expr := .app (.share 0) (.var 3)
/-- `metaSharing[1]`, shared: `share 1 = p + 0` is `metaSharing[0]`. -/
private def sharedM1 : Ixon.Expr := .app (.share 1) (.share 0)
/-- The unshared originals of the two entries. -/
private def plainM0 : Ixon.Expr := .app prim0 (.var 3)
private def plainM1 : Ixon.Expr := .app plainM0 prim0

/-- Expected decompilations: `prim0`, `plainM0`, `plainM1`. -/
private def ixPrim0 : Ix.Expr := Ix.Expr.mkApp (Ix.Expr.mkBVar 1) (Ix.Expr.mkBVar 2)
private def ixM0 : Ix.Expr := Ix.Expr.mkApp ixPrim0 (Ix.Expr.mkBVar 3)
private def ixM1 : Ix.Expr := Ix.Expr.mkApp ixM0 ixPrim0

/-- The primary root: `head #99` (the callSite head is named by metadata). -/
private def msRoot : Ixon.Expr := .app (.ref 0 #[]) (.var 99)

/-- Arena: `0` leaf (the kept argument), `1` the call site, whose source
    spine is `head <metaSharing[k]> #99`. -/
private def msArena (k : UInt64) (origHead : Option (UInt64 × UInt64) := none) :
    ExprMetaArena := ⟨#[
  .leaf,
  .callSite nHead.getHash #[.collapsed k UInt64.MAX, .kept 0 0] #[0] origHead ]⟩

private def msCtx (metaSharing : Array Ixon.Expr) (arena : ExprMetaArena)
    (root : Ixon.Expr := msRoot) : BlockCtx :=
  mkBlockCtx ⟨.axio ⟨false, 0, root⟩, #[prim0], #[], #[]⟩ #[] #[] arena
    { metaSharing }

private def msRun (ctx : BlockCtx) (root : Ixon.Expr := msRoot) (rootIdx : UInt64 := 1) :
    Except DecompileError Ix.Expr :=
  (DecompileM.run msEnv ctx {} (decompileExpr root rootIdx)).map (·.1)

/-- `head x #99`. -/
private def spine (x : Ix.Expr) : Ix.Expr :=
  Ix.Expr.mkApp (Ix.Expr.mkApp (Ix.Expr.mkConst nHead #[]) x) (Ix.Expr.mkBVar 99)

private def isMetaShareErr {α : Type} (idx entry p q : Nat) : Except DecompileError α → Bool
  | .error (.invalidMetaShareIndex i j p' q' _) =>
    i.toNat == idx && j.toNat == entry && p' == p && q' == q
  | _ => false

private def okEq (r : Except DecompileError Ix.Expr) (expected : Ix.Expr) : Bool :=
  match r with
  | .ok e => e == expected
  | .error _ => false

/-- `share i`, `i < p`: the primary entry. -/
private def msPrimary : Bool :=
  okEq (msRun (msCtx #[sharedM0] (msArena 0))) (spine ixM0)

/-- `p ≤ i < p + j`: an earlier metadata entry, and through it a primary
    entry. -/
private def msEarlierMeta : Bool :=
  okEq (msRun (msCtx #[sharedM0, sharedM1] (msArena 1))) (spine ixM1)

/-- Round trip: the shared table decompiles exactly like the unshared
    original. -/
private def msRoundTrip : Bool :=
  let shared := msRun (msCtx #[sharedM0, sharedM1] (msArena 1))
  let plain := msRun (msCtx #[plainM0, plainM1] (msArena 1))
  match shared, plain with
  | .ok s, .ok u => s == u && s == spine ixM1
  | _, _ => false

/-- `origHead` reads its entry in that entry's metadata scope too:
    source spine `<metaSharing[1]> <metaSharing[0]> #99`. -/
private def msOrigHead : Bool :=
  okEq (msRun (msCtx #[sharedM0, sharedM1] (msArena 0 (some (1, UInt64.MAX)))))
    (Ix.Expr.mkApp (Ix.Expr.mkApp ixM1 ixM0) (Ix.Expr.mkBVar 99))

/-- Forward reference (`metaSharing[0]` → `metaSharing[1]`): rejected, both
    lazily and by the table check. -/
private def msForward : Bool :=
  let table := #[.app (.share 2) (.var 3), .var 4]
  isMetaShareErr 2 0 1 2 (msRun (msCtx table (msArena 0)))
    && isMetaShareErr 2 0 1 2 (validateMetaSharing 1 table)

/-- Self reference (`share p` in `metaSharing[0]`): rejected, not a loop. -/
private def msSelf : Bool :=
  let table := #[.app (.share 1) (.var 3)]
  isMetaShareErr 1 0 1 1 (msRun (msCtx table (msArena 0)))
    && isMetaShareErr 1 0 1 1 (validateMetaSharing 1 table)

/-- `i ≥ p + q`: out of range. -/
private def msOutOfRange : Bool :=
  let table := #[.var 0, .app (.share 5) (.var 3)]
  let r := msRun (msCtx table (msArena 1))
  isMetaShareErr 5 1 1 2 r
    && isMetaShareErr 5 1 1 2 (validateMetaSharing 1 table)
    && (match r with
        | .error e => (toString e).contains "out of range"
        | .ok _ => false)

/-- A primary `share i` with `i ≥ p` stays invalid although `metaSharing`
    has entries: metadata never changes how primary bytes decode. -/
private def msPrimaryUnchanged : Bool :=
  let root : Ixon.Expr := .app (.ref 0 #[]) (.share 1)
  match msRun (msCtx #[sharedM0] (msArena 0) root) root with
  | .error (.invalidShareIndex 1 1 _) => true
  | _ => false

/-- The expression cache is keyed by scope: `sub = (share 1) #7` is valid in
    `metaSharing[1]` (decoded first, as the collapsed argument of the call
    site in function position) and must still be rejected when the primary
    root applies the call site to the same `sub` at the same arena index
    (no call-site scan covers that occurrence). -/
private def msCacheScope : Bool :=
  let sub : Ixon.Expr := .app (.share 1) (.var 7)
  let root : Ixon.Expr := .app msRoot sub
  let arena : ExprMetaArena := ⟨#[
    .leaf,
    .callSite nHead.getHash #[.collapsed 1 UInt64.MAX, .kept 0 0] #[0] none,
    .app 1 UInt64.MAX ]⟩
  match msRun (msCtx #[sharedM0, sub] arena root) root (rootIdx := 2) with
  | .error (.invalidShareIndex 1 1 _) => true
  | _ => false

/-- A call site nested in a metadata expression: its canonical spine runs
    through a metadata share into `metaSharing[0]` and an argument there is
    a primary share. Source: `head (head2 (#1 #2) #9) #99`. -/
private def msNestedCallSite : Bool :=
  let m0 : Ixon.Expr := .app (.ref 0 #[]) (.share 0)
  let m1 : Ixon.Expr := .app (.share 1) (.var 9)
  let arena : ExprMetaArena := ⟨#[
    .leaf,
    .callSite nHead2.getHash #[.kept 0 UInt64.MAX, .kept 1 UInt64.MAX]
      #[UInt64.MAX, UInt64.MAX] none,
    .callSite nHead.getHash #[.collapsed 1 1, .kept 0 0] #[0] none ]⟩
  let inner := Ix.Expr.mkApp
    (Ix.Expr.mkApp (Ix.Expr.mkConst nHead2 #[]) ixPrim0) (Ix.Expr.mkBVar 9)
  okEq (msRun (msCtx #[m0, m1] arena) (rootIdx := 2)) (spine inner)

/-- An eta call site in a metadata expression: the synthesized wrapper is
    stripped across a metadata share (`metaSharing[1] = λ. share 1`, the
    inner lambda being `metaSharing[0]`). Source: `head (head2 #1) #99`
    (the kept `#3` is lowered by the two synthesized binders). -/
private def msEtaCallSite : Bool :=
  let m0 : Ixon.Expr := .lam .many (.var 5)
    (.app (.app (.ref 0 #[]) (.var 3)) (.var 0))
  let m1 : Ixon.Expr := .lam .many (.var 6) (.share 1)
  let arena : ExprMetaArena := ⟨#[
    .leaf,
    .etaCallSite 2 nHead2.getHash #[.kept 0 UInt64.MAX]
      #[UInt64.MAX, UInt64.MAX] UInt64.MAX,
    .callSite nHead.getHash #[.collapsed 1 1, .kept 0 0] #[0] none ]⟩
  let inner := Ix.Expr.mkApp (Ix.Expr.mkConst nHead2 #[]) (Ix.Expr.mkBVar 1)
  okEq (msRun (msCtx #[m0, m1] arena) (rootIdx := 2)) (spine inner)

/-- Whole-constant path (`decompileAxiom` → `withFreshBlock`): the table
    check rejects a malformed entry that no call site reads, and a valid
    shared table decompiles to the unshared original. -/
private def msAxiom (metaSharing : Array Ixon.Expr) :
    Except DecompileError Ix.ConstantInfo :=
  let ax : Ixon.Axiom := ⟨false, 0, msRoot⟩
  let cnst : Ixon.Constant := ⟨.axio ax, #[prim0], #[], #[]⟩
  let cm : ConstantMeta :=
    { info := .axio nAx.getHash #[] (msArena 1) 1, metaSharing }
  (DecompileM.run msEnv default {} (decompileAxiom ax cnst cm)).map (·.1)

private def msAxiomOk : Bool :=
  match msAxiom #[sharedM0, sharedM1] with
  | .ok (.axiomInfo v) => v.cnst.type == spine ixM1 && v.cnst.name == nAx
  | _ => false

private def msAxiomUnreadEntryRejected : Bool :=
  -- Entry 2 is never read (the call site reads entry 1) but references
  -- itself (`share 3 = p + 2`).
  isMetaShareErr 3 2 1 3 (msAxiom #[sharedM0, sharedM1, .app (.share 3) (.var 0)])

/-- Regression: metadata without shares behaves as before. -/
private def msNoShares : Bool :=
  okEq (msRun (msCtx #[plainM0] (msArena 0))) (spine ixM0)
    && (validateMetaSharing 0 #[plainM0, plainM1] matches .ok ())

/-! ### Lean/Rust parity through the `.ixe` decompile FFI

The same serialized env is decompiled by the Lean decompiler and by the
Rust one (`rs_decompile_env_consts`, i.e. `decompile_env` plus
materialization): both must accept a valid shared table with the same
result, and both must reject the malformed ones with the same
`invalidMetaShareIndex` fields. -/

/-- `MS.head : Sort 0` and `MS.ax : head <metaSharing[1]> #99`, the latter
    carrying `metaSharing`. -/
private def msParityEnv (metaSharing : Array Ixon.Expr) : Ixon.Env := Id.run do
  let headC : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let headAddr := Address.blake3 (Ixon.serConstant headC)
  let axC : Ixon.Constant :=
    ⟨.axio ⟨false, 0, msRoot⟩, #[prim0], #[headAddr], #[]⟩
  let axAddr := Address.blake3 (Ixon.serConstant axC)
  let mut env : Ixon.Env := {}
  env := env.storeConst headAddr headC
  env := env.storeConst axAddr axC
  env := { env with
    names := [nHead, nAx].foldl (init := env.names) Ixon.RawEnv.addNameComponents }
  env := env.registerName nHead
    { addr := headAddr, constMeta := { info := .axio nHead.getHash #[] ⟨#[.leaf]⟩ 0 } }
  env := env.registerName nAx
    { addr := axAddr,
      constMeta := { info := .axio nAx.getHash #[] (msArena 1) 1, metaSharing } }
  return env

/-- Lean side, from the serialized bytes: `MS.ax`'s decompiled type or the
    decompile error. -/
private def msParityLean (bytes : ByteArray) :
    Except String (Except DecompileError Ix.Expr) := do
  let env ← Ixon.deEnv bytes
  let some named := env.named.get? nAx | throw "MS.ax not in the decoded env"
  let some cnst := env.getConst? named.addr | throw "MS.ax constant missing"
  let .axio ax := cnst.info | throw "MS.ax is not an axiom"
  return (DecompileM.run { ixonEnv := env } default {}
    (decompileAxiom ax cnst named.constMeta)).map fun (ci, _) => ci.getCnst.type

/-- `MS.ax`'s type as Rust materializes it: `MS.head ((#1 #2 #3) (#1 #2)) #99`. -/
private def msParityLeanExpr : Lean.Expr :=
  let b := Lean.mkBVar
  let prim := Lean.mkApp (b 1) (b 2)
  .app (.app (.const (Lean.Name.mkSimple "MS.head") [])
    (.app (.app prim (b 3)) prim)) (b 99)

/-- Run both decompilers on `msParityEnv metaSharing`. `expect` is `none`
    for acceptance, or the `(idx, entry, p, q)` of the expected rejection. -/
private def msParityCase (label : String) (metaSharing : Array Ixon.Expr)
    (expect : Option (Nat × Nat × Nat × Nat)) : IO (Option String) := do
  let bytes ← match Ixon.serEnv (msParityEnv metaSharing) with
    | .ok b => pure b
    | .error e => return some s!"{label}: serEnv failed: {e}"
  let dir ← IO.FS.createTempDir
  let path := (dir / "meta-share.ixe").toString
  try
    IO.FS.writeBinFile path bytes
    let lean ← match msParityLean bytes with
      | .ok r => pure r
      | .error e => return some s!"{label}: Lean env: {e}"
    let rust : Except String (Array (Lean.Name × Lean.ConstantInfo)) ←
      tryCatch (Except.ok <$> Ix.ImportIxe.materializeIxe path)
        fun e => pure (Except.error (toString e))
    match expect, lean, rust with
    | none, .ok ty, .ok consts =>
      let rustTy := consts.findSome? fun (n, ci) =>
        if n == Lean.Name.mkSimple "MS.ax" then some ci.type else none
      if ty != spine ixM1 then return some s!"{label}: Lean type differs"
      if rustTy != some msParityLeanExpr then
        return some s!"{label}: Rust type differs: {rustTy}"
      return none
    | some (i, j, p, q), .error le, .error re =>
      if !isMetaShareErr i j p q (Except.error le : Except DecompileError Unit) then
        return some s!"{label}: Lean rejected with {le}"
      let want := s!"InvalidMetaShareIndex \{ idx: {i}, entry: {j}, \
        primary_len: {p}, meta_len: {q}"
      if !re.contains want then
        return some s!"{label}: Rust rejected with {re}"
      return none
    | _, l, r =>
      let ls := match l with | .ok _ => "accepted" | .error e => toString e
      let rs := match r with | .ok _ => "accepted" | .error e => e
      return some s!"{label}: Lean {ls}; Rust {rs}"
  finally
    IO.FS.removeDirAll dir

private def msParity : TestSeq :=
  .individualIO "metadata share: Lean/Rust decompile parity" none (do
    let cases : List (String × Array Ixon.Expr × Option (Nat × Nat × Nat × Nat)) := [
      ("valid", #[sharedM0, sharedM1], none),
      ("forward", #[sharedM0, .app (.share 3) (.var 3), .var 4], some (3, 1, 1, 3)),
      ("unread self", #[sharedM0, sharedM1, .app (.share 3) (.var 0)],
        some (3, 2, 1, 3)),
      ("out of range", #[sharedM0, .app (.share 7) (.var 3)], some (7, 1, 1, 2)) ]
    let mut failures : Array String := #[]
    for (label, table, expect) in cases do
      if let some msg ← msParityCase label table expect then
        failures := failures.push msg
    if failures.isEmpty then
      return (true, 0, 0, none)
    else
      return (false, 0, 0, some ("; ".intercalate failures.toList))) .done

end MetaShare

public def unitSuite : List TestSeq := [
  test "extension append: virtual ref/univ indices resolve"
      extAppendResolves
    ++ test "extension append: absent metadata leaves indices OOB"
      extAppendTeeth,
  test "metadata share: i < p is the primary entry" msPrimary
    ++ test "metadata share: p ≤ i < p + j is an earlier metadata entry"
      msEarlierMeta
    ++ test "metadata share: round trip equals the unshared original"
      msRoundTrip
    ++ test "metadata share: origHead reads its entry's scope" msOrigHead
    ++ test "metadata share: forward reference rejected" msForward
    ++ test "metadata share: self reference rejected" msSelf
    ++ test "metadata share: i ≥ p + q rejected" msOutOfRange
    ++ test "metadata share: primary share ≥ p still rejected"
      msPrimaryUnchanged
    ++ test "metadata share: expression cache keyed by scope" msCacheScope
    ++ test "metadata share: nested call site crosses scopes"
      msNestedCallSite
    ++ test "metadata share: eta wrapper stripped across a metadata share"
      msEtaCallSite
    ++ test "metadata share: whole constant decompiles" msAxiomOk
    ++ test "metadata share: unread malformed entry rejected"
      msAxiomUnreadEntryRejected
    ++ test "metadata share: tables without shares unchanged" msNoShares,
  msParity
]

/-! ## Test Suite -/

public def decompileSuiteIO : List TestSeq := [
  testDecompile,
]

end Tests.Decompile
