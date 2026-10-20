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

/-! ## Metadata `share`: the extended index space (pure unit)

`share i` inside `metaSharing[j]` denotes primary entry `i` (`i < p`) or
`metaSharing[i - p]` (`p ≤ i < p + j`); anything else is
`invalidMetaShareIndex`. No compiler emits such a share today, so these
hand-built fixtures are the only thing pinning the reader rule (Rust
mirror: `meta_share_*` tests in `crates/compile/src/decompile.rs`).

Every fixture has one primary entry (`p = 1`), `prim0 = (#1 #2)`, and a
primary root `head #99`, the compiled occurrence under a Pass 3 decompile
record `[(_ix.inline, k), (_ix.inline_meta, 0)]` (`msArena k`): the
occurrence decompiles as `metaSharing[k]`, read in that entry's scope at
the leaf arena node `0`. (Before CQ3.6 the fixtures reached the rule
through the retired call-site metadata.) -/

section MetaShare

open Ix.DecompileM Ixon

private def nHead : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "MS.head"
private def nAx : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "MS.ax"

/-- `n` as a metadata nat blob (the compiler's encoding). -/
private def msNatBlob (n : Nat) : ByteArray := ByteArray.mk (Nat.toBytesLE n)

/-- The decompile record `[(_ix.inline, s), (_ix.inline_meta, m)]`. -/
private def msRecord (s m : Nat) : Ixon.KVMap :=
  #[(Ix.Compile.Pass.inlineKey.getHash, .ofNat (Address.admissionHash (msNatBlob s))),
    (Ix.Compile.Pass.inlineMetaKey.getHash,
      .ofNat (Address.admissionHash (msNatBlob m)))]

/-- The names and nat blobs the records read. -/
private def msNames (env : Ixon.Env) : Ixon.Env := Id.run do
  let mut env := { env with
    names := [nHead, nAx, Ix.Compile.Pass.inlineKey,
      Ix.Compile.Pass.inlineMetaKey].foldl (init := env.names)
      Ixon.RawEnv.addNameComponents }
  for n in [0, 1, 2] do
    env := (env.storeBlob (msNatBlob n)).1
  return env

private def msEnv : DecompileEnv := { ixonEnv := msNames {} }

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

/-- The primary root `head #99`, the compiled occurrence a record replaces. -/
private def msRoot : Ixon.Expr := .app (.ref 0 #[]) (.var 99)

/-- Arena: `0` a leaf (the source occurrence's metadata root), `1` the
    decompile record over it: the occurrence decompiles as
    `metaSharing[k]`. -/
private def msArena (k : Nat) : ExprMetaArena := ⟨#[.leaf, .mdata #[msRecord k 0] 0]⟩

private def msCtx (metaSharing : Array Ixon.Expr) (arena : ExprMetaArena)
    (root : Ixon.Expr := msRoot) : BlockCtx :=
  mkBlockCtx ⟨.axio ⟨false, 0, root⟩, #[prim0], #[], #[]⟩ #[] #[] arena
    { metaSharing }

private def msRun (ctx : BlockCtx) (root : Ixon.Expr := msRoot) (rootIdx : UInt64 := 1) :
    Except DecompileError Ix.Expr :=
  (DecompileM.run msEnv ctx {} (decompileExpr root rootIdx)).map (·.1)

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
  okEq (msRun (msCtx #[sharedM0] (msArena 0))) ixM0

/-- `p ≤ i < p + j`: an earlier metadata entry, and through it a primary
    entry. -/
private def msEarlierMeta : Bool :=
  okEq (msRun (msCtx #[sharedM0, sharedM1] (msArena 1))) ixM1

/-- Round trip: the shared table decompiles exactly like the unshared
    original. -/
private def msRoundTrip : Bool :=
  let shared := msRun (msCtx #[sharedM0, sharedM1] (msArena 1))
  let plain := msRun (msCtx #[plainM0, plainM1] (msArena 1))
  match shared, plain with
  | .ok s, .ok u => s == u && s == ixM1
  | _, _ => false

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
    has entries: metadata never changes how primary bytes decode. The root
    `<record> (share 1)` reads its function through the record and its
    argument in the primary scope. -/
private def msPrimaryUnchanged : Bool :=
  let root : Ixon.Expr := .app msRoot (.share 1)
  let arena : ExprMetaArena := ⟨(msArena 0).nodes.push (.app 1 0)⟩
  match msRun (msCtx #[sharedM0] arena root) root (rootIdx := 2) with
  | .error (.invalidShareIndex 1 1 _) => true
  | _ => false

/-- The expression cache is keyed by scope: `sub = (share 1) #7` is valid in
    `metaSharing[1]` (decoded first, as the source occurrence of the record
    in function position, at arena node 0) and must still be rejected when
    the primary root applies the record to the same `sub` (same arena node
    0, primary scope). -/
private def msCacheScope : Bool :=
  let sub : Ixon.Expr := .app (.share 1) (.var 7)
  let root : Ixon.Expr := .app msRoot sub
  let arena : ExprMetaArena := ⟨(msArena 1).nodes.push (.app 1 0)⟩
  match msRun (msCtx #[sharedM0, sub] arena root) root (rootIdx := 2) with
  | .error (.invalidShareIndex 1 1 _) => true
  | _ => false

/-- A record nested in a metadata entry crosses scopes: the root record
    (node 3) replays `metaSharing[1] = #5 (share 0)` at node 2, whose
    function part (the compiled `#5`) carries a record (node 1) replaying
    `metaSharing[0]` in its own scope, and whose argument `share 0` is the
    primary entry. Source: `(#1 #2 #3) (#1 #2)`. -/
private def msNestedRecord : Bool :=
  let m1 : Ixon.Expr := .app (.var 5) (.share 0)
  let arena : ExprMetaArena := ⟨#[
    .leaf, .mdata #[msRecord 0 0] 0, .app 1 0, .mdata #[msRecord 1 2] 0 ]⟩
  okEq (msRun (msCtx #[sharedM0, m1] arena) (rootIdx := 3)) ixM1

/-- Whole-constant path (`decompileAxiom` → `withFreshBlock`): the table
    check rejects a malformed entry that no record reads, and a valid
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
  | .ok (.axiomInfo v) => v.cnst.type == ixM1 && v.cnst.name == nAx
  | _ => false

private def msAxiomUnreadEntryRejected : Bool :=
  -- Entry 2 is never read (the record reads entry 1) but references
  -- itself (`share 3 = p + 2`). The error names the constant.
  let r := msAxiom #[sharedM0, sharedM1, .app (.share 3) (.var 0)]
  isMetaShareErr 3 2 1 3 r && match r with
    | .error (.invalidMetaShareIndex _ _ _ _ c) => c == nAx.pretty
    | _ => false

/-- Regression: metadata without shares behaves as before. -/
private def msNoShares : Bool :=
  okEq (msRun (msCtx #[plainM0] (msArena 0))) ixM0
    && (validateMetaSharing 0 #[plainM0, plainM1] matches .ok ())

/-- The table check visits each shared node once: the chain
    `e(k+1) = app e(k) e(k)` of depth 64 (2^64 nodes as a tree) validates, and
    the first violation inside it is still its leftmost leaf. -/
private def msSharedChain : Bool :=
  let chain := (List.range 64).foldl (fun e _ => Ixon.Expr.app e e)
    (Ixon.Expr.app (.share 0) (.var 0))
  (validateMetaSharing 1 #[chain, chain] matches .ok ()) &&
    isMetaShareErr 0 0 0 1 (validateMetaSharing 0 #[chain])

/-! ### Lean/Rust parity through the `.ixe` decompile FFI

The same serialized env is decompiled by the Lean decompiler and by the
Rust one (`rs_decompile_env_consts`, i.e. `decompile_env` plus
materialization): both must accept a valid shared table with the same
result, and both must reject the malformed ones with the same
`invalidMetaShareIndex` fields. -/

/-- `MS.head : Sort 0` and `MS.ax`, whose type is the compiled `head #99`
    under the record for `metaSharing[1]`, carrying `metaSharing`. -/
private def msParityEnv (metaSharing : Array Ixon.Expr) : Ixon.Env := Id.run do
  let headC : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let headAddr := Address.blake3 (Ixon.serConstant headC)
  let axC : Ixon.Constant :=
    ⟨.axio ⟨false, 0, msRoot⟩, #[prim0], #[headAddr], #[]⟩
  let axAddr := Address.blake3 (Ixon.serConstant axC)
  let mut env : Ixon.Env := msNames {}
  env := env.storeConst headAddr headC
  env := env.storeConst axAddr axC
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

/-- `MS.ax`'s type as Rust materializes it: `(#1 #2 #3) (#1 #2)`. -/
private def msParityLeanExpr : Lean.Expr :=
  let b := Lean.mkBVar
  let prim := Lean.mkApp (b 1) (b 2)
  .app (.app prim (b 3)) prim

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
      if ty != ixM1 then return some s!"{label}: Lean type differs"
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

/-! ## Pass 3 decompile records (pure unit, and Lean/Rust parity)

A call site that Pass 3 rewrote carries the decompile record
`[(_ix.inline, s), (_ix.inline_meta, m)]` on its metadata chain: the
decompiled term is the source occurrence `metaSharing[s]` read at arena root
`m`, not the compiled (rewritten) term under the record. No compiler writes
a record before Pass 3 is wired, so these hand-built fixtures pin the reader
rule in both decompilers (Rust mirror: `inline_record_tests` in
`crates/compile/src/decompile.rs`).

Every fixture: the compiled root `canon #2 #1` (`refs[0]`), one primary
sharing entry (`p = 1`), and the source occurrence `src #1 #2` as
`metaSharing[1]`, whose head is the extension reference `metaRefs[0]`
(virtual index 1) and whose first argument is the metadata share
`share 1 = metaSharing[0] = #1`. Arena nodes `0`–`4` describe the compiled
term, `5`–`9` the source occurrence; record and layer nodes follow. -/

section InlineRecord

open Ix.DecompileM Ixon

private def nCanon : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "IR.canon"
private def nSrc : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "IR.src"
private def nIrAx : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "IR.ax"
private def nTag : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "IR.tag"

/-- `n` as a metadata nat blob (the compiler's encoding). -/
private def natBlob (n : Nat) : ByteArray := ByteArray.mk (Nat.toBytesLE n)

private def natAddr (n : Nat) : Address := Address.admissionHash (natBlob n)

/-- The decompile record `[(_ix.inline, s), (_ix.inline_meta, m)]`. -/
private def record (s m : Nat) : Ixon.KVMap :=
  #[(Ix.Compile.Pass.inlineKey.getHash, .ofNat (natAddr s)),
    (Ix.Compile.Pass.inlineMetaKey.getHash, .ofNat (natAddr m))]

/-- An ordinary metadata layer. -/
private def tag (b : Bool) : Ixon.KVMap := #[(nTag.getHash, .ofBool b)]

/-- The names and nat blobs the fixtures read. -/
private def irNames (env : Ixon.Env) : Ixon.Env := Id.run do
  let mut env := { env with
    names := [nCanon, nSrc, nIrAx, nTag, Ix.Compile.Pass.inlineKey,
      Ix.Compile.Pass.inlineMetaKey].foldl (init := env.names)
      Ixon.RawEnv.addNameComponents }
  for n in [0, 1, 3, 5, 9, 99] do
    env := (env.storeBlob (natBlob n)).1
  return env

private def irEnv : DecompileEnv := { ixonEnv := irNames {} }

/-- The compiled (rewritten) root `canon #2 #1`. -/
private def irRoot : Ixon.Expr := .app (.app (.ref 0 #[]) (.var 2)) (.var 1)

/-- `metaSharing`: `#1`, and the source occurrence `src (share 1) #2`. -/
private def irMetaSharing : Array Ixon.Expr :=
  #[.var 1, .app (.app (.ref 1 #[]) (.share 1)) (.var 2)]

private def irCanonAddr : Address := Address.blake3 "inline-record-canon".toUTF8
private def irSrcAddr : Address := Address.blake3 "inline-record-src".toUTF8

/-- The compiled term's nodes `0`–`4`, the source occurrence's `5`–`9`,
    then `extra`. -/
private def irArena (extra : Array ExprMetaData) : ExprMetaArena := ⟨#[
  .ref nCanon.getHash, .leaf, .app 0 1, .leaf, .app 2 3,
  .ref nSrc.getHash, .leaf, .app 5 6, .leaf, .app 7 8] ++ extra⟩

private def irConst (refs : Array Address := #[irCanonAddr]) : Ixon.Constant :=
  ⟨.axio ⟨false, 0, irRoot⟩, #[.var 7], refs, #[]⟩

private def irMeta (arena : ExprMetaArena) (root : UInt64)
    (metaSharing : Array Ixon.Expr := irMetaSharing)
    (src : Address := irSrcAddr) : ConstantMeta :=
  { info := .axio nIrAx.getHash #[] arena root, metaSharing, metaRefs := #[src] }

private def irRun (arena : ExprMetaArena) (root : UInt64)
    (metaSharing : Array Ixon.Expr := irMetaSharing)
    (denv : DecompileEnv := irEnv) : Except DecompileError Ix.Expr :=
  let ctx := mkBlockCtx (irConst) #[] #[] arena (irMeta arena root metaSharing)
  (DecompileM.run denv ctx {} (decompileExpr irRoot root)).map (·.1)

private def ixCanon : Ix.Expr :=
  Ix.Expr.mkApp (Ix.Expr.mkApp (Ix.Expr.mkConst nCanon #[]) (Ix.Expr.mkBVar 2))
    (Ix.Expr.mkBVar 1)

private def ixSrc : Ix.Expr :=
  Ix.Expr.mkApp (Ix.Expr.mkApp (Ix.Expr.mkConst nSrc #[]) (Ix.Expr.mkBVar 1))
    (Ix.Expr.mkBVar 2)

private def ixTag (b : Bool) (e : Ix.Expr) : Ix.Expr :=
  Ix.Expr.mkMData #[(nTag, .ofBool b)] e

private def errContains (r : Except DecompileError Ix.Expr) (msg : String) : Bool :=
  match r with
  | .error e => (toString e).contains msg
  | .ok _ => false

/-- The record (node 10) replays the source occurrence: `src #1 #2`, with
    the record's `s` a direct `metaSharing` index read in its own scope. -/
private def irReplays : Bool :=
  okEq (irRun (irArena #[.mdata #[record 1 9] 4]) 10) ixSrc

/-- Without the record the same root decodes to the compiled term. -/
private def irCompiledWithoutRecord : Bool :=
  okEq (irRun (irArena #[]) 4) ixCanon

/-- The chain's other layers wrap the replayed source, outermost first:
    `[tag true]` (node 11) over `[record, tag false]` (node 10). -/
private def irLayersKept : Bool :=
  okEq (irRun (irArena #[.mdata #[record 1 9, tag false] 4,
      .mdata #[tag true] 10]) 11)
    (ixTag true (ixTag false ixSrc))

/-- The first record on the chain is replayed; a later one is dropped, not
    kept as a layer (the inner record would give `#1`). -/
private def irFirstRecordWins : Bool :=
  okEq (irRun (irArena #[.mdata #[record 1 9] 11, .mdata #[record 0 3] 4]) 10) ixSrc

/-- A single `_ix.inline` key (the rewrite's placeholder shape) is not a
    record: it stays an ordinary layer over the compiled term. -/
private def irSingleKeyIsMetadata : Bool :=
  let placeholder : Ixon.KVMap :=
    #[(Ix.Compile.Pass.inlineKey.getHash, .ofNat (natAddr 1))]
  okEq (irRun (irArena #[.mdata #[placeholder] 4]) 10)
    (Ix.Expr.mkMData #[(Ix.Compile.Pass.inlineKey, .ofNat 1)] ixCanon)

/-- `s` outside `metaSharing` is rejected. -/
private def irIndexOutOfRange : Bool :=
  errContains (irRun (irArena #[.mdata #[record 5 9] 4]) 10)
    "Pass 3 inline record 5 out of range (2 metadata entries)"

/-- `m` outside the arena is rejected. -/
private def irRootOutOfRange : Bool :=
  errContains (irRun (irArena #[.mdata #[record 1 99] 4]) 10)
    "Pass 3 inline record arena root 99 out of range (11 arena nodes)"

/-- `compiledTerms` reads the compiled term and drops the record, keeping
    the other layers. -/
private def irCompiledTerms : Bool :=
  okEq (irRun (irArena #[.mdata #[record 1 9, tag false] 4,
      .mdata #[tag true] 10]) 11 (denv := { irEnv with compiledTerms := true }))
    (ixTag true (ixTag false ixCanon))

/-- Whole-constant path (`decompileAxiom` → `withFreshBlock`): the
    extension tables come from the constant's metadata. -/
private def irAxiom : Bool :=
  let arena := irArena #[.mdata #[record 1 9] 4]
  let r := DecompileM.run irEnv default {} (decompileAxiom ⟨false, 0, irRoot⟩
    (irConst) (irMeta arena 10))
  match r with
  | .ok (.axiomInfo v, _) => v.cnst.type == ixSrc && v.cnst.name == nIrAx
  | _ => false

/-! ### Lean/Rust parity through the `.ixe` decompile FFI

The same serialized env is decompiled by the Lean decompiler and by the
Rust one (`rs_decompile_env_consts`): both replay a valid record to the
same type, and both reject the out-of-range ones with the same message. -/

/-- `IR.canon : Sort 1`, `IR.src : Sort 0`, and `IR.ax`, whose type is
    the compiled `canon #2 #1` under the record `(s, m)` (node 10). -/
private def irParityEnv (s m : Nat) : Ixon.Env := Id.run do
  let canonC : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let srcC : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let canonAddr := Address.blake3 (Ixon.serConstant canonC)
  let srcAddr := Address.blake3 (Ixon.serConstant srcC)
  let axC := irConst #[canonAddr]
  let axAddr := Address.blake3 (Ixon.serConstant axC)
  let mut env := irNames {}
  env := env.storeConst canonAddr canonC
  env := env.storeConst srcAddr srcC
  env := env.storeConst axAddr axC
  env := env.registerName nCanon
    { addr := canonAddr, constMeta := { info := .axio nCanon.getHash #[] ⟨#[.leaf]⟩ 0 } }
  env := env.registerName nSrc
    { addr := srcAddr, constMeta := { info := .axio nSrc.getHash #[] ⟨#[.leaf]⟩ 0 } }
  env := env.registerName nIrAx
    { addr := axAddr,
      constMeta := irMeta (irArena #[.mdata #[record s m] 4]) 10 (src := srcAddr) }
  return env

/-- Lean side, from the serialized bytes: `IR.ax`'s decompiled type. -/
private def irParityLean (bytes : ByteArray) :
    Except String (Except DecompileError Ix.Expr) := do
  let env ← Ixon.deEnv bytes
  let some named := env.named.get? nIrAx | throw "IR.ax not in the decoded env"
  let some cnst := env.getConst? named.addr | throw "IR.ax constant missing"
  let .axio ax := cnst.info | throw "IR.ax is not an axiom"
  return (DecompileM.run { ixonEnv := env } default {}
    (decompileAxiom ax cnst named.constMeta)).map fun (ci, _) => ci.getCnst.type

/-- `IR.ax`'s type as Rust materializes it: `IR.src #1 #2`. -/
private def irParityLeanExpr : Lean.Expr :=
  .app (.app (.const (Lean.Name.mkSimple "IR.src") []) (Lean.mkBVar 1)) (Lean.mkBVar 2)

/-- Run both decompilers on `irParityEnv s m`. `expect` is `none` for the
    replay, or a message both rejections contain. -/
private def irParityCase (label : String) (s m : Nat) (expect : Option String) :
    IO (Option String) := do
  let bytes ← match Ixon.serEnv (irParityEnv s m) with
    | .ok b => pure b
    | .error e => return some s!"{label}: serEnv failed: {e}"
  let dir ← IO.FS.createTempDir
  let path := (dir / "inline-record.ixe").toString
  try
    IO.FS.writeBinFile path bytes
    let lean ← match irParityLean bytes with
      | .ok r => pure r
      | .error e => return some s!"{label}: Lean env: {e}"
    let rust : Except String (Array (Lean.Name × Lean.ConstantInfo)) ←
      tryCatch (Except.ok <$> Ix.ImportIxe.materializeIxe path)
        fun e => pure (Except.error (toString e))
    match expect, lean, rust with
    | none, .ok ty, .ok consts =>
      let rustTy := consts.findSome? fun (n, ci) =>
        if n == Lean.Name.mkSimple "IR.ax" then some ci.type else none
      if ty != ixSrc then return some s!"{label}: Lean type differs"
      if rustTy != some irParityLeanExpr then
        return some s!"{label}: Rust type differs: {rustTy}"
      return none
    | some msg, .error le, .error re =>
      if !(toString le).contains msg then
        return some s!"{label}: Lean rejected with {le}"
      if !re.contains msg then
        return some s!"{label}: Rust rejected with {re}"
      return none
    | _, l, r =>
      let ls := match l with | .ok _ => "accepted" | .error e => toString e
      let rs := match r with | .ok _ => "accepted" | .error e => e
      return some s!"{label}: Lean {ls}; Rust {rs}"
  finally
    IO.FS.removeDirAll dir

private def irParity : TestSeq :=
  .individualIO "inline record: Lean/Rust decompile parity" none (do
    let cases : List (String × Nat × Nat × Option String) := [
      ("replay", 1, 9, none),
      ("index out of range", 5, 9,
        some "Pass 3 inline record 5 out of range (2 metadata entries)"),
      ("root out of range", 1, 99,
        some "Pass 3 inline record arena root 99 out of range (11 arena nodes)") ]
    let mut failures : Array String := #[]
    for (label, s, m, expect) in cases do
      if let some msg ← irParityCase label s m expect then
        failures := failures.push msg
    if failures.isEmpty then
      return (true, 0, 0, none)
    else
      return (false, 0, 0, some ("; ".intercalate failures.toList))) .done

end InlineRecord

/-! ## Compiler support under reserved names (pure unit)

The full driver's Pass 1 skips names with a reserved `_ix` component
(compiler support, refused as compiler input, so never a source
declaration). No compiler writes one before Pass 3 is wired, so a
hand-built env holds `RS.src : Sort 0` and, with `support`,
`RS._ix.helper : Sort 1`. -/

section ReservedSupport

open Ix.DecompileM Ixon

private def rsAxiom (env : Ixon.Env) (n : Ix.Name) (univ : Ixon.Univ) : Ixon.Env :=
  let c : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[univ]⟩
  let addr := Address.blake3 (Ixon.serConstant c)
  let env := { env with names := Ixon.RawEnv.addNameComponents env.names n }
  (env.storeConst addr c).registerName n
    { addr, constMeta := { info := .axio n.getHash #[] ⟨#[.leaf]⟩ 0 } }

private def nRsSrc : Ix.Name := Ix.Name.fromLeanName `RS.src
private def nRsHelper : Ix.Name := Ix.Name.fromLeanName `RS._ix.helper

private def rsEnv (support : Bool) : Ixon.Env :=
  let env := rsAxiom {} nRsSrc .zero
  if support then rsAxiom env nRsHelper (.succ .zero) else env

/-- The full driver decompiles the source axiom and skips the support. The
    input is read through a reference, so the driver (whose recompiles call
    the FFI) runs when the test runs, not as a closed term when the suite is
    built. -/
private def rsSupportSkipped : TestSeq :=
  .individualIO "reserved support: the full driver skips it" none (do
    let support ← IO.mkRef true
    let (decompiled, errors, _) := decompileEnvFull (rsEnv (← support.get)) {}
    if errors.isEmpty && decompiled.contains nRsSrc && !decompiled.contains nRsHelper
        && decompiled.size == 1 then
      return (true, 0, 0, none)
    return (false, 0, 0, some s!"decompiled {decompiled.size} constants, \
      {errors.size} errors, support present: {decompiled.contains nRsHelper}")) .done

end ReservedSupport

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
    ++ test "metadata share: forward reference rejected" msForward
    ++ test "metadata share: self reference rejected" msSelf
    ++ test "metadata share: i ≥ p + q rejected" msOutOfRange
    ++ test "metadata share: primary share ≥ p still rejected"
      msPrimaryUnchanged
    ++ test "metadata share: expression cache keyed by scope" msCacheScope
    ++ test "metadata share: a record nested in an entry crosses scopes"
      msNestedRecord
    ++ test "metadata share: whole constant decompiles" msAxiomOk
    ++ test "metadata share: unread malformed entry rejected"
      msAxiomUnreadEntryRejected
    ++ test "metadata share: tables without shares unchanged" msNoShares
    ++ test "metadata share: shared subterms are checked once" msSharedChain,
  msParity,
  test "inline record: the source occurrence is replayed" irReplays
    ++ test "inline record: without a record the compiled term is read"
      irCompiledWithoutRecord
    ++ test "inline record: other layers wrap the replayed source" irLayersKept
    ++ test "inline record: the first record on the chain is replayed"
      irFirstRecordWins
    ++ test "inline record: a single _ix.inline key is ordinary metadata"
      irSingleKeyIsMetadata
    ++ test "inline record: metaSharing index out of range rejected"
      irIndexOutOfRange
    ++ test "inline record: arena root out of range rejected" irRootOutOfRange
    ++ test "inline record: compiledTerms reads the compiled term"
      irCompiledTerms
    ++ test "inline record: whole constant decompiles" irAxiom,
  rsSupportSkipped,
  irParity
]

/-! ## Test Suite -/

public def decompileSuiteIO : List TestSeq := [
  testDecompile,
]

end Tests.Decompile
