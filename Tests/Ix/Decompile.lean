module
public import Ix.Ixon
public import Ix.Environment
public import Ix.Address
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.CompileCertified
public import Ix.DecompileM
public import Ix.DecompileDriver
public import Ix.ImportIxe
public import Lean
public import LSpec
public import Tests.Ix.Fixtures

/-!
  Decompilation tests.
  Runs the certified compilation pipeline, then decompiles back to Ix constants
  and compares via content hashes.
-/

open LSpec

namespace Tests.Decompile

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
(`validateMetaSharing`, which every constant's block setup runs).

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
    ++ test "metadata share: shared subterms are checked once" msSharedChain
]

end Tests.Decompile
