/-
  Ixon.* type FFI roundtrip tests.
  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/
module

public import LSpec
public import Tests.Gen.Ixon
public import Ix.Ixon

public section

open LSpec SlimCheck Gen Ixon
open Ix (DefKind DefinitionSafety QuotKind)

namespace Tests.FFI.Ixon

/-! ## Ixon type roundtrip FFI declarations -/

-- Simple enums (use lean_box/lean_unbox)
@[extern "rs_roundtrip_ixon_def_kind"]
opaque roundtripIxonDefKind : @& DefKind → DefKind

@[extern "rs_roundtrip_ixon_definition_safety"]
opaque roundtripIxonDefinitionSafety : @& DefinitionSafety → DefinitionSafety

@[extern "rs_roundtrip_ixon_quot_kind"]
opaque roundtripIxonQuotKind : @& QuotKind → QuotKind

-- Core recursive types
@[extern "rs_roundtrip_ixon_univ"]
opaque roundtripIxonUniv : @& Univ → Univ

@[extern "rs_roundtrip_ixon_expr"]
opaque roundtripIxonExpr : @& Expr → Expr

-- Constant structures
@[extern "rs_roundtrip_ixon_definition"]
opaque roundtripIxonDefinition : @& Definition → Definition

@[extern "rs_roundtrip_ixon_recursor_rule"]
opaque roundtripIxonRecursorRule : @& RecursorRule → RecursorRule

@[extern "rs_roundtrip_ixon_recursor"]
opaque roundtripIxonRecursor : @& Recursor → Recursor

@[extern "rs_roundtrip_ixon_axiom"]
opaque roundtripIxonAxiom : @& Axiom → Axiom

@[extern "rs_roundtrip_ixon_quotient"]
opaque roundtripIxonQuotient : @& Quotient → Quotient

@[extern "rs_roundtrip_ixon_constructor"]
opaque roundtripIxonConstructor : @& Constructor → Constructor

@[extern "rs_roundtrip_ixon_inductive"]
opaque roundtripIxonInductive : @& Inductive → Inductive

-- Projection types
@[extern "rs_roundtrip_ixon_inductive_proj"]
opaque roundtripIxonInductiveProj : @& InductiveProj → InductiveProj

@[extern "rs_roundtrip_ixon_constructor_proj"]
opaque roundtripIxonConstructorProj : @& ConstructorProj → ConstructorProj

@[extern "rs_roundtrip_ixon_recursor_proj"]
opaque roundtripIxonRecursorProj : @& RecursorProj → RecursorProj

@[extern "rs_roundtrip_ixon_definition_proj"]
opaque roundtripIxonDefinitionProj : @& DefinitionProj → DefinitionProj

-- Composite types
@[extern "rs_roundtrip_ixon_mut_const"]
opaque roundtripIxonMutConst : @& MutConst → MutConst

@[extern "rs_roundtrip_ixon_constant_info"]
opaque roundtripIxonConstantInfo : @& ConstantInfo → ConstantInfo

@[extern "rs_roundtrip_ixon_constant"]
opaque roundtripIxonConstant : @& Constant → Constant

-- Metadata types
@[extern "rs_roundtrip_ixon_data_value"]
opaque roundtripIxonDataValue : @& DataValue → DataValue

@[extern "rs_roundtrip_ixon_expr_meta_data"]
opaque roundtripIxonExprMetaData : @& ExprMetaData → ExprMetaData

@[extern "rs_roundtrip_ixon_expr_meta_arena"]
opaque roundtripIxonExprMetaArena : @& ExprMetaArena → ExprMetaArena

@[extern "rs_roundtrip_ixon_constant_meta"]
opaque roundtripIxonConstantMeta : @& ConstantMeta → ConstantMeta

@[extern "rs_roundtrip_ixon_named"]
opaque roundtripIxonNamed : @& Named → Named

@[extern "rs_roundtrip_ixon_comm"]
opaque roundtripIxonComm : @& Comm → Comm

/-! ## Ixon type FFI unit tests -/

def ixonDefKindTests : TestSeq :=
  test "Ixon.DefKind.defn" (roundtripIxonDefKind .defn == .defn) ++
  test "Ixon.DefKind.opaq" (roundtripIxonDefKind .opaq == .opaq) ++
  test "Ixon.DefKind.thm" (roundtripIxonDefKind .thm == .thm)

def ixonDefinitionSafetyTests : TestSeq :=
  test "Ixon.DefinitionSafety.unsaf" (roundtripIxonDefinitionSafety .unsaf == .unsaf) ++
  test "Ixon.DefinitionSafety.safe" (roundtripIxonDefinitionSafety .safe == .safe) ++
  test "Ixon.DefinitionSafety.part" (roundtripIxonDefinitionSafety .part == .part)

def ixonQuotKindTests : TestSeq :=
  test "Ixon.QuotKind.type" (roundtripIxonQuotKind .type == .type) ++
  test "Ixon.QuotKind.ctor" (roundtripIxonQuotKind .ctor == .ctor) ++
  test "Ixon.QuotKind.lift" (roundtripIxonQuotKind .lift == .lift) ++
  test "Ixon.QuotKind.ind" (roundtripIxonQuotKind .ind == .ind)

def ixonUnivTests : TestSeq :=
  test "Ixon.Univ.zero" (roundtripIxonUniv .zero == .zero) ++
  test "Ixon.Univ.var 0" (roundtripIxonUniv (.var 0) == .var 0) ++
  test "Ixon.Univ.var 42" (roundtripIxonUniv (.var 42) == .var 42) ++
  test "Ixon.Univ.succ zero" (roundtripIxonUniv (.succ .zero) == .succ .zero) ++
  test "Ixon.Univ.max" (roundtripIxonUniv (.max .zero (.var 1)) == .max .zero (.var 1)) ++
  test "Ixon.Univ.imax" (roundtripIxonUniv (.imax (.var 0) .zero) == .imax (.var 0) .zero)

def ixonExprTests : TestSeq :=
  test "Ixon.Expr.sort" (roundtripIxonExpr (.sort 0) == .sort 0) ++
  test "Ixon.Expr.var" (roundtripIxonExpr (.var 5) == .var 5) ++
  test "Ixon.Expr.ref" (roundtripIxonExpr (.ref 1 #[0, 1]) == .ref 1 #[0, 1]) ++
  test "Ixon.Expr.recur" (roundtripIxonExpr (.recur 2 #[]) == .recur 2 #[]) ++
  test "Ixon.Expr.str" (roundtripIxonExpr (.str 3) == .str 3) ++
  test "Ixon.Expr.nat" (roundtripIxonExpr (.nat 42) == .nat 42) ++
  test "Ixon.Expr.share" (roundtripIxonExpr (.share 0) == .share 0) ++
  test "Ixon.Expr.app" (roundtripIxonExpr (.app (.var 0) (.var 1)) == .app (.var 0) (.var 1)) ++
  test "Ixon.Expr.lam" (roundtripIxonExpr (.lam (.sort 0) (.var 0)) == .lam (.sort 0) (.var 0)) ++
  test "Ixon.Expr.all" (roundtripIxonExpr (.all (.sort 0) (.var 0)) == .all (.sort 0) (.var 0)) ++
  test "Ixon.Expr.letE" (roundtripIxonExpr (.letE true (.sort 0) (.var 0) (.var 1)) == .letE true (.sort 0) (.var 0) (.var 1)) ++
  test "Ixon.Expr.prj" (roundtripIxonExpr (.prj 0 1 (.var 0)) == .prj 0 1 (.var 0))

/-! ## Metadata Unit Tests -/

def exprMetaDataTests : TestSeq :=
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let _kvmap : KVMap := #[(testAddr, DataValue.ofBool true)]
  test "ExprMetaData.leaf" (roundtripIxonExprMetaData .leaf == .leaf) ++
  test "ExprMetaData.app" (roundtripIxonExprMetaData (.app 0 1) == .app 0 1) ++
  test "ExprMetaData.ref" (roundtripIxonExprMetaData (.ref testAddr) == .ref testAddr) ++
  test "ExprMetaData.prj" (roundtripIxonExprMetaData (.prj testAddr 5) == .prj testAddr 5) ++
  test "ExprMetaData.letBinder" (roundtripIxonExprMetaData (.letBinder testAddr 0 1 2) == .letBinder testAddr 0 1 2) ++
  test "ExprMetaData.mdata empty" (roundtripIxonExprMetaData (.mdata #[] 0) == .mdata #[] 0) ++
  test "ExprMetaData.mdata with kvmap" (roundtripIxonExprMetaData (.mdata #[_kvmap] 3) == .mdata #[_kvmap] 3) ++
  test "ExprMetaData.binder default" (roundtripIxonExprMetaData (.binder testAddr .default 0 1) == .binder testAddr .default 0 1) ++
  test "ExprMetaData.binder implicit" (roundtripIxonExprMetaData (.binder testAddr .implicit 2 3) == .binder testAddr .implicit 2 3) ++
  test "ExprMetaData.binder strictImplicit" (roundtripIxonExprMetaData (.binder testAddr .strictImplicit 0 0) == .binder testAddr .strictImplicit 0 0) ++
  test "ExprMetaData.binder instImplicit" (roundtripIxonExprMetaData (.binder testAddr .instImplicit 0 0) == .binder testAddr .instImplicit 0 0)

def exprMetaArenaTests : TestSeq :=
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let emptyArena : ExprMetaArena := {}
  let singleLeaf : ExprMetaArena := { nodes := #[.leaf] }
  let smallArena : ExprMetaArena := { nodes := #[.leaf, .app 0 0, .ref testAddr] }
  let mixedArena : ExprMetaArena := { nodes := #[
    .leaf, .ref testAddr, .app 0 0, .binder testAddr .default 0 1,
    .letBinder testAddr 0 1 2, .prj testAddr 0, .mdata #[] 0
  ] }
  checkIO "ExprMetaArena empty" (roundtripIxonExprMetaArena emptyArena == emptyArena) ++
  checkIO "ExprMetaArena single leaf" (roundtripIxonExprMetaArena singleLeaf == singleLeaf) ++
  checkIO "ExprMetaArena small" (roundtripIxonExprMetaArena smallArena == smallArena) ++
  checkIO "ExprMetaArena mixed" (roundtripIxonExprMetaArena mixedArena == mixedArena)

def constantMetaTests : TestSeq :=
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let emptyArena : ExprMetaArena := {}
  let smallArena : ExprMetaArena := { nodes := #[.leaf, .app 0 0, .ref testAddr] }
  checkIO "ConstantMeta.empty" (roundtripIxonConstantMeta .empty == .empty) ++
  checkIO "ConstantMeta.defn" (roundtripIxonConstantMeta
    (.defn testAddr #[testAddr] .opaque #[] #[] smallArena 0 1) ==
    .defn testAddr #[testAddr] .opaque #[] #[] smallArena 0 1) ++
  checkIO "ConstantMeta.axio" (roundtripIxonConstantMeta
    (.axio testAddr #[] emptyArena 0) ==
    .axio testAddr #[] emptyArena 0) ++
  checkIO "ConstantMeta.ctor" (roundtripIxonConstantMeta
    (.ctor testAddr #[] testAddr smallArena 2) ==
    .ctor testAddr #[] testAddr smallArena 2) ++
  checkIO "ConstantMeta.recr" (roundtripIxonConstantMeta
    (.recr testAddr #[] #[] #[] #[] smallArena 0 #[1, 2]) ==
    .recr testAddr #[] #[] #[] #[] smallArena 0 #[1, 2])

/-! ## Cross-implementation serialization comparison FFI declarations -/

@[extern "rs_eq_univ_serialization"]
opaque rsEqUnivSerialization : @& Univ → @& ByteArray → Bool

@[extern "rs_eq_expr_serialization"]
opaque rsEqExprSerialization : @& Expr → @& ByteArray → Bool

@[extern "rs_eq_constant_serialization"]
opaque rsEqConstantSerialization : @& Constant → @& ByteArray → Bool

@[extern "rs_eq_env_serialization"]
opaque rsEqEnvSerialization : @& RawEnv → @& ByteArray → Bool

/-! ## RawEnv roundtrip FFI -/

@[extern "rs_roundtrip_raw_env"]
opaque roundtripRawEnv : @& RawEnv → RawEnv

instance : Shrinkable RawEnv where
  shrink env :=
    if env.consts.isEmpty && env.named.isEmpty && env.blobs.isEmpty && env.comms.isEmpty then []
    else [{
      consts := if env.consts.isEmpty then #[] else env.consts.pop,
      named := if env.named.isEmpty then #[] else env.named.pop,
      blobs := if env.blobs.isEmpty then #[] else env.blobs.pop,
      comms := if env.comms.isEmpty then #[] else env.comms.pop
    }]

/-- Compare RawEnv with content-aware comparison.
    Checks array sizes and content matching by Address. -/
def rawEnvEq (a b : RawEnv) : Bool :=
  a.consts.size == b.consts.size &&
  a.named.size == b.named.size &&
  a.blobs.size == b.blobs.size &&
  a.comms.size == b.comms.size &&
  a.names.size == b.names.size &&
  -- Size equality + one-directional all/any is sufficient when addresses are unique:
  -- if sizes match and every element in 'a' has a match in 'b', then 'b' cannot
  -- have extra elements (since sizes are equal and addresses uniquely identify items).
  -- Content comparison for consts
  a.consts.all fun rc =>
    b.consts.any fun rc' => rc.addr == rc'.addr &&
      rc.const.info == rc'.const.info &&
      rc.const.sharing.size == rc'.const.sharing.size &&
      rc.const.refs.size == rc'.const.refs.size &&
      rc.const.univs.size == rc'.const.univs.size

/-! ## RawEnv unit tests -/

def rawEnvTests : TestSeq :=
  let empty : RawEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
  -- Create test data for non-empty case
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let testExpr : Expr := .sort 0
  let testDef : Definition := {
    kind := .defn, safety := .safe, lvls := 0,
    typ := testExpr, value := testExpr
  }
  let testConst : Constant := {
    info := .defn testDef, sharing := #[], refs := #[], univs := #[]
  }
  let testRawConst : RawConst := { addr := testAddr, const := testConst }
  let testComm : Comm := { secret := testAddr, payload := testAddr }
  let testRawComm : RawComm := { addr := testAddr, comm := testComm }
  let testRawBlob : RawBlob := { addr := testAddr, bytes := ByteArray.mk #[1, 2, 3] }
  let testName := Ix.Name.mkStr Ix.Name.mkAnon "test"
  let testRawNamed : RawNamed := {
    name := testName, addr := testAddr, constMeta := .empty
  }
  let withData : RawEnv := {
    consts := #[testRawConst],
    named := #[testRawNamed],
    blobs := #[testRawBlob],
    comms := #[testRawComm]
  }
  test "RawEnv empty" (rawEnvEq (roundtripRawEnv empty) empty) ++
  test "RawEnv with data" (rawEnvEq (roundtripRawEnv withData) withData)

/-! ## Env diff FFI (`rs_diff_envs`)

The classification logic is covered by Rust unit tests
(`crates/ixon/src/diff.rs`); these tests pin the FFI marshaling — a
constructor-slot swap would surface as wrong-category contents. -/

def envDiffTests : TestSeq :=
  let fooName := Ix.Name.mkStr Ix.Name.mkAnon "foo"
  let barName := Ix.Name.mkStr Ix.Name.mkAnon "bar"
  -- `.var` exprs only: classification resolves table indices, so a
  -- `.sort 0` over an empty univs table would be a (correctly) rejected
  -- malformed constant.
  let mkConst (value : Expr) : Constant :=
    { info := .defn { kind := .defn, safety := .safe, lvls := 0,
                      typ := .var 3, value }
      sharing := #[], refs := #[], univs := #[] }
  -- Named metadata carries the hint; `anonHints` stays empty so the
  -- writer derives §3 from the named `Def` metadata.
  let mkEnv (c : Constant) (h : Lean.ReducibilityHints) : Env := Id.run do
    let addr := Address.blake3 (serConstant c)
    let mut env : Env := {}
    env := env.storeConst addr c
    env := { env with names := RawEnv.addNameComponents env.names fooName }
    env := env.registerName fooName
      { addr, constMeta := .defn fooName.getHash #[] h #[] #[] {} 0 0 }
    return env
  let constA := mkConst (.var 0)
  let constB := mkConst (.var 1)
  let addrA := Address.blake3 (serConstant constA)
  let addrB := Address.blake3 (serConstant constB)
  let envBase := mkEnv constA (.regular 5)
  let envValueChanged := mkEnv constB (.regular 5)
  let envHintChanged := mkEnv constA (.regular 6)
  let envExtra := Id.run do
    let mut env := envBase
    env := env.storeConst addrB constB
    env := { env with names := RawEnv.addNameComponents env.names barName }
    env := env.registerName barName { addr := addrB, constMeta := .empty }
    return env
  let runDiff (a b : Env) (compareMeta : Bool := false) :
      Option Ixon.EnvDiff :=
    (Ixon.rsDiffEnvs (serEnv a) (serEnv b) compareMeta).toOption
  test "EnvDiff: self-diff empty (anon)"
    ((runDiff envBase envBase).any (·.isEmpty)) ++
  test "EnvDiff: self-diff empty (meta)"
    ((runDiff envBase envBase true).any (·.isEmpty)) ++
  test "EnvDiff: stats populated"
    ((runDiff envBase envBase).any fun d =>
      d.statsA.consts == 1 && d.statsA.named == 1 && d.statsB == d.statsA) ++
  test "EnvDiff: added name"
    ((runDiff envBase envExtra).any fun d =>
      d.namedAdded == #[("bar", addrB)] && d.constsOnlyB == #[addrB]
      && d.namedRemoved.isEmpty && d.namedChanged.isEmpty) ++
  test "EnvDiff: removed name"
    ((runDiff envExtra envBase).any fun d =>
      d.namedRemoved == #[("bar", addrB)] && d.constsOnlyA == #[addrB]) ++
  test "EnvDiff: value change classified"
    ((runDiff envBase envValueChanged).any fun d =>
      d.namedChanged.size == 1 &&
      (d.namedChanged[0]!).name == "foo" &&
      (d.namedChanged[0]!).oldAddr == addrA &&
      (d.namedChanged[0]!).newAddr == addrB &&
      (d.namedChanged[0]!).oldKind == "defn" &&
      (d.namedChanged[0]!).newKind == "defn" &&
      (d.namedChanged[0]!).fields == #["value"] &&
      (d.namedChanged[0]!).metaFields.isEmpty &&
      (d.namedChanged[0]!).rippled == false) ++
  -- A dependent whose only change is its ref re-addressing must marshal
  -- `rippled == true` (pins the num_8 scalar slot against layout swaps).
  test "EnvDiff: ripple verdict marshals"
    (let mkRefConst (r : Address) : Constant :=
      { info := .defn { kind := .defn, safety := .safe, lvls := 0,
                        typ := .var 3, value := .ref 0 #[] }
        sharing := #[], refs := #[r], univs := #[] }
     let mkPair (leaf : Constant) : Env := Id.run do
       let leafAddr := Address.blake3 (serConstant leaf)
       let dep := mkRefConst leafAddr
       let depAddr := Address.blake3 (serConstant dep)
       let mut env : Env := {}
       env := env.storeConst leafAddr leaf
       env := env.storeConst depAddr dep
       env := { env with names := RawEnv.addNameComponents env.names fooName }
       env := env.registerName fooName { addr := leafAddr, constMeta := .empty }
       env := { env with names := RawEnv.addNameComponents env.names barName }
       env := env.registerName barName { addr := depAddr, constMeta := .empty }
       return env
     (runDiff (mkPair constA) (mkPair constB)).any fun d =>
       d.namedChanged.size == 2 &&
       (d.namedChanged.find? (·.name == "foo")).any (·.rippled == false) &&
       (d.namedChanged.find? (·.name == "bar")).any (·.rippled == true)) ++
  -- Hints derive into anon §3, so a hint tweak is visible in the
  -- default anon mode; the metadata carrying it only shows under meta.
  test "EnvDiff: hint change visible in anon mode"
    ((runDiff envBase envHintChanged).any fun d =>
      d.hintsChanged == #[(addrA, "regular(5)", "regular(6)")]
      && d.namedMetaOnly.isEmpty && d.namedChanged.isEmpty) ++
  test "EnvDiff: hint change flags metadata under meta mode"
    ((runDiff envBase envHintChanged true).any fun d =>
      d.hintsChanged.size == 1
      && d.namedMetaOnly == #[("foo", #["meta.info"])]) ++
  test "EnvDiff: main change"
    ((runDiff { envBase with main := some addrA } envBase).any fun d =>
      d.mainChanged == some (some addrA, none)) ++
  test "EnvDiff: assumptions delta"
    (let p := Address.blake3 (ByteArray.mk #[1])
     let q := Address.blake3 (ByteArray.mk #[2])
     let r := Address.blake3 (ByteArray.mk #[3])
     let a := { envBase with
       assumptions := ({} : Std.HashSet Address).insert p |>.insert q }
     let b := { envBase with
       assumptions := ({} : Std.HashSet Address).insert q |>.insert r }
     (runDiff a b).any fun d =>
       d.assumptionsAdded == #[r] && d.assumptionsRemoved == #[p]) ++
  -- The mmap file-path entry must agree with the bytes-based one, and
  -- the byte-equality fast path must distinguish same vs different.
  (TestSeq.individualIO "EnvDiff: file-based diff matches bytes-based"
    none (do
      let dir ← IO.FS.createTempDir
      let pa := dir / "a.ixe"
      let pb := dir / "b.ixe"
      let bytesA := serEnv envBase
      let bytesB := serEnv envValueChanged
      IO.FS.writeBinFile pa bytesA
      IO.FS.writeBinFile pb bytesB
      let r ← try
        let eqSame ← Ixon.rsIxeFilesEqual pa.toString pa.toString
        let eqDiff ← Ixon.rsIxeFilesEqual pa.toString pb.toString
        let dFiles ← Ixon.rsDiffEnvFiles pa.toString pb.toString false
        let ok := eqSame && !eqDiff &&
          (match Ixon.rsDiffEnvs bytesA bytesB false with
           | .ok dBytes => dFiles == dBytes
           | .error _ => false)
        pure (ok, if ok then none else some "file/bytes reports disagree")
      catch e => pure (false, some e.toString)
      IO.FS.removeDirAll dir
      pure (r.1, 0, 0, r.2)) .done)

/-- Self-diff over the pure-Lean writer's bytes must be empty in both
    modes (also exercises report marshaling on arbitrary inputs). -/
def selfDiffEmpty (compareMeta : Bool) (env : RawEnv) : Bool :=
  match Ixon.rsDiffEnvs (serEnv env.toEnv) (serEnv env.toEnv) compareMeta with
  | .ok d => d.isEmpty
  | .error _ => false

/-! ## Env pack FFI (`rs_pack_env`)

The prune/validate engine is covered by Rust unit tests (the
`prune_to_closure` tests in `crates/ixon/src/env.rs`); these pin the
FFI surface end-to-end — file IO, name/hex resolution, bundle-field
population — and the closed-subset relationship to the source env. -/

/-- Write `env` to a temp `.ixe`, pack `mainName` with `assume` cuts,
    and parse the resulting bundle. Pack failures surface as `.error`. -/
private def packFixture (env : Env) (mainName : String)
    (assume : Array String) (anon : Bool := false) :
    IO (Except String Env) := do
  let dir ← IO.FS.createTempDir
  let src := dir / "src.ixe"
  let out := dir / "bundle.ixe"
  -- Every failure mode is caught into `.error`, so cleanup always runs.
  let result ← try
    IO.FS.writeBinFile src (serEnv env)
    Ixon.rsPackEnv src.toString mainName assume out.toString anon false
    let bytes ← IO.FS.readBinFile out
    pure (Ixon.rsDeEnv bytes)
  catch e =>
    pure (.error e.toString)
  IO.FS.removeDirAll dir
  return result

/-- IO test asserting on a successfully packed bundle. -/
private def packTest (descr : String) (act : IO (Except String Env))
    (check : Env → Bool) : TestSeq :=
  .individualIO descr none (do
    match ← act with
    | .ok bundle =>
      let ok := check bundle
      pure (ok, 0, 0, if ok then none else some "bundle assertion failed")
    | .error e => pure (false, 0, 0, some e)) .done

/-- IO test asserting the pack call fails. -/
private def packErrTest (descr : String) (act : IO (Except String Env)) :
    TestSeq :=
  .individualIO descr none (do
    match ← act with
    | .ok _ => pure (false, 0, 0, some "expected pack to fail")
    | .error _ => pure (true, 0, 0, none)) .done

def envPackTests : TestSeq :=
  let fooName := Ix.Name.mkStr Ix.Name.mkAnon "foo"
  let barName := Ix.Name.mkStr Ix.Name.mkAnon "bar"
  let quxName := Ix.Name.mkStr Ix.Name.mkAnon "qux"
  let leaf (v : UInt64) : Constant :=
    { info := .defn { kind := .defn, safety := .safe, lvls := 0,
                      typ := .var 3, value := .var v }
      sharing := #[], refs := #[], univs := #[] }
  let fooConst := leaf 0
  let quxConst := leaf 1
  let fooAddr := Address.blake3 (serConstant fooConst)
  -- `bar` reaches `foo` through its refs table (a genuine closure
  -- edge); `qux` is unreachable from `bar` and must be pruned away.
  let barConst : Constant :=
    { info := .defn { kind := .defn, safety := .safe, lvls := 0,
                      typ := .var 3, value := .ref 0 #[] }
      sharing := #[], refs := #[fooAddr], univs := #[] }
  let barAddr := Address.blake3 (serConstant barConst)
  let src : Env := Id.run do
    let mut env : Env := {}
    for (n, c) in [(fooName, fooConst), (barName, barConst),
                   (quxName, quxConst)] do
      let addr := Address.blake3 (serConstant c)
      env := env.storeConst addr c
      -- String components ride as blobs (the compiler's convention);
      -- prune's `carry_name` recreates them in the bundle, so a fixture
      -- without them would spuriously diff as bundle-only blobs.
      let (names, blobs) :=
        RawEnv.addNameComponentsWithBlobs env.names env.blobs n
      env := { env with names, blobs }
      env := env.registerName n { addr, constMeta := .empty }
    return env
  packTest "EnvPack: closure bundle pins main and prunes"
    (packFixture src "bar" #[]) (fun b =>
      b.main == some barAddr
      && b.getAddr? barName == some barAddr
      && b.getAddr? fooName == some fooAddr
      && (b.getAddr? quxName).isNone
      && b.consts.size == 2
      && b.assumptions.isEmpty) ++
  (TestSeq.individualIO "EnvPack: bundle is a removals-only subset under diff"
    none (do
      match ← packFixture src "bar" #[] with
      | .error e => pure (false, 0, 0, some e)
      | .ok b =>
        match Ixon.rsDiffEnvs (serEnv src) (serEnv b) with
        | .error e => pure (false, 0, 0, some s!"diff failed: {e}")
        | .ok d =>
          let ok := d.mainChanged == some (none, some barAddr)
            && d.namedRemoved.size == 1
            && d.namedAdded.isEmpty && d.namedChanged.isEmpty
            && d.constsOnlyB.isEmpty && d.blobsOnlyB.isEmpty
          let msg := s!"mainOk={d.mainChanged == some (none, some barAddr)} \
            removed={d.namedRemoved.map (·.1)} \
            added={d.namedAdded.map (·.1)} \
            changed={d.namedChanged.map (·.name)} \
            constsOnlyB={d.constsOnlyB.size} blobsOnlyB={d.blobsOnlyB.size}"
          pure (ok, 0, 0, if ok then none else some msg)) .done) ++
  packTest "EnvPack: assume cut (by name) records assumption"
    (packFixture src "bar" #["foo"]) (fun b =>
      b.main == some barAddr
      && (b.getAddr? fooName).isNone
      && b.consts.size == 1
      && b.assumptions.size == 1
      && b.assumptions.contains fooAddr) ++
  packTest "EnvPack: assume cut (by hex address) records assumption"
    (packFixture src "bar" #[toString fooAddr]) (fun b =>
      b.consts.size == 1 && b.assumptions.contains fooAddr) ++
  packTest "EnvPack: anon bundle has no metadata, keeps the value pin"
    (packFixture src "bar" #[] (anon := true)) (fun b =>
      b.main == some barAddr
      && b.named.isEmpty
      -- The writer always emits the anonymous name as §4 entry 0.
      && b.names.size <= 1
      && b.consts.size == 2
      && (b.getAddr? barName).isNone) ++
  packErrTest "EnvPack: unknown root name errors"
    (packFixture src "nope" #[]) ++
  packErrTest "EnvPack: main cannot be assumed"
    (packFixture src "bar" #["bar"])

/-! ## Test Suite -/

def suite : List TestSeq := [
  -- Ixon type unit tests
  ixonDefKindTests,
  ixonDefinitionSafetyTests,
  ixonQuotKindTests,
  ixonUnivTests,
  ixonExprTests,
  exprMetaDataTests,
  exprMetaArenaTests,
  constantMetaTests,
  rawEnvTests,
  -- Ixon property tests - basic types
  checkIO "Ixon.DefKind roundtrip" (∀ x : DefKind, roundtripIxonDefKind x == x),
  checkIO "Ixon.DefinitionSafety roundtrip" (∀ x : DefinitionSafety, roundtripIxonDefinitionSafety x == x),
  checkIO "Ixon.QuotKind roundtrip" (∀ x : QuotKind, roundtripIxonQuotKind x == x),
  checkIO "Ixon.Univ roundtrip" (∀ x : Univ, roundtripIxonUniv x == x),
  checkIO "Ixon.Expr roundtrip" (∀ x : Expr, roundtripIxonExpr x == x),
  checkIO "Ixon.Definition roundtrip" (∀ x : Definition, roundtripIxonDefinition x == x),
  checkIO "Ixon.RecursorRule roundtrip" (∀ x : RecursorRule, roundtripIxonRecursorRule x == x),
  checkIO "Ixon.Recursor roundtrip" (∀ x : Recursor, roundtripIxonRecursor x == x),
  checkIO "Ixon.Axiom roundtrip" (∀ x : Axiom, roundtripIxonAxiom x == x),
  checkIO "Ixon.Quotient roundtrip" (∀ x : Quotient, roundtripIxonQuotient x == x),
  checkIO "Ixon.Constructor roundtrip" (∀ x : Constructor, roundtripIxonConstructor x == x),
  checkIO "Ixon.Inductive roundtrip" (∀ x : Inductive, roundtripIxonInductive x == x),
  checkIO "Ixon.InductiveProj roundtrip" (∀ x : InductiveProj, roundtripIxonInductiveProj x == x),
  checkIO "Ixon.ConstructorProj roundtrip" (∀ x : ConstructorProj, roundtripIxonConstructorProj x == x),
  checkIO "Ixon.RecursorProj roundtrip" (∀ x : RecursorProj, roundtripIxonRecursorProj x == x),
  checkIO "Ixon.DefinitionProj roundtrip" (∀ x : DefinitionProj, roundtripIxonDefinitionProj x == x),
  checkIO "Ixon.MutConst roundtrip" (∀ x : MutConst, roundtripIxonMutConst x == x),
  checkIO "Ixon.ConstantInfo roundtrip" (∀ x : ConstantInfo, roundtripIxonConstantInfo x == x),
  checkIO "Ixon.Constant roundtrip" (∀ x : Constant, roundtripIxonConstant x == x),
  checkIO "Ixon.DataValue roundtrip" (∀ x : DataValue, roundtripIxonDataValue x == x),
  checkIO "Ixon.Comm roundtrip" (∀ x : Comm, roundtripIxonComm x == x),
  -- Metadata types (arena-based)
  checkIO "Ixon.ExprMetaData roundtrip" (∀ x : ExprMetaData, roundtripIxonExprMetaData x == x),
  checkIO "Ixon.ConstantMeta roundtrip" (∀ x : ConstantMeta, roundtripIxonConstantMeta x == x),
  checkIO "Ixon.Named roundtrip" (∀ x : Named, roundtripIxonNamed x == x),
  ---- RawEnv roundtrip
  checkIO "Ixon.RawEnv roundtrip" (∀ env : RawEnv, rawEnvEq (roundtripRawEnv env) env),
  ---- Env diff
  envDiffTests,
  checkIO "Ixon.EnvDiff self-diff empty (anon)"
    (∀ env : RawEnv, selfDiffEmpty false env),
  checkIO "Ixon.EnvDiff self-diff empty (meta)"
    (∀ env : RawEnv, selfDiffEmpty true env),
  ---- Env pack
  envPackTests,
]

end Tests.FFI.Ixon

end
