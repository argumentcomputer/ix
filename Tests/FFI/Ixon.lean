module

public import LSpec
public import Tests.Gen.Ixon
public import Ix.Ixon
public import Ix.Cli.DiffCmd

/-!
  Ixon.* type FFI roundtrip tests.
  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/

public section

open LSpec LSpec.Prop Gen Ixon
open Ix (DefKind DefinitionSafety QuotKind)

namespace Tests.FFI.Ixon

/-- `serEnv` for known-well-formed test fixtures: the env-construction
    helpers in this file always store the referenced consts and name
    components, so a serializer error here is a fixture bug — surface
    it as a panic. -/
def serEnv! (env : Env) : ByteArray :=
  match Ixon.serEnv env with
  | .ok bytes => bytes
  | .error e => panic! s!"serEnv! failed on test fixture: {e}"

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

def ixonDefKindTests : LSpec.Spec := do
  itBool "Ixon.DefKind.defn" (roundtripIxonDefKind .defn == .defn)
  itBool "Ixon.DefKind.opaq" (roundtripIxonDefKind .opaq == .opaq)
  itBool "Ixon.DefKind.thm" (roundtripIxonDefKind .thm == .thm)

def ixonDefinitionSafetyTests : LSpec.Spec := do
  itBool "Ixon.DefinitionSafety.unsaf" (roundtripIxonDefinitionSafety .unsaf == .unsaf)
  itBool "Ixon.DefinitionSafety.safe" (roundtripIxonDefinitionSafety .safe == .safe)
  itBool "Ixon.DefinitionSafety.part" (roundtripIxonDefinitionSafety .part == .part)

def ixonQuotKindTests : LSpec.Spec := do
  itBool "Ixon.QuotKind.type" (roundtripIxonQuotKind .type == .type)
  itBool "Ixon.QuotKind.ctor" (roundtripIxonQuotKind .ctor == .ctor)
  itBool "Ixon.QuotKind.lift" (roundtripIxonQuotKind .lift == .lift)
  itBool "Ixon.QuotKind.ind" (roundtripIxonQuotKind .ind == .ind)

def ixonUnivTests : LSpec.Spec := do
  itBool "Ixon.Univ.zero" (roundtripIxonUniv .zero == .zero)
  itBool "Ixon.Univ.var 0" (roundtripIxonUniv (.var 0) == .var 0)
  itBool "Ixon.Univ.var 42" (roundtripIxonUniv (.var 42) == .var 42)
  itBool "Ixon.Univ.succ zero" (roundtripIxonUniv (.succ .zero) == .succ .zero)
  itBool "Ixon.Univ.max" (roundtripIxonUniv (.max .zero (.var 1)) == .max .zero (.var 1))
  itBool "Ixon.Univ.imax" (roundtripIxonUniv (.imax (.var 0) .zero) == .imax (.var 0) .zero)

def ixonExprTests : LSpec.Spec := do
  itBool "Ixon.Expr.sort" (roundtripIxonExpr (.sort 0) == .sort 0)
  itBool "Ixon.Expr.var" (roundtripIxonExpr (.var 5) == .var 5)
  itBool "Ixon.Expr.ref" (roundtripIxonExpr (.ref 1 #[0, 1]) == .ref 1 #[0, 1])
  itBool "Ixon.Expr.recur" (roundtripIxonExpr (.recur 2 #[]) == .recur 2 #[])
  itBool "Ixon.Expr.str" (roundtripIxonExpr (.str 3) == .str 3)
  itBool "Ixon.Expr.nat" (roundtripIxonExpr (.nat 42) == .nat 42)
  itBool "Ixon.Expr.share" (roundtripIxonExpr (.share 0) == .share 0)
  itBool "Ixon.Expr.app" (roundtripIxonExpr (.app (.var 0) (.var 1)) == .app (.var 0) (.var 1))
  itBool "Ixon.Expr.lam" (roundtripIxonExpr (.lam (.sort 0) (.var 0)) == .lam (.sort 0) (.var 0))
  itBool "Ixon.Expr.all" (roundtripIxonExpr (.all (.sort 0) (.var 0)) == .all (.sort 0) (.var 0))
  itBool "Ixon.Expr.letE" (roundtripIxonExpr (.leanLet true (.sort 0) (.var 0) (.var 1)) == .leanLet true (.sort 0) (.var 0) (.var 1))
  itBool "Ixon.Expr.letE unique" (roundtripIxonExpr (.letE false (.value .unique) (.sort 0) (.var 0) (.var 1)) ==
    .letE false (.value .unique) (.sort 0) (.var 0) (.var 1))
  itBool "Ixon.Expr.letE borrow" (roundtripIxonExpr (.letE true .borrow (.sort 0) (.var 0) (.var 1)) ==
    .letE true .borrow (.sort 0) (.var 0) (.var 1))
  itBool "Ixon.Expr.prj" (roundtripIxonExpr (.prj 0 1 (.var 0)) == .prj 0 1 (.var 0))

/-! ## Metadata Unit Tests -/

def exprMetaDataTests : LSpec.Spec := do
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let _kvmap : KVMap := #[(testAddr, DataValue.ofBool true)]
  itBool "ExprMetaData.leaf" (roundtripIxonExprMetaData .leaf == .leaf)
  itBool "ExprMetaData.app" (roundtripIxonExprMetaData (.app 0 1) == .app 0 1)
  itBool "ExprMetaData.ref" (roundtripIxonExprMetaData (.ref testAddr) == .ref testAddr)
  itBool "ExprMetaData.prj" (roundtripIxonExprMetaData (.prj testAddr 5) == .prj testAddr 5)
  itBool "ExprMetaData.letBinder" (roundtripIxonExprMetaData (.letBinder testAddr 0 1 2) == .letBinder testAddr 0 1 2)
  itBool "ExprMetaData.mdata empty" (roundtripIxonExprMetaData (.mdata #[] 0) == .mdata #[] 0)
  itBool "ExprMetaData.mdata with kvmap" (roundtripIxonExprMetaData (.mdata #[_kvmap] 3) == .mdata #[_kvmap] 3)
  itBool "ExprMetaData.binder default" (roundtripIxonExprMetaData (.binder testAddr .default 0 1) == .binder testAddr .default 0 1)
  itBool "ExprMetaData.binder implicit" (roundtripIxonExprMetaData (.binder testAddr .implicit 2 3) == .binder testAddr .implicit 2 3)
  itBool "ExprMetaData.binder strictImplicit" (roundtripIxonExprMetaData (.binder testAddr .strictImplicit 0 0) == .binder testAddr .strictImplicit 0 0)
  itBool "ExprMetaData.binder instImplicit" (roundtripIxonExprMetaData (.binder testAddr .instImplicit 0 0) == .binder testAddr .instImplicit 0 0)

def exprMetaArenaTests : LSpec.Spec := do
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let emptyArena : ExprMetaArena := {}
  let singleLeaf : ExprMetaArena := { nodes := #[.leaf] }
  let smallArena : ExprMetaArena := { nodes := #[.leaf, .app 0 0, .ref testAddr] }
  let mixedArena : ExprMetaArena := { nodes := #[
    .leaf, .ref testAddr, .app 0 0, .binder testAddr .default 0 1,
    .letBinder testAddr 0 1 2, .prj testAddr 0, .mdata #[] 0
  ] }
  itBool "ExprMetaArena empty" (roundtripIxonExprMetaArena emptyArena == emptyArena)
  itBool "ExprMetaArena single leaf" (roundtripIxonExprMetaArena singleLeaf == singleLeaf)
  itBool "ExprMetaArena small" (roundtripIxonExprMetaArena smallArena == smallArena)
  itBool "ExprMetaArena mixed" (roundtripIxonExprMetaArena mixedArena == mixedArena)

def constantMetaTests : LSpec.Spec := do
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let emptyArena : ExprMetaArena := {}
  let smallArena : ExprMetaArena := { nodes := #[.leaf, .app 0 0, .ref testAddr] }
  -- An arena with an mdata node over a reference (the shape of a retired
  -- decompile record's metadata).
  let recordArena : ExprMetaArena := { nodes := #[
    .ref testAddr,
    .mdata #[#[(testAddr, .ofBool true)]] 0
  ] }
  let rt (cm : ConstantMeta) : Bool := roundtripIxonConstantMeta cm == cm
  itBool "ConstantMeta.empty" (rt .empty)
  itBool "ConstantMeta.defn" (rt (.new
    (.defn testAddr #[testAddr] #[] #[] smallArena 0 1)))
  itBool "ConstantMeta.axio" (rt (.new (.axio testAddr #[] emptyArena 0)))
  itBool "ConstantMeta.ctor" (rt (.new
    (.ctor testAddr #[] testAddr smallArena 2)))
  itBool "ConstantMeta.recr" (rt (.new
    (.recr testAddr #[] #[] #[] #[] smallArena 0 #[1, 2])))
  itBool "ConstantMeta.muts auxLayout none" (rt (.new
    (.muts #[#[testAddr]] none)))
  -- `evaporated` fixtures spell the canonical one-flag-per-perm-entry
  -- form the compiler materializes (the Rust FFI decode expands the
  -- `#[]` construction default to that shape).
  itBool "ConstantMeta.muts auxLayout some" (rt (.new
    (.muts #[#[testAddr]] (some ⟨#[1, 0], #[2, 3], #[0, 0]⟩))))
  itBool "ConstantMeta.muts auxLayout evaporated" (rt (.new
    (.muts #[#[testAddr]] (some ⟨#[1, 0], #[2, 3], #[0, 1]⟩))))
  itBool "ConstantMeta mdata arena" (rt (.new
    (.defn testAddr #[] #[] #[] recordArena 0 1)))
  itBool "ConstantMeta extension tables" (rt
    { info := .defn testAddr #[] #[] #[] recordArena 0 1,
      metaSharing := #[.app (.share 0) (.var 3), .sort 1],
      metaRefs := #[testAddr],
      metaUnivs := #[.succ (.var 0), .zero],
      univPatches := #[⟨0, #[1]⟩, ⟨7, #[2, 0, 5]⟩] })

/-! ## Cross-implementation serialization comparison FFI declarations -/

@[extern "rs_eq_univ_serialization"]
opaque rsEqUnivSerialization : @& Univ → @& ByteArray → Bool

@[extern "rs_eq_expr_serialization"]
opaque rsEqExprSerialization : @& Expr → @& ByteArray → Bool

@[extern "rs_eq_constant_serialization"]
opaque rsEqConstantSerialization : @& Constant → @& ByteArray → Bool

/-- Whether Rust reads the bytes as one canonical record (`Constant::get`, the
same bytes again, `Constant::binders_canonical`). -/
@[extern "rs_constant_canonical"]
opaque rsConstantCanonical : @& ByteArray → Bool

@[extern "rs_eq_env_serialization"]
opaque rsEqEnvSerialization : @& RawEnv → @& ByteArray → Bool

/-! ## RawEnv roundtrip FFI -/

@[extern "rs_roundtrip_raw_env"]
opaque roundtripRawEnv : @& RawEnv → RawEnv

/-- Compare RawEnv with content-aware comparison.
    Checks array sizes and content matching by Address. -/
def rawEnvEq (a b : RawEnv) : Bool :=
  a.roleBinding == b.roleBinding &&
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

def rawEnvTests : LSpec.Spec := do
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
  itBool "RawEnv empty" (rawEnvEq (roundtripRawEnv empty) empty)
  itBool "RawEnv with data" (rawEnvEq (roundtripRawEnv withData) withData)

/-! ## Env diff FFI (`rs_diff_envs`)

The classification logic is covered by Rust unit tests
(`crates/ixon/src/diff.rs`); these tests pin the FFI marshaling — a
constructor-slot swap would surface as wrong-category contents. -/

def envDiffTests : LSpec.Spec := do
  let fooName := Ix.Name.mkStr Ix.Name.mkAnon "foo"
  let barName := Ix.Name.mkStr Ix.Name.mkAnon "bar"
  -- `.var` exprs only: classification resolves table indices, so a
  -- `.sort 0` over an empty univs table would be a (correctly) rejected
  -- malformed constant.
  let mkConst (value : Expr) : Constant :=
    { info := .defn { kind := .defn, safety := .safe, lvls := 0,
                      typ := .var 3, value }
      sharing := #[], refs := #[], univs := #[] }
  -- Hints live in `env.anonHints`, keyed by constant address; the
  -- writer serializes that map as the hints section.
  let mkEnv (c : Constant) (h : Lean.ReducibilityHints) : Env := Id.run do
    let addr := Address.blake3 (serConstant c)
    let mut env : Env := {}
    env := env.storeConst addr c
    env := { env with names := RawEnv.addNameComponents env.names fooName }
    env := env.registerName fooName
      { addr, constMeta := .new (.defn fooName.getHash #[] #[] #[] {} 0 0) }
    env := { env with anonHints := env.anonHints.insert addr h }
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
    (Ixon.rsDiffEnvs (serEnv! a) (serEnv! b) compareMeta).toOption
  it "EnvDiff: CLI exit codes" do
    let dir ← IO.FS.createTempDir
    try
      let pa := dir / "a.ixe"
      let pb := dir / "b.ixe"
      IO.FS.writeBinFile pa (serEnv! envBase)
      IO.FS.writeBinFile pb (serEnv! envValueChanged)
      let (sameOut, sameCode) ← IO.FS.withIsolatedStreams
        (diffCmd.validate [pa.toString, pa.toString, "--meta"])
      let (_, differCode) ← IO.FS.withIsolatedStreams
        (diffCmd.validate [pa.toString, pb.toString, "--anon"])
      expect (sameCode == 0 && sameOut.contains "identical" && differCode == 1)
        s!"CLI exits {sameCode}/{differCode}"
    finally
      IO.FS.removeDirAll dir
  itBool "EnvDiff: self-diff empty (anon)"
    ((runDiff envBase envBase).any (·.isEmpty))
  itBool "EnvDiff: self-diff empty (meta)"
    ((runDiff envBase envBase true).any (·.isEmpty))
  itBool "EnvDiff: stats populated"
    ((runDiff envBase envBase).any fun d =>
      d.statsA.consts == 1 && d.statsA.named == 1 && d.statsB == d.statsA)
  itBool "EnvDiff: added name"
    ((runDiff envBase envExtra).any fun d =>
      d.namedAdded == #[("bar", addrB)] && d.constsOnlyB == #[addrB]
      && d.namedRemoved.isEmpty && d.namedChanged.isEmpty)
  itBool "EnvDiff: removed name"
    ((runDiff envExtra envBase).any fun d =>
      d.namedRemoved == #[("bar", addrB)] && d.constsOnlyA == #[addrB])
  itBool "EnvDiff: value change classified"
    ((runDiff envBase envValueChanged).any fun d =>
      d.namedChanged.size == 1 &&
      (d.namedChanged[0]!).name == "foo" &&
      (d.namedChanged[0]!).oldAddr == addrA &&
      (d.namedChanged[0]!).newAddr == addrB &&
      (d.namedChanged[0]!).oldKind == "defn" &&
      (d.namedChanged[0]!).newKind == "defn" &&
      (d.namedChanged[0]!).fields == #["value"] &&
      (d.namedChanged[0]!).metaFields.isEmpty &&
      (d.namedChanged[0]!).rippled == false)
  -- A dependent whose only change is its ref re-addressing must marshal
  -- `rippled == true` (pins the num_8 scalar slot against layout swaps).
  itBool "EnvDiff: ripple verdict marshals"
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
       (d.namedChanged.find? (·.name == "bar")).any (·.rippled == true))
  -- Hints live only in the env-level hints section, so a hint tweak
  -- is a pure `hintsChanged` row — no metadata difference in either
  -- mode (the named entries are identical).
  itBool "EnvDiff: hint change visible in anon mode"
    ((runDiff envBase envHintChanged).any fun d =>
      d.hintsChanged == #[(addrA, "regular(5)", "regular(6)")]
      && d.namedMetaOnly.isEmpty && d.namedChanged.isEmpty)
  itBool "EnvDiff: hint change is not a metadata change"
    ((runDiff envBase envHintChanged true).any fun d =>
      d.hintsChanged.size == 1 && d.namedMetaOnly.isEmpty
      && d.namedChanged.isEmpty)
  itBool "EnvDiff: main change"
    ((runDiff { envBase with main := some addrA } envBase).any fun d =>
      d.mainChanged == some (some addrA, none))
  itBool "EnvDiff: assumptions delta"
    (let p := Address.blake3 (ByteArray.mk #[1])
     let q := Address.blake3 (ByteArray.mk #[2])
     let r := Address.blake3 (ByteArray.mk #[3])
     let a := { envBase with
       assumptions := ({} : Std.HashSet Address).insert p |>.insert q }
     let b := { envBase with
       assumptions := ({} : Std.HashSet Address).insert q |>.insert r }
     (runDiff a b).any fun d =>
       d.assumptionsAdded == #[r] && d.assumptionsRemoved == #[p])
  -- The mmap file-path entry must agree with the bytes-based one, and
  -- the byte-equality fast path must distinguish same vs different.
  it "EnvDiff: file-based diff matches bytes-based" do
    let dir ← IO.FS.createTempDir
    try
      let pa := dir / "a.ixe"
      let pb := dir / "b.ixe"
      let bytesA := serEnv! envBase
      let bytesB := serEnv! envValueChanged
      IO.FS.writeBinFile pa bytesA
      IO.FS.writeBinFile pb bytesB
      let eqSame ← Ixon.rsIxeFilesEqual pa.toString pa.toString
      let eqDiff ← Ixon.rsIxeFilesEqual pa.toString pb.toString
      let dFiles ← Ixon.rsDiffEnvFiles pa.toString pb.toString false
      let dBytes ← expectOk (Ixon.rsDiffEnvs bytesA bytesB false)
      expect (eqSame && !eqDiff && dFiles == dBytes) "file/bytes reports disagree"
    finally
      IO.FS.removeDirAll dir

/-- Self-diff over the pure-Lean writer's bytes must be empty in both
    modes (also exercises report marshaling on arbitrary inputs). -/
def selfDiffEmpty (compareMeta : Bool) (env : RawEnv) : Bool :=
  match Ixon.serEnv env.toEnv with
  | .error _ => false
  | .ok bytes =>
    match Ixon.rsDiffEnvs bytes bytes compareMeta with
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
    IO.FS.writeBinFile src (serEnv! env)
    Ixon.rsPackEnv src.toString mainName assume out.toString anon false
    let bytes ← IO.FS.readBinFile out
    pure (Ixon.rsDeEnv bytes)
  catch e =>
    pure (.error e.toString)
  IO.FS.removeDirAll dir
  return result

/-- IO test asserting on a successfully packed bundle. -/
private def packTest (descr : String) (act : IO (Except String Env))
    (check : Env → Bool) : Spec :=
  it descr do
    let bundle ← expectOk (← act)
    expect (check bundle) "bundle assertion failed"

/-- IO test asserting the pack call fails. -/
private def packErrTest (descr : String) (act : IO (Except String Env)) :
    Spec :=
  it descr do
    match ← act with
    | .ok _ => fail "expected pack to fail"
    | .error _ => pure ()

def envPackTests : LSpec.Spec := do
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
      && b.assumptions.isEmpty)
  it "EnvPack: bundle is a removals-only subset under diff" do
    let b ← expectOk (← packFixture src "bar" #[])
    let d ← expectOk (Ixon.rsDiffEnvs (serEnv! src) (serEnv! b))
    let ok := d.mainChanged == some (none, some barAddr)
      && d.namedRemoved.size == 1
      && d.namedAdded.isEmpty && d.namedChanged.isEmpty
      && d.constsOnlyB.isEmpty && d.blobsOnlyB.isEmpty
    let msg := s!"mainOk={d.mainChanged == some (none, some barAddr)} \
      removed={d.namedRemoved.map (·.1)} \
      added={d.namedAdded.map (·.1)} \
      changed={d.namedChanged.map (·.name)} \
      constsOnlyB={d.constsOnlyB.size} blobsOnlyB={d.blobsOnlyB.size}"
    expect ok msg
  packTest "EnvPack: assume cut (by name) records assumption"
    (packFixture src "bar" #["foo"]) (fun b =>
      b.main == some barAddr
      && (b.getAddr? fooName).isNone
      && b.consts.size == 1
      && b.assumptions.size == 1
      && b.assumptions.contains fooAddr)
  packTest "EnvPack: assume cut (by hex address) records assumption"
    (packFixture src "bar" #[toString fooAddr]) (fun b =>
      b.consts.size == 1 && b.assumptions.contains fooAddr)
  packTest "EnvPack: anon bundle has no metadata, keeps the value pin"
    (packFixture src "bar" #[] (anon := true)) (fun b =>
      b.main == some barAddr
      && b.named.isEmpty
      -- The writer always emits the anonymous name as §4 entry 0.
      && b.names.size <= 1
      && b.consts.size == 2
      && (b.getAddr? barName).isNone)
  packErrTest "EnvPack: unknown root name errors"
    (packFixture src "nope" #[])
  packErrTest "EnvPack: main cannot be assumed"
    (packFixture src "bar" #["bar"])

/-! ## Test Suite -/

set_option compiler.extract_closed false in
def suiteWith (cfg : LSpec.Prop.PropertyConfig := {}) : Spec := do
  -- Ixon type unit tests
  ixonDefKindTests
  ixonDefinitionSafetyTests
  ixonQuotKindTests
  ixonUnivTests
  ixonExprTests
  exprMetaDataTests
  exprMetaArenaTests
  constantMetaTests
  rawEnvTests
  -- Ixon property tests - recursive & composite types
  -- (finite enums `DefKind`, `DefinitionSafety`, `QuotKind` are exhaustively unit-tested above)
  propWith "Ixon.Univ roundtrip" cfg fun (x : Univ) => roundtripIxonUniv x == x
  propWith "Ixon.Expr roundtrip" cfg fun (x : Expr) => roundtripIxonExpr x == x
  propWith "Ixon.Definition roundtrip" cfg fun (x : Definition) => roundtripIxonDefinition x == x
  propWith "Ixon.RecursorRule roundtrip" cfg fun (x : RecursorRule) => roundtripIxonRecursorRule x == x
  propWith "Ixon.Recursor roundtrip" cfg fun (x : Recursor) => roundtripIxonRecursor x == x
  propWith "Ixon.Axiom roundtrip" cfg fun (x : Axiom) => roundtripIxonAxiom x == x
  propWith "Ixon.Quotient roundtrip" cfg fun (x : Quotient) => roundtripIxonQuotient x == x
  propWith "Ixon.Constructor roundtrip" cfg fun (x : Constructor) => roundtripIxonConstructor x == x
  propWith "Ixon.Inductive roundtrip" cfg fun (x : Inductive) => roundtripIxonInductive x == x
  propWith "Ixon.InductiveProj roundtrip" cfg fun (x : InductiveProj) => roundtripIxonInductiveProj x == x
  propWith "Ixon.ConstructorProj roundtrip" cfg fun (x : ConstructorProj) => roundtripIxonConstructorProj x == x
  propWith "Ixon.RecursorProj roundtrip" cfg fun (x : RecursorProj) => roundtripIxonRecursorProj x == x
  propWith "Ixon.DefinitionProj roundtrip" cfg fun (x : DefinitionProj) => roundtripIxonDefinitionProj x == x
  propWith "Ixon.MutConst roundtrip" cfg fun (x : MutConst) => roundtripIxonMutConst x == x
  propWith "Ixon.ConstantInfo roundtrip" cfg fun (x : ConstantInfo) => roundtripIxonConstantInfo x == x
  propWith "Ixon.Constant roundtrip" cfg fun (x : Constant) => roundtripIxonConstant x == x
  propWith "Ixon.DataValue roundtrip" cfg fun (x : DataValue) => roundtripIxonDataValue x == x
  propWith "Ixon.Comm roundtrip" cfg fun (x : Comm) => roundtripIxonComm x == x
  -- Metadata types (arena-based)
  propWith "Ixon.ExprMetaData roundtrip" cfg fun (x : ExprMetaData) => roundtripIxonExprMetaData x == x
  propWith "Ixon.ConstantMeta roundtrip" cfg fun (x : ConstantMeta) => roundtripIxonConstantMeta x == x
  propWith "Ixon.Named roundtrip" cfg fun (x : Named) => roundtripIxonNamed x == x
  ---- RawEnv roundtrip
  propWith "Ixon.RawEnv roundtrip" cfg fun (env : RawEnv) => rawEnvEq (roundtripRawEnv env) env
  ---- Env diff
  envDiffTests
  propWith "Ixon.EnvDiff self-diff empty (anon)" cfg fun (env : RawEnv) =>
    selfDiffEmpty false env
  propWith "Ixon.EnvDiff self-diff empty (meta)" cfg fun (env : RawEnv) =>
    selfDiffEmpty true env
  ---- Env pack
  envPackTests

def suite : Spec := suiteWith {}

end Tests.FFI.Ixon

end
