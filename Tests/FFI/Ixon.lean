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
  -- RawEnv roundtrip
  checkIO "Ixon.RawEnv roundtrip" (∀ env : RawEnv, rawEnvEq (roundtripRawEnv env) env),
]

end Tests.FFI.Ixon

end
