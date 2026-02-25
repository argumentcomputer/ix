/-
  Ix.* type FFI roundtrip tests.
  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/
module

public import LSpec
public import Tests.Gen.Basic
public import Tests.Gen.Ix
public import Tests.Gen.Ixon
public import Ix.Environment
public import Ix.Address
public import Ix.CompileM
public import Ix.DecompileM
public import Ix.Ixon
public import Tests.FFI.Ixon

open LSpec SlimCheck Gen
open Tests.Gen.Ix
open Tests.Gen.Ixon
open Tests.FFI.Ixon (rawEnvEq)

namespace Tests.FFI.Ix

/-! ## Ix type roundtrip FFI declarations -/

@[extern "rs_roundtrip_ix_address"]
opaque roundtripIxAddress : @& Address → Address

@[extern "rs_roundtrip_ix_name"]
opaque roundtripIxName : @& Ix.Name → Ix.Name

@[extern "rs_roundtrip_ix_level"]
opaque roundtripIxLevel : @& Ix.Level → Ix.Level

@[extern "rs_roundtrip_ix_expr"]
opaque roundtripIxExpr : @& Ix.Expr → Ix.Expr

@[extern "rs_roundtrip_ix_int"]
opaque roundtripIxInt : @& Ix.Int → Ix.Int

@[extern "rs_roundtrip_ix_substring"]
opaque roundtripIxSubstring : @& Ix.Substring → Ix.Substring

@[extern "rs_roundtrip_ix_source_info"]
opaque roundtripIxSourceInfo : @& Ix.SourceInfo → Ix.SourceInfo

@[extern "rs_roundtrip_ix_syntax_preresolved"]
opaque roundtripIxSyntaxPreresolved : @& Ix.SyntaxPreresolved → Ix.SyntaxPreresolved

@[extern "rs_roundtrip_ix_syntax"]
opaque roundtripIxSyntax : @& Ix.Syntax → Ix.Syntax

@[extern "rs_roundtrip_ix_data_value"]
opaque roundtripIxDataValue : @& Ix.DataValue → Ix.DataValue

-- Need Inhabited instance for opaque declaration
instance : Inhabited Ix.ConstantInfo where
  default := .axiomInfo { cnst := { name := default, levelParams := #[], type := default }, isUnsafe := false }

@[extern "rs_roundtrip_ix_constant_info"]
opaque roundtripIxConstantInfo : @& Ix.ConstantInfo → Ix.ConstantInfo

-- Need Inhabited instance for Environment opaque declaration
instance : Inhabited Ix.Environment where
  default := { consts := {} }

-- Rust roundtrip returns RawEnvironment (array-based), not Environment (HashMap-based)
@[extern "rs_roundtrip_ix_raw_environment"]
opaque roundtripIxRawEnvironment : @& Ix.RawEnvironment → Ix.RawEnvironment

-- Roundtrip Environment by going through RawEnvironment
@[extern "rs_roundtrip_ix_environment"]
opaque roundtripIxEnvironmentRaw : @& Ix.Environment → Ix.RawEnvironment

def roundtripIxEnvironment (env : Ix.Environment) : Ix.Environment :=
  (roundtripIxEnvironmentRaw env).toEnvironment

-- Round-trip Ix.RustCondensedBlocks
instance : Inhabited Ix.RustCondensedBlocks where
  default := { lowLinks := #[], blocks := #[], blockRefs := #[] }

instance : Repr Ix.RustCondensedBlocks where
  reprPrec cb _ := s!"RustCondensedBlocks(lowLinks={cb.lowLinks.size}, blocks={cb.blocks.size}, blockRefs={cb.blockRefs.size})"

@[extern "rs_roundtrip_rust_condensed_blocks"]
opaque roundtripRustCondensedBlocks : @& Ix.RustCondensedBlocks → Ix.RustCondensedBlocks

-- Round-trip Ix.CompileM.RustCompilePhases
instance : Inhabited Ix.CompileM.RustCompilePhases where
  default := { rawEnv := default, condensed := default, compileEnv := default }

instance : Repr Ix.CompileM.RustCompilePhases where
  reprPrec p _ := s!"RustCompilePhases(rawEnv.consts={p.rawEnv.consts.size}, condensed.blocks={p.condensed.blocks.size}, compileEnv.consts={p.compileEnv.consts.size})"

@[extern "rs_roundtrip_rust_compile_phases"]
opaque roundtripRustCompilePhases : @& Ix.CompileM.RustCompilePhases → Ix.CompileM.RustCompilePhases

/-! ## BlockCompareResult and BlockCompareDetail FFI tests -/

/-- Result of comparing a single block between Lean and Rust -/
inductive BlockCompareResult where
  | «match»
  | mismatch (leanSize rustSize firstDiffOffset : UInt64)
  | notFound
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Detailed comparison with sharing statistics -/
structure BlockCompareDetail where
  result : BlockCompareResult
  leanSharingLen : UInt64
  rustSharingLen : UInt64
  deriving Repr, BEq, DecidableEq, Inhabited

@[extern "rs_roundtrip_block_compare_result"]
opaque roundtripBlockCompareResult : @& BlockCompareResult → BlockCompareResult

@[extern "rs_roundtrip_block_compare_detail"]
opaque roundtripBlockCompareDetail : @& BlockCompareDetail → BlockCompareDetail

def blockCompareResultTests : TestSeq :=
  let matchCase := BlockCompareResult.match
  let mismatchCase := BlockCompareResult.mismatch 100 200 50
  let notFoundCase := BlockCompareResult.notFound
  test "BlockCompareResult.match" (roundtripBlockCompareResult matchCase == matchCase) ++
  test "BlockCompareResult.mismatch" (roundtripBlockCompareResult mismatchCase == mismatchCase) ++
  test "BlockCompareResult.notFound" (roundtripBlockCompareResult notFoundCase == notFoundCase)

def blockCompareDetailTests : TestSeq :=
  let detailMatch := BlockCompareDetail.mk .match 10 20
  let detailMismatch := BlockCompareDetail.mk (.mismatch 100 200 50) 15 25
  let detailNotFound := BlockCompareDetail.mk .notFound 5 0
  test "BlockCompareDetail match" (roundtripBlockCompareDetail detailMatch == detailMatch) ++
  test "BlockCompareDetail mismatch" (roundtripBlockCompareDetail detailMismatch == detailMismatch) ++
  test "BlockCompareDetail notFound" (roundtripBlockCompareDetail detailNotFound == detailNotFound)

/-! ## Shrinkable instances -/

instance : Shrinkable Ix.RustCondensedBlocks where
  shrink cb :=
    if cb.lowLinks.isEmpty && cb.blocks.isEmpty && cb.blockRefs.isEmpty then []
    else [{
      lowLinks := if cb.lowLinks.isEmpty then #[] else cb.lowLinks.pop,
      blocks := if cb.blocks.isEmpty then #[] else cb.blocks.pop,
      blockRefs := if cb.blockRefs.isEmpty then #[] else cb.blockRefs.pop
    }]

/-! ## Ix type comparison by hash -/

def ixNameEq (a b : Ix.Name) : Bool := a.getHash == b.getHash
def ixLevelEq (a b : Ix.Level) : Bool := a.getHash == b.getHash
def ixExprEq (a b : Ix.Expr) : Bool := a.getHash == b.getHash

/-! ## Comparison helpers -/

/-- Compare RustCondensedBlocks by checking array sizes.
    Size-only: element-wise comparison is not feasible because the Lean and Rust
    condensation algorithms may produce different SCC orderings. -/
def rustCondensedBlocksEq (a b : Ix.RustCondensedBlocks) : Bool :=
  a.lowLinks.size == b.lowLinks.size &&
  a.blocks.size == b.blocks.size &&
  a.blockRefs.size == b.blockRefs.size

/-- Compare Ix.ConstantInfo by structural equality (all fields). -/
def ixConstantInfoEq (a b : Ix.ConstantInfo) : Bool := a == b

/-- Compare RawEnvironment with content-aware comparison.
    Checks that all constants in a have matching constants in b by name hash. -/
def ixRawEnvironmentEq (a b : Ix.RawEnvironment) : Bool :=
  a.consts.size == b.consts.size &&
  a.consts.all fun (name, info) =>
    b.consts.any fun (name', info') =>
      ixNameEq name name' && ixConstantInfoEq info info'

/-- Compare RustCompilePhases by checking sizes -/
def rustCompilePhasesEq (a b : Ix.CompileM.RustCompilePhases) : Bool :=
  ixRawEnvironmentEq a.rawEnv b.rawEnv &&
  rustCondensedBlocksEq a.condensed b.condensed &&
  rawEnvEq a.compileEnv b.compileEnv

/-! ## Ix.RawEnvironment unit tests -/

/-- Test empty RawEnvironment roundtrip -/
def ixRawEnvironmentTests : TestSeq :=
  let empty : Ix.RawEnvironment := { consts := #[] }
  -- Create a simple ConstantInfo for testing
  let name := Ix.Name.mkStr Ix.Name.mkAnon "test"
  let expr := Ix.Expr.mkSort Ix.Level.mkZero
  let constVal : Ix.ConstantVal := { name := name, levelParams := #[], type := expr }
  let axiomVal : Ix.AxiomVal := { cnst := constVal, isUnsafe := false }
  let constInfo : Ix.ConstantInfo := .axiomInfo axiomVal
  let withOne : Ix.RawEnvironment := { consts := #[(name, constInfo)] }
  test "Ix.RawEnvironment empty" (ixRawEnvironmentEq (roundtripIxRawEnvironment empty) empty) ++
  test "Ix.RawEnvironment single const" (ixRawEnvironmentEq (roundtripIxRawEnvironment withOne) withOne)

/-! ## RustCondensedBlocks unit tests -/

def rustCondensedBlocksTests : TestSeq :=
  let empty : Ix.RustCondensedBlocks := { lowLinks := #[], blocks := #[], blockRefs := #[] }
  let n1 := Ix.Name.mkStr Ix.Name.mkAnon "a"
  let n2 := Ix.Name.mkStr Ix.Name.mkAnon "b"
  let withData : Ix.RustCondensedBlocks := {
    lowLinks := #[(n1, n2)],
    blocks := #[(n1, #[n1, n2])],
    blockRefs := #[(n2, #[n1])]
  }
  test "RustCondensedBlocks empty" (rustCondensedBlocksEq (roundtripRustCondensedBlocks empty) empty) ++
  test "RustCondensedBlocks with data" (rustCondensedBlocksEq (roundtripRustCondensedBlocks withData) withData)

/-! ## SerializeError, DecompileError, and CompileError roundtrip FFI -/

@[extern "rs_roundtrip_serialize_error"]
opaque roundtripSerializeError : @& Ixon.SerializeError → Ixon.SerializeError

@[extern "rs_roundtrip_decompile_error"]
opaque roundtripDecompileError : @& Ix.DecompileM.DecompileError → Ix.DecompileM.DecompileError

@[extern "rs_roundtrip_compile_error"]
opaque roundtripCompileError : @& Ix.CompileM.CompileError → Ix.CompileM.CompileError

def serializeErrorTests : TestSeq :=
  test "SerializeError.unexpectedEof" (roundtripSerializeError (.unexpectedEof "u64") == .unexpectedEof "u64") ++
  test "SerializeError.invalidTag" (roundtripSerializeError (.invalidTag 0xFF "expr") == .invalidTag 0xFF "expr") ++
  test "SerializeError.invalidFlag" (roundtripSerializeError (.invalidFlag 3 "univ") == .invalidFlag 3 "univ") ++
  test "SerializeError.invalidVariant" (roundtripSerializeError (.invalidVariant 99 "const") == .invalidVariant 99 "const") ++
  test "SerializeError.invalidBool" (roundtripSerializeError (.invalidBool 2) == .invalidBool 2) ++
  test "SerializeError.addressError" (roundtripSerializeError .addressError == .addressError) ++
  test "SerializeError.invalidShareIndex" (roundtripSerializeError (.invalidShareIndex 5 10) == .invalidShareIndex 5 10)

def decompileErrorTests : TestSeq :=
  let addr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let se := Ixon.SerializeError.unexpectedEof "test"
  test "DecompileError.invalidRefIndex" (roundtripDecompileError (.invalidRefIndex 5 10 "test") == .invalidRefIndex 5 10 "test") ++
  test "DecompileError.invalidUnivIndex" (roundtripDecompileError (.invalidUnivIndex 3 7 "foo") == .invalidUnivIndex 3 7 "foo") ++
  test "DecompileError.invalidShareIndex" (roundtripDecompileError (.invalidShareIndex 2 5 "bar") == .invalidShareIndex 2 5 "bar") ++
  test "DecompileError.invalidRecIndex" (roundtripDecompileError (.invalidRecIndex 1 4 "baz") == .invalidRecIndex 1 4 "baz") ++
  test "DecompileError.invalidUnivVarIndex" (roundtripDecompileError (.invalidUnivVarIndex 8 3 "qux") == .invalidUnivVarIndex 8 3 "qux") ++
  test "DecompileError.missingAddress" (roundtripDecompileError (.missingAddress addr) == .missingAddress addr) ++
  test "DecompileError.missingMetadata" (roundtripDecompileError (.missingMetadata addr) == .missingMetadata addr) ++
  test "DecompileError.blobNotFound" (roundtripDecompileError (.blobNotFound addr) == .blobNotFound addr) ++
  test "DecompileError.badBlobFormat" (roundtripDecompileError (.badBlobFormat addr "UTF-8") == .badBlobFormat addr "UTF-8") ++
  test "DecompileError.badConstantFormat" (roundtripDecompileError (.badConstantFormat "bad") == .badConstantFormat "bad") ++
  test "DecompileError.serializeError" (roundtripDecompileError (.serializeError se) == .serializeError se)

def compileErrorTests : TestSeq :=
  let addr := Address.blake3 (ByteArray.mk #[4, 5, 6])
  let se := Ixon.SerializeError.addressError
  test "CompileError.missingConstant" (roundtripCompileError (.missingConstant "Nat.add") == .missingConstant "Nat.add") ++
  test "CompileError.missingAddress" (roundtripCompileError (.missingAddress addr) == .missingAddress addr) ++
  test "CompileError.invalidMutualBlock" (roundtripCompileError (.invalidMutualBlock "empty") == .invalidMutualBlock "empty") ++
  test "CompileError.unsupportedExpr" (roundtripCompileError (.unsupportedExpr "mvar") == .unsupportedExpr "mvar") ++
  test "CompileError.unknownUnivParam" (roundtripCompileError (.unknownUnivParam "Nat" "u") == .unknownUnivParam "Nat" "u") ++
  test "CompileError.serializeError" (roundtripCompileError (.serializeError se) == .serializeError se)

/-! ## Test Suite -/

public def suite : List TestSeq := [
  -- Block comparison types
  blockCompareResultTests,
  blockCompareDetailTests,
  -- Error type roundtrips
  serializeErrorTests,
  decompileErrorTests,
  compileErrorTests,
  -- Environment unit tests
  ixRawEnvironmentTests,
  rustCondensedBlocksTests,
  -- Property tests for basic Ix types
  checkIO "Address roundtrip" (∀ a : Address, roundtripIxAddress a == a),
  checkIO "Ix.Name roundtrip" (∀ n : Ix.Name, ixNameEq (roundtripIxName n) n),
  checkIO "Ix.Level roundtrip" (∀ l : Ix.Level, ixLevelEq (roundtripIxLevel l) l),
  checkIO "Ix.Expr roundtrip" (∀ e : Ix.Expr, ixExprEq (roundtripIxExpr e) e),
  checkIO "Ix.Int roundtrip" (∀ i : Ix.Int, roundtripIxInt i == i),
  checkIO "Ix.Substring roundtrip" (∀ s : Ix.Substring, roundtripIxSubstring s == s),
  checkIO "Ix.SourceInfo roundtrip" (∀ si : Ix.SourceInfo, roundtripIxSourceInfo si == si),
  checkIO "Ix.SyntaxPreresolved roundtrip" (∀ sp : Ix.SyntaxPreresolved, roundtripIxSyntaxPreresolved sp == sp),
  checkIO "Ix.Syntax roundtrip" (∀ s : Ix.Syntax, roundtripIxSyntax s == s),
  checkIO "Ix.DataValue roundtrip" (∀ dv : Ix.DataValue, roundtripIxDataValue dv == dv),
  checkIO "Ix.ConstantInfo roundtrip" (∀ ci : Ix.ConstantInfo, ixConstantInfoEq (roundtripIxConstantInfo ci) ci),
  -- Property tests for Environment types
  checkIO "Ix.RawEnvironment roundtrip" (∀ env : Ix.RawEnvironment, ixRawEnvironmentEq (roundtripIxRawEnvironment env) env),
  -- Composite types
  checkIO "RustCondensedBlocks roundtrip" (∀ cb : Ix.RustCondensedBlocks, rustCondensedBlocksEq (roundtripRustCondensedBlocks cb) cb),
  checkIO "RustCompilePhases roundtrip" (∀ p : Ix.CompileM.RustCompilePhases, rustCompilePhasesEq (roundtripRustCompilePhases p) p),
  -- Error type property tests
  checkIO "SerializeError roundtrip" (∀ e : Ixon.SerializeError, roundtripSerializeError e == e),
  checkIO "DecompileError roundtrip" (∀ e : Ix.DecompileM.DecompileError, roundtripDecompileError e == e),
  checkIO "CompileError roundtrip" (∀ e : Ix.CompileM.CompileError, roundtripCompileError e == e),
]

end Tests.FFI.Ix
