//! Ix-specific Lean domain type definitions.
//!
//! Ctor-backed types use `lean_inductive!` which declares the domain type,
//! variant wrappers, layout metadata, and typed accessors in one shot.
//! Types without a ctor layout (simple enums, opaque objects, arenas) use
//! bare `lean_domain_type!`.

use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanOwned, LeanRef};

// =============================================================================
// Types without ctor layouts (simple enums, opaque objects, arenas)
// =============================================================================

lean_ffi::lean_domain_type! {
  // Simple enums (passed as raw unboxed tag values)
  LeanIxBinderInfo;
  LeanIxonDefKind;
  LeanIxonDefinitionSafety;
  LeanIxonQuotKind;

  // Opaque / arena types
  LeanIxRawEnvironment;
  LeanIxEnvironment;
  LeanIxonExprMetaArena;

  // Aiur parameter types (no scalar fields, used opaquely)
  LeanAiurCommitmentParameters;
  LeanAiurFriParameters;
}

// =============================================================================
// Ixon structures (single-constructor, tag 0)
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxonDefinition { num_obj: 2, num_64: 1, num_8: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonRecursorRule { num_obj: 1, num_64: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonRecursor { num_obj: 2, num_64: 5, num_8: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonAxiom { num_obj: 1, num_64: 1, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonQuotient { num_obj: 1, num_64: 1, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonConstructor { num_obj: 1, num_64: 4, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonInductive { num_obj: 2, num_64: 4, num_8: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxonInductiveProj { num_obj: 1, num_64: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonConstructorProj { num_obj: 1, num_64: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonRecursorProj { num_obj: 1, num_64: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonDefinitionProj { num_obj: 1, num_64: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxonNamed { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonComm { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonConstant { num_obj: 4 }
}
lean_ffi::lean_inductive! {
  LeanIxonRawConst { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonRawNamed { num_obj: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxonRawBlob { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonRawComm { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonRawNameEntry { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxonRawEnv { num_obj: 5 }
}

// =============================================================================
// Ixon multi-variant inductives
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxonUniv {
    LeanIxonUnivVar  { tag: 4, num_64: 1 },
    LeanIxonUnivSucc { tag: 1, num_obj: 1 },
    LeanIxonUnivMax  { tag: 2, num_obj: 2 },
    LeanIxonUnivIMax { tag: 3, num_obj: 2 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxonExpr {
    LeanIxonExprSort  { num_64: 1 },
    LeanIxonExprVar   { tag: 1, num_64: 1 },
    LeanIxonExprRef   { tag: 2, num_obj: 1, num_64: 1 },
    LeanIxonExprRec   { tag: 3, num_obj: 1, num_64: 1 },
    LeanIxonExprPrj   { tag: 4, num_obj: 1, num_64: 2 },
    LeanIxonExprStr   { tag: 5, num_64: 1 },
    LeanIxonExprNat   { tag: 6, num_64: 1 },
    LeanIxonExprApp   { tag: 7, num_obj: 2 },
    LeanIxonExprLam   { tag: 8, num_obj: 2 },
    LeanIxonExprAll   { tag: 9, num_obj: 2 },
    LeanIxonExprLet   { tag: 10, num_obj: 3, num_8: 1 },
    LeanIxonExprShare { tag: 11, num_64: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxonExprMetaData {
    LeanIxonExprMetaApp       { tag: 1, num_64: 2 },
    LeanIxonExprMetaBinder    { tag: 2, num_obj: 1, num_64: 2, num_8: 1 },
    LeanIxonExprMetaLetBinder { tag: 3, num_obj: 1, num_64: 3 },
    LeanIxonExprMetaRef       { tag: 4, num_obj: 1 },
    LeanIxonExprMetaPrj       { tag: 5, num_obj: 1, num_64: 1 },
    LeanIxonExprMetaMdata     { tag: 6, num_obj: 1, num_64: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxonConstantMeta {
    LeanIxonConstantMetaDef  { tag: 1, num_obj: 6, num_64: 2 },
    LeanIxonConstantMetaAxio { tag: 2, num_obj: 3, num_64: 1 },
    LeanIxonConstantMetaQuot { tag: 3, num_obj: 3, num_64: 1 },
    LeanIxonConstantMetaIndc { tag: 4, num_obj: 6, num_64: 1 },
    LeanIxonConstantMetaCtor { tag: 5, num_obj: 4, num_64: 1 },
    LeanIxonConstantMetaRec  { tag: 6, num_obj: 7, num_64: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxonDataValue {
    LeanIxonDataValueString { num_obj: 1 },
    LeanIxonDataValueBool   { tag: 1, num_8: 1 },
    LeanIxonDataValueName   { tag: 2, num_obj: 1 },
    LeanIxonDataValueNat    { tag: 3, num_obj: 1 },
    LeanIxonDataValueInt    { tag: 4, num_obj: 1 },
    LeanIxonDataValueSyntax { tag: 5, num_obj: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxonMutConst {
    LeanIxonMutConstDefn { num_obj: 1 },
    LeanIxonMutConstIndc { tag: 1, num_obj: 1 },
    LeanIxonMutConstRecr { tag: 2, num_obj: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxonConstantInfo {
    LeanIxonConstantInfoDefn { num_obj: 1 },
    LeanIxonConstantInfoRecr { tag: 1, num_obj: 1 },
    LeanIxonConstantInfoAxio { tag: 2, num_obj: 1 },
    LeanIxonConstantInfoQuot { tag: 3, num_obj: 1 },
    LeanIxonConstantInfoCPrj { tag: 4, num_obj: 1 },
    LeanIxonConstantInfoRPrj { tag: 5, num_obj: 1 },
    LeanIxonConstantInfoIPrj { tag: 6, num_obj: 1 },
    LeanIxonConstantInfoDPrj { tag: 7, num_obj: 1 },
    LeanIxonConstantInfoMuts { tag: 8, num_obj: 1 },
  }
}

// =============================================================================
// Ix structures (single-constructor, tag 0)
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxConstantVal { num_obj: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxRecursorRule { num_obj: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxTheoremVal { num_obj: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxCondensedBlocks { num_obj: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxCompilePhases { num_obj: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxSubstring { num_obj: 3 }
}

// =============================================================================
// Ix multi-variant inductives
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxName {
    LeanIxNameAnonymous { num_obj: 1 },
    LeanIxNameStr       { tag: 1, num_obj: 3 },
    LeanIxNameNum       { tag: 2, num_obj: 3 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxLevel {
    LeanIxLevelZero  { num_obj: 1 },
    LeanIxLevelSucc  { tag: 1, num_obj: 2 },
    LeanIxLevelMax   { tag: 2, num_obj: 3 },
    LeanIxLevelImax  { tag: 3, num_obj: 3 },
    LeanIxLevelParam { tag: 4, num_obj: 2 },
    LeanIxLevelMvar  { tag: 5, num_obj: 2 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxExpr {
    LeanIxExprBvar    { num_obj: 2 },
    LeanIxExprFvar    { tag: 1, num_obj: 2 },
    LeanIxExprMvar    { tag: 2, num_obj: 2 },
    LeanIxExprSort    { tag: 3, num_obj: 2 },
    LeanIxExprConst   { tag: 4, num_obj: 3 },
    LeanIxExprApp     { tag: 5, num_obj: 3 },
    LeanIxExprLam     { tag: 6, num_obj: 4, num_8: 1 },
    LeanIxExprForallE { tag: 7, num_obj: 4, num_8: 1 },
    LeanIxExprLetE    { tag: 8, num_obj: 5, num_8: 1 },
    LeanIxExprLit     { tag: 9, num_obj: 2 },
    LeanIxExprMdata   { tag: 10, num_obj: 3 },
    LeanIxExprProj    { tag: 11, num_obj: 4 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxConstantInfo {
    LeanIxConstantInfoAxiom  { num_obj: 1 },
    LeanIxConstantInfoDefn   { tag: 1, num_obj: 1 },
    LeanIxConstantInfoThm    { tag: 2, num_obj: 1 },
    LeanIxConstantInfoOpaque { tag: 3, num_obj: 1 },
    LeanIxConstantInfoQuot   { tag: 4, num_obj: 1 },
    LeanIxConstantInfoInduct { tag: 5, num_obj: 1 },
    LeanIxConstantInfoCtor   { tag: 6, num_obj: 1 },
    LeanIxConstantInfoRec    { tag: 7, num_obj: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxReducibilityHints {
    LeanIxReducibilityHintsRegular { tag: 2, num_32: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxLiteral {
    LeanIxLiteralNat { num_obj: 1 },
    LeanIxLiteralStr { tag: 1, num_obj: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxInt {
    LeanIxIntOfNat   { num_obj: 1 },
    LeanIxIntNegSucc { tag: 1, num_obj: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxSourceInfo {
    LeanIxSourceInfoOriginal  { num_obj: 4 },
    LeanIxSourceInfoSynthetic { tag: 1, num_obj: 2, num_8: 1 },
    LeanIxSourceInfoNone      { tag: 2 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxSyntax {
    LeanIxSyntaxMissing {},
    LeanIxSyntaxNode  { tag: 1, num_obj: 3 },
    LeanIxSyntaxAtom  { tag: 2, num_obj: 2 },
    LeanIxSyntaxIdent { tag: 3, num_obj: 4 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxSyntaxPreresolved {
    LeanIxSyntaxPreresolvedA { num_obj: 1 },
    LeanIxSyntaxPreresolvedB { tag: 1, num_obj: 2 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxDataValue {
    LeanIxDataValueString  { num_obj: 1 },
    LeanIxDataValueBool    { tag: 1, num_8: 1 },
    LeanIxDataValueName    { tag: 2, num_obj: 1 },
    LeanIxDataValueNat     { tag: 3, num_obj: 1 },
    LeanIxDataValueInt     { tag: 4, num_obj: 1 },
    LeanIxDataValueSyntax  { tag: 5, num_obj: 1 },
  }
}

// =============================================================================
// Lean kernel inner val types (used in Ix.ConstantInfo decode)
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxAxiomVal { num_obj: 1, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxDefinitionVal { num_obj: 4, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxOpaqueVal { num_obj: 3, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxQuotVal { num_obj: 1, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxInductiveVal { num_obj: 6, num_8: 3 }
}
lean_ffi::lean_inductive! {
  LeanIxConstructorVal { num_obj: 5, num_8: 1 }
}
lean_ffi::lean_inductive! {
  LeanIxRecursorVal { num_obj: 7, num_8: 2 }
}

// =============================================================================
// Aiur types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanAiurToplevel { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanAiurFunction { num_obj: 2, num_8: 2 }
}

// =============================================================================
// Block / comparison types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxBlockCompareResult {
    LeanIxBlockCompareResultMatch    {},
    LeanIxBlockCompareResultMismatch { tag: 1, num_64: 3 },
    LeanIxBlockCompareResultNotFound { tag: 2 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxBlockCompareDetail { num_obj: 1, num_64: 2 }
}
lean_ffi::lean_inductive! {
  LeanIxBlock { num_obj: 2, num_64: 1 }
}

// =============================================================================
// Error types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxSerializeError {
    LeanIxSerializeErrorUnexpectedEof    { num_obj: 1 },
    LeanIxSerializeErrorInvalidTag       { tag: 1, num_obj: 1, num_8: 1 },
    LeanIxSerializeErrorInvalidFlag      { tag: 2, num_obj: 1, num_8: 1 },
    LeanIxSerializeErrorInvalidVariant   { tag: 3, num_obj: 1, num_64: 1 },
    LeanIxSerializeErrorInvalidBool      { tag: 4, num_8: 1 },
    LeanIxSerializeErrorInvalidShareIndex { tag: 6, num_obj: 1, num_64: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxDecompileError {
    LeanIxDecompileErrorRefIndex           { num_obj: 2, num_64: 1 },
    LeanIxDecompileErrorUnivIndex          { tag: 1, num_obj: 2, num_64: 1 },
    LeanIxDecompileErrorShareIndex         { tag: 2, num_obj: 2, num_64: 1 },
    LeanIxDecompileErrorRecIndex           { tag: 3, num_obj: 2, num_64: 1 },
    LeanIxDecompileErrorUnivVarIndex       { tag: 4, num_obj: 2, num_64: 1 },
    LeanIxDecompileErrorMissingAddress     { tag: 5, num_obj: 1 },
    LeanIxDecompileErrorMissingMetadata    { tag: 6, num_obj: 1 },
    LeanIxDecompileErrorBlobNotFound       { tag: 7, num_obj: 1 },
    LeanIxDecompileErrorBadBlobFormat      { tag: 8, num_obj: 2 },
    LeanIxDecompileErrorBadConstantFormat  { tag: 9, num_obj: 1 },
    LeanIxDecompileErrorSerialize          { tag: 10, num_obj: 1 },
  }
}

lean_ffi::lean_inductive! {
  LeanIxCompileError {
    LeanIxCompileErrorMissingConstant    { num_obj: 1 },
    LeanIxCompileErrorMissingAddress     { tag: 1, num_obj: 1 },
    LeanIxCompileErrorInvalidMutualBlock { tag: 2, num_obj: 1 },
    LeanIxCompileErrorUnsupportedExpr    { tag: 3, num_obj: 1 },
    LeanIxCompileErrorUnknownUnivParam   { tag: 4, num_obj: 2 },
    LeanIxCompileErrorSerialize          { tag: 5, num_obj: 1 },
  }
}

// =============================================================================
// Iroh types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanPutResponse { num_obj: 2 }
}
lean_ffi::lean_inductive! {
  LeanGetResponse { num_obj: 3 }
}

// =============================================================================
// LeanIxAddress — manual newtype over LeanByteArray
// =============================================================================

/// Lean `Address` object — newtype over `LeanByteArray`.
///
/// Address is a single-field struct in Lean, so it's unboxed to ByteArray
/// at the FFI boundary.
#[repr(transparent)]
pub struct LeanIxAddress<R: LeanRef>(LeanByteArray<R>);

impl<R: LeanRef> Clone for LeanIxAddress<R> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<R: LeanRef + Copy> Copy for LeanIxAddress<R> {}

impl<R: LeanRef> std::ops::Deref for LeanIxAddress<R> {
  type Target = LeanByteArray<R>;
  #[inline]
  fn deref(&self) -> &LeanByteArray<R> {
    &self.0
  }
}

impl From<LeanIxAddress<LeanOwned>> for LeanOwned {
  #[inline]
  fn from(x: LeanIxAddress<LeanOwned>) -> Self {
    x.0.into()
  }
}

impl<'a> From<LeanByteArray<LeanBorrowed<'a>>>
  for LeanIxAddress<LeanBorrowed<'a>>
{
  #[inline]
  fn from(x: LeanByteArray<LeanBorrowed<'a>>) -> Self {
    Self(x)
  }
}

impl From<LeanByteArray<LeanOwned>> for LeanIxAddress<LeanOwned> {
  #[inline]
  fn from(x: LeanByteArray<LeanOwned>) -> Self {
    Self(x)
  }
}

impl LeanIxAddress<LeanOwned> {
  #[inline]
  pub fn new(ba: LeanByteArray<LeanOwned>) -> Self {
    Self(ba)
  }
}

impl<'a> LeanIxAddress<LeanBorrowed<'a>> {
  #[inline]
  pub fn from_borrowed(ba: LeanByteArray<LeanBorrowed<'a>>) -> Self {
    Self(ba)
  }
}
