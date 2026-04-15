//! Ix-specific Lean domain type definitions.
//!
//! Generic Lean FFI wrappers live in the `lean_ffi` crate. This module defines
//! typed newtypes for ix-specific Lean types using `lean_ffi::lean_domain_type!`.

use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanOwned, LeanRef};

lean_ffi::lean_domain_type! {
  // Ix core types
  /// Lean `Ix.Name` object.
  LeanIxName;
  /// Lean `Ix.Level` object.
  LeanIxLevel;
  /// Lean `Ix.Expr` object.
  LeanIxExpr;
  /// Lean `Ix.ConstantInfo` object.
  LeanIxConstantInfo;
  /// Lean `Ix.ConstantVal` object.
  LeanIxConstantVal;
  /// Lean `Ix.ReducibilityHints` object.
  LeanIxReducibilityHints;
  /// Lean `Ix.Literal` object.
  LeanIxLiteral;
  /// Lean `Ix.BinderInfo` object.
  LeanIxBinderInfo;
  /// Lean `Ix.RecursorRule` object.
  LeanIxRecursorRule;
  /// Lean `Ix.RawEnvironment` object.
  LeanIxRawEnvironment;
  /// Lean `Ix.Environment` object.
  LeanIxEnvironment;
  /// Lean `Ix.RustCondensedBlocks` object.
  LeanIxCondensedBlocks;
  /// Lean `Ix.CompileM.RustCompilePhases` object.
  LeanIxCompilePhases;

  // Ix data types
  /// Lean `Ix.Int` object.
  LeanIxInt;
  /// Lean `Ix.Substring` object.
  LeanIxSubstring;
  /// Lean `Ix.SourceInfo` object.
  LeanIxSourceInfo;
  /// Lean `Ix.SyntaxPreresolved` object.
  LeanIxSyntaxPreresolved;
  /// Lean `Ix.Syntax` object.
  LeanIxSyntax;
  /// Lean `Ix.DataValue` object.
  LeanIxDataValue;

  // Ixon types
  /// Lean `Ixon.DefKind` object.
  LeanIxonDefKind;
  /// Lean `Ixon.DefinitionSafety` object.
  LeanIxonDefinitionSafety;
  /// Lean `Ixon.QuotKind` object.
  LeanIxonQuotKind;
  /// Lean `Ixon.Univ` object.
  LeanIxonUniv;
  /// Lean `Ixon.Expr` object.
  LeanIxonExpr;
  /// Lean `Ixon.Definition` object.
  LeanIxonDefinition;
  /// Lean `Ixon.RecursorRule` object.
  LeanIxonRecursorRule;
  /// Lean `Ixon.Recursor` object.
  LeanIxonRecursor;
  /// Lean `Ixon.Axiom` object.
  LeanIxonAxiom;
  /// Lean `Ixon.Quotient` object.
  LeanIxonQuotient;
  /// Lean `Ixon.Constructor` object.
  LeanIxonConstructor;
  /// Lean `Ixon.Inductive` object.
  LeanIxonInductive;
  /// Lean `Ixon.InductiveProj` object.
  LeanIxonInductiveProj;
  /// Lean `Ixon.ConstructorProj` object.
  LeanIxonConstructorProj;
  /// Lean `Ixon.RecursorProj` object.
  LeanIxonRecursorProj;
  /// Lean `Ixon.DefinitionProj` object.
  LeanIxonDefinitionProj;
  /// Lean `Ixon.MutConst` object.
  LeanIxonMutConst;
  /// Lean `Ixon.ConstantInfo` object.
  LeanIxonConstantInfo;
  /// Lean `Ixon.Constant` object.
  LeanIxonConstant;
  /// Lean `Ixon.DataValue` object.
  LeanIxonDataValue;
  /// Lean `Ixon.ExprMetaData` object.
  LeanIxonExprMetaData;
  /// Lean `Ixon.ExprMetaArena` object.
  LeanIxonExprMetaArena;
  /// Lean `Ixon.ConstantMeta` object.
  LeanIxonConstantMeta;
  /// Lean `Ixon.Named` object.
  LeanIxonNamed;
  /// Lean `Ixon.Comm` object.
  LeanIxonComm;
  /// Lean `Ixon.RawEnv` object.
  LeanIxonRawEnv;
  /// Lean `Ixon.RawConst` object.
  LeanIxonRawConst;
  /// Lean `Ixon.RawNamed` object.
  LeanIxonRawNamed;
  /// Lean `Ixon.RawBlob` object.
  LeanIxonRawBlob;
  /// Lean `Ixon.RawComm` object.
  LeanIxonRawComm;
  /// Lean `Ixon.RawNameEntry` object.
  LeanIxonRawNameEntry;

  // Aiur types
  /// Lean `Aiur.Bytecode.Toplevel` object.
  LeanAiurToplevel;
  /// Lean `Aiur.CommitmentParameters` object.
  LeanAiurCommitmentParameters;
  /// Lean `Aiur.FriParameters` object.
  LeanAiurFriParameters;

  // Ix inner val types (ConstantInfo variants)
  /// Lean `Ix.AxiomVal` object.
  LeanIxAxiomVal;
  /// Lean `Ix.DefinitionVal` object.
  LeanIxDefinitionVal;
  /// Lean `Ix.OpaqueVal` object.
  LeanIxOpaqueVal;
  /// Lean `Ix.QuotVal` object.
  LeanIxQuotVal;
  /// Lean `Ix.InductiveVal` object.
  LeanIxInductiveVal;
  /// Lean `Ix.ConstructorVal` object.
  LeanIxConstructorVal;
  /// Lean `Ix.RecursorVal` object.
  LeanIxRecursorVal;
  /// Lean `Ix.ReducibilityHints.Regular` object.
  LeanIxReducibilityHintsRegular;

  // Aiur inner types
  /// Lean `Aiur.Bytecode.Function` object.
  LeanAiurFunction;

  // Ixon multi-scalar variant types
  /// Lean `Ixon.ExprMetaData.App` (tag 1) object.
  LeanIxonExprMetaApp;
  /// Lean `Ixon.ExprMetaData.Binder` (tag 2) object.
  LeanIxonExprMetaBinder;
  /// Lean `Ixon.ExprMetaData.LetBinder` (tag 3) object.
  LeanIxonExprMetaLetBinder;
  /// Lean `Ixon.ConstantMeta.Def` (tag 1) object.
  LeanIxonConstantMetaDef;
  /// Lean `Ixon.Expr.Prj` (tag 4) object.
  LeanIxonExprPrj;

  // Ixon single-scalar variant types
  /// Lean `Ixon.ConstantMeta.Axio` (tag 2) object.
  LeanIxonConstantMetaAxio;
  /// Lean `Ixon.ConstantMeta.Quot` (tag 3) object.
  LeanIxonConstantMetaQuot;
  /// Lean `Ixon.ConstantMeta.Indc` (tag 4) object.
  LeanIxonConstantMetaIndc;
  /// Lean `Ixon.ConstantMeta.Ctor` (tag 5) object.
  LeanIxonConstantMetaCtor;
  /// Lean `Ixon.ConstantMeta.Rec` (tag 6) object.
  LeanIxonConstantMetaRec;
  /// Lean `Ixon.ExprMetaData.Prj` (tag 5) object.
  LeanIxonExprMetaPrj;
  /// Lean `Ixon.ExprMetaData.Mdata` (tag 6) object.
  LeanIxonExprMetaMdata;
  /// Lean `Ixon.DataValue.OfBool` (tag 1) object.
  LeanIxonDataValueBool;
  /// Lean `Ixon.Expr.Sort` (tag 0) object.
  LeanIxonExprSort;
  /// Lean `Ixon.Expr.Var` (tag 1) object.
  LeanIxonExprVar;
  /// Lean `Ixon.Expr.Ref` (tag 2) object.
  LeanIxonExprRef;
  /// Lean `Ixon.Expr.Rec` (tag 3) object.
  LeanIxonExprRec;
  /// Lean `Ixon.Expr.Str` (tag 5) object.
  LeanIxonExprStr;
  /// Lean `Ixon.Expr.Nat` (tag 6) object.
  LeanIxonExprNat;
  /// Lean `Ixon.Expr.Let` (tag 10) object.
  LeanIxonExprLet;
  /// Lean `Ixon.Expr.Share` (tag 11) object.
  LeanIxonExprShare;
  /// Lean `Ixon.Univ.Var` (tag 4) object.
  LeanIxonUnivVar;
  /// Lean `Ix.Expr.Lam` (tag 6) object.
  LeanIxExprLam;
  /// Lean `Ix.Expr.ForallE` (tag 7) object.
  LeanIxExprForallE;
  /// Lean `Ix.Expr.LetE` (tag 8) object.
  LeanIxExprLetE;
  /// Lean `Ix.SourceInfo.Synthetic` (tag 1) object.
  LeanIxSourceInfoSynthetic;
  /// Lean `Ix.DataValue.OfBool` (tag 1) object.
  LeanIxDataValueBool;

  // Block types
  /// Lean `BlockCompareResult.Mismatch` (tag 1) object.
  LeanIxBlockCompareResultMismatch;
  /// Lean `Ix.Block` object.
  LeanIxBlock;

  // SerializeError variant types
  /// Lean `Ixon.SerializeError.InvalidTag` (tag 1) object.
  LeanIxSerializeErrorInvalidTag;
  /// Lean `Ixon.SerializeError.InvalidFlag` (tag 2) object.
  LeanIxSerializeErrorInvalidFlag;
  /// Lean `Ixon.SerializeError.InvalidVariant` (tag 3) object.
  LeanIxSerializeErrorInvalidVariant;
  /// Lean `Ixon.SerializeError.InvalidBool` (tag 4) object.
  LeanIxSerializeErrorInvalidBool;
  /// Lean `Ixon.SerializeError.InvalidShareIndex` (tag 6) object.
  LeanIxSerializeErrorInvalidShareIndex;

  // DecompileError variant types (tags 0-4 share layout: 2 obj + 1 u64)
  /// Lean `Ix.DecompileError.InvalidRefIndex` (tag 0) object.
  LeanIxDecompileErrorRefIndex;
  /// Lean `Ix.DecompileError.InvalidUnivIndex` (tag 1) object.
  LeanIxDecompileErrorUnivIndex;
  /// Lean `Ix.DecompileError.InvalidShareIndex` (tag 2) object.
  LeanIxDecompileErrorShareIndex;
  /// Lean `Ix.DecompileError.InvalidRecIndex` (tag 3) object.
  LeanIxDecompileErrorRecIndex;
  /// Lean `Ix.DecompileError.InvalidUnivVarIndex` (tag 4) object.
  LeanIxDecompileErrorUnivVarIndex;

  // Error types
  /// Lean `Ixon.SerializeError` object.
  LeanIxSerializeError;
  /// Lean `Ix.DecompileM.DecompileError` object.
  LeanIxDecompileError;
  /// Lean `Ix.CompileM.CompileError` object.
  LeanIxCompileError;
  /// Lean `BlockCompareResult` object.
  LeanIxBlockCompareResult;
  /// Lean `BlockCompareDetail` object.
  LeanIxBlockCompareDetail;
}

// =============================================================================
// LeanCtorScalar impls for Ixon structure types
// =============================================================================

// ixon/constant.rs structures
lean_ffi::impl_ctor_scalar!(LeanIxonDefinition     { NUM_OBJ = 2, NUM_64 = 1, NUM_8 = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxonRecursorRule   { NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonRecursor       { NUM_OBJ = 2, NUM_64 = 5, NUM_8 = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxonAxiom          { NUM_OBJ = 1, NUM_64 = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonQuotient       { NUM_OBJ = 1, NUM_64 = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstructor    { NUM_OBJ = 1, NUM_64 = 4, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonInductive      { NUM_OBJ = 2, NUM_64 = 4, NUM_8 = 3 });
lean_ffi::impl_ctor_scalar!(LeanIxonInductiveProj  { NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstructorProj { NUM_OBJ = 1, NUM_64 = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxonRecursorProj   { NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonDefinitionProj { NUM_OBJ = 1, NUM_64 = 1 });

// ixon/compare.rs + compile.rs
lean_ffi::impl_ctor_scalar!(LeanIxBlockCompareDetail { NUM_OBJ = 1, NUM_64 = 2 });

// Ix inner val types (ix/constant.rs + lean_env.rs)
lean_ffi::impl_ctor_scalar!(LeanIxAxiomVal          { NUM_OBJ = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxDefinitionVal     { NUM_OBJ = 4, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxOpaqueVal         { NUM_OBJ = 3, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxQuotVal           { NUM_OBJ = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxInductiveVal      { NUM_OBJ = 6, NUM_8 = 3 });
lean_ffi::impl_ctor_scalar!(LeanIxConstructorVal    { NUM_OBJ = 5, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxRecursorVal       { NUM_OBJ = 7, NUM_8 = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxReducibilityHintsRegular { TAG = 2, NUM_32 = 1 });

// Aiur inner types
lean_ffi::impl_ctor_scalar!(LeanAiurFunction        { NUM_OBJ = 2, NUM_8 = 2 });

// Ixon multi-scalar variant types
lean_ffi::impl_ctor_scalar!(LeanIxonExprMetaApp        { TAG = 1, NUM_64 = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprMetaBinder     { TAG = 2, NUM_OBJ = 1, NUM_64 = 2, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprMetaLetBinder  { TAG = 3, NUM_OBJ = 1, NUM_64 = 3 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstantMetaDef    { TAG = 1, NUM_OBJ = 6, NUM_64 = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprPrj            { TAG = 4, NUM_OBJ = 1, NUM_64 = 2 });

// Ixon single-scalar variant types
lean_ffi::impl_ctor_scalar!(LeanIxonConstantMetaAxio   { TAG = 2, NUM_OBJ = 3, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstantMetaQuot   { TAG = 3, NUM_OBJ = 3, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstantMetaIndc   { TAG = 4, NUM_OBJ = 6, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstantMetaCtor   { TAG = 5, NUM_OBJ = 4, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstantMetaRec    { TAG = 6, NUM_OBJ = 7, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprMetaPrj        { TAG = 5, NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprMetaMdata      { TAG = 6, NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonDataValueBool      { TAG = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprSort           { TAG = 0, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprVar            { TAG = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprRef            { TAG = 2, NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprRec            { TAG = 3, NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprStr            { TAG = 5, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprNat            { TAG = 6, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprLet            { TAG = 10, NUM_OBJ = 3, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonExprShare          { TAG = 11, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonUnivVar            { TAG = 4, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxExprLam              { TAG = 6, NUM_OBJ = 4, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxExprForallE          { TAG = 7, NUM_OBJ = 4, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxExprLetE             { TAG = 8, NUM_OBJ = 5, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxSourceInfoSynthetic  { TAG = 1, NUM_OBJ = 2, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxDataValueBool        { TAG = 1, NUM_8 = 1 });

// SerializeError variant types
lean_ffi::impl_ctor_scalar!(LeanIxSerializeErrorInvalidTag        { TAG = 1, NUM_OBJ = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxSerializeErrorInvalidFlag       { TAG = 2, NUM_OBJ = 1, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxSerializeErrorInvalidVariant    { TAG = 3, NUM_OBJ = 1, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxSerializeErrorInvalidBool       { TAG = 4, NUM_8 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxSerializeErrorInvalidShareIndex { TAG = 6, NUM_OBJ = 1, NUM_64 = 1 });

// DecompileError variant types (tags 0-4: 2 obj + 1 u64)
lean_ffi::impl_ctor_scalar!(LeanIxDecompileErrorRefIndex      { NUM_OBJ = 2, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxDecompileErrorUnivIndex     { TAG = 1, NUM_OBJ = 2, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxDecompileErrorShareIndex    { TAG = 2, NUM_OBJ = 2, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxDecompileErrorRecIndex      { TAG = 3, NUM_OBJ = 2, NUM_64 = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxDecompileErrorUnivVarIndex  { TAG = 4, NUM_OBJ = 2, NUM_64 = 1 });

// Block types
lean_ffi::impl_ctor_scalar!(LeanIxBlockCompareResultMismatch { TAG = 1, NUM_64 = 3 });
lean_ffi::impl_ctor_scalar!(LeanIxBlock             { NUM_OBJ = 2, NUM_64 = 1 });

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
