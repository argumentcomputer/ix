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
lean_ffi::impl_ctor_scalar!(LeanIxonDefinition     { NUM_8B = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonRecursorRule   { NUM_8B = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonRecursor       { NUM_8B = 5 });
lean_ffi::impl_ctor_scalar!(LeanIxonAxiom          { NUM_8B = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonQuotient       { NUM_8B = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstructor    { NUM_8B = 4 });
lean_ffi::impl_ctor_scalar!(LeanIxonInductive      { NUM_8B = 4 });
lean_ffi::impl_ctor_scalar!(LeanIxonInductiveProj  { NUM_8B = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonConstructorProj { NUM_8B = 2 });
lean_ffi::impl_ctor_scalar!(LeanIxonRecursorProj   { NUM_8B = 1 });
lean_ffi::impl_ctor_scalar!(LeanIxonDefinitionProj { NUM_8B = 1 });

// ixon/compare.rs + compile.rs
lean_ffi::impl_ctor_scalar!(LeanIxBlockCompareDetail { NUM_8B = 2 });

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
