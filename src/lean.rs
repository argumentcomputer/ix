//! Ix-specific Lean domain type definitions.
//!
//! Generic Lean FFI wrappers live in the `lean_sys` crate. This module defines
//! typed newtypes for ix-specific Lean types using `lean_sys::lean_domain_type!`.

lean_sys::lean_domain_type! {
  // Ix core types
  /// Lean `Ix.Name` object.
  LeanIxName;
  /// Lean `Ix.Level` object.
  LeanIxLevel;
  /// Lean `Ix.Expr` object.
  LeanIxExpr;
  /// Lean `Ix.ConstantInfo` object.
  LeanIxConstantInfo;
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

/// `Ix.Address = { hash : ByteArray }` — single-field struct, unboxed to `ByteArray`.
pub type LeanIxAddress = lean_sys::object::LeanByteArray;
