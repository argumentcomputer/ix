//! Ix-specific Lean domain type definitions.
//!
//! Ctor-backed types use `lean_inductive!` which declares the domain type,
//! layout metadata (one entry per Lean constructor), and typed accessors.
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
// Ixon structures (single-constructor)
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxonDefinition [ { num_obj: 2, num_64: 1, num_8: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRecursorRule [ { num_obj: 1, num_64: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRecursor [ { num_obj: 2, num_64: 5, num_8: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonAxiom [ { num_obj: 1, num_64: 1, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonQuotient [ { num_obj: 1, num_64: 1, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonConstructor [ { num_obj: 1, num_64: 4, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonInductive [ { num_obj: 2, num_64: 4, num_8: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonInductiveProj [ { num_obj: 1, num_64: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonConstructorProj [ { num_obj: 1, num_64: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRecursorProj [ { num_obj: 1, num_64: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonDefinitionProj [ { num_obj: 1, num_64: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonNamed [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonComm [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonConstant [ { num_obj: 4 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRawConst [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRawNamed [ { num_obj: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRawBlob [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRawComm [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRawNameEntry [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxonRawEnv [ { num_obj: 5 } ]
}

// =============================================================================
// Ixon multi-variant inductives
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxonUniv [
    { },                              // tag 0: zero
    { num_obj: 1 },                   // tag 1: succ
    { num_obj: 2 },                   // tag 2: max
    { num_obj: 2 },                   // tag 3: imax
    { num_64: 1 },                    // tag 4: var
  ]
}

lean_ffi::lean_inductive! {
  LeanIxonExpr [
    { num_64: 1 },                    // tag 0: sort
    { num_64: 1 },                    // tag 1: var
    { num_obj: 1, num_64: 1 },        // tag 2: ref
    { num_obj: 1, num_64: 1 },        // tag 3: rec
    { num_obj: 1, num_64: 2 },        // tag 4: prj
    { num_64: 1 },                    // tag 5: str
    { num_64: 1 },                    // tag 6: nat
    { num_obj: 2 },                   // tag 7: app
    { num_obj: 2 },                   // tag 8: lam
    { num_obj: 2 },                   // tag 9: all
    { num_obj: 3, num_8: 1 },         // tag 10: let
    { num_64: 1 },                    // tag 11: share
  ]
}

lean_ffi::lean_inductive! {
  LeanIxonExprMetaData [
    { },                              // tag 0: leaf (scalar)
    { num_64: 2 },                    // tag 1: app
    { num_obj: 1, num_64: 2, num_8: 1 }, // tag 2: binder
    { num_obj: 1, num_64: 3 },        // tag 3: letBinder
    { num_obj: 1 },                   // tag 4: ref
    { num_obj: 1, num_64: 1 },        // tag 5: prj
    { num_obj: 1, num_64: 1 },        // tag 6: mdata
  ]
}

lean_ffi::lean_inductive! {
  LeanIxonConstantMeta [
    { },                              // tag 0: empty (scalar)
    { num_obj: 6, num_64: 2 },        // tag 1: defn
    { num_obj: 3, num_64: 1 },        // tag 2: axio
    { num_obj: 3, num_64: 1 },        // tag 3: quot
    { num_obj: 6, num_64: 1 },        // tag 4: indc
    { num_obj: 4, num_64: 1 },        // tag 5: ctor
    { num_obj: 7, num_64: 1 },        // tag 6: recr
  ]
}

lean_ffi::lean_inductive! {
  LeanIxonDataValue [
    { num_obj: 1 },                   // tag 0: ofString
    { num_8: 1 },                     // tag 1: ofBool
    { num_obj: 1 },                   // tag 2: ofName
    { num_obj: 1 },                   // tag 3: ofNat
    { num_obj: 1 },                   // tag 4: ofInt
    { num_obj: 1 },                   // tag 5: ofSyntax
  ]
}

lean_ffi::lean_inductive! {
  LeanIxonMutConst [
    { num_obj: 1 },                   // tag 0: defn
    { num_obj: 1 },                   // tag 1: indc
    { num_obj: 1 },                   // tag 2: recr
  ]
}

lean_ffi::lean_inductive! {
  LeanIxonConstantInfo [
    { num_obj: 1 },                   // tag 0: defn
    { num_obj: 1 },                   // tag 1: recr
    { num_obj: 1 },                   // tag 2: axio
    { num_obj: 1 },                   // tag 3: quot
    { num_obj: 1 },                   // tag 4: cPrj
    { num_obj: 1 },                   // tag 5: rPrj
    { num_obj: 1 },                   // tag 6: iPrj
    { num_obj: 1 },                   // tag 7: dPrj
    { num_obj: 1 },                   // tag 8: muts
  ]
}

// =============================================================================
// Ix structures (single-constructor)
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxConstantVal [ { num_obj: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxRecursorRule [ { num_obj: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxTheoremVal [ { num_obj: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxCondensedBlocks [ { num_obj: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxCompilePhases [ { num_obj: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxSubstring [ { num_obj: 3 } ]
}

// =============================================================================
// Ix multi-variant inductives
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxName [
    { num_obj: 1 },                   // tag 0: anonymous
    { num_obj: 3 },                   // tag 1: str
    { num_obj: 3 },                   // tag 2: num
  ]
}

lean_ffi::lean_inductive! {
  LeanIxLevel [
    { num_obj: 1 },                   // tag 0: zero
    { num_obj: 2 },                   // tag 1: succ
    { num_obj: 3 },                   // tag 2: max
    { num_obj: 3 },                   // tag 3: imax
    { num_obj: 2 },                   // tag 4: param
    { num_obj: 2 },                   // tag 5: mvar
  ]
}

lean_ffi::lean_inductive! {
  LeanIxExpr [
    { num_obj: 2 },                   // tag 0: bvar
    { num_obj: 2 },                   // tag 1: fvar
    { num_obj: 2 },                   // tag 2: mvar
    { num_obj: 2 },                   // tag 3: sort
    { num_obj: 3 },                   // tag 4: const
    { num_obj: 3 },                   // tag 5: app
    { num_obj: 4, num_8: 1 },         // tag 6: lam
    { num_obj: 4, num_8: 1 },         // tag 7: forallE
    { num_obj: 5, num_8: 1 },         // tag 8: letE
    { num_obj: 2 },                   // tag 9: lit
    { num_obj: 3 },                   // tag 10: mdata
    { num_obj: 4 },                   // tag 11: proj
  ]
}

lean_ffi::lean_inductive! {
  LeanIxConstantInfo [
    { num_obj: 1 },                   // tag 0: axiom
    { num_obj: 1 },                   // tag 1: defn
    { num_obj: 1 },                   // tag 2: thm
    { num_obj: 1 },                   // tag 3: opaque
    { num_obj: 1 },                   // tag 4: quot
    { num_obj: 1 },                   // tag 5: induct
    { num_obj: 1 },                   // tag 6: ctor
    { num_obj: 1 },                   // tag 7: rec
  ]
}

lean_ffi::lean_inductive! {
  LeanIxReducibilityHints [
    { },                              // tag 0: opaque (scalar)
    { },                              // tag 1: abbrev (scalar)
    { num_32: 1 },                    // tag 2: regular
  ]
}

lean_ffi::lean_inductive! {
  LeanIxLiteral [
    { num_obj: 1 },                   // tag 0: nat
    { num_obj: 1 },                   // tag 1: str
  ]
}

lean_ffi::lean_inductive! {
  LeanIxInt [
    { num_obj: 1 },                   // tag 0: ofNat
    { num_obj: 1 },                   // tag 1: negSucc
  ]
}

lean_ffi::lean_inductive! {
  LeanIxSourceInfo [
    { num_obj: 4 },                   // tag 0: original
    { num_obj: 2, num_8: 1 },         // tag 1: synthetic
    { },                              // tag 2: none
  ]
}

lean_ffi::lean_inductive! {
  LeanIxSyntax [
    { },                              // tag 0: missing
    { num_obj: 3 },                   // tag 1: node
    { num_obj: 2 },                   // tag 2: atom
    { num_obj: 4 },                   // tag 3: ident
  ]
}

lean_ffi::lean_inductive! {
  LeanIxSyntaxPreresolved [
    { num_obj: 1 },                   // tag 0: namespace
    { num_obj: 2 },                   // tag 1: decl
  ]
}

lean_ffi::lean_inductive! {
  LeanIxDataValue [
    { num_obj: 1 },                   // tag 0: ofString
    { num_8: 1 },                     // tag 1: ofBool
    { num_obj: 1 },                   // tag 2: ofName
    { num_obj: 1 },                   // tag 3: ofNat
    { num_obj: 1 },                   // tag 4: ofInt
    { num_obj: 1 },                   // tag 5: ofSyntax
  ]
}

// =============================================================================
// Lean kernel inner val types (used in Ix.ConstantInfo decode)
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxAxiomVal [ { num_obj: 1, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxDefinitionVal [ { num_obj: 4, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxOpaqueVal [ { num_obj: 3, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxQuotVal [ { num_obj: 1, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxInductiveVal [ { num_obj: 6, num_8: 3 } ]
}
lean_ffi::lean_inductive! {
  LeanIxConstructorVal [ { num_obj: 5, num_8: 1 } ]
}
lean_ffi::lean_inductive! {
  LeanIxRecursorVal [ { num_obj: 7, num_8: 2 } ]
}

// =============================================================================
// Aiur types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanAiurToplevel [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanAiurFunction [ { num_obj: 2, num_8: 2 } ]
}

// =============================================================================
// Block / comparison types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxBlockCompareResult [
    { },                              // tag 0: match
    { num_64: 3 },                    // tag 1: mismatch
    { },                              // tag 2: notFound
  ]
}

lean_ffi::lean_inductive! {
  LeanIxBlockCompareDetail [ { num_obj: 1, num_64: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanIxBlock [ { num_obj: 2, num_64: 1 } ]
}

// =============================================================================
// Error types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanIxSerializeError [
    { num_obj: 1 },                   // tag 0: unexpectedEof
    { num_obj: 1, num_8: 1 },         // tag 1: invalidTag
    { num_obj: 1, num_8: 1 },         // tag 2: invalidFlag
    { num_obj: 1, num_64: 1 },        // tag 3: invalidVariant
    { num_8: 1 },                     // tag 4: invalidBool
    { },                              // tag 5: addressError
    { num_obj: 1, num_64: 1 },        // tag 6: invalidShareIndex
  ]
}

lean_ffi::lean_inductive! {
  LeanIxDecompileError [
    { num_obj: 2, num_64: 1 },        // tag 0: invalidRefIndex
    { num_obj: 2, num_64: 1 },        // tag 1: invalidUnivIndex
    { num_obj: 2, num_64: 1 },        // tag 2: invalidShareIndex
    { num_obj: 2, num_64: 1 },        // tag 3: invalidRecIndex
    { num_obj: 2, num_64: 1 },        // tag 4: invalidUnivVarIndex
    { num_obj: 1 },                   // tag 5: missingAddress
    { num_obj: 1 },                   // tag 6: missingMetadata
    { num_obj: 1 },                   // tag 7: blobNotFound
    { num_obj: 2 },                   // tag 8: badBlobFormat
    { num_obj: 1 },                   // tag 9: badConstantFormat
    { num_obj: 1 },                   // tag 10: serialize
  ]
}

lean_ffi::lean_inductive! {
  LeanIxCompileError [
    { num_obj: 1 },                   // tag 0: missingConstant
    { num_obj: 1 },                   // tag 1: missingAddress
    { num_obj: 1 },                   // tag 2: invalidMutualBlock
    { num_obj: 1 },                   // tag 3: unsupportedExpr
    { num_obj: 2 },                   // tag 4: unknownUnivParam
    { num_obj: 1 },                   // tag 5: serialize
  ]
}

// =============================================================================
// Iroh types
// =============================================================================

lean_ffi::lean_inductive! {
  LeanPutResponse [ { num_obj: 2 } ]
}
lean_ffi::lean_inductive! {
  LeanGetResponse [ { num_obj: 3 } ]
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
