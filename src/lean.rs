//! Ix-specific Lean domain type definitions.
//!
//! Ctor-backed types use `lean_inductive!` which declares the domain type,
//! layout metadata (one entry per Lean constructor), and typed accessors.
//! Types without a ctor layout (simple enums, opaque objects, arenas) use
//! bare `lean_domain_type!`.

use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanOwned, LeanRef};

// =============================================================================
// Types without ctor layouts
// =============================================================================

lean_ffi::lean_domain_type! {
  // Simple enums (passed as raw unboxed tag values)
  LeanIxBinderInfo;
  LeanIxonDefKind;
  LeanIxonDefinitionSafety;
  LeanIxonQuotKind;

  // Opaque types (passed through without field access)
  LeanIxRawEnvironment;
  LeanIxEnvironment;
  LeanIxonExprMetaArena;
  LeanAiurCommitmentParameters;
  LeanAiurFriParameters;
}

// =============================================================================
// Ctor-backed types
// =============================================================================

lean_ffi::lean_inductive! {
  // --- Ixon structures (single-constructor) ---

  LeanIxonDefinition      [ { num_obj: 2, num_64: 1, num_8: 2 } ];
  LeanIxonRecursorRule    [ { num_obj: 1, num_64: 1 } ];
  LeanIxonRecursor        [ { num_obj: 2, num_64: 5, num_8: 2 } ];
  LeanIxonAxiom           [ { num_obj: 1, num_64: 1, num_8: 1 } ];
  LeanIxonQuotient        [ { num_obj: 1, num_64: 1, num_8: 1 } ];
  LeanIxonConstructor     [ { num_obj: 1, num_64: 4, num_8: 1 } ];
  LeanIxonInductive       [ { num_obj: 2, num_64: 4, num_8: 3 } ];
  LeanIxonInductiveProj   [ { num_obj: 1, num_64: 1 } ];
  LeanIxonConstructorProj [ { num_obj: 1, num_64: 2 } ];
  LeanIxonRecursorProj    [ { num_obj: 1, num_64: 1 } ];
  LeanIxonDefinitionProj  [ { num_obj: 1, num_64: 1 } ];
  LeanIxonNamed           [ { num_obj: 3 } ];
  LeanIxonComm            [ { num_obj: 2 } ];
  LeanIxonConstant        [ { num_obj: 4 } ];
  LeanIxonRawConst        [ { num_obj: 2 } ];
  LeanIxonRawNamed        [ { num_obj: 3 } ];
  LeanIxonRawBlob         [ { num_obj: 2 } ];
  LeanIxonRawComm         [ { num_obj: 2 } ];
  LeanIxonRawNameEntry    [ { num_obj: 2 } ];
  LeanIxonRawEnv          [ { num_obj: 5 } ];

  // --- Ixon multi-variant inductives ---

  LeanIxonUniv [
    { },                                      // tag 0: zero
    { num_obj: 1 },                           // tag 1: succ
    { num_obj: 2 },                           // tag 2: max
    { num_obj: 2 },                           // tag 3: imax
    { num_64: 1 },                            // tag 4: var
  ];

  LeanIxonExpr [
    { num_64: 1 },                            // tag 0: sort
    { num_64: 1 },                            // tag 1: var
    { num_obj: 1, num_64: 1 },                // tag 2: ref
    { num_obj: 1, num_64: 1 },                // tag 3: rec
    { num_obj: 1, num_64: 2 },                // tag 4: prj
    { num_64: 1 },                            // tag 5: str
    { num_64: 1 },                            // tag 6: nat
    { num_obj: 2 },                           // tag 7: app
    { num_obj: 2 },                           // tag 8: lam
    { num_obj: 2 },                           // tag 9: all
    { num_obj: 3, num_8: 1 },                 // tag 10: let
    { num_64: 1 },                            // tag 11: share
  ];

  LeanIxonExprMetaData [
    { },                                      // tag 0: leaf (scalar)
    { num_64: 2 },                            // tag 1: app
    { num_obj: 1, num_64: 2, num_8: 1 },      // tag 2: binder
    { num_obj: 1, num_64: 3 },                // tag 3: letBinder
    { num_obj: 1 },                           // tag 4: ref
    { num_obj: 1, num_64: 1 },                // tag 5: prj
    { num_obj: 1, num_64: 1 },                // tag 6: mdata
  ];

  LeanIxonConstantMeta [
    { },                                      // tag 0: empty (scalar)
    { num_obj: 6, num_64: 2 },                // tag 1: defn
    { num_obj: 3, num_64: 1 },                // tag 2: axio
    { num_obj: 3, num_64: 1 },                // tag 3: quot
    { num_obj: 6, num_64: 1 },                // tag 4: indc
    { num_obj: 4, num_64: 1 },                // tag 5: ctor
    { num_obj: 7, num_64: 1 },                // tag 6: recr
    { num_obj: 1 },                           // tag 7: muts
  ];

  LeanIxonDataValue [
    { num_obj: 1 },                           // tag 0: ofString
    { num_8: 1 },                             // tag 1: ofBool
    { num_obj: 1 },                           // tag 2: ofName
    { num_obj: 1 },                           // tag 3: ofNat
    { num_obj: 1 },                           // tag 4: ofInt
    { num_obj: 1 },                           // tag 5: ofSyntax
  ];

  LeanIxonMutConst [
    { num_obj: 1 },                           // tag 0: defn
    { num_obj: 1 },                           // tag 1: indc
    { num_obj: 1 },                           // tag 2: recr
  ];

  LeanIxonConstantInfo [
    { num_obj: 1 },                           // tag 0: defn
    { num_obj: 1 },                           // tag 1: recr
    { num_obj: 1 },                           // tag 2: axio
    { num_obj: 1 },                           // tag 3: quot
    { num_obj: 1 },                           // tag 4: cPrj
    { num_obj: 1 },                           // tag 5: rPrj
    { num_obj: 1 },                           // tag 6: iPrj
    { num_obj: 1 },                           // tag 7: dPrj
    { num_obj: 1 },                           // tag 8: muts
  ];

  // --- Ix structures (single-constructor) ---

  LeanIxConstantVal     [ { num_obj: 3 } ];
  LeanIxRecursorRule    [ { num_obj: 3 } ];
  LeanIxTheoremVal      [ { num_obj: 3 } ];
  LeanIxCondensedBlocks [ { num_obj: 3 } ];
  LeanIxCompilePhases   [ { num_obj: 3 } ];
  LeanIxSubstring       [ { num_obj: 3 } ];

  // --- Ix multi-variant inductives ---

  LeanIxName [
    { num_obj: 1 },                           // tag 0: anonymous
    { num_obj: 3 },                           // tag 1: str
    { num_obj: 3 },                           // tag 2: num
  ];

  LeanIxLevel [
    { num_obj: 1 },                           // tag 0: zero
    { num_obj: 2 },                           // tag 1: succ
    { num_obj: 3 },                           // tag 2: max
    { num_obj: 3 },                           // tag 3: imax
    { num_obj: 2 },                           // tag 4: param
    { num_obj: 2 },                           // tag 5: mvar
  ];

  LeanIxExpr [
    { num_obj: 2 },                           // tag 0: bvar
    { num_obj: 2 },                           // tag 1: fvar
    { num_obj: 2 },                           // tag 2: mvar
    { num_obj: 2 },                           // tag 3: sort
    { num_obj: 3 },                           // tag 4: const
    { num_obj: 3 },                           // tag 5: app
    { num_obj: 4, num_8: 1 },                 // tag 6: lam
    { num_obj: 4, num_8: 1 },                 // tag 7: forallE
    { num_obj: 5, num_8: 1 },                 // tag 8: letE
    { num_obj: 2 },                           // tag 9: lit
    { num_obj: 3 },                           // tag 10: mdata
    { num_obj: 4 },                           // tag 11: proj
  ];

  LeanIxConstantInfo [
    { num_obj: 1 },                           // tag 0: axiom
    { num_obj: 1 },                           // tag 1: defn
    { num_obj: 1 },                           // tag 2: thm
    { num_obj: 1 },                           // tag 3: opaque
    { num_obj: 1 },                           // tag 4: quot
    { num_obj: 1 },                           // tag 5: induct
    { num_obj: 1 },                           // tag 6: ctor
    { num_obj: 1 },                           // tag 7: rec
  ];

  LeanIxReducibilityHints [
    { },                                      // tag 0: opaque (scalar)
    { },                                      // tag 1: abbrev (scalar)
    { num_32: 1 },                            // tag 2: regular
  ];

  LeanIxLiteral [
    { num_obj: 1 },                           // tag 0: nat
    { num_obj: 1 },                           // tag 1: str
  ];

  LeanIxInt [
    { num_obj: 1 },                           // tag 0: ofNat
    { num_obj: 1 },                           // tag 1: negSucc
  ];

  LeanIxSourceInfo [
    { num_obj: 4 },                           // tag 0: original
    { num_obj: 2, num_8: 1 },                 // tag 1: synthetic
    { },                                      // tag 2: none
  ];

  LeanIxSyntax [
    { },                                      // tag 0: missing
    { num_obj: 3 },                           // tag 1: node
    { num_obj: 2 },                           // tag 2: atom
    { num_obj: 4 },                           // tag 3: ident
  ];

  LeanIxSyntaxPreresolved [
    { num_obj: 1 },                           // tag 0: namespace
    { num_obj: 2 },                           // tag 1: decl
  ];

  LeanIxDataValue [
    { num_obj: 1 },                           // tag 0: ofString
    { num_8: 1 },                             // tag 1: ofBool
    { num_obj: 1 },                           // tag 2: ofName
    { num_obj: 1 },                           // tag 3: ofNat
    { num_obj: 1 },                           // tag 4: ofInt
    { num_obj: 1 },                           // tag 5: ofSyntax
  ];

  // --- Lean kernel inner val types (used in Ix.ConstantInfo decode) ---

  LeanIxAxiomVal       [ { num_obj: 1, num_8: 1 } ];
  LeanIxDefinitionVal  [ { num_obj: 4, num_8: 1 } ];
  LeanIxOpaqueVal      [ { num_obj: 3, num_8: 1 } ];
  LeanIxQuotVal        [ { num_obj: 1, num_8: 1 } ];
  LeanIxInductiveVal   [ { num_obj: 6, num_8: 3 } ];
  LeanIxConstructorVal [ { num_obj: 5, num_8: 1 } ];
  LeanIxRecursorVal    [ { num_obj: 7, num_8: 2 } ];

  // --- Aiur types ---

  LeanAiurToplevel [ { num_obj: 2 } ];
  LeanAiurFunction [ { num_obj: 2, num_8: 2 } ];

  // --- Block / comparison types ---

  LeanIxBlockCompareResult [
    { },                                      // tag 0: match
    { num_64: 3 },                            // tag 1: mismatch
    { },                                      // tag 2: notFound
  ];

  LeanIxBlockCompareDetail [ { num_obj: 1, num_64: 2 } ];
  LeanIxBlock              [ { num_obj: 2, num_64: 1 } ];

  // --- Error types ---

  LeanIxSerializeError [
    { num_obj: 1 },                           // tag 0: unexpectedEof
    { num_obj: 1, num_8: 1 },                 // tag 1: invalidTag
    { num_obj: 1, num_8: 1 },                 // tag 2: invalidFlag
    { num_obj: 1, num_64: 1 },                // tag 3: invalidVariant
    { num_8: 1 },                             // tag 4: invalidBool
    { },                                      // tag 5: addressError
    { num_obj: 1, num_64: 1 },                // tag 6: invalidShareIndex
  ];

  LeanIxDecompileError [
    { num_obj: 2, num_64: 1 },                // tag 0: invalidRefIndex
    { num_obj: 2, num_64: 1 },                // tag 1: invalidUnivIndex
    { num_obj: 2, num_64: 1 },                // tag 2: invalidShareIndex
    { num_obj: 2, num_64: 1 },                // tag 3: invalidRecIndex
    { num_obj: 2, num_64: 1 },                // tag 4: invalidUnivVarIndex
    { num_obj: 1 },                           // tag 5: missingAddress
    { num_obj: 1 },                           // tag 6: missingMetadata
    { num_obj: 1 },                           // tag 7: blobNotFound
    { num_obj: 2 },                           // tag 8: badBlobFormat
    { num_obj: 1 },                           // tag 9: badConstantFormat
    { num_obj: 1 },                           // tag 10: serialize
  ];

  LeanIxCompileError [
    { num_obj: 1 },                           // tag 0: missingConstant
    { num_obj: 1 },                           // tag 1: missingAddress
    { num_obj: 1 },                           // tag 2: invalidMutualBlock
    { num_obj: 1 },                           // tag 3: unsupportedExpr
    { num_obj: 2 },                           // tag 4: unknownUnivParam
    { num_obj: 1 },                           // tag 5: serialize
  ];

  // --- Iroh types ---

  LeanPutResponse [ { num_obj: 2 } ];
  LeanGetResponse [ { num_obj: 3 } ];
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
