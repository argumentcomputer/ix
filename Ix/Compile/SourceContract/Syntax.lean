module

public import Lean

/-!
# Scoped `@`-prefixed mode keyword grammar

All modifier atoms use `atomic ("@" >> checkNoWsBefore ... >> nonReservedSymbol w)`
so ZERO tokens are added to Lean's global `TokenTable`. Parsers are NOT registered
globally here; `Ix.Compile.SourceContract.Elab` registers them `scoped` under
`namespace Ix.Modes` (`open scoped Ix.Modes`).
-/

public meta section

namespace Ix.Compile.SourceSyntax

open Lean Parser

/-- Parse an `@`-prefixed mode keyword without adding any token to `TokenTable`. -/
@[expose] def modeKw (w : String) : Parser :=
  atomic ("@" >> checkNoWsBefore "no space after @" >> nonReservedSymbol w)

/-! ### Mode prefixes -/

@[expose] def binderModeAtom := leading_parser
  modeKw "borrowed" <|> modeKw "unique" <|> modeKw "once" <|> modeKw "erased"

@[expose] def binderModePrefix := leading_parser many1 binderModeAtom

@[expose] def resultModeAtom := leading_parser
  modeKw "borrowed" <|> modeKw "unique" <|> modeKw "once" <|> modeKw "erased"

@[expose] def resultModePrefix := leading_parser many1 resultModeAtom

@[expose] def letModeAtom := leading_parser
  modeKw "borrowed" <|> modeKw "unique" <|> modeKw "once" <|> modeKw "erased" <|> modeKw "borrow"

@[expose] def letModePrefix := leading_parser many1 letModeAtom

@[expose] def fieldModeAtom := leading_parser
  modeKw "shared" <|> modeKw "erased" <|>
  modeKw "borrowed" <|> modeKw "unique" <|> modeKw "once" <|> modeKw "borrow"

@[expose] def fieldModePrefix := leading_parser many1 fieldModeAtom

/-! ### Annotated binders (all 4 bracket kinds, multi-name groups, optional `: T`) -/

@[expose] def explicitBinder := leading_parser
  "(" >> binderModePrefix >> many1 Term.binderIdent >> Term.optType >> ")"

@[expose] def implicitBinder := leading_parser
  "{" >> binderModePrefix >> many1 Term.binderIdent >> Term.optType >> "}"

@[expose] def strictImplicitBinder := leading_parser
  Term.strictImplicitLeftBracket >> binderModePrefix >> many1 Term.binderIdent >> Term.optType >>
  Term.strictImplicitRightBracket

@[expose] def instanceBinder := leading_parser
  "[" >> binderModePrefix >> optional (atomic (ident >> " : ")) >> termParser >> "]"

@[expose] def annotatedBinder :=
  explicitBinder <|> strictImplicitBinder <|> implicitBinder <|> instanceBinder

@[expose] def isAnnotatedBinderKind (k : SyntaxNodeKind) : Bool :=
  k == ``explicitBinder || k == ``implicitBinder ||
  k == ``strictImplicitBinder || k == ``instanceBinder

/-! ### Declaration signatures (`def`, `abbrev`, `opaque`, `axiom`) -/

@[expose] def resultType := leading_parser " : " >> resultModePrefix >> termParser

@[expose] def optDeclSig := leading_parser
  many (ppSpace >> (atomic annotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >>
    (atomic resultType <|> Term.optType)

@[expose] def declSig := leading_parser
  many (ppSpace >> (atomic annotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >>
    (atomic resultType <|> Term.typeSpec)

@[expose] def hasAnnotatedBinder (signature : Syntax) : Bool :=
  signature[0].getArgs.any fun binder => isAnnotatedBinderKind binder.getKind

@[expose] def hasAnnotatedDeclSig (signature : Syntax) : Bool :=
  hasAnnotatedBinder signature || signature[1].isOfKind ``resultType

@[expose] def definitionDecl := leading_parser
  "def " >> Command.declId >> ppIndent optDeclSig >>
  checkStackTop hasAnnotatedDeclSig "annotated definition" >>
  Command.declVal >> Command.optDefDeriving

@[expose] def abbrevDecl := leading_parser
  "abbrev " >> Command.declId >> ppIndent optDeclSig >>
  checkStackTop hasAnnotatedDeclSig "annotated abbrev" >>
  Command.declVal

@[expose] def opaqueDecl := leading_parser
  "opaque " >> Command.declId >> ppIndent declSig >>
  checkStackTop hasAnnotatedDeclSig "annotated opaque" >>
  optional Command.declValSimple

@[expose] def axiomDecl := leading_parser
  "axiom " >> Command.declId >> ppIndent declSig >>
  checkStackTop hasAnnotatedDeclSig "annotated axiom"

@[expose] def declaration := leading_parser
  Command.declModifiers false >> (definitionDecl <|> abbrevDecl <|> opaqueDecl <|> axiomDecl)

/-! ### Term-level mode syntax (`fun`, `∀`, `→`, `let`, `do`-`let`) -/

@[expose] def funSignature := leading_parser
  many1 (ppSpace >> (atomic annotatedBinder <|> Term.funBinder)) >> Term.optType

@[expose] def annotatedFun := leading_parser:maxPrec
  unicodeSymbol "λ" "fun" >> funSignature >>
  checkStackTop hasAnnotatedBinder "annotated function binder" >>
  unicodeSymbol " ↦" " =>" >> termParser

@[expose] def forallSignature := leading_parser
  many1 (ppSpace >> (atomic annotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >>
  Term.optType >> ", " >> optional resultModePrefix

@[expose] def hasForallContract (signature : Syntax) : Bool :=
  hasAnnotatedBinder signature || !signature[3].isNone

@[expose] def annotatedForall := leading_parser:leadPrec
  unicodeSymbol "∀" "forall" >> forallSignature >>
  checkStackTop hasForallContract "annotated forall" >> termParser

@[expose] def dependentArrowSignature := leading_parser
  (atomic annotatedBinder <|> Term.bracketedBinder true) >>
  unicodeSymbol " → " " -> " >> optional resultModePrefix

@[expose] def hasArrowContract (signature : Syntax) : Bool :=
  isAnnotatedBinderKind signature[0].getKind || !signature[2].isNone

@[expose] def annotatedDepArrow := leading_parser:25
  dependentArrowSignature >> checkStackTop hasArrowContract "annotated arrow" >> termParser

@[expose] def annotatedArrow := trailing_parser
  checkPrec 25 >> unicodeSymbol " → " " -> " >> resultModePrefix >> termParser 25

@[expose] def annotatedLet := leading_parser:leadPrec
  withPosition ("let" >> atomic letModePrefix >> Term.binderIdent >> Term.optType >> " := " >> termParser) >>
  Term.optSemicolon termParser

@[expose] def doAnnotatedLet := leading_parser
  "let " >> atomic letModePrefix >> Term.binderIdent >> Term.optType >> " := " >> termParser

/-! ### Structure & inductive fields (`@shared`, `@erased`) -/

@[expose] def structAnnotatedSimpleField := leading_parser
  atomic (Command.declModifiers true >> fieldModePrefix) >> ident >>
  Command.optDeclSig >> optional (Term.binderTactic <|> Term.binderDefault)

@[expose] def structAnnotatedExplicitBinder := leading_parser
  atomic (Command.declModifiers true >> "(" >> fieldModePrefix) >>
  withoutPosition (many1 ident >> ppIndent Command.optDeclSig >>
    optional (Term.binderTactic <|> Term.binderDefault)) >>
  ")"

@[expose] def structAnnotatedImplicitBinder := leading_parser
  atomic (Command.declModifiers true >> "{" >> fieldModePrefix) >>
  withoutPosition (many1 ident >> Command.declSig) >> "}"

@[expose] def structAnnotatedInstBinder := leading_parser
  atomic (Command.declModifiers true >> "[" >> fieldModePrefix) >>
  withoutPosition (many1 ident >> Command.declSig) >> "]"

@[expose] def isAnnotatedStructFieldKind (k : SyntaxNodeKind) : Bool :=
  k == ``structAnnotatedSimpleField || k == ``structAnnotatedExplicitBinder ||
  k == ``structAnnotatedImplicitBinder || k == ``structAnnotatedInstBinder

@[expose] def annotatedStructFields := leading_parser
  manyIndent (ppLine >> checkColGe >> ppGroup
    (structAnnotatedExplicitBinder <|> structAnnotatedImplicitBinder <|>
      structAnnotatedInstBinder <|> structAnnotatedSimpleField <|>
      Command.structExplicitBinder <|> Command.structImplicitBinder <|>
      Command.structInstBinder <|> Command.structSimpleBinder))

@[expose] def hasAnnotatedStructField (fields : Syntax) : Bool :=
  fields[0].getArgs.any fun f => isAnnotatedStructFieldKind f.getKind

@[expose] def annotatedStructureDecl := leading_parser
  (Command.structureTk <|> Command.classTk) >> Command.declId >>
  ppIndent (Command.optDeclSig >> optional Command.extends) >>
  (" := " <|> " where ") >> optional Command.structCtor >> annotatedStructFields >>
  checkStackTop hasAnnotatedStructField "annotated structure field" >>
  Command.optDeriving

@[expose] def annotatedStructure := leading_parser
  Command.declModifiers false >> annotatedStructureDecl

@[expose] def ctorExplicitBinder := leading_parser
  "(" >> fieldModePrefix >> many1 Term.binderIdent >> Term.optType >> ")"

@[expose] def ctorImplicitBinder := leading_parser
  "{" >> fieldModePrefix >> many1 Term.binderIdent >> Term.optType >> "}"

@[expose] def ctorStrictImplicitBinder := leading_parser
  Term.strictImplicitLeftBracket >> fieldModePrefix >> many1 Term.binderIdent >> Term.optType >>
  Term.strictImplicitRightBracket

@[expose] def ctorInstBinder := leading_parser
  "[" >> fieldModePrefix >> optional (atomic (ident >> " : ")) >> termParser >> "]"

@[expose] def ctorAnnotatedBinder :=
  ctorExplicitBinder <|> ctorStrictImplicitBinder <|> ctorImplicitBinder <|> ctorInstBinder

@[expose] def isCtorAnnotatedBinderKind (k : SyntaxNodeKind) : Bool :=
  k == ``ctorExplicitBinder || k == ``ctorImplicitBinder ||
  k == ``ctorStrictImplicitBinder || k == ``ctorInstBinder

@[expose] def ctorFieldArrow := leading_parser
  (atomic ctorAnnotatedBinder <|> Term.bracketedBinder true <|> termParser 26) >>
  unicodeSymbol " → " " -> "

@[expose] def ctorTypeSpec := leading_parser
  " : " >> many (atomic ctorFieldArrow) >> termParser

@[expose] def ctorOptDeclSig := leading_parser
  many (ppSpace >> (atomic ctorAnnotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >>
  optional ctorTypeSpec

@[expose] def annotatedCtor := leading_parser
  atomic (optional Command.docComment >> "\n| ") >>
  ppGroup (Command.declModifiers true >> rawIdent >> ctorOptDeclSig)

@[expose] def ctorHasFieldAnnotation (ctor : Syntax) : Bool :=
  let sig := ctor[4]
  let bindersAnn := sig[0].getArgs.any fun b => isCtorAnnotatedBinderKind b.getKind
  let arrowsAnn := !sig[1].isNone &&
    sig[1][0][1].getArgs.any fun arr => isCtorAnnotatedBinderKind arr[0].getKind
  bindersAnn || arrowsAnn

@[expose] def hasAnnotatedInductiveCtor (ctors : Syntax) : Bool :=
  ctors.getArgs.any ctorHasFieldAnnotation

@[expose] def annotatedInductiveDecl := leading_parser
  "inductive " >> Command.declId >> ppIndent Command.optDeclSig >>
  optional (" :=" <|> " where") >> many annotatedCtor >>
  checkStackTop hasAnnotatedInductiveCtor "annotated inductive field" >>
  optional (ppDedent ppLine >> Command.computedFields) >> Command.optDeriving

@[expose] def annotatedInductive := leading_parser
  Command.declModifiers false >> annotatedInductiveDecl

/-! ### Internal programmatic elaboration node (NEVER exported as a parser) -/

@[expose] def annotatedType := leading_parser
  nonReservedSymbol "__ix_binder_internal" >> numLit >> ident >> numLit >> numLit >> numLit >>
  "(" >> termParser >> ")"

/-! ### Scoped `DefAsserts` attribute parsers (ZERO `TokenTable` entries) -/

@[expose] def ix_modes_no_rc := leading_parser nonReservedSymbol "no_rc"
@[expose] def ix_modes_no_alloc := leading_parser nonReservedSymbol "no_alloc"
@[expose] def ix_modes_bounded_stack := leading_parser nonReservedSymbol "bounded_stack"

-- Register syntax node kinds locally without exporting ANY global parser.
section
attribute [local term_parser] annotatedType annotatedFun annotatedForall annotatedDepArrow annotatedArrow annotatedLet
attribute [local doElem_parser] doAnnotatedLet
attribute [local command_parser] declaration annotatedStructure annotatedInductive
attribute [local attr_parser] ix_modes_no_rc ix_modes_no_alloc ix_modes_bounded_stack
end

end Ix.Compile.SourceSyntax

end
