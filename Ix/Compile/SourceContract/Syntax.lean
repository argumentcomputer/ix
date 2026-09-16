module

public import Lean

/-!
# Binder-prefix grammar

The declaration parser activates only when a header has an annotated binder.
The elaborator is loaded by importing SourceContract.Elab.
-/

public meta section

namespace Ix.Compile.SourceSyntax

open Lean Parser

@[expose] def prefixAtom := leading_parser
  rawCh '!' (trailingWs := true) <|> rawCh '~' (trailingWs := true) <|> numLit <|> "&"

@[expose] def binderPrefix := leading_parser many1 prefixAtom

@[expose] def explicitBinder := leading_parser
  "(" >> binderPrefix >> checkWsBefore "space required before the binder name" >>
  ident >> " : " >> termParser >> ")"

@[expose] def implicitBinder := leading_parser
  "{" >> binderPrefix >> checkWsBefore "space required before the binder name" >>
  ident >> " : " >> termParser >> "}"

@[expose] def strictImplicitBinder := leading_parser
  Term.strictImplicitLeftBracket >> binderPrefix >>
  checkWsBefore "space required before the binder name" >>
  ident >> " : " >> termParser >> Term.strictImplicitRightBracket

@[expose] def instanceBinder := leading_parser
  "[" >> binderPrefix >> checkWsBefore "space required before the binder name" >>
  ident >> " : " >> termParser >> "]"

@[expose] def annotatedBinder :=
  explicitBinder <|> strictImplicitBinder <|> implicitBinder <|> instanceBinder

@[expose] def valueAtom := leading_parser
  rawCh '!' (trailingWs := true) <|> rawCh '~' (trailingWs := true)

@[expose] def valuePrefix := leading_parser many1 valueAtom

@[expose] def resultType := leading_parser " : " >> valuePrefix >> termParser

@[expose] def declarationSignature := leading_parser
  many (ppSpace >> (atomic annotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >>
    (atomic resultType <|> Term.optType)

@[expose] def hasAnnotatedBinder (signature : Syntax) : Bool :=
  signature[0].getArgs.any fun binder =>
    binder.isOfKind ``explicitBinder || binder.isOfKind ``implicitBinder ||
    binder.isOfKind ``strictImplicitBinder || binder.isOfKind ``instanceBinder

@[expose] def definition := leading_parser
  "def " >> Command.declId >> ppIndent declarationSignature >>
  Command.declVal >> Command.optDefDeriving

@[expose] def declaration := leading_parser Command.declModifiers false >> definition

@[expose] def funSignature := leading_parser
  many1 (ppSpace >> (atomic annotatedBinder <|> Term.funBinder)) >> Term.optType

@[expose] def annotatedFun := leading_parser:maxPrec
  unicodeSymbol "λ" "fun" >> funSignature >>
  checkStackTop hasAnnotatedBinder "annotated function binder" >>
  unicodeSymbol " ↦" " =>" >> termParser

@[expose] def forallSignature := leading_parser
  many1 (ppSpace >> (atomic annotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >>
  Term.optType >> ", " >> optional valuePrefix

@[expose] def hasForallContract (signature : Syntax) : Bool :=
  hasAnnotatedBinder signature || !signature[3].isNone

@[expose] def annotatedForall := leading_parser:leadPrec
  unicodeSymbol "∀" "forall" >> forallSignature >>
  checkStackTop hasForallContract "annotated forall" >> termParser

@[expose] def dependentArrowSignature := leading_parser
  (atomic annotatedBinder <|> Term.bracketedBinder true) >>
  unicodeSymbol " → " " -> " >> optional valuePrefix

@[expose] def hasArrowContract (signature : Syntax) : Bool :=
  let binder := signature[0]
  binder.isOfKind ``explicitBinder || binder.isOfKind ``implicitBinder ||
  binder.isOfKind ``strictImplicitBinder || binder.isOfKind ``instanceBinder ||
  !signature[2].isNone

@[expose] def annotatedDepArrow := leading_parser:25
  dependentArrowSignature >> checkStackTop hasArrowContract "annotated arrow" >> termParser

@[expose] def annotatedArrow := trailing_parser
  checkPrec 25 >> unicodeSymbol " → " " -> " >> valuePrefix >> termParser 25

@[expose] def annotatedLet := leading_parser:leadPrec
  withPosition ("let" >> optional "borrow" >> explicitBinder >> " := " >> termParser) >>
  Term.optSemicolon termParser

attribute [term_parser 2000] annotatedFun annotatedForall annotatedDepArrow annotatedArrow annotatedLet

-- Compile parser hooks and register syntax kinds without enabling the general
-- declaration parser in importing modules before its elaborator is available.
section
attribute [local command_parser 2000] declaration
end

end Ix.Compile.SourceSyntax

end
