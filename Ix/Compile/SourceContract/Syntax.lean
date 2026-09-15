module

public import Lean

/-!
# Binder-prefix grammar

The declaration parser activates only when a header has an annotated binder.
Region names use a contextual raw apostrophe, leaving Lean character literals
unchanged. The elaborator is loaded by importing SourceContract.Elab.
-/

public meta section

namespace Ix.Compile.SourceSyntax

open Lean Parser

@[expose] def regionName := leading_parser rawCh '\'' >> ident

@[expose] def quantity := leading_parser numLit <|> "&"

@[expose] def binderPrefix := leading_parser
  lookahead (regionName <|> rawCh '!' <|> quantity) >>
  optional (rawCh '!' (trailingWs := true)) >>
  optional (notFollowedBy (rawCh '\'') "region name" >> quantity) >>
  optional regionName

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

@[expose] def declarationSignature := leading_parser
  many (ppSpace >> (annotatedBinder <|> Term.bracketedBinder <|> Term.binderIdent)) >> Term.optType

@[expose] def hasAnnotatedBinder (signature : Syntax) : Bool :=
  signature[0].getArgs.any fun binder =>
    binder.isOfKind ``explicitBinder || binder.isOfKind ``implicitBinder ||
    binder.isOfKind ``strictImplicitBinder || binder.isOfKind ``instanceBinder

@[expose] def definition := leading_parser
  "def " >> Command.declId >> ppIndent declarationSignature >>
  checkStackTop hasAnnotatedBinder "annotated binder" >>
  Command.declVal >> Command.optDefDeriving

@[expose] def declaration := leading_parser Command.declModifiers false >> definition

@[expose] def regions := leading_parser
  nonReservedSymbol "regions" (includeIdent := true) >>
  many1 (ppSpace >> regionName) >> " in " >> commandParser

attribute [command_parser 2000] declaration regions

end Ix.Compile.SourceSyntax

end
