/-
  Ix.Frontend.Format: Pure, Total Surface Syntax Pretty-Printer & Round-Trip Formatter
  for the Ix Frontend and `IxVCS` Merge Engine.

  Features:
  - 100% pure, total, and kernel-reducible (`Nat.rec` / `List.rec` structural recursion,
    using `strAppendPure` and `strIntercalatePure` with zero `@[extern]` blockers).
  - Formats `Ix.Syntax` (`formatSyntax`), `ModuleSchedule` (`formatModuleSchedule`),
    and `MergeOutcome` (`formatMergeOutcome`) back to valid, re-parseable `.ix` / `.lean`
    surface text, including first-class `.#merge` identifiers (`foo.#merge._1`),
    substructural contracts (`0`, `1`, `&`, `!`, `~`, `let borrow`), tactics, macros,
    structures, inductives, and `#merge ... end` blocks.
-/
module

public import Ix.Frontend.Merge

@[expose] public section

namespace Ix.Frontend

open Ix.Frontend.Parser
open Ix.Frontend.Elab

/-! ## String & Identifier Escaping Helpers -/

/-- Escape special characters inside a string literal. -/
def escapeStringChars : List Char → List Char
  | [] => []
  | '"'  :: cs => '\\' :: '"'  :: escapeStringChars cs
  | '\\' :: cs => '\\' :: '\\' :: escapeStringChars cs
  | '\n' :: cs => '\\' :: 'n'  :: escapeStringChars cs
  | '\t' :: cs => '\\' :: 't'  :: escapeStringChars cs
  | '\r' :: cs => '\\' :: 'r'  :: escapeStringChars cs
  | c    :: cs => c :: escapeStringChars cs

def formatStringLiteral (s : String) : String :=
  "\"" ++ String.ofList (escapeStringChars s.toList) ++ "\""

def formatCharLiteral (s : String) : String :=
  match s.toList with
  | ['\''] => "'\\''"
  | ['\\'] => "'\\\\'"
  | ['\n'] => "'\\n'"
  | ['\t'] => "'\\t'"
  | ['\r'] => "'\\r'"
  | c :: _ => "'" ++ String.singleton c ++ "'"
  | []     => "'\\x00'"

/-- True if a single identifier component `part` requires French quotes `«...»`. -/
def componentNeedsEscape (part : String) : Bool :=
  if part == "#merge" || part == "_" then false
  else if defaultKeywords.contains part then true
  else
    match part.toList with
    | [] => true
    | c :: cs => !isIdFirst c || !cs.all isIdRest

/-- Format a hierarchical `Ix.Name` for surface syntax output, preserving `.#merge` segments
    and escaping reserved keyword components with `«...»`. -/
def formatSurfaceName (nm : Ix.Name) : String :=
  if Name.isAnonymous nm then "_"
  else
    let parts := (Name.components nm).map fun p =>
      if componentNeedsEscape p then "«" ++ p ++ "»" else p
    strIntercalatePure "." parts

/-- Join non-empty formatted strings with `sep`. -/
def joinNonEmpty (sep : String) (xs : List String) : String :=
  strIntercalatePure sep (xs.filter (fun s => !(s == "")))

/-- Extract the surface text of a token node (`.atom` or `.ident`). -/
def formatTokenVal : Ix.Syntax → String
  | .atom _ val => val
  | .ident _ _ id _ => strIntercalatePure "." (Name.components id)
  | _ => ""

/-! ## Core Structural `Syntax` Pretty-Printer (`formatSyntaxAux`) -/

/-- Format a list of `Ix.Syntax` nodes using `fmtOne` and join with `sep`. -/
def formatSyntaxList (fmtOne : Ix.Syntax → String) (sep : String) : List Ix.Syntax → String
  | [] => ""
  | [x] => fmtOne x
  | x :: xs => fmtOne x ++ sep ++ formatSyntaxList fmtOne sep xs

/-- Format a contract prefix node (`binderPrefix` or `valuePrefix`), adding a trailing space when non-empty. -/
def formatPrefixSpace (stx : Ix.Syntax) : String :=
  let atoms := (Syntax.getArgs stx).toList.map Syntax.getAtomVal |>.filter (fun s => !(s == ""))
  if atoms.isEmpty then ""
  else strIntercalatePure " " atoms ++ " "

/-- Format universe parameter list `.{u, v}` if non-empty. -/
def formatUnivParamsNode (stx : Ix.Syntax) : String :=
  let args := (Syntax.getArgs stx).toList
  if args.isEmpty then ""
  else
    let names := args.map fun a => formatSurfaceName (Syntax.getId a)
    ".{" ++ strIntercalatePure ", " names ++ "}"

/-- Format declaration modifiers (`@[simp]`, `private`, `protected`, `noncomputable`, etc.). -/
def formatModifiersNode (stx : Ix.Syntax) : String :=
  let args := (Syntax.getArgs stx).toList
  if args.isEmpty then ""
  else
    let attrs := args.filterMap fun a =>
      match a with
      | .ident _ _ id _ => if Name.isAnonymous id then none else some (formatSurfaceName id)
      | _ => none
    let kwMods := args.filterMap fun a =>
      match a with
      | .atom _ v => if v == "" then none else some v
      | _ => none
    let attrPart :=
      if attrs.isEmpty then ""
      else "@[" ++ strIntercalatePure ", " attrs ++ "] "
    let kwPart :=
      if kwMods.isEmpty then ""
      else strIntercalatePure " " kwMods ++ " "
    attrPart ++ kwPart

/-- Main structurally recursive `Ix.Syntax` formatter (`fuel : Nat`). -/
def formatSyntaxAux : Nat → Ix.Syntax → String
  | 0, _ => "_"
  | fuel + 1, stx =>
    let fmt (s : Ix.Syntax) : String := formatSyntaxAux fuel s
    let fmtAtom (s : Ix.Syntax) : String :=
      match s with
      | .node _ k _ =>
        if k == SyntaxKind.appTerm || k == SyntaxKind.binOpTerm || k == SyntaxKind.unaryOpTerm ||
           k == SyntaxKind.arrowTerm || k == SyntaxKind.forallTerm || k == SyntaxKind.funTerm ||
           k == SyntaxKind.letTerm || k == SyntaxKind.letBorrowTerm || k == SyntaxKind.letRecTerm ||
           k == SyntaxKind.haveTerm || k == SyntaxKind.ifTerm || k == SyntaxKind.matchTerm ||
           k == SyntaxKind.byTactic || k == SyntaxKind.calcTerm then
          "(" ++ fmt s ++ ")"
        else fmt s
      | _ => fmt s
    match stx with
    | .missing => ""
    | .atom _ val => val
    | .ident _ _ id _ => formatSurfaceName id
    | .node _ kind args =>
      let argList := args.toList
      let getA (i : Nat) : Ix.Syntax := Syntax.listGetD argList i .missing
      if kind == SyntaxKind.nullKind then
        joinNonEmpty " " (argList.map fmt)
      else if kind == SyntaxKind.moduleKind then
        joinNonEmpty "\n\n" (argList.map fmt)
      else if kind == SyntaxKind.univParamsKind then
        formatUnivParamsNode stx
      else if kind == SyntaxKind.modifiersKind then
        formatModifiersNode stx
      else if kind == SyntaxKind.binderPrefix || kind == SyntaxKind.valuePrefix then
        strIntercalatePure " " (argList.map Syntax.getAtomVal |>.filter (fun s => !(s == "")))
      -- Literals & Atomic Terms
      else if kind == SyntaxKind.hashRef then
        "#" ++ Syntax.getAtomVal (getA 0)
      else if kind == SyntaxKind.numLit then
        Syntax.getAtomVal (getA 0)
      else if kind == SyntaxKind.strLit then
        formatStringLiteral (Syntax.getAtomVal (getA 0))
      else if kind == SyntaxKind.charLit then
        formatCharLiteral (Syntax.getAtomVal (getA 0))
      else if kind == SyntaxKind.holeTerm then
        "_"
      else if kind == SyntaxKind.sorryTerm then
        "sorry"
      else if kind == SyntaxKind.propTerm then
        "Prop"
      else if kind == SyntaxKind.typeTerm then
        let optLvl := getA 1
        if Syntax.isNone optLvl || Syntax.isMissing optLvl then "Type"
        else "Type " ++ fmtAtom optLvl
      else if kind == SyntaxKind.sortTerm then
        let optLvl := getA 1
        if Syntax.isNone optLvl || Syntax.isMissing optLvl then "Sort"
        else "Sort " ++ fmtAtom optLvl
      else if kind == SyntaxKind.antiquotTerm then
        "$" ++ fmt (getA 1)
      else if kind == SyntaxKind.macroCall then
        joinNonEmpty " " (argList.map fmtAtom)
      -- Universe Levels
      else if kind == SyntaxKind.levelAdd then
        "(" ++ fmt (getA 0) ++ " + " ++ fmt (getA 2) ++ ")"
      else if kind == SyntaxKind.levelMax then
        "(max " ++ formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList ++ ")"
      else if kind == SyntaxKind.levelIMax then
        "(imax " ++ formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList ++ ")"
      -- Binders
      else if kind == SyntaxKind.explicitBinder || kind == SyntaxKind.implicitBinder ||
              kind == SyntaxKind.strictImplicitBinder then
        let (openB, closeB) :=
          if kind == SyntaxKind.implicitBinder then ("{", "}")
          else if kind == SyntaxKind.strictImplicitBinder then ("⦃", "⦄")
          else ("(", ")")
        let bPref := formatPrefixSpace (getA 0)
        let ids := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
        let vPref := formatPrefixSpace (getA 2)
        let tyNode := getA 3
        if Syntax.isOfKind tyNode SyntaxKind.binOpTerm &&
           Syntax.getAtomVal (Syntax.getArg tyNode 0) == "_bound" then
          let opSym := Syntax.getAtomVal (Syntax.getArg tyNode 1)
          let rhs := fmt (Syntax.getArg tyNode 2)
          openB ++ bPref ++ ids ++ " " ++ opSym ++ " " ++ rhs ++ closeB
        else if Syntax.isNone tyNode || Syntax.isMissing tyNode then
          openB ++ bPref ++ ids ++ closeB
        else
          openB ++ bPref ++ ids ++ " : " ++ vPref ++ fmt tyNode ++ closeB
      else if kind == SyntaxKind.instBinder then
        let bPref := formatPrefixSpace (getA 0)
        let idNode := Syntax.getArg (getA 1) 0
        let idVal := Syntax.getId idNode
        let vPref := formatPrefixSpace (getA 2)
        let tyStr := fmt (getA 3)
        if Name.isAnonymous idVal then
          "[" ++ bPref ++ vPref ++ tyStr ++ "]"
        else
          "[" ++ bPref ++ formatSurfaceName idVal ++ " : " ++ vPref ++ tyStr ++ "]"
      -- Composite Terms
      else if kind == SyntaxKind.explicitTerm then
        if argList.length >= 3 && Syntax.getAtomVal (getA 0) == "@" then
          let idStr := fmt (getA 1)
          let univStr := formatUnivParamsNode (getA 2)
          "@" ++ idStr ++ univStr
        else
          fmt (getA 0) ++ formatUnivParamsNode (getA 1)
      else if kind == SyntaxKind.parenTerm then
        "(" ++ fmt (getA 1) ++ ")"
      else if kind == SyntaxKind.tupleTerm then
        if argList.length <= 2 then "()"
        else
          let first := fmt (getA 1)
          let rest := formatSyntaxList fmt ", " (Syntax.getArgs (getA 3)).toList
          "(" ++ first ++ ", " ++ rest ++ ")"
      else if kind == SyntaxKind.typeAscription then
        let tStr := fmt (getA 1)
        let vPref := formatPrefixSpace (getA 3)
        let tyStr := fmt (getA 4)
        "(" ++ tStr ++ " : " ++ vPref ++ tyStr ++ ")"
      else if kind == SyntaxKind.listLit then
        "[" ++ formatSyntaxList fmt ", " (Syntax.getArgs (getA 1)).toList ++ "]"
      else if kind == SyntaxKind.anonCtor then
        "⟨" ++ formatSyntaxList fmt ", " (Syntax.getArgs (getA 1)).toList ++ "⟩"
      else if kind == SyntaxKind.structInst then
        let spreadNode := getA 1
        let spreadStr :=
          if Syntax.isNone spreadNode || Syntax.isMissing spreadNode then ""
          else fmt (Syntax.getArg spreadNode 0) ++ " with "
        let assigns := formatSyntaxList fmt ", " (Syntax.getArgs (getA 2)).toList
        "{ " ++ spreadStr ++ assigns ++ " }"
      else if kind == SyntaxKind.structFieldAssign then
        if argList.length >= 4 then
          let fId := fmt (getA 0)
          let bStr := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
          let valStr := fmt (getA 3)
          fId ++ (if bStr == "" then "" else " " ++ bStr) ++ " := " ++ valStr
        else
          fmt (getA 0) ++ " := " ++ fmt (getA 2)
      else if kind == SyntaxKind.projTerm then
        fmtAtom (getA 0) ++ "." ++ fmt (getA 2)
      else if kind == SyntaxKind.appTerm then
        fmt (getA 0) ++ " " ++ fmtAtom (getA 1)
      else if kind == SyntaxKind.binOpTerm then
        "(" ++ fmt (getA 0) ++ " " ++ formatTokenVal (getA 1) ++ " " ++ fmt (getA 2) ++ ")"
      else if kind == SyntaxKind.unaryOpTerm then
        "(" ++ formatTokenVal (getA 0) ++ " " ++ fmtAtom (getA 1) ++ ")"
      else if kind == SyntaxKind.arrowTerm then
        let dom := fmtAtom (getA 0)
        let vPref := formatPrefixSpace (getA 2)
        let cod := fmt (getA 3)
        dom ++ " → " ++ vPref ++ cod
      else if kind == SyntaxKind.forallTerm then
        let firstArg := getA 0
        let kw := formatTokenVal firstArg
        let isKw := kw == "forall" || kw == "∀" || kw == "∃" || kw == "exists"
        if isKw then
          let outKw := if kw == "exists" then "∃" else if kw == "forall" then "∀" else kw
          let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
          let vPref := formatPrefixSpace (getA 3)
          let body := fmt (getA 4)
          outKw ++ " " ++ binders ++ ", " ++ vPref ++ body
        else
          let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 0)).toList
          let vPref := formatPrefixSpace (getA 2)
          let body := fmt (getA 3)
          binders ++ " → " ++ vPref ++ body
      else if kind == SyntaxKind.funTerm then
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
        let body := fmt (getA 3)
        "fun " ++ binders ++ " => " ++ body
      else if kind == SyntaxKind.letTerm then
        let bPref := formatPrefixSpace (getA 1)
        let idStr := fmt (getA 2)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 3)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let optTy := getA 4
        let tyPart :=
          if Syntax.isNone optTy || Syntax.isMissing optTy then ""
          else if Syntax.isOfKind optTy SyntaxKind.nullKind then
            " : " ++ formatPrefixSpace (Syntax.getArg optTy 1) ++ fmt (Syntax.getArg optTy 2)
          else " : " ++ fmt optTy
        let valStr := fmt (getA 6)
        let bodyStr := fmt (getA 8)
        "let " ++ bPref ++ idStr ++ bPart ++ tyPart ++ " := " ++ valStr ++ ";\n" ++ bodyStr
      else if kind == SyntaxKind.letBorrowTerm || kind == SyntaxKind.letRecTerm then
        let kw2 := formatTokenVal (getA 1)
        let bPref := formatPrefixSpace (getA 2)
        let idStr := fmt (getA 3)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 4)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let optTy := getA 5
        let tyPart :=
          if Syntax.isNone optTy || Syntax.isMissing optTy then ""
          else if Syntax.isOfKind optTy SyntaxKind.nullKind then
            " : " ++ formatPrefixSpace (Syntax.getArg optTy 1) ++ fmt (Syntax.getArg optTy 2)
          else " : " ++ fmt optTy
        let valNode := getA 7
        let bodyStr := fmt (getA 9)
        if Syntax.isOfKind valNode SyntaxKind.nullKind then
          let alts := formatSyntaxList fmt "\n" (Syntax.getArgs valNode).toList
          "let " ++ kw2 ++ " " ++ bPref ++ idStr ++ bPart ++ tyPart ++ "\n" ++ alts ++ ";\n" ++ bodyStr
        else
          "let " ++ kw2 ++ " " ++ bPref ++ idStr ++ bPart ++ tyPart ++ " := " ++ fmt valNode ++ ";\n" ++ bodyStr
      else if kind == SyntaxKind.haveTerm then
        if argList.length >= 8 then
          let idStr := fmt (getA 1)
          let optTy := getA 3
          let tyPart := if Syntax.isNone optTy || Syntax.isMissing optTy then "" else " : " ++ fmt optTy
          "have " ++ idStr ++ tyPart ++ " := " ++ fmt (getA 5) ++ ";\n" ++ fmt (getA 7)
        else
          let idStr := fmt (getA 1)
          let optTy := getA 2
          let tyPart :=
            if Syntax.isNone optTy || Syntax.isMissing optTy then ""
            else if Syntax.isOfKind optTy SyntaxKind.nullKind then
              " : " ++ formatPrefixSpace (Syntax.getArg optTy 1) ++ fmt (Syntax.getArg optTy 2)
            else " : " ++ fmt optTy
          "have " ++ idStr ++ tyPart ++ " := " ++ fmt (getA 4) ++ ";\n" ++ fmt (getA 6)
      else if kind == SyntaxKind.ifTerm then
        if argList.length >= 8 then
          let hStr := fmt (getA 1)
          let condStr := fmt (getA 3)
          let thenStr := fmt (getA 5)
          let elseStr := fmt (getA 7)
          "if " ++ hStr ++ " : " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
        else
          let condStr := fmt (getA 2)
          let thenStr := fmt (getA 4)
          let elseStr := fmt (getA 6)
          "if " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
      else if kind == SyntaxKind.matchTerm then
        let discrs := formatSyntaxList fmt ", " (Syntax.getArgs (getA 1)).toList
        let alts := formatSyntaxList fmt "\n" (Syntax.getArgs (getA 3)).toList
        "match " ++ discrs ++ " with\n" ++ alts
      else if kind == SyntaxKind.matchAlt then
        let pats := formatSyntaxList fmt ", " (Syntax.getArgs (getA 1)).toList
        "| " ++ pats ++ " => " ++ fmt (getA 3)
      -- Tactics, `calc`, and `rcases`
      else if kind == SyntaxKind.byTactic then
        if formatTokenVal (getA 0) == "calc" then
          fmt (getA 1)
        else
          "by\n  " ++ fmt (getA 1)
      else if kind == SyntaxKind.tacticSeq then
        formatSyntaxList fmt "; " argList
      else if kind == SyntaxKind.tacticParen then
        "(" ++ fmt (getA 1) ++ ")"
      else if kind == SyntaxKind.tacticFocus then
        "· (" ++ fmt (getA 1) ++ ")"
      else if kind == SyntaxKind.tacticCase || kind == SyntaxKind.tacticAlt then
        let kw := formatTokenVal (getA 0)
        let tagStr := fmt (getA 1)
        let bStr := formatSyntaxList fmt " " (Syntax.getArgs (getA 2)).toList
        let bPart := if bStr == "" then "" else " " ++ bStr
        kw ++ " " ++ tagStr ++ bPart ++ " => " ++ fmt (getA 4)
      else if kind == SyntaxKind.tacticFirst then
        let branches := (Syntax.getArgs (getA 1)).toList.map fun b => "| " ++ fmt (Syntax.getArg b 1)
        "first " ++ strIntercalatePure " " branches
      else if kind == SyntaxKind.tacticTry || kind == SyntaxKind.tacticRepeat ||
              kind == SyntaxKind.tacticAllGoals || kind == SyntaxKind.tacticAnyGoals then
        formatTokenVal (getA 0) ++ " " ++ fmt (getA 1)
      else if kind == SyntaxKind.tacticAndThen then
        fmt (getA 0) ++ " <;> " ++ fmt (getA 2)
      else if kind == SyntaxKind.tacticIntro || kind == SyntaxKind.tacticFunext ||
              kind == SyntaxKind.tacticExt || kind == SyntaxKind.tacticClear ||
              kind == SyntaxKind.tacticRevert || kind == SyntaxKind.tacticSubst then
        let kw := formatTokenVal (getA 0)
        let ids := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
        if ids == "" then kw else kw ++ " " ++ ids
      else if kind == SyntaxKind.tacticRintro then
        let pats := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
        let optTy := getA 2
        let tyPart := if Syntax.getNumArgs optTy >= 2 then " : " ++ fmt (Syntax.getArg optTy 1) else ""
        "rintro" ++ (if pats == "" then "" else " " ++ pats) ++ tyPart
      else if kind == SyntaxKind.tacticRcases then
        let hId := Syntax.getId (getA 1)
        let hPart := if Name.isAnonymous hId then "" else formatSurfaceName hId ++ " : "
        let target := fmt (getA 2)
        let optWith := getA 3
        let withPart := if Syntax.getNumArgs optWith >= 2 then " with " ++ fmt (Syntax.getArg optWith 1) else ""
        "rcases " ++ hPart ++ target ++ withPart
      else if kind == SyntaxKind.tacticObtain then
        let patStr := fmt (getA 1)
        let optTy := getA 2
        let tyPart := if Syntax.getNumArgs optTy >= 2 then " : " ++ fmt (Syntax.getArg optTy 1) else ""
        "obtain " ++ patStr ++ tyPart ++ " := " ++ fmt (getA 4)
      else if kind == SyntaxKind.rcasesPatWildcard then "_"
      else if kind == SyntaxKind.rcasesPatRfl then "rfl"
      else if kind == SyntaxKind.rcasesPatIdent then fmt (getA 0)
      else if kind == SyntaxKind.rcasesPatTuple then
        "⟨" ++ formatSyntaxList fmt ", " (Syntax.getArgs (getA 0)).toList ++ "⟩"
      else if kind == SyntaxKind.rcasesPatAlt then
        "(" ++ formatSyntaxList fmt " | " (Syntax.getArgs (getA 0)).toList ++ ")"
      else if kind == SyntaxKind.tacticCalc || kind == SyntaxKind.calcTerm then
        "calc\n" ++ formatSyntaxList fmt "\n" (Syntax.getArgs (getA 1)).toList
      else if kind == SyntaxKind.calcStep then
        "  " ++ fmt (getA 0) ++ " := " ++ fmt (getA 2)
      else if kind == SyntaxKind.tacticExact || kind == SyntaxKind.tacticApply ||
              kind == SyntaxKind.tacticRefine || kind == SyntaxKind.tacticShow ||
              kind == SyntaxKind.tacticChange then
        formatTokenVal (getA 0) ++ " " ++ fmt (getA 1)
      else if kind == SyntaxKind.tacticRfl || kind == SyntaxKind.tacticConstructor ||
              kind == SyntaxKind.tacticDecide || kind == SyntaxKind.tacticAssumption ||
              kind == SyntaxKind.tacticSorry || kind == SyntaxKind.tacticLeft ||
              kind == SyntaxKind.tacticRight || kind == SyntaxKind.tacticSplit ||
              kind == SyntaxKind.tacticSymm || kind == SyntaxKind.tacticCongr ||
              kind == SyntaxKind.tacticTrivial || kind == SyntaxKind.tacticContradiction ||
              kind == SyntaxKind.tacticExfalso || kind == SyntaxKind.tacticDone ||
              kind == SyntaxKind.tacticRing || kind == SyntaxKind.tacticOmega then
        formatTokenVal (getA 0)
      else if kind == SyntaxKind.tacticNormNum then
        let optAt := getA 1
        let atPart := if Syntax.getNumArgs optAt >= 2 then " at " ++ fmt (Syntax.getArg optAt 1) else ""
        "norm_num" ++ atPart
      else if kind == SyntaxKind.tacticExists then
        let kw := formatTokenVal (getA 0)
        kw ++ " " ++ formatSyntaxList fmt ", " (Syntax.getArgs (getA 1)).toList
      else if kind == SyntaxKind.tacticTrans then
        let optT := getA 1
        let tPart := if Syntax.getNumArgs optT >= 1 then " " ++ fmt (Syntax.getArg optT 0) else ""
        "trans" ++ tPart
      else if kind == SyntaxKind.tacticRwRule then
        let symmNode := getA 0
        let prefixArrow := if Syntax.getNumArgs symmNode >= 1 then "← " else ""
        prefixArrow ++ fmt (getA 1)
      else if kind == SyntaxKind.tacticRw then
        let kw := formatTokenVal (getA 0)
        let rules := formatSyntaxList fmt ", " (Syntax.getArgs (getA 2)).toList
        let optAt := getA 4
        let atPart := if Syntax.getNumArgs optAt >= 2 then " at " ++ fmt (Syntax.getArg optAt 1) else ""
        kw ++ " [" ++ rules ++ "]" ++ atPart
      else if kind == SyntaxKind.tacticSimp || kind == SyntaxKind.tacticDSimp then
        let kw := formatTokenVal (getA 0)
        let onlyPart := if Syntax.getNumArgs (getA 1) >= 1 then " only" else ""
        let rulesBlk := getA 2
        let rulesPart :=
          if Syntax.getNumArgs rulesBlk >= 2 then
            " [" ++ formatSyntaxList fmt ", " (Syntax.getArgs (Syntax.getArg rulesBlk 1)).toList ++ "]"
          else ""
        let optAt := getA 3
        let atPart := if Syntax.getNumArgs optAt >= 2 then " at " ++ fmt (Syntax.getArg optAt 1) else ""
        kw ++ onlyPart ++ rulesPart ++ atPart
      else if kind == SyntaxKind.tacticHave || kind == SyntaxKind.tacticLet then
        let kw := formatTokenVal (getA 0)
        let idStr := fmt (getA 1)
        let optTy := getA 2
        let tyPart := if Syntax.getNumArgs optTy >= 2 then " : " ++ fmt (Syntax.getArg optTy 1) else ""
        kw ++ " " ++ idStr ++ tyPart ++ " := " ++ fmt (getA 4)
      else if kind == SyntaxKind.tacticSuffices then
        let idVal := Syntax.getId (getA 1)
        let idPart := if Name.isAnonymous idVal then "" else formatSurfaceName idVal ++ " : "
        let tyStr := fmt (getA 3)
        let modeKw := formatTokenVal (getA 4)
        "suffices " ++ idPart ++ tyStr ++ " " ++ modeKw ++ " " ++ fmt (getA 5)
      else if kind == SyntaxKind.tacticSpecialize then
        "specialize " ++ fmt (getA 1) ++ " " ++ formatSyntaxList fmtAtom " " (Syntax.getArgs (getA 2)).toList
      else if kind == SyntaxKind.tacticGeneralize then
        let hVal := Syntax.getId (getA 1)
        let hPart := if Name.isAnonymous hVal then "" else formatSurfaceName hVal ++ " : "
        "generalize " ++ hPart ++ fmt (getA 2) ++ " = " ++ fmt (getA 4)
      else if kind == SyntaxKind.tacticByCases then
        let hVal := Syntax.getId (getA 1)
        let hPart := if Name.isAnonymous hVal then "" else formatSurfaceName hVal ++ " : "
        "by_cases " ++ hPart ++ fmt (getA 2)
      else if kind == SyntaxKind.tacticByContra then
        let hVal := Syntax.getId (getA 1)
        if Name.isAnonymous hVal then "by_contra" else "by_contra " ++ formatSurfaceName hVal
      else if kind == SyntaxKind.tacticCases || kind == SyntaxKind.tacticInduction then
        let kw := formatTokenVal (getA 0)
        let target := fmt (getA 1)
        let optWith := getA 2
        if Syntax.getNumArgs optWith >= 2 then
          let alts := formatSyntaxList fmt "\n  " (Syntax.getArgs (Syntax.getArg optWith 1)).toList
          kw ++ " " ++ target ++ " with\n  " ++ alts
        else
          kw ++ " " ++ target
      -- Top-Level Commands
      else if kind == SyntaxKind.importDecl then
        let modStr := fmt (getA 1)
        let pinNode := getA 2
        if Syntax.isOfKind pinNode SyntaxKind.hashRef then
          "import " ++ modStr ++ " @ " ++ fmt pinNode
        else
          "import " ++ modStr
      else if kind == SyntaxKind.hashImport then
        "import " ++ fmt (getA 1)
      else if kind == SyntaxKind.buildMapDecl then
        "map " ++ fmt (getA 1) ++ " := " ++ fmt (getA 3)
      else if kind == SyntaxKind.namespaceDecl then
        "namespace " ++ fmt (getA 1)
      else if kind == SyntaxKind.sectionDecl || kind == SyntaxKind.endDecl then
        let kw := formatTokenVal (getA 0)
        let optId := getA 1
        if Syntax.isNone optId || Syntax.isMissing optId then kw
        else kw ++ " " ++ fmt (Syntax.getArg optId 0)
      else if kind == SyntaxKind.openDecl then
        let nss := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
        let optOnly := getA 2
        if Syntax.isNone optOnly || Syntax.isMissing optOnly then
          "open " ++ nss
        else
          "open " ++ nss ++ " (" ++ formatSyntaxList fmt " " (Syntax.getArgs optOnly).toList ++ ")"
      else if kind == SyntaxKind.variableDecl then
        "variable " ++ formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
      else if kind == SyntaxKind.universeDecl then
        "universe " ++ formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
      else if kind == SyntaxKind.mutualDecl then
        "mutual\n" ++ formatSyntaxList fmt "\n\n" (Syntax.getArgs (getA 1)).toList ++ "\nend"
      else if kind == SyntaxKind.mergeConflictDecl then
        "#merge\n" ++ formatSyntaxList fmt "\n" (Syntax.getArgs (getA 1)).toList ++ "\nend"
      else if kind == SyntaxKind.mergeArm then
        "| " ++ fmt (getA 1) ++ " =>\n  " ++ fmt (getA 3)
      else if kind == SyntaxKind.defDecl || kind == SyntaxKind.abbrevDecl ||
              kind == SyntaxKind.theoremDecl || kind == SyntaxKind.opaqueDecl then
        let mods := formatModifiersNode (getA 0)
        let kw := formatTokenVal (getA 1)
        let outKw := if kw == "lemma" then "theorem" else kw
        let idStr := fmt (getA 2)
        let univs := formatUnivParamsNode (getA 3)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 4)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let vPref := formatPrefixSpace (getA 5)
        let optTy := getA 6
        let tyPart :=
          if Syntax.isNone optTy || Syntax.isMissing optTy then ""
          else " : " ++ vPref ++ fmt optTy
        if argList.length == 8 then
          let alts := formatSyntaxList fmt "\n  " (Syntax.getArgs (getA 7)).toList
          mods ++ outKw ++ " " ++ idStr ++ univs ++ bPart ++ tyPart ++ "\n  " ++ alts
        else
          mods ++ outKw ++ " " ++ idStr ++ univs ++ bPart ++ tyPart ++ " := " ++ fmt (getA 8)
      else if kind == SyntaxKind.axiomDecl then
        let mods := formatModifiersNode (getA 0)
        let idStr := fmt (getA 2)
        let univs := formatUnivParamsNode (getA 3)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 4)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let vPref := formatPrefixSpace (getA 5)
        let tyStr := fmt (getA 6)
        mods ++ "axiom " ++ idStr ++ univs ++ bPart ++ " : " ++ vPref ++ tyStr
      else if kind == SyntaxKind.instanceDecl then
        let mods := formatModifiersNode (getA 0)
        let idVal := Syntax.getId (getA 2)
        let idPart := if Name.isAnonymous idVal then "" else " " ++ formatSurfaceName idVal
        let univs := formatUnivParamsNode (getA 3)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 4)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let vPref := formatPrefixSpace (getA 5)
        let tyStr := fmt (getA 6)
        if formatTokenVal (getA 7) == "where" then
          let assigns := formatSyntaxList fmt "\n  " (Syntax.getArgs (getA 8)).toList
          mods ++ "instance" ++ idPart ++ univs ++ bPart ++ " : " ++ vPref ++ tyStr ++ " where\n  " ++ assigns
        else
          mods ++ "instance" ++ idPart ++ univs ++ bPart ++ " : " ++ vPref ++ tyStr ++ " := " ++ fmt (getA 8)
      else if kind == SyntaxKind.inductiveDecl then
        let mods := formatModifiersNode (getA 0)
        let idStr := fmt (getA 2)
        let univs := formatUnivParamsNode (getA 3)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 4)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let vPref := formatPrefixSpace (getA 5)
        let optTy := getA 6
        let tyPart := if Syntax.isNone optTy || Syntax.isMissing optTy then "" else " : " ++ vPref ++ fmt optTy
        let ctors := formatSyntaxList fmt "\n  " (Syntax.getArgs (getA 7)).toList
        let cPart := if ctors == "" then "" else " where\n  " ++ ctors
        let derivs := formatSyntaxList fmt ", " (Syntax.getArgs (getA 8)).toList
        let dPart := if derivs == "" then "" else "\n  deriving " ++ derivs
        mods ++ "inductive " ++ idStr ++ univs ++ bPart ++ tyPart ++ cPart ++ dPart
      else if kind == SyntaxKind.ctorDecl then
        let idStr := fmt (getA 1)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 2)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let vPref := formatPrefixSpace (getA 3)
        let optTy := getA 4
        let tyPart := if Syntax.isNone optTy || Syntax.isMissing optTy then "" else " : " ++ vPref ++ fmt optTy
        "| " ++ idStr ++ bPart ++ tyPart
      else if kind == SyntaxKind.structureDecl || kind == SyntaxKind.classDecl then
        let mods := formatModifiersNode (getA 0)
        let kw := formatTokenVal (getA 1)
        let idStr := fmt (getA 2)
        let univs := formatUnivParamsNode (getA 3)
        let binders := formatSyntaxList fmt " " (Syntax.getArgs (getA 4)).toList
        let bPart := if binders == "" then "" else " " ++ binders
        let extStr := formatSyntaxList fmt ", " (Syntax.getArgs (getA 5)).toList
        let extPart := if extStr == "" then "" else " extends " ++ extStr
        let vPref := formatPrefixSpace (getA 6)
        let optTy := getA 7
        let tyPart := if Syntax.isNone optTy || Syntax.isMissing optTy then "" else " : " ++ vPref ++ fmt optTy
        let customCtor := getA 8
        let ctorPart :=
          if Syntax.isNone customCtor || Syntax.isMissing customCtor || Name.isAnonymous (Syntax.getId customCtor) then ""
          else "\n  " ++ fmt customCtor ++ " ::"
        let fields := formatSyntaxList fmt "\n  " (Syntax.getArgs (getA 9)).toList
        let fPart := if fields == "" then "" else " where" ++ ctorPart ++ "\n  " ++ fields
        let derivs := formatSyntaxList fmt ", " (Syntax.getArgs (getA 10)).toList
        let dPart := if derivs == "" then "" else "\n  deriving " ++ derivs
        mods ++ kw ++ " " ++ idStr ++ univs ++ bPart ++ extPart ++ tyPart ++ fPart ++ dPart
      else if kind == SyntaxKind.fieldDecl then
        if argList.length >= 8 then
          let openB := formatTokenVal (getA 0)
          let bPref := formatPrefixSpace (getA 1)
          let ids := formatSyntaxList fmt " " (Syntax.getArgs (getA 2)).toList
          let vPref := formatPrefixSpace (getA 4)
          let tyStr := fmt (getA 5)
          let closeB := formatTokenVal (getA 7)
          openB ++ bPref ++ ids ++ " : " ++ vPref ++ tyStr ++ closeB
        else
          let bPref := formatPrefixSpace (getA 0)
          let ids := formatSyntaxList fmt " " (Syntax.getArgs (getA 1)).toList
          let vPref := formatPrefixSpace (getA 3)
          let tyStr := fmt (getA 4)
          let optDef := getA 5
          let defPart := if Syntax.isNone optDef || Syntax.isMissing optDef then "" else " := " ++ fmt optDef
          bPref ++ ids ++ " : " ++ vPref ++ tyStr ++ defPart
      else if kind == SyntaxKind.notationDecl then
        if argList.length >= 6 then
          let fixKw := formatTokenVal (getA 0)
          let precStr := fmt (getA 1)
          let pPart := if precStr == "" then "" else ":" ++ precStr
          let symStr := fmt (getA 2)
          let targetStr := fmt (getA 4)
          fixKw ++ pPart ++ " " ++ symStr ++ " => " ++ targetStr
        else
          let precStr := fmt (getA 1)
          let pPart := if precStr == "" then "" else ":" ++ precStr
          let items := formatSyntaxList fmt " " (Syntax.getArgs (getA 2)).toList
          "notation" ++ pPart ++ " " ++ items ++ " => " ++ fmt (getA 3)
      else if kind == SyntaxKind.macroDecl then
        if formatTokenVal (getA 0) == "macro_rules" then
          let alts := formatSyntaxList fmt "\n  " (Syntax.getArgs (getA 1)).toList
          "macro_rules\n  " ++ alts
        else
          let precStr := fmt (getA 1)
          let pPart := if precStr == "" then "" else ":" ++ precStr
          let items := formatSyntaxList fmt " " (Syntax.getArgs (getA 2)).toList
          "macro" ++ pPart ++ " " ++ items ++ " => " ++ fmt (getA 3)
      else
        joinNonEmpty " " (argList.map fmt)

/-- Format an `Ix.Syntax` tree into a surface `.ix` / `.lean` string. -/
def formatSyntax (fuel : Nat := 1024) (stx : Ix.Syntax) : String :=
  formatSyntaxAux fuel stx

/-- Format a top-level module syntax node into surface text. -/
def formatModule (stx : Ix.Syntax) : String :=
  formatSyntax 1024 stx

/-- Format a `ModuleSchedule` (using `hermeticizeModule` so all scoped namespaces, variables,
    and universes are self-contained on each declaration). -/
def formatModuleSchedule (sched : ModuleSchedule) : String :=
  match hermeticizeModule sched with
  | .ok hSched => formatSyntax 1024 (synthesizeModuleSyntax hSched)
  | .error _   => formatSyntax 1024 (synthesizeModuleSyntax sched)

/-- Format a `MergeOutcome` from `mergeSource2` / `mergeSource3` into `.ix` surface text. -/
def formatMergeOutcome (outcome : MergeOutcome) : String :=
  formatSyntax 1024 outcome.moduleStx

end Ix.Frontend

end
