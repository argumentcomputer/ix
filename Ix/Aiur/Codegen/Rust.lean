/- The Rust syntax subset used by Aiur code generation.

This is a syntax tree, not a Rust type checker. Names and paths are trusted
identifiers supplied by the generator; user-provided text is a string literal.
Executable code has no raw-text escape hatch. Rendering belongs here, not in
bytecode emission. Blocks distinguish statements from a value-producing tail.
-/
module
public import Std

public section
namespace Aiur.Codegen

inductive RustSize where
  | value (n : Nat)
  | named (name : String)
  deriving Inhabited, BEq

inductive RustType where
  | named (name : String)
  | app (name : String) (args : Array RustType)
  | array (elem : RustType) (size : RustSize)
  | slice (elem : RustType)
  | ref (mutable : Bool) (ty : RustType)
  | ptr (mutable : Bool) (ty : RustType)
  | tuple (elems : Array RustType)
  deriving Inhabited, BEq

inductive RustBinOp where
  | add | sub | mul | eq | ne | lt | ge | and | or | bitAnd | bitOr | shl | shr
  deriving Inhabited, BEq

inductive MatchPat where
  | binding (name : String)
  | litU64 (n : Nat)
  | wildcard
  | tuple (elems : Array MatchPat)
  | constructor (path : Array String) (args : Array MatchPat)
  deriving Inhabited, BEq

mutual
inductive RustExpr where
  | var (name : String)
  | nat (n : Nat)
  | bool (b : Bool)
  | string (value : String)
  | path (segments : Array String)
  | call (callee : RustExpr) (args : Array RustExpr)
  | methodCall (receiver : RustExpr) (name : String) (args : Array RustExpr)
  | constGeneric (callee : RustExpr) (args : Array RustExpr)
  | index (arr idx : RustExpr)
  | field (e : RustExpr) (name : String)
  | binop (op : RustBinOp) (a b : RustExpr)
  | deref (e : RustExpr)
  | ref (e : RustExpr)
  | not (e : RustExpr)
  | cast (e : RustExpr) (ty : RustType)
  | tryExpr (e : RustExpr)
  | range (start stop : Option RustExpr)
  | macroCall (name : String) (args : Array RustExpr)
  | arrayLit (elems : Array RustExpr)
  | tuple (elems : Array RustExpr)
  | structLit (path : Array String) (fields : Array (String × RustExpr))
  | block (body : RustBlock)
  | unsafeBlock (body : RustBlock)
  | labeledBlock (label : String) (body : RustBlock)
  | ifExpr (cond : RustExpr) (thenBody elseBody : RustBlock)
  | matchExpr (scrut : RustExpr) (arms : Array MatchArm)
  | closure (params : Array MatchPat) (body : RustExpr)
  deriving Inhabited

inductive RustStmt where
  | letStmt (isMut : Bool) (name : String) (ty : Option RustType) (val : RustExpr)
  | letPattern (pat : MatchPat) (ty : Option RustType) (val : RustExpr)
  | exprStmt (e : RustExpr)
  | returnStmt (e : RustExpr)
  | ifStmt (cond : RustExpr) (thenStmts : Array RustStmt)
      (elseStmts : Option (Array RustStmt))
  | matchStmt (scrut : RustExpr) (arms : Array MatchArm)
  | block (stmts : Array RustStmt)
  | forStmt (pat : MatchPat) (iter : RustExpr) (body : Array RustStmt)
  | breakWith (label : String) (e : RustExpr)
  deriving Inhabited

structure RustBlock where
  stmts : Array RustStmt := #[]
  tail : Option RustExpr := none
  deriving Inhabited

structure MatchArm where
  pat : MatchPat
  guard : Option RustExpr := none
  body : RustBlock
  deriving Inhabited
end

inductive RustVisibility where
  | internal | crate
  deriving Inhabited, BEq

structure RustFunction where
  name : String
  visibility : RustVisibility := .internal
  constParams : Array (String × RustType) := #[]
  params : Array (String × RustType)
  returnTy : RustType
  body : RustBlock
  deriving Inhabited

inductive RustItem where
  | constUsize (name : String) (value : Nat)
  | function (fn : RustFunction)
  deriving Inhabited

/-! ## Rendering -/

private def commaSep (xs : Array String) : String := ", ".intercalate xs.toList
private def tupleText (xs : Array String) : String :=
  "(" ++ commaSep xs ++ (if xs.size == 1 then "," else "") ++ ")"

def RustSize.toStr : RustSize → String
  | .value n => toString n
  | .named n => n

partial def RustType.toStr : RustType → String
  | .named n => n
  | .app n args => n ++ "<" ++ commaSep (args.map RustType.toStr) ++ ">"
  | .array t n => "[" ++ t.toStr ++ "; " ++ n.toStr ++ "]"
  | .slice t => "[" ++ t.toStr ++ "]"
  | .ref isMut t => "&" ++ (if isMut then "mut " else "") ++ t.toStr
  | .ptr isMut t => (if isMut then "*mut " else "*const ") ++ t.toStr
  | .tuple ts => tupleText (ts.map RustType.toStr)

def RustBinOp.toStr : RustBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .ge => ">="
  | .and => "&&" | .or => "||" | .bitAnd => "&" | .bitOr => "|"
  | .shl => "<<" | .shr => ">>"

partial def MatchPat.toStr : MatchPat → String
  | .binding n => n
  | .litU64 n => s!"{n}u64"
  | .wildcard => "_"
  | .tuple ps => tupleText (ps.map MatchPat.toStr)
  | .constructor path ps => "::".intercalate path.toList ++
      "(" ++ commaSep (ps.map MatchPat.toStr) ++ ")"

/-- Escape literal contents once, independently of format-string escaping. -/
private def stringLiteral (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap fun c =>
    match c with
    | '\\' => ['\\', '\\'] | '"' => ['\\', '"']
    | '\n' => ['\\', 'n'] | '\r' => ['\\', 'r'] | '\t' => ['\\', 't']
    | '\x00' => ['\\', '0']
    | c => [c]) ++ "\""

mutual
partial def RustExpr.toStr : RustExpr → String
  | .var n => n
  | .nat n => toString n
  | .bool b => if b then "true" else "false"
  | .string s => stringLiteral s
  | .path p => "::".intercalate p.toList
  | .call f xs =>
    -- Calling a function-valued field is distinct from method dispatch.
    let callee := match f with
      | .field .. => "(" ++ f.toStr ++ ")"
      | _ => f.postfixBase
    callee ++ "(" ++ commaSep (xs.map (·.toStr)) ++ ")"
  | .methodCall e n xs => e.postfixBase ++ "." ++ n ++
      "(" ++ commaSep (xs.map (·.toStr)) ++ ")"
  | .constGeneric f xs => f.postfixBase ++ "::<" ++ commaSep (xs.map (·.toStr)) ++ ">"
  | .index a i => a.postfixBase ++ "[" ++ i.toStr ++ "]"
  | .field e n => e.postfixBase ++ "." ++ n
  | .binop op a b => "(" ++ a.toStr ++ " " ++ op.toStr ++ " " ++ b.toStr ++ ")"
  -- Parenthesize prefix/cast expressions so postfix composition preserves precedence.
  | .deref e => "(*" ++ e.toStr ++ ")"
  | .ref e => "(&" ++ e.toStr ++ ")"
  | .not e => "(!" ++ e.toStr ++ ")"
  | .cast e t => "(" ++ e.toStr ++ " as " ++ t.toStr ++ ")"
  | .tryExpr e => e.postfixBase ++ "?"
  | .range a b => (a.map (·.toStr) |>.getD "") ++ ".." ++
      (b.map (·.toStr) |>.getD "")
  | .macroCall n xs => n ++ "!(" ++ commaSep (xs.map (·.toStr)) ++ ")"
  | .arrayLit xs => "[" ++ commaSep (xs.map (·.toStr)) ++ "]"
  | .tuple xs => tupleText (xs.map (·.toStr))
  | .structLit p fs => "::".intercalate p.toList ++ " { " ++
      commaSep (fs.map fun (n, e) => n ++ ": " ++ e.toStr) ++ " }"
  | .block b => b.toStr
  | .unsafeBlock b => "unsafe " ++ b.toStr
  | .labeledBlock label b => "'" ++ label ++ ": " ++ b.toStr
  | .ifExpr c t e => "if " ++ c.toStr ++ " " ++ t.toStr ++ " else " ++ e.toStr
  | .matchExpr e arms => renderMatch e arms
  | .closure ps e => "|" ++ commaSep (ps.map MatchPat.toStr) ++ "| " ++ e.toStr

/-- A closure or control-flow expression must be grouped before a postfix
    operation; otherwise, for example, a call can attach to the closure body. -/
partial def RustExpr.postfixBase (e : RustExpr) : String :=
  match e with
  | .closure .. | .ifExpr .. | .matchExpr .. | .range .. => "(" ++ e.toStr ++ ")"
  | _ => e.toStr

/-- Generated source stays compact: whitespace separates tokens, but nested
    syntax never expands into additional lines. Each top-level item gets one
    line. String contents are escaped before rendering, not whitespace-stripped. -/
partial def RustBlock.toStr (b : RustBlock) : String :=
  "{ " ++ stmtsToStr b.stmts ++
    (if b.stmts.isEmpty then "" else " ") ++
    (b.tail.map RustExpr.toStr |>.getD "") ++ " }"

partial def renderMatch (scrut : RustExpr) (arms : Array MatchArm) : String :=
  "match " ++ scrut.toStr ++ " { " ++
    commaSep (arms.map fun arm =>
      arm.pat.toStr ++
      (arm.guard.map (fun g => " if " ++ g.toStr) |>.getD "") ++
      " => " ++ arm.body.toStr) ++ (if arms.isEmpty then "" else ",") ++ " }"

partial def RustStmt.toStr : RustStmt → String
  | .letStmt isMut n ty e => "let " ++ (if isMut then "mut " else "") ++ n ++
      (ty.map (fun t => ": " ++ t.toStr) |>.getD "") ++ " = " ++ e.toStr ++ ";"
  | .letPattern p ty e => "let " ++ p.toStr ++
      (ty.map (fun t => ": " ++ t.toStr) |>.getD "") ++ " = " ++ e.toStr ++ ";"
  | .exprStmt e => e.toStr ++ ";"
  | .returnStmt e => "return " ++ e.toStr ++ ";"
  | .ifStmt c t e => "if " ++ c.toStr ++ " " ++
      RustBlock.toStr { stmts := t } ++
      (e.map (fun ss => " else " ++ RustBlock.toStr { stmts := ss }) |>.getD "")
  | .matchStmt e arms => renderMatch e arms
  | .block ss => RustBlock.toStr { stmts := ss }
  | .forStmt p e ss => "for " ++ p.toStr ++ " in " ++ e.toStr ++
      " " ++ RustBlock.toStr { stmts := ss }
  | .breakWith label e => "break '" ++ label ++ " " ++ e.toStr ++ ";"

partial def stmtsToStr (ss : Array RustStmt) : String :=
  " ".intercalate (ss.toList.map RustStmt.toStr)
end

def RustItem.toStr : RustItem → String
  | .constUsize n v => s!"const {n}: usize = {v};\n"
  | .function f =>
    let vis := match f.visibility with | .internal => "" | .crate => "pub(crate) "
    let generics := if f.constParams.isEmpty then "" else
      "<" ++ commaSep (f.constParams.map fun (n, t) => "const " ++ n ++ ": " ++ t.toStr) ++ ">"
    vis ++ "fn " ++ f.name ++ generics ++ "(" ++
      commaSep (f.params.map fun (n, t) => n ++ ": " ++ t.toStr) ++
      (if f.params.isEmpty then "" else ",") ++
      ") -> " ++ f.returnTy.toStr ++ " " ++ f.body.toStr ++ "\n"

end Aiur.Codegen
end
