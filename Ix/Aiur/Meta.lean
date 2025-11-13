import Lean
import Ix.Aiur.Term

namespace Aiur

open Lean Elab Meta

abbrev ElabStxCat name := TSyntax name → TermElabM Expr

declare_syntax_cat                             pattern
syntax ("." noWs)? ident                     : pattern
syntax "_"                                   : pattern
syntax ident "(" pattern (", " pattern)* ")" : pattern
syntax num                                   : pattern
syntax "(" pattern (", " pattern)* ")"       : pattern
syntax "[" pattern (", " pattern)* "]"       : pattern
syntax pattern "|" pattern                   : pattern

def elabListCore (head : α) (tail : Array α) (elabFn : α → TermElabM Expr)
    (listEltType : Expr) (isArray := false) : TermElabM Expr := do
  let mut elaborated := Array.mkEmpty (tail.size + 1)
  elaborated := elaborated.push $ ← elabFn head
  for elt in tail do
    elaborated := elaborated.push $ ← elabFn elt
  if isArray
  then mkArrayLit listEltType elaborated.toList
  else mkListLit listEltType elaborated.toList

def elabList (head : α) (tail : Array α) (elabFn : α → TermElabM Expr)
    (listEltTypeName : Name) (isArray := false) : TermElabM Expr :=
  elabListCore head tail elabFn (mkConst listEltTypeName) isArray

def elabEmptyList (listEltTypeName : Name) : TermElabM Expr :=
  mkListLit (mkConst listEltTypeName) []

def elabG (n : TSyntax `num) : TermElabM Expr :=
  mkAppM ``G.ofNat #[mkNatLit n.getNat]

partial def elabPattern : ElabStxCat `pattern
  | `(pattern| $v:ident($p:pattern $[, $ps:pattern]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr v.getId]
    mkAppM ``Pattern.ref #[g, ← elabList p ps elabPattern ``Pattern]
  | `(pattern| .$i:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
  | `(pattern| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Pattern.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      let g ← mkAppM ``Global.mk #[toExpr name]
      mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
    | _ => throw $ .error i "Illegal pattern name"
  | `(pattern| _) => pure $ mkConst ``Pattern.wildcard
  | `(pattern| $n:num) => do mkAppM ``Pattern.field #[← elabG n]
  | `(pattern| ($p:pattern $[, $ps:pattern]*)) => do
    mkAppM ``Pattern.tuple #[← elabList p ps elabPattern ``Pattern true]
  | `(pattern| [$p:pattern $[, $ps:pattern]*]) => do
    mkAppM ``Pattern.array #[← elabList p ps elabPattern ``Pattern true]
  | `(pattern| $p₁:pattern | $p₂:pattern) => do
    mkAppM ``Pattern.or #[← elabPattern p₁, ← elabPattern p₂]
  | stx => throw $ .error stx "Invalid syntax for pattern"

declare_syntax_cat                               typ
syntax "G"                                     : typ
syntax "(" typ (", " typ)* ")"                 : typ
syntax "[" typ "; " num "]"                    : typ
syntax "&" typ                                 : typ
syntax ("." noWs)? ident                       : typ
syntax "fn" "(" ")" " -> " typ                 : typ
syntax "fn" "(" typ (", " typ)* ")" " -> " typ : typ

partial def elabTyp : ElabStxCat `typ
  | `(typ| G) => pure $ mkConst ``Typ.field
  | `(typ| ($t:typ $[, $ts:typ]*)) => do
    mkAppM ``Typ.tuple #[← elabList t ts elabTyp ``Typ true]
  | `(typ| [$t:typ; $n:num]) => do
    mkAppM ``Typ.array #[← elabTyp t, mkNatLit n.getNat]
  | `(typ| &$t:typ) => do
    mkAppM ``Typ.pointer #[← elabTyp t]
  | `(typ| $[.]?$i:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Typ.dataType #[g]
  | `(typ| fn() -> $t:typ) => do
    mkAppM ``Typ.function #[← elabEmptyList ``Typ, ← elabTyp t]
  | `(typ| fn($t$[, $ts:typ]*) -> $t':typ) => do
    mkAppM ``Typ.function #[← elabList t ts elabTyp ``Typ, ← elabTyp t']
  | stx => throw $ .error stx "Invalid syntax for type"

declare_syntax_cat                                              trm
syntax ("." noWs)? ident                                      : trm
syntax num                                                    : trm
syntax "(" trm (", " trm)* ")"                                : trm
syntax "[" trm (", " trm)* "]"                                : trm
syntax "[" trm "; " num "]"                                   : trm
syntax "return " trm                                          : trm
syntax "let " pattern (":" typ)? " = " trm "; " trm           : trm
syntax "match " trm " { " (pattern " => " trm ", ")+ " }"     : trm
syntax ("." noWs)? ident "(" ")"                              : trm
syntax ("." noWs)? ident "(" trm (", " trm)* ")"              : trm
syntax:50 trm " + " trm                                       : trm
syntax:50 trm " - " trm                                       : trm
syntax trm " * " trm:51                                       : trm
syntax "eq_zero" "(" trm ")"                                  : trm
syntax "proj" "(" trm ", " num ")"                            : trm
syntax trm "[" num "]"                                        : trm
syntax trm "[" num ".." num "]"                               : trm
syntax "set" "(" trm ", " num ", " trm ")"                    : trm
syntax "store" "(" trm ")"                                    : trm
syntax "load" "(" trm ")"                                     : trm
syntax "ptr_val" "(" trm ")"                                  : trm
syntax "assert_eq!" "(" trm ", " trm ")" ";" (trm)?           : trm
syntax trm ": " typ                                           : trm
syntax "io_get_info" "(" trm ")"                              : trm
syntax "io_set_info" "(" trm ", " trm ", " trm ")" ";" (trm)? : trm
syntax "io_read" "(" trm ", " num ")"                         : trm
syntax "io_write" "(" trm ")" ";" (trm)?                      : trm
syntax "u8_bit_decomposition" "(" trm ")"                     : trm
syntax "u8_shift_left" "(" trm ")"                            : trm
syntax "u8_shift_right" "(" trm ")"                           : trm
syntax "u8_xor" "(" trm ", " trm ")"                          : trm
syntax "u8_add" "(" trm ", " trm ")"                          : trm
syntax "dbg!" "(" str (", " trm)? ")" ";" (trm)?              : trm

partial def elabTrm : ElabStxCat `trm
  | `(trm| .$i:ident) => do
    mkAppM ``Term.ref #[← mkAppM ``Global.mk #[toExpr i.getId]]
  | `(trm| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Term.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      mkAppM ``Term.ref #[← mkAppM ``Global.mk #[toExpr name]]
    | _ => throw $ .error i "Illegal name"
  | `(trm| $n:num) => do
    let data ← mkAppM ``Data.field #[← elabG n]
    mkAppM ``Term.data #[data]
  | `(trm| ($t:trm $[, $ts:trm]*)) => do
    if ts.isEmpty then elabTrm t
    else
      let data ← mkAppM ``Data.tuple #[← elabList t ts elabTrm ``Term true]
      mkAppM ``Term.data #[data]
  | `(trm| [$t:trm $[, $ts:trm]*]) => do
    let data ← mkAppM ``Data.array #[← elabList t ts elabTrm ``Term true]
    mkAppM ``Term.data #[data]
  | `(trm| [$t:trm; $n:num]) => do
    let ts ← mkArrayLit (mkConst ``Term) (.replicate n.getNat (← elabTrm t))
    let data ← mkAppM ``Data.array #[ts]
    mkAppM ``Term.data #[data]
  | `(trm| return $t:trm) => do
    mkAppM ``Term.ret #[← elabTrm t]
  | `(trm| let $p:pattern $[: $ty:typ]? = $t:trm; $t':trm) => match ty with
    | none => do mkAppM ``Term.let #[← elabPattern p, ← elabTrm t, ← elabTrm t']
    | some ty => do
      let t ← mkAppM ``Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Term.let #[← elabPattern p, t, ← elabTrm t']
  | `(trm| match $t:trm {$[$ps:pattern => $ts:trm,]*}) => do
    let mut prods := Array.mkEmpty (ps.size + 1)
    for (p, t) in ps.zip ts do
      prods := prods.push $ ← mkAppM ``Prod.mk #[← elabPattern p, ← elabTrm t]
    let prodType ← mkAppM ``Prod #[mkConst ``Pattern, mkConst ``Term]
    mkAppM ``Term.match #[← elabTrm t, ← mkListLit prodType prods.toList]
  | `(trm| $[.]?$f:ident ()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Term.app #[g, ← elabEmptyList ``Term]
  | `(trm| $[.]?$f:ident ($a:trm $[, $as:trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Term.app #[g, ← elabList a as elabTrm ``Term]
  | `(trm| $a:trm + $b:trm) => do
    mkAppM ``Term.add #[← elabTrm a, ← elabTrm b]
  | `(trm| $a:trm - $b:trm) => do
    mkAppM ``Term.sub #[← elabTrm a, ← elabTrm b]
  | `(trm| $a:trm * $b:trm) => do
    mkAppM ``Term.mul #[← elabTrm a, ← elabTrm b]
  | `(trm| eq_zero($a:trm)) => do
    mkAppM ``Term.eqZero #[← elabTrm a]
  | `(trm| proj($a:trm, $i:num)) => do
    mkAppM ``Term.proj #[← elabTrm a, toExpr i.getNat]
  | `(trm| $t:trm[$i:num]) => do
    mkAppM ``Term.get #[← elabTrm t, toExpr i.getNat]
  | `(trm| $t:trm[$i:num .. $j:num]) => do
    mkAppM ``Term.slice #[← elabTrm t, toExpr i.getNat, toExpr j.getNat]
  | `(trm| set($a:trm, $i:num, $v:trm)) => do
    mkAppM ``Term.set #[← elabTrm a, toExpr i.getNat, ← elabTrm v]
  | `(trm| store($a:trm)) => do
    mkAppM ``Term.store #[← elabTrm a]
  | `(trm| load($a:trm)) => do
    mkAppM ``Term.load #[← elabTrm a]
  | `(trm| ptr_val($a:trm)) => do
    mkAppM ``Term.ptrVal #[← elabTrm a]
  | `(trm| assert_eq!($a:trm, $b:trm); $[$ret:trm]?) => do
    mkAppM ``Term.assertEq #[← elabTrm a, ← elabTrm b, ← elabRet ret]
  | `(trm| $v:trm : $t:typ) => do
    mkAppM ``Term.ann #[← elabTyp t, ← elabTrm v]
  | `(trm| io_get_info($key:trm)) => do
    mkAppM ``Term.ioGetInfo #[← elabTrm key]
  | `(trm| io_set_info($key:trm, $idx:trm, $len:trm); $[$ret:trm]?) => do
    mkAppM ``Term.ioSetInfo
      #[← elabTrm key, ← elabTrm idx, ← elabTrm len, ← elabRet ret]
  | `(trm| io_read($idx:trm, $len:num)) => do
    mkAppM ``Term.ioRead #[← elabTrm idx, mkNatLit len.getNat]
  | `(trm| io_write($data:trm); $[$ret:trm]?) => do
    mkAppM ``Term.ioWrite #[← elabTrm data, ← elabRet ret]
  | `(trm| u8_bit_decomposition($byte:trm)) => do
    mkAppM ``Term.u8BitDecomposition #[← elabTrm byte]
  | `(trm| u8_shift_left($byte:trm)) => do
    mkAppM ``Term.u8ShiftLeft #[← elabTrm byte]
  | `(trm| u8_shift_right($byte:trm)) => do
    mkAppM ``Term.u8ShiftRight #[← elabTrm byte]
  | `(trm| u8_xor($i:trm, $j:trm)) => do
    mkAppM ``Term.u8Xor #[← elabTrm i, ← elabTrm j]
  | `(trm| u8_add($i:trm, $j:trm)) => do
    mkAppM ``Term.u8Add #[← elabTrm i, ← elabTrm j]
  | `(trm| dbg!($label:str $[, $t:trm]?); $[$ret:trm]?) => do
    let t ← match t with
      | none => mkAppOptM ``Option.none #[some (mkConst ``Term)]
      | some t => mkAppM ``Option.some #[← elabTrm t]
    mkAppM ``Term.debug #[mkStrLit label.getString, t, ← elabRet ret]
  | stx => throw $ .error stx "Invalid syntax for term"
where elabRet : Option (TSyntax `trm) → TermElabM Expr
  | none => pure $ mkConst ``Term.unit
  | some ret => elabTrm ret

declare_syntax_cat                     constructor
syntax ident                         : constructor
syntax ident "(" typ (", " typ)* ")" : constructor

def elabConstructor : ElabStxCat `constructor
  | `(constructor| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Constructor.mk #[toExpr name, ← elabEmptyList ``Typ]
    | _ => throw $ .error i "Illegal constructor name"
  | `(constructor| $i:ident($t:typ$[, $ts:typ]*)) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Constructor.mk #[toExpr name, ← elabList t ts elabTyp ``Typ]
    | _ => throw $ .error i "Illegal constructor name"
  | stx => throw $ .error stx "Invalid syntax for constructor"

declare_syntax_cat                                             data_type
syntax "enum " ident                                         : data_type
syntax "enum " ident "{" constructor (", " constructor)* "}" : data_type

def elabDataType : ElabStxCat `data_type
  | `(data_type| enum $n:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``DataType.mk #[g, ← elabEmptyList ``Constructor]
  | `(data_type| enum $n:ident {$c:constructor $[, $cs:constructor]*}) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``DataType.mk #[g, ← elabList c cs elabConstructor ``Constructor]
  | stx => throw $ .error stx "Invalid syntax for data type"

declare_syntax_cat      bind
syntax ident ": " typ : bind

def elabBind : ElabStxCat `bind
  | `(bind| $i:ident: $t:typ) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Prod.mk #[← mkAppM ``Local.str #[toExpr name], ← elabTyp t]
    | _ => throw $ .error i "Illegal variable name"
  | stx => throw $ .error stx "Invalid syntax for binding"

declare_syntax_cat                                                                              function
syntax ("#[unconstrained] ")? "fn " ident "(" ")" (" -> " typ)? "{" trm "}"                   : function
syntax ("#[unconstrained] ")? "fn " ident "(" bind (", " bind)* ")" (" -> " typ)? "{" trm "}" : function

def elabFunction : ElabStxCat `function
  | `(function| $[#[unconstrained]%$u]? fn $i:ident() $[-> $ty:typ]? {$t:trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    let u := elabUnconstrainedBool u
    mkAppM ``Function.mk #[g, ← mkListLit bindType [], ← elabRetTyp ty, ← elabTrm t, u]
  | `(function| $[#[unconstrained]%$u]? fn $i:ident($b:bind $[, $bs:bind]*) $[-> $ty:typ]? {$t:trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    let u := elabUnconstrainedBool u
    mkAppM ``Function.mk
      #[g, ← elabListCore b bs elabBind bindType, ← elabRetTyp ty, ← elabTrm t, u]
  | stx => throw $ .error stx "Invalid syntax for function"
where
  elabUnconstrainedBool : Option Syntax → Expr
    | none => mkConst ``Bool.false
    | some _ => mkConst ``Bool.true
  elabRetTyp : Option (TSyntax `typ) → TermElabM Expr
    | none => pure $ mkConst ``Typ.unit
    | some typ => elabTyp typ

declare_syntax_cat declaration
syntax function  : declaration
syntax data_type : declaration

def accElabDeclarations (declarations : (Array Expr × Array Expr))
    (stx : TSyntax `declaration) : TermElabM (Array Expr × Array Expr) :=
  let (dataTypes, functions) := declarations
  match stx with
  | `(declaration| $f:function) => do
    pure (dataTypes, functions.push $ ← elabFunction f)
  | `(declaration| $d:data_type) => do
    pure (dataTypes.push $ ← elabDataType d, functions)
  | stx => throw $ .error stx "Invalid syntax for declaration"

declare_syntax_cat    toplevel
syntax declaration* : toplevel

def elabToplevel : ElabStxCat `toplevel
  | `(toplevel| $[$ds:declaration]*) => do
    let (dataTypes, functions) ← ds.foldlM (init := default) accElabDeclarations
    mkAppM ``Toplevel.mk #[
      ← mkListLit (mkConst ``DataType) dataTypes.toList,
      ← mkListLit (mkConst ``Function) functions.toList,
    ]
  | stx => throw $ .error stx "Invalid syntax for toplevel"

elab "⟦" t:toplevel "⟧" : term => elabToplevel t

end Aiur
