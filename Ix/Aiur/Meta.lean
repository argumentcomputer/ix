module
public import Lean.Elab
public import Lean.Elab.Term.TermElabM
public import Ix.Aiur.Stages.Source

/-!
Surface DSL for `Aiur.Source.Toplevel` — direct port of `Ix/Aiur/Meta.lean`
with the `.data`-wrapped tuple/array/field constructors inlined to match
`Aiur.Source.Term`'s flat shape.

Usage:
```
def myProgram : Source.Toplevel := ⟦
  pub fn add(a: G, b: G) -> G {
    a + b
  }
⟧
```
-/

public meta section

namespace Aiur

open Lean Elab Meta Source

abbrev ElabStxCat name := TSyntax name → TermElabM Expr

declare_syntax_cat                               aiur_typ
syntax "G"                                     : aiur_typ
syntax "(" aiur_typ (", " aiur_typ)* ")"     : aiur_typ
syntax "[" aiur_typ "; " num "]"              : aiur_typ
syntax "&" aiur_typ                           : aiur_typ
syntax ("." noWs)? ident                                       : aiur_typ
syntax ("." noWs)? ident "‹" aiur_typ (", " aiur_typ)* "›"   : aiur_typ
syntax "fn" "(" ")" " -> " aiur_typ                                   : aiur_typ
syntax "fn" "(" aiur_typ (", " aiur_typ)* ")" " -> " aiur_typ       : aiur_typ

declare_syntax_cat                                                aiur_pattern
syntax ("." noWs)? ident                                        : aiur_pattern
syntax "_"                                                      : aiur_pattern
syntax ident "(" aiur_pattern (", " aiur_pattern)* ")"        : aiur_pattern
syntax num                                                      : aiur_pattern
syntax "(" aiur_pattern (", " aiur_pattern)* ")"              : aiur_pattern
syntax "[" aiur_pattern (", " aiur_pattern)* "]"              : aiur_pattern
syntax aiur_pattern "|" aiur_pattern                          : aiur_pattern
syntax "&" aiur_pattern                                        : aiur_pattern
syntax ident "‹" aiur_typ (", " aiur_typ)* "›" "." noWs ident
       "(" aiur_pattern (", " aiur_pattern)* ")"              : aiur_pattern
syntax ident "‹" aiur_typ (", " aiur_typ)* "›" "." noWs ident : aiur_pattern

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

partial def elabTyp : ElabStxCat `aiur_typ
  | `(aiur_typ| G) => pure $ mkConst ``Typ.field
  | `(aiur_typ| ($t:aiur_typ $[, $ts:aiur_typ]*)) => do
    mkAppM ``Typ.tuple #[← elabList t ts elabTyp ``Typ true]
  | `(aiur_typ| [$t:aiur_typ; $n:num]) => do
    mkAppM ``Typ.array #[← elabTyp t, mkNatLit n.getNat]
  | `(aiur_typ| &$t:aiur_typ) => do
    mkAppM ``Typ.pointer #[← elabTyp t]
  | `(aiur_typ| $[.]?$i:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Typ.ref #[g]
  | `(aiur_typ| fn() -> $t:aiur_typ) => do
    mkAppM ``Typ.function #[← elabEmptyList ``Typ, ← elabTyp t]
  | `(aiur_typ| fn($t$[, $ts:aiur_typ]*) -> $t':aiur_typ) => do
    mkAppM ``Typ.function #[← elabList t ts elabTyp ``Typ, ← elabTyp t']
  | `(aiur_typ| $[.]?$i:ident‹$t:aiur_typ $[, $ts:aiur_typ]*›) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Typ.app #[g, ← elabList t ts elabTyp ``Typ true]
  | stx => throw $ .error stx "Invalid syntax for type"

partial def elabPattern : ElabStxCat `aiur_pattern
  | `(aiur_pattern| $v:ident($p:aiur_pattern $[, $ps:aiur_pattern]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr v.getId]
    mkAppM ``Pattern.ref #[g, ← elabList p ps elabPattern ``Pattern]
  | `(aiur_pattern| .$i:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
  | `(aiur_pattern| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Pattern.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      let g ← mkAppM ``Global.mk #[toExpr name]
      mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
    | _ => throw $ .error i "Illegal pattern name"
  | `(aiur_pattern| _) => pure $ mkConst ``Pattern.wildcard
  | `(aiur_pattern| $n:num) => do mkAppM ``Pattern.field #[← elabG n]
  | `(aiur_pattern| ($p:aiur_pattern $[, $ps:aiur_pattern]*)) => do
    mkAppM ``Pattern.tuple #[← elabList p ps elabPattern ``Pattern true]
  | `(aiur_pattern| [$p:aiur_pattern $[, $ps:aiur_pattern]*]) => do
    mkAppM ``Pattern.array #[← elabList p ps elabPattern ``Pattern true]
  | `(aiur_pattern| $p₁:aiur_pattern | $p₂:aiur_pattern) => do
    mkAppM ``Pattern.or #[← elabPattern p₁, ← elabPattern p₂]
  | `(aiur_pattern| &$p:aiur_pattern) => do
    mkAppM ``Pattern.pointer #[← elabPattern p]
  | `(aiur_pattern| $tmpl:ident‹$_:aiur_typ $[, $_:aiur_typ]*›.$ctor:ident
        ($p:aiur_pattern $[, $ps:aiur_pattern]*)) => do
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Pattern.ref #[g, ← elabList p ps elabPattern ``Pattern]
  | `(aiur_pattern| $tmpl:ident‹$_:aiur_typ $[, $_:aiur_typ]*›.$ctor:ident) => do
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
  | stx => throw $ .error stx "Invalid syntax for pattern"

declare_syntax_cat                                                              aiur_trm
syntax ("." noWs)? ident                                                      : aiur_trm
syntax num                                                                    : aiur_trm
syntax "(" ")"                                                                : aiur_trm
syntax "(" aiur_trm (", " aiur_trm)* ")"                                    : aiur_trm
syntax "[" aiur_trm (", " aiur_trm)* "]"                                    : aiur_trm
syntax "[" aiur_trm "; " num "]"                                             : aiur_trm
syntax "return " aiur_trm                                                    : aiur_trm
syntax "let " aiur_pattern (":" aiur_typ)? " = " aiur_trm "; " aiur_trm   : aiur_trm
syntax "let " aiur_pattern (":" aiur_typ)? " = " aiur_trm ";"              : aiur_trm
syntax "let " aiur_pattern (":" aiur_typ)? " = " aiur_trm                  : aiur_trm
syntax "match " aiur_trm " { "
       (aiur_pattern " => " aiur_trm ", ")+ " }"                            : aiur_trm
syntax ("." noWs)? ident "(" ")"                                              : aiur_trm
syntax ("." noWs)? ident "(" aiur_trm (", " aiur_trm)* ")"                  : aiur_trm
syntax "#" noWs ("." noWs)? ident "(" ")"                                     : aiur_trm
syntax "#" noWs ("." noWs)? ident "(" aiur_trm (", " aiur_trm)* ")"         : aiur_trm
syntax ident "‹" aiur_typ (", " aiur_typ)* "›" "(" ")"                      : aiur_trm
syntax ident "‹" aiur_typ (", " aiur_typ)* "›" "(" aiur_trm
       (", " aiur_trm)* ")"                                                  : aiur_trm
syntax "#" noWs ident "‹" aiur_typ (", " aiur_typ)* "›" "(" ")"             : aiur_trm
syntax "#" noWs ident "‹" aiur_typ (", " aiur_typ)* "›" "(" aiur_trm
       (", " aiur_trm)* ")"                                                  : aiur_trm
syntax ident "‹" aiur_typ (", " aiur_typ)* "›" "." noWs ident "(" ")"       : aiur_trm
syntax ident "‹" aiur_typ (", " aiur_typ)* "›" "." noWs ident
       "(" aiur_trm (", " aiur_trm)* ")"                                    : aiur_trm
syntax:50 aiur_trm " + " aiur_trm                                           : aiur_trm
syntax:50 aiur_trm " - " aiur_trm                                           : aiur_trm
syntax aiur_trm " * " aiur_trm:51                                           : aiur_trm
syntax "eq_zero" "(" aiur_trm ")"                                            : aiur_trm
syntax "proj" "(" aiur_trm ", " num ")"                                      : aiur_trm
syntax aiur_trm "[" num "]"                                                  : aiur_trm
syntax aiur_trm "[" num ".." num "]"                                         : aiur_trm
syntax "set" "(" aiur_trm ", " num ", " aiur_trm ")"                        : aiur_trm
syntax "store" "(" aiur_trm ")"                                              : aiur_trm
syntax "load" "(" aiur_trm ")"                                               : aiur_trm
syntax "ptr_val" "(" aiur_trm ")"                                            : aiur_trm
syntax "assert_eq!" "(" aiur_trm ", " aiur_trm ")" ";" (aiur_trm)?         : aiur_trm
syntax aiur_trm ": " aiur_typ                                               : aiur_trm
syntax "io_get_info" "(" aiur_trm ")"                                        : aiur_trm
syntax "io_set_info" "(" aiur_trm ", " aiur_trm ", " aiur_trm ")" ";"
       (aiur_trm)?                                                           : aiur_trm
syntax "io_read" "(" aiur_trm ", " num ")"                                   : aiur_trm
syntax "io_write" "(" aiur_trm ")" ";" (aiur_trm)?                          : aiur_trm
syntax "u8_bit_decomposition" "(" aiur_trm ")"                               : aiur_trm
syntax "u8_shift_left" "(" aiur_trm ")"                                      : aiur_trm
syntax "u8_shift_right" "(" aiur_trm ")"                                     : aiur_trm
syntax "u8_xor" "(" aiur_trm ", " aiur_trm ")"                              : aiur_trm
syntax "u8_add" "(" aiur_trm ", " aiur_trm ")"                              : aiur_trm
syntax "u8_sub" "(" aiur_trm ", " aiur_trm ")"                              : aiur_trm
syntax "u8_and" "(" aiur_trm ", " aiur_trm ")"                              : aiur_trm
syntax "u8_or" "(" aiur_trm ", " aiur_trm ")"                               : aiur_trm
syntax "u8_less_than" "(" aiur_trm ", " aiur_trm ")"                        : aiur_trm
syntax "u32_less_than" "(" aiur_trm ", " aiur_trm ")"                       : aiur_trm
syntax "dbg!" "(" str (", " aiur_trm)? ")" ";" (aiur_trm)?                  : aiur_trm

syntax aiur_trm "[" "@" noWs ident "]"                                                              : aiur_trm
syntax "set" "(" aiur_trm ", " "@" noWs ident ", " aiur_trm ")"                                     : aiur_trm
syntax "fold" "(" num ".." num ", " aiur_trm ", " "|" aiur_pattern ", " "@" noWs ident "|" aiur_trm ")" : aiur_trm

partial def elabTrm : ElabStxCat `aiur_trm
  | `(aiur_trm| .$i:ident) => do
    mkAppM ``Source.Term.ref #[← mkAppM ``Global.mk #[toExpr i.getId]]
  | `(aiur_trm| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Source.Term.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      mkAppM ``Source.Term.ref #[← mkAppM ``Global.mk #[toExpr name]]
    | _ => throw $ .error i "Illegal name"
  | `(aiur_trm| $n:num) => do
    -- Aiur.Source.Term has `.field` directly (no `.data` wrapper).
    mkAppM ``Source.Term.field #[← elabG n]
  | `(aiur_trm| ()) => pure $ mkConst ``Source.Term.unit
  | `(aiur_trm| ($t:aiur_trm $[, $ts:aiur_trm]*)) => do
    if ts.isEmpty then elabTrm t
    else
      mkAppM ``Source.Term.tuple #[← elabList t ts elabTrm ``Source.Term true]
  | `(aiur_trm| [$t:aiur_trm $[, $ts:aiur_trm]*]) => do
    mkAppM ``Source.Term.array #[← elabList t ts elabTrm ``Source.Term true]
  | `(aiur_trm| [$t:aiur_trm; $n:num]) => do
    let ts ← mkArrayLit (mkConst ``Source.Term) (.replicate n.getNat (← elabTrm t))
    mkAppM ``Source.Term.array #[ts]
  | `(aiur_trm| return $t:aiur_trm) => do
    mkAppM ``Source.Term.ret #[← elabTrm t]
  | `(aiur_trm| let $p:aiur_pattern $[: $ty:aiur_typ]? = $t:aiur_trm; $t':aiur_trm) =>
    match ty with
    | none => do mkAppM ``Source.Term.let #[← elabPattern p, ← elabTrm t, ← elabTrm t']
    | some ty => do
      let t ← mkAppM ``Source.Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Source.Term.let #[← elabPattern p, t, ← elabTrm t']
  | `(aiur_trm| let $p:aiur_pattern $[: $ty:aiur_typ]? = $t:aiur_trm;) =>
    match ty with
    | none => do mkAppM ``Source.Term.let #[← elabPattern p, ← elabTrm t, mkConst ``Source.Term.unit]
    | some ty => do
      let t ← mkAppM ``Source.Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Source.Term.let #[← elabPattern p, t, mkConst ``Source.Term.unit]
  | `(aiur_trm| let $p:aiur_pattern $[: $ty:aiur_typ]? = $t:aiur_trm) =>
    match ty with
    | none => do mkAppM ``Source.Term.let #[← elabPattern p, ← elabTrm t, mkConst ``Source.Term.unit]
    | some ty => do
      let t ← mkAppM ``Source.Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Source.Term.let #[← elabPattern p, t, mkConst ``Source.Term.unit]
  | `(aiur_trm| match $t:aiur_trm {$[$ps:aiur_pattern => $ts:aiur_trm,]*}) => do
    let mut prods := Array.mkEmpty (ps.size + 1)
    for (p, t) in ps.zip ts do
      prods := prods.push $ ← mkAppM ``Prod.mk #[← elabPattern p, ← elabTrm t]
    let prodType ← mkAppM ``Prod #[mkConst ``Pattern, mkConst ``Source.Term]
    mkAppM ``Source.Term.match #[← elabTrm t, ← mkListLit prodType prods.toList]
  | `(aiur_trm| $[.]?$f:ident ()) => do
    match f.getId with
    | .str .anonymous _ => pure ()
    | _ => logWarningAt f "empty parentheses are not needed; use the name without parentheses"
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, toExpr false]
  | `(aiur_trm| $[.]?$f:ident ($a:aiur_trm $[, $as:aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, toExpr false]
  | `(aiur_trm| #$[.]?$f:ident()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, toExpr true]
  | `(aiur_trm| #$[.]?$f:ident($a:aiur_trm $[, $as:aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, toExpr true]
  | `(aiur_trm| $a:aiur_trm + $b:aiur_trm) => do
    mkAppM ``Source.Term.add #[← elabTrm a, ← elabTrm b]
  | `(aiur_trm| $a:aiur_trm - $b:aiur_trm) => do
    mkAppM ``Source.Term.sub #[← elabTrm a, ← elabTrm b]
  | `(aiur_trm| $a:aiur_trm * $b:aiur_trm) => do
    mkAppM ``Source.Term.mul #[← elabTrm a, ← elabTrm b]
  | `(aiur_trm| eq_zero($a:aiur_trm)) => do
    mkAppM ``Source.Term.eqZero #[← elabTrm a]
  | `(aiur_trm| proj($a:aiur_trm, $i:num)) => do
    mkAppM ``Source.Term.proj #[← elabTrm a, toExpr i.getNat]
  | `(aiur_trm| $t:aiur_trm[$i:num]) => do
    mkAppM ``Source.Term.get #[← elabTrm t, toExpr i.getNat]
  | `(aiur_trm| $t:aiur_trm[$i:num .. $j:num]) => do
    mkAppM ``Source.Term.slice #[← elabTrm t, toExpr i.getNat, toExpr j.getNat]
  | `(aiur_trm| set($a:aiur_trm, $i:num, $v:aiur_trm)) => do
    mkAppM ``Source.Term.set #[← elabTrm a, toExpr i.getNat, ← elabTrm v]
  | `(aiur_trm| store($a:aiur_trm)) => do
    mkAppM ``Source.Term.store #[← elabTrm a]
  | `(aiur_trm| load($a:aiur_trm)) => do
    mkAppM ``Source.Term.load #[← elabTrm a]
  | `(aiur_trm| ptr_val($a:aiur_trm)) => do
    mkAppM ``Source.Term.ptrVal #[← elabTrm a]
  | `(aiur_trm| assert_eq!($a:aiur_trm, $b:aiur_trm); $[$ret:aiur_trm]?) => do
    mkAppM ``Source.Term.assertEq #[← elabTrm a, ← elabTrm b, ← elabRet ret]
  | `(aiur_trm| $v:aiur_trm : $t:aiur_typ) => do
    mkAppM ``Source.Term.ann #[← elabTyp t, ← elabTrm v]
  | `(aiur_trm| io_get_info($key:aiur_trm)) => do
    mkAppM ``Source.Term.ioGetInfo #[← elabTrm key]
  | `(aiur_trm| io_set_info($key:aiur_trm, $idx:aiur_trm, $len:aiur_trm); $[$ret:aiur_trm]?) => do
    mkAppM ``Source.Term.ioSetInfo
      #[← elabTrm key, ← elabTrm idx, ← elabTrm len, ← elabRet ret]
  | `(aiur_trm| io_read($idx:aiur_trm, $len:num)) => do
    mkAppM ``Source.Term.ioRead #[← elabTrm idx, mkNatLit len.getNat]
  | `(aiur_trm| io_write($data:aiur_trm); $[$ret:aiur_trm]?) => do
    mkAppM ``Source.Term.ioWrite #[← elabTrm data, ← elabRet ret]
  | `(aiur_trm| u8_bit_decomposition($byte:aiur_trm)) => do
    mkAppM ``Source.Term.u8BitDecomposition #[← elabTrm byte]
  | `(aiur_trm| u8_shift_left($byte:aiur_trm)) => do
    mkAppM ``Source.Term.u8ShiftLeft #[← elabTrm byte]
  | `(aiur_trm| u8_shift_right($byte:aiur_trm)) => do
    mkAppM ``Source.Term.u8ShiftRight #[← elabTrm byte]
  | `(aiur_trm| u8_xor($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u8Xor #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| u8_add($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u8Add #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| u8_sub($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u8Sub #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| u8_and($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u8And #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| u8_or($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u8Or #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| u8_less_than($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u8LessThan #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| u32_less_than($i:aiur_trm, $j:aiur_trm)) => do
    mkAppM ``Source.Term.u32LessThan #[← elabTrm i, ← elabTrm j]
  | `(aiur_trm| dbg!($label:str $[, $t:aiur_trm]?); $[$ret:aiur_trm]?) => do
    let t ← match t with
      | none => mkAppOptM ``Option.none #[some (mkConst ``Source.Term)]
      | some t => mkAppM ``Option.some #[← elabTrm t]
    mkAppM ``Source.Term.debug #[mkStrLit label.getString, t, ← elabRet ret]
  -- Template function calls: explicit type args are dropped (inferred)
  | `(aiur_trm| $f:ident‹$_:aiur_typ $[, $_:aiur_typ]*›()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, toExpr false]
  | `(aiur_trm| $f:ident‹$_:aiur_typ $[, $_:aiur_typ]*›
                 ($a:aiur_trm $[, $as:aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, toExpr false]
  | `(aiur_trm| #$f:ident‹$_:aiur_typ $[, $_:aiur_typ]*›()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, toExpr true]
  | `(aiur_trm| #$f:ident‹$_:aiur_typ $[, $_:aiur_typ]*›
                 ($a:aiur_trm $[, $as:aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, toExpr true]
  -- Template constructor calls
  | `(aiur_trm| $tmpl:ident‹$_:aiur_typ $[, $_:aiur_typ]*›.$ctor:ident()) => do
    logWarningAt ctor "empty parentheses are not needed; use the name without parentheses"
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, toExpr false]
  | `(aiur_trm| $tmpl:ident‹$_:aiur_typ $[, $_:aiur_typ]*›.$ctor:ident
                 ($a:aiur_trm $[, $as:aiur_trm]*)) => do
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, toExpr false]
  | `(aiur_trm| fold($i .. $j, $init, |$acc, @$v| $body)) => do
    let i := i.getNat
    let j := j.getNat
    let range := if i ≤ j then List.range' i (j - i)
      else (List.range' j (i - j)).reverse
    let mut res := init
    for n in range do
      let body' ← replaceToken v.getId n body
      res ← `(aiur_trm| let $acc = $res; $body')
    elabTrm res
  | `(aiur_trm| $_[@$var]) => throw $ .error var "Unbound macro variable"
  | `(aiur_trm| set($_, @$var, $_)) => throw $ .error var "Unbound macro variable"
  | stx => throw $ .error stx "Invalid syntax for term"
where
  elabRet : Option (TSyntax `aiur_trm) → TermElabM Expr
    | none => pure $ mkConst ``Source.Term.unit
    | some ret => elabTrm ret
  replaceToken (old : Name) (new : Nat) : TSyntax `aiur_trm → TermElabM (TSyntax `aiur_trm)
    | `(aiur_trm| $arr[@$var]) => do
      let arr ← replaceToken old new arr
      if var.getId = old then
        let new := Syntax.mkNatLit new
        `(aiur_trm| $arr[$new])
      else `(aiur_trm| $arr[@$var])
    | `(aiur_trm| set($arr, @$var, $v)) => do
      let arr ← replaceToken old new arr
      let v ← replaceToken old new v
      if var.getId = old then
        let new := Syntax.mkNatLit new
        `(aiur_trm| set($arr, $new, $v))
      else `(aiur_trm| set($arr, @$var, $v))
    | `(aiur_trm| ($t $[, $ts]*)) => do
      let t ← replaceToken old new t
      let ts ← ts.mapM $ replaceToken old new
      `(aiur_trm| ($t $[, $ts]*))
    | `(aiur_trm| [$t $[, $ts]*]) => do
      let t ← replaceToken old new t
      let ts ← ts.mapM $ replaceToken old new
      `(aiur_trm| [$t $[, $ts]*])
    | `(aiur_trm| [$t; $n]) => do
      let t ← replaceToken old new t
      `(aiur_trm| [$t; $n])
    | `(aiur_trm| return $t:aiur_trm) => do
      let t ← replaceToken old new t
      `(aiur_trm| return $t)
    | `(aiur_trm| let $p:aiur_pattern $[: $ty]? = $t:aiur_trm; $t':aiur_trm) => do
      let t ← replaceToken old new t
      let t' ← replaceToken old new t'
      `(aiur_trm| let $p $[: $ty]? = $t; $t')
    | `(aiur_trm| let $p:aiur_pattern $[: $ty]? = $t:aiur_trm;) => do
      let t ← replaceToken old new t
      `(aiur_trm| let $p $[: $ty]? = $t;)
    | `(aiur_trm| let $p:aiur_pattern $[: $ty]? = $t:aiur_trm) => do
      let t ← replaceToken old new t
      `(aiur_trm| let $p $[: $ty]? = $t)
    | `(aiur_trm| match $t:aiur_trm {$[$ps:aiur_pattern => $ts:aiur_trm,]*}) => do
      let t ← replaceToken old new t
      let ts ← ts.mapM $ replaceToken old new
      `(aiur_trm| match $t {$[$ps:aiur_pattern => $ts:aiur_trm,]*})
    | `(aiur_trm| $[.%$dot]?$f:ident ($a:aiur_trm $[, $as:aiur_trm]*)) => do
      let a ← replaceToken old new a
      let as ← as.mapM $ replaceToken old new
      if dot.isSome then `(aiur_trm| .$f:ident ($a $[, $as]*))
      else `(aiur_trm| $f:ident ($a $[, $as]*))
    | `(aiur_trm| #$[.%$dot]?$f:ident($a:aiur_trm $[, $as:aiur_trm]*)) => do
      let a ← replaceToken old new a
      let as ← as.mapM $ replaceToken old new
      if dot.isSome then `(aiur_trm| #.$f:ident($a $[, $as]*))
      else `(aiur_trm| #$f:ident($a $[, $as]*))
    | `(aiur_trm| $a + $b) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(aiur_trm| $a + $b)
    | `(aiur_trm| $a - $b) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(aiur_trm| $a - $b)
    | `(aiur_trm| $a * $b) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(aiur_trm| $a * $b)
    | `(aiur_trm| eq_zero($a:aiur_trm)) => do
      let a ← replaceToken old new a
      `(aiur_trm| eq_zero($a))
    | `(aiur_trm| proj($a:aiur_trm, $i:num)) => do
      let a ← replaceToken old new a
      `(aiur_trm| proj($a, $i))
    | `(aiur_trm| $t:aiur_trm[$i:num]) => do
      let t ← replaceToken old new t
      `(aiur_trm| $t[$i])
    | `(aiur_trm| $t:aiur_trm[$i:num..$j:num]) => do
      let t ← replaceToken old new t
      `(aiur_trm| $t[$i..$j])
    | `(aiur_trm| set($a:aiur_trm, $i:num, $v:aiur_trm)) => do
      let a ← replaceToken old new a
      let v ← replaceToken old new v
      `(aiur_trm| set($a, $i, $v))
    | `(aiur_trm| store($a:aiur_trm)) => do
      let a ← replaceToken old new a
      `(aiur_trm| store($a))
    | `(aiur_trm| load($a:aiur_trm)) => do
      let a ← replaceToken old new a
      `(aiur_trm| load($a))
    | `(aiur_trm| ptr_val($a:aiur_trm)) => do
      let a ← replaceToken old new a
      `(aiur_trm| ptr_val($a))
    | `(aiur_trm| assert_eq!($a:aiur_trm, $b:aiur_trm); $[$ret:aiur_trm]?) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      let ret' ← ret.mapM $ replaceToken old new
      `(aiur_trm| assert_eq!($a, $b); $[$ret']?)
    | `(aiur_trm| $v:aiur_trm : $t:aiur_typ) => do
      let v ← replaceToken old new v
      `(aiur_trm| $v : $t)
    | `(aiur_trm| io_get_info($key:aiur_trm)) => do
      let key ← replaceToken old new key
      `(aiur_trm| io_get_info($key))
    | `(aiur_trm| io_set_info($key:aiur_trm, $idx:aiur_trm, $len:aiur_trm); $[$ret:aiur_trm]?) => do
      let key ← replaceToken old new key
      let idx ← replaceToken old new idx
      let len ← replaceToken old new len
      let ret' ← ret.mapM $ replaceToken old new
      `(aiur_trm| io_set_info($key, $idx, $len); $[$ret']?)
    | `(aiur_trm| io_read($idx:aiur_trm, $len:num)) => do
      let idx ← replaceToken old new idx
      `(aiur_trm| io_read($idx, $len))
    | `(aiur_trm| io_write($data:aiur_trm); $[$ret:aiur_trm]?) => do
      let data ← replaceToken old new data
      let ret' ← ret.mapM $ replaceToken old new
      `(aiur_trm| io_write($data); $[$ret']?)
    | `(aiur_trm| u8_bit_decomposition($byte:aiur_trm)) => do
      let byte ← replaceToken old new byte
      `(aiur_trm| u8_bit_decomposition($byte))
    | `(aiur_trm| u8_shift_left($byte:aiur_trm)) => do
      let byte ← replaceToken old new byte
      `(aiur_trm| u8_shift_left($byte))
    | `(aiur_trm| u8_shift_right($byte:aiur_trm)) => do
      let byte ← replaceToken old new byte
      `(aiur_trm| u8_shift_right($byte))
    | `(aiur_trm| u8_xor($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u8_xor($i, $j))
    | `(aiur_trm| u8_add($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u8_add($i, $j))
    | `(aiur_trm| u8_sub($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u8_sub($i, $j))
    | `(aiur_trm| u8_and($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u8_and($i, $j))
    | `(aiur_trm| u8_or($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u8_or($i, $j))
    | `(aiur_trm| u8_less_than($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u8_less_than($i, $j))
    | `(aiur_trm| u32_less_than($i:aiur_trm, $j:aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(aiur_trm| u32_less_than($i, $j))
    | `(aiur_trm| dbg!($label:str $[, $t:aiur_trm]?); $[$ret:aiur_trm]?) => do
      let t' ← t.mapM $ replaceToken old new
      let ret' ← ret.mapM $ replaceToken old new
      `(aiur_trm| dbg!($label $[, $t']?); $[$ret']?)
    | `(aiur_trm| fold($i .. $j, $init, |$acc, @$v| $body)) => do
      let init ← replaceToken old new init
      -- Don't conflict with shadowing tokens.
      let body ← if v.getId = old then pure body
        else replaceToken old new body
      `(aiur_trm| fold($i .. $j, $init, |$acc, @$v| $body))
    | stx => pure stx

declare_syntax_cat                                aiur_constructor
syntax ident                                    : aiur_constructor
syntax ident "(" aiur_typ (", " aiur_typ)* ")" : aiur_constructor

def elabConstructor : ElabStxCat `aiur_constructor
  | `(aiur_constructor| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Constructor.mk #[toExpr name, ← elabEmptyList ``Typ]
    | _ => throw $ .error i "Illegal constructor name"
  | `(aiur_constructor| $i:ident($t:aiur_typ$[, $ts:aiur_typ]*)) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Constructor.mk #[toExpr name, ← elabList t ts elabTyp ``Typ]
    | _ => throw $ .error i "Illegal constructor name"
  | stx => throw $ .error stx "Invalid syntax for constructor"

def elabTypeParams (head : TSyntax `ident) (tail : Array (TSyntax `ident)) :
    TermElabM (Array String × Expr) := do
  let mut params := #[]
  for p in #[head] ++ tail do
    match p.getId with
    | .str .anonymous name => params := params.push name
    | _ => throw $ .error p "Illegal type parameter name"
  let expr ← mkListLit (mkConst ``String) (params.map toExpr).toList
  pure (params, expr)

declare_syntax_cat                                              aiur_data_type
syntax "enum " ident                                          : aiur_data_type
syntax "enum " ident "{" aiur_constructor
       (", " aiur_constructor)* "}"                          : aiur_data_type
syntax "enum " ident "‹" ident (", " ident)* "›"              : aiur_data_type
syntax "enum " ident "‹" ident (", " ident)* "›" "{"
       aiur_constructor (", " aiur_constructor)* "}"        : aiur_data_type

def elabDataType : ElabStxCat `aiur_data_type
  | `(aiur_data_type| enum $n:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``DataType.mk #[g, ← elabEmptyList ``String, ← elabEmptyList ``Constructor]
  | `(aiur_data_type| enum $n:ident
       {$c:aiur_constructor $[, $cs:aiur_constructor]*}) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``DataType.mk
      #[g, ← elabEmptyList ``String,
        ← elabList c cs elabConstructor ``Constructor]
  | `(aiur_data_type| enum $n:ident‹$p:ident $[, $ps:ident]*›) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    mkAppM ``DataType.mk #[g, paramsExpr, ← elabEmptyList ``Constructor]
  | `(aiur_data_type| enum $n:ident‹$p:ident $[, $ps:ident]*›
       {$c:aiur_constructor $[, $cs:aiur_constructor]*}) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    mkAppM ``DataType.mk
      #[g, paramsExpr, ← elabList c cs elabConstructor ``Constructor]
  | stx => throw $ .error stx "Invalid syntax for data type"

declare_syntax_cat                                                  aiur_type_alias
syntax "type " ident " = " aiur_typ                              : aiur_type_alias
syntax "type " ident "‹" ident (", " ident)* "›" " = " aiur_typ  : aiur_type_alias

def elabTypeAlias : ElabStxCat `aiur_type_alias
  | `(aiur_type_alias| type $n:ident = $t:aiur_typ) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``TypeAlias.mk #[g, ← elabEmptyList ``String, ← elabTyp t]
  | `(aiur_type_alias| type $n:ident‹$p:ident $[, $ps:ident]*› = $t:aiur_typ) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    mkAppM ``TypeAlias.mk #[g, paramsExpr, ← elabTyp t]
  | stx => throw $ .error stx "Invalid syntax for type alias"

declare_syntax_cat            aiur_bind
syntax ident ": " aiur_typ : aiur_bind

def elabBind : ElabStxCat `aiur_bind
  | `(aiur_bind| $i:ident: $t:aiur_typ) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Prod.mk #[← mkAppM ``Local.str #[toExpr name], ← elabTyp t]
    | _ => throw $ .error i "Illegal variable name"
  | stx => throw $ .error stx "Invalid syntax for binding"

declare_syntax_cat                                                                                aiur_function
syntax ("pub ")? "fn " ident "(" ")" (" -> " aiur_typ)? "{" aiur_trm "}"                      : aiur_function
syntax ("pub ")? "fn " ident "(" aiur_bind (", " aiur_bind)* ")"
       (" -> " aiur_typ)? "{" aiur_trm "}"                                                    : aiur_function
syntax "fn " ident "‹" ident (", " ident)* "›" "(" ")"
       (" -> " aiur_typ)? "{" aiur_trm "}"                                                    : aiur_function
syntax "fn " ident "‹" ident (", " ident)* "›"
       "(" aiur_bind (", " aiur_bind)* ")"
       (" -> " aiur_typ)? "{" aiur_trm "}"                                                    : aiur_function

def elabFunction : ElabStxCat `aiur_function
  | `(aiur_function| $[pub%$e]? fn $i:ident() $[-> $ty:aiur_typ]? {$t:aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    let e := elabEntryBool e
    mkAppM ``Source.Function.mono
      #[g, ← mkListLit bindType [], ← elabRetTyp ty, ← elabTrm t, e]
  | `(aiur_function| $[pub%$e]? fn $i:ident($b:aiur_bind $[, $bs:aiur_bind]*)
        $[-> $ty:aiur_typ]? {$t:aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    let e := elabEntryBool e
    mkAppM ``Source.Function.mono
      #[g, ← elabListCore b bs elabBind bindType,
        ← elabRetTyp ty, ← elabTrm t, e]
  | `(aiur_function| fn $i:ident‹$p:ident $[, $ps:ident]*›()
        $[-> $ty:aiur_typ]? {$t:aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    mkAppM ``Source.Function.poly
      #[g, paramsExpr, ← mkListLit bindType [], ← elabRetTyp ty, ← elabTrm t]
  | `(aiur_function| fn $i:ident‹$p:ident $[, $ps:ident]*›
        ($b:aiur_bind $[, $bs:aiur_bind]*)
        $[-> $ty:aiur_typ]? {$t:aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    mkAppM ``Source.Function.poly
      #[g, paramsExpr, ← elabListCore b bs elabBind bindType,
        ← elabRetTyp ty, ← elabTrm t]
  | stx => throw $ .error stx "Invalid syntax for function"
where
  elabEntryBool : Option Syntax → Expr
    | none => mkConst ``Bool.false
    | some _ => mkConst ``Bool.true
  elabRetTyp : Option (TSyntax `aiur_typ) → TermElabM Expr
    | none => pure $ mkConst ``Typ.unit
    | some typ => elabTyp typ

declare_syntax_cat       aiur_declaration
syntax aiur_function   : aiur_declaration
syntax aiur_data_type  : aiur_declaration
syntax aiur_type_alias : aiur_declaration

def accElabDeclarations (declarations : (Array Expr × Array Expr × Array Expr))
    (stx : TSyntax `aiur_declaration) :
    TermElabM (Array Expr × Array Expr × Array Expr) :=
  let (dataTypes, typeAliases, functions) := declarations
  match stx with
  | `(aiur_declaration| $f:aiur_function) => do
    pure (dataTypes, typeAliases, functions.push $ ← elabFunction f)
  | `(aiur_declaration| $d:aiur_data_type) => do
    pure (dataTypes.push $ ← elabDataType d, typeAliases, functions)
  | `(aiur_declaration| $ta:aiur_type_alias) => do
    pure (dataTypes, typeAliases.push $ ← elabTypeAlias ta, functions)
  | stx => throw $ .error stx "Invalid syntax for declaration"

declare_syntax_cat          aiur_toplevel
syntax aiur_declaration* : aiur_toplevel

def elabToplevel : ElabStxCat `aiur_toplevel
  | `(aiur_toplevel| $[$ds:aiur_declaration]*) => do
    let (dataTypes, typeAliases, functions) ←
      ds.foldlM (init := default) accElabDeclarations
    mkAppM ``Source.Toplevel.mk #[
      ← mkArrayLit (mkConst ``DataType) dataTypes.toList,
      ← mkArrayLit (mkConst ``TypeAlias) typeAliases.toList,
      ← mkArrayLit (mkConst ``Source.Function) functions.toList,
    ]
  | stx => throw $ .error stx "Invalid syntax for toplevel"

elab "⟦" t:aiur_toplevel "⟧" : term => elabToplevel t

end Aiur

end
