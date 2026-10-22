module
public import Lean.Elab
public import Lean.Elab.Term.TermElabM
public import LegacyAiur.Stages.Source

/-!
Surface DSL for `LegacyAiur.Source.Toplevel` — direct port of `LegacyAiur/Meta.lean`
with the `.data`-wrapped tuple/array/field constructors inlined to match
`LegacyAiur.Source.Term`'s flat shape.

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

namespace LegacyAiur

open Lean Elab Meta Source

abbrev ElabStxCat name := TSyntax name → TermElabM Expr

declare_syntax_cat                               legacy_aiur_typ
syntax "G"                                     : legacy_aiur_typ
syntax "U8"                                    : legacy_aiur_typ
syntax "(" legacy_aiur_typ (", " legacy_aiur_typ)* ")"     : legacy_aiur_typ
syntax "[" legacy_aiur_typ "; " num "]"              : legacy_aiur_typ
syntax "&" legacy_aiur_typ                           : legacy_aiur_typ
syntax ("." noWs)? ident                                       : legacy_aiur_typ
syntax ("." noWs)? ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›"   : legacy_aiur_typ
syntax "fn" "(" ")" " -> " legacy_aiur_typ                                   : legacy_aiur_typ
syntax "fn" "(" legacy_aiur_typ (", " legacy_aiur_typ)* ")" " -> " legacy_aiur_typ       : legacy_aiur_typ

declare_syntax_cat                                                legacy_aiur_pattern
syntax ("." noWs)? ident                                        : legacy_aiur_pattern
syntax "_"                                                      : legacy_aiur_pattern
syntax ident "(" legacy_aiur_pattern (", " legacy_aiur_pattern)* ")"        : legacy_aiur_pattern
syntax num                                                      : legacy_aiur_pattern
syntax:max num "u8"                                             : legacy_aiur_pattern
syntax "(" legacy_aiur_pattern (", " legacy_aiur_pattern)* ")"              : legacy_aiur_pattern
syntax "[" legacy_aiur_pattern (", " legacy_aiur_pattern)* "]"              : legacy_aiur_pattern
syntax legacy_aiur_pattern "|" legacy_aiur_pattern                          : legacy_aiur_pattern
syntax "&" legacy_aiur_pattern                                        : legacy_aiur_pattern
syntax ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "." noWs ident
       "(" legacy_aiur_pattern (", " legacy_aiur_pattern)* ")"              : legacy_aiur_pattern
syntax ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "." noWs ident : legacy_aiur_pattern

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

partial def elabTyp : ElabStxCat `legacy_aiur_typ
  | `(legacy_aiur_typ| G) => pure $ mkConst ``Typ.field
  | `(legacy_aiur_typ| U8) => pure $ mkConst ``Typ.u8
  | `(legacy_aiur_typ| ($t:legacy_aiur_typ $[, $ts:legacy_aiur_typ]*)) => do
    mkAppM ``Typ.tuple #[← elabList t ts elabTyp ``Typ true]
  | `(legacy_aiur_typ| [$t:legacy_aiur_typ; $n:num]) => do
    mkAppM ``Typ.array #[← elabTyp t, mkNatLit n.getNat]
  | `(legacy_aiur_typ| &$t:legacy_aiur_typ) => do
    mkAppM ``Typ.pointer #[← elabTyp t]
  | `(legacy_aiur_typ| $[.]?$i:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Typ.ref #[g]
  | `(legacy_aiur_typ| fn() -> $t:legacy_aiur_typ) => do
    mkAppM ``Typ.function #[← elabEmptyList ``Typ, ← elabTyp t]
  | `(legacy_aiur_typ| fn($t$[, $ts:legacy_aiur_typ]*) -> $t':legacy_aiur_typ) => do
    mkAppM ``Typ.function #[← elabList t ts elabTyp ``Typ, ← elabTyp t']
  | `(legacy_aiur_typ| $[.]?$i:ident‹$t:legacy_aiur_typ $[, $ts:legacy_aiur_typ]*›) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Typ.app #[g, ← elabList t ts elabTyp ``Typ true]
  | stx => throw $ .error stx "Invalid syntax for type"

partial def elabPattern : ElabStxCat `legacy_aiur_pattern
  | `(legacy_aiur_pattern| $v:ident($p:legacy_aiur_pattern $[, $ps:legacy_aiur_pattern]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr v.getId]
    mkAppM ``Pattern.ref #[g, ← elabList p ps elabPattern ``Pattern]
  | `(legacy_aiur_pattern| .$i:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
  | `(legacy_aiur_pattern| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Pattern.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      let g ← mkAppM ``Global.mk #[toExpr name]
      mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
    | _ => throw $ .error i "Illegal pattern name"
  | `(legacy_aiur_pattern| _) => pure $ mkConst ``Pattern.wildcard
  | `(legacy_aiur_pattern| $n:num) => do mkAppM ``Pattern.field #[← elabG n]
  -- `Nu8` byte-literal pattern: same `Pattern.field` value, kept for clarity
  -- when matching a `U8` scrutinee.
  | `(legacy_aiur_pattern| $n:num u8) => do mkAppM ``Pattern.field #[← elabG n]
  | `(legacy_aiur_pattern| ($p:legacy_aiur_pattern $[, $ps:legacy_aiur_pattern]*)) => do
    mkAppM ``Pattern.tuple #[← elabList p ps elabPattern ``Pattern true]
  | `(legacy_aiur_pattern| [$p:legacy_aiur_pattern $[, $ps:legacy_aiur_pattern]*]) => do
    mkAppM ``Pattern.array #[← elabList p ps elabPattern ``Pattern true]
  | `(legacy_aiur_pattern| $p₁:legacy_aiur_pattern | $p₂:legacy_aiur_pattern) => do
    mkAppM ``Pattern.or #[← elabPattern p₁, ← elabPattern p₂]
  | `(legacy_aiur_pattern| &$p:legacy_aiur_pattern) => do
    mkAppM ``Pattern.pointer #[← elabPattern p]
  | `(legacy_aiur_pattern| $tmpl:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›.$ctor:ident
        ($p:legacy_aiur_pattern $[, $ps:legacy_aiur_pattern]*)) => do
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Pattern.ref #[g, ← elabList p ps elabPattern ``Pattern]
  | `(legacy_aiur_pattern| $tmpl:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›.$ctor:ident) => do
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Pattern.ref #[g, ← elabEmptyList ``Pattern]
  | stx => throw $ .error stx "Invalid syntax for pattern"

declare_syntax_cat                                                              legacy_aiur_trm
syntax ("." noWs)? ident                                                      : legacy_aiur_trm
syntax num                                                                    : legacy_aiur_trm
syntax "(" ")"                                                                : legacy_aiur_trm
syntax "(" legacy_aiur_trm (", " legacy_aiur_trm)* ")"                                    : legacy_aiur_trm
-- Array elements and `return` operands parse at prec 1: it keeps the
-- statement-sequencing rule (prec 0, below `let`) out of expression
-- positions and keeps `[t; n]` replicate vs `[t]` list unambiguous.
syntax "[" legacy_aiur_trm:1 (", " legacy_aiur_trm:1)* "]"                                : legacy_aiur_trm
syntax "[" legacy_aiur_trm:1 "; " num "]"                                           : legacy_aiur_trm
syntax "return " legacy_aiur_trm:1                                                  : legacy_aiur_trm
-- `let` right-hand sides parse at prec 1 so the statement-sequencing rule
-- (prec 0, below) can't swallow the `let`'s own `;` and continuation.
syntax "let " legacy_aiur_pattern (":" legacy_aiur_typ)? " = " legacy_aiur_trm:1 "; " legacy_aiur_trm  : legacy_aiur_trm
syntax "let " legacy_aiur_pattern (":" legacy_aiur_typ)? " = " legacy_aiur_trm:1 ";"            : legacy_aiur_trm
syntax "let " legacy_aiur_pattern (":" legacy_aiur_typ)? " = " legacy_aiur_trm:1                : legacy_aiur_trm
-- Statement sequencing: `t; rest` discards `t`'s value (elaborates to
-- `let _ = t; rest`); trailing `t;` closes the block with `()`. Lets
-- unit-returning calls sit in statement position without `let _ =`.
syntax:0 legacy_aiur_trm "; " (legacy_aiur_trm)?                                          : legacy_aiur_trm
syntax "match " legacy_aiur_trm " { "
       (legacy_aiur_pattern " => " legacy_aiur_trm ", ")+ " }"                            : legacy_aiur_trm
syntax ("." noWs)? ident "(" ")"                                              : legacy_aiur_trm
syntax ("." noWs)? ident "(" legacy_aiur_trm (", " legacy_aiur_trm)* ")"                  : legacy_aiur_trm
syntax "#" noWs ("." noWs)? ident "(" ")"                                     : legacy_aiur_trm
syntax "#" noWs ("." noWs)? ident "(" legacy_aiur_trm (", " legacy_aiur_trm)* ")"         : legacy_aiur_trm
-- Inlined call: `@fn(args)` splices `fn`'s body into the caller at compile
-- time (no separate circuit). Callee must not be inline-recursive.
syntax "@" noWs ("." noWs)? ident "(" ")"                                     : legacy_aiur_trm
syntax "@" noWs ("." noWs)? ident "(" legacy_aiur_trm (", " legacy_aiur_trm)* ")"         : legacy_aiur_trm
syntax ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "(" ")"                      : legacy_aiur_trm
syntax ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "(" legacy_aiur_trm
       (", " legacy_aiur_trm)* ")"                                                  : legacy_aiur_trm
syntax "#" noWs ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "(" ")"             : legacy_aiur_trm
syntax "#" noWs ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "(" legacy_aiur_trm
       (", " legacy_aiur_trm)* ")"                                                  : legacy_aiur_trm
syntax ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "." noWs ident "(" ")"       : legacy_aiur_trm
syntax ident "‹" legacy_aiur_typ (", " legacy_aiur_typ)* "›" "." noWs ident
       "(" legacy_aiur_trm (", " legacy_aiur_trm)* ")"                                    : legacy_aiur_trm
-- Right operands parse at prec 1 (not 0) so the statement-sequencing rule
-- can't swallow `<binop-expr>; rest` from inside the right operand. All
-- other rules have prec ≥ 50, so associativity/precedence are unchanged.
syntax:50 legacy_aiur_trm " + " legacy_aiur_trm:1                                         : legacy_aiur_trm
syntax:50 legacy_aiur_trm " - " legacy_aiur_trm:1                                         : legacy_aiur_trm
syntax legacy_aiur_trm " * " legacy_aiur_trm:51                                           : legacy_aiur_trm
syntax "eq_zero" "(" legacy_aiur_trm ")"                                            : legacy_aiur_trm
syntax "proj" "(" legacy_aiur_trm ", " num ")"                                      : legacy_aiur_trm
syntax legacy_aiur_trm "[" num "]"                                                  : legacy_aiur_trm
syntax legacy_aiur_trm "[" num ".." num "]"                                         : legacy_aiur_trm
syntax "set" "(" legacy_aiur_trm ", " num ", " legacy_aiur_trm ")"                        : legacy_aiur_trm
syntax "store" "(" legacy_aiur_trm ")"                                              : legacy_aiur_trm
syntax "load" "(" legacy_aiur_trm ")"                                               : legacy_aiur_trm
syntax "ptr_val" "(" legacy_aiur_trm ")"                                            : legacy_aiur_trm
syntax "assert_eq!" "(" legacy_aiur_trm ", " legacy_aiur_trm (", " str)? ")" ";" (legacy_aiur_trm)? : legacy_aiur_trm
syntax legacy_aiur_trm ": " legacy_aiur_typ                                               : legacy_aiur_trm
syntax "io_get_info" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                          : legacy_aiur_trm
syntax "io_set_info" "(" legacy_aiur_trm ", " legacy_aiur_trm ", " legacy_aiur_trm ", " legacy_aiur_trm ")" ";"
       (legacy_aiur_trm)?                                                           : legacy_aiur_trm
syntax "io_read" "(" legacy_aiur_trm ", " legacy_aiur_trm ", " num ")"                    : legacy_aiur_trm
syntax "io_write" "(" legacy_aiur_trm ", " legacy_aiur_trm ")" ";" (legacy_aiur_trm)?            : legacy_aiur_trm
syntax "u8_bit_decomposition" "(" legacy_aiur_trm ")"                               : legacy_aiur_trm
syntax "u8_shift_left" "(" legacy_aiur_trm ")"                                      : legacy_aiur_trm
syntax "u8_shift_right" "(" legacy_aiur_trm ")"                                     : legacy_aiur_trm
syntax "u8_xor" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                              : legacy_aiur_trm
syntax "u8_add" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                              : legacy_aiur_trm
syntax "u8_mul" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                              : legacy_aiur_trm
syntax "u8_xor_split7" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                       : legacy_aiur_trm
syntax "u8_xor_split4" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                       : legacy_aiur_trm
syntax "u8_sub" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                              : legacy_aiur_trm
syntax "u8_and" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                              : legacy_aiur_trm
syntax "u8_or" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                               : legacy_aiur_trm
syntax "u8_less_than" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                        : legacy_aiur_trm
syntax "u32_less_than" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                       : legacy_aiur_trm
syntax "unconstrained_u32_add" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"               : legacy_aiur_trm
syntax "unconstrained_u32_add3" "(" legacy_aiur_trm ", " legacy_aiur_trm ", " legacy_aiur_trm ")" : legacy_aiur_trm
syntax "u32_to_field" "(" legacy_aiur_trm ")"                                      : legacy_aiur_trm
syntax "u8_range_check" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"                      : legacy_aiur_trm
syntax "unconstrained_big_uint_div_mod" "(" legacy_aiur_trm ", " legacy_aiur_trm ")"           : legacy_aiur_trm
syntax "unconstrained_g_to_bytes" "(" legacy_aiur_trm ")"                          : legacy_aiur_trm
syntax "unconstrained_g_inverse" "(" legacy_aiur_trm ")"                           : legacy_aiur_trm
syntax "to_field" "(" legacy_aiur_trm ")"                                          : legacy_aiur_trm
syntax "u8_from_field_unsafe" "(" legacy_aiur_trm ")"                              : legacy_aiur_trm
syntax:max num "u8"                                                         : legacy_aiur_trm
syntax "dbg!" "(" str (", " legacy_aiur_trm)? ")" ";" (legacy_aiur_trm)?                  : legacy_aiur_trm

syntax legacy_aiur_trm "[" "@" noWs ident "]"                                                              : legacy_aiur_trm
syntax "set" "(" legacy_aiur_trm ", " "@" noWs ident ", " legacy_aiur_trm ")"                                     : legacy_aiur_trm
syntax "fold" "(" num ".." num ", " legacy_aiur_trm ", " "|" legacy_aiur_pattern ", " "@" noWs ident "|" legacy_aiur_trm ")" : legacy_aiur_trm

partial def elabTrm : ElabStxCat `legacy_aiur_trm
  | `(legacy_aiur_trm| .$i:ident) => do
    mkAppM ``Source.Term.ref #[← mkAppM ``Global.mk #[toExpr i.getId]]
  | `(legacy_aiur_trm| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Source.Term.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      mkAppM ``Source.Term.ref #[← mkAppM ``Global.mk #[toExpr name]]
    | _ => throw $ .error i "Illegal name"
  | `(legacy_aiur_trm| $n:num) => do
    -- LegacyAiur.Source.Term has `.field` directly (no `.data` wrapper).
    mkAppM ``Source.Term.field #[← elabG n]
  | `(legacy_aiur_trm| ()) => pure $ mkConst ``Source.Term.unit
  | `(legacy_aiur_trm| ($t:legacy_aiur_trm $[, $ts:legacy_aiur_trm]*)) => do
    if ts.isEmpty then elabTrm t
    else
      mkAppM ``Source.Term.tuple #[← elabList t ts elabTrm ``Source.Term true]
  | `(legacy_aiur_trm| [$t:legacy_aiur_trm $[, $ts:legacy_aiur_trm]*]) => do
    mkAppM ``Source.Term.array #[← elabList t ts elabTrm ``Source.Term true]
  | `(legacy_aiur_trm| [$t:legacy_aiur_trm; $n:num]) => do
    let ts ← mkArrayLit (mkConst ``Source.Term) (.replicate n.getNat (← elabTrm t))
    mkAppM ``Source.Term.array #[ts]
  | `(legacy_aiur_trm| return $t:legacy_aiur_trm) => do
    mkAppM ``Source.Term.ret #[← elabTrm t]
  | `(legacy_aiur_trm| let $p:legacy_aiur_pattern $[: $ty:legacy_aiur_typ]? = $t:legacy_aiur_trm; $t':legacy_aiur_trm) =>
    match ty with
    | none => do mkAppM ``Source.Term.let #[← elabPattern p, ← elabTrm t, ← elabTrm t']
    | some ty => do
      let t ← mkAppM ``Source.Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Source.Term.let #[← elabPattern p, t, ← elabTrm t']
  | `(legacy_aiur_trm| let $p:legacy_aiur_pattern $[: $ty:legacy_aiur_typ]? = $t:legacy_aiur_trm;) =>
    match ty with
    | none => do mkAppM ``Source.Term.let #[← elabPattern p, ← elabTrm t, mkConst ``Source.Term.unit]
    | some ty => do
      let t ← mkAppM ``Source.Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Source.Term.let #[← elabPattern p, t, mkConst ``Source.Term.unit]
  | `(legacy_aiur_trm| let $p:legacy_aiur_pattern $[: $ty:legacy_aiur_typ]? = $t:legacy_aiur_trm) =>
    match ty with
    | none => do mkAppM ``Source.Term.let #[← elabPattern p, ← elabTrm t, mkConst ``Source.Term.unit]
    | some ty => do
      let t ← mkAppM ``Source.Term.ann #[← elabTyp ty, ← elabTrm t]
      mkAppM ``Source.Term.let #[← elabPattern p, t, mkConst ``Source.Term.unit]
  | `(legacy_aiur_trm| $t:legacy_aiur_trm; $[$t':legacy_aiur_trm]?) => do
    mkAppM ``Source.Term.let
      #[mkConst ``Pattern.wildcard, ← elabTrm t, ← elabRet t']
  | `(legacy_aiur_trm| match $t:legacy_aiur_trm {$[$ps:legacy_aiur_pattern => $ts:legacy_aiur_trm,]*}) => do
    let mut prods := Array.mkEmpty (ps.size + 1)
    for (p, t) in ps.zip ts do
      prods := prods.push $ ← mkAppM ``Prod.mk #[← elabPattern p, ← elabTrm t]
    let prodType ← mkAppM ``Prod #[mkConst ``Pattern, mkConst ``Source.Term]
    mkAppM ``Source.Term.match #[← elabTrm t, ← mkListLit prodType prods.toList]
  | `(legacy_aiur_trm| $[.]?$f:ident ()) => do
    match f.getId with
    | .str .anonymous _ => pure ()
    | _ => logWarningAt f "empty parentheses are not needed; use the name without parentheses"
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, mkConst ``Source.CallMode.normal]
  | `(legacy_aiur_trm| $[.]?$f:ident ($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, mkConst ``Source.CallMode.normal]
  | `(legacy_aiur_trm| #$[.]?$f:ident()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, mkConst ``Source.CallMode.unconstrained]
  | `(legacy_aiur_trm| #$[.]?$f:ident($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, mkConst ``Source.CallMode.unconstrained]
  | `(legacy_aiur_trm| @$[.]?$f:ident()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, mkConst ``Source.CallMode.inlined]
  | `(legacy_aiur_trm| @$[.]?$f:ident($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, mkConst ``Source.CallMode.inlined]
  | `(legacy_aiur_trm| $a:legacy_aiur_trm + $b:legacy_aiur_trm) => do
    mkAppM ``Source.Term.add #[← elabTrm a, ← elabTrm b]
  | `(legacy_aiur_trm| $a:legacy_aiur_trm - $b:legacy_aiur_trm) => do
    mkAppM ``Source.Term.sub #[← elabTrm a, ← elabTrm b]
  | `(legacy_aiur_trm| $a:legacy_aiur_trm * $b:legacy_aiur_trm) => do
    mkAppM ``Source.Term.mul #[← elabTrm a, ← elabTrm b]
  | `(legacy_aiur_trm| eq_zero($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.eqZero #[← elabTrm a]
  | `(legacy_aiur_trm| proj($a:legacy_aiur_trm, $i:num)) => do
    mkAppM ``Source.Term.proj #[← elabTrm a, toExpr i.getNat]
  | `(legacy_aiur_trm| $t:legacy_aiur_trm[$i:num]) => do
    mkAppM ``Source.Term.get #[← elabTrm t, toExpr i.getNat]
  | `(legacy_aiur_trm| $t:legacy_aiur_trm[$i:num .. $j:num]) => do
    mkAppM ``Source.Term.slice #[← elabTrm t, toExpr i.getNat, toExpr j.getNat]
  | `(legacy_aiur_trm| set($a:legacy_aiur_trm, $i:num, $v:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.set #[← elabTrm a, toExpr i.getNat, ← elabTrm v]
  | `(legacy_aiur_trm| store($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.store #[← elabTrm a]
  | `(legacy_aiur_trm| load($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.load #[← elabTrm a]
  | `(legacy_aiur_trm| ptr_val($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.ptrVal #[← elabTrm a]
  | `(legacy_aiur_trm| assert_eq!($a:legacy_aiur_trm, $b:legacy_aiur_trm $[, $msg:str]?); $[$ret:legacy_aiur_trm]?) => do
    let msgExpr ← match msg with
      | some m => mkAppM ``Option.some #[mkStrLit m.getString]
      | none   => mkAppOptM ``Option.none #[Lean.mkConst ``String]
    mkAppM ``Source.Term.assertEq #[← elabTrm a, ← elabTrm b, msgExpr, ← elabRet ret]
  | `(legacy_aiur_trm| $v:legacy_aiur_trm : $t:legacy_aiur_typ) => do
    mkAppM ``Source.Term.ann #[← elabTyp t, ← elabTrm v]
  | `(legacy_aiur_trm| io_get_info($ch:legacy_aiur_trm, $key:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.ioGetInfo #[← elabTrm ch, ← elabTrm key]
  | `(legacy_aiur_trm| io_set_info($ch:legacy_aiur_trm, $key:legacy_aiur_trm, $idx:legacy_aiur_trm, $len:legacy_aiur_trm); $[$ret:legacy_aiur_trm]?) => do
    mkAppM ``Source.Term.ioSetInfo
      #[← elabTrm ch, ← elabTrm key, ← elabTrm idx, ← elabTrm len, ← elabRet ret]
  | `(legacy_aiur_trm| io_read($ch:legacy_aiur_trm, $idx:legacy_aiur_trm, $len:num)) => do
    mkAppM ``Source.Term.ioRead #[← elabTrm ch, ← elabTrm idx, mkNatLit len.getNat]
  | `(legacy_aiur_trm| io_write($ch:legacy_aiur_trm, $data:legacy_aiur_trm); $[$ret:legacy_aiur_trm]?) => do
    mkAppM ``Source.Term.ioWrite #[← elabTrm ch, ← elabTrm data, ← elabRet ret]
  | `(legacy_aiur_trm| u8_bit_decomposition($byte:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8BitDecomposition #[← elabTrm byte]
  | `(legacy_aiur_trm| u8_shift_left($byte:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8ShiftLeft #[← elabTrm byte]
  | `(legacy_aiur_trm| u8_shift_right($byte:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8ShiftRight #[← elabTrm byte]
  | `(legacy_aiur_trm| u8_xor($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8Xor #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_add($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8Add #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_mul($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8Mul #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_xor_split7($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8XorSplit7 #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_xor_split4($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8XorSplit4 #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_sub($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8Sub #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_and($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8And #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_or($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8Or #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u8_less_than($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8LessThan #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| u32_less_than($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u32LessThan #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| unconstrained_u32_add($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.unconstrainedU32Add #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| unconstrained_u32_add3($i:legacy_aiur_trm, $j:legacy_aiur_trm, $k:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.unconstrainedU32Add3 #[← elabTrm i, ← elabTrm j, ← elabTrm k]
  | `(legacy_aiur_trm| u32_to_field($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u32ToField #[← elabTrm a]
  | `(legacy_aiur_trm| u8_range_check($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8RangeCheck #[← elabTrm i, ← elabTrm j]
  | `(legacy_aiur_trm| unconstrained_big_uint_div_mod($a:legacy_aiur_trm, $b:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.unconstrainedBigUintDivMod #[← elabTrm a, ← elabTrm b]
  | `(legacy_aiur_trm| unconstrained_g_to_bytes($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.unconstrainedGToBytes #[← elabTrm a]
  | `(legacy_aiur_trm| unconstrained_g_inverse($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.unconstrainedGInverse #[← elabTrm a]
  | `(legacy_aiur_trm| to_field($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.toField #[← elabTrm a]
  | `(legacy_aiur_trm| u8_from_field_unsafe($a:legacy_aiur_trm)) => do
    mkAppM ``Source.Term.u8FromFieldUnsafe #[← elabTrm a]
  | `(legacy_aiur_trm| $n:num u8) => do
    mkAppM ``Source.Term.u8Lit #[mkNatLit n.getNat]
  | `(legacy_aiur_trm| dbg!($label:str $[, $t:legacy_aiur_trm]?); $[$ret:legacy_aiur_trm]?) => do
    let t ← match t with
      | none => mkAppOptM ``Option.none #[some (mkConst ``Source.Term)]
      | some t => mkAppM ``Option.some #[← elabTrm t]
    mkAppM ``Source.Term.debug #[mkStrLit label.getString, t, ← elabRet ret]
  -- Template function calls: explicit type args are dropped (inferred)
  | `(legacy_aiur_trm| $f:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, mkConst ``Source.CallMode.normal]
  | `(legacy_aiur_trm| $f:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›
                 ($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, mkConst ``Source.CallMode.normal]
  | `(legacy_aiur_trm| #$f:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, mkConst ``Source.CallMode.unconstrained]
  | `(legacy_aiur_trm| #$f:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›
                 ($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, mkConst ``Source.CallMode.unconstrained]
  -- Template constructor calls
  | `(legacy_aiur_trm| $tmpl:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›.$ctor:ident()) => do
    logWarningAt ctor "empty parentheses are not needed; use the name without parentheses"
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Source.Term.app #[g, ← elabEmptyList ``Source.Term, mkConst ``Source.CallMode.normal]
  | `(legacy_aiur_trm| $tmpl:ident‹$_:legacy_aiur_typ $[, $_:legacy_aiur_typ]*›.$ctor:ident
                 ($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
    let name := tmpl.getId ++ ctor.getId
    let g ← mkAppM ``Global.mk #[toExpr name]
    mkAppM ``Source.Term.app #[g, ← elabList a as elabTrm ``Source.Term, mkConst ``Source.CallMode.normal]
  | `(legacy_aiur_trm| fold($i .. $j, $init, |$acc, @$v| $body)) => do
    let i := i.getNat
    let j := j.getNat
    let range := if i ≤ j then List.range' i (j - i)
      else (List.range' j (i - j)).reverse
    let mut res := init
    for n in range do
      let body' ← replaceToken v.getId n body
      res ← `(legacy_aiur_trm| let $acc = $res; $body')
    elabTrm res
  | `(legacy_aiur_trm| $_[@$var]) => throw $ .error var "Unbound macro variable"
  | `(legacy_aiur_trm| set($_, @$var, $_)) => throw $ .error var "Unbound macro variable"
  | stx => throw $ .error stx "Invalid syntax for term"
where
  elabRet : Option (TSyntax `legacy_aiur_trm) → TermElabM Expr
    | none => pure $ mkConst ``Source.Term.unit
    | some ret => elabTrm ret
  replaceToken (old : Name) (new : Nat) : TSyntax `legacy_aiur_trm → TermElabM (TSyntax `legacy_aiur_trm)
    | `(legacy_aiur_trm| $arr[@$var]) => do
      let arr ← replaceToken old new arr
      if var.getId = old then
        let new := Syntax.mkNatLit new
        `(legacy_aiur_trm| $arr[$new])
      else `(legacy_aiur_trm| $arr[@$var])
    | `(legacy_aiur_trm| set($arr, @$var, $v)) => do
      let arr ← replaceToken old new arr
      let v ← replaceToken old new v
      if var.getId = old then
        let new := Syntax.mkNatLit new
        `(legacy_aiur_trm| set($arr, $new, $v))
      else `(legacy_aiur_trm| set($arr, @$var, $v))
    | `(legacy_aiur_trm| ($t $[, $ts]*)) => do
      let t ← replaceToken old new t
      let ts ← ts.mapM $ replaceToken old new
      `(legacy_aiur_trm| ($t $[, $ts]*))
    | `(legacy_aiur_trm| [$t $[, $ts]*]) => do
      let t ← replaceToken old new t
      let ts ← ts.mapM $ replaceToken old new
      `(legacy_aiur_trm| [$t $[, $ts]*])
    | `(legacy_aiur_trm| [$t; $n]) => do
      let t ← replaceToken old new t
      `(legacy_aiur_trm| [$t; $n])
    | `(legacy_aiur_trm| return $t:legacy_aiur_trm) => do
      let t ← replaceToken old new t
      `(legacy_aiur_trm| return $t)
    | `(legacy_aiur_trm| let $p:legacy_aiur_pattern $[: $ty]? = $t:legacy_aiur_trm; $t':legacy_aiur_trm) => do
      let t ← replaceToken old new t
      let t' ← replaceToken old new t'
      `(legacy_aiur_trm| let $p $[: $ty]? = $t; $t')
    | `(legacy_aiur_trm| let $p:legacy_aiur_pattern $[: $ty]? = $t:legacy_aiur_trm;) => do
      let t ← replaceToken old new t
      `(legacy_aiur_trm| let $p $[: $ty]? = $t;)
    | `(legacy_aiur_trm| let $p:legacy_aiur_pattern $[: $ty]? = $t:legacy_aiur_trm) => do
      let t ← replaceToken old new t
      `(legacy_aiur_trm| let $p $[: $ty]? = $t)
    | `(legacy_aiur_trm| match $t:legacy_aiur_trm {$[$ps:legacy_aiur_pattern => $ts:legacy_aiur_trm,]*}) => do
      let t ← replaceToken old new t
      let ts ← ts.mapM $ replaceToken old new
      `(legacy_aiur_trm| match $t {$[$ps:legacy_aiur_pattern => $ts:legacy_aiur_trm,]*})
    | `(legacy_aiur_trm| $[.%$dot]?$f:ident ($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
      let a ← replaceToken old new a
      let as ← as.mapM $ replaceToken old new
      if dot.isSome then `(legacy_aiur_trm| .$f:ident ($a $[, $as]*))
      else `(legacy_aiur_trm| $f:ident ($a $[, $as]*))
    | `(legacy_aiur_trm| #$[.%$dot]?$f:ident($a:legacy_aiur_trm $[, $as:legacy_aiur_trm]*)) => do
      let a ← replaceToken old new a
      let as ← as.mapM $ replaceToken old new
      if dot.isSome then `(legacy_aiur_trm| #.$f:ident($a $[, $as]*))
      else `(legacy_aiur_trm| #$f:ident($a $[, $as]*))
    | `(legacy_aiur_trm| $a + $b) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(legacy_aiur_trm| $a + $b)
    | `(legacy_aiur_trm| $a - $b) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(legacy_aiur_trm| $a - $b)
    | `(legacy_aiur_trm| $a * $b) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(legacy_aiur_trm| $a * $b)
    | `(legacy_aiur_trm| eq_zero($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| eq_zero($a))
    | `(legacy_aiur_trm| proj($a:legacy_aiur_trm, $i:num)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| proj($a, $i))
    | `(legacy_aiur_trm| $t:legacy_aiur_trm[$i:num]) => do
      let t ← replaceToken old new t
      `(legacy_aiur_trm| $t[$i])
    | `(legacy_aiur_trm| $t:legacy_aiur_trm[$i:num..$j:num]) => do
      let t ← replaceToken old new t
      `(legacy_aiur_trm| $t[$i..$j])
    | `(legacy_aiur_trm| set($a:legacy_aiur_trm, $i:num, $v:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      let v ← replaceToken old new v
      `(legacy_aiur_trm| set($a, $i, $v))
    | `(legacy_aiur_trm| store($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| store($a))
    | `(legacy_aiur_trm| load($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| load($a))
    | `(legacy_aiur_trm| ptr_val($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| ptr_val($a))
    | `(legacy_aiur_trm| assert_eq!($a:legacy_aiur_trm, $b:legacy_aiur_trm $[, $msg:str]?); $[$ret:legacy_aiur_trm]?) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      let ret' ← ret.mapM $ replaceToken old new
      `(legacy_aiur_trm| assert_eq!($a, $b $[, $msg]?); $[$ret']?)
    | `(legacy_aiur_trm| $v:legacy_aiur_trm : $t:legacy_aiur_typ) => do
      let v ← replaceToken old new v
      `(legacy_aiur_trm| $v : $t)
    | `(legacy_aiur_trm| io_get_info($ch:legacy_aiur_trm, $key:legacy_aiur_trm)) => do
      let ch ← replaceToken old new ch
      let key ← replaceToken old new key
      `(legacy_aiur_trm| io_get_info($ch, $key))
    | `(legacy_aiur_trm| io_set_info($ch:legacy_aiur_trm, $key:legacy_aiur_trm, $idx:legacy_aiur_trm, $len:legacy_aiur_trm); $[$ret:legacy_aiur_trm]?) => do
      let ch ← replaceToken old new ch
      let key ← replaceToken old new key
      let idx ← replaceToken old new idx
      let len ← replaceToken old new len
      let ret' ← ret.mapM $ replaceToken old new
      `(legacy_aiur_trm| io_set_info($ch, $key, $idx, $len); $[$ret']?)
    | `(legacy_aiur_trm| io_read($ch:legacy_aiur_trm, $idx:legacy_aiur_trm, $len:num)) => do
      let ch ← replaceToken old new ch
      let idx ← replaceToken old new idx
      `(legacy_aiur_trm| io_read($ch, $idx, $len))
    | `(legacy_aiur_trm| io_write($ch:legacy_aiur_trm, $data:legacy_aiur_trm); $[$ret:legacy_aiur_trm]?) => do
      let ch ← replaceToken old new ch
      let data ← replaceToken old new data
      let ret' ← ret.mapM $ replaceToken old new
      `(legacy_aiur_trm| io_write($ch, $data); $[$ret']?)
    | `(legacy_aiur_trm| u8_bit_decomposition($byte:legacy_aiur_trm)) => do
      let byte ← replaceToken old new byte
      `(legacy_aiur_trm| u8_bit_decomposition($byte))
    | `(legacy_aiur_trm| u8_shift_left($byte:legacy_aiur_trm)) => do
      let byte ← replaceToken old new byte
      `(legacy_aiur_trm| u8_shift_left($byte))
    | `(legacy_aiur_trm| u8_shift_right($byte:legacy_aiur_trm)) => do
      let byte ← replaceToken old new byte
      `(legacy_aiur_trm| u8_shift_right($byte))
    | `(legacy_aiur_trm| u8_xor($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_xor($i, $j))
    | `(legacy_aiur_trm| u8_add($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_add($i, $j))
    | `(legacy_aiur_trm| u8_mul($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_mul($i, $j))
    | `(legacy_aiur_trm| u8_xor_split7($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_xor_split7($i, $j))
    | `(legacy_aiur_trm| u8_xor_split4($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_xor_split4($i, $j))
    | `(legacy_aiur_trm| u8_sub($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_sub($i, $j))
    | `(legacy_aiur_trm| u8_and($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_and($i, $j))
    | `(legacy_aiur_trm| u8_or($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_or($i, $j))
    | `(legacy_aiur_trm| u8_less_than($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_less_than($i, $j))
    | `(legacy_aiur_trm| u32_less_than($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u32_less_than($i, $j))
    | `(legacy_aiur_trm| unconstrained_u32_add($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| unconstrained_u32_add($i, $j))
    | `(legacy_aiur_trm| unconstrained_u32_add3($i:legacy_aiur_trm, $j:legacy_aiur_trm, $k:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      let k ← replaceToken old new k
      `(legacy_aiur_trm| unconstrained_u32_add3($i, $j, $k))
    | `(legacy_aiur_trm| u32_to_field($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| u32_to_field($a))
    | `(legacy_aiur_trm| u8_range_check($i:legacy_aiur_trm, $j:legacy_aiur_trm)) => do
      let i ← replaceToken old new i
      let j ← replaceToken old new j
      `(legacy_aiur_trm| u8_range_check($i, $j))
    | `(legacy_aiur_trm| unconstrained_big_uint_div_mod($a:legacy_aiur_trm, $b:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      let b ← replaceToken old new b
      `(legacy_aiur_trm| unconstrained_big_uint_div_mod($a, $b))
    | `(legacy_aiur_trm| unconstrained_g_to_bytes($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| unconstrained_g_to_bytes($a))
    | `(legacy_aiur_trm| unconstrained_g_inverse($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| unconstrained_g_inverse($a))
    | `(legacy_aiur_trm| to_field($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| to_field($a))
    | `(legacy_aiur_trm| u8_from_field_unsafe($a:legacy_aiur_trm)) => do
      let a ← replaceToken old new a
      `(legacy_aiur_trm| u8_from_field_unsafe($a))
    | `(legacy_aiur_trm| dbg!($label:str $[, $t:legacy_aiur_trm]?); $[$ret:legacy_aiur_trm]?) => do
      let t' ← t.mapM $ replaceToken old new
      let ret' ← ret.mapM $ replaceToken old new
      `(legacy_aiur_trm| dbg!($label $[, $t']?); $[$ret']?)
    | `(legacy_aiur_trm| fold($i .. $j, $init, |$acc, @$v| $body)) => do
      let init ← replaceToken old new init
      -- Don't conflict with shadowing tokens.
      let body ← if v.getId = old then pure body
        else replaceToken old new body
      `(legacy_aiur_trm| fold($i .. $j, $init, |$acc, @$v| $body))
    | `(legacy_aiur_trm| $t:legacy_aiur_trm; $[$t':legacy_aiur_trm]?) => do
      let t ← replaceToken old new t
      let t' ← t'.mapM $ replaceToken old new
      `(legacy_aiur_trm| $t; $[$t']?)
    | stx => pure stx

declare_syntax_cat                                legacy_aiur_constructor
syntax ident                                    : legacy_aiur_constructor
syntax ident "(" legacy_aiur_typ (", " legacy_aiur_typ)* ")" : legacy_aiur_constructor

def elabConstructor : ElabStxCat `legacy_aiur_constructor
  | `(legacy_aiur_constructor| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Constructor.mk #[toExpr name, ← elabEmptyList ``Typ]
    | _ => throw $ .error i "Illegal constructor name"
  | `(legacy_aiur_constructor| $i:ident($t:legacy_aiur_typ$[, $ts:legacy_aiur_typ]*)) => match i.getId with
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

declare_syntax_cat                                              legacy_aiur_data_type
syntax "enum " ident                                          : legacy_aiur_data_type
syntax "enum " ident "{" legacy_aiur_constructor
       (", " legacy_aiur_constructor)* "}"                          : legacy_aiur_data_type
syntax "enum " ident "‹" ident (", " ident)* "›"              : legacy_aiur_data_type
syntax "enum " ident "‹" ident (", " ident)* "›" "{"
       legacy_aiur_constructor (", " legacy_aiur_constructor)* "}"        : legacy_aiur_data_type

def elabDataType : ElabStxCat `legacy_aiur_data_type
  | `(legacy_aiur_data_type| enum $n:ident) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``DataType.mk #[g, ← elabEmptyList ``String, ← elabEmptyList ``Constructor]
  | `(legacy_aiur_data_type| enum $n:ident
       {$c:legacy_aiur_constructor $[, $cs:legacy_aiur_constructor]*}) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``DataType.mk
      #[g, ← elabEmptyList ``String,
        ← elabList c cs elabConstructor ``Constructor]
  | `(legacy_aiur_data_type| enum $n:ident‹$p:ident $[, $ps:ident]*›) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    mkAppM ``DataType.mk #[g, paramsExpr, ← elabEmptyList ``Constructor]
  | `(legacy_aiur_data_type| enum $n:ident‹$p:ident $[, $ps:ident]*›
       {$c:legacy_aiur_constructor $[, $cs:legacy_aiur_constructor]*}) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    mkAppM ``DataType.mk
      #[g, paramsExpr, ← elabList c cs elabConstructor ``Constructor]
  | stx => throw $ .error stx "Invalid syntax for data type"

declare_syntax_cat                                                  legacy_aiur_type_alias
syntax "type " ident " = " legacy_aiur_typ                              : legacy_aiur_type_alias
syntax "type " ident "‹" ident (", " ident)* "›" " = " legacy_aiur_typ  : legacy_aiur_type_alias

def elabTypeAlias : ElabStxCat `legacy_aiur_type_alias
  | `(legacy_aiur_type_alias| type $n:ident = $t:legacy_aiur_typ) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    mkAppM ``TypeAlias.mk #[g, ← elabEmptyList ``String, ← elabTyp t]
  | `(legacy_aiur_type_alias| type $n:ident‹$p:ident $[, $ps:ident]*› = $t:legacy_aiur_typ) => do
    let g ← mkAppM ``Global.mk #[toExpr n.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    mkAppM ``TypeAlias.mk #[g, paramsExpr, ← elabTyp t]
  | stx => throw $ .error stx "Invalid syntax for type alias"

declare_syntax_cat            legacy_aiur_bind
syntax ident ": " legacy_aiur_typ : legacy_aiur_bind

def elabBind : ElabStxCat `legacy_aiur_bind
  | `(legacy_aiur_bind| $i:ident: $t:legacy_aiur_typ) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Prod.mk #[← mkAppM ``Local.str #[toExpr name], ← elabTyp t]
    | _ => throw $ .error i "Illegal variable name"
  | stx => throw $ .error stx "Invalid syntax for binding"

declare_syntax_cat                                                                                legacy_aiur_function
syntax ("pub ")? "fn " ident "(" ")" (" -> " legacy_aiur_typ)? "{" legacy_aiur_trm "}"                      : legacy_aiur_function
syntax ("pub ")? "fn " ident "(" legacy_aiur_bind (", " legacy_aiur_bind)* ")"
       (" -> " legacy_aiur_typ)? "{" legacy_aiur_trm "}"                                                    : legacy_aiur_function
syntax "fn " ident "‹" ident (", " ident)* "›" "(" ")"
       (" -> " legacy_aiur_typ)? "{" legacy_aiur_trm "}"                                                    : legacy_aiur_function
syntax "fn " ident "‹" ident (", " ident)* "›"
       "(" legacy_aiur_bind (", " legacy_aiur_bind)* ")"
       (" -> " legacy_aiur_typ)? "{" legacy_aiur_trm "}"                                                    : legacy_aiur_function

def elabFunction : ElabStxCat `legacy_aiur_function
  | `(legacy_aiur_function| $[pub%$e]? fn $i:ident() $[-> $ty:legacy_aiur_typ]? {$t:legacy_aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    let inputs ← mkListLit bindType []
    let output ← elabRetTyp ty
    let body ← elabTrm t
    mkMonoFun e g inputs output body
  | `(legacy_aiur_function| $[pub%$e]? fn $i:ident($b:legacy_aiur_bind $[, $bs:legacy_aiur_bind]*)
        $[-> $ty:legacy_aiur_typ]? {$t:legacy_aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    let inputs ← elabListCore b bs elabBind bindType
    let output ← elabRetTyp ty
    let body ← elabTrm t
    mkMonoFun e g inputs output body
  | `(legacy_aiur_function| fn $i:ident‹$p:ident $[, $ps:ident]*›()
        $[-> $ty:legacy_aiur_typ]? {$t:legacy_aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    mkAppM ``Source.Function.poly
      #[g, paramsExpr, ← mkListLit bindType [],
        ← elabRetTyp ty, ← elabTrm t]
  | `(legacy_aiur_function| fn $i:ident‹$p:ident $[, $ps:ident]*›
        ($b:legacy_aiur_bind $[, $bs:legacy_aiur_bind]*)
        $[-> $ty:legacy_aiur_typ]? {$t:legacy_aiur_trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let (_, paramsExpr) ← elabTypeParams p ps
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    mkAppM ``Source.Function.poly
      #[g, paramsExpr,
        ← elabListCore b bs elabBind bindType,
        ← elabRetTyp ty, ← elabTrm t]
  | stx => throw $ .error stx "Invalid syntax for function"
where
  elabRetTyp : Option (TSyntax `legacy_aiur_typ) → TermElabM Expr
    | none => pure $ mkConst ``Typ.unit
    | some typ => elabTyp typ
  /-- Build a monomorphic `Source.Function`. If `pubKw?` is `some _`
  (public/entry function), require a `sigPointerFree` proof: signatures
  with `.pointer` types are rejected with a Meta-level error. -/
  mkMonoFun (pubKw? : Option Syntax) (name inputs output body : Expr) :
      TermElabM Expr := do
    match pubKw? with
    | none =>
      mkAppM ``Source.Function.monoNonEntry #[name, inputs, output, body]
    | some kw =>
      let sigExpr ← mkAppM ``Source.sigPointerFree #[inputs, output]
      let propExpr ← mkAppM ``Eq #[sigExpr, mkConst ``Bool.true]
      let proof ←
        try
          Lean.Meta.mkDecideProof propExpr
        catch _ =>
          throw $ .error kw
            "Public (entry) function signatures cannot contain pointer types"
      mkAppM ``Source.Function.monoEntry #[name, inputs, output, body, proof]

declare_syntax_cat       legacy_aiur_declaration
syntax legacy_aiur_function   : legacy_aiur_declaration
syntax legacy_aiur_data_type  : legacy_aiur_declaration
syntax legacy_aiur_type_alias : legacy_aiur_declaration

def accElabDeclarations (declarations : (Array Expr × Array Expr × Array Expr))
    (stx : TSyntax `legacy_aiur_declaration) :
    TermElabM (Array Expr × Array Expr × Array Expr) :=
  let (dataTypes, typeAliases, functions) := declarations
  match stx with
  | `(legacy_aiur_declaration| $f:legacy_aiur_function) => do
    pure (dataTypes, typeAliases, functions.push $ ← elabFunction f)
  | `(legacy_aiur_declaration| $d:legacy_aiur_data_type) => do
    pure (dataTypes.push $ ← elabDataType d, typeAliases, functions)
  | `(legacy_aiur_declaration| $ta:legacy_aiur_type_alias) => do
    pure (dataTypes, typeAliases.push $ ← elabTypeAlias ta, functions)
  | stx => throw $ .error stx "Invalid syntax for declaration"

declare_syntax_cat          legacy_aiur_toplevel
syntax legacy_aiur_declaration* : legacy_aiur_toplevel

def elabToplevel : ElabStxCat `legacy_aiur_toplevel
  | `(legacy_aiur_toplevel| $[$ds:legacy_aiur_declaration]*) => do
    let (dataTypes, typeAliases, functions) ←
      ds.foldlM (init := default) accElabDeclarations
    mkAppM ``Source.Toplevel.mk #[
      ← mkArrayLit (mkConst ``DataType) dataTypes.toList,
      ← mkArrayLit (mkConst ``TypeAlias) typeAliases.toList,
      ← mkArrayLit (mkConst ``Source.Function) functions.toList,
    ]
  | stx => throw $ .error stx "Invalid syntax for toplevel"

elab "⟦" t:legacy_aiur_toplevel "⟧" : term => elabToplevel t

end LegacyAiur

end
