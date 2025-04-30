import Lean
import Ix.Aiur.Term

namespace Aiur

open Lean Elab Meta

abbrev ElabStxCat name := TSyntax name → TermElabM Expr

declare_syntax_cat                             primitive
syntax (name := primitiveU1)  num noWs "u1"  : primitive
syntax (name := primitiveU8)  num noWs "u8"  : primitive
syntax (name := primitiveU16) num noWs "u16" : primitive
syntax (name := primitiveU32) num noWs "u32" : primitive
syntax (name := primitiveU64) num noWs "u64" : primitive

def elabPrimitive : ElabStxCat `primitive
  | stx@⟨.node _ ``primitiveU1 ts⟩ =>
    match getNat ts with
    | 0 => mkAppM ``Primitive.u1 #[mkConst ``Bool.false]
    | 1 => mkAppM ``Primitive.u1 #[mkConst ``Bool.true]
    | n => throwOutOfRange stx n "u1"
  | stx@⟨.node _ ``primitiveU8 ts⟩ =>
    let n := getNat ts
    if h : n < UInt8.size then mkAppM ``Primitive.u8 #[toExpr $ UInt8.ofNatLT n h]
    else throwOutOfRange stx n "u8"
  | stx@⟨.node _ ``primitiveU16 ts⟩ =>
    let n := getNat ts
    if h : n < UInt16.size then mkAppM ``Primitive.u16 #[toExpr $ UInt16.ofNatLT n h]
    else throwOutOfRange stx n "u16"
  | stx@⟨.node _ ``primitiveU32 ts⟩ =>
    let n := getNat ts
    if h : n < UInt32.size then mkAppM ``Primitive.u32 #[toExpr $ UInt32.ofNatLT n h]
    else throwOutOfRange stx n "u32"
  | stx@⟨.node _ ``primitiveU64 ts⟩ =>
    let n := getNat ts
    if h : n < UInt64.size then mkAppM ``Primitive.u64 #[toExpr $ UInt64.ofNatLT n h]
    else throwOutOfRange stx n "u64"
  | stx => throw $ .error stx "Invalid syntax for primitive"
where
  getNat ts :=
    let numLit : NumLit := ⟨ts[0]!⟩
    numLit.getNat
  throwOutOfRange stx n ty :=
    throw $ .error stx s!"{n} is out of range for {ty}"

declare_syntax_cat                       pattern
syntax ("." noWs)? ident               : pattern
syntax "_"                             : pattern
syntax ident pattern+                  : pattern
syntax primitive                       : pattern
syntax "(" pattern (", " pattern)* ")" : pattern
syntax pattern "|" pattern             : pattern

def elabListCore (head : α) (tail : Array α) (elabFn : α → TermElabM Expr)
    (listEltType : Expr) : TermElabM Expr := do
  let mut elaborated := Array.mkEmpty (tail.size + 1)
  elaborated := elaborated.push $ ← elabFn head
  for elt in tail do
    elaborated := elaborated.push $ ← elabFn elt
  mkListLit listEltType elaborated.toList

def elabList (head : α) (tail : Array α) (elabFn : α → TermElabM Expr)
    (listEltTypeName : Name) : TermElabM Expr :=
  elabListCore head tail elabFn (mkConst listEltTypeName)

def elabEmptyList (listEltTypeName : Name) : TermElabM Expr :=
  mkListLit (mkConst listEltTypeName) []

partial def elabPattern : ElabStxCat `pattern
  | `(pattern| $v:ident $[$ps:pattern]*) => do
    let ps ← ps.mapM elabPattern
    let g ← mkAppM ``Global.mk #[toExpr v.getId]
    mkAppM ``Pattern.ref #[g, ← mkListLit (mkConst ``Pattern) ps.toList]
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
  | `(pattern| $prim:primitive) => do
    mkAppM ``Pattern.primitive #[← elabPrimitive prim]
  | `(pattern| ($p:pattern $[, $ps:pattern]*)) => do
    mkAppM ``Pattern.tuple #[← elabList p ps elabPattern ``Pattern]
  | `(pattern| $p₁:pattern | $p₂:pattern) => do
    mkAppM ``Pattern.or #[← elabPattern p₁, ← elabPattern p₂]
  | stx => throw $ .error stx "Invalid syntax for pattern"

declare_syntax_cat primitive_type
syntax "u1"      : primitive_type
syntax "u8"      : primitive_type
syntax "u16"     : primitive_type
syntax "u32"     : primitive_type
syntax "u64"     : primitive_type

def elabPrimitiveType : ElabStxCat `primitive_type
  | `(primitive_type| u1) => pure $ mkConst ``PrimitiveType.u1
  | `(primitive_type| u8) => pure $ mkConst ``PrimitiveType.u8
  | `(primitive_type| u16) => pure $ mkConst ``PrimitiveType.u16
  | `(primitive_type| u32) => pure $ mkConst ``PrimitiveType.u32
  | `(primitive_type| u64) => pure $ mkConst ``PrimitiveType.u64
  | stx => throw $ .error stx "Invalid syntax for primitive type"

declare_syntax_cat                               typ
syntax primitive_type                          : typ
syntax "(" typ (", " typ)* ")"                 : typ
syntax "&" typ                                 : typ
syntax ("." noWs)? ident                       : typ
syntax "fn" "(" ")" " -> " typ                 : typ
syntax "fn" "(" typ (", " typ)* ")" " -> " typ : typ

partial def elabTyp : ElabStxCat `typ
  | `(typ| $p:primitive_type) => do
    mkAppM ``Typ.primitive #[← elabPrimitiveType p]
  | `(typ| ($t:typ $[, $ts:typ]*)) => do
    mkAppM ``Typ.tuple #[← elabList t ts elabTyp ``Typ]
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

declare_syntax_cat                                          trm
syntax ("." noWs)? ident                                  : trm
syntax primitive                                          : trm
syntax "(" trm (", " trm)* ")"                            : trm
syntax "return " trm                                      : trm
syntax "let " pattern " = " trm "; " trm                  : trm
syntax "match " trm " { " (pattern " => " trm ", ")+ " }" : trm
syntax "if " trm " { " trm " } " " else " " { " trm " } " : trm
syntax ("." noWs)? ident "(" ")"                          : trm
syntax ("." noWs)? ident "(" trm (", " trm)* ")"          : trm
syntax "preimg" "(" ("." noWs)? ident ", " trm ")"        : trm
syntax "xor" "(" trm ", " trm ")"                         : trm
syntax "and" "(" trm ", " trm ")"                         : trm
syntax "get" "(" trm ", " num ")"                         : trm
syntax "slice" "(" trm ", " num ", " num ")"              : trm
syntax "store" "(" trm ")"                                : trm
syntax "load" "(" trm ")"                                 : trm
syntax "pointer_as_u64" "(" trm ")"                       : trm
syntax trm ": " typ                                       : trm

partial def elabTrm : ElabStxCat `trm
  | `(trm| .$i:ident) => do
    mkAppM ``Term.ref #[← mkAppM ``Global.mk #[toExpr i.getId]]
  | `(trm| $i:ident) => match i.getId with
    | .str .anonymous name => do
      mkAppM ``Term.var #[← mkAppM ``Local.str #[toExpr name]]
    | name@(.str _ _) => do
      mkAppM ``Term.ref #[← mkAppM ``Global.mk #[toExpr name]]
    | _ => throw $ .error i "Illegal name"
  | `(trm| $p:primitive) => do
    let data ← mkAppM ``Data.primitive #[← elabPrimitive p]
    mkAppM ``Term.data #[data]
  | `(trm| ($t:trm $[, $ts:trm]*)) => do
    let data ← mkAppM ``Data.tuple #[← elabList t ts elabTrm ``Term]
    mkAppM ``Term.data #[data]
  | `(trm| return $t:trm) => do
    mkAppM ``Term.ret #[← elabTrm t]
  | `(trm| let $p:pattern = $t:trm; $t':trm) => do
    mkAppM ``Term.let #[← elabPattern p, ← elabTrm t, ← elabTrm t']
  | `(trm| match $t:trm {$[$ps:pattern => $ts:trm,]*}) => do
    let mut prods := Array.mkEmpty (ps.size + 1)
    for (p, t) in ps.zip ts do
      prods := prods.push $ ← mkAppM ``Prod.mk #[← elabPattern p, ← elabTrm t]
    let prodType ← mkAppM ``Prod #[mkConst ``Pattern, mkConst ``Term]
    mkAppM ``Term.match #[← elabTrm t, ← mkListLit prodType prods.toList]
  | `(trm| if $b:trm {$t:trm} else {$f:trm}) => do
    mkAppM ``Term.if #[← elabTrm b, ← elabTrm t, ← elabTrm f]
  | `(trm| $[.]?$f:ident ()) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Term.app #[g, ← elabEmptyList ``Term]
  | `(trm| $[.]?$f:ident ($a:trm $[, $as:trm]*)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Term.app #[g, ← elabList a as elabTrm ``Term]
  | `(trm| preimg($[.]?$f:ident, $t:trm)) => do
    let g ← mkAppM ``Global.mk #[toExpr f.getId]
    mkAppM ``Term.preimg #[g, ← elabTrm t]
  | `(trm| xor($a:trm, $b:trm)) => do
    mkAppM ``Term.xor #[← elabTrm a, ← elabTrm b]
  | `(trm| and($a:trm, $b:trm)) => do
    mkAppM ``Term.and #[← elabTrm a, ← elabTrm b]
  | `(trm| get($a:trm, $i:num)) => do
    mkAppM ``Term.get #[← elabTrm a, toExpr i.getNat]
  | `(trm| slice($a:trm, $i:num, $j:num)) => do
    mkAppM ``Term.slice #[← elabTrm a, toExpr i.getNat, toExpr j.getNat]
  | `(trm| store($a:trm)) => do
    mkAppM ``Term.store #[← elabTrm a]
  | `(trm| load($a:trm)) => do
    mkAppM ``Term.load #[← elabTrm a]
  | `(trm| pointer_as_u64($a:trm)) => do
    mkAppM ``Term.pointerAsU64 #[← elabTrm a]
  | `(trm| $v:trm : $t:typ) => do
    mkAppM ``Term.ann #[← elabTyp t, ← elabTrm v]
  | stx => throw $ .error stx "Invalid syntax for term"

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

declare_syntax_cat                                                    function
syntax "fn " ident "(" ")" " -> " typ "{" trm "}"                   : function
syntax "fn " ident "(" bind (", " bind)* ")" " -> " typ "{" trm "}" : function

def elabFunction : ElabStxCat `function
  | `(function| fn $i:ident() -> $ty:typ {$t:trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    mkAppM ``Function.mk #[g, ← mkListLit bindType [], ← elabTyp ty, ← elabTrm t]
  | `(function| fn $i:ident($b:bind $[, $bs:bind]*) -> $ty:typ {$t:trm}) => do
    let g ← mkAppM ``Global.mk #[toExpr i.getId]
    let bindType ← mkAppM ``Prod #[mkConst ``Local, mkConst ``Typ]
    mkAppM ``Function.mk
      #[g, ← elabListCore b bs elabBind bindType, ← elabTyp ty, ← elabTrm t]
  | stx => throw $ .error stx "Invalid syntax for function"

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
