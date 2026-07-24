/-
  Surface AST for the Ixon text format (`.ixon`).

  Behavioral mirror of `crates/ixon/src/syntax/ast.rs` — same shapes,
  same invariants. The AST is the hub shared by the parser and the
  pretty-printer: it denotes the *named Ix level* (Ix.Expr minus
  fvar/mvar/mdata) plus source spans and the three reference forms
  (`Name`, `#hash`, `Name#hash`). Nothing here knows about the pack
  format: no tables, no de Bruijn indices, no blob addresses.

  Every node carries a byte-offset `Span`. Roundtrip tests compare at
  the text level (`print ∘ parse ∘ print = print`), never by AST
  equality (spans differ across a roundtrip).
-/
module

public import Lean.Expr

public section

namespace Ixon.Syntax

/-- Grammar version this implementation speaks (R7). The `ixon <n>`
    header is optional: absent means version 1, forever; grammar
    versions ≥ 2 must declare themselves, and canonical version-1
    output omits the header. Mirrors Rust `syntax::VERSION`. -/
def VERSION : Nat := 1

/-- Parser resource caps (R2: gas for admission). Mirrors Rust
    `syntax::Limits`, including the defaults. -/
structure Limits where
  /-- Maximum input length in bytes (checked before any work). -/
  maxBytes : Nat := 1 <<< 20
  /-- Maximum AST node count (checked after parse; no ε-productions,
      so `maxBytes` already bounds it). -/
  maxNodes : Nat := 1 <<< 20
  /-- Maximum nesting depth (checked during descent). -/
  maxDepth : Nat := 512
  deriving BEq, Repr, Inhabited

/-- Byte-offset span into the source: `start` inclusive, `stop`
    exclusive. -/
structure Span where
  start : Nat := 0
  stop : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Smallest span covering both. -/
def Span.to (a b : Span) : Span :=
  ⟨min a.start b.start, max a.stop b.stop⟩

/-- One surface name component. Mirrors Rust
    `ix_common::env::NameComponent`. -/
inductive NameComponent where
  | str (s : String)
  | num (n : Nat)
  deriving BEq, Repr, Inhabited

/-- A surface (dotted) name: raw components, no hashing. Numeric
    components are legal only in non-leading position. -/
structure SName where
  parts : Array NameComponent
  span : Span := {}
  deriving BEq, Repr, Inhabited

/-- A `#hex` reference: 4–64 lowercase hex digits (exactly 64 in
    import position). -/
structure HashRef where
  hex : String
  span : Span := {}
  deriving BEq, Repr, Inhabited

/-- Universe-level expression. -/
inductive UnivExpr where
  | nat (n : Nat) (span : Span)
  | var (c : NameComponent) (span : Span)
  | add (u : UnivExpr) (n : Nat) (span : Span)
  | max (a b : UnivExpr) (span : Span)
  | imax (a b : UnivExpr) (span : Span)
  deriving BEq, Repr, Inhabited

def UnivExpr.span : UnivExpr → Span
  | .nat _ s | .var _ s | .add _ _ s | .max _ _ s | .imax _ _ s => s

/-- Constant reference: `Name`, `#hash`, or pinned `Name#hash`.
    Invariant: at least one of `name`/`hash` present; `levels = none`
    is the bare zero-default form, `some vs` the explicit `.{…}` form
    (`vs` nonempty). -/
structure ConstRef where
  name : Option SName := none
  hash : Option HashRef := none
  levels : Option (Array UnivExpr) := none
  span : Span := {}
  deriving BEq, Repr, Inhabited

/-- `Prop` | `Type u?` | `Sort u` — surface distinction kept for exact
    printing. -/
inductive SortKind where
  | prop
  | type (u : Option UnivExpr)
  | sort (u : UnivExpr)
  deriving BEq, Repr, Inhabited

/-- A binder name: identifier component or `_`. -/
inductive BinderName where
  | ident (c : NameComponent) (span : Span)
  | anon (span : Span)
  deriving BEq, Repr, Inhabited

def BinderName.span : BinderName → Span
  | .ident _ s | .anon s => s

mutual

/-- Surface term. Mirrors Rust `syntax::ast::Term`. -/
inductive Term where
  | ref (r : ConstRef)
  | sort (k : SortKind) (span : Span)
  /-- Application spine `f a b c` (`args` nonempty); the canonical
      printer flattens nested spines. -/
  | app (head : Term) (args : Array Term) (span : Span)
  | lam (binders : Array BinderGroup) (body : Term) (span : Span)
  | pi (binders : Array BinderGroup) (body : Term) (span : Span)
  | arrow (dom cod : Term) (span : Span)
  /-- `let` (`nonDep = false`) / `have` (`nonDep = true`) —
      address-relevant. -/
  | letE (nonDep : Bool) (name : BinderName) (ty val body : Term)
      (span : Span)
  | natLit (n : Nat) (span : Span)
  | strLit (s : String) (span : Span)
  | proj (typeRef : ConstRef) (idx : Nat) (val : Term) (span : Span)

/-- One bracketed binder group; bracket shape is `Lean.BinderInfo` —
    metadata only, never address-relevant. Unnamed instance `[T]` has
    empty `names`. -/
inductive BinderGroup where
  | mk (info : Lean.BinderInfo) (names : Array BinderName) (ty : Term)
      (span : Span)

end

instance : Inhabited Term := ⟨.sort .prop {}⟩

instance : Inhabited BinderGroup :=
  ⟨.mk .default #[] (.sort .prop {}) {}⟩

def BinderGroup.info : BinderGroup → Lean.BinderInfo
  | .mk i _ _ _ => i

def BinderGroup.names : BinderGroup → Array BinderName
  | .mk _ n _ _ => n

def BinderGroup.ty : BinderGroup → Term
  | .mk _ _ t _ => t

def BinderGroup.span : BinderGroup → Span
  | .mk _ _ _ s => s

def Term.span : Term → Span
  | .ref r => r.span
  | .sort _ s | .natLit _ s | .strLit _ s => s
  | .app _ _ s | .lam _ _ s | .pi _ _ s | .arrow _ _ s
  | .letE _ _ _ _ _ s | .proj _ _ _ s => s

/-- `def` / `theorem` / `opaque` — address-relevant. -/
inductive DefKw where
  | defn
  | thm
  | opaq
  deriving BEq, Repr, Inhabited

/-- Declaration modifiers — address-relevant (`DefinitionSafety`). -/
structure Modifiers where
  isUnsafe : Bool := false
  isPartial : Bool := false
  deriving BEq, Repr, Inhabited

/-- Universe parameter binder in `.{u, v}` declaration position. -/
structure UParam where
  name : NameComponent
  span : Span := {}
  deriving BEq, Repr, Inhabited

/-- `def Name.{u} : T := v`. -/
structure DefDecl where
  kw : DefKw
  mods : Modifiers := {}
  name : Option SName := none
  uparams : Array UParam := #[]
  ty : Term
  value : Term
  span : Span := {}
  deriving Inhabited

/-- `axiom Name.{u} : T`. -/
structure AxiomDecl where
  isUnsafe : Bool := false
  name : Option SName := none
  uparams : Array UParam := #[]
  ty : Term
  span : Span := {}
  deriving Inhabited

/-- The four quotient primitives. -/
inductive QuotKindKw where
  | type
  | ctor
  | lift
  | ind
  deriving BEq, Repr, Inhabited

/-- `quot type|ctor|lift|ind Name.{u} : T`. -/
structure QuotDecl where
  kind : QuotKindKw
  name : Option SName := none
  uparams : Array UParam := #[]
  ty : Term
  span : Span := {}
  deriving Inhabited

/-- Constructor inside `inductive … where`. -/
structure CtorDecl where
  name : Option SName := none
  params : Nat
  fields : Nat
  ty : Term
  span : Span := {}
  deriving Inhabited

/-- `inductive Name.{u} (params := n) (indices := m) : T where …`. -/
structure IndDecl where
  isUnsafe : Bool := false
  name : Option SName := none
  uparams : Array UParam := #[]
  params : Nat
  indices : Nat
  ty : Term
  ctors : Array CtorDecl := #[]
  span : Span := {}
  deriving Inhabited

/-- Recursor rule `| rule (fields := n) := rhs`. -/
structure RuleDecl where
  fields : Nat
  rhs : Term
  span : Span := {}
  deriving Inhabited

/-- `recursor Name.{u} (params := …) … : T where …`. -/
structure RecrDecl where
  isUnsafe : Bool := false
  name : Option SName := none
  uparams : Array UParam := #[]
  params : Nat
  indices : Nat
  motives : Nat
  minors : Nat
  k : Bool := false
  ty : Term
  rules : Array RuleDecl := #[]
  span : Span := {}
  deriving Inhabited

/-- The four projection-constant kinds. -/
inductive PrjKind where
  | dprj
  | iprj
  | cprj
  | rprj
  deriving BEq, Repr, Inhabited

/-- Projection constant `cprj Name := #block i c` etc.; `cidx` present
    iff `kind = cprj`. -/
structure PrjDecl where
  kind : PrjKind
  name : Option SName := none
  block : HashRef
  idx : Nat
  cidx : Option Nat := none
  span : Span := {}
  deriving Inhabited

/-- Top-level declaration. `muts` members are restricted to
    `defn`/`indc`/`recr`. -/
inductive Decl where
  | defn (d : DefDecl)
  | axio (d : AxiomDecl)
  | quot (d : QuotDecl)
  | indc (d : IndDecl)
  | recr (d : RecrDecl)
  | muts (members : Array Decl) (span : Span)
  | prj (d : PrjDecl)
  deriving Inhabited

def Decl.span : Decl → Span
  | .defn d => d.span
  | .axio d => d.span
  | .quot d => d.span
  | .indc d => d.span
  | .recr d => d.span
  | .muts _ s => s
  | .prj d => d.span

/-- `import Foo.Bar#hash` (mount under prefix) / `import #hash` (mount
    at root); import hashes are always full 64-hex. -/
structure ImportDecl where
  prefixName : Option SName := none
  hash : HashRef
  span : Span := {}
  deriving Inhabited

/-- The file's main expression: a trailing `⊢ value : type` item. The
    annotation is mandatory (it is the constant's `typ` — inference
    would be elaboration, R4); the turnstile is load-bearing (without
    it a preceding declaration's final term absorbs an atom-headed
    value as an application argument). Compiles like an anonymous
    `def : T := v` (defn-kind, safe, monomorphic) and marks the result
    as the file's `main` constant. -/
structure MainExpr where
  value : Term
  ty : Term
  span : Span := {}
  deriving Inhabited

/-- A parsed `.ixon` file. -/
structure File where
  version : Nat
  imports : Array ImportDecl := #[]
  decls : Array Decl := #[]
  main : Option MainExpr := none
  span : Span := {}
  deriving Inhabited

/-! ## Node counting (the `maxNodes` limit, R2) -/

mutual

partial def countTermNodes : Term → Nat
  | .ref r => countRefNodes r
  | .sort k _ =>
    match k with
    | .type (some u) | .sort u => 1 + countUnivNodes u
    | _ => 1
  | .app h args _ =>
    args.foldl (fun acc a => acc + countTermNodes a) (1 + countTermNodes h)
  | .lam bs body _ | .pi bs body _ =>
    bs.foldl (fun acc b => acc + 1 + countTermNodes b.ty)
      (1 + countTermNodes body)
  | .arrow d c _ => 1 + countTermNodes d + countTermNodes c
  | .letE _ _ t v b _ =>
    1 + countTermNodes t + countTermNodes v + countTermNodes b
  | .natLit .. | .strLit .. => 1
  | .proj tr _ v _ => 1 + countRefNodes tr + countTermNodes v

partial def countRefNodes (r : ConstRef) : Nat :=
  match r.levels with
  | some ls => ls.foldl (fun acc l => acc + countUnivNodes l) 1
  | none => 1

partial def countUnivNodes : UnivExpr → Nat
  | .nat .. | .var .. => 1
  | .add a _ _ => 1 + countUnivNodes a
  | .max a b _ | .imax a b _ => 1 + countUnivNodes a + countUnivNodes b

end

partial def countDeclNodes : Decl → Nat
  | .defn d => 1 + countTermNodes d.ty + countTermNodes d.value
  | .axio d => 1 + countTermNodes d.ty
  | .quot d => 1 + countTermNodes d.ty
  | .indc d =>
    d.ctors.foldl (fun acc c => acc + 1 + countTermNodes c.ty)
      (1 + countTermNodes d.ty)
  | .recr d =>
    d.rules.foldl (fun acc r => acc + 1 + countTermNodes r.rhs)
      (1 + countTermNodes d.ty)
  | .muts ms _ => ms.foldl (fun acc m => acc + countDeclNodes m) 1
  | .prj _ => 1

def countFileNodes (f : File) : Nat :=
  let base := f.decls.foldl (fun acc d => acc + countDeclNodes d)
    (1 + f.imports.size)
  match f.main with
  | some m => base + 1 + countTermNodes m.value + countTermNodes m.ty
  | none => base

end Ixon.Syntax
