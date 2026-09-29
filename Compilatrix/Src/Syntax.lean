import Compilatrix.Ixon.V3.Const
import Std.Data.HashMap

/-! # Src syntax

The first IR of the rebuilt pipeline (design note `plans/x86-v2/01-src.md`
§2): the resolved, table-free reading of a Tc-typed Ixon v3 closure, with the
relevance annotation (note 02 §3) written into its binders, arguments and
lets, and the evaluation modes that `Src.Lazify` sets.

Constants are numbered densely (`CId`) by ingress; each entry keeps its source
identity (`CRef`, Ix.Kernel's `ConstRef` shape) and its v3 address. Src is not
content-addressed. Contracts are carried exactly and never read by the
semantics (D16). -/

namespace Compilatrix.Src

open Compilatrix.Ixon

/-- Source identity of a constant: a member of a (possibly singleton) block,
or a constructor of an inductive member. -/
inductive CRef where
  | member (block : Address) (i : Nat)
  | ctor (block : Address) (i c : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Dense constant index into `Program.consts`, fixed by ingress. -/
abbrev CId := Nat

/-- Evaluation mode of an argument. `irr` comes from the relevance
annotation; `byName` only from `Src.Lazify`. Any assignment preserves meaning,
and an `irr` argument is never evaluated. -/
inductive Mode where
  | strict
  | byName
  | irr
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

/-- Relevance class of a binder, argument or let (note 02 §3.1). -/
inductive Rel where
  | rel
  | proof
  | type
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

/-- When a λ is a proof: `never`, or exactly when every listed universe
parameter is zero (`allZero []` means always). The β guard of rule A1. -/
inductive PropWhen where
  | never
  | allZero (params : List Nat)
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

structure Binder where
  /-- Written contract: carried, never read. -/
  contract : V3.BinderContract := {}
  /-- Untrusted relevance annotation (note 02). -/
  rel : Rel := .rel
  /-- When this λ is a proof (the A1 guard). -/
  propWhen : PropWhen := .never
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

inductive Term where
  | var (i : Nat)
  | sort (u : Univ)
  | const (c : CId) (us : List Univ)
  | app (f a : Term) (m : Mode)
  | lam (b : Binder) (dom body : Term)
  | pi (b : Binder) (res : V3.ValueContract) (dom cod : Term)
  | letE (c : V3.LetContract) (r : Rel) (ty val body : Term)
  | proj (s : CId) (field : Nat) (e : Term)
  | natLit (n : Nat)
  /-- A valid UTF-8 string literal (stage S only; declined before K4). -/
  | strLit (s : String)
  deriving BEq, Repr, Inhabited, Hashable

/-- One recursor rule: `rhs = λ ps motives minors fields. …`, selected by
`ctor` (constructor index `rules[j]` of the major inductive). -/
structure Rule where
  ctor : CId
  fields : Nat
  rhs : Term
  deriving BEq, Repr, Inhabited

inductive Decl where
  | defn (kind : DefKind) (safety : DefinitionSafety) (lvls : Nat) (type value : Term)
  | induct (safe : Bool) (lvls params indices : Nat) (type : Term) (ctors : Array CId)
  | ctor (safe : Bool) (lvls : Nat) (ind : CId) (cidx params fields : Nat) (type : Term)
  | recr (safe k : Bool) (lvls params motives minors indices : Nat) (ind : CId)
      (rules : Array Rule) (type : Term)
  | quot (kind : QuotKind) (lvls : Nat) (type : Term)
  | axio (safe : Bool) (lvls : Nat) (type : Term)
  deriving Repr, Inhabited

namespace Decl

def type : Decl → Term
  | .defn _ _ _ type _ | .induct _ _ _ _ type _ | .ctor _ _ _ _ _ _ type
  | .recr _ _ _ _ _ _ _ _ _ type | .quot _ _ type | .axio _ _ type => type

def lvls : Decl → Nat
  | .defn _ _ lvls .. | .induct _ lvls .. | .ctor _ lvls .. | .recr _ _ lvls ..
  | .quot _ lvls _ | .axio _ lvls _ => lvls

/-- Short kind label for diagnostics. -/
def kindName : Decl → String
  | .defn .defn .safe .. => "definition"
  | .defn .defn .unsaf .. => "unsafe definition"
  | .defn .defn .part .. => "partial definition"
  | .defn .opaq .. => "opaque"
  | .defn .thm .. => "theorem"
  | .induct .. => "inductive"
  | .ctor .. => "constructor"
  | .recr .. => "recursor"
  | .quot .. => "quotient"
  | .axio .. => "axiom"

/-- Arity of a recursor spine: parameters, motives, minors, indices, major. -/
def recArity : Decl → Option Nat
  | .recr _ _ _ params motives minors indices .. =>
      some (params + motives + minors + indices + 1)
  | _ => none

end Decl

/-- A constant: its source identity, v3 address and resolved declaration. -/
structure ConstEntry where
  ref : CRef
  addr : Address
  decl : Decl
  deriving Repr, Inhabited

/-- Nat primitives with a native meaning (note 01 §3.4). -/
inductive PrimOp where
  | add | sub | mul | div | mod | pow | gcd | beq | ble
  | land | lor | xor | shiftLeft | shiftRight | pred
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace PrimOp

def all : List PrimOp :=
  [.add, .sub, .mul, .div, .mod, .pow, .gcd, .beq, .ble,
   .land, .lor, .xor, .shiftLeft, .shiftRight, .pred]

def arity : PrimOp → Nat
  | .pred => 1
  | _ => 2

/-- Whether the result is a `Bool` rather than a `Nat`. -/
def isPredicate : PrimOp → Bool
  | .beq | .ble => true
  | _ => false

def name : PrimOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .pow => "pow" | .gcd => "gcd" | .beq => "beq" | .ble => "ble" | .land => "land"
  | .lor => "lor" | .xor => "xor" | .shiftLeft => "shiftLeft"
  | .shiftRight => "shiftRight" | .pred => "pred"

end PrimOp

/-- How a reference is resolved; absent means its declaration's body. -/
inductive Resolve where
  | prim (op : PrimOp)
  /-- `us` are `g`'s levels over `f`'s parameters. -/
  | csimp (g : CId) (us : List Univ) (thm : CId)
  /-- `body = λ xs. rhs`, from the checked equation theorem. -/
  | eqn (thm : CId) (body : Term)
  /-- Key `T.casesOn`; `rec` is `T.rec`. -/
  | case (rec : CId)
  deriving Repr, Inhabited

/-- Where a subsingleton recursor field comes from. -/
inductive FieldSrc where
  | index (i : Nat)
  | proof
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Derived recursor kind (note 01 §4.1). -/
inductive RecKind where
  | ordinary
  | subsingleton (fields : Array FieldSrc)
  | empty
  deriving BEq, Repr, Inhabited

/-- The checked unfolding table, indexed by `CId`. -/
structure Table where
  resolve : Array (Option Resolve) := #[]
  recKind : Array (Option RecKind) := #[]
  /-- By-name arity of `lazy` constants, consumed by `Src.Lazify`. -/
  lazy : Array (Option Nat) := #[]
  /-- Inliner hints for 02; no semantic effect. -/
  inline : Array Bool := #[]
  /-- D12 allowlist: opaques evaluated through their value (`Lean.opaqueId`). -/
  opaqueByValue : Array Bool := #[]
  deriving Repr, Inhabited

namespace Table

def resolveOf (t : Table) (c : CId) : Option Resolve := (t.resolve[c]?).join
def recKindOf (t : Table) (c : CId) : Option RecKind := (t.recKind[c]?).join
def lazyOf (t : Table) (c : CId) : Option Nat := (t.lazy[c]?).join
def isInline (t : Table) (c : CId) : Bool := t.inline[c]?.getD false
def isOpaqueByValue (t : Table) (c : CId) : Bool := t.opaqueByValue[c]?.getD false

end Table

/-- `CId`s of the pinned constants present in the program (note 01 §4.2). -/
structure Known where
  nat : Option CId := none
  natZero : Option CId := none
  natSucc : Option CId := none
  natRec : Option CId := none
  bool : Option CId := none
  boolTrue : Option CId := none
  boolFalse : Option CId := none
  eq : Option CId := none
  deriving Repr, Inhabited

/-- A resolved program with its unfolding table and roots.

Identity: every constant is keyed by its Ixon source identity (`CRef`: block
address and member index, and constructor index) and its v3 address. Terms
refer to constants by a dense `CId`, an index into `consts` fixed by ingress,
so that SrcEval's δ is an array access; `byAddr` and `byRef` invert it. -/
structure Program where
  consts : Array ConstEntry
  byAddr : Std.HashMap Address CId
  byRef : Std.HashMap CRef CId := {}
  table : Table := {}
  roots : Array (Address × CId) := #[]
  known : Known := {}
  deriving Inhabited

namespace Program

def decl? (p : Program) (c : CId) : Option Decl := p.consts[c]?.map (·.decl)
def addr (p : Program) (c : CId) : Address := (p.consts[c]?.map (·.addr)).getD default
def size (p : Program) : Nat := p.consts.size
def lookup (p : Program) (a : Address) : Option CId := p.byAddr[a]?
def cref (p : Program) (c : CId) : CRef := (p.consts[c]?.map (·.ref)).getD default
def ofRef (p : Program) (r : CRef) : Option CId := p.byRef[r]?

/-- Short address prefix for diagnostics. -/
def short (p : Program) (c : CId) : String := ((toString (p.addr c)).take 8).toString

end Program

/-! ## Diagnostics -/

/-- A pipeline diagnostic: its code, the constant it concerns, the reference
path from the root (by address), an optional name from untrusted metadata or
a sidecar (labelled as such), and a message. -/
structure Diag where
  code : String
  addr : Option Address := none
  path : List Address := []
  name : Option String := none
  message : String := ""
  deriving Inhabited

def Diag.of (code message : String) (addr : Option Address := none) (path : List Address := [])
    (name : Option String := none) : Diag :=
  { code, addr, path, name, message }

def Diag.render (d : Diag) : String :=
  let where_ := match d.addr with
    | some a => s!" at {((toString a).take 8).toString}"
    | none => ""
  let named := match d.name with
    | some n => s!" (untrusted name {n})"
    | none => ""
  let path := if d.path.isEmpty then "" else
    s!" via {String.intercalate " → " (d.path.map fun a => ((toString a).take 8).toString)}"
  s!"[{d.code}]{where_}{named}{path}: {d.message}"

instance : ToString Diag := ⟨Diag.render⟩

/-! ## Term utilities -/

namespace Term

/-- Collect an application spine: head and arguments with their modes, left
to right. -/
def spine (t : Term) : Term × Array (Term × Mode) :=
  go t #[]
where
  go : Term → Array (Term × Mode) → Term × Array (Term × Mode)
    | .app f a m, acc => go f (acc.push (a, m))
    | t, acc => (t, acc.reverse)

def mkApps (f : Term) (args : Array (Term × Mode)) : Term :=
  args.foldl (fun t (a, m) => .app t a m) f

/-- Split a leading λ-telescope. -/
def lams : Term → Array (Binder × Term) × Term
  | t => go t #[]
where
  go : Term → Array (Binder × Term) → Array (Binder × Term) × Term
    | .lam b d t, acc => go t (acc.push (b, d))
    | t, acc => (acc, t)

/-- Split a leading Π-telescope. -/
def pis : Term → Array (Binder × Term) × Term
  | t => go t #[]
where
  go : Term → Array (Binder × Term) → Array (Binder × Term) × Term
    | .pi b _ d t, acc => go t (acc.push (b, d))
    | t, acc => (acc, t)

def lamCount : Term → Nat
  | .lam _ _ t => t.lamCount + 1
  | _ => 0

/-- Syntactic equality ignoring contracts, modes and annotations (the
equality of the table checks, note 01 §4). -/
def eqv : Term → Term → Bool
  | .var i, .var j => i == j
  | .sort u, .sort v => u == v
  | .const c us, .const d vs => c == d && us == vs
  | .app f a _, .app g b _ => eqv f g && eqv a b
  | .lam _ d t, .lam _ e u => eqv d e && eqv t u
  | .pi _ _ d t, .pi _ _ e u => eqv d e && eqv t u
  | .letE _ _ t v b, .letE _ _ t' v' b' => eqv t t' && eqv v v' && eqv b b'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && eqv e e'
  | .natLit n, .natLit m => n == m
  | .strLit s, .strLit s' => s == s'
  | _, _ => false

/-- Ordinary Lean source contracts: many/shared/unrestricted inputs and
results, with ordinary lets (the Src reading of `V3.Expr.leanFragment`). -/
def leanFragment : Term → Bool
  | .lam b d t => b.contract == .many && d.leanFragment && t.leanFragment
  | .pi b r d t => b.contract == .many && r == .shared && d.leanFragment && t.leanFragment
  | .letE c _ t v b => c.kind == .value && c.binder == .many &&
      t.leanFragment && v.leanFragment && b.leanFragment
  | .app f a _ => f.leanFragment && a.leanFragment
  | .proj _ _ e => e.leanFragment
  | _ => true

/-- Whether constant `c` occurs syntactically. -/
def mentions (c : CId) : Term → Bool
  | .const d _ => c == d
  | .app f a _ => f.mentions c || a.mentions c
  | .lam _ d t | .pi _ _ d t => d.mentions c || t.mentions c
  | .letE _ _ t v b => t.mentions c || v.mentions c || b.mentions c
  | .proj s _ e => s == c || e.mentions c
  | _ => false

/-- Number of nodes (a tree size; shared subterms count once per use). -/
def nodes : Term → Nat
  | .app f a _ => f.nodes + a.nodes + 1
  | .lam _ d t | .pi _ _ d t => d.nodes + t.nodes + 1
  | .letE _ _ t v b => t.nodes + v.nodes + b.nodes + 1
  | .proj _ _ e => e.nodes + 1
  | _ => 1

end Term

/-- Concrete universe instantiation. -/
abbrev Levels := List Nat

/-- Evaluate a universe at a concrete instantiation (out-of-range parameters
read as zero; well-formed programs have none). -/
def evalUniv (ls : Levels) : Univ → Nat
  | .zero => 0
  | .succ u => evalUniv ls u + 1
  | .max a b => Nat.max (evalUniv ls a) (evalUniv ls b)
  | .imax a b => let vb := evalUniv ls b; if vb == 0 then 0 else Nat.max (evalUniv ls a) vb
  | .var i => ls.getD i.toNat 0

/-- The λ's regime at an instantiation: `false` when it is a proof there. -/
def PropWhen.allowsBeta (ls : Levels) : PropWhen → Bool
  | .never => true
  | .allZero ps => !ps.all fun p => ls.getD p 0 == 0

end Compilatrix.Src
