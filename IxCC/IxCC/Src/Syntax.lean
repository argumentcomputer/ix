import IxCC.Ixon.V3.Const
import IxCC.Src.Level
import IxCC.Src.NatMap
import IxCC.Src.Resource.Syntax

/-! # Src syntax

The first IR of the rebuilt pipeline: the resolved, table-free reading of an Ixon closure the certified kernel accepted,
with the relevance annotation written into its binders, arguments and
lets, and the evaluation modes that `Src.Lazify` sets.

Relevance is level-exact (D18): every annotated position carries a `Rel`
whose `proof` class holds under a zero condition over the constant's universe
parameters (`Src.Level`), so sort-polymorphic code is irrelevant exactly at
the instances where its position is a proof.

Constants are numbered densely (`CId`) by ingress; each entry keeps its source
identity (`CRef`, Ix.Kernel's `ConstRef` shape) and its v3 address. Src is not
content-addressed. Contracts are carried exactly and never read by the
semantics (D16).

The program, its table and its declarations are kernel-evaluable data (D17): persistent `NatMap`s
over `CId` and lists, never arrays or hash maps, so the recheck path reads them by structural
recursion. -/

namespace IxCC.Src

open IxCC.Ixon

/-- Source identity of a constant: a member of a (possibly singleton) block,
or a constructor of an inductive member. -/
inductive CRef where
  | member (block : Address) (i : Nat)
  | ctor (block : Address) (i c : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Dense constant index into `Program.consts`, fixed by ingress. -/
abbrev CId := Nat

/-- Evaluation mode of an argument where it is relevant: `byName` comes only
from `Src.Lazify`. Any assignment preserves meaning. Whether the argument is
relevant at all is its `Rel`. -/
inductive Mode where
  | strict
  | byName
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

/-- Relevance class of a binder, argument, let or constructor field, level-exact (D18): `proof when`
is a proof exactly where `when` holds and relevant elsewhere (`proof .never` is written `rel`); a
`type` is irrelevant at every instance. -/
inductive Rel where
  | rel
  | proof (when : PropWhen)
  | type
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Rel

/-- A proof at every instance. -/
def prf : Rel := .proof .always

/-- When the position is irrelevant. -/
def irrWhen : Rel → PropWhen
  | .rel => .never
  | .proof w => w
  | .type => .always

/-- Irrelevant at concrete levels (SrcEval). -/
def irrAt (ls : Levels) (r : Rel) : Bool := r.irrWhen.holds ls

/-- Irrelevant at a profile (the checker, `Admit`, erasure). -/
def irrP (prof : Profile) (r : Rel) : Bool := r.irrWhen.holdsP prof

/-- Irrelevant at every instance: never evaluated, never annotated inside. -/
def alwaysIrr (r : Rel) : Bool := r.irrWhen == .always

end Rel

structure Binder where
  /-- Written contract: carried, never read. -/
  contract : V3.BinderContract := {}
  /-- Untrusted relevance annotation of the parameter. -/
  rel : Rel := .rel
  /-- When this λ is a proof (the A1 guard): the zero condition of its
  codomain's sort. -/
  propWhen : PropWhen := .never
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

inductive Term where
  | var (i : Nat)
  | sort (u : Univ)
  | const (c : CId) (us : List Univ)
  /-- `a` is irrelevant where `r` is; elsewhere it is passed by `m`. -/
  | app (f a : Term) (m : Mode) (r : Rel)
  | lam (b : Binder) (dom body : Term)
  | pi (b : Binder) (res : V3.ValueContract) (dom cod : Term)
  | letE (c : V3.LetContract) (r : Rel) (ty val body : Term)
  | proj (s : CId) (field : Nat) (e : Term)
  | natLit (n : Nat)
  /-- A valid UTF-8 string literal (stage S only; declined before K4). -/
  | strLit (s : String)
  deriving BEq, Repr, Inhabited, Hashable

/-- The value ingress stores for a theorem it reads by its statement
(`Program.byStatement`): `Sort 0`, which is no proof of an equation (its type
is `Sort 1`). It stands for a proof that is not in the program; the theorem is
recorded in `Program.byStatement`, and every consumer that could take a
theorem's value either never takes one (SrcEval, erasure, the annotator: a
theorem is never a runtime term) or refuses a theorem recorded there. -/
def Term.unreadProof : Term := .sort .zero

/-- One recursor rule: `rhs = λ ps motives minors fields. …`, selected by
`ctor` (constructor index `rules[j]` of the major inductive). -/
structure Rule where
  ctor : CId
  fields : Nat
  rhs : Term
  deriving BEq, Repr, Inhabited

inductive Decl where
  | defn (kind : DefKind) (safety : DefinitionSafety) (lvls : Nat) (type value : Term)
  | induct (safe : Bool) (lvls params indices : Nat) (type : Term) (ctors : List CId)
  | ctor (safe : Bool) (lvls : Nat) (ind : CId) (cidx params fields : Nat) (type : Term)
  | recr (safe k : Bool) (lvls params motives minors indices : Nat) (ind : CId)
      (rules : List Rule) (type : Term)
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

/-- Nat primitives with a native meaning. -/
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
  deriving BEq, Repr, Inhabited

/-- Where a subsingleton recursor field comes from. -/
inductive FieldSrc where
  | index (i : Nat)
  | proof
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Derived recursor kind, per universe profile (D18): a
`subsingleton when` recursor is a subsingleton eliminator where `when` holds
(its inductive is a proposition there) and an ordinary one elsewhere; for
`PUnit.{u}.rec` it is `u = 0`, for `Eq.rec` always. -/
inductive RecKind where
  | ordinary
  | subsingleton (when : PropWhen) (fields : List FieldSrc)
  | empty
  deriving BEq, Repr, Inhabited

namespace RecKind

/-- The kind at concrete levels (a subsingleton kind whose condition fails
is ordinary). -/
def atLevels (ls : Levels) : RecKind → RecKind
  | .subsingleton w fs => if w.holds ls then .subsingleton w fs else .ordinary
  | k => k

/-- The kind at a profile. -/
def atProfile (prof : Profile) : RecKind → RecKind
  | .subsingleton w fs => if w.holdsP prof then .subsingleton w fs else .ordinary
  | k => k

/-- Whether an irrelevant major is allowed (subsingleton or empty). -/
def allowsIrrMajor : RecKind → Bool
  | .ordinary => false
  | _ => true

end RecKind

/-- The checked unfolding table, keyed by `CId` (D17). -/
structure Table where
  resolve : NatMap Resolve := .leaf
  recKind : NatMap RecKind := .leaf
  /-- By-name arity of `lazy` constants, consumed by `Src.Lazify`. -/
  lazy : NatMap Nat := .leaf
  /-- Inliner hints for the middle end; no semantic effect. -/
  inline : NatSet := .leaf
  /-- D12 allowlist: opaques evaluated through their value (`Lean.opaqueId`). -/
  opaqueByValue : NatSet := .leaf
  deriving Repr, Inhabited

namespace Table

def resolveOf (t : Table) (c : CId) : Option Resolve := t.resolve.get? c
def recKindOf (t : Table) (c : CId) : Option RecKind := t.recKind.get? c
def lazyOf (t : Table) (c : CId) : Option Nat := t.lazy.get? c
def isInline (t : Table) (c : CId) : Bool := t.inline.contains c
def isOpaqueByValue (t : Table) (c : CId) : Bool := t.opaqueByValue.contains c

end Table

/-- Where the pinned identities are: each address as a 256-bit number, its 32
bytes read big-endian (`Src.Pinned.addrNat`), so that the recheck path compares
addresses with pins in the kernel (D17). An identity without a pin (`none`, or
an operation or axiom missing from its list) is absent from the program, as an
identity whose constant is missing from the closure is. Ingress takes the pins
from the role table the certified kernel admitted, through the stated mapping
from the kernel's roles (`KernelFront.pinsOfTable`); the fixed table
`Pins.fixed` is the default (`Src.Pinned`). -/
structure Pins where
  nat : Option Nat := none
  natZero : Option Nat := none
  natSucc : Option Nat := none
  natRec : Option Nat := none
  bool : Option Nat := none
  boolTrue : Option Nat := none
  boolFalse : Option Nat := none
  eq : Option Nat := none
  decIsFalse : Option Nat := none
  decIsTrue : Option Nat := none
  /-- The primitive operations that have a pin, with it. -/
  prims : List (PrimOp × Nat) := []
  /-- The standard axioms (`propext`, `Quot.sound`, `Classical.choice`). -/
  stdAxioms : List Nat := []
  /-- The D12 allowlist: opaques evaluated through their value (`Lean.opaqueId`). -/
  opaqueByValue : List Nat := []
  deriving Repr, Inhabited

namespace Pins

/-- The fixed table: the addresses of `fixtures/ixon-v4/primitives.tsv` and
`src-tables.tsv` (`Src.Pinned`'s rows, which `#guard`s tie to these numbers):
the default pins of a program built without ingress, and the allowlist's
address (`KernelFront.pinsOfTable`). -/
def fixed : Pins :=
  { nat := some 0x35e1cc809f6f076521a43f85068d5592220407c0532b6a08952f40d8523d04bc
    natZero := some 0xeeb2e6268ff6d0e6b2e9764d9940b81bb64b9f8f4b1358d294ff9817e6941a46
    natSucc := some 0x42d6ed31536f0958176f1dc973383808ac8583223746ebca78dbe389b65321a6
    natRec := some 0xc8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992
    bool := some 0xe6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4
    boolTrue := some 0xa29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762
    boolFalse := some 0xdda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e
    eq := some 0xc37d6290e00fb865fb5db7bce18fd69e6d1674ad573724b85466ea9f7578a207
    decIsFalse := some 0x8cc0e1360c1b29108dab3d6172e7fce8a9aa9640daa4bbe99ba1305d9623624b
    decIsTrue := some 0x363d071182be414e1a58599b83f5e19f9b873723054f4287ba69705aafef27da
    prims :=
      [ (.add, 0x3e8aadcc611c4d8677cadf00c78506561d33738ee3d571f7a4196e260580c9b8),
        (.sub, 0x03b3a041285b0fe202d90b227d405c4cec252df18ba7616acd6dae2792e672bb),
        (.mul, 0x373b7d74f6b40da11b7ed79603a45ec7011a8831b720b57d2efe92e82a3d57f0),
        (.div, 0x824d1c53d8c1c3cf0a27f24639ec2be1ecc13d4a01c993171595edccf6949737),
        (.mod, 0x11abbf986481c53a21c8cb21ee2581ae6238aedbec15f972959d086bef1a1985),
        (.pow, 0x5baaf05c969d2cf377312111be51bb64c600c13fa164ee722e92243b0f771bab),
        (.gcd, 0xaba94bfb41351d4db36172c379a512f04219ef21dc5454d71590967d4e8f913f),
        (.beq, 0xd3d8ff924af9dc4b5cd869760615b3e7ee80916bb617259d45890c69f4128337),
        (.ble, 0x9e445b9d5f8252772347872e909b5db4e7eca7086cedf4fec6de840f6b7b5f92),
        (.land, 0xde8c100c22f82a5c3533c67e4370671813434a6fec5d023998ded090df4a4934),
        (.lor, 0x93afc1cd298c63606e5f468d1e5989ab4680d256e95d07a8642a88b5c6b858e1),
        (.xor, 0x77dd40d7b6ca310cc59466d1f24df4f180ef50e1b00fd850698458cd26901c5d),
        (.shiftLeft, 0x05bb657e8b9d5dc224e7ef3d53e54153ce3ac26da8d1f1b1d61069a3726566cd),
        (.shiftRight, 0x25019ff485fcf5709597cd1e07fcc3ce796776ef3f715a6d187eb5831c63b4be),
        (.pred, 0x3244687301d779ec757274761d903def3eb3135177327b709bcbd854ef496f79) ]
    stdAxioms :=
      [ 0x209c96511648d09459019701f6e1005409320a710a3cfd1895e5672134161e34,
        0x9b2874e754d995db8d27868f8100eb4d99c07cc2c8bfd099bb1e2986d0a6784a,
        0xcfa39364a87c7561ae41e5093915e97ccced20c5907ef7f67c02ac7029423c40 ]
    opaqueByValue := [0xd0e998ecf33a57f1fcf98311611d1402b361f426d81d6a8ade77123e2e7b8046] }

/-- The pin of a primitive operation, if it has one. -/
def prim? (p : Pins) (op : PrimOp) : Option Nat := p.prims.lookup op

end Pins

/-- `CId`s of the pinned constants present in the program, and the pins they
were resolved against. -/
structure Known where
  nat : Option CId := none
  natZero : Option CId := none
  natSucc : Option CId := none
  natRec : Option CId := none
  bool : Option CId := none
  boolTrue : Option CId := none
  boolFalse : Option CId := none
  eq : Option CId := none
  /-- `Decidable.isFalse`/`isTrue`: erasure retags them as `Bool.false`/`true`
  (D19). -/
  decIsFalse : Option CId := none
  decIsTrue : Option CId := none
  /-- The pins: ingress's choice for the environment the program was read
  from; every check of a pinned identity compares with these. -/
  pins : Pins := Pins.fixed
  deriving Repr, Inhabited

/-- A resolved program with its unfolding table and roots.

Identity: every constant is keyed by its Ixon source identity (`CRef`: block
address and member index, and constructor index) and its v3 address. Terms
refer to constants by a dense `CId`, a key of `consts` fixed by ingress
(every key below `size` is present). The program is kernel-evaluable data
(D17): `consts` is a persistent `NatMap`, and the address index that inverts
it belongs to the producer (`lookup` scans; `Table.build` indexes once). -/
structure Program where
  consts : NatMap ConstEntry := .leaf
  /-- The number of constants: `consts` holds exactly the keys below it. -/
  size : Nat := 0
  table : Table := {}
  roots : List (Address × CId) := []
  known : Known := {}
  /-- Untrusted address/header bindings; revalidated with the unfolding table.
  This is not a resource-safety or profile-execution certificate. -/
  resource : Option Resource.Context := none
  /-- The theorems ingress read by their statement (`Src.Ingress.reach`):
  theorems the program reaches only as constants, not as ones whose proof the
  unfolding table may examine. Each one's type is read; its proof is not, and
  its stored value is `Term.unreadProof`. The unfolding table's checks refuse
  such a theorem (`Table.checkEqn`, `checkCsimp`, and `checkAxiomClosure` on
  both its branches: the walk at its first step, and its all-standard shortcut
  does not apply to such a theorem), and the recheck path refuses an
  annotation that names its value (`Recheck.checkRelevanceKeys`). -/
  byStatement : NatSet := .leaf
  deriving Inhabited

namespace Program

/-- A program whose constants are `consts`, in `CId` order. -/
def ofConsts (consts : List ConstEntry) : Program :=
  { consts := NatMap.ofDense consts, size := consts.length }

def entry? (p : Program) (c : CId) : Option ConstEntry := p.consts.get? c
def decl? (p : Program) (c : CId) : Option Decl := (p.entry? c).map (·.decl)
def addr (p : Program) (c : CId) : Address := ((p.entry? c).map (·.addr)).getD default
def cref (p : Program) (c : CId) : CRef := ((p.entry? c).map (·.ref)).getD default

/-- The constants in `CId` order. -/
def entries (p : Program) : List ConstEntry := (List.range p.size).filterMap p.entry?

/-- Append a constant under the next `CId`. -/
def push (p : Program) (e : ConstEntry) : Program :=
  { p with consts := p.consts.insert p.size e, size := p.size + 1 }

/-- Replace the declaration of `c`. -/
def setDecl (p : Program) (c : CId) (decl : Decl) : Program :=
  { p with consts := p.consts.modify c fun e => { e with decl } }

/-- The constant at an address: a linear scan (addresses are unique in a
closure); `Table.addrIndex` indexes a whole program once. -/
def lookup (p : Program) (a : Address) : Option CId :=
  (List.range p.size).find? fun c => (p.entry? c).any (·.addr == a)

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

/-- An application argument: the term, its mode where relevant, and its class. -/
abbrev Arg := Term × Mode × Rel

/-- Collect an application spine: head and arguments with their modes and
classes, left to right (structural). -/
def spine (t : Term) : Term × List Arg :=
  go t []
where
  go : Term → List Arg → Term × List Arg
    | .app f a m r, acc => go f ((a, m, r) :: acc)
    | t, acc => (t, acc)

/-- `spine`, under the name the checker and erasure use. -/
abbrev spineL (t : Term) : Term × List Arg := t.spine

def mkApps (f : Term) (args : List Arg) : Term :=
  args.foldl (fun t (a, m, r) => .app t a m r) f

/-- Split a leading λ-telescope (structural). -/
def lams : Term → List (Binder × Term) × Term
  | .lam b d t => let (bs, body) := lams t; ((b, d) :: bs, body)
  | t => ([], t)

/-- Split a leading Π-telescope (structural). -/
def pis : Term → List (Binder × Term) × Term
  | .pi b _ d t => let (bs, body) := pis t; ((b, d) :: bs, body)
  | t => ([], t)

/-- The number of leading Π binders. -/
def piCount : Term → Nat
  | .pi _ _ _ t => t.piCount + 1
  | _ => 0

def lamCount : Term → Nat
  | .lam _ _ t => t.lamCount + 1
  | _ => 0

/-- Syntactic equality ignoring contracts, modes and annotations (the
equality of the table checks). -/
def eqv : Term → Term → Bool
  | .var i, .var j => i == j
  | .sort u, .sort v => u == v
  | .const c us, .const d vs => c == d && us == vs
  | .app f a _ _, .app g b _ _ => eqv f g && eqv a b
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
  | .app f a _ _ => f.leanFragment && a.leanFragment
  | .proj _ _ e => e.leanFragment
  | _ => true

/-- Whether constant `c` occurs syntactically. -/
def mentions (c : CId) : Term → Bool
  | .const d _ => c == d
  | .app f a _ _ => f.mentions c || a.mentions c
  | .lam _ d t | .pi _ _ d t => d.mentions c || t.mentions c
  | .letE _ _ t v b => t.mentions c || v.mentions c || b.mentions c
  | .proj s _ e => s == c || e.mentions c
  | _ => false

/-- Number of nodes (a tree size; shared subterms count once per use). -/
def nodes : Term → Nat
  | .app f a _ _ => f.nodes + a.nodes + 1
  | .lam _ d t | .pi _ _ d t => d.nodes + t.nodes + 1
  | .letE _ _ t v b => t.nodes + v.nodes + b.nodes + 1
  | .proj _ _ e => e.nodes + 1
  | _ => 1

/-- Remaining node budget after visiting `t`, or `none` if `t`'s tree expansion
exceeds `b` nodes. Structural over `t`, short-circuiting as soon as the budget
is exhausted so shared DAGs cannot cause exponential walks. -/
def nodesBudget : Term → Nat → Option Nat
  | _, 0 => none
  | .app f a _ _, b + 1 => do
    let b1 ← nodesBudget f b
    nodesBudget a b1
  | .lam _ d t, b + 1 | .pi _ _ d t, b + 1 => do
    let b1 ← nodesBudget d b
    nodesBudget t b1
  | .letE _ _ t v body, b + 1 => do
    let b1 ← nodesBudget t b
    let b2 ← nodesBudget v b1
    nodesBudget body b2
  | .proj _ _ e, b + 1 =>
    nodesBudget e b
  | _, b + 1 => some b

/-- Whether `t`'s tree expansion has at most `cap` nodes. -/
def nodesLe (t : Term) (cap : Nat) : Bool :=
  (nodesBudget t (cap + 1)).isSome

/-- Collect constant IDs referenced in `t` within a node budget `b`, returning
`none` if the tree expansion of `t` exceeds `b` nodes. -/
def constsBudget : Term → Nat → List CId → Option (Nat × List CId)
  | _, 0, _ => none
  | .const c _, b + 1, acc =>
    some (b, if acc.contains c then acc else c :: acc)
  | .app f a _ _, b + 1, acc => do
    let (b1, acc1) ← constsBudget f b acc
    constsBudget a b1 acc1
  | .lam _ d t, b + 1, acc | .pi _ _ d t, b + 1, acc => do
    let (b1, acc1) ← constsBudget d b acc
    constsBudget t b1 acc1
  | .letE _ _ t v body, b + 1, acc => do
    let (b1, acc1) ← constsBudget t b acc
    let (b2, acc2) ← constsBudget v b1 acc1
    constsBudget body b2 acc2
  | .proj s _ e, b + 1, acc =>
    let acc' := if acc.contains s then acc else s :: acc
    constsBudget e b acc'
  | _, b + 1, acc => some (b, acc)

/-- The universe arguments of a Π-telescope's `i`-th binder domain head
(structural: no array indexing). -/
def domainUnivs? : Nat → Term → Option (List Univ)
  | 0, .pi _ _ d _ =>
    match d.spineL.1 with
    | .const _ us => some us
    | _ => none
  | i + 1, .pi _ _ _ t => domainUnivs? i t
  | _, _ => none

end Term

/-- The universe arguments of a recursor's major inductive, over the
recursor's own universe parameters (read off the major binder's domain). -/
def Program.majorUnivs (p : Program) (r : CId) : Option (List Univ) :=
  match p.decl? r with
  | some (.recr _ _ _ np nmot nmin ni _ _ ty) => ty.domainUnivs? (np + nmot + nmin + ni)
  | _ => none

/-- How deep a source term may nest: eight times the deepest term of a
committed program (256), and four times below the shallowest depth at which a
traversal from ingress to erasure overflows an 8 MiB stack (erasure, on a
constructor chain about 8,960 deep; the front end survives 32,768). Ingress
checks it per expression (`Ingress.depthBudget`), the recheck path again on the
whole program (`Recheck.checkSrc`), and erasure's fuel is the same
(`Lam.Erase.termFuel`). -/
def maxTermDepth : Nat := 2048

end IxCC.Src
