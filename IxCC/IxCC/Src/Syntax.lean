import IxCC.Ixon.V3.Const
import IxCC.Src.Level
import IxCC.Src.NatMap
import IxCC.Src.Word

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
content-addressed. Modes are carried exactly and never read by the
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
  /-- Written Ixon v5 mode (`input : BinderMode` and arrow `result : ResultMode`):
  read by relevance (`isErased`), table transport, specialisation (`isUnique`),
  ownership (`zeroRcBinder`), and RC production. -/
  mode : V3.AllMode := {}
  /-- Untrusted relevance annotation of the parameter. -/
  rel : Rel := .rel
  /-- When this λ is a proof (the A1 guard): the zero condition of its
  codomain's sort. -/
  propWhen : PropWhen := .never
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Binder

def binderMode (b : Binder) : V3.BinderMode := b.mode.input
def resultMode (b : Binder) : V3.ResultMode := b.mode.result
def usage (b : Binder) : V3.Usage := b.mode.usage
def isUnique (b : Binder) : Bool := b.mode.isUnique
def isBorrowed (b : Binder) : Bool := b.mode.isBorrowed
def isErased (b : Binder) : Bool := b.mode.isErased
def isDefault (b : Binder) : Bool := b.mode.isDefault

end Binder

inductive Term where
  | var (i : Nat)
  | sort (u : Univ)
  | const (c : CId) (us : List Univ)
  /-- `a` is irrelevant where `r` is; elsewhere it is passed by `m`. -/
  | app (f a : Term) (m : Mode) (r : Rel)
  | lam (b : Binder) (dom body : Term)
  | pi (b : Binder) (dom cod : Term)
  | letE (nonDep : Bool) (letMode : V3.LetMode) (r : Rel) (ty val body : Term)
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
  /-- A fixed-width word operation (stage W1, F6w): `op` at width `w`, its meaning the stored
  theorem `thm`, which states the operation on `UIntN.ofNat` words as `UIntN.ofNat` of a
  formula over `Nat`'s operations (`ofNat`'s: the bridge to the constructor tower). -/
  | word (w : Width) (op : WordOp) (thm : CId)
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
  /-- `Nat.le` (the kernel's role `natLe`): the bound of a word's bridge (stage W1). -/
  natLe : Option Nat := none
  /-- Fixed-width words (stage W1), which no kernel role names, so always the fixed table's: per
  width the type `UIntN` and its constructor `UIntN.ofBitVec`, the inner constructors of a
  word's tower `BitVec.ofFin` and `Fin.mk`, and the primitive operations with their pins. -/
  wordTypes : List (Width × Nat) := []
  wordCtors : List (Width × Nat) := []
  bitVecOfFin : Option Nat := none
  finMk : Option Nat := none
  wordOps : List ((Width × WordOp) × Nat) := []
  deriving Repr, Inhabited

namespace Pins

/-- The fixed table: the addresses of `fixtures/ixon-v4/primitives.tsv` and
`src-tables.tsv` (`Src.Pinned`'s rows, which `#guard`s tie to these numbers):
the default pins of a program built without ingress, and the allowlist's
address (`KernelFront.pinsOfTable`). -/
def fixed : Pins :=
  { nat := some 0xee5d424f6fbb5410ce82a4657c586ed8dc57eb2588947578636676e42ed0072b
    natZero := some 0x09851a0422a18822447d9785123b46be1d53f1a2d0137992fe16ae693cb3f07d
    natSucc := some 0x757ca9ddbbfdfcb939a42c164c435dede6d6d234279f89e1d13668f3ef4d891d
    natRec := some 0xa37d28a22a02cd33b3c87380f45c8990c95cce53f154ad332a9cb5f9b1638753
    bool := some 0x77db82d7052a606eaaf324893161d6989049ef4e0f393e2fe9edaf52f4225ed8
    boolTrue := some 0xef156463a527bfd236472e606b2ccddf73f4585195e365e0430ee3c20921d8cc
    boolFalse := some 0xa5fc856de635cfc40ab703eea51cb704dce6985fd7de921f94b8d635e9d3667f
    eq := some 0x9d3c7bcfcc8f1f1661bce87d371a5da0d5188c1bc05def21d4aa176138c91b10
    decIsFalse := some 0xf1fe3bef188e3a340b3ba29ae5ecdd265c970439e3993b5b3fb3bf8d85342663
    decIsTrue := some 0x23e3b904854e2f117770ac908a90ef0bdd50bf2ed11a6274b8c233db4cdb866f
    prims :=
      [ (.add, 0xa04e7e6b19f5e48dbb0b53dae24db5dcc1b1a98c8e97551db8fb4b5f4a14caa8),
        (.sub, 0xf8410bb7b91afaa0cb6f9162faeee2a682e98cde21acf19712380f4e9dbcbf00),
        (.mul, 0x7e736639472dcc920bdc54d8ff0255a4c03b3c05375eacf08814e341deebd331),
        (.div, 0x2f22b34c61096990d6ce6b2485b31ed9696feaae6902855de6116b6a58e90331),
        (.mod, 0xfdc3d6f24a0d4968b0e2bd5502a95a54506566a6d6f8bf5673b95b5278da8cdd),
        (.pow, 0x473d7239744c820ddb45b6ce56d0506734ba90e5699e985444fd7a6647e9b0a0),
        (.gcd, 0xf1286e3ceac7bf4afa1c95a2f70c69ffc0667295035661b9be57ed6f0b08babb),
        (.beq, 0xdd0668fbe8c2b2a2260e95da62a2bea5df42c670a3e95ccffea03c3a7ffdc1c2),
        (.ble, 0xa939cc7925834d04a7ced860c5c44484231c9f5c44728d83d55f19c08037f3b4),
        (.land, 0xa4f25748d7376a55ce31462ae4ad90ac33181a6000b9908f398cc850ad865f67),
        (.lor, 0x0330cfdb86165b40463f2931bf794d375aa7acecd21feaabe1319e03fd80a5d9),
        (.xor, 0x7c79bfc28b46cca9137779a26b8da0b4aedc718eaf554f76e6e38650074327d6),
        (.shiftLeft, 0xc2a2258d56e14ebdb8c9986365cf0c0f6dfe4128a8faf847dd5e50b4ae7bb310),
        (.shiftRight, 0x74a4836a0eddfd07e45e5da0929df974e0caef28fd26001f7de1712d5beddd4e),
        (.pred, 0xb8d8ab1875dbb7fdb150a34988c32d7006204b9506a0ba148f453e5c555bf218) ]
    stdAxioms :=
      [ 0xa56bf0c90cd1e293cacb5ad709212c8ba11e3473c8b8bef8ca00e21dc6d094e1,
        0x84f6bad412f1b4ea4396a0c4d15eefc28d3078521bf00621cfbbfa5b2fe439cf,
        0xc68061d89f1d05288db51b6befa396d3c7d7941ea105a48609c92dec9afaf3bb ]
    opaqueByValue := [0xef85cfcf05fee3d8108813b6b572dc2d4561a7b1ea5f177f245fe5c5adca5be9]
    natLe := some 0xe21c596c35b75e7bc59cf21bf4bb5cd494179366612215fb0b263bca4236ecdd
    wordTypes :=
      [ (.w8, 0x93be7ce2ba5276dcfdc71099cb3d30f67a72965636ea4d24ceb7a845d2f52ca6),
        (.w16, 0xf759e0d786f5911dcacd44a51f546ede706e4aecc7027dacaf336a09a8ad31af),
        (.w32, 0x70fc2340e867d05c63df7e616cfa1f937fb080d2db7eb49b7e223ad2c9fdf203),
        (.w64, 0x7a31307b020bb907fa3c972dc19cdafcf213109498e9b124fd0466a71b429934) ]
    wordCtors :=
      [ (.w8, 0x04059c9d4b0851a74177a675add3c99dd3042e41e37ca871d5e8000f5bb8412a),
        (.w16, 0x6c9bc90402a456c3a7579e8e0beb4ac431c47afdfa0c78d328303fae8f639f3e),
        (.w32, 0x1ece74a7af34175db6c6633af4cea37e9490f262835b2b46568faa7cdc4b8c02),
        (.w64, 0x3c0514850ce61d4ea2be26f444140aa56badd7d3fec77d6b3dce56a6ba09acef) ]
    bitVecOfFin := some 0x78863b037be3f1025dfb3cb04942b82942e1c7dd1dd97b285648c7e62b6766cf
    finMk := some 0x5539b6daf9043f34c808412384e515aa6503e72b411d04ef000bddc11a7b5a97
    wordOps :=
      [ ((.w8, .add), 0xfc56b9c28ed33de651eb2987cdcd3955c15524c6a16900db20b7078821991b06),
        ((.w8, .sub), 0xdf4b7256512999e59132ce21043a45d46b7b3355af2f1233a1d705de1eeca80f),
        ((.w8, .mul), 0xec21ae6609c843851a3cda0b0f68fe2d04b6fff27d46060a027e67ddb5f73ac2),
        ((.w8, .div), 0xf5a25c82817d935f7a2e785f814392e4e71dfa3d37188ae408f6c3e8b3fb5c6b),
        ((.w8, .mod), 0x840b89085bb989e5e7a526edb48d5b58a06ce5fe5126e4cd4fb4614499496e11),
        ((.w8, .land), 0x50a6b934d8a45dafd986b76abc29be993d5cc1ecd5bae3f167892070bbb9832e),
        ((.w8, .lor), 0x96c0b1970d97a4ccd8b85043b4eec2625a6ebc491a0ff7be7ba6e535d2cef780),
        ((.w8, .xor), 0x0e5f87983f211af1ba7ebea7a86c404fda131d254d27a96e786175a0c388a5e1),
        ((.w8, .shiftLeft), 0x59377487e72b3fa1cd4d49b5cb00ecb37224a446b0295ed0f72d7f2bc9863f75),
        ((.w8, .shiftRight), 0xefdd5ec1d9e2f2f96c0f6517d676b173fec1a418a8eca5daa48d0039caa52a6f),
        ((.w8, .complement), 0x95c05c20957bce2d90216a491308c578310272cbea53d30dc1a7327b9128f3fa),
        ((.w8, .neg), 0xce7013ec1563bccdf1482180612610f8397395d1c8be5c09cd2f6617edbb8909),
        ((.w8, .ofNat), 0x7314090c6dff1b634aaa2283415a27cbc7db41d03f5664f18530b04692a8e3da),
        ((.w8, .toNat), 0xa0c2c77fb7f42644f635a3d25f914baaa15a5cbfc006815c32d565751fa6c8ed),
        ((.w8, .convert .w16), 0x0bb457d6cb7a7d85b13e0a3d77411fac31d5b5af1ce4a95c4b8a100e724a6346),
        ((.w8, .convert .w32), 0x446c80a5509fea7cb9a5f3f4dec8304eb10ac0913f5b6453a113c3ae4eb1716d),
        ((.w8, .convert .w64), 0x8ff9b8c0280d94eba5e39a380deac9689afb95558837bb62106a60e1f6a28a2f),
        ((.w16, .add), 0x0d8ee0047e4ef6120cb9acbcd75bb1beddc556095ed601034ab01a3571a6b938),
        ((.w16, .sub), 0x886a61979c44d21b38e1d1ebb83605a9d9b8a1da5bd275da0f91ab095535a4a1),
        ((.w16, .mul), 0xda120d4bf9fb8f8b5957136c0a2f89dda72b1464cb2531a6acef70bc7f13ccbc),
        ((.w16, .div), 0x304126634a53a9bd9c0aa1d5cc09ed81f4e5cc353546f16bc8cf7ddfe760bbd9),
        ((.w16, .mod), 0x5db1e86ed013772016f4a68c3cb006c43cdebc7580c83a830668771246267961),
        ((.w16, .land), 0xb68f086e1d2c3bddd0d54576bdf3dbb03b2d0df738ef04718fc0aeb5f9d213d7),
        ((.w16, .lor), 0x0ca38582e573fd089c72bd34f542279ed1fe9b9442aa9244c12a1eaf8f713cc0),
        ((.w16, .xor), 0xa53c4613de0f7369a77def74fd3b15138134759842bc4d9d0fcc751cb6d5e731),
        ((.w16, .shiftLeft), 0xaf89a898af86a8964ab99e6ff760c3f52fd2fc980ea8f227f4e887e823855ef4),
        ((.w16, .shiftRight), 0xc515d10a2c94243e4acafd64a02e4f80ffdf53c31b1d6072e023c74de2579258),
        ((.w16, .complement), 0x43c230af8c26fd5039880eaa34789cf6cb860f96152c979720aa6056000ec165),
        ((.w16, .neg), 0x7ba579706ac7835aaefb4c96c4636705c8107d90d82b952c4bc56a751517bd8a),
        ((.w16, .ofNat), 0x686dd7580df6137349cba7e43d627beb19f90dea4d26e5c7676fc004d267f8fe),
        ((.w16, .toNat), 0xe39b3eacafc58b79d948a708d035ada7fba42628ce9f88ed978fef9a428c773f),
        ((.w16, .convert .w8), 0x804360d6c65855cb209bbf3f860239ae2b93d87fae350353803d8a46990923bc),
        ((.w16, .convert .w32), 0x77e6472ef4ddd35faae6eedfce69840cbd90416481db76796cd3e7d82c7e4ec5),
        ((.w16, .convert .w64), 0x7f22212ead635eab0d608f557e282c9e7e7d9368e89f4e142a8a3e3a91bbef35),
        ((.w32, .add), 0x2777f287d20586bfc762300a0cddbb148a958f5fca01d28426863740c318fcbd),
        ((.w32, .sub), 0x8008fe38585660bee22027ae68ec3094fb8f89fe6fcb06c24cde9eee1cadfed9),
        ((.w32, .mul), 0x575b5ba790bc80b3a77447cdff119ca86e1735c5c2185dae069b309524e3daa2),
        ((.w32, .div), 0x9c84824847bafe925934238376bf52015ae8b507e33756b9fc76ec9f72f92e9b),
        ((.w32, .mod), 0x803b1924aef6be11adf6026fef90edc7b3d05c3ff36acf50b4f93b5c1576a068),
        ((.w32, .land), 0x2663e08c39482aac31a319b86a84c47c8677f97cc034fe790e58f915f2113392),
        ((.w32, .lor), 0x3e946ce00a8daf1a672e46d35d060a02c83e4671e0595444b6f5e2944972a334),
        ((.w32, .xor), 0x2b860fd097e555cf8d6f1a1431b455f656d5915d6f42ba83c6cf22f5ddfeb8bb),
        ((.w32, .shiftLeft), 0xa71f5748e75913d4934dbff9cc01a93bef1df27825ce49d6094df587d95d1892),
        ((.w32, .shiftRight), 0xcffba7a6990ebd5bc956dfebb16439f264b94b9084da72886ccdb22fc712912c),
        ((.w32, .complement), 0x2af0ca4f6dfc7b45feb5fef246fa58918ce2ff4f939ef2e4913861611a5c456e),
        ((.w32, .neg), 0xea7fc9de90dc64b91630e52422717c1430ee672e9c88cba6fb276577e276d534),
        ((.w32, .ofNat), 0x66e93962b9fd7c59ceb25f464d743cc91e1a71ede93531b8c2845365656247bb),
        ((.w32, .toNat), 0x5be965ce1a377f2906072c2e3ece076a225492b6494dd03f32104a7ce4d8bbd5),
        ((.w32, .convert .w8), 0x4432c7bb164ab242c83d7561b3ed52dd07e7b22057ad8f7def5811e3e7357625),
        ((.w32, .convert .w16), 0x6730293c3cec038e03b7afd228e657a2e946de72f54d66a3e77a7ebbd66875fd),
        ((.w32, .convert .w64), 0x4810543904c09cbe37bd3ae0aa62120cf56970c6eb96d841541093092d6bd548),
        ((.w64, .add), 0xaede79e0eb58dd8bbc0ebc8a62fcf9b4b0f1c4d9a2cb307aa52f55e4856070d7),
        ((.w64, .sub), 0x5d5bf18754b0e2b117409cf433957717f320174dd0c9249429067e1dadd5dd2b),
        ((.w64, .mul), 0x56201633afdcbcec0c2ea478dafaa294c0567c4cacf5c9213acee77ef75afccf),
        ((.w64, .div), 0x53771b78fc95038290543c451a98664a2f3c387eb7eb85ad6d6ed386d560491e),
        ((.w64, .mod), 0x6653bc25dd5801201db6731b97976abb34d5425bbf93198f93e4e0d598ff6aca),
        ((.w64, .land), 0x712a83ec9fe8a1cf51db851554a7e746fc31a6ea1065ea0d4913faa4df2b4639),
        ((.w64, .lor), 0x91b5ab70755d2d22a212b8e63a9dafeb6c67c0dbf5a5948277f13d66ce1bd8ed),
        ((.w64, .xor), 0x6ee654a8024610d5f893b9bb779b3059e50529cb0fec792e07c63accc05b8456),
        ((.w64, .shiftLeft), 0xa797b319a421a39ec619fd8d4dbdb9caf087f29e4fc5c73d977e182f2d97f1c9),
        ((.w64, .shiftRight), 0x6a3eaecb08c2e75bac09d8ff001da3838511416290bdcbac59c049e54a6a694a),
        ((.w64, .complement), 0xf39f5aaec910251b1fe78b7cb790f0197efb4a1ab2b6088918bc6497c92b7928),
        ((.w64, .neg), 0x333d59279c125c3b76eb9cb8ab196dac21962f45933b3735757b93eca095bb12),
        ((.w64, .ofNat), 0x39d1228356e89b66707825b482f59a27b84417b58db3866939065878cabf7919),
        ((.w64, .toNat), 0xb15266d22b62aabf5799e9008036bbfcca016b7fee6d5937300e133079471ed2),
        ((.w64, .convert .w8), 0x7b9034c00374a5b444bfe0a5310cd8db77a523f68b7f3e2161c0b411b3c85fc8),
        ((.w64, .convert .w16), 0x46fc52f9a4f722e836fb971ec1d6f46d57f36eac9f6059bdd35bd4fef779d8d9),
        ((.w64, .convert .w32), 0xa313a2c84cf34dc3d899b5c485bdf77bcb91bd60988fedbc6eafab37ee7c6317) ] }


/-- The pin of a primitive operation, if it has one. -/
def prim? (p : Pins) (op : PrimOp) : Option Nat := p.prims.lookup op

/-- The pin of a word operation, if it has one. -/
def wordOp? (p : Pins) (w : Width) (op : WordOp) : Option Nat := p.wordOps.lookup (w, op)

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
  /-- Fixed-width words (stage W1): per width the constructor `UIntN.ofBitVec`, and the inner
  constructors `BitVec.ofFin` and `Fin.mk` of a word's tower, which F6w reads and builds. -/
  wordCtors : List (Width × CId) := []
  bitVecOfFin : Option CId := none
  finMk : Option CId := none
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
  | .pi b d t => let (bs, body) := pis t; ((b, d) :: bs, body)
  | t => ([], t)

/-- The number of leading Π binders. -/
def piCount : Term → Nat
  | .pi _ _ t => t.piCount + 1
  | _ => 0

def lamCount : Term → Nat
  | .lam _ _ t => t.lamCount + 1
  | _ => 0

/-- Syntactic equality ignoring modes and annotations (the
equality of the table checks). -/
def eqv : Term → Term → Bool
  | .var i, .var j => i == j
  | .sort u, .sort v => u == v
  | .const c us, .const d vs => c == d && us == vs
  | .app f a _ _, .app g b _ _ => eqv f g && eqv a b
  | .lam _ d t, .lam _ e u => eqv d e && eqv t u
  | .pi _ d t, .pi _ e u => eqv d e && eqv t u
  | .letE _ _ _ t v b, .letE _ _ _ t' v' b' => eqv t t' && eqv v v' && eqv b b'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && eqv e e'
  | .natLit n, .natLit m => n == m
  | .strLit s, .strLit s' => s == s'
  | _, _ => false

/-- Ordinary Lean source modes: default `AllMode` on every λ and Π, and
default `LetMode` on every `let` (the Src reading of `V3.Expr.leanFragment`). -/
def leanFragment : Term → Bool
  | .lam b d t | .pi b d t => b.isDefault && d.leanFragment && t.leanFragment
  | .letE _ m _ t v b => m.isDefault &&
      t.leanFragment && v.leanFragment && b.leanFragment
  | .app f a _ _ => f.leanFragment && a.leanFragment
  | .proj _ _ e => e.leanFragment
  | _ => true

/-- Whether constant `c` occurs syntactically. -/
def mentions (c : CId) : Term → Bool
  | .const d _ => c == d
  | .app f a _ _ => f.mentions c || a.mentions c
  | .lam _ d t | .pi _ d t => d.mentions c || t.mentions c
  | .letE _ _ _ t v b => t.mentions c || v.mentions c || b.mentions c
  | .proj s _ e => s == c || e.mentions c
  | _ => false

/-- Number of nodes (a tree size; shared subterms count once per use). -/
def nodes : Term → Nat
  | .app f a _ _ => f.nodes + a.nodes + 1
  | .lam _ d t | .pi _ d t => d.nodes + t.nodes + 1
  | .letE _ _ _ t v b => t.nodes + v.nodes + b.nodes + 1
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
  | .lam _ d t, b + 1 | .pi _ d t, b + 1 => do
    let b1 ← nodesBudget d b
    nodesBudget t b1
  | .letE _ _ _ t v body, b + 1 => do
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
  | .lam _ d t, b + 1, acc | .pi _ d t, b + 1, acc => do
    let (b1, acc1) ← constsBudget d b acc
    constsBudget t b1 acc1
  | .letE _ _ _ t v body, b + 1, acc => do
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
  | 0, .pi _ d _ =>
    match d.spineL.1 with
    | .const _ us => some us
    | _ => none
  | i + 1, .pi _ _ t => domainUnivs? i t
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
