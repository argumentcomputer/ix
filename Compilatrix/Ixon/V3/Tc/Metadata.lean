import Compilatrix.Ixon.V3.Tc.Support

/-! Adapted from ix `0a31c8dbc63755924c645bf1afedc563e395e88a`, `Ix/Environment.lean`.
The anonymous checker uses the local v3 byte decoder and existing BLAKE3 interface.
See docs/ixon-v3.md for the adaptation and validation boundary. -/

namespace Compilatrix.Ixon.V3.Tc
namespace Metadata


open Std (HashMap)
open Blake3.Rust (Hasher)

/-! ## LEON (Lean Objective Notation) Tags (must match Rust env.rs) -/
def TAG_NANON : UInt8 := 0x00
def TAG_NSTR : UInt8 := 0x01
def TAG_NNUM : UInt8 := 0x02
def TAG_UZERO : UInt8 := 0x03
def TAG_USUCC : UInt8 := 0x04
def TAG_UMAX : UInt8 := 0x05
def TAG_UIMAX : UInt8 := 0x06
def TAG_UPARAM : UInt8 := 0x10
def TAG_UMVAR : UInt8 := 0x70
def TAG_EVAR : UInt8 := 0x20
def TAG_ESORT : UInt8 := 0x80
def TAG_EREF : UInt8 := 0x30
def TAG_EPRJ : UInt8 := 0x50
def TAG_ESTR : UInt8 := 0x81
def TAG_ENAT : UInt8 := 0x82
def TAG_EAPP : UInt8 := 0x83
def TAG_ELAM : UInt8 := 0x84
def TAG_EALL : UInt8 := 0x85
def TAG_ELET : UInt8 := 0x86
def TAG_EFVAR : UInt8 := 0x72
def TAG_EMVAR : UInt8 := 0x73
def TAG_EMDATA : UInt8 := 0x74
def TAG_DEFN : UInt8 := 0xA0
def TAG_RECR : UInt8 := 0xA1
def TAG_AXIO : UInt8 := 0xA2
def TAG_QUOT : UInt8 := 0xA3
def TAG_INDC : UInt8 := 0xA6
def TAG_CTOR : UInt8 := 0xC0
def TAG_THEO : UInt8 := 0xC1
def TAG_OPAQ : UInt8 := 0xC2
def TAG_MINT : UInt8 := 0xF1
def TAG_MSSTR : UInt8 := 0xF2
def TAG_MSINFO : UInt8 := 0xF3
def TAG_MSPRE : UInt8 := 0xF4
def TAG_MSYN : UInt8 := 0xF5
def TAG_MDVAL : UInt8 := 0xF6

/-! ## Name -/

/-- Content-addressed hierarchical name. Mirrors `Lean.Name` but carries a Blake3 hash at each node for O(1) equality. -/
inductive Name where
  | anonymous (hash : Address)
  | str (parent : Name) (s : String) (hash : Address)
  | num (parent : Name) (i : Nat) (hash : Address)
  deriving Repr, Nonempty

namespace Name

/-- Extract the Blake3 hash stored at the root of a `Name`. -/
def getHash : Name → Address
  | anonymous h => h
  | str _ _ h => h
  | num _ _ h => h

instance : BEq Name where
  beq a b := a.getHash == b.getHash

instance : Hashable Name where
  hash n := hash n.getHash  -- Uses Address's Hashable (first 8 bytes as LE u64)

/-- The anonymous (root) name with its canonical hash. -/
def mkAnon : Name := .anonymous <| Address.blake3 (ByteArray.mk #[TAG_NANON])

instance : Inhabited Name where
  default := mkAnon

/-- Construct a string name component, hashing the tag, parent hash, and string bytes. -/
def mkStr (pre: Name) (s: String): Name := Id.run <| do
  let mut h := Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_NSTR])
  h := h.update pre.getHash.hash
  h := h.update s.toUTF8
  .str pre s (finishHash h)

/-- Construct a numeric name component, hashing the tag, parent hash, and little-endian nat bytes. -/
def mkNat (pre: Name) (i: Nat): Name := Id.run <| do
  let mut h := Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_NNUM])
  h := h.update pre.getHash.hash
  h := h.update ⟨(tcNatBytesLE i)⟩
  .num pre i (finishHash h)

partial def toStringAux : Name → String
  | .anonymous _ => ""
  | .str (.anonymous _) s _ => s
  | .str parent s _ => s!"{toStringAux parent}.{s}"
  | .num (.anonymous _) n _ => s!"«{n}»"
  | .num parent n _ => s!"{toStringAux parent}.«{n}»"

instance : ToString Name where
  toString := toStringAux

/-- Dot-separated bare rendering — byte-for-byte mirror of the Rust
    `Name::pretty` (str components verbatim, num components as plain
    digits, NO `«»` escaping). The kernel's canonical aux ordering seeds
    on this exact string (`Compilatrix.Ixon.V3.Tc.canonicalAuxOrder` ↔ Rust
    `canonical_aux_order`), so `toString` (which escapes nums as `«n»`)
    must not be substituted there. -/
partial def pretty : Name → String
  | .anonymous _ => ""
  | .str (.anonymous _) s _ => s
  | .str parent s _ => s!"{pretty parent}.{s}"
  | .num (.anonymous _) n _ => s!"{n}"
  | .num parent n _ => s!"{pretty parent}.{n}"

def fromLeanName : Lean.Name → Name
  | .anonymous => .mkAnon
  | .str pre s => .mkStr (.fromLeanName pre) s
  | .num pre n => .mkNat (.fromLeanName pre) n

end Name


/-- Ix-local integer type used within `MData` values (mirrors `Int` for serialization). -/
inductive Int where
  | ofNat (n : Nat)
  | negSucc (n : Nat)
  deriving BEq, Repr, Inhabited

structure Substring where
  str : String
  startPos : Nat
  stopPos : Nat
  deriving BEq, Repr, Inhabited

inductive SourceInfo where
  | original (leading : Substring) (leadingPos : Nat)
      (trailing : Substring) (trailingPos : Nat)
  | synthetic (start : Nat) (stop : Nat) (canonical : Bool)
  | none
  deriving BEq, Repr, Inhabited

inductive SyntaxPreresolved where
  | namespace (name : Name)
  | decl (name : Name) (aliases : Array String)
  deriving BEq, Repr, Inhabited

inductive Syntax where
  | missing
  | node (info : SourceInfo) (kind : Name) (args : Array Syntax)
  | atom (info : SourceInfo) (val : String)
  | ident (info : SourceInfo) (rawVal : Substring) (val : Name)
      (preresolved : Array SyntaxPreresolved)
  deriving BEq, Repr, Inhabited, Nonempty

/-- A metadata value carried in an `mdata` expression node. -/
inductive DataValue where
  | ofString (s : String)
  | ofBool (b : Bool)
  | ofName (n : Name)
  | ofNat (n : Nat)
  | ofInt (i : Int)
  | ofSyntax (s : Syntax)
  deriving BEq, Repr, Inhabited

def hashInt (h : Hasher) (i : Int) : Hasher := Id.run do
  let mut h := h.update (ByteArray.mk #[TAG_MINT])
  match i with
  | .ofNat n =>
    h := h.update (ByteArray.mk #[0])
    h := h.update ⟨(tcNatBytesLE n)⟩
  | .negSucc n =>
    h := h.update (ByteArray.mk #[1])
    h := h.update ⟨(tcNatBytesLE n)⟩
  h

def hashSubstring (h : Hasher) (ss : Substring) : Hasher :=
  Id.run do
    let mut h := h.update (ByteArray.mk #[TAG_MSSTR])
    h := h.update ss.str.toUTF8
    h := h.update ⟨(tcNatBytesLE ss.startPos)⟩
    h := h.update ⟨(tcNatBytesLE ss.stopPos)⟩
    h

def hashSourceInfo (h : Hasher) (si : SourceInfo) : Hasher :=
  Id.run do
    let mut h := h.update (ByteArray.mk #[TAG_MSINFO])
    match si with
    | .original leading leadingPos trailing trailingPos =>
      h := h.update (ByteArray.mk #[0])
      h := hashSubstring h leading
      h := h.update ⟨(tcNatBytesLE leadingPos)⟩
      h := hashSubstring h trailing
      h := h.update ⟨(tcNatBytesLE trailingPos)⟩
    | .synthetic start stop canonical =>
      h := h.update (ByteArray.mk #[1])
      h := h.update ⟨(tcNatBytesLE start)⟩
      h := h.update ⟨(tcNatBytesLE stop)⟩
      h := h.update (ByteArray.mk #[if canonical then 1 else 0])
    | .none =>
      h := h.update (ByteArray.mk #[2])
    h

def hashSyntaxPreresolved (h : Hasher) (sp : SyntaxPreresolved)
    : Hasher := Id.run do
  let mut h := h.update (ByteArray.mk #[TAG_MSPRE])
  match sp with
  | .namespace name =>
    h := h.update (ByteArray.mk #[0])
    h := h.update name.getHash.hash
  | .decl name aliases =>
    h := h.update (ByteArray.mk #[1])
    h := h.update name.getHash.hash
    for a in aliases do
      h := h.update a.toUTF8
      h := h.update (ByteArray.mk #[0])
  h

private partial def hashSyntax (h : Hasher) (syn : Syntax)
    : Hasher := Id.run do
  let mut h := h.update (ByteArray.mk #[TAG_MSYN])
  match syn with
  | .missing =>
    h := h.update (ByteArray.mk #[0])
  | .node info kind args =>
    h := h.update (ByteArray.mk #[1])
    h := hashSourceInfo h info
    h := h.update kind.getHash.hash
    h := h.update ⟨(tcNatBytesLE args.size)⟩
    for arg in args do
      h := hashSyntax h arg
  | .atom info val =>
    h := h.update (ByteArray.mk #[2])
    h := hashSourceInfo h info
    h := h.update val.toUTF8
  | .ident info rawVal val preresolved =>
    h := h.update (ByteArray.mk #[3])
    h := hashSourceInfo h info
    h := hashSubstring h rawVal
    h := h.update val.getHash.hash
    h := h.update ⟨(tcNatBytesLE preresolved.size)⟩
    for pr in preresolved do
      h := hashSyntaxPreresolved h pr
  h

def hashDataValue (h : Hasher) (dv : DataValue)
    : Hasher := Id.run do
  let mut h := h.update (ByteArray.mk #[TAG_MDVAL])
  match dv with
  | .ofString s =>
    h := h.update (ByteArray.mk #[0])
    h := h.update s.toUTF8
  | .ofBool b =>
    h := h.update (ByteArray.mk #[1])
    h := h.update (ByteArray.mk #[if b then 1 else 0])
  | .ofName name =>
    h := h.update (ByteArray.mk #[2])
    h := h.update name.getHash.hash
  | .ofNat n =>
    h := h.update (ByteArray.mk #[3])
    h := h.update ⟨(tcNatBytesLE n)⟩
  | .ofInt i =>
    h := h.update (ByteArray.mk #[4])
    h := hashInt h i
  | .ofSyntax syn =>
    h := h.update (ByteArray.mk #[5])
    h := hashSyntax h syn
  h


end Metadata
end Compilatrix.Ixon.V3.Tc
