/-
  Canonical Lean types with embedded content-addressed hashes.

  Ix types mirror Lean's core types but include a Blake3 hash at each node,
  enabling O(1) equality checks and content-addressed storage.
-/

import Lean
import Blake3
import Std.Data.HashMap
import Batteries.Data.RBMap
import Ix.Address

namespace Ix

open Std (HashMap)

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
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_NSTR])
  h := h.update pre.getHash.hash
  h := h.update s.toUTF8
  .str pre s ⟨(h.finalizeWithLength 32).val⟩

/-- Construct a numeric name component, hashing the tag, parent hash, and little-endian nat bytes. -/
def mkNat (pre: Name) (i: Nat): Name := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_NNUM])
  h := h.update pre.getHash.hash
  h := h.update ⟨i.toBytesLE⟩
  .num pre i ⟨(h.finalizeWithLength 32).val⟩

partial def toStringAux : Name → String
  | .anonymous _ => ""
  | .str (.anonymous _) s _ => s
  | .str parent s _ => s!"{toStringAux parent}.{s}"
  | .num (.anonymous _) n _ => s!"«{n}»"
  | .num parent n _ => s!"{toStringAux parent}.«{n}»"

instance : ToString Name where
  toString := toStringAux

end Name

/-- Compare Ix.Name by hash for ordered collections. -/
def nameCompare (a b : Name) : Ordering :=
  compare a.getHash b.getHash

instance : Ord Name where
  compare := nameCompare

/-! ## Level -/

/-- Content-addressed universe level. Mirrors `Lean.Level` with a Blake3 hash at each node. -/
inductive Level where
  | zero (hash : Address)
  | succ (x : Level) (hash : Address)
  | max (x y : Level) (hash : Address)
  | imax (x y : Level) (hash : Address)
  | param (n : Name) (hash : Address)
  | mvar (n : Name) (hash : Address)
  deriving Repr, Nonempty

namespace Level

/-- Extract the Blake3 hash stored at the root of a `Level`. -/
def getHash : Level → Address
  | zero h => h
  | succ _ h => h
  | max _ _ h => h
  | imax _ _ h => h
  | param _ h => h
  | mvar _ h => h

def mkZero : Level := .zero <| Address.blake3 (ByteArray.mk #[TAG_UZERO])

def mkSucc (x: Level) : Level := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_USUCC])
  h := h.update x.getHash.hash
  .succ x ⟨(h.finalizeWithLength 32).val⟩

def mkMax (x y : Level) : Level := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_UMAX])
  h := h.update x.getHash.hash
  h := h.update y.getHash.hash
  .max x y ⟨(h.finalizeWithLength 32).val⟩

def mkIMax (x y : Level) : Level := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_UIMAX])
  h := h.update x.getHash.hash
  h := h.update y.getHash.hash
  .imax x y ⟨(h.finalizeWithLength 32).val⟩

def mkParam (n: Name) : Level := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_UPARAM])
  h := h.update n.getHash.hash
  .param n ⟨(h.finalizeWithLength 32).val⟩

def mkMvar (n: Name) : Level := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_UMVAR])
  h := h.update n.getHash.hash
  .mvar n ⟨(h.finalizeWithLength 32).val⟩

instance : BEq Level where
  beq a b := a.getHash == b.getHash

instance : Hashable Level where
  hash l := hash l.getHash  -- Uses Address's Hashable (first 8 bytes as LE u64)

instance : Inhabited Level where
  default := mkZero

end Level

/-! ## Auxiliary types for MData -/

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

/-! ## Expr -/

/-- Content-addressed expression. Mirrors `Lean.Expr` with a Blake3 hash at each node,
    enabling O(1) structural equality and content-addressed storage. -/
inductive Expr where
  | bvar (idx : Nat) (hash : Address)
  | fvar (name : Name) (hash : Address)
  | mvar (name : Name) (hash : Address)
  | sort (level : Level) (hash : Address)
  | const (name : Name) (levels : Array Level) (hash : Address)
  | app (fn arg : Expr) (hash : Address)
  | lam (name : Name) (ty body : Expr) (bi : Lean.BinderInfo) (hash : Address)
  | forallE (name : Name) (ty body : Expr) (bi : Lean.BinderInfo) (hash : Address)
  | letE (name : Name) (ty val body : Expr) (nonDep : Bool) (hash : Address)
  | lit (l : Lean.Literal) (hash : Address)
  | mdata (data : Array (Name × DataValue)) (expr : Expr) (hash : Address)
  | proj (typeName : Name) (idx : Nat) (struct : Expr) (hash : Address)
  deriving Repr, Nonempty

namespace Expr

def binderInfoTag : Lean.BinderInfo → UInt8
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

/-- Extract the Blake3 hash stored at the root of an `Expr`. -/
def getHash : Expr → Address
  | bvar _ h => h
  | fvar _ h => h
  | mvar _ h => h
  | sort _ h => h
  | const _ _ h => h
  | app _ _ h => h
  | lam _ _ _ _ h => h
  | forallE _ _ _ _ h => h
  | letE _ _ _ _ _ h => h
  | lit _ h => h
  | mdata _ _ h => h
  | proj _ _ _ h => h

instance : BEq Expr where
  beq a b := a.getHash == b.getHash

instance : Hashable Expr where
  hash e := hash e.getHash  -- Uses Address's Hashable (first 8 bytes as LE u64)

def mkBVar (x: Nat) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EVAR])
  h := h.update ⟨x.toBytesLE⟩
  .bvar x ⟨(h.finalizeWithLength 32).val⟩

def mkFVar (x: Name) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EFVAR])
  h := h.update x.getHash.hash
  .fvar x ⟨(h.finalizeWithLength 32).val⟩

def mkMVar (x: Name) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EMVAR])
  h := h.update x.getHash.hash
  .mvar x ⟨(h.finalizeWithLength 32).val⟩

def mkSort (x: Level) : Expr := Id.run <| do
  let h := Blake3.Hasher.init ()
  let h := h.update (ByteArray.mk #[TAG_ESORT])
  let h := h.update x.getHash.hash
  .sort x ⟨(h.finalizeWithLength 32).val⟩

def mkConst (x: Name) (us: Array Level): Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EREF])
  h := h.update x.getHash.hash
  for u in us do
    h := h.update u.getHash.hash
  .const x us ⟨(h.finalizeWithLength 32).val⟩

def mkApp (f a : Expr) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EAPP])
  h := h.update f.getHash.hash
  h := h.update a.getHash.hash
  .app f a ⟨(h.finalizeWithLength 32).val⟩

def mkLam (n : Name) (t b : Expr) (bi : Lean.BinderInfo) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_ELAM])
  h := h.update n.getHash.hash
  h := h.update t.getHash.hash
  h := h.update b.getHash.hash
  h := h.update (ByteArray.mk #[binderInfoTag bi])
  .lam n t b bi ⟨(h.finalizeWithLength 32).val⟩

def mkForallE (n : Name) (t b : Expr) (bi : Lean.BinderInfo) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EALL])
  h := h.update n.getHash.hash
  h := h.update t.getHash.hash
  h := h.update b.getHash.hash
  h := h.update (ByteArray.mk #[binderInfoTag bi])
  .forallE n t b bi ⟨(h.finalizeWithLength 32).val⟩

def mkLetE (n : Name) (t v b : Expr) (nd : Bool) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_ELET])
  h := h.update n.getHash.hash
  h := h.update t.getHash.hash
  h := h.update v.getHash.hash
  h := h.update b.getHash.hash
  h := h.update (ByteArray.mk #[if nd then 1 else 0])
  .letE n t v b nd ⟨(h.finalizeWithLength 32).val⟩

def mkLit (l : Lean.Literal) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  match l with
  | .natVal n =>
    h := h.update (ByteArray.mk #[TAG_ENAT])
    h := h.update ⟨n.toBytesLE⟩
  | .strVal s =>
    h := h.update (ByteArray.mk #[TAG_ESTR])
    h := h.update s.toUTF8
  .lit l ⟨(h.finalizeWithLength 32).val⟩

def mkProj (n : Name) (i : Nat) (e : Expr) : Expr := Id.run <| do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EPRJ])
  h := h.update n.getHash.hash
  h := h.update ⟨i.toBytesLE⟩
  h := h.update e.getHash.hash
  .proj n i e ⟨(h.finalizeWithLength 32).val⟩

def hashInt (h : Blake3.Hasher) (i : Int) : Blake3.Hasher := Id.run do
  let mut h := h.update (ByteArray.mk #[TAG_MINT])
  match i with
  | .ofNat n =>
    h := h.update (ByteArray.mk #[0])
    h := h.update ⟨n.toBytesLE⟩
  | .negSucc n =>
    h := h.update (ByteArray.mk #[1])
    h := h.update ⟨n.toBytesLE⟩
  h

def hashSubstring (h : Blake3.Hasher) (ss : Substring) : Blake3.Hasher :=
  Id.run do
    let mut h := h.update (ByteArray.mk #[TAG_MSSTR])
    h := h.update ss.str.toUTF8
    h := h.update ⟨ss.startPos.toBytesLE⟩
    h := h.update ⟨ss.stopPos.toBytesLE⟩
    h

def hashSourceInfo (h : Blake3.Hasher) (si : SourceInfo) : Blake3.Hasher :=
  Id.run do
    let mut h := h.update (ByteArray.mk #[TAG_MSINFO])
    match si with
    | .original leading leadingPos trailing trailingPos =>
      h := h.update (ByteArray.mk #[0])
      h := hashSubstring h leading
      h := h.update ⟨leadingPos.toBytesLE⟩
      h := hashSubstring h trailing
      h := h.update ⟨trailingPos.toBytesLE⟩
    | .synthetic start stop canonical =>
      h := h.update (ByteArray.mk #[1])
      h := h.update ⟨start.toBytesLE⟩
      h := h.update ⟨stop.toBytesLE⟩
      h := h.update (ByteArray.mk #[if canonical then 1 else 0])
    | .none =>
      h := h.update (ByteArray.mk #[2])
    h

def hashSyntaxPreresolved (h : Blake3.Hasher) (sp : SyntaxPreresolved)
    : Blake3.Hasher := Id.run do
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

private partial def hashSyntax (h : Blake3.Hasher) (syn : Syntax)
    : Blake3.Hasher := Id.run do
  let mut h := h.update (ByteArray.mk #[TAG_MSYN])
  match syn with
  | .missing =>
    h := h.update (ByteArray.mk #[0])
  | .node info kind args =>
    h := h.update (ByteArray.mk #[1])
    h := hashSourceInfo h info
    h := h.update kind.getHash.hash
    h := h.update ⟨args.size.toBytesLE⟩
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
    h := h.update ⟨preresolved.size.toBytesLE⟩
    for pr in preresolved do
      h := hashSyntaxPreresolved h pr
  h

def hashDataValue (h : Blake3.Hasher) (dv : DataValue)
    : Blake3.Hasher := Id.run do
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
    h := h.update ⟨n.toBytesLE⟩
  | .ofInt i =>
    h := h.update (ByteArray.mk #[4])
    h := hashInt h i
  | .ofSyntax syn =>
    h := h.update (ByteArray.mk #[5])
    h := hashSyntax h syn
  h

def mkMData (data : Array (Name × DataValue)) (e : Expr) : Expr := Id.run do
  let mut h := Blake3.Hasher.init ()
  h := h.update (ByteArray.mk #[TAG_EMDATA])
  h := h.update ⟨data.size.toBytesLE⟩
  for (name, dv) in data do
    h := h.update name.getHash.hash
    h := hashDataValue h dv
  h := h.update e.getHash.hash
  .mdata data e ⟨(h.finalizeWithLength 32).val⟩

instance : Inhabited Expr where
  default := mkBVar 0

end Expr

/-! ## Constant Types -/

/-- Common fields shared by all constant declarations: name, universe parameters, and type. -/
structure ConstantVal where
  name : Name
  levelParams : Array Name
  type : Expr
  deriving Repr, BEq

structure AxiomVal where
  cnst : ConstantVal
  isUnsafe : Bool
  deriving Repr, BEq

structure DefinitionVal where
  cnst : ConstantVal
  value : Expr
  hints : Lean.ReducibilityHints
  safety : Lean.DefinitionSafety
  all : Array Name
  deriving Repr, BEq

structure TheoremVal where
  cnst : ConstantVal
  value : Expr
  all : Array Name
  deriving Repr, BEq

structure OpaqueVal where
  cnst : ConstantVal
  value : Expr
  isUnsafe : Bool
  all : Array Name
  deriving Repr, BEq

structure QuotVal where
  cnst : ConstantVal
  kind : Lean.QuotKind
  deriving Repr, BEq

structure InductiveVal where
  cnst : ConstantVal
  numParams : Nat
  numIndices : Nat
  all : Array Name
  ctors : Array Name
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool
  deriving Repr, BEq

structure ConstructorVal where
  cnst : ConstantVal
  induct : Name
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool
  deriving Repr, BEq

structure RecursorRule where
  ctor : Name
  nfields : Nat
  rhs : Expr
  deriving Repr, BEq

structure RecursorVal where
  cnst : ConstantVal
  all : Array Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : Array RecursorRule
  k : Bool
  isUnsafe : Bool
  deriving Repr, BEq

/-- Sum type of all Lean constant declarations (axioms, definitions, theorems, inductives, etc.). -/
inductive ConstantInfo where
  | axiomInfo (v : AxiomVal)
  | defnInfo (v : DefinitionVal)
  | thmInfo (v : TheoremVal)
  | opaqueInfo (v : OpaqueVal)
  | quotInfo (v : QuotVal)
  | inductInfo (v : InductiveVal)
  | ctorInfo (v : ConstructorVal)
  | recInfo (v : RecursorVal)
  deriving Repr

/-- Extract the `ConstantVal` common fields from any `ConstantInfo` variant. -/
def ConstantInfo.getCnst : ConstantInfo → ConstantVal
  | .axiomInfo v => v.cnst
  | .defnInfo v => v.cnst
  | .thmInfo v => v.cnst
  | .opaqueInfo v => v.cnst
  | .quotInfo v => v.cnst
  | .inductInfo v => v.cnst
  | .ctorInfo v => v.cnst
  | .recInfo v => v.cnst

/-! ## Environment -/

/-- A content-addressed Lean environment: a map from `Ix.Name` to `ConstantInfo`. -/
structure Environment where
  consts : HashMap Name ConstantInfo

/-- Raw environment data as arrays (returned from Rust FFI).
    Use `toEnvironment` to convert to Environment with HashMaps. -/
structure RawEnvironment where
  consts : Array (Name × ConstantInfo)
  deriving Repr, Inhabited

/-- Convert raw arrays to Environment with HashMaps.
    This is done on the Lean side for correct hash function usage. -/
def RawEnvironment.toEnvironment (raw : RawEnvironment) : Environment :=
  { consts := raw.consts.foldl (init := {}) fun m (k, v) => m.insert k v }

/-- Convert Environment to raw arrays for FFI usage. -/
def Environment.toRaw (env : Environment) : RawEnvironment :=
  { consts := env.consts.toArray }

/-! ## Context Types for Compilation -/

/-- Mutual context mapping Name to index within block. -/
abbrev MutCtx := Batteries.RBMap Name Nat nameCompare

instance : Ord MutCtx where
  compare a b := compare a.toList b.toList

/-- Set of Names (for tracking constants in a block). -/
abbrev NameSet := Batteries.RBSet Name nameCompare

end Ix
