/-
  Ix.Frontend.Syntax: Pure constructors and syntax node helpers for the Ix Frontend.

  All content hashes are computed via `Address.admissionHash` (`Address.blake3Pure` in the
  kernel logic, `@[implemented_by Address.blake3]` on the host), so every constructor is
  100% pure, total, and kernel-reducible while producing byte-identical `Address` digests
  to `Ix.Environment`.
-/
module

public import Ix.Environment
public import Ix.Address.Admission
public import IxC.Ixon.Types.Modes
public import IxC.Ixon.Types.Contract

@[expose] public section

namespace Ix.Frontend

/-- Pure `Nat` total order using `Nat.ble` and `Nat.beq` (zero `Decidable` proof terms). -/
@[inline] def natCmpPure (a b : Nat) : Ordering :=
  if Nat.ble (a + 1) b then .lt
  else if Nat.beq a b then .eq
  else .gt

/-- Structural byte-list equality on `List UInt8` (zero proof terms). -/
def bytesBeq : List UInt8 → List UInt8 → Bool
  | [], []           => true
  | a :: as, b :: bs => Nat.beq a.toNat b.toNat && bytesBeq as bs
  | _, _             => false

/-- Structural lexicographical comparison on `List UInt8` (zero `WellFounded.fix` or proof terms). -/
def bytesCmp : List UInt8 → List UInt8 → Ordering
  | [], []           => .eq
  | [], _ :: _       => .lt
  | _ :: _, []       => .gt
  | a :: as, b :: bs =>
    let na := a.toNat
    let nb := b.toNat
    if Nat.ble (na + 1) nb then .lt
    else if Nat.ble (nb + 1) na then .gt
    else bytesCmp as bs

/-- Structural character-list equality on `List Char` (zero proof terms, zero UTF-8 re-encoding). -/
def charsBeq : List Char → List Char → Bool
  | [], []           => true
  | a :: as, b :: bs => Nat.beq a.val.toNat b.val.toNat && charsBeq as bs
  | _, _             => false

/-- Structural lexicographical comparison on `List Char` (zero `WellFounded.fix` or proof terms). -/
def charsCmp : List Char → List Char → Ordering
  | [], []           => .eq
  | [], _ :: _       => .lt
  | _ :: _, []       => .gt
  | a :: as, b :: bs =>
    let na := a.val.toNat
    let nb := b.val.toNat
    if Nat.ble (na + 1) nb then .lt
    else if Nat.ble (nb + 1) na then .gt
    else charsCmp as bs

/-- Pure structural equality on `String`: checks O(1) `utf8ByteSize` first so strings of
    different byte lengths never expand `KLiteral.Str` to `List Char` in `IxVM`. -/
@[inline] def strBeqPure (a b : String) : Bool :=
  Nat.beq a.utf8ByteSize b.utf8ByteSize && charsBeq a.toList b.toList

/-- Pure structural shortlex order on `String` (compares O(1) `utf8ByteSize` first,
    only expanding `.toList` when two strings have the same UTF-8 byte length). -/
@[inline] def strCmpPure (a b : String) : Ordering :=
  match natCmpPure a.utf8ByteSize b.utf8ByteSize with
  | .eq => charsCmp a.toList b.toList
  | ord => ord

scoped instance (priority := 2000) : BEq String where
  beq := strBeqPure

scoped instance (priority := 2000) : Ord String where
  compare := strCmpPure

/-- Pure string concatenation (`String.ofList (a.toList ++ b.toList)`) so that
    `parseSource` and `elabSource` have zero `opaque` constants in their transitive closure. -/
@[inline] def strAppendPure (a b : String) : String :=
  String.ofList (a.toList ++ b.toList)

scoped instance (priority := 2000) : Append String where
  append := strAppendPure

/-- Pure `intercalate` over `List String` using `strAppendPure`. -/
def strIntercalatePure (sep : String) : List String → String
  | []      => ""
  | [x]     => x
  | x :: xs => strAppendPure x (strAppendPure sep (strIntercalatePure sep xs))

/-- Placeholder empty `Address` used during intermediate AST/expression construction
    so that `Address.admissionHash` (`Blake3.Pure.hash`) is not evaluated on every
    temporary `Name`, `Level`, or `Expr` node during parsing and elaboration.
    Exact 32-byte Merkle hashes are populated on demand via `Name.computeHash` and `ConstantInfo.rehash`. -/
def dummyAddr : Address := ⟨ByteArray.mk #[]⟩

/-! ## Pure `Ix.Name` Constructors & Operations -/

namespace Name

/-- The anonymous root `Ix.Name` (with deferred `dummyAddr`). -/
def mkAnon : Ix.Name :=
  .anonymous dummyAddr

/-- Construct a string component `Ix.Name` (with deferred `dummyAddr`). -/
def mkStr (pre : Ix.Name) (s : String) : Ix.Name :=
  .str pre s dummyAddr

/-- Construct a numeric component `Ix.Name` (with deferred `dummyAddr`). -/
def mkNat (pre : Ix.Name) (i : Nat) : Ix.Name :=
  .num pre i dummyAddr

/-- Compute the canonical 32-byte `Address` of an `Ix.Name` via `Address.admissionHash`,
    reusing an already-populated 32-byte hash when present. -/
def computeHash : Ix.Name → Address
  | .anonymous h =>
    if Nat.beq h.hash.size 32 then h
    else Address.admissionHash (ByteArray.mk #[Ix.TAG_NANON])
  | .str p s h =>
    if Nat.beq h.hash.size 32 then h
    else Address.admissionHash (ByteArray.mk #[Ix.TAG_NSTR] ++ (computeHash p).hash ++ s.toUTF8)
  | .num p i h =>
    if Nat.beq h.hash.size 32 then h
    else Address.admissionHash (ByteArray.mk #[Ix.TAG_NNUM] ++ (computeHash p).hash ++ ⟨i.toBytesLE⟩)

/-- Recursively populate the canonical 32-byte `Address` hash on every node of an `Ix.Name`. -/
def rehash : Ix.Name → Ix.Name
  | n@(.anonymous h) =>
    if Nat.beq h.hash.size 32 then n
    else .anonymous (Address.admissionHash (ByteArray.mk #[Ix.TAG_NANON]))
  | n@(.str p s h) =>
    if Nat.beq h.hash.size 32 then n
    else
      let p' := rehash p
      .str p' s (Address.admissionHash (ByteArray.mk #[Ix.TAG_NSTR] ++ p'.getHash.hash ++ s.toUTF8))
  | n@(.num p i h) =>
    if Nat.beq h.hash.size 32 then n
    else
      let p' := rehash p
      .num p' i (Address.admissionHash (ByteArray.mk #[Ix.TAG_NNUM] ++ p'.getHash.hash ++ ⟨i.toBytesLE⟩))

/-- Structural equality on `Ix.Name` that reads no hash (avoiding `Address.blake3Pure`
    reduction during kernel and `IxVM` evaluation of parsing and elaboration). -/
def beqStruct : Ix.Name → Ix.Name → Bool
  | .anonymous _, .anonymous _ => true
  | .str p1 s1 _, .str p2 s2 _ => strBeqPure s1 s2 && beqStruct p1 p2
  | .num p1 i1 _, .num p2 i2 _ => Nat.beq i1 i2 && beqStruct p1 p2
  | _, _                       => false

/-- Leaf-first structural total order on `Ix.Name` that reads no hash and compares
    the leaf component (`i₁` vs `i₂` or `s₁` vs `s₂`) before recursing on the prefix. -/
def cmpStruct : Ix.Name → Ix.Name → Ordering
  | .anonymous _, .anonymous _ => .eq
  | .anonymous _, _            => .lt
  | _, .anonymous _            => .gt
  | .num p₁ i₁ _, .num p₂ i₂ _ => (natCmpPure i₁ i₂).then (cmpStruct p₁ p₂)
  | .num .., .str ..           => .lt
  | .str .., .num ..           => .gt
  | .str p₁ s₁ _, .str p₂ s₂ _ => (strCmpPure s₁ s₂).then (cmpStruct p₁ p₂)

instance (priority := 2000) : BEq Ix.Name where
  beq := beqStruct

instance (priority := 2000) : Ord Ix.Name where
  compare := cmpStruct

/-- Build a hierarchical `Ix.Name` from a list of string components. -/
def fromComponents (parts : List String) : Ix.Name :=
  parts.foldl mkStr mkAnon

/-- Build a single-component `Ix.Name`. -/
def simple (s : String) : Ix.Name :=
  mkStr mkAnon s

/-- Build a two-component `Ix.Name`. -/
def mkStr2 (s1 s2 : String) : Ix.Name :=
  mkStr (mkStr mkAnon s1) s2

/-- Build a three-component `Ix.Name`. -/
def mkStr3 (s1 s2 s3 : String) : Ix.Name :=
  mkStr (mkStr (mkStr mkAnon s1) s2) s3

/-- True if the name is `.anonymous`. -/
def isAnonymous : Ix.Name → Bool
  | .anonymous _ => true
  | _            => false

/-- Append two `Ix.Name`s purely (`a ++ b`). -/
def append (a b : Ix.Name) : Ix.Name :=
  if isAnonymous a then b else go b
where
  go : Ix.Name → Ix.Name
    | .anonymous _ => a
    | .str p s _   => mkStr (go p) s
    | .num p i _   => mkNat (go p) i

/-- Extract the string components of a name from root to leaf. -/
def componentsRev : Ix.Name → List String
  | .anonymous _ => []
  | .str p s _   => s :: componentsRev p
  | .num p n _   => toString n :: componentsRev p

def components (n : Ix.Name) : List String :=
  (componentsRev n).reverse

/-- Check whether `pre` is a structural prefix of `n`. -/
def isPrefixOf (pre : Ix.Name) : Ix.Name → Bool
  | .anonymous _ => isAnonymous pre
  | n@(.str p _ _) => if pre == n then true else isPrefixOf pre p
  | n@(.num p _ _) => if pre == n then true else isPrefixOf pre p

/-- Replace prefix `pre` with `newPre` in `n`. -/
def replacePrefix (n pre newPre : Ix.Name) : Ix.Name :=
  if n == pre then newPre
  else match n with
    | .anonymous _ => n
    | .str p s _ =>
      let p' := replacePrefix p pre newPre
      if p' == p then n else mkStr p' s
    | .num p i _ =>
      let p' := replacePrefix p pre newPre
      if p' == p then n else mkNat p' i

/-- Total `toString` for `Ix.Name`. -/
def toStringTotal : Ix.Name → String
  | .anonymous _ => "[anonymous]"
  | .str (.anonymous _) s _ => s
  | .str p s _ => toStringTotal p ++ "." ++ s
  | .num (.anonymous _) i _ => toString i
  | .num p i _ => toStringTotal p ++ "." ++ toString i

end Name

/-! ## Pure `Ix.Level` & `Ix.Expr` Constructors -/

namespace Level

def mkZero : Ix.Level :=
  .zero dummyAddr

def mkSucc (x : Ix.Level) : Ix.Level :=
  .succ x dummyAddr

def mkMax (x y : Ix.Level) : Ix.Level :=
  .max x y dummyAddr

def mkIMax (x y : Ix.Level) : Ix.Level :=
  .imax x y dummyAddr

def mkParam (n : Ix.Name) : Ix.Level :=
  .param n dummyAddr

def mkMVar (n : Ix.Name) : Ix.Level :=
  .mvar n dummyAddr

def ofNat : Nat → Ix.Level
  | 0     => mkZero
  | n + 1 => mkSucc (ofNat n)

/-- Recursively populate the canonical 32-byte `Address` hash on every node of an `Ix.Level`. -/
def rehash : Ix.Level → Ix.Level
  | l@(.zero h) =>
    if Nat.beq h.hash.size 32 then l
    else .zero (Address.admissionHash (ByteArray.mk #[Ix.TAG_UZERO]))
  | l@(.succ x h) =>
    if Nat.beq h.hash.size 32 then l
    else
      let x' := rehash x
      .succ x' (Address.admissionHash (ByteArray.mk #[Ix.TAG_USUCC] ++ x'.getHash.hash))
  | l@(.max x y h) =>
    if Nat.beq h.hash.size 32 then l
    else
      let x' := rehash x
      let y' := rehash y
      .max x' y' (Address.admissionHash (ByteArray.mk #[Ix.TAG_UMAX] ++ x'.getHash.hash ++ y'.getHash.hash))
  | l@(.imax x y h) =>
    if Nat.beq h.hash.size 32 then l
    else
      let x' := rehash x
      let y' := rehash y
      .imax x' y' (Address.admissionHash (ByteArray.mk #[Ix.TAG_UIMAX] ++ x'.getHash.hash ++ y'.getHash.hash))
  | l@(.param n h) =>
    if Nat.beq h.hash.size 32 then l
    else
      let n' := Name.rehash n
      .param n' (Address.admissionHash (ByteArray.mk #[Ix.TAG_UPARAM] ++ n'.getHash.hash))
  | l@(.mvar n h) =>
    if Nat.beq h.hash.size 32 then l
    else
      let n' := Name.rehash n
      .mvar n' (Address.admissionHash (ByteArray.mk #[Ix.TAG_UMVAR] ++ n'.getHash.hash))

/-- Structural equality on `Ix.Level` that reads no hash. -/
def beqStruct : Ix.Level → Ix.Level → Bool
  | .zero _, .zero _         => true
  | .succ a _, .succ b _     => beqStruct a b
  | .max a1 a2 _, .max b1 b2 _   => beqStruct a1 b1 && beqStruct a2 b2
  | .imax a1 a2 _, .imax b1 b2 _ => beqStruct a1 b1 && beqStruct a2 b2
  | .param n1 _, .param n2 _ => Name.beqStruct n1 n2
  | .mvar n1 _, .mvar n2 _   => Name.beqStruct n1 n2
  | _, _                     => false

instance (priority := 2000) : BEq Ix.Level where
  beq := beqStruct

end Level

namespace Expr

def mkBVar (idx : Nat) : Ix.Expr :=
  .bvar idx dummyAddr

def mkFVar (name : Ix.Name) : Ix.Expr :=
  .fvar name dummyAddr

def mkMVar (name : Ix.Name) : Ix.Expr :=
  .mvar name dummyAddr

def mkSort (u : Ix.Level) : Ix.Expr :=
  .sort u dummyAddr

def mkProp : Ix.Expr :=
  mkSort Level.mkZero

def mkType (u : Ix.Level := Level.mkZero) : Ix.Expr :=
  mkSort (Level.mkSucc u)

def mkConst (name : Ix.Name) (us : Array Ix.Level := #[]) : Ix.Expr :=
  .const name us dummyAddr

def mkApp (f a : Ix.Expr) : Ix.Expr :=
  .app f a dummyAddr

def mkAppList : Ix.Expr → List Ix.Expr → Ix.Expr
  | f, []      => f
  | f, a :: as => mkAppList (mkApp f a) as

def mkAppN (f : Ix.Expr) (args : Array Ix.Expr) : Ix.Expr :=
  mkAppList f args.toList

def mkLam (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo := .default) : Ix.Expr :=
  .lam n t b bi dummyAddr

def mkForallE (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo := .default) : Ix.Expr :=
  .forallE n t b bi dummyAddr

def mkArrow (d c : Ix.Expr) : Ix.Expr :=
  mkForallE Name.mkAnon d c .default

def mkLetE (n : Ix.Name) (t v b : Ix.Expr) (nonDep : Bool := false) : Ix.Expr :=
  .letE n t v b nonDep dummyAddr

def mkLit (l : Lean.Literal) : Ix.Expr :=
  .lit l dummyAddr

def mkNatLit (n : Nat) : Ix.Expr :=
  mkLit (.natVal n)

def mkStrLit (s : String) : Ix.Expr :=
  mkLit (.strVal s)

def mkProj (typeName : Ix.Name) (idx : Nat) (struct : Ix.Expr) : Ix.Expr :=
  .proj typeName idx struct dummyAddr

/-- Encode an `Ix.Int` into bytes matching `Ix.Expr.hashInt`. -/
def encodeIntBytes : Ix.Int → ByteArray
  | .ofNat n => ByteArray.mk #[Ix.TAG_MINT, 0] ++ ⟨n.toBytesLE⟩
  | .negSucc n => ByteArray.mk #[Ix.TAG_MINT, 1] ++ ⟨n.toBytesLE⟩

/-- Rehash any `Ix.Name` inside an `Ix.DataValue`. -/
def rehashDataValue : Ix.DataValue → Ix.DataValue
  | .ofName n => .ofName (Name.rehash n)
  | dv        => dv

/-- Encode an `Ix.DataValue` into bytes matching `Ix.Expr.hashDataValue` (for non-syntax metadata). -/
def encodeDataValueBytes : Ix.DataValue → ByteArray
  | .ofString s => ByteArray.mk #[Ix.TAG_MDVAL, 0] ++ s.toUTF8
  | .ofBool b   => ByteArray.mk #[Ix.TAG_MDVAL, 1, if b then 1 else 0]
  | .ofName n   => ByteArray.mk #[Ix.TAG_MDVAL, 2] ++ (Name.computeHash n).hash
  | .ofNat n    => ByteArray.mk #[Ix.TAG_MDVAL, 3] ++ ⟨n.toBytesLE⟩
  | .ofInt i    => ByteArray.mk #[Ix.TAG_MDVAL, 4] ++ encodeIntBytes i
  | .ofSyntax _ => ByteArray.mk #[Ix.TAG_MDVAL, 5, Ix.TAG_MSYN, 0]

/-- Pure `Ix.Expr.mdata` constructor (with deferred `dummyAddr`). -/
def mkMData (data : Array (Ix.Name × Ix.DataValue)) (e : Ix.Expr) : Ix.Expr :=
  .mdata data e dummyAddr

def beqLevelList : List Ix.Level → List Ix.Level → Bool
  | [], [] => true
  | x :: xs, y :: ys => Level.beqStruct x y && beqLevelList xs ys
  | _, _ => false

def beqDataValue : Ix.DataValue → Ix.DataValue → Bool
  | .ofString s1, .ofString s2 => strBeqPure s1 s2
  | .ofBool b1, .ofBool b2     => b1 == b2
  | .ofName n1, .ofName n2     => Name.beqStruct n1 n2
  | .ofNat n1, .ofNat n2       => Nat.beq n1 n2
  | .ofInt (.ofNat n1), .ofInt (.ofNat n2)     => Nat.beq n1 n2
  | .ofInt (.negSucc n1), .ofInt (.negSucc n2) => Nat.beq n1 n2
  | .ofSyntax _, .ofSyntax _   => true
  | _, _                       => false

def beqMDataList : List (Ix.Name × Ix.DataValue) → List (Ix.Name × Ix.DataValue) → Bool
  | [], [] => true
  | (k1, v1) :: xs, (k2, v2) :: ys =>
    Name.beqStruct k1 k2 && beqDataValue v1 v2 && beqMDataList xs ys
  | _, _ => false

/-- Structural equality on `Ix.Expr` that reads no hash. -/
def beqStruct : Ix.Expr → Ix.Expr → Bool
  | .bvar i _, .bvar j _ => Nat.beq i j
  | .fvar n1 _, .fvar n2 _ => Name.beqStruct n1 n2
  | .mvar n1 _, .mvar n2 _ => Name.beqStruct n1 n2
  | .sort u _, .sort v _ => Level.beqStruct u v
  | .const n1 us1 _, .const n2 us2 _ => Name.beqStruct n1 n2 && beqLevelList us1.toList us2.toList
  | .app f1 a1 _, .app f2 a2 _ => beqStruct f1 f2 && beqStruct a1 a2
  | .lam _ d1 b1 bi1 _, .lam _ d2 b2 bi2 _ => bi1 == bi2 && beqStruct d1 d2 && beqStruct b1 b2
  | .forallE _ d1 b1 bi1 _, .forallE _ d2 b2 bi2 _ => bi1 == bi2 && beqStruct d1 d2 && beqStruct b1 b2
  | .letE _ t1 v1 b1 nd1 _, .letE _ t2 v2 b2 nd2 _ =>
    nd1 == nd2 && beqStruct t1 t2 && beqStruct v1 v2 && beqStruct b1 b2
  | .lit (.natVal n1) _, .lit (.natVal n2) _ => Nat.beq n1 n2
  | .lit (.strVal s1) _, .lit (.strVal s2) _ => strBeqPure s1 s2
  | .mdata d1 e1 _, .mdata d2 e2 _ => beqMDataList d1.toList d2.toList && beqStruct e1 e2
  | .proj s1 i1 e1 _, .proj s2 i2 e2 _ => Name.beqStruct s1 s2 && Nat.beq i1 i2 && beqStruct e1 e2
  | _, _ => false

instance (priority := 2000) : BEq Ix.Expr where
  beq := beqStruct

/-- Recursively populate the canonical 32-byte `Address` hash on every node of an `Ix.Expr`. -/
def rehash : Ix.Expr → Ix.Expr
  | e@(.bvar idx h) =>
    if Nat.beq h.hash.size 32 then e
    else .bvar idx (Address.admissionHash (ByteArray.mk #[Ix.TAG_EVAR] ++ ⟨idx.toBytesLE⟩))
  | e@(.fvar name h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let name' := Name.rehash name
      .fvar name' (Address.admissionHash (ByteArray.mk #[Ix.TAG_EFVAR] ++ name'.getHash.hash))
  | e@(.mvar name h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let name' := Name.rehash name
      .mvar name' (Address.admissionHash (ByteArray.mk #[Ix.TAG_EMVAR] ++ name'.getHash.hash))
  | e@(.sort u h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let u' := Level.rehash u
      .sort u' (Address.admissionHash (ByteArray.mk #[Ix.TAG_ESORT] ++ u'.getHash.hash))
  | e@(.const name us h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let name' := Name.rehash name
      let usList := us.toList.map Level.rehash
      let digest := Address.admissionHash (
        usList.foldl (fun acc u => acc ++ u.getHash.hash)
          (ByteArray.mk #[Ix.TAG_EREF] ++ name'.getHash.hash))
      .const name' (Array.mk usList) digest
  | e@(.app f a h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let f' := rehash f
      let a' := rehash a
      .app f' a' (Address.admissionHash (ByteArray.mk #[Ix.TAG_EAPP] ++ f'.getHash.hash ++ a'.getHash.hash))
  | e@(.lam n t b bi h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let n' := Name.rehash n
      let t' := rehash t
      let b' := rehash b
      let digest := Address.admissionHash (
        ByteArray.mk #[Ix.TAG_ELAM] ++ n'.getHash.hash ++ t'.getHash.hash ++
        b'.getHash.hash ++ ByteArray.mk #[Ix.Expr.binderInfoTag bi])
      .lam n' t' b' bi digest
  | e@(.forallE n t b bi h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let n' := Name.rehash n
      let t' := rehash t
      let b' := rehash b
      let digest := Address.admissionHash (
        ByteArray.mk #[Ix.TAG_EALL] ++ n'.getHash.hash ++ t'.getHash.hash ++
        b'.getHash.hash ++ ByteArray.mk #[Ix.Expr.binderInfoTag bi])
      .forallE n' t' b' bi digest
  | e@(.letE n t v b nonDep h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let n' := Name.rehash n
      let t' := rehash t
      let v' := rehash v
      let b' := rehash b
      let digest := Address.admissionHash (
        ByteArray.mk #[Ix.TAG_ELET] ++ n'.getHash.hash ++ t'.getHash.hash ++
        v'.getHash.hash ++ b'.getHash.hash ++ ByteArray.mk #[if nonDep then 1 else 0])
      .letE n' t' v' b' nonDep digest
  | e@(.lit l h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let digest := Address.admissionHash (match l with
        | .natVal n => ByteArray.mk #[Ix.TAG_ENAT] ++ ⟨n.toBytesLE⟩
        | .strVal s => ByteArray.mk #[Ix.TAG_ESTR] ++ s.toUTF8)
      .lit l digest
  | e@(.proj typeName idx struct h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let typeName' := Name.rehash typeName
      let struct' := rehash struct
      let digest := Address.admissionHash (
        ByteArray.mk #[Ix.TAG_EPRJ] ++ typeName'.getHash.hash ++
        ⟨idx.toBytesLE⟩ ++ struct'.getHash.hash)
      .proj typeName' idx struct' digest
  | e@(.mdata data inner h) =>
    if Nat.beq h.hash.size 32 then e
    else
      let dataList := data.toList.map fun (nm, dv) => (Name.rehash nm, rehashDataValue dv)
      let inner' := rehash inner
      let header := ByteArray.mk #[Ix.TAG_EMDATA] ++ ⟨dataList.length.toBytesLE⟩
      let body := dataList.foldl (fun acc (nm, dv) =>
        acc ++ nm.getHash.hash ++ encodeDataValueBytes dv) header
      let digest := Address.admissionHash (body ++ inner'.getHash.hash)
      .mdata (Array.mk dataList) inner' digest

/-- Pure `Ix.ConstantInfo.getCnst` exposed for kernel-level reduction. -/
def ConstantInfo.getCnstPure : Ix.ConstantInfo → Ix.ConstantVal
  | .axiomInfo v  => v.cnst
  | .defnInfo v   => v.cnst
  | .thmInfo v    => v.cnst
  | .opaqueInfo v => v.cnst
  | .quotInfo v   => v.cnst
  | .inductInfo v => v.cnst
  | .ctorInfo v   => v.cnst
  | .recInfo v    => v.cnst

/-- Populate canonical 32-byte `Address` hashes on an `Ix.ConstantVal`. -/
def rehashConstantVal (cv : Ix.ConstantVal) : Ix.ConstantVal :=
  { name        := Name.rehash cv.name
    levelParams := Array.mk (cv.levelParams.toList.map Name.rehash)
    type        := rehash cv.type }

/-- Populate canonical 32-byte `Address` hashes on an `Ix.RecursorRule`. -/
def rehashRecursorRule (r : Ix.RecursorRule) : Ix.RecursorRule :=
  { r with
    ctor := Name.rehash r.ctor
    rhs  := rehash r.rhs }

/-- Populate canonical 32-byte `Address` hashes throughout an `Ix.ConstantInfo`. -/
def ConstantInfo.rehash : Ix.ConstantInfo → Ix.ConstantInfo
  | .axiomInfo v => .axiomInfo { v with cnst := rehashConstantVal v.cnst }
  | .defnInfo v => .defnInfo {
      v with
      cnst  := rehashConstantVal v.cnst
      value := Expr.rehash v.value
      all   := Array.mk (v.all.toList.map Name.rehash) }
  | .thmInfo v => .thmInfo {
      v with
      cnst  := rehashConstantVal v.cnst
      value := Expr.rehash v.value
      all   := Array.mk (v.all.toList.map Name.rehash) }
  | .opaqueInfo v => .opaqueInfo {
      v with
      cnst  := rehashConstantVal v.cnst
      value := Expr.rehash v.value
      all   := Array.mk (v.all.toList.map Name.rehash) }
  | .quotInfo v => .quotInfo { v with cnst := rehashConstantVal v.cnst }
  | .inductInfo v => .inductInfo {
      v with
      cnst  := rehashConstantVal v.cnst
      all   := Array.mk (v.all.toList.map Name.rehash)
      ctors := Array.mk (v.ctors.toList.map Name.rehash) }
  | .ctorInfo v => .ctorInfo {
      v with
      cnst   := rehashConstantVal v.cnst
      induct := Name.rehash v.induct }
  | .recInfo v => .recInfo {
      v with
      cnst  := rehashConstantVal v.cnst
      all   := Array.mk (v.all.toList.map Name.rehash)
      rules := Array.mk (v.rules.toList.map rehashRecursorRule) }

/-- Pure `ix.contract` metadata key `ix.contract`. -/
def contractKey : Ix.Name := Name.mkStr2 "ix" "contract"

/-- Construct the 3-entry `ix.contract` metadata array purely via `Address.admissionHash`. -/
def mkContractMData (kindCode code : Nat) : Array (Ix.Name × Ix.DataValue) :=
  let key := contractKey
  #[ (key, .ofNat 3),
     (Name.mkStr key "kind", .ofNat kindCode),
     (Name.mkStr key "code", .ofNat code) ]

/-- Construct a `lam` node, attaching an `ix.contract` frame when `binder != .many`. -/
def mkLamContract (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo := .default)
    (binder : Ixon.BinderContract := default) : Ix.Expr :=
  let lam := mkLam n t b bi
  if binder == .many then lam
  else mkMData (mkContractMData 0 binder.toBits.toNat) lam

/-- Construct a `forallE` node, attaching an `ix.contract` frame when `binder != .many` or `result != .shared`. -/
def mkForallContract (n : Ix.Name) (t b : Ix.Expr) (bi : Lean.BinderInfo := .default)
    (binder : Ixon.BinderContract := default)
    (result : Ixon.ValueContract := .shared) : Ix.Expr :=
  let all := mkForallE n t b bi
  if binder == .many && result == .shared then all
  else
    let code := (Ixon.packAllContract binder result).toNat
    mkMData (mkContractMData 1 code) all

/-- Construct a `letE` node, attaching an `ix.contract` frame when `binder != .many` or `letKind != .value`. -/
def mkLetContract (n : Ix.Name) (t v b : Ix.Expr) (nonDep : Bool := false)
    (binder : Ixon.BinderContract := default)
    (letKind : Ixon.LetKind := .value) : Ix.Expr :=
  let letNode := mkLetE n t v b nonDep
  if binder == .many && letKind == .value then letNode
  else
    let code := binder.toBits.toNat + (if letKind == .borrowShared then 16 else 0)
    mkMData (mkContractMData 2 code) letNode

end Expr

/-! ## Substructural Surface Annotation AST -/

/-- Parsed surface usage/ownership/locality modifier on a binder or return type. -/
structure ParsedBinderContract where
  uses     : Option Ixon.Uses := none
  owned    : Option Ixon.Owned := none
  locality : Option Ixon.Locality := none
  deriving BEq, DecidableEq, Repr, Inhabited

namespace ParsedBinderContract

def isEmpty (c : ParsedBinderContract) : Bool :=
  c.uses.isNone && c.owned.isNone && c.locality.isNone

def toValueContract (c : ParsedBinderContract) : Ixon.ValueContract :=
  { owned    := c.owned.getD .shared
    locality := c.locality.getD .unrestricted }

def toBinderContract (c : ParsedBinderContract) : Ixon.BinderContract :=
  { uses  := c.uses.getD .many
    value := c.toValueContract }

end ParsedBinderContract

/-! ## Well-Known Syntax Node Kinds (`SyntaxKind`) -/

namespace SyntaxKind

def nullKind : Ix.Name := Name.simple "null"
def missingKind : Ix.Name := Name.simple "missing"
def identKind : Ix.Name := Name.simple "ident"

-- Module & top-level commands
def moduleKind        : Ix.Name := Name.mkStr2 "Ix" "module"
def headerKind        : Ix.Name := Name.mkStr2 "Ix" "header"
def importDecl        : Ix.Name := Name.mkStr2 "Ix" "importDecl"
def hashImport        : Ix.Name := Name.mkStr2 "Ix" "hashImport"
def buildMapDecl      : Ix.Name := Name.mkStr2 "Ix" "buildMapDecl"
def namespaceDecl     : Ix.Name := Name.mkStr2 "Ix" "namespaceDecl"
def sectionDecl       : Ix.Name := Name.mkStr2 "Ix" "sectionDecl"
def endDecl           : Ix.Name := Name.mkStr2 "Ix" "endDecl"
def openDecl          : Ix.Name := Name.mkStr2 "Ix" "openDecl"
def variableDecl      : Ix.Name := Name.mkStr2 "Ix" "variableDecl"
def universeDecl      : Ix.Name := Name.mkStr2 "Ix" "universeDecl"
def mutualDecl        : Ix.Name := Name.mkStr2 "Ix" "mutualDecl"
def defDecl           : Ix.Name := Name.mkStr2 "Ix" "defDecl"
def abbrevDecl        : Ix.Name := Name.mkStr2 "Ix" "abbrevDecl"
def theoremDecl       : Ix.Name := Name.mkStr2 "Ix" "theoremDecl"
def axiomDecl         : Ix.Name := Name.mkStr2 "Ix" "axiomDecl"
def opaqueDecl        : Ix.Name := Name.mkStr2 "Ix" "opaqueDecl"
def instanceDecl      : Ix.Name := Name.mkStr2 "Ix" "instanceDecl"
def inductiveDecl     : Ix.Name := Name.mkStr2 "Ix" "inductiveDecl"
def structureDecl     : Ix.Name := Name.mkStr2 "Ix" "structureDecl"
def classDecl         : Ix.Name := Name.mkStr2 "Ix" "classDecl"
def ctorDecl          : Ix.Name := Name.mkStr2 "Ix" "ctorDecl"
def fieldDecl         : Ix.Name := Name.mkStr2 "Ix" "fieldDecl"
def notationDecl      : Ix.Name := Name.mkStr2 "Ix" "notationDecl"
def macroDecl         : Ix.Name := Name.mkStr2 "Ix" "macroDecl"
def modifiersKind     : Ix.Name := Name.mkStr2 "Ix" "modifiers"
def univParamsKind    : Ix.Name := Name.mkStr2 "Ix" "univParams"

-- Substructural contract nodes
def binderPrefix      : Ix.Name := Name.mkStr3 "Ix" "contract" "binderPrefix"
def valuePrefix       : Ix.Name := Name.mkStr3 "Ix" "contract" "valuePrefix"
def explicitBinder    : Ix.Name := Name.mkStr2 "Ix" "explicitBinder"
def implicitBinder    : Ix.Name := Name.mkStr2 "Ix" "implicitBinder"
def strictImplicitBinder : Ix.Name := Name.mkStr2 "Ix" "strictImplicitBinder"
def instBinder        : Ix.Name := Name.mkStr2 "Ix" "instBinder"

-- Terms & Universe Levels
def hashRef           : Ix.Name := Name.mkStr2 "Ix" "hashRef"
def numLit            : Ix.Name := Name.mkStr2 "Ix" "numLit"
def strLit            : Ix.Name := Name.mkStr2 "Ix" "strLit"
def charLit           : Ix.Name := Name.mkStr2 "Ix" "charLit"
def appTerm           : Ix.Name := Name.mkStr2 "Ix" "app"
def arrowTerm         : Ix.Name := Name.mkStr2 "Ix" "arrow"
def forallTerm        : Ix.Name := Name.mkStr2 "Ix" "forall"
def funTerm           : Ix.Name := Name.mkStr2 "Ix" "fun"
def letTerm           : Ix.Name := Name.mkStr2 "Ix" "let"
def letBorrowTerm     : Ix.Name := Name.mkStr2 "Ix" "letBorrow"
def haveTerm          : Ix.Name := Name.mkStr2 "Ix" "have"
def ifTerm            : Ix.Name := Name.mkStr2 "Ix" "if"
def matchTerm         : Ix.Name := Name.mkStr2 "Ix" "match"
def matchAlt          : Ix.Name := Name.mkStr2 "Ix" "matchAlt"
def projTerm          : Ix.Name := Name.mkStr2 "Ix" "proj"
def anonCtor          : Ix.Name := Name.mkStr2 "Ix" "anonCtor"
def structInst        : Ix.Name := Name.mkStr2 "Ix" "structInst"
def structFieldAssign : Ix.Name := Name.mkStr2 "Ix" "structFieldAssign"
def listLit           : Ix.Name := Name.mkStr2 "Ix" "listLit"
def tupleTerm         : Ix.Name := Name.mkStr2 "Ix" "tuple"
def parenTerm         : Ix.Name := Name.mkStr2 "Ix" "paren"
def typeAscription    : Ix.Name := Name.mkStr2 "Ix" "typeAscription"
def holeTerm          : Ix.Name := Name.mkStr2 "Ix" "hole"
def sorryTerm         : Ix.Name := Name.mkStr2 "Ix" "sorry"
def sortTerm          : Ix.Name := Name.mkStr2 "Ix" "sort"
def propTerm          : Ix.Name := Name.mkStr2 "Ix" "prop"
def typeTerm          : Ix.Name := Name.mkStr2 "Ix" "type"
def binOpTerm         : Ix.Name := Name.mkStr2 "Ix" "binOp"
def unaryOpTerm       : Ix.Name := Name.mkStr2 "Ix" "unaryOp"
def explicitTerm      : Ix.Name := Name.mkStr2 "Ix" "explicit"
def levelLit          : Ix.Name := Name.mkStr2 "Ix" "levelLit"
def levelAdd          : Ix.Name := Name.mkStr2 "Ix" "levelAdd"
def levelMax          : Ix.Name := Name.mkStr2 "Ix" "levelMax"
def levelIMax         : Ix.Name := Name.mkStr2 "Ix" "levelIMax"

-- Tactics
def byTactic          : Ix.Name := Name.mkStr2 "Ix" "byTactic"
def tacticSeq         : Ix.Name := Name.mkStr2 "Ix" "tacticSeq"
def tacticIntro       : Ix.Name := Name.mkStr3 "Ix" "tactic" "intro"
def tacticExact       : Ix.Name := Name.mkStr3 "Ix" "tactic" "exact"
def tacticApply       : Ix.Name := Name.mkStr3 "Ix" "tactic" "apply"
def tacticRefine      : Ix.Name := Name.mkStr3 "Ix" "tactic" "refine"
def tacticRfl         : Ix.Name := Name.mkStr3 "Ix" "tactic" "rfl"
def tacticRw          : Ix.Name := Name.mkStr3 "Ix" "tactic" "rw"
def tacticRwRule      : Ix.Name := Name.mkStr3 "Ix" "tactic" "rwRule"
def tacticCases       : Ix.Name := Name.mkStr3 "Ix" "tactic" "cases"
def tacticInduction   : Ix.Name := Name.mkStr3 "Ix" "tactic" "induction"
def tacticAlt         : Ix.Name := Name.mkStr3 "Ix" "tactic" "alt"
def tacticHave        : Ix.Name := Name.mkStr3 "Ix" "tactic" "have"
def tacticLet         : Ix.Name := Name.mkStr3 "Ix" "tactic" "let"
def tacticChange      : Ix.Name := Name.mkStr3 "Ix" "tactic" "change"
def tacticConstructor : Ix.Name := Name.mkStr3 "Ix" "tactic" "constructor"
def tacticSimp        : Ix.Name := Name.mkStr3 "Ix" "tactic" "simp"
def tacticDecide      : Ix.Name := Name.mkStr3 "Ix" "tactic" "decide"
def tacticAssumption    : Ix.Name := Name.mkStr3 "Ix" "tactic" "assumption"
def tacticSorry         : Ix.Name := Name.mkStr3 "Ix" "tactic" "sorry"
def tacticAndThen       : Ix.Name := Name.mkStr3 "Ix" "tactic" "andThen"
def tacticFocus         : Ix.Name := Name.mkStr3 "Ix" "tactic" "focus"
def tacticCase          : Ix.Name := Name.mkStr3 "Ix" "tactic" "case"
def tacticParen         : Ix.Name := Name.mkStr3 "Ix" "tactic" "paren"
def tacticFirst         : Ix.Name := Name.mkStr3 "Ix" "tactic" "first"
def tacticTry           : Ix.Name := Name.mkStr3 "Ix" "tactic" "try"
def tacticRepeat        : Ix.Name := Name.mkStr3 "Ix" "tactic" "repeat"
def tacticAllGoals      : Ix.Name := Name.mkStr3 "Ix" "tactic" "allGoals"
def tacticAnyGoals      : Ix.Name := Name.mkStr3 "Ix" "tactic" "anyGoals"
def tacticShow          : Ix.Name := Name.mkStr3 "Ix" "tactic" "show"
def tacticLeft          : Ix.Name := Name.mkStr3 "Ix" "tactic" "left"
def tacticRight         : Ix.Name := Name.mkStr3 "Ix" "tactic" "right"
def tacticSplit         : Ix.Name := Name.mkStr3 "Ix" "tactic" "split"
def tacticExists        : Ix.Name := Name.mkStr3 "Ix" "tactic" "exists"
def tacticSymm          : Ix.Name := Name.mkStr3 "Ix" "tactic" "symm"
def tacticTrans         : Ix.Name := Name.mkStr3 "Ix" "tactic" "trans"
def tacticCongr         : Ix.Name := Name.mkStr3 "Ix" "tactic" "congr"
def tacticFunext        : Ix.Name := Name.mkStr3 "Ix" "tactic" "funext"
def tacticExt           : Ix.Name := Name.mkStr3 "Ix" "tactic" "ext"
def tacticDSimp         : Ix.Name := Name.mkStr3 "Ix" "tactic" "dsimp"
def tacticTrivial       : Ix.Name := Name.mkStr3 "Ix" "tactic" "trivial"
def tacticContradiction : Ix.Name := Name.mkStr3 "Ix" "tactic" "contradiction"
def tacticExfalso       : Ix.Name := Name.mkStr3 "Ix" "tactic" "exfalso"
def tacticDone          : Ix.Name := Name.mkStr3 "Ix" "tactic" "done"

end SyntaxKind

/-! ## `Ix.SourceInfo` & `Ix.Syntax` Helpers -/

namespace SourceInfo

def startPos? : Ix.SourceInfo → Option Nat
  | .original _ pos _ _  => some pos
  | .synthetic pos _ _   => some pos
  | .none                => none

def endPos? : Ix.SourceInfo → Option Nat
  | .original _ _ _ pos  => some pos
  | .synthetic _ pos _   => some pos
  | .none                => none

end SourceInfo

namespace Syntax

def mkAtom (info : Ix.SourceInfo) (val : String) : Ix.Syntax :=
  .atom info val

def mkSimpleAtom (val : String) : Ix.Syntax :=
  .atom .none val

def mkIdent (info : Ix.SourceInfo) (rawVal : Ix.Substring) (val : Ix.Name) : Ix.Syntax :=
  .ident info rawVal val #[]

def mkSimpleIdent (val : Ix.Name) : Ix.Syntax :=
  let s := Name.toStringTotal val
  .ident .none ⟨s, 0, s.utf8ByteSize⟩ val #[]

def mkNode (kind : Ix.Name) (args : Array Ix.Syntax) (info : Ix.SourceInfo := .none) : Ix.Syntax :=
  .node info kind args

def mkNullNode (args : Array Ix.Syntax := #[]) : Ix.Syntax :=
  .node .none SyntaxKind.nullKind args

def getKind : Ix.Syntax → Ix.Name
  | .missing         => SyntaxKind.missingKind
  | .node _ kind _   => kind
  | .atom _ v        => Name.simple v
  | .ident _ _ _ _   => SyntaxKind.identKind

def isOfKind (stx : Ix.Syntax) (k : Ix.Name) : Bool :=
  getKind stx == k

def isMissing : Ix.Syntax → Bool
  | .missing => true
  | _        => false

def getArgs : Ix.Syntax → Array Ix.Syntax
  | .node _ _ args => args
  | _              => #[]

def getNumArgs (stx : Ix.Syntax) : Nat :=
  (getArgs stx).size

/-- Proof-free `List` element lookup with default for kernel reduction. -/
def listGetD : List α → Nat → α → α
  | [], _, d            => d
  | x :: _, 0, _        => x
  | _ :: rest, k + 1, d => listGetD rest k d

/-- Proof-free `List` optional element lookup for kernel reduction. -/
def listGet? : List α → Nat → Option α
  | [], _            => none
  | x :: _, 0        => some x
  | _ :: rest, k + 1 => listGet? rest k

def getArg (stx : Ix.Syntax) (i : Nat) : Ix.Syntax :=
  listGetD (getArgs stx).toList i .missing

def isNone : Ix.Syntax → Bool
  | .node _ kind ⟨[]⟩ => kind == SyntaxKind.nullKind
  | _                 => false

def getOptional? (stx : Ix.Syntax) : Option Ix.Syntax :=
  if isOfKind stx SyntaxKind.nullKind then
    listGet? (getArgs stx).toList 0
  else
    none

def getId : Ix.Syntax → Ix.Name
  | .ident _ _ val _ => val
  | _                => Name.mkAnon

def getAtomVal : Ix.Syntax → String
  | .atom _ val => val
  | _           => ""

def getHeadInfo? (fuel : Nat := 128) (stx : Ix.Syntax) : Option Ix.SourceInfo :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stx with
    | .missing        => none
    | .atom info _    => some info
    | .ident info _ _ _ => some info
    | .node info _ args =>
      match info with
      | .none => args.findSome? (getHeadInfo? fuel)
      | _     => some info

def getPos? (stx : Ix.Syntax) : Option Nat := do
  let info ← getHeadInfo? 128 stx
  SourceInfo.startPos? info

/-- Pretty-print an `Ix.Syntax` tree for debugging and tests (fuel-bounded). -/
def format (fuel : Nat := 256) (stx : Ix.Syntax) : String :=
  match fuel with
  | 0 => "..."
  | fuel + 1 =>
    match stx with
    | .missing => "<missing>"
    | .atom _ val => reprStr val
    | .ident _ _ val _ => s!"`{Name.toStringTotal val}"
    | .node _ kind args =>
      let kStr := Name.toStringTotal kind
      if args.isEmpty then
        s!"({kStr})"
      else
        let childStrs := args.toList.map (format fuel)
        s!"({kStr} {strIntercalatePure " " childStrs})"

end Syntax

end Ix.Frontend
