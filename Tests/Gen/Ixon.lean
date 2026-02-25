/-
  Generators for Ixon.* types (alpha-invariant serialization format).
  Extracted from Tests/Ix/Ixon.lean.
-/
module

public import LSpec
public import Tests.Gen.Basic
public import Ix.Ixon
public import Ix.Address

public section

open LSpec SlimCheck Gen Ixon
open Ix (DefKind DefinitionSafety QuotKind)

namespace Tests.Gen.Ixon

/-! ## Basic Ixon generators -/

/-- Generate a random Address by hashing random bytes -/
def genAddress : Gen Address := do
  let mut bytes : ByteArray := ByteArray.empty
  for _ in [:32] do
    let b ← Gen.choose Nat 0 255
    bytes := bytes.push b.toUInt8
  pure ⟨(Blake3.hash bytes).val⟩

def genIxonNat : Gen Nat := USize.toNat <$> genUSize

-- aggressively reduce size parameter to avoid tree blow-up
def genList (n: Gen α) : Gen (List α) :=
  resize (fun s => if s > 8 then 8 else s / 2) $ listOf n

def genUInt64Small : Gen UInt64 := USize.toUInt64 <$> genUSize

def genDefKind : Gen DefKind :=
  elements #[.defn, .opaq, .thm]

def genDefinitionSafety : Gen DefinitionSafety :=
  elements #[.unsaf, .safe, .part]

def genQuotKindNew : Gen QuotKind :=
  elements #[.type, .ctor, .lift, .ind]

def genArray (g: Gen α) : Gen (Array α) :=
  Array.mk <$> genList g

/-- Generate a universe level (new format) - non-recursive base cases heavily weighted -/
partial def genUniv : Gen Univ :=
  resize (fun s => if s > 2 then 2 else s / 2) <|
  frequency [
    (50, pure .zero),  -- Heavily weighted base case
    (20, .var <$> genUInt64Small),  -- Another base case
    (10, .succ <$> genUniv),
    (5, .max <$> genUniv <*> genUniv),
    (5, .imax <$> genUniv <*> genUniv),
  ]

/-- Generate an expression (new format) - non-recursive cases heavily weighted -/
partial def genExpr : Gen Expr :=
  resize (fun s => if s > 2 then 2 else s / 2) <|
  frequency [
    (30, .sort <$> genUInt64Small),   -- Base cases heavily weighted
    (30, .var <$> genUInt64Small),
    (20, .str <$> genUInt64Small),
    (20, .nat <$> genUInt64Small),
    (20, .share <$> genUInt64Small),
    (15, .ref <$> genUInt64Small <*> genArray genUInt64Small),
    (15, .recur <$> genUInt64Small <*> genArray genUInt64Small),
    (5, .prj <$> genUInt64Small <*> genUInt64Small <*> genExpr),
    (5, .app <$> genExpr <*> genExpr),
    (5, .lam <$> genExpr <*> genExpr),
    (5, .all <$> genExpr <*> genExpr),
    (2, .letE <$> genBool <*> genExpr <*> genExpr <*> genExpr),
  ]

def genDefinition : Gen Definition :=
  .mk <$> genDefKind <*> genDefinitionSafety <*> genUInt64Small <*> genExpr <*> genExpr

def genAxiom : Gen Axiom :=
  .mk <$> genBool <*> genUInt64Small <*> genExpr

def genQuotKind : Gen Lean.QuotKind :=
  elements #[.type, .ctor, .lift, .ind]

def genQuotient : Gen Quotient :=
  .mk <$> genQuotKindNew <*> genUInt64Small <*> genExpr

def genConstructorProj : Gen ConstructorProj :=
  .mk <$> genUInt64Small <*> genUInt64Small <*> genAddress

def genRecursorProj : Gen RecursorProj :=
  .mk <$> genUInt64Small <*> genAddress

def genInductiveProj : Gen InductiveProj :=
  .mk <$> genUInt64Small <*> genAddress

def genDefinitionProj : Gen DefinitionProj :=
  .mk <$> genUInt64Small <*> genAddress

def genRecursorRule : Gen RecursorRule :=
  .mk <$> genUInt64Small <*> genExpr

def genRecursor : Gen Recursor :=
  .mk <$> genBool <*> genBool <*> genUInt64Small <*> genUInt64Small <*> genUInt64Small
    <*> genUInt64Small <*> genUInt64Small <*> genExpr <*> genArray genRecursorRule

def genConstructor : Gen Constructor :=
  .mk <$> genBool <*> genUInt64Small <*> genUInt64Small <*> genUInt64Small <*> genUInt64Small <*> genExpr

def genInductive : Gen Inductive :=
  .mk <$> genBool <*> genBool <*> genBool <*> genUInt64Small <*> genUInt64Small
    <*> genUInt64Small <*> genUInt64Small <*> genExpr <*> genArray genConstructor


def genBinderInfo : Gen Lean.BinderInfo :=
  elements #[.default, .implicit, .strictImplicit, .instImplicit]

def genReducibilityHints : Gen Lean.ReducibilityHints :=
  frequency [
    (10, pure .opaque),
    (10, pure .abbrev),
    (10, .regular <$> genUInt32),
  ]


/-- Generate small arrays for Constant to avoid memory issues -/
def genSmallArray (g : Gen α) : Gen (Array α) :=
  resize (fun s => if s > 3 then 3 else s / 2) <|
  Array.mk <$> genList g

/-- Generate a MutConst (new format) -/
def genMutConst : Gen MutConst :=
  frequency [
    (10, MutConst.defn <$> genDefinition),
    (5, MutConst.indc <$> genInductive),
    (5, MutConst.recr <$> genRecursor),
  ]

/-- Generate a ConstantInfo (new format) -/
def genConstantInfo : Gen ConstantInfo :=
  frequency [
    (10, .defn <$> genDefinition),
    (5, .recr <$> genRecursor),
    (10, .axio <$> genAxiom),
    (10, .quot <$> genQuotient),
    (10, .cPrj <$> genConstructorProj),
    (5, .rPrj <$> genRecursorProj),
    (10, .iPrj <$> genInductiveProj),
    (10, .dPrj <$> genDefinitionProj),
    (5, .muts <$> genSmallArray genMutConst),
  ]

/-- Generate a Constant (new format) -/
def genConstant : Gen Constant :=
  Constant.mk <$> genConstantInfo
    <*> genSmallArray genExpr
    <*> genSmallArray genAddress
    <*> genSmallArray genUniv

/-! ## Shrinkable instances -/

-- Simple enums - can't shrink
instance : Shrinkable DefKind where shrink _ := []
instance : Shrinkable DefinitionSafety where shrink _ := []
instance : Shrinkable QuotKind where shrink _ := []

-- Recursive types - shrink by returning sub-terms / halving indices
instance : Shrinkable Univ where
  shrink u := match u with
    | .zero => []
    | .succ inner => [inner]
    | .max a b => [a, b]
    | .imax a b => [a, b]
    | .var idx => if idx > 0 then [.var (idx / 2), .zero] else [.zero]

instance : Shrinkable Expr where
  shrink e := match e with
    | .sort idx => if idx > 0 then [.sort (idx / 2)] else []
    | .var idx => if idx > 0 then [.var (idx / 2)] else []
    | .ref ri us => (if us.size > 0 then [.ref ri us.pop] else []) ++
                    (if ri > 0 then [.ref (ri / 2) us] else [])
    | .recur ri us => (if us.size > 0 then [.recur ri us.pop] else []) ++
                      (if ri > 0 then [.recur (ri / 2) us] else [])
    | .prj ti fi val => [val] ++ (if fi > 0 then [.prj ti (fi / 2) val] else [])
    | .str ri => if ri > 0 then [.str (ri / 2)] else []
    | .nat ri => if ri > 0 then [.nat (ri / 2)] else []
    | .app f a => [f, a]
    | .lam ty body => [ty, body]
    | .all ty body => [ty, body]
    | .letE _ ty val body => [ty, val, body]
    | .share idx => if idx > 0 then [.share (idx / 2)] else []

-- Struct types - shrink by simplifying expressions
instance : Shrinkable Definition where
  shrink d :=
    (if d.typ != .sort 0 then [{ d with typ := .sort 0 }] else []) ++
    (if d.value != .var 0 then [{ d with value := .var 0 }] else []) ++
    (if d.lvls > 0 then [{ d with lvls := d.lvls / 2 }] else [])

instance : Shrinkable Axiom where
  shrink a :=
    (if a.typ != .sort 0 then [{ a with typ := .sort 0 }] else []) ++
    (if a.lvls > 0 then [{ a with lvls := a.lvls / 2 }] else [])

instance : Shrinkable Quotient where
  shrink q :=
    (if q.typ != .sort 0 then [{ q with typ := .sort 0 }] else []) ++
    (if q.lvls > 0 then [{ q with lvls := q.lvls / 2 }] else [])

instance : Shrinkable RecursorRule where
  shrink r :=
    (if r.rhs != .var 0 then [{ r with rhs := .var 0 }] else []) ++
    (if r.fields > 0 then [{ r with fields := r.fields / 2 }] else [])

instance : Shrinkable Recursor where
  shrink r :=
    (if r.rules.size > 0 then [{ r with rules := r.rules.pop }] else []) ++
    (if r.typ != .sort 0 then [{ r with typ := .sort 0 }] else [])

instance : Shrinkable Constructor where
  shrink c :=
    (if c.typ != .sort 0 then [{ c with typ := .sort 0 }] else []) ++
    (if c.lvls > 0 then [{ c with lvls := c.lvls / 2 }] else [])

instance : Shrinkable Inductive where
  shrink i :=
    (if i.ctors.size > 0 then [{ i with ctors := i.ctors.pop }] else []) ++
    (if i.typ != .sort 0 then [{ i with typ := .sort 0 }] else [])

-- Projection types - shrink numeric fields
instance : Shrinkable InductiveProj where
  shrink p := if p.idx > 0 then [{ p with idx := p.idx / 2 }] else []

instance : Shrinkable ConstructorProj where
  shrink p :=
    (if p.idx > 0 then [{ p with idx := p.idx / 2 }] else []) ++
    (if p.cidx > 0 then [{ p with cidx := p.cidx / 2 }] else [])

instance : Shrinkable RecursorProj where
  shrink p := if p.idx > 0 then [{ p with idx := p.idx / 2 }] else []

instance : Shrinkable DefinitionProj where
  shrink p := if p.idx > 0 then [{ p with idx := p.idx / 2 }] else []

-- Composite types - shrink to simpler variants
instance : Shrinkable MutConst where
  shrink
    | .defn d => .defn <$> Shrinkable.shrink d
    | .indc i => [.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩] ++ (.indc <$> Shrinkable.shrink i)
    | .recr r => [.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩] ++ (.recr <$> Shrinkable.shrink r)

instance : Shrinkable ConstantInfo where
  shrink
    | .defn d => .defn <$> Shrinkable.shrink d
    | .axio a => (.axio <$> Shrinkable.shrink a) ++ [.axio ⟨false, 0, .sort 0⟩]
    | .quot q => (.quot <$> Shrinkable.shrink q) ++ [.axio ⟨false, 0, .sort 0⟩]
    | .recr r => (.recr <$> Shrinkable.shrink r) ++ [.axio ⟨false, 0, .sort 0⟩]
    | .cPrj p => .cPrj <$> Shrinkable.shrink p
    | .rPrj p => .rPrj <$> Shrinkable.shrink p
    | .iPrj p => .iPrj <$> Shrinkable.shrink p
    | .dPrj p => .dPrj <$> Shrinkable.shrink p
    | .muts ms => if ms.size > 0 then [.muts ms.pop] else []

instance : Shrinkable Constant where
  shrink c :=
    (if c.sharing.size > 0 then [{ c with sharing := c.sharing.pop }] else []) ++
    (if c.refs.size > 0 then [{ c with refs := c.refs.pop }] else []) ++
    (if c.univs.size > 0 then [{ c with univs := c.univs.pop }] else [])

-- DataValue - shrink to simpler variant
instance : Shrinkable DataValue where
  shrink
    | .ofBool _ => []
    | _ => [.ofBool true]

/-! ## SampleableExt instances -/

instance : SampleableExt DefKind := SampleableExt.mkSelfContained genDefKind
instance : SampleableExt DefinitionSafety := SampleableExt.mkSelfContained genDefinitionSafety
instance : SampleableExt QuotKind := SampleableExt.mkSelfContained genQuotKindNew
instance : SampleableExt Univ := SampleableExt.mkSelfContained genUniv
instance : SampleableExt Expr := SampleableExt.mkSelfContained genExpr
instance : SampleableExt Definition := SampleableExt.mkSelfContained genDefinition
instance : SampleableExt Axiom := SampleableExt.mkSelfContained genAxiom
instance : SampleableExt Quotient := SampleableExt.mkSelfContained genQuotient
instance : SampleableExt RecursorRule := SampleableExt.mkSelfContained genRecursorRule
instance : SampleableExt Recursor := SampleableExt.mkSelfContained genRecursor
instance : SampleableExt Constructor := SampleableExt.mkSelfContained genConstructor
instance : SampleableExt Inductive := SampleableExt.mkSelfContained genInductive
instance : SampleableExt InductiveProj := SampleableExt.mkSelfContained genInductiveProj
instance : SampleableExt ConstructorProj := SampleableExt.mkSelfContained genConstructorProj
instance : SampleableExt RecursorProj := SampleableExt.mkSelfContained genRecursorProj
instance : SampleableExt DefinitionProj := SampleableExt.mkSelfContained genDefinitionProj
instance : SampleableExt MutConst := SampleableExt.mkSelfContained genMutConst
instance : SampleableExt ConstantInfo := SampleableExt.mkSelfContained genConstantInfo
instance : SampleableExt Constant := SampleableExt.mkSelfContained genConstant

/-! ## Generators for Metadata Types -/

/-- Generate a DataValue. -/
def genDataValueNew : Gen DataValue :=
  frequency [
    (10, .ofString <$> genAddress),
    (10, .ofBool <$> genBool),
    (10, .ofName <$> genAddress),
    (10, .ofNat <$> genAddress),
    (10, .ofInt <$> genAddress),
    (10, .ofSyntax <$> genAddress),
  ]

instance : SampleableExt DataValue := SampleableExt.mkSelfContained genDataValueNew

/-! ## Generators for Constant Metadata Types -/

/-- Generate a KVMap entry -/
def genKVMapEntry : Gen (Address × DataValue) :=
  Prod.mk <$> genAddress <*> genDataValueNew

/-- Generate a KVMap (key-value pairs for mdata) -/
def genKVMap : Gen KVMap :=
  genSmallArray genKVMapEntry

/-- Generate an ExprMetaData node with arena indices bounded by arenaSize -/
def genExprMetaData (arenaSize : Nat := 0) : Gen ExprMetaData :=
  let genIdx : Gen UInt64 :=
    if arenaSize == 0 then pure 0
    else UInt64.ofNat <$> Gen.choose Nat 0 (arenaSize - 1)
  frequency [
    (20, pure .leaf),
    (15, ExprMetaData.app <$> genIdx <*> genIdx),
    (15, ExprMetaData.binder <$> genAddress <*> genBinderInfo <*> genIdx <*> genIdx),
    (10, ExprMetaData.letBinder <$> genAddress <*> genIdx <*> genIdx <*> genIdx),
    (15, ExprMetaData.ref <$> genAddress),
    (10, ExprMetaData.prj <$> genAddress <*> genIdx),
    (5, ExprMetaData.mdata <$> genSmallArray genKVMap <*> genIdx),
  ]

/-- Generate a valid ExprMetaArena by building nodes bottom-up
    so child indices always reference earlier entries. -/
def genExprMetaArena : Gen ExprMetaArena := do
  let numNodes ← Gen.choose Nat 0 6
  let mut arena : ExprMetaArena := {}
  for _ in [:numNodes] do
    let node ← genExprMetaData arena.nodes.size
    arena := { nodes := arena.nodes.push node }
  pure arena

/-- Generate a ConstantMeta with all variants -/
def genConstantMeta : Gen ConstantMeta := do
  let arena ← genExprMetaArena
  let genRoot : Gen UInt64 :=
    if arena.nodes.size == 0 then pure 0
    else UInt64.ofNat <$> Gen.choose Nat 0 (arena.nodes.size - 1)
  frequency [
    (10, pure .empty),
    (15, ConstantMeta.defn <$> genAddress <*> genSmallArray genAddress
      <*> genReducibilityHints <*> genSmallArray genAddress <*> genSmallArray genAddress
      <*> pure arena <*> genRoot <*> genRoot),
    (15, ConstantMeta.axio <$> genAddress <*> genSmallArray genAddress
      <*> pure arena <*> genRoot),
    (10, ConstantMeta.quot <$> genAddress <*> genSmallArray genAddress
      <*> pure arena <*> genRoot),
    (15, ConstantMeta.indc <$> genAddress <*> genSmallArray genAddress <*> genSmallArray genAddress
      <*> genSmallArray genAddress <*> genSmallArray genAddress
      <*> pure arena <*> genRoot),
    (15, ConstantMeta.ctor <$> genAddress <*> genSmallArray genAddress <*> genAddress
      <*> pure arena <*> genRoot),
    (15, ConstantMeta.recr <$> genAddress <*> genSmallArray genAddress <*> genSmallArray genAddress
      <*> genSmallArray genAddress <*> genSmallArray genAddress
      <*> pure arena <*> genRoot <*> genSmallArray genRoot),
  ]

instance : Shrinkable ExprMetaData where
  shrink em := match em with
    | .leaf => []
    | _ => [.leaf]

instance : Shrinkable ExprMetaArena where
  shrink arena := if arena.nodes.size > 0 then [{ nodes := arena.nodes.pop }] else []

instance : Shrinkable ConstantMeta where
  shrink m := match m with
    | .empty => []
    | _ => [.empty]

instance : SampleableExt ExprMetaData := SampleableExt.mkSelfContained (genExprMetaData 5)
instance : SampleableExt ExprMetaArena := SampleableExt.mkSelfContained genExprMetaArena
instance : SampleableExt ConstantMeta := SampleableExt.mkSelfContained genConstantMeta

/-- Generate a Named entry with proper metadata. -/
def genNamed : Gen Named :=
  Named.mk <$> genAddress <*> genConstantMeta

/-- Generate a Comm. -/
def genCommNew : Gen Comm :=
  Comm.mk <$> genAddress <*> genAddress

instance : Shrinkable Named where
  shrink n := match n.constMeta with
    | .empty => []
    | _ => [{ n with constMeta := .empty }]

instance : Shrinkable Comm where
  shrink _ := []

instance : SampleableExt Named := SampleableExt.mkSelfContained genNamed
instance : SampleableExt Comm := SampleableExt.mkSelfContained genCommNew

/-! ## Generators for RawEnv Types -/

/-- Generate a ByteArray for blobs -/
def genByteArray : Gen ByteArray := do
  let len ← Gen.choose Nat 0 32
  let mut bytes : Array UInt8 := #[]
  for _ in [:len] do
    let b ← Gen.choose Nat 0 255
    bytes := bytes.push b.toUInt8
  pure (ByteArray.mk bytes)

/-- Generate an Ix.Name for RawNamed -/
def genIxName : Nat → Gen Ix.Name
  | 0 => pure Ix.Name.mkAnon
  | fuel + 1 => Gen.frequency #[
      (3, pure Ix.Name.mkAnon),
      (5, do
        let parent ← genIxName fuel
        let s ← Gen.elements #["a", "b", "test", "foo", "bar"]
        pure (Ix.Name.mkStr parent s)),
      (2, do
        let parent ← genIxName fuel
        let n ← Gen.choose Nat 0 100
        pure (Ix.Name.mkNat parent n))
    ] (pure Ix.Name.mkAnon)

/-- Generate a RawConst -/
def genRawConst : Gen RawConst :=
  RawConst.mk <$> genAddress <*> genConstant

/-- Generate a RawNamed with empty metadata (matching Rust test generator).
    Metadata addresses must reference valid names in env.names for indexed serialization. -/
def genRawNamed : Gen RawNamed :=
  RawNamed.mk <$> genIxName 3 <*> genAddress <*> pure .empty

/-- Generate a RawBlob -/
def genRawBlob : Gen RawBlob :=
  RawBlob.mk <$> genAddress <*> genByteArray

/-- Generate a RawComm -/
def genRawComm : Gen RawComm :=
  RawComm.mk <$> genAddress <*> genCommNew

/-- Generate a RawNameEntry -/
def genRawNameEntry : Gen RawNameEntry :=
  RawNameEntry.mk <$> genAddress <*> genIxName 3

/-- Generate a RawEnv with small arrays to avoid memory issues -/
def genRawEnv : Gen RawEnv :=
  RawEnv.mk <$> genSmallArray genRawConst
    <*> genSmallArray genRawNamed
    <*> genSmallArray genRawBlob
    <*> genSmallArray genRawComm
    <*> genSmallArray genRawNameEntry

instance : Shrinkable RawConst where
  shrink rc := (fun c => { rc with const := c }) <$> Shrinkable.shrink rc.const

instance : Shrinkable RawNamed where
  shrink rn := match rn.constMeta with
    | .empty => []
    | _ => [{ rn with constMeta := .empty }]

instance : Shrinkable RawBlob where
  shrink rb := if rb.bytes.size > 0 then [{ rb with bytes := ByteArray.empty }] else []

instance : Shrinkable RawComm where
  shrink _ := []

instance : Shrinkable RawEnv where
  shrink env :=
    (if env.consts.size > 0 then [{ env with consts := env.consts.pop }] else []) ++
    (if env.named.size > 0 then [{ env with named := env.named.pop }] else []) ++
    (if env.blobs.size > 0 then [{ env with blobs := env.blobs.pop }] else []) ++
    (if env.comms.size > 0 then [{ env with comms := env.comms.pop }] else []) ++
    (if env.names.size > 0 then [{ env with names := env.names.pop }] else [])

instance : SampleableExt RawConst := SampleableExt.mkSelfContained genRawConst
instance : SampleableExt RawNamed := SampleableExt.mkSelfContained genRawNamed
instance : SampleableExt RawBlob := SampleableExt.mkSelfContained genRawBlob
instance : SampleableExt RawComm := SampleableExt.mkSelfContained genRawComm
instance : SampleableExt RawEnv := SampleableExt.mkSelfContained genRawEnv

end Tests.Gen.Ixon

end
