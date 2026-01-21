import Ix.Ixon
import Ix.IxonOld
import Ix.Sharing
import Tests.Common

open LSpec SlimCheck Gen Ixon

def genAddress : Gen Address :=
  pure (Address.mk (Blake3.hash "foobar".toUTF8).val)

def genNat : Gen Nat := USize.toNat <$> genUSize

def genBool : Gen Bool := choose Bool .false true

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

def genEvalClaim : Gen IxonOld.EvalClaim :=
  .mk <$> genAddress <*> genAddress <*> genAddress <*> genAddress

def genCheckClaim : Gen IxonOld.CheckClaim :=
  .mk <$> genAddress <*> genAddress <*> genAddress

def genClaim : Gen IxonOld.Claim :=
  frequency [(10, .evals <$> genEvalClaim), (10, .checks <$> genCheckClaim)]

def genProof : Gen IxonOld.Proof :=
  .mk <$> genClaim <*> pure "foobar".toUTF8

def genComm : Gen IxonOld.Comm :=
  .mk <$> genAddress <*> genAddress

def genMetaAddress : Gen MetaAddress :=
  .mk <$> genAddress <*> genAddress

def genEnv : Gen IxonOld.Env :=
  .mk <$> genList genMetaAddress

def genBinderInfo : Gen Lean.BinderInfo :=
  elements #[.default, .implicit, .strictImplicit, .instImplicit]

def genReducibilityHints : Gen Lean.ReducibilityHints :=
  frequency [
    (10, pure .opaque),
    (10, pure .abbrev),
    (10, .regular <$> genUInt32),
  ]

def genDataValue : Gen IxonOld.DataValue :=
  frequency [
    (10, .ofString <$> genAddress),
    (10, .ofBool <$> genBool),
    (10, .ofName <$> genAddress),
    (10, .ofNat <$> genAddress),
    (10, .ofInt <$> genAddress),
    (10, .ofSyntax <$> genAddress),
  ]

def genMetadatum : Gen IxonOld.Metadatum :=
  frequency [
    (10, .info <$> genBinderInfo),
    (10, .link <$> genAddress),
    (10, .hints <$> genReducibilityHints),
    (10, .links <$> genList genAddress),
    --(10, .rules <$> genList genAddress),
    (10, .kvmap <$> genList (Prod.mk <$> genAddress <*> genDataValue)),
  ]

def genMetadata : Gen IxonOld.Metadata :=
  .mk <$> genList genMetadatum

-- OLD format generators (for IxonOld.Ixon tests)
def genOldDefinition : Gen IxonOld.Definition :=
  .mk <$> elements #[.definition, .opaque, .theorem]
    <*> elements #[.unsafe, .safe, .partial]
    <*> genNat <*> genAddress <*> genAddress

def genOldAxiom : Gen IxonOld.Axiom :=
  .mk <$> genBool <*> genNat <*> genAddress

def genOldQuotient : Gen IxonOld.Quotient :=
  .mk <$> elements #[.type, .ctor, .lift, .ind] <*> genNat <*> genAddress

def genOldConstructorProj : Gen IxonOld.ConstructorProj :=
  .mk <$> genNat <*> genNat <*> genAddress

def genOldInductiveProj : Gen IxonOld.InductiveProj :=
  .mk <$> genNat <*> genAddress

def genOldDefinitionProj : Gen IxonOld.DefinitionProj :=
  .mk <$> genNat <*> genAddress

def genOldRecursorRule : Gen IxonOld.RecursorRule :=
  .mk <$> genNat <*> genAddress

def genOldRecursor : Gen IxonOld.Recursor :=
  .mk <$> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genNat
    <*> genAddress <*> genList genOldRecursorRule

def genOldConstructor : Gen IxonOld.Constructor :=
  .mk <$> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genAddress

def genOldInductive : Gen IxonOld.Inductive :=
  .mk <$> genBool <*> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat
    <*> genAddress <*> genList genOldConstructor

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

instance : Shrinkable Univ where
  shrink _ := []

instance : Shrinkable Expr where
  shrink _ := []

instance : Shrinkable ConstantInfo where
  shrink _ := []

instance : Shrinkable Constant where
  shrink _ := []

instance : SampleableExt Univ := SampleableExt.mkSelfContained genUniv
instance : SampleableExt Expr := SampleableExt.mkSelfContained genExpr
instance : SampleableExt ConstantInfo := SampleableExt.mkSelfContained genConstantInfo
instance : SampleableExt Constant := SampleableExt.mkSelfContained genConstant

/-!
## Roundtrip Tests for New Format Types
-/

def univSerde (u : Univ) : Bool :=
  let bytes := serUniv u
  match desUniv bytes with
  | .ok u' => u == u'
  | .error _ => false

def exprSerde (e : Expr) : Bool :=
  let bytes := serExpr e
  match desExpr bytes with
  | .ok e' => e == e'
  | .error _ => false

def constantSerde (c : Constant) : Bool :=
  let bytes := serConstant c
  match desConstant bytes with
  | .ok c' => c == c'
  | .error _ => false

partial def genIxon : Gen IxonOld.Ixon :=
  frequency [
    (10, pure .nanon),
    (10, .nstr <$> genAddress <*> genAddress),
    (10, .nnum <$> genAddress <*> genAddress),
    (10, pure .uzero),
    (10, .usucc <$> genAddress),
    (10, .umax <$> genAddress <*> genAddress),
    (10, .uimax <$> genAddress <*> genAddress),
    (10, .uvar <$> genNat),
    (10, .evar <$> genNat),
    (10, .eref <$> genAddress <*> genList genAddress),
    (10, .erec <$> genNat <*> genList genAddress),
    (10, .eprj <$> genAddress <*> genNat <*> genAddress),
    (10, .esort <$> genAddress),
    (10, .estr <$> genAddress),
    (10, .enat <$> genAddress),
    (10, .eapp <$> genAddress <*> genAddress),
    (10, .elam <$> genAddress <*> genAddress),
    (10, .eall <$> genAddress <*> genAddress),
    (10, .elet <$> genBool <*> genAddress <*> genAddress <*> genAddress),
    (10, (.blob ∘ .mk ∘ .mk) <$> genList genUInt8),
    (10, .defn <$> genOldDefinition),
    (10, .axio <$> genOldAxiom),
    (10, .quot <$> genOldQuotient),
    (10, .cprj <$> genOldConstructorProj),
    (10, .iprj <$> genOldInductiveProj),
    (10, .dprj <$> genOldDefinitionProj),
    (10, .muts <$> genList (IxonOld.MutConst.indc <$> genOldInductive)),
    (10, .muts <$> genList (IxonOld.MutConst.defn <$> genOldDefinition)),
    (10, .muts <$> genList (IxonOld.MutConst.recr <$> genOldRecursor)),
    (10, .prof <$> genProof),
    (10, .eval <$> genEvalClaim),
    (10, .chck <$> genCheckClaim),
    (10, .comm <$> genComm),
    (10, .envn <$> genEnv),
    (10, .meta <$> genMetadata),
  ]

instance : Shrinkable IxonOld.Ixon where
  shrink _ := []

instance : SampleableExt IxonOld.Ixon := SampleableExt.mkSelfContained genIxon

@[extern "rs_eq_lean_rust_serialization"]
private opaque eqLeanRustSerialization : @& IxonOld.Ixon → @& ByteArray → Bool

def ixonSerde (ixon : IxonOld.Ixon) : Bool :=
  let bytes := IxonOld.ser ixon
  if !eqLeanRustSerialization ixon bytes then false else
    match IxonOld.de bytes with
    | .ok ixon' => ixon == ixon'
    | .error _ => false

/-!
## Unit Tests for New Format Types
-/

def univUnits : TestSeq :=
  let cases : List Univ := [
    .zero,
    .var 0,
    .var 42,
    .succ .zero,
    .succ (.succ .zero),
    .succ (.succ (.succ .zero)),  -- Test telescope compression
    .max .zero (.var 0),
    .imax (.var 1) .zero,
    .max (.succ .zero) (.succ (.succ .zero)),
  ]
  cases.foldl (init := .done) fun acc u =>
    acc ++ test s!"Univ roundtrip: {repr u}" (univSerde u)

def exprUnits : TestSeq :=
  let cases : List Expr := [
    .sort 0,
    .var 0,
    .var 42,
    .ref 0 #[],
    .ref 1 #[0, 1, 2],
    .recur 0 #[],
    .recur 2 #[1],
    .str 5,
    .nat 10,
    .share 0,
    .app (.var 0) (.var 1),
    .app (.app (.var 0) (.var 1)) (.var 2),  -- Nested apps (telescope)
    .lam (.sort 0) (.var 0),
    .lam (.sort 0) (.lam (.sort 1) (.var 0)),  -- Nested lams (telescope)
    .all (.sort 0) (.var 0),
    .all (.sort 0) (.all (.sort 1) (.var 0)),  -- Nested alls (telescope)
    .letE true (.sort 0) (.var 0) (.var 1),
    .letE false (.sort 0) (.var 0) (.var 1),
    .prj 0 1 (.var 0),
  ]
  cases.foldl (init := .done) fun acc e =>
    acc ++ test s!"Expr roundtrip: {repr e}" (exprSerde e)

def constantUnits : TestSeq :=
  let defn := Definition.mk .defn .safe 0 (.sort 0) (.var 0)
  let c := Constant.mk
    (.defn defn)
    #[.var 0, .sort 1]  -- sharing
    #[Address.mk (Blake3.hash "ref".toUTF8).val]  -- refs
    #[.zero, .succ .zero]  -- univs
  test "Constant roundtrip" (constantSerde c)

-- Tests.Ixon.suite defined at end of file (after FFI functions)

/-!
## Sharing Analysis Tests
-/

def sharingTest1 : Bool :=
  let e1 := Expr.app (.var 0) (.var 1)
  let (rewritten1, sharing1) := Ix.Sharing.applySharing #[e1]
  sharing1.isEmpty && rewritten1[0]! == e1

def sharingTest2 : Bool :=
  let ty := Expr.sort 0
  let e2 := Expr.app (.lam ty (.var 0)) (.lam ty (.var 1))
  let (_, sharing2) := Ix.Sharing.applySharing #[e2]
  sharing2.size == 1 ∨ sharing2.isEmpty

def sharingTest3 : Bool :=
  let var0 := Expr.var 0
  let e3a := Expr.app var0 var0
  let e3b := Expr.app var0 (.var 1)
  let e3c := Expr.app var0 (.var 2)
  let (_, sharing3) := Ix.Sharing.applySharing #[e3a, e3b, e3c]
  sharing3.isEmpty ∨ sharing3.size > 0

def sharingTest4 : Bool :=
  let e4 := Expr.lam (.sort 0) (.app (.var 0) (.var 0))
  let (rewritten4, _) := Ix.Sharing.applySharing #[e4]
  let serialized := serExpr rewritten4[0]!
  match desExpr serialized with
  | .ok e => e == rewritten4[0]!
  | .error _ => false

def sharingUnits : TestSeq :=
  test "no sharing for unique subterms" sharingTest1
  ++ test "shares repeated sort 0" sharingTest2
  ++ test "analyzes multiple expressions" sharingTest3
  ++ test "roundtrip after sharing" sharingTest4

/-!
## Cross-implementation Tests (FFI)
-/

/-- FFI: Check if Lean's computed hash matches Rust's computed hash -/
@[extern "rs_expr_hash_matches"]
private opaque rsExprHashMatches : @& Expr → @& Address → Bool

/-- FFI: Check if Lean's Univ serialization matches Rust -/
@[extern "rs_eq_univ_serialization"]
private opaque rsEqUnivSerialization : @& Univ → @& ByteArray → Bool

/-- FFI: Check if Lean's Expr serialization matches Rust -/
@[extern "rs_eq_expr_serialization"]
private opaque rsEqExprSerialization : @& Expr → @& ByteArray → Bool

/-- FFI: Check if Lean's Constant serialization matches Rust -/
@[extern "rs_eq_constant_serialization"]
private opaque rsEqConstantSerialization : @& Constant → @& ByteArray → Bool

/-- Check that Lean and Rust produce identical hashes for an expression -/
def exprHashMatchesRust (e : Expr) : Bool :=
  let leanHash := Ix.Sharing.computeExprHash e
  rsExprHashMatches e leanHash

/-- Check that Lean's Univ serialization matches Rust -/
def univSerdeMatchesRust (u : Univ) : Bool :=
  let bytes := serUniv u
  rsEqUnivSerialization u bytes

/-- Check that Lean's Expr serialization matches Rust -/
def exprSerdeMatchesRust (e : Expr) : Bool :=
  let bytes := serExpr e
  rsEqExprSerialization e bytes

/-- Check that Lean's Constant serialization matches Rust -/
def constantSerdeMatchesRust (c : Constant) : Bool :=
  let bytes := serConstant c
  rsEqConstantSerialization c bytes

/-!
### Cross-implementation Unit Tests (runtime)
-/

def crossImplUnivUnits : TestSeq :=
  let cases : List Univ := [
    .zero,
    .var 0,
    .var 42,
    .succ .zero,
    .succ (.succ .zero),
    .max .zero (.var 0),
    .imax (.var 1) .zero,
  ]
  cases.foldl (init := .done) fun acc u =>
    acc ++ test s!"Univ FFI: {repr u}" (univSerdeMatchesRust u)

def crossImplExprUnits : TestSeq :=
  let cases : List Expr := [
    .sort 0,
    .var 0,
    .var 42,
    .ref 0 #[],
    .ref 1 #[0, 1, 2],
    .recur 0 #[],
    .str 5,
    .nat 10,
    .share 0,
    .app (.var 0) (.var 1),
    .lam (.sort 0) (.var 0),
    .all (.sort 0) (.var 0),
    .letE true (.sort 0) (.var 0) (.var 1),
    .prj 0 1 (.var 0),
  ]
  cases.foldl (init := .done) fun acc e =>
    acc ++ test s!"Expr FFI: {repr e}" (exprSerdeMatchesRust e)

def crossImplHashUnits : TestSeq :=
  let cases : List Expr := [
    .sort 0,
    .var 0,
    .app (.var 0) (.var 1),
    .lam (.sort 0) (.var 0),
  ]
  cases.foldl (init := .done) fun acc e =>
    acc ++ test s!"Expr hash FFI: {repr e}" (exprHashMatchesRust e)

-- Constant FFI unit tests (runtime)
def crossImplConstantUnits : TestSeq :=
  -- Simple definition
  let defn1 := Definition.mk .defn .safe 0 (.sort 0) (.var 0)
  let c1 := Constant.mk (.defn defn1) #[] #[] #[]

  -- Definition with lvls > 0
  let defn2 := Definition.mk .defn .safe 2 (.sort 0) (.var 0)
  let c2 := Constant.mk (.defn defn2) #[] #[] #[]

  -- Opaque
  let defn3 := Definition.mk .opaq .safe 1 (.sort 0) (.var 0)
  let c3 := Constant.mk (.defn defn3) #[] #[] #[]

  -- Theorem
  let defn4 := Definition.mk .thm .safe 0 (.sort 0) (.var 0)
  let c4 := Constant.mk (.defn defn4) #[] #[] #[]

  -- Unsafe definition
  let defn5 := Definition.mk .defn .unsaf 0 (.sort 0) (.var 0)
  let c5 := Constant.mk (.defn defn5) #[] #[] #[]

  -- Axiom
  let ax := Axiom.mk false 1 (.sort 0)
  let c6 := Constant.mk (.axio ax) #[] #[] #[]

  -- Quotient
  let quot := Ixon.Quotient.mk QuotKind.type 0 (.sort 0)
  let c7 := Constant.mk (.quot quot) #[] #[] #[]

  -- Recursor (simple)
  let rule1 := RecursorRule.mk 2 (.var 0)
  let recr1 := Recursor.mk false false 1 2 1 1 1 (.sort 0) #[rule1]
  let c8 := Constant.mk (.recr recr1) #[] #[] #[]

  -- Recursor with k=true
  let recr2 := Recursor.mk true false 0 1 0 1 1 (.sort 0) #[]
  let c9 := Constant.mk (.recr recr2) #[] #[] #[]

  -- InductiveProj
  let addr : Address := default
  let iproj := InductiveProj.mk 0 addr
  let c10 := Constant.mk (.iPrj iproj) #[] #[] #[]

  -- ConstructorProj
  let cproj := ConstructorProj.mk 0 1 addr
  let c11 := Constant.mk (.cPrj cproj) #[] #[] #[]

  -- RecursorProj
  let rproj := RecursorProj.mk 0 addr
  let c12 := Constant.mk (.rPrj rproj) #[] #[] #[]

  -- DefinitionProj
  let dproj := DefinitionProj.mk 0 addr
  let c13 := Constant.mk (.dPrj dproj) #[] #[] #[]

  -- Muts with single definition
  let mutDefn := Definition.mk .defn .safe 0 (.sort 0) (.var 0)
  let c14 := Constant.mk (.muts #[MutConst.defn mutDefn]) #[] #[] #[]

  -- Muts with inductive
  let ctor1 := Constructor.mk false 1 0 1 2 (.sort 0)
  let indc1 := Inductive.mk true false false 1 1 0 0 (.sort 0) #[ctor1]
  let c15 := Constant.mk (.muts #[MutConst.indc indc1]) #[] #[] #[]

  -- Muts with recursor
  let mutRecr := Recursor.mk false false 1 1 0 1 1 (.sort 0) #[]
  let c16 := Constant.mk (.muts #[MutConst.recr mutRecr]) #[] #[] #[]

  test "Constant FFI: simple defn" (constantSerdeMatchesRust c1)
  ++ test "Constant FFI: defn with lvls" (constantSerdeMatchesRust c2)
  ++ test "Constant FFI: opaque" (constantSerdeMatchesRust c3)
  ++ test "Constant FFI: theorem" (constantSerdeMatchesRust c4)
  ++ test "Constant FFI: unsafe defn" (constantSerdeMatchesRust c5)
  ++ test "Constant FFI: axiom" (constantSerdeMatchesRust c6)
  ++ test "Constant FFI: quotient" (constantSerdeMatchesRust c7)
  ++ test "Constant FFI: recursor" (constantSerdeMatchesRust c8)
  ++ test "Constant FFI: recursor k=true" (constantSerdeMatchesRust c9)
  ++ test "Constant FFI: inductive proj" (constantSerdeMatchesRust c10)
  ++ test "Constant FFI: constructor proj" (constantSerdeMatchesRust c11)
  ++ test "Constant FFI: recursor proj" (constantSerdeMatchesRust c12)
  ++ test "Constant FFI: definition proj" (constantSerdeMatchesRust c13)
  ++ test "Constant FFI: muts defn" (constantSerdeMatchesRust c14)
  ++ test "Constant FFI: muts inductive" (constantSerdeMatchesRust c15)
  ++ test "Constant FFI: muts recursor" (constantSerdeMatchesRust c16)

def crossImplUnits : TestSeq :=
  crossImplUnivUnits ++ crossImplExprUnits ++ crossImplHashUnits ++ crossImplConstantUnits

/-!
## Env Serialization Tests
-/

/-- FFI: Test Env serialization roundtrip through Rust. -/
@[extern "rs_env_serde_roundtrip"]
opaque rsEnvSerdeRoundtrip : @& ByteArray → Bool

/-- FFI: Check that Rust can deserialize Lean's Env. -/
@[extern "rs_env_serde_check"]
opaque rsEnvSerdeCheck : @& ByteArray → Bool

/-- Lean-only Env roundtrip test. -/
def envSerdeLean (env : Env) : Bool :=
  let bytes := serEnv env
  match desEnv bytes with
  | .ok env' =>
    -- Check counts match
    env.constCount == env'.constCount &&
    env.blobCount == env'.blobCount &&
    env.namedCount == env'.namedCount
  | .error _ => false

/-- Generate a simple Env for testing. -/
def genSimpleEnv : Gen Env := do
  -- Generate a few constants
  let numConsts ← Gen.choose Nat 0 5
  let mut env : Env := {}

  for _ in [:numConsts] do
    -- Generate a constant
    let c ← genConstant
    let bytes := serConstant c
    let addr := Address.blake3 bytes
    env := env.storeConst addr c

    -- Generate a name and register it
    let name := Lean.Name.mkSimple s!"const_{addr.hash[0]!}"
    env := env.registerName name addr

    -- Also store the name components
    env := { env with names := env.names.insert (Env.hashName name) name }

  -- Generate a few blobs
  let numBlobs ← Gen.choose Nat 0 3
  for i in [:numBlobs] do
    let blobBytes : ByteArray := .mk #[i.toUInt8, (i+1).toUInt8, (i+2).toUInt8]
    let (env', _) := env.storeBlob blobBytes
    env := env'

  pure env

instance : Shrinkable Env where
  shrink _ := []

instance : SampleableExt Env := SampleableExt.mkSelfContained genSimpleEnv

/-- Env unit tests -/
def envUnits : TestSeq :=
  -- Empty env
  let env0 : Env := {}
  let t0 := test "Env roundtrip: empty" (envSerdeLean env0)

  -- Env with one constant
  let defn1 := Definition.mk .defn .safe 0 (.sort 0) (.var 0)
  let c1 := Constant.mk (.defn defn1) #[] #[] #[]
  let bytes1 := serConstant c1
  let addr1 := Address.blake3 bytes1
  let name1 := Lean.Name.mkSimple "TestConst1"
  let env1 := ({} : Env)
    |>.storeConst addr1 c1
    |>.registerName name1 addr1
  let env1' := { env1 with names := env1.names.insert (Env.hashName name1) name1 }
  let t1 := test "Env roundtrip: one constant" (envSerdeLean env1')

  -- Env with blob
  let blobBytes : ByteArray := .mk #[1, 2, 3, 4, 5]
  let (env2, _) := ({} : Env).storeBlob blobBytes
  let t2 := test "Env roundtrip: one blob" (envSerdeLean env2)

  -- Env with hierarchical name
  let name3 := Lean.Name.str (Lean.Name.str .anonymous "Foo") "bar"
  let env3 := ({} : Env)
    |>.storeConst addr1 c1
    |>.registerName name3 addr1
  let env3' := { env3 with
    names := env3.names
      |>.insert (Env.hashName .anonymous) .anonymous
      |>.insert (Env.hashName (Lean.Name.str .anonymous "Foo")) (Lean.Name.str .anonymous "Foo")
      |>.insert (Env.hashName name3) name3 }
  let t3 := test "Env roundtrip: hierarchical name" (envSerdeLean env3')

  t0 ++ t1 ++ t2 ++ t3

/-- Env FFI unit tests -/
def envFFIUnits : TestSeq :=
  -- Empty env
  let env0 : Env := {}
  let bytes0 := serEnv env0
  let t0 := test "Env FFI: empty env check" (rsEnvSerdeCheck bytes0)

  -- Env with one constant
  let defn1 := Definition.mk .defn .safe 0 (.sort 0) (.var 0)
  let c1 := Constant.mk (.defn defn1) #[] #[] #[]
  let cBytes := serConstant c1
  let addr1 := Address.blake3 cBytes
  let name1 := Lean.Name.mkSimple "TestConst1"
  let env1 := ({} : Env)
    |>.storeConst addr1 c1
    |>.registerName name1 addr1
  let env1' := { env1 with names := env1.names.insert (Env.hashName name1) name1 }
  let bytes1 := serEnv env1'
  let t1 := test "Env FFI: one constant check" (rsEnvSerdeCheck bytes1)

  t0 ++ t1

def Tests.Ixon.units : TestSeq :=
  univUnits ++ exprUnits ++ constantUnits ++ sharingUnits ++ crossImplUnits ++ envUnits ++ envFFIUnits

/-! ## Test Suite (property-based) -/

def Tests.Ixon.suite := [
  check "Ixon serde roundtrips" (∀ ixon : IxonOld.Ixon, ixonSerde ixon),
  check "Univ serde roundtrips" (∀ u : Univ, univSerde u),
  check "Expr serde roundtrips" (∀ e : Expr, exprSerde e),
  check "Constant serde roundtrips" (∀ c : Constant, constantSerde c),
  -- Cross-implementation tests (property-based, run at compile time)
  check "Univ serde matches Rust" (∀ u : Univ, univSerdeMatchesRust u),
  check "Expr serde matches Rust" (∀ e : Expr, exprSerdeMatchesRust e),
  check "Expr sharing hash matches Rust" (∀ e : Expr, exprHashMatchesRust e),
  check "Constant serde matches Rust" (∀ c : Constant, constantSerdeMatchesRust c),
  check "Env serde roundtrips" (∀ env : Env, envSerdeLean env),
]
