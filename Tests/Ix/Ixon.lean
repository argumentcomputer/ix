import Ix.Ixon
import Tests.Common

open LSpec SlimCheck Gen

def genAddress : Gen Address :=
  pure (Address.mk (Blake3.hash "foobar".toUTF8).val)

def genNat : Gen Nat := USize.toNat <$> genUSize

def genBool : Gen Bool := choose Bool .false true

-- aggressively reduce size parameter to avoid tree blow-up
def genList (n: Gen α) : Gen (List α) :=
  resize (fun s => if s > 8 then 8 else s / 2) $ listOf n

def genDefKind : Gen Ix.DefKind :=
  elements #[.definition, .opaque, .theorem]

def genDefinitionSafety : Gen Lean.DefinitionSafety :=
  elements #[.unsafe, .safe, .partial]

def genDefinition : Gen Ixon.Definition :=
  .mk <$> genDefKind <*> genDefinitionSafety <*> genNat <*> genAddress <*> genAddress

def genAxiom : Gen Ixon.Axiom :=
  .mk <$> genBool <*> genNat <*> genAddress

def genQuotKind : Gen Lean.QuotKind :=
  elements #[.type, .ctor, .lift, .ind]

def genQuotient : Gen Ixon.Quotient :=
  .mk <$> genQuotKind <*> genNat <*> genAddress

def genConstructorProj : Gen Ixon.ConstructorProj :=
  .mk <$> genNat <*> genNat <*> genAddress

def genRecursorProj : Gen Ixon.RecursorProj :=
  .mk <$> genNat <*> genAddress

def genInductiveProj : Gen Ixon.InductiveProj :=
  .mk <$> genNat <*> genAddress

def genDefinitionProj : Gen Ixon.DefinitionProj :=
  .mk <$> genNat <*> genAddress

def genRecursorRule : Gen Ixon.RecursorRule :=
  .mk <$> genNat <*> genAddress

def genRecursor : Gen Ixon.Recursor :=
  .mk <$> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genNat
    <*> genAddress <*> genList genRecursorRule

def genConstructor : Gen Ixon.Constructor :=
  .mk <$> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genAddress

def genInductive : Gen Ixon.Inductive :=
  .mk <$> genBool <*> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat
    <*> genAddress <*> genList genConstructor
    --<*> genList genRecursor

def genEvalClaim : Gen Ixon.EvalClaim :=
  .mk <$> genAddress <*> genAddress <*> genAddress <*> genAddress

def genCheckClaim : Gen Ixon.CheckClaim :=
  .mk <$> genAddress <*> genAddress <*> genAddress

def genClaim : Gen Ixon.Claim :=
  frequency [(10, .evals <$> genEvalClaim), (10, .checks <$> genCheckClaim)]

def genProof : Gen Ixon.Proof :=
  .mk <$> genClaim <*> pure "foobar".toUTF8

def genComm : Gen Ixon.Comm :=
  .mk <$> genAddress <*> genAddress

def genMetaAddress : Gen MetaAddress :=
  .mk <$> genAddress <*> genAddress

def genEnv : Gen Ixon.Env :=
  .mk <$> genList genMetaAddress

def genBinderInfo : Gen Lean.BinderInfo :=
  elements #[.default, .implicit, .strictImplicit, .instImplicit]

def genReducibilityHints : Gen Lean.ReducibilityHints :=
  frequency [
    (10, pure .opaque),
    (10, pure .abbrev),
    (10, .regular <$> genUInt32),
  ]

def genDataValue : Gen Ixon.DataValue :=
  frequency [
    (10, .ofString <$> genAddress),
    (10, .ofBool <$> genBool),
    (10, .ofName <$> genAddress),
    (10, .ofNat <$> genAddress),
    (10, .ofInt <$> genAddress),
    (10, .ofSyntax <$> genAddress),
  ]

def genMetadatum : Gen Ixon.Metadatum :=
  frequency [
    (10, .info <$> genBinderInfo),
    (10, .link <$> genAddress),
    (10, .hints <$> genReducibilityHints),
    (10, .links <$> genList genAddress),
    --(10, .rules <$> genList genAddress),
    (10, .kvmap <$> genList (Prod.mk <$> genAddress <*> genDataValue)),
  ]

def genMetadata : Gen Ixon.Metadata :=
  .mk <$> genList genMetadatum


partial def genIxon : Gen Ixon.Ixon :=
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
    (10, .defn <$> genDefinition),
    (10, .axio <$> genAxiom),
    (10, .quot <$> genQuotient),
    (10, .cprj <$> genConstructorProj),
    (10, .iprj <$> genInductiveProj),
    (10, .dprj <$> genDefinitionProj),
    (10, .muts <$> genList (.indc <$> genInductive)),
    (10, .muts <$> genList (.defn <$> genDefinition)),
    (10, .muts <$> genList (.recr <$> genRecursor)),
    (10, .prof <$> genProof),
    (10, .eval <$> genEvalClaim),
    (10, .chck <$> genCheckClaim),
    (10, .comm <$> genComm),
    (10, .envn <$> genEnv),
    (10, .meta <$> genMetadata),
  ]

instance : Shrinkable Ixon.Ixon where
  shrink _ := []

instance : SampleableExt Ixon.Ixon := SampleableExt.mkSelfContained genIxon

def ixonSerde (ixon : Ixon.Ixon) : Bool :=
  let bytes := Ixon.ser ixon
  match Ixon.de bytes with
  | .ok ixon' => ixon == ixon'
  | .error _ => false

def Tests.Ixon.suite := [
  check "Ixon serde roundtrips" (∀ ixon : Ixon.Ixon, ixonSerde ixon)
]

