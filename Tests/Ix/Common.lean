import LSpec
import Ix.Ixon
import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import Ix.Ixon.Metadata
import LSpec.SlimCheck.Gen
import LSpec
import Blake3
import Tests.Common

open LSpec
open SlimCheck
open SlimCheck.Gen

def genAddress : SlimCheck.Gen Address := 
  pure (Address.mk (Blake3.hash "foobar".toUTF8).val)

-- TODO: Bias char distribution towards ASCII to be more useful
def genChar : SlimCheck.Gen Char :=
  Char.ofNat <$> (choose Nat 0 0xd800)

def genString : SlimCheck.Gen String := do
  let cs ← listOf genChar
  return String.mk cs

def genBool : Gen Bool := choose Bool .false true

-- aggressively reduce size parameter to avoid tree blow-up
def resizeListOf (n: Gen α) : Gen (List α) := resize (· / 2) $ listOf n

def genNat' : Gen Nat := choose Nat 0 10

def genNatUSize : Gen Nat := USize.toNat <$> genUSize

def genList' (gen: Gen α) : Gen (List α) := do
  let n ← genNat'
  List.mapM (fun _ => gen) (List.range n)

def genOption (gen: Gen α) : Gen (Option α) :=
  oneOf #[ pure .none, .some <$> gen]

def genAlphaNum : Gen Char := do
  let n <- oneOf #[choose Nat 48 57, choose Nat 65 90, choose Nat 97 122]
  return Char.ofNat n

def genAlphaNumStr : Gen String := do
  String.mk <$> genList' genAlphaNum

def genNamePart : Gen Ixon.NamePart := 
  oneOf #[ .str <$> genAlphaNumStr, .num <$> genNat']

def genName : Gen Lean.Name := Ixon.nameFromParts <$> genList' genNamePart

def genBinderInfo : Gen Lean.BinderInfo := oneOf
  #[ pure .default
   , pure .instImplicit
   , pure .strictImplicit
   , pure .instImplicit
   ]
