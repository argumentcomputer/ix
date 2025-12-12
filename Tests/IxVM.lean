import Tests.Common
import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Ixon
import Blake3

def mkBlake3HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  ⟨`blake3_test, #[], output, buffer, buffer⟩

def mkIxonSerdeTestCase (ixon : Ixon.Ixon) : AiurTestCase :=
  let bytes := Ixon.ser ixon
  let size := bytes.size
  let ⟨⟨hash⟩, _⟩ := Blake3.hash bytes
  let hashG := hash.map .ofUInt8
  let buffer := ⟨bytes.data.map .ofUInt8, .ofList [(hashG, ⟨0, size⟩)]⟩
  ⟨`ixon_blake3_test, hashG, #[], buffer, buffer⟩

def ixTestCases : List AiurTestCase :=
  let addr1 := Address.mk ⟨.replicate 32 1⟩
  let addr2 := Address.mk ⟨.replicate 32 2⟩
  let addr3 := Address.mk ⟨.replicate 32 3⟩
  let addr4 := Address.mk ⟨.replicate 32 4⟩
  [
    .noIO `relaxed_u64_succ #[0, 0, 0, 0, 0, 0, 0, 0] #[1, 0, 0, 0, 0, 0, 0, 0],
    .noIO `relaxed_u64_succ #[255, 0, 0, 0, 0, 0, 0, 0] #[0, 1, 0, 0, 0, 0, 0, 0],
    .noIO `relaxed_u64_succ #[255, 255, 0, 0, 0, 0, 0, 0] #[0, 0, 1, 0, 0, 0, 0, 0],
    .noIO `relaxed_u64_succ #[255, 255, 255, 0, 0, 0, 0, 0] #[0, 0, 0, 1, 0, 0, 0, 0],
    .noIO `relaxed_u64_succ #[255, 255, 255, 255, 0, 0, 0, 0] #[0, 0, 0, 0, 1, 0, 0, 0],
    .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 0, 0, 0] #[0, 0, 0, 0, 0, 1, 0, 0],
    .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 255, 0, 0] #[0, 0, 0, 0, 0, 0, 1, 0],
    .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 255, 255, 0] #[0, 0, 0, 0, 0, 0, 0, 1],
    .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 255, 255, 255] #[0, 0, 0, 0, 0, 0, 0, 0],
    mkBlake3HashTestCase 0,
    mkBlake3HashTestCase 32,
    mkBlake3HashTestCase 64,
    mkBlake3HashTestCase 96,
    mkBlake3HashTestCase 1024,
    mkBlake3HashTestCase 1056,
    mkBlake3HashTestCase 1088,
    mkBlake3HashTestCase 1120,
    mkBlake3HashTestCase 2048,
    mkBlake3HashTestCase 2080,
    mkBlake3HashTestCase 2112,
    mkBlake3HashTestCase 2144,
    mkBlake3HashTestCase 3072,
    mkBlake3HashTestCase 3104,
    mkBlake3HashTestCase 3136,
    mkBlake3HashTestCase 3168,
    mkIxonSerdeTestCase .nanon,
    mkIxonSerdeTestCase (.nstr addr1 addr2),
    mkIxonSerdeTestCase (.nnum addr1 addr2),
    mkIxonSerdeTestCase .uzero,
    mkIxonSerdeTestCase (.usucc addr1),
    mkIxonSerdeTestCase (.umax addr1 addr2),
    mkIxonSerdeTestCase (.uimax addr1 addr2),
    mkIxonSerdeTestCase (.uvar 42),
    mkIxonSerdeTestCase (.evar 42),
    mkIxonSerdeTestCase (.eref addr1 [addr2, addr3, addr4]),
    mkIxonSerdeTestCase (.erec 42 [addr2, addr3, addr4]),
    mkIxonSerdeTestCase (.eprj addr1 42 addr2),
    mkIxonSerdeTestCase (.esort addr1),
    mkIxonSerdeTestCase (.estr addr1),
    mkIxonSerdeTestCase (.enat addr1),
    mkIxonSerdeTestCase (.eapp addr1 addr2),
    mkIxonSerdeTestCase (.elam addr1 addr2),
    mkIxonSerdeTestCase (.eall addr1 addr2),
    mkIxonSerdeTestCase (.elet false addr1 addr2 addr3),
    mkIxonSerdeTestCase (.elet true addr1 addr2 addr3),
    mkIxonSerdeTestCase (.defn ⟨.opaque, .safe, 5, addr1, addr2⟩),
    mkIxonSerdeTestCase (.recr ⟨false, true, 1, 2, 3, 4, 5, addr1, [⟨6, addr2⟩]⟩),
    mkIxonSerdeTestCase (.axio ⟨true, 5, addr1⟩),
    mkIxonSerdeTestCase (.quot ⟨.ctor, 5, addr1⟩),
    mkIxonSerdeTestCase (.cprj ⟨3, 4, addr1⟩),
    mkIxonSerdeTestCase (.rprj ⟨3, addr1⟩),
    mkIxonSerdeTestCase (.iprj ⟨3, addr1⟩),
    mkIxonSerdeTestCase (.dprj ⟨3, addr1⟩),
    mkIxonSerdeTestCase (.muts [
      .defn ⟨.opaque, .safe, 5, addr1, addr2⟩,
      .indc ⟨false, true, true, 1, 2, 3, 4, addr1,
        [⟨true, 5, 6, 7, 8, addr2⟩]⟩,
      .recr ⟨false, true, 1, 2, 3, 4, 5, addr1, [⟨6, addr2⟩]⟩,
    ]),
    mkIxonSerdeTestCase (.eval ⟨addr1, addr2, addr3, addr4⟩),
    mkIxonSerdeTestCase (.chck ⟨addr1, addr2, addr3⟩),
    mkIxonSerdeTestCase (.comm ⟨addr1, addr2⟩),
    mkIxonSerdeTestCase (.blob ⟨#[0, 1, 2, 3]⟩),
    mkIxonSerdeTestCase (.blob ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]⟩),
  ]

def Tests.IxVM.suite := [
  mkAiurTests IxVM.ixVM ixTestCases
]
