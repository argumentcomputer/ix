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

def ixTestCases : List AiurTestCase := [
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
  mkIxonSerdeTestCase (.nstr default default),
  mkIxonSerdeTestCase (.nnum default default),
  mkIxonSerdeTestCase .uzero,
  mkIxonSerdeTestCase (.usucc default),
  mkIxonSerdeTestCase (.umax default default),
  mkIxonSerdeTestCase (.uimax default default),
  mkIxonSerdeTestCase (.uvar 42),
  mkIxonSerdeTestCase (.evar 42),
  mkIxonSerdeTestCase (.eref default [default, default, default]),
  mkIxonSerdeTestCase (.erec 42 [default, default, default]),
  mkIxonSerdeTestCase (.eprj default 42 default),
  mkIxonSerdeTestCase (.esort default),
  mkIxonSerdeTestCase (.estr default),
  mkIxonSerdeTestCase (.enat default),
  mkIxonSerdeTestCase (.eapp default default),
  mkIxonSerdeTestCase (.elam default default),
  mkIxonSerdeTestCase (.eall default default),
  mkIxonSerdeTestCase (.elet false default default default),
  mkIxonSerdeTestCase (.elet true default default default),
  mkIxonSerdeTestCase (.defn ⟨.opaque, .safe, 5, default, default⟩),
  mkIxonSerdeTestCase (.axio ⟨true, 5, default⟩),
  mkIxonSerdeTestCase (.quot ⟨.ctor, 5, default⟩),
  mkIxonSerdeTestCase (.cprj ⟨3, 4, default⟩),
  mkIxonSerdeTestCase (.rprj ⟨3, default⟩),
  mkIxonSerdeTestCase (.iprj ⟨3, default⟩),
  mkIxonSerdeTestCase (.dprj ⟨3, default⟩),
  mkIxonSerdeTestCase (.eval ⟨default, default, default, default⟩),
  mkIxonSerdeTestCase (.chck ⟨default, default, default⟩),
  mkIxonSerdeTestCase (.comm ⟨default, default⟩),
  mkIxonSerdeTestCase (.blob ⟨#[0, 1, 2, 3]⟩),
  mkIxonSerdeTestCase (.blob ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]⟩),
]

def Tests.IxVM.suite := [
  mkAiurTests IxVM.ixVM ixTestCases
]
