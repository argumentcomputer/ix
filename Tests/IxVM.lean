import Tests.Common
import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Blake3

def mkBlake3HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  ⟨`blake3_test, #[], output, buffer, buffer⟩

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
]

def Tests.IxVM.suite := [
  mkAiurTests IxVM.ixVM ixTestCases
]
