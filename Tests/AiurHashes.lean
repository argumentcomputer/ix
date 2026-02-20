import Tests.Common
import Ix.IxVM.ByteStream
import Ix.IxVM.Blake3
import Ix.IxVM.Sha256
import Blake3

@[extern "rs_sha256"]
opaque rsSha256 : @&ByteArray → ByteArray

def mkBlake3HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  ⟨`blake3_test, #[], output, buffer, buffer⟩

def mkSha256HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := rsSha256 ⟨inputBytes⟩ |>.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  ⟨`sha256_test, #[], output, buffer, buffer⟩

def blake3TestCases : List AiurTestCase := [
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

def sha256TestCases : List AiurTestCase := [
  mkSha256HashTestCase 0,
  mkSha256HashTestCase 1,
  mkSha256HashTestCase 14,
  mkSha256HashTestCase 16,
  mkSha256HashTestCase 17,
  mkSha256HashTestCase 31,
  mkSha256HashTestCase 32,
  mkSha256HashTestCase 33,
  mkSha256HashTestCase 63,
  mkSha256HashTestCase 64,
  mkSha256HashTestCase 65,
  mkSha256HashTestCase 120,
  mkSha256HashTestCase 1200,
]

def Tests.AiurHashes.suite := [
  mkAiurTests (IxVM.byteStream.merge IxVM.blake3) blake3TestCases,
  mkAiurTests (IxVM.byteStream.merge IxVM.sha256) sha256TestCases,
]
