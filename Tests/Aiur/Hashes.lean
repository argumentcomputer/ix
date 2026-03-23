module

public import Tests.Aiur.Common
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.Sha256
public import Tests.Sha256
public import Blake3.Rust

def mkBlake3HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.Rust.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  { functionName := `blake3_test, label := s!"blake3 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer }

def mkSha256HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Sha256.hash ⟨inputBytes⟩ |>.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  { functionName := `sha256_test, label := s!"sha256 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer }

public def blake3TestCases : List AiurTestCase := [
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

public def sha256TestCases : List AiurTestCase := [
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
