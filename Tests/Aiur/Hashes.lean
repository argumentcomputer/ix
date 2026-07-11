module

public import Tests.Aiur.Common
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.IxVM.Sha256
public import Ix.IxVM.Keccak
public import Ix.Keccak
public import Tests.Sha256
public import Blake3.Rust

def mkBlake3HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.Rust.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer : Aiur.IOBuffer :=
    ⟨.ofList [(0, input)], .ofList [((0, #[0]), ⟨0, size⟩)]⟩
    -- channel 0; key fixed as #[0]
  { functionName := `blake3_test, label := s!"blake3 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer
    interpret := false }

def mkSha256HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Sha256.hash ⟨inputBytes⟩ |>.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer : Aiur.IOBuffer :=
    ⟨.ofList [(0, input)], .ofList [((0, #[0]), ⟨0, size⟩)]⟩
    -- channel 0; key fixed as #[0]
  { functionName := `sha256_test, label := s!"sha256 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer
    interpret := false }

def mkKeccakHashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := (Keccak.hash ⟨inputBytes⟩).data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer : Aiur.IOBuffer :=
    ⟨.ofList [(0, input)], .ofList [((0, #[0]), ⟨0, size⟩)]⟩
  { functionName := `keccak256_test, label := s!"keccak256 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer
    interpret := false }

/-- Rate-boundary coverage: 135/136/137 straddle one 136-byte rate block
    (135 pads in-block, 136 forces the extra all-padding block, 137 spills
    into a second block), 271/272/273 the same around two blocks. -/
public def keccakTestCases : List AiurTestCase := [
  mkKeccakHashTestCase 0,
  mkKeccakHashTestCase 1,
  mkKeccakHashTestCase 32,
  mkKeccakHashTestCase 135,
  mkKeccakHashTestCase 136,
  mkKeccakHashTestCase 137,
  mkKeccakHashTestCase 271,
  mkKeccakHashTestCase 272,
  mkKeccakHashTestCase 273,
  mkKeccakHashTestCase 1200,
]

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
