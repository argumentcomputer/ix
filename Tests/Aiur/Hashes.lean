module

public import Tests.Aiur.Common
public import Ix.Aiur.Library.ByteStream
public import Ix.Aiur.Library.Blake3
public import Ix.IxVM.Sha256
public import Tests.Sha256
public import Blake3.Rust

/-!
The size sweeps exercise execution paths (padding, chunk/block
boundaries, tree parents); correctness per size is checked against the
Rust reference output by execution alone. Constraint and lookup coverage
saturates with one small and one multi-chunk proof per hash, so only the
`prove := true` sizes pay for prove+verify.
-/

def mkBlake3HashTestCase (size : Nat) (prove : Bool := false)
    (interp : Bool := false) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.Rust.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer : Aiur.IOBuffer :=
    ⟨.ofList [(0, input)], .ofList [((0, #[0]), ⟨0, size⟩)]⟩
    -- channel 0; key fixed as #[0]
  { functionName := `blake3_test, label := s!"blake3 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer
    interpret := interp, withProof := prove }

def mkSha256HashTestCase (size : Nat) (prove : Bool := false)
    (interp : Bool := false) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Sha256.hash ⟨inputBytes⟩ |>.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer : Aiur.IOBuffer :=
    ⟨.ofList [(0, input)], .ofList [((0, #[0]), ⟨0, size⟩)]⟩
    -- channel 0; key fixed as #[0]
  { functionName := `sha256_test, label := s!"sha256 (size={size})"
    expectedOutput := output, inputIOBuffer := buffer, expectedIOBuffer := buffer
    interpret := interp, withProof := prove }

/-- Resume the ordinary chunk loop after a checked prefix. This exercises
every byte's boundary checks without assuming a multiple-of-four offset. -/
public def blake3BoundaryProgram := ⟦
  fn blake3_resume_seek(input: ByteStream, acc: ByteStream, offset: G) -> (ByteStream, ByteStream) {
    match offset {
      0 => (input, acc),
      _ =>
        let &ListNode.Cons(head, tail) = input;
        blake3_resume_seek(tail, store(ListNode.Cons(head, acc)), offset - 1),
    }
  }
  pub fn blake3_resume_test(offset: G) -> [[U8; 4]; 8] {
    assert_eq!(u32_less_than(offset, 64), 1);
    let (idx, len) = io_get_info(0, [0]);
    let stream = read_checked_byte_stream(0, idx, len);
    let (rest, acc) = blake3_resume_seek(stream, store(ListNode.Nil), offset);
    let IV = [[103u8, 230u8, 9u8, 106u8], [133u8, 174u8, 103u8, 187u8], [114u8, 243u8, 110u8, 60u8], [58u8, 245u8, 79u8, 165u8], [127u8, 82u8, 14u8, 81u8], [140u8, 104u8, 5u8, 155u8], [171u8, 217u8, 131u8, 31u8], [25u8, 205u8, 224u8, 91u8]];
    blake3_compress_layer(blake3_compress_chunks(rest, acc, offset, offset,
      store([0u8; 8]), store(IV), store(LayerNode.Nil)))
  }
⟧

public def blake3ResumeTestCases : List AiurTestCase :=
  ([1, 2, 3, 4, 60, 61, 62, 63] : List Nat).flatMap fun offset =>
    [offset, offset + 1, offset + 2, offset + 3, 64, 65, 1023, 1024, 1025, 2049].map fun size =>
      let tc := mkBlake3HashTestCase size
      { tc with
        functionName := `blake3_resume_test,
        label := s!"blake3 (size={size}, resume={offset})",
        input := #[Aiur.G.ofNat offset] }

public def blake3TestCases : List AiurTestCase := [
  -- prove: empty input (padding-only path) and a two-chunk input with a
  -- parent node (chunk = 1024 bytes). interp: the two smallest sizes give
  -- the interpreter real-program coverage at bounded cost.
  mkBlake3HashTestCase 0 (prove := true) (interp := true),
  mkBlake3HashTestCase 1 (interp := true),
  mkBlake3HashTestCase 2 (interp := true),
  mkBlake3HashTestCase 3 (interp := true),
  mkBlake3HashTestCase 4 (interp := true),
  mkBlake3HashTestCase 32 (interp := true),
  mkBlake3HashTestCase 63,
  mkBlake3HashTestCase 64,
  mkBlake3HashTestCase 65,
  mkBlake3HashTestCase 96,
  mkBlake3HashTestCase 1023,
  mkBlake3HashTestCase 1024,
  mkBlake3HashTestCase 1025,
  mkBlake3HashTestCase 1056,
  mkBlake3HashTestCase 1088 (prove := true),
  mkBlake3HashTestCase 1120,
  mkBlake3HashTestCase 2048,
  mkBlake3HashTestCase 2049,
  mkBlake3HashTestCase 2080,
  mkBlake3HashTestCase 2112,
  mkBlake3HashTestCase 2144,
  mkBlake3HashTestCase 3072,
  mkBlake3HashTestCase 3073,
  mkBlake3HashTestCase 3104,
  mkBlake3HashTestCase 3136,
  mkBlake3HashTestCase 3168,
] ++ blake3ResumeTestCases

public def sha256TestCases : List AiurTestCase := [
  -- prove: empty input (padding-only path) and a two-block input whose
  -- length spills past the first block (block = 64 bytes). interp: the two
  -- smallest sizes give the interpreter real-program coverage at bounded cost.
  mkSha256HashTestCase 0 (prove := true) (interp := true),
  mkSha256HashTestCase 1 (interp := true),
  mkSha256HashTestCase 14,
  mkSha256HashTestCase 16,
  mkSha256HashTestCase 17,
  mkSha256HashTestCase 31,
  mkSha256HashTestCase 32,
  mkSha256HashTestCase 33,
  mkSha256HashTestCase 63,
  mkSha256HashTestCase 64,
  mkSha256HashTestCase 65 (prove := true),
  mkSha256HashTestCase 120,
  mkSha256HashTestCase 1200,
]
