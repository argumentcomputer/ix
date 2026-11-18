import MultiStark.BN.Program
import Aiur.Artifact

namespace KzgXofFixture
open Aiur

def client : Modules.Program Nat := aiur⟦
module KzgXofTest {
  fn read(length: Field, offset: Field) -> Bytes::Stream {
    match length {
      0 => &(Lists::Node::Nil),
      _ => {
        let byte = UInt8::from_field(hint::<Field>("kzg.test.byte", offset));
        &(Lists::Node::Cons(byte, read(length - 1, offset + 1)))
      },
    }
  }
  inline fn byte(offset: Field) -> UInt8::U8 {
    UInt8::from_field(hint::<Field>("kzg.test.byte", offset))
  }
  fn read_words(count: Field, offset: Field) -> KzgIO::Words {
    match count {
      0 => &(Lists::Node::Nil),
      _ => &(Lists::Node::Cons(UInt32::from_bytes([byte(offset), byte(offset + 1), byte(offset + 2), byte(offset + 3)]),
        read_words(count - 1, offset + 4))),
    }
  }
  -- The input as a verifier channel holds it: `length mod 4` pending bytes,
  -- then whole words. Returns the 96 XOF bytes and the BLAKE3 digest.
  fn run_input(length: Field) -> [Field; 32] {
    let (words, lead) = KzgIO::split4(length);
    let zero = UInt8::BYTE_0;
    let input = match lead {
      0 => (read_words(words, 0), 0),
      1 => (&(Lists::Node::Cons(UInt32::from_bytes([zero, zero, zero, byte(0)]), read_words(words, 1))), 3),
      2 => (&(Lists::Node::Cons(UInt32::from_bytes([zero, zero, byte(0), byte(1)]), read_words(words, 2))), 2),
      3 => (&(Lists::Node::Cons(UInt32::from_bytes([zero, byte(0), byte(1), byte(2)]), read_words(words, 3))), 1),
    };
    let (body, tail_length, tail) = KzgBlake3::aligned(input);
    let (wide, state) = KzgBlake3::xof96_words(body, length, tail_length, tail);
    let digest = KzgBlake3::hash_input(input, length);
    [Blake3::pack_word(wide[0]), Blake3::pack_word(wide[1]), Blake3::pack_word(wide[2]), Blake3::pack_word(wide[3]), Blake3::pack_word(wide[4]), Blake3::pack_word(wide[5]), Blake3::pack_word(wide[6]), Blake3::pack_word(wide[7]), Blake3::pack_word(wide[8]), Blake3::pack_word(wide[9]), Blake3::pack_word(wide[10]), Blake3::pack_word(wide[11]), Blake3::pack_word(wide[12]), Blake3::pack_word(wide[13]), Blake3::pack_word(wide[14]), Blake3::pack_word(wide[15]), Blake3::pack_word(state[0]), Blake3::pack_word(state[1]), Blake3::pack_word(state[2]), Blake3::pack_word(state[3]), Blake3::pack_word(state[4]), Blake3::pack_word(state[5]), Blake3::pack_word(state[6]), Blake3::pack_word(state[7]),
     Blake3::pack_word(digest[0]), Blake3::pack_word(digest[1]), Blake3::pack_word(digest[2]), Blake3::pack_word(digest[3]), Blake3::pack_word(digest[4]), Blake3::pack_word(digest[5]), Blake3::pack_word(digest[6]), Blake3::pack_word(digest[7])]
  }
  fn run(length: Field) -> [Field; 24] {
    let (wide, state) = KzgBlake3::xof96(read(length, 0));
    [Blake3::pack_word(wide[0]), Blake3::pack_word(wide[1]), Blake3::pack_word(wide[2]), Blake3::pack_word(wide[3]), Blake3::pack_word(wide[4]), Blake3::pack_word(wide[5]), Blake3::pack_word(wide[6]), Blake3::pack_word(wide[7]), Blake3::pack_word(wide[8]), Blake3::pack_word(wide[9]), Blake3::pack_word(wide[10]), Blake3::pack_word(wide[11]), Blake3::pack_word(wide[12]), Blake3::pack_word(wide[13]), Blake3::pack_word(wide[14]), Blake3::pack_word(wide[15]), Blake3::pack_word(state[0]), Blake3::pack_word(state[1]), Blake3::pack_word(state[2]), Blake3::pack_word(state[3]), Blake3::pack_word(state[4]), Blake3::pack_word(state[5]), Blake3::pack_word(state[6]), Blake3::pack_word(state[7])]
  }
}
⟧

def main (args : List String) : IO Unit := do
  let program := MultiStark.BN.program.append (client.toField MultiStark.BN.F)
  let prepared ← IO.ofExcept (Modules.prepare program ["KzgXofTest::run", "KzgXofTest::run_input"])
  let exported ← IO.ofExcept prepared.exportExecution
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val)
  let path := args.headD "crates/aiur/tests/fixtures/kzg-xof.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do throw (IO.userError "KZG XOF fixture differs from its Lean export")
  else Artifact.write path bytes
  IO.println s!"KZG XOF fixture: {bytes.size} bytes"

end KzgXofFixture

def main : List String → IO Unit := KzgXofFixture.main
