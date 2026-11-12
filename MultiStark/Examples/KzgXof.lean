import MultiStark.BN.KzgBlake3
import Aiur.Library.Blake3.BN254
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
  fn run(length: Field) -> [Field; 24] {
    let (wide, state) = KzgBlake3::xof96(read(length, 0));
    [Blake3::pack_word(wide[0]), Blake3::pack_word(wide[1]), Blake3::pack_word(wide[2]), Blake3::pack_word(wide[3]), Blake3::pack_word(wide[4]), Blake3::pack_word(wide[5]), Blake3::pack_word(wide[6]), Blake3::pack_word(wide[7]), Blake3::pack_word(wide[8]), Blake3::pack_word(wide[9]), Blake3::pack_word(wide[10]), Blake3::pack_word(wide[11]), Blake3::pack_word(wide[12]), Blake3::pack_word(wide[13]), Blake3::pack_word(wide[14]), Blake3::pack_word(wide[15]), Blake3::pack_word(state[0]), Blake3::pack_word(state[1]), Blake3::pack_word(state[2]), Blake3::pack_word(state[3]), Blake3::pack_word(state[4]), Blake3::pack_word(state[5]), Blake3::pack_word(state[6]), Blake3::pack_word(state[7])]
  }
}
⟧

def main (args : List String) : IO Unit := do
  let program := Library.Blake3.BN254.program.append (MultiStark.Source.kzgBlake3.toField Library.Field.BN254.F)
    |>.append (client.toField Library.Field.BN254.F)
  let prepared ← IO.ofExcept (Modules.prepare program ["KzgXofTest::run"])
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
