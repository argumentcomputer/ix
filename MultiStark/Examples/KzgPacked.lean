import MultiStark.BN.KzgPackedProgram

namespace MultiStark.Source

/-- Test entry: verifies the packed proof on channels 1–3 (key, claims, proof)
and returns the transcript fold weight and the folded accumulator words for
the given policy, statement, stage, key digest and previous accumulator. -/
def kzgPackedTest : Aiur.Modules.Program Nat := aiur⟦
module KzgPackedTest {
  fn fold(policy:KzgIO::Digest,statement:KzgIO::Digest,stage:Field,key_digest:KzgIO::Digest,previous:[Field;4])->[Field;5] {
    let key=KzgPackedDeserialize::key(KzgIO::channel(1));
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (transcript,current_a,current_b)=KzgPackedVerifier::verify(key,KzgPackedDeserialize::proof(KzgIO::channel(3)),claims);
    let (previous_a,previous_b)=KzgAccumulator::unpack(previous);
    let weight=CompressBNPacked::fold_weight(transcript,policy,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    let (a,b)=CompressBNPacked::fold(transcript,policy,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    let words=KzgAccumulator::pack(a,b);
    [weight,words[0],words[1],words[2],words[3]]
  }
}
⟧

#aiur_check MultiStark.BN.libraries.append MultiStark.BN.source |>.append MultiStark.BN.Packed.source
  |>.append kzgPackedTest

end MultiStark.Source

/-! Exports the packed-SHPLONK Aiur verifier artifact with the fold test
entry. `--check` compares against an existing artifact instead of writing
it. -/
def main (args : List String) : IO Unit := do
  let program := MultiStark.BN.Packed.program.append (MultiStark.Source.kzgPackedTest.toField MultiStark.BN.F)
  let bytes ← MultiStark.BN.Packed.compilePackage (!(args.contains "--no-trace"))
    [MultiStark.BN.Packed.verifierEntry, "KzgPackedTest::fold"] [] program
  let path := (args.filter (!·.startsWith "--")).headD "crates/aiur/tests/fixtures/kzg-packed-shplonk.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless expected.data == bytes.data do throw (IO.userError "packed SHPLONK verifier artifact differs")
  else Aiur.Artifact.write path bytes
  IO.println s!"packed SHPLONK verifier artifact: {bytes.size} bytes"
