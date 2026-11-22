import MultiStark.BN.Program

/-! Cross-language fixtures for the KZG source protocol and recursive envelope.
The source verifier emits a deferred accumulator; tests discharge it separately
and prove its computation through the generic Aiur KZG adapter. -/
namespace KzgSourceFixture
open Aiur

def client : Modules.Program Nat := aiur⟦
module KzgTest {
  fn read_scalar() -> Field {
    let (value,rest)=KzgIO::scalar(KzgIO::channel(1)); KzgIO::finish(rest); value
  }
  fn scalar_bytes(value: Field) -> [Field;32] { Blake3::address_to_fields(KzgIO::scalar_bytes(value)) }
  fn transcript(a: Field,b: Field) -> [Field;4] {
    let transcript=KzgTranscript::start(KzgIO::channel(1));
    let transcript=KzgTranscript::observe_field(KzgTranscript::observe_field(transcript,a),b);
    let (beta,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,beta);
    let (gamma,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,gamma);
    let g=BN254G1::from_raw([1,0,0,0,2,0,0,0,0]);
    let first=&(Lists::Node::Cons(g,&(Lists::Node::Cons(BN254G1::neg(g),&(Lists::Node::Nil)))));
    let second=&(Lists::Node::Cons(BN254G1::INFINITY,&(Lists::Node::Nil)));
    let rows=&(Lists::Node::Cons(first,&(Lists::Node::Cons(second,&(Lists::Node::Nil)))));
    let transcript=KzgTranscript::observe_commitment(transcript,rows);
    let transcript=KzgTranscript::observe_u64(KzgTranscript::observe_u64(transcript,0),28);
    let (alpha,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(KzgTranscript::observe_field(KzgTranscript::observe_field(transcript,beta),gamma),alpha);
    let (zeta,_transcript)=KzgTranscript::sample(transcript);
    [beta,gamma,alpha,zeta]
  }
  fn msm2(a:[Field;9],s:Field,b:[Field;9],t:Field)->[Field;9] {
    let terms=&(Lists::Node::Cons((BN254G1::from_raw(a),s),&(Lists::Node::Cons((BN254G1::from_raw(b),t),&(Lists::Node::Nil)))));
    BN254G1::to_raw(KzgMsm::msm(terms))
  }
  fn accumulator(words:[Field;4])->[Field;4] {
    let (a,b)=KzgAccumulator::unpack(words); KzgAccumulator::pack(a,b)
  }
  fn fold(policy:KzgIO::Digest,statement:KzgIO::Digest,stage:Field,key:KzgIO::Digest,proof:KzgIO::Digest,
      previous:[Field;18],current:[Field;18])->[Field;4] {
    let (a,b)=CompressBN::fold(policy,statement,stage,key,proof,
      BN254G1::from_raw(previous[0 .. 9]),BN254G1::from_raw(previous[9 .. 18]),
      BN254G1::from_raw(current[0 .. 9]),BN254G1::from_raw(current[9 .. 18]));
    KzgAccumulator::pack(a,b)
  }
}
⟧

def entries : List String := [MultiStark.BN.verifierEntry, MultiStark.BN.compressionEntry,
  "KzgTest::read_scalar","KzgTest::scalar_bytes","KzgTest::transcript","KzgTest::msm2","KzgTest::accumulator","KzgTest::fold"]

#aiur_check MultiStark.BN.libraries.append MultiStark.BN.source |>.append client

def main (args : List String) : IO Unit := do
  let program := MultiStark.BN.program.append (client.toField MultiStark.BN.F)
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, trace) ← if args.contains "--no-trace" then pure (exported, none) else do
    let (exported, trace) ← Trace.exportPlanParallelWide MultiStark.BN.modulus ZMod.val
      prepared.environment.source prepared.entries exported
    pure (exported, some trace)
  let bytes ← IO.ofExcept (Artifact.packageWide exported MultiStark.BN.modulus ZMod.val trace)
  let path := args.headD "crates/aiur/tests/fixtures/kzg-source.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do throw (IO.userError "KZG source fixture differs from its Lean export")
  else Artifact.write path bytes
  IO.println s!"KZG source fixture: {bytes.size} bytes"

end KzgSourceFixture

def main : List String → IO Unit := KzgSourceFixture.main
