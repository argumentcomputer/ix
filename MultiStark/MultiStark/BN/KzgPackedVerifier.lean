import Aiur.Modules.Frontend

/-! Native-Fr multi-stark verification of packed-SHPLONK proofs. The
transcript replays the native packed configuration exactly: packed commitments
are absorbed as their native bytes. The complete key and claims bytes are
authenticated independently; terminal verification must discharge the
returned pairing operands. `verify` also returns the final transcript, from
which `CompressBNPacked::fold` squeezes the accumulator fold weight. -/
namespace MultiStark.Source

def kzgPackedVerifier : Aiur.Modules.Program Nat := aiur⟦
module KzgPackedVerifier {
  -- The native transcript through the fixed commitment: circuit count and
  -- shapes, each circuit's fixed slot plus one when slots are shared, the
  -- activation flags and the fixed commitment bytes.
  fn observe_key(seed:KzgIO::Input,circuits:Lists::List<KzgDeserialize::Circuit>,active:Lists::List<Field>,
      fixed:KzgPackedDeserialize::Fixed)->KzgTranscript::Transcript {
    let transcript=KzgTranscript::observe_field(KzgTranscript::start(seed),Lists::length(circuits));
    let transcript=KzgVerifier::observe_shape(transcript,circuits);
    match fixed {
      KzgPackedDeserialize::Fixed::None=>KzgTranscript::observe_fields(transcript,active),
      KzgPackedDeserialize::Fixed::Some(fixed)=>KzgTranscript::observe_input(KzgTranscript::observe_fields(transcript,active),
        KzgPcsPacked::commitment_bytes(fixed)),
      KzgPackedDeserialize::Fixed::Shared(fixed,slots)=>KzgTranscript::observe_input(
        KzgTranscript::observe_fields(KzgTranscript::observe_fields(transcript,slots),active),KzgPcsPacked::commitment_bytes(fixed)),
    }
  }

  fn verify(key:KzgPackedDeserialize::Key,proof:KzgPackedDeserialize::Proof,claims:Lists::List<Lists::List<Field>>)
      ->(KzgTranscript::Transcript,BN254G1::Point,BN254G1::Point) {
    let frames=KzgPackedShape::frames(key,proof);
    let KzgPackedDeserialize::Key::Mk(seed,max_log,_budget,generator,_anchors,circuits,fixed)=key;
    let KzgPackedDeserialize::Proof::Mk(active,logs,main,stage2,quotient,accumulators,_mo,_so,_qo,_fo,extras,w1,w2)=proof;
    let transcript=observe_key(seed,circuits,active,fixed);
    let transcript=KzgTranscript::observe_input(transcript,KzgPcsPacked::commitment_bytes(main));
    let transcript=KzgTranscript::observe_fields(transcript,logs);
    let transcript=KzgTranscript::observe_claims(transcript,claims);
    let (beta,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,beta);
    let (gamma,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,gamma);
    let initial=KzgAlgebra::claims_accumulator(claims,beta,gamma);
    let transcript=KzgTranscript::observe_input(transcript,KzgPcsPacked::commitment_bytes(stage2));
    let transcript=KzgTranscript::observe_fields(transcript,accumulators);
    let (alpha,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_input(transcript,KzgPcsPacked::commitment_bytes(quotient));
    let (zeta,transcript)=KzgTranscript::sample(transcript);
    assert_eq!(Fields::is_zero(zeta),0,"zero packed evaluation challenge");
    KzgPackedShape::verify_frames(frames,beta,gamma,alpha,zeta,initial);
    let rounds=KzgPcsPacked::rounds(frames,main,stage2,quotient,fixed);
    KzgPcsPacked::reduce(transcript,rounds,extras,w1,w2,zeta,generator,max_log)
  }

  fn verify_deferred(expected_key:KzgIO::Digest,expected_claims:KzgIO::Digest)->[Field;4] {
    KzgIO::digest_bytes(expected_key);KzgIO::digest_bytes(expected_claims);
    let (key_bytes,key_length)=KzgIO::sized_channel(1);let (claims_bytes,claims_length)=KzgIO::sized_channel(2);
    let proof_bytes=KzgIO::channel(3);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(key_bytes,key_length)),expected_key,"packed key digest mismatch");
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(claims_bytes,claims_length)),expected_claims,"packed claims digest mismatch");
    let (_transcript,a,b)=verify(KzgPackedDeserialize::key(key_bytes),KzgPackedDeserialize::proof(proof_bytes),KzgDeserialize::claims(claims_bytes));
    KzgAccumulator::pack(a,b)
  }
}
⟧

end MultiStark.Source
