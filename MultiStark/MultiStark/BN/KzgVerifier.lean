import Aiur.Modules.Frontend

/-! Generic native-Fr multi-stark verification with a deferred KZG opening
pairing. The complete key and claims bytes are authenticated independently;
terminal verification must discharge the returned pairing operands. -/
namespace MultiStark.Source

def kzgVerifier : Aiur.Modules.Program Nat := aiur⟦
module KzgVerifier {
  fn observe_shape(transcript: KzgTranscript::Transcript, circuits: Lists::List<KzgDeserialize::Circuit>) -> KzgTranscript::Transcript {
    match *circuits {
      Lists::Node::Nil=>transcript,
      Lists::Node::Cons(circuit,rest)=>{
        let KzgDeserialize::Circuit::Mk(shape,_nodes,_roots,_lookups,_mn,_fn)=circuit;
        let transcript=KzgTranscript::observe_field(transcript,shape[0]);
        let transcript=KzgTranscript::observe_field(transcript,shape[1]);
        let transcript=KzgTranscript::observe_field(transcript,shape[2]);
        let transcript=KzgTranscript::observe_field(transcript,shape[3]);
        let transcript=KzgTranscript::observe_field(transcript,shape[4]);
        let transcript=KzgTranscript::observe_field(transcript,shape[5]);
        let transcript=KzgTranscript::observe_field(transcript,shape[6]);
        observe_shape(transcript,rest)
      },
    }
  }

  fn verify(key: KzgDeserialize::Key, proof: KzgDeserialize::Proof, claims: Lists::List<Lists::List<Field>>) -> (BN254G1::Point,BN254G1::Point) {
    let frames=KzgShape::frames(key,proof);
    let KzgDeserialize::Key::Mk(seed,_max_log,_budget,generator,_anchors,circuits,fixed)=key;
    let KzgDeserialize::Proof::Mk(active,logs,main,stage2,quotient,accumulators,witnesses,_mo,_so,_qo,_fo)=proof;
    let transcript=KzgTranscript::observe_field(KzgTranscript::start(seed),Lists::length(circuits));
    let transcript=observe_shape(transcript,circuits);
    let transcript=KzgTranscript::observe_fields(transcript,active);
    let transcript=match fixed {KzgDeserialize::Fixed::None=>transcript,
      KzgDeserialize::Fixed::Some(fixed)=>KzgTranscript::observe_commitment(transcript,fixed)};
    let transcript=KzgTranscript::observe_commitment(transcript,main);
    let transcript=KzgTranscript::observe_fields(transcript,logs);
    let transcript=KzgTranscript::observe_claims(transcript,claims);
    let (beta,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,beta);
    let (gamma,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,gamma);
    let initial=KzgAlgebra::claims_accumulator(claims,beta,gamma);
    let transcript=KzgTranscript::observe_commitment(transcript,stage2);
    let transcript=KzgTranscript::observe_fields(transcript,accumulators);
    let (alpha,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_commitment(transcript,quotient);
    let (zeta,transcript)=KzgTranscript::sample(transcript);
    assert_eq!(Fields::is_zero(zeta),0,"zero KZG evaluation challenge");
    KzgAlgebra::verify_frames(frames,beta,gamma,alpha,zeta,initial);
    KzgPcs::reduce(transcript,frames,fixed,witnesses,zeta,generator)
  }

  fn verify_deferred(expected_key: KzgIO::Digest, expected_claims: KzgIO::Digest) -> [Field;4] {
    KzgIO::digest_bytes(expected_key); KzgIO::digest_bytes(expected_claims);
    let key_bytes=KzgIO::channel(1); let claims_bytes=KzgIO::channel(2); let proof_bytes=KzgIO::channel(3);
    assert_eq!(Blake3::pack_digest(Blake3::hash(key_bytes)),expected_key,"KZG key digest mismatch");
    assert_eq!(Blake3::pack_digest(Blake3::hash(claims_bytes)),expected_claims,"KZG claims digest mismatch");
    let (a,b)=verify(KzgDeserialize::key(key_bytes),KzgDeserialize::proof(proof_bytes),KzgDeserialize::claims(claims_bytes));
    KzgAccumulator::pack(a,b)
  }
}
⟧

end MultiStark.Source
