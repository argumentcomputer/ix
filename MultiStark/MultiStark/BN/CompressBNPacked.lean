import Aiur.Modules.Frontend

/-! The accumulator fold of a stage that verifies a packed-SHPLONK proof. The
weight is squeezed from the packed verifier's final transcript, which has
absorbed the whole predecessor proof and its claims, after a domain tag and
the policy, statement, stage, predecessor key digest and all four accumulator
points, so the predecessor proof bytes are not hashed separately.

The fixed-key narrow stage (`CompressNarrowFixed`) and the narrow terminal
(`CompressFinalNarrow`) fold with `fold`. -/
namespace MultiStark.Source

def compressBNPacked : Aiur.Modules.Program Nat := aiur⟦
module CompressBNPacked {
  type Digest=KzgIO::Digest;
  type Values=Lists::List<Field>;

  inline fn fold_domain(tail: Bytes::Stream) -> Bytes::Stream {
    let tail=&(Lists::Node::Cons(UInt8::BYTE_0,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_49,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_118,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_116,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_105,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_114,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_99,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_115,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_110,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_97,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_114,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_116,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_45,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_100,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_108,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_111,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_102,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_103,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_122,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_114,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_117,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_105,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_97,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_120,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_105,tail));
    tail
  }

  -- The fold weight: the challenge squeezed from the predecessor verifier's
  -- final transcript after absorbing the fold domain, policy, statement,
  -- little-endian stage, predecessor key digest and the four points.
  inline fn fold_weight(transcript: KzgTranscript::Transcript, policy: Digest, statement: Digest, stage: Field,
      key_digest: Digest, previous_a: BN254G1::Point, previous_b: BN254G1::Point, current_a: BN254G1::Point,
      current_b: BN254G1::Point) -> Field {
    let points=&(Lists::Node::Cons(previous_a,&(Lists::Node::Cons(previous_b,
      &(Lists::Node::Cons(current_a,&(Lists::Node::Cons(current_b,&(Lists::Node::Nil)))))))));
    let tail=KzgIO::fields_to_bytes(BN254G1::point_list_bytes(points));
    let tail=CompressBN::digest_onto(key_digest,tail);
    let tail=KzgIO::prepend4(UInt32::to_bytes(KzgIO::digest_word(stage)),tail);
    let tail=CompressBN::digest_onto(policy,CompressBN::digest_onto(statement,tail));
    let (weight,_transcript)=KzgTranscript::sample(KzgTranscript::observe_bytes(transcript,fold_domain(tail)));
    assert_eq!(Fields::is_zero(weight),0,"zero compression fold challenge");
    weight
  }

  -- `current + fold_weight(...)·previous`.
  fn fold(transcript: KzgTranscript::Transcript, policy: Digest, statement: Digest, stage: Field, key_digest: Digest,
      previous_a: BN254G1::Point, previous_b: BN254G1::Point, current_a: BN254G1::Point, current_b: BN254G1::Point)
      -> (BN254G1::Point,BN254G1::Point) {
    let weight=fold_weight(transcript,policy,statement,stage,key_digest,previous_a,previous_b,current_a,current_b);
    let a=KzgMsm::msm(&(Lists::Node::Cons((previous_a,weight),&(Lists::Node::Nil))));
    let b=KzgMsm::msm(&(Lists::Node::Cons((previous_b,weight),&(Lists::Node::Nil))));
    (BN254G1::add(current_a,a),BN254G1::add(current_b,b))
  }
}
⟧

end MultiStark.Source
