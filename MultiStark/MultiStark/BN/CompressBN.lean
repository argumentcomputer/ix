import Aiur.Modules.Frontend

/-! Version-one recursive KZG compression. The public call has exactly 23
fields: CALL and physical entry ID, policy digest (8 u32 words), positive u32
stage, original statement digest (8 u32 words), and four u128 accumulator
chunks. Stage one accepts the authorized 18-word CompressGL call; later stages
accept this exact schema with the same policy and statement and stage minus one.
The final verifier must pin the policy digest and this program's verifying key. -/
namespace MultiStark.Source

def compressBN : Aiur.Modules.Program Nat := aiur⟦
module CompressBN {
  type Digest=KzgIO::Digest;
  type Values=Lists::List<Field>;

  fn take8(values: Values) -> ([Field;8],Values) {
    let Lists::Node::Cons(v0,values)=*values;
    let Lists::Node::Cons(v1,values)=*values;
    let Lists::Node::Cons(v2,values)=*values;
    let Lists::Node::Cons(v3,values)=*values;
    let Lists::Node::Cons(v4,values)=*values;
    let Lists::Node::Cons(v5,values)=*values;
    let Lists::Node::Cons(v6,values)=*values;
    let Lists::Node::Cons(v7,values)=*values;
    ([v0, v1, v2, v3, v4, v5, v6, v7],values)
  }

  fn previous(policy: KzgDeserialize::Policy, policy_digest: Digest, stage: Field, statement: Digest,
      claims: Lists::List<Values>) -> (BN254G1::Point,BN254G1::Point) {
    let KzgDeserialize::Policy::Mk(_anchors,_gl_key,gl_entry,_bn_key,bn_entry)=policy;
    let Lists::Node::Cons(claim,rest)=*claims; let Lists::Node::Nil=*rest;
    let Lists::Node::Cons(tag,claim)=*claim;
    let Lists::Node::Cons(entry,claim)=*claim;
    assert_eq!(tag,1,"compression predecessor CALL namespace");
    match stage {
      1=>{
        assert_eq!(entry,gl_entry,"compression GL entry");
        let (reserved,claim)=take8(claim); assert_eq!(reserved,[0;8],"compression GL reserved words");
        let (claimed_statement,claim)=take8(claim); assert_eq!(claimed_statement,statement,"compression GL statement");
        let Lists::Node::Nil=*claim;
        (BN254G1::INFINITY,BN254G1::INFINITY)
      },
      _=>{
        assert_eq!(entry,bn_entry,"compression BN entry");
        let (claimed_policy,claim)=take8(claim); assert_eq!(claimed_policy,policy_digest,"compression predecessor policy");
        let Lists::Node::Cons(previous_stage,claim)=*claim;
        assert_eq!(previous_stage,stage-1,"compression predecessor stage");
        let (claimed_statement,claim)=take8(claim); assert_eq!(claimed_statement,statement,"compression predecessor statement");
        let Lists::Node::Cons(a0,claim)=*claim; let Lists::Node::Cons(a1,claim)=*claim;
        let Lists::Node::Cons(b0,claim)=*claim; let Lists::Node::Cons(b1,claim)=*claim;
        let Lists::Node::Nil=*claim;
        KzgAccumulator::unpack([a0,a1,b0,b1])
      },
    }
  }

  inline fn point_bytes(point: BN254G1::Point, tail: Bytes::Stream) -> Bytes::Stream {
    KzgIO::prepend32(Blake3::address_from_fields(BN254G1::to_bytes(point)),tail)
  }

  inline fn domain(tail: Bytes::Stream) -> Bytes::Stream {
    let tail=&(Lists::Node::Cons(UInt8::BYTE_0,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_49,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_118,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
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

  fn fold(policy: Digest, statement: Digest, stage: Field, key_digest: Digest, proof_digest: Digest,
      previous_a: BN254G1::Point, previous_b: BN254G1::Point, current_a: BN254G1::Point, current_b: BN254G1::Point)
      -> (BN254G1::Point,BN254G1::Point) {
    let tail=point_bytes(previous_a,point_bytes(previous_b,point_bytes(current_a,point_bytes(current_b,&(Lists::Node::Nil)))));
    let tail=KzgIO::prepend32(KzgIO::digest_bytes(key_digest),KzgIO::prepend32(KzgIO::digest_bytes(proof_digest),tail));
    let tail=KzgIO::prepend4(UInt32::to_bytes(KzgIO::digest_word(stage)),tail);
    let tail=KzgIO::prepend32(KzgIO::digest_bytes(policy),KzgIO::prepend32(KzgIO::digest_bytes(statement),tail));
    let weight=KzgTranscript::derive(domain(tail));
    assert_eq!(Fields::is_zero(weight),0,"zero compression fold challenge");
    let a=KzgMsm::msm(&(Lists::Node::Cons((previous_a,weight),&(Lists::Node::Nil))));
    let b=KzgMsm::msm(&(Lists::Node::Cons((previous_b,weight),&(Lists::Node::Nil))));
    (BN254G1::add(current_a,a),BN254G1::add(current_b,b))
  }

  fn step_v1(policy_digest: Digest, stage: Field, statement: Digest) -> ([Field;4],Bytes::Stream) {
    KzgIO::digest_bytes(policy_digest); KzgIO::digest_bytes(statement);
    KzgIO::digest_word(stage);
    assert_eq!(UInt32::less_than_fields(0,stage),1,"compression stage must be positive");
    let policy_bytes=KzgIO::channel(4);
    assert_eq!(Blake3::pack_digest(Blake3::hash(policy_bytes)),policy_digest,"compression policy digest mismatch");
    let policy=KzgDeserialize::policy(policy_bytes);
    let KzgDeserialize::Policy::Mk(anchors,gl_key,_gl_entry,bn_key,_bn_entry)=policy;
    let key_bytes=KzgIO::channel(1);
    let key_digest=Blake3::pack_digest(Blake3::hash(key_bytes));
    let expected=match stage {1=>gl_key,_=>bn_key};
    assert_eq!(key_digest,expected,"unauthorized compression predecessor key");
    let key=KzgDeserialize::key(key_bytes);
    let KzgDeserialize::Key::Mk(_seed,_max_log,_budget,_generator,key_anchors,_circuits,_fixed)=key;
    KzgIO::equal_bytes(anchors,key_anchors);
    let claims=KzgDeserialize::claims(KzgIO::channel(2));
    let (previous_a,previous_b)=previous(policy,policy_digest,stage,statement,claims);
    let proof_bytes=KzgIO::channel(3);
    let proof_digest=Blake3::pack_digest(Blake3::hash(proof_bytes));
    let (current_a,current_b)=KzgVerifier::verify(key,KzgDeserialize::proof(proof_bytes),claims);
    let (a,b)=fold(policy_digest,statement,stage,key_digest,proof_digest,previous_a,previous_b,current_a,current_b);
    (KzgAccumulator::pack(a,b),anchors)
  }

  fn compress_v1(policy_digest: Digest, stage: Field, statement: Digest) -> [Field;4] {
    let (result,_anchors)=step_v1(policy_digest,stage,statement);
    result
  }
}
⟧

end MultiStark.Source
