import Aiur.Modules.Frontend

/-! Canonical source-wire grammar for packed-SHPLONK multi-stark keys and
proofs. Circuits, scalars and openings share the column verifier's parser;
a key lists each distinct circuit once with its copy count, and the parsed key
holds every copy, as the native system does.
Packed commitments keep their exact native bytes, which the transcript absorbs,
alongside the matrix shapes (height, width, declared next-row class) and pack
points parsed from them.
The fixed section is tag 0 (no fixed matrices), tag 1 (one committed matrix
per circuit with fixed columns) or tag 2: the commitment followed by one u32
per circuit, its fixed slot plus one (zero without fixed columns), for a
system in which circuits share committed fixed matrices
(`System::new_shared`). The slot list is checked against the circuits by
`KzgPackedShape::frames`.
`chain_policy` reads the two-key policy (`IXAUKG01`) of a chain whose
CompressGL stage is packed, authorizing the GL key at stage one and the
narrow key after it. -/
namespace MultiStark.Source

def kzgPackedDeserialize : Aiur.Modules.Program Nat := aiur⟦
module KzgPackedDeserialize {
  type Values=Lists::List<Field>;
  type Shapes=Lists::List<(Field,Field,Field)>;
  type Points=Lists::List<BN254G1::Point>;
  type Openings=KzgDeserialize::Openings;
  enum Commitment { Mk(KzgIO::Input,Shapes,Points) }
  enum Fixed { None, Some(Commitment), Shared(Commitment,Values) }
  enum Key { Mk(KzgIO::Input,Field,Field,BN254G1::Point,KzgIO::Input,Lists::List<KzgDeserialize::Circuit>,Fixed) }
  enum Witness { Mk(BN254G1::Point,[UInt8::U8;32]) }
  enum Proof { Mk(Values,Values,Commitment,Commitment,Commitment,Values,Openings,Openings,Openings,
    KzgDeserialize::FixedOpen,Values,Witness,Witness) }

  fn shapes(input:KzgIO::Input,count:Field)->(Shapes,KzgIO::Input) {
    match count {
      0=>(&(Lists::Node::Nil),input),
      _=>{
        let (log,input)=KzgIO::tag(input); let (width,input)=KzgIO::u32(input);
        let (next,input)=KzgIO::tag(input);
        assert_eq!(UInt32::less_than_fields(log,29),1,"packed matrix domain");
        assert_eq!(Fields::is_zero(width),0,"empty packed matrix");
        assert_eq!(next*(next-1),0,"packed matrix class");
        let (tail,input)=shapes(input,count-1);
        (&(Lists::Node::Cons((log,width,next),tail)),input)
      },
    }
  }

  fn commitment(bytes:KzgIO::Input)->Commitment {
    let input=KzgIO::magic(bytes,[73,88,80,83,72,67,48,50]);
    let (count,input)=KzgIO::u32(input); let (shapes,input)=shapes(input,count);
    let (count,input)=KzgIO::u32(input); let (points,input)=KzgDeserialize::points(input,count);
    KzgIO::finish(input); Commitment::Mk(bytes,shapes,points)
  }

  fn copies_of(circuit:KzgDeserialize::Circuit,copies:Field,tail:Lists::List<KzgDeserialize::Circuit>)
      ->Lists::List<KzgDeserialize::Circuit> {
    match copies {
      0=>tail,
      _=>&(Lists::Node::Cons(circuit,copies_of(circuit,copies-1,tail))),
    }
  }

  fn circuits(input:KzgIO::Input,count:Field,budget:Field)->(Lists::List<KzgDeserialize::Circuit>,KzgIO::Input) {
    match count {
      0=>(&(Lists::Node::Nil),input),
      _=>{
        let (copies,input)=KzgIO::u32(input);
        assert_eq!(Fields::is_zero(copies),0,"packed circuit without copies");
        let (one,input)=KzgDeserialize::circuits(input,1,budget);
        let Lists::Node::Cons(circuit,_rest)=*one;
        let (tail,input)=circuits(input,count-1,budget);
        (copies_of(circuit,copies,tail),input)
      },
    }
  }

  fn words(input:KzgIO::Input,count:Field)->(Values,KzgIO::Input) {
    match count {
      0=>(&(Lists::Node::Nil),input),
      _=>{let (head,input)=KzgIO::u32(input);let (tail,input)=words(input,count-1);
        (&(Lists::Node::Cons(head,tail)),input)},
    }
  }

  -- The key's fixed section, through the end of the key.
  fn fixed(input:KzgIO::Input,circuits:Field)->Fixed {
    let (tag,input)=KzgIO::tag(input);
    match tag {
      0=>{KzgIO::finish(input);Fixed::None},
      1=>{let (fixed,input)=KzgIO::blob(input);KzgIO::finish(input);Fixed::Some(commitment(fixed))},
      2=>{
        let (fixed,input)=KzgIO::blob(input);
        let (count,input)=KzgIO::u32(input);
        assert_eq!(count,circuits,"packed fixed slot count");
        let (slots,input)=words(input,count);KzgIO::finish(input);
        Fixed::Shared(commitment(fixed),slots)
      },
    }
  }

  fn witness(input:KzgIO::Input)->(Witness,KzgIO::Input) {
    let (bytes,input)=KzgIO::read32(input);
    (Witness::Mk(BN254G1::from_bytes(Blake3::address_to_fields(bytes)),bytes),input)
  }

  fn key(input:KzgIO::Input)->Key {
    let input=KzgIO::magic(input,[73,88,65,85,83,75,48,50]);
    let (seed,input)=KzgIO::blob(input);
    let (max_log,input)=KzgIO::u32(input);
    assert_eq!(UInt32::less_than_fields(max_log,29),1,"packed trace cap exceeds Fr domain");
    assert_eq!(UInt32::less_than_fields(0,max_log),1,"packed trace cap below two rows");
    let (budget,input)=KzgIO::u32(input); KzgDeserialize::supported_power(budget,1,28);
    let (generator,input)=KzgIO::point(input);
    let (anchors,input)=KzgIO::read_bytes(input,128);
    let (count,input)=KzgIO::u32(input);
    assert_eq!(Fields::is_zero(count),0,"empty packed system");
    let (circuits,input)=circuits(input,count,budget);
    Key::Mk(seed,max_log,budget,generator,anchors,circuits,fixed(input,Lists::length(circuits)))
  }

  inline fn chain_policy(input:KzgIO::Input)->KzgDeserialize::Policy {
    let input=KzgIO::magic(input,[73,88,65,85,75,71,48,49]);
    let (anchors,input)=KzgIO::read_bytes(input,128);
    let (gl_digest,input)=KzgIO::digest(input); let (gl_entry,input)=KzgIO::u32(input);
    let (bn_digest,input)=KzgIO::digest(input); let (bn_entry,input)=KzgIO::u32(input);
    KzgIO::finish(input); KzgDeserialize::Policy::Mk(anchors,gl_digest,gl_entry,bn_digest,bn_entry)
  }

  fn proof_tail(input:KzgIO::Input,active:Values,logs:Values,main:Commitment,stage2:Commitment,quotient:Commitment,
      accumulators:Values,mo:Openings,so:Openings,qo:Openings,fo:KzgDeserialize::FixedOpen)->Proof {
    let (count,input)=KzgIO::u32(input);let (extras,input)=KzgDeserialize::scalars(input,count);
    let (w1,input)=witness(input);let (w2,input)=witness(input);KzgIO::finish(input);
    Proof::Mk(active,logs,main,stage2,quotient,accumulators,mo,so,qo,fo,extras,w1,w2)
  }

  fn proof(input:KzgIO::Input)->Proof {
    let input=KzgIO::magic(input,[73,88,65,85,83,80,48,49]);
    let (count,input)=KzgIO::u32(input);let (active,input)=KzgDeserialize::tags(input,count);
    let (count,input)=KzgIO::u32(input);let (logs,input)=KzgDeserialize::tags(input,count);
    let (main,input)=KzgIO::blob(input);let main=commitment(main);
    let (stage2,input)=KzgIO::blob(input);let stage2=commitment(stage2);
    let (quotient,input)=KzgIO::blob(input);let quotient=commitment(quotient);
    let (count,input)=KzgIO::u32(input);let (accumulators,input)=KzgDeserialize::scalars(input,count);
    let (mo,input)=KzgDeserialize::openings(input);let (so,input)=KzgDeserialize::openings(input);
    let (qo,input)=KzgDeserialize::openings(input);let (tag,input)=KzgIO::tag(input);
    match tag {
      0=>proof_tail(input,active,logs,main,stage2,quotient,accumulators,mo,so,qo,KzgDeserialize::FixedOpen::None),
      1=>{let (fo,input)=KzgDeserialize::openings(input);
        proof_tail(input,active,logs,main,stage2,quotient,accumulators,mo,so,qo,KzgDeserialize::FixedOpen::Some(fo))},
    }
  }
}
⟧

end MultiStark.Source
