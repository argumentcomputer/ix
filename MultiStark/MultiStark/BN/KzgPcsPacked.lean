import Aiur.Modules.Frontend

/-! Packed-SHPLONK opening reduction (BDFG with one challenge γ across packs).
Packs are reconstructed from authenticated matrix shapes: columns grouped by
increasing height, then declared next-row class (next-row readers first), then
source order, `2^(max_log−log)` columns per pack; no prover-supplied
column-to-pack mapping is accepted. The class only steers grouping. A pack opens every column
at the union of its matrices' points, `{ζ}` or `{ζ, ζω}` (one point at height
one, where `ω = 1`); values a matrix does not request come from the proof's
extra evaluations, in round, pack, point, column order. Every value is
absorbed before `γ`. With `y = z^W` for a pack of `W` columns,
`Z_S(z) = Π_a (y − a)` and `r(z) = Σ_a L_a(y) · Σ_j f_j(a) z^j`, so no root of
`X^W − a` is needed. The output `[A, B]` is a deferred check
`e(A, [1]₂) · e(B, [τ]₂) = 1`, never a completed pairing. It is returned with
the transcript after `[W₂]`, which has then absorbed every value the verifier
read from the proof. -/
namespace MultiStark.Source

def kzgPcsPacked : Aiur.Modules.Program Nat := aiur⟦
module KzgPcsPacked {
  type Values=Lists::List<Field>;
  type Columns=Lists::List<(Field,Field,Field)>;
  type Points=Lists::List<BN254G1::Point>;
  type Pairs=Lists::List<(BN254G1::Point,Field)>;
  enum Group { Mk(Field,Columns,BN254G1::Point) }
  enum Pack { Mk(BN254G1::Point,Field,Field,Values,Values) }
  type Packs=Lists::List<Pack>;
  type Round=&(KzgPackedDeserialize::Commitment,KzgPackedShape::Matrices);
  type Rounds=Lists::List<Round>;

  inline fn open_domain(tail:Bytes::Stream)->Bytes::Stream {
    let tail=&(Lists::Node::Cons(UInt8::BYTE_0,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_49,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_118,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_110,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_101,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_111,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_115,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_99,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_45,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_110,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_111,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_108,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_104,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_115,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_45,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_100,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_101,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_99,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_97,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_103,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_122,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_120,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_105,tail));
    tail
  }

  inline fn batch_domain(tail:Bytes::Stream)->Bytes::Stream {
    let tail=&(Lists::Node::Cons(UInt8::BYTE_0,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_49,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_118,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_110,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_111,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_108,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_104,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_115,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_45,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_100,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_101,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_99,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_97,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_112,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_103,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_122,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_107,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_47,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_120,tail));
    let tail=&(Lists::Node::Cons(UInt8::BYTE_105,tail));
    tail
  }

  fn columns_onto(current:Values,next:Values,has_next:Field,log:Field,tail:Columns)->Columns {
    match *current {
      Lists::Node::Nil=>{let Lists::Node::Nil=*next;tail},
      Lists::Node::Cons(value,rest)=>{
        match has_next {
          0=>&(Lists::Node::Cons((value,0,0),columns_onto(rest,next,0,log,tail))),
          1=>{
            let Lists::Node::Cons(after,next)=*next;
            match log {0=>{assert_eq!(value,after,"conflicting repeated packed evaluation");()},_=>()};
            &(Lists::Node::Cons((value,after,1),columns_onto(rest,next,1,log,tail)))
          },
        }
      },
    }
  }

  fn columns_at(matrices:KzgPackedShape::Matrices,shapes:KzgPackedDeserialize::Shapes,log:Field,next:Field)->Columns {
    match *matrices {
      Lists::Node::Nil=>{let Lists::Node::Nil=*shapes;&(Lists::Node::Nil)},
      Lists::Node::Cons(matrix,rest)=>{
        let KzgPackedShape::Matrix::Mk(found,_width,rows)=matrix;
        let Lists::Node::Cons((_log,_width,kind),shapes)=*shapes;
        let tail=columns_at(rest,shapes,log,next);
        match Fields::is_zero(found-log)*Fields::is_zero(kind-next) {
          0=>tail,
          1=>columns_onto(KzgAlgebra::first_row(rows),KzgAlgebra::next_row(rows),Lists::length(rows)-1,log,tail),
        }
      },
    }
  }

  fn split(columns:Columns,remaining:Field)->(Columns,Columns) {
    match remaining {
      0=>(&(Lists::Node::Nil),columns),
      _=>match *columns {
        Lists::Node::Nil=>(columns,columns),
        Lists::Node::Cons(column,rest)=>{
          let (head,tail)=split(rest,remaining-1);
          (&(Lists::Node::Cons(column,head)),tail)
        },
      },
    }
  }

  fn at_log(columns:Columns,points:Points,log:Field,capacity:Field)->(Lists::List<Group>,Points) {
    match *columns {
      Lists::Node::Nil=>(&(Lists::Node::Nil),points),
      _=>{
        let (head,columns)=split(columns,capacity);
        let Lists::Node::Cons(point,points)=*points;
        let (tail,points)=at_log(columns,points,log,capacity);
        (&(Lists::Node::Cons(Group::Mk(log,head,point),tail)),points)
      },
    }
  }

  fn walk(matrices:KzgPackedShape::Matrices,shapes:KzgPackedDeserialize::Shapes,points:Points,log:Field,max_log:Field)
      ->Lists::List<Group> {
    let capacity=KzgShape::power2(max_log-log);
    let (next,points)=at_log(columns_at(matrices,shapes,log,1),points,log,capacity);
    let (current,points)=at_log(columns_at(matrices,shapes,log,0),points,log,capacity);
    let head=Lists::concat(next,current);
    match Fields::is_zero(log-max_log) {
      1=>{let Lists::Node::Nil=*points;head},
      0=>Lists::concat(head,walk(matrices,shapes,points,log+1,max_log)),
    }
  }

  fn has_next(columns:Columns)->Field {
    match *columns {
      Lists::Node::Nil=>0,
      Lists::Node::Cons((_value,_next,has),rest)=>1-(1-has)*(1-has_next(rest)),
    }
  }

  fn values(columns:Columns,extras:Values,need_next:Field)->(Values,Values,Values) {
    match *columns {
      Lists::Node::Nil=>(&(Lists::Node::Nil),&(Lists::Node::Nil),extras),
      Lists::Node::Cons((value,next,has_next),rest)=>{
        match need_next {
          0=>{
            let (current,_next,extras)=values(rest,extras,0);
            (&(Lists::Node::Cons(value,current)),&(Lists::Node::Nil),extras)
          },
          1=>{
            let (next,extras)=match has_next {
              1=>(next,extras),
              0=>{let Lists::Node::Cons(extra,extras)=*extras;(extra,extras)},
            };
            let (current,after,extras)=values(rest,extras,1);
            (&(Lists::Node::Cons(value,current)),&(Lists::Node::Cons(next,after)),extras)
          },
        }
      },
    }
  }

  fn observe_matrix_queries(transcript:KzgTranscript::Transcript,matrices:KzgPackedShape::Matrices,zeta:Field)->KzgTranscript::Transcript {
    match *matrices {
      Lists::Node::Nil=>transcript,
      Lists::Node::Cons(matrix,rest)=>{
        let KzgPackedShape::Matrix::Mk(log,_width,rows)=matrix;
        let count=Lists::length(rows);
        let transcript=KzgTranscript::observe_u64(transcript,count);
        let transcript=KzgTranscript::observe_field(transcript,zeta);
        let transcript=match count {1=>transcript,2=>KzgTranscript::observe_field(transcript,zeta*KzgAlgebra::two_adic_gen(log))};
        observe_matrix_queries(transcript,rest,zeta)
      },
    }
  }

  fn commitment_bytes(commitment:KzgPackedDeserialize::Commitment)->KzgIO::Input {
    let KzgPackedDeserialize::Commitment::Mk(bytes,_shapes,_points)=commitment; bytes
  }

  fn observe_rounds(transcript:KzgTranscript::Transcript,rounds:Rounds,zeta:Field)->KzgTranscript::Transcript {
    match *rounds {
      Lists::Node::Nil=>transcript,
      Lists::Node::Cons(round,rest)=>{
        let (commitment,matrices)=*round;
        let transcript=KzgTranscript::observe_input(transcript,commitment_bytes(commitment));
        let transcript=KzgTranscript::observe_u64(transcript,Lists::length(matrices));
        observe_rounds(observe_matrix_queries(transcript,matrices,zeta),rest,zeta)
      },
    }
  }

  fn group_packs(transcript:KzgTranscript::Transcript,groups:Lists::List<Group>,extras:Values,tail:Packs)
      ->(KzgTranscript::Transcript,Packs,Values) {
    match *groups {
      Lists::Node::Nil=>(transcript,tail,extras),
      Lists::Node::Cons(group,rest)=>{
        let Group::Mk(log,columns,point)=group;
        let need_next=has_next(columns)*(1-Fields::is_zero(log));
        let (current,next,extras)=values(columns,extras,need_next);
        let transcript=KzgTranscript::observe_fields(transcript,current);
        let transcript=KzgTranscript::observe_fields(transcript,next);
        let (transcript,packs,extras)=group_packs(transcript,rest,extras,tail);
        (transcript,&(Lists::Node::Cons(Pack::Mk(point,log,need_next,current,next),packs)),extras)
      },
    }
  }

  fn round_packs(transcript:KzgTranscript::Transcript,rounds:Rounds,extras:Values,max_log:Field)
      ->(KzgTranscript::Transcript,Packs) {
    match *rounds {
      Lists::Node::Nil=>{let Lists::Node::Nil=*extras;(transcript,&(Lists::Node::Nil))},
      Lists::Node::Cons(round,rest)=>{
        let (commitment,matrices)=*round;
        let KzgPackedDeserialize::Commitment::Mk(_bytes,shapes,points)=commitment;
        let groups=walk(matrices,shapes,points,0,max_log);
        let (transcript,head,extras)=group_packs(transcript,groups,extras,&(Lists::Node::Nil));
        let (transcript,tail)=round_packs(transcript,rest,extras,max_log);
        (transcript,Lists::concat(head,tail))
      },
    }
  }

  fn pow_byte(accumulator:Field,base:Field,bits:[Field;8])->Field {
    let accumulator=accumulator*accumulator*(1+bits[7]*(base-1));
    let accumulator=accumulator*accumulator*(1+bits[6]*(base-1));
    let accumulator=accumulator*accumulator*(1+bits[5]*(base-1));
    let accumulator=accumulator*accumulator*(1+bits[4]*(base-1));
    let accumulator=accumulator*accumulator*(1+bits[3]*(base-1));
    let accumulator=accumulator*accumulator*(1+bits[2]*(base-1));
    let accumulator=accumulator*accumulator*(1+bits[1]*(base-1));
    accumulator*accumulator*(1+bits[0]*(base-1))
  }

  fn pow_u32(base:Field,exponent:Field)->Field {
    let bytes=UInt32::to_bytes(UInt32::from_field(exponent));
    let value=pow_byte(1,base,UInt8::bit_decomposition(bytes[3]));
    let value=pow_byte(value,base,UInt8::bit_decomposition(bytes[2]));
    let value=pow_byte(value,base,UInt8::bit_decomposition(bytes[1]));
    pow_byte(value,base,UInt8::bit_decomposition(bytes[0]))
  }

  fn weigh(packs:Packs,gamma:Field,z:Field,zeta:Field,power:Field,constant:Field,terms:Pairs)->(Field,Pairs) {
    match *packs {
      Lists::Node::Nil=>(constant,terms),
      Lists::Node::Cons(pack,rest)=>{
        let Pack::Mk(point,log,need_next,current,next)=pack;
        let y=pow_u32(z,Lists::length(current));
        let here=KzgAlgebra::polynomial(current,z);
        let (vanishing,remainder)=match need_next {
          0=>(y-zeta,here),
          1=>{
            let after=zeta*KzgAlgebra::two_adic_gen(log);
            let lagrange=(y-after)/(zeta-after);
            ((y-zeta)*(y-after),lagrange*here+(1-lagrange)*KzgAlgebra::polynomial(next,z))
          },
        };
        assert_eq!(Fields::is_zero(vanishing),0,"packed SHPLONK challenge on a pack point set");
        let weight=power/vanishing;
        weigh(rest,gamma,z,zeta,power*gamma,constant+weight*remainder,&(Lists::Node::Cons((point,weight),terms)))
      },
    }
  }

  fn rounds(frames:Lists::List<KzgPackedShape::Frame>,main:KzgPackedDeserialize::Commitment,
      stage2:KzgPackedDeserialize::Commitment,quotient:KzgPackedDeserialize::Commitment,
      fixed:KzgPackedDeserialize::Fixed)->Rounds {
    let tail=match fixed {
      KzgPackedDeserialize::Fixed::None=>&(Lists::Node::Nil),
      KzgPackedDeserialize::Fixed::Some(fixed)=>&(Lists::Node::Cons(&(fixed,KzgPackedShape::matrices(frames,3)),&(Lists::Node::Nil))),
      KzgPackedDeserialize::Fixed::Shared(fixed,_slots)=>&(Lists::Node::Cons(&(fixed,KzgPackedShape::matrices(frames,3)),&(Lists::Node::Nil))),
    };
    &(Lists::Node::Cons(&(main,KzgPackedShape::matrices(frames,0)),
      &(Lists::Node::Cons(&(stage2,KzgPackedShape::matrices(frames,1)),
      &(Lists::Node::Cons(&(quotient,KzgPackedShape::matrices(frames,2)),tail))))))
  }

  fn reduce(transcript:KzgTranscript::Transcript,rounds:Rounds,extras:Values,
      w1:KzgPackedDeserialize::Witness,w2:KzgPackedDeserialize::Witness,
      zeta:Field,generator:BN254G1::Point,max_log:Field)->(KzgTranscript::Transcript,BN254G1::Point,BN254G1::Point) {
    let transcript=KzgTranscript::observe_bytes(transcript,open_domain(&(Lists::Node::Nil)));
    let transcript=KzgTranscript::observe_u64(transcript,Lists::length(rounds));
    let transcript=observe_rounds(transcript,rounds,zeta);
    let (transcript,packs)=round_packs(transcript,rounds,extras,max_log);
    let KzgPackedDeserialize::Witness::Mk(w1,w1_bytes)=w1;
    let KzgPackedDeserialize::Witness::Mk(w2,w2_bytes)=w2;
    let transcript=KzgTranscript::observe_bytes(transcript,batch_domain(&(Lists::Node::Nil)));
    let (gamma,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe32(transcript,w1_bytes);
    let (z,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe32(transcript,w2_bytes);
    let (constant,terms)=weigh(packs,gamma,z,zeta,1,0,&(Lists::Node::Nil));
    let terms=&(Lists::Node::Cons((generator,0-constant),&(Lists::Node::Cons((w2,z),terms))));
    (transcript,BN254G1::add(KzgMsm::msm(terms),BN254G1::neg(w1)),BN254G1::neg(w2))
  }
}
⟧

end MultiStark.Source
