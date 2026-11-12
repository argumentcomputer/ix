import Aiur.Modules.Frontend

/-! The pinned KZG PCS opening reduction: per-point v batching followed by
cross-point r batching. The output is a deferred two-pairing product against
(G2, tau-G2); this module never treats deferred verification as a pairing check. -/
namespace MultiStark.Source

def kzgPcs : Aiur.Modules.Program Nat := aiur⟦
module KzgPcs {
  type Point = BN254G1::Point;
  type Points = Lists::List<Point>;
  type Values = Lists::List<Field>;
  type Pairs = Lists::List<(Point,Field)>;
  enum Matrix { Mk(Field,Points,KzgShape::Rows) }
  type Round = Lists::List<Matrix>;
  enum Batch { Mk(Field,Pairs) }

  fn matrices(frames: Lists::List<KzgShape::Frame>, round: Field) -> Round {
    match *frames {
      Lists::Node::Nil=>&(Lists::Node::Nil),
      Lists::Node::Cons(frame,rest)=>{
        let KzgShape::Frame::Mk(circuit,log,main,stage2,quotient,_acc,main_open,stage2_open,quotient_open,fixed,fixed_open)=frame;
        let tail=matrices(rest,round);
        match round {
          0=>&(Lists::Node::Cons(Matrix::Mk(log,main,main_open),tail)),
          1=>&(Lists::Node::Cons(Matrix::Mk(log,stage2,stage2_open),tail)),
          2=>&(Lists::Node::Cons(Matrix::Mk(log,quotient,quotient_open),tail)),
          3=>{
            let KzgDeserialize::Circuit::Mk(shape,_nodes,_roots,_lookups,_mn,_fn)=circuit;
            match shape[3] {0=>tail,_=>&(Lists::Node::Cons(Matrix::Mk(log,fixed,fixed_open),tail))}
          },
        }
      },
    }
  }

  fn rounds(frames: Lists::List<KzgShape::Frame>, fixed: KzgDeserialize::Fixed) -> Lists::List<Round> {
    let tail=match fixed {KzgDeserialize::Fixed::None=>&(Lists::Node::Nil),
      KzgDeserialize::Fixed::Some(_)=>&(Lists::Node::Cons(matrices(frames,3),&(Lists::Node::Nil)))};
    &(Lists::Node::Cons(matrices(frames,0),&(Lists::Node::Cons(matrices(frames,1),
      &(Lists::Node::Cons(matrices(frames,2),tail))))))
  }

  fn commitments(round: Round) -> KzgDeserialize::Commitment {
    match *round {
      Lists::Node::Nil=>&(Lists::Node::Nil),
      Lists::Node::Cons(matrix,rest)=>{
        let Matrix::Mk(_log,points,_values)=matrix;
        &(Lists::Node::Cons(points,commitments(rest)))
      },
    }
  }

  fn observe_logs(transcript: KzgTranscript::Transcript, round: Round) -> KzgTranscript::Transcript {
    match *round {
      Lists::Node::Nil=>transcript,
      Lists::Node::Cons(matrix,rest)=>{
        let Matrix::Mk(log,_points,_values)=matrix;
        observe_logs(KzgTranscript::observe_u64(transcript,log),rest)
      },
    }
  }

  fn observe_rounds(transcript: KzgTranscript::Transcript, rounds: Lists::List<Round>) -> KzgTranscript::Transcript {
    match *rounds {
      Lists::Node::Nil=>transcript,
      Lists::Node::Cons(round,rest)=>{
        let transcript=KzgTranscript::observe_commitment(transcript,commitments(round));
        observe_rounds(observe_logs(transcript,round),rest)
      },
    }
  }

  fn prepend_pairs(points: Points, values: Values, reverse: Pairs) -> Pairs {
    match (*points, *values) {
      (Lists::Node::Nil,Lists::Node::Nil)=>reverse,
      (Lists::Node::Cons(point,points),Lists::Node::Cons(value,values))=>
        prepend_pairs(points,values,&(Lists::Node::Cons((point,value),reverse))),
    }
  }

  fn add_batch(batches: Lists::List<Batch>, generator: Field, points: Points, values: Values) -> Lists::List<Batch> {
    match *batches {
      Lists::Node::Nil=>&(Lists::Node::Cons(Batch::Mk(generator,prepend_pairs(points,values,&(Lists::Node::Nil))),&(Lists::Node::Nil))),
      Lists::Node::Cons(batch,rest)=>{
        let Batch::Mk(existing,reverse)=batch;
        match Fields::is_zero(generator-existing) {
          1=>&(Lists::Node::Cons(Batch::Mk(existing,prepend_pairs(points,values,reverse)),rest)),
          0=>&(Lists::Node::Cons(batch,add_batch(rest,generator,points,values))),
        }
      },
    }
  }

  fn observe_rows(transcript: KzgTranscript::Transcript, batches: Lists::List<Batch>, rows: KzgShape::Rows,
      points: Points, generator: Field, index: Field) -> (KzgTranscript::Transcript,Lists::List<Batch>) {
    match *rows {
      Lists::Node::Nil=>(transcript,batches),
      Lists::Node::Cons(values,rest)=>{
        let factor=match index {0=>1,1=>generator};
        let transcript=KzgTranscript::observe_fields(transcript,values);
        let batches=add_batch(batches,factor,points,values);
        observe_rows(transcript,batches,rest,points,generator,index+1)
      },
    }
  }

  fn observe_matrices(transcript: KzgTranscript::Transcript, batches: Lists::List<Batch>, round: Round)
      -> (KzgTranscript::Transcript,Lists::List<Batch>) {
    match *round {
      Lists::Node::Nil=>(transcript,batches),
      Lists::Node::Cons(matrix,rest)=>{
        let Matrix::Mk(log,points,rows)=matrix;
        let (transcript,batches)=observe_rows(transcript,batches,rows,points,KzgAlgebra::two_adic_gen(log),0);
        observe_matrices(transcript,batches,rest)
      },
    }
  }

  fn observe_openings(transcript: KzgTranscript::Transcript, batches: Lists::List<Batch>, rounds: Lists::List<Round>)
      -> (KzgTranscript::Transcript,Lists::List<Batch>) {
    match *rounds {
      Lists::Node::Nil=>(transcript,batches),
      Lists::Node::Cons(round,rest)=>{
        let (transcript,batches)=observe_matrices(transcript,batches,round);
        observe_openings(transcript,batches,rest)
      },
    }
  }

  fn observe_witnesses(transcript: KzgTranscript::Transcript, witnesses: Points) -> KzgTranscript::Transcript {
    match *witnesses {
      Lists::Node::Nil=>transcript,
      Lists::Node::Cons(point,rest)=>{
        let bytes=Blake3::address_from_fields(BN254G1::to_bytes(point));
        let transcript=KzgTranscript::observe_bytes(transcript,KzgIO::prepend32(bytes,&(Lists::Node::Nil)));
        observe_witnesses(transcript,rest)
      },
    }
  }

  fn fold_pairs(pairs: Pairs, v: Field, power: Field, weight: Field, expected: Field, terms: Pairs) -> (Field,Pairs) {
    match *pairs {
      Lists::Node::Nil=>(expected,terms),
      Lists::Node::Cons((point,value),rest)=>fold_pairs(rest,v,power*v,weight,expected+power*value,
        &(Lists::Node::Cons((point,power*weight),terms))),
    }
  }

  fn collect(batches: Lists::List<Batch>, witnesses: Points, v: Field, r: Field, weight: Field,
      zeta: Field, generator: Point, left: Pairs, right: Pairs) -> (Pairs,Pairs) {
    match (*batches, *witnesses) {
      (Lists::Node::Nil,Lists::Node::Nil)=>(left,right),
      (Lists::Node::Cons(batch,batches),Lists::Node::Cons(witness,witnesses))=>{
        let Batch::Mk(factor,reverse)=batch;
        let (expected,left)=fold_pairs(Lists::reverse(reverse),v,1,weight,0,left);
        let left=&(Lists::Node::Cons((generator,0-expected*weight),left));
        let left=&(Lists::Node::Cons((witness,zeta*factor*weight),left));
        let right=&(Lists::Node::Cons((witness,0-weight),right));
        collect(batches,witnesses,v,r,weight*r,zeta,generator,left,right)
      },
    }
  }

  fn reduce(transcript: KzgTranscript::Transcript, frames: Lists::List<KzgShape::Frame>, fixed: KzgDeserialize::Fixed,
      witnesses: Points, zeta: Field, generator: Point) -> (Point,Point) {
    let rounds=rounds(frames,fixed);
    let transcript=observe_rounds(transcript,rounds);
    let (transcript,batches)=observe_openings(transcript,&(Lists::Node::Nil),rounds);
    assert_eq!(Lists::length(batches),Lists::length(witnesses),"KZG opening witness count");
    let (v,transcript)=KzgTranscript::sample(transcript);
    let transcript=observe_witnesses(transcript,witnesses);
    let (r,_transcript)=KzgTranscript::sample(transcript);
    let (left,right)=collect(batches,witnesses,v,r,1,zeta,generator,&(Lists::Node::Nil),&(Lists::Node::Nil));
    (KzgMsm::msm(left),KzgMsm::msm(right))
  }
}
⟧

end MultiStark.Source
