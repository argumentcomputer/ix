import Aiur.Modules.Frontend

/-! Activation, domain and opening-shape checks for packed proofs. Every
packed matrix shape must equal the trusted AIR width at the proof's height,
in the native round order. Frames carry only scalar openings; the AIR checks
reuse the column verifier's algebra.

Fixed matrices are opened per committed slot. Without sharing every circuit
with fixed columns owns one slot. With a shared key (`Fixed::Shared`) circuit
`i` names its slot; slots are numbered in order of first use, so a circuit
either opens the next slot (consuming its shape and openings) or reads an
earlier slot's opened rows. A reader must have the slot's height, width and
next-row class, and the key must share at least one slot, as for the native
`System::new_shared`. The frame's last field is 1 when it owns its slot: the
opening reduction lists each slot once, at its owner. -/
namespace MultiStark.Source

def kzgPackedShape : Aiur.Modules.Program Nat := aiur⟦
module KzgPackedShape {
  type Values=Lists::List<Field>;
  type Rows=KzgShape::Rows;
  type Openings=KzgDeserialize::Openings;
  type Shapes=KzgPackedDeserialize::Shapes;
  type Cursor=&(Values,Shapes,Shapes,Shapes,Values,Openings,Openings,Openings,Shapes,Openings);
  enum Frame { Mk(KzgDeserialize::Circuit,Field,Field,Rows,Rows,Rows,Rows,Field) }
  -- Sharing flag, remaining slot list, opened slots (height, rows; newest
  -- first), slot count, circuits with fixed columns.
  type Sharing=&(Field,Values,Lists::List<(Field,Rows)>,Field,Field);
  enum Matrix { Mk(Field,Field,Rows) }
  type Matrices=Lists::List<Matrix>;

  fn shape(shapes:Shapes,log:Field,width:Field)->Shapes {
    let Lists::Node::Cons((found_log,found_width,_next),rest)=*shapes;
    assert_eq!(found_log,log,"packed matrix height");
    assert_eq!(found_width,width,"packed matrix width");
    rest
  }

  fn consume(circuit:KzgDeserialize::Circuit,cursor:Cursor,sharing:Sharing,max_log:Field)->(Frame,Cursor,Sharing) {
    let KzgDeserialize::Circuit::Mk(widths,_nodes,_roots,_lookups,mn,fixed_next)=circuit;
    let (logs,main,stage2,quotient,accumulators,mo,so,qo,fixed,fo)=*cursor;
    let Lists::Node::Cons(log,logs)=*logs;
    assert_eq!(UInt32::less_than_fields(log,max_log+1),1,"packed trace capacity");
    assert_eq!(UInt32::less_than_fields(log+KzgShape::power_log(widths[7]),29),1,"packed quotient domain");
    let main=shape(main,log,widths[4]);let stage2=shape(stage2,log,widths[5]);let quotient=shape(quotient,log,widths[7]);
    let Lists::Node::Cons(acc,accumulators)=*accumulators;
    let Lists::Node::Cons(mv,mo)=*mo;let Lists::Node::Cons(sv,so)=*so;let Lists::Node::Cons(qv,qo)=*qo;
    KzgShape::rows_width(mv,widths[4],1+mn);KzgShape::rows_width(sv,widths[5],2);KzgShape::rows_width(qv,widths[7],1);
    let (shared,slots,seen,count,readers)=*sharing;
    let (slot,slots)=match shared {0=>(0,slots),1=>{let Lists::Node::Cons(slot,rest)=*slots;(slot,rest)}};
    match widths[3] {
      0=>{
        assert_eq!(slot,0,"packed fixed slot without fixed columns");
        (Frame::Mk(circuit,log,acc,mv,sv,qv,&(Lists::Node::Nil),0),&(logs,main,stage2,quotient,accumulators,mo,so,qo,fixed,fo),
          &(shared,slots,seen,count,readers))
      },
      _=>{
        assert_eq!(widths[2],KzgShape::power2(log),"packed fixed domain");
        match 1-shared*(1-Fields::is_zero(slot-count-1)) {
          1=>{
            let fixed=shape(fixed,log,widths[3]);let Lists::Node::Cons(fv,fo)=*fo;
            KzgShape::rows_width(fv,widths[3],1+fixed_next);
            (Frame::Mk(circuit,log,acc,mv,sv,qv,fv,1),&(logs,main,stage2,quotient,accumulators,mo,so,qo,fixed,fo),
              &(shared,slots,&(Lists::Node::Cons((log,fv),seen)),count+1,readers+1))
          },
          0=>{
            assert_eq!(Fields::is_zero(slot),0,"packed fixed circuit without a slot");
            assert_eq!(UInt32::less_than_fields(slot,count+1),1,"packed fixed slot out of order");
            let (owner_log,fv)=Lists::lookup(seen,count-slot);
            assert_eq!(owner_log,log,"packed shared fixed height");
            KzgShape::rows_width(fv,widths[3],1+fixed_next);
            (Frame::Mk(circuit,log,acc,mv,sv,qv,fv,0),&(logs,main,stage2,quotient,accumulators,mo,so,qo,fixed,fo),
              &(shared,slots,seen,count,readers+1))
          },
        }
      },
    }
  }

  fn walk(circuits:Lists::List<KzgDeserialize::Circuit>,active:Values,cursor:Cursor,sharing:Sharing,max_log:Field,total:Field,budget:Field)->Lists::List<Frame> {
    match (*circuits, *active) {
      (Lists::Node::Nil,Lists::Node::Nil)=>{
        let (logs,main,stage2,quotient,accumulators,mo,so,qo,fixed,fo)=*cursor;
        let Lists::Node::Nil=*logs;let Lists::Node::Nil=*main;let Lists::Node::Nil=*stage2;
        let Lists::Node::Nil=*quotient;let Lists::Node::Nil=*accumulators;
        let Lists::Node::Nil=*mo;let Lists::Node::Nil=*so;let Lists::Node::Nil=*qo;
        let Lists::Node::Nil=*fixed;let Lists::Node::Nil=*fo;
        let (shared,slots,_seen,count,readers)=*sharing;
        let Lists::Node::Nil=*slots;
        match shared {0=>(),1=>{assert_eq!(UInt32::less_than_fields(count,readers),1,"packed shared key shares no fixed slot");()}};
        assert_eq!(Fields::is_zero(total),0,"no active packed circuits");
        let rows=UInt64::from_field(total);assert_eq!(UInt64::to_field(rows),total,"packed rows exceed u64");
        let (_,borrow)=UInt64::sub_with_borrow(rows,UInt64::from_field(549755813889));
        assert_eq!(borrow,1,"packed total rows exceed 2^39");
        assert_eq!(UInt64::to_field(UInt64::from_field(budget)),budget,"packed lookup budget exceeds u64");
        &(Lists::Node::Nil)
      },
      (Lists::Node::Cons(circuit,rest),Lists::Node::Cons(on,active))=>{
        let KzgDeserialize::Circuit::Mk(widths,_nodes,_roots,lookups,_mn,_fn)=circuit;
        match on {
          0=>{
            assert_eq!(widths[2],0,"inactive packed fixed table");
            let (shared,slots,seen,count,readers)=*sharing;
            let slots=match shared {0=>slots,1=>{let Lists::Node::Cons(slot,rest)=*slots;
              assert_eq!(slot,0,"packed fixed slot without fixed columns");rest}};
            walk(rest,active,cursor,&(shared,slots,seen,count,readers),max_log,total,budget)
          },
          1=>{
            let (frame,cursor,sharing)=consume(circuit,cursor,sharing,max_log);
            let Frame::Mk(_c,log,_acc,_mo,_so,_qo,_fo,_owns)=frame;
            let rows=KzgShape::power2(log);let count=Lists::length(lookups);
            let tail=walk(rest,active,cursor,sharing,max_log,total+rows,budget+rows*(count+Fields::is_zero(count)));
            &(Lists::Node::Cons(frame,tail))
          },
        }
      },
    }
  }

  fn shapes(commitment:KzgPackedDeserialize::Commitment)->Shapes {
    let KzgPackedDeserialize::Commitment::Mk(_bytes,shapes,_points)=commitment; shapes
  }

  fn frames(key:KzgPackedDeserialize::Key,proof:KzgPackedDeserialize::Proof)->Lists::List<Frame> {
    let KzgPackedDeserialize::Key::Mk(_seed,max_log,_budget,_g,_anchors,circuits,fixed)=key;
    let KzgPackedDeserialize::Proof::Mk(active,logs,main,stage2,quotient,accumulators,mo,so,qo,fo,_extras,_w1,_w2)=proof;
    let unshared=&(0,&(Lists::Node::Nil),&(Lists::Node::Nil),0,0);
    match (fixed,fo) {
      (KzgPackedDeserialize::Fixed::None,KzgDeserialize::FixedOpen::None)=>
        walk(circuits,active,&(logs,shapes(main),shapes(stage2),shapes(quotient),accumulators,mo,so,qo,
          &(Lists::Node::Nil),&(Lists::Node::Nil)),unshared,max_log,0,1),
      (KzgPackedDeserialize::Fixed::Some(fixed),KzgDeserialize::FixedOpen::Some(fo))=>
        walk(circuits,active,&(logs,shapes(main),shapes(stage2),shapes(quotient),accumulators,mo,so,qo,
          shapes(fixed),fo),unshared,max_log,0,1),
      (KzgPackedDeserialize::Fixed::Shared(fixed,slots),KzgDeserialize::FixedOpen::Some(fo))=>
        walk(circuits,active,&(logs,shapes(main),shapes(stage2),shapes(quotient),accumulators,mo,so,qo,
          shapes(fixed),fo),&(1,slots,&(Lists::Node::Nil),0,0),max_log,0,1),
    }
  }

  fn verify_frames(frames:Lists::List<Frame>,beta:Field,gamma:Field,alpha:Field,zeta:Field,accumulator:Field)->() {
    match *frames {
      Lists::Node::Nil=>{assert_eq!(accumulator,0,"packed unbalanced final accumulator");()},
      Lists::Node::Cons(frame,rest)=>{
        let Frame::Mk(circuit,log,next_accumulator,mo,so,qo,fo,_owns)=frame;
        let KzgDeserialize::Circuit::Mk(shape,nodes,roots,lookups,_mn,_fn)=circuit;
        let z_n=KzgAlgebra::exp_power2(zeta,log);let vanishing=z_n-1;
        assert_eq!(Fields::is_zero(vanishing),0,"packed challenge lies on trace domain");
        let g=KzgAlgebra::two_adic_gen(log);let transition=zeta-1/g;
        let first=vanishing/(zeta-1);let last=vanishing/transition;
        let current=KzgAlgebra::first_row(so);let next=KzgAlgebra::next_row(so);
        let context=&(KzgAlgebra::first_row(mo),KzgAlgebra::next_row(mo),KzgAlgebra::first_row(fo),KzgAlgebra::next_row(fo),
          current,next,[beta,gamma,accumulator,next_accumulator],first,last,transition);
        let folded=KzgAlgebra::fold_roots(roots,nodes,context,alpha,0);
        let injection=last*(next_accumulator-accumulator)/(KzgShape::power2(log)*g);
        let folded=KzgAlgebra::fold_lookups(lookups,shape[6],0,nodes,context,beta,gamma,alpha,current,next,injection,folded);
        let quotient=KzgAlgebra::polynomial(KzgAlgebra::first_row(qo),z_n);
        assert_eq!(folded,vanishing*quotient,"packed quotient relation");
        verify_frames(rest,beta,gamma,alpha,zeta,next_accumulator)
      },
    }
  }

  fn matrices(frames:Lists::List<Frame>,round:Field)->Matrices {
    match *frames {
      Lists::Node::Nil=>&(Lists::Node::Nil),
      Lists::Node::Cons(frame,rest)=>{
        let Frame::Mk(circuit,log,_acc,mo,so,qo,fo,owns)=frame;
        let KzgDeserialize::Circuit::Mk(shape,_n,_r,_l,_mn,_fn)=circuit;
        let tail=matrices(rest,round);
        match round {
          0=>&(Lists::Node::Cons(Matrix::Mk(log,shape[4],mo),tail)),
          1=>&(Lists::Node::Cons(Matrix::Mk(log,shape[5],so),tail)),
          2=>&(Lists::Node::Cons(Matrix::Mk(log,shape[7],qo),tail)),
          3=>match owns {0=>tail,1=>&(Lists::Node::Cons(Matrix::Mk(log,shape[3],fo),tail))},
        }
      },
    }
  }
}
⟧

end MultiStark.Source
