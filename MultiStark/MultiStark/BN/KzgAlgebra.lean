import Aiur.Modules.Frontend

/-! Native-Fr AIR, grouped logUp and quotient checks. Evaluation follows the
compiled graph and the pinned multi-stark Horner order; no witness-supplied
constraint evaluation is trusted. -/
namespace MultiStark.Source

def kzgAlgebra : Aiur.Modules.Program Nat := aiur⟦
module KzgAlgebra {
  type Values = Lists::List<Field>;
  type Nodes = Lists::List<KzgDeserialize::Node>;
  type Context = &(Values,Values,Values,Values,Values,Values,[Field;4],Field,Field,Field);

  fn two_adic_gen(log: Field) -> Field {
    match log {28 => 19103219067921713944291392827692070036145651957329286315305642004821462161904, _ => {let value = two_adic_gen(log+1); value*value}}
  }

  fn exp_power2(value: Field, log: Field) -> Field {
    match log {0 => value, _ => exp_power2(value*value,log-1)}
  }

  fn fingerprint(values: Values, gamma: Field) -> Field {
    match *values {Lists::Node::Nil => 0,
      Lists::Node::Cons(value,rest) => value+gamma*fingerprint(rest,gamma)}
  }

  fn claims_accumulator(claims: Lists::List<Values>, beta: Field, gamma: Field) -> Field {
    match *claims {Lists::Node::Nil => 0,
      Lists::Node::Cons(claim,rest) => 1/(beta+fingerprint(claim,gamma))+claims_accumulator(rest,beta,gamma)}
  }

  fn eval_at(nodes: Nodes, index: Field, context: Context) -> Field {
    let (main,main_next,fixed,fixed_next,stage2,stage2_next,publics,first,last,transition) = *context;
    match Lists::lookup(nodes,index) {
      KzgDeserialize::Node::Const(value) => value,
      KzgDeserialize::Node::Var(source,offset,column) => match source+source+offset {
        0=>Lists::lookup(fixed,column),1=>Lists::lookup(fixed_next,column),
        2=>Lists::lookup(main,column),3=>Lists::lookup(main_next,column),
        4=>Lists::lookup(stage2,column),5=>Lists::lookup(stage2_next,column),
      },
      KzgDeserialize::Node::Public(index) => match index {0=>publics[0],1=>publics[1],2=>publics[2],3=>publics[3]},
      KzgDeserialize::Node::First => first,
      KzgDeserialize::Node::Last => last,
      KzgDeserialize::Node::Transition => transition,
      KzgDeserialize::Node::Add(a,b) => eval_at(nodes,a,context)+eval_at(nodes,b,context),
      KzgDeserialize::Node::Sub(a,b) => eval_at(nodes,a,context)-eval_at(nodes,b,context),
      KzgDeserialize::Node::Mul(a,b) => eval_at(nodes,a,context)*eval_at(nodes,b,context),
      KzgDeserialize::Node::Neg(a) => 0-eval_at(nodes,a,context),
    }
  }

  fn fold_roots(roots: Values, nodes: Nodes, context: Context, alpha: Field, accumulator: Field) -> Field {
    match *roots {
      Lists::Node::Nil=>accumulator,
      Lists::Node::Cons(root,rest)=>fold_roots(rest,nodes,context,alpha,accumulator*alpha+eval_at(nodes,root,context)),
    }
  }

  fn lookup_fingerprint(args: Values, nodes: Nodes, context: Context, gamma: Field) -> Field {
    match *args {Lists::Node::Nil=>0,
      Lists::Node::Cons(arg,rest)=>eval_at(nodes,arg,context)+gamma*lookup_fingerprint(rest,nodes,context,gamma)}
  }

  fn group_summary(lookups: Lists::List<KzgDeserialize::Lookup>, remaining: Field,
      nodes: Nodes, context: Context, beta: Field, gamma: Field, product: Field, numerator: Field)
      -> (Field,Field,Lists::List<KzgDeserialize::Lookup>) {
    match remaining {
      0=>(product,numerator,lookups),
      _=>match *lookups {
        Lists::Node::Nil=>(product,numerator,lookups),
        Lists::Node::Cons(lookup,rest)=>{
          let KzgDeserialize::Lookup::Mk(multiplicity,args)=lookup;
          let message=beta+lookup_fingerprint(args,nodes,context,gamma);
          group_summary(rest,remaining-1,nodes,context,beta,gamma,
            product*message,numerator*message+eval_at(nodes,multiplicity,context)*product)
        },
      },
    }
  }

  fn fold_lookups(lookups: Lists::List<KzgDeserialize::Lookup>, size: Field, index: Field,
      nodes: Nodes, context: Context, beta: Field, gamma: Field, alpha: Field,
      current: Values, next: Values, injection: Field, accumulator: Field) -> Field {
    match *lookups {
      Lists::Node::Nil=>accumulator*alpha+Lists::lookup(next,0)-Lists::lookup(current,0)+injection,
      _=>{
        let (product,numerator,rest)=group_summary(lookups,size,nodes,context,beta,gamma,1,0);
        let last=Lists::is_empty(rest);
        let target=match last {1=>Lists::lookup(next,0)+injection,0=>Lists::lookup(current,index+1)};
        let value=product*(target-Lists::lookup(current,index))-numerator;
        let accumulator=accumulator*alpha+value;
        match last {1=>accumulator,0=>fold_lookups(rest,size,index+1,nodes,context,beta,gamma,alpha,current,next,injection,accumulator)}
      },
    }
  }

  fn polynomial(values: Values, point: Field) -> Field {
    match *values {Lists::Node::Nil=>0,Lists::Node::Cons(value,rest)=>value+point*polynomial(rest,point)}
  }

  fn first_row(rows: KzgShape::Rows) -> Values {
    match *rows {Lists::Node::Nil=>&(Lists::Node::Nil),Lists::Node::Cons(row,_rest)=>row}
  }
  fn next_row(rows: KzgShape::Rows) -> Values {
    match *rows {Lists::Node::Nil=>&(Lists::Node::Nil),Lists::Node::Cons(_row,rest)=>first_row(rest)}
  }

  fn verify_frames(frames: Lists::List<KzgShape::Frame>, beta: Field, gamma: Field, alpha: Field, zeta: Field, accumulator: Field) -> () {
    match *frames {
      Lists::Node::Nil=>{assert_eq!(accumulator,0,"KZG unbalanced final accumulator"); ()},
      Lists::Node::Cons(frame,rest)=>{
        let KzgShape::Frame::Mk(circuit,log,_main,_stage2,_quotient,next_accumulator,main_open,stage2_open,quotient_open,_fixed,fixed_open)=frame;
        let KzgDeserialize::Circuit::Mk(shape,nodes,roots,lookups,_main_next,_fixed_next)=circuit;
        let z_n=exp_power2(zeta,log);
        let vanishing=z_n-1;
        assert_eq!(Fields::is_zero(vanishing),0,"KZG challenge lies on trace domain");
        let g=two_adic_gen(log);
        let transition=zeta-1/g;
        let first=vanishing/(zeta-1);
        let last=vanishing/transition;
        let current=first_row(stage2_open);
        let next=next_row(stage2_open);
        let context=&(first_row(main_open),next_row(main_open),first_row(fixed_open),next_row(fixed_open),
          current,next,[beta,gamma,accumulator,next_accumulator],first,last,transition);
        let folded=fold_roots(roots,nodes,context,alpha,0);
        let injection=last*(next_accumulator-accumulator)/(KzgShape::power2(log)*g);
        let folded=fold_lookups(lookups,shape[6],0,nodes,context,beta,gamma,alpha,current,next,injection,folded);
        let quotient=polynomial(first_row(quotient_open),z_n);
        assert_eq!(folded,vanishing*quotient,"KZG quotient relation");
        verify_frames(rest,beta,gamma,alpha,zeta,next_accumulator)
      },
    }
  }
}
⟧

end MultiStark.Source
