import Aiur.Modules.Frontend

/-! Canonical source-wire grammar for native-Fr multi-stark keys and proofs.
Graph children precede parents, every scalar and point is canonical, and no
trailing bytes or unknown tags are accepted. -/
namespace MultiStark.Source

def kzgDeserialize : Aiur.Modules.Program Nat := aiur⟦
module KzgDeserialize {
  enum Node { Const(Field), Var(Field, Field, Field), Public(Field), First, Last, Transition,
    Add(Field, Field), Sub(Field, Field), Mul(Field, Field), Neg(Field) }
  enum Lookup { Mk(Field, Lists::List<Field>) }
  enum Circuit { Mk([Field; 8], Lists::List<Node>, Lists::List<Field>, Lists::List<Lookup>, Field, Field) }
  type Commitment = Lists::List<Lists::List<BN254G1::Point>>;
  type Openings = Lists::List<Lists::List<Lists::List<Field>>>;
  enum Fixed { None, Some(Commitment) }
  enum FixedOpen { None, Some(Openings) }
  enum Key { Mk(Bytes::Stream, Field, Field, BN254G1::Point, Bytes::Stream, Lists::List<Circuit>, Fixed) }
  enum Proof { Mk(Lists::List<Field>, Lists::List<Field>, Commitment, Commitment, Commitment,
    Lists::List<Field>, Lists::List<BN254G1::Point>, Openings, Openings, Openings, FixedOpen) }
  enum Policy { Mk(Bytes::Stream, KzgIO::Digest, Field, KzgIO::Digest, Field) }

  fn check_child(child: Field, index: Field) -> () {
    assert_eq!(UInt32::less_than_fields(child, index), 1, "KZG graph child does not precede parent"); ()
  }

  fn node(input: Bytes::Stream, index: Field, widths: [Field;8]) -> (Node, Bytes::Stream, Field, Field) {
    let (tag, input) = KzgIO::tag(input);
    match tag {
      0 => {let (value, input) = KzgIO::scalar(input); (Node::Const(value), input, 0, 0)},
      1 => {
        let (source, input) = KzgIO::tag(input);
        let (offset, input) = KzgIO::tag(input);
        let (column, input) = KzgIO::u32(input);
        assert_eq!(offset * (offset - 1), 0, "KZG graph row offset");
        match source {
          0 => {assert_eq!(UInt32::less_than_fields(column, widths[3]), 1, "KZG fixed column"); (Node::Var(0, offset, column), input, 0, offset)},
          1 => {assert_eq!(UInt32::less_than_fields(column, widths[4]), 1, "KZG main column"); (Node::Var(1, offset, column), input, offset, 0)},
          2 => {assert_eq!(UInt32::less_than_fields(column, widths[5]), 1, "KZG lookup column"); (Node::Var(2, offset, column), input, 0, 0)},
        }
      },
      2 => {let (index, input) = KzgIO::u32(input); assert_eq!(UInt32::less_than_fields(index, 4), 1, "KZG public column"); (Node::Public(index), input, 0, 0)},
      3 => (Node::First, input, 0, 0),
      4 => (Node::Last, input, 0, 0),
      5 => (Node::Transition, input, 0, 0),
      6 => {let (a, input) = KzgIO::u32(input); let (b, input) = KzgIO::u32(input);
        check_child(a, index); check_child(b, index); (Node::Add(a, b), input, 0, 0)},
      7 => {let (a, input) = KzgIO::u32(input); let (b, input) = KzgIO::u32(input);
        check_child(a, index); check_child(b, index); (Node::Sub(a, b), input, 0, 0)},
      8 => {let (a, input) = KzgIO::u32(input); let (b, input) = KzgIO::u32(input);
        check_child(a, index); check_child(b, index); (Node::Mul(a, b), input, 0, 0)},
      9 => {let (a, input) = KzgIO::u32(input); check_child(a, index); (Node::Neg(a), input, 0, 0)},
    }
  }

  fn nodes(input: Bytes::Stream, count: Field, index: Field, widths: [Field;8]) -> (Lists::List<Node>, Bytes::Stream, Field, Field) {
    match count {
      0 => (&(Lists::Node::Nil), input, 0, 0),
      _ => {
        let (head, input, main, fixed) = node(input, index, widths);
        let (tail, input, main_tail, fixed_tail) = nodes(input, count - 1, index + 1, widths);
        (&(Lists::Node::Cons(head, tail)), input,
          1 - (1 - main) * (1 - main_tail), 1 - (1 - fixed) * (1 - fixed_tail))
      },
    }
  }

  fn ids(input: Bytes::Stream, count: Field, bound: Field) -> (Lists::List<Field>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {
        let (head, input) = KzgIO::u32(input); check_child(head, bound);
        let (tail, input) = ids(input, count - 1, bound);
        (&(Lists::Node::Cons(head, tail)), input)
      },
    }
  }

  fn lookups(input: Bytes::Stream, count: Field, bound: Field) -> (Lists::List<Lookup>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {
        let (multiplicity, input) = KzgIO::u32(input); check_child(multiplicity, bound);
        let (width, input) = KzgIO::u32(input);
        let (args, input) = ids(input, width, bound);
        let (tail, input) = lookups(input, count - 1, bound);
        (&(Lists::Node::Cons(Lookup::Mk(multiplicity, args), tail)), input)
      },
    }
  }

  fn group_count(count: Field, size: Field) -> Field {
    match count {
      0 => 0,
      _ => match UInt32::less_than_fields(count, size) {
        1 => 1,
        0 => 1 + group_count(count - size, size),
      },
    }
  }

  fn quotient_degree(degree: Field, candidate: Field) -> Field {
    match UInt32::less_than_fields(degree, candidate + 2) {
      1 => candidate,
      0 => quotient_degree(degree, candidate * 2),
    }
  }

  fn supported_power(value: Field, candidate: Field, remaining: Field) -> () {
    match Fields::is_zero(value - candidate) {
      1 => (),
      0 => {assert_eq!(Fields::is_zero(remaining), 0, "KZG unsupported power of two"); supported_power(value, candidate * 2, remaining - 1)},
    }
  }

  fn circuits(input: Bytes::Stream, count: Field, budget: Field) -> (Lists::List<Circuit>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {
        let (m0, input) = KzgIO::u32(input);
        let (m1, input) = KzgIO::u32(input);
        let (m2, input) = KzgIO::u32(input);
        let (m3, input) = KzgIO::u32(input);
        let (m4, input) = KzgIO::u32(input);
        let (m5, input) = KzgIO::u32(input);
        let (m6, input) = KzgIO::u32(input);
        let (m7, input) = KzgIO::u32(input);
        let shape = [m0,m1,m2,m3,m4,m5,m6,m7];
        assert_eq!(UInt32::less_than_fields(0, m6), 1, "zero KZG lookup group size");
        assert_eq!(UInt32::less_than_fields(m6, 9), 1, "KZG lookup group too large");
        assert_eq!(UInt32::less_than_fields(m1, budget + 2), 1, "KZG quotient budget exceeded");
        assert_eq!(m7, quotient_degree(m1, 1), "KZG quotient degree metadata");
        assert_eq!(Fields::is_zero(m2), Fields::is_zero(m3), "KZG fixed shape metadata");
        let (node_count, input) = KzgIO::u32(input);
        let (nodes, input, main_next, fixed_next) = nodes(input, node_count, 0, shape);
        let (root_count, input) = KzgIO::u32(input);
        let (roots, input) = ids(input, root_count, node_count);
        let (lookup_count, input) = KzgIO::u32(input);
        let (lookups, input) = lookups(input, lookup_count, node_count);
        let groups = group_count(lookup_count, m6);
        let groups = groups + Fields::is_zero(groups);
        assert_eq!(m5, groups, "KZG stage-two width metadata");
        assert_eq!(m0, root_count + groups, "KZG constraint count metadata");
        let (tail, input) = circuits(input, count - 1, budget);
        (&(Lists::Node::Cons(Circuit::Mk(shape, nodes, roots, lookups, main_next, fixed_next), tail)), input)
      },
    }
  }

  fn scalars(input: Bytes::Stream, count: Field) -> (Lists::List<Field>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {let (head, input) = KzgIO::scalar(input); let (tail, input) = scalars(input, count - 1);
        (&(Lists::Node::Cons(head, tail)), input)},
    }
  }

  fn points(input: Bytes::Stream, count: Field) -> (Lists::List<BN254G1::Point>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {let (head, input) = KzgIO::point(input); let (tail, input) = points(input, count - 1);
        (&(Lists::Node::Cons(head, tail)), input)},
    }
  }

  fn tags(input: Bytes::Stream, count: Field) -> (Lists::List<Field>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {let (head, input) = KzgIO::tag(input); let (tail, input) = tags(input, count - 1);
        (&(Lists::Node::Cons(head, tail)), input)},
    }
  }

  fn scalar_rows(input: Bytes::Stream, count: Field) -> (Lists::List<Lists::List<Field>>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {let (width, input) = KzgIO::u32(input); let (head, input) = scalars(input, width);
        let (tail, input) = scalar_rows(input, count - 1); (&(Lists::Node::Cons(head, tail)), input)},
    }
  }

  fn point_rows(input: Bytes::Stream, count: Field) -> (Lists::List<Lists::List<BN254G1::Point>>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {let (width, input) = KzgIO::u32(input); let (head, input) = points(input, width);
        let (tail, input) = point_rows(input, count - 1); (&(Lists::Node::Cons(head, tail)), input)},
    }
  }

  fn opening_matrices(input: Bytes::Stream, count: Field) -> (Lists::List<Lists::List<Lists::List<Field>>>, Bytes::Stream) {
    match count {
      0 => (&(Lists::Node::Nil), input),
      _ => {let (width, input) = KzgIO::u32(input); let (head, input) = scalar_rows(input, width);
        let (tail, input) = opening_matrices(input, count - 1); (&(Lists::Node::Cons(head, tail)), input)},
    }
  }

  fn commitment(input: Bytes::Stream) -> (Commitment, Bytes::Stream) {
    let (count, input) = KzgIO::u32(input); point_rows(input, count)
  }
  fn openings(input: Bytes::Stream) -> (Openings, Bytes::Stream) {
    let (count, input) = KzgIO::u32(input); opening_matrices(input, count)
  }

  fn key(input: Bytes::Stream) -> Key {
    let input = KzgIO::magic(input, [73,88,65,85,75,89,48,49]);
    let (seed, input) = KzgIO::blob(input);
    let (max_log, input) = KzgIO::u32(input);
    assert_eq!(UInt32::less_than_fields(max_log, 29), 1, "KZG trace cap exceeds Fr domain");
    assert_eq!(UInt32::less_than_fields(0, max_log), 1, "KZG trace cap below two rows");
    let (budget, input) = KzgIO::u32(input);
    supported_power(budget, 1, 28);
    let (generator, input) = KzgIO::point(input);
    let (anchors, input) = KzgIO::read_bytes(input, 128);
    let (count, input) = KzgIO::u32(input);
    assert_eq!(Fields::is_zero(count), 0, "empty KZG system");
    let (circuits, input) = circuits(input, count, budget);
    let (tag, input) = KzgIO::tag(input);
    match tag {
      0 => {KzgIO::finish(input); Key::Mk(seed, max_log, budget, generator, anchors, circuits, Fixed::None)},
      1 => {let (fixed, input) = commitment(input); KzgIO::finish(input);
        Key::Mk(seed, max_log, budget, generator, anchors, circuits, Fixed::Some(fixed))},
    }
  }

  fn proof(input: Bytes::Stream) -> Proof {
    let input = KzgIO::magic(input, [73,88,65,85,80,70,48,49]);
    let (count, input) = KzgIO::u32(input); let (active, input) = tags(input, count);
    let (count, input) = KzgIO::u32(input); let (logs, input) = tags(input, count);
    let (main, input) = commitment(input); let (stage2, input) = commitment(input);
    let (quotient, input) = commitment(input);
    let (count, input) = KzgIO::u32(input); let (accumulators, input) = scalars(input, count);
    let (count, input) = KzgIO::u32(input); let (witnesses, input) = points(input, count);
    let (main_open, input) = openings(input); let (stage2_open, input) = openings(input);
    let (quotient_open, input) = openings(input);
    let (tag, input) = KzgIO::tag(input);
    match tag {
      0 => {KzgIO::finish(input); Proof::Mk(active,logs,main,stage2,quotient,accumulators,witnesses,main_open,stage2_open,quotient_open,FixedOpen::None)},
      1 => {let (fixed_open, input) = openings(input); KzgIO::finish(input);
        Proof::Mk(active,logs,main,stage2,quotient,accumulators,witnesses,main_open,stage2_open,quotient_open,FixedOpen::Some(fixed_open))},
    }
  }

  fn claims(input: Bytes::Stream) -> Lists::List<Lists::List<Field>> {
    let input = KzgIO::magic(input, [73,88,65,85,67,76,48,49]);
    let (count, input) = KzgIO::u32(input);
    let (claims, input) = scalar_rows(input, count); KzgIO::finish(input); claims
  }

  fn policy(input: Bytes::Stream) -> Policy {
    let input = KzgIO::magic(input, [73,88,65,85,75,76,48,49]);
    let (anchors, input) = KzgIO::read_bytes(input, 128);
    let (gl_digest, input) = KzgIO::digest(input); let (gl_entry, input) = KzgIO::u32(input);
    let (bn_digest, input) = KzgIO::digest(input); let (bn_entry, input) = KzgIO::u32(input);
    KzgIO::finish(input); Policy::Mk(anchors,gl_digest,gl_entry,bn_digest,bn_entry)
  }
}
⟧

end MultiStark.Source
