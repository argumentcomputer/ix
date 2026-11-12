import Aiur.Modules.Frontend

/-! Activation, domain and opening-shape checks for the Aiur KZG adapter.
Fixed tables remain active on their compiled domains; padded total rows are
bounded by 2^39 and the conservative lookup budget fits a u64 integer. -/
namespace MultiStark.Source

def kzgShape : Aiur.Modules.Program Nat := aiur⟦
module KzgShape {
  type Points = Lists::List<BN254G1::Point>;
  type Rows = Lists::List<Lists::List<Field>>;
  type Commitment = KzgDeserialize::Commitment;
  type Openings = KzgDeserialize::Openings;
  type Cursor = &(Lists::List<Field>, Commitment, Commitment, Commitment, Lists::List<Field>,
    Openings, Openings, Openings, Commitment, Openings);
  enum Frame { Mk(KzgDeserialize::Circuit, Field, Points, Points, Points, Field, Rows, Rows, Rows, Points, Rows) }

  fn power2(log: Field) -> Field {
    match log { 0 => 1, _ => 2 * power2(log - 1) }
  }

  fn power_log(value: Field) -> Field {
    match value { 1 => 0, _ => 1 + power_log(value / 2) }
  }

  fn rows_width(rows: Rows, width: Field, count: Field) -> () {
    match count {
      0 => {let Lists::Node::Nil = *rows; ()},
      _ => {let Lists::Node::Cons(row, rest) = *rows;
        assert_eq!(Lists::length(row), width, "KZG opening width"); rows_width(rest, width, count - 1)},
    }
  }

  fn consume(circuit: KzgDeserialize::Circuit, cursor: Cursor, max_log: Field) -> (Frame, Cursor) {
    let KzgDeserialize::Circuit::Mk(shape, _nodes, _roots, _lookups, main_next, fixed_next) = circuit;
    let (logs, main, stage2, quotient, accumulators, main_open, stage2_open, quotient_open, fixed, fixed_open) = *cursor;
    let Lists::Node::Cons(log, logs) = *logs;
    assert_eq!(UInt32::less_than_fields(log, max_log + 1), 1, "KZG trace capacity");
    assert_eq!(UInt32::less_than_fields(log + power_log(shape[7]), 29), 1, "KZG quotient domain");
    let Lists::Node::Cons(main_row, main) = *main;
    let Lists::Node::Cons(stage2_row, stage2) = *stage2;
    let Lists::Node::Cons(quotient_row, quotient) = *quotient;
    let Lists::Node::Cons(next_accumulator, accumulators) = *accumulators;
    let Lists::Node::Cons(main_values, main_open) = *main_open;
    let Lists::Node::Cons(stage2_values, stage2_open) = *stage2_open;
    let Lists::Node::Cons(quotient_values, quotient_open) = *quotient_open;
    assert_eq!(Lists::length(main_row), shape[4], "KZG main commitment width");
    assert_eq!(Lists::length(stage2_row), shape[5], "KZG stage-two commitment width");
    assert_eq!(Lists::length(quotient_row), shape[7], "KZG quotient commitment width");
    rows_width(main_values, shape[4], 1 + main_next);
    rows_width(stage2_values, shape[5], 2);
    rows_width(quotient_values, shape[7], 1);
    match shape[3] {
      0 => {
        let tail = &(logs,main,stage2,quotient,accumulators,main_open,stage2_open,quotient_open,fixed,fixed_open);
        (Frame::Mk(circuit,log,main_row,stage2_row,quotient_row,next_accumulator,main_values,stage2_values,quotient_values,
          &(Lists::Node::Nil),&(Lists::Node::Nil)), tail)
      },
      _ => {
        assert_eq!(shape[2], power2(log), "KZG fixed domain");
        let Lists::Node::Cons(fixed_row, fixed) = *fixed;
        let Lists::Node::Cons(fixed_values, fixed_open) = *fixed_open;
        assert_eq!(Lists::length(fixed_row), shape[3], "KZG fixed commitment width");
        rows_width(fixed_values, shape[3], 1 + fixed_next);
        let tail = &(logs,main,stage2,quotient,accumulators,main_open,stage2_open,quotient_open,fixed,fixed_open);
        (Frame::Mk(circuit,log,main_row,stage2_row,quotient_row,next_accumulator,main_values,stage2_values,quotient_values,fixed_row,fixed_values),tail)
      },
    }
  }

  fn walk(circuits: Lists::List<KzgDeserialize::Circuit>, active: Lists::List<Field>, cursor: Cursor,
      max_log: Field, total_rows: Field, lookup_budget: Field) -> Lists::List<Frame> {
    match (*circuits, *active) {
      (Lists::Node::Nil, Lists::Node::Nil) => {
        let (logs,main,stage2,quotient,accumulators,main_open,stage2_open,quotient_open,fixed,fixed_open) = *cursor;
        let Lists::Node::Nil = *logs; let Lists::Node::Nil = *main;
        let Lists::Node::Nil = *stage2; let Lists::Node::Nil = *quotient;
        let Lists::Node::Nil = *accumulators; let Lists::Node::Nil = *main_open;
        let Lists::Node::Nil = *stage2_open; let Lists::Node::Nil = *quotient_open;
        let Lists::Node::Nil = *fixed; let Lists::Node::Nil = *fixed_open;
        assert_eq!(Fields::is_zero(total_rows), 0, "KZG proof has no active circuits");
        let rows = UInt64::from_field(total_rows);
        assert_eq!(UInt64::to_field(rows), total_rows, "KZG row count exceeds u64");
        let (_, borrow) = UInt64::sub_with_borrow(rows, UInt64::from_field(549755813889));
        assert_eq!(borrow, 1, "KZG total rows exceed 2^39");
        assert_eq!(UInt64::to_field(UInt64::from_field(lookup_budget)), lookup_budget, "KZG lookup budget exceeds u64");
        &(Lists::Node::Nil)
      },
      (Lists::Node::Cons(circuit, rest), Lists::Node::Cons(on, active_rest)) => {
        let KzgDeserialize::Circuit::Mk(shape, _nodes, _roots, lookups, _main_next, _fixed_next) = circuit;
        match on {
          0 => {assert_eq!(shape[2], 0, "inactive KZG fixed table");
            walk(rest,active_rest,cursor,max_log,total_rows,lookup_budget)},
          1 => {
            let (frame,cursor) = consume(circuit,cursor,max_log);
            let Frame::Mk(_c,log,_m,_s,_q,_a,_mo,_so,_qo,_f,_fo) = frame;
            let rows = power2(log);
            let lookup_count = Lists::length(lookups);
            let lookup_count = lookup_count + Fields::is_zero(lookup_count);
            let tail = walk(rest,active_rest,cursor,max_log,total_rows+rows,lookup_budget+rows*lookup_count);
            &(Lists::Node::Cons(frame,tail))
          },
        }
      },
    }
  }

  fn frames(key: KzgDeserialize::Key, proof: KzgDeserialize::Proof) -> Lists::List<Frame> {
    let KzgDeserialize::Key::Mk(_seed,max_log,_budget,_generator,_anchors,circuits,fixed) = key;
    let KzgDeserialize::Proof::Mk(active,logs,main,stage2,quotient,accumulators,_witnesses,main_open,stage2_open,quotient_open,fixed_open) = proof;
    match (fixed,fixed_open) {
      (KzgDeserialize::Fixed::None,KzgDeserialize::FixedOpen::None) =>
        walk(circuits,active,&(logs,main,stage2,quotient,accumulators,main_open,stage2_open,quotient_open,&(Lists::Node::Nil),&(Lists::Node::Nil)),max_log,0,1),
      (KzgDeserialize::Fixed::Some(fixed),KzgDeserialize::FixedOpen::Some(fixed_open)) =>
        walk(circuits,active,&(logs,main,stage2,quotient,accumulators,main_open,stage2_open,quotient_open,fixed,fixed_open),max_log,0,1),
    }
  }
}
⟧

end MultiStark.Source
