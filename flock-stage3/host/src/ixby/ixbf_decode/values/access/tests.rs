use super::super::super::{GrammarKind, NaturalCapacity, scalar_payload_tests};
use super::*;
use crate::{
  blake3_backend::{Blake3Backend, Blake3CompressionSlots},
  ixby::{
    bits::fill_words, bounded_hash::tests as hash_tests, io::LayoutEmitter,
  },
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{ShapeBuilder, SlotId},
  field::F128,
};

pub(super) fn checked(g: &ValueAccessGate, input: &[F128]) -> Vec<F128> {
  let out = relation::evaluate(g, input);
  assert_eq!(
    crate::ixby::bits::evaluate_words(g.plan(), input, g.output_count()),
    out,
    "{:?} {:?}: {input:?}",
    g.kind(),
    g.op()
  );
  out
}
fn layout() -> ValueLayout {
  ValueLayout::new(GrammarKind::Input, 4, 4, NaturalCapacity::new(127).unwrap())
    .unwrap()
}
fn sample(g: &ValueAccessGate) -> Vec<F128> {
  let mut input = vec![F128::ZERO; g.input_count()];
  input[0] = F128::ONE;
  let last = g.layout().nodes() - 1;
  match g.kind() {
    ValueKind::Manifest => {},
    ValueKind::Node => input[1] = F128::new(last.min(3), 0),
    ValueKind::Child => {
      input[1] = F128::new(last.min(1), 0);
      input[2] = input[1];
      input[3] = F128::new(last.min(3), 0);
    },
    ValueKind::Root => {
      input[2] = F128::new(last.min(1), 0);
      input[3] = F128::new(last.min(3), 0);
    },
  }
  if g.op() == ValueAccessOp::Record {
    for (i, w) in
      input[4..4 + g.layout().record_words(g.kind())].iter_mut().enumerate()
    {
      *w = F128::new(17 + i as u64, 31 + i as u64);
    }
    if g.kind() == ValueKind::Manifest {
      input[9] = F128::new(super::super::super::grammar::Phase::Done as u64, 0);
    } else {
      input[4] = F128::ONE;
      let at = 4 + g.layout().tree_start();
      input[at] = if g.kind() == ValueKind::Child {
        F128::new(input[1].lo + 1, 0)
      } else {
        F128::ZERO
      };
      input[at + 1] = input[2];
    }
  }
  input
}
#[test]
fn access_relations_bind_full_width_queries_locators_and_all_output_bits() {
  for kind in ValueKind::ALL {
    for op in [ValueAccessOp::Request, ValueAccessOp::Record] {
      let g = ValueAccessGate::new(3, layout(), kind, op).unwrap();
      let input = sample(&g);
      assert_eq!(checked(&g, &input).last(), Some(&F128::ZERO));
      for at in 0..input.len() {
        for bit in [0, 31, 63, 64, 100, 127] {
          let mut wrong = input.clone();
          if bit < 64 {
            wrong[at].lo ^= 1 << bit;
          } else {
            wrong[at].hi ^= 1 << (bit - 64);
          }
          checked(&g, &wrong);
        }
      }
      for byte in 0..=255 {
        let mut wrong = input.clone();
        wrong[0] = F128::new(byte, 0);
        checked(&g, &wrong);
      }
      let out = checked(&g, &input);
      let r1cs = g.r1cs();
      let mut bits =
        scalar_payload_tests::checked(g.plan(), &r1cs, &input, &out);
      super::super::super::tests::output_bits_are_bound(
        &r1cs,
        &mut bits,
        input.len() * 128,
        out.len() * 128,
      );
      bits[g.plan().k() - 1] = true;
      assert!(!super::super::super::tests::satisfies(&r1cs, &bits));
      for n in [0, 1, 5] {
        let rows = vec![ValueAccessRow(input.clone()); n];
        crate::ixby::test_support::padding(
          g.plan(),
          &rows,
          |r, bits| fill_words(&r.0, bits),
          |dst| g.generate_witness_into(&rows, dst),
        );
      }
    }
  }
}
#[test]
fn access_rejects_bounds_overflow_missing_nodes_bad_tree_metadata_and_disabled_advice()
 {
  let c = layout();
  for kind in ValueKind::ALL {
    for op in [ValueAccessOp::Request, ValueAccessOp::Record] {
      let g = ValueAccessGate::new(3, c, kind, op).unwrap();
      let input = sample(&g);
      for at in 1..4 {
        for value in [
          F128::new(4, 0),
          F128::new(u32::MAX as u64, 0),
          F128::new(u64::MAX, 0),
          F128::new(0, 1),
          F128::new(0, 1 << 63),
          F128::new(u64::MAX, u64::MAX),
        ] {
          let mut wrong = input.clone();
          wrong[at] = value;
          assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
        }
      }
      let disabled = vec![F128::ZERO; g.input_count()];
      assert_eq!(checked(&g, &disabled).last(), Some(&F128::ZERO));
      for at in 1..disabled.len() {
        let mut wrong = disabled.clone();
        wrong[at] = F128::ONE;
        assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
      }
      if op == ValueAccessOp::Record {
        let mut absent = vec![F128::ZERO; g.input_count()];
        absent[0] = F128::ONE;
        assert_eq!(checked(&g, &absent).last(), Some(&F128::ONE));
        if matches!(kind, ValueKind::Child | ValueKind::Root) {
          for at in [4 + c.tree_start(), 5 + c.tree_start()] {
            for bit in 0..128 {
              let mut wrong = input.clone();
              if bit < 64 {
                wrong[at].lo ^= 1 << bit;
              } else {
                wrong[at].hi ^= 1 << (bit - 64);
              }
              assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
            }
          }
        }
      } else {
        let out = checked(&g, &input);
        assert_eq!(
          out[0],
          F128::new(
            fixtures::offset(c, kind, input.as_slice().try_into().unwrap()),
            c.bytes()
          )
        );
      }
    }
  }
  for (kind, nodes, depth) in [
    (GrammarKind::Program, 1, 1),
    (GrammarKind::Input, 0, 0),
    (GrammarKind::Input, 1, 0),
    (GrammarKind::Output, 2, 3),
    (GrammarKind::Input, u32::MAX as u64 + 1, 1),
  ] {
    assert!(ValueLayout::new(kind, nodes, depth, c.natural()).is_err());
  }
  for nu in [0, 2, 21, usize::MAX] {
    assert!(
      ValueAccessGate::new(nu, c, ValueKind::Node, ValueAccessOp::Request)
        .is_err()
    );
  }
}
fn access_only(
  b: &mut impl CircuitEmitter,
  nu: usize,
  c: ValueLayout,
) -> (ValueAccessSlots, SlotId) {
  let compression =
    Blake3CompressionSlots::declare(b, nu, Blake3Backend::LegacyOptionF)
      .unwrap();
  let Blake3CompressionSlots::LegacyOptionF { slot, .. } = compression else {
    unreachable!()
  };
  let access = ValueAccessSlots::declare(b, nu, c, &compression).unwrap();
  let root = [b.input(), b.input()];
  let length = b.fixed_public_input(F128::new(c.bytes(), 0));
  let values = SealedValues::expected(c, root, length);
  let query = std::array::from_fn(|_| b.input());
  let request = access.request(b, ValueKind::Node, query);
  let chunks = request.chunk_indices().map(|index| {
    let proof = fixtures::proof_wires(b, c.depth());
    access.authenticate(b, &values, index, &proof)
  });
  let read = access.read(b, &values, &request, [&chunks[0], &chunks[1]]);
  b.publish(read.index);
  for word in read.record {
    b.publish(word);
  }
  (access, slot)
}
#[test]
fn large_value_access_counts_stay_lazy_and_scale_with_path_depth() {
  let n = NaturalCapacity::new(4096).unwrap();
  for c in [
    ValueLayout::new(GrammarKind::Input, 1, 1, n).unwrap(),
    ValueLayout::new(GrammarKind::Input, 4, 4, n).unwrap(),
    ValueLayout::new(GrammarKind::Output, 1_000_000, 1024, n).unwrap(),
    ValueLayout::new(GrammarKind::Input, u32::MAX as u64, u32::MAX as u64, n)
      .unwrap(),
  ] {
    let mut count = CountingEmitter::new();
    access_only(&mut count, 3, c);
    let nu = count.required_nu(3).unwrap();
    let mut builder = ShapeBuilder::new(nu);
    let (access, compression) = access_only(&mut builder, nu, c);
    let shape = builder.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    assert_eq!(
      shape.counts[shape.registry_slot(compression)],
      2 * (16 + c.depth())
    );
    assert_eq!(
      shape.counts[shape.registry_slot(access.source_slots().block_gate().0)],
      32
    );
    assert_eq!(
      shape.counts[shape.registry_slot(access.source_slots().path_gate().0)],
      2 * c.depth()
    );
    for kind in ValueKind::ALL {
      for op in [ValueAccessOp::Request, ValueAccessOp::Record] {
        let g = ValueAccessGate::new(nu, c, kind, op).unwrap();
        let mut lazy = CountingEmitter::new();
        let slot = lazy.slot(g.clone());
        let input: Vec<_> =
          (0..g.input_count()).map(|_| lazy.input()).collect();
        lazy.gate(slot, &input);
        assert!(g.plan.get().is_none());
        let input = sample(&g);
        assert_eq!(checked(&g, &input).last(), Some(&F128::ZERO));
        if op == ValueAccessOp::Request {
          let last = F128::new(c.nodes() - 1, 0);
          let q = match kind {
            ValueKind::Manifest => {
              [F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO]
            },
            ValueKind::Node => [F128::ONE, last, F128::ZERO, F128::ZERO],
            ValueKind::Child => [F128::ONE, last, last, last],
            ValueKind::Root => [F128::ONE, F128::ZERO, last, last],
          };
          let out = checked(&g, &q);
          assert_eq!(out.last(), Some(&F128::ZERO));
          assert_eq!(
            out[0],
            F128::new(fixtures::offset(c, kind, &q), c.bytes())
          );
          if kind != ValueKind::Manifest {
            assert_eq!(out[0].lo + out[1].lo, c.bytes());
          }
        }
      }
    }
    eprintln!(
      "value access census nodes={} bytes={} depth={} compression={} node_words={}",
      c.nodes(),
      c.bytes(),
      c.depth(),
      2 * (16 + c.depth()),
      c.node_words()
    );
  }
}
#[test]
fn single_chunk_value_reads_bind_final_byte_length_flags_and_padding() {
  use super::super::super::{bodies::BodyCapacity, registry::RegistryCapacity};
  use super::super::{ValueCapacity, ValueConfig};
  let config = ValueConfig {
    kind: GrammarKind::Output,
    registry: RegistryCapacity::new(2, 2, 2).unwrap(),
    arena: ValueCapacity::new(1, 1, NaturalCapacity::new(0).unwrap()).unwrap(),
  };
  let c = ValueLayout::from_arena(config);
  assert_eq!((c.bytes(), c.depth()), (864, 0));
  let body =
    BodyCapacity::new(config.registry, NaturalCapacity::new(4096).unwrap(), 3)
      .unwrap();
  let forest = super::super::fixtures::encode(
    config.kind,
    config.arena,
    &super::super::fixtures::spec(1),
    &[super::super::fixtures::Value::Erased],
  );
  let f = fixtures::Fixture::new(config, body, "single-chunk", forest);
  let mut builder = ShapeBuilder::new(5);
  let mut b = LayoutEmitter::new(&mut builder);
  let (_, compression) = access_only(&mut b, 5, c);
  let (inputs, public) = b.finish();
  let shape = builder.finish().unwrap();
  let mut private = hash_tests::expected(&f.image).to_vec();
  private.extend([F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO]);
  for _ in 0..2 {
    private
      .extend(super::super::super::source::test_chunk_advice(&f.image, 0, 0));
  }
  let run = |p: &[F128]| shape.run(&inputs.assign(p).unwrap(), &[]);
  let w = run(&private);
  assert_eq!(w.public, public.instantiate(&f.records[1]).unwrap());
  let rows = w.rows::<crate::hash::Blake3Gate>(compression);
  for row in [&rows[13], &rows[29]] {
    assert_eq!(row.3, 32);
    assert_eq!(row.4, crate::hash::CHUNK_END | crate::hash::ROOT);
  }
  for at in [6 + 53, 6 + 54, 6 + 64 + 53, 6 + 64 + 54] {
    let mut wrong = private.clone();
    wrong[at].lo ^= 1;
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&wrong)))
        .is_err()
    );
  }
}

#[test]
fn cached_values_reject_cross_root_handles_and_authenticate_locator_candidates()
{
  use super::super::super::{
    bodies::BodyCapacity, registry::RegistryCapacity, source::*,
  };
  use super::super::{ValueCapacity, ValueConfig};
  let config = ValueConfig {
    kind: GrammarKind::Input,
    registry: RegistryCapacity::new(2, 2, 2).unwrap(),
    arena: ValueCapacity::new(4, 4, NaturalCapacity::new(4096).unwrap())
      .unwrap(),
  };
  let c = ValueLayout::from_arena(config);
  let body = BodyCapacity::new(config.registry, c.natural(), 3).unwrap();
  let fixtures = fixtures::corpus(config, body);
  let nested = fixtures.iter().find(|f| f.name == "nested").unwrap();
  let multiple = fixtures.iter().find(|f| f.name == "multiple-roots").unwrap();
  let erased = fixtures.iter().find(|f| f.name == "erased").unwrap();
  for kind in ValueKind::ALL {
    let mut builder = ShapeBuilder::new(6);
    let mut b = LayoutEmitter::new(&mut builder);
    let compression =
      Blake3CompressionSlots::declare(&mut b, 6, Blake3Backend::LegacyOptionF)
        .unwrap();
    let access = ValueAccessSlots::declare(&mut b, 6, c, &compression).unwrap();
    let root_a = [b.input(), b.input()];
    let root_b = [b.input(), b.input()];
    let length = b.fixed_public_input(F128::new(c.bytes(), 0));
    let a = SealedValues::expected(c, root_a, length);
    let other = SealedValues::expected(c, root_b, length);
    let indices = [b.input(), b.input()];
    let query = std::array::from_fn(|_| b.input());
    let request = access.request(&mut b, kind, query);
    let chunks = indices.map(|index| {
      let proof = fixtures::proof_wires(&mut b, c.depth());
      access.authenticate(&mut b, &a, index, &proof)
    });
    for values in [&a, &other] {
      let read =
        access.read(&mut b, values, &request, [&chunks[0], &chunks[1]]);
      b.publish(read.index);
      for w in read.record {
        b.publish(w);
      }
    }
    let (inputs, public) = b.finish();
    let shape = builder.finish().unwrap();
    let f = if kind == ValueKind::Root { multiple } else { nested };
    let active = match kind {
      ValueKind::Manifest => [1, 0, 0, 0],
      ValueKind::Node => [1, 3, 0, 0],
      ValueKind::Child => [1, 1, 0, 2],
      ValueKind::Root => [1, 0, 1, 2],
    }
    .map(|v| F128::new(v, 0));
    let make = |f: &fixtures::Fixture, query: [F128; 4]| {
      let root = hash_tests::expected(&f.image);
      let mut p = root.into_iter().chain(root).collect::<Vec<_>>();
      let first = fixtures::offset(c, kind, &query) / 1024;
      let next = (first + 1).min((c.bytes() - 1) / 1024);
      p.extend([F128::new(first, 0), F128::new(next, 0)]);
      p.extend(query);
      for index in [first, next] {
        p.extend(test_chunk_advice(&f.image, index as usize, c.depth()));
      }
      p
    };
    let run = |p: &[F128]| shape.run(&inputs.assign(p).unwrap(), &[]);
    for enabled in [true, false] {
      let query = if enabled { active } else { [F128::ZERO; 4] };
      let private = make(f, query);
      let w = run(&private);
      let expected = if !enabled {
        vec![F128::ZERO; 1 + c.record_words(kind)]
      } else if kind == ValueKind::Manifest {
        f.records[0].clone()
      } else {
        let i = query[if kind == ValueKind::Node { 1 } else { 3 }].lo as usize;
        std::iter::once(F128::new(i as u64, 0))
          .chain(f.forest.records[i].clone())
          .collect()
      };
      assert_eq!(w.public, public.instantiate(&expected.repeat(2)).unwrap());
      assert_eq!(
        w.rows::<SourceBlockGate>(access.source_slots().block_gate().0).len(),
        32
      );
      assert_eq!(
        w.rows::<SourceWindowGate>(access.source_slots().window_gate().0).len(),
        2
      );
      let mut cases = Vec::new();
      for (name, at) in
        [("other root", 2), ("chunk bytes", 10), ("path sibling", 10 + 64)]
      {
        let mut p = private.clone();
        p[at].lo ^= 1;
        cases.push((name, p));
      }
      let mut p = private.clone();
      p[4].hi ^= 1;
      cases.push(("wide handle index", p));
      let mut p = private.clone();
      p.swap(4, 5);
      let width = 64 + 2 * c.depth();
      for i in 0..width {
        p.swap(10 + i, 10 + width + i);
      }
      cases.push(("valid swapped handles", p));
      if enabled && matches!(kind, ValueKind::Child | ValueKind::Root) {
        let mut wrong = query;
        wrong[3] = F128::ONE;
        cases.push(("authenticated wrong locator", make(f, wrong)));
        let mut wrong = query;
        wrong[2].lo ^= 1;
        cases.push(("wrong ordinal", make(f, wrong)));
      }
      if enabled && kind == ValueKind::Node {
        let wrong = [F128::ONE, F128::ONE, F128::ZERO, F128::ZERO];
        cases.push(("authenticated absent node", make(erased, wrong)));
      }
      for (name, p) in cases {
        assert!(
          std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&p)))
            .is_err(),
          "{kind:?} enabled={enabled}: {name}"
        );
      }
    }
  }
}
