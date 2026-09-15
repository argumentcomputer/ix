use super::super::{NaturalCapacity, scalar_payload_tests};
use super::*;
use crate::{
  blake3_backend::{Blake3Backend, Blake3CompressionSlots},
  ixby::bits::fill_words,
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{circuit::builder::ShapeBuilder, field::F128};
pub(super) fn checked(g: &CodeGate, input: &[F128]) -> Vec<F128> {
  let out = relation::evaluate(g, input);
  assert_eq!(
    crate::ixby::bits::evaluate_words(g.plan(), input, g.output_count()),
    out,
    "{:?} {:?} {input:?}",
    g.kind(),
    g.op()
  );
  out
}
fn layout() -> CodeLayout {
  CodeLayout::new(2, 2, 2, 3, NaturalCapacity::new(127).unwrap()).unwrap()
}
fn request(c: CodeLayout, kind: CodeKind) -> Vec<F128> {
  let mut q = vec![F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO];
  let address = c.address(kind);
  let bounds = c.bounds(kind);
  for i in 0..3 {
    if address[i + 1] != 0 {
      q[i + 1] = F128::new(bounds[i].saturating_sub(1), 0);
    }
  }
  q
}
fn sample(g: &CodeGate) -> Vec<F128> {
  if g.op() == CodeOp::Request {
    return request(g.layout(), g.kind());
  }
  let mut input = vec![F128::ZERO; g.input_count()];
  input[0] = F128::ONE;
  for (i, v) in
    input[1..=g.layout().record_words(g.kind())].iter_mut().enumerate()
  {
    *v = F128::new(17 + i as u64, 31 + i as u64);
  }
  if g.kind() == CodeKind::Program {
    input[4] = F128::new(super::super::grammar::Phase::Done as u64, 0);
  } else {
    input[1] = F128::ONE;
  }
  input
}
#[test]
fn code_relations_cover_full_width_indices_controls_and_record_outputs() {
  for kind in CodeKind::ALL {
    for op in [CodeOp::Request, CodeOp::Record] {
      let g = CodeGate::new(3, layout(), kind, op).unwrap();
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
      super::super::tests::output_bits_are_bound(
        &r1cs,
        &mut bits,
        input.len() * 128,
        out.len() * 128,
      );
      bits[g.plan().k() - 1] = true;
      assert!(!super::super::tests::satisfies(&r1cs, &bits));
      for n in [0, 1, 5] {
        let rows = vec![CodeRow(input.clone()); n];
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
fn code_requests_reject_aliasing_bounds_overflow_and_disabled_advice() {
  let c = layout();
  for kind in CodeKind::ALL {
    let g = CodeGate::new(3, c, kind, CodeOp::Request).unwrap();
    let q = request(c, kind);
    let out = checked(&g, &q);
    assert_eq!(
      out[0],
      F128::new(
        fixtures::offset(c, kind, q.as_slice().try_into().unwrap()),
        c.bytes()
      )
    );
    assert_eq!(out[1], F128::new((c.record_words(kind) * 16) as u64, 0));
    for at in 1..4 {
      for v in [
        F128::new(u32::MAX as u64, 0),
        F128::new(u64::MAX, 0),
        F128::new(0, 1),
        F128::new(0, 1 << 63),
        F128::new(u64::MAX, u64::MAX),
      ] {
        let mut bad = q.clone();
        bad[at] = v;
        assert_eq!(checked(&g, &bad).last(), Some(&F128::ONE));
      }
    }
    let disabled = [F128::ZERO; 4];
    let out = checked(&g, &disabled);
    assert_eq!(out.last(), Some(&F128::ZERO));
    assert_eq!(out[0], F128::new(0, c.bytes()));
    assert_eq!(out[1], F128::ZERO);
    for at in 1..4 {
      let mut bad = disabled;
      bad[at] = F128::ONE;
      assert_eq!(checked(&g, &bad).last(), Some(&F128::ONE));
    }
    let g = CodeGate::new(3, c, kind, CodeOp::Record).unwrap();
    let mut absent = vec![F128::ZERO; g.input_count()];
    absent[0] = F128::ONE;
    assert_eq!(checked(&g, &absent).last(), Some(&F128::ONE));
    absent[0] = F128::ZERO;
    assert!(checked(&g, &absent).iter().all(|v| *v == F128::ZERO));
    for at in 1..absent.len() {
      let mut bad = absent.clone();
      bad[at] = F128::ONE;
      assert_eq!(checked(&g, &bad).last(), Some(&F128::ONE));
    }
  }
  let empty =
    CodeLayout::new(0, 1, 1, 1, NaturalCapacity::new(0).unwrap()).unwrap();
  for kind in [CodeKind::Constructor, CodeKind::Alternative] {
    let g = CodeGate::new(3, empty, kind, CodeOp::Request).unwrap();
    assert_eq!(
      checked(&g, &[F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO]).last(),
      Some(&F128::ONE)
    );
  }
  for bad in [
    (0, 0, 1, 1),
    (0, 1, 0, 1),
    (0, 1, 1, 0),
    (u64::MAX, 1, 1, 1),
    (1, u64::MAX, 1, 1),
    (u32::MAX as u64, u32::MAX as u64, u32::MAX as u64, u32::MAX as u64),
  ] {
    assert!(CodeLayout::new(bad.0, bad.1, bad.2, bad.3, c.natural()).is_err());
  }
  for nu in [0, 2, 21, usize::MAX] {
    assert!(CodeGate::new(nu, c, CodeKind::Block, CodeOp::Request).is_err());
  }
}

fn access_only(
  b: &mut impl CircuitEmitter,
  nu: usize,
  c: CodeLayout,
) -> (CodeAccessSlots, flock_prover::circuit::builder::SlotId) {
  let compression =
    Blake3CompressionSlots::declare(b, nu, Blake3Backend::LegacyOptionF)
      .unwrap();
  let Blake3CompressionSlots::LegacyOptionF { slot, .. } = compression else {
    unreachable!()
  };
  let access = CodeAccessSlots::declare(b, nu, c, &compression).unwrap();
  let root = [b.input(), b.input()];
  let length = b.fixed_public_input(F128::new(c.bytes(), 0));
  let code = SealedCode::expected(c, root, length);
  let q = std::array::from_fn(|_| b.input());
  let request = access.request(b, CodeKind::Operand, q);
  let indices = request.chunk_indices();
  let chunks: Vec<_> = indices
    .into_iter()
    .map(|index| {
      let p = fixtures::proof_wires(b, c.depth());
      access.authenticate(b, &code, index, &p)
    })
    .collect();
  let read = access.read(b, &code, &request, [&chunks[0], &chunks[1]]);
  for w in read.fields {
    b.publish(w);
  }
  (access, slot)
}

#[test]
fn single_chunk_code_reads_bind_root_flags_and_final_padding() {
  use super::super::{
    bodies::{self, BodyCapacity},
    registry::RegistryCapacity,
  };
  use crate::ixby::{bounded_hash::tests as hash_tests, io::LayoutEmitter};
  let c = BodyCapacity::new(
    RegistryCapacity::new(0, 1, 1).unwrap(),
    NaturalCapacity::new(0).unwrap(),
    1,
  )
  .unwrap();
  let layout = CodeLayout::from_bodies(c);
  assert_eq!((layout.bytes(), layout.depth()), (1008, 0));
  let f = fixtures::Fixture::new(
    c,
    bodies::fixtures::encode(
      c,
      "single-chunk",
      &bodies::fixtures::base(),
      false,
    ),
  );
  let mut builder = ShapeBuilder::new(5);
  let mut b = LayoutEmitter::new(&mut builder);
  let (_, compression) = access_only(&mut b, 5, layout);
  let (inputs, public) = b.finish();
  let shape = builder.finish().unwrap();
  let mut private = hash_tests::expected(&f.image).to_vec();
  private.extend([F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO]);
  for _ in 0..2 {
    private.extend(super::super::source::test_chunk_advice(&f.image, 0, 0));
  }
  let run = |p: &[F128]| shape.run(&inputs.assign(p).unwrap(), &[]);
  let w = run(&private);
  assert_eq!(w.public, public.instantiate(&f.records[5]).unwrap());
  let rows = w.rows::<crate::hash::Blake3Gate>(compression);
  assert_eq!(rows.len(), 32);
  for row in [&rows[15], &rows[31]] {
    assert_eq!(row.3, 48);
    assert_eq!(row.4, crate::hash::CHUNK_END | crate::hash::ROOT);
  }
  for at in [6 + 63, 6 + 64 + 63] {
    let mut p = private.clone();
    p[at].lo ^= 1;
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&p)))
        .is_err()
    );
  }
}
#[test]
fn code_access_shapes_scale_with_path_depth_and_keep_counting_lazy() {
  let n = NaturalCapacity::new(4096).unwrap();
  for c in [
    CodeLayout::new(0, 1, 1, 1, n).unwrap(),
    CodeLayout::new(2, 2, 2, 3, n).unwrap(),
    CodeLayout::new(4, 1024, 128, 4, n).unwrap(),
    CodeLayout::new(4, u32::MAX as u64, 1, 4, n).unwrap(),
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
    assert_eq!(
      shape.counts[shape.registry_slot(access.source_slots().window_gate().0)],
      1
    );
    for op in [CodeOp::Request, CodeOp::Record] {
      let g = CodeGate::new(3, c, CodeKind::Operand, op).unwrap();
      let mut count = CountingEmitter::new();
      let slot = count.slot(g.clone());
      let input: Vec<_> = (0..g.input_count()).map(|_| count.input()).collect();
      count.gate(slot, &input);
      assert!(g.plan.get().is_none());
      let input = sample(&g);
      assert_eq!(checked(&g, &input).last(), Some(&F128::ZERO));
      for at in 1..4 {
        if op == CodeOp::Request {
          let mut wrong = input.clone();
          wrong[at] = F128::new(u64::MAX, u64::MAX);
          checked(&g, &wrong);
        }
      }
    }
    eprintln!(
      "code access census bytes={} depth={} compression={} query_words=4 record_words={}",
      c.bytes(),
      c.depth(),
      2 * (16 + c.depth()),
      c.record_words(CodeKind::Operand)
    );
  }
}

#[test]
fn reused_code_handles_reject_other_roots_addresses_and_missing_records() {
  use super::super::{bodies::BodyCapacity, registry::RegistryCapacity};
  use crate::ixby::{bounded_hash::tests as hash_tests, io::LayoutEmitter};
  let c = BodyCapacity::new(
    RegistryCapacity::new(2, 2, 2).unwrap(),
    NaturalCapacity::new(4096).unwrap(),
    3,
  )
  .unwrap();
  let layout = CodeLayout::from_bodies(c);
  let f = fixtures::corpus(c).into_iter().find(|f| f.name == "zero").unwrap();
  let root = hash_tests::expected(&f.image);
  for (kind, record) in
    [(CodeKind::Program, 0), (CodeKind::Function, 2), (CodeKind::Operand, 5)]
  {
    let mut builder = ShapeBuilder::new(6);
    let mut b = LayoutEmitter::new(&mut builder);
    let compression =
      Blake3CompressionSlots::declare(&mut b, 6, Blake3Backend::LegacyOptionF)
        .unwrap();
    let access =
      CodeAccessSlots::declare(&mut b, 6, layout, &compression).unwrap();
    let root_a = [b.input(), b.input()];
    let root_b = [b.input(), b.input()];
    let length = b.fixed_public_input(F128::new(layout.bytes(), 0));
    let a = SealedCode::expected(layout, root_a, length);
    let other = SealedCode::expected(layout, root_b, length);
    let indices = [b.input(), b.input()];
    let query = std::array::from_fn(|_| b.input());
    let request = access.request(&mut b, kind, query);
    let chunks = indices.map(|index| {
      let proof = fixtures::proof_wires(&mut b, layout.depth());
      access.authenticate(&mut b, &a, index, &proof)
    });
    for code in [&a, &other] {
      for word in
        access.read(&mut b, code, &request, [&chunks[0], &chunks[1]]).fields
      {
        b.publish(word);
      }
    }
    let (inputs, public) = b.finish();
    let shape = builder.finish().unwrap();
    let proof_words = 64 + 2 * layout.depth();
    for enabled in [true, false] {
      let q = if enabled { f.requests[record] } else { [F128::ZERO; 4] };
      let offset = fixtures::offset(layout, kind, &q);
      let first = offset / 1024;
      let next = (first + 1).min((layout.bytes() - 1) / 1024);
      let mut private = root.into_iter().chain(root).collect::<Vec<_>>();
      private.extend([F128::new(first, 0), F128::new(next, 0)]);
      private.extend(q);
      for index in [first, next] {
        private.extend(super::super::source::test_chunk_advice(
          &f.image,
          index as usize,
          layout.depth(),
        ));
      }
      let run = |p: &[F128]| shape.run(&inputs.assign(p).unwrap(), &[]);
      let w = run(&private);
      let expected = if enabled {
        f.records[record].repeat(2)
      } else {
        vec![F128::ZERO; layout.record_words(kind) * 2]
      };
      assert_eq!(w.public, public.instantiate(&expected).unwrap());
      let source = access.source_slots();
      assert_eq!(
        w.rows::<super::super::source::SourceBlockGate>(source.block_gate().0)
          .len(),
        32
      );
      assert_eq!(
        w.rows::<super::super::source::SourceWindowGate>(
          source.window_gate().0
        )
        .len(),
        2
      );
      let mut bad = Vec::new();
      let mut p = private.clone();
      p[2].lo ^= 1;
      bad.push(("other root", p));
      let mut p = private.clone();
      p[4].hi ^= 1;
      bad.push(("wide index", p));
      let mut p = private.clone();
      p[10].lo ^= 1;
      bad.push(("chunk bytes", p));
      let mut p = private.clone();
      p[10 + 64].lo ^= 1;
      bad.push(("sibling", p));
      let mut p = private.clone();
      p.swap(4, 5);
      for i in 0..proof_words {
        p.swap(10 + i, 10 + proof_words + i);
      }
      bad.push(("valid swapped handles", p));
      if enabled && kind != CodeKind::Program {
        let mut p = private.clone();
        p[if kind == CodeKind::Function { 7 } else { 9 }] = F128::ONE;
        bad.push(("absent physical record", p));
      }
      for (name, p) in bad {
        assert!(
          std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&p)))
            .is_err(),
          "{kind:?} enabled={enabled} {name}"
        );
      }
    }
  }
}
