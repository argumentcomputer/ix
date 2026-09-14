// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compare checked scopes without allocating values near machine bounds.

use super::{
  block_expressions::write_block, block_rows::block_fixture,
  operation_expressions::write_op, operation_rows::fixtures, *,
};
use crate::emission_checks::check_emission_ops;

fn write_result(out: &mut impl Write, result: Option<usize>) -> io::Result<()> {
  out.write_all(&[u8::from(result.is_some())])?;
  if let Some(value) = result {
    write_u64(out, value as u64)?;
  }
  Ok(())
}

fn edge_blocks() -> Vec<Block> {
  fn ret(index: usize, outputs: Vec<usize>) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Return(index, outputs) }
  }
  fn yielded(index: usize, outputs: Vec<usize>) -> Block {
    Block { ops: vec![], ctrl: Ctrl::Yield(index, outputs) }
  }
  fn continued(arm: Block, size: usize, cont: Block) -> Block {
    Block {
      ops: vec![],
      ctrl: Ctrl::MatchContinue(
        0,
        [(G::ZERO, arm)].into_iter().collect(),
        Some(Box::new(ret(1, vec![]))),
        size,
        0,
        0,
        Box::new(cont),
      ),
    }
  }
  vec![
    ret(0, vec![]),
    ret(0, vec![0]),
    ret(1, vec![]),
    ret(usize::MAX, vec![]),
    yielded(0, vec![]),
    yielded(0, vec![0]),
    Block { ops: vec![], ctrl: Ctrl::Match(0, Default::default(), None) },
    Block { ops: vec![Op::Store(vec![0])], ctrl: Ctrl::Return(0, vec![0]) },
    Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [
          (
            G::ZERO,
            Block {
              ops: vec![Op::Const(G::ONE)],
              ctrl: Ctrl::Return(0, vec![1]),
            },
          ),
          (G::ONE, ret(1, vec![1])),
        ]
        .into_iter()
        .collect(),
        None,
      ),
    },
    continued(yielded(0, vec![0]), 1, ret(2, vec![1])),
    continued(yielded(0, vec![0]), 1, ret(2, vec![2])),
    continued(yielded(0, vec![]), 1, ret(2, vec![1])),
    continued(yielded(0, vec![0, 0]), 1, ret(2, vec![1])),
    continued(ret(0, vec![0]), 0, yielded(2, vec![0])),
    continued(
      continued(yielded(0, vec![0]), 1, yielded(2, vec![1])),
      1,
      ret(3, vec![1]),
    ),
    continued(
      continued(yielded(0, vec![0]), 1, yielded(2, vec![])),
      1,
      ret(3, vec![1]),
    ),
    continued(yielded(0, vec![]), usize::MAX, ret(2, vec![])),
  ]
}

#[test]
fn emission_checks_snapshot() -> io::Result<()> {
  let scopes = [
    0,
    1,
    2,
    3,
    4,
    7,
    8,
    9,
    12,
    16,
    usize::MAX - 8,
    usize::MAX - 1,
    usize::MAX,
  ];
  let mut groups = fixtures();
  for width in [0, 1, 2, 3, 5, 6] {
    groups.push(vec![Op::U32ToField(vec![0; width])]);
    groups.push(vec![Op::UnconstrainedU32Add(vec![0; 4], vec![0; width])]);
    groups.push(vec![Op::UnconstrainedU32Add3(
      vec![0; 4],
      vec![0; width],
      vec![0; 4],
    )]);
  }
  groups.extend([
    vec![Op::AssertEq(vec![0], vec![], None)],
    vec![Op::AssertEq(vec![], vec![0], None)],
    vec![Op::Store(vec![usize::MAX])],
    vec![Op::IORead(0, 0, usize::MAX)],
    vec![Op::Load(usize::MAX, 0)],
    vec![Op::Call(0, vec![], usize::MAX, true)],
  ]);
  let mut out = b"Aiur emission checks v1\n".to_vec();
  write_u64(&mut out, scopes.len() as u64)?;
  for &scope in &scopes {
    write_u64(&mut out, scope as u64)?;
  }
  write_u64(&mut out, groups.len() as u64)?;
  let mut operation_checks = 0;
  for ops in &groups {
    write_u64(&mut out, ops.len() as u64)?;
    for op in ops {
      write_op(&mut out, op)?;
      write_u64(&mut out, op.output_size() as u64)?;
      for &scope in &scopes {
        out.push(u8::from(op.emission_inputs(scope)));
        write_result(
          &mut out,
          check_emission_ops(std::slice::from_ref(op), scope).ok(),
        )?;
        operation_checks += 1;
      }
    }
    for &scope in &scopes {
      write_result(&mut out, check_emission_ops(ops, scope).ok())?;
    }
  }
  let mut blocks = Vec::new();
  for depth in 0..4 {
    for seed in 0..12 {
      let mut selectors = 0;
      let block = block_fixture(depth, seed, 2, &mut selectors);
      blocks.push((block, selectors));
    }
  }
  blocks.extend(edge_blocks().into_iter().map(|block| (block, 4)));
  write_u64(&mut out, blocks.len() as u64)?;
  let mut block_checks = 0;
  for (block, selectors) in &blocks {
    write_block(&mut out, block)?;
    let available = [0, 1, 2, 3, usize::MAX];
    let selectors = [0, selectors.saturating_sub(1), *selectors, selectors + 1];
    let yields = [None, Some(0), Some(1), Some(2), Some(3)];
    write_u64(
      &mut out,
      (available.len() * selectors.len() * yields.len()) as u64,
    )?;
    for available in available {
      for selectors in selectors {
        for yield_size in yields {
          write_u64(&mut out, available as u64)?;
          write_u64(&mut out, selectors as u64)?;
          write_result(&mut out, yield_size)?;
          out.push(u8::from(
            block.check_emission(available, selectors, yield_size).is_ok(),
          ));
          block_checks += 1;
        }
      }
    }
  }
  if let Some(path) = std::env::var_os("IX_EMISSION_CHECK_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "emission checks: {operation_checks} operations, {} sequences, {block_checks} control scopes",
    groups.len() * scopes.len()
  );
  Ok(())
}
