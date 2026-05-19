use std::collections::BTreeSet;

use super::bytecode::{Block, Ctrl, Function, FunctionLayout, Op, ValIdx};

/// Compute the `FunctionLayout` (input_size / selectors / auxiliaries /
/// lookups) of a `Function` by walking its bytecode. Port of
/// `Ix/Aiur/Compiler/Layout.lean::blockLayout`.
pub fn compute_layout(function: &Function) -> FunctionLayout {
  let input_size = function.layout.input_size;
  let mut state = LayoutState::new(input_size);
  state.block_layout(&function.body);
  // Reserve one lookup slot for the function's return lookup (mirrors the
  // `+ 1` added after `blockLayout` in `Concrete.Function.compile`).
  state.function_layout.lookups += 1;
  state.function_layout
}

#[derive(Clone, Copy)]
struct SharedData {
  auxiliaries: usize,
  lookups: usize,
}

impl SharedData {
  fn maximals(self, other: Self) -> Self {
    SharedData {
      auxiliaries: self.auxiliaries.max(other.auxiliaries),
      lookups: self.lookups.max(other.lookups),
    }
  }
}

struct LayoutState {
  function_layout: FunctionLayout,
  #[allow(dead_code)]
  mem_sizes: BTreeSet<usize>,
  degrees: Vec<usize>,
}

impl LayoutState {
  fn new(input_size: usize) -> Self {
    LayoutState {
      function_layout: FunctionLayout {
        input_size,
        selectors: 0,
        auxiliaries: 1,
        lookups: 0,
      },
      mem_sizes: BTreeSet::new(),
      degrees: vec![1; input_size],
    }
  }

  fn bump_selectors(&mut self, n: usize) {
    self.function_layout.selectors += n;
  }

  fn bump_lookups(&mut self, n: usize) {
    self.function_layout.lookups += n;
  }

  fn bump_auxiliaries(&mut self, n: usize) {
    self.function_layout.auxiliaries += n;
  }

  fn add_mem_size(&mut self, size: usize) {
    self.mem_sizes.insert(size);
  }

  fn push_degree(&mut self, d: usize) {
    self.degrees.push(d);
  }

  fn push_degrees(&mut self, ds: &[usize]) {
    self.degrees.extend_from_slice(ds);
  }

  fn get_degree(&self, v: ValIdx) -> usize {
    self.degrees.get(v).copied().unwrap_or(0)
  }

  fn get_shared(&self) -> SharedData {
    SharedData {
      auxiliaries: self.function_layout.auxiliaries,
      lookups: self.function_layout.lookups,
    }
  }

  fn set_shared(&mut self, s: SharedData) {
    self.function_layout.auxiliaries = s.auxiliaries;
    self.function_layout.lookups = s.lookups;
  }

  fn op_layout(&mut self, op: &Op) {
    match op {
      Op::Const(_) => self.push_degree(0),
      Op::Add(a, b) | Op::Sub(a, b) => {
        let d = self.get_degree(*a).max(self.get_degree(*b));
        self.push_degree(d);
      },
      Op::Mul(a, b) => {
        let d = self.get_degree(*a) + self.get_degree(*b);
        if d < 2 {
          self.push_degree(d);
        } else {
          self.push_degree(1);
          self.bump_auxiliaries(1);
        }
      },
      Op::EqZero(a) => {
        let d = self.get_degree(*a);
        if d == 0 {
          self.push_degree(0);
        } else {
          self.push_degree(1);
          self.bump_auxiliaries(2);
        }
      },
      Op::Call(_, _, output_size, unconstrained) => {
        let ones = vec![1usize; *output_size];
        self.push_degrees(&ones);
        self.bump_auxiliaries(*output_size);
        if !*unconstrained {
          self.bump_lookups(1);
        }
      },
      Op::Store(values) => {
        self.push_degree(1);
        self.bump_auxiliaries(1);
        self.bump_lookups(1);
        self.add_mem_size(values.len());
      },
      Op::Load(size, _) => {
        let ones = vec![1usize; *size];
        self.push_degrees(&ones);
        self.bump_auxiliaries(*size);
        self.bump_lookups(1);
        self.add_mem_size(*size);
      },
      Op::AssertEq(..)
      | Op::IOSetInfo(..)
      | Op::IOWrite(..)
      | Op::Debug(..) => {},
      Op::IOGetInfo(_) => {
        self.push_degrees(&[1, 1]);
        self.bump_auxiliaries(2);
      },
      Op::IORead(_, len) => {
        let ones = vec![1usize; *len];
        self.push_degrees(&ones);
        self.bump_auxiliaries(*len);
      },
      Op::U8BitDecomposition(_) => {
        self.push_degrees(&[1; 8]);
        self.bump_auxiliaries(8);
        self.bump_lookups(1);
      },
      Op::U8ShiftLeft(_)
      | Op::U8ShiftRight(_)
      | Op::U8Xor(..)
      | Op::U8And(..)
      | Op::U8Or(..)
      | Op::U8LessThan(..) => {
        self.push_degree(1);
        self.bump_auxiliaries(1);
        self.bump_lookups(1);
      },
      Op::U8Add(..) | Op::U8Mul(..) | Op::U8Sub(..) => {
        self.push_degrees(&[1, 1]);
        self.bump_auxiliaries(2);
        self.bump_lookups(1);
      },
      Op::U32LessThan(..) => {
        self.push_degree(1);
        self.bump_auxiliaries(12);
        self.bump_lookups(6);
      },
    }
  }

  fn block_layout(&mut self, block: &Block) {
    for op in &block.ops {
      self.op_layout(op);
    }
    self.ctrl_layout(&block.ctrl);
  }

  fn ctrl_layout(&mut self, ctrl: &Ctrl) {
    match ctrl {
      Ctrl::Return(..) | Ctrl::Yield(..) => self.bump_selectors(1),
      Ctrl::Match(_, branches, default) => {
        let init_shared = self.get_shared();
        let degrees_save = self.degrees.clone();
        let mut max_shared = init_shared;
        for branch in branches.values() {
          self.set_shared(init_shared);
          self.block_layout(branch);
          let branch_shared = self.get_shared();
          self.degrees = degrees_save.clone();
          max_shared = max_shared.maximals(branch_shared);
        }
        if let Some(default_block) = default {
          self.set_shared(init_shared);
          self.bump_auxiliaries(branches.len());
          self.block_layout(default_block);
          let default_shared = self.get_shared();
          self.degrees = degrees_save.clone();
          max_shared = max_shared.maximals(default_shared);
        }
        self.set_shared(max_shared);
      },
      Ctrl::MatchContinue(
        _,
        branches,
        default,
        output_size,
        _shared_aux,
        _shared_lookups,
        continuation,
      ) => {
        let init_shared = self.get_shared();
        let degrees_save = self.degrees.clone();
        let mut max_shared = init_shared;
        for branch in branches.values() {
          self.set_shared(init_shared);
          self.block_layout(branch);
          let branch_shared = self.get_shared();
          self.degrees = degrees_save.clone();
          max_shared = max_shared.maximals(branch_shared);
        }
        if let Some(default_block) = default {
          self.set_shared(init_shared);
          self.bump_auxiliaries(branches.len());
          self.block_layout(default_block);
          let default_shared = self.get_shared();
          self.degrees = degrees_save.clone();
          max_shared = max_shared.maximals(default_shared);
        }
        self.set_shared(max_shared);
        self.bump_auxiliaries(*output_size);
        let ones = vec![1usize; *output_size];
        self.push_degrees(&ones);
        self.block_layout(continuation);
      },
    }
  }
}
