//! A minimal hand-written Aiur `Toplevel` for exercising the full
//! prove-then-compress pipeline without the Lean frontend.
//!
//! Two functions:
//!   0 (entry): `square_sum(x, y) = add(x, y) * add(x, y)` — one function-call
//!     lookup into function 1 and one degree-2 `Mul` auxiliary.
//!   1: `add(x, y) = x + y` — pure compound expression, no auxiliaries.
//!
//! Layout accounting (see `aiur::constraints`): columns are
//! `[inputs | selectors | multiplicity + auxiliaries]`, so `auxiliaries`
//! counts the multiplicity column plus one column per `Call` output /
//! degree-2 `Mul`; `lookups` counts the reserved return lookup (slot 0)
//! plus one per `Call`.

use aiur::bytecode::{
  Block, Circuit, Ctrl, Function, FunctionLayout, Op, Toplevel,
};

pub fn toplevel() -> Toplevel {
  let square_sum_layout = FunctionLayout {
    input_size: 2,
    selectors: 1,
    // multiplicity + call output + mul auxiliary
    auxiliaries: 3,
    // return lookup + call lookup
    lookups: 2,
  };
  let square_sum = Function {
    body: Block {
      ops: vec![
        // idx 2 = add(x, y): one output column
        Op::Call(1, vec![0, 1], 1, false),
        // idx 3 = idx2 * idx2: both operands degree 1, so one auxiliary
        Op::Mul(2, 2),
      ],
      ctrl: Ctrl::Return(0, vec![3]),
    },
    layout: square_sum_layout,
    entry: true,
    constrained: true,
  };
  let add_layout = FunctionLayout {
    input_size: 2,
    selectors: 1,
    // multiplicity only
    auxiliaries: 1,
    // return lookup only
    lookups: 1,
  };
  let add = Function {
    body: Block { ops: vec![Op::Add(0, 1)], ctrl: Ctrl::Return(0, vec![2]) },
    layout: add_layout,
    entry: false,
    constrained: true,
  };
  Toplevel {
    functions: vec![square_sum, add],
    memory_sizes: vec![],
    // Ungrouped functions get one singleton circuit each, in function order
    // (mirrors `Bytecode.Toplevel.buildCircuits` on the Lean side).
    circuits: vec![
      Circuit { members: vec![0], layout: square_sum_layout },
      Circuit { members: vec![1], layout: add_layout },
    ],
  }
}

/// Entry function index for [`toplevel`].
pub const ENTRY_FUN_IDX: usize = 0;
