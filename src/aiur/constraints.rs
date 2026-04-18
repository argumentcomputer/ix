use multi_stark::{
  builder::symbolic::{SymbolicExpression, var},
  lookup::Lookup,
  p3_air::{Air, AirBuilder, BaseAir, WindowAccess},
  p3_field::{Field, PrimeCharacteristicRing},
};
use std::{array, ops::Range};

use crate::{
  FxIndexMap,
  aiur::{
    G,
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel, ValIdx},
    function_channel,
    gadgets::{
      AiurGadget,
      bytes1::{Bytes1, Bytes1Op},
      bytes2::{Bytes2, Bytes2Op},
    },
    memory_channel, u8_add_channel, u8_and_channel,
    u8_bit_decomposition_channel, u8_less_than_channel, u8_or_channel,
    u8_range_check_channel, u8_shift_left_channel, u8_shift_right_channel,
    u8_sub_channel, u8_xor_channel,
  },
};

type Expr = SymbolicExpression<G>;
type Degree = u8;

/// Holds data for a function circuit.
pub struct Constraints {
  pub zeros: Vec<Expr>,
  pub selectors: Range<usize>,
  pub width: usize,
}

impl BaseAir<G> for Constraints {
  fn width(&self) -> usize {
    self.width
  }
}

impl<AB> Air<AB> for Constraints
where
  AB: AirBuilder<F = G>,
{
  fn eval(&self, builder: &mut AB) {
    let main = builder.main();
    let row = main.current_slice();
    for zero in &self.zeros {
      builder.assert_zero(zero.interpret(row, None));
    }
    for sel in self.selectors.clone() {
      builder.assert_bool(row[sel]);
    }
  }
}

struct ConstraintState {
  function_index: G,
  layout: FunctionLayout,
  column: usize,
  lookup: usize,
  lookups: Vec<Lookup<Expr>>,
  map: Vec<(Expr, Degree)>,
  constraints: Constraints,
  /// Yield info collected from branches, used by MatchContinue.
  /// NOT part of save/restore so yields persist across branch restores.
  yield_info: Vec<(Expr, Vec<(Expr, Degree)>)>,
}

struct SharedState {
  column: usize,
  lookup: usize,
  map_len: usize,
}

impl ConstraintState {
  fn selector_index(&self, sel: usize) -> usize {
    sel + self.layout.input_size
  }

  fn next_lookup(&mut self) -> &mut Lookup<Expr> {
    let lookup = &mut self.lookups[self.lookup];
    self.lookup += 1;
    lookup
  }

  fn next_auxiliary(&mut self) -> Expr {
    self.column += 1;
    var(self.column - 1)
  }

  fn save(&mut self) -> SharedState {
    SharedState {
      column: self.column,
      lookup: self.lookup,
      map_len: self.map.len(),
    }
  }

  fn restore(&mut self, init: &SharedState) {
    self.column = init.column;
    self.lookup = init.lookup;
    self.map.truncate(init.map_len);
  }
}

impl Toplevel {
  pub fn build_constraints(
    &self,
    function_index: usize,
  ) -> (Constraints, Vec<Lookup<Expr>>) {
    let function = &self.functions[function_index];
    let constraints = Constraints {
      zeros: vec![],
      selectors: 0..0,
      width: function.layout.width(),
    };
    let mut state = ConstraintState {
      function_index: G::from_usize(function_index),
      layout: function.layout,
      column: 0,
      lookup: 0,
      map: vec![],
      lookups: vec![Lookup::empty(); function.layout.lookups],
      constraints,
      yield_info: vec![],
    };
    function.build_constraints(&mut state);
    (state.constraints, state.lookups)
  }
}

impl Function {
  fn build_constraints(&self, state: &mut ConstraintState) {
    // the first columns are occupied by the input, which is also mapped
    state.column += self.layout.input_size;
    (0..self.layout.input_size).for_each(|i| state.map.push((var(i), 1)));
    // then comes the selectors, which are not mapped
    let init_sel = state.column;
    let final_sel = state.column + self.layout.selectors;
    state.constraints.selectors = init_sel..final_sel;
    state.column = final_sel;
    // the multiplicity occupies another column
    let multiplicity = var(state.column);
    state.column += 1;
    // the return lookup occupies the first lookup slot
    state.lookups[0].multiplicity = -multiplicity.clone();
    state.lookup += 1;
    self.body.collect_constraints(self.body.get_block_selector(state), state);
  }
}

impl Block {
  fn collect_constraints(&self, sel: Expr, state: &mut ConstraintState) {
    // Boolean constraint for this block's selector
    let block_sel = self.get_block_selector(state);
    state
      .constraints
      .zeros
      .push(block_sel.clone() * (Expr::from(G::ONE) - block_sel));
    self.ops.iter().for_each(|op| op.collect_constraints(&sel, state));
    self.ctrl.collect_constraints(sel, state);
  }

  /// Compute this block's selector as the sum of its immediate children's
  /// selectors. For leaf blocks (Return/Yield) this is the single selector
  /// variable. For Match/MatchContinue this is the sum of case branch
  /// selectors — crucially excluding the MatchContinue's continuation,
  /// whose return selector fires alongside a yield selector and must not
  /// be double-counted.
  fn get_block_selector(&self, state: &ConstraintState) -> Expr {
    match &self.ctrl {
      Ctrl::Return(sel, _) | Ctrl::Yield(sel, _) => {
        var(state.selector_index(*sel))
      },
      Ctrl::Match(_, cases, def) | Ctrl::MatchContinue(_, cases, def, ..) => {
        let mut sel = Expr::from(G::ZERO);
        for branch in cases.values() {
          sel += branch.get_block_selector(state);
        }
        if let Some(branch) = def {
          sel += branch.get_block_selector(state);
        }
        sel
      },
    }
  }
}

/// Process match cases and optional default branch, emitting selector-gated
/// constraints. Each branch is processed with save/restore so branches share
/// auxiliary columns. Returns (max_column, max_lookup) across all branches.
fn collect_branch_constraints(
  var: ValIdx,
  cases: &FxIndexMap<G, Block>,
  def: &Option<Box<Block>>,
  state: &mut ConstraintState,
) -> (usize, usize) {
  let (var, _) = state.map[var].clone();
  let init = state.save();
  let mut max_column = init.column;
  let mut max_lookup = init.lookup;
  for (&value, branch) in cases.iter() {
    let branch_sel = branch.get_block_selector(state);
    state
      .constraints
      .zeros
      .push(branch_sel.clone() * (var.clone() - Expr::from(value)));
    branch.collect_constraints(branch_sel, state);
    max_column = max_column.max(state.column);
    max_lookup = max_lookup.max(state.lookup);
    state.restore(&init);
  }
  if let Some(branch) = def {
    let branch_sel = branch.get_block_selector(state);
    for &value in cases.keys() {
      let inverse = state.next_auxiliary();
      state.constraints.zeros.push(
        branch_sel.clone()
          * ((var.clone() - Expr::from(value)) * inverse - Expr::from(G::ONE)),
      );
    }
    branch.collect_constraints(branch_sel, state);
    max_column = max_column.max(state.column);
    max_lookup = max_lookup.max(state.lookup);
    state.restore(&init);
  }
  (max_column, max_lookup)
}

impl Ctrl {
  #[allow(clippy::needless_pass_by_value)]
  fn collect_constraints(&self, sel: Expr, state: &mut ConstraintState) {
    match self {
      Ctrl::Return(_, values) => {
        // channel and function index
        let mut args = vec![
          sel.clone() * function_channel(),
          sel.clone() * state.function_index,
        ];
        // input
        args.extend(
          (0..state.layout.input_size)
            .map(|arg| sel.clone() * state.map[arg].0.clone()),
        );
        // output
        args.extend(
          values.iter().map(|arg| sel.clone() * state.map[*arg].0.clone()),
        );
        let lookup = &mut state.lookups[0];
        combine_lookup_args(lookup, args);
        // multiplicity is already set
      },
      Ctrl::Yield(sel, values) => {
        let yield_sel = var(state.selector_index(*sel));
        let yield_vals: Vec<(Expr, Degree)> =
          values.iter().map(|&v| state.map[v].clone()).collect();
        state.yield_info.push((yield_sel, yield_vals));
      },
      Ctrl::Match(var, cases, def) => {
        let (max_column, max_lookup) =
          collect_branch_constraints(*var, cases, def, state);
        state.column = max_column;
        state.lookup = max_lookup;
      },
      Ctrl::MatchContinue(
        var,
        cases,
        def,
        output_size,
        _shared_aux,
        _shared_lookups,
        continuation,
      ) => {
        let yield_info_base = state.yield_info.len();
        let (max_column, max_lookup) =
          collect_branch_constraints(*var, cases, def, state);

        // Advance past the shared branch region so merge + continuation
        // auxiliaries don't collide with branch auxiliaries.
        state.column = max_column;
        state.lookup = max_lookup;

        // Collect yield info from branches
        let yields: Vec<_> =
          state.yield_info.drain(yield_info_base..).collect();

        // Compute continuation selector = sum of yield selectors
        let cont_sel = yields
          .iter()
          .map(|(sel, _)| sel.clone())
          .fold(Expr::from(G::ZERO), |a, b| a + b);

        // Merge constraints, gated by the parent selector `sel`. Gating is
        // required because a matchContinue inside a tail match branch may be
        // inactive (the other branch was taken). At the OOD evaluation point,
        // ungated constraints on shared auxiliary columns don't evaluate to 0.
        for i in 0..*output_size {
          let merged = state.next_auxiliary();
          let sum = yields
            .iter()
            .map(|(sel_j, vals)| sel_j.clone() * vals[i].0.clone())
            .fold(Expr::from(G::ZERO), |a, b| a + b);
          state.constraints.zeros.push(sel.clone() * (merged.clone() - sum));
          state.map.push((merged, 1));
        }

        // Link continuation selector to the continuation block's selector
        let cont_block_sel = continuation.get_block_selector(state);
        state.constraints.zeros.push(cont_block_sel - cont_sel.clone());

        // Collect constraints for the continuation, gated by cont_sel
        continuation.collect_constraints(cont_sel, state);
      },
    }
  }
}

impl Op {
  fn collect_constraints(&self, sel: &Expr, state: &mut ConstraintState) {
    match self {
      Op::Const(f) => state.map.push(((*f).into(), 0)),
      Op::Add(a, b) => {
        let (a, a_deg) = &state.map[*a];
        let (b, b_deg) = &state.map[*b];
        let deg = a_deg.max(b_deg);
        state.map.push((a.clone() + b.clone(), *deg));
      },
      Op::Sub(a, b) => {
        let (a, a_deg) = &state.map[*a];
        let (b, b_deg) = &state.map[*b];
        let deg = a_deg.max(b_deg);
        state.map.push((a.clone() - b.clone(), *deg));
      },
      Op::Mul(a, b) => {
        let (a, a_deg) = &state.map[*a];
        let (b, b_deg) = &state.map[*b];
        let deg = a_deg + b_deg;
        let mul = a.clone() * b.clone();
        if deg < 2 {
          state.map.push((mul, deg));
        } else {
          let col = state.next_auxiliary();
          state.map.push((col.clone(), 1));
          state.constraints.zeros.push(sel.clone() * (col - mul));
        }
      },
      Op::EqZero(a) => {
        let (a, deg) = state.map[*a].clone();
        if let Expr::Constant(a) = a {
          assert_eq!(deg, 0);
          state.map.push((Expr::from_bool(a == G::ZERO), 0));
        } else {
          // We have two constraints:
          // 1. ax = 0
          // 2. ad + x = 1
          // When a = 0, the first constraint is trivial and the second
          // constraint enforces x = 1.
          // When a ≠ 0, the first constraint enforces x = 0 and the
          // second constraint can be satisfied with d = a⁻¹.
          // In both cases, x has the semantics that we want.
          let d = state.next_auxiliary();
          let x = state.next_auxiliary();
          state.constraints.zeros.push(sel.clone() * a.clone() * x.clone());
          state
            .constraints
            .zeros
            .push(sel.clone() * (a * d + x.clone() - Expr::ONE));
          state.map.push((x, 1));
        }
      },
      Op::Call(function_index, inputs, output_size, op_unconstrained) => {
        if *op_unconstrained {
          // No lookup constraint -- unconstrained call
          for _ in 0..*output_size {
            let col = state.next_auxiliary();
            state.map.push((col.clone(), 1));
          }
        } else {
          // channel and function index
          let mut lookup_args = vec![
            sel.clone() * function_channel(),
            sel.clone() * G::from_usize(*function_index),
          ];
          // input
          lookup_args.extend(
            inputs.iter().map(|arg| sel.clone() * state.map[*arg].0.clone()),
          );
          // output
          let output = (0..*output_size).map(|_| {
            let col = state.next_auxiliary();
            state.map.push((col.clone(), 1));
            sel.clone() * col
          });
          lookup_args.extend(output);

          let lookup = state.next_lookup();
          combine_lookup_args(lookup, lookup_args);
          lookup.multiplicity += sel.clone();
        }
      },
      Op::Store(values) => {
        let size = values.len();
        // channel, function index and pointer
        let ptr = state.next_auxiliary();
        state.map.push((ptr.clone(), 1));
        let mut lookup_args = vec![
          sel.clone() * memory_channel(),
          sel.clone() * G::from_usize(size),
          sel.clone() * ptr,
        ];
        // stored values
        lookup_args.extend(
          values.iter().map(|value| sel.clone() * state.map[*value].0.clone()),
        );

        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity += sel.clone();
      },
      Op::Load(size, ptr) => {
        // channel, size and pointer
        let mut lookup_args = vec![
          sel.clone() * memory_channel(),
          sel.clone() * G::from_usize(*size),
          sel.clone() * state.map[*ptr].0.clone(),
        ];
        // loaded values
        let values = (0..*size).map(|_| {
          let col = state.next_auxiliary();
          state.map.push((col.clone(), 1));
          sel.clone() * col
        });
        lookup_args.extend(values);

        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity += sel.clone();
      },
      Op::AssertEq(xs, ys) => {
        assert_eq!(xs.len(), ys.len());
        for (x, y) in xs.iter().zip(ys) {
          let (x, _) = &state.map[*x];
          let (y, _) = &state.map[*y];
          state.constraints.zeros.push(sel.clone() * (x.clone() - y.clone()));
        }
      },
      Op::AssertApp(function_index, inputs, expected_outputs) => {
        let mut lookup_args = vec![
          sel.clone() * function_channel(),
          sel.clone() * G::from_usize(*function_index),
        ];
        lookup_args.extend(
          inputs.iter().map(|arg| sel.clone() * state.map[*arg].0.clone()),
        );
        lookup_args.extend(
          expected_outputs
            .iter()
            .map(|arg| sel.clone() * state.map[*arg].0.clone()),
        );
        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity += sel.clone();
      },
      Op::IOGetInfo(_) => (0..2).for_each(|_| {
        let col = state.next_auxiliary();
        state.map.push((col, 1));
      }),
      Op::IORead(_, len) => (0..*len).for_each(|_| {
        let col = state.next_auxiliary();
        state.map.push((col, 1));
      }),
      Op::U8BitDecomposition(byte) => bytes1_constraints(
        *byte,
        &Bytes1Op::BitDecomposition,
        u8_bit_decomposition_channel(),
        sel.clone(),
        state,
      ),
      Op::U8ShiftLeft(byte) => bytes1_constraints(
        *byte,
        &Bytes1Op::ShiftLeft,
        u8_shift_left_channel(),
        sel.clone(),
        state,
      ),
      Op::U8ShiftRight(byte) => bytes1_constraints(
        *byte,
        &Bytes1Op::ShiftRight,
        u8_shift_right_channel(),
        sel.clone(),
        state,
      ),
      Op::U8Xor(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::Xor,
        u8_xor_channel(),
        sel.clone(),
        state,
      ),
      Op::U8Add(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::Add,
        u8_add_channel(),
        sel.clone(),
        state,
      ),
      Op::U8Sub(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::Sub,
        u8_sub_channel(),
        sel.clone(),
        state,
      ),
      Op::U8And(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::And,
        u8_and_channel(),
        sel.clone(),
        state,
      ),
      Op::U8Or(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::Or,
        u8_or_channel(),
        sel.clone(),
        state,
      ),
      Op::U8LessThan(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::LessThan,
        u8_less_than_channel(),
        sel.clone(),
        state,
      ),
      Op::U32LessThan(x_idx, y_idx) => {
        // u32 less-than via addition carry chain.
        //
        // Goal: constrain output = 1 if a < b, 0 otherwise, where a and b are
        // u32 values (< 2^32) represented as Goldilocks field elements.
        //
        // Approach: find witness c (non-deterministic) such that
        //     a + c + 1 = b + carry · 2^32
        // The +1 ensures strict less-than (not ≤). Then a < b ⟺ carry = 0.
        //
        // Decompose a, c, b into 4 little-endian bytes each (x_k, y_k, z_k).
        // The carry chain is computed as polynomial expressions:
        //     c_k = (x_k + y_k + prev - z_k) / 256
        // where prev = 1 for k=0, prev = c_{k-1} for k>0.
        // Each c_k is constrained to be boolean (assert_bool).
        //
        // All 12 bytes are range-checked via 6 Bytes2 range-check lookups
        // (2 bytes per lookup).
        //
        // Resources: 12 auxiliaries, 6 lookups, 6 polynomial constraints
        // (2 decomposition + 4 assert_bool).
        let a = state.map[*x_idx].0.clone();
        let b = state.map[*y_idx].0.clone();

        // Byte decomposition auxiliaries
        let x_bytes: [Expr; 4] = array::from_fn(|_| state.next_auxiliary());
        let y_bytes: [Expr; 4] = array::from_fn(|_| state.next_auxiliary());
        let z_bytes: [Expr; 4] = array::from_fn(|_| state.next_auxiliary());

        // Decomposition constraints: a = Σ x_k * 256^k, b = Σ z_k * 256^k
        let base =
          |k: usize| G::from_u64(256u64.pow(u32::try_from(k).unwrap()));
        let recompose = |bytes: &[Expr; 4]| {
          bytes
            .iter()
            .enumerate()
            .fold(Expr::Constant(G::ZERO), |acc, (k, b)| {
              acc + b.clone() * base(k)
            })
        };
        state.constraints.zeros.push(sel.clone() * (a - recompose(&x_bytes)));
        state.constraints.zeros.push(sel.clone() * (b - recompose(&z_bytes)));

        // Carry chain: a + c + 1 = b + carry * 2^32
        let base_inv = G::from_u64(256).inverse();
        let mut carry = Expr::ONE; // initial carry = 1 for strict less-than
        for k in 0..4 {
          let sum = x_bytes[k].clone() + y_bytes[k].clone() + carry;
          carry = (sum - z_bytes[k].clone()) * base_inv;
          state
            .constraints
            .zeros
            .push(sel.clone() * (carry.clone() * (carry.clone() - Expr::ONE)));
        }

        // Range-check byte pairs via Bytes2 lookups
        let rc_channel = u8_range_check_channel();
        for pair in [
          (&x_bytes[0], &x_bytes[1]),
          (&x_bytes[2], &x_bytes[3]),
          (&y_bytes[0], &y_bytes[1]),
          (&y_bytes[2], &y_bytes[3]),
          (&z_bytes[0], &z_bytes[1]),
          (&z_bytes[2], &z_bytes[3]),
        ] {
          let lookup = state.next_lookup();
          combine_lookup_args(
            lookup,
            vec![
              sel.clone() * rc_channel,
              sel.clone() * pair.0.clone(),
              sel.clone() * pair.1.clone(),
            ],
          );
          lookup.multiplicity += sel.clone();
        }

        // Output: 1 - carry
        let output = Expr::ONE - carry;
        state.map.push((output, 1));
      },
      Op::IOSetInfo(..) | Op::IOWrite(_) | Op::Debug(..) => (),
    }
  }
}

fn bytes1_constraints(
  byte: usize,
  op: &Bytes1Op,
  channel: G,
  sel: SymbolicExpression<G>,
  state: &mut ConstraintState,
) {
  let size = Bytes1.output_size(op);

  let mut lookup_args =
    vec![sel.clone() * channel, sel.clone() * state.map[byte].0.clone()];

  let output = (0..size).map(|_| {
    let col = state.next_auxiliary();
    state.map.push((col.clone(), 1));
    sel.clone() * col
  });
  lookup_args.extend(output);

  let lookup = state.next_lookup();
  combine_lookup_args(lookup, lookup_args);
  lookup.multiplicity += sel;
}

fn bytes2_constraints(
  i: usize,
  j: usize,
  op: &Bytes2Op,
  channel: G,
  sel: SymbolicExpression<G>,
  state: &mut ConstraintState,
) {
  let size = Bytes2.output_size(op);

  let mut lookup_args = vec![
    sel.clone() * channel,
    sel.clone() * state.map[i].0.clone(),
    sel.clone() * state.map[j].0.clone(),
  ];

  let output = (0..size).map(|_| {
    let col = state.next_auxiliary();
    state.map.push((col.clone(), 1));
    sel.clone() * col
  });
  lookup_args.extend(output);

  let lookup = state.next_lookup();
  combine_lookup_args(lookup, lookup_args);
  lookup.multiplicity += sel;
}

fn combine_lookup_args(
  lookup: &mut Lookup<SymbolicExpression<G>>,
  args: impl IntoIterator<Item = SymbolicExpression<G>>,
) {
  let mut args_iterator = args.into_iter();
  lookup.args.iter_mut().zip(args_iterator.by_ref()).for_each(
    |(arg, value)| {
      *arg += value;
    },
  );
  lookup.args.extend(args_iterator);
}
