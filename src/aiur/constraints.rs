use multi_stark::{
  builder::symbolic::{SymbolicExpression, var},
  lookup::Lookup,
  p3_air::{Air, AirBuilder, BaseAir},
  p3_field::PrimeCharacteristicRing,
  p3_matrix::Matrix,
};
use std::ops::Range;

use crate::aiur::{
  G,
  bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
  function_channel,
  gadgets::{
    AiurGadget,
    bytes1::{Bytes1, Bytes1Op},
    bytes2::{Bytes2, Bytes2Op},
  },
  memory_channel, u8_add_channel, u8_and_channel, u8_bit_decomposition_channel,
  u8_less_than_channel, u8_or_channel, u8_shift_left_channel,
  u8_shift_right_channel, u8_sub_channel, u8_xor_channel,
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
    let row = main.row_slice(0).unwrap();
    for zero in &self.zeros {
      builder.assert_zero(zero.interpret(&row, None));
    }
    for sel in self.selectors.clone() {
      builder.assert_bool(row[sel].clone());
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
    };
    function.build_constraints(&mut state, self);
    (state.constraints, state.lookups)
  }
}

impl Function {
  fn build_constraints(
    &self,
    state: &mut ConstraintState,
    toplevel: &Toplevel,
  ) {
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
    // the multiplicity can only be set if one and only one selector is set
    let sel = self.body.get_block_selector(state);
    state
      .constraints
      .zeros
      .push(multiplicity * (Expr::from(G::ONE) - sel.clone()));
    self.body.collect_constraints(sel, state, toplevel);
  }
}

impl Block {
  fn collect_constraints(
    &self,
    sel: Expr,
    state: &mut ConstraintState,
    toplevel: &Toplevel,
  ) {
    self
      .ops
      .iter()
      .for_each(|op| op.collect_constraints(&sel, state, toplevel));
    self.ctrl.collect_constraints(sel, state, toplevel);
  }

  fn get_block_selector(&self, state: &mut ConstraintState) -> Expr {
    (self.min_sel_included..self.max_sel_excluded)
      .map(|i| var(state.selector_index(i)))
      .fold(Expr::Constant(G::ZERO), |var, acc| var + acc)
  }
}

impl Ctrl {
  #[allow(clippy::needless_pass_by_value)]
  fn collect_constraints(
    &self,
    sel: Expr,
    state: &mut ConstraintState,
    toplevel: &Toplevel,
  ) {
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
      Ctrl::Match(var, cases, def) => {
        let (var, _) = state.map[*var].clone();
        let init = state.save();
        for (&value, branch) in cases.iter() {
          let branch_sel = branch.get_block_selector(state);
          state
            .constraints
            .zeros
            .push(branch_sel.clone() * (var.clone() - Expr::from(value)));
          branch.collect_constraints(branch_sel, state, toplevel);
          state.restore(&init);
        }
        if let Some(branch) = def {
          let branch_sel = branch.get_block_selector(state);
          for &value in cases.keys() {
            let inverse = state.next_auxiliary();
            state.constraints.zeros.push(
              branch_sel.clone()
                * ((var.clone() - Expr::from(value)) * inverse
                  - Expr::from(G::ONE)),
            );
          }
          branch.collect_constraints(branch_sel, state, toplevel);
        }
      },
    }
  }
}

impl Op {
  fn collect_constraints(
    &self,
    sel: &Expr,
    state: &mut ConstraintState,
    toplevel: &Toplevel,
  ) {
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
      Op::Call(function_index, inputs, output_size) => {
        if toplevel.functions[*function_index].unconstrained {
          // The callee is unconstrained and isn't going to pull its claim.
          // Therefore we don't push it.

          // Just feed the map with the output and move on.
          for _ in 0..*output_size {
            let col = state.next_auxiliary();
            state.map.push((col.clone(), 1));
          }
          return;
        }

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
        // u32 less-than via byte decomposition and subtraction with borrow chain.
        //
        // Goal: constrain output = 1 if x < y, 0 otherwise, where x and y are
        // u32 values (< 2^32) represented as Goldilocks field elements.
        //
        // Step 1 — Byte decomposition. Decompose x and y into 4 little-endian
        // bytes each:
        //     x = Σ_{k=0}^{3} x_k · 256^k
        //     y = Σ_{k=0}^{3} y_k · 256^k
        // Each byte is range-checked to [0, 255] by appearing as an operand in
        // a u8_sub lookup against the Bytes2 preprocessed table.
        //
        // No canonicality check is needed. Since 2^32 < p, the 4- byte decomposition
        // of any field element v is unique iff v < 2^32. If v ≥ 2^32, no 4-byte
        // decomposition sums to v in the field, so the decomposition constraint
        // is unsatisfiable and the prover simply cannot produce a valid witness.
        // This means u32_less_than is only usable on values that actually fit in
        // 32 bits; applying it to larger values will cause proof generation to fail.
        //
        // Step 2 — Borrow-chain subtraction. We compute
        //     y_int − x_int − 1
        // byte-by-byte using two u8_sub lookups per byte (8 total):
        //     u8_sub(y_k, x_k) → (t_k, b_k')
        //     u8_sub(t_k, c_k)  → (r_k, b_k'')
        // where c_0 = 1 (the −1 offset) and c_k = b_{k−1}' + b_{k−1}'' for k > 0.
        //
        // The algebraic identity across all 4 bytes gives:
        //     r_int − 2^32 · b_3 = y_int − x_int − 1
        // where r_int = Σ r_k · 256^k ∈ [0, 2^32−1] and b_3 = b_3' + b_3'' is
        // the final borrow.
        //
        // Step 3 — Soundness of the final borrow. Since x, y < 2^32:
        //   • y − x − 1 ∈ [−(2^32−1), 2^32 − 2]  ⊂  (−2^32, 2^32)
        //   • r_int ∈ [0, 2^32 − 1]
        // So b_3 = (r_int − (y − x − 1)) / 2^32. If b_3 ≥ 2 then
        // y − x − 1 = r_int − 2·2^32 ≤ 2^32−1 − 2^33 < −2^32, contradicting the
        // lower bound. Hence b_3 ∈ {0, 1}:
        //   • b_3 = 0  ⟹  y − x − 1 ≥ 0  ⟹  x < y
        //   • b_3 = 1  ⟹  y − x − 1 < 0  ⟹  x ≥ y
        //
        // Output: 1 − b_3 = 1 − (b_3' + b_3'').
        //
        // Resources: 24 auxiliaries (8 bytes + 16 borrow chain), 8 lookups
        // (all u8_sub), 2 polynomial constraints (decomposition only).
        let x = state.map[*x_idx].0.clone();
        let y = state.map[*y_idx].0.clone();

        // Byte decomposition: 4 byte auxiliaries per operand
        let x_bytes: Vec<Expr> =
          (0..4).map(|_| state.next_auxiliary()).collect();
        let y_bytes: Vec<Expr> =
          (0..4).map(|_| state.next_auxiliary()).collect();

        // Decomposition constraints: x = Σ xi * 256^i
        let x_sum = x_bytes.iter().enumerate().fold(
          Expr::Constant(G::ZERO),
          |acc, (k, b)| {
            acc + b.clone() * G::from_u64(256u64.pow(u32::try_from(k).unwrap()))
          },
        );
        state.constraints.zeros.push(sel.clone() * (x - x_sum));

        let y_sum = y_bytes.iter().enumerate().fold(
          Expr::Constant(G::ZERO),
          |acc, (k, b)| {
            acc + b.clone() * G::from_u64(256u64.pow(u32::try_from(k).unwrap()))
          },
        );
        state.constraints.zeros.push(sel.clone() * (y - y_sum));

        // Borrow chain: y - x - 1 byte-by-byte
        let sub_channel = u8_sub_channel();
        let mut prev_borrow: Option<Expr> = None;
        for k in 0..4 {
          let t_k = state.next_auxiliary();
          let b_k_prime = state.next_auxiliary();
          let r_k = state.next_auxiliary();
          let b_k_double_prime = state.next_auxiliary();

          // Lookup 1: u8_sub(y_k, x_k) -> (t_k, b_k')
          let lookup = state.next_lookup();
          combine_lookup_args(
            lookup,
            vec![
              sel.clone() * sub_channel,
              sel.clone() * y_bytes[k].clone(),
              sel.clone() * x_bytes[k].clone(),
              sel.clone() * t_k.clone(),
              sel.clone() * b_k_prime.clone(),
            ],
          );
          lookup.multiplicity += sel.clone();

          // Lookup 2: u8_sub(t_k, borrow_in) -> (r_k, b_k'')
          let borrow_in = match prev_borrow {
            None => Expr::Constant(G::ONE),
            Some(prev_borrow) => prev_borrow.clone(),
          };
          let lookup = state.next_lookup();
          combine_lookup_args(
            lookup,
            vec![
              sel.clone() * sub_channel,
              sel.clone() * t_k,
              sel.clone() * borrow_in,
              sel.clone() * r_k,
              sel.clone() * b_k_double_prime.clone(),
            ],
          );
          lookup.multiplicity += sel.clone();

          prev_borrow = Some(b_k_prime + b_k_double_prime);
        }

        // Output: 1 - (b_3' + b_3'')
        let output = Expr::ONE - prev_borrow.unwrap();
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
    col
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
    col
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
