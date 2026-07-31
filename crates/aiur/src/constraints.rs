use multi_stark::{
  lookup::Lookup,
  p3_field::{Field, PrimeCharacteristicRing},
};
use std::{array, ops::Range, sync::LazyLock};

use crate::{
  FxIndexMap, G,
  bytecode::{Block, Ctrl, Op, Toplevel, ValIdx},
  function_channel,
  gadgets::{
    AiurGadget,
    bytes1::{Bytes1, Bytes1Op},
    bytes2::{Bytes2, Bytes2Op},
  },
  memory_channel, u8_add_channel, u8_and_channel, u8_bit_decomposition_channel,
  u8_chain_rotr4_channel, u8_chain_rotr7_channel, u8_less_than_channel,
  u8_mul_channel, u8_or_channel, u8_range_check_channel, u8_shift_left_channel,
  u8_shift_right_channel, u8_sub_channel, u8_xor_channel,
};

type Expr = multi_stark::expr::Expr<G>;
type Degree = u8;

/// Main-trace column variable at index `i`.
#[inline]
fn var(i: usize) -> Expr {
  Expr::main(u32::try_from(i).expect("column index exceeds u32"))
}

/// Base-field constant expression.
#[inline]
fn konst(value: G) -> Expr {
  Expr::constant(value)
}

/// `256⁻¹` in the Goldilocks field. The field inversion is expensive, so it is
/// computed once and reused by the byte carry-chain constraints.
static INV_256: LazyLock<G> = LazyLock::new(|| G::from_u64(256).inverse());

/// Holds data for a function circuit.
pub struct Constraints {
  pub zeros: Vec<Expr>,
  pub selectors: Range<usize>,
  pub width: usize,
}

struct ConstraintState {
  /// Index of the circuit member currently being walked.
  function_index: G,
  /// Exactly one selector: the circuit backs a single function with a
  /// single leaf block (no matches), so every lookup slot is written by
  /// exactly one branch.
  branchless: bool,
  /// Input size of the current member (inputs live in columns
  /// `0..input_size` for every member; the circuit reserves the max).
  input_size: usize,
  /// Column of the current member's first selector: the circuit's input
  /// block plus the selector counts of the members walked before it.
  sel_base: usize,
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
    sel + self.sel_base
  }

  /// Selector-gate a lookup argument. Lookup slots shared across branches
  /// superpose their arguments (`Σ_b sel_b·arg_b`, sound because the
  /// selectors are mutually exclusive), which needs the weighting — but it
  /// costs a degree: the argument becomes degree 2. A branchless function
  /// has a single branch, so its arguments are sent RAW (degree ≤ 1): the
  /// multiplicity (still selector-gated) alone decides whether the lookup
  /// counts, and on inactive (padding) rows a zero multiplicity makes the
  /// message value irrelevant. Degree-1 messages leave the degree headroom
  /// to group two lookups per chained-accumulator step.
  fn gate(&self, sel: &Expr, arg: Expr) -> Expr {
    if self.branchless { arg } else { sel.clone() * arg }
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
  /// Build the constraints of one circuit. The circuit's members are walked
  /// like branches of a single function: each walk restarts the auxiliary
  /// column / lookup-slot counters (so members share those, like match arms
  /// do), while selector columns are laid out consecutively per member. All
  /// members fold their return message into the shared lookup slot 0, gated
  /// by their own selectors and carrying their own function index, against
  /// the single shared multiplicity column.
  pub fn build_constraints(
    &self,
    circuit_index: usize,
  ) -> (Constraints, Vec<Lookup<Expr>>) {
    let circuit = &self.circuits[circuit_index];
    let layout = circuit.layout;
    let constraints = Constraints {
      zeros: vec![],
      selectors: layout.input_size..layout.input_size + layout.selectors,
      width: layout.width(),
    };
    let mut state = ConstraintState {
      function_index: G::ZERO,
      branchless: layout.selectors == 1,
      input_size: 0,
      sel_base: 0,
      column: 0,
      lookup: 0,
      map: vec![],
      lookups: vec![empty_lookup(); layout.lookups],
      constraints,
      yield_info: vec![],
    };
    // The shared multiplicity column: first auxiliary, right after the
    // selectors. The return lookup occupies the first lookup slot.
    let multiplicity = var(layout.input_size + layout.selectors);
    state.lookups[0].multiplicity = -multiplicity;
    let aux_start = layout.input_size + layout.selectors + 1;
    let mut sel_base = layout.input_size;
    let mut circuit_sel = Expr::from(G::ZERO);
    for &member in &circuit.members {
      let function = &self.functions[member];
      state.function_index = G::from_usize(member);
      state.input_size = function.layout.input_size;
      state.sel_base = sel_base;
      state.column = aux_start;
      state.lookup = 1;
      state.map.clear();
      (0..function.layout.input_size).for_each(|i| state.map.push((var(i), 1)));
      let body_sel = function.body.get_block_selector(&state);
      circuit_sel = circuit_sel + body_sel.clone();
      function.body.collect_constraints(body_sel, &mut state);
      debug_assert!(state.yield_info.is_empty());
      sel_base += function.layout.selectors;
    }
    // The old `Air::eval` asserted each selector column boolean; the new
    // system compiles a constraint vector, so materialize those explicitly.
    for sel in state.constraints.selectors.clone() {
      let s = var(sel);
      state.constraints.zeros.push(s.clone() * (s - konst(G::ONE)));
    }
    // Cross-member exclusivity: the circuit-level selector (the sum of the
    // members' top-block selectors) must be boolean, so at most one member
    // is active per row and the shared return lookup emits a single
    // member's message. A singleton circuit already gets this from its top
    // block's own boolean constraint.
    if circuit.members.len() > 1 {
      state
        .constraints
        .zeros
        .push(circuit_sel.clone() * (Expr::from(G::ONE) - circuit_sel));
    }
    (state.constraints, state.lookups)
  }
}

fn empty_lookup() -> Lookup<Expr> {
  Lookup { multiplicity: konst(G::ZERO), args: vec![] }
}

impl Block {
  fn collect_constraints(&self, sel: Expr, state: &mut ConstraintState) {
    // Boolean constraint for this block's selector
    let block_sel = self.get_block_selector(state);
    state
      .constraints
      .zeros
      .push(block_sel.clone() * (konst(G::ONE) - block_sel));
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
        let mut sel = konst(G::ZERO);
        for branch in cases.values() {
          sel = sel + branch.get_block_selector(state);
        }
        if let Some(branch) = def {
          sel = sel + branch.get_block_selector(state);
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
  var_idx: ValIdx,
  cases: &FxIndexMap<G, Block>,
  def: &Option<Box<Block>>,
  state: &mut ConstraintState,
) -> (usize, usize) {
  let (matched, _) = state.map[var_idx].clone();
  let init = state.save();
  let mut max_column = init.column;
  let mut max_lookup = init.lookup;
  for (&value, branch) in cases.iter() {
    let branch_sel = branch.get_block_selector(state);
    state
      .constraints
      .zeros
      .push(branch_sel.clone() * (matched.clone() - konst(value)));
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
          * ((matched.clone() - konst(value)) * inverse - konst(G::ONE)),
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
          state.gate(&sel, konst(function_channel())),
          state.gate(&sel, konst(state.function_index)),
        ];
        // input
        args.extend(
          (0..state.input_size)
            .map(|arg| state.gate(&sel, state.map[arg].0.clone())),
        );
        // output
        args.extend(
          values.iter().map(|arg| state.gate(&sel, state.map[*arg].0.clone())),
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
      Ctrl::Match(var_idx, cases, def) => {
        let (max_column, max_lookup) =
          collect_branch_constraints(*var_idx, cases, def, state);
        state.column = max_column;
        state.lookup = max_lookup;
      },
      Ctrl::MatchContinue(
        var_idx,
        cases,
        def,
        output_size,
        _shared_aux,
        _shared_lookups,
        continuation,
      ) => {
        let yield_info_base = state.yield_info.len();
        let (max_column, max_lookup) =
          collect_branch_constraints(*var_idx, cases, def, state);

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
          .fold(konst(G::ZERO), |a, b| a + b);

        // Merge constraints, gated by the parent selector `sel`. Gating is
        // required because a matchContinue inside a tail match branch may be
        // inactive (the other branch was taken). At the OOD evaluation point,
        // ungated constraints on shared auxiliary columns don't evaluate to 0.
        for i in 0..*output_size {
          let merged = state.next_auxiliary();
          let sum = yields
            .iter()
            .map(|(sel_j, vals)| sel_j.clone() * vals[i].0.clone())
            .fold(konst(G::ZERO), |a, b| a + b);
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
        if let Expr::Const(a) = a {
          assert_eq!(deg, 0);
          state.map.push((konst(G::from_bool(a == G::ZERO)), 0));
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
            .push(sel.clone() * (a * d + x.clone() - konst(G::ONE)));
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
            state.gate(sel, konst(function_channel())),
            state.gate(sel, konst(G::from_usize(*function_index))),
          ];
          // input
          lookup_args.extend(
            inputs.iter().map(|arg| state.gate(sel, state.map[*arg].0.clone())),
          );
          // output
          let output: Vec<Expr> = (0..*output_size)
            .map(|_| {
              let col = state.next_auxiliary();
              state.map.push((col.clone(), 1));
              col
            })
            .collect();
          lookup_args
            .extend(output.into_iter().map(|col| state.gate(sel, col)));

          let lookup = state.next_lookup();
          combine_lookup_args(lookup, lookup_args);
          lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
        }
      },
      Op::Store(values) => {
        let size = values.len();
        // channel, function index and pointer
        let ptr = state.next_auxiliary();
        state.map.push((ptr.clone(), 1));
        let mut lookup_args = vec![
          state.gate(sel, konst(memory_channel())),
          state.gate(sel, konst(G::from_usize(size))),
          state.gate(sel, ptr),
        ];
        // stored values
        lookup_args.extend(
          values
            .iter()
            .map(|value| state.gate(sel, state.map[*value].0.clone())),
        );

        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
      },
      Op::Load(size, ptr) => {
        // channel, size and pointer
        let mut lookup_args = vec![
          state.gate(sel, konst(memory_channel())),
          state.gate(sel, konst(G::from_usize(*size))),
          state.gate(sel, state.map[*ptr].0.clone()),
        ];
        // loaded values
        let values: Vec<Expr> = (0..*size)
          .map(|_| {
            let col = state.next_auxiliary();
            state.map.push((col.clone(), 1));
            col
          })
          .collect();
        lookup_args.extend(values.into_iter().map(|col| state.gate(sel, col)));

        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
      },
      // The message is diagnostic only — it never enters the constraint
      // system, so a labelled and an unlabelled assert are identical in
      // the circuit.
      Op::AssertEq(xs, ys, _) => {
        assert_eq!(xs.len(), ys.len());
        for (x, y) in xs.iter().zip(ys) {
          let (x, _) = &state.map[*x];
          let (y, _) = &state.map[*y];
          state.constraints.zeros.push(sel.clone() * (x.clone() - y.clone()));
        }
      },
      Op::IOGetInfo(_, _) => (0..2).for_each(|_| {
        let col = state.next_auxiliary();
        state.map.push((col, 1));
      }),
      Op::IORead(_, _, len) => (0..*len).for_each(|_| {
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
      Op::U8Add(i, j) => {
        // The add lookup pins only the low byte `z = (x + y) mod 256`. The
        // carry is then `c = (x + y - z) / 256`, a compound expression that
        // needs no auxiliary column or lookup output.
        let (x, x_deg) = state.map[*i].clone();
        let (y, y_deg) = state.map[*j].clone();
        let z = state.next_auxiliary();
        let lookup_args = vec![
          state.gate(sel, konst(u8_add_channel())),
          state.gate(sel, x.clone()),
          state.gate(sel, y.clone()),
          state.gate(sel, z.clone()),
        ];
        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
        let carry = (x + y - z.clone()) * konst(*INV_256);
        state.map.push((z, 1));
        state.map.push((carry, x_deg.max(y_deg).max(1)));
      },
      Op::U8Mul(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::Mul,
        u8_mul_channel(),
        sel.clone(),
        state,
      ),
      Op::U8Sub(i, j) => {
        // The sub lookup pins only the low byte `z = (x - y) mod 256`. Since
        // `z + y = x (mod 256)`, the borrow is `c = (z + y - x) / 256`, a
        // compound expression that needs no auxiliary column or lookup output.
        let (x, x_deg) = state.map[*i].clone();
        let (y, y_deg) = state.map[*j].clone();
        let z = state.next_auxiliary();
        let lookup_args = vec![
          state.gate(sel, konst(u8_sub_channel())),
          state.gate(sel, x.clone()),
          state.gate(sel, y.clone()),
          state.gate(sel, z.clone()),
        ];
        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
        let borrow = (z.clone() + y - x) * konst(*INV_256);
        state.map.push((z, 1));
        state.map.push((borrow, x_deg.max(y_deg).max(1)));
      },
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
      Op::U8ChainRotr7(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::ChainRotr7,
        u8_chain_rotr7_channel(),
        sel.clone(),
        state,
      ),
      Op::U8ChainRotr4(i, j) => bytes2_constraints(
        *i,
        *j,
        &Bytes2Op::ChainRotr4,
        u8_chain_rotr4_channel(),
        sel.clone(),
        state,
      ),
      Op::U8RangeCheck(i, j) => {
        // Pure range-check lookup: no output columns (the `u8` results alias
        // the inputs), just require `(i, j)` from the byte chip.
        let x = state.map[*i].0.clone();
        let y = state.map[*j].0.clone();
        let lookup_args = vec![
          state.gate(sel, konst(u8_range_check_channel())),
          state.gate(sel, x),
          state.gate(sel, y),
        ];
        let lookup = state.next_lookup();
        combine_lookup_args(lookup, lookup_args);
        lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
      },
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
          bytes.iter().enumerate().fold(konst(G::ZERO), |acc, (k, b)| {
            acc + b.clone() * konst(base(k))
          })
        };
        state.constraints.zeros.push(sel.clone() * (a - recompose(&x_bytes)));
        state.constraints.zeros.push(sel.clone() * (b - recompose(&z_bytes)));

        // Carry chain: a + c + 1 = b + carry * 2^32
        let mut carry = konst(G::ONE); // initial carry = 1 for strict less-than
        for k in 0..4 {
          let sum = x_bytes[k].clone() + y_bytes[k].clone() + carry;
          carry = (sum - z_bytes[k].clone()) * konst(*INV_256);
          state.constraints.zeros.push(
            sel.clone() * (carry.clone() * (carry.clone() - konst(G::ONE))),
          );
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
          let lookup_args = vec![
            state.gate(sel, konst(rc_channel)),
            state.gate(sel, pair.0.clone()),
            state.gate(sel, pair.1.clone()),
          ];
          let lookup = state.next_lookup();
          combine_lookup_args(lookup, lookup_args);
          lookup.multiplicity = lookup.multiplicity.clone() + sel.clone();
        }

        // Output: 1 - carry
        let output = konst(G::ONE) - carry;
        state.map.push((output, 1));
      },
      Op::IOSetInfo(..) | Op::IOWrite(..) | Op::Debug(..) => (),
      Op::UnconstrainedBigUintDivMod(_, _) => {
        // Unconstrained: outputs are two fresh witness columns holding the
        // quotient/remainder list-head pointers. Mirrors `IORead`'s shape —
        // no constraint relation, just two new auxiliary slots. Verification
        // (`q*b + r == a`, `r < b`) is the caller's responsibility in
        // constrained code.
        for _ in 0..2 {
          let col = state.next_auxiliary();
          state.map.push((col, 1));
        }
      },
      Op::UnconstrainedGToBytes(_) => {
        // Unconstrained hint bytes: 8 fresh auxiliary columns, no relation,
        // no lookup. The caller pins them (range checks + recomposition +
        // canonicality asserts) in constrained code.
        for _ in 0..8 {
          let col = state.next_auxiliary();
          state.map.push((col, 1));
        }
      },
      Op::UnconstrainedGInverse(_) => {
        // Unconstrained hint inverse: one fresh auxiliary column, no
        // relation. The caller pins it via multiply-and-assert.
        let col = state.next_auxiliary();
        state.map.push((col, 1));
      },
    }
  }
}

fn bytes1_constraints(
  byte: usize,
  op: &Bytes1Op,
  channel: G,
  sel: Expr,
  state: &mut ConstraintState,
) {
  let size = Bytes1.output_size(op);

  let mut lookup_args = vec![
    state.gate(&sel, konst(channel)),
    state.gate(&sel, state.map[byte].0.clone()),
  ];

  let output: Vec<Expr> = (0..size)
    .map(|_| {
      let col = state.next_auxiliary();
      state.map.push((col.clone(), 1));
      col
    })
    .collect();
  lookup_args.extend(output.into_iter().map(|col| state.gate(&sel, col)));

  let lookup = state.next_lookup();
  combine_lookup_args(lookup, lookup_args);
  lookup.multiplicity = lookup.multiplicity.clone() + sel;
}

fn bytes2_constraints(
  i: usize,
  j: usize,
  op: &Bytes2Op,
  channel: G,
  sel: Expr,
  state: &mut ConstraintState,
) {
  let size = Bytes2.output_size(op);

  let mut lookup_args = vec![
    state.gate(&sel, konst(channel)),
    state.gate(&sel, state.map[i].0.clone()),
    state.gate(&sel, state.map[j].0.clone()),
  ];

  let output: Vec<Expr> = (0..size)
    .map(|_| {
      let col = state.next_auxiliary();
      state.map.push((col.clone(), 1));
      col
    })
    .collect();
  lookup_args.extend(output.into_iter().map(|col| state.gate(&sel, col)));

  let lookup = state.next_lookup();
  combine_lookup_args(lookup, lookup_args);
  lookup.multiplicity = lookup.multiplicity.clone() + sel;
}

fn combine_lookup_args(
  lookup: &mut Lookup<Expr>,
  args: impl IntoIterator<Item = Expr>,
) {
  let mut args_iterator = args.into_iter();
  lookup.args.iter_mut().zip(args_iterator.by_ref()).for_each(
    |(arg, value)| {
      *arg = arg.clone() + value;
    },
  );
  lookup.args.extend(args_iterator);
}
