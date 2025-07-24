use multi_stark::{
    builder::symbolic::SymbolicExpression, lookup::Lookup, p3_field::PrimeCharacteristicRing,
};
use std::ops::Range;

use super::{
    G,
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
    trace::Channel,
};

#[macro_export]
macro_rules! sym_var {
    ($a:expr) => {{
        use multi_stark::builder::symbolic::*;
        let entry = Entry::Main { offset: 0 };
        SymbolicExpression::Variable(SymbolicVariable::new(entry, $a))
    }};
}

type Expr = SymbolicExpression<G>;
type Degree = u8;

/// Holds data for a function circuit.
pub struct Constraints {
    pub zeros: Vec<Expr>,
    pub selectors: Range<usize>,
    pub width: usize,
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
        sym_var!(self.column - 1)
    }

    fn save(&mut self) -> SharedState {
        SharedState {
            column: self.column,
            lookup: self.lookup,
            map_len: self.map.len(),
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn restore(&mut self, init: SharedState) {
        self.column = init.column;
        self.lookup = init.lookup;
        self.map.truncate(init.map_len);
    }
}

impl Toplevel {
    pub fn build_constraints(&self, function_index: usize) -> (Constraints, Vec<Lookup<Expr>>) {
        let function = &self.functions[function_index];
        let empty_lookup = Lookup {
            multiplicity: Expr::Constant(G::ZERO),
            args: vec![],
        };
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
            lookups: vec![empty_lookup; function.layout.lookups],
            constraints,
        };
        function.build_constraints(&mut state, self);
        (state.constraints, state.lookups)
    }
}

impl Function {
    fn build_constraints(&self, state: &mut ConstraintState, toplevel: &Toplevel) {
        // the first columns are occupied by the input, which is also mapped
        state.column += self.layout.input_size;
        (0..self.layout.input_size).for_each(|i| state.map.push((sym_var!(i), 1)));
        // then comes the selectors, which are not mapped
        let init_sel = state.column;
        let final_sel = state.column + self.layout.selectors;
        state.constraints.selectors = init_sel..final_sel;
        state.column = final_sel;
        // the multiplicity occupies another column
        let multiplicity = sym_var!(state.column);
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
    fn collect_constraints(&self, sel: Expr, state: &mut ConstraintState, toplevel: &Toplevel) {
        self.ops
            .iter()
            .for_each(|op| op.collect_constraints(&sel, state));
        self.ctrl.collect_constraints(sel, state, toplevel);
    }

    fn get_block_selector(&self, state: &mut ConstraintState) -> Expr {
        (self.min_sel_included..self.max_sel_excluded)
            .map(|i| sym_var!(state.selector_index(i)))
            .fold(Expr::Constant(G::ZERO), |var, acc| var + acc)
    }
}

impl Ctrl {
    #[allow(clippy::needless_pass_by_value)]
    fn collect_constraints(&self, sel: Expr, state: &mut ConstraintState, toplevel: &Toplevel) {
        match self {
            Ctrl::Return(_, values) => {
                // channel and function index
                let mut vector = vec![
                    sel.clone() * Channel::Function.to_field(),
                    sel.clone() * state.function_index,
                ];
                // input
                vector.extend(
                    (0..state.layout.input_size).map(|arg| sel.clone() * state.map[arg].0.clone()),
                );
                // output
                vector.extend(
                    values
                        .iter()
                        .map(|arg| sel.clone() * state.map[*arg].0.clone()),
                );
                let mut values_iter = vector.into_iter();
                let lookup = &mut state.lookups[0];
                lookup
                    .args
                    .iter_mut()
                    .zip(values_iter.by_ref())
                    .for_each(|(arg, value)| {
                        *arg += value;
                    });
                lookup.args.extend(values_iter);
                // multiplicity is already set
            }
            Ctrl::Match(var, cases, def) => {
                let (var, _) = state.map[*var].clone();
                for (&value, branch) in cases.iter() {
                    let init = state.save();
                    let branch_sel = branch.get_block_selector(state);
                    state
                        .constraints
                        .zeros
                        .push(branch_sel.clone() * (var.clone() - Expr::from(value)));
                    branch.collect_constraints(branch_sel, state, toplevel);
                    state.restore(init);
                }
                def.iter().for_each(|branch| {
                    let init = state.save();
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
                    state.restore(init);
                })
            }
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
            }
            Op::Sub(a, b) => {
                let (a, a_deg) = &state.map[*a];
                let (b, b_deg) = &state.map[*b];
                let deg = a_deg.max(b_deg);
                state.map.push((a.clone() - b.clone(), *deg));
            }
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
            }
            Op::Call(function_index, inputs, output_size) => {
                // channel and function index
                let mut vector = vec![
                    sel.clone() * Channel::Function.to_field(),
                    sel.clone() * G::from_usize(*function_index),
                ];
                // input
                vector.extend(
                    inputs
                        .iter()
                        .map(|arg| sel.clone() * state.map[*arg].0.clone()),
                );
                // output
                let output = (0..*output_size).map(|_| {
                    let col = state.next_auxiliary();
                    state.map.push((col.clone(), 1));
                    col
                });
                vector.extend(output);
                let mut values_iter = vector.into_iter();
                let lookup = state.next_lookup();
                lookup
                    .args
                    .iter_mut()
                    .zip(values_iter.by_ref())
                    .for_each(|(arg, value)| {
                        *arg += value;
                    });
                lookup.args.extend(values_iter);
                lookup.multiplicity += sel.clone();
            }
            Op::Store(values) => {
                let size = values.len();
                // channel, function index and pointer
                let ptr = state.next_auxiliary();
                state.map.push((ptr.clone(), 1));
                let mut vector = vec![
                    sel.clone() * Channel::Memory.to_field(),
                    sel.clone() * G::from_usize(size),
                    sel.clone() * ptr.clone(),
                ];
                // stored values
                vector.extend(
                    values
                        .iter()
                        .map(|value| sel.clone() * state.map[*value].0.clone()),
                );
                let mut values_iter = vector.into_iter();
                let lookup = state.next_lookup();
                lookup
                    .args
                    .iter_mut()
                    .zip(values_iter.by_ref())
                    .for_each(|(arg, value)| {
                        *arg += value;
                    });
                lookup.args.extend(values_iter);
                lookup.multiplicity += sel.clone();
            }
            Op::Load(size, ptr) => {
                // channel, size and pointer
                let mut vector = vec![
                    sel.clone() * Channel::Memory.to_field(),
                    sel.clone() * G::from_usize(*size),
                    sel.clone() * state.map[*ptr].0.clone(),
                ];
                // loaded values
                let values = (0..*size).map(|_| {
                    let col = state.next_auxiliary();
                    state.map.push((col.clone(), 1));
                    col
                });
                vector.extend(values);
                let mut values_iter = vector.into_iter();
                let lookup = state.next_lookup();
                lookup
                    .args
                    .iter_mut()
                    .zip(values_iter.by_ref())
                    .for_each(|(arg, value)| {
                        *arg += value;
                    });
                lookup.args.extend(values_iter);
                lookup.multiplicity += sel.clone();
            }
        }
    }
}
