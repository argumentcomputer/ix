use std::ops::{Add, AddAssign, Mul, Sub};

use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::oracle::OracleId;
use binius_field::{Field, TowerField, underlier::WithUnderlier};

use super::{
    ir::{Block, Ctrl, FuncIdx, Function, Op, Prim, SelIdx, ValIdx},
    layout::{B1, B8, B64, Layout},
};

#[derive(Clone, Debug)]
pub enum Expr {
    Const(B64),
    Var(OracleId),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, u64),
}

impl Mul for Expr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Const(B64::ONE), b) => b,
            (a, Expr::Const(B64::ONE)) => a,
            (Expr::Const(a), Expr::Const(b)) => Expr::Const(a * b),
            (a, b) => Self::Mul(a.into(), b.into()),
        }
    }
}

impl AddAssign for Expr {
    fn add_assign(&mut self, rhs: Expr) {
        *self = self.clone() + rhs;
    }
}

impl Add for Expr {
    type Output = Self;

    fn add(self, rhs: Expr) -> Self {
        match (self, rhs) {
            (Expr::Const(B64::ZERO), b) => b,
            (a, Expr::Const(B64::ZERO)) => a,
            (Expr::Const(a), Expr::Const(b)) => Expr::Const(a + b),
            (a, b) => Self::Add(a.into(), b.into()),
        }
    }
}

impl Sub for Expr {
    type Output = Self;

    // Subtraction is the same thing as addition in Binius
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: Expr) -> Self {
        self + rhs
    }
}

impl Expr {
    fn zero() -> Self {
        Self::Const(B64::ZERO)
    }

    fn one() -> Self {
        Self::Const(B64::ONE)
    }
}

#[derive(Clone)]
pub struct Constraints {
    pub shared_constraints: Vec<Expr>,
    pub unique_constraints: Vec<Expr>,
    pub sends: Vec<(Channel, Expr, Vec<Expr>)>,
    pub requires: Vec<(Channel, Expr, OracleId, Vec<Expr>)>,
    pub topmost_selector: Expr,
    pub io: Vec<OracleId>,
    pub multiplicity: OracleId,
}

#[derive(Clone)]
pub enum Channel {
    Add,
    Mul,
    Fun(FuncIdx),
    Mem(u32),
}

impl Constraints {
    pub fn new(function: &Function, layout: &Layout, columns: &Columns) -> Self {
        let shared_constraints = vec![Expr::zero(); layout.shared_constraints as usize];
        let unique_constraints = vec![];
        let sends = vec![];
        let requires = vec![];
        let topmost_selector = block_selector(&function.body, columns);
        let mut io = columns.inputs.clone();
        io.extend(columns.outputs.iter().cloned());
        let multiplicity = columns.multiplicity;
        Self {
            shared_constraints,
            unique_constraints,
            sends,
            requires,
            topmost_selector,
            io,
            multiplicity,
        }
    }

    fn push_unique(&mut self, expr: Expr) {
        self.unique_constraints.push(expr);
    }

    fn send(&mut self, channel: Channel, sel: Expr, args: Vec<Expr>) {
        self.sends.push((channel, sel, args));
    }

    fn require(&mut self, channel: Channel, sel: Expr, prev_idx: OracleId, args: Vec<Expr>) {
        self.requires.push((channel, sel, prev_idx, args));
    }
}

#[derive(Clone, Default)]
struct ConstraintState {
    constraint_index: usize,
    u1_auxiliary_index: usize,
    u8_auxiliary_index: usize,
    u64_auxiliary_index: usize,
    var_map: Vec<Expr>,
}

impl ConstraintState {
    fn save(&self) -> Self {
        self.clone()
    }

    fn restore(&mut self, state: Self) {
        *self = state;
    }

    fn push_var(&mut self, expr: Expr) {
        self.var_map.push(expr);
    }

    fn get_var(&self, idx: ValIdx) -> &Expr {
        &self.var_map[idx.to_usize()]
    }

    #[allow(dead_code)]
    fn get_vars(&self, idx: ValIdx, offset: usize) -> &[Expr] {
        let idx = idx.to_usize();
        &self.var_map[idx..idx + offset]
    }

    fn bind_u1_column(&mut self, columns: &Columns) -> OracleId {
        let col = self.next_u1_column(columns);
        self.var_map.push(Expr::Var(col));
        col
    }

    #[allow(dead_code)]
    fn bind_u8_column(&mut self, columns: &Columns) -> OracleId {
        let col = self.next_u8_column(columns);
        self.var_map.push(Expr::Var(col));
        col
    }

    fn bind_u64_column(&mut self, columns: &Columns) -> OracleId {
        let col = self.next_u64_column(columns);
        self.var_map.push(Expr::Var(col));
        col
    }

    fn next_u1_column(&mut self, columns: &Columns) -> OracleId {
        let col = columns.u1_auxiliaries[self.u1_auxiliary_index];
        self.u1_auxiliary_index += 1;
        col
    }

    #[allow(dead_code)]
    fn next_u8_column(&mut self, columns: &Columns) -> OracleId {
        let col = columns.u8_auxiliaries[self.u8_auxiliary_index];
        self.u8_auxiliary_index += 1;
        col
    }

    fn next_u64_column(&mut self, columns: &Columns) -> OracleId {
        let col = columns.u64_auxiliaries[self.u64_auxiliary_index];
        self.u64_auxiliary_index += 1;
        col
    }

    fn add_shared_constraint(&mut self, constraints: &mut Constraints, expr: Expr) {
        constraints.shared_constraints[self.constraint_index] += expr;
        self.constraint_index += 1;
    }
}

#[derive(Clone, Default)]
pub struct Columns {
    pub inputs: Vec<OracleId>,
    pub outputs: Vec<OracleId>,
    pub u1_auxiliaries: Vec<OracleId>,
    pub u8_auxiliaries: Vec<OracleId>,
    pub u64_auxiliaries: Vec<OracleId>,
    pub multiplicity: OracleId,
    pub selectors: Vec<OracleId>,
}

impl Columns {
    pub fn get_selector(&self, idx: SelIdx) -> OracleId {
        self.selectors[idx.to_usize()]
    }

    pub fn from_layout(
        builder: &mut ConstraintSystemBuilder<'_>,
        layout: &Layout,
        log_n: u8,
    ) -> Self {
        let u1_level = B1::TOWER_LEVEL;
        let u8_level = B8::TOWER_LEVEL;
        let u64_level = B64::TOWER_LEVEL;
        let log_n = log_n as usize;
        let inputs = (0..layout.inputs)
            .map(|i| builder.add_committed(format!("input{i}"), log_n, u64_level))
            .collect();
        let outputs = (0..layout.outputs)
            .map(|i| builder.add_committed(format!("outputs{i}"), log_n, u64_level))
            .collect();
        let u1_auxiliaries = (0..layout.u1_auxiliaries)
            .map(|i| builder.add_committed(format!("u1_auxiliaries{i}"), log_n, u1_level))
            .collect();
        let u8_auxiliaries = (0..layout.u8_auxiliaries)
            .map(|i| builder.add_committed(format!("u8_auxiliaries{i}"), log_n, u8_level))
            .collect();
        let u64_auxiliaries = (0..layout.u64_auxiliaries)
            .map(|i| builder.add_committed(format!("u64_auxiliary{i}"), log_n, u64_level))
            .collect();
        let multiplicity = builder.add_committed("multiplicity", log_n, u64_level);
        let selectors = (0..layout.selectors)
            .map(|i| builder.add_committed(format!("selectors{i}"), log_n, u1_level))
            .collect();
        Self {
            inputs,
            outputs,
            u1_auxiliaries,
            u8_auxiliaries,
            u64_auxiliaries,
            multiplicity,
            selectors,
        }
    }
}

pub fn build_func_constraints(
    function: &Function,
    layout: &Layout,
    columns: &Columns,
) -> Constraints {
    let mut state = ConstraintState::default();
    columns
        .inputs
        .iter()
        .for_each(|input| state.var_map.push(Expr::Var(*input)));
    let mut constraints = Constraints::new(function, layout, columns);
    collect_block_constraints(&function.body, &mut state, columns, &mut constraints);
    constraints
}

fn collect_block_constraints(
    block: &Block,
    state: &mut ConstraintState,
    columns: &Columns,
    constraints: &mut Constraints,
) {
    let sel = block_selector(block, columns);
    block
        .ops
        .iter()
        .for_each(|op| collect_op_constraints(op, state, columns, constraints, &sel));
    match block.ctrl.as_ref() {
        Ctrl::If(b, t, f) => {
            let b = state.get_var(*b).clone();
            let saved = state.save();
            let t_sel = block_selector(t, columns);
            let d = Expr::Var(state.next_u64_column(columns));
            constraints.push_unique(t_sel * (b.clone() * d - Expr::one()));
            collect_block_constraints(t, state, columns, constraints);
            state.restore(saved);
            let f_sel = block_selector(f, columns);
            constraints.push_unique(f_sel * b);
            collect_block_constraints(f, state, columns, constraints);
        }
        Ctrl::Return(id, rs) => {
            let sel_col = columns.get_selector(*id);
            for (r, o) in rs.iter().zip(columns.outputs.iter()) {
                let r = state.get_var(*r).clone();
                let o = Expr::Var(*o);
                let sel = Expr::Var(sel_col);
                state.add_shared_constraint(constraints, sel * (r - o));
            }
        }
    }
}

fn collect_op_constraints(
    op: &Op,
    state: &mut ConstraintState,
    columns: &Columns,
    constraints: &mut Constraints,
    sel: &Expr,
) {
    match op {
        Op::Prim(Prim::Bool(a)) => {
            let a = B64::from_underlier(*a as u64);
            state.push_var(Expr::Const(a));
        }
        Op::Prim(Prim::U64(a)) => {
            let a = B64::from_underlier(*a);
            state.push_var(Expr::Const(a));
        }
        Op::Add(a, b) => {
            let a = state.get_var(*a).clone();
            let b = state.get_var(*b).clone();
            // 8 bytes of result
            let c = Expr::Var(state.bind_u64_column(columns));
            // 1 byte of carry, which is not bound
            let carry = Expr::Var(state.next_u1_column(columns));
            let args = [a, b, c, carry];
            constraints.send(Channel::Add, sel.clone(), args.to_vec());
        }
        Op::Sub(c, b) => {
            // `c - b = a` is equivalent to `a + b = c`.
            let a = Expr::Var(state.bind_u64_column(columns));
            let b = state.get_var(*b).clone();
            let c = state.get_var(*c).clone();
            let carry = Expr::Var(state.next_u1_column(columns));
            let args = [a, b, c, carry];
            constraints.send(Channel::Add, sel.clone(), args.to_vec());
        }
        Op::Lt(c, b) => {
            // `c < b` is equivalent to `c - b` underflowing, which is
            // equivalent to the addition in `a + b = c` overflowing
            // Note that the result of the subtraction is not bound
            let a = Expr::Var(state.next_u64_column(columns));
            let b = state.get_var(*b).clone();
            let c = state.get_var(*c).clone();
            // The carry is bound
            let carry = Expr::Var(state.bind_u1_column(columns));
            let args = [a, b, c, carry];
            constraints.send(Channel::Add, sel.clone(), args.to_vec());
        }
        Op::Mul(a, b) => {
            let a = state.get_var(*a).clone();
            let b = state.get_var(*b).clone();
            // 8 bytes of result
            let c = Expr::Var(state.bind_u64_column(columns));
            let args = [a, b, c];
            constraints.send(Channel::Mul, sel.clone(), args.to_vec());
        }
        Op::Xor(a, b) => {
            let a = state.get_var(*a).clone();
            let b = state.get_var(*b).clone();
            state.push_var(a + b);
        }
        Op::And(a, b) => {
            let a = state.get_var(*a).clone();
            let b = state.get_var(*b).clone();
            let c = Expr::Var(state.bind_u1_column(columns));
            state.push_var(c.clone());
            state.add_shared_constraint(constraints, sel.clone() * (c - a * b));
        }
        Op::Store(values) => {
            let len = values
                .len()
                .try_into()
                .expect("Error: too many arguments to store");
            let mut args = [Expr::Var(state.bind_u64_column(columns))].to_vec();
            args.extend(values.iter().map(|value| state.get_var(*value).clone()));
            let require = state.next_u64_column(columns);
            constraints.require(Channel::Mem(len), sel.clone(), require, args);
        }
        Op::Load(len, ptr) => {
            let mut args = [state.get_var(*ptr).clone()].to_vec();
            let values = (0..*len).map(|_| Expr::Var(state.bind_u64_column(columns)));
            args.extend(values);
            let require = state.next_u64_column(columns);
            constraints.require(Channel::Mem(*len), sel.clone(), require, args);
        }
        Op::Call(f, args, out_size) => {
            let mut args = args
                .iter()
                .map(|a| state.get_var(*a).clone())
                .collect::<Vec<_>>();
            let out = (0..*out_size).map(|_| Expr::Var(state.bind_u64_column(columns)));
            args.extend(out);
            let require = state.next_u64_column(columns);
            constraints.require(Channel::Fun(*f), sel.clone(), require, args);
        }
    }
}

fn block_selector(block: &Block, columns: &Columns) -> Expr {
    block
        .return_idents
        .iter()
        .map(|id| Expr::Var(columns.get_selector(*id)))
        .fold(Expr::zero(), |var, acc| acc + var)
}
