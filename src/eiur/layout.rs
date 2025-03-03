use binius_field::{BinaryField8b, BinaryField64b, BinaryField128b, arch::OptimalUnderlier};

use super::ir::{Block, Ctrl, Function, Op};

/// The Eiur circuit field
pub type EiurField = BinaryField128b;
/// The field of bytes, which constitute Eiur data
pub type EiurByteField = BinaryField8b;
/// The field of multiplicities. Its multiplicative group is used to express
/// the multiplicity of lookups
pub type MultiplicityField = BinaryField64b;
pub type Underlier = OptimalUnderlier;

/// The circuit layout of a function.
/// The `auxiliaries` represent registers that hold temporary values
/// and can be shared by different circuit paths, since they never
/// overlap.
/// The `selectors` are bit values that identify which path the computation
/// took. Exactly one selector must be set.
/// The `shared_constraints` are constraint slots that can be shared in
/// different paths of the circuit.
#[derive(Clone, Default, Debug)]
pub struct Layout {
    pub inputs: u32,
    pub outputs: u32,
    pub auxiliaries: u32,
    pub require_hints: u32,
    pub selectors: u32,
    pub shared_constraints: u32,
}

#[derive(Clone, Default)]
struct LayoutBranchState {
    auxiliary_init: u32,
    auxiliary_max: u32,
    require_hints_init: u32,
    require_hints_max: u32,
    shared_constraint_init: u32,
    shared_constraint_max: u32,
}

impl Layout {
    // `save` before the first branch
    fn save(&self) -> LayoutBranchState {
        // auxiliary
        let auxiliary_init = self.auxiliaries;
        let auxiliary_max = auxiliary_init;
        // require hints
        let require_hints_init = self.require_hints;
        let require_hints_max = require_hints_init;
        // shared constraints
        let shared_constraint_init = self.shared_constraints;
        let shared_constraint_max = shared_constraint_init;
        LayoutBranchState {
            auxiliary_init,
            auxiliary_max,
            require_hints_init,
            require_hints_max,
            shared_constraint_init,
            shared_constraint_max,
        }
    }

    // `restore` before new branches
    fn restore(&mut self, state: &mut LayoutBranchState) {
        // auxiliary
        state.auxiliary_max = state.auxiliary_max.max(self.auxiliaries);
        self.auxiliaries = state.auxiliary_init;
        // require hints
        state.require_hints_max = state.require_hints_max.max(self.require_hints);
        self.require_hints = state.require_hints_init;
        // shared constraints
        state.shared_constraint_max = state.shared_constraint_max.max(self.shared_constraints);
        self.shared_constraints = state.shared_constraint_init;
    }

    // `finish` at the end
    fn finish(&mut self, state: &LayoutBranchState) {
        self.auxiliaries = state.auxiliary_max;
        self.require_hints = state.require_hints_max;
        self.shared_constraints = state.shared_constraint_max;
    }
}

pub fn func_layout(func: &Function) -> Layout {
    let mut layout = Layout {
        inputs: func.input_size,
        outputs: func.output_size,
        ..Default::default()
    };
    block_layout(&func.body, &mut layout);
    layout
}

pub fn block_layout(block: &Block, layout: &mut Layout) {
    let op_layout = |op| op_layout(op, layout);
    block.ops.iter().for_each(op_layout);
    match block.ctrl.as_ref() {
        Ctrl::If(_, t, f) => {
            let mut state = layout.save();
            // This auxiliary is for proving inequality
            layout.auxiliaries += 1;
            block_layout(t, layout);
            layout.restore(&mut state);
            block_layout(f, layout);
            layout.finish(&state);
        }
        Ctrl::If64(_, t, f) => {
            let mut state = layout.save();
            // These auxiliaries are for proving inequality
            layout.auxiliaries += 8;
            block_layout(t, layout);
            layout.restore(&mut state);
            block_layout(f, layout);
            layout.finish(&state);
        }
        Ctrl::Return(_, rs) => {
            // One selector per return
            layout.selectors += 1;
            // Each output must equal its respective return variable,
            // thus one constraint per return variable
            layout.shared_constraints +=
                u32::try_from(rs.len()).expect("Failed to convert usize to u32");
        }
    }
}

pub fn op_layout(op: &Op, layout: &mut Layout) {
    match op {
        Op::Prim(..) | Op::Xor(..) => {}
        Op::And(..) => {
            // `And` is achieved by multiplication. Since we do not want
            // expressions of order greater than 1, we create a new auxiliary
            // and constrain it to be equal to the product of the two expressions
            layout.shared_constraints += 1;
            layout.auxiliaries += 1;
        }
        Op::Add(..) | Op::Lt(..) | Op::Sub(..) => {
            // uses the addition gadget which outputs 8 bytes of sum
            // plus 1 byte of carry
            layout.auxiliaries += 9;
        }
        Op::Mul(..) => {
            // uses the multiplication gadget which outputs 8 bytes
            layout.auxiliaries += 8;
        }
        Op::Call(_, _, out_size) => {
            layout.auxiliaries += out_size;
            layout.require_hints += 1;
        }
    }
}
