use binius_field::{
    BinaryField1b, BinaryField8b, BinaryField32b, BinaryField64b, BinaryField128b,
    arch::OptimalUnderlier,
};

use super::ir::{Block, Ctrl, Function, Op};

pub type B1 = BinaryField1b;
pub type B8 = BinaryField8b;
pub type B32 = BinaryField32b;
pub type B64 = BinaryField64b;
pub type B128 = BinaryField128b;
pub type U = OptimalUnderlier;

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
    pub u1_auxiliaries: u32,
    pub u8_auxiliaries: u32,
    pub u64_auxiliaries: u32,
    pub selectors: u32,
    pub shared_constraints: u32,
}

#[derive(Clone, Default)]
struct LayoutBranchState {
    u1_auxiliary_init: u32,
    u1_auxiliary_max: u32,
    u8_auxiliary_init: u32,
    u8_auxiliary_max: u32,
    u64_auxiliary_init: u32,
    u64_auxiliary_max: u32,
    shared_constraint_init: u32,
    shared_constraint_max: u32,
}

impl Layout {
    // `save` before the first branch
    fn save(&self) -> LayoutBranchState {
        // auxiliaries
        let u1_auxiliary_init = self.u1_auxiliaries;
        let u1_auxiliary_max = u1_auxiliary_init;
        let u8_auxiliary_init = self.u8_auxiliaries;
        let u8_auxiliary_max = u8_auxiliary_init;
        let u64_auxiliary_init = self.u64_auxiliaries;
        let u64_auxiliary_max = u64_auxiliary_init;
        // shared constraints
        let shared_constraint_init = self.shared_constraints;
        let shared_constraint_max = shared_constraint_init;
        LayoutBranchState {
            u1_auxiliary_init,
            u1_auxiliary_max,
            u8_auxiliary_init,
            u8_auxiliary_max,
            u64_auxiliary_init,
            u64_auxiliary_max,
            shared_constraint_init,
            shared_constraint_max,
        }
    }

    // `restore` before new branches
    fn restore(&mut self, state: &mut LayoutBranchState) {
        // auxiliaries
        state.u1_auxiliary_max = state.u1_auxiliary_max.max(self.u1_auxiliaries);
        self.u1_auxiliaries = state.u1_auxiliary_init;
        state.u8_auxiliary_max = state.u8_auxiliary_max.max(self.u8_auxiliaries);
        self.u8_auxiliaries = state.u8_auxiliary_init;
        state.u64_auxiliary_max = state.u64_auxiliary_max.max(self.u64_auxiliaries);
        self.u64_auxiliaries = state.u64_auxiliary_init;
        // shared constraints
        state.shared_constraint_max = state.shared_constraint_max.max(self.shared_constraints);
        self.shared_constraints = state.shared_constraint_init;
    }

    // `finish` at the end
    fn finish(&mut self, state: &LayoutBranchState) {
        self.u1_auxiliaries = state.u1_auxiliary_max;
        self.u8_auxiliaries = state.u8_auxiliary_max;
        self.u64_auxiliaries = state.u64_auxiliary_max;
        self.shared_constraints = state.shared_constraint_max;
    }
}

pub fn func_layout(func: &Function, mem_sizes: &mut Vec<u32>) -> Layout {
    let mut layout = Layout {
        inputs: func.input_size,
        outputs: func.output_size,
        ..Default::default()
    };
    block_layout(&func.body, &mut layout, mem_sizes);
    layout
}

pub fn block_layout(block: &Block, layout: &mut Layout, mem_sizes: &mut Vec<u32>) {
    let op_layout = |op| op_layout(op, layout, mem_sizes);
    block.ops.iter().for_each(op_layout);
    match block.ctrl.as_ref() {
        Ctrl::If(_, t, f) => {
            let mut state = layout.save();
            // This auxiliary is for proving inequality
            layout.u64_auxiliaries += 1;
            block_layout(t, layout, mem_sizes);
            layout.restore(&mut state);
            block_layout(f, layout, mem_sizes);
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

pub fn op_layout(op: &Op, layout: &mut Layout, mem_sizes: &mut Vec<u32>) {
    match op {
        Op::Prim(..) | Op::Xor(..) => {}
        Op::And(..) => {
            // `And` is achieved by multiplication. Since we do not want
            // expressions of order greater than 1, we create a new auxiliary
            // and constrain it to be equal to the product of the two expressions
            layout.shared_constraints += 1;
            layout.u1_auxiliaries += 1;
        }
        Op::Add(..) | Op::Lt(..) | Op::Sub(..) => {
            // uses the addition gadget which outputs 8 bytes of sum
            // plus 1 byte of carry
            layout.u64_auxiliaries += 1;
            layout.u1_auxiliaries += 1;
        }
        Op::Mul(..) => {
            // uses the multiplication gadget which outputs 8 bytes
            layout.u64_auxiliaries += 1;
        }
        Op::Store(values) => {
            let len = values
                .len()
                .try_into()
                .expect("Number of arguments exceeds 256.");
            if !mem_sizes.contains(&len) {
                mem_sizes.push(len)
            }
            // outputs a pointer and a require hint
            layout.u64_auxiliaries += 2;
        }
        Op::Load(len, _) => {
            if !mem_sizes.contains(len) {
                mem_sizes.push(*len)
            }
            // outputs the loaded values and a require hint
            layout.u64_auxiliaries += *len + 1;
        }
        Op::Call(_, _, out_size) => {
            layout.u64_auxiliaries += out_size + 1;
        }
    }
}
