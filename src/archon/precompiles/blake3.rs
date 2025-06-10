#![allow(dead_code)]

use crate::archon::arith_expr::ArithExpr;
use crate::archon::circuit::CircuitModule;
use crate::archon::witness::WitnessModule;
use crate::archon::{ModuleId, OracleIdx};
use binius_circuits::arithmetic::u32::LOG_U32_BITS;
use binius_core::oracle::ShiftVariant;
use binius_field::{BinaryField1b, BinaryField32b, BinaryField128b, Field};
use binius_utils::checked_arithmetics::log2_ceil_usize;

const STATE_SIZE: usize = 32;
const SINGLE_COMPRESSION_N_VARS: usize = 6;
#[allow(clippy::cast_possible_truncation)]
const SINGLE_COMPRESSION_HEIGHT: usize = 2usize.pow(SINGLE_COMPRESSION_N_VARS as u32);
const ADDITION_OPERATIONS_NUMBER: usize = 6;
const PROJECTED_SELECTOR_INPUT: u64 = 0;
const PROJECTED_SELECTOR_OUTPUT: u64 = 57;
const OUT_HEIGHT: usize = 8;

const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

type B128 = BinaryField128b;
type B32 = BinaryField32b;
type B1 = BinaryField1b;

#[derive(Debug, Clone)]
pub struct Trace {
    state_trace: [Vec<u32>; STATE_SIZE],
    a_in_trace: Vec<u32>,
    b_in_trace: Vec<u32>,
    c_in_trace: Vec<u32>,
    d_in_trace: Vec<u32>,
    mx_in_trace: Vec<u32>,
    my_in_trace: Vec<u32>,

    a_0_tmp_trace: Vec<u32>,
    a_0_trace: Vec<u32>,
    d_in_xor_a_0_trace: Vec<u32>,
    d_0_trace: Vec<u32>,
    c_0_trace: Vec<u32>,
    _b_in_xor_c_0_trace: Vec<u32>,
    b_0_trace: Vec<u32>,
    a_1_tmp_trace: Vec<u32>,
    a_1_trace: Vec<u32>,
    _d_0_xor_a_1_trace: Vec<u32>,
    d_1_trace: Vec<u32>,
    c_1_trace: Vec<u32>,
    _b_0_xor_c_1_trace: Vec<u32>,
    _b_1_trace: Vec<u32>,

    _cin_trace: [Vec<u32>; ADDITION_OPERATIONS_NUMBER],
    cout_trace: [Vec<u32>; ADDITION_OPERATIONS_NUMBER],

    cv_trace: Vec<u32>,
    state_i_trace: Vec<u32>,
    state_i_8_trace: Vec<u32>,
    _state_i_xor_state_i_8_trace: Vec<u32>,
    _state_i_8_xor_cv_trace: Vec<u32>,
}

pub struct Blake3CompressionOracles {
    pub input: [OracleIdx; STATE_SIZE],
    pub output: [OracleIdx; STATE_SIZE],
}

#[allow(clippy::type_complexity)]
pub fn blake3_compress(
    traces: &Trace,
    traces_len: usize,
) -> Result<
    (
        Vec<CircuitModule>,
        Vec<WitnessModule>,
        Vec<u64>,
        Blake3CompressionOracles,
    ),
    anyhow::Error,
> {
    // FIXME: Implement modules' gluing

    let (compression_oracles, circuit_module_0, witness_module_0, height_0) =
        state_transition_module(0, traces, traces_len)?;
    let (circuit_module_1, witness_module_1, height_1) =
        additions_xor_rotates_module(1, traces, traces_len)?;
    let (circuit_module_2, witness_module_2, height_2) = cv_output_module(2, traces, traces_len)?;

    let witness_modules = vec![witness_module_0, witness_module_1, witness_module_2];
    let circuit_modules = vec![circuit_module_0, circuit_module_1, circuit_module_2];

    Ok((
        circuit_modules,
        witness_modules,
        vec![height_0, height_1, height_2],
        compression_oracles,
    ))
}

fn state_transition_module(
    id: ModuleId,
    traces: &Trace,
    traces_len: usize,
) -> Result<(Blake3CompressionOracles, CircuitModule, WitnessModule, u64), anyhow::Error> {
    let state_n_vars = log2_ceil_usize(traces_len * SINGLE_COMPRESSION_HEIGHT);
    let height = 2u64.pow(u32::try_from(state_n_vars)?);

    let mut circuit_module = CircuitModule::new(id);
    let state_transitions: [OracleIdx; STATE_SIZE] = array_util::try_from_fn(|xy| {
        circuit_module.add_committed::<B32>(&format!("state-transition-{:?}", xy))
    })?;

    let input: [OracleIdx; STATE_SIZE] = array_util::try_from_fn(|xy| {
        circuit_module.add_projected(
            &format!("input-{:?}", xy),
            state_transitions[xy],
            PROJECTED_SELECTOR_INPUT,
            SINGLE_COMPRESSION_HEIGHT,
        )
    })?;

    let output: [OracleIdx; STATE_SIZE] = array_util::try_from_fn(|xy| {
        circuit_module.add_projected(
            &format!("output-{:?}", xy),
            state_transitions[xy],
            PROJECTED_SELECTOR_OUTPUT,
            SINGLE_COMPRESSION_HEIGHT,
        )
    })?;
    circuit_module.freeze_oracles();

    let mut witness_module = circuit_module.init_witness_module()?;

    for (xy, trace) in traces.clone().state_trace.into_iter().enumerate() {
        let entry_id_xy = witness_module.new_entry();
        witness_module.push_u32s_to(trace, entry_id_xy);
        witness_module.bind_oracle_to::<B32>(state_transitions[xy], entry_id_xy);
    }

    witness_module.populate(height)?;

    Ok((
        Blake3CompressionOracles { input, output },
        circuit_module,
        witness_module,
        height,
    ))
}

fn additions_xor_rotates_module(
    id: ModuleId,
    traces: &Trace,
    traces_len: usize,
) -> Result<(CircuitModule, WitnessModule, u64), anyhow::Error> {
    let state_n_vars = log2_ceil_usize(traces_len * SINGLE_COMPRESSION_HEIGHT);

    let height = 2u64.pow(u32::try_from(state_n_vars + 5)?);
    let mut circuit_module = CircuitModule::new(id);

    let a_in = circuit_module.add_committed::<B1>("a_in")?;
    let b_in = circuit_module.add_committed::<B1>("b_in")?;
    let c_in = circuit_module.add_committed::<B1>("c_in")?;
    let d_in = circuit_module.add_committed::<B1>("d_in")?;
    let mx_in = circuit_module.add_committed::<B1>("mx_in")?;
    let my_in = circuit_module.add_committed::<B1>("my_in")?;

    let a_0 = circuit_module.add_committed::<B1>("a_0")?;
    let a_0_tmp = circuit_module.add_committed::<B1>("a_0_tmp")?;
    let c_0 = circuit_module.add_committed::<B1>("c_0")?;
    let a_1 = circuit_module.add_committed::<B1>("a_1")?;
    let a_1_tmp = circuit_module.add_committed::<B1>("a_1_tmp")?;
    let c_1 = circuit_module.add_committed::<B1>("c_1")?;

    let b_in_xor_c_0 = circuit_module.add_linear_combination("b_in_xor_c_0", B128::ZERO, [
        (b_in, B128::ONE),
        (c_0, B128::ONE),
    ])?;

    let d_in_xor_a_0 = circuit_module.add_linear_combination("d_in_xor_a_0", B128::ZERO, [
        (d_in, B128::ONE),
        (a_0, B128::ONE),
    ])?;

    let b_0 = circuit_module.add_shifted(
        "b_0",
        b_in_xor_c_0,
        32 - 12,
        LOG_U32_BITS,
        ShiftVariant::CircularLeft,
    )?;
    let d_0 = circuit_module.add_shifted(
        "d_0",
        d_in_xor_a_0,
        32 - 16,
        LOG_U32_BITS,
        ShiftVariant::CircularLeft,
    )?;

    let d_0_xor_a_1 = circuit_module.add_linear_combination("d_0_xor_a_1", B128::ZERO, [
        (d_0, B128::ONE),
        (a_1, B128::ONE),
    ])?;

    let b_0_xor_c_1 = circuit_module.add_linear_combination("b_0_xor_c_1", B128::ZERO, [
        (b_0, B128::ONE),
        (c_1, B128::ONE),
    ])?;

    let d_1 = circuit_module.add_shifted(
        "d_1",
        d_0_xor_a_1,
        32 - 8,
        LOG_U32_BITS,
        ShiftVariant::CircularLeft,
    )?;
    let _b_1 = circuit_module.add_shifted(
        "b_1",
        b_0_xor_c_1,
        32 - 7,
        LOG_U32_BITS,
        ShiftVariant::CircularLeft,
    )?;

    let couts: [OracleIdx; ADDITION_OPERATIONS_NUMBER] = array_util::try_from_fn(|xy| {
        circuit_module.add_committed::<B1>(&format!("cout-{:?}", xy))
    })?;
    let cins: [OracleIdx; ADDITION_OPERATIONS_NUMBER] = array_util::try_from_fn(|xy| {
        circuit_module.add_shifted(
            &format!("cin-{:?}", xy),
            couts[xy],
            1,
            5,
            ShiftVariant::LogicalLeft,
        )
    })?;

    let xins = [a_in, a_0_tmp, c_in, a_0, a_1_tmp, c_0];
    let yins = [b_in, mx_in, d_0, b_0, my_in, d_1];
    let zouts = [a_0_tmp, a_0, c_0, a_1_tmp, a_1, c_1];

    for xy in 0..ADDITION_OPERATIONS_NUMBER {
        circuit_module.assert_zero(
            "sum",
            [xins[xy], yins[xy], cins[xy], zouts[xy]],
            ArithExpr::Oracle(xins[xy])
                + ArithExpr::Oracle(yins[xy])
                + ArithExpr::Oracle(cins[xy])
                + ArithExpr::Oracle(zouts[xy]),
        );
        circuit_module.assert_zero(
            "carry",
            [xins[xy], yins[xy], cins[xy], couts[xy]],
            (ArithExpr::Oracle(xins[xy]) + ArithExpr::Oracle(cins[xy]))
                * (ArithExpr::Oracle(yins[xy]) + ArithExpr::Oracle(cins[xy]))
                + ArithExpr::Oracle(cins[xy])
                + ArithExpr::Oracle(couts[xy]),
        );
    }

    circuit_module.freeze_oracles();

    let mut witness_module = circuit_module.init_witness_module()?;

    let xin_traces = [
        traces.a_in_trace.clone(),
        traces.a_0_tmp_trace.clone(),
        traces.c_in_trace.clone(),
        traces.a_0_trace.clone(),
        traces.a_1_tmp_trace.clone(),
        traces.c_0_trace.clone(),
    ];
    let yin_traces = [
        traces.b_in_trace.clone(),
        traces.mx_in_trace.clone(),
        traces.d_0_trace.clone(),
        traces.b_0_trace.clone(),
        traces.my_in_trace.clone(),
        traces.d_1_trace.clone(),
    ];
    let zout_traces = [
        traces.a_0_tmp_trace.clone(),
        traces.a_0_trace.clone(),
        traces.c_0_trace.clone(),
        traces.a_1_tmp_trace.clone(),
        traces.a_1_trace.clone(),
        traces.c_1_trace.clone(),
    ];

    for xy in 0..ADDITION_OPERATIONS_NUMBER {
        let cout_entry = witness_module.new_entry();
        let xin_entry = witness_module.new_entry();
        let yin_entry = witness_module.new_entry();
        let zout_entry = witness_module.new_entry();

        witness_module.push_u32s_to(xin_traces[xy].clone(), xin_entry);
        witness_module.push_u32s_to(yin_traces[xy].clone(), yin_entry);
        witness_module.push_u32s_to(traces.cout_trace[xy].clone(), cout_entry);
        witness_module.push_u32s_to(zout_traces[xy].clone(), zout_entry);

        witness_module.bind_oracle_to::<B1>(xins[xy], xin_entry);
        witness_module.bind_oracle_to::<B1>(yins[xy], yin_entry);
        witness_module.bind_oracle_to::<B1>(couts[xy], cout_entry);
        witness_module.bind_oracle_to::<B1>(zouts[xy], zout_entry);
    }

    // not to forget about d_in
    let d_in_entry = witness_module.new_entry();
    witness_module.push_u32s_to(traces.d_in_trace.clone(), d_in_entry);
    witness_module.bind_oracle_to::<B1>(d_in, d_in_entry);

    witness_module.populate(height)?;

    Ok((circuit_module, witness_module, height))
}

fn cv_output_module(
    id: ModuleId,
    traces: &Trace,
    traces_len: usize,
) -> Result<(CircuitModule, WitnessModule, u64), anyhow::Error> {
    let out_n_vars = log2_ceil_usize(traces_len * OUT_HEIGHT);

    let height = 2u64.pow(u32::try_from(out_n_vars)?);
    let mut circuit_module = CircuitModule::new(id);

    let cv = circuit_module.add_committed::<B32>("cv")?;
    let state_i = circuit_module.add_committed::<B32>("state_i")?;
    let state_i_8 = circuit_module.add_committed::<B32>("state_i_8")?;

    let _state_i_xor_state_i_8 =
        circuit_module.add_linear_combination("state_i_xor_state_i_8", B128::ZERO, [
            (state_i, B128::ONE),
            (state_i_8, B128::ONE),
        ])?;

    let _cv_oracle_xor_state_i_8 =
        circuit_module.add_linear_combination("cv_oracle_xor_state_i_8", B128::ZERO, [
            (cv, B128::ONE),
            (state_i_8, B128::ONE),
        ])?;

    circuit_module.freeze_oracles();

    let mut witness_module = circuit_module.init_witness_module()?;

    let cv_entry = witness_module.new_entry();
    let state_i_entry = witness_module.new_entry();
    let state_i_8_entry = witness_module.new_entry();

    witness_module.push_u32s_to(traces.cv_trace.clone(), cv_entry);
    witness_module.push_u32s_to(traces.state_i_trace.clone(), state_i_entry);
    witness_module.push_u32s_to(traces.state_i_8_trace.clone(), state_i_8_entry);

    witness_module.bind_oracle_to::<B32>(cv, cv_entry);
    witness_module.bind_oracle_to::<B32>(state_i, state_i_entry);
    witness_module.bind_oracle_to::<B32>(state_i_8, state_i_8_entry);

    witness_module.populate(height)?;

    Ok((circuit_module, witness_module, height))
}

#[cfg(test)]
pub mod tests {
    use crate::archon::circuit::{CircuitModule, init_witness_modules};
    use crate::archon::precompiles::blake3::{
        ADDITION_OPERATIONS_NUMBER, B1, B128, Blake3CompressionOracles, IV, MSG_PERMUTATION,
        OUT_HEIGHT, PROJECTED_SELECTOR_OUTPUT, SINGLE_COMPRESSION_HEIGHT, STATE_SIZE, Trace,
        additions_xor_rotates_module, cv_output_module, state_transition_module,
    };
    use crate::archon::protocol::validate_witness;
    use crate::archon::witness::{WitnessModule, compile_witness_modules};
    use binius_field::Field;
    use binius_utils::checked_arithmetics::log2_ceil_usize;
    use rand::prelude::StdRng;
    use rand::{Rng, SeedableRng};
    use std::array;

    #[derive(Debug, Default, Copy, Clone)]
    pub(super) struct Blake3CompressState {
        pub cv: [u32; 8],
        pub block: [u32; 16],
        pub counter_low: u32,
        pub counter_high: u32,
        pub block_len: u32,
        pub flags: u32,
    }

    // taken (and slightly refactored) from reference Blake3 implementation:
    // https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs
    fn compress(
        chaining_value: &[u32; 8],
        block_words: &[u32; 16],
        counter: u64,
        block_len: u32,
        flags: u32,
    ) -> [u32; 16] {
        #[allow(clippy::cast_possible_truncation)]
        let counter_low = counter as u32;
        #[allow(clippy::cast_possible_truncation)]
        let counter_high = (counter >> 32) as u32;

        let mut state = [
            chaining_value[0],
            chaining_value[1],
            chaining_value[2],
            chaining_value[3],
            chaining_value[4],
            chaining_value[5],
            chaining_value[6],
            chaining_value[7],
            IV[0],
            IV[1],
            IV[2],
            IV[3],
            counter_low,
            counter_high,
            block_len,
            flags,
            block_words[0],
            block_words[1],
            block_words[2],
            block_words[3],
            block_words[4],
            block_words[5],
            block_words[6],
            block_words[7],
            block_words[8],
            block_words[9],
            block_words[10],
            block_words[11],
            block_words[12],
            block_words[13],
            block_words[14],
            block_words[15],
        ];

        let a = [0, 1, 2, 3, 0, 1, 2, 3];
        let b = [4, 5, 6, 7, 5, 6, 7, 4];
        let c = [8, 9, 10, 11, 10, 11, 8, 9];
        let d = [12, 13, 14, 15, 15, 12, 13, 14];
        let mx = [16, 18, 20, 22, 24, 26, 28, 30];
        let my = [17, 19, 21, 23, 25, 27, 29, 31];

        // we have 7 rounds in total
        for round_idx in 0..7 {
            for j in 0..8 {
                let a_in = state[a[j]];
                let b_in = state[b[j]];
                let c_in = state[c[j]];
                let d_in = state[d[j]];
                let mx_in = state[mx[j]];
                let my_in = state[my[j]];

                let a_0 = a_in.wrapping_add(b_in).wrapping_add(mx_in);
                let d_0 = (d_in ^ a_0).rotate_right(16);
                let c_0 = c_in.wrapping_add(d_0);
                let b_0 = (b_in ^ c_0).rotate_right(12);

                let a_1 = a_0.wrapping_add(b_0).wrapping_add(my_in);
                let d_1 = (d_0 ^ a_1).rotate_right(8);
                let c_1 = c_0.wrapping_add(d_1);
                let b_1 = (b_0 ^ c_1).rotate_right(7);

                state[a[j]] = a_1;
                state[b[j]] = b_1;
                state[c[j]] = c_1;
                state[d[j]] = d_1;
            }

            // execute permutation for the 6 first rounds
            if round_idx < 6 {
                let mut permuted = [0; 16];
                for i in 0..16 {
                    permuted[i] = state[16 + MSG_PERMUTATION[i]];
                }
                state[16..32].copy_from_slice(&permuted);
            }
        }

        for i in 0..8 {
            state[i] ^= state[i + 8];
            state[i + 8] ^= chaining_value[i];
        }

        let state_out: [u32; 16] = array::from_fn(|i| state[i]);
        state_out
    }

    pub fn generate_trace(size: usize) -> (Vec<Vec<u32>>, Trace) {
        let compressions = size;

        let mut rng = StdRng::seed_from_u64(0);
        let mut expected = vec![];
        let inputs = (0..compressions)
            .map(|_| {
                let cv: [u32; 8] = array::from_fn(|_| rng.random::<u32>());
                let block: [u32; 16] = array::from_fn(|_| rng.random::<u32>());
                let counter = rng.random::<u64>();
                #[allow(clippy::cast_possible_truncation)]
                let counter_low = counter as u32;
                #[allow(clippy::cast_possible_truncation)]
                let counter_high = (counter >> 32) as u32;
                let block_len = rng.random::<u32>();
                let flags = rng.random::<u32>();

                // save expected value to use later in test
                expected.push(compress(&cv, &block, counter, block_len, flags).to_vec());

                Blake3CompressState {
                    cv,
                    block,
                    counter_low,
                    counter_high,
                    block_len,
                    flags,
                }
            })
            .collect::<Vec<Blake3CompressState>>();

        // <trace>
        let mut state_trace: [Vec<u32>; STATE_SIZE] =
            array::from_fn(|_xy| vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT]);
        fn write_state_trace(
            state_trace: &mut [Vec<u32>; STATE_SIZE],
            index: usize,
            state: [u32; STATE_SIZE],
        ) {
            for xy in 0..STATE_SIZE {
                state_trace[xy][index] = state[xy];
            }
        }

        let mut cv_trace = vec![0u32; compressions * OUT_HEIGHT];
        let mut state_i_trace = vec![0u32; compressions * OUT_HEIGHT];
        let mut state_i_8_trace = vec![0u32; compressions * OUT_HEIGHT];
        let mut state_i_xor_state_i_8_trace = vec![0u32; compressions * OUT_HEIGHT];
        let mut state_i_8_xor_cv_trace = vec![0u32; compressions * OUT_HEIGHT];

        let mut a_in_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut b_in_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut c_in_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut d_in_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut mx_in_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut my_in_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];

        let mut a_0_tmp_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut a_0_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut d_in_xor_a_0_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut d_0_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut c_0_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut b_in_xor_c_0_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut b_0_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut a_1_tmp_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut a_1_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut d_0_xor_a_1_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut d_1_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut c_1_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut b_0_xor_c_1_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        let mut b_1_trace = vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT];
        fn write_var_trace(var_trace: &mut [u32], index: usize, value: u32) {
            var_trace[index] = value;
        }

        let mut cin_trace: [Vec<u32>; ADDITION_OPERATIONS_NUMBER] =
            array::from_fn(|_xy| vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT]);
        let mut cout_trace: [Vec<u32>; ADDITION_OPERATIONS_NUMBER] =
            array::from_fn(|_xy| vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT]);
        fn write_addition_trace(
            addition_trace: &mut [Vec<u32>; ADDITION_OPERATIONS_NUMBER],
            add_offset: usize,
            var_offset: usize,
            addition: u32,
        ) {
            addition_trace[add_offset][var_offset] = addition;
        }
        //

        // execute Blake3 compression and save execution trace
        let mut compression_offset = 0;
        for (input_idx, input) in inputs.into_iter().enumerate() {
            let counter_low = input.counter_low;
            let counter_high = input.counter_high;

            let mut state = [
                input.cv[0],
                input.cv[1],
                input.cv[2],
                input.cv[3],
                input.cv[4],
                input.cv[5],
                input.cv[6],
                input.cv[7],
                IV[0],
                IV[1],
                IV[2],
                IV[3],
                counter_low,
                counter_high,
                input.block_len,
                input.flags,
                input.block[0],
                input.block[1],
                input.block[2],
                input.block[3],
                input.block[4],
                input.block[5],
                input.block[6],
                input.block[7],
                input.block[8],
                input.block[9],
                input.block[10],
                input.block[11],
                input.block[12],
                input.block[13],
                input.block[14],
                input.block[15],
            ];

            // <trace>
            write_state_trace(&mut state_trace, compression_offset, state);
            //

            let a = [0, 1, 2, 3, 0, 1, 2, 3];
            let b = [4, 5, 6, 7, 5, 6, 7, 4];
            let c = [8, 9, 10, 11, 10, 11, 8, 9];
            let d = [12, 13, 14, 15, 15, 12, 13, 14];
            let mx = [16, 18, 20, 22, 24, 26, 28, 30];
            let my = [17, 19, 21, 23, 25, 27, 29, 31];

            let mut state_offset = 1usize;
            let mut temp_vars_offset = 0usize;

            fn add(a: u32, b: u32) -> (u32, u32, u32) {
                let zout;
                let carry;

                (zout, carry) = a.overflowing_add(b);
                let cin = a ^ b ^ zout;
                let cout = ((carry as u32) << 31) | (cin >> 1);

                (cin, cout, zout)
            }

            for round_idx in 0..7 {
                for j in 0..8 {
                    // <trace>
                    let state_transition_idx = state_offset + compression_offset;
                    let var_offset = temp_vars_offset + compression_offset;
                    let mut add_offset = 0usize;
                    //

                    let a_in = state[a[j]];
                    let b_in = state[b[j]];
                    let c_in = state[c[j]];
                    let d_in = state[d[j]];
                    let mx_in = state[mx[j]];
                    let my_in = state[my[j]];

                    // <trace>
                    write_var_trace(&mut a_in_trace, var_offset, a_in);
                    write_var_trace(&mut b_in_trace, var_offset, b_in);
                    write_var_trace(&mut c_in_trace, var_offset, c_in);
                    write_var_trace(&mut d_in_trace, var_offset, d_in);
                    write_var_trace(&mut mx_in_trace, var_offset, mx_in);
                    write_var_trace(&mut my_in_trace, var_offset, my_in);
                    //

                    let (cin, cout, a_0_tmp) = add(a_in, b_in);
                    // <trace>
                    write_addition_trace(&mut cin_trace, add_offset, var_offset, cin);
                    write_addition_trace(&mut cout_trace, add_offset, var_offset, cout);
                    add_offset += 1;
                    //

                    let (cin, cout, a_0) = add(a_0_tmp, mx_in);
                    // <trace>
                    write_addition_trace(&mut cin_trace, add_offset, var_offset, cin);
                    write_addition_trace(&mut cout_trace, add_offset, var_offset, cout);
                    add_offset += 1;
                    //

                    let d_in_xor_a_0 = d_in ^ a_0;
                    let d_0 = d_in_xor_a_0.rotate_right(16);

                    let (cin, cout, c_0) = add(c_in, d_0);
                    // <trace>
                    write_addition_trace(&mut cin_trace, add_offset, var_offset, cin);
                    write_addition_trace(&mut cout_trace, add_offset, var_offset, cout);
                    add_offset += 1;
                    //

                    let b_in_xor_c_0 = b_in ^ c_0;
                    let b_0 = b_in_xor_c_0.rotate_right(12);

                    let (cin, cout, a_1_tmp) = add(a_0, b_0);
                    // <trace>
                    write_addition_trace(&mut cin_trace, add_offset, var_offset, cin);
                    write_addition_trace(&mut cout_trace, add_offset, var_offset, cout);
                    add_offset += 1;
                    //

                    let (cin, cout, a_1) = add(a_1_tmp, my_in);
                    // <trace>
                    write_addition_trace(&mut cin_trace, add_offset, var_offset, cin);
                    write_addition_trace(&mut cout_trace, add_offset, var_offset, cout);
                    add_offset += 1;
                    //

                    let d_0_xor_a_1 = d_0 ^ a_1;
                    let d_1 = d_0_xor_a_1.rotate_right(8);

                    let (cin, cout, c_1) = add(c_0, d_1);
                    // <trace>
                    write_addition_trace(&mut cin_trace, add_offset, var_offset, cin);
                    write_addition_trace(&mut cout_trace, add_offset, var_offset, cout);
                    //

                    let b_0_xor_c_1 = b_0 ^ c_1;
                    let b_1 = b_0_xor_c_1.rotate_right(7);

                    // <trace>
                    write_var_trace(&mut a_0_tmp_trace, var_offset, a_0_tmp);
                    write_var_trace(&mut a_0_trace, var_offset, a_0);
                    write_var_trace(&mut d_in_xor_a_0_trace, var_offset, d_in_xor_a_0);
                    write_var_trace(&mut d_0_trace, var_offset, d_0);
                    write_var_trace(&mut c_0_trace, var_offset, c_0);
                    write_var_trace(&mut b_in_xor_c_0_trace, var_offset, b_in_xor_c_0);
                    write_var_trace(&mut b_0_trace, var_offset, b_0);
                    write_var_trace(&mut a_1_tmp_trace, var_offset, a_1_tmp);
                    write_var_trace(&mut a_1_trace, var_offset, a_1);
                    write_var_trace(&mut d_0_xor_a_1_trace, var_offset, d_0_xor_a_1);
                    write_var_trace(&mut d_1_trace, var_offset, d_1);
                    write_var_trace(&mut c_1_trace, var_offset, c_1);
                    write_var_trace(&mut b_0_xor_c_1_trace, var_offset, b_0_xor_c_1);
                    write_var_trace(&mut b_1_trace, var_offset, b_1);
                    //

                    state[a[j]] = a_1;
                    state[b[j]] = b_1;
                    state[c[j]] = c_1;
                    state[d[j]] = d_1;

                    // <trace>
                    write_state_trace(&mut state_trace, state_transition_idx, state);
                    //

                    state_offset += 1;
                    temp_vars_offset += 1;
                }

                // execute permutation for the 6 first rounds
                if round_idx < 6 {
                    let mut permuted = [0; 16];
                    for i in 0..16 {
                        permuted[i] = state[16 + MSG_PERMUTATION[i]];
                    }
                    state[16..32].copy_from_slice(&permuted);
                }
            }

            for i in 0..8 {
                // <trace>
                write_var_trace(&mut cv_trace, input_idx * 8 + i, input.cv[i]);
                write_var_trace(&mut state_i_trace, input_idx * 8 + i, state[i]);
                write_var_trace(&mut state_i_8_trace, input_idx * 8 + i, state[i + 8]);
                //

                state[i] ^= state[i + 8];
                // <trace>
                write_var_trace(
                    &mut state_i_xor_state_i_8_trace,
                    input_idx * 8 + i,
                    state[i],
                );
                //

                state[i + 8] ^= input.cv[i];
                // <trace>
                write_var_trace(&mut state_i_8_xor_cv_trace, input_idx * 8 + i, state[i + 8]);
                //
            }

            // <trace>
            write_state_trace(
                &mut state_trace,
                compression_offset + usize::try_from(PROJECTED_SELECTOR_OUTPUT).unwrap(),
                state,
            );
            //

            compression_offset += SINGLE_COMPRESSION_HEIGHT;
        }

        (expected, Trace {
            state_trace,
            a_in_trace,
            b_in_trace,
            c_in_trace,
            d_in_trace,
            mx_in_trace,
            my_in_trace,
            a_0_tmp_trace,
            a_0_trace,
            d_in_xor_a_0_trace,
            d_0_trace,
            c_0_trace,
            _b_in_xor_c_0_trace: b_in_xor_c_0_trace,
            b_0_trace,
            a_1_tmp_trace,
            a_1_trace,
            _d_0_xor_a_1_trace: d_0_xor_a_1_trace,
            d_1_trace,
            c_1_trace,
            _b_0_xor_c_1_trace: b_0_xor_c_1_trace,
            _b_1_trace: b_1_trace,
            _cin_trace: cin_trace,
            cout_trace,
            cv_trace,
            state_i_trace,
            state_i_8_trace,
            _state_i_xor_state_i_8_trace: state_i_xor_state_i_8_trace,
            _state_i_8_xor_cv_trace: state_i_8_xor_cv_trace,
        })
    }

    const COMPRESSIONS_LOG_TEST: u32 = 5;

    #[test]
    fn test_state_transition_module() {
        let trace_len = 2usize.pow(COMPRESSIONS_LOG_TEST);
        let (expected, traces) = generate_trace(trace_len);

        let (compression_oracles, circuit_module, witness_module, height) =
            state_transition_module(0, &traces, trace_len).unwrap();

        assert_expected_output(&compression_oracles, &expected, &witness_module);

        // check that Binius proof can be constructed and verified
        let witness_modules = [witness_module];
        let circuit_modules = [circuit_module];
        let witness = compile_witness_modules(&witness_modules, vec![height]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
    }

    #[test]
    fn test_additions_xor_rotates_module() {
        let trace_len = 2usize.pow(COMPRESSIONS_LOG_TEST);
        let (_, traces) = generate_trace(trace_len);

        let (circuit_module, witness_module, height) =
            additions_xor_rotates_module(0, &traces, trace_len).unwrap();

        let witness_modules = [witness_module];
        let circuit_modules = [circuit_module];

        let witness = compile_witness_modules(&witness_modules, vec![height]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
    }

    #[test]
    fn test_cv_output_module() {
        let trace_len = 2usize.pow(COMPRESSIONS_LOG_TEST);
        let (_, traces) = generate_trace(trace_len);

        let (circuit_module, witness_module, height) =
            cv_output_module(0, &traces, trace_len).unwrap();

        let witness_modules = [witness_module];
        let circuit_modules = [circuit_module];

        let witness = compile_witness_modules(&witness_modules, vec![height]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
    }

    #[test]
    fn test_whole_blake3_compression() {
        let trace_len = 2usize.pow(COMPRESSIONS_LOG_TEST);
        let (expected, traces) = generate_trace(trace_len);

        let (compression_oracles, circuit_module_0, witness_module_0, height_0) =
            state_transition_module(0, &traces, trace_len).unwrap();
        let (circuit_module_1, witness_module_1, height_1) =
            additions_xor_rotates_module(1, &traces, trace_len).unwrap();
        let (circuit_module_2, witness_module_2, height_2) =
            cv_output_module(2, &traces, trace_len).unwrap();

        assert_expected_output(&compression_oracles, &expected, &witness_module_0);

        let witness_modules = [witness_module_0, witness_module_1, witness_module_2];
        let circuit_modules = [circuit_module_0, circuit_module_1, circuit_module_2];

        let witness =
            compile_witness_modules(&witness_modules, vec![height_0, height_1, height_2]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
    }

    #[test]
    fn test_lc_over_bits() {
        let trace_len = 2usize.pow(COMPRESSIONS_LOG_TEST);
        let (_, traces) = generate_trace(trace_len);

        let state_n_vars = log2_ceil_usize(trace_len * SINGLE_COMPRESSION_HEIGHT);
        let height = 2u64.pow(u32::try_from(state_n_vars + 5).unwrap());

        let circuit_module_id = 0;
        let mut circuit_module_1 = CircuitModule::new(circuit_module_id);

        let a_0 = circuit_module_1.add_committed::<B1>("a_0").unwrap();
        let d_in = circuit_module_1.add_committed::<B1>("d_in").unwrap();

        let d_in_xor_a_0 = circuit_module_1
            .add_linear_combination("d_in_xor_a_0", B128::ZERO, [
                (a_0, B128::ONE),
                (d_in, B128::ONE),
            ])
            .unwrap();

        circuit_module_1.freeze_oracles();

        let circuit_modules = [circuit_module_1];
        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();

        let witness_module_id = 0;

        let a_0_entry = witness_modules[witness_module_id].new_entry();
        let d_in_entry = witness_modules[witness_module_id].new_entry();

        let Trace {
            a_0_trace,
            d_in_trace,
            ..
        } = traces;
        witness_modules[witness_module_id].push_u32s_to(a_0_trace, a_0_entry);
        witness_modules[witness_module_id].push_u32s_to(d_in_trace, d_in_entry);

        witness_modules[witness_module_id].bind_oracle_to::<B1>(a_0, a_0_entry);
        witness_modules[witness_module_id].bind_oracle_to::<B1>(d_in, d_in_entry);

        witness_modules[witness_module_id].populate(height).unwrap();

        let lc_data = witness_modules[witness_module_id].get_data(&d_in_xor_a_0);
        let expected = traces
            .d_in_xor_a_0_trace
            .into_iter()
            .flat_map(u32::to_le_bytes)
            .collect::<Vec<_>>();
        assert_eq!(lc_data, expected);

        let witness_archon = compile_witness_modules(&witness_modules, vec![height]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok());
    }

    fn transpose<T>(v: &[Vec<T>]) -> Vec<Vec<T>>
    where
        T: Clone,
    {
        assert!(!v.is_empty());
        (0..v[0].len())
            .map(|i| v.iter().map(|inner| inner[i].clone()).collect::<Vec<T>>())
            .collect()
    }

    // checks that output of the circuit contains expected values
    pub fn assert_expected_output(
        oracles: &Blake3CompressionOracles,
        expected: &[Vec<u32>],
        witness_module: &WitnessModule,
    ) {
        let expected = transpose(expected);
        for (i, expected_i) in expected.into_iter().enumerate() {
            let actual = witness_module.get_data(&oracles.output[i]);
            let expected_i = expected_i
                .into_iter()
                .flat_map(u32::to_le_bytes)
                .collect::<Vec<_>>();
            assert_eq!(actual, expected_i);
        }
    }
}
