use binius_field::{BinaryField1b, BinaryField32b, BinaryField128b};

const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

#[derive(Debug, Default, Copy, Clone)]
pub struct Blake3CompressState {
    pub cv: [u32; 8],
    pub block: [u32; 16],
    pub counter_low: u32,
    pub counter_high: u32,
    pub block_len: u32,
    pub flags: u32,
}

const STATE_SIZE: usize = 32;

const SINGLE_COMPRESSION_N_VARS: usize = 6;

const SINGLE_COMPRESSION_HEIGHT: usize = 2usize.pow(SINGLE_COMPRESSION_N_VARS as u32);

const ADDITION_OPERATIONS_NUMBER: usize = 6;

const PROJECTED_SELECTOR_INPUT: u64 = 0;
const PROJECTED_SELECTOR_OUTPUT: u64 = 56;

type B128 = BinaryField128b;
type B32 = BinaryField32b;
type B1 = BinaryField1b;

#[cfg(test)]
mod tests {
    use crate::aiur::layout::B128;
    use crate::archon::ProjectedSelectorInfo;
    use crate::archon::arith_expr::ArithExpr;
    use crate::archon::circuit::{CircuitModule, init_witness_modules};
    use crate::archon::precompiles::blake3::{
        ADDITION_OPERATIONS_NUMBER, B1, B32, Blake3CompressState, COMPRESSIONS_TEST, IV,
        MSG_PERMUTATION, PROJECTED_SELECTOR_INPUT, PROJECTED_SELECTOR_OUTPUT,
        SINGLE_COMPRESSION_HEIGHT, SINGLE_COMPRESSION_N_VARS, STATE_SIZE,
    };
    use crate::archon::protocol::validate_witness;
    use crate::archon::witness::compile_witness_modules;
    use binius_circuits::arithmetic::u32::LOG_U32_BITS;
    use binius_circuits::builder::ConstraintSystemBuilder;
    use binius_circuits::builder::types::F;
    use binius_core::oracle::{OracleId, ProjectionVariant, ShiftVariant};
    use binius_field::{Field, TowerField};
    use binius_maybe_rayon::iter::ParallelIterator;
    use binius_utils::checked_arithmetics::log2_ceil_usize;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use rayon::prelude::{IndexedParallelIterator, IntoParallelIterator};
    use std::array;

    // taken (and slightly refactored) from reference Blake3 implementation:
    // https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs
    fn compress(
        chaining_value: &[u32; 8],
        block_words: &[u32; 16],
        counter: u64,
        block_len: u32,
        flags: u32,
    ) -> [u32; 16] {
        let counter_low = counter as u32;
        let counter_high = (counter >> 32) as u32;

        #[rustfmt::skip]
        let mut state = [
            chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
            chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
            IV[0],             IV[1],             IV[2],             IV[3],
            counter_low,       counter_high,      block_len,         flags,
            block_words[0], block_words[1], block_words[2], block_words[3],
            block_words[4], block_words[5], block_words[6], block_words[7],
            block_words[8], block_words[9], block_words[10], block_words[11],
            block_words[12], block_words[13], block_words[14], block_words[15],
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

    #[test]
    fn test_debug() {
        let compressions = COMPRESSIONS_TEST;

        let mut rng = StdRng::seed_from_u64(0);
        let mut expected = vec![];
        let inputs = (0..compressions)
            .map(|_| {
                let cv: [u32; 8] = array::from_fn(|_| rng.random::<u32>());
                let block: [u32; 16] = array::from_fn(|_| rng.random::<u32>());
                let counter = rng.random::<u64>();
                let counter_low = counter as u32;
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
            array::from_fn(|xy| vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT]);
        fn write_state_trace(
            state_trace: &mut [Vec<u32>; STATE_SIZE],
            index: usize,
            state: [u32; STATE_SIZE],
        ) {
            for xy in 0..STATE_SIZE {
                state_trace[xy][index] = state[xy];
            }
        }

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
        fn write_var_trace(var_trace: &mut Vec<u32>, index: usize, value: u32) {
            var_trace[index] = value;
        }

        let mut cin_trace: [Vec<u32>; ADDITION_OPERATIONS_NUMBER] =
            array::from_fn(|xy| vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT]);
        let mut cout_trace: [Vec<u32>; ADDITION_OPERATIONS_NUMBER] =
            array::from_fn(|xy| vec![0u32; compressions * SINGLE_COMPRESSION_HEIGHT]);
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
        for input in inputs.clone() {
            let counter_low = input.counter_low;
            let counter_high = input.counter_high;

            #[rustfmt::skip]
            let mut state = [
                input.cv[0], input.cv[1], input.cv[2], input.cv[3],
                input.cv[4], input.cv[5], input.cv[6], input.cv[7],
                IV[0],             IV[1],             IV[2],             IV[3],
                counter_low,       counter_high,      input.block_len,   input.flags,
                input.block[0], input.block[1], input.block[2], input.block[3],
                input.block[4], input.block[5], input.block[6], input.block[7],
                input.block[8], input.block[9], input.block[10], input.block[11],
                input.block[12], input.block[13], input.block[14], input.block[15],
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
                    add_offset += 1;
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
                state[i] ^= state[i + 8];
                state[i + 8] ^= input.cv[i];
            }

            compression_offset += SINGLE_COMPRESSION_HEIGHT;

            //let state_out: [u32; 16] = array::from_fn(|i| state[i]);
        }

        /*
        // Binius circuit
        let allocator = bumpalo::Bump::new();
        let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);
        let state_n_vars = log2_ceil_usize(inputs.len() * SINGLE_COMPRESSION_HEIGHT);

        let b_in_xor_c_0 = builder.add_committed("b_in_xor_c_0", state_n_vars + 5, B1::TOWER_LEVEL);
        let shifted = builder.add_shifted("shifted", b_in_xor_c_0, (32 - 12) as usize, LOG_U32_BITS, ShiftVariant::CircularLeft).unwrap();

        if let Some(witness) = builder.witness() {
            let mut b_in_xor_c_0_col = witness.new_column::<B1>(b_in_xor_c_0);
            let b_in_xor_c_vals = b_in_xor_c_0_col.as_mut_slice::<u32>();

            let mut shifted_col = witness.new_column::<B1>(shifted);
            let shifted_vals = shifted_col.as_mut_slice::<u32>();

            b_in_xor_c_vals.copy_from_slice(b_in_xor_c_0_trace.as_slice());

            for (shifted, trace) in shifted_vals.iter_mut().zip(b_in_xor_c_0_trace.iter()) {
                //*shifted = trace.rotate_right(12);
                *shifted = trace.rotate_left(32 - 12);
            }
        }
        */



        let witness = builder.take_witness().unwrap();
        let cs = builder.build().unwrap();

        //println!("binius cs: {:?}", cs);
        println!("binius OK");

        binius_core::constraint_system::validate::validate_witness(&cs, &[], &witness).unwrap();
        */

        // Archon circuit
        let state_n_vars = log2_ceil_usize(inputs.len() * SINGLE_COMPRESSION_HEIGHT);

        let height = 2u64.pow(u32::try_from(state_n_vars).unwrap());
        let height_1 = 2u64.pow(u32::try_from(state_n_vars + 5).unwrap());

        let mut circuit_module = CircuitModule::new(0);
        let state_transitions: [OracleId; 1] = array::from_fn(|xy| {
            circuit_module
                .add_committed::<B32>(&format!("state-transition-{:?}", xy))
                .unwrap()
        });

        let input: [OracleId; 1] = array::from_fn(|xy| {
            circuit_module
                .add_projected(
                    &format!("input-{:?}", xy),
                    state_transitions[xy],
                    ProjectedSelectorInfo {
                        selector_value: PROJECTED_SELECTOR_INPUT,
                        single_unprojected_len: SINGLE_COMPRESSION_HEIGHT as u64,
                    },
                )
                .unwrap()
        });

        let output: [OracleId; 1] = array::from_fn(|xy| {
            circuit_module
                .add_projected(
                    &format!("output-{:?}", xy),
                    state_transitions[xy],
                    ProjectedSelectorInfo {
                        selector_value: PROJECTED_SELECTOR_OUTPUT,
                        single_unprojected_len: SINGLE_COMPRESSION_HEIGHT as u64,
                    },
                )
                .unwrap()
        });
        circuit_module.freeze_oracles();

        let mut circuit_module_1 = CircuitModule::new(1);

        // TODO: Implement linear_combination processing for bits and use it for 'b_in_xor_c_0', 'd_in_xor_a_0', 'd_0_xor_a_1', 'b_0_xor_c_1'
        let a_in = circuit_module_1.add_committed::<B1>("a_in").unwrap();
        let b_in = circuit_module_1.add_committed::<B1>("b_in").unwrap();
        let c_in = circuit_module_1.add_committed::<B1>("c_in").unwrap();
        let d_in = circuit_module_1.add_committed::<B1>("d_in").unwrap();
        let mx_in = circuit_module_1.add_committed::<B1>("mx_in").unwrap();
        let my_in = circuit_module_1.add_committed::<B1>("my_in").unwrap();

        let a_0 = circuit_module_1.add_committed::<B1>("a_0").unwrap();
        let a_0_tmp = circuit_module_1.add_committed::<B1>("a_0_tmp").unwrap();
        let c_0 = circuit_module_1.add_committed::<B1>("c_0").unwrap();
        let a_1 = circuit_module_1.add_committed::<B1>("a_1").unwrap();
        let a_1_tmp = circuit_module_1.add_committed::<B1>("a_1_tmp").unwrap();
        let c_1 = circuit_module_1.add_committed::<B1>("c_1").unwrap();

        let b_in_xor_c_0 = circuit_module_1
            .add_committed::<B1>("b_in_xor_c_0")
            .unwrap();
        let d_in_xor_a_0 = circuit_module_1
            .add_committed::<B1>("d_in_xor_a_0")
            .unwrap();
        let d_0_xor_a_1 = circuit_module_1.add_committed::<B1>("d_0_xor_a_1").unwrap();
        let b_0_xor_c_1 = circuit_module_1.add_committed::<B1>("b_0_xor_c_1").unwrap();

        let b_0 = circuit_module_1
            .add_shifted(
                "b_0",
                b_in_xor_c_0,
                (32 - 12) as usize,
                LOG_U32_BITS,
                ShiftVariant::CircularLeft,
            )
            .unwrap();
        let d_0 = circuit_module_1
            .add_shifted(
                "d_0",
                d_in_xor_a_0,
                (32 - 16) as usize,
                LOG_U32_BITS,
                ShiftVariant::CircularLeft,
            )
            .unwrap();
        let d_1 = circuit_module_1
            .add_shifted(
                "d_1",
                d_0_xor_a_1,
                (32 - 8) as usize,
                LOG_U32_BITS,
                ShiftVariant::CircularLeft,
            )
            .unwrap();
        let b_1 = circuit_module_1
            .add_shifted(
                "b_1",
                b_0_xor_c_1,
                (32 - 7) as usize,
                LOG_U32_BITS,
                ShiftVariant::CircularLeft,
            )
            .unwrap();

        let cout: [OracleId; 1] = array::from_fn(|xy| {
            circuit_module_1
                .add_committed::<B1>(&format!("cout-{:?}", xy))
                .unwrap()
        });
        let cin: [OracleId; 1] = array::from_fn(|xy| {
            circuit_module_1
                .add_shifted(
                    &format!("cin-{:?}", xy),
                    cout[xy],
                    1,
                    5,
                    ShiftVariant::LogicalLeft,
                )
                .unwrap()
        });

        /* TODO: figure out why constraints doesn't work
        let xins = [a_in, a_0_tmp, c_in, a_0, a_1_tmp, c_0];
        let yins = [b_in, mx_in, d_0, b_0, my_in, d_1];
        let zouts = [a_0_tmp, a_0, c_0, a_1_tmp, a_1, c_1];

        for (idx, (xin, (yin, zout))) in xins
            .into_iter()
            .zip(yins.into_iter().zip(zouts.into_iter()))
            .enumerate()
        {
            circuit_module.assert_zero(
                &format!("sum{}", idx),
                [xin, yin, cin[idx], zout],
                ArithExpr::Oracle(xin)
                    + ArithExpr::Oracle(yin)
                    + ArithExpr::Oracle(cin[idx])
                    + ArithExpr::Oracle(zout),
            );
        }*/

        circuit_module_1.freeze_oracles();

        let circuit_modules = [circuit_module, circuit_module_1];
        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();

        // populate committed columns of circuit_module_0 (state_transition)
        state_trace.into_iter().enumerate().for_each(|(xy, trace)| {
            if xy == 0 {
                let entry_id_xy = witness_modules[0].new_entry();
                trace.chunks(4).for_each(|chunk| {
                    assert_eq!(chunk.len(), 4);
                    let mut array = [0u32; 4];
                    array[0] = chunk[0];
                    array[1] = chunk[1];
                    array[2] = chunk[2];
                    array[3] = chunk[3];

                    witness_modules[0].push_u32s_to(array, entry_id_xy);
                });
                witness_modules[0].bind_oracle_to::<B32>(state_transitions[xy], entry_id_xy);
            }
        });
        witness_modules[0].populate(height).unwrap();

        // populate committed columns of circuit_module_1

        // (input, temp variables)
        for (trace, temp_variable) in [
            a_in_trace.clone(),
            b_in_trace.clone(),
            c_in_trace.clone(),
            d_in_trace.clone(),
            mx_in_trace.clone(),
            my_in_trace.clone(),

            a_0_trace.clone(),
            a_0_tmp_trace.clone(),
            c_0_trace.clone(),
            a_1_trace.clone(),
            a_1_tmp_trace.clone(),
            c_1_trace.clone(),

            b_in_xor_c_0_trace.clone(),
            d_in_xor_a_0_trace.clone(),
            d_0_xor_a_1_trace.clone(),
            b_0_xor_c_1_trace.clone(),
        ]
        .into_iter()
        .zip(
            [
                a_in,
                b_in,
                c_in,
                d_in,
                mx_in,
                my_in,

                a_0.clone(),
                a_0_tmp.clone(),
                c_0.clone(),
                a_1.clone(),
                a_1_tmp.clone(),
                c_1.clone(),

                b_in_xor_c_0.clone(),
                d_in_xor_a_0.clone(),
                d_0_xor_a_1.clone(),
                b_0_xor_c_1.clone(),
            ]
            .into_iter(),
        ) {
            let entry = witness_modules[1].new_entry();
            trace.chunks(4).for_each(|chunk| {
                assert_eq!(chunk.len(), 4);
                let mut array = [0u32; 4];
                array[0] = chunk[0];
                array[1] = chunk[1];
                array[2] = chunk[2];
                array[3] = chunk[3];
                witness_modules[1].push_u32s_to(array, entry);
            });
            witness_modules[1].bind_oracle_to::<B1>(temp_variable, entry);
        }

        // (cout)
        for (trace, cout_i) in cout_trace.into_iter().zip(cout.into_iter()) {
            let entry = witness_modules[1].new_entry();
            trace.chunks(4).for_each(|chunk| {
                assert_eq!(chunk.len(), 4);
                let mut array = [0u32; 4];
                array[0] = chunk[0];
                array[1] = chunk[1];
                array[2] = chunk[2];
                array[3] = chunk[3];
                witness_modules[1].push_u32s_to(array, entry);
            });
            witness_modules[1].bind_oracle_to::<B1>(cout_i, entry);
        }

        witness_modules[1].populate(height_1).unwrap();


        let witness_archon =
            compile_witness_modules(&witness_modules, vec![height, height_1]).unwrap();
        assert!(validate_witness(&circuit_modules, &witness_archon, &[]).is_ok());
    }
}

const COMPRESSIONS_TEST: usize = 4;
