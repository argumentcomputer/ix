//! THIS MODULE IS CURRENTLY NOT BEING USED
//!
//! It contains a Rust implementation of the "G function" used in blake3, using
//! Aiur API.
//!
//! This code can be useful in the future in case we want to use it to speed up
//! execution (instead of interpreting Aiur code).

use multi_stark::{
    builder::symbolic::SymbolicExpression,
    lookup::Lookup,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::dense::RowMajorMatrix,
};

use crate::aiur::{
    G,
    execute::QueryRecord,
    gadgets::{
        AiurGadget,
        bytes1::{Bytes1, Bytes1Op},
        bytes2::{Bytes2, Bytes2Op},
    },
};

const TRACE_WIDTH: usize = 0; // TODO

pub(crate) struct Blake3;

impl BaseAir<G> for Blake3 {
    fn width(&self) -> usize {
        TRACE_WIDTH
    }
}

impl<AB: AirBuilder<F = G>> Air<AB> for Blake3 {
    /// A no-op, since all constraints are enforced through lookups.
    fn eval(&self, _builder: &mut AB) {}
}

pub(crate) enum Blake3Op {
    GFunction,
}

impl AiurGadget for Blake3 {
    type Op = Blake3Op;

    fn output_size(&self, op: &Self::Op) -> usize {
        match op {
            Blake3Op::GFunction => 16, // four 4-byte words
        }
    }

    fn execute(&self, op: &Self::Op, input: &[G], record: &mut QueryRecord) -> Vec<G> {
        match op {
            Blake3Op::GFunction => {
                if let Some(result) = record.blake3_g_function.get_mut(input) {
                    result.multiplicity += G::ONE;
                    return result.output.to_vec();
                }

                let u8_bits = |x, record: &mut QueryRecord| -> [G; 8] {
                    Bytes1
                        .execute(&Bytes1Op::BitDecomposition, &[x], record)
                        .try_into()
                        .expect("Wrong output size")
                };
                let u8_add = |a, b, record: &mut QueryRecord| -> [G; 2] {
                    Bytes2
                        .execute(&Bytes2Op::Add, &[a, b], record)
                        .try_into()
                        .expect("Wrong output size")
                };
                let u8_xor = |a, b, record: &mut QueryRecord| {
                    Bytes2
                        .execute(&Bytes2Op::Xor, &[a, b], record)
                        .pop()
                        .expect("Missing output")
                };
                let u32_add = |a: [G; 4], b: [G; 4], record: &mut QueryRecord| {
                    let [a0, a1, a2, a3] = a;
                    let [b0, b1, b2, b3] = b;

                    // Byte 0 addition (no initial carry)
                    let [sum0, carry1] = u8_add(a0, b0, record);

                    // Byte 1 addition
                    let [sum1, overflow1] = u8_add(a1, b1, record);
                    let [sum1_with_carry, carry1a] = u8_add(sum1, carry1, record);
                    let carry2 = u8_xor(overflow1, carry1a, record);

                    // Byte 2 addition
                    let [sum2, overflow2] = u8_add(a2, b2, record);
                    let [sum2_with_carry, carry2a] = u8_add(sum2, carry2, record);
                    let carry3 = u8_xor(overflow2, carry2a, record);

                    // Byte 3 addition
                    let [sum3, _] = u8_add(a3, b3, record);
                    let [sum3_with_carry, _] = u8_add(sum3, carry3, record);

                    [sum0, sum1_with_carry, sum2_with_carry, sum3_with_carry]
                };
                let u32_xor = |a: [G; 4], b: [G; 4], record: &mut QueryRecord| {
                    let [a0, a1, a2, a3] = a;
                    let [b0, b1, b2, b3] = b;
                    let c0 = u8_xor(a0, b0, record);
                    let c1 = u8_xor(a1, b1, record);
                    let c2 = u8_xor(a2, b2, record);
                    let c3 = u8_xor(a3, b3, record);
                    [c0, c1, c2, c3]
                };
                let u8_recompose = |bits: [G; 8]| {
                    let [b0, b1, b2, b3, b4, b5, b6, b7] = bits;
                    b0 + G::TWO * b1
                        + G::from_u8(4) * b2
                        + G::from_u8(8) * b3
                        + G::from_u8(16) * b4
                        + G::from_u8(32) * b5
                        + G::from_u8(64) * b6
                        + G::from_u8(128) * b7
                };

                let extract_u32 = |idx: usize| [idx, idx + 1, idx + 2, idx + 3].map(|i| input[i]);
                let a = extract_u32(0);
                let b = extract_u32(4);
                let c = extract_u32(8);
                let d = extract_u32(12);
                let x = extract_u32(16);
                let y = extract_u32(20);

                let a = u32_add(u32_add(a, b, record), x, record);
                let [d0, d1, d2, d3] = u32_xor(d, a, record);
                let d = [d2, d3, d0, d1]; // Right-rotated 16

                let c = u32_add(c, d, record);
                let [b0, b1, b2, b3] = u32_xor(b, c, record);
                let [b00, b01, b02, b03, b04, b05, b06, b07] = u8_bits(b0, record);
                let [b10, b11, b12, b13, b14, b15, b16, b17] = u8_bits(b1, record);
                let [b20, b21, b22, b23, b24, b25, b26, b27] = u8_bits(b2, record);
                let [b30, b31, b32, b33, b34, b35, b36, b37] = u8_bits(b3, record);
                let b0 = u8_recompose([b14, b15, b16, b17, b20, b21, b22, b23]);
                let b1 = u8_recompose([b24, b25, b26, b27, b30, b31, b32, b33]);
                let b2 = u8_recompose([b34, b35, b36, b37, b00, b01, b02, b03]);
                let b3 = u8_recompose([b04, b05, b06, b07, b10, b11, b12, b13]);
                let b = [b0, b1, b2, b3]; // Right-rotated 12

                let a = u32_add(u32_add(a, b, record), y, record);
                let [d0, d1, d2, d3] = u32_xor(d, a, record);
                let d = [d1, d2, d3, d0]; // Right-rotated 8

                let c = u32_add(c, d, record);
                let [b0, b1, b2, b3] = u32_xor(b, c, record);
                let [b00, b01, b02, b03, b04, b05, b06, b07] = u8_bits(b0, record);
                let [b10, b11, b12, b13, b14, b15, b16, b17] = u8_bits(b1, record);
                let [b20, b21, b22, b23, b24, b25, b26, b27] = u8_bits(b2, record);
                let [b30, b31, b32, b33, b34, b35, b36, b37] = u8_bits(b3, record);
                let b0 = u8_recompose([b07, b10, b11, b12, b13, b14, b15, b16]);
                let b1 = u8_recompose([b17, b20, b21, b22, b23, b24, b25, b26]);
                let b2 = u8_recompose([b27, b30, b31, b32, b33, b34, b35, b36]);
                let b3 = u8_recompose([b37, b00, b01, b02, b03, b04, b05, b06]);
                let b = [b0, b1, b2, b3]; // Right-rotated 7

                let mut output = Vec::with_capacity(16);
                output.extend(a);
                output.extend(b);
                output.extend(c);
                output.extend(d);
                output
            }
        }
    }

    fn lookups(&self) -> Vec<Lookup<SymbolicExpression<G>>> {
        todo!()
    }

    fn witness_data(&self, record: &QueryRecord) -> (RowMajorMatrix<G>, Vec<Vec<Lookup<G>>>) {
        todo!()
    }
}
