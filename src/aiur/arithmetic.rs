use std::array::from_fn;

use binius_circuits::{
    builder::{ConstraintSystemBuilder, witness},
    lasso::{
        batch::LookupBatch,
        big_integer_ops::byte_sliced_mul,
        lookups::u8_arithmetic::{add_lookup, dci_lookup, mul_lookup},
    },
    transparent,
};
use binius_core::{
    constraint_system::channel::ChannelId,
    oracle::{OracleId, ProjectionVariant, ShiftVariant},
};
use binius_field::{
    Field,
    packed::set_packed_slice,
    tower_levels::{TowerLevel8, TowerLevel16},
    underlier::{U1, WithUnderlier},
};
use binius_macros::arith_expr;
use binius_maybe_rayon::prelude::*;

use crate::aiur::layout::{B1, B8, B64};

use super::{
    constraints::Expr,
    execute::QueryRecord,
    layout::{B1_LEVEL, B8_LEVEL, B64_LEVEL, B128},
};

struct AddCols {
    xin: OracleId,
    yin: OracleId,
    cin: OracleId,
    zout: OracleId,
    cout: OracleId,
    packed_xin: OracleId,
    packed_yin: OracleId,
    packed_zout: OracleId,
    projected_cout: OracleId,
}

pub struct AddTrace {
    xin: Vec<u64>,
    yin: Vec<u64>,
    height: usize,
}

impl AddTrace {
    pub fn generate_trace(record: &QueryRecord) -> Self {
        let height = record.add_queries.len();
        let mut trace = AddTrace {
            xin: Vec::with_capacity(height),
            yin: Vec::with_capacity(height),
            height,
        };
        for (xin, yin) in record.add_queries.iter() {
            trace.xin.push(*xin);
            trace.yin.push(*yin);
        }
        trace
    }
}

impl AddCols {
    fn new(builder: &mut ConstraintSystemBuilder<'_>, log_n: usize) -> Self {
        let xin = builder.add_committed("xin", log_n + B64_LEVEL, B1_LEVEL);
        let yin = builder.add_committed("yin", log_n + B64_LEVEL, B1_LEVEL);
        let zout = builder.add_committed("zout", log_n + B64_LEVEL, B1_LEVEL);
        let cout = builder.add_committed("cout", log_n + B64_LEVEL, B1_LEVEL);
        let cin = builder
            .add_shifted("cin", cout, 1, B64_LEVEL, ShiftVariant::LogicalLeft)
            .unwrap();
        let packed_xin = builder.add_packed("packed_xin", xin, B64_LEVEL).unwrap();
        let packed_yin = builder.add_packed("packed_yin", yin, B64_LEVEL).unwrap();
        let packed_zout = builder.add_packed("packed_zout", zout, B64_LEVEL).unwrap();
        let args = [B128::ONE; B64_LEVEL].to_vec();
        let projected_cout = builder
            .add_projected("projected_cout", cout, args, ProjectionVariant::FirstVars)
            .unwrap();
        AddCols {
            xin,
            yin,
            cin,
            zout,
            cout,
            packed_xin,
            packed_yin,
            packed_zout,
            projected_cout,
        }
    }

    fn populate(&self, witness: &mut witness::Builder<'_>, trace: &AddTrace, count: usize) {
        witness.new_column::<B1>(self.xin).as_mut_slice::<u64>()[..count]
            .copy_from_slice(&trace.xin);
        witness.new_column::<B1>(self.yin).as_mut_slice::<u64>()[..count]
            .copy_from_slice(&trace.yin);
        (
            witness.get::<B1>(self.xin).unwrap().as_slice::<u64>(),
            witness.get::<B1>(self.yin).unwrap().as_slice::<u64>(),
            witness.new_column::<B1>(self.zout).as_mut_slice::<u64>(),
            witness.new_column::<B1>(self.cout).as_mut_slice::<u64>(),
            witness.new_column::<B1>(self.cin).as_mut_slice::<u64>(),
        )
            .into_par_iter()
            .for_each(|(xin, yin, zout, cout, cin)| {
                let carry;
                (*zout, carry) = (*xin).overflowing_add(*yin);
                *cin = (*xin) ^ (*yin) ^ (*zout);
                *cout = ((carry as u64) << 63) | (*cin >> 1);
            });
        let packed_xin_witness = witness.get::<B1>(self.xin).unwrap();
        let packed_yin_witness = witness.get::<B1>(self.yin).unwrap();
        let packed_zout_witness = witness.get::<B1>(self.zout).unwrap();
        witness
            .set(self.packed_xin, packed_xin_witness.repacked::<B64>())
            .unwrap();
        witness
            .set(self.packed_yin, packed_yin_witness.repacked::<B64>())
            .unwrap();
        witness
            .set(self.packed_zout, packed_zout_witness.repacked::<B64>())
            .unwrap();
        let cout_witness = witness.get::<B1>(self.cout).unwrap().as_slice::<u64>();
        let mut projected_cout_witness = witness.new_column::<B1>(self.projected_cout);
        let projected_cout_witness = projected_cout_witness.packed();
        for (i, word) in cout_witness.iter().enumerate() {
            let bit = (word >> 63) as u8;
            set_packed_slice(projected_cout_witness, i, B1::from_underlier(U1::new(bit)));
        }
    }
}

fn constrain_add(
    builder: &mut ConstraintSystemBuilder<'_>,
    add_channel_id: ChannelId,
    cols: &AddCols,
    count: usize,
) {
    builder.assert_zero(
        "sum",
        [cols.xin, cols.yin, cols.cin, cols.zout],
        arith_expr!([xin, yin, cin, zout] = xin + yin + cin - zout).convert_field(),
    );

    builder.assert_zero(
        "carry",
        [cols.xin, cols.yin, cols.cin, cols.cout],
        arith_expr!([xin, yin, cin, cout] = (xin + cin) * (yin + cin) + cin - cout).convert_field(),
    );
    let args = [
        cols.packed_xin,
        cols.packed_yin,
        cols.packed_zout,
        cols.projected_cout,
    ];
    builder.receive(add_channel_id, count, args).unwrap();
}

pub fn prover_synthesize_add(
    builder: &mut ConstraintSystemBuilder<'_>,
    add_channel_id: ChannelId,
    trace: &AddTrace,
) {
    let log_n = trace.height.next_power_of_two().ilog2() as usize;
    let count = trace.height;
    let cols = AddCols::new(builder, log_n);
    cols.populate(builder.witness().unwrap(), trace, count);
    constrain_add(builder, add_channel_id, &cols, count);
}

pub fn verifier_synthesize_add(
    builder: &mut ConstraintSystemBuilder<'_>,
    add_channel_id: ChannelId,
    count: u64,
) {
    let log_n = count.next_power_of_two().ilog2() as usize;
    let cols = AddCols::new(builder, log_n);
    constrain_add(builder, add_channel_id, &cols, count.try_into().expect(""));
}

struct MulCols {
    xin: OracleId,
    yin: OracleId,
    xin_bytes: [OracleId; 8],
    yin_bytes: [OracleId; 8],
    zout: OracleId,
    zero_carry: OracleId,
    lookup_t_mul: OracleId,
    lookup_t_add: OracleId,
    lookup_t_dci: OracleId,
}

impl MulCols {
    fn new(builder: &mut ConstraintSystemBuilder<'_>, log_n: usize) -> Self {
        let xin = builder.add_committed("xin", log_n, B64_LEVEL);
        let yin = builder.add_committed("yin", log_n, B64_LEVEL);
        let zout = builder.add_committed("zout", log_n, B64_LEVEL);
        let xin_bytes =
            from_fn(|i| builder.add_committed(format!("xin_bytes{i}"), log_n, B8_LEVEL));
        let yin_bytes =
            from_fn(|i| builder.add_committed(format!("yin_bytes{i}"), log_n, B8_LEVEL));
        let zero_carry = transparent::constant(builder, "zero carry", log_n, B1::ZERO).unwrap();
        let lookup_t_mul = mul_lookup(builder, "mul lookup").unwrap();
        let lookup_t_add = add_lookup(builder, "add lookup").unwrap();
        let lookup_t_dci = dci_lookup(builder, "dci lookup").unwrap();
        Self {
            xin,
            yin,
            zout,
            xin_bytes,
            yin_bytes,
            zero_carry,
            lookup_t_mul,
            lookup_t_add,
            lookup_t_dci,
        }
    }

    fn populate(&self, witness: &mut witness::Builder<'_>, trace: &MulTrace, count: usize) {
        witness.new_column::<B64>(self.xin).as_mut_slice::<u64>()[..count]
            .copy_from_slice(&trace.xin);
        witness.new_column::<B64>(self.yin).as_mut_slice::<u64>()[..count]
            .copy_from_slice(&trace.yin);
        (
            witness.get::<B64>(self.xin).unwrap().as_slice::<u64>(),
            witness.get::<B64>(self.yin).unwrap().as_slice::<u64>(),
            witness.new_column::<B64>(self.zout).as_mut_slice::<u64>(),
        )
            .into_par_iter()
            .for_each(|(xin, yin, zout)| {
                *zout = xin.wrapping_mul(*yin);
            });
        for (i, xin_byte) in self.xin_bytes.iter().enumerate() {
            (
                witness.get::<B64>(self.xin).unwrap().as_slice::<u64>(),
                witness.new_column::<B8>(*xin_byte).as_mut_slice::<u8>(),
            )
                .into_par_iter()
                .for_each(|(xin, xin_byte)| {
                    let byte = xin.to_le_bytes()[i];
                    *xin_byte = byte;
                });
        }
        for (i, yin_byte) in self.yin_bytes.iter().enumerate() {
            (
                witness.get::<B64>(self.yin).unwrap().as_slice::<u64>(),
                witness.new_column::<B8>(*yin_byte).as_mut_slice::<u8>(),
            )
                .into_par_iter()
                .for_each(|(yin, yin_byte)| {
                    let byte = yin.to_le_bytes()[i];
                    *yin_byte = byte;
                });
        }
    }
}

pub struct MulTrace {
    xin: Vec<u64>,
    yin: Vec<u64>,
    height: usize,
}

impl MulTrace {
    pub fn generate_trace(record: &QueryRecord) -> Self {
        let height = record.mul_queries.len();
        let mut trace = MulTrace {
            xin: Vec::with_capacity(height),
            yin: Vec::with_capacity(height),
            height,
        };
        for (xin, yin) in record.mul_queries.iter() {
            trace.xin.push(*xin);
            trace.yin.push(*yin);
        }
        trace
    }
}

pub fn prover_synthesize_mul(
    builder: &mut ConstraintSystemBuilder<'_>,
    mul_channel_id: ChannelId,
    trace: &MulTrace,
) {
    let log_n = trace.height.next_power_of_two().ilog2() as usize;
    let cols = MulCols::new(builder, log_n);
    let count = trace.height;
    cols.populate(builder.witness().unwrap(), trace, count);
    constrain_mul(builder, mul_channel_id, &cols, log_n, count);
}

pub fn verifier_synthesize_mul(
    builder: &mut ConstraintSystemBuilder<'_>,
    mul_channel_id: ChannelId,
    count: u64,
) {
    let log_n = count.next_power_of_two().ilog2() as usize;
    let cols = MulCols::new(builder, log_n);
    let count = count.try_into().expect("");
    constrain_mul(builder, mul_channel_id, &cols, log_n, count);
}

fn constrain_mul(
    builder: &mut ConstraintSystemBuilder<'_>,
    mul_channel_id: ChannelId,
    cols: &MulCols,
    log_n: usize,
    count: usize,
) {
    byte_decomposition(builder, &cols.xin_bytes, cols.xin);
    byte_decomposition(builder, &cols.yin_bytes, cols.yin);
    let mut lookup_batch_mul = LookupBatch::new([cols.lookup_t_mul]);
    let mut lookup_batch_add = LookupBatch::new([cols.lookup_t_add]);
    let mut lookup_batch_dci = LookupBatch::new([cols.lookup_t_dci]);
    let zout_bytes_and_cout = byte_sliced_mul::<TowerLevel8, TowerLevel16>(
        builder,
        "lasso_bytesliced_mul",
        &cols.xin_bytes,
        &cols.yin_bytes,
        log_n,
        cols.zero_carry,
        &mut lookup_batch_mul,
        &mut lookup_batch_add,
        &mut lookup_batch_dci,
    )
    .unwrap();
    lookup_batch_mul.execute::<B64>(builder).unwrap();
    lookup_batch_add.execute::<B64>(builder).unwrap();
    lookup_batch_dci.execute::<B64>(builder).unwrap();
    let zout_bytes = (&zout_bytes_and_cout[0..8]).try_into().unwrap();
    byte_decomposition(builder, zout_bytes, cols.zout);
    let args = [cols.xin, cols.yin, cols.zout];
    builder.receive(mul_channel_id, count, args).unwrap();
}

fn byte_decomposition(
    builder: &mut ConstraintSystemBuilder<'_>,
    bytes: &[OracleId; 8],
    word: OracleId,
) {
    let mut expr: Expr = Expr::Var(word);
    let mut coeff = 1u64;
    for byte in bytes {
        expr = expr - Expr::Const(coeff.into()) * Expr::Var(*byte);
        coeff = coeff.wrapping_add(256);
    }
    let (oracles, arith) = expr.to_arith_expr();
    builder.assert_zero("byte decomposition", oracles, arith);
}
