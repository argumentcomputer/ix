use binius_circuits::builder::{ConstraintSystemBuilder, witness};
use binius_core::{
    constraint_system::channel::ChannelId,
    oracle::{OracleId, ProjectionVariant, ShiftVariant},
};
use binius_field::{
    Field,
    packed::set_packed_slice,
    underlier::{U1, WithUnderlier},
};
use binius_macros::arith_expr;
use binius_maybe_rayon::prelude::*;

use crate::aiur::layout::{B1, B64};

use super::{
    execute::QueryRecord,
    layout::{B1_LEVEL, B64_LEVEL, B128},
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

    fn populate(&self, witness: &mut witness::Builder<'_>, trace: &AddTrace) {
        let count = trace.xin.len();
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
    count: u64,
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
    let count = count
        .try_into()
        .expect("Value too big for current architecture");
    builder.receive(add_channel_id, count, args).unwrap();
}

pub fn prover_synthesize_add(
    builder: &mut ConstraintSystemBuilder<'_>,
    add_channel_id: ChannelId,
    trace: &AddTrace,
) -> u8 {
    let log_n = trace.height.next_power_of_two().ilog2() as usize;
    let count = trace.height.try_into().expect("");
    let cols = AddCols::new(builder, log_n);
    cols.populate(builder.witness().unwrap(), trace);
    constrain_add(builder, add_channel_id, &cols, count);
    log_n.try_into().expect("Trace too large")
}

pub fn verifier_synthesize_add(
    builder: &mut ConstraintSystemBuilder<'_>,
    add_channel_id: ChannelId,
    count: u64,
) {
    let log_n = count.next_power_of_two().ilog2() as usize;
    let cols = AddCols::new(builder, log_n);
    constrain_add(builder, add_channel_id, &cols, count);
}
