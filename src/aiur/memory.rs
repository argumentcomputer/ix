use binius_circuits::builder::{ConstraintSystemBuilder, witness};
use binius_core::{constraint_system::channel::ChannelId, oracle::OracleId};
use binius_field::Field;

use crate::aiur::{layout::B64, trace::load_mem_map, transparent::Address};

use super::{
    execute::QueryRecord,
    layout::B64_LEVEL,
    synthesis::{VirtualMap, provide},
    trace::MULT_GEN,
};

struct MemCols {
    address: OracleId,
    values: Vec<OracleId>,
    multiplicity: OracleId,
}

pub struct MemTrace {
    pub values: Vec<Vec<u64>>,
    pub multiplicity: Vec<B64>,
    pub height: usize,
}

impl MemTrace {
    pub fn generate_trace(width: u32, record: &QueryRecord) -> Self {
        let mem_map = load_mem_map(&record.mem_queries, width);
        let height = mem_map.len();
        let mut trace = MemTrace {
            values: vec![Vec::with_capacity(height); width as usize],
            multiplicity: Vec::with_capacity(height),
            height,
        };
        for (args, result) in mem_map.iter() {
            for (i, arg) in args.iter().enumerate() {
                trace.values[i].push(*arg);
            }
            trace.multiplicity.push(MULT_GEN.pow([result.multiplicity]));
        }
        trace
    }
}

impl MemCols {
    fn new(builder: &mut ConstraintSystemBuilder<'_>, log_n: usize, width: usize) -> Self {
        let address = builder.add_transparent("", Address::new(log_n)).unwrap();
        let values: Vec<_> = (0..width)
            .map(|i| builder.add_committed(format!("value-{i}"), log_n, B64_LEVEL))
            .collect();
        let multiplicity = builder.add_committed("multiplicity", log_n, B64_LEVEL);
        MemCols {
            address,
            values,
            multiplicity,
        }
    }

    fn populate(&self, witness: &mut witness::Builder<'_>, trace: &MemTrace) {
        let count = trace.height;
        Address::populate(self.address, witness);
        for (id, values) in self.values.iter().zip(trace.values.iter()) {
            witness.new_column::<B64>(*id).as_mut_slice::<u64>()[..count].copy_from_slice(values);
        }
        {
            witness
                .new_column::<B64>(self.multiplicity)
                .as_mut_slice::<B64>()[..count]
                .copy_from_slice(&trace.multiplicity);
        }
    }
}

pub fn prover_synthesize_mem(
    builder: &mut ConstraintSystemBuilder<'_>,
    mem_channel_id: ChannelId,
    trace: &MemTrace,
) -> u8 {
    let log_n = trace.height.next_power_of_two().ilog2() as usize;
    let width = trace.values.len();
    let count = trace.height.try_into().expect("");
    let cols = MemCols::new(builder, log_n, width);
    cols.populate(builder.witness().unwrap(), trace);
    let mut virt_map = VirtualMap::default();
    let mut args = [cols.address].to_vec();
    args.extend(cols.values);
    provide(
        builder,
        mem_channel_id,
        cols.multiplicity,
        args,
        count,
        &mut virt_map,
    );
    log_n.try_into().expect("Trace too large")
}

pub fn verifier_synthesize_mem(
    builder: &mut ConstraintSystemBuilder<'_>,
    mem_channel_id: ChannelId,
    width: u32,
    count: u64,
) {
    let log_n = count.next_power_of_two().ilog2() as usize;
    let cols = MemCols::new(builder, log_n, width as usize);
    let mut virt_map = VirtualMap::default();
    let mut args = cols.values;
    args.push(cols.address);
    provide(
        builder,
        mem_channel_id,
        cols.multiplicity,
        args,
        count,
        &mut virt_map,
    );
}
