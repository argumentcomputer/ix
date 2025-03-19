#![allow(clippy::cast_possible_truncation)]

use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::{
    constraint_system::channel::{ChannelId, FlushDirection},
    oracle::OracleId,
    transparent::{constant::Constant, step_down::StepDown},
};
use binius_field::{
    BinaryField1b, BinaryField8b, Field,
    packed::{get_packed_slice, set_packed_slice},
    underlier::WithUnderlier,
};
use binius_math::ArithExpr;
use binius_maybe_rayon::prelude::*;

use crate::aiur::layout::AiurByteField;

use super::{
    constraints::{Channel, Columns, Constraints, Expr, build_func_constraints},
    execute::{FxIndexMap, QueryRecord},
    ir::Toplevel,
    layout::{AiurField, FunctionIndexField, MultiplicityField, func_layout},
    memory::{NUM_MEM_TABLES, mem_index_from_size},
    trace::{MULT_GEN, Trace},
    transparent::{Fields, Virtual},
};

#[derive(Clone)]
pub struct AiurChannelIds {
    pub fun: ChannelId,
    pub add: ChannelId,
    pub mul: ChannelId,
    pub mem: Vec<ChannelId>,
}

#[derive(Default)]
struct VirtualMap {
    map: FxIndexMap<Virtual, OracleId>,
}

impl VirtualMap {
    fn sum_bit(
        &mut self,
        builder: &mut ConstraintSystemBuilder<'_>,
        oracles: Vec<OracleId>,
        offset: AiurField,
        log_n: usize,
    ) -> OracleId {
        let virt = Virtual::Sum {
            oracles,
            offset,
            log_n,
        };
        let id = self.map.entry(virt).or_insert_with_key(|virt| {
            let Virtual::Sum { oracles, .. } = virt else {
                unreachable!()
            };
            let lc = oracles.iter().map(|oracle| (*oracle, AiurField::ONE));
            let id = builder
                .add_linear_combination_with_offset("linear combination", log_n, offset, lc)
                .unwrap();
            if let Some(witness) = builder.witness() {
                let slices = oracles
                    .iter()
                    .map(|oracle| witness.get::<BinaryField1b>(*oracle).unwrap().packed())
                    .collect::<Vec<_>>();
                let mut bits = witness.new_column::<BinaryField1b>(id);
                let bits = bits.packed();
                (0..(1 << log_n)).for_each(|i| {
                    slices.iter().for_each(|slice| {
                        let acc = get_packed_slice(bits, i);
                        let a = get_packed_slice(slice, i);
                        set_packed_slice(bits, i, acc + a);
                    })
                });
            }
            id
        });
        *id
    }

    fn sum_byte(
        &mut self,
        builder: &mut ConstraintSystemBuilder<'_>,
        oracles: Vec<OracleId>,
        offset: AiurField,
        log_n: usize,
    ) -> OracleId {
        let virt = Virtual::Sum {
            oracles,
            offset,
            log_n,
        };
        let id = self.map.entry(virt).or_insert_with_key(|virt| {
            let Virtual::Sum { oracles, .. } = virt else {
                unreachable!()
            };
            let lc = oracles.iter().map(|oracle| (*oracle, AiurField::ONE));
            let id = builder
                .add_linear_combination_with_offset("linear combination", log_n, offset, lc)
                .unwrap();
            if let Some(witness) = builder.witness() {
                let slices = oracles
                    .iter()
                    .map(|oracle| {
                        witness
                            .get::<AiurByteField>(*oracle)
                            .unwrap()
                            .as_slice::<AiurByteField>()
                    })
                    .collect::<Vec<_>>();
                witness
                    .new_column::<AiurByteField>(id)
                    .as_mut_slice::<AiurByteField>()
                    .into_par_iter()
                    .enumerate()
                    .for_each(|(i, w)| {
                        let mut res = AiurByteField::ZERO;
                        for slice in slices.iter() {
                            res += slice[i];
                        }
                        *w = res;
                    });
            }
            id
        });
        *id
    }

    fn constant(
        &mut self,
        builder: &mut ConstraintSystemBuilder<'_>,
        constant: Fields,
        log_n: usize,
    ) -> OracleId {
        let virt = Virtual::Constant { constant, log_n };
        let id = self.map.entry(virt).or_insert_with(|| match constant {
            Fields::FunctionIndex(f) => {
                let id = builder
                    .add_transparent("constant", Constant::new(log_n, f))
                    .unwrap();
                if let Some(witness) = builder.witness() {
                    witness.new_column_with_default(id, f);
                }
                id
            }
            Fields::Multiplicity(f) => {
                let id = builder
                    .add_transparent("constant", Constant::new(log_n, f))
                    .unwrap();
                if let Some(witness) = builder.witness() {
                    witness.new_column_with_default(id, f);
                }
                id
            }
        });
        *id
    }

    #[allow(dead_code)]
    fn step_down(
        &mut self,
        builder: &mut ConstraintSystemBuilder<'_>,
        log_n: usize,
        index: usize,
    ) -> OracleId {
        let virt = Virtual::StepDown { index, log_n };
        let id = self.map.entry(virt).or_insert_with(|| {
            let step_down = StepDown::new(log_n, index).unwrap();
            let id = builder
                .add_transparent("step_down", step_down.clone())
                .unwrap();
            if let Some(witness) = builder.witness() {
                step_down.populate(witness.new_column::<BinaryField1b>(id).packed());
            }
            id
        });
        *id
    }
}

impl AiurChannelIds {
    pub fn initialize_channels(builder: &mut ConstraintSystemBuilder<'_>) -> Self {
        let fun = builder.add_channel();
        let add = builder.add_channel();
        let mul = builder.add_channel();
        let mem = (0..NUM_MEM_TABLES).map(|_| builder.add_channel()).collect();
        AiurChannelIds { fun, add, mul, mem }
    }
}

impl Expr {
    fn to_sum_bit(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        virt_map: &mut VirtualMap,
        log_n: u8,
    ) -> Option<OracleId> {
        let mut sum = vec![];
        let mut offset = AiurField::ZERO;
        self.accumulate_sum(&mut sum, &mut offset)?;
        Some(virt_map.sum_bit(builder, sum, offset, log_n as usize))
    }

    fn to_sum_byte(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        virt_map: &mut VirtualMap,
        log_n: u8,
    ) -> Option<OracleId> {
        let mut sum = vec![];
        let mut offset = AiurField::ZERO;
        self.accumulate_sum(&mut sum, &mut offset)?;
        Some(virt_map.sum_byte(builder, sum, offset, log_n as usize))
    }

    fn accumulate_sum(&self, sum: &mut Vec<OracleId>, offset: &mut AiurField) -> Option<()> {
        match self {
            Self::Const(k) => *offset += *k,
            Self::Var(x) => sum.push(*x),
            Self::Add(a, b) => {
                a.accumulate_sum(sum, offset);
                b.accumulate_sum(sum, offset);
            }
            _ => return None,
        };
        Some(())
    }

    fn to_arith_expr(&self) -> (Vec<OracleId>, ArithExpr<AiurField>) {
        let mut map = FxIndexMap::default();
        let arith = self.to_arith_expr_aux(&mut map);
        let oracles = map.keys().copied().collect();
        (oracles, arith)
    }

    fn to_arith_expr_aux(&self, map: &mut FxIndexMap<OracleId, usize>) -> ArithExpr<AiurField> {
        match self {
            Expr::Const(f) => ArithExpr::Const((*f).into()),
            Expr::Var(id) => {
                let len = map.len();
                let index = map.entry(*id).or_insert(len);
                ArithExpr::Var(*index)
            }
            Expr::Add(a, b) => {
                let a = a.to_arith_expr_aux(map).into();
                let b = b.to_arith_expr_aux(map).into();
                ArithExpr::Add(a, b)
            }
            Expr::Mul(a, b) => {
                let a = a.to_arith_expr_aux(map).into();
                let b = b.to_arith_expr_aux(map).into();
                ArithExpr::Mul(a, b)
            }
            Expr::Pow(a, n) => {
                let a = a.to_arith_expr_aux(map).into();
                ArithExpr::Pow(a, *n)
            }
        }
    }
}

impl Columns {
    fn populate(&mut self, builder: &mut ConstraintSystemBuilder<'_>, trace: &Trace) {
        let witness = builder.witness().unwrap();
        for (id, values) in self.inputs.iter().zip(trace.inputs.iter()) {
            let count = values.len();
            witness
                .new_column::<BinaryField8b>(*id)
                .as_mut_slice::<u8>()[..count]
                .copy_from_slice(values);
        }
        for (id, values) in self.outputs.iter().zip(trace.outputs.iter()) {
            let count = values.len();
            witness
                .new_column::<BinaryField8b>(*id)
                .as_mut_slice::<u8>()[..count]
                .copy_from_slice(values);
        }
        for (id, values) in self.auxiliaries.iter().zip(trace.auxiliaries.iter()) {
            let count = values.len();
            witness
                .new_column::<BinaryField8b>(*id)
                .as_mut_slice::<u8>()[..count]
                .copy_from_slice(values);
        }
        {
            let count = trace.multiplicity.len();
            witness
                .new_column::<MultiplicityField>(self.multiplicity)
                .as_mut_slice::<MultiplicityField>()[..count]
                .copy_from_slice(&trace.multiplicity);
        }
        for (id, values) in self.require_hints.iter().zip(trace.require_hints.iter()) {
            let count = values.len();
            witness
                .new_column::<MultiplicityField>(*id)
                .as_mut_slice::<MultiplicityField>()[..count]
                .copy_from_slice(values);
        }
        for (id, values) in self.selectors.iter().zip(trace.selectors.iter()) {
            let mut bits = witness.new_column::<BinaryField1b>(*id);
            let bits = bits.packed();
            values.iter().enumerate().for_each(|(i, value)| {
                set_packed_slice(bits, i, BinaryField1b::from_underlier(*value));
            });
        }
    }
}

impl Toplevel {
    pub fn prover_synthesize(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        record: &QueryRecord,
    ) -> (Vec<u64>, AiurChannelIds) {
        let traces = self.generate_trace(record);
        let mut counts = Vec::with_capacity(self.functions.len());
        let channel_ids = AiurChannelIds::initialize_channels(builder);
        for (func_idx, (function, (trace, layout))) in
            self.functions.iter().zip(traces.into_iter()).enumerate()
        {
            let mut virt_map = VirtualMap::default();
            let count = trace.num_queries;
            counts.push(count);
            let log_n = count.next_power_of_two().ilog2() as u8;
            let mut columns = Columns::from_layout(builder, &layout, log_n);
            columns.populate(builder, &trace);
            let constraints = build_func_constraints(function, &layout, &columns);
            synthesize_constraints(
                builder,
                func_idx as u32,
                &channel_ids,
                count,
                constraints,
                &mut virt_map,
            );
        }
        (counts, channel_ids)
    }

    pub fn verifier_synthesize(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        counts: &[u64],
    ) -> AiurChannelIds {
        let channel_ids = AiurChannelIds::initialize_channels(builder);
        for (func_idx, (function, count)) in self.functions.iter().zip(counts).enumerate() {
            let mut virt_map = VirtualMap::default();
            let layout = func_layout(function);
            let log_n = count.next_power_of_two().ilog2() as u8;
            let columns = Columns::from_layout(builder, &layout, log_n);
            let constraints = build_func_constraints(function, &layout, &columns);
            synthesize_constraints(
                builder,
                func_idx as u32,
                &channel_ids,
                *count,
                constraints,
                &mut virt_map,
            );
        }
        channel_ids
    }
}

fn synthesize_constraints(
    builder: &mut ConstraintSystemBuilder<'_>,
    func_idx: u32,
    channel_ids: &AiurChannelIds,
    count: u64,
    mut constraints: Constraints,
    virt_map: &mut VirtualMap,
) {
    let log_n = count.next_power_of_two().ilog2() as u8;
    let constant = virt_map.constant(
        builder,
        Fields::FunctionIndex(FunctionIndexField::from_underlier(func_idx)),
        log_n as usize,
    );
    constraints.io.push(constant);
    provide(
        builder,
        channel_ids.fun,
        constraints.multiplicity,
        constraints.io,
        count,
        virt_map,
    );
    for (i, expr) in constraints.unique_constraints.into_iter().enumerate() {
        let ns = format!("unique constraint {i}");
        let (expr, oracles) = expr.to_arith_expr();
        builder.assert_zero(ns, expr, oracles);
    }
    for (i, expr) in constraints.shared_constraints.into_iter().enumerate() {
        let ns = format!("shared constraint {i}");
        let (expr, oracles) = expr.to_arith_expr();
        builder.assert_zero(ns, expr, oracles);
    }
    // TODO: Add, Mul gadgets
    // for (channel, sel, args) in constraints.sends {
    //     let sel = sel.to_sum_bit(builder, virt_map, log_n).unwrap();
    //     let oracles = args
    //         .iter()
    //         .map(|arg| arg.to_sum_byte(builder, virt_map, log_n).unwrap())
    //         .collect::<Vec<_>>();
    //     match channel {
    //         Channel::Add => builder
    //             .flush_custom(FlushDirection::Push, channel_ids.add, sel, oracles, 1)
    //             .unwrap(),
    //         Channel::Mul => builder
    //             .flush_custom(FlushDirection::Push, channel_ids.mul, sel, oracles, 1)
    //             .unwrap(),
    //         _ => (),
    //     };
    // }
    for (channel, sel, prev_index, args) in constraints.requires {
        let sel = sel.to_sum_bit(builder, virt_map, log_n).unwrap();
        let mut oracles = args
            .iter()
            .map(|arg| arg.to_sum_byte(builder, virt_map, log_n).unwrap())
            .collect::<Vec<_>>();
        match channel {
            Channel::Fun(func_idx) => {
                let idx = virt_map.constant(
                    builder,
                    Fields::FunctionIndex(FunctionIndexField::from_underlier(func_idx.0)),
                    log_n as usize,
                );
                oracles.push(idx);
                require(
                    builder,
                    channel_ids.fun,
                    prev_index,
                    oracles,
                    sel,
                    log_n.into(),
                );
            }
            Channel::Mem(size) => {
                let index = mem_index_from_size(size as usize);
                require(
                    builder,
                    channel_ids.mem[index],
                    prev_index,
                    oracles,
                    sel,
                    log_n.into(),
                );
            }
            _ => unreachable!(),
        };
    }
}

fn provide(
    builder: &mut ConstraintSystemBuilder<'_>,
    channel_id: ChannelId,
    multiplicity: OracleId,
    mut receive_args: Vec<OracleId>,
    count: u64,
    virt_map: &mut VirtualMap,
) {
    let mut send_args = receive_args.clone();
    let count = count as usize;
    let log_n = count.next_power_of_two().ilog2() as usize;
    let ones = virt_map.constant(builder, Fields::Multiplicity(MultiplicityField::ONE), log_n);
    if let Some(witness) = builder.witness() {
        witness.new_column_with_default(ones, MultiplicityField::ONE);
    }
    send_args.push(ones);
    receive_args.push(multiplicity);
    builder.send(channel_id, count, send_args).unwrap();
    builder.receive(channel_id, count, receive_args).unwrap();
}

fn require(
    builder: &mut ConstraintSystemBuilder<'_>,
    channel_id: ChannelId,
    prev_index: OracleId,
    mut send_args: Vec<OracleId>,
    sel: OracleId,
    log_n: usize,
) {
    let mut receive_args = send_args.clone();
    let index = builder
        .add_linear_combination(format!("index-{channel_id}"), log_n, [(
            prev_index,
            MULT_GEN.into(),
        )])
        .unwrap();
    if let Some(witness) = builder.witness() {
        (
            witness
                .get::<MultiplicityField>(prev_index)
                .unwrap()
                .as_slice::<u64>(),
            witness
                .new_column::<MultiplicityField>(index)
                .as_mut_slice::<u64>(),
        )
            .into_par_iter()
            .for_each(|(prev, index)| {
                *index = (MultiplicityField::from_underlier(*prev) * MULT_GEN).to_underlier()
            });
    }
    receive_args.push(prev_index);
    send_args.push(index);
    builder
        .flush_custom(FlushDirection::Pull, channel_id, sel, receive_args, 1)
        .unwrap();
    builder
        .flush_custom(FlushDirection::Push, channel_id, sel, send_args, 1)
        .unwrap();
}

#[cfg(test)]
mod tests {
    use binius_circuits::builder::{ConstraintSystemBuilder, types::U};
    use binius_core::{
        constraint_system::{
            self,
            channel::{Boundary, FlushDirection},
            validate::validate_witness,
        },
        fiat_shamir::HasherChallenger,
        tower::CanonicalTowerFamily,
    };
    use binius_field::{Field, underlier::WithUnderlier};
    use binius_hal::make_portable_backend;
    use binius_hash::compress::Groestl256ByteCompression;
    use binius_math::DefaultEvaluationDomainFactory;
    use groestl_crypto::Groestl256;

    use crate::aiur::{
        execute::tests::factorial_function,
        ir::{FuncIdx, Toplevel},
        layout::AiurField,
        trace::MULT_GEN,
    };

    #[test]
    fn test_factorial() {
        let toplevel = Toplevel {
            functions: vec![factorial_function()],
        };

        let allocator = bumpalo::Bump::new();
        let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);

        let record = toplevel.execute(FuncIdx(0), 100u64.to_le_bytes().to_vec());
        let (_counts, channel_ids) = toplevel.prover_synthesize(&mut builder, &record);

        let witness = builder
            .take_witness()
            .expect("builder created with witness");
        let constraint_system = builder.build().unwrap();

        let domain_factory = DefaultEvaluationDomainFactory::default();
        let backend = make_portable_backend();
        const LOG_INV_RATE: usize = 1;
        const SECURITY_BITS: usize = 100;

        let f = AiurField::from_underlier;
        let io = vec![
            // input
            f(100),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            // output
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            // function index
            f(0),
        ];
        let mut push_io = io.clone();
        push_io.push(MULT_GEN.into());
        let push_boundaries = Boundary {
            values: push_io,
            channel_id: channel_ids.fun,
            direction: FlushDirection::Push,
            multiplicity: 1,
        };

        let mut pull_io = io;
        pull_io.push(AiurField::ONE);
        let pull_boundaries = Boundary {
            values: pull_io,
            channel_id: channel_ids.fun,
            direction: FlushDirection::Pull,
            multiplicity: 1,
        };

        let boundaries = vec![pull_boundaries, push_boundaries];
        validate_witness(&constraint_system, &boundaries, &witness).unwrap();

        let proof = constraint_system::prove::<
            U,
            CanonicalTowerFamily,
            _,
            Groestl256,
            Groestl256ByteCompression,
            HasherChallenger<Groestl256>,
            _,
        >(
            &constraint_system,
            LOG_INV_RATE,
            SECURITY_BITS,
            &boundaries,
            witness,
            &domain_factory,
            &backend,
        )
        .unwrap();

        constraint_system::verify::<
            U,
            CanonicalTowerFamily,
            Groestl256,
            Groestl256ByteCompression,
            HasherChallenger<Groestl256>,
        >(
            &constraint_system,
            LOG_INV_RATE,
            SECURITY_BITS,
            &boundaries,
            proof,
        )
        .unwrap();
    }
}
