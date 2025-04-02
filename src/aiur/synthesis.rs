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
    layout::{AiurField, FunctionIndexField, MultiplicityField},
    memory::{MemTrace, prover_synthesize_mem, verifier_synthesize_mem},
    trace::{MULT_GEN, Trace},
    transparent::{Fields, Virtual},
};

#[derive(Clone)]
pub struct AiurChannelIds {
    pub fun: ChannelId,
    pub add: ChannelId,
    pub mul: ChannelId,
    pub mem: Vec<(u32, ChannelId)>,
}

impl AiurChannelIds {
    pub fn get_mem_channel(&self, size: u32) -> ChannelId {
        *self.mem.iter().find(|(k, _)| *k == size).map_or_else(
            || panic!("Internal error: no memory map of size {size}"),
            |(_, v)| v,
        )
    }

    pub fn get_mem_pos(&self, size: u32) -> usize {
        self.mem
            .iter()
            .position(|(k, _)| *k == size)
            .unwrap_or_else(|| panic!("Internal error: no memory map of size {size}"))
    }
}

pub struct AiurCount {
    pub fun: Vec<u64>,
    pub mem: Vec<u64>,
}

#[derive(Default)]
pub struct VirtualMap {
    pub map: FxIndexMap<Virtual, OracleId>,
}

impl VirtualMap {
    fn sum_bit(
        &mut self,
        builder: &mut ConstraintSystemBuilder<'_>,
        oracles: Vec<OracleId>,
        offset: AiurByteField,
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
                .add_linear_combination_with_offset("linear combination", log_n, offset.into(), lc)
                .unwrap();
            if let Some(witness) = builder.witness() {
                let slices = oracles
                    .iter()
                    .map(|oracle| witness.get::<BinaryField1b>(*oracle).unwrap().packed())
                    .collect::<Vec<_>>();
                let mut bits = witness.new_column::<BinaryField1b>(id);
                let bits = bits.packed();
                (0..(1 << log_n)).for_each(|i| {
                    let mut res = offset
                        .try_into()
                        .expect("Internal error: The offset is not a bit");
                    for slice in slices.iter() {
                        res += get_packed_slice(slice, i);
                    }
                    set_packed_slice(bits, i, res);
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
        offset: AiurByteField,
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
                .add_linear_combination_with_offset("linear combination", log_n, offset.into(), lc)
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
                        let mut res = offset;
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
        macro_rules! constant {
            ($f:ident) => {{
                let id = builder
                    .add_transparent("constant", Constant::new(log_n, $f))
                    .unwrap();
                if let Some(witness) = builder.witness() {
                    witness.new_column_with_default(id, $f);
                }
                id
            }};
        }
        let id = self.map.entry(virt).or_insert_with(|| match constant {
            Fields::Bit(f) => constant!(f),
            Fields::Byte(f) => constant!(f),
            Fields::Multiplicity(f) => constant!(f),
            Fields::FunctionIndex(f) => constant!(f),
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
    pub fn initialize_channels(
        builder: &mut ConstraintSystemBuilder<'_>,
        mem_sizes: &[u32],
    ) -> Self {
        let fun = builder.add_channel();
        let add = builder.add_channel();
        let mul = builder.add_channel();
        let mem = mem_sizes
            .iter()
            .map(|size| (*size, builder.add_channel()))
            .collect();
        AiurChannelIds { fun, add, mul, mem }
    }
}

impl Expr {
    fn to_sum_bit(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        virt_map: &mut VirtualMap,
        log_n: u8,
    ) -> OracleId {
        if let Expr::Const(x) = self {
            let bit = (*x).try_into().expect("Constant not a bit");
            return virt_map.constant(builder, Fields::Bit(bit), log_n as usize);
        }
        let mut sum = vec![];
        let mut offset = AiurByteField::ZERO;
        self.accumulate_sum(&mut sum, &mut offset).unwrap();
        if sum.len() == 1 && offset == AiurByteField::ZERO {
            return sum[0];
        }
        virt_map.sum_bit(builder, sum, offset, log_n as usize)
    }

    fn to_sum_byte(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        virt_map: &mut VirtualMap,
        log_n: u8,
    ) -> OracleId {
        if let Expr::Const(x) = self {
            return virt_map.constant(builder, Fields::Byte(*x), log_n as usize);
        }
        let mut sum = vec![];
        let mut offset = AiurByteField::ZERO;
        self.accumulate_sum(&mut sum, &mut offset).unwrap();
        if sum.len() == 1 && offset == AiurByteField::ZERO {
            return sum[0];
        }
        virt_map.sum_byte(builder, sum, offset, log_n as usize)
    }

    fn accumulate_sum(&self, sum: &mut Vec<OracleId>, offset: &mut AiurByteField) -> Option<()> {
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
    ) -> (AiurCount, AiurChannelIds) {
        let traces = self.generate_trace(record);
        let mut aiur_count = AiurCount {
            fun: Vec::with_capacity(self.functions.len()),
            mem: Vec::with_capacity(self.mem_sizes.len()),
        };
        let channel_ids = AiurChannelIds::initialize_channels(builder, &self.mem_sizes);
        for (func_idx, function) in self.functions.iter().enumerate() {
            let trace = &traces[func_idx];
            let layout = &self.layouts[func_idx];
            let mut virt_map = VirtualMap::default();
            let count = trace.num_queries;
            aiur_count.fun.push(count);
            let log_n = count.next_power_of_two().ilog2() as u8;
            let mut columns = Columns::from_layout(builder, layout, log_n);
            columns.populate(builder, trace);
            let constraints = build_func_constraints(function, layout, &columns);
            synthesize_constraints(
                builder,
                func_idx as u32,
                &channel_ids,
                count,
                constraints,
                &mut virt_map,
            );
        }
        for &size in self.mem_sizes.iter() {
            let mem_channel = channel_ids.get_mem_channel(size);
            let trace = MemTrace::generate_trace(size, record);
            let count = trace.height;
            aiur_count.mem.push(count.try_into().unwrap());
            prover_synthesize_mem(builder, mem_channel, &trace);
        }
        (aiur_count, channel_ids)
    }

    pub fn verifier_synthesize(
        &self,
        builder: &mut ConstraintSystemBuilder<'_>,
        count: &AiurCount,
    ) -> AiurChannelIds {
        let channel_ids = AiurChannelIds::initialize_channels(builder, &self.mem_sizes);
        for (func_idx, function) in self.functions.iter().enumerate() {
            let count = count.fun[func_idx];
            let layout = &self.layouts[func_idx];
            let mut virt_map = VirtualMap::default();
            let log_n = count.next_power_of_two().ilog2() as u8;
            let columns = Columns::from_layout(builder, layout, log_n);
            let constraints = build_func_constraints(function, layout, &columns);
            synthesize_constraints(
                builder,
                func_idx as u32,
                &channel_ids,
                count,
                constraints,
                &mut virt_map,
            );
        }
        for &size in self.mem_sizes.iter() {
            let mem_channel = channel_ids.get_mem_channel(size);
            let idx = channel_ids.get_mem_pos(size);
            let mem_counts = count.mem[idx];
            verifier_synthesize_mem(builder, mem_channel, size, mem_counts);
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
    {
        // Topmost selector must be equal to the count step down
        let step_down = virt_map.step_down(builder, log_n as usize, count as usize);
        let (expr, oracles) = (constraints.topmost_selector - Expr::Var(step_down)).to_arith_expr();
        builder.assert_zero("topmost", expr, oracles);
    }
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
    // TODO: Add, Mul chips
    // for (channel, sel, args) in constraints.sends {
    //     let sel = sel.to_sum_bit(builder, virt_map, log_n);
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
        match channel {
            Channel::Fun(func_idx) => {
                let sel = sel.to_sum_bit(builder, virt_map, log_n);
                let mut oracles = args
                    .iter()
                    .map(|arg| arg.to_sum_byte(builder, virt_map, log_n))
                    .collect::<Vec<_>>();
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
                let sel = sel.to_sum_bit(builder, virt_map, log_n);
                let oracles = args
                    .iter()
                    .map(|arg| arg.to_sum_byte(builder, virt_map, log_n))
                    .collect::<Vec<_>>();
                let channel_id = channel_ids.get_mem_channel(size);
                require(builder, channel_id, prev_index, oracles, sel, log_n.into());
            }
            _ => unreachable!(),
        };
    }
}

pub fn provide(
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
    use binius_hash::groestl::Groestl256ByteCompression;
    use groestl_crypto::Groestl256;

    use crate::{
        aiur::{
            execute::tests::factorial_toplevel,
            frontend::expr::toplevel_from_funcs,
            ir::{FuncIdx, Toplevel},
            layout::AiurField,
            trace::MULT_GEN,
        },
        func,
    };

    fn prove_verify(toplevel: &Toplevel, index: u8, input: &[u8], output: &[u8]) {
        let allocator = bumpalo::Bump::new();
        let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);

        let record = toplevel.execute(FuncIdx(index as u32), input.to_vec());
        let (_counts, channel_ids) = toplevel.prover_synthesize(&mut builder, &record);

        let witness = builder
            .take_witness()
            .expect("builder created with witness");
        let constraint_system = builder.build().unwrap();

        let backend = make_portable_backend();
        const LOG_INV_RATE: usize = 1;
        const SECURITY_BITS: usize = 100;

        let f = |x: u8| AiurField::from_underlier(x.into());
        let mut io = input.iter().copied().map(f).collect::<Vec<_>>();
        io.extend(output.iter().copied().map(f));
        io.push(f(index));
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

        let boundaries = [pull_boundaries, push_boundaries];
        validate_witness(&constraint_system, &boundaries, &witness).unwrap();

        let proof = constraint_system::prove::<
            U,
            CanonicalTowerFamily,
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

    #[test]
    fn test_factorial() {
        let toplevel = factorial_toplevel();
        let func_idx = 0;
        let input = &[100, 0, 0, 0, 0, 0, 0, 0];
        let output = &[0, 0, 0, 0, 0, 0, 0, 0];
        prove_verify(&toplevel, func_idx, input, output);
    }

    #[test]
    fn test_load_store() {
        let func = func!(
        fn load_store(n): [8] {
            let one = 1;
            if !n {
                let ptr = 50;
                let x = load(ptr);
                return x
            }
            let _ptr = store(n);
            let pred = sub(n, one);
            let m = call(load_store, pred);
            return m
        });
        let toplevel = toplevel_from_funcs(&[func]);
        let func_idx = 0;
        let input = &[100, 0, 0, 0, 0, 0, 0, 0];
        let output = &[50, 0, 0, 0, 0, 0, 0, 0];
        prove_verify(&toplevel, func_idx, input, output);
    }
}
