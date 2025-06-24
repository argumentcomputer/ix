use anyhow::{Result, bail, ensure};
use binius_core::oracle::ShiftVariant;
use binius_field::{
    BinaryField1b as B1, BinaryField8b as B8, BinaryField16b as B16, BinaryField32b as B32,
    BinaryField64b as B64, BinaryField128b as B128, Field, TowerField,
    arch::OptimalUnderlier,
    underlier::{UnderlierType, UnderlierWithBitOps},
};
use binius_utils::checked_arithmetics::log2_strict_usize;
use indexmap::IndexSet;
use rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator,
        ParallelIterator,
    },
    slice::{ParallelSlice, ParallelSliceMut},
};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{collections::hash_map::Entry, iter::repeat, mem::transmute};

use super::{
    ModuleMode, OracleIdx, OracleKind, RelativeHeight,
    transparent::{Incremental, Transparent, replicate_within_u128},
    witness::{UNDERLIER_SIZE, WitnessModule},
};

impl WitnessModule {
    /// Populates a witness module according to a given `ModuleMode`.
    ///
    /// Note: Parts of this algorithm assume that the dependency oracles are
    /// optimally packed. That is, there is no sparse data encoded.
    pub fn populate(&mut self, mode: ModuleMode) -> Result<()> {
        let ModuleMode::Active { log_height, depth } = mode else {
            // Deactivated module.
            return Ok(());
        };

        let log_height_usize = log_height as usize;

        // "Root oracles" are those which aren't committed and aren't dependencies
        // of any other oracle. `root_oracles` starts with all oracles, which are
        // removed as the following loop finds out they break such condition.
        //
        // The loop also uses ensures that committed oracles are bound to entries,
        // accumulating the amount of missing bytes for each entry to be padded
        // with zero afterwards in order to empty out their buffers.
        let mut root_oracles: FxHashSet<_> = (0..self.num_oracles()).map(OracleIdx).collect();
        let mut missing_bytes_map = FxHashMap::default();
        for (oracle_idx, oracle_info) in self.oracles.iter().enumerate() {
            let oracle_idx = OracleIdx(oracle_idx);
            match &oracle_info.kind {
                OracleKind::Committed => {
                    let Some(&(entry_id, tower_level)) = self.entry_map.get(&oracle_idx) else {
                        bail!(
                            "Committed oracle {} (id={oracle_idx}) for witness module {} is unbound",
                            &oracle_info.name,
                            &self.module_id,
                        );
                    };

                    let target_log_height = oracle_info.relative_height.transform(log_height);
                    let target_log_num_bits = target_log_height as usize + tower_level;
                    ensure!(
                        target_log_num_bits >= OptimalUnderlier::LOG_BITS,
                        "Committed oracle {} (id={oracle_idx}) for witness module {} doesn't fulfill 128 bits",
                        &oracle_info.name,
                        &self.module_id,
                    );
                    let target_num_bytes = (1 << target_log_num_bits) / 8;

                    let current_num_bytes = UNDERLIER_SIZE * self.entries[entry_id].len()
                        + self.buffers[entry_id].len();
                    ensure!(
                        current_num_bytes <= target_num_bytes,
                        "Too many bytes for oracle {} (id={oracle_idx}). Maximum allowed is {target_num_bytes}",
                        &oracle_info.name
                    );

                    // Compute and accumulate the amount of missing bytes.
                    if current_num_bytes < target_num_bytes {
                        let num_missing_bytes = target_num_bytes - current_num_bytes;
                        if let Some(existing_num_missing_bytes) =
                            missing_bytes_map.insert(entry_id, num_missing_bytes)
                        {
                            ensure!(
                                num_missing_bytes == existing_num_missing_bytes,
                                "Incompatible amount of missing data for entry {entry_id}"
                            );
                        }
                    }

                    // A committed oracle is not a root oracle.
                    root_oracles.remove(&oracle_idx);
                }
                OracleKind::LinearCombination { inner, .. } => {
                    for (inner_oracle_id, _) in inner {
                        root_oracles.remove(inner_oracle_id);
                    }
                }
                OracleKind::Packed { inner, .. }
                | OracleKind::Shifted { inner, .. }
                | OracleKind::Projected { inner, .. } => {
                    root_oracles.remove(inner);
                }
                OracleKind::Transparent(_) | OracleKind::StepDown => (),
            }
        }

        // Pad missing bytes with zeros.
        for (entry_id, num_missing_bytes) in missing_bytes_map {
            self.push_u8s_to(repeat(0).take(num_missing_bytes), entry_id);
        }

        // The incoming code block aims to calculate a compute order for the
        // oracles, in which the root oracles will be last and the leaf oracles
        // will be first. It is stored in `compute_order` in reverse so that
        // iterating over the oracles should be done by popping.
        let mut compute_order = IndexSet::<_, FxBuildHasher>::default();
        let mut to_visit_stack = Vec::from_iter(root_oracles);
        macro_rules! stack_to_visit {
            ($o:ident) => {
                if !compute_order.contains($o) {
                    to_visit_stack.push(*$o);
                }
            };
        }
        while let Some(oracle_idx) = to_visit_stack.pop() {
            let mut is_committed = false;
            match &self.oracles[oracle_idx.val()].kind {
                OracleKind::Committed => is_committed = true,
                OracleKind::LinearCombination { inner, .. } => {
                    for (inner_oracle_id, _) in inner {
                        stack_to_visit!(inner_oracle_id);
                    }
                }
                OracleKind::Packed { inner, .. }
                | OracleKind::Shifted { inner, .. }
                | OracleKind::Projected { inner, .. } => {
                    stack_to_visit!(inner)
                }
                OracleKind::Transparent(_) | OracleKind::StepDown => (),
            }
            if !is_committed {
                compute_order.insert(oracle_idx);
            }
        }

        // And now we're finally able to populate the witness, following the
        // correct compute order and making the assumption that dependency oracles
        // were already populated.
        while let Some(oracle_idx) = compute_order.pop() {
            if self.entry_map.contains_key(&oracle_idx) {
                // Already populated. Skip.
                continue;
            }
            let oracle_info = &self.oracles[oracle_idx.val()];
            let oracle_entry = match &oracle_info.kind {
                OracleKind::Committed => unreachable!("Committed oracles shouldn't be computed"),
                OracleKind::LinearCombination { offset, inner } => {
                    // The strategy to compute linear combinations is to pack the same number
                    // of binary field elements in an underlier as the target oracle. For example,
                    // if the target oracle is in the tower level 6, that means it will contain
                    // two B64's in a single underlier and thus we need to pack the dependencies
                    // in the same manner.

                    let mut tower_level = offset.min_tower_level();
                    let mut inner_data = Vec::with_capacity(inner.len());

                    // Extract entry data from `inner`, assuming it was already computed.
                    for (inner_oracle_id, coeff) in inner {
                        let &(entry_id, inner_tower_level) = self
                            .entry_map
                            .get(inner_oracle_id)
                            .expect("Data should be available");
                        tower_level = tower_level
                            .max(inner_tower_level)
                            .max(coeff.min_tower_level());
                        inner_data.push((inner_oracle_id, coeff, entry_id, inner_tower_level));
                    }

                    let log_height = oracle_info.relative_height.transform(log_height);

                    // The number of underliers for the target oracle and also for the dependencies
                    let entry_len =
                        (1 << (log_height as usize + tower_level)) / OptimalUnderlier::BITS;
                    ensure!(
                        entry_len != 0,
                        "Not enough data to compute linear combination. 128 bits are required."
                    );

                    // Expand an underlier into multiple underliers, extracting binary field elements
                    // data for upcasts into the tower level of the target oracle
                    let expand = |u, tower_diff| {
                        assert_ne!(tower_diff, 0);
                        let u128 = unsafe { transmute::<OptimalUnderlier, u128>(u) };
                        let tower_diff_pow = 1usize << tower_diff;
                        let step = 128 / tower_diff_pow;
                        let mask = (1u128 << step) - 1;
                        (0..tower_diff_pow)
                            .map(|i| OptimalUnderlier::from((u128 >> (i * step)) & mask))
                            .collect::<Vec<_>>()
                    };
                    // For every inner oracle dependency, cache the underliers needed to compute
                    // the linear combination, according to the tower diff w.r.t. the target oracle
                    let mut dependencies = FxHashMap::default();
                    for &(inner_oracle_id, _, entry_id, inner_tower_level) in &inner_data {
                        let tower_diff = tower_level - inner_tower_level;
                        if let Entry::Vacant(e) = dependencies.entry(inner_oracle_id) {
                            let underliers = if tower_diff == 0 {
                                self.entries[entry_id].clone()
                            } else {
                                let entries = &self.entries[entry_id];
                                let mut dep_underliers = vec![OptimalUnderlier::ZERO; entry_len];
                                dep_underliers
                                    .par_chunks_mut(1 << tower_diff)
                                    .enumerate()
                                    .for_each(|(chunk_idx, chunk)| {
                                        let expanded = expand(entries[chunk_idx], tower_diff);
                                        assert_eq!(chunk.len(), expanded.len());
                                        for (chunk_elt, expanded_item) in
                                            chunk.iter_mut().zip(expanded)
                                        {
                                            *chunk_elt = expanded_item;
                                        }
                                    });
                                dep_underliers
                            };
                            e.insert(underliers);
                        }
                    }
                    // Convenient getter for the i-th underlier from `dependencies`
                    let get_dep_underlier = |inner_oracle_id, i| {
                        dependencies
                            .get(inner_oracle_id)
                            .expect("Data should be available")[i]
                    };

                    // The resulting underliers start with zeros and are mutated in parallel for
                    // extra speed.
                    let mut underliers = vec![OptimalUnderlier::ZERO; entry_len];
                    match tower_level {
                        0 => {
                            let span = |b| if b == &B128::ZERO { 0 } else { u128::MAX };
                            let offset = span(offset);
                            underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                let res = inner_data.iter().fold(
                                    offset,
                                    |acc, (inner_oracle_id, coeff, ..)| {
                                        let underlier = get_dep_underlier(inner_oracle_id, i);
                                        let u128 = unsafe {
                                            transmute::<OptimalUnderlier, u128>(underlier)
                                        };
                                        let coeff = span(*coeff);
                                        // In `B1`, addition is bitwise XOR and multiplication
                                        // is bitwise AND
                                        acc ^ (coeff & u128)
                                    },
                                );
                                *u = unsafe { transmute::<u128, OptimalUnderlier>(res) };
                            });
                        }
                        1 | 2 => todo!(),
                        3 => {
                            let offset: B8 =
                                (*offset).try_into().expect("Wrong minimal tower level");
                            underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                #[rustfmt::skip]
                                let res = inner_data.iter().fold(
                                    [offset; 16],
                                    |[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15],
                                    (inner_oracle_id, coeff, ..)| {
                                        let underlier = get_dep_underlier(inner_oracle_id, i);
                                        let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] = unsafe {
                                            transmute::<OptimalUnderlier, [B8; 16]>(underlier)
                                        };
                                        let coeff: B8 =
                                            (**coeff).try_into().expect("Wrong minimal tower");
                                        [
                                            a0 + coeff * b0, a1 + coeff * b1, a2 + coeff * b2, a3 + coeff * b3,
                                            a4 + coeff * b4, a5 + coeff * b5, a6 + coeff * b6, a7 + coeff * b7,
                                            a8 + coeff * b8, a9 + coeff * b9, a10 + coeff * b10, a11 + coeff * b11,
                                            a12 + coeff * b12, a13 + coeff * b13, a14 + coeff * b14, a15 + coeff * b15
                                        ]
                                    },
                                );
                                *u = unsafe { transmute::<[B8; 16], OptimalUnderlier>(res) };
                            })
                        }
                        4 => {
                            let offset: B16 =
                                (*offset).try_into().expect("Wrong minimal tower level");
                            underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                let res = inner_data.iter().fold(
                                    [offset; 8],
                                    |[a0, a1, a2, a3, a4, a5, a6, a7], (inner_oracle_id, coeff, ..)| {
                                        let underlier = get_dep_underlier(inner_oracle_id, i);
                                        let [b0, b1, b2, b3, b4, b5, b6, b7] = unsafe {
                                            transmute::<OptimalUnderlier, [B16; 8]>(underlier)
                                        };
                                        let coeff: B16 =
                                            (**coeff).try_into().expect("Wrong minimal tower");
                                        [
                                            a0 + coeff * b0, a1 + coeff * b1, a2 + coeff * b2, a3 + coeff * b3,
                                            a4 + coeff * b4, a5 + coeff * b5, a6 + coeff * b6, a7 + coeff * b7,
                                        ]
                                    },
                                );
                                *u = unsafe { transmute::<[B16; 8], OptimalUnderlier>(res) };
                            })
                        }
                        5 => {
                            let offset: B32 =
                                (*offset).try_into().expect("Wrong minimal tower level");
                            underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                let res = inner_data.iter().fold(
                                    [offset; 4],
                                    |[a0, a1, a2, a3], (inner_oracle_id, coeff, ..)| {
                                        let underlier = get_dep_underlier(inner_oracle_id, i);
                                        let [b0, b1, b2, b3] = unsafe {
                                            transmute::<OptimalUnderlier, [B32; 4]>(underlier)
                                        };
                                        let coeff: B32 =
                                            (**coeff).try_into().expect("Wrong minimal tower");
                                        [
                                            a0 + coeff * b0,
                                            a1 + coeff * b1,
                                            a2 + coeff * b2,
                                            a3 + coeff * b3,
                                        ]
                                    },
                                );
                                *u = unsafe { transmute::<[B32; 4], OptimalUnderlier>(res) };
                            })
                        }
                        6 => {
                            let offset: B64 =
                                (*offset).try_into().expect("Wrong minimal tower level");
                            underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                let res = inner_data.iter().fold(
                                    [offset; 2],
                                    |[a0, a1], (inner_oracle_id, coeff, ..)| {
                                        let underlier = get_dep_underlier(inner_oracle_id, i);
                                        let [b0, b1] = unsafe {
                                            transmute::<OptimalUnderlier, [B64; 2]>(underlier)
                                        };
                                        let coeff: B64 =
                                            (**coeff).try_into().expect("Wrong minimal tower");
                                        [a0 + coeff * b0, a1 + coeff * b1]
                                    },
                                );
                                *u = unsafe { transmute::<[B64; 2], OptimalUnderlier>(res) };
                            })
                        }
                        7 => underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                            let res = inner_data.iter().fold(
                                *offset,
                                |acc, (inner_oracle_id, coeff, ..)| {
                                    let underlier = get_dep_underlier(inner_oracle_id, i);
                                    let b =
                                        unsafe { transmute::<OptimalUnderlier, B128>(underlier) };
                                    acc + **coeff * b
                                },
                            );
                            *u = unsafe { transmute::<B128, OptimalUnderlier>(res) };
                        }),
                        _ => bail!("Unsupported tower level: {tower_level}"),
                    }
                    let entry_id = self.new_entry();
                    self.entries[entry_id] = underliers;
                    (entry_id, tower_level)
                }
                OracleKind::Packed { inner, log_degree } => {
                    let &(inner_entry_id, inner_tower_level) =
                        self.entry_map.get(inner).expect("Data should be available");
                    (inner_entry_id, inner_tower_level + log_degree)
                }
                OracleKind::Transparent(transparent) => match transparent {
                    Transparent::Constant(c) => {
                        let log_height = oracle_info.relative_height.transform(log_height);
                        let log_height_usize = log_height as usize;
                        let tower_level = oracle_info.tower_level;
                        let log_num_bits = log_height_usize + tower_level;
                        if log_num_bits >= OptimalUnderlier::LOG_BITS {
                            let u = OptimalUnderlier::from(replicate_within_u128(*c));
                            let num_underliers = (1 << log_num_bits) / OptimalUnderlier::BITS;
                            let entry_id = self.new_entry();
                            self.entries[entry_id] = vec![u; num_underliers];
                            (entry_id, tower_level)
                        } else {
                            let height = 1 << log_height;
                            let shift_size = OptimalUnderlier::BITS / height;
                            let mut u128 = 0u128;
                            for i in 0..height {
                                u128 |= c.val() << (i * shift_size);
                            }
                            let entry_id = self.new_entry();
                            self.entries[entry_id] = vec![OptimalUnderlier::from(u128)];
                            (entry_id, OptimalUnderlier::LOG_BITS - log_height_usize)
                        }
                    }
                    Transparent::Incremental => {
                        let log_height = oracle_info.relative_height.transform(log_height);
                        let log_height_usize = log_height as usize;
                        let tower_level = Incremental::min_tower_level(log_height);
                        let log_num_bits = log_height_usize + tower_level;
                        if log_num_bits >= OptimalUnderlier::LOG_BITS {
                            let num_underliers = (1 << log_num_bits) / OptimalUnderlier::BITS;
                            let mut underliers = vec![OptimalUnderlier::ZERO; num_underliers];
                            match tower_level {
                                3 => {
                                    underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                        let i = (i % (u8::MAX as usize)).try_into().unwrap();
                                        let (start, _) = 16u8.overflowing_mul(i);
                                        #[rustfmt::skip]
                                        let data = [
                                            start,      start +  1, start +  2, start +  3,
                                            start +  4, start +  5, start +  6, start +  7,
                                            start +  8, start +  9, start + 10, start + 11,
                                            start + 12, start + 13, start + 14, start + 15,
                                        ];
                                        *u = unsafe {
                                            transmute::<[u8; 16], OptimalUnderlier>(data)
                                        };
                                    });
                                }
                                4 => {
                                    underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                        let i = (i % (u16::MAX as usize)).try_into().unwrap();
                                        let (start, _) = 8u16.overflowing_mul(i);
                                        #[rustfmt::skip]
                                        let data = [
                                            start,     start + 1, start + 2, start + 3,
                                            start + 4, start + 5, start + 6, start + 7,
                                        ];
                                        *u = unsafe {
                                            transmute::<[u16; 8], OptimalUnderlier>(data)
                                        };
                                    });
                                }
                                5 => {
                                    underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                        let i = (i % (u32::MAX as usize)).try_into().unwrap();
                                        let (start, _) = 4u32.overflowing_mul(i);
                                        let data = [start, start + 1, start + 2, start + 3];
                                        *u = unsafe {
                                            transmute::<[u32; 4], OptimalUnderlier>(data)
                                        };
                                    });
                                }
                                6 => {
                                    underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                        let (start, _) = 2u64.overflowing_mul(i as u64);
                                        let data = [start, start + 1];
                                        *u = unsafe {
                                            transmute::<[u64; 2], OptimalUnderlier>(data)
                                        };
                                    });
                                }
                                _ => todo!(),
                            };
                            let entry_id = self.new_entry();
                            self.entries[entry_id] = underliers;
                            (entry_id, tower_level)
                        } else {
                            let height = 1 << log_height;
                            let shift_size = OptimalUnderlier::BITS / height;
                            let mut u128 = 0u128;
                            for i in 0..height {
                                u128 |= (i as u128) << (i * shift_size);
                            }
                            let entry_id = self.new_entry();
                            self.entries[entry_id] = vec![OptimalUnderlier::from(u128)];
                            (entry_id, OptimalUnderlier::LOG_BITS - log_height_usize)
                        }
                    }
                },
                OracleKind::StepDown => {
                    let tower_level = oracle_info.tower_level;
                    assert_eq!(tower_level, 0);
                    assert_eq!(oracle_info.relative_height, RelativeHeight::Base);
                    let depth_usize: usize = depth.try_into()?;
                    if log_height_usize >= OptimalUnderlier::LOG_BITS {
                        let num_underliers = (1 << log_height) / OptimalUnderlier::BITS;
                        let mut underliers = vec![OptimalUnderlier::from(0u128); num_underliers];
                        let step_down_changes_at = depth_usize / OptimalUnderlier::BITS;

                        // Set the first bits to 1.
                        underliers[..step_down_changes_at]
                            .par_iter_mut()
                            .for_each(|u| *u = OptimalUnderlier::from(u128::MAX));

                        if step_down_changes_at < num_underliers {
                            // Produce an `u128` with the `depth_usize % OptimalUnderlier::BITS`
                            // least significant bits set to one and the rest set to zero.
                            let u128: u128 = (1 << (depth_usize % OptimalUnderlier::BITS)) - 1;
                            underliers[step_down_changes_at] = OptimalUnderlier::from(u128);
                        }

                        let entry_id = self.new_entry();
                        self.entries[entry_id] = underliers;
                        (entry_id, tower_level)
                    } else {
                        // Fill an `OptimalUnderlier` with sparse data
                        let shift_size = OptimalUnderlier::BITS / (1 << log_height);
                        let mut u = 0u128;
                        for i in 0..depth_usize {
                            u |= 1 << (i * shift_size)
                        }

                        let entry_id = self.new_entry();
                        self.entries[entry_id] = vec![OptimalUnderlier::from(u)];
                        (entry_id, OptimalUnderlier::LOG_BITS - log_height_usize)
                    }
                }
                OracleKind::Shifted {
                    inner,
                    shift_offset,
                    block_bits,
                    variant,
                } => {
                    let tower_level = oracle_info.tower_level;

                    let &(inner_entry_id, _) =
                        self.entry_map.get(inner).expect("Data should be available");

                    let mut underliers = self.entries[inner_entry_id].clone();

                    macro_rules! shift_underliers {
                        ($parts_typ:ty, $f:expr) => {
                            underliers.par_iter_mut().for_each(|underlier| {
                                let mut out = unsafe {
                                    transmute::<OptimalUnderlier, $parts_typ>(*underlier)
                                };
                                for out_i in out.iter_mut() {
                                    *out_i = $f(out_i).into();
                                }
                                *underlier =
                                    unsafe { transmute::<$parts_typ, OptimalUnderlier>(out) };
                            });
                        };
                    }

                    match (block_bits, variant) {
                        (3, ShiftVariant::LogicalRight) => {
                            shift_underliers!([B8; 16], |x: &B8| x.val() >> shift_offset);
                        }
                        (3, ShiftVariant::LogicalLeft) => {
                            shift_underliers!([B8; 16], |x: &B8| x.val() << shift_offset);
                        }
                        (3, ShiftVariant::CircularLeft) => {
                            shift_underliers!([B8; 16], |x: &B8| x
                                .val()
                                .rotate_left(*shift_offset));
                        }
                        (4, ShiftVariant::LogicalRight) => {
                            shift_underliers!([B16; 8], |x: &B16| x.val() >> shift_offset);
                        }
                        (4, ShiftVariant::LogicalLeft) => {
                            shift_underliers!([B16; 8], |x: &B16| x.val() << shift_offset);
                        }
                        (4, ShiftVariant::CircularLeft) => {
                            shift_underliers!([B16; 8], |x: &B16| x
                                .val()
                                .rotate_left(*shift_offset));
                        }
                        (5, ShiftVariant::LogicalRight) => {
                            shift_underliers!([B32; 4], |x: &B32| x.val() >> shift_offset);
                        }
                        (5, ShiftVariant::LogicalLeft) => {
                            shift_underliers!([B32; 4], |x: &B32| x.val() << shift_offset);
                        }
                        (5, ShiftVariant::CircularLeft) => {
                            shift_underliers!([B32; 4], |x: &B32| x
                                .val()
                                .rotate_left(*shift_offset));
                        }
                        (6, ShiftVariant::LogicalRight) => {
                            shift_underliers!([B64; 2], |x: &B64| x.val() >> shift_offset);
                        }
                        (6, ShiftVariant::LogicalLeft) => {
                            shift_underliers!([B64; 2], |x: &B64| x.val() << shift_offset);
                        }
                        (6, ShiftVariant::CircularLeft) => {
                            shift_underliers!([B64; 2], |x: &B64| x
                                .val()
                                .rotate_left(*shift_offset));
                        }
                        (7, ShiftVariant::LogicalRight) => {
                            shift_underliers!([B128; 1], |x: &B128| x.val() >> shift_offset);
                        }
                        (7, ShiftVariant::LogicalLeft) => {
                            shift_underliers!([B128; 1], |x: &B128| x.val() << shift_offset);
                        }
                        (7, ShiftVariant::CircularLeft) => {
                            shift_underliers!([B128; 1], |x: &B128| x
                                .val()
                                .rotate_left(*shift_offset));
                        }
                        _ => unimplemented!(),
                    };

                    let entry_id = self.new_entry();
                    self.entries[entry_id] = underliers;
                    (entry_id, tower_level)
                }

                OracleKind::Projected {
                    inner,
                    selection,
                    chunk_size,
                    ..
                } => {
                    let tower_level = oracle_info.tower_level;
                    let &(inner_entry_id, _) =
                        self.entry_map.get(inner).expect("Data should be available");

                    macro_rules! project_underliers {
                        ($d:literal, $ty:ident, $uty:ident, $unpack:expr, $pack:expr) => {{
                            const DIVISOR: usize = $d;

                            let chunk_size = *chunk_size;
                            let selection_usize = usize::try_from(*selection)?;

                            // Compute total number of elements
                            let num_elts = self.entries[inner_entry_id].len() * DIVISOR;
                            let num_chunks = num_elts.div_ceil(chunk_size);

                            let unpacked_data = self.entries[inner_entry_id]
                                .par_iter()
                                .flat_map($unpack)
                                .collect::<Vec<_>>();

                            let num_projections = (1 << tower_level) * num_chunks;
                            if num_projections >= 128 {
                                // An `OptimalUnderlier` won't exceed the expected amount of data

                                // Pre-allocate the projected field elements
                                let mut projected_field_elements = Vec::with_capacity(num_chunks);

                                unpacked_data
                                    .par_chunks_exact(chunk_size)
                                    .map(|chunk| chunk[selection_usize])
                                    .collect_into_vec(&mut projected_field_elements);

                                // Pad to multiple of DIVISOR
                                #[allow(clippy::modulo_one)]
                                let pad_len = projected_field_elements.len() % DIVISOR;
                                if pad_len != 0 {
                                    projected_field_elements
                                        .extend(repeat($ty::ZERO).take(DIVISOR - pad_len));
                                }

                                // Compose underliers in parallel
                                let underliers = projected_field_elements
                                    .par_chunks_exact(DIVISOR)
                                    .map(|chunk| $pack(chunk.try_into().unwrap()))
                                    .collect();
                                (underliers, tower_level)
                            } else {
                                // We need to fill an `OptimalUnderlier` with sparse data
                                let shift_size = 128 / num_projections;
                                let new_tower_level = log2_strict_usize(shift_size);
                                let mut u = 0u128;

                                #[allow(trivial_numeric_casts)]
                                for (chunk_idx, chunk) in
                                    unpacked_data.chunks_exact(chunk_size).enumerate()
                                {
                                    let uty =
                                        unsafe { transmute::<$ty, $uty>(chunk[selection_usize]) };
                                    u |= (uty as u128) << (chunk_idx * shift_size);
                                }
                                (vec![OptimalUnderlier::from(u)], new_tower_level)
                            }
                        }};
                    }

                    let (projected_underliers, new_tower_level) = match tower_level {
                        0 => project_underliers!(
                            128,
                            B1,
                            u8,
                            |u| {
                                let u = unsafe { transmute::<OptimalUnderlier, u128>(*u) };
                                let mut arr = [B1::ZERO; 128];
                                for (i, b) in arr.iter_mut().enumerate() {
                                    if (u >> i) & 1 == 1 {
                                        *b = B1::ONE;
                                    }
                                }
                                arr
                            },
                            |a: [B1; 128]| {
                                let mut u = 0;
                                for (i, b) in a.into_iter().enumerate() {
                                    if b == B1::ONE {
                                        u |= 1 << i;
                                    }
                                }
                                unsafe { transmute::<u128, OptimalUnderlier>(u) }
                            }
                        ),
                        3 => project_underliers!(
                            16,
                            B8,
                            u8,
                            |u| unsafe { transmute::<OptimalUnderlier, [B8; 16]>(*u) },
                            |a| unsafe { transmute::<[B8; 16], OptimalUnderlier>(a) }
                        ),
                        4 => project_underliers!(
                            8,
                            B16,
                            u16,
                            |u| unsafe { transmute::<OptimalUnderlier, [B16; 8]>(*u) },
                            |a| unsafe { transmute::<[B16; 8], OptimalUnderlier>(a) }
                        ),
                        5 => project_underliers!(
                            4,
                            B32,
                            u32,
                            |u| unsafe { transmute::<OptimalUnderlier, [B32; 4]>(*u) },
                            |a| unsafe { transmute::<[B32; 4], OptimalUnderlier>(a) }
                        ),
                        6 => project_underliers!(
                            2,
                            B64,
                            u64,
                            |u| unsafe { transmute::<OptimalUnderlier, [B64; 2]>(*u) },
                            |a| unsafe { transmute::<[B64; 2], OptimalUnderlier>(a) }
                        ),
                        7 => project_underliers!(
                            1,
                            B128,
                            u128,
                            |u| unsafe { transmute::<OptimalUnderlier, [B128; 1]>(*u) },
                            |a| unsafe { transmute::<[B128; 1], OptimalUnderlier>(a) }
                        ),
                        _ => unimplemented!(),
                    };

                    let entry_id = self.new_entry();
                    self.entries[entry_id] = projected_underliers;
                    (entry_id, new_tower_level)
                }
            };

            self.entry_map.insert(oracle_idx, oracle_entry);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use binius_core::oracle::ShiftVariant;
    use binius_field::{
        BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
        BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64,
        BinaryField128b as B128, Field, arch::OptimalUnderlier, underlier::UnderlierType,
    };
    use binius_utils::checked_arithmetics::log2_ceil_usize;
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    use crate::archon::{
        ModuleMode, RelativeHeight,
        arith_expr::ArithExpr,
        circuit::{CircuitModule, init_witness_modules},
        protocol::validate_witness,
        transparent::Transparent,
        witness::compile_witness_modules,
    };

    fn f(u128: u128) -> B128 {
        B128::new(u128)
    }

    const DEPTHS: [usize; 15] = [1, 2, 3, 5, 14, 30, 60, 65, 66, 128, 200, 256, 400, 512, 600];

    #[test]
    fn test_populate_constant() {
        let mut circuit_module = CircuitModule::new(0);
        macro_rules! constant_for {
            ($t:ident) => {
                Transparent::Constant(f(($t::MAX - $t::MAX / 3) as u128))
            };
        }
        circuit_module
            .add_transparent("b1_0", Transparent::Constant(f(0)), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b1_1", Transparent::Constant(f(1)), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b2", Transparent::Constant(f(2)), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b4", Transparent::Constant(f(9)), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b8", constant_for!(u8), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b16", constant_for!(u16), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b32", constant_for!(u32), RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_transparent("b64", constant_for!(u64), RelativeHeight::Base)
            .unwrap();
        #[allow(trivial_numeric_casts)]
        circuit_module
            .add_transparent("b128", constant_for!(u128), RelativeHeight::Base)
            .unwrap();

        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let test_with_depth = |depth| {
            let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
            let log_height = log2_ceil_usize(depth).try_into().unwrap();
            let depth = depth as u64;
            let mode = ModuleMode::active(log_height, depth);
            witness_modules[0].populate(mode).unwrap();
            assert!(!witness_modules[0].entry_map.is_empty());
            let witness = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
            assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
        };

        DEPTHS.into_par_iter().for_each(test_with_depth);
    }

    #[test]
    fn test_populate_incremental() {
        let mut circuit_module = CircuitModule::new(0);
        circuit_module
            .add_transparent("incr", Transparent::Incremental, RelativeHeight::Base)
            .unwrap();
        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let test_with_depth = |depth| {
            let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
            let log_height = log2_ceil_usize(depth).try_into().unwrap();
            let depth = depth as u64;
            let mode = ModuleMode::active(log_height, depth);
            witness_modules[0].populate(mode).unwrap();
            assert!(!witness_modules[0].entry_map.is_empty());
            let witness = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
            assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
        };

        DEPTHS.into_par_iter().for_each(test_with_depth);
    }

    #[test]
    fn test_populate_linear_combination() {
        let mut circuit_module = CircuitModule::new(0);
        let b1 = circuit_module
            .add_committed::<B1>("b1", RelativeHeight::Base)
            .unwrap();
        let b2 = circuit_module
            .add_committed::<B2>("b2", RelativeHeight::Base)
            .unwrap();
        let b4 = circuit_module
            .add_committed::<B4>("b4", RelativeHeight::Base)
            .unwrap();
        let b8 = circuit_module
            .add_committed::<B8>("b8", RelativeHeight::Base)
            .unwrap();
        let b16 = circuit_module
            .add_committed::<B16>("b16", RelativeHeight::Base)
            .unwrap();
        let b32 = circuit_module
            .add_committed::<B32>("b32", RelativeHeight::Base)
            .unwrap();
        let b64 = circuit_module
            .add_committed::<B64>("b64", RelativeHeight::Base)
            .unwrap();
        let b128 = circuit_module
            .add_committed::<B128>("b128", RelativeHeight::Base)
            .unwrap();

        circuit_module
            .add_linear_combination(
                "lcb128",
                f(3),
                [
                    (b1, f(3)),
                    (b2, f(4)),
                    (b4, f(5)),
                    (b8, f(6)),
                    (b16, f(7)),
                    (b32, f(8)),
                    (b64, f(9)),
                    (b128, f(10)),
                ],
                RelativeHeight::Base,
            )
            .unwrap();

        circuit_module
            .add_linear_combination(
                "lcb64",
                f(907898),
                [
                    (b1, f(500)),
                    (b2, f(2000)),
                    (b4, f(5)),
                    (b8, f(4)),
                    (b16, f(7)),
                    (b32, f(8)),
                    (b64, f(9879)),
                ],
                RelativeHeight::Base,
            )
            .unwrap();

        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();

        let mut oracles = [b1, b2, b4, b8, b16, b32, b64, b128];
        oracles.sort_by_key(|x| ((x.val() + 3) * (x.val() + 5)) % 7);
        for (i, oracle_id) in oracles.into_iter().enumerate() {
            let entry_id = witness_modules[0].new_entry();
            for j in 0..1u128 << i {
                witness_modules[0].push_u128s_to([j * j + 17], entry_id);
            }
            match i {
                0 => witness_modules[0].bind_oracle_to::<B1>(oracle_id, entry_id),
                1 => witness_modules[0].bind_oracle_to::<B2>(oracle_id, entry_id),
                2 => witness_modules[0].bind_oracle_to::<B4>(oracle_id, entry_id),
                3 => witness_modules[0].bind_oracle_to::<B8>(oracle_id, entry_id),
                4 => witness_modules[0].bind_oracle_to::<B16>(oracle_id, entry_id),
                5 => witness_modules[0].bind_oracle_to::<B32>(oracle_id, entry_id),
                6 => witness_modules[0].bind_oracle_to::<B64>(oracle_id, entry_id),
                7 => witness_modules[0].bind_oracle_to::<B128>(oracle_id, entry_id),
                _ => unreachable!(),
            }
        }
        let mode = ModuleMode::active(7, 0);
        witness_modules[0].populate(mode).unwrap();
        assert!(!witness_modules[0].entry_map.is_empty());
        let witness = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok())
    }

    #[test]
    fn test_populate_linear_combination_b1() {
        let mut circuit_module = CircuitModule::new(0);
        let a = circuit_module
            .add_committed::<B1>("a", RelativeHeight::Base)
            .unwrap();
        let b = circuit_module
            .add_committed::<B1>("b", RelativeHeight::Base)
            .unwrap();
        let c = circuit_module
            .add_committed::<B1>("c", RelativeHeight::Base)
            .unwrap();

        circuit_module
            .add_linear_combination("lc1", B128::ZERO, [], RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_linear_combination("lc2", B128::ONE, [], RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_linear_combination("lc3", B128::ZERO, [(a, B128::ONE)], RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_linear_combination("lc4", B128::ONE, [(b, B128::ONE)], RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_linear_combination(
                "lc5",
                B128::ZERO,
                [(a, B128::ONE), (b, B128::ONE)],
                RelativeHeight::Base,
            )
            .unwrap();
        circuit_module
            .add_linear_combination(
                "lc6",
                B128::ONE,
                [(a, B128::ONE), (b, B128::ONE)],
                RelativeHeight::Base,
            )
            .unwrap();
        circuit_module
            .add_linear_combination(
                "lc7",
                B128::ZERO,
                [(a, B128::ONE), (b, B128::ONE), (c, B128::ONE)],
                RelativeHeight::Base,
            )
            .unwrap();
        circuit_module
            .add_linear_combination(
                "lc8",
                B128::ONE,
                [(a, B128::ONE), (b, B128::ONE), (c, B128::ONE)],
                RelativeHeight::Base,
            )
            .unwrap();

        circuit_module.freeze_oracles();
        let mut witness_module = circuit_module.init_witness_module().unwrap();

        let entry_a = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128s_to([u128::MAX - u128::MAX / 2 + u128::MAX / 4], entry_a);
        witness_module.bind_oracle_to::<B1>(a, entry_a);

        let entry_b = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128s_to([u128::MAX - u128::MAX / 3 + u128::MAX / 7], entry_b);
        witness_module.bind_oracle_to::<B1>(b, entry_b);

        let entry_c = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128s_to([u128::MAX - u128::MAX / 5 + u128::MAX / 11], entry_c);
        witness_module.bind_oracle_to::<B1>(c, entry_c);

        let mode = ModuleMode::active(7, 0);
        witness_module.populate(mode).unwrap();

        let witness_modules = [witness_module];
        let witness = compile_witness_modules(&witness_modules, vec![mode]).unwrap();

        let circuit_modules = [circuit_module];
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok())
    }

    #[test]
    fn test_packed() {
        let mut circuit_module = CircuitModule::new(0);
        let input = circuit_module
            .add_committed::<B1>("input", RelativeHeight::Base)
            .unwrap();
        for log_degree in 0..=7 {
            circuit_module
                .add_packed(&format!("packed-{input}-{log_degree}"), input, log_degree)
                .unwrap();
        }
        circuit_module.freeze_oracles();

        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let entry_id = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128s_to([u128::MAX - u128::MAX / 2 + u128::MAX / 4], entry_id);
        witness_module.bind_oracle_to::<B1>(input, entry_id);
        let mode = ModuleMode::active(7, 0);
        witness_module.populate(mode).unwrap();

        let witness_modules = [witness_module];
        let witness = compile_witness_modules(&witness_modules, vec![mode]).unwrap();

        let circuit_modules = [circuit_module];
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok())
    }

    #[test]
    fn test_xor_via_linear_combination() {
        let log_height = 3;
        let mode = ModuleMode::active(log_height, 0);
        let mut circuit_module = CircuitModule::new(0);
        let a = circuit_module
            .add_committed::<B32>("a", RelativeHeight::Base)
            .unwrap();
        let b = circuit_module
            .add_committed::<B32>("b", RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_linear_combination(
                "lc",
                f(0),
                [(a, B128::ONE), (b, B128::ONE)],
                RelativeHeight::Base,
            )
            .unwrap();
        circuit_module.freeze_oracles();

        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let a_id = witness_module.new_entry();
        let b_id = witness_module.new_entry();

        let height = 1 << log_height;
        // we use U32 field for 'a' and 'b' columns, so divide height by 4 (4 u32 in 1 u128)
        for _ in 0..height / 4 {
            witness_module.push_u32s_to([0x0000bbbb, 0x0000bbbb, 0x0000bbbb, 0x0000bbbb], a_id);
            witness_module.push_u32s_to([0xaaaa0000, 0xaaaa0000, 0xaaaa0000, 0xaaaa0000], b_id);
        }

        witness_module.bind_oracle_to::<B32>(a, a_id);
        witness_module.bind_oracle_to::<B32>(b, b_id);
        witness_module.populate(mode).unwrap();

        let witness_modules = [witness_module];
        let circuit_modules = [circuit_module];
        let witness_archon = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok());
    }

    #[test]
    fn test_packed_b8_b32() {
        let mode = ModuleMode::active(4, 0);
        let packed_log_degree = 2usize;

        let mut circuit_module = CircuitModule::new(0);
        let input = circuit_module
            .add_committed::<B8>("input", RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_packed(
                &format!("packed-{input}-{packed_log_degree}"),
                input,
                packed_log_degree,
            )
            .unwrap();
        circuit_module.freeze_oracles();
        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let entry_id = witness_module.new_entry();
        witness_module.push_u8s_to(
            [
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff,
            ],
            entry_id,
        );
        witness_module.bind_oracle_to::<B8>(input, entry_id);

        witness_module.populate(mode).unwrap();
        let witness_modules = [witness_module];
        let witness_archon = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
        let circuit_modules = [circuit_module];

        assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok());
    }

    #[test]
    fn test_shifted() {
        fn test_inner(
            input_value: u8,
            shift_offset: u32,
            block_bits: usize,
            optimal_underliers_num: usize,
            variant: ShiftVariant,
        ) {
            let log_height = (OptimalUnderlier::LOG_BITS + optimal_underliers_num)
                .try_into()
                .unwrap();
            let mode = ModuleMode::active(log_height, 0);
            let height = 1usize << log_height;
            let mut circuit_module = CircuitModule::new(0);
            let input = circuit_module
                .add_committed::<B1>("input", RelativeHeight::Base)
                .unwrap();
            circuit_module
                .add_shifted("shifted", input, shift_offset, block_bits, variant)
                .unwrap();

            circuit_module.freeze_oracles();

            let mut witness_module = circuit_module.init_witness_module().unwrap();
            let entry_id = witness_module.new_entry();
            let input_values = [input_value; 16];

            for _ in 0..height / OptimalUnderlier::BITS {
                witness_module.push_u8s_to(input_values, entry_id);
            }

            witness_module.bind_oracle_to::<B1>(input, entry_id);

            witness_module.populate(mode).unwrap();

            let witness_modules = [witness_module];
            let circuit_modules = [circuit_module];
            let witness_archon = compile_witness_modules(&witness_modules, vec![mode]).unwrap();

            assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok())
        }

        let input_value = 0b10000000u8;
        let shift_offset = 7;
        let block_bits = 3usize; // we consider input column storing data as bytes
        let optimal_underliers_num_powered = 3;

        test_inner(
            input_value,
            shift_offset,
            block_bits,
            optimal_underliers_num_powered,
            ShiftVariant::LogicalRight,
        );

        let input_value = 0b11100011u8;
        let shift_offset = 1;
        let block_bits = 5usize; // we consider input column storing data as u32s
        let optimal_underliers_num_powered = 7;

        test_inner(
            input_value,
            shift_offset,
            block_bits,
            optimal_underliers_num_powered,
            ShiftVariant::LogicalRight,
        );

        let input_value = 0b10000000u8;
        let shift_offset = 5;
        let block_bits = 3usize; // we consider input column storing data as bytes
        let optimal_underliers_num_powered = 8;

        test_inner(
            input_value,
            shift_offset,
            block_bits,
            optimal_underliers_num_powered,
            ShiftVariant::LogicalLeft,
        );

        // this test case is important for Blake3 compression
        let input_value = 0b10100111u8;
        let shift_offset = 1;
        let block_bits = 5usize; // we consider input column storing data as u32s
        let optimal_underliers_num_powered = 12;

        test_inner(
            input_value,
            shift_offset,
            block_bits,
            optimal_underliers_num_powered,
            ShiftVariant::LogicalLeft,
        );

        // this test case is important for Blake3 compression
        let input_value = 0b11011010u8;
        let shift_offset = 16;
        let block_bits = 5usize; // we consider input column storing data as u32s
        let optimal_underliers_num_powered = 10;

        test_inner(
            input_value,
            shift_offset,
            block_bits,
            optimal_underliers_num_powered,
            ShiftVariant::CircularLeft,
        );
    }

    #[test]
    fn test_projected() {
        let mut circuit_module = CircuitModule::new(0);
        let b1 = circuit_module
            .add_committed::<B1>("b1", RelativeHeight::Base)
            .unwrap();
        let b8 = circuit_module
            .add_committed::<B8>("b8", RelativeHeight::Base)
            .unwrap();
        let b16 = circuit_module
            .add_committed::<B16>("b16", RelativeHeight::Base)
            .unwrap();
        let b32 = circuit_module
            .add_committed::<B32>("b32", RelativeHeight::Base)
            .unwrap();
        let b64 = circuit_module
            .add_committed::<B64>("b64", RelativeHeight::Base)
            .unwrap();
        let b128 = circuit_module
            .add_committed::<B128>("b128", RelativeHeight::Base)
            .unwrap();

        circuit_module.add_projected("p1_1", b1, 27, 32).unwrap();
        circuit_module.add_projected("p1_2", b1, 63, 64).unwrap();
        circuit_module.add_projected("p1_3", b1, 87, 128).unwrap();
        circuit_module.add_projected("p1_4", b1, 151, 256).unwrap();
        circuit_module.add_projected("p8_1", b8, 3, 4).unwrap();
        circuit_module.add_projected("p8_2", b8, 3, 8).unwrap();
        circuit_module.add_projected("p8_2", b8, 15, 16).unwrap();
        circuit_module.add_projected("p16", b16, 5, 16).unwrap();
        circuit_module.add_projected("p32", b32, 7, 8).unwrap();
        circuit_module.add_projected("p64_1", b64, 3, 4).unwrap();
        circuit_module
            .add_projected("p64_2", b64, 101, 128)
            .unwrap();
        circuit_module.add_projected("p128", b128, 11, 16).unwrap();
        circuit_module.freeze_oracles();

        let mut witness_module = circuit_module.init_witness_module().unwrap();

        let b1_entry = witness_module.new_entry();
        let b1_data: [u8; 32] = rand::random(); // 256 bits
        witness_module.push_u8s_to(b1_data, b1_entry);
        witness_module.bind_oracle_to::<B1>(b1, b1_entry);

        let b8_entry = witness_module.new_entry();
        let b8_data: [u8; 256] = rand::random();
        witness_module.push_u8s_to(b8_data, b8_entry);
        witness_module.bind_oracle_to::<B8>(b8, b8_entry);

        let b16_entry = witness_module.new_entry();
        let b16_data: [u16; 256] = rand::random();
        witness_module.push_u16s_to(b16_data, b16_entry);
        witness_module.bind_oracle_to::<B16>(b16, b16_entry);

        let b32_entry = witness_module.new_entry();
        let b32_data: [u32; 256] = rand::random();
        witness_module.push_u32s_to(b32_data, b32_entry);
        witness_module.bind_oracle_to::<B32>(b32, b32_entry);

        let b64_entry = witness_module.new_entry();
        let b64_data: [u64; 256] = rand::random();
        witness_module.push_u64s_to(b64_data, b64_entry);
        witness_module.bind_oracle_to::<B64>(b64, b64_entry);

        let b128_entry = witness_module.new_entry();
        let b128_data: [u128; 256] = rand::random();
        witness_module.push_u128s_to(b128_data, b128_entry);
        witness_module.bind_oracle_to::<B128>(b128, b128_entry);

        let mode = ModuleMode::active(8, 0);
        witness_module.populate(mode).unwrap();

        let witness_modules = [witness_module];
        let witness_archon = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
        let circuit_modules = [circuit_module];

        assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok());
    }

    #[test]
    fn test_projected_u32() {
        let log_height = 6;
        let mode = ModuleMode::active(log_height, 0);
        let selection = 0u64; // we have long input and every "selected" item is taken into projection

        let height = 1 << log_height;
        let chunk_size = height / 4;

        let mut circuit_module = CircuitModule::new(0);
        let input = circuit_module
            .add_committed::<B32>("input", RelativeHeight::Base)
            .unwrap();
        circuit_module
            .add_projected(
                &format!("projected-{input}"),
                input,
                selection,
                chunk_size.try_into().unwrap(),
            )
            .unwrap();
        circuit_module.freeze_oracles();

        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let entry_id = witness_module.new_entry();

        // let's use 'push_u32s_to' for populating
        for _ in 0..chunk_size {
            let push: [u32; 4] = rand::random();
            witness_module.push_u32s_to(push, entry_id);
        }

        witness_module.bind_oracle_to::<B32>(input, entry_id);
        witness_module.populate(mode).unwrap();

        let witness_modules = [witness_module];
        let witness_archon = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
        let circuit_modules = [circuit_module];

        assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok());
    }

    #[test]
    fn test_autocomplete() {
        let mut circuit_module = CircuitModule::new(0);
        let x = circuit_module
            .add_committed::<B8>("b8", RelativeHeight::Base)
            .unwrap();
        let y = circuit_module
            .add_committed::<B8>("b8", RelativeHeight::Base)
            .unwrap();
        use ArithExpr::*;
        circuit_module.assert_zero("x = y", [], Oracle(x) + Oracle(y));
        circuit_module.freeze_oracles();

        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let entry_id = witness_module.new_entry();
        witness_module.push_u8s_to([42], entry_id); // This wouldn't be enough
        witness_module.bind_oracle_to::<B8>(x, entry_id);
        witness_module.bind_oracle_to::<B8>(y, entry_id);

        let mode = ModuleMode::active(4, 0);
        witness_module.populate(mode).unwrap();

        let witness_modules = [witness_module];
        let witness_archon = compile_witness_modules(&witness_modules, vec![mode]).unwrap();
        let circuit_modules = [circuit_module];

        assert!(validate_witness(&circuit_modules, &[], &witness_archon).is_ok());
    }
}
