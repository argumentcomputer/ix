use anyhow::{Context, Result, bail, ensure};
use binius_core::{oracle::OracleId, witness::MultilinearExtensionIndex};
use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    TowerField,
    arch::OptimalUnderlier,
    as_packed_field::PackedType,
    underlier::{UnderlierType, UnderlierWithBitOps, WithUnderlier},
};
use binius_math::MultilinearExtension;
use indexmap::IndexSet;
use rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
    },
    slice::ParallelSliceMut,
};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{
    collections::{HashMap, hash_map::Entry},
    mem::transmute,
    sync::Arc,
};

use super::{
    ModuleId, OracleInfo, OracleKind,
    transparent::{Incremental, Transparent, replicate_within_u128},
};

pub type EntryId = usize;

pub struct WitnessModule {
    module_id: ModuleId,
    oracles: Arc<Vec<OracleInfo>>,
    entries: Vec<Vec<OptimalUnderlier>>,
    /// Maps oracles to their entries and tower levels
    entry_map: FxHashMap<OracleId, (EntryId, usize)>,
}

pub struct Witness<'a> {
    pub(crate) mlei: MultilinearExtensionIndex<'a, OptimalUnderlier, B128>,
    /// The heights for each module. `0` means that the circuit module is
    /// deactivated and must be skipped during compilation.
    pub(crate) modules_heights: Vec<u64>,
}

#[inline]
pub fn populate_witness_modules(
    modules: &mut [WitnessModule],
    modules_heights: Vec<u64>,
) -> Result<()> {
    ensure!(
        modules.len() == modules_heights.len(),
        "Incompatible numbers of modules and heights"
    );
    modules
        .par_iter_mut()
        .zip(modules_heights)
        .try_for_each(|(module, height)| module.populate(height))
}

pub fn compile_witness_modules(
    modules: &[WitnessModule],
    heights: Vec<u64>,
) -> Result<Witness<'_>> {
    ensure!(modules.len() == heights.len());
    let mut witness = Witness::with_capacity(modules.len());
    let mut oracle_offset = 0;
    for (module_idx, (module, height)) in modules.iter().zip(heights).enumerate() {
        ensure!(
            module_idx == module.module_id,
            "Wrong compilation order. Expected module {module_idx}, but got {}.",
            module.module_id
        );
        if height == 0 {
            // Deactivate module.
            witness.modules_heights.push(0);
            continue;
        }
        let oracles_data_results = (0..module.num_oracles())
            .into_par_iter()
            .map(|oracle_id| {
                let Some(&(entry_id, tower_level)) = module.entry_map.get(&oracle_id) else {
                    bail!("Entry not found for oracle {oracle_id}, module {module_idx}.");
                };
                let entry = &module.entries[entry_id];
                let expected_num_underliers = WitnessModule::num_underliers_for_height(height, tower_level)?;
                let got_num_underliers = entry.len();
                ensure!(
                    got_num_underliers == expected_num_underliers,
                    [
                        format!(
                            "Wrong number of underliers for entry {entry_id}, bound to oracle {oracle_id}, module {module_idx}.\n"
                        ),
                        format!(
                            "Expected {expected_num_underliers} but got {got_num_underliers}."
                        )
                    ].concat()
                );
                macro_rules! oracle_poly {
                    ($bf:ident) => {{
                        let values =
                            PackedType::<OptimalUnderlier, $bf>::from_underliers_ref(entry);
                        let mle = MultilinearExtension::from_values_generic(values)
                            .context(format!(
                                "MLE instantiation for entry {entry_id}, oracle {oracle_id}, module {module_idx}"
                            ))?
                            .specialize_arc_dyn();
                        Ok(((oracle_offset + oracle_id, mle), height))
                    }};
                }
                match tower_level {
                    0 => oracle_poly!(B1),
                    1 => oracle_poly!(B2),
                    2 => oracle_poly!(B4),
                    3 => oracle_poly!(B8),
                    4 => oracle_poly!(B16),
                    5 => oracle_poly!(B32),
                    6 => oracle_poly!(B64),
                    7 => oracle_poly!(B128),
                    _ => bail!(
                        "Unsupported tower level {tower_level} for oracle {oracle_id}, module {module_idx}"
                    ),
                }
            })
            .collect::<Vec<_>>();
        let mut oracle_poly_vec = Vec::with_capacity(oracles_data_results.len());
        let mut height_opt = None;
        for oracle_data_result in oracles_data_results {
            let (oracle_poly, oracle_height) = oracle_data_result?;
            match height_opt {
                Some(known_height) => ensure!(
                    oracle_height == known_height,
                    "Witness for module {module_idx} has incompatible heights: {oracle_height} != {known_height}"
                ),
                None => height_opt = Some(oracle_height),
            }
            oracle_poly_vec.push(oracle_poly);
        }
        let height = height_opt.unwrap_or(0); // Deactivate module without oracles
        witness.mlei.update_multilin_poly(oracle_poly_vec)?;
        witness.modules_heights.push(height);
        oracle_offset += module.num_oracles();
    }
    Ok(witness)
}

impl WitnessModule {
    #[inline]
    pub fn new_entry(&mut self) -> EntryId {
        self.entries.push(vec![]);
        self.entries.len() - 1
    }

    #[inline]
    pub fn new_entry_with_capacity(&mut self, log_bits: u8) -> EntryId {
        let num_underliers = (1 << log_bits) / OptimalUnderlier::BITS;
        self.entries.push(Vec::with_capacity(num_underliers));
        self.entries.len() - 1
    }

    #[inline]
    pub fn bind_oracle_to<FS: TowerField>(&mut self, oracle_id: OracleId, entry_id: EntryId) {
        self.entry_map
            .insert(oracle_id, (entry_id, FS::TOWER_LEVEL));
    }

    #[inline]
    pub fn push_u8s_to(&mut self, u8s: [u8; 16], entry_id: EntryId) {
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128::from_le_bytes(u8s)))
    }

    #[inline]
    pub fn push_u16s_to(&mut self, u16s: [u16; 8], entry_id: EntryId) {
        let u128 = unsafe { transmute::<[u16; 8], u128>(u16s) };
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    #[inline]
    pub fn push_u32s_to(&mut self, u32s: [u32; 4], entry_id: EntryId) {
        let u128 = unsafe { transmute::<[u32; 4], u128>(u32s) };
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    #[inline]
    pub fn push_u64s_to(&mut self, u64s: [u64; 2], entry_id: EntryId) {
        let u128 = unsafe { transmute::<[u64; 2], u128>(u64s) };
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    #[inline]
    pub fn push_u128_to(&mut self, u128: u128, entry_id: EntryId) {
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    /// Populates a witness module with data to reach a given height.
    /// # Errors
    /// This function errors if a prepopulated oracle doesn't have this same height.
    pub fn populate(&mut self, height: u64) -> Result<()> {
        let ensure_height = |entry_id: usize, tower_level| -> Result<()> {
            let expected_num_underliers = Self::num_underliers_for_height(height, tower_level)?;
            let got_num_underliers = self.entries[entry_id].len();
            ensure!(
                expected_num_underliers == got_num_underliers,
                format!(
                    "Expected length {expected_num_underliers} for entry {entry_id} on module {}. Got {got_num_underliers}.",
                    self.module_id,
                ),
            );
            Ok(())
        };

        // "Root oracles" are those which aren't committed and aren't dependencies
        // of any other oracle. `root_oracles` starts with all oracles, which are
        // removed as the following loop finds out they break such condition.
        //
        // The loop also uses `ensure_height` to make sure that prepopulated
        // oracles have the right amount of data.
        let mut root_oracles: FxHashSet<_> = (0..self.num_oracles()).collect();
        for (oracle_id, oracle_info) in self.oracles.iter().enumerate() {
            let mut is_committed = false;
            match &oracle_info.kind {
                OracleKind::Committed => {
                    root_oracles.remove(&oracle_id);
                    is_committed = true;
                }
                OracleKind::LinearCombination { offset: _, inner } => {
                    for (inner_oracle_id, _) in inner {
                        root_oracles.remove(inner_oracle_id);
                    }
                }
                OracleKind::Transparent(_) | OracleKind::StepDown => (),
            }

            if is_committed {
                let Some(&(entry_id, tower_level)) = self.entry_map.get(&oracle_id) else {
                    bail!(
                        "Committed oracle {} (id={oracle_id}) for witness module {} is not populated",
                        &oracle_info.name,
                        &self.module_id,
                    );
                };
                ensure_height(entry_id, tower_level)?;
            } else if let Some(&(entry_id, tower_level)) = self.entry_map.get(&oracle_id) {
                ensure_height(entry_id, tower_level)?;
            }
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
        while let Some(oracle_id) = to_visit_stack.pop() {
            let mut is_committed = false;
            match &self.oracles[oracle_id].kind {
                OracleKind::Committed => is_committed = true,
                OracleKind::LinearCombination { inner, .. } => {
                    for (inner_oracle_id, _) in inner {
                        stack_to_visit!(inner_oracle_id);
                    }
                }
                OracleKind::Transparent(_) | OracleKind::StepDown => (),
            }
            if !is_committed {
                compute_order.insert(oracle_id);
            }
        }

        // And now we're finally able to populate the witness, following the
        // correct compute order and making the assumption that dependency oracles
        // were already populated.
        while let Some(oracle_id) = compute_order.pop() {
            if self.entry_map.contains_key(&oracle_id) {
                // Already populated. Skip.
                continue;
            }
            let oracle_info = &self.oracles[oracle_id];
            let oracle_witness_data = match &oracle_info.kind {
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

                    // The number of underliers for the target oracle and also for the dependencies
                    let entry_len = Self::num_underliers_for_height(height, tower_level)?;

                    // Expand an underlier into multiple underliers, extracting binary field elements
                    // data for upcasts into the tower level of the target oracle
                    let expand = |u, tower_diff| {
                        assert_ne!(tower_diff, 0);
                        let u128 = unsafe { transmute::<OptimalUnderlier, u128>(u) };
                        let tower_diff_pow = 1usize << tower_diff;
                        let step = 128 / tower_diff_pow;
                        let mask = (1u128 << step) - 1;
                        (0..tower_diff_pow)
                            .map(|i| OptimalUnderlier::from_u128((u128 >> (i * step)) & mask))
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
                        0..=2 => todo!(),
                        3 => underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                            let offset: B8 =
                                (*offset).try_into().expect("Wrong minimal tower level");
                            #[rustfmt::skip]
                            let res = inner_data.iter().fold(
                                [offset; 16],
                                |[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15],
                                 (inner_oracle_id, coeff, _, _)| {
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
                        }),
                        4 => underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                            let offset: B16 =
                                (*offset).try_into().expect("Wrong minimal tower level");
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
                        }),
                        5 => underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                            let offset: B32 =
                                (*offset).try_into().expect("Wrong minimal tower level");
                            let res = inner_data.iter().fold(
                                [offset; 4],
                                |[a0, a1, a2, a3], (inner_oracle_id, coeff, ..)| {
                                    let underlier = get_dep_underlier(inner_oracle_id, i);
                                    let [b0, b1, b2, b3] = unsafe {
                                        transmute::<OptimalUnderlier, [B32; 4]>(underlier)
                                    };
                                    let coeff: B32 =
                                        (**coeff).try_into().expect("Wrong minimal tower");
                                    [a0 + coeff * b0, a1 + coeff * b1, a2 + coeff * b2, a3 + coeff * b3]
                                },
                            );
                            *u = unsafe { transmute::<[B32; 4], OptimalUnderlier>(res) };
                        }),
                        6 => underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                            let offset: B64 =
                                (*offset).try_into().expect("Wrong minimal tower level");
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
                        }),
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

                    (underliers, tower_level)
                }
                OracleKind::Transparent(transparent) => match transparent {
                    Transparent::Constant(b) => {
                        let tower_level = oracle_info.tower_level;
                        let u = OptimalUnderlier::from_u128(replicate_within_u128(*b));
                        let num_underliers = Self::num_underliers_for_height(height, tower_level)?;
                        (vec![u; num_underliers], tower_level)
                    }
                    Transparent::Incremental => {
                        let tower_level = Incremental::min_tower_level(height);
                        let num_underliers = Self::num_underliers_for_height(height, tower_level)?;
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
                                    *u = unsafe { transmute::<[u8; 16], OptimalUnderlier>(data) };
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
                                    *u = unsafe { transmute::<[u16; 8], OptimalUnderlier>(data) };
                                });
                            }
                            5 => {
                                underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                    let i = (i % (u32::MAX as usize)).try_into().unwrap();
                                    let (start, _) = 4u32.overflowing_mul(i);
                                    let data = [start, start + 1, start + 2, start + 3];
                                    *u = unsafe { transmute::<[u32; 4], OptimalUnderlier>(data) };
                                });
                            }
                            6 => {
                                underliers.par_iter_mut().enumerate().for_each(|(i, u)| {
                                    let (start, _) = 2u64.overflowing_mul(i as u64);
                                    let data = [start, start + 1];
                                    *u = unsafe { transmute::<[u64; 2], OptimalUnderlier>(data) };
                                });
                            }
                            _ => unreachable!(),
                        };
                        (underliers, tower_level)
                    }
                },
                OracleKind::StepDown => {
                    let tower_level = oracle_info.tower_level;
                    assert_eq!(tower_level, 0);
                    let num_underliers = Self::num_underliers_for_height(height, tower_level)?;
                    // Start the underliers with a bunch of B1(1)s and then set the padding
                    // bits to zero if necessary.
                    let mut underliers =
                        vec![OptimalUnderlier::from_u128(u128::MAX); num_underliers];
                    let height_usize: usize = height.try_into()?;
                    let step_down_changes_at = height_usize / OptimalUnderlier::BITS;
                    if step_down_changes_at < num_underliers {
                        // Produce an `u128` with the `height_usize % OptimalUnderlier::BITS`
                        // least significant bits set to one and the rest set to zero.
                        let u128 = (1 << (height_usize % OptimalUnderlier::BITS)) - 1;
                        underliers[step_down_changes_at] = OptimalUnderlier::from_u128(u128);

                        // The next underliers must all be zeros.
                        underliers
                            .par_iter_mut()
                            .skip(step_down_changes_at + 1)
                            .for_each(|u| *u = OptimalUnderlier::from_u128(0));
                    }
                    (underliers, tower_level)
                }
            };

            let (underliers, tower_level) = oracle_witness_data;
            let entry_id = self.new_entry();
            self.entries[entry_id] = underliers;
            self.entry_map.insert(oracle_id, (entry_id, tower_level));
        }

        Ok(())
    }

    #[inline]
    pub(crate) fn new(module_id: ModuleId, oracles: Arc<Vec<OracleInfo>>) -> Self {
        let num_oracles = oracles.len();
        Self {
            module_id,
            oracles,
            entries: vec![],
            entry_map: HashMap::with_capacity_and_hasher(num_oracles, FxBuildHasher),
        }
    }

    /// Computes the number of `OptimalUnderlier`s needed to reach a certain
    /// height at a given tower level.
    fn num_underliers_for_height(height: u64, tower_level: usize) -> Result<usize> {
        let num_bits = height * (1 << tower_level);
        let num_underliers = num_bits.div_ceil(OptimalUnderlier::BITS as u64);
        let num_underliers_rounded = num_underliers.next_power_of_two();
        ensure!(num_underliers_rounded != 0, "Height overflow");
        let num_underliers_rounded_usize: usize = num_underliers_rounded
            .try_into()
            .context("Representing the number of underliers as an usize")?;
        Ok(num_underliers_rounded_usize)
    }

    fn num_oracles(&self) -> usize {
        self.oracles.len()
    }
}

impl Witness<'_> {
    #[inline]
    fn with_capacity(num_modules: usize) -> Self {
        Self {
            mlei: MultilinearExtensionIndex::new(),
            modules_heights: Vec::with_capacity(num_modules),
        }
    }
}

#[cfg(test)]
mod tests {
    use binius_field::{
        BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
        BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64,
        BinaryField128b as B128,
    };
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    use crate::archon::{
        circuit::{CircuitModule, init_witness_modules},
        protocol::validate_witness,
        transparent::Transparent,
        witness::compile_witness_modules,
    };

    fn f(u128: u128) -> B128 {
        B128::new(u128)
    }

    const HEIGHTS: [u64; 13] = [1, 2, 3, 4, 5, 65, 66, 128, 200, 256, 400, 512, 600];

    #[test]
    fn test_populate_constant() {
        let mut circuit_module = CircuitModule::new(0);
        macro_rules! constant_for {
            ($t:ident) => {
                Transparent::Constant(f(($t::MAX - $t::MAX / 3) as u128))
            };
        }
        circuit_module
            .add_transparent("b1_0", Transparent::Constant(f(0)))
            .unwrap();
        circuit_module
            .add_transparent("b1_1", Transparent::Constant(f(1)))
            .unwrap();
        circuit_module
            .add_transparent("b2", Transparent::Constant(f(2)))
            .unwrap();
        circuit_module
            .add_transparent("b4", Transparent::Constant(f(9)))
            .unwrap();
        circuit_module
            .add_transparent("b8", constant_for!(u8))
            .unwrap();
        circuit_module
            .add_transparent("b16", constant_for!(u16))
            .unwrap();
        circuit_module
            .add_transparent("b32", constant_for!(u32))
            .unwrap();
        circuit_module
            .add_transparent("b64", constant_for!(u64))
            .unwrap();
        #[allow(trivial_numeric_casts)]
        circuit_module
            .add_transparent("b128", constant_for!(u128))
            .unwrap();

        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let test_with_height = |height| {
            let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
            witness_modules[0].populate(height).unwrap();
            assert!(!witness_modules[0].entry_map.is_empty());
            let witness = compile_witness_modules(&witness_modules, vec![height]).unwrap();
            assert!(validate_witness(&circuit_modules, &witness, &[]).is_ok());
        };

        HEIGHTS.into_par_iter().for_each(test_with_height);
    }

    #[test]
    fn test_populate_incremental() {
        let mut circuit_module = CircuitModule::new(0);
        circuit_module
            .add_transparent("incr", Transparent::Incremental)
            .unwrap();
        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let test_with_height = |height| {
            let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
            witness_modules[0].populate(height).unwrap();
            assert!(!witness_modules[0].entry_map.is_empty());
            let witness = compile_witness_modules(&witness_modules, vec![height]).unwrap();
            assert!(validate_witness(&circuit_modules, &witness, &[]).is_ok());
        };

        HEIGHTS.into_par_iter().for_each(test_with_height);
    }

    #[test]
    fn test_populate_linear_combination() {
        let mut circuit_module = CircuitModule::new(0);
        let b1 = circuit_module.add_committed::<B1>("b1").unwrap();
        let b2 = circuit_module.add_committed::<B2>("b2").unwrap();
        let b4 = circuit_module.add_committed::<B4>("b4").unwrap();
        let b8 = circuit_module.add_committed::<B8>("b8").unwrap();
        let b16 = circuit_module.add_committed::<B16>("b16").unwrap();
        let b32 = circuit_module.add_committed::<B32>("b32").unwrap();
        let b64 = circuit_module.add_committed::<B64>("b64").unwrap();
        let b128 = circuit_module.add_committed::<B128>("b128").unwrap();

        circuit_module
            .add_linear_combination("lcb128", f(3), [
                (b1, f(3)),
                (b2, f(4)),
                (b4, f(5)),
                (b8, f(6)),
                (b16, f(7)),
                (b32, f(8)),
                (b64, f(9)),
                (b128, f(10)),
            ])
            .unwrap();

        circuit_module
            .add_linear_combination("lcb64", f(907898), [
                (b1, f(500)),
                (b2, f(2000)),
                (b4, f(5)),
                (b8, f(4)),
                (b16, f(7)),
                (b32, f(8)),
                (b64, f(9879)),
            ])
            .unwrap();

        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();

        let mut oracles = [b1, b2, b4, b8, b16, b32, b64, b128];
        oracles.sort_by_key(|x| ((x + 3) * (x + 5)) % 7);
        for (i, oracle_id) in oracles.into_iter().enumerate() {
            let entry_id = witness_modules[0].new_entry();
            for j in 0..1u128 << i {
                witness_modules[0].push_u128_to(j * j + 17, entry_id);
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
        let height = 128;
        witness_modules[0].populate(height).unwrap();
        assert!(!witness_modules[0].entry_map.is_empty());
        let witness = compile_witness_modules(&witness_modules, vec![height]).unwrap();
        assert!(validate_witness(&circuit_modules, &witness, &[]).is_ok())
    }
}
