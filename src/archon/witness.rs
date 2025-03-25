use anyhow::{Context, Result, bail, ensure};
use binius_core::{oracle::OracleId, witness::MultilinearExtensionIndex};
use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    arch::OptimalUnderlier,
    as_packed_field::PackedType,
    underlier::{UnderlierType, WithUnderlier},
};
use binius_math::MultilinearExtension;
use binius_utils::checked_arithmetics::log2_strict_usize;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::{collections::HashMap, sync::Arc};

use super::{ModuleId, OracleInfo};

pub type EntryId = usize;

pub struct WitnessModule {
    module_id: ModuleId,
    oracles: Arc<Vec<OracleInfo>>,
    entries: Vec<Vec<OptimalUnderlier>>,
    entry_map: FxHashMap<OracleId, EntryId>,
}

pub struct Witness<'a> {
    pub(crate) mlei: MultilinearExtensionIndex<'a, OptimalUnderlier, B128>,
    /// The sets of `n_vars` for each module. `None` means that the circuit
    /// module needs to be deactivated/skipped at compilation time.
    pub(crate) modules_n_vars: Vec<Option<Vec<usize>>>,
}

impl Witness<'_> {
    #[inline]
    fn with_capacity(num_modules: usize) -> Self {
        Self {
            mlei: MultilinearExtensionIndex::new(),
            modules_n_vars: Vec::with_capacity(num_modules),
        }
    }
}

pub fn compile_witness_modules(modules: &[WitnessModule]) -> Result<Witness<'_>> {
    let mut witness = Witness::with_capacity(modules.len());
    let mut oracle_offset = 0;
    for (module_idx, module) in modules.iter().enumerate() {
        ensure!(
            module_idx == module.module_id,
            "Wrong compilation order. Expected module {module_idx}, but got {}.",
            module.module_id
        );
        if module.entry_map.is_empty() {
            witness.modules_n_vars.push(None);
            continue;
        }
        let oracles_data = module
            .oracles
            .par_iter()
            .enumerate()
            .map(|(oracle_id, oracle_info)| {
                let OracleInfo { tower_level, .. } = oracle_info;
                let Some(entry_id) = module.entry_map.get(&oracle_id) else {
                    bail!("Entry not found for oracle {oracle_id}, module {module_idx}.");
                };
                let entry = &module.entries[*entry_id];
                ensure!(
                    entry.len().is_power_of_two(),
                    "Length of entry {entry_id}, bound to oracle {oracle_id}, module {module_idx}, is not a power of two."
                );
                let n_vars = log2_strict_usize(entry.len()) + OptimalUnderlier::LOG_BITS - tower_level;
                macro_rules! oracle_poly {
                    ($bf:ident) => {{
                        let values =
                            PackedType::<OptimalUnderlier, $bf>::from_underliers_ref(entry);
                        let mle = MultilinearExtension::from_values_generic(values)
                            .context(format!(
                                "MLE instantiation for entry {entry_id}, oracle {oracle_id}, module {module_idx}"
                            ))?
                            .specialize_arc_dyn();
                        Ok(((oracle_offset + oracle_id, mle), n_vars))
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
        let mut oracle_poly_vec = Vec::with_capacity(oracles_data.len());
        let mut n_vars_vec = Vec::with_capacity(oracles_data.len());
        for oracle_data_result in oracles_data {
            let (oracle_poly, n_vars) = oracle_data_result?;
            oracle_poly_vec.push(oracle_poly);
            n_vars_vec.push(n_vars);
        }
        witness.mlei.update_multilin_poly(oracle_poly_vec)?;
        witness.modules_n_vars.push(Some(n_vars_vec));
        oracle_offset += module.oracles.len();
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
    pub fn new_entry_with_capacity(&mut self, log_bits: usize) -> EntryId {
        let num_underliers = (1 << log_bits) / OptimalUnderlier::BITS;
        self.entries.push(Vec::with_capacity(num_underliers));
        self.entries.len() - 1
    }

    #[inline]
    pub fn bind_oracle_to(&mut self, oracle_id: OracleId, entry_id: EntryId) {
        self.entry_map.insert(oracle_id, entry_id);
    }

    #[inline]
    pub fn push_u8s_to(&mut self, u8s: [u8; 16], entry_id: EntryId) {
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128::from_le_bytes(u8s)))
    }

    #[inline]
    pub fn push_u16s_to(&mut self, u16s: [u16; 8], entry_id: EntryId) {
        let u128 = unsafe { std::mem::transmute::<[u16; 8], u128>(u16s) };
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    #[inline]
    pub fn push_u32s_to(&mut self, u32s: [u32; 4], entry_id: EntryId) {
        let u128 = unsafe { std::mem::transmute::<[u32; 4], u128>(u32s) };
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    #[inline]
    pub fn push_u64s_to(&mut self, u64s: [u64; 2], entry_id: EntryId) {
        let u128 = unsafe { std::mem::transmute::<[u64; 2], u128>(u64s) };
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
    }

    #[inline]
    pub fn push_u128_to(&mut self, u128: u128, entry_id: EntryId) {
        self.entries[entry_id].push(OptimalUnderlier::from_u128(u128))
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
}
