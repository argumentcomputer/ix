use anyhow::{Context, Result, bail, ensure};
use binius_core::witness::MultilinearExtensionIndex;
use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    TowerField,
    arch::OptimalUnderlier,
    as_packed_field::PackedType,
    underlier::{UnderlierType, WithUnderlier},
};
use binius_math::MultilinearExtension;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator,
    IntoParallelRefMutIterator, ParallelIterator,
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::{collections::HashMap, mem::transmute, sync::Arc};

use super::{ModuleId, ModuleMode, OracleIdx, OracleInfo};

pub type EntryId = usize;

pub(super) const UNDERLIER_SIZE: usize = size_of::<OptimalUnderlier>();

#[derive(Default)]
pub struct WitnessModule {
    pub(super) module_id: ModuleId,
    pub(super) oracles: Arc<Vec<OracleInfo>>,
    pub(super) entries: Vec<Vec<OptimalUnderlier>>,
    pub(super) buffers: Vec<Vec<u8>>,
    /// Maps oracles to their entries and tower levels
    pub(super) entry_map: FxHashMap<OracleIdx, (EntryId, usize)>,
}

#[derive(Default)]
pub struct Witness<'a> {
    pub(crate) mlei: MultilinearExtensionIndex<'a, PackedType<OptimalUnderlier, B128>>,
    pub(crate) modes: Vec<ModuleMode>,
}

#[inline]
pub fn populate_witness_modules(
    witness_modules: &mut [WitnessModule],
    modes: Vec<ModuleMode>,
) -> Result<()> {
    ensure!(
        witness_modules.len() == modes.len(),
        "Incompatible numbers of modules and modes"
    );
    witness_modules
        .par_iter_mut()
        .zip(modes)
        .try_for_each(|(module, mode)| module.populate(mode))
}

pub fn compile_witness_modules(
    modules: &[WitnessModule],
    modes: Vec<ModuleMode>,
) -> Result<Witness<'_>> {
    ensure!(modules.len() == modes.len());
    let mut witness = Witness::with_capacity(modules.len());
    let mut oracle_offset = 0;
    for (module_idx, (module, mode)) in modules.iter().zip(modes).enumerate() {
        ensure!(
            module_idx == module.module_id,
            "Wrong compilation order. Expected module {module_idx}, but got {}.",
            module.module_id
        );
        let ModuleMode::Active { log_height, depth } = mode else {
            // Deactivate module.
            witness.modes.push(ModuleMode::Inactive);
            continue;
        };
        let num_oracles = module.num_oracles();
        let oracles_poly_results = (0..num_oracles)
            .into_par_iter()
            .map(|oracle_idx| {
                let oracle_idx = OracleIdx(oracle_idx);
                let Some(&(entry_id, tower_level)) = module.entry_map.get(&oracle_idx) else {
                    bail!("Entry not found for oracle {oracle_idx}, module {module_idx}.");
                };
                let entry = &module.entries[entry_id];
                macro_rules! oracle_poly {
                    ($bf:ident) => {{
                        let values =
                            PackedType::<OptimalUnderlier, $bf>::from_underliers_ref(entry);
                        let mle = MultilinearExtension::from_values_generic(values)
                            .context(format!(
                                "MLE instantiation for entry {entry_id}, oracle {oracle_idx}, module {module_idx}"
                            ))?
                            .specialize_arc_dyn();
                        Ok((oracle_idx.oracle_id(oracle_offset), mle))
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
                        "Unsupported tower level {tower_level} for oracle {oracle_idx}, module {module_idx}"
                    ),
                }
            })
            .collect::<Vec<_>>();
        let mut oracle_poly_vec = Vec::with_capacity(oracles_poly_results.len());
        for oracle_data_result in oracles_poly_results {
            oracle_poly_vec.push(oracle_data_result?);
        }
        witness.mlei.update_multilin_poly(oracle_poly_vec)?;
        witness.modes.push(ModuleMode::Active { log_height, depth });
        oracle_offset += num_oracles;
    }
    Ok(witness)
}

impl WitnessModule {
    #[inline]
    pub fn new_entry(&mut self) -> EntryId {
        self.entries.push(vec![]);
        self.buffers.push(vec![]);
        self.entries.len() - 1
    }

    #[inline]
    pub fn new_entry_with_capacity(&mut self, log_bits: u8) -> EntryId {
        let bits = 1 << log_bits;
        let num_underliers = bits / OptimalUnderlier::BITS;
        let num_bytes = bits / 8;
        self.entries.push(Vec::with_capacity(num_underliers));
        self.buffers.push(Vec::with_capacity(num_bytes));
        self.entries.len() - 1
    }

    #[inline]
    pub fn bind_oracle_to<FS: TowerField>(&mut self, oracle_idx: OracleIdx, entry_id: EntryId) {
        self.entry_map
            .insert(oracle_idx, (entry_id, FS::TOWER_LEVEL));
    }

    #[inline]
    pub fn push_u8s_to(&mut self, u8s: impl IntoIterator<Item = u8>, entry_id: EntryId) {
        self.buffers[entry_id].extend(u8s);
        self.drain_buffer(entry_id);
    }

    #[inline]
    pub fn push_u16s_to(&mut self, u16s: impl IntoIterator<Item = u16>, entry_id: EntryId) {
        let u8s = u16s.into_iter().flat_map(u16::to_le_bytes);
        self.push_u8s_to(u8s, entry_id);
    }

    #[inline]
    pub fn push_u32s_to(&mut self, u32s: impl IntoIterator<Item = u32>, entry_id: EntryId) {
        let u8s = u32s.into_iter().flat_map(u32::to_le_bytes);
        self.push_u8s_to(u8s, entry_id);
    }

    #[inline]
    pub fn push_u64s_to(&mut self, u64s: impl IntoIterator<Item = u64>, entry_id: EntryId) {
        let u8s = u64s.into_iter().flat_map(u64::to_le_bytes);
        self.push_u8s_to(u8s, entry_id);
    }

    #[inline]
    pub fn push_u128s_to(&mut self, u128s: impl IntoIterator<Item = u128>, entry_id: EntryId) {
        let u8s = u128s.into_iter().flat_map(u128::to_le_bytes);
        self.push_u8s_to(u8s, entry_id);
    }

    fn drain_buffer(&mut self, entry_id: EntryId) {
        const CHUNK_SIZE: usize = size_of::<u128>() / size_of::<u8>();
        let num_chunks = self.buffers[entry_id].len() / CHUNK_SIZE;
        for chunk_idx in 0..num_chunks {
            let start = chunk_idx * CHUNK_SIZE;
            let end = start + CHUNK_SIZE;
            let mut bytes = [0; CHUNK_SIZE];
            bytes.copy_from_slice(&self.buffers[entry_id][start..end]);
            self.entries[entry_id].push(OptimalUnderlier::from(u128::from_le_bytes(bytes)));
        }
        self.buffers[entry_id].drain(..num_chunks * CHUNK_SIZE);
    }

    pub fn get_data_num_bytes(&self, oracle_idx: &OracleIdx) -> usize {
        let (entry_id, _) = self.entry_map.get(oracle_idx).expect("No entry found");
        UNDERLIER_SIZE * self.entries[*entry_id].len() + self.buffers[*entry_id].len()
    }

    pub fn get_data(&self, oracle_idx: &OracleIdx) -> Vec<u8> {
        let (entry_id, _) = self.entry_map.get(oracle_idx).expect("No entry found");
        self.entries[*entry_id]
            .par_iter()
            .flat_map(|&u| unsafe { transmute::<OptimalUnderlier, [u8; 16]>(u) })
            .chain(self.buffers[*entry_id].clone())
            .collect::<Vec<_>>()
    }

    #[inline]
    pub(crate) fn new(module_id: ModuleId, oracles: Arc<Vec<OracleInfo>>) -> Self {
        let num_oracles = oracles.len();
        Self {
            module_id,
            oracles,
            entries: vec![],
            buffers: vec![],
            entry_map: HashMap::with_capacity_and_hasher(num_oracles, FxBuildHasher),
        }
    }

    pub(super) fn num_oracles(&self) -> usize {
        self.oracles.len()
    }
}

impl Witness<'_> {
    #[inline]
    fn with_capacity(num_modules: usize) -> Self {
        Self {
            mlei: MultilinearExtensionIndex::new(),
            modes: Vec::with_capacity(num_modules),
        }
    }
}
