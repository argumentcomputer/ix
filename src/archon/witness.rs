use anyhow::{Context, Result, bail, ensure};
use binius_core::{oracle::OracleId, witness::MultilinearExtensionIndex};
use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
    Field, TowerField,
    arch::OptimalUnderlier,
    as_packed_field::PackedType,
    underlier::{UnderlierType, WithUnderlier},
};
use binius_math::MultilinearExtension;
use binius_utils::checked_arithmetics::log2_strict_usize;
use indexmap::IndexSet;
use rayon::iter::{IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{collections::HashMap, sync::Arc};

use super::{
    ModuleId, OracleInfo, OracleKind,
    transparent::{ConstVal, Transparent},
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
    /// The `n_vars` for each module. `0` means that the circuit module is
    /// deactivated and must be skipped at compilation time.
    pub(crate) modules_n_vars: Vec<u8>,
}

#[inline]
pub fn populate_witness_modules(modules: &mut [WitnessModule]) -> Result<()> {
    modules.par_iter_mut().try_for_each(WitnessModule::populate)
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
            // Deactivate module.
            witness.modules_n_vars.push(0);
            continue;
        }
        let oracles_data_results = (0..module.num_oracles())
            .into_par_iter()
            .map(|oracle_id| {
                let Some(&(entry_id, tower_level)) = module.entry_map.get(&oracle_id) else {
                    bail!("Entry not found for oracle {oracle_id}, module {module_idx}.");
                };
                let entry = &module.entries[entry_id];
                let n_vars_usize = WitnessModule::n_vars(entry.len(), tower_level).context(
                    format!("Computing n_vars for entry {entry_id}, bound to oracle {oracle_id}, module {module_idx}")
                )?;
                let n_vars: u8 = n_vars_usize
                    .try_into()
                    .context(format!("Representing n_vars={n_vars_usize} as an u8"))?;
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
        let mut oracle_poly_vec = Vec::with_capacity(oracles_data_results.len());
        let mut n_vars_opt = None;
        for oracle_data_result in oracles_data_results {
            let (oracle_poly, oracle_n_vars) = oracle_data_result?;
            match n_vars_opt {
                Some(known_n_vars) => ensure!(
                    oracle_n_vars == known_n_vars,
                    "Witness for module {module_idx} has incompatible columns sizes: {oracle_n_vars} != {known_n_vars}"
                ),
                None => n_vars_opt = Some(oracle_n_vars),
            }
            oracle_poly_vec.push(oracle_poly);
        }
        let n_vars = n_vars_opt.unwrap_or(0); // Deactivate module without oracles
        witness.mlei.update_multilin_poly(oracle_poly_vec)?;
        witness.modules_n_vars.push(n_vars);
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

    /// Populates the witness module with `n_vars` inferred from the length of
    /// the data bound to the committed oracles.
    #[inline]
    pub fn populate(&mut self) -> Result<()> {
        self.populate_with_n_vars(None)
    }

    fn populate_with_n_vars(&mut self, mut n_vars_opt: Option<usize>) -> Result<()> {
        let mut set_n_vars_opt = |entry_id: usize, tower_level| -> Result<()> {
            let num_underliers = self.entries[entry_id].len();
            let n_vars = WitnessModule::n_vars(num_underliers, tower_level).context(format!(
                "Computing n_vars for entry {entry_id} of witness module {}",
                self.module_id
            ))?;
            match n_vars_opt {
                Some(known_n_vars) => ensure!(
                    n_vars == known_n_vars,
                    "Found prepopulated oracles with incompatible lengths"
                ),
                None => n_vars_opt = Some(n_vars),
            }
            Ok(())
        };

        // "Root oracles" are those which aren't committed and aren't dependencies
        // of any other oracle. `root_oracles` starts with all oracles, which are
        // removed as the following loop finds out they break such condition.
        //
        // The loop also uses `set_n_vars_opt` to make sure that `n_vars_opt` ends
        // up with an unified target length for all oracles.
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
                OracleKind::Transparent(_) => (),
            }

            if is_committed {
                let Some(&(entry_id, tower_level)) = self.entry_map.get(&oracle_id) else {
                    bail!(
                        "Committed oracle {} (id={oracle_id}) for witness module {} is not populated",
                        &oracle_info.name,
                        &self.module_id,
                    );
                };
                set_n_vars_opt(entry_id, tower_level)?;
            } else if let Some(&(entry_id, tower_level)) = self.entry_map.get(&oracle_id) {
                set_n_vars_opt(entry_id, tower_level)?;
            }
        }

        // Extract the target n_vars for a potential early error return.
        let Some(n_vars) = n_vars_opt else {
            bail!("Couldn't infer n_vars for module {}", &self.module_id);
        };

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
                OracleKind::Transparent(_) => (),
                OracleKind::LinearCombination { inner, .. } => {
                    for (inner_oracle_id, _) in inner {
                        stack_to_visit!(inner_oracle_id);
                    }
                }
            }
            if !is_committed {
                compute_order.insert(oracle_id);
            }
        }

        // And now we're finally able to populate the witness, following the
        // correct compute order and making the assumption that dependency oracles
        // were already populated.
        let num_underliers =
            |tower_level| 1usize << (n_vars + tower_level - OptimalUnderlier::LOG_BITS);
        while let Some(oracle_id) = compute_order.pop() {
            if self.entry_map.contains_key(&oracle_id) {
                // Already populated. Skip.
                continue;
            }
            let oracle_info = &self.oracles[oracle_id];
            let tower_level = oracle_info.tower_level;
            ensure!(
                n_vars + tower_level >= OptimalUnderlier::LOG_BITS,
                "n_vars + tower_level needs to be at least {}",
                OptimalUnderlier::LOG_BITS
            );
            let underliers = match &oracle_info.kind {
                OracleKind::Committed => unreachable!("Committed oracles shouldn't be computed"),
                OracleKind::LinearCombination { .. } => vec![], // TODO
                OracleKind::Transparent(transparent) => match transparent {
                    Transparent::Constant(c) => {
                        let u128 = match c {
                            ConstVal::B1(B1::ZERO)
                            | ConstVal::B2(B2::ZERO)
                            | ConstVal::B4(B4::ZERO)
                            | ConstVal::B8(B8::ZERO)
                            | ConstVal::B16(B16::ZERO)
                            | ConstVal::B32(B32::ZERO)
                            | ConstVal::B64(B64::ZERO)
                            | ConstVal::B128(B128::ZERO) => 0,
                            ConstVal::B1(_) => u128::MAX,
                            ConstVal::B2(b) => replicate_2_bits(b.to_underlier().val()),
                            ConstVal::B4(b) => replicate_4_bits(b.to_underlier().val()),
                            ConstVal::B8(b) => u128::from_le_bytes([b.to_underlier(); 16]),
                            ConstVal::B16(b) => {
                                let u16s = [b.to_underlier(); 8];
                                unsafe { std::mem::transmute::<[u16; 8], u128>(u16s) }
                            }
                            ConstVal::B32(b) => {
                                let u32s = [b.to_underlier(); 4];
                                unsafe { std::mem::transmute::<[u32; 4], u128>(u32s) }
                            }
                            ConstVal::B64(b) => {
                                let u64s = [b.to_underlier(); 2];
                                unsafe { std::mem::transmute::<[u64; 2], u128>(u64s) }
                            }
                            ConstVal::B128(b) => b.to_underlier(),
                        };
                        vec![OptimalUnderlier::from_u128(u128); num_underliers(tower_level)]
                    }
                },
            };
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

    /// Computes the number of variables given the number of `OptimalUnderlier`s
    /// used and the tower level of the oracle.
    ///
    /// # Panics
    /// This function panics if `num_underliers` isn't a power of two.
    fn n_vars(num_underliers: usize, tower_level: usize) -> Result<usize> {
        ensure!(
            num_underliers.is_power_of_two(),
            "Data size is not a power of two."
        );
        Ok(log2_strict_usize(num_underliers) + OptimalUnderlier::LOG_BITS - tower_level)
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
            modules_n_vars: Vec::with_capacity(num_modules),
        }
    }
}

#[inline(always)]
fn replicate_2_bits(byte: u8) -> u128 {
    let bits = (byte & 0b11) as u128; // Extract the first 2 bits
    bits * 0x55555555555555555555555555555555u128 // Repeat pattern 64 times
}

#[inline(always)]
fn replicate_4_bits(byte: u8) -> u128 {
    let bits = (byte & 0b1111) as u128; // Extract first 4 bits
    bits * 0x11111111111111111111111111111111u128 // Repeat pattern 16 times
}

#[cfg(test)]
mod tests {
    use binius_field::{
        BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
        BinaryField32b as B32, BinaryField128b as B128, underlier::SmallU,
    };

    use crate::archon::{
        circuit::{CircuitModule, init_witness_modules},
        protocol::validate_witness,
        transparent::{ConstVal, Transparent},
        witness::{replicate_2_bits, replicate_4_bits},
    };

    use super::compile_witness_modules;

    #[test]
    fn test_populate() {
        let mut circuit_module = CircuitModule::new(0);
        circuit_module
            .add_transparent(
                "b1",
                Transparent::Constant(ConstVal::B1(B1::new(SmallU::new(1)))),
            )
            .unwrap();
        circuit_module
            .add_transparent(
                "b2",
                Transparent::Constant(ConstVal::B2(B2::new(SmallU::new(1)))),
            )
            .unwrap();
        circuit_module
            .add_transparent(
                "b4",
                Transparent::Constant(ConstVal::B4(B4::new(SmallU::new(3)))),
            )
            .unwrap();
        circuit_module
            .add_transparent("b8", Transparent::Constant(ConstVal::B8(B8::new(42))))
            .unwrap();
        circuit_module
            .add_transparent("b32", Transparent::Constant(ConstVal::B32(B32::new(42))))
            .unwrap();
        circuit_module
            .add_transparent("b128", Transparent::Constant(ConstVal::B128(B128::new(42))))
            .unwrap();

        circuit_module.freeze_oracles();
        let circuit_modules = [circuit_module];

        let test_n_vars = |n_vars| {
            let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
            witness_modules[0]
                .populate_with_n_vars(Some(n_vars))
                .unwrap();
            assert!(!witness_modules[0].entry_map.is_empty());
            let witness = compile_witness_modules(&witness_modules).unwrap();
            assert!(validate_witness(&circuit_modules, &witness, &[]).is_ok());
        };

        test_n_vars(7);
        test_n_vars(8);
        test_n_vars(9);
    }

    #[test]
    fn test_replicate_2_bits() {
        assert_eq!(
            replicate_2_bits(0b00000000),
            0x00000000000000000000000000000000u128
        );
        assert_eq!(
            replicate_2_bits(0b00000001),
            0x55555555555555555555555555555555u128
        );
        assert_eq!(
            replicate_2_bits(0b00000010),
            0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAu128
        );
        assert_eq!(
            replicate_2_bits(0b00000011),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFu128
        );
    }

    #[test]
    fn test_replicate_4_bits() {
        assert_eq!(
            replicate_4_bits(0b00000000),
            0x00000000000000000000000000000000u128
        );
        assert_eq!(
            replicate_4_bits(0b00000001),
            0x11111111111111111111111111111111u128
        );
        assert_eq!(
            replicate_4_bits(0b00000010),
            0x22222222222222222222222222222222u128
        );
        assert_eq!(
            replicate_4_bits(0b00000011),
            0x33333333333333333333333333333333u128
        );
        assert_eq!(
            replicate_4_bits(0b00000100),
            0x44444444444444444444444444444444u128
        );
        assert_eq!(
            replicate_4_bits(0b00000101),
            0x55555555555555555555555555555555u128
        );
        assert_eq!(
            replicate_4_bits(0b00000110),
            0x66666666666666666666666666666666u128
        );
        assert_eq!(
            replicate_4_bits(0b00000111),
            0x77777777777777777777777777777777u128
        );
        assert_eq!(
            replicate_4_bits(0b00001000),
            0x88888888888888888888888888888888u128
        );
        assert_eq!(
            replicate_4_bits(0b00001001),
            0x99999999999999999999999999999999u128
        );
        assert_eq!(
            replicate_4_bits(0b00001010),
            0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAu128
        );
        assert_eq!(
            replicate_4_bits(0b00001011),
            0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBu128
        );
        assert_eq!(
            replicate_4_bits(0b00001100),
            0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCu128
        );
        assert_eq!(
            replicate_4_bits(0b00001101),
            0xDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDu128
        );
        assert_eq!(
            replicate_4_bits(0b00001110),
            0xEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEu128
        );
        assert_eq!(
            replicate_4_bits(0b00001111),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFu128
        );
    }
}
