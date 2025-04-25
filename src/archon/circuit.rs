use crate::archon::transparent::{Incremental, constant_from_b128};
use anyhow::{Result, bail, ensure};
use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::oracle::ShiftVariant;
use binius_core::{
    constraint_system::{
        ConstraintSystem,
        channel::{ChannelId, Flush, FlushDirection},
    },
    oracle::OracleId,
    transparent::step_down::StepDown,
};
use binius_field::{TowerField, arch::OptimalUnderlier, underlier::UnderlierType};
use binius_utils::checked_arithmetics::log2_ceil_usize;
use rayon::iter::{IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};
use std::sync::Arc;

use super::{
    F, ModuleId, OracleInfo, OracleKind, arith_expr::ArithExpr, transparent::Transparent,
    witness::WitnessModule,
};

#[inline]
pub fn freeze_circuit_modules_oracles(circuit_modules: &mut [CircuitModule]) {
    circuit_modules
        .par_iter_mut()
        .for_each(|module| module.freeze_oracles())
}

#[inline]
pub fn init_witness_modules(circuit_modules: &[CircuitModule]) -> Result<Vec<WitnessModule>> {
    circuit_modules
        .par_iter()
        .map(CircuitModule::init_witness_module)
        .collect()
}

pub struct CircuitModule {
    module_id: ModuleId,
    oracles: Freezable<Vec<OracleInfo>>,
    flushes: Vec<Flush>,
    constraints: Vec<Constraint>,
    non_zero_oracle_ids: Vec<OracleId>,
    namespacer: Namespacer,
}

impl CircuitModule {
    #[inline]
    pub fn new(module_id: ModuleId) -> Self {
        let step_down = OracleInfo {
            name: format!("step_down-module-{module_id}"),
            tower_level: 0,
            kind: OracleKind::StepDown,
        };
        let oracles = Freezable::Raw(vec![step_down]);
        Self {
            module_id,
            oracles,
            flushes: vec![],
            constraints: vec![],
            non_zero_oracle_ids: vec![],
            namespacer: Namespacer::default(),
        }
    }

    #[inline]
    pub const fn selector(&self) -> OracleId {
        0
    }

    #[inline]
    pub fn freeze_oracles(&mut self) {
        self.oracles.freeze()
    }

    #[inline]
    pub fn init_witness_module(&self) -> Result<WitnessModule> {
        Ok(WitnessModule::new(
            self.module_id,
            self.oracles.get_frozen()?,
        ))
    }

    #[inline]
    pub fn flush(
        &mut self,
        direction: FlushDirection,
        channel_id: ChannelId,
        selector: OracleId,
        oracle_ids: impl IntoIterator<Item = OracleId>,
        multiplicity: u64,
    ) {
        self.flushes.push(Flush {
            oracles: oracle_ids.into_iter().collect(),
            channel_id,
            direction,
            selector,
            multiplicity,
        });
    }

    #[inline]
    pub fn assert_zero(
        &mut self,
        name: &(impl ToString + ?Sized),
        oracle_ids: impl IntoIterator<Item = OracleId>,
        composition: ArithExpr,
    ) {
        self.constraints.push(Constraint {
            name: name.to_string(),
            oracle_ids: oracle_ids.into_iter().collect(),
            composition,
        });
    }

    #[inline]
    pub fn assert_not_zero(&mut self, oracle_id: OracleId) {
        self.non_zero_oracle_ids.push(oracle_id);
    }

    #[inline]
    pub fn add_committed<FS: TowerField>(
        &mut self,
        name: &(impl ToString + ?Sized),
    ) -> Result<OracleId> {
        let oracle_info = OracleInfo {
            name: self.namespacer.scoped_name(name),
            tower_level: FS::TOWER_LEVEL,
            kind: OracleKind::Committed,
        };
        self.add_oracle_info(oracle_info)
    }

    #[inline]
    pub fn add_transparent(
        &mut self,
        name: &(impl ToString + ?Sized),
        transparent: Transparent,
    ) -> Result<OracleId> {
        let oracle_info = OracleInfo {
            name: self.namespacer.scoped_name(name),
            tower_level: transparent.tower_level(),
            kind: OracleKind::Transparent(transparent),
        };
        self.add_oracle_info(oracle_info)
    }

    pub fn add_linear_combination(
        &mut self,
        name: &(impl ToString + ?Sized),
        offset: F,
        inner: impl IntoIterator<Item = (OracleId, F)>,
    ) -> Result<OracleId> {
        let inner = inner.into_iter().collect::<Vec<_>>();
        let tower_level = inner
            .iter()
            .map(|(oracle_id, coeff)| {
                self.oracles.get_ref()[*oracle_id]
                    .tower_level
                    .max(coeff.min_tower_level())
            })
            .max()
            .unwrap_or(0)
            .max(offset.min_tower_level());
        let oracle_info = OracleInfo {
            name: self.namespacer.scoped_name(name),
            tower_level,
            kind: OracleKind::LinearCombination { offset, inner },
        };
        self.add_oracle_info(oracle_info)
    }

    #[inline]
    pub fn add_packed(
        &mut self,
        name: &(impl ToString + ?Sized),
        inner: OracleId,
        log_degree: usize,
    ) -> Result<OracleId> {
        let inner_tower_level = self.oracles.get_ref()[inner].tower_level;
        let oracle_info = OracleInfo {
            name: self.namespacer.scoped_name(name),
            tower_level: inner_tower_level + log_degree,
            kind: OracleKind::Packed { inner, log_degree },
        };
        self.add_oracle_info(oracle_info)
    }

    pub fn add_shifted(
        &mut self,
        name: &(impl ToString + ?Sized),
        inner: OracleId,
        shift_offset: usize,
        block_bits: usize,
        variant: ShiftVariant,
    ) -> Result<OracleId> {
        let inner_tower_level = self.oracles.get_ref()[inner].tower_level;

        // Shifted columns only make sense when instantiated from BinaryField1b committed columns
        assert_eq!(inner_tower_level, 0usize);

        let oracle_info = OracleInfo {
            name: self.namespacer.scoped_name(name),
            tower_level: inner_tower_level,
            kind: OracleKind::Shifted {
                inner,
                shift_offset,
                block_bits,
                variant,
            },
        };
        self.add_oracle_info(oracle_info)
    }

    #[inline]
    pub fn push_namespace<S: ToString + ?Sized>(&mut self, name: &S) {
        self.namespacer.push(name);
    }

    #[inline]
    pub fn pop_namespace(&mut self) {
        self.namespacer.pop();
    }

    #[inline]
    fn add_oracle_info(&mut self, oracle_info: OracleInfo) -> Result<OracleId> {
        self.oracles.get_mut()?.push(oracle_info);
        Ok(self.oracles.get_ref().len() - 1)
    }
}

pub fn compile_circuit_modules(
    modules: &[CircuitModule],
    modules_heights: &[u64],
) -> Result<ConstraintSystem<F>> {
    ensure!(
        modules.len() == modules_heights.len(),
        "Number of modules is incompatible with the number of heights"
    );
    let mut oracle_offset = 0;
    let mut builder = ConstraintSystemBuilder::new();
    for (module_idx, (module, &height)) in modules.iter().zip(modules_heights).enumerate() {
        if height == 0 {
            // Deactivated module. Skip.
            continue;
        }
        let height_usize: usize = height.try_into()?;
        let log_height = log2_ceil_usize(height_usize);
        ensure!(
            module_idx == module.module_id,
            "Wrong compilation order. Expected module {module_idx}, but got {}.",
            module.module_id
        );

        // `n_vars` must be at least the number of variables in an underlier
        let n_vars_fn = |tower_level| {
            let underlier_n_vars = OptimalUnderlier::LOG_BITS - tower_level;
            log_height.max(underlier_n_vars)
        };

        for OracleInfo {
            name,
            tower_level,
            kind,
        } in module.oracles.get_ref()
        {
            match kind {
                OracleKind::Committed => {
                    let n_vars = n_vars_fn(*tower_level);
                    builder.add_committed(name, n_vars, *tower_level)
                }
                OracleKind::LinearCombination { offset, inner } => {
                    let n_vars = n_vars_fn(*tower_level);
                    let inner = inner
                        .iter()
                        .map(|(oracle_id, f)| (oracle_id + oracle_offset, *f));
                    builder.add_linear_combination_with_offset(name, n_vars, *offset, inner)?
                }
                OracleKind::Packed { inner, log_degree } => {
                    builder.add_packed(name, inner + oracle_offset, *log_degree)?
                }
                OracleKind::Transparent(Transparent::Constant(b128)) => {
                    let n_vars = n_vars_fn(*tower_level);
                    builder.add_transparent(name, constant_from_b128(*b128, n_vars))?
                }
                OracleKind::Transparent(Transparent::Incremental) => {
                    let tower_level = Incremental::min_tower_level(height);
                    let n_vars = n_vars_fn(tower_level);
                    builder.add_transparent(name, Incremental {
                        n_vars,
                        tower_level,
                    })?
                }
                OracleKind::StepDown => {
                    let n_vars = n_vars_fn(*tower_level);
                    builder.add_transparent(name, StepDown::new(n_vars, height_usize)?)?
                }

                OracleKind::Shifted {
                    inner,
                    shift_offset,
                    block_bits,
                    variant,
                } => builder.add_shifted(
                    name,
                    inner + oracle_offset,
                    *shift_offset,
                    *block_bits,
                    *variant,
                )?,
            };
        }

        for Constraint {
            name,
            oracle_ids,
            composition,
        } in &module.constraints
        {
            let mut oracle_ids = oracle_ids.iter().map(|o| o + oracle_offset).collect();
            let mut composition = composition.clone();
            composition.offset_oracles(oracle_offset);
            let composition = composition.into_arith_expr_core(&mut oracle_ids);
            builder.assert_zero(name, oracle_ids, composition);
        }

        for non_zero_oracle_id in &module.non_zero_oracle_ids {
            builder.assert_not_zero(non_zero_oracle_id + oracle_offset);
        }

        for Flush {
            oracles,
            channel_id,
            direction,
            selector,
            multiplicity,
        } in &module.flushes
        {
            builder.flush_custom(
                *direction,
                *channel_id,
                selector + oracle_offset,
                oracles.iter().map(|o| o + oracle_offset),
                *multiplicity,
            )?;
        }

        oracle_offset += module.oracles.get_ref().len();
    }
    builder.build()
}

struct Constraint {
    name: String,
    oracle_ids: Vec<OracleId>,
    composition: ArithExpr,
}

#[derive(Clone)]
enum Freezable<T> {
    Raw(T),
    Frozen(Arc<T>),
}

impl<T> Freezable<T> {
    fn freeze(&mut self)
    where
        T: Default,
    {
        if let Self::Raw(data) = self {
            *self = Self::Frozen(Arc::new(std::mem::take(data)))
        }
    }

    fn get_ref(&self) -> &T {
        match self {
            Self::Raw(data) => data,
            Self::Frozen(data) => data,
        }
    }

    fn get_mut(&mut self) -> Result<&mut T> {
        match self {
            Self::Raw(data) => Ok(data),
            Self::Frozen(_) => bail!("Data is frozen"),
        }
    }

    fn get_frozen(&self) -> Result<Arc<T>> {
        match self {
            Self::Raw(_) => bail!("Data is not frozen"),
            Self::Frozen(data) => Ok(data.clone()),
        }
    }
}

/// A namespacing struct that caches joined paths.
#[derive(Default)]
struct Namespacer {
    path: Vec<String>,
    joined_path: Option<String>,
}

impl Namespacer {
    fn push<S: ToString + ?Sized>(&mut self, limb: &S) {
        self.path.push(limb.to_string());
        self.joined_path = None;
    }

    fn pop(&mut self) {
        self.path.pop();
        self.joined_path = None;
    }

    fn scoped_name<S: ToString + ?Sized>(&mut self, name: &S) -> String {
        let concat = |joined: &str, name| {
            if joined.is_empty() {
                name
            } else {
                format!("{joined}::{name}")
            }
        };
        if let Some(joined) = &self.joined_path {
            concat(joined, name.to_string())
        } else {
            let joined = self.path.join("::");
            let concatenated = concat(&joined, name.to_string());
            self.joined_path = Some(joined);
            concatenated
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Namespacer;

    #[test]
    fn test_namespace() {
        let test_when_empty = |namespacer: &mut Namespacer| {
            assert_eq!(namespacer.scoped_name("a"), "a");
            assert_eq!(namespacer.scoped_name("b"), "b");
        };
        let test_with_foo = |namespacer: &mut Namespacer| {
            assert_eq!(namespacer.scoped_name("a"), "foo::a");
        };
        let test_with_foo_bar = |namespacer: &mut Namespacer| {
            assert_eq!(namespacer.scoped_name("a"), "foo::bar::a");
        };

        let namespacer = &mut Namespacer::default();
        test_when_empty(namespacer);

        namespacer.pop();
        test_when_empty(namespacer);

        namespacer.push("foo");
        test_with_foo(namespacer);

        namespacer.push("bar");
        test_with_foo_bar(namespacer);

        namespacer.pop();
        test_with_foo(namespacer);

        namespacer.push("bar");
        test_with_foo_bar(namespacer);

        namespacer.pop();
        test_with_foo(namespacer);

        namespacer.pop();
        test_when_empty(namespacer);
    }
}
