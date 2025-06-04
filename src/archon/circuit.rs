use anyhow::{Result, bail, ensure};
use binius_core::constraint_system::channel::{Flush, OracleOrConst};
use binius_core::constraint_system::exp::Exp;
use binius_core::oracle::{ConstraintSetBuilder, MultilinearOracleSet, ShiftVariant};
use binius_core::{
    constraint_system::{
        ConstraintSystem,
        channel::{ChannelId, FlushDirection},
    },
    transparent::step_down::StepDown,
};
use binius_field::{TowerField, arch::OptimalUnderlier, underlier::UnderlierType};
use binius_utils::checked_arithmetics::log2_ceil_usize;
use rayon::iter::{IntoParallelRefIterator, IntoParallelRefMutIterator, ParallelIterator};
use std::sync::Arc;

use crate::archon::transparent::{Incremental, constant_from_b128};

use super::OracleIdx;
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

pub(super) struct ArchonFlush {
    pub(super) oracles: Vec<OracleIdx>,
    pub(super) channel_id: ChannelId,
    pub(super) direction: FlushDirection,
    pub(super) selector: OracleIdx,
    pub(super) multiplicity: u64,
}

pub(super) enum ArchonOracleOrConst {
    Oracle(OracleIdx),
    Const { base: F, tower_level: usize },
}

pub(super) struct ArchonExp {
    pub(super) exp_bits: Vec<OracleIdx>,
    pub(super) base: ArchonOracleOrConst,
    pub(super) result: OracleIdx,
}

pub struct CircuitModule {
    pub(super) module_id: ModuleId,
    pub(super) oracles: Freezable<Vec<OracleInfo>>,
    pub(super) flushes: Vec<ArchonFlush>,
    pub(super) constraints: Vec<Constraint>,
    pub(super) non_zero_oracle_idxs: Vec<OracleIdx>,
    pub(super) exponents: Vec<ArchonExp>,
    pub(super) namespacer: Namespacer,
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
            non_zero_oracle_idxs: vec![],
            exponents: vec![],
            namespacer: Namespacer::default(),
        }
    }

    #[inline]
    pub const fn selector(&self) -> OracleIdx {
        OracleIdx(0)
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
        selector: OracleIdx,
        oracle_idxs: impl IntoIterator<Item = OracleIdx>,
        multiplicity: u64,
    ) {
        self.flushes.push(ArchonFlush {
            oracles: oracle_idxs.into_iter().collect(),
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
        oracle_idxs: impl IntoIterator<Item = OracleIdx>,
        composition: ArithExpr,
    ) {
        self.constraints.push(Constraint {
            name: name.to_string(),
            oracle_idxs: oracle_idxs.into_iter().collect(),
            composition,
        });
    }

    #[inline]
    pub fn assert_not_zero(&mut self, oracle_idx: OracleIdx) {
        self.non_zero_oracle_idxs.push(oracle_idx);
    }

    #[inline]
    pub fn assert_dynamic_exp(
        &mut self,
        exp_bits: Vec<OracleIdx>,
        result: OracleIdx,
        base: OracleIdx,
    ) {
        self.exponents.push(ArchonExp {
            exp_bits,
            base: ArchonOracleOrConst::Oracle(base),
            result,
        })
    }

    #[inline]
    pub fn assert_static_exp(
        &mut self,
        exp_bits: Vec<OracleIdx>,
        result: OracleIdx,
        base: F,
        base_tower_level: usize,
    ) {
        self.exponents.push(ArchonExp {
            exp_bits,
            base: ArchonOracleOrConst::Const {
                base,
                tower_level: base_tower_level,
            },
            result,
        })
    }

    #[inline]
    pub fn add_committed<FS: TowerField>(
        &mut self,
        name: &(impl ToString + ?Sized),
    ) -> Result<OracleIdx> {
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
    ) -> Result<OracleIdx> {
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
        inner: impl IntoIterator<Item = (OracleIdx, F)>,
    ) -> Result<OracleIdx> {
        let inner = inner.into_iter().collect::<Vec<_>>();
        let tower_level = inner
            .iter()
            .map(|(oracle_idx, coeff)| {
                self.oracles.get_ref()[oracle_idx.val()]
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
        inner: OracleIdx,
        log_degree: usize,
    ) -> Result<OracleIdx> {
        let inner_tower_level = self.oracles.get_ref()[inner.val()].tower_level;
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
        inner: OracleIdx,
        shift_offset: u32,
        block_bits: usize,
        variant: ShiftVariant,
    ) -> Result<OracleIdx> {
        let inner_tower_level = self.oracles.get_ref()[inner.val()].tower_level;
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

    pub fn add_projected(
        &mut self,
        name: &(impl ToString + ?Sized),
        inner: OracleIdx,
        mask: u64,
        unprojected_size: usize,
    ) -> Result<OracleIdx> {
        let inner_tower_level = self.oracles.get_ref()[inner.val()].tower_level;

        let mut mask_bits: Vec<F> = (0..64)
            .map(|n| F::from(((mask >> n) & 1) as u128))
            .collect();

        mask_bits.truncate(log2_ceil_usize(unprojected_size));

        let oracle_info = OracleInfo {
            name: self.namespacer.scoped_name(name),
            tower_level: inner_tower_level,
            kind: OracleKind::Projected {
                inner,
                mask,
                mask_bits,
                unprojected_size,
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
    fn add_oracle_info(&mut self, oracle_info: OracleInfo) -> Result<OracleIdx> {
        self.oracles.get_mut()?.push(oracle_info);
        Ok(OracleIdx(self.oracles.get_ref().len() - 1))
    }
}

pub fn compile_circuit_modules(
    modules: &[&CircuitModule],
    modules_heights: &[u64],
) -> Result<ConstraintSystem<F>> {
    ensure!(
        modules.len() == modules_heights.len(),
        "Number of modules is incompatible with the number of heights"
    );
    let mut oracle_offset = 0;
    let mut oracles = MultilinearOracleSet::new();
    let mut constraint_builder = ConstraintSetBuilder::new();
    let mut flushes = Vec::new();
    let mut non_zero_oracle_ids = Vec::new();
    let mut exponents = Vec::new();
    let mut max_channel_id = 0;
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
                    oracles.add_named(name).committed(n_vars, *tower_level);
                }
                OracleKind::LinearCombination { offset, inner } => {
                    let n_vars = n_vars_fn(*tower_level);
                    let inner = inner
                        .iter()
                        .map(|(oracle_idx, f)| (oracle_idx.oracle_id(oracle_offset), *f));
                    oracles
                        .add_named(name)
                        .linear_combination_with_offset(n_vars, *offset, inner)?;
                }
                OracleKind::Packed { inner, log_degree } => {
                    oracles
                        .add_named(name)
                        .packed(inner.oracle_id(oracle_offset), *log_degree)?;
                }
                OracleKind::Transparent(Transparent::Constant(b128)) => {
                    let n_vars = n_vars_fn(*tower_level);
                    oracles
                        .add_named(name)
                        .transparent(constant_from_b128(*b128, n_vars))?;
                }
                OracleKind::Transparent(Transparent::Incremental) => {
                    let tower_level = Incremental::min_tower_level(height);
                    let n_vars = n_vars_fn(tower_level);
                    oracles.add_named(name).transparent(Incremental {
                        n_vars,
                        tower_level,
                    })?;
                }
                OracleKind::StepDown => {
                    let n_vars = n_vars_fn(*tower_level);
                    oracles
                        .add_named(name)
                        .transparent(StepDown::new(n_vars, height_usize)?)?;
                }

                OracleKind::Shifted {
                    inner,
                    shift_offset,
                    block_bits,
                    variant,
                } => {
                    oracles.add_named(name).shifted(
                        inner.oracle_id(oracle_offset),
                        *shift_offset as usize,
                        *block_bits,
                        *variant,
                    )?;
                }
                OracleKind::Projected {
                    inner, mask_bits, ..
                } => {
                    oracles.add_named(name).projected(
                        inner.oracle_id(oracle_offset),
                        mask_bits.clone(),
                        0,
                    )?;
                }
            };
        }

        for Constraint {
            name,
            oracle_idxs,
            composition,
        } in &module.constraints
        {
            let mut oracle_idxs = oracle_idxs
                .iter()
                .map(|o| o.oracle_id(oracle_offset))
                .collect();
            let mut composition = composition.clone();
            composition.offset_oracles(oracle_offset);
            let composition = composition.into_arith_expr_core(&mut oracle_idxs);
            constraint_builder.add_zerocheck(name, oracle_idxs, composition.into());
        }

        for non_zero_oracle_idx in &module.non_zero_oracle_idxs {
            non_zero_oracle_ids.push(non_zero_oracle_idx.oracle_id(oracle_offset));
        }

        for ArchonExp {
            exp_bits,
            base,
            result,
        } in &module.exponents
        {
            let bits_ids = exp_bits
                .iter()
                .map(|o| o.oracle_id(oracle_offset))
                .collect();
            let base = match base {
                ArchonOracleOrConst::Oracle(o) => OracleOrConst::Oracle(o.oracle_id(oracle_offset)),
                ArchonOracleOrConst::Const { base, tower_level } => OracleOrConst::Const {
                    base: *base,
                    tower_level: *tower_level,
                },
            };
            let exp_result_id = result.oracle_id(oracle_offset);
            exponents.push(Exp {
                bits_ids,
                base,
                exp_result_id,
            });
        }

        for ArchonFlush {
            oracles,
            channel_id,
            direction,
            selector,
            multiplicity,
        } in &module.flushes
        {
            max_channel_id = max_channel_id.max(*channel_id);
            flushes.push(Flush {
                channel_id: *channel_id,
                direction: *direction,
                selectors: vec![selector.oracle_id(oracle_offset)],
                oracles: oracles
                    .iter()
                    .map(|o| OracleOrConst::Oracle(o.oracle_id(oracle_offset)))
                    .collect(),
                multiplicity: *multiplicity,
            });
        }

        oracle_offset += module.oracles.get_ref().len();
    }
    let table_constraints = constraint_builder.build(&oracles)?;
    Ok(ConstraintSystem {
        oracles,
        table_constraints,
        flushes,
        non_zero_oracle_ids,
        max_channel_id,
        exponents,
    })
}

pub(super) struct Constraint {
    pub(super) name: String,
    pub(super) oracle_idxs: Vec<OracleIdx>,
    pub(super) composition: ArithExpr,
}

#[derive(Clone)]
pub(super) enum Freezable<T> {
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

    pub(super) fn get_ref(&self) -> &T {
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
pub(super) struct Namespacer {
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
