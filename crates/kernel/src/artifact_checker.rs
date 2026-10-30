//! Sealed host workers. Source snapshots are shared; declaration/reduction
//! caches are private to a worker and cannot be seeded by a public KEnv caller.
//! A bound worker's primitive table holds only the roles its source has
//! admitted, and a unit holding a role that is not admitted refuses.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::Name;
use ixon::env::Env;

use crate::env::KEnv;
use crate::error::TcError;
use crate::id::KId;
use crate::ingress::{IxonIngressLookups, ingress_name_with_input};
use crate::input::Input;
use crate::mode::{Anon, CheckDupLevelParams, KernelMode};
use crate::primitive::Primitives;
use crate::primitive_context::PrimitiveContext;
use crate::profile::ProfileSink;
use crate::role_admission::{ArtifactSource, Error};
use crate::tc::TypeChecker;

#[derive(Default)]
pub struct CheckStats {
  pub fuel_used: u64,
  pub def_eq_peak: u32,
  pub hot_misses: String,
}

type MakeChecker<M> = for<'a> fn(
  &'a mut KEnv<M>,
  &'a ArtifactSource,
  &'a IxonIngressLookups,
  PrimitiveContext<M>,
) -> TypeChecker<'a, M>;

fn make_named<'a, M: KernelMode>(
  env: &'a mut KEnv<M>,
  source: &'a ArtifactSource,
  lookups: &'a IxonIngressLookups,
  primitives: PrimitiveContext<M>,
) -> TypeChecker<'a, M> {
  TypeChecker::for_artifact_named(env, source, lookups, primitives)
}
fn make_anon<'a>(
  env: &'a mut KEnv<Anon>,
  source: &'a ArtifactSource,
  lookups: &'a IxonIngressLookups,
  primitives: PrimitiveContext<Anon>,
) -> TypeChecker<'a, Anon> {
  TypeChecker::for_artifact_anon(env, source, lookups, primitives)
}

pub struct ArtifactChecker<M: KernelMode> {
  source: Result<ArtifactSource, Error>,
  pub(crate) kernel: KEnv<M>,
  lookups: Arc<IxonIngressLookups>,
  primitives: PrimitiveContext<M>,
  make: MakeChecker<M>,
  last_check: CheckStats,
  debug_label: Option<String>,
}

impl<M: KernelMode> ArtifactChecker<M> {
  fn prepare(
    source: Result<ArtifactSource, Error>,
    named: bool,
    make: MakeChecker<M>,
  ) -> Self {
    let lookups = if named {
      source.as_ref().map_or_else(
        |_| Arc::new(IxonIngressLookups::default()),
        ArtifactSource::lookups,
      )
    } else {
      Arc::new(IxonIngressLookups::default())
    };
    let primitives = match &source {
      Ok(source) if source.binding().is_some() => PrimitiveContext::bound(
        source.clone(),
        source.admission().roles(),
        |address| lookups.name_for_addr(address).cloned(),
      ),
      Ok(_) => PrimitiveContext::Legacy(Arc::new(Primitives::from_addr_names(
        |address| lookups.name_for_addr(address).cloned(),
      ))),
      Err(_) => PrimitiveContext::UnpreparedBound,
    };
    Self {
      source,
      kernel: KEnv::new(),
      lookups,
      primitives,
      make,
      last_check: CheckStats::default(),
      debug_label: None,
    }
  }

  /// Borrowed capture requires quiescent input maps. Production drivers should
  /// prepare once before worker creation and clone the resulting source.
  pub fn new_named(source: &Env) -> Self {
    Self::from_named_source(ArtifactSource::snapshot(source))
  }
  pub fn from_named_source(source: Result<ArtifactSource, Error>) -> Self {
    Self::prepare(source, true, make_named)
  }

  fn source_for(
    &self,
    address: &Address,
  ) -> Result<&ArtifactSource, TcError<M>> {
    let source = self
      .source
      .as_ref()
      .map_err(|error| TcError::Other(error.to_string()))?;
    if source.binding().is_some() {
      // The certified checker reads no stream whose prelude it cannot read.
      if let Some(reason) = source.prelude_refusal() {
        return Err(TcError::Other(format!(
          "the artifact's prelude is not admitted: {reason}"
        )));
      }
      let roles = source
        .unit_roles(address)
        .map_err(|error| TcError::Other(error.to_string()))?;
      // A unit holding a bound role is checked only once that role's group
      // has been admitted; its candidate address is otherwise only syntax.
      if let Some(role) = roles.iter().find(|role| !source.is_admitted(**role))
      {
        let candidate = self.primitives.candidate_address(*role);
        return Err(TcError::Other(format!(
          "bound unit requires unadmitted role {role:?} at {candidate:?}"
        )));
      }
    }
    Ok(source)
  }

  pub fn check_const(&mut self, address: &Address) -> Result<(), TcError<M>>
  where
    M::MField<Vec<Name>>: CheckDupLevelParams,
  {
    self.last_check = CheckStats::default();
    self.source_for(address)?;
    let source = self
      .source
      .as_ref()
      .map_err(|error| TcError::Other(error.to_string()))?;
    let id = KId::new(
      address.clone(),
      M::meta_field(
        self.lookups.name_for_addr(address).cloned().unwrap_or_else(Name::anon),
      ),
    );
    self.check_id(&id, &source.clone())
  }

  /// The records a verdict on `roots` rests on, including both the reference
  /// closure of `roots` and the binding's support closure.
  pub fn verdict_closure(
    &self,
    roots: &[Address],
  ) -> Result<rustc_hash::FxHashSet<Address>, TcError<M>> {
    let source = self
      .source
      .as_ref()
      .map_err(|error| TcError::Other(error.to_string()))?;
    source
      .verdict_closure(roots)
      .map_err(|error| TcError::Other(error.to_string()))
  }

  /// Check `address` together with every record and blob in its
  /// [`ArtifactSource::verdict_closure`].
  pub fn check_const_with_verdict_closure(
    &mut self,
    address: &Address,
  ) -> Result<(), TcError<M>>
  where
    M::MField<Vec<Name>>: CheckDupLevelParams,
  {
    let source = self.source_for(address)?.clone();
    let mut closure: Vec<_> = source
      .verdict_closure(std::slice::from_ref(address))
      .map_err(|error| TcError::Other(error.to_string()))?
      .into_iter()
      .collect();
    closure.sort_unstable();
    for entry in &closure {
      if source.contains_record(entry) {
        if source
          .record_tag(entry)
          .map_err(|error| TcError::Other(error.to_string()))?
          != ixon::lazy::ConstVariantTag::Muts
        {
          self.check_const(entry)?;
        }
      } else {
        source
          .blob(entry)
          .map_err(|error| TcError::Other(error.to_string()))?;
      }
    }
    if !closure.contains(address) {
      self.check_const(address)?;
    }
    Ok(())
  }

  pub fn check_name(&mut self, name: &Name) -> Result<(), TcError<M>>
  where
    M::MField<Vec<Name>>: CheckDupLevelParams,
  {
    self.last_check = CheckStats::default();
    let source = self
      .source
      .as_ref()
      .map_err(|error| TcError::Other(error.to_string()))?
      .clone();
    let named = source.named(name).ok_or_else(|| {
      TcError::Other(format!("{}: missing Named entry", name.pretty()))
    })?;
    self.source_for(&named.addr)?;
    let id = ingress_name_with_input(
      &mut self.kernel,
      Input::Artifact(&source),
      &self.lookups,
      name,
    )
    .map_err(TcError::Other)?;
    self.check_id(&id, &source)
  }

  fn check_id(
    &mut self,
    id: &KId<M>,
    source: &ArtifactSource,
  ) -> Result<(), TcError<M>>
  where
    M::MField<Vec<Name>>: CheckDupLevelParams,
  {
    let mut checker = (self.make)(
      &mut self.kernel,
      source,
      &self.lookups,
      self.primitives.clone(),
    );
    if let Some(label) = &self.debug_label {
      checker.set_debug_label(label.clone());
    }
    let result = checker.check_ixon_const(id);
    self.last_check = CheckStats {
      fuel_used: checker.fuel_used(),
      def_eq_peak: checker.def_eq_peak,
      hot_misses: checker.hot_miss_summary(),
    };
    checker.finish_constant_accounting();
    result
  }

  pub fn last_check(&self) -> &CheckStats {
    &self.last_check
  }
  pub fn set_debug_label(&mut self, label: String) {
    self.debug_label = Some(label);
  }
  pub fn perf(&self) -> &crate::perf::PerfCounters {
    &self.kernel.perf
  }
  pub fn cache_sizes(&self) -> crate::env::KEnvCacheSizes {
    self.kernel.cache_sizes()
  }
  pub fn clear_releasing_memory(&mut self) {
    self.kernel.clear_releasing_memory();
  }
  pub fn clear_with_capacity_limit(&mut self, max: usize) {
    self.kernel.clear_with_capacity_limit(max);
  }
  pub fn clear_reduction_caches(&mut self) {
    self.kernel.clear_reduction_caches();
  }
  pub fn set_profile_sink(&mut self, sink: ProfileSink) {
    self.kernel.profile_sink = Some(sink);
  }
  pub fn take_profile_sink(&mut self) -> Option<ProfileSink> {
    self.kernel.profile_sink.take()
  }
}

impl ArtifactChecker<Anon> {
  /// Drive an actual carried unit owner. Its semantic primary may have no
  /// separate projection record; arbitrary missing-address lookup is unchanged.
  pub fn check_owner(&mut self, owner: &Address) -> Result<(), TcError<Anon>> {
    self.last_check = CheckStats::default();
    let source = self.source_for(owner)?.clone();
    let record = source
      .record(owner)
      .map_err(|error| TcError::Other(error.to_string()))?;
    let members = crate::ingress::ingress_anon_block_input(
      &mut self.kernel,
      Input::Artifact(&source),
      record.constant(),
      owner,
    )
    .map_err(TcError::Other)?;
    let primary = members
      .first()
      .ok_or_else(|| TcError::Other("empty owner unit".into()))?;
    self.check_id(primary, &source)
  }

  pub fn check_work(
    &mut self,
    work: &crate::anon_work::AnonWorkItem,
  ) -> Result<(), TcError<Anon>> {
    match work {
      crate::anon_work::AnonWorkItem::Standalone { addr } => {
        self.check_const(addr)
      },
      crate::anon_work::AnonWorkItem::Block { block_addr, .. } => {
        self.check_owner(block_addr)
      },
    }
  }

  /// Check every work item required for a sound verdict on `roots` (including
  /// the binding's support closure via [`ArtifactSource::verdict_closure`]).
  #[cfg(not(target_arch = "riscv64"))]
  pub fn check_verdict(
    &mut self,
    roots: &[Address],
    dependencies: bool,
  ) -> Result<(), TcError<Anon>> {
    let source = self
      .source
      .as_ref()
      .map_err(|error| TcError::Other(error.to_string()))?
      .clone();
    let work = crate::anon_work::build_artifact_work(&source)
      .map_err(TcError::Other)?;
    let selected =
      crate::anon_work::verdict_work(&source, &work, roots, dependencies)
        .map_err(TcError::Other)?;
    for item in &selected {
      self.check_work(item)?;
    }
    Ok(())
  }
  /// Capturing from an mmap retains the loader's immutable-file lifetime
  /// requirement. The anonymous worker never constructs metadata lookups.
  pub fn new(source: &Env) -> Self {
    Self::from_source(ArtifactSource::snapshot(source))
  }
  pub fn from_source(source: Result<ArtifactSource, Error>) -> Self {
    Self::prepare(source, false, make_anon)
  }
}
