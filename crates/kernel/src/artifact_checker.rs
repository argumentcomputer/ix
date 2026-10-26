//! Sealed host workers. Source snapshots are shared; declaration/reduction
//! caches are private to a worker and cannot be seeded by a public KEnv caller.
//! Foundation admission is still pending, so bound role units explicitly
//! refuse and no bound primitive capability is issued by this stage.

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
      Ok(source) if source.binding().is_some() => {
        PrimitiveContext::Bound(source.clone())
      },
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
      let roles = source
        .unit_roles(address)
        .map_err(|error| TcError::Other(error.to_string()))?;
      if let Some(role) = roles.first() {
        // Addresses are available to future validators only as syntax. This
        // stage has no admitted group and cannot reuse a prior cached success.
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
  /// Capturing from an mmap retains the loader's immutable-file lifetime
  /// requirement. The anonymous worker never constructs metadata lookups.
  pub fn new(source: &Env) -> Self {
    Self::from_source(ArtifactSource::snapshot(source))
  }
  pub fn from_source(source: Result<ArtifactSource, Error>) -> Self {
    Self::prepare(source, false, make_anon)
  }
}
