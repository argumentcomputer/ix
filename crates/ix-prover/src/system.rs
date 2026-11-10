//! Rust-owned programs, proving systems and the per-command registry that
//! shares them.
//!
//! A [`Program`] is one checked application revision: its bytecode, trace
//! artifact, trace plan and executor. A [`System`] adds explicit STARK
//! parameters and the device-independent verification data derived from
//! them: the verifying backend and key. Proving backends on a device belong
//! to a lane and are built from a system by [`System::prover`].
//!
//! Plans and backends read their program through [`aiur::shared::Shared`]:
//! a handle holds them with owned `Arc`s, so nothing borrows across calls
//! and the backing data is released with the last handle.
use std::{
  collections::HashMap,
  sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
  },
};

use aiur::trace::{
  TraceArtifact, TracePlan,
  stark::{Backend, BatchProof, Parameters},
};
use multi_stark::{p3_field::PrimeField64, types::Val};

use crate::{Field, executor::Executor};

static PROGRAMS: AtomicUsize = AtomicUsize::new(0);
static PLANS: AtomicUsize = AtomicUsize::new(0);
static SYSTEMS: AtomicUsize = AtomicUsize::new(0);
static PROVERS: AtomicUsize = AtomicUsize::new(0);

/// How many objects this process has constructed, for checking that repeated
/// operations reuse their handles.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counters {
  /// Programs checked from an artifact.
  pub programs: usize,
  /// Trace plans built from a program.
  pub plans: usize,
  /// Systems prepared: verifying backends and keys.
  pub systems: usize,
  /// Proving backends built for a lane or a single-claim scope.
  pub provers: usize,
}

pub fn counters() -> Counters {
  Counters {
    programs: PROGRAMS.load(Ordering::Relaxed),
    plans: PLANS.load(Ordering::Relaxed),
    systems: SYSTEMS.load(Ordering::Relaxed),
    provers: PROVERS.load(Ordering::Relaxed),
  }
}

type CheckedProgram = crate::Program;
type Plan = TracePlan<'static, Field>;
pub(crate) type Prover = Backend<'static, 'static, Field>;

struct ProgramInner {
  checked: Arc<CheckedProgram>,
  trace: TraceArtifact,
  plan: Mutex<Option<Arc<Plan>>>,
  executor: Executor,
  identity: [u8; 32],
}

/// A checked program with its trace artifact. Cloning shares it.
#[derive(Clone)]
pub struct Program(Arc<ProgramInner>);

impl Program {
  /// Check `program` against the Goldilocks field, have its execution
  /// record the call heights the trace's depth circuits read, check its
  /// trace artifact by building the trace plan, and select its executor.
  /// The handle exists only once all of that succeeded. Its identity is the
  /// BLAKE3 digest of the artifact it was decoded from
  /// ([`aiur::artifact::Digest`]); programs with the same identity are
  /// interchangeable.
  pub fn new(
    program: aiur::Program,
    trace: TraceArtifact,
    identity: aiur::artifact::Digest,
  ) -> Result<Self, String> {
    let identity = identity.0;
    let mut checked = program.check_field::<Val>()?;
    checked.track_depth(&trace)?;
    let checked = Arc::new(checked);
    let plan = Arc::new(TracePlan::new(Arc::clone(&checked), trace.clone())?);
    PLANS.fetch_add(1, Ordering::Relaxed);
    let executor = Executor::select(&checked)?;
    PROGRAMS.fetch_add(1, Ordering::Relaxed);
    Ok(Self(Arc::new(ProgramInner {
      checked,
      trace,
      plan: Mutex::new(Some(plan)),
      executor,
      identity,
    })))
  }

  pub fn checked(&self) -> &CheckedProgram {
    &self.0.checked
  }

  pub fn trace(&self) -> &TraceArtifact {
    &self.0.trace
  }

  pub fn identity(&self) -> &[u8; 32] {
    &self.0.identity
  }

  pub(crate) fn executor(&self) -> Executor {
    self.0.executor
  }

  /// The executor this program runs on: `interpreter`, or the name of the
  /// linked native executor generated from exactly this program.
  pub fn executor_name(&self) -> &'static str {
    self.0.executor.name()
  }

  /// The fingerprint a native executor generated from this program carries.
  pub fn native_fingerprint(&self) -> &str {
    self.0.checked.native_fingerprint()
  }

  /// The trace plan, built on first use and shared afterwards.
  pub fn plan(&self) -> Result<Arc<Plan>, String> {
    let mut slot =
      self.0.plan.lock().map_err(|_| "trace plan lock poisoned")?;
    if let Some(plan) = &*slot {
      return Ok(Arc::clone(plan));
    }
    let plan = Arc::new(TracePlan::new(
      Arc::clone(&self.0.checked),
      self.0.trace.clone(),
    )?);
    PLANS.fetch_add(1, Ordering::Relaxed);
    *slot = Some(Arc::clone(&plan));
    Ok(plan)
  }

  /// The first entry point's name.
  pub fn first_entry(&self) -> Result<&str, String> {
    Ok(
      &self
        .0
        .checked
        .program()
        .entries
        .first()
        .ok_or("program has no entrypoint")?
        .name,
    )
  }
}

/// The STARK parameters a system is prepared for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ProtocolParameters {
  pub log_blowup: usize,
  pub num_queries: usize,
  pub commit_proof_of_work_bits: usize,
  pub query_proof_of_work_bits: usize,
}

impl Default for ProtocolParameters {
  fn default() -> Self {
    Parameters::default().into()
  }
}

impl From<ProtocolParameters> for Parameters {
  fn from(p: ProtocolParameters) -> Self {
    Self {
      log_blowup: p.log_blowup,
      num_queries: p.num_queries,
      commit_proof_of_work_bits: p.commit_proof_of_work_bits,
      query_proof_of_work_bits: p.query_proof_of_work_bits,
    }
  }
}

impl From<Parameters> for ProtocolParameters {
  fn from(p: Parameters) -> Self {
    Self {
      log_blowup: p.log_blowup,
      num_queries: p.num_queries,
      commit_proof_of_work_bits: p.commit_proof_of_work_bits,
      query_proof_of_work_bits: p.query_proof_of_work_bits,
    }
  }
}

struct SystemInner {
  program: Program,
  parameters: ProtocolParameters,
  plan: Arc<Plan>,
  verifier: Prover,
  key: Vec<u8>,
}

/// A program under explicit STARK parameters with its verifying backend and
/// key. Verification needs no CUDA context. Cloning shares it.
#[derive(Clone)]
pub struct System(Arc<SystemInner>);

/// How claims address a system: its verifying key, the entry's function
/// index and the call channel.
pub struct Identity {
  pub key: Vec<u8>,
  pub function_index: u64,
  pub call_channel: u64,
}

impl System {
  pub fn prepare(
    program: &Program,
    parameters: ProtocolParameters,
  ) -> Result<Self, String> {
    let plan = program.plan()?;
    let verifier =
      Backend::for_batch_verification(Arc::clone(&plan), parameters.into())?;
    let key = verifier.verifying_key_bytes()?;
    SYSTEMS.fetch_add(1, Ordering::Relaxed);
    Ok(Self(Arc::new(SystemInner {
      program: program.clone(),
      parameters,
      plan,
      verifier,
      key,
    })))
  }

  pub fn program(&self) -> &Program {
    &self.0.program
  }

  pub fn parameters(&self) -> ProtocolParameters {
    self.0.parameters
  }

  pub fn key(&self) -> &[u8] {
    &self.0.key
  }

  pub(crate) fn verifier(&self) -> &Prover {
    &self.0.verifier
  }

  /// The identity of `entry`'s claims, from a claim over zero arguments.
  pub fn identity(
    &self,
    entry: &str,
    arity: usize,
  ) -> Result<Identity, String> {
    let claim =
      self.0.verifier.claim(entry, &vec![Val::default(); arity], &[])?;
    let [call_channel, function_index, ..] = claim[..] else {
      return Err("claim lacks its call namespace".into());
    };
    Ok(Identity {
      key: self.0.key.clone(),
      function_index: function_index.as_canonical_u64(),
      call_channel: call_channel.as_canonical_u64(),
    })
  }

  /// Verify the raw batch proof `bytes` of `entry(args)` on the CPU. The
  /// bytes must be the proof's canonical encoding. Returns the shard count.
  pub fn verify(
    &self,
    entry: &str,
    args: &[u64],
    bytes: &[u8],
  ) -> Result<usize, String> {
    use aiur::field::FieldBackend;
    let args = self.0.program.checked().field().decode(args)?;
    let proof = BatchProof::from_bytes(bytes).map_err(|e| e.to_string())?;
    if proof.to_bytes().map_err(|e| e.to_string())? != bytes {
      return Err("noncanonical or trailing proof bytes".into());
    }
    self.0.verifier.verify_batch(entry, &args, &[], &proof)?;
    Ok(proof.proofs.len())
  }

  /// A proving backend on `device` (the CPU for `None`) whose key must equal
  /// the system's. Each lane or single-claim scope owns its own.
  pub fn prover(&self, device: Option<i32>) -> Result<Prover, String> {
    let prover = Backend::for_batch_on_device(
      Arc::clone(&self.0.plan),
      self.0.parameters.into(),
      device,
    )?;
    PROVERS.fetch_add(1, Ordering::Relaxed);
    if prover.verifying_key_bytes()? != self.0.key {
      return Err("the proving key differs from the system's".into());
    }
    Ok(prover)
  }
}

/// One entry, initialized once even when requested concurrently.
type Slot<T> = Arc<Mutex<Option<T>>>;
type SystemKey = ([u8; 32], ProtocolParameters);

fn slot<K: std::hash::Hash + Eq, T>(
  map: &Mutex<HashMap<K, Slot<T>>>,
  key: K,
) -> Result<Slot<T>, String> {
  let mut map = map.lock().map_err(|_| "registry lock poisoned")?;
  Ok(Arc::clone(map.entry(key).or_default()))
}

fn get_or_init<T: Clone>(
  slot: &Slot<T>,
  init: impl FnOnce() -> Result<T, String>,
) -> Result<T, String> {
  let mut value = slot.lock().map_err(|_| "registry entry lock poisoned")?;
  if let Some(value) = &*value {
    return Ok(value.clone());
  }
  let made = init()?;
  *value = Some(made.clone());
  Ok(made)
}

/// The programs and systems one command selected. Each is constructed once;
/// concurrent requests for the same entry wait for the first. A failed
/// construction leaves the entry empty. The registry belongs to the command
/// that created it and is released with it.
#[derive(Default)]
pub struct Registry {
  programs: Mutex<HashMap<String, Slot<Program>>>,
  systems: Mutex<HashMap<SystemKey, Slot<System>>>,
}

impl Registry {
  /// The program registered under `key`, made by `make` the first time.
  pub fn program(
    &self,
    key: &str,
    make: impl FnOnce() -> Result<Program, String>,
  ) -> Result<Program, String> {
    get_or_init(&slot(&self.programs, key.to_owned())?, make)
  }

  /// `program` under `parameters`.
  pub fn system(
    &self,
    program: &Program,
    parameters: ProtocolParameters,
  ) -> Result<System, String> {
    let entry = slot(&self.systems, (*program.identity(), parameters))?;
    get_or_init(&entry, || System::prepare(program, parameters))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn registry_entries_initialize_once_and_retry_after_failure() {
    let entry: Slot<usize> = Arc::default();
    let made = AtomicUsize::new(0);
    std::thread::scope(|scope| {
      for _ in 0..8 {
        scope.spawn(|| {
          let value = get_or_init(&entry, || {
            std::thread::sleep(std::time::Duration::from_millis(20));
            Ok(made.fetch_add(1, Ordering::SeqCst) + 41)
          })
          .unwrap();
          assert_eq!(value, 41);
        });
      }
    });
    assert_eq!(made.load(Ordering::SeqCst), 1);
    let failing: Slot<usize> = Arc::default();
    assert!(get_or_init(&failing, || Err("no".into())).is_err());
    assert_eq!(get_or_init(&failing, || Ok(7)).unwrap(), 7);
    let map: Mutex<HashMap<String, Slot<u8>>> = Mutex::default();
    let a = slot(&map, "a".to_owned()).unwrap();
    let b = slot(&map, "a".to_owned()).unwrap();
    assert!(Arc::ptr_eq(&a, &b));
  }
}
