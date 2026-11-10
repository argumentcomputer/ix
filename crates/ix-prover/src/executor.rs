//! Executor selection. With feature `native`, a loaded program runs on the
//! native executor generated from exactly that program, if one is linked
//! (`crates/formal-generated`) and the program has no depth circuits;
//! otherwise, or with `IX_PROVER_EXECUTOR=interpreter`, on the interpreter.
//! Both produce identical records.
use crate::Field;
use aiur::{Execution, ExecutionError, hints::PreparedHints};
use record_pool::RecordReservation;

type Element = <Field as aiur::field::FieldBackend>::Element;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Executor {
  Interpreter,
  #[cfg(feature = "native")]
  Native(Kernel),
}

/// The generated native executors compiled into this prover.
#[cfg(feature = "native")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kernel {
  Ixvm,
  Verifier,
  Aggregation,
}

impl Executor {
  /// The executor for `program`, chosen once when its artifact is loaded.
  pub fn select(program: &crate::Program) -> Result<Self, String> {
    match std::env::var("IX_PROVER_EXECUTOR").as_deref() {
      Ok("interpreter") => return Ok(Self::Interpreter),
      Ok("native") | Err(_) => {},
      Ok(other) => {
        return Err(format!(
          "IX_PROVER_EXECUTOR must be `native` or `interpreter`, not `{other}`"
        ));
      },
    }
    // Generated kernels do not record call heights, which depth circuits
    // read, so a program that records them runs on the interpreter.
    #[cfg(feature = "native")]
    if !program.records_depth()
      && let Some(kernel) = Kernel::matching(program)
    {
      return Ok(Self::Native(kernel));
    }
    #[cfg(not(feature = "native"))]
    let _ = program;
    Ok(Self::Interpreter)
  }

  /// Every executor compiled into this build.
  pub fn available() -> &'static [&'static str] {
    #[cfg(feature = "native")]
    {
      &["interpreter", "native-ixvm", "native-verifier", "native-aggregation"]
    }
    #[cfg(not(feature = "native"))]
    {
      &["interpreter"]
    }
  }

  pub fn name(self) -> &'static str {
    match self {
      Self::Interpreter => "interpreter",
      #[cfg(feature = "native")]
      Self::Native(Kernel::Ixvm) => "native-ixvm",
      #[cfg(feature = "native")]
      Self::Native(Kernel::Verifier) => "native-verifier",
      #[cfg(feature = "native")]
      Self::Native(Kernel::Aggregation) => "native-aggregation",
    }
  }

  /// Execute `entry` under `reservation`, and name the executor that ran.
  /// A kernel that refuses to bind (a map override that disagrees with its
  /// table) leaves the job to the interpreter, which honours overrides.
  pub fn execute(
    self,
    hints: &PreparedHints<'_, Field>,
    entry: &str,
    args: Vec<Element>,
    reservation: &RecordReservation,
  ) -> (Result<Execution<Field>, ExecutionError>, &'static str) {
    #[cfg(feature = "native")]
    if let Self::Native(kernel) = self
      && let Some(result) =
        kernel.execute(hints, entry, args.clone(), reservation)
    {
      return (result, self.name());
    }
    (hints.execute_reserved(entry, args, reservation), Self::Interpreter.name())
  }
}

#[cfg(feature = "native")]
impl Kernel {
  fn matching(program: &crate::Program) -> Option<Self> {
    use aiur::native::Kernel as _;
    let fingerprint = program.native_fingerprint();
    [
      (formal_generated::Ixvm::FINGERPRINT, Self::Ixvm),
      (formal_generated::Verifier::FINGERPRINT, Self::Verifier),
      (formal_generated::Aggregation::FINGERPRINT, Self::Aggregation),
    ]
    .into_iter()
    .find_map(|(k, kernel)| (k == fingerprint).then_some(kernel))
  }

  fn execute(
    self,
    hints: &PreparedHints<'_, Field>,
    entry: &str,
    args: Vec<Element>,
    reservation: &RecordReservation,
  ) -> Option<Result<Execution<Field>, ExecutionError>> {
    fn run<K: aiur::native::Kernel>(
      hints: &PreparedHints<'_, Field>,
      entry: &str,
      args: Vec<Element>,
      reservation: &RecordReservation,
    ) -> Option<Result<Execution<Field>, ExecutionError>> {
      let native = hints.bind_native::<K>().ok()?;
      Some(native.execute_reserved(entry, args, reservation))
    }
    match self {
      Self::Ixvm => {
        run::<formal_generated::Ixvm>(hints, entry, args, reservation)
      },
      Self::Verifier => {
        run::<formal_generated::Verifier>(hints, entry, args, reservation)
      },
      Self::Aggregation => {
        run::<formal_generated::Aggregation>(hints, entry, args, reservation)
      },
    }
  }
}
