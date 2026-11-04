//! Rust source for native executors of checked Aiur programs.
//!
//! [`native_executor`] turns a checked program into Rust source defining a
//! unit type that implements [`aiur::native::Kernel`]. Its input is the
//! program's bytecode and normalized execution plan only, so the source, and
//! the fingerprint it carries, change exactly when those do. Binding the
//! executor (`PreparedHints::bind_native`) checks that fingerprint, so
//! generated code only ever runs the program it was generated from.
//!
//! The source is meant to be written to a file and compiled with
//! `include!`; it is a sequence of items with no inner attributes.
use aiur::{bytecode::CheckedProgram, field::FieldBackend};

mod native;

/// Rust source for the native executor of `program`, as the public unit
/// type `name`. The first line records the executor's fingerprint
/// ([`aiur::native::native_fingerprint`]).
pub fn native_executor<B: FieldBackend>(
  program: &CheckedProgram<B>,
  name: &str,
) -> Result<String, String> {
  let identifier = name.chars().next().is_some_and(|c| c.is_ascii_alphabetic())
    && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
  if !identifier {
    return Err(format!("executor name {name:?} is not an identifier"));
  }
  let plan = program.native_plan();
  let fingerprint = aiur::native::native_fingerprint(program.program(), &plan);
  let mut source = format!(
    "// Native executor fingerprint {fingerprint} (scheme {}).\n",
    aiur::native::NATIVE_FINGERPRINT_SCHEME
  );
  source.push_str(&native::kernel(&native::Kernel {
    program: program.program(),
    public: true,
    name,
    fingerprint: &fingerprint,
    plan: &plan,
  }));
  Ok(source)
}
