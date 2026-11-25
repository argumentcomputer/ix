//! Advice for programs lowered from IxCC's first-order IR (Lean package
//! `IxCCAiur`, `IxCCAiur/IxCCAiur/Lower.lean`): the quotient and remainder its
//! division helper asks for on channel `ixcc.divmod`. The answer is raw. The
//! lowered program range-checks both words and asserts `q * y + r = x` and
//! `r < y` before it uses them, so a wrong answer here loses the execution
//! and cannot change what is proved.
use crate::{bytecode::Type, field::FieldBackend, hints::HintChannels};

pub const DIVMOD: &str = "ixcc.divmod";

/// `(x, y) -> (x / y, x % y)` on canonical values that fit in a `u64`, with
/// Lean's conventions at `y = 0` (quotient `0`, remainder `x`), as the Lean
/// provider answers (`IxCC.AiurBackend.Hints.dispatcher`).
pub fn register<B: FieldBackend>(
  channels: &mut HintChannels<B::Element>,
  field: B,
) -> Result<(), String> {
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  channels.insert_fixed::<2, 2>(DIVMOD, pair.clone(), pair, move |input| {
    let x = field.try_to_u64(input[0])?;
    let y = field.try_to_u64(input[1])?;
    let q = x.checked_div(y).unwrap_or(0);
    let r = x.checked_rem(y).unwrap_or(x);
    Ok([field.from_u64(q), field.from_u64(r)])
  })
}
