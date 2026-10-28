//! Optional reductions enabled by checked role specifications.
//!
//! A bound source can enable the String and BitVec families after semantic
//! admission. Each reducer also checks admission of its own head and stays
//! within the input shapes covered by that head's equations. Decision-procedure
//! proof construction and the Nat offset/linear-recursion shortcuts remain
//! disabled in production. Unbound checking retains ordinary delta and iota.

/// One group of optional reductions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExtraReduction {
  /// `Nat.decEq`, `Nat.decLe` and `Nat.decLt` on literals, which build
  /// `Decidable.isTrue`/`isFalse` from four `Nat` lemmas, and the literal
  /// normalisation of `Int.decEq`, `Int.decLe` and `Int.decLt` arguments.
  Decidable,
  /// `BitVec.toNat (BitVec.ofNat w n)` and `BitVec.ult` on literals.
  BitVec,
  /// `String` operations on literals: the `String.ofList` collapse,
  /// `append`, `decEq`, `back`, `utf8ByteSize`, and `toByteArray ""`.
  String,
  /// The `Nat` offset forms, one unit: `x + k`, `x / k` and `x % k` kept
  /// stuck in WHNF, the recursor-major cleanup of `x + (k+1)` to
  /// `Nat.succ (x + k)` that the stuck forms rely on, and the
  /// definitional-equality strip of a shared `+ k`. The stuck forms without
  /// the cleanup leave recursors stuck on offset majors.
  NatOffsets,
  /// The collapse of `succ`-step `Nat.rec` applications on a literal major.
  NatRecLinear,
}

impl ExtraReduction {
  const fn bit(self) -> u8 {
    match self {
      ExtraReduction::Decidable => 1,
      ExtraReduction::BitVec => 1 << 1,
      ExtraReduction::String => 1 << 2,
      ExtraReduction::NatOffsets => 1 << 3,
      ExtraReduction::NatRecLinear => 1 << 4,
    }
  }
}

/// The groups of [`ExtraReduction`] a type checker takes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ExtraReductions(u8);

impl ExtraReductions {
  /// No optional reductions, including the unbound production setting.
  pub const NONE: Self = ExtraReductions(0);

  /// Every group, for unit tests of the reducers.
  #[cfg(test)]
  pub(crate) const ALL: Self = ExtraReductions(0b1_1111);

  #[cfg(not(target_arch = "riscv64"))]
  pub(crate) fn from_admitted(
    admitted: impl Fn(ixon::role_table::Role) -> bool,
  ) -> Self {
    use ixon::role_table::Role;
    let mut bits = 0;
    if admitted(Role::BitVecToNat) {
      bits |= ExtraReduction::BitVec.bit();
    }
    if [
      Role::StringAppend,
      Role::StringDecEq,
      Role::StringBack,
      Role::StringUtf8ByteSize,
      Role::StringToByteArray,
    ]
    .into_iter()
    .any(admitted)
    {
      bits |= ExtraReduction::String.bit();
    }
    Self(bits)
  }

  pub fn allows(self, group: ExtraReduction) -> bool {
    self.0 & group.bit() != 0
  }
}
