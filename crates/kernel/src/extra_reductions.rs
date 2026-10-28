//! Reductions outside the certified checker's specification set.
//!
//! The certified checker (IxC) specifies Lean's kernel rules plus a fixed set
//! of primitive roles: the `Nat` basis with literals and fifteen operations on
//! literals, `Eq`, `Quot`, and the string-literal support. The groups below
//! are further shortcuts that this kernel implements. Each is sound, but none
//! is specified there, so the kernel does not take them: every group is off
//! and the terms they would shortcut reduce by ordinary delta and iota. A
//! group returns once the certified checker specifies it. Until then only
//! unit tests of the reducers themselves turn them on.

/// One group of reductions outside the certified specification set.
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
  /// No group: the production setting.
  pub const NONE: Self = ExtraReductions(0);

  /// Every group, for unit tests of the reducers.
  #[cfg(test)]
  pub(crate) const ALL: Self = ExtraReductions(0b1_1111);

  pub fn allows(self, group: ExtraReduction) -> bool {
    self.0 & group.bit() != 0
  }
}
