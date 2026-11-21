//! Resource modes of an Ixon record (mirrors `IxC/Ixon/Types/Modes.lean`).
//!
//! The modes a record gives its binders, its `let`s, its constructors' fields
//! and its definitions. Each type is exactly its legal set: no combination of
//! fields is excluded by a side condition. Each has a wire code, a bijection
//! between the type and its legal codes (`of_code(m.to_code()) == Some(m)`;
//! every other code decodes to `None`), with the default at code 0. Every
//! binder of Lean source has the default mode, so a plain Lean record writes
//! only zero codes.
//!
//! Where the codes go on the wire:
//! - a `Lam` or `All` binder's mode: the high five bits of the binder's node
//!   in the record's binder-data section ([`AllMode`]: the bound variable's
//!   mode and the mode of the result of the binder's own arrow, for a `Lam` as
//!   for an `All`);
//! - a `Let`'s mode: its header's TagN value, `non_dep + 2 * LetMode::to_code`
//!   ([`LetMode::header`]);
//! - a constructor's field modes: a flag bit in its first byte, then one byte
//!   per field ([`FieldModes`]);
//! - a definition's assertions: the high nibble of its kind and safety byte
//!   ([`DefAsserts`]; the default on a theorem).
//!
//! Modes are data of the record, hashed into its address. Kernel terms carry
//! none.

/// A binder's usage: any number of times (the default), at most once, or
/// never at run time.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Usage {
  #[default]
  Many,
  Once,
  Erased,
}

/// The mode of a bound variable: a `Lam` or `All` binder's input, a value
/// `Let`'s. Usage `many` with any ownership and locality, usage `once`
/// (shared) with any locality, or `erased`: seven values. `Many` (shared and
/// unrestricted) is the default.
///
/// Code: bit 0 borrowed, bit 1 unique or erased, bit 2 once or erased, so 0
/// to 6 in the order of the variants; 7 (an erased binder that is borrowed)
/// is no mode.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BinderMode {
  /// Usage `many`, shared, unrestricted: the default (code 0).
  #[default]
  Many = 0,
  /// Usage `many`, shared, lent for the binder's scope (code 1).
  Borrowed = 1,
  /// Usage `many`, unaliased (code 2).
  Unique = 2,
  /// Usage `many`, unaliased and lent (code 3).
  UniqueBorrowed = 3,
  /// Usage at most once, shared (code 4).
  Once = 4,
  /// Usage at most once, shared and lent (code 5).
  OnceBorrowed = 5,
  /// Absent at run time (code 6).
  Erased = 6,
}

impl BinderMode {
  /// Every mode, in code order.
  pub const ALL: [Self; 7] = [
    Self::Many,
    Self::Borrowed,
    Self::Unique,
    Self::UniqueBorrowed,
    Self::Once,
    Self::OnceBorrowed,
    Self::Erased,
  ];

  pub const fn usage(self) -> Usage {
    match self {
      Self::Many | Self::Borrowed | Self::Unique | Self::UniqueBorrowed => {
        Usage::Many
      },
      Self::Once | Self::OnceBorrowed => Usage::Once,
      Self::Erased => Usage::Erased,
    }
  }

  pub const fn is_unique(self) -> bool {
    matches!(self, Self::Unique | Self::UniqueBorrowed)
  }

  pub const fn is_borrowed(self) -> bool {
    matches!(self, Self::Borrowed | Self::UniqueBorrowed | Self::OnceBorrowed)
  }

  pub const fn to_code(self) -> u8 {
    self as u8
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    match code {
      0 => Some(Self::Many),
      1 => Some(Self::Borrowed),
      2 => Some(Self::Unique),
      3 => Some(Self::UniqueBorrowed),
      4 => Some(Self::Once),
      5 => Some(Self::OnceBorrowed),
      6 => Some(Self::Erased),
      _ => None,
    }
  }
}

/// The mode of a binder's result (the result of its arrow: an `All`'s
/// codomain, a `Lam`'s body): its ownership and locality. `Shared` (and
/// unrestricted) is the default. Code: bit 0 borrowed, bit 1 unique, as the
/// low two bits of a [`BinderMode`] of usage `many`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ResultMode {
  /// Shared, unrestricted: the default (code 0).
  #[default]
  Shared = 0,
  /// Shared, lent (code 1).
  Borrowed = 1,
  /// Unaliased (code 2).
  Unique = 2,
  /// Unaliased and lent (code 3).
  UniqueBorrowed = 3,
}

impl ResultMode {
  /// Every mode, in code order.
  pub const ALL: [Self; 4] =
    [Self::Shared, Self::Borrowed, Self::Unique, Self::UniqueBorrowed];

  pub const fn is_unique(self) -> bool {
    matches!(self, Self::Unique | Self::UniqueBorrowed)
  }

  pub const fn is_borrowed(self) -> bool {
    matches!(self, Self::Borrowed | Self::UniqueBorrowed)
  }

  pub const fn to_code(self) -> u8 {
    self as u8
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    match code {
      0 => Some(Self::Shared),
      1 => Some(Self::Borrowed),
      2 => Some(Self::Unique),
      3 => Some(Self::UniqueBorrowed),
      _ => None,
    }
  }
}

/// The mode of a `Lam` or `All` binder: its bound variable's (`input`) and
/// its arrow's result's (`result`), 7 × 4 = 28 values. A `Lam`'s result is
/// the result mode of its own arrow, so a definition's `Lam` telescope agrees
/// with its type's `All` telescope node for node. Code (five bits): the
/// input's code, plus 8 times the result's; the codes whose low three bits are
/// 7 are no mode.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct AllMode {
  pub input: BinderMode,
  pub result: ResultMode,
}

impl AllMode {
  pub const fn new(input: BinderMode, result: ResultMode) -> Self {
    Self { input, result }
  }

  pub const fn to_code(self) -> u8 {
    self.input.to_code() | (self.result.to_code() << 3)
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    if code >= 32 {
      return None;
    }
    let Some(input) = BinderMode::of_code(code & 7) else { return None };
    let Some(result) = ResultMode::of_code(code >> 3) else { return None };
    Some(Self { input, result })
  }

  /// Whether this is the default mode (code 0).
  pub fn is_default(self) -> bool {
    self == Self::default()
  }
}

/// The mode of a `Let`: a value `Let` binds its variable at a
/// [`BinderMode`], and a `Borrow` lends a shared value for the `Let`'s body
/// (its variable is `Borrowed`). Eight values, all legal codes 0 to 7: a value
/// `Let`'s code is its mode's, a `Borrow`'s is 7. `Value(Many)` is the
/// default.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LetMode {
  Value(BinderMode),
  Borrow,
}

impl Default for LetMode {
  fn default() -> Self {
    Self::Value(BinderMode::Many)
  }
}

impl LetMode {
  /// The mode of the bound variable.
  pub const fn binder_mode(self) -> BinderMode {
    match self {
      Self::Value(m) => m,
      Self::Borrow => BinderMode::Borrowed,
    }
  }

  pub const fn to_code(self) -> u8 {
    match self {
      Self::Value(m) => m.to_code(),
      Self::Borrow => 7,
    }
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    if code == 7 {
      return Some(Self::Borrow);
    }
    match BinderMode::of_code(code) {
      Some(m) => Some(Self::Value(m)),
      None => None,
    }
  }

  /// The `Let` header's TagN value: `non_dep` in bit 0, the mode's code above
  /// it, so below 16; a default `Let`'s is 0 or 1 and its header one byte.
  pub fn header(non_dep: bool, mode: Self) -> u64 {
    u64::from(non_dep) | (u64::from(mode.to_code()) << 1)
  }

  /// The `non_dep` flag and mode of a `Let` header's TagN value; `None` from
  /// 16 on.
  pub fn of_header(header: u64) -> Option<(bool, Self)> {
    if header >= 16 {
      return None;
    }
    let mode = Self::of_code(u8::try_from(header >> 1).ok()?)?;
    Some((header & 1 == 1, mode))
  }
}

/// The mode of a constructor's field: `Inherited` (the default: owned or lent
/// with its container) or `Shared` (an ordinary counted reference, excused
/// from its container's uniqueness). An erased field is erased by its binder's
/// mode in the constructor's type, and has no field mode of its own.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FieldMode {
  #[default]
  Inherited = 0,
  Shared = 1,
}

impl FieldMode {
  pub const fn to_code(self) -> u8 {
    self as u8
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    match code {
      0 => Some(Self::Inherited),
      1 => Some(Self::Shared),
      _ => None,
    }
  }
}

/// The field modes of a constructor with `n` fields (`Ixon.FieldModes n`):
/// every field `Inherited` (the default, no bytes on the wire), or exactly
/// `n` modes of which at least one is `Shared` (the constructor's flag bit
/// set, then one byte per field).
///
/// The Lean type carries `n` and the "some shared" rule in its type; here a
/// `Listed` value is well formed when it has the constructor's `fields`
/// entries and one of them is `Shared` ([`FieldModes::listed`] builds only
/// such values, and the decoder produces only such values).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum FieldModes {
  #[default]
  Inherited,
  Listed(Vec<FieldMode>),
}

impl FieldModes {
  /// `modes` as the field modes of a constructor with `n` fields: `Listed`
  /// when there are `n` of them and one is `Shared` (`FieldModes.listed?`).
  pub fn listed(modes: Vec<FieldMode>, n: u64) -> Option<Self> {
    if Self::lists(&modes, n) { Some(Self::Listed(modes)) } else { None }
  }

  /// `modes` as field modes: `Listed` when there are `n` of them and one is
  /// `Shared`, otherwise `Inherited` (`FieldModes.ofArray`).
  pub fn of_vec(modes: Vec<FieldMode>, n: u64) -> Self {
    Self::listed(modes, n).unwrap_or_default()
  }

  /// The listed modes; none for `Inherited`.
  pub fn as_slice(&self) -> &[FieldMode] {
    match self {
      Self::Inherited => &[],
      Self::Listed(modes) => modes,
    }
  }

  /// The mode of field `i` (`Inherited` past the last field).
  pub fn get(&self, i: usize) -> FieldMode {
    self.as_slice().get(i).copied().unwrap_or_default()
  }

  /// Whether every field is `Inherited` (the flag bit clear).
  pub fn is_inherited(&self) -> bool {
    matches!(self, Self::Inherited)
  }

  /// Whether this is well formed for a constructor with `n` fields:
  /// `Inherited`, or `n` modes of which one is `Shared`.
  pub fn well_formed(&self, n: u64) -> bool {
    match self {
      Self::Inherited => true,
      Self::Listed(modes) => Self::lists(modes, n),
    }
  }

  /// Whether `modes` are `n` modes of which one is `Shared`.
  fn lists(modes: &[FieldMode], n: u64) -> bool {
    usize::try_from(n).is_ok_and(|n| n == modes.len())
      && modes.contains(&FieldMode::Shared)
  }
}

/// What a definition asserts about its allocation: nothing (the default), no
/// reference-count operation, or no allocation at all (which implies no
/// reference-count operation).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AllocAssert {
  #[default]
  Unrestricted = 0,
  NoRc = 1,
  NoAlloc = 2,
}

impl AllocAssert {
  /// Every assertion, in code order.
  pub const ALL: [Self; 3] = [Self::Unrestricted, Self::NoRc, Self::NoAlloc];

  pub const fn to_code(self) -> u8 {
    self as u8
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    match code {
      0 => Some(Self::Unrestricted),
      1 => Some(Self::NoRc),
      2 => Some(Self::NoAlloc),
      _ => None,
    }
  }
}

/// A definition's assertions: its allocation, and whether its call graph has
/// bounded stack depth. Six values; the default asserts nothing. Code (four
/// bits): the allocation's code, plus 4 for a bounded stack; a code of 8 or
/// more, or an allocation code of 3, is no `DefAsserts`. A theorem asserts
/// nothing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct DefAsserts {
  pub alloc: AllocAssert,
  pub bounded_stack: bool,
}

impl DefAsserts {
  pub const fn to_code(self) -> u8 {
    let stack = if self.bounded_stack { 4 } else { 0 };
    self.alloc.to_code() | stack
  }

  pub const fn of_code(code: u8) -> Option<Self> {
    if code >= 8 {
      return None;
    }
    match AllocAssert::of_code(code & 3) {
      Some(alloc) => Some(Self { alloc, bounded_stack: code & 4 == 4 }),
      None => None,
    }
  }

  /// Whether this asserts nothing (code 0).
  pub fn is_default(self) -> bool {
    self == Self::default()
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  impl Arbitrary for BinderMode {
    fn arbitrary(g: &mut Gen) -> Self {
      *g.choose(&Self::ALL).unwrap()
    }
  }

  impl Arbitrary for ResultMode {
    fn arbitrary(g: &mut Gen) -> Self {
      *g.choose(&Self::ALL).unwrap()
    }
  }

  impl Arbitrary for AllMode {
    fn arbitrary(g: &mut Gen) -> Self {
      // Half the nodes at the default mode, as in compiled records.
      if bool::arbitrary(g) {
        Self::default()
      } else {
        Self::new(BinderMode::arbitrary(g), ResultMode::arbitrary(g))
      }
    }
  }

  impl Arbitrary for LetMode {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 {
        0 => Self::default(),
        1 => Self::Borrow,
        _ => Self::Value(BinderMode::arbitrary(g)),
      }
    }
  }

  impl Arbitrary for FieldMode {
    fn arbitrary(g: &mut Gen) -> Self {
      if bool::arbitrary(g) { Self::Shared } else { Self::Inherited }
    }
  }

  impl Arbitrary for DefAsserts {
    fn arbitrary(g: &mut Gen) -> Self {
      Self {
        alloc: *g.choose(&AllocAssert::ALL).unwrap(),
        bounded_stack: bool::arbitrary(g),
      }
    }
  }

  /// Well-formed field modes for a constructor with `n` fields.
  pub fn gen_field_modes(g: &mut Gen, n: u64) -> FieldModes {
    if n == 0 || bool::arbitrary(g) {
      return FieldModes::Inherited;
    }
    let mut modes: Vec<FieldMode> =
      (0..n).map(|_| FieldMode::arbitrary(g)).collect();
    let i = usize::arbitrary(g) % modes.len();
    modes[i] = FieldMode::Shared;
    FieldModes::Listed(modes)
  }

  /// Every code of every mode type: the legal ones round-trip, the rest are
  /// refused, and the default is code 0.
  #[test]
  fn codes_are_bijections_onto_their_legal_sets() {
    for code in 0..=u8::MAX {
      let binder = BinderMode::of_code(code);
      assert_eq!(binder.is_some(), code < 7, "binder {code}");
      if let Some(m) = binder {
        assert_eq!(m.to_code(), code);
      }
      let result = ResultMode::of_code(code);
      assert_eq!(result.is_some(), code < 4, "result {code}");
      if let Some(m) = result {
        assert_eq!(m.to_code(), code);
      }
      let all = AllMode::of_code(code);
      assert_eq!(all.is_some(), code < 32 && code & 7 != 7, "all {code}");
      if let Some(m) = all {
        assert_eq!(m.to_code(), code);
      }
      let let_mode = LetMode::of_code(code);
      assert_eq!(let_mode.is_some(), code < 8, "let {code}");
      if let Some(m) = let_mode {
        assert_eq!(m.to_code(), code);
      }
      let field = FieldMode::of_code(code);
      assert_eq!(field.is_some(), code < 2, "field {code}");
      if let Some(m) = field {
        assert_eq!(m.to_code(), code);
      }
      let alloc = AllocAssert::of_code(code);
      assert_eq!(alloc.is_some(), code < 3, "alloc {code}");
      let asserts = DefAsserts::of_code(code);
      assert_eq!(
        asserts.is_some(),
        code < 8 && code & 3 != 3,
        "asserts {code}"
      );
      if let Some(a) = asserts {
        assert_eq!(a.to_code(), code);
      }
    }
    assert_eq!(BinderMode::default().to_code(), 0);
    assert_eq!(ResultMode::default().to_code(), 0);
    assert_eq!(AllMode::default().to_code(), 0);
    assert_eq!(LetMode::default().to_code(), 0);
    assert_eq!(FieldMode::default().to_code(), 0);
    assert_eq!(DefAsserts::default().to_code(), 0);
    // 28 binder modes, 8 let modes, 6 assertions.
    assert_eq!((0..=u8::MAX).filter_map(AllMode::of_code).count(), 28);
    assert_eq!((0..=u8::MAX).filter_map(LetMode::of_code).count(), 8);
    assert_eq!((0..=u8::MAX).filter_map(DefAsserts::of_code).count(), 6);
  }

  #[test]
  fn let_headers_are_the_sixteen_values_below_sixteen() {
    for header in 0..64u64 {
      match LetMode::of_header(header) {
        Some((non_dep, mode)) => {
          assert!(header < 16);
          assert_eq!(LetMode::header(non_dep, mode), header);
        },
        None => assert!(header >= 16),
      }
    }
    assert_eq!(LetMode::of_header(u64::MAX), None);
    assert_eq!(LetMode::header(false, LetMode::default()), 0);
    assert_eq!(LetMode::header(true, LetMode::default()), 1);
    assert_eq!(LetMode::header(true, LetMode::Borrow), 15);
  }

  #[test]
  fn accessors() {
    assert_eq!(BinderMode::OnceBorrowed.usage(), Usage::Once);
    assert_eq!(BinderMode::Erased.usage(), Usage::Erased);
    assert_eq!(BinderMode::UniqueBorrowed.usage(), Usage::Many);
    assert!(BinderMode::UniqueBorrowed.is_unique());
    assert!(BinderMode::UniqueBorrowed.is_borrowed());
    assert!(!BinderMode::Once.is_borrowed());
    assert_eq!(LetMode::Borrow.binder_mode(), BinderMode::Borrowed);
    assert!(FieldModes::listed(vec![FieldMode::Inherited], 1).is_none());
    assert!(FieldModes::listed(vec![FieldMode::Shared], 2).is_none());
    let listed = FieldModes::listed(vec![FieldMode::Shared], 1).unwrap();
    assert_eq!(listed.get(0), FieldMode::Shared);
    assert_eq!(listed.get(1), FieldMode::Inherited);
    assert_eq!(FieldModes::of_vec(vec![], 0), FieldModes::Inherited);
  }
}
