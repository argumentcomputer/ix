//! Canonical unsigned field transport values, independent of field arithmetic.
//!
//! A word is four little-endian `u64` limbs in memory. Its wire encoding is a
//! TagN limb count followed by the nonempty low-limb prefix, also as TagN
//! integers. The most significant encoded limb must be nonzero; zero has an
//! empty prefix. Modulus and field-value bounds are checked separately.
use crate::ixon::{Reader, Writer};
use serde::{Deserialize, Serialize};
use std::{cmp::Ordering, fmt};

#[derive(
  Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize,
)]
#[serde(transparent)]
pub struct FieldWord([u64; 4]);

impl FieldWord {
  pub const ZERO: Self = Self([0; 4]);
  pub const ONE: Self = Self([1, 0, 0, 0]);

  pub const fn from_limbs_le(limbs: [u64; 4]) -> Self {
    Self(limbs)
  }

  pub const fn limbs_le(&self) -> &[u64; 4] {
    &self.0
  }

  pub const fn to_limbs_le(self) -> [u64; 4] {
    self.0
  }

  /// Narrow only values represented exactly by one word; no truncation or
  /// field reduction is performed at this transport boundary.
  pub fn to_u64(self) -> Result<u64, String> {
    if self.0[1..].iter().any(|&limb| limb != 0) {
      Err(format!("field word {self} exceeds u64"))
    } else {
      Ok(self.0[0])
    }
  }

  /// The representation already bounds the value below `2^256`. This checks
  /// only the lower modulus bound; it makes no primality claim.
  pub fn validate_modulus(self) -> Result<(), String> {
    if self < Self::from(2) {
      Err("field modulus must be at least two".into())
    } else {
      Ok(())
    }
  }

  pub fn validate_field(self, modulus: Self) -> Result<(), String> {
    modulus.validate_modulus()?;
    if self < modulus {
      Ok(())
    } else {
      Err(format!(
        "noncanonical field word {self} is not below modulus {modulus}"
      ))
    }
  }

  pub fn write(self, writer: &mut Writer) {
    let count = self.0.iter().rposition(|&limb| limb != 0).map_or(0, |i| i + 1);
    writer.usize(count);
    for &limb in &self.0[..count] {
      writer.nat(limb);
    }
  }

  pub fn read(reader: &mut Reader<'_>) -> Result<Self, String> {
    let count = reader.nat()?;
    if count > 4 {
      return Err(
        reader.error(format!("field word limb count {count} exceeds four")),
      );
    }
    let count = usize::try_from(count).map_err(|error| reader.error(error))?;
    let mut limbs = [0; 4];
    for limb in &mut limbs[..count] {
      *limb = reader.nat()?;
    }
    if count != 0 && limbs[count - 1] == 0 {
      return Err(reader.error("noncanonical field word has a zero high limb"));
    }
    Ok(Self(limbs))
  }

  pub fn read_modulus(reader: &mut Reader<'_>) -> Result<Self, String> {
    let value = Self::read(reader)?;
    value.validate_modulus().map_err(|error| reader.error(error))?;
    Ok(value)
  }

  pub fn read_field(
    reader: &mut Reader<'_>,
    modulus: Self,
  ) -> Result<Self, String> {
    let value = Self::read(reader)?;
    value.validate_field(modulus).map_err(|error| reader.error(error))?;
    Ok(value)
  }

  pub fn write_field(
    self,
    writer: &mut Writer,
    modulus: Self,
  ) -> Result<(), String> {
    self.validate_field(modulus)?;
    self.write(writer);
    Ok(())
  }
}

impl From<u64> for FieldWord {
  fn from(value: u64) -> Self {
    Self([value, 0, 0, 0])
  }
}

impl TryFrom<FieldWord> for u64 {
  type Error = String;

  fn try_from(value: FieldWord) -> Result<Self, Self::Error> {
    value.to_u64()
  }
}

impl Ord for FieldWord {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.iter().rev().cmp(other.0.iter().rev())
  }
}

impl PartialOrd for FieldWord {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl fmt::Display for FieldWord {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    let Some(high) = self.0.iter().rposition(|&limb| limb != 0) else {
      return formatter.write_str("0");
    };
    write!(formatter, "0x{:x}", self.0[high])?;
    for limb in self.0[..high].iter().rev() {
      write!(formatter, "{limb:016x}")?;
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const BN254_FR: FieldWord = FieldWord::from_limbs_le([
    0x43e1_f593_f000_0001,
    0x2833_e848_79b9_7091,
    0xb850_45b6_8181_585d,
    0x3064_4e72_e131_a029,
  ]);

  fn encode(value: FieldWord) -> Vec<u8> {
    let mut writer = Writer::new();
    value.write(&mut writer);
    writer.into_bytes()
  }

  #[test]
  fn canonical_encoding_uses_minimal_little_endian_limbs() {
    assert_eq!(encode(FieldWord::ZERO), [0]);
    assert_eq!(encode(FieldWord::ONE), [1, 1]);
    assert_eq!(encode(FieldWord::from_limbs_le([0, 1, 0, 0])), [2, 0, 1]);
    assert_eq!(encode(FieldWord::from_limbs_le([0, 0, 1, 0])), [3, 0, 0, 1]);
    assert_eq!(encode(FieldWord::from_limbs_le([0, 0, 0, 1])), [4, 0, 0, 0, 1]);
    for value in [
      FieldWord::ZERO,
      FieldWord::ONE,
      FieldWord::from(u64::MAX),
      FieldWord::from_limbs_le([0, 1, 0, 0]),
      BN254_FR,
      FieldWord::from_limbs_le([u64::MAX; 4]),
    ] {
      let bytes = encode(value);
      let mut reader = Reader::new(&bytes);
      assert_eq!(FieldWord::read(&mut reader).unwrap(), value);
      reader.finish().unwrap();
    }
  }

  #[test]
  fn numeric_ordering_and_narrowing_do_not_follow_low_limb_order() {
    let values = [
      FieldWord::ZERO,
      FieldWord::ONE,
      FieldWord::from(u64::MAX),
      FieldWord::from_limbs_le([0, 1, 0, 0]),
      FieldWord::from_limbs_le([u64::MAX, u64::MAX, 0, 0]),
      FieldWord::from_limbs_le([0, 0, 1, 0]),
      FieldWord::from_limbs_le([0, 0, 0, 1]),
      BN254_FR,
      FieldWord::from_limbs_le([u64::MAX; 4]),
    ];
    assert!(values.windows(2).all(|pair| pair[0] < pair[1]));
    assert_eq!(FieldWord::ZERO.to_u64().unwrap(), 0);
    assert_eq!(u64::try_from(FieldWord::from(u64::MAX)).unwrap(), u64::MAX);
    for value in &values[3..] {
      assert!(value.to_u64().is_err());
    }
  }

  #[test]
  fn field_bounds_are_strict_and_moduli_need_not_be_prime() {
    let mut below = BN254_FR.to_limbs_le();
    below[0] -= 1;
    let below = FieldWord::from_limbs_le(below);
    assert!(below.validate_field(BN254_FR).is_ok());
    assert!(BN254_FR.validate_field(BN254_FR).is_err());
    assert!(
      FieldWord::from_limbs_le([u64::MAX; 4]).validate_field(BN254_FR).is_err()
    );
    assert!(FieldWord::ZERO.validate_modulus().is_err());
    assert!(FieldWord::ONE.validate_modulus().is_err());
    assert!(FieldWord::from(4).validate_modulus().is_ok());
    assert!(FieldWord::from_limbs_le([u64::MAX; 4]).validate_modulus().is_ok());
    let bytes = encode(below);
    assert_eq!(
      FieldWord::read_field(&mut Reader::new(&bytes), BN254_FR).unwrap(),
      below
    );
    assert!(
      FieldWord::read_field(&mut Reader::new(&encode(BN254_FR)), BN254_FR)
        .is_err()
    );
    for modulus in [FieldWord::ZERO, FieldWord::ONE] {
      assert!(
        FieldWord::read_modulus(&mut Reader::new(&encode(modulus))).is_err()
      );
      assert!(FieldWord::ZERO.validate_field(modulus).is_err());
    }
    let mut writer = Writer::new();
    assert!(BN254_FR.write_field(&mut writer, BN254_FR).is_err());
    assert!(writer.into_bytes().is_empty());
  }

  #[test]
  fn decoding_rejects_noncanonical_overwide_truncated_and_overflowing_words() {
    for bytes in
      [vec![1, 0], vec![2, 1, 0], vec![4, 1, 2, 3, 0], vec![5], vec![1, 0xc4]]
    {
      assert!(FieldWord::read(&mut Reader::new(&bytes)).is_err(), "{bytes:?}");
    }
    let mut writer = Writer::new();
    writer.nat(u64::MAX);
    assert!(FieldWord::read(&mut Reader::new(&writer.into_bytes())).is_err());
    let mut overflow = vec![1, 0xc3];
    overflow.extend([0xff; 8]);
    assert!(FieldWord::read(&mut Reader::new(&overflow)).is_err());
    let bytes = encode(FieldWord::from_limbs_le([u64::MAX; 4]));
    for end in 0..bytes.len() {
      assert!(FieldWord::read(&mut Reader::new(&bytes[..end])).is_err());
    }
    let mut reader = Reader::new(&[0, 0]);
    FieldWord::read(&mut reader).unwrap();
    assert!(reader.finish().is_err());
  }

  #[test]
  fn generic_transport_models_preserve_narrow_json_and_wide_values() {
    let narrow_json = serde_json::json!({
      "version": 2, "modulus": 17,
      "functions": [{
        "name": "value", "params": [], "result": {"kind": "field"},
        "registers": 1,
        "code": [
          {"op": "literal", "dest": 0, "value": 16},
          {"op": "ret", "value": [0]}
        ]
      }],
      "enums": [],
      "tables": [{"name": "table", "type": {"kind": "field"}, "rows": [[16]]}],
      "maps": [], "entries": []
    });
    let narrow: crate::Program =
      serde_json::from_value(narrow_json.clone()).unwrap();
    assert_eq!(serde_json::to_value(narrow).unwrap(), narrow_json);

    let value = FieldWord::from_limbs_le([0, 1, 0, 0]);
    let mut wide_json = narrow_json;
    wide_json["modulus"] = serde_json::json!(BN254_FR);
    wide_json["functions"][0]["code"][0]["value"] = serde_json::json!(value);
    wide_json["tables"][0]["rows"][0][0] = serde_json::json!(value);
    let wide: crate::Program<FieldWord> =
      serde_json::from_value(wide_json.clone()).unwrap();
    assert_eq!(wide.modulus, BN254_FR);
    assert_eq!(wide.tables[0].rows[0][0], value);
    assert!(
      matches!(wide.functions[0].code[0], crate::bytecode::Instruction::Literal { value: actual, .. } if actual == value)
    );
    assert_eq!(serde_json::to_value(wide).unwrap(), wide_json);

    let polynomial_json =
      serde_json::json!({"add": [{"const": value}, {"var": 2}]});
    let polynomial: crate::trace::Polynomial<FieldWord> =
      serde_json::from_value(polynomial_json.clone()).unwrap();
    assert_eq!(serde_json::to_value(polynomial).unwrap(), polynomial_json);
  }
}
