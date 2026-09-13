use super::bytes::{Bits, Decoder};
use crate::ixby::value::{
  BOOL_TAG, ERASED_TAG, EXT_TAG, FIELD_TAG, WORD32_TAG,
};

pub(super) struct ScalarBits {
  pub tag: Bits,
  pub payload: Bits,
}

impl Decoder {
  fn canonical_goldilocks(&mut self, enabled: usize, bits: &[usize]) {
    assert_eq!(bits.len(), 64);
    // p = 0xffff_ffff_0000_0001. The only excluded u64 values have
    // high32 = 0xffff_ffff and a nonzero low32, including the modulus.
    let high = self.eq_const(&bits[32..], u32::MAX as u64);
    let low = self.any(&bits[..32]);
    let bad = self.and(high, low);
    let bad = self.and(enabled, bad);
    self.violate(bad);
  }

  pub(super) fn scalar(&mut self, enabled: usize) -> ScalarBits {
    let tag = self.byte(enabled);
    let matches: Vec<_> =
      (0..4).map(|tag_value| self.eq_const(&tag, tag_value)).collect();
    let valid = self.sum(&matches);
    self.require(enabled, valid);
    let flags: Vec<_> =
      matches.iter().map(|matched| self.and(enabled, *matched)).collect();
    let [boolean, word, field, extension]: [usize; 4] =
      flags.try_into().unwrap();
    let payload =
      self.read(128, &[(boolean, 1), (word, 4), (field, 8), (extension, 16)]);
    self.require_zero(boolean, &payload[1..8]);
    let first_field = self.sum(&[field, extension]);
    self.canonical_goldilocks(first_field, &payload[..64]);
    self.canonical_goldilocks(extension, &payload[64..]);
    let boolean_tag = self.constant(128, BOOL_TAG);
    let word_tag = self.constant(128, WORD32_TAG);
    let field_tag = self.constant(128, FIELD_TAG);
    let extension_tag = self.constant(128, EXT_TAG);
    let tag = self.choose(&[
      (boolean, &boolean_tag),
      (word, &word_tag),
      (field, &field_tag),
      (extension, &extension_tag),
    ]);
    ScalarBits { tag, payload }
  }

  pub(super) fn value(&mut self, enabled: usize) -> ScalarBits {
    let tag = self.byte(enabled);
    let scalar = self.eq_const(&tag, 0);
    let erased = self.eq_const(&tag, 3);
    let valid = self.sum(&[scalar, erased]);
    self.require(enabled, valid);
    let scalar = self.and(enabled, scalar);
    let erased = self.and(enabled, erased);
    let value = self.scalar(scalar);
    let erased_tag = self.constant(128, ERASED_TAG);
    let tag = self.choose(&[(self.one, &value.tag), (erased, &erased_tag)]);
    ScalarBits { tag, payload: value.payload }
  }

  /// Local reference or already decoded constant. Physical kind 0 is only
  /// inactive padding; kind 1 is local, kind 2 is literal/erased. Byte tags
  /// 0/1/2 remain distinct while parsing and consuming the original bytes.
  pub(super) fn operand(
    &mut self,
    enabled: usize,
    locals: &[usize],
  ) -> [Bits; 3] {
    let tag = self.byte(enabled);
    let matches: Vec<_> =
      (0..3).map(|value| self.eq_const(&tag, value)).collect();
    let valid = self.sum(&matches);
    self.require(enabled, valid);
    let local = self.and(enabled, matches[0]);
    let literal = self.and(enabled, matches[1]);
    let erased = self.and(enabled, matches[2]);
    let constant = self.sum(&[literal, erased]);
    let index = self.u32(local);
    let in_range = self.less(&index, locals);
    self.require(local, in_range);
    let scalar = self.scalar(literal);
    let erased_tag = self.constant(128, ERASED_TAG);
    let value_tag =
      self.choose(&[(self.one, &scalar.tag), (erased, &erased_tag)]);
    let kind = vec![local, constant];
    [self.pack(&[&kind, &index]), value_tag, scalar.payload]
  }
}
