//! Tag encodings for compact serialization.
//!
//! - Tag4: 4-bit flag for expressions (16 variants)
//! - Tag2: 2-bit flag for universes (4 variants)
//! - Tag0: No flag, just variable-length u64
//! - TagN: nibble-bootstrapped integer with a 0, 2 or 4-bit flag (the Share
//!   index code selectable through `serialize::ShareCodec`)

#![allow(clippy::needless_pass_by_value)]

/// Count how many bytes needed to represent a u64.
pub fn u64_byte_count(x: u64) -> u8 {
  match x {
    0 => 0,
    x if x < 0x0000_0000_0000_0100 => 1,
    x if x < 0x0000_0000_0001_0000 => 2,
    x if x < 0x0000_0000_0100_0000 => 3,
    x if x < 0x0000_0001_0000_0000 => 4,
    x if x < 0x0000_0100_0000_0000 => 5,
    x if x < 0x0001_0000_0000_0000 => 6,
    x if x < 0x0100_0000_0000_0000 => 7,
    _ => 8,
  }
}

/// Write a u64 in minimal little-endian bytes.
pub fn u64_put_trimmed_le(x: u64, buf: &mut Vec<u8>) {
  let n = u64_byte_count(x) as usize;
  buf.extend_from_slice(&x.to_le_bytes()[..n])
}

/// Read a u64 from minimal little-endian bytes.
pub fn u64_get_trimmed_le(len: usize, buf: &mut &[u8]) -> Result<u64, String> {
  let mut res = [0u8; 8];
  if len > 8 {
    return Err("u64_get_trimmed_le: len > 8".to_string());
  }
  match buf.split_at_checked(len) {
    Some((head, rest)) => {
      *buf = rest;
      res[..len].copy_from_slice(head);
      Ok(u64::from_le_bytes(res))
    },
    None => Err(format!("u64_get_trimmed_le: EOF, need {len} bytes")),
  }
}

/// Tag4: 4-bit flag for expressions.
///
/// Header byte: `[flag:4][large:1][size:3]`
/// - If large=0: size is in low 3 bits (0-7)
/// - If large=1: (size+1) bytes follow containing the actual size
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag4 {
  pub flag: u8,
  pub size: u64,
}

impl Tag4 {
  pub fn new(flag: u8, size: u64) -> Self {
    debug_assert!(flag < 16, "Tag4 flag must be < 16");
    Tag4 { flag, size }
  }

  #[allow(clippy::cast_possible_truncation)]
  pub fn encode_head(&self) -> u8 {
    if self.size < 8 {
      (self.flag << 4) + (self.size as u8)
    } else {
      (self.flag << 4) + 0b1000 + (u64_byte_count(self.size) - 1)
    }
  }

  pub fn decode_head(head: u8) -> (u8, bool, u8) {
    (head >> 4, head & 0b1000 != 0, head % 0b1000)
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    buf.push(self.encode_head());
    if self.size >= 8 {
      u64_put_trimmed_le(self.size, buf)
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let head = match buf.split_first() {
      Some((&h, rest)) => {
        *buf = rest;
        h
      },
      None => return Err("Tag4::get: EOF".to_string()),
    };
    let (flag, large, small) = Self::decode_head(head);
    let size = if large {
      u64_get_trimmed_le((small + 1) as usize, buf)?
    } else {
      u64::from(small)
    };
    if large && (size < 8 || u64_byte_count(size) != small + 1) {
      return Err("Tag4::get: noncanonical integer".into());
    }
    Ok(Tag4 { flag, size })
  }

  /// Calculate the encoded size of this tag in bytes.
  pub fn encoded_size(&self) -> usize {
    if self.size < 8 { 1 } else { 1 + u64_byte_count(self.size) as usize }
  }
}

/// Tag2: 2-bit flag for universes.
///
/// Header byte: `[flag:2][large:1][size:5]`
/// - If large=0: size is in low 5 bits (0-31)
/// - If large=1: (size+1) bytes follow containing the actual size
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag2 {
  pub flag: u8,
  pub size: u64,
}

impl Tag2 {
  pub fn new(flag: u8, size: u64) -> Self {
    debug_assert!(flag < 4, "Tag2 flag must be < 4");
    Tag2 { flag, size }
  }

  #[allow(clippy::cast_possible_truncation)]
  pub fn encode_head(&self) -> u8 {
    if self.size < 32 {
      (self.flag << 6) + (self.size as u8)
    } else {
      (self.flag << 6) + 0b10_0000 + (u64_byte_count(self.size) - 1)
    }
  }

  pub fn decode_head(head: u8) -> (u8, bool, u8) {
    (head >> 6, head & 0b10_0000 != 0, head % 0b10_0000)
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    buf.push(self.encode_head());
    if self.size >= 32 {
      u64_put_trimmed_le(self.size, buf)
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let head = match buf.split_first() {
      Some((&h, rest)) => {
        *buf = rest;
        h
      },
      None => return Err("Tag2::get: EOF".to_string()),
    };
    let (flag, large, small) = Self::decode_head(head);
    let size = if large {
      u64_get_trimmed_le((small + 1) as usize, buf)?
    } else {
      u64::from(small)
    };
    if large && (size < 32 || u64_byte_count(size) != small + 1) {
      return Err("Tag2::get: noncanonical integer".into());
    }
    Ok(Tag2 { flag, size })
  }

  /// Calculate the encoded size of this tag in bytes.
  pub fn encoded_size(&self) -> usize {
    if self.size < 32 { 1 } else { 1 + u64_byte_count(self.size) as usize }
  }
}

/// Tag0: No flag, just variable-length u64.
///
/// Header byte: `[large:1][size:7]`
/// - If large=0: size is in low 7 bits (0-127)
/// - If large=1: (size+1) bytes follow containing the actual size
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tag0 {
  pub size: u64,
}

impl Tag0 {
  pub fn new(size: u64) -> Self {
    Tag0 { size }
  }

  #[allow(clippy::cast_possible_truncation)]
  pub fn encode_head(&self) -> u8 {
    if self.size < 128 {
      self.size as u8
    } else {
      0b1000_0000 + (u64_byte_count(self.size) - 1)
    }
  }

  pub fn decode_head(head: u8) -> (bool, u8) {
    (head & 0b1000_0000 != 0, head % 0b1000_0000)
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    buf.push(self.encode_head());
    if self.size >= 128 {
      u64_put_trimmed_le(self.size, buf)
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let head = match buf.split_first() {
      Some((&h, rest)) => {
        *buf = rest;
        h
      },
      None => return Err("Tag0::get: EOF".to_string()),
    };
    let (large, small) = Self::decode_head(head);
    let size = if large {
      u64_get_trimmed_le((small + 1) as usize, buf)?
    } else {
      u64::from(small)
    };
    if large && (size < 128 || u64_byte_count(size) != small + 1) {
      return Err("Tag0::get: noncanonical integer".into());
    }
    Ok(Tag0 { size })
  }

  /// Calculate the encoded size of this tag in bytes.
  pub fn encoded_size(&self) -> usize {
    if self.size < 128 { 1 } else { 1 + u64_byte_count(self.size) as usize }
  }
}

/// TagN: nibble-bootstrapped integer code. A rule-for-rule port of
/// `Ixon.putTagN` / `Ixon.getTagN` (`Ix/Ixon.lean`).
///
/// One header byte `[flag : f bits][payload : r = 8 - f bits]`
/// (`f` in `{0, 2, 4}`) followed by 0, 1, 2, 4 or 8 little-endian bytes.
/// With `L` the top payload bit and `M` the next one:
///
/// * `L = 0`: the low `r - 1` payload bits are the value (rung 1,
///   `[0, R1)`, `R1 = 2^(r-1)`);
/// * `L = 1, M = 0`: the low `r - 2` bits followed by one byte hold
///   `value - R1` (rung 2, `[R1, R2)`, `R2 = R1 + 2^(r-2+8)`);
/// * `L = 1, M = 1`: the low `r - 2` bits are a code `c`; `c = 0, 1, 2`
///   select 2, 4, 8 following bytes holding `value - R2`, `value - R3`,
///   `value - R4` (`R3 = R2 + 2^16`, `R4 = R3 + 2^32`); every other code is
///   invalid.
///
/// Each rung starts where the previous one ends, so a value has exactly one
/// encoding (the code is bijective and needs no canonicality check). Rung
/// ends:
///
/// | f | R1 | R2 | R3 | R4 |
/// |---|---|---|---|---|
/// | 0 | 128 | 16512 | 82048 | 4295049344 |
/// | 2 | 32 | 4128 | 69664 | 4295036960 |
/// | 4 | 8 | 1032 | 66568 | 4295033864 |
///
/// Every `u64` is representable for each `f`; the decoder rejects 8-byte
/// payloads whose value would reach `2^64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TagN {
  pub flag: u8,
  pub value: u64,
}

impl TagN {
  /// End (exclusive) of rung 1 for an `f`-bit flag (`Ixon.tagNEnd1`).
  pub const fn end1(f: u32) -> u64 {
    1 << (8 - f - 1)
  }

  /// End of rung 2 (`Ixon.tagNEnd2`).
  pub const fn end2(f: u32) -> u64 {
    Self::end1(f) + (1 << (8 - f - 2 + 8))
  }

  /// End of rung 3 (`Ixon.tagNEnd3`).
  pub const fn end3(f: u32) -> u64 {
    Self::end2(f) + (1 << 16)
  }

  /// End of rung 4 (`Ixon.tagNEnd4`). Rung 5 ends at `end4 + 2^64`, beyond
  /// every `u64`.
  pub const fn end4(f: u32) -> u64 {
    Self::end3(f) + (1 << 32)
  }

  /// Byte width of the encoding of `value` (`Ixon.tagNByteWidth`):
  /// 1, 2, 3, 5 or 9.
  pub const fn byte_width(f: u32, value: u64) -> usize {
    if value < Self::end1(f) {
      1
    } else if value < Self::end2(f) {
      2
    } else if value < Self::end3(f) {
      3
    } else if value < Self::end4(f) {
      5
    } else {
      9
    }
  }

  /// Header byte: `flag` in the high `f` bits, `payload` in the low `8 - f`
  /// (`Ixon.tagNHeader`, truncated to a byte like `Nat.toUInt8`).
  #[allow(clippy::cast_possible_truncation)]
  const fn header(f: u32, flag: u8, payload: u64) -> u8 {
    (((flag as u64) << (8 - f)) + payload) as u8
  }

  /// Write `value` with an `f`-bit `flag` (`Ixon.putTagN`).
  pub fn put(f: u32, flag: u8, value: u64, buf: &mut Vec<u8>) {
    debug_assert!(
      f == 0 || f == 2 || f == 4,
      "TagN flag width must be 0, 2 or 4"
    );
    debug_assert!(u64::from(flag) < (1u64 << f), "TagN flag out of range");
    let lead = 1u64 << (8 - f - 1);
    let mbit = 1u64 << (8 - f - 2);
    if value < Self::end1(f) {
      buf.push(Self::header(f, flag, value));
    } else if value < Self::end2(f) {
      let v = value - Self::end1(f);
      buf.push(Self::header(f, flag, lead + v / 256));
      buf.push(v.to_le_bytes()[0]);
    } else if value < Self::end3(f) {
      buf.push(Self::header(f, flag, lead + mbit));
      buf.extend_from_slice(&(value - Self::end2(f)).to_le_bytes()[..2]);
    } else if value < Self::end4(f) {
      buf.push(Self::header(f, flag, lead + mbit + 1));
      buf.extend_from_slice(&(value - Self::end3(f)).to_le_bytes()[..4]);
    } else {
      buf.push(Self::header(f, flag, lead + mbit + 2));
      buf.extend_from_slice(&(value - Self::end4(f)).to_le_bytes());
    }
  }

  /// Read a TagN integer with an `f`-bit flag (`Ixon.getTagN`). Invalid codes
  /// and values reaching `2^64` are rejected.
  pub fn get(f: u32, buf: &mut &[u8]) -> Result<TagN, String> {
    debug_assert!(
      f == 0 || f == 2 || f == 4,
      "TagN flag width must be 0, 2 or 4"
    );
    let head = match buf.split_first() {
      Some((&h, rest)) => {
        *buf = rest;
        h
      },
      None => return Err("TagN::get: EOF".to_string()),
    };
    let r = 8 - f;
    let flag = if f == 0 { 0 } else { head >> r };
    let p = u64::from(head) & ((1u64 << r) - 1);
    let lead = 1u64 << (r - 1);
    let mbit = 1u64 << (r - 2);
    if p < lead {
      return Ok(TagN { flag, value: p });
    }
    if p - lead < mbit {
      let lo = match buf.split_first() {
        Some((&b, rest)) => {
          *buf = rest;
          b
        },
        None => return Err("TagN::get: EOF, need 1 byte".to_string()),
      };
      return Ok(TagN {
        flag,
        value: Self::end1(f) + (p - lead) * 256 + u64::from(lo),
      });
    }
    let (len, base) = match p - lead - mbit {
      0 => (2, Self::end2(f)),
      1 => (4, Self::end3(f)),
      2 => (8, Self::end4(f)),
      c => return Err(format!("TagN::get: invalid TagN code {c}")),
    };
    let x = u64_get_trimmed_le(len, buf)?;
    let value = base
      .checked_add(x)
      .ok_or_else(|| "TagN::get: TagN value exceeds UInt64".to_string())?;
    Ok(TagN { flag, value })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};
  use quickcheck_macros::quickcheck;

  // ============================================================================
  // Arbitrary implementations
  // ============================================================================

  impl Arbitrary for Tag4 {
    fn arbitrary(g: &mut Gen) -> Self {
      let flag = u8::arbitrary(g) % 16;
      Tag4::new(flag, u64::arbitrary(g))
    }
  }

  impl Arbitrary for Tag2 {
    fn arbitrary(g: &mut Gen) -> Self {
      let flag = u8::arbitrary(g) % 4;
      Tag2::new(flag, u64::arbitrary(g))
    }
  }

  impl Arbitrary for Tag0 {
    fn arbitrary(g: &mut Gen) -> Self {
      Tag0::new(u64::arbitrary(g))
    }
  }

  // ============================================================================
  // Property-based tests
  // ============================================================================

  #[quickcheck]
  fn prop_tag4_roundtrip(t: Tag4) -> bool {
    let mut buf = Vec::new();
    t.put(&mut buf);
    match Tag4::get(&mut buf.as_slice()) {
      Ok(t2) => t == t2,
      Err(_) => false,
    }
  }

  #[quickcheck]
  fn prop_tag4_encoded_size(t: Tag4) -> bool {
    let mut buf = Vec::new();
    t.put(&mut buf);
    buf.len() == t.encoded_size()
  }

  #[quickcheck]
  fn prop_tag2_roundtrip(t: Tag2) -> bool {
    let mut buf = Vec::new();
    t.put(&mut buf);
    match Tag2::get(&mut buf.as_slice()) {
      Ok(t2) => t == t2,
      Err(_) => false,
    }
  }

  #[quickcheck]
  fn prop_tag2_encoded_size(t: Tag2) -> bool {
    let mut buf = Vec::new();
    t.put(&mut buf);
    buf.len() == t.encoded_size()
  }

  #[quickcheck]
  fn prop_tag0_roundtrip(t: Tag0) -> bool {
    let mut buf = Vec::new();
    t.put(&mut buf);
    match Tag0::get(&mut buf.as_slice()) {
      Ok(t2) => t == t2,
      Err(_) => false,
    }
  }

  #[quickcheck]
  fn prop_tag0_encoded_size(t: Tag0) -> bool {
    let mut buf = Vec::new();
    t.put(&mut buf);
    buf.len() == t.encoded_size()
  }

  // ============================================================================
  // Unit tests
  // ============================================================================

  #[test]
  fn test_u64_trimmed() {
    fn roundtrip(x: u64) -> bool {
      let mut buf = Vec::new();
      let n = u64_byte_count(x);
      u64_put_trimmed_le(x, &mut buf);
      match u64_get_trimmed_le(n as usize, &mut buf.as_slice()) {
        Ok(y) => x == y,
        Err(_) => false,
      }
    }
    assert!(roundtrip(0));
    assert!(roundtrip(1));
    assert!(roundtrip(127));
    assert!(roundtrip(128));
    assert!(roundtrip(255));
    assert!(roundtrip(256));
    assert!(roundtrip(0xFFFF_FFFF_FFFF_FFFF));
  }

  #[test]
  fn tag4_small_values() {
    for size in 0..8u64 {
      for flag in 0..16u8 {
        let tag = Tag4::new(flag, size);
        let mut buf = Vec::new();
        tag.put(&mut buf);
        assert_eq!(buf.len(), 1, "Tag4({flag}, {size}) should be 1 byte");

        let mut slice: &[u8] = &buf;
        let recovered = Tag4::get(&mut slice).unwrap();
        assert_eq!(recovered, tag, "Tag4({flag}, {size}) roundtrip failed");
        assert!(slice.is_empty(), "Tag4({flag}, {size}) had trailing bytes");
      }
    }
  }

  #[test]
  fn tag4_large_values() {
    let sizes = [8u64, 255, 256, 65535, 65536, u64::from(u32::MAX), u64::MAX];
    for size in sizes {
      for flag in 0..16u8 {
        let tag = Tag4::new(flag, size);
        let mut buf = Vec::new();
        tag.put(&mut buf);

        let mut slice: &[u8] = &buf;
        let recovered = Tag4::get(&mut slice).unwrap();
        assert_eq!(recovered, tag, "Tag4({flag}, {size}) roundtrip failed");
        assert!(slice.is_empty(), "Tag4({flag}, {size}) had trailing bytes");
      }
    }
  }

  #[test]
  fn tag4_encoded_size_test() {
    assert_eq!(Tag4::new(0, 0).encoded_size(), 1);
    assert_eq!(Tag4::new(0, 7).encoded_size(), 1);
    assert_eq!(Tag4::new(0, 8).encoded_size(), 2);
    assert_eq!(Tag4::new(0, 255).encoded_size(), 2);
    assert_eq!(Tag4::new(0, 256).encoded_size(), 3);
    assert_eq!(Tag4::new(0, 65535).encoded_size(), 3);
    assert_eq!(Tag4::new(0, 65536).encoded_size(), 4);
  }

  #[test]
  fn tag4_byte_boundaries() {
    let test_cases: Vec<(u64, usize)> = vec![
      (0, 1),
      (7, 1),
      (8, 2),
      (0xFF, 2),
      (0x100, 3),
      (0xFFFF, 3),
      (0x10000, 4),
      (0xFFFFFF, 4),
      (0x1000000, 5),
      (0xFFFFFFFF, 5),
      (0x100000000, 6),
      (0xFFFFFFFFFF, 6),
      (0x10000000000, 7),
      (0xFFFFFFFFFFFF, 7),
      (0x1000000000000, 8),
      (0xFFFFFFFFFFFFFF, 8),
      (0x100000000000000, 9),
      (u64::MAX, 9),
    ];

    for (size, expected_bytes) in &test_cases {
      let tag = Tag4::new(0, *size);
      let mut buf = Vec::new();
      tag.put(&mut buf);

      assert_eq!(
        buf.len(),
        *expected_bytes,
        "Tag4 with size 0x{:X} should be {} bytes, got {}",
        size,
        expected_bytes,
        buf.len()
      );

      let mut slice: &[u8] = &buf;
      let recovered = Tag4::get(&mut slice).unwrap();
      assert_eq!(recovered, tag, "Round-trip failed for size 0x{:X}", size);
      assert!(slice.is_empty());
    }
  }

  // ============================================================================
  // Tag2 unit tests
  // ============================================================================

  #[test]
  fn tag2_small_values() {
    for size in 0..32u64 {
      for flag in 0..4u8 {
        let tag = Tag2::new(flag, size);
        let mut buf = Vec::new();
        tag.put(&mut buf);
        assert_eq!(buf.len(), 1, "Tag2({flag}, {size}) should be 1 byte");

        let mut slice: &[u8] = &buf;
        let recovered = Tag2::get(&mut slice).unwrap();
        assert_eq!(recovered, tag, "Tag2({flag}, {size}) roundtrip failed");
        assert!(slice.is_empty(), "Tag2({flag}, {size}) had trailing bytes");
      }
    }
  }

  #[test]
  fn tag2_large_values() {
    let sizes = [32u64, 255, 256, 65535, 65536, u64::from(u32::MAX), u64::MAX];
    for size in sizes {
      for flag in 0..4u8 {
        let tag = Tag2::new(flag, size);
        let mut buf = Vec::new();
        tag.put(&mut buf);

        let mut slice: &[u8] = &buf;
        let recovered = Tag2::get(&mut slice).unwrap();
        assert_eq!(recovered, tag, "Tag2({flag}, {size}) roundtrip failed");
        assert!(slice.is_empty(), "Tag2({flag}, {size}) had trailing bytes");
      }
    }
  }

  #[test]
  fn tag2_encoded_size_test() {
    assert_eq!(Tag2::new(0, 0).encoded_size(), 1);
    assert_eq!(Tag2::new(0, 31).encoded_size(), 1);
    assert_eq!(Tag2::new(0, 32).encoded_size(), 2);
    assert_eq!(Tag2::new(0, 255).encoded_size(), 2);
    assert_eq!(Tag2::new(0, 256).encoded_size(), 3);
    assert_eq!(Tag2::new(0, 65535).encoded_size(), 3);
    assert_eq!(Tag2::new(0, 65536).encoded_size(), 4);
  }

  #[test]
  fn tag2_byte_boundaries() {
    let test_cases: Vec<(u64, usize)> = vec![
      (0, 1),
      (31, 1),
      (32, 2),
      (0xFF, 2),
      (0x100, 3),
      (0xFFFF, 3),
      (0x10000, 4),
      (0xFFFFFF, 4),
      (0x1000000, 5),
      (0xFFFFFFFF, 5),
      (0x100000000, 6),
      (0xFFFFFFFFFF, 6),
      (0x10000000000, 7),
      (0xFFFFFFFFFFFF, 7),
      (0x1000000000000, 8),
      (0xFFFFFFFFFFFFFF, 8),
      (0x100000000000000, 9),
      (u64::MAX, 9),
    ];

    for (size, expected_bytes) in &test_cases {
      let tag = Tag2::new(0, *size);
      let mut buf = Vec::new();
      tag.put(&mut buf);

      assert_eq!(
        buf.len(),
        *expected_bytes,
        "Tag2 with size 0x{:X} should be {} bytes, got {}",
        size,
        expected_bytes,
        buf.len()
      );

      let mut slice: &[u8] = &buf;
      let recovered = Tag2::get(&mut slice).unwrap();
      assert_eq!(recovered, tag, "Round-trip failed for size 0x{:X}", size);
      assert!(slice.is_empty());
    }
  }

  // ============================================================================
  // Tag0 unit tests
  // ============================================================================

  #[test]
  fn tag0_small_values() {
    for size in 0..128u64 {
      let tag = Tag0::new(size);
      let mut buf = Vec::new();
      tag.put(&mut buf);
      assert_eq!(buf.len(), 1, "Tag0({size}) should be 1 byte");

      let mut slice: &[u8] = &buf;
      let recovered = Tag0::get(&mut slice).unwrap();
      assert_eq!(recovered, tag, "Tag0({size}) roundtrip failed");
      assert!(slice.is_empty(), "Tag0({size}) had trailing bytes");
    }
  }

  #[test]
  fn tag0_large_values() {
    let sizes = [128u64, 255, 256, 65535, 65536, u64::from(u32::MAX), u64::MAX];
    for size in sizes {
      let tag = Tag0::new(size);
      let mut buf = Vec::new();
      tag.put(&mut buf);

      let mut slice: &[u8] = &buf;
      let recovered = Tag0::get(&mut slice).unwrap();
      assert_eq!(recovered, tag, "Tag0({size}) roundtrip failed");
      assert!(slice.is_empty(), "Tag0({size}) had trailing bytes");
    }
  }

  #[test]
  fn tag0_encoded_size_test() {
    assert_eq!(Tag0::new(0).encoded_size(), 1);
    assert_eq!(Tag0::new(127).encoded_size(), 1);
    assert_eq!(Tag0::new(128).encoded_size(), 2);
    assert_eq!(Tag0::new(255).encoded_size(), 2);
    assert_eq!(Tag0::new(256).encoded_size(), 3);
    assert_eq!(Tag0::new(65535).encoded_size(), 3);
    assert_eq!(Tag0::new(65536).encoded_size(), 4);
  }

  #[test]
  fn tag0_byte_boundaries() {
    let test_cases: Vec<(u64, usize)> = vec![
      (0, 1),
      (127, 1),
      (128, 2),
      (0xFF, 2),
      (0x100, 3),
      (0xFFFF, 3),
      (0x10000, 4),
      (0xFFFFFF, 4),
      (0x1000000, 5),
      (0xFFFFFFFF, 5),
      (0x100000000, 6),
      (0xFFFFFFFFFF, 6),
      (0x10000000000, 7),
      (0xFFFFFFFFFFFF, 7),
      (0x1000000000000, 8),
      (0xFFFFFFFFFFFFFF, 8),
      (0x100000000000000, 9),
      (u64::MAX, 9),
    ];

    for (size, expected_bytes) in &test_cases {
      let tag = Tag0::new(*size);
      let mut buf = Vec::new();
      tag.put(&mut buf);

      assert_eq!(
        buf.len(),
        *expected_bytes,
        "Tag0 with size 0x{:X} should be {} bytes, got {}",
        size,
        expected_bytes,
        buf.len()
      );

      let mut slice: &[u8] = &buf;
      let recovered = Tag0::get(&mut slice).unwrap();
      assert_eq!(recovered, tag, "Round-trip failed for size 0x{:X}", size);
      assert!(slice.is_empty());
    }
  }

  // ============================================================================
  // TagN: the vectors of `Tests/Ix/Ixon.lean` (`tagNUnits`), byte for byte
  // ============================================================================

  fn tagn_bytes(f: u32, flag: u8, v: u64) -> Vec<u8> {
    let mut buf = Vec::new();
    TagN::put(f, flag, v, &mut buf);
    buf
  }

  /// Decode all of `bytes` (trailing bytes are an error, like
  /// `runGetExact`).
  fn tagn_exact(f: u32, bytes: &[u8]) -> Result<TagN, String> {
    let mut cur = bytes;
    let t = TagN::get(f, &mut cur)?;
    if cur.is_empty() {
      Ok(t)
    } else {
      Err(format!("trailing bytes: {}", cur.len()))
    }
  }

  /// `tagNBoundaries`: 0, 1, `2^64 - 1` and every rung end `e - 1, e, e + 1`.
  fn tagn_boundaries(f: u32) -> Vec<u64> {
    let mut v = vec![0, 1, u64::MAX];
    for e in [TagN::end1(f), TagN::end2(f), TagN::end3(f), TagN::end4(f)] {
      v.extend([e - 1, e, e + 1]);
    }
    v
  }

  #[test]
  fn tagn_boundaries_roundtrip() {
    for f in [0u32, 2, 4] {
      let flags = [0u8, u8::try_from((1u32 << f) - 1).expect("f <= 4")];
      for flag in flags {
        for v in tagn_boundaries(f) {
          let bytes = tagn_bytes(f, flag, v);
          assert_eq!(bytes.len(), TagN::byte_width(f, v), "f={f} v={v}");
          assert_eq!(
            tagn_exact(f, &bytes),
            Ok(TagN { flag, value: v }),
            "f={f} flag={flag} v={v}"
          );
        }
      }
    }
  }

  #[test]
  fn tagn_rung_ends() {
    let ends =
      |f: u32| [TagN::end1(f), TagN::end2(f), TagN::end3(f), TagN::end4(f)];
    assert_eq!(ends(0), [128, 16512, 82048, 4_295_049_344]);
    assert_eq!(ends(2), [32, 4128, 69664, 4_295_036_960]);
    assert_eq!(ends(4), [8, 1032, 66568, 4_295_033_864]);
  }

  #[test]
  fn tagn_expected_bytes() {
    let cases: &[(u32, u8, u64, &[u8])] = &[
      (4, 0xA, 7, &[0xA7]),
      (4, 0xA, 8, &[0xA8, 0x00]),
      (4, 0x1, 1031, &[0x1B, 0xFF]),
      (4, 0, 1032, &[0x0C, 0x00, 0x00]),
      (4, 0, 66568, &[0x0D, 0, 0, 0, 0]),
      (4, 0, 4_295_033_864, &[0x0E, 0, 0, 0, 0, 0, 0, 0, 0]),
      (0, 0, 127, &[0x7F]),
      (0, 0, 128, &[0x80, 0x00]),
      (0, 0, 16512, &[0xC0, 0x00, 0x00]),
      (2, 3, 32, &[0xE0, 0x00]),
      (2, 3, 4128, &[0xF0, 0x00, 0x00]),
    ];
    for &(f, flag, v, expected) in cases {
      assert_eq!(tagn_bytes(f, flag, v), expected, "f={f} flag={flag} v={v}");
      assert_eq!(tagn_exact(f, expected), Ok(TagN { flag, value: v }));
    }
  }

  #[test]
  fn tagn_rejects() {
    let cases: &[(u32, &[u8], &str)] = &[
      (4, &[0x0F, 0, 0, 0, 0, 0, 0, 0, 0], "f=4 code 3"),
      (2, &[0x33], "f=2 code 3"),
      (2, &[0x3F], "f=2 code 15"),
      (0, &[0xC3], "f=0 code 3"),
      (0, &[0xFF], "f=0 code 63"),
      (
        4,
        &[0x0E, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        "f=4 overflow",
      ),
      (
        0,
        &[0xC2, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        "f=0 overflow",
      ),
      (4, &[0x08], "truncated rung 2"),
      (4, &[0x07, 0x00], "trailing byte"),
    ];
    for &(f, bytes, what) in cases {
      assert!(tagn_exact(f, bytes).is_err(), "accepted {what}: {bytes:02x?}");
    }
  }

  /// `tagNShortCanonical`: every string of one or two bytes that decodes
  /// exactly re-encodes to itself.
  #[test]
  fn tagn_short_strings_canonical() {
    for f in [0u32, 2, 4] {
      for a in 0..=255u8 {
        if let Ok(t) = tagn_exact(f, &[a]) {
          assert_eq!(tagn_bytes(f, t.flag, t.value), [a], "f={f} {a:02x}");
        }
        for b in 0..=255u8 {
          if let Ok(t) = tagn_exact(f, &[a, b]) {
            assert_eq!(
              tagn_bytes(f, t.flag, t.value),
              [a, b],
              "f={f} {a:02x} {b:02x}"
            );
          }
        }
      }
    }
  }

  #[quickcheck]
  fn prop_tagn_roundtrip(f_sel: u8, flag: u8, v: u64) -> bool {
    let f = [0u32, 2, 4][usize::from(f_sel % 3)];
    let flag = if f == 0 { 0 } else { flag % (1u8 << f) };
    let bytes = tagn_bytes(f, flag, v);
    bytes.len() == TagN::byte_width(f, v)
      && tagn_exact(f, &bytes) == Ok(TagN { flag, value: v })
  }
}
