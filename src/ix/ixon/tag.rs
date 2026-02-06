//! Tag encodings for compact serialization.
//!
//! - Tag4: 4-bit flag for expressions (16 variants)
//! - Tag2: 2-bit flag for universes (4 variants)
//! - Tag0: No flag, just variable-length u64

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
      small as u64
    };
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
      small as u64
    };
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
      small as u64
    };
    Ok(Tag0 { size })
  }

  /// Calculate the encoded size of this tag in bytes.
  pub fn encoded_size(&self) -> usize {
    if self.size < 128 { 1 } else { 1 + u64_byte_count(self.size) as usize }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

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
}
