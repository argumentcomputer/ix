//! The Ixon integer code: TagN.
//!
//! Every integer field of the wire format is a TagN integer with a 4-bit flag
//! (expression, constant, environment, commitment, claim and proof headers),
//! a 2-bit flag (universe terms) or no flag (counts, indices and every other
//! unsigned integer).

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

/// TagN: the Ixon integer code. A rule-for-rule port of `Ixon.putTagN` /
/// `Ixon.getTagN` (`Ix/Ixon.lean`).
///
/// One header byte `[flag : f bits][payload : r = 8 - f bits]`
/// (`f` in `{0, 2, 4}`) followed by 0, 1, 2, 3, 4 or 8 little-endian bytes.
/// With `L` the top payload bit and `M` the next one:
///
/// * `L = 0`: the low `r - 1` payload bits are the value (rung 1,
///   `[0, R1)`, `R1 = 2^(r-1)`);
/// * `L = 1, M = 0`: the low `r - 2` bits followed by one byte hold
///   `value - R1` (rung 2, `[R1, R2)`, `R2 = R1 + 2^(r-2+8)`);
/// * `L = 1, M = 1`: the low `r - 2` bits are a code `c`; `c = 0, 1, 2, 3`
///   select 2, 3, 4, 8 following bytes holding `value - R2`, `value - R3`,
///   `value - R4`, `value - R5` (`R3 = R2 + 2^16`, `R4 = R3 + 2^24`,
///   `R5 = R4 + 2^32`); every other code is invalid (none for `f = 4`).
///
/// Each rung starts where the previous one ends, so a value has exactly one
/// encoding (the code is bijective and needs no canonicality check). Widths
/// 1, 2, 3, 4, 5, 9; rung ends:
///
/// | f | R1 | R2 | R3 | R4 | R5 |
/// |---|---|---|---|---|---|
/// | 0 | 128 | 16512 | 82048 | 16859264 | 4311826560 |
/// | 2 | 32 | 4128 | 69664 | 16846880 | 4311814176 |
/// | 4 | 8 | 1032 | 66568 | 16843784 | 4311811080 |
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

  /// End of rung 4 (`Ixon.tagNEnd4`).
  pub const fn end4(f: u32) -> u64 {
    Self::end3(f) + (1 << 24)
  }

  /// End of rung 5 (`Ixon.tagNEnd5`). Rung 6 ends at `end5 + 2^64`, beyond
  /// every `u64`.
  pub const fn end5(f: u32) -> u64 {
    Self::end4(f) + (1 << 32)
  }

  /// Byte width of the encoding of `value` (`Ixon.tagNByteWidth`):
  /// 1, 2, 3, 4, 5 or 9.
  pub const fn byte_width(f: u32, value: u64) -> usize {
    if value < Self::end1(f) {
      1
    } else if value < Self::end2(f) {
      2
    } else if value < Self::end3(f) {
      3
    } else if value < Self::end4(f) {
      4
    } else if value < Self::end5(f) {
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
      buf.extend_from_slice(&(value - Self::end3(f)).to_le_bytes()[..3]);
    } else if value < Self::end5(f) {
      buf.push(Self::header(f, flag, lead + mbit + 2));
      buf.extend_from_slice(&(value - Self::end4(f)).to_le_bytes()[..4]);
    } else {
      buf.push(Self::header(f, flag, lead + mbit + 3));
      buf.extend_from_slice(&(value - Self::end5(f)).to_le_bytes());
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
      1 => (3, Self::end3(f)),
      2 => (4, Self::end4(f)),
      3 => (8, Self::end5(f)),
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
  use quickcheck_macros::quickcheck;

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
    for e in [
      TagN::end1(f),
      TagN::end2(f),
      TagN::end3(f),
      TagN::end4(f),
      TagN::end5(f),
    ] {
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
    let ends = |f: u32| {
      [
        TagN::end1(f),
        TagN::end2(f),
        TagN::end3(f),
        TagN::end4(f),
        TagN::end5(f),
      ]
    };
    assert_eq!(ends(0), [128, 16512, 82048, 16_859_264, 4_311_826_560]);
    assert_eq!(ends(2), [32, 4128, 69664, 16_846_880, 4_311_814_176]);
    assert_eq!(ends(4), [8, 1032, 66568, 16_843_784, 4_311_811_080]);
  }

  #[test]
  fn tagn_expected_bytes() {
    let cases: &[(u32, u8, u64, &[u8])] = &[
      (4, 0xA, 7, &[0xA7]),
      (4, 0xA, 8, &[0xA8, 0x00]),
      (4, 0x1, 1031, &[0x1B, 0xFF]),
      (4, 0, 1032, &[0x0C, 0x00, 0x00]),
      (4, 0, 66567, &[0x0C, 0xFF, 0xFF]),
      (4, 0, 66568, &[0x0D, 0, 0, 0]),
      (4, 0, 16_843_783, &[0x0D, 0xFF, 0xFF, 0xFF]),
      (4, 0, 16_843_784, &[0x0E, 0, 0, 0, 0]),
      (4, 0, 4_311_811_079, &[0x0E, 0xFF, 0xFF, 0xFF, 0xFF]),
      (4, 0, 4_311_811_080, &[0x0F, 0, 0, 0, 0, 0, 0, 0, 0]),
      (0, 0, 127, &[0x7F]),
      (0, 0, 128, &[0x80, 0x00]),
      (0, 0, 16512, &[0xC0, 0x00, 0x00]),
      (0, 0, 82047, &[0xC0, 0xFF, 0xFF]),
      (0, 0, 82048, &[0xC1, 0, 0, 0]),
      (0, 0, 16_859_263, &[0xC1, 0xFF, 0xFF, 0xFF]),
      (0, 0, 16_859_264, &[0xC2, 0, 0, 0, 0]),
      (0, 0, 4_311_826_560, &[0xC3, 0, 0, 0, 0, 0, 0, 0, 0]),
      (
        0,
        0,
        u64::MAX,
        &[0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF],
      ),
      (2, 3, 32, &[0xE0, 0x00]),
      (2, 3, 4128, &[0xF0, 0x00, 0x00]),
      (2, 3, 69663, &[0xF0, 0xFF, 0xFF]),
      (2, 3, 69664, &[0xF1, 0, 0, 0]),
      (2, 3, 16_846_879, &[0xF1, 0xFF, 0xFF, 0xFF]),
      (2, 3, 16_846_880, &[0xF2, 0, 0, 0, 0]),
      (2, 3, 4_311_814_176, &[0xF3, 0, 0, 0, 0, 0, 0, 0, 0]),
    ];
    for &(f, flag, v, expected) in cases {
      assert_eq!(tagn_bytes(f, flag, v), expected, "f={f} flag={flag} v={v}");
      assert_eq!(tagn_exact(f, expected), Ok(TagN { flag, value: v }));
    }
  }

  #[test]
  fn tagn_rejects() {
    let cases: &[(u32, &[u8], &str)] = &[
      (2, &[0x34], "f=2 code 4"),
      (2, &[0x3F], "f=2 code 15"),
      (0, &[0xC4], "f=0 code 4"),
      (0, &[0xFF], "f=0 code 63"),
      (
        4,
        &[0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        "f=4 overflow",
      ),
      (
        0,
        &[0xC3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        "f=0 overflow",
      ),
      (4, &[0x08], "truncated rung 2"),
      (4, &[0x0D, 0x00, 0x00], "truncated rung 4"),
      (4, &[0x0F, 0x00, 0x00, 0x00], "truncated rung 6"),
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
