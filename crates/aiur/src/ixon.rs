//! The Ixon v4 primitives that Aiur artifacts are written with.
//!
//! Aiur does not depend on the `ixon` crate, so this module carries the few
//! Ixon conventions the artifact grammar (`crate::artifact`) needs:
//!
//! * a `nat` is an unsigned integer in Ixon's TagN code with no flag bits
//!   (`ixon::tag::TagN::put(0, 0, v)`, Lean `Ixon.putTagN 0 0 v`);
//! * a count or length is a `nat`; a list is its count followed by its items;
//! * bytes and strings are a `nat` length followed by the raw (UTF-8) bytes;
//! * a bool is one byte, 0 or 1; an option is the byte 0, or the byte 1 and
//!   the value;
//! * a sum is one tag byte followed by the variant's fields in order.
//!
//! TagN is bijective, and every tag, bool and option byte is checked, so the
//! encoding is canonical: an accepted byte string has exactly one decoding,
//! and re-encoding that decoding returns the same bytes. `ix-ffi`'s tests pin
//! [`Writer::nat`] and [`Reader::nat`] to `ixon::tag::TagN`; the Lean copy is
//! `Aiur.Ixon`, pinned to `Ixon.putTagN` in `Ix.AiurArtifact`.

/// TagN rung ends for a zero-bit flag (`ixon::tag::TagN::end1(0)` .. `end5`).
const END1: u64 = 1 << 7;
const END2: u64 = END1 + (1 << 14);
const END3: u64 = END2 + (1 << 16);
const END4: u64 = END3 + (1 << 24);
const END5: u64 = END4 + (1 << 32);

/// An append-only Ixon byte writer.
#[derive(Clone, Debug, Default)]
pub struct Writer {
  bytes: Vec<u8>,
}

impl Writer {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn into_bytes(self) -> Vec<u8> {
    self.bytes
  }

  /// Bytes written verbatim, with no length (magic numbers, nested objects).
  pub fn raw(&mut self, bytes: &[u8]) {
    self.bytes.extend_from_slice(bytes);
  }

  pub fn u8(&mut self, value: u8) {
    self.bytes.push(value);
  }

  /// A TagN integer with no flag bits.
  pub fn nat(&mut self, value: u64) {
    let header = |payload: u64| u8::try_from(payload).expect("TagN header");
    if value < END1 {
      self.bytes.push(header(value));
    } else if value < END2 {
      let v = value - END1;
      self.bytes.push(header(END1 + v / 256));
      self.bytes.push(v.to_le_bytes()[0]);
    } else {
      let (code, base, width) = if value < END3 {
        (0, END2, 2)
      } else if value < END4 {
        (1, END3, 3)
      } else if value < END5 {
        (2, END4, 4)
      } else {
        (3, END5, 8)
      };
      self.bytes.push(header(END1 + (1 << 6) + code));
      self.bytes.extend_from_slice(&(value - base).to_le_bytes()[..width]);
    }
  }

  pub fn usize(&mut self, value: usize) {
    self.nat(value as u64);
  }

  pub fn bool(&mut self, value: bool) {
    self.bytes.push(u8::from(value));
  }

  pub fn bytes(&mut self, bytes: &[u8]) {
    self.usize(bytes.len());
    self.raw(bytes);
  }

  pub fn str(&mut self, value: &str) {
    self.bytes(value.as_bytes());
  }

  pub fn list<T>(&mut self, items: &[T], mut item: impl FnMut(&mut Self, &T)) {
    self.usize(items.len());
    for x in items {
      item(self, x);
    }
  }

  pub fn nats(&mut self, items: &[u64]) {
    self.list(items, |w, &x| w.nat(x));
  }

  pub fn usizes(&mut self, items: &[usize]) {
    self.list(items, |w, &x| w.usize(x));
  }

  pub fn option<T>(
    &mut self,
    value: Option<&T>,
    item: impl FnOnce(&mut Self, &T),
  ) {
    match value {
      None => self.u8(0),
      Some(x) => {
        self.u8(1);
        item(self, x);
      },
    }
  }
}

/// A strict Ixon reader over one complete buffer. Every failure names the
/// byte offset at which it was detected.
#[derive(Clone, Debug)]
pub struct Reader<'a> {
  bytes: &'a [u8],
  offset: usize,
}

impl<'a> Reader<'a> {
  pub fn new(bytes: &'a [u8]) -> Self {
    Self { bytes, offset: 0 }
  }

  pub fn offset(&self) -> usize {
    self.offset
  }

  pub fn remaining(&self) -> usize {
    self.bytes.len() - self.offset
  }

  pub fn error(&self, message: impl std::fmt::Display) -> String {
    format!("ixon: {message} at byte {}", self.offset)
  }

  /// Reject trailing bytes.
  pub fn finish(self) -> Result<(), String> {
    if self.remaining() == 0 {
      Ok(())
    } else {
      Err(self.error(format!("{} trailing bytes", self.remaining())))
    }
  }

  pub fn raw(&mut self, length: usize) -> Result<&'a [u8], String> {
    if length > self.remaining() {
      return Err(self.error(format!("need {length} bytes, end of input")));
    }
    let slice = &self.bytes[self.offset..self.offset + length];
    self.offset += length;
    Ok(slice)
  }

  /// The bytes consumed since `start` (an earlier [`Reader::offset`]).
  pub fn since(&self, start: usize) -> &'a [u8] {
    &self.bytes[start..self.offset]
  }

  pub fn u8(&mut self) -> Result<u8, String> {
    Ok(self.raw(1)?[0])
  }

  /// A sum tag below `count`.
  pub fn tag(&mut self, what: &str, count: u8) -> Result<u8, String> {
    let tag = self.u8()?;
    if tag < count {
      Ok(tag)
    } else {
      self.offset -= 1;
      Err(self.error(format!("unknown {what} tag {tag}")))
    }
  }

  /// A TagN integer with no flag bits.
  pub fn nat(&mut self) -> Result<u64, String> {
    let start = self.offset;
    let head = u64::from(self.u8()?);
    if head < END1 {
      return Ok(head);
    }
    if head - END1 < 1 << 6 {
      let low = u64::from(self.u8()?);
      return Ok(END1 + (head - END1) * 256 + low);
    }
    let (width, base) = match head - END1 - (1 << 6) {
      0 => (2, END2),
      1 => (3, END3),
      2 => (4, END4),
      3 => (8, END5),
      code => {
        self.offset = start;
        return Err(self.error(format!("invalid TagN code {code}")));
      },
    };
    let mut le = [0u8; 8];
    le[..width].copy_from_slice(self.raw(width)?);
    base.checked_add(u64::from_le_bytes(le)).ok_or_else(|| {
      let error = self.error("TagN value exceeds u64");
      self.offset = start;
      error
    })
  }

  pub fn usize(&mut self) -> Result<usize, String> {
    let value = self.nat()?;
    usize::try_from(value)
      .map_err(|_e| self.error(format!("{value} exceeds usize")))
  }

  pub fn u32(&mut self) -> Result<u32, String> {
    let value = self.nat()?;
    u32::try_from(value)
      .map_err(|_e| self.error(format!("{value} exceeds u32")))
  }

  pub fn bool(&mut self) -> Result<bool, String> {
    Ok(self.tag("bool", 2)? == 1)
  }

  /// A count of items occupying at least one byte each, so no count can
  /// allocate more than the remaining input could fill.
  pub fn count(&mut self) -> Result<usize, String> {
    let count = self.usize()?;
    if count > self.remaining() {
      return Err(self.error(format!(
        "count {count} exceeds the {} remaining bytes",
        self.remaining()
      )));
    }
    Ok(count)
  }

  pub fn bytes(&mut self) -> Result<&'a [u8], String> {
    let length = self.usize()?;
    self.raw(length)
  }

  pub fn string(&mut self) -> Result<String, String> {
    let start = self.offset;
    let bytes = self.bytes()?;
    String::from_utf8(bytes.to_vec()).map_err(|_e| {
      let error = self.error("invalid UTF-8 string");
      self.offset = start;
      error
    })
  }

  pub fn list<T>(
    &mut self,
    mut item: impl FnMut(&mut Self) -> Result<T, String>,
  ) -> Result<Vec<T>, String> {
    let count = self.count()?;
    let mut items = Vec::with_capacity(count);
    for _ in 0..count {
      items.push(item(self)?);
    }
    Ok(items)
  }

  pub fn nats(&mut self) -> Result<Vec<u64>, String> {
    self.list(Self::nat)
  }

  pub fn usizes(&mut self) -> Result<Vec<usize>, String> {
    self.list(Self::usize)
  }

  pub fn option<T>(
    &mut self,
    item: impl FnOnce(&mut Self) -> Result<T, String>,
  ) -> Result<Option<T>, String> {
    if self.tag("option", 2)? == 1 { Ok(Some(item(self)?)) } else { Ok(None) }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn nat_bytes(value: u64) -> Vec<u8> {
    let mut w = Writer::new();
    w.nat(value);
    w.into_bytes()
  }

  pub(crate) fn boundaries() -> Vec<u64> {
    let mut values = vec![0, 1, u64::MAX - 1, u64::MAX];
    for end in [END1, END2, END3, END4, END5] {
      values.extend([end - 1, end, end + 1]);
    }
    values
  }

  #[test]
  fn nat_round_trips_with_ixon_widths() {
    for value in boundaries() {
      let bytes = nat_bytes(value);
      let width = match value {
        v if v < END1 => 1,
        v if v < END2 => 2,
        v if v < END3 => 3,
        v if v < END4 => 4,
        v if v < END5 => 5,
        _ => 9,
      };
      assert_eq!(bytes.len(), width, "{value}");
      let mut r = Reader::new(&bytes);
      assert_eq!(r.nat().unwrap(), value);
      r.finish().unwrap();
    }
  }

  #[test]
  fn nat_matches_ixon_reference_bytes() {
    // Expected encodings from `ixon::tag` (f = 0).
    assert_eq!(nat_bytes(127), [0x7F]);
    assert_eq!(nat_bytes(128), [0x80, 0x00]);
    assert_eq!(nat_bytes(16511), [0xBF, 0xFF]);
    assert_eq!(nat_bytes(16512), [0xC0, 0x00, 0x00]);
    assert_eq!(nat_bytes(82048), [0xC1, 0x00, 0x00, 0x00]);
    assert_eq!(nat_bytes(16859264), [0xC2, 0, 0, 0, 0]);
    assert_eq!(nat_bytes(4311826560), [0xC3, 0, 0, 0, 0, 0, 0, 0, 0]);
  }

  #[test]
  fn reader_rejects_malformed_input() {
    // An invalid TagN code, and a 9-byte value past u64::MAX.
    assert!(Reader::new(&[0xC4]).nat().unwrap_err().contains("TagN code"));
    let mut overflow = vec![0xC3];
    overflow.extend([0xFF; 8]);
    assert!(Reader::new(&overflow).nat().unwrap_err().contains("exceeds"));
    assert!(Reader::new(&[0x80]).nat().unwrap_err().contains("end of input"));
    assert!(Reader::new(&[2]).bool().unwrap_err().contains("bool tag 2"));
    assert!(Reader::new(&[2]).option(Reader::nat).is_err());
    assert!(Reader::new(&[1, 0xFF]).string().unwrap_err().contains("UTF-8"));
    assert!(Reader::new(&[5, 0]).nats().unwrap_err().contains("count 5"));
    let mut r = Reader::new(&[1, 2]);
    r.nat().unwrap();
    assert!(r.finish().unwrap_err().contains("1 trailing"));
  }
}
