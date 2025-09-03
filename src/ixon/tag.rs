use crate::ixon::serialize::Serialize;

pub fn u64_byte_count(x: u64) -> u8 {
  match x {
    0 => 0,
    x if x < 0x0000000000000100 => 1,
    x if x < 0x0000000000010000 => 2,
    x if x < 0x0000000001000000 => 3,
    x if x < 0x0000000100000000 => 4,
    x if x < 0x0000010000000000 => 5,
    x if x < 0x0001000000000000 => 6,
    x if x < 0x0100000000000000 => 7,
    _ => 8,
  }
}

pub fn u64_put_trimmed_le(x: u64, buf: &mut Vec<u8>) {
  let n = u64_byte_count(x) as usize;
  buf.extend_from_slice(&x.to_le_bytes()[..n])
}

pub fn u64_get_trimmed_le(len: usize, buf: &mut &[u8]) -> Result<u64, String> {
  let mut res = [0u8; 8];
  if len > 8 {
    return Err("get trimmed_le_64 len > 8".to_string());
  }
  match buf.split_at_checked(len) {
    Some((head, rest)) => {
      *buf = rest;
      res[..len].copy_from_slice(head);
      Ok(u64::from_le_bytes(res))
    },
    None => Err("get trimmed_le_u64 EOF".to_string()),
  }
}

//  F := flag, L := large-bit, X := small-field, A := large_field
// 0xFFLX_XXXX {AAAA_AAAA, ...}
#[derive(Clone, Debug)]
pub struct Tag2 {
  flag: u8,
  size: u64,
}

impl Tag2 {
  pub fn encode_head(&self) -> u8 {
    if self.size < 32 {
      (self.flag << 6) + (self.size as u8)
    } else {
      (self.flag << 6) + 0b10_0000 + u64_byte_count(self.size) - 1
    }
  }
  pub fn decode_head(head: u8) -> (u8, bool, u8) {
    (head >> 6, head & 0b10_0000 == 0, head % 0b10_0000)
  }
}

impl Serialize for Tag2 {
  fn put(&self, buf: &mut Vec<u8>) {
    self.encode_head().put(buf);
    if self.size >= 32 {
      u64_put_trimmed_le(self.size, buf)
    }
  }
  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let head = u8::get(buf)?;
    let (flag, large, small) = Tag2::decode_head(head);
    let size = if large {
      u64_get_trimmed_le((small + 1) as usize, buf)?
    } else {
      small as u64
    };
    Ok(Tag2 { flag, size })
  }
}

//  F := flag, L := large-bit, X := small-field, A := large_field
// 0xFFFF_LXXX {AAAA_AAAA, ...}
// "Tag" means the whole thing
// "Head" means the first byte of the tag
// "Flag" means the first nibble of the head
#[derive(Clone, Debug)]
pub struct Tag4 {
  flag: u8,
  size: u64,
}

impl Tag4 {
  pub fn encode_head(&self) -> u8 {
    if self.size < 8 {
      (self.flag << 4) + (self.size as u8)
    } else {
      (self.flag << 4) + 0b1000 + u64_byte_count(self.size) - 1
    }
  }
  pub fn decode_head(head: u8) -> (u8, bool, u8) {
    (head >> 4, head & 0b1000 == 0, head % 0b1000)
  }
}

impl Serialize for Tag4 {
  fn put(&self, buf: &mut Vec<u8>) {
    self.encode_head().put(buf);
    if self.size >= 8 {
      u64_put_trimmed_le(self.size, buf)
    }
  }
  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let head = u8::get(buf)?;
    let (flag, large, small) = Tag4::decode_head(head);
    let size = if large {
      u64_get_trimmed_le((small + 1) as usize, buf)?
    } else {
      small as u64
    };
    Ok(Tag4 { flag, size })
  }
}
