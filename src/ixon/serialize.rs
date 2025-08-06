pub trait Serialize: Sized {
  fn put(self, buf: &mut Vec<u8>);
  fn get(buf: &mut &[u8]) -> Result<Self, String>;
}

impl Serialize for u8 {
  fn put(self, buf: &mut Vec<u8>) {
    buf.push(self)
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_first() {
      Some((&x, rest)) => {
        *buf = rest;
        Ok(x)
      },
      None => Err("get u8 EOF".to_string()),
    }
  }
}

impl Serialize for u16 {
  fn put(self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(&self.to_le_bytes());
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(2) {
      Some((head, rest)) => {
        *buf = rest;
        Ok(u16::from_le_bytes([head[0], head[1]]))
      },
      None => Err("get u16 EOF".to_string()),
    }
  }
}

impl Serialize for u32 {
  fn put(self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(&self.to_le_bytes());
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(4) {
      Some((head, rest)) => {
        *buf = rest;
        Ok(u32::from_le_bytes([head[0], head[1], head[2], head[3]]))
      },
      None => Err("get u32 EOF".to_string()),
    }
  }
}

impl Serialize for u64 {
  fn put(self, buf: &mut Vec<u8>) {
    buf.extend_from_slice(&self.to_le_bytes());
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(8) {
      Some((head, rest)) => {
        *buf = rest;
        Ok(u64::from_le_bytes([
          head[0], head[1], head[2], head[3], head[4], head[5], head[6],
          head[7],
        ]))
      },
      None => Err("get u64 EOF".to_string()),
    }
  }
}

impl Serialize for bool {
  fn put(self, buf: &mut Vec<u8>) {
    match self {
      false => Serialize::put(0u8, buf),
      true => Serialize::put(1u8, buf),
    }
  }
  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match <u8 as Serialize>::get(buf) {
      Ok(0u8) => Ok(false),
      Ok(1u8) => Ok(true),
      Ok(x) => Err(format!("get bool invalid {x}")),
      Err(e) => Err(e),
    }
  }
}

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

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  #[quickcheck]
  fn prop_u64_trimmed_le_readback(x: u64) -> bool {
    let mut buf = Vec::new();
    let n = u64_byte_count(x);
    u64_put_trimmed_le(x, &mut buf);
    match u64_get_trimmed_le(n as usize, &mut buf.as_slice()) {
      Ok(y) => x == y,
      Err(e) => {
        println!("err: {}", e);
        false
      },
    }
  }
}
