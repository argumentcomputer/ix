use crate::ixon::*;

pub trait Serialize: Sized {
  fn put(&self, buf: &mut Vec<u8>);
  fn get(buf: &mut &[u8]) -> Result<Self, String>;
}

impl Serialize for u8 {
  fn put(&self, buf: &mut Vec<u8>) {
    buf.push(*self)
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
  fn put(&self, buf: &mut Vec<u8>) {
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
  fn put(&self, buf: &mut Vec<u8>) {
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
  fn put(&self, buf: &mut Vec<u8>) {
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
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      false => buf.push(0),
      true => buf.push(1),
    }
  }
  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(1) {
      Some((head, rest)) => {
        *buf = rest;
        match head[0] {
          0 => Ok(false),
          1 => Ok(true),
          x => Err(format!("get bool invalid {x}")),
        }
      },
      None => Err("get bool EOF".to_string()),
    }
  }
}

impl<S: Serialize> Serialize for Vec<S> {
  fn put(&self, buf: &mut Vec<u8>) {
    Ixon::put_array(self, buf)
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    Ixon::get_array(buf)
  }
}

impl<X: Serialize, Y: Serialize> Serialize for (X, Y) {
  fn put(&self, buf: &mut Vec<u8>) {
    Serialize::put(&self.0, buf);
    Serialize::put(&self.1, buf);
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let x = Serialize::get(buf)?;
    let y = Serialize::get(buf)?;
    Ok((x, y))
  }
}
