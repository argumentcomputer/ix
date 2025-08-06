use crate::ixon::serialize::{
  u64_byte_count, u64_get_trimmed_le, u64_put_trimmed_le, Serialize,
};

// 0xTTTL_XXXX
pub enum Univ {
  // 0x0, 1
  Const(u64),
  // 0x1, ^1
  Var(u64),
  // 0x2, (+ x y)
  Add(u64, Box<Univ>),
  // 0x3, (max x y)
  Max(Box<Univ>, Box<Univ>),
  // 0x4, (imax x y)
  IMax(Box<Univ>, Box<Univ>),
}

impl Univ {
  fn put_tag(tag: u8, val: u64, buf: &mut Vec<u8>) {
    if val < 16 {
      buf.push((tag << 5) | (val as u8));
    } else {
      buf.push((tag << 5) | 0b1_0000 | (u64_byte_count(val)));
      u64_put_trimmed_le(val, buf);
    }
  }

  fn get_tag(
    is_large: bool,
    small: u8,
    buf: &mut &[u8],
  ) -> Result<u64, String> {
    if is_large {
      u64_get_trimmed_le((small + 1) as usize, buf)
    } else {
      Ok(small as u64)
    }
  }
}

impl Serialize for Univ {
  fn put(self, buf: &mut Vec<u8>) {
    match self {
      Self::Const(x) => Univ::put_tag(0x0, x, buf),
      Self::Var(x) => Univ::put_tag(0x1, x, buf),
      Self::Add(x, y) => {
        Univ::put_tag(0x2, x, buf);
        y.put(buf)
      },
      Self::Max(x, y) => {
        Univ::put_tag(0x3, 0, buf);
        x.put(buf);
        y.put(buf);
      },
      Self::IMax(x, y) => {
        Univ::put_tag(0x4, 0, buf);
        x.put(buf);
        y.put(buf);
      },
    }
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag_byte = u8::get(buf)?;
    let tag = tag_byte >> 5;
    let small_size = tag_byte & 0b1111;
    let is_large = tag_byte & 0b10000 == 0;
    match tag {
      0x0 => {
        let x = Univ::get_tag(is_large, small_size, buf)?;
        Ok(Self::Const(x))
      },
      0x1 => {
        let x = Univ::get_tag(is_large, small_size, buf)?;
        Ok(Self::Var(x))
      },
      0x2 => {
        let x = Univ::get_tag(is_large, small_size, buf)?;
        let y = Univ::get(buf)?;
        Ok(Self::Add(x, Box::new(y)))
      },
      0x3 => {
        let x = Univ::get(buf)?;
        let y = Univ::get(buf)?;
        Ok(Self::Max(Box::new(x), Box::new(y)))
      },
      0x4 => {
        let x = Univ::get(buf)?;
        let y = Univ::get(buf)?;
        Ok(Self::IMax(Box::new(x), Box::new(y)))
      },
      x => Err(format!("get Univ invalid tag {x}")),
    }
  }
}
