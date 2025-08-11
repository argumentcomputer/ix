use crate::ixon::serialize::{
  u64_byte_count, u64_get_trimmed_le, u64_put_trimmed_le, Serialize,
};

// 0xTTTL_XXXX
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
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

impl Default for Univ {
  fn default() -> Self {
    Self::Const(0)
  }
}

impl Univ {
  fn put_tag(tag: u8, val: u64, buf: &mut Vec<u8>) {
    if val < 16 {
      buf.push((tag << 5) | (val as u8));
    } else {
      buf.push((tag << 5) | 0b1_0000 | (u64_byte_count(val) - 1));
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
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Const(x) => Univ::put_tag(0x0, *x, buf),
      Self::Var(x) => Univ::put_tag(0x1, *x, buf),
      Self::Add(x, y) => {
        Univ::put_tag(0x2, *x, buf);
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
    let is_large = tag_byte & 0b10000 != 0;
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

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::ixon::common::tests::{gen_range, next_case};
  use quickcheck::{Arbitrary, Gen};

  use std::ptr;

  #[derive(Debug, Clone, Copy)]
  pub enum UnivCase {
    Const,
    Var,
    Add,
    Max,
    IMax,
  }

  // incremental tree generation without recursion stack overflows
  pub fn arbitrary_univ(g: &mut Gen, ctx: u64) -> Univ {
    let mut root = Univ::Const(0);
    let mut stack: Vec<*mut Univ> = vec![&mut root as *mut Univ];

    while let Some(ptr) = stack.pop() {
      let gens: Vec<(usize, UnivCase)> = vec![
        (100, UnivCase::Const),
        (100, UnivCase::Var),
        (75, UnivCase::Add),
        (50, UnivCase::Max),
        (50, UnivCase::IMax),
      ];

      match next_case(g, &gens) {
        UnivCase::Const => {
          let x: u64 = Arbitrary::arbitrary(g);
          unsafe {
            ptr::replace(ptr, Univ::Const(x));
          }
        },
        UnivCase::Var => {
          let x: u64 = gen_range(g, 0..(ctx as usize)) as u64;
          unsafe {
            ptr::replace(ptr, Univ::Var(x));
          }
        },
        UnivCase::Add => {
          let x: u64 = Arbitrary::arbitrary(g);
          let mut y_box = Box::new(Univ::Const(0));
          let y_ptr: *mut Univ = &mut *y_box;
          stack.push(y_ptr);
          unsafe {
            ptr::replace(ptr, Univ::Add(x, y_box));
          }
        },
        UnivCase::Max => {
          let mut x_box = Box::new(Univ::Const(0));
          let x_ptr: *mut Univ = &mut *x_box;
          stack.push(x_ptr);
          let mut y_box = Box::new(Univ::Const(0));
          let y_ptr: *mut Univ = &mut *y_box;
          stack.push(y_ptr);
          unsafe {
            ptr::replace(ptr, Univ::Max(x_box, y_box));
          }
        },
        UnivCase::IMax => {
          let mut x_box = Box::new(Univ::Const(0));
          let x_ptr: *mut Univ = &mut *x_box;
          stack.push(x_ptr);
          let mut y_box = Box::new(Univ::Const(0));
          let y_ptr: *mut Univ = &mut *y_box;
          stack.push(y_ptr);
          unsafe {
            ptr::replace(ptr, Univ::Max(x_box, y_box));
          }
        },
      }
    }
    root
  }

  impl Arbitrary for Univ {
    fn arbitrary(g: &mut Gen) -> Self {
      let ctx: u64 = Arbitrary::arbitrary(g);
      arbitrary_univ(g, ctx)
    }
  }

  #[quickcheck]
  fn prop_univ_readback(x: Univ) -> bool {
    let mut buf = Vec::new();
    Univ::put(&x, &mut buf);
    match Univ::get(&mut buf.as_slice()) {
      Ok(y) => x == y,
      Err(e) => {
        println!("err: {e}");
        false
      },
    }
  }
}
