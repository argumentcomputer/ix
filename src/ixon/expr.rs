use crate::ixon::address::Address;
use crate::ixon::nat::Nat;
use crate::ixon::serialize::{
  u64_byte_count, u64_get_trimmed_le, u64_put_trimmed_le, Serialize,
};
use crate::ixon::univ::Univ;
use num_bigint::BigUint;

// 0xTTTT_LXXX
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum Expr {
  // 0x0, ^1
  Vari(u64),
  // 0x1, {max (add 1 2) (var 1)}
  Sort(Box<Univ>),
  // 0x2 #dead_beef_cafe_babe {u1, u2, ... }
  Refr(Address, Vec<Univ>),
  // 0x3 #1.{u1, u2, u3}
  Recr(u64, Vec<Univ>),
  // 0x4 (f x y z)
  Apps(Box<Expr>, Box<Expr>, Vec<Expr>),
  // 0x5 (λ A B C => body)
  Lams(Vec<Expr>, Box<Expr>),
  // 0x6 (∀ A B C -> body)
  Alls(Vec<Expr>, Box<Expr>),
  // 0x7 (let d : A in b)
  Let(bool, Box<Expr>, Box<Expr>, Box<Expr>),
  // 0x8 .1
  Proj(Address, u64, Box<Expr>),
  // 0x9 "foobar"
  Strl(String),
  // 0xA 0xdead_beef
  Natl(Nat),
}

impl Default for Expr {
  fn default() -> Self {
    Self::Vari(0)
  }
}

impl Expr {
  fn put_tag(tag: u8, val: u64, buf: &mut Vec<u8>) {
    if val < 8 {
      buf.push((tag << 4) | (val as u8));
    } else {
      buf.push((tag << 4) | 0b1000 | (u64_byte_count(val) - 1));
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

impl Serialize for Expr {
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Vari(x) => Self::put_tag(0x0, *x, buf),
      Self::Sort(x) => {
        Self::put_tag(0x1, 0, buf);
        x.put(buf);
      },
      Self::Refr(addr, lvls) => {
        Self::put_tag(0x2, lvls.len() as u64, buf);
        addr.put(buf);
        for l in lvls {
          l.put(buf);
        }
      },
      Self::Recr(x, lvls) => {
        Self::put_tag(0x3, lvls.len() as u64, buf);
        x.put(buf);
        for l in lvls {
          l.put(buf);
        }
      },
      Self::Apps(f, a, args) => {
        Self::put_tag(0x4, args.len() as u64, buf);
        f.put(buf);
        a.put(buf);
        for x in args {
          x.put(buf);
        }
      },
      Self::Lams(ts, b) => {
        Self::put_tag(0x5, ts.len() as u64, buf);
        for t in ts {
          t.put(buf);
        }
        b.put(buf);
      },
      Self::Alls(ts, b) => {
        Self::put_tag(0x6, ts.len() as u64, buf);
        for t in ts {
          t.put(buf);
        }
        b.put(buf);
      },
      Self::Let(nd, t, d, b) => {
        if *nd {
          Self::put_tag(0x7, 1, buf);
        } else {
          Self::put_tag(0x7, 0, buf);
        }
        t.put(buf);
        d.put(buf);
        b.put(buf);
      },
      Self::Proj(t, n, x) => {
        Self::put_tag(0x8, *n, buf);
        t.put(buf);
        x.put(buf);
      },
      Self::Strl(s) => {
        let bytes = s.as_bytes();
        Self::put_tag(0x9, bytes.len() as u64, buf);
        buf.extend_from_slice(bytes);
      },
      Self::Natl(n) => {
        let bytes = n.0.to_bytes_le();
        Self::put_tag(0xA, bytes.len() as u64, buf);
        buf.extend_from_slice(&bytes);
      },
    }
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag_byte = u8::get(buf)?;
    let tag = tag_byte >> 4;
    let small_size = tag_byte & 0b111;
    let is_large = tag_byte & 0b1000 != 0;
    match tag {
      0x0 => {
        let x = Expr::get_tag(is_large, small_size, buf)?;
        Ok(Self::Vari(x))
      },
      0x1 => {
        let u = Univ::get(buf)?;
        Ok(Self::Sort(Box::new(u)))
      },
      0x2 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let a = Address::get(buf)?;
        let mut lvls = Vec::new();
        for _ in 0..n {
          let l = Univ::get(buf)?;
          lvls.push(l);
        }
        Ok(Self::Refr(a, lvls))
      },
      0x3 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let x = u64::get(buf)?;
        let mut lvls = Vec::new();
        for _ in 0..n {
          let l = Univ::get(buf)?;
          lvls.push(l);
        }
        Ok(Self::Recr(x, lvls))
      },
      0x4 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let f = Expr::get(buf)?;
        let a = Expr::get(buf)?;
        let mut args = Vec::new();
        for _ in 0..n {
          let x = Expr::get(buf)?;
          args.push(x);
        }
        Ok(Self::Apps(Box::new(f), Box::new(a), args))
      },
      0x5 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let mut ts = Vec::new();
        for _ in 0..n {
          let x = Expr::get(buf)?;
          ts.push(x);
        }
        let b = Expr::get(buf)?;
        Ok(Self::Lams(ts, Box::new(b)))
      },
      0x6 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let mut ts = Vec::new();
        for _ in 0..n {
          let x = Expr::get(buf)?;
          ts.push(x);
        }
        let b = Expr::get(buf)?;
        Ok(Self::Alls(ts, Box::new(b)))
      },
      0x7 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let nd = n == 1;
        let t = Expr::get(buf)?;
        let d = Expr::get(buf)?;
        let b = Expr::get(buf)?;
        Ok(Self::Let(nd, Box::new(t), Box::new(d), Box::new(b)))
      },
      0x8 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        let t = Address::get(buf)?;
        let x = Expr::get(buf)?;
        Ok(Self::Proj(t, n, Box::new(x)))
      },
      0x9 => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        match buf.split_at_checked(n as usize) {
          Some((head, rest)) => {
            *buf = rest;
            match String::from_utf8(head.to_owned()) {
              Ok(s) => Ok(Expr::Strl(s)),
              Err(e) => Err(format!("UTF8 Error: {e}")),
            }
          },
          None => Err("get Expr Strl EOF".to_string()),
        }
      },
      0xA => {
        let n = Expr::get_tag(is_large, small_size, buf)?;
        match buf.split_at_checked(n as usize) {
          Some((head, rest)) => {
            *buf = rest;
            Ok(Expr::Natl(Nat(BigUint::from_bytes_le(head))))
          },
          None => Err("get Expr Natl EOF".to_string()),
        }
      },
      x => Err(format!("get Expr invalid tag {x}")),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixon::common::tests::{gen_range, next_case};
  use crate::ixon::nat::tests::*;
  use crate::ixon::univ::tests::*;
  use quickcheck::{Arbitrary, Gen};

  use std::ptr;

  #[derive(Debug, Clone, Copy)]
  pub enum ExprCase {
    Vari,
    Sort,
    Refr,
    Recr,
    Apps,
    Lams,
    Alls,
    Let,
    Proj,
    Strl,
    Natl,
  }

  // incremental tree generation without recursion stack overflows
  pub fn arbitrary_expr(g: &mut Gen, ctx: u64) -> Expr {
    let mut root = Expr::default();
    let mut stack = vec![&mut root as *mut Expr];

    while let Some(ptr) = stack.pop() {
      let gens: Vec<(usize, ExprCase)> = vec![
        (100, ExprCase::Vari),
        (100, ExprCase::Sort),
        (75, ExprCase::Refr),
        (50, ExprCase::Recr),
        (25, ExprCase::Apps),
        (25, ExprCase::Lams),
        (50, ExprCase::Alls),
        (50, ExprCase::Let),
        (50, ExprCase::Proj),
        (100, ExprCase::Strl),
        (100, ExprCase::Natl),
      ];

      match next_case(g, &gens) {
        ExprCase::Vari => {
          let x: u64 = Arbitrary::arbitrary(g);
          unsafe {
            ptr::replace(ptr, Expr::Vari(x));
          }
        },
        ExprCase::Sort => {
          let u = arbitrary_univ(g, ctx);
          unsafe {
            ptr::replace(ptr, Expr::Sort(Box::new(u)));
          }
        },
        ExprCase::Refr => {
          let addr = Address::arbitrary(g);
          let mut lvls = vec![];
          for _ in 0..gen_range(g, 0..4) {
            lvls.push(arbitrary_univ(g, ctx));
          }
          unsafe {
            ptr::replace(ptr, Expr::Refr(addr, lvls));
          }
        },
        ExprCase::Recr => {
          let n = u64::arbitrary(g);
          let mut lvls = vec![];
          for _ in 0..gen_range(g, 0..4) {
            lvls.push(arbitrary_univ(g, ctx));
          }
          unsafe {
            ptr::replace(ptr, Expr::Recr(n, lvls));
          }
        },
        ExprCase::Apps => {
          let mut f_box = Box::new(Expr::default());
          let f_ptr: *mut Expr = &mut *f_box;
          stack.push(f_ptr);

          let mut a_box = Box::new(Expr::default());
          let a_ptr: *mut Expr = &mut *a_box;
          stack.push(a_ptr);

          let n = gen_range(g, 0..4);
          let mut xs: Vec<Expr> = Vec::with_capacity(n);
          xs.resize(n, Expr::Vari(0));
          for i in 0..n {
            let p = unsafe { xs.as_mut_ptr().add(i) };
            stack.push(p);
          }

          unsafe {
            std::ptr::replace(ptr, Expr::Apps(f_box, a_box, xs));
          }
        },
        ExprCase::Lams => {
          let n = gen_range(g, 0..4);
          let mut ts: Vec<Expr> = Vec::with_capacity(n);
          ts.resize(n, Expr::Vari(0));
          for i in 0..n {
            let p = unsafe { ts.as_mut_ptr().add(i) };
            stack.push(p);
          }

          let mut b_box = Box::new(Expr::default());
          let b_ptr: *mut Expr = &mut *b_box;
          stack.push(b_ptr);

          unsafe {
            std::ptr::replace(ptr, Expr::Lams(ts, b_box));
          }
        },
        ExprCase::Alls => {
          let n = gen_range(g, 0..4);
          let mut ts: Vec<Expr> = Vec::with_capacity(n);
          ts.resize(n, Expr::Vari(0));
          for i in 0..n {
            let p = unsafe { ts.as_mut_ptr().add(i) };
            stack.push(p);
          }

          let mut b_box = Box::new(Expr::default());
          let b_ptr: *mut Expr = &mut *b_box;
          stack.push(b_ptr);

          unsafe {
            std::ptr::replace(ptr, Expr::Alls(ts, b_box));
          }
        },
        ExprCase::Let => {
          let nd = bool::arbitrary(g);

          let mut t_box = Box::new(Expr::default());
          let t_ptr: *mut Expr = &mut *t_box;
          stack.push(t_ptr);

          let mut d_box = Box::new(Expr::default());
          let d_ptr: *mut Expr = &mut *d_box;
          stack.push(d_ptr);

          let mut b_box = Box::new(Expr::default());
          let b_ptr: *mut Expr = &mut *b_box;
          stack.push(b_ptr);

          unsafe {
            ptr::replace(ptr, Expr::Let(nd, t_box, d_box, b_box));
          }
        },
        ExprCase::Proj => {
          let addr = Address::arbitrary(g);
          let n = u64::arbitrary(g);

          let mut t_box = Box::new(Expr::default());
          let t_ptr: *mut Expr = &mut *t_box;
          stack.push(t_ptr);

          unsafe {
            ptr::replace(ptr, Expr::Proj(addr, n, t_box));
          }
        },
        ExprCase::Strl => {
          let cs = gen_range(g, 0..4);
          let mut s = String::new();
          for _ in 0..cs {
            s.push(char::arbitrary(g));
          }

          unsafe {
            ptr::replace(ptr, Expr::Strl(s));
          }
        },
        ExprCase::Natl => {
          let size = gen_range(g, 0..4);
          unsafe {
            ptr::replace(ptr, Expr::Natl(arbitrary_nat(g, size)));
          }
        },
      }
    }
    root
  }

  impl Arbitrary for Expr {
    fn arbitrary(g: &mut Gen) -> Self {
      let ctx = gen_range(g, 0..4);
      arbitrary_expr(g, ctx as u64)
    }
  }

  #[quickcheck]
  fn prop_expr_readback(x: Expr) -> bool {
    let mut buf = Vec::new();
    Expr::put(&x, &mut buf);
    match Expr::get(&mut buf.as_slice()) {
      Ok(y) => x == y,
      Err(e) => {
        println!("err: {e}");
        false
      },
    }
  }
}
