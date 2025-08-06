use crate::ixon::address::Address;
use crate::ixon::nat::Nat;
use crate::ixon::univ::Univ;

pub enum Expr {
  Vari(u64),
  Sort(Box<Univ>),
  Refr(Address, Vec<Univ>),
  Recr(u64, Vec<Univ>),
  Apps(Box<Expr>, Box<Expr>, Vec<Expr>),
  Lams(Vec<Expr>, Box<Expr>),
  Alls(Vec<Expr>, Box<Expr>),
  Let(bool, Box<Expr>, Box<Expr>, Box<Expr>),
  Proj(Address, u64, Box<Expr>),
  Strl(String),
  Natl(Nat),
}
