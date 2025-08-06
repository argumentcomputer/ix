use crate::ixon::nat::Nat;

pub enum NamePart {
  Str(String),
  Num(Nat),
}

pub struct Name {
  pub parts: Vec<NamePart>,
}
