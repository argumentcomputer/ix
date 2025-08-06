use crate::ixon::address::Address;
use crate::ixon::common::{BinderInfo, ReducibilityHints};
use crate::ixon::name::Name;
use crate::ixon::nat::Nat;
use std::collections::BTreeMap;

pub enum Metadatum {
  Name(Name),
  Info(BinderInfo),
  Link(Address),
  Hints(ReducibilityHints),
  All(Vec<Name>),
  MutCtx(Vec<Vec<Name>>),
}

pub struct Metadata {
  pub map: BTreeMap<Nat, Metadatum>,
}
