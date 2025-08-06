use crate::ixon::address::Address;
use std::collections::BTreeSet;

pub enum Claim {
  Checks { lvls: Address, typ_: Address, value: Address },
  Evals { lvls: Address, typ_: Address, input: Address, output: Address },
}

pub struct Proof {
  pub claim: Claim,
  pub proof: Vec<u8>,
}

pub struct Claims {
  pub map: BTreeSet<Address>,
}
