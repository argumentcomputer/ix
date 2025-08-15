use crate::ixon::address::Address;
use crate::ixon::serialize::Serialize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Claim {
  Checks { lvls: Address, typ: Address, value: Address },
  Evals { lvls: Address, typ: Address, input: Address, output: Address },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
  pub claim: Claim,
  pub proof: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env {
  env: Vec<(Address, Address)>,
}

impl Serialize for Claim {
  fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Checks { lvls, typ, value } => {
        buf.push(0);
        lvls.put(buf);
        typ.put(buf);
        value.put(buf);
      },
      Self::Evals { lvls, typ, input, output } => {
        buf.push(1);
        lvls.put(buf);
        typ.put(buf);
        input.put(buf);
        output.put(buf);
      },
    }
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match buf.split_at_checked(1) {
      Some((head, rest)) => {
        *buf = rest;
        match head[0] {
          0 => {
            let lvls = Address::get(buf)?;
            let typ = Address::get(buf)?;
            let value = Address::get(buf)?;
            Ok(Self::Checks { lvls, typ, value })
          },
          1 => {
            let lvls = Address::get(buf)?;
            let typ = Address::get(buf)?;
            let input = Address::get(buf)?;
            let output = Address::get(buf)?;
            Ok(Self::Evals { lvls, typ, input, output })
          },
          x => Err(format!("get Claim invalid {x}")),
        }
      },
      None => Err("get Claim EOF".to_string()),
    }
  }
}

impl Serialize for Proof {
  fn put(&self, buf: &mut Vec<u8>) {
    self.claim.put(buf);
    self.proof.put(buf);
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let claim = Claim::get(buf)?;
    let proof = Serialize::get(buf)?;
    Ok(Proof { claim, proof })
  }
}

impl Serialize for Env {
  fn put(&self, buf: &mut Vec<u8>) {
    self.env.put(buf)
  }

  fn get(buf: &mut &[u8]) -> Result<Self, String> {
    Ok(Env { env: Serialize::get(buf)? })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ixon::tests::gen_range;
  use quickcheck::{Arbitrary, Gen};

  impl Arbitrary for Claim {
    fn arbitrary(g: &mut Gen) -> Self {
      let x = gen_range(g, 0..1);
      match x {
        0 => Self::Checks {
          lvls: Address::arbitrary(g),
          typ: Address::arbitrary(g),
          value: Address::arbitrary(g),
        },
        _ => Self::Evals {
          lvls: Address::arbitrary(g),
          typ: Address::arbitrary(g),
          input: Address::arbitrary(g),
          output: Address::arbitrary(g),
        },
      }
    }
  }

  impl Arbitrary for Proof {
    fn arbitrary(g: &mut Gen) -> Self {
      let x = gen_range(g, 0..32);
      let mut bytes = vec![];
      for _ in 0..x {
        bytes.push(u8::arbitrary(g));
      }
      Proof { claim: Claim::arbitrary(g), proof: bytes }
    }
  }

  impl Arbitrary for Env {
    fn arbitrary(g: &mut Gen) -> Self {
      let x = gen_range(g, 0..32);
      let mut env = vec![];
      for _ in 0..x {
        env.push((Address::arbitrary(g), Address::arbitrary(g)));
      }
      Env { env }
    }
  }
}
