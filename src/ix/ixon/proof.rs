//! Proof and claim types for ZK verification.

use crate::ix::address::Address;

use super::tag::Tag4;

/// An evaluation claim: asserts that evaluating `input` at type `typ` yields `output`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EvalClaim {
  /// Address of universe level parameters
  pub lvls: Address,
  /// Address of the type
  pub typ: Address,
  /// Address of the input expression
  pub input: Address,
  /// Address of the output expression
  pub output: Address,
}

/// A type-checking claim: asserts that `value` has type `typ`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CheckClaim {
  /// Address of universe level parameters
  pub lvls: Address,
  /// Address of the type
  pub typ: Address,
  /// Address of the value expression
  pub value: Address,
}

/// A claim that can be proven.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Claim {
  /// Evaluation claim
  Evals(EvalClaim),
  /// Type-checking claim
  Checks(CheckClaim),
}

/// A proof of a claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
  /// The claim being proven
  pub claim: Claim,
  /// The proof data (opaque bytes, e.g., ZK proof)
  pub proof: Vec<u8>,
}

/// Tag4 flag for claims and proofs (0xF).
/// Size field encodes variant:
/// - 0: EvalClaim (no proof)
/// - 1: EvalProof (proof of EvalClaim)
/// - 2: CheckClaim (no proof)
/// - 3: CheckProof (proof of CheckClaim)
pub const FLAG: u8 = 0xF;

const VARIANT_EVAL_CLAIM: u64 = 0;
const VARIANT_EVAL_PROOF: u64 = 1;
const VARIANT_CHECK_CLAIM: u64 = 2;
const VARIANT_CHECK_PROOF: u64 = 3;

impl Claim {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Claim::Evals(eval) => {
        Tag4::new(FLAG, VARIANT_EVAL_CLAIM).put(buf);
        buf.extend_from_slice(eval.lvls.as_bytes());
        buf.extend_from_slice(eval.typ.as_bytes());
        buf.extend_from_slice(eval.input.as_bytes());
        buf.extend_from_slice(eval.output.as_bytes());
      },
      Claim::Checks(check) => {
        Tag4::new(FLAG, VARIANT_CHECK_CLAIM).put(buf);
        buf.extend_from_slice(check.lvls.as_bytes());
        buf.extend_from_slice(check.typ.as_bytes());
        buf.extend_from_slice(check.value.as_bytes());
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG {
      return Err(format!(
        "Claim::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG, tag.flag
      ));
    }

    match tag.size {
      VARIANT_EVAL_CLAIM => {
        let lvls = get_address(buf)?;
        let typ = get_address(buf)?;
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        Ok(Claim::Evals(EvalClaim { lvls, typ, input, output }))
      },
      VARIANT_CHECK_CLAIM => {
        let lvls = get_address(buf)?;
        let typ = get_address(buf)?;
        let value = get_address(buf)?;
        Ok(Claim::Checks(CheckClaim { lvls, typ, value }))
      },
      VARIANT_EVAL_PROOF | VARIANT_CHECK_PROOF => {
        Err(format!("Claim::get: got Proof variant {}, use Proof::get", tag.size))
      },
      x => Err(format!("Claim::get: invalid variant {x}")),
    }
  }

  /// Serialize a claim and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }
}

impl Proof {
  pub fn new(claim: Claim, proof: Vec<u8>) -> Self {
    Proof { claim, proof }
  }

  pub fn put(&self, buf: &mut Vec<u8>) {
    match &self.claim {
      Claim::Evals(eval) => {
        Tag4::new(FLAG, VARIANT_EVAL_PROOF).put(buf);
        buf.extend_from_slice(eval.lvls.as_bytes());
        buf.extend_from_slice(eval.typ.as_bytes());
        buf.extend_from_slice(eval.input.as_bytes());
        buf.extend_from_slice(eval.output.as_bytes());
      },
      Claim::Checks(check) => {
        Tag4::new(FLAG, VARIANT_CHECK_PROOF).put(buf);
        buf.extend_from_slice(check.lvls.as_bytes());
        buf.extend_from_slice(check.typ.as_bytes());
        buf.extend_from_slice(check.value.as_bytes());
      },
    }
    // Proof bytes: length prefix + data
    super::tag::Tag0::new(self.proof.len() as u64).put(buf);
    buf.extend_from_slice(&self.proof);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    if tag.flag != FLAG {
      return Err(format!(
        "Proof::get: expected flag 0x{:X}, got 0x{:X}",
        FLAG, tag.flag
      ));
    }

    let claim = match tag.size {
      VARIANT_EVAL_PROOF => {
        let lvls = get_address(buf)?;
        let typ = get_address(buf)?;
        let input = get_address(buf)?;
        let output = get_address(buf)?;
        Claim::Evals(EvalClaim { lvls, typ, input, output })
      },
      VARIANT_CHECK_PROOF => {
        let lvls = get_address(buf)?;
        let typ = get_address(buf)?;
        let value = get_address(buf)?;
        Claim::Checks(CheckClaim { lvls, typ, value })
      },
      VARIANT_EVAL_CLAIM | VARIANT_CHECK_CLAIM => {
        return Err(format!(
          "Proof::get: got Claim variant {}, use Claim::get",
          tag.size
        ));
      },
      x => return Err(format!("Proof::get: invalid variant {x}")),
    };

    // Proof bytes
    let len = usize::try_from(super::tag::Tag0::get(buf)?.size).expect("Tag0 size overflows usize");
    if buf.len() < len {
      return Err(format!(
        "Proof::get: need {} bytes for proof data, have {}",
        len,
        buf.len()
      ));
    }
    let (proof_bytes, rest) = buf.split_at(len);
    *buf = rest;

    Ok(Proof { claim, proof: proof_bytes.to_vec() })
  }

  /// Serialize a proof and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }
}

fn get_address(buf: &mut &[u8]) -> Result<Address, String> {
  if buf.len() < 32 {
    return Err(format!("get_address: need 32 bytes, have {}", buf.len()));
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).map_err(|_e| "get_address: invalid".to_string())
}

#[cfg(test)]
mod tests {
  use super::*;
  use quickcheck::{Arbitrary, Gen};

  impl Arbitrary for EvalClaim {
    fn arbitrary(g: &mut Gen) -> Self {
      EvalClaim {
        lvls: Address::arbitrary(g),
        typ: Address::arbitrary(g),
        input: Address::arbitrary(g),
        output: Address::arbitrary(g),
      }
    }
  }

  impl Arbitrary for CheckClaim {
    fn arbitrary(g: &mut Gen) -> Self {
      CheckClaim {
        lvls: Address::arbitrary(g),
        typ: Address::arbitrary(g),
        value: Address::arbitrary(g),
      }
    }
  }

  impl Arbitrary for Claim {
    fn arbitrary(g: &mut Gen) -> Self {
      if bool::arbitrary(g) {
        Claim::Evals(EvalClaim::arbitrary(g))
      } else {
        Claim::Checks(CheckClaim::arbitrary(g))
      }
    }
  }

  impl Arbitrary for Proof {
    fn arbitrary(g: &mut Gen) -> Self {
      let len = u8::arbitrary(g) as usize % 64;
      let proof: Vec<u8> = (0..len).map(|_| u8::arbitrary(g)).collect();
      Proof { claim: Claim::arbitrary(g), proof }
    }
  }

  fn claim_roundtrip(c: &Claim) -> bool {
    let mut buf = Vec::new();
    c.put(&mut buf);
    match Claim::get(&mut buf.as_slice()) {
      Ok(c2) => c == &c2,
      Err(e) => {
        eprintln!("claim_roundtrip error: {e}");
        false
      },
    }
  }

  fn proof_roundtrip(p: &Proof) -> bool {
    let mut buf = Vec::new();
    p.put(&mut buf);
    match Proof::get(&mut buf.as_slice()) {
      Ok(p2) => p == &p2,
      Err(e) => {
        eprintln!("proof_roundtrip error: {e}");
        false
      },
    }
  }

  #[allow(clippy::needless_pass_by_value)]
  #[quickcheck]
  fn prop_claim_roundtrip(c: Claim) -> bool {
    claim_roundtrip(&c)
  }

  #[allow(clippy::needless_pass_by_value)]
  #[quickcheck]
  fn prop_proof_roundtrip(p: Proof) -> bool {
    proof_roundtrip(&p)
  }

  #[test]
  fn test_eval_claim_roundtrip() {
    let claim = Claim::Evals(EvalClaim {
      lvls: Address::hash(b"lvls"),
      typ: Address::hash(b"typ"),
      input: Address::hash(b"input"),
      output: Address::hash(b"output"),
    });
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_check_claim_roundtrip() {
    let claim = Claim::Checks(CheckClaim {
      lvls: Address::hash(b"lvls"),
      typ: Address::hash(b"typ"),
      value: Address::hash(b"value"),
    });
    assert!(claim_roundtrip(&claim));
  }

  #[test]
  fn test_eval_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Evals(EvalClaim {
        lvls: Address::hash(b"lvls"),
        typ: Address::hash(b"typ"),
        input: Address::hash(b"input"),
        output: Address::hash(b"output"),
      }),
      vec![1, 2, 3, 4],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_check_proof_roundtrip() {
    let proof = Proof::new(
      Claim::Checks(CheckClaim {
        lvls: Address::hash(b"lvls"),
        typ: Address::hash(b"typ"),
        value: Address::hash(b"value"),
      }),
      vec![5, 6, 7, 8, 9],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_empty_proof_data() {
    let proof = Proof::new(
      Claim::Evals(EvalClaim {
        lvls: Address::hash(b"a"),
        typ: Address::hash(b"b"),
        input: Address::hash(b"c"),
        output: Address::hash(b"d"),
      }),
      vec![],
    );
    assert!(proof_roundtrip(&proof));
  }

  #[test]
  fn test_claim_tags() {
    // EvalClaim should be 0xF0
    let eval_claim = Claim::Evals(EvalClaim {
      lvls: Address::hash(b"a"),
      typ: Address::hash(b"b"),
      input: Address::hash(b"c"),
      output: Address::hash(b"d"),
    });
    let mut buf = Vec::new();
    eval_claim.put(&mut buf);
    assert_eq!(buf[0], 0xF0);

    // CheckClaim should be 0xF2
    let check_claim = Claim::Checks(CheckClaim {
      lvls: Address::hash(b"a"),
      typ: Address::hash(b"b"),
      value: Address::hash(b"c"),
    });
    let mut buf = Vec::new();
    check_claim.put(&mut buf);
    assert_eq!(buf[0], 0xF2);
  }

  #[test]
  fn test_proof_tags() {
    // EvalProof should be 0xF1
    let eval_proof = Proof::new(
      Claim::Evals(EvalClaim {
        lvls: Address::hash(b"a"),
        typ: Address::hash(b"b"),
        input: Address::hash(b"c"),
        output: Address::hash(b"d"),
      }),
      vec![1, 2, 3],
    );
    let mut buf = Vec::new();
    eval_proof.put(&mut buf);
    assert_eq!(buf[0], 0xF1);

    // CheckProof should be 0xF3
    let check_proof = Proof::new(
      Claim::Checks(CheckClaim {
        lvls: Address::hash(b"a"),
        typ: Address::hash(b"b"),
        value: Address::hash(b"c"),
      }),
      vec![4, 5, 6],
    );
    let mut buf = Vec::new();
    check_proof.put(&mut buf);
    assert_eq!(buf[0], 0xF3);
  }
}
