//! `streams_parity FIXTURE [CATALOG]`: rebuilds every advice case that
//! `formal-aggregate-tests` dumped (`aggregation.json.streams.json`) with the
//! Rust encoder, from the same statements and proofs, and requires the same
//! ordered streams byte for byte.
//!
//! - Pair cases also require the Rust statement fold to reach Lean's output
//!   claim. Ownership for the fold: the first child's subjects belong to
//!   shard 0, the second's to shard 1, any other constant to shard 2. Each
//!   child carries its claim (`Ix.Claim.ser`), whose context the rebuilt
//!   statement takes and whose bytes it must reproduce.
//! - Discharge cases require the Rust discharge fold
//!   (`statement::discharged_claim`) to reach Lean's output from the first
//!   child's claim.
//! - Catalog cases (`cross-binding`, `catalog-join`) rebuild the whole plan
//!   with `catalog::plan` from the members, which come from the case, the
//!   fixture, or the `members` of CATALOG (a `pr678-refs catalog` dump), and
//!   require the node's claim and its children's claims to be Lean's.
//!
//! A claim is a hex string, or an object whose `hex` field is one.

use std::sync::Arc;

use aggregate_controller::{
  Identity, catalog,
  protocol::{ChildKind, WordIdentity},
  statement::{
    CanonicalTree, ShardSet, Statement, SubjectTree, discharged_claim,
  },
  streams::{self, Child, Keys, Streams, Transport},
};
use ix_common::address::Address;
use rustc_hash::FxHashMap;
use serde_json::Value;

fn bytes(value: &Value) -> Result<Vec<u8>, String> {
  let text = value.as_str().ok_or("expected a hex string")?;
  if text.len() % 2 != 0 {
    return Err("odd hex length".into());
  }
  (0..text.len())
    .step_by(2)
    .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(|e| e.to_string()))
    .collect()
}

fn addresses(value: &Value) -> Result<Vec<Address>, String> {
  let mut out: Vec<Address> = value
    .as_array()
    .ok_or("expected an address list")?
    .iter()
    .map(|v| {
      v.as_str()
        .and_then(Address::from_hex)
        .ok_or_else(|| format!("bad address {v}"))
    })
    .collect::<Result<_, _>>()?;
  out.sort_unstable();
  Ok(out)
}

/// A claim's bytes: a hex string, or an object with a `hex` field.
fn claim_bytes(value: &Value) -> Result<Vec<u8>, String> {
  match value {
    Value::Object(object) => {
      bytes(object.get("hex").ok_or("claim has no hex")?)
    },
    other => bytes(other),
  }
}

fn members(value: &Value) -> Result<Vec<catalog::Member>, String> {
  value
    .as_array()
    .ok_or("expected a member list")?
    .iter()
    .map(|m| {
      Ok(catalog::Member {
        label: m["label"].as_str().unwrap_or("?").to_owned(),
        claim: ixon::Claim::from_bytes(&claim_bytes(&m["claim"])?)?,
        binding_section: bytes(&m["binding_section"])?,
        literal_class: match &m["literal_class"] {
          Value::Null => None,
          v => Some(
            v.as_str()
              .and_then(Address::from_hex)
              .ok_or_else(|| format!("bad literal class {v}"))?,
          ),
        },
      })
    })
    .collect()
}

/// A child given by its kind, claim and proof, with the claim list of its
/// outer claim.
struct Proven {
  kind: ChildKind,
  claim: Vec<u8>,
  proof: Vec<u8>,
  claims: Vec<u8>,
}

impl Proven {
  fn load(identity: &WordIdentity, child: &Value) -> Result<Self, String> {
    let kind = kind(&child["kind"])?;
    let claim = claim_bytes(&child["claim"])?;
    let claims = identity.claims_bytes(&identity.outer_claim(kind, &claim));
    Ok(Self { kind, claim, proof: bytes(&child["proof"])?, claims })
  }

  fn transport(&self) -> Transport<'_> {
    Transport { kind: self.kind, proof: &self.proof, claims: &self.claims }
  }
}

fn kind(value: &Value) -> Result<ChildKind, String> {
  match value.as_u64() {
    Some(0) => Ok(ChildKind::Ixvm),
    Some(1) => Ok(ChildKind::Aggr),
    _ => Err(format!("bad child kind {value}")),
  }
}

struct Loaded {
  kind: ChildKind,
  statement: Arc<Statement>,
  proof: Vec<u8>,
  claims: Vec<u8>,
}

fn as_child(c: &Loaded) -> Child<'_> {
  Child {
    kind: c.kind,
    statement: &c.statement,
    proof: &c.proof,
    claims: &c.claims,
  }
}

fn entries(streams: &Streams<'_>) -> Vec<(u64, Vec<u64>, Vec<u8>)> {
  streams
    .entries()
    .iter()
    .map(|(c, k, p)| (*c, k.clone(), p.to_vec()))
    .collect()
}

fn expected(case: &Value) -> Result<Vec<(u64, Vec<u64>, Vec<u8>)>, String> {
  case["entries"]
    .as_array()
    .ok_or("missing entries")?
    .iter()
    .map(|entry| {
      let channel = entry[0].as_u64().ok_or("bad channel")?;
      let key = entry[1]
        .as_array()
        .ok_or("bad key")?
        .iter()
        .map(|w| w.as_u64().ok_or("bad key word"))
        .collect::<Result<_, _>>()?;
      Ok((channel, key, bytes(&entry[2])?))
    })
    .collect()
}

fn read_json(path: &str) -> Result<Value, String> {
  serde_json::from_slice(
    &std::fs::read(path).map_err(|e| format!("{path}: {e}"))?,
  )
  .map_err(|e| format!("{path}: {e}"))
}

/// The streams of a case whose children carry claims and proofs only.
fn extra_case(
  identity: &WordIdentity,
  keys: Keys<'_>,
  case: &Value,
  shared_members: Option<&Value>,
) -> Result<Vec<(u64, Vec<u64>, Vec<u8>)>, String> {
  let label = case["label"].as_str().unwrap_or("?");
  let children: Vec<Proven> = case["children"]
    .as_array()
    .ok_or("missing children")?
    .iter()
    .map(|child| Proven::load(identity, child))
    .collect::<Result<_, _>>()?;
  let output = bytes(&case["output"])?;
  match case["type"].as_str() {
    Some("discharge") => {
      let [child, binding] = &children[..] else {
        return Err(format!("{label}: a discharge has two children"));
      };
      let claim = ixon::Claim::from_bytes(&child.claim)?;
      let mut rebuilt = Vec::new();
      discharged_claim(&claim)?.put(&mut rebuilt);
      if rebuilt != output {
        return Err(format!(
          "{label}: the Rust discharge reached another claim"
        ));
      }
      Ok(entries(&streams::discharge(
        keys,
        child.transport(),
        &child.claim,
        binding.transport(),
        &binding.claim,
        &output,
      )?))
    },
    Some("cross-binding" | "catalog-join") => {
      let list = match &case["members"] {
        Value::Null => shared_members.ok_or_else(|| {
          format!("{label}: no members; pass the catalog dump as CATALOG")
        })?,
        list => list,
      };
      let members = members(list)?;
      let plan = catalog::plan(&members)?;
      let index = usize::try_from(case["node"].as_u64().ok_or("missing node")?)
        .map_err(|e| e.to_string())?;
      let statement = plan
        .statements
        .get(index)
        .ok_or_else(|| format!("{label}: no node {index}"))?;
      if statement.claim_bytes != output {
        return Err(format!(
          "{label}: the Rust catalog plan reached another claim"
        ));
      }
      let advice = plan
        .advice(&members, index)
        .ok_or_else(|| format!("{label}: node {index} is a member"))?;
      if u64::from(advice.shape) != case["shape"].as_u64().unwrap_or(u64::MAX) {
        return Err(format!("{label}: the Rust plan proves another shape"));
      }
      let child_nodes =
        plan.nodes[index].children().ok_or("a join has children")?;
      let [left, right] = &children[..] else {
        return Err(format!("{label}: a catalog join has two children"));
      };
      for (child, node) in [left, right].into_iter().zip(child_nodes) {
        if child.claim != plan.statements[node].claim_bytes {
          return Err(format!("{label}: child {node} has another claim"));
        }
      }
      let trees: Vec<&CanonicalTree> =
        advice.trees.iter().map(|tree| &**tree).collect();
      Ok(entries(&streams::catalog(
        keys,
        advice.shape,
        [left.transport(), right.transport()],
        &output,
        &advice.preimages,
        &trees,
      )))
    },
    other => Err(format!("{label}: unknown case type {other:?}")),
  }
}

fn run(path: &str, catalog_path: Option<&str>) -> Result<usize, String> {
  let fixture = read_json(path)?;
  let catalog_dump = catalog_path.map(read_json).transpose()?;
  let shared_members = match &fixture["members"] {
    Value::Null => catalog_dump.as_ref().map(|dump| &dump["members"]),
    list => Some(list),
  };
  let (ixvm_key, aggr_key) =
    (bytes(&fixture["ixvm_key"])?, bytes(&fixture["aggr_key"])?);
  let identity = WordIdentity::new(1, &ixvm_key, 0, &aggr_key, 0, Vec::new());
  if bytes(&fixture["allowed"])? != identity.allowed {
    return Err("identity blob differs".into());
  }
  let keys =
    Keys { allowed: &identity.allowed, ixvm: &ixvm_key, aggr: &aggr_key };
  let cases = fixture["cases"].as_array().ok_or("missing cases")?;
  for case in cases {
    let label = case["label"].as_str().unwrap_or("?");
    if !matches!(case["type"].as_str(), Some("wrap" | "pair")) {
      let actual = extra_case(&identity, keys, case, shared_members)
        .map_err(|e| format!("{label}: {e}"))?;
      compare(label, &actual, &expected(case)?)?;
      continue;
    }
    let shape = u8::try_from(case["shape"].as_u64().unwrap_or(0))
      .map_err(|e| e.to_string())?;
    let mut owners: FxHashMap<Address, usize> = FxHashMap::default();
    let children: Vec<Loaded> = case["children"]
      .as_array()
      .map(Vec::as_slice)
      .unwrap_or_default()
      .iter()
      .enumerate()
      .map(|(shard, child)| {
        let subjects = addresses(&child["subjects"])?;
        for leaf in &subjects {
          owners.insert(leaf.clone(), shard);
        }
        let assumptions = match &child["assumptions"] {
          Value::Null => None,
          list => CanonicalTree::from_sorted(addresses(list)?)?,
        };
        let claim_bytes = bytes(&child["claim"])?;
        let claim = ixon::Claim::from_bytes(&claim_bytes)?;
        let ctx = claim.context().ok_or("a child claim is not CheckEnv")?;
        let statement = Statement::new(
          ctx.clone(),
          SubjectTree::canonical(subjects, ShardSet::singleton(shard, 3))?,
          assumptions,
        );
        if statement.claim_bytes != claim_bytes {
          return Err("a child statement does not rebuild its claim".into());
        }
        let kind = kind(&child["kind"])?;
        let claims = identity
          .claims_bytes(&identity.outer_claim(kind, &statement.claim_bytes));
        Ok(Loaded { kind, statement, proof: bytes(&child["proof"])?, claims })
      })
      .collect::<Result<_, String>>()?;
    for child in &children {
      for leaf in
        child.statement.assumptions.iter().flat_map(|t| t.leaves.iter())
      {
        owners.entry(leaf.clone()).or_insert(2);
      }
    }
    let field = |name: &str| bytes(&case[name]);
    let output;
    let actual = match case["type"].as_str() {
      Some("wrap") => {
        entries(&streams::wrap(keys, shape, as_child(&children[0]).transport()))
      },
      Some("pair") => {
        let structural = case["structural"].as_bool().unwrap_or(false);
        output = Statement::join(
          &children[0].statement,
          &children[1].statement,
          structural,
          &owners,
        )?;
        if output.claim_bytes != field("output")? {
          return Err(format!("{label}: the Rust fold reached another claim"));
        }
        entries(&streams::pair(
          keys,
          shape,
          as_child(&children[0]),
          as_child(&children[1]),
          &output,
          structural,
          &owners,
        )?)
      },
      other => return Err(format!("{label}: unknown case type {other:?}")),
    };
    compare(label, &actual, &expected(case)?)?;
  }
  Ok(cases.len())
}

type Entries = [(u64, Vec<u64>, Vec<u8>)];

fn compare(
  label: &str,
  actual: &Entries,
  expected: &Entries,
) -> Result<(), String> {
  if actual == expected {
    return Ok(());
  }
  let at = actual
    .iter()
    .zip(expected)
    .position(|(a, e)| a != e)
    .unwrap_or(actual.len().min(expected.len()));
  Err(format!(
    "{label}: streams differ at entry {at} ({} Rust, {} Lean): Rust {:?}, Lean {:?}",
    actual.len(),
    expected.len(),
    actual.get(at).map(|(c, k, p)| (c, k, p.len())),
    expected.get(at).map(|(c, k, p)| (c, k, p.len())),
  ))
}

fn main() {
  let args: Vec<String> = std::env::args().collect();
  let Some(path) = args.get(1) else {
    eprintln!(
      "usage: streams_parity AGGREGATION.json.streams.json [CATALOG.json]"
    );
    std::process::exit(2);
  };
  match run(path, args.get(2).map(String::as_str)) {
    Ok(count) => println!("{count} advice cases match Lean's streams"),
    Err(error) => {
      eprintln!("streams_parity: {error}");
      std::process::exit(1);
    },
  }
}
