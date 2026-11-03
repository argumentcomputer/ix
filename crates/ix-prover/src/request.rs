//! What a job executes, and how its advice is prepared. A leaf request
//! names a Rust-owned environment, a target or the manifest blocks a shard
//! owns, and the claim the caller expects; the prover recomputes the claim,
//! builds the witness from the environment and binds it as compact advice.
//! Claim forms without a Rust builder arrive as prepared [`Advice`].
use crate::{Field, PrepFailure, Program, protocol::Kind};
use aiur::{
  field::FieldBackend,
  hints::PreparedHints,
  library::{
    advice::{Advice, AdviceBuilder},
    io::Invocation,
  },
};
use ix_common::address::Address;
use ixon::{
  Claim,
  witness::{
    self, AdviceStream, ClaimWitness, Payload, StreamKey, WitnessRequest,
  },
};
use record_pool::BudgetError;
use rustc_hash::FxHashMap;
use std::{
  borrow::Cow,
  path::Path,
  sync::{Arc, OnceLock},
  time::Instant,
};

pub(crate) const IXVM_ENTRY: &str = "IxVM::verify_claim";
pub(crate) const RECURSIVE_ENTRIES: [&str; 2] =
  ["MultiStark::verify_multi_stark_proof", "MultiStark::ix_aggr"];

/// An immutable environment shared by every job that names it, with its
/// ownership index built on first use.
pub struct Environment {
  env: ixon::Env,
  /// Each check-schedule block (a projection's `block`, otherwise the
  /// constant itself) with the constants it owns, sorted.
  owners: OnceLock<Result<FxHashMap<Address, Vec<Address>>, String>>,
}

impl Environment {
  /// Map an `.ixe` file; constant bytes stay in the mapping.
  pub fn open(path: &Path) -> Result<Self, String> {
    Ok(Self::new(ixon::Env::get_anon_mmap(path)?))
  }

  /// Decode a serialized environment.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut cursor = bytes;
    let env = ixon::Env::get(&mut cursor)?;
    if !cursor.is_empty() {
      return Err("trailing environment bytes".into());
    }
    Ok(Self::new(env))
  }

  pub fn new(env: ixon::Env) -> Self {
    Self { env, owners: OnceLock::new() }
  }

  pub fn env(&self) -> &ixon::Env {
    &self.env
  }

  fn owners(&self) -> Result<&FxHashMap<Address, Vec<Address>>, String> {
    self
      .owners
      .get_or_init(|| {
        let mut owners: FxHashMap<Address, Vec<Address>> = FxHashMap::default();
        for entry in self.env.consts.iter() {
          let block =
            ixon::shard_claim::check_block(entry.key(), entry.value())?;
          owners.entry(block).or_default().push(entry.key().clone());
        }
        owners.values_mut().for_each(|owned| owned.sort_unstable());
        Ok(owners)
      })
      .as_ref()
      .map_err(Clone::clone)
  }

  /// The constants owned by `blocks`, sorted, as `Ix.Shard.ownedConstsPer`
  /// assigns them.
  pub fn owned(&self, blocks: &[Address]) -> Result<Vec<Address>, String> {
    let owners = self.owners()?;
    let mut owned: Vec<Address> = blocks
      .iter()
      .filter_map(|block| owners.get(block))
      .flatten()
      .cloned()
      .collect();
    owned.sort_unstable();
    owned.dedup();
    Ok(owned)
  }
}

/// A claim whose witness the prover builds from an environment.
#[derive(Clone)]
pub enum Leaf {
  /// `Check { ctx, target, assumptions: None }`.
  Check(Address),
  /// A shard `CheckEnv` over the constants these manifest blocks own.
  Shard(Vec<Address>),
}

#[derive(Clone)]
pub enum Request {
  /// An `Invocation` in the JSON interchange format: test fixtures and
  /// diagnostics.
  Invocation(Arc<[u8]>),
  /// A claim prepared by the prover; `expected` must equal the claim
  /// recomputed from the environment.
  Leaf { env: Arc<Environment>, leaf: Leaf, expected: Claim },
  /// An existing witness, already validated into compact advice.
  Advice { entry: String, args: Vec<u64>, advice: Advice<Field> },
  /// Executed: nothing is retained for proving.
  Released,
}

impl Request {
  /// `Check { ctx, target, assumptions: None }`, with the expected claim as
  /// `Ix.Claim.ser` bytes.
  pub fn check(
    env: Arc<Environment>,
    target: &[u8],
    expected: &[u8],
  ) -> Result<Self, String> {
    let target = Address::from_slice(target)
      .map_err(|_| "a target address has 32 bytes".to_owned())?;
    Ok(Self::Leaf {
      env,
      leaf: Leaf::Check(target),
      expected: parse_claim(expected)?,
    })
  }

  /// A shard `CheckEnv` over the constants owned by `blocks`, concatenated
  /// 32-byte addresses.
  pub fn shard(
    env: Arc<Environment>,
    blocks: &[u8],
    expected: &[u8],
  ) -> Result<Self, String> {
    let blocks = parse_addresses(blocks)?;
    if blocks.is_empty() {
      return Err("a shard request names at least one block".into());
    }
    Ok(Self::Leaf {
      env,
      leaf: Leaf::Shard(blocks),
      expected: parse_claim(expected)?,
    })
  }

  /// An existing witness as flat buffers; see [`buffer_advice`].
  pub fn buffers(
    entry: String,
    args: Vec<u64>,
    meta: &[u8],
    bytes: &[u8],
    words: &[u8],
  ) -> Result<Self, String> {
    let advice = buffer_advice(Field::default(), meta, bytes, words)?;
    Ok(Self::Advice { entry, args, advice })
  }
}

/// Decode `Ix.Claim.ser` bytes, rejecting trailing bytes.
pub fn parse_claim(bytes: &[u8]) -> Result<Claim, String> {
  let mut cursor = bytes;
  let claim = Claim::get(&mut cursor)?;
  if !cursor.is_empty() {
    return Err("trailing claim bytes".into());
  }
  Ok(claim)
}

/// Decode concatenated 32-byte addresses.
pub fn parse_addresses(bytes: &[u8]) -> Result<Vec<Address>, String> {
  let (chunks, rest) = bytes.as_chunks::<32>();
  if !rest.is_empty() {
    return Err("address list length is not a multiple of 32".into());
  }
  Ok(chunks.iter().map(|c| Address::from_slice(c).expect("32 bytes")).collect())
}

fn read_u64s(bytes: &[u8], what: &str) -> Result<Vec<u64>, String> {
  let (words, rest) = bytes.as_chunks::<8>();
  if !rest.is_empty() {
    return Err(format!("{what} length is not a multiple of 8"));
  }
  Ok(words.iter().map(|w| u64::from_le_bytes(*w)).collect())
}

/// Advice from flat buffers, streams in order. `meta` holds little-endian
/// words: per stream its channel, payload kind (0 bytes, 1 numeric words),
/// key length, the key words and the payload length. Byte payloads are
/// consecutive in `bytes`; numeric payloads are consecutive little-endian
/// words in `words`. Every buffer must be consumed exactly; channels, key
/// uniqueness and canonical words are validated as the advice is built.
pub fn buffer_advice(
  field: crate::Field,
  meta: &[u8],
  bytes: &[u8],
  words: &[u8],
) -> Result<Advice<Field>, String> {
  let meta = read_u64s(meta, "stream metadata")?;
  let words = read_u64s(words, "numeric payload")?;
  let mut builder = AdviceBuilder::new(field)?;
  let mut meta = meta.iter().copied();
  let (mut byte_at, mut word_at) = (0usize, 0usize);
  let truncated = || "truncated stream metadata".to_owned();
  while let Some(channel) = meta.next() {
    let kind = meta.next().ok_or_else(truncated)?;
    let key_len = usize::try_from(meta.next().ok_or_else(truncated)?)
      .map_err(|e| e.to_string())?;
    let key: Vec<u64> = meta.by_ref().take(key_len).collect();
    if key.len() != key_len {
      return Err(truncated());
    }
    let len = usize::try_from(meta.next().ok_or_else(truncated)?)
      .map_err(|e| e.to_string())?;
    match kind {
      0 => {
        let end = byte_at
          .checked_add(len)
          .filter(|&end| end <= bytes.len())
          .ok_or("byte payload exceeds its buffer")?;
        builder.push_bytes(channel, &key, &bytes[byte_at..end])?;
        byte_at = end;
      },
      1 => {
        let end = word_at
          .checked_add(len)
          .filter(|&end| end <= words.len())
          .ok_or("numeric payload exceeds its buffer")?;
        builder.push_words(channel, &key, &words[word_at..end])?;
        word_at = end;
      },
      _ => return Err(format!("unknown stream payload kind {kind}")),
    }
  }
  if byte_at != bytes.len() || word_at != words.len() {
    return Err("unused payload bytes".into());
  }
  Ok(builder.finish())
}

/// An upper estimate of the advice built from `streams`, charged before it
/// is allocated.
fn advice_size(streams: &[AdviceStream]) -> usize {
  streams.iter().map(stream_size).sum()
}

fn stream_size(stream: &AdviceStream) -> usize {
  let key = match &stream.key {
    StreamKey::ClaimDigest(_) => 8,
    StreamKey::Address(_) => 32,
  };
  stream.payload.len()
    + key * 8
    + size_of::<aiur::library::advice::StreamInfo>()
}

fn push_stream(
  builder: &mut AdviceBuilder<Field>,
  stream: &AdviceStream,
) -> Result<(), String> {
  let key = stream.key.words();
  let channel = u64::from(stream.channel);
  match &stream.payload {
    Payload::Bytes(bytes) => {
      builder.push_bytes(channel, &key, bytes.as_slice())
    },
    Payload::Tag(tag) => builder.push_words(channel, &key, &[*tag]),
  }
}

/// Compact advice for a witness, in its stream order.
pub fn witness_advice(
  field: Field,
  witness: &ClaimWitness,
) -> Result<Advice<Field>, String> {
  streams_advice(field, &witness.streams)
}

fn streams_advice(
  field: Field,
  streams: &[AdviceStream],
) -> Result<Advice<Field>, String> {
  let mut builder = AdviceBuilder::new(field)?;
  for stream in streams {
    push_stream(&mut builder, stream)?;
  }
  Ok(builder.finish())
}

/// Charges against a job's record reservation, or nothing for stateless
/// checks.
pub(crate) trait Charge {
  fn reserve(&self, bytes: usize) -> Result<(), BudgetError>;
  fn release(&self, bytes: usize);
}
impl Charge for record_pool::RecordReservation {
  fn reserve(&self, bytes: usize) -> Result<(), BudgetError> {
    record_pool::RecordReservation::reserve(self, bytes)
  }
  fn release(&self, bytes: usize) {
    record_pool::RecordReservation::release(self, bytes);
  }
}
pub(crate) struct Uncharged;
impl Charge for Uncharged {
  fn reserve(&self, _: usize) -> Result<(), BudgetError> {
    Ok(())
  }
  fn release(&self, _: usize) {}
}

/// Hold `actual` instead of a reservation of `charged` bytes.
fn settle(
  charge: &impl Charge,
  charged: usize,
  actual: usize,
) -> Result<(), BudgetError> {
  if actual > charged {
    charge.reserve(actual - charged)
  } else {
    charge.release(charged - actual);
    Ok(())
  }
}

/// A request ready to execute: entry, arguments and bound hints. The hints
/// own the advice payload; its metadata is released once they are bound.
pub(crate) struct Bound<'a> {
  pub entry: String,
  pub args: Vec<<Field as FieldBackend>::Element>,
  pub hints: PreparedHints<'a, Field>,
  /// Bytes charged for the advice and the hint maps. Release them once the
  /// hints and the request that owns the advice are dropped.
  pub charged: usize,
  pub report: serde_json::Map<String, serde_json::Value>,
}

/// Prepare `request` for `kind`, charging advice before it is allocated
/// and holding the payload's retained bytes afterwards.
pub(crate) fn bind<'a>(
  program: &'a Program,
  kind: Kind,
  request: &Request,
  charge: &impl Charge,
) -> Result<Bound<'a>, PrepFailure> {
  use serde_json::json;
  let other = PrepFailure::Other;
  let field = program.field();
  let mut report = serde_json::Map::new();
  let (entry, args, advice) = match request {
    Request::Invocation(input) => {
      // Parsing holds the decoded payloads alongside the text.
      let bytes = input.len() as u64;
      let parsing =
        usize::try_from(bytes.saturating_mul(8)).unwrap_or(usize::MAX);
      charge.reserve(parsing)?;
      let invocation: Invocation =
        serde_json::from_slice(input).map_err(|e| other(e.to_string()))?;
      let advice =
        Advice::from_streams(field, &invocation.streams).map_err(other)?;
      settle(charge, parsing, advice.retained_bytes().total())?;
      report.insert("input_json_bytes".into(), json!(bytes));
      (invocation.entry, invocation.args, Cow::Owned(advice))
    },
    Request::Leaf { env, leaf, expected } => {
      if kind != Kind::Ixvm {
        return Err(other("leaf requests need the IxVM artifact".into()));
      }
      let owned;
      let assume_binding =
        expected.context().is_some_and(|c| c.binding_assumed);
      let request = match leaf {
        Leaf::Check(target) => WitnessRequest::Check { target, assume_binding },
        Leaf::Shard(blocks) => {
          owned = env.owned(blocks).map_err(other)?;
          report.insert("owned_constants".into(), json!(owned.len()));
          WitnessRequest::ShardCheckEnv { owned: &owned, assume_binding }
        },
      };
      let (args, advice) =
        leaf_advice(env.env(), request, expected, field, charge, &mut report)?;
      (IXVM_ENTRY.to_owned(), args, Cow::Owned(advice))
    },
    Request::Advice { entry, args, advice } => {
      charge.reserve(advice.retained_bytes().total())?;
      (entry.clone(), args.clone(), Cow::Borrowed(advice))
    },
    Request::Released => {
      return Err(other("job input was already released".into()));
    },
  };
  bind_advice(program, kind, entry, args, &advice, charge, report)
}

/// The witness of `request`, whose claim must be `expected`, as compact
/// advice charged to `charge`, with the `verify_claim` arguments.
pub(crate) fn leaf_advice(
  env: &ixon::Env,
  request: WitnessRequest<'_>,
  expected: &Claim,
  field: Field,
  charge: &impl Charge,
  report: &mut serde_json::Map<String, serde_json::Value>,
) -> Result<(Vec<u64>, Advice<Field>), PrepFailure> {
  use serde_json::json;
  let other = PrepFailure::Other;
  let start = Instant::now();
  let witness = witness::prepare(env, request, expected)
    .map_err(|e| other(e.to_string()))?;
  report.insert("witness_seconds".into(), json!(start.elapsed().as_secs_f64()));
  report.insert("claim_digest".into(), json!(witness.digest.hex()));
  let estimate = advice_size(&witness.streams);
  charge.reserve(estimate)?;
  let advice = witness_advice(field, &witness).map_err(other)?;
  settle(charge, estimate, advice.retained_bytes().total())?;
  Ok((witness.digest_words().to_vec(), advice))
}

/// Binds advice whose payload is already charged: checks the entrypoint,
/// then charges the hint maps and builds the hints.
pub(crate) fn bind_advice<'a>(
  program: &'a Program,
  kind: Kind,
  entry: String,
  args: Vec<u64>,
  advice: &Advice<Field>,
  charge: &impl Charge,
  mut report: serde_json::Map<String, serde_json::Value>,
) -> Result<Bound<'a>, PrepFailure> {
  use serde_json::json;
  let other = PrepFailure::Other;
  let field = program.field();
  let valid = match kind {
    Kind::Ixvm => entry == IXVM_ENTRY && args.len() == 8,
    Kind::Recursion => {
      RECURSIVE_ENTRIES.contains(&entry.as_str()) && args.len() == 16
    },
  };
  if !valid {
    return Err(other("wrong application entrypoint".into()));
  }
  let args = field.decode(&args).map_err(other)?;
  let retained = advice.retained_bytes();
  // The hint providers copy every stream's key and metadata value into their
  // own maps, estimated at the size of the stream metadata. Charged before
  // binding, it stays charged with the payload until the hints are dropped.
  charge.reserve(retained.metadata)?;
  let binding = Instant::now();
  let hints = match kind {
    Kind::Ixvm => ixvm::prepare_advice(program, advice),
    Kind::Recursion => stark_verifier::prepare_advice(program, advice),
  }
  .map_err(other)?;
  report.insert(
    "hint_preparation_seconds".into(),
    json!(binding.elapsed().as_secs_f64()),
  );
  report.insert("advice_payload_bytes".into(), json!(retained.payload));
  report.insert("advice_metadata_bytes".into(), json!(retained.metadata));
  let charged = retained.total() + retained.metadata;
  report.insert("advice_reserved_bytes".into(), json!(charged));
  Ok(Bound { entry, args, hints, charged, report })
}

#[cfg(test)]
mod tests {
  use super::*;
  use aiur::field::NativeField;

  fn encode(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
  }

  #[test]
  fn buffer_validation() {
    let field = NativeField::default();
    let meta = encode(&[2, 0, 1, 7, 3, 3, 1, 1, 7, 1]);
    let advice =
      buffer_advice(field, &meta, &[1, 2, 3], &encode(&[300])).unwrap();
    assert_eq!(advice.streams().len(), 2);
    assert!(advice.is_byte_channel(2) && !advice.is_byte_channel(3));
    // Lengths must be consumed exactly.
    assert!(
      buffer_advice(field, &meta, &[1, 2, 3, 4], &encode(&[300])).is_err()
    );
    assert!(buffer_advice(field, &meta, &[1, 2], &encode(&[300])).is_err());
    assert!(
      buffer_advice(
        field,
        &meta[..meta.len() - 8],
        &[1, 2, 3],
        &encode(&[300])
      )
      .is_err()
    );
    assert!(buffer_advice(field, &meta[..5], &[], &[]).is_err());
    // Duplicate keys, out-of-range channels, unknown kinds, noncanonical words.
    let duplicate = encode(&[2, 0, 1, 7, 1, 2, 0, 1, 7, 1]);
    assert!(buffer_advice(field, &duplicate, &[1, 2], &[]).is_err());
    assert!(buffer_advice(field, &encode(&[256, 0, 0, 0]), &[], &[]).is_err());
    assert!(buffer_advice(field, &encode(&[1, 2, 0, 0]), &[], &[]).is_err());
    assert!(
      buffer_advice(field, &encode(&[1, 1, 0, 1]), &[], &encode(&[u64::MAX]))
        .is_err()
    );
    assert!(parse_addresses(&[0; 33]).is_err());
    assert_eq!(parse_addresses(&[0; 64]).unwrap().len(), 2);
    assert!(parse_claim(&[]).is_err());
  }
}
