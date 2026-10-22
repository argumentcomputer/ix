//! Host advice for the ordinary Aiur recursive verifier. Source and compilation
//! live in the independent MultiStark Lean package; no generated Rust kernels.
use aiur::{
  bytecode::{CheckedProgram, Type},
  field::FieldBackend,
  hints::{HintChannels, PreparedHints},
  library::io::Streams,
  maps::MapOverrides,
};

pub fn prepare<'a, B: FieldBackend>(
  program: &'a CheckedProgram<B>,
  streams: &Streams,
) -> Result<PreparedHints<'a, B>, String> {
  let field = program.field();
  let arenas = streams.prepare(field)?;
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, field)?;
  aiur::library::u64::register(&mut channels, field)?;
  channels.insert_fixed::<1, 1>(
    "goldilocks.inverse",
    Type::Field,
    Type::Field,
    move |[x]| Ok([field.inverse(x).unwrap_or_else(|| field.zero())]),
  )?;
  arenas.register_read::<1>("stark.io.read1", false, &mut channels)?;
  arenas.register_read::<8>("stark.io.read8", false, &mut channels)?;
  arenas.register_read::<64>("stark.io.read64", false, &mut channels)?;
  let mut data = arenas.metadata(
    "stark.io.info",
    Type::Tuple { items: vec![Type::Field; 2] },
    None,
    |s| s.key.len() == 1,
    false,
  )?;
  data.extend(arenas.metadata(
    "stark.io.address",
    Type::Tuple {
      items: vec![Type::Field, Type::Tuple { items: vec![Type::Field; 32] }],
    },
    None,
    |s| s.key.len() == 32,
    false,
  )?);
  data.extend(arenas.metadata(
    "stark.io.digest",
    Type::Tuple { items: vec![Type::Field; 8] },
    Some(4),
    |s| s.channel == 4 && s.key.len() == 8,
    false,
  )?);
  let prepared = program.prepare_hint_channels(&data, &channels)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(program, &mut maps)?;
  prepared.with_map_overrides(&maps)
}

pub fn digest_words(bytes: &[u8]) -> Vec<u64> {
  blake3::hash(bytes)
    .as_bytes()
    .as_chunks::<4>()
    .0
    .iter()
    .map(|b| u64::from(u32::from_le_bytes(*b)))
    .collect()
}

pub fn claims_bytes(claims: &[Vec<multi_stark::types::Val>]) -> Vec<u8> {
  use multi_stark::p3_field::PrimeField64;
  let mut bytes = (claims.len() as u64).to_le_bytes().to_vec();
  for claim in claims {
    bytes.extend_from_slice(&(claim.len() as u64).to_le_bytes());
    for word in claim {
      bytes.extend_from_slice(&word.as_canonical_u64().to_le_bytes());
    }
  }
  bytes
}

pub use aiur::library::io::Invocation;

/// The proof is advice. Only the key and public claims enter the statement.
pub fn invocation(key: &[u8], claims: &[u8], proof: &[u8]) -> Invocation {
  use aiur::library::io::Stream;
  let mut args = digest_words(key);
  args.extend(digest_words(claims));
  let streams = Streams(
    [proof, key, claims]
      .iter()
      .enumerate()
      .map(|(channel, bytes)| Stream {
        channel: channel as u64,
        key: vec![0],
        values: bytes.iter().map(|&b| u64::from(b)).collect(),
      })
      .collect(),
  );
  Invocation {
    entry: "MultiStark::verify_multi_stark_proof".into(),
    args,
    streams,
  }
}
