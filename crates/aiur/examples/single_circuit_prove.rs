//! Prove and verify a Lean-exported formally certified single-circuit Goldilocks
//! STARK end-to-end in `multi-stark`.
//!
//! Auto-detects both certified single-circuit layout formats from `LAYOUT.json`:
//! - `ix-wide-layout-1` (`wide_export --single-circuit --pow2-rows [--vector-rom K]`,
//!   backed by `Aiur.Tiling.SingleCircuit.wide_single_circuit_sound_goldilocks`
//!   and `Aiur.Tiling.VectorRom.wide_vector_rom_single_circuit_sound_goldilocks`)
//! - `ix-tiling-v2-layout-1` (`tiling_export2 --goldilocks --single-circuit --pow2-rows`,
//!   backed by `Aiur.Tiling.SingleCircuit.narrow_compact_single_circuit_sound_goldilocks`)
//!
//! Usage:
//!   single_circuit_prove PACKAGE.ixa LAYOUT.json FIXED.bin
//!     [--args N,N,...] [--advice ADVICE.ixa] [--tamper-hint CHANNEL]
//!     [--pin PIN.json] [--stark-io KEY.bin CLAIMS.bin PROOF.bin]
//!     [--controls] [--stark-128] [--fri-mla K] [--fri-lfp K]
//!     [--log-blowup K] [--num-queries K] [--query-pow K] [--commit-pow K]
//!     [--lookup-group K] [--no-check] [--proof-out PATH] [--report-out PATH]

use aiur::artifact::{
  self, Digest, EXECUTION_MAGIC, ExecutionPackage, PACKAGE_MAGIC, Package,
};
use aiur::bytecode::{CheckedProgram, Program, Type};
use aiur::field::{FieldBackend, NativeField};
use aiur::hints::{HintChannels, HintEntry, PreparedHints};
use aiur::library::advice::{Advice, Entry as AdviceEntry, Payload};
use aiur::library::io::StreamAdvice;
use aiur::maps::MapOverrides;
use aiur::trace::TracePlan;
use aiur::trace::stark::{MAX_BATCH_ROWS, Parameters, Proof};
use multi_stark::eval::VarValues;
use multi_stark::expr::Expr;
use multi_stark::graph::ConstraintGraph;
use multi_stark::lookup::{
  Lookup, MAX_LOOKUP_GROUP, logup_max_degree, stage2_width,
};
use multi_stark::p3_adapter::fri_batching::FriBatching;
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use multi_stark::p3_matrix::Matrix;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::system::{CircuitInputs, System, extension_params};
use multi_stark::types::{
  CommitmentParameters, FriParameters, GoldilocksBlake3V6Config, Val,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::{Value, json};
use std::error::Error;
use std::path::Path;
use std::sync::atomic::Ordering;
use std::time::Instant;

const WIDE_LAYOUT_FORMAT: &str = "ix-wide-layout-1";
const TILING_V2_LAYOUT_FORMAT: &str = "ix-tiling-v2-layout-1";
const FIXED_MAGIC: &[u8; 8] = b"IXTLFX01";
const CALL_TAG: u64 = 1;
const ROM_TAG: u64 = 2;
const CHUNK_STRIDE: u64 = 1u64 << 32;
const COMPRESS_WRAP_ENTRY: &str = "CompressWrap::verify_root";
const MULTI_STARK_ENTRY: &str = "MultiStark::verify_multi_stark_proof";
const COMPRESS_WRAP_STATEMENT_DOMAIN: &[u8; 20] = b"ix/compress-wrap/v1\0";

const USAGE: &str = "usage: single_circuit_prove PACKAGE.ixa LAYOUT.json FIXED.bin \
  [--args N,N,...] [--advice ADVICE.ixa] [--tamper-hint CHANNEL] \
  [--pin PIN.json] [--stark-io KEY.bin CLAIMS.bin PROOF.bin] \
  [--controls] [--stark-128] [--fri-mla K] [--fri-lfp K] \
  [--log-blowup K] [--num-queries K] [--query-pow K] [--commit-pow K] \
  [--lookup-group K] [--no-check] [--proof-out PATH] [--report-out PATH]";

struct Cli {
  package: String,
  layout: String,
  fixed: String,
  override_args: Option<Vec<u64>>,
  advice: Option<String>,
  tamper_hint: Option<String>,
  pin: Option<String>,
  stark_io: Option<(String, String, String)>,
  controls: bool,
  check: bool,
  log_blowup: usize,
  num_queries: usize,
  commit_pow: usize,
  query_pow: usize,
  fri_mla: usize,
  fri_lfp: usize,
  lookup_group: Option<usize>,
  proof_out: Option<String>,
  report_out: Option<String>,
}

fn parse_usize_flag(
  flag: &str,
  raw: &mut std::env::Args,
) -> Result<usize, String> {
  let value = raw.next().ok_or_else(|| format!("{flag} expects an integer"))?;
  value
    .parse::<usize>()
    .map_err(|e| format!("invalid {flag} value {value:?}: {e}"))
}

fn parse_cli() -> Result<Cli, String> {
  let defaults = Parameters::DEFAULT;
  let mut pos = Vec::new();
  let mut override_args: Option<Vec<u64>> = None;
  let mut advice: Option<String> = None;
  let mut tamper_hint: Option<String> = None;
  let mut pin: Option<String> = None;
  let mut stark_io: Option<(String, String, String)> = None;
  let mut controls = false;
  let mut check = true;
  let mut log_blowup = defaults.log_blowup;
  let mut num_queries = defaults.num_queries;
  let mut commit_pow = defaults.commit_proof_of_work_bits;
  let mut query_pow = defaults.query_proof_of_work_bits;
  let mut fri_mla = 1usize;
  let mut fri_lfp = 0usize;
  let mut lookup_group: Option<usize> = None;
  let mut proof_out: Option<String> = None;
  let mut report_out: Option<String> = None;

  let mut raw = std::env::args();
  let _exe = raw.next();
  while let Some(arg) = raw.next() {
    match arg.as_str() {
      "--args" => {
        let list =
          raw.next().ok_or("--args expects a comma-separated integer list")?;
        override_args = Some(
          list
            .split(',')
            .filter(|w| !w.is_empty())
            .map(|w| {
              w.parse::<u64>()
                .map_err(|e| format!("invalid --args element {w:?}: {e}"))
            })
            .collect::<Result<_, _>>()?,
        );
      },
      "--advice" => {
        advice = Some(raw.next().ok_or("--advice expects a file path")?);
      },
      "--tamper-hint" => {
        tamper_hint =
          Some(raw.next().ok_or("--tamper-hint expects a channel name")?);
      },
      "--pin" => {
        pin = Some(raw.next().ok_or("--pin expects a file path")?);
      },
      "--stark-io" => {
        let key = raw
          .next()
          .ok_or("--stark-io expects KEY.bin CLAIMS.bin PROOF.bin")?;
        let claims = raw
          .next()
          .ok_or("--stark-io expects KEY.bin CLAIMS.bin PROOF.bin")?;
        let proof = raw
          .next()
          .ok_or("--stark-io expects KEY.bin CLAIMS.bin PROOF.bin")?;
        stark_io = Some((key, claims, proof));
      },
      "--controls" => controls = true,
      "--stark-128" => {
        log_blowup = 3;
        num_queries = 78;
        query_pow = 20;
      },
      "--no-check" => check = false,
      "--fri-mla" => fri_mla = parse_usize_flag("--fri-mla", &mut raw)?,
      "--fri-lfp" => fri_lfp = parse_usize_flag("--fri-lfp", &mut raw)?,
      "--log-blowup" => {
        log_blowup = parse_usize_flag("--log-blowup", &mut raw)?;
      },
      "--num-queries" => {
        num_queries = parse_usize_flag("--num-queries", &mut raw)?;
      },
      "--query-pow" => query_pow = parse_usize_flag("--query-pow", &mut raw)?,
      "--commit-pow" => {
        commit_pow = parse_usize_flag("--commit-pow", &mut raw)?;
      },
      "--lookup-group" => {
        lookup_group = Some(parse_usize_flag("--lookup-group", &mut raw)?);
      },
      "--proof-out" => {
        proof_out = Some(raw.next().ok_or("--proof-out expects a file path")?);
      },
      "--report-out" => {
        report_out =
          Some(raw.next().ok_or("--report-out expects a file path")?);
      },
      "-h" | "--help" => return Err(USAGE.into()),
      other if other.starts_with("--") => {
        return Err(format!("unknown option {other}\n{USAGE}"));
      },
      other => pos.push(other.to_owned()),
    }
  }
  if pos.len() != 3 {
    return Err(USAGE.into());
  }
  if tamper_hint.is_some() && advice.is_none() {
    return Err("--tamper-hint requires --advice ADVICE.ixa".into());
  }
  if !(1..=10).contains(&fri_mla) {
    return Err(format!("--fri-mla must be in 1..=10, got {fri_mla}"));
  }
  if log_blowup == 0 || log_blowup > 6 {
    return Err(format!("--log-blowup must be in 1..=6, got {log_blowup}"));
  }
  if num_queries == 0 {
    return Err("--num-queries must be positive".into());
  }
  let mut iter = pos.into_iter();
  Ok(Cli {
    package: iter.next().unwrap(),
    layout: iter.next().unwrap(),
    fixed: iter.next().unwrap(),
    override_args,
    advice,
    tamper_hint,
    pin,
    stark_io,
    controls,
    check,
    log_blowup,
    num_queries,
    commit_pow,
    query_pow,
    fri_mla,
    fri_lfp,
    lookup_group,
    proof_out,
    report_out,
  })
}

fn peak_rss_kb() -> Option<u64> {
  let status = std::fs::read_to_string("/proc/self/status").ok()?;
  let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
  line.split_whitespace().nth(1)?.parse().ok()
}

fn load_advice_program(
  path: &str,
) -> Result<(Program, Digest), Box<dyn Error>> {
  let (raw_bytes, digest) = artifact::read(Path::new(path))?;
  let package = if raw_bytes.starts_with(PACKAGE_MAGIC) {
    Package::decode(&raw_bytes)
      .map_err(|e| format!("invalid advice package {path}: {e}"))?
  } else if raw_bytes.starts_with(EXECUTION_MAGIC) {
    ExecutionPackage::decode(&raw_bytes)
      .map_err(|e| format!("invalid advice execution package {path}: {e}"))?
      .package
  } else {
    return Err(format!(
      "unrecognized advice artifact magic in {path} (expected IXAIURP\\0 or IXAIURX\\0)"
    )
    .into());
  };
  Ok((package.program, digest))
}

/// The compiled program alone, as `ixcc-aiur` hashes it for the pin: a
/// package with the file's program and no trace section.
fn program_only(program: &Program) -> Vec<u8> {
  Package { program: program.clone(), trace: None }.encode()
}

/// Whether `program` (a package without a trace section) is, up to its last
/// byte (the trace option's tag), the embedded package's prefix in `file`.
fn embedded(file: &[u8], program: &[u8]) -> bool {
  let Some((_, prefix)) = program.split_last() else { return false };
  let Some(start) =
    file.windows(PACKAGE_MAGIC.len()).take(32).position(|w| w == PACKAGE_MAGIC)
  else {
    return false;
  };
  file.get(start..start + prefix.len()) == Some(prefix)
}

/// Check the pin `ixcc-aiur` wrote beside a package (`PACKAGE.ixa.pin.json`)
/// against the file's bytes, before anything is decoded for proving: the
/// BLAKE3 of the whole file (`package_blake3`), and the BLAKE3 of the
/// compiled program alone (`program_blake3`), recomputed from the decoded
/// program, whose bytes must also be the file's own. Any mismatch refuses.
fn check_pin(
  pin_path: &str,
  file: &[u8],
  digest: Digest,
) -> Result<Value, Box<dyn Error>> {
  let pin: Value = serde_json::from_slice(&std::fs::read(pin_path)?)?;
  let pinned = |key: &str| -> Result<Digest, String> {
    let hex =
      pin[key].as_str().ok_or_else(|| format!("pin {pin_path}: no {key}"))?;
    Digest::from_hex(hex)
  };
  let package_pin = pinned("package_blake3")?;
  let program_pin = pinned("program_blake3")?;
  let mut mismatches = Vec::new();
  if digest != package_pin {
    mismatches
      .push(format!("package_blake3: file {digest}, pin {package_pin}"));
  }
  let decoded_program = if file.starts_with(PACKAGE_MAGIC) {
    Package::decode(file).map(|pkg| pkg.program)
  } else if file.starts_with(EXECUTION_MAGIC) {
    ExecutionPackage::decode(file).map(|exec| exec.package.program)
  } else {
    Err(
      "unrecognized artifact magic (expected IXAIURP\\0 or IXAIURX\\0)".into(),
    )
  };
  match decoded_program {
    Ok(prog) => {
      let program = program_only(&prog);
      let program_digest = Digest::of(&program);
      if program_digest != program_pin {
        mismatches.push(format!(
          "program_blake3: file {program_digest}, pin {program_pin}"
        ));
      }
      if !embedded(file, &program) {
        mismatches.push(
          "program_blake3: the re-encoded program is not the file's bytes"
            .into(),
        );
      }
    },
    Err(error) => mismatches
      .push(format!("program_blake3: the file does not decode ({error})")),
  }
  if !mismatches.is_empty() {
    return Err(
      format!("pin {pin_path} refused: {}", mismatches.join("; ")).into(),
    );
  }
  Ok(json!({
    "pin": pin_path,
    "package_blake3": package_pin.to_string(),
    "program_blake3": program_pin.to_string(),
    "checked": true,
  }))
}

struct StarkIoFiles {
  key: Vec<u8>,
  claims: Vec<u8>,
  proof: Vec<u8>,
  key_blake3: String,
  claims_blake3: String,
  proof_blake3: String,
}

fn load_stark_io(
  key_path: &str,
  claims_path: &str,
  proof_path: &str,
) -> Result<StarkIoFiles, String> {
  let key = std::fs::read(key_path)
    .map_err(|e| format!("failed to read --stark-io key {key_path}: {e}"))?;
  let claims = std::fs::read(claims_path).map_err(|e| {
    format!("failed to read --stark-io claims {claims_path}: {e}")
  })?;
  let proof = std::fs::read(proof_path).map_err(|e| {
    format!("failed to read --stark-io proof {proof_path}: {e}")
  })?;
  let key_blake3 = blake3::hash(&key).to_hex().to_string();
  let claims_blake3 = blake3::hash(&claims).to_hex().to_string();
  let proof_blake3 = blake3::hash(&proof).to_hex().to_string();
  Ok(StarkIoFiles {
    key,
    claims,
    proof,
    key_blake3,
    claims_blake3,
    proof_blake3,
  })
}

fn digest_words(bytes: &[u8]) -> Vec<u64> {
  blake3::hash(bytes)
    .as_bytes()
    .as_chunks::<4>()
    .0
    .iter()
    .map(|b| u64::from(u32::from_le_bytes(*b)))
    .collect()
}

fn stark_io_default_args(entry: &str, io: &StarkIoFiles) -> Vec<u64> {
  if entry == COMPRESS_WRAP_ENTRY {
    let mut preimage = [0u8; COMPRESS_WRAP_STATEMENT_DOMAIN.len() + 64];
    preimage[..COMPRESS_WRAP_STATEMENT_DOMAIN.len()]
      .copy_from_slice(COMPRESS_WRAP_STATEMENT_DOMAIN);
    preimage[COMPRESS_WRAP_STATEMENT_DOMAIN.len()
      ..COMPRESS_WRAP_STATEMENT_DOMAIN.len() + 32]
      .copy_from_slice(blake3::hash(&io.key).as_bytes());
    preimage[COMPRESS_WRAP_STATEMENT_DOMAIN.len() + 32..]
      .copy_from_slice(blake3::hash(&io.claims).as_bytes());
    let mut args = vec![0u64; 8];
    args.extend(digest_words(&preimage));
    args
  } else if entry == MULTI_STARK_ENTRY {
    let mut args = digest_words(&io.key);
    args.extend(digest_words(&io.claims));
    args
  } else {
    Vec::new()
  }
}

fn register_stark_io(
  channels: &mut HintChannels<Val>,
  field: NativeField<Val>,
  io: &StarkIoFiles,
) -> Result<(), String> {
  channels.insert_fixed::<1, 1>(
    "goldilocks.inverse",
    Type::Field,
    Type::Field,
    move |[x]| Ok([field.inverse(x).unwrap_or_else(|| field.zero())]),
  )?;
  let advice = Advice::from_entries(
    field,
    [&io.proof, &io.key, &io.claims].into_iter().enumerate().map(
      |(channel, bytes)| AdviceEntry {
        channel: channel as u64,
        key: &[0],
        payload: Payload::Bytes(bytes),
      },
    ),
  )?;
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  let lens = [
    u64::try_from(io.proof.len())
      .map_err(|e| format!("PROOF.bin length overflow: {e}"))?,
    u64::try_from(io.key.len())
      .map_err(|e| format!("KEY.bin length overflow: {e}"))?,
    u64::try_from(io.claims.len())
      .map_err(|e| format!("CLAIMS.bin length overflow: {e}"))?,
  ];
  channels.insert_fixed::<2, 2>(
    "stark.io.info",
    pair.clone(),
    pair,
    move |[channel, subkey]| {
      let ch = field
        .try_to_u64(channel)
        .map_err(|e| format!("stark.io.info channel: {e}"))?;
      let sub = field
        .try_to_u64(subkey)
        .map_err(|e| format!("stark.io.info key: {e}"))?;
      if sub != 0 {
        return Err(format!(
          "stark.io.info: unexpected stream key ({ch}, {sub})"
        ));
      }
      let idx = usize::try_from(ch)
        .map_err(|e| format!("stark.io.info channel {ch} overflow: {e}"))?;
      let len = *lens
        .get(idx)
        .ok_or_else(|| format!("stark.io.info: unknown channel {ch}"))?;
      Ok([field.zero(), field.from_u64(len)])
    },
  )?;
  advice.register_read::<1>("stark.io.read1", false, channels)?;
  advice.register_read::<8>("stark.io.read8", false, channels)?;
  advice.register_read::<64>("stark.io.read64", false, channels)?;
  Ok(())
}

fn build_hints<'a>(
  program: &'a CheckedProgram<NativeField<Val>>,
  embedded_hints: &[HintEntry],
  stark_io: Option<&StarkIoFiles>,
  advice_raw: Option<&Program>,
  tamper_channel: Option<&str>,
) -> Result<
  (
    PreparedHints<'a, NativeField<Val>>,
    Vec<String>,
    Option<std::sync::Arc<std::sync::atomic::AtomicUsize>>,
  ),
  String,
> {
  let field = program.field();
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, field)?;
  aiur::library::u64::register(&mut channels, field)?;
  aiur::library::ixcc::register(&mut channels, field)?;
  if let Some(io) = stark_io {
    register_stark_io(&mut channels, field, io)?;
  }
  let mut guess_channels = Vec::new();
  let mut tamper_hits = None;
  if let Some(adv_raw) = advice_raw {
    let checked_adv = adv_raw.clone().check_field::<Val>()?;
    if let Some(ch) = tamper_channel {
      let (regs, hits) = aiur::library::ixcc::register_tampered_advice_program(
        &mut channels,
        program,
        checked_adv,
        ch,
      )?;
      guess_channels = regs;
      tamper_hits = Some(hits);
    } else {
      guess_channels = aiur::library::ixcc::register_advice_program(
        &mut channels,
        program,
        checked_adv,
      )?;
    }
  }
  let prepared = program.prepare_hint_channels(embedded_hints, &channels)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(program, &mut maps)?;
  let hints = prepared.with_map_overrides(&maps)?;
  Ok((hints, guess_channels, tamper_hits))
}

fn natural(v: &Value, ctx: &str) -> Result<usize, String> {
  v.as_u64()
    .and_then(|n| usize::try_from(n).ok())
    .ok_or_else(|| format!("{ctx}: expected natural number, got {v}"))
}

fn scalar(v: &Value, ctx: &str) -> Result<Val, String> {
  let n = match v {
    Value::String(s) => {
      s.parse::<u64>().map_err(|e| format!("{ctx}: invalid scalar {s}: {e}"))?
    },
    _ => v
      .as_u64()
      .ok_or_else(|| format!("{ctx}: expected field element, got {v}"))?,
  };
  if n >= Val::ORDER_U64 {
    return Err(format!("{ctx}: scalar {n} exceeds Goldilocks modulus"));
  }
  Ok(Val::from_u64(n))
}

#[derive(Clone, Debug)]
enum ConstituentKind {
  Unit { chip: String },
  Map { length: usize },
  Rom { words: usize, rom_vector: usize },
  Shard { shard_index: usize },
  CompactMap,
  CompactRom,
}

#[derive(Clone, Debug)]
struct Constituent {
  kind: ConstituentKind,
  rows: usize,
  main_offset: usize,
  main_width: usize,
  fixed_offset: usize,
  fixed_width: usize,
  active_col: Option<usize>,
}

#[derive(Clone, Copy, Debug)]
enum V2Term {
  Lin(Val, usize),
  Prod(Val, usize, usize),
}

#[derive(Clone, Debug)]
enum V2Slot {
  Column(usize),
  Sum { k: Val, terms: Vec<V2Term> },
  Key,
  Invocation,
}

#[derive(Clone, Debug)]
enum V2Lane {
  Empty,
  Gate { qm: Val, q: [Val; 4], qc: Val, cells: [Option<usize>; 4] },
  Msg { ts: u64, mk: Val, mc: Val, cells: [Option<usize>; 4] },
}

#[derive(Clone, Debug)]
enum V2Row {
  Gate {
    lanes: Vec<V2Lane>,
    spans: Vec<(usize, usize)>,
  },
  Message {
    ts: u64,
    mk: Val,
    mc: Val,
    receive_key: bool,
    cells: Vec<Option<usize>>,
  },
}

impl V2Row {
  fn cell(&self, j: usize) -> Option<usize> {
    match self {
      Self::Gate { lanes, .. } => match &lanes[j / 4] {
        V2Lane::Empty => None,
        V2Lane::Gate { cells, .. } | V2Lane::Msg { cells, .. } => cells[j % 4],
      },
      Self::Message { cells, .. } => cells[j],
    }
  }
}

#[derive(Clone, Debug)]
struct V2Template {
  slots: Vec<V2Slot>,
  rows: Vec<V2Row>,
}

#[derive(Clone, Copy, Debug)]
enum V2WideNode {
  Const(Val),
  Var(usize),
  Add(usize, usize),
  Sub(usize, usize),
  Mul(usize, usize),
  Neg(usize),
}

#[derive(Clone, Debug)]
struct V2WideGraph {
  nodes: Vec<V2WideNode>,
  lookups: Vec<(usize, Vec<usize>)>,
}

#[derive(Clone, Debug)]
struct V2CircuitMeta {
  chip: String,
  unroll_stages: Option<usize>,
  wide_width: usize,
  wide_graph: Option<V2WideGraph>,
}

struct TilingV2Data {
  shard_width: usize,
  shards: usize,
  caps: Vec<usize>,
  places: usize,
  ids_per_shard: u64,
  request: Vec<Vec<Val>>,
  code_to_bus: FxHashMap<u64, (u64, u64, bool)>,
  bus_to_code: FxHashMap<(u64, u64), (u64, bool)>,
  circuits: Vec<V2CircuitMeta>,
  templates: Vec<V2Template>,
}

enum LayoutKind {
  Wide { request: Vec<Val>, rom_vector: usize },
  TilingV2(Box<TilingV2Data>),
}

struct SingleCircuitLayout {
  kind: LayoutKind,
  rows: usize,
  main_width: usize,
  fixed_width: usize,
  num_constraints: usize,
  num_lookups: usize,
  bound: u64,
  constituents: Vec<Constituent>,
  constraints: Vec<Expr<Val>>,
  lookups: Vec<Lookup<Expr<Val>>>,
}

fn parse_graph(
  v: &Value,
  expected_main_width: usize,
  expected_fixed_width: usize,
) -> Result<(Vec<Expr<Val>>, Vec<Lookup<Expr<Val>>>), String> {
  let width = natural(&v["width"], "circuit.width")?;
  let fixed_width = natural(&v["fixed_width"], "circuit.fixed_width")?;
  if width != expected_main_width || fixed_width != expected_fixed_width {
    return Err(format!(
      "circuit dimensions ({width} main, {fixed_width} fixed) disagree with \
       single_circuit ({expected_main_width} main, {expected_fixed_width} fixed)"
    ));
  }
  let column = |x: usize| {
    u32::try_from(x).map_err(|e| format!("column {x} overflows u32: {e}"))
  };
  let raw_nodes = v["nodes"]
    .as_array()
    .ok_or("single_circuit.circuit missing nodes array")?;
  let mut nodes: Vec<Expr<Val>> = Vec::with_capacity(raw_nodes.len());
  for (i, n) in raw_nodes.iter().enumerate() {
    let arr =
      n.as_array().ok_or_else(|| format!("graph node {i} not array"))?;
    let op = arr
      .first()
      .and_then(Value::as_str)
      .ok_or_else(|| format!("graph node {i} missing op"))?;
    let child = |k: usize| -> Result<Expr<Val>, String> {
      let idx = natural(
        arr.get(k).ok_or_else(|| {
          format!("graph node {i} ({op}) missing operand {k}")
        })?,
        "graph operand",
      )?;
      if idx >= i {
        return Err(format!(
          "graph node {i} references non-topological operand {idx}"
        ));
      }
      Ok(nodes[idx].clone())
    };
    let expr = match op {
      "const" => Expr::constant(scalar(
        arr.get(1).ok_or_else(|| format!("const node {i} missing value"))?,
        "const node",
      )?),
      "var" => {
        let x = natural(
          arr.get(1).ok_or_else(|| format!("var node {i} missing index"))?,
          "var node",
        )?;
        if x < width {
          Expr::main(column(x)?)
        } else if x < width + fixed_width {
          Expr::preprocessed(column(x - width)?)
        } else {
          return Err(format!(
            "var {x} outside {width} main + {fixed_width} fixed columns"
          ));
        }
      },
      "add" => child(1)? + child(2)?,
      "sub" => child(1)? - child(2)?,
      "mul" => child(1)? * child(2)?,
      "neg" => -child(1)?,
      other => return Err(format!("unknown graph node op {other:?}")),
    };
    nodes.push(expr);
  }
  let lookup_node = |x: &Value, ctx: &str| -> Result<Expr<Val>, String> {
    let idx = natural(x, ctx)?;
    nodes
      .get(idx)
      .cloned()
      .ok_or_else(|| format!("{ctx}: node index {idx} out of range"))
  };
  let constraints = v["zeros"]
    .as_array()
    .ok_or("single_circuit.circuit missing zeros array")?
    .iter()
    .map(|z| lookup_node(z, "zeros"))
    .collect::<Result<Vec<_>, _>>()?;
  let lookups = v["lookups"]
    .as_array()
    .ok_or("single_circuit.circuit missing lookups array")?
    .iter()
    .map(|l| {
      let arr = l.as_array().ok_or("lookup entry not an array")?;
      let m = lookup_node(
        arr.first().ok_or("lookup missing multiplicity")?,
        "lookup.multiplicity",
      )?;
      let args = arr
        .get(1)
        .and_then(Value::as_array)
        .ok_or("lookup missing args array")?
        .iter()
        .map(|a| lookup_node(a, "lookup.arg"))
        .collect::<Result<Vec<_>, _>>()?;
      // Lean's IChip.lower / mapCircuit / romCircuit already encode signs in
      // multiplicity (-mult for providers, +enable for consumers).
      Ok(Lookup::push(m, args))
    })
    .collect::<Result<Vec<_>, String>>()?;
  Ok((constraints, lookups))
}

fn parse_opt_cell(
  v: &Value,
  slots: &[V2Slot],
  ctx: &str,
) -> Result<Option<usize>, String> {
  if v.is_null() {
    return Ok(None);
  }
  let s = natural(v, ctx)?;
  let slot = slots
    .get(s)
    .ok_or_else(|| format!("{ctx}: slot index {s} out of range"))?;
  if matches!(slot, V2Slot::Invocation) {
    return Err(format!("{ctx}: physical cell references invocation slot {s}"));
  }
  Ok(Some(s))
}

fn parse_v2_wide_graph(v: &Value) -> Result<V2WideGraph, String> {
  let width = natural(&v["width"], "wide.width")?;
  let raw_nodes = v["nodes"].as_array().ok_or("wide graph missing nodes")?;
  let mut nodes = Vec::with_capacity(raw_nodes.len());
  for (i, n) in raw_nodes.iter().enumerate() {
    let arr = n.as_array().ok_or_else(|| format!("wide node {i} not array"))?;
    let op = arr
      .first()
      .and_then(Value::as_str)
      .ok_or_else(|| format!("wide node {i} missing op"))?;
    let child = |k: usize| -> Result<usize, String> {
      let idx = natural(
        arr
          .get(k)
          .ok_or_else(|| format!("wide node {i} ({op}) missing operand {k}"))?,
        "wide operand",
      )?;
      if idx >= i {
        return Err(format!("wide node {i} non-topological operand {idx}"));
      }
      Ok(idx)
    };
    let node = match op {
      "const" => V2WideNode::Const(scalar(
        arr.get(1).ok_or_else(|| format!("wide const {i} missing value"))?,
        "wide const",
      )?),
      "var" => {
        let x = natural(
          arr.get(1).ok_or_else(|| format!("wide var {i} missing index"))?,
          "wide var",
        )?;
        if x >= width {
          return Err(format!("wide var {x} exceeds width {width}"));
        }
        V2WideNode::Var(x)
      },
      "add" => V2WideNode::Add(child(1)?, child(2)?),
      "sub" => V2WideNode::Sub(child(1)?, child(2)?),
      "mul" => V2WideNode::Mul(child(1)?, child(2)?),
      "neg" => V2WideNode::Neg(child(1)?),
      other => return Err(format!("unknown wide node op {other:?}")),
    };
    nodes.push(node);
  }
  let check_node = |x: &Value, ctx: &str| -> Result<usize, String> {
    let idx = natural(x, ctx)?;
    if idx >= nodes.len() {
      return Err(format!("{ctx}: node index {idx} out of range"));
    }
    Ok(idx)
  };
  let lookups = v["lookups"]
    .as_array()
    .ok_or("wide graph missing lookups")?
    .iter()
    .map(|l| {
      let arr = l.as_array().ok_or("wide lookup not array")?;
      let m = check_node(
        arr.first().ok_or("wide lookup missing mult")?,
        "wide lookup.mult",
      )?;
      let args = arr
        .get(1)
        .and_then(Value::as_array)
        .ok_or("wide lookup missing args")?
        .iter()
        .map(|a| check_node(a, "wide lookup.arg"))
        .collect::<Result<Vec<_>, _>>()?;
      Ok((m, args))
    })
    .collect::<Result<Vec<_>, String>>()?;
  Ok(V2WideGraph { nodes, lookups })
}

fn parse_v2_template(v: &Value, width: usize) -> Result<V2Template, String> {
  let lanes_per_row = width / 4;
  let raw_slots =
    v["slots"].as_array().ok_or("template missing slots array")?;
  let mut slots: Vec<V2Slot> = Vec::with_capacity(raw_slots.len());
  for (idx, s) in raw_slots.iter().enumerate() {
    let obj = s.as_object().ok_or_else(|| format!("slot {idx} not object"))?;
    let slot = if let Some(col_v) = obj.get("column") {
      V2Slot::Column(natural(col_v, "slot.column")?)
    } else if let Some(sum_v) = obj.get("sum") {
      let k = scalar(&sum_v["k"], "slot.sum.k")?;
      let raw_terms = sum_v["terms"]
        .as_array()
        .ok_or_else(|| format!("slot {idx} sum missing terms"))?;
      let mut terms = Vec::with_capacity(raw_terms.len());
      let check_ref =
        |s_idx: usize, cur_slots: &[V2Slot]| -> Result<(), String> {
          if s_idx >= idx {
            return Err(format!(
              "slot {idx} references non-topological slot {s_idx}"
            ));
          }
          if matches!(cur_slots[s_idx], V2Slot::Key | V2Slot::Invocation) {
            return Err(format!(
              "slot {idx} sum references key/invocation slot {s_idx}"
            ));
          }
          Ok(())
        };
      for t in raw_terms {
        let arr = t.as_array().ok_or("sum term not array")?;
        let kind =
          arr.first().and_then(Value::as_str).ok_or("sum term missing op")?;
        match kind {
          "lin" => {
            let c =
              scalar(arr.get(1).ok_or("lin missing coeff")?, "lin.coeff")?;
            let a = natural(arr.get(2).ok_or("lin missing slot")?, "lin.slot")?;
            check_ref(a, &slots)?;
            terms.push(V2Term::Lin(c, a));
          },
          "prod" => {
            let c =
              scalar(arr.get(1).ok_or("prod missing coeff")?, "prod.coeff")?;
            let a =
              natural(arr.get(2).ok_or("prod missing slot a")?, "prod.a")?;
            let b =
              natural(arr.get(3).ok_or("prod missing slot b")?, "prod.b")?;
            check_ref(a, &slots)?;
            check_ref(b, &slots)?;
            terms.push(V2Term::Prod(c, a, b));
          },
          other => return Err(format!("unknown sum term kind {other:?}")),
        }
      }
      V2Slot::Sum { k, terms }
    } else if obj.contains_key("key") {
      V2Slot::Key
    } else if obj.get("invocation").and_then(Value::as_bool) == Some(true) {
      V2Slot::Invocation
    } else {
      return Err(format!("slot {idx} has unrecognized shape: {s}"));
    };
    slots.push(slot);
  }

  let raw_rows = v["rows"].as_array().ok_or("template missing rows array")?;
  let mut rows = Vec::with_capacity(raw_rows.len());
  for (ri, r) in raw_rows.iter().enumerate() {
    let obj = r.as_object().ok_or_else(|| format!("row {ri} not object"))?;
    if let Some(g) = obj.get("gate") {
      let raw_lanes = g["lanes"]
        .as_array()
        .ok_or_else(|| format!("gate row {ri} missing lanes"))?;
      if raw_lanes.len() != lanes_per_row {
        return Err(format!(
          "gate row {ri} has {} lanes, expected {lanes_per_row}",
          raw_lanes.len()
        ));
      }
      let mut lanes = Vec::with_capacity(lanes_per_row);
      for (li, l) in raw_lanes.iter().enumerate() {
        if l.as_str() == Some("empty") {
          lanes.push(V2Lane::Empty);
        } else if let Some(gl) = l.get("gate") {
          let qm = scalar(&gl["qm"], "lane.gate.qm")?;
          let qc = scalar(&gl["qc"], "lane.gate.qc")?;
          let q_arr = gl["q"].as_array().ok_or("lane.gate missing q")?;
          if q_arr.len() != 4 {
            return Err("lane.gate q must have 4 entries".into());
          }
          let q = [
            scalar(&q_arr[0], "lane.gate.q[0]")?,
            scalar(&q_arr[1], "lane.gate.q[1]")?,
            scalar(&q_arr[2], "lane.gate.q[2]")?,
            scalar(&q_arr[3], "lane.gate.q[3]")?,
          ];
          let c_arr =
            gl["cells"].as_array().ok_or("lane.gate missing cells")?;
          if c_arr.len() != 4 {
            return Err("lane.gate cells must have 4 entries".into());
          }
          let cells = [
            parse_opt_cell(&c_arr[0], &slots, "lane.gate.cells[0]")?,
            parse_opt_cell(&c_arr[1], &slots, "lane.gate.cells[1]")?,
            parse_opt_cell(&c_arr[2], &slots, "lane.gate.cells[2]")?,
            parse_opt_cell(&c_arr[3], &slots, "lane.gate.cells[3]")?,
          ];
          lanes.push(V2Lane::Gate { qm, q, qc, cells });
        } else if let Some(ml) = l.get("msg") {
          let ts = scalar(&ml["ts"], "lane.msg.ts")?.as_canonical_u64();
          let mk = scalar(&ml["mk"], "lane.msg.mk")?;
          let mc = scalar(&ml["mc"], "lane.msg.mc")?;
          let c_arr = ml["cells"].as_array().ok_or("lane.msg missing cells")?;
          if c_arr.len() != 4 {
            return Err("lane.msg cells must have 4 entries".into());
          }
          let cells = [
            parse_opt_cell(&c_arr[0], &slots, "lane.msg.cells[0]")?,
            parse_opt_cell(&c_arr[1], &slots, "lane.msg.cells[1]")?,
            parse_opt_cell(&c_arr[2], &slots, "lane.msg.cells[2]")?,
            parse_opt_cell(&c_arr[3], &slots, "lane.msg.cells[3]")?,
          ];
          lanes.push(V2Lane::Msg { ts, mk, mc, cells });
        } else {
          return Err(format!("gate row {ri} lane {li} unrecognized: {l}"));
        }
      }
      let raw_spans = g["spans"]
        .as_array()
        .ok_or_else(|| format!("gate row {ri} missing spans"))?;
      let mut spans = Vec::with_capacity(raw_spans.len());
      for sp in raw_spans {
        let arr = sp.as_array().ok_or("span not array")?;
        if arr.len() != 2 {
          return Err("span must have 2 elements".into());
        }
        let start = natural(&arr[0], "span.start")?;
        let len = natural(&arr[1], "span.len")?;
        if start + len > lanes_per_row {
          return Err(format!(
            "span ({start}, {len}) exceeds {lanes_per_row} lanes"
          ));
        }
        spans.push((start, len));
      }
      rows.push(V2Row::Gate { lanes, spans });
    } else if let Some(m) = obj.get("message") {
      let ts = scalar(&m["ts"], "row.msg.ts")?.as_canonical_u64();
      let mk = scalar(&m["mk"], "row.msg.mk")?;
      let mc = scalar(&m["mc"], "row.msg.mc")?;
      let receive_key = m["key"].as_bool().ok_or("row.msg missing bool key")?;
      let raw_cells = m["cells"].as_array().ok_or("row.msg missing cells")?;
      if raw_cells.len() != width {
        return Err(format!(
          "message row {ri} has {} cells, expected {width}",
          raw_cells.len()
        ));
      }
      let cells = raw_cells
        .iter()
        .map(|c| parse_opt_cell(c, &slots, "row.msg.cell"))
        .collect::<Result<Vec<_>, _>>()?;
      rows.push(V2Row::Message { ts, mk, mc, receive_key, cells });
    } else {
      return Err(format!("template row {ri} unrecognized: {r}"));
    }
  }
  Ok(V2Template { slots, rows })
}

fn parse_layout(bytes: &[u8]) -> Result<SingleCircuitLayout, String> {
  let root: Value = serde_json::from_slice(bytes)
    .map_err(|e| format!("failed to parse layout JSON: {e}"))?;
  let fmt =
    root["format"].as_str().ok_or("layout JSON missing string \"format\"")?;
  if fmt != WIDE_LAYOUT_FORMAT && fmt != TILING_V2_LAYOUT_FORMAT {
    return Err(format!(
      "unexpected layout format {fmt:?} (expected {WIDE_LAYOUT_FORMAT:?} or {TILING_V2_LAYOUT_FORMAT:?})"
    ));
  }
  let expected_modulus = Val::ORDER_U64.to_string();
  if root["modulus"].as_str() != Some(expected_modulus.as_str()) {
    return Err(format!(
      "layout modulus {:?} is not Goldilocks ({expected_modulus})",
      root["modulus"]
    ));
  }
  if let Some(field_val) = root.get("field")
    && field_val.as_str() != Some("goldilocks")
  {
    return Err(format!("layout field {field_val} is not \"goldilocks\""));
  }
  let bound = root["bound"].as_u64().ok_or("layout missing u64 bound")?;

  let sc = root.get("single_circuit").filter(|v| v.is_object()).ok_or(
    "layout missing \"single_circuit\" object \
       (re-export with `--single-circuit --pow2-rows`)",
  )?;
  let num_circuits =
    natural(&sc["num_circuits"], "single_circuit.num_circuits")?;
  if num_circuits != 1 {
    return Err(format!(
      "single_circuit.num_circuits must be 1, got {num_circuits}"
    ));
  }
  let rows = natural(&sc["rows"], "single_circuit.rows")?;
  if rows == 0 || !rows.is_power_of_two() {
    return Err(format!(
      "single_circuit.rows ({rows}) must be a positive power of two \
       (re-export with --pow2-rows)"
    ));
  }
  if u64::try_from(rows).is_ok_and(|r| r > MAX_BATCH_ROWS) {
    return Err(format!(
      "single_circuit.rows ({rows}) exceeds Goldilocks depth bound 2^39"
    ));
  }
  let main_width = natural(&sc["main_width"], "single_circuit.main_width")?;
  let fixed_width = natural(&sc["fixed_width"], "single_circuit.fixed_width")?;
  let num_constraints =
    natural(&sc["num_constraints"], "single_circuit.num_constraints")?;
  let num_lookups = natural(&sc["num_lookups"], "single_circuit.num_lookups")?;

  let raw_constituents = sc["constituents"]
    .as_array()
    .ok_or("single_circuit missing constituents array")?;

  let (kind, constituents) = if fmt == WIDE_LAYOUT_FORMAT {
    let request = root["request"]
      .as_array()
      .ok_or("layout missing request array")?
      .iter()
      .map(|x| scalar(x, "request"))
      .collect::<Result<Vec<_>, _>>()?;
    let top_rom_vector = match root.get("rom_vector") {
      Some(v) if !v.is_null() => {
        let k = natural(v, "layout.rom_vector")?;
        if k == 0 {
          return Err("layout.rom_vector must be at least 1".into());
        }
        k
      },
      _ => 1,
    };
    let mut constituents = Vec::with_capacity(raw_constituents.len());
    let mut expected_m_off = 0usize;
    let mut expected_f_off = 0usize;
    for (idx, c) in raw_constituents.iter().enumerate() {
      let c_rows = natural(&c["rows"], "constituent.rows")?;
      let m_off = natural(&c["main_offset"], "constituent.main_offset")?;
      let m_w = natural(&c["main_width"], "constituent.main_width")?;
      let f_off = natural(&c["fixed_offset"], "constituent.fixed_offset")?;
      let f_w = natural(&c["fixed_width"], "constituent.fixed_width")?;
      let active_col = match c.get("active_col") {
        Some(v) if !v.is_null() => Some(natural(v, "constituent.active_col")?),
        _ => None,
      };
      if c_rows > rows {
        return Err(format!(
          "constituent {idx} rows ({c_rows}) exceeds packed rows ({rows})"
        ));
      }
      if m_off != expected_m_off || f_off != expected_f_off {
        return Err(format!(
          "constituent {idx} offset mismatch: got (m={m_off}, f={f_off}), \
           expected (m={expected_m_off}, f={expected_f_off})"
        ));
      }
      let needs_act = c_rows < rows;
      match (needs_act, active_col) {
        (true, Some(ac)) if ac == f_off + f_w => {},
        (false, None) => {},
        _ => {
          return Err(format!(
            "constituent {idx} active_col {active_col:?} disagrees with \
             rows={c_rows} vs packed_rows={rows} (f_off={f_off}, f_w={f_w})"
          ));
        },
      }
      let c_kind = match c["kind"].as_str() {
        Some("unit") => {
          let chip = c["chip"]
            .as_str()
            .ok_or_else(|| format!("unit constituent {idx} missing chip name"))?
            .to_owned();
          ConstituentKind::Unit { chip }
        },
        Some("map") => {
          let length = natural(&c["length"], "map constituent.length")?;
          if m_w != 1 || f_w != length + 1 {
            return Err(format!(
              "map constituent {idx} shape mismatch: m_w={m_w}, f_w={f_w}, length={length}"
            ));
          }
          ConstituentKind::Map { length }
        },
        Some("rom") => {
          let words = natural(&c["words"], "rom constituent.words")?;
          let rom_vector = match c.get("rom_vector") {
            Some(v) if !v.is_null() => {
              let k = natural(v, "rom constituent.rom_vector")?;
              if k == 0 {
                return Err(format!(
                  "rom constituent {idx} rom_vector must be at least 1"
                ));
              }
              k
            },
            _ => 1,
          };
          if rom_vector != top_rom_vector {
            return Err(format!(
              "rom constituent {idx} rom_vector ({rom_vector}) disagrees with \
               layout rom_vector ({top_rom_vector})"
            ));
          }
          let expected_m_w = words
            .checked_add(1)
            .and_then(|w| w.checked_mul(rom_vector))
            .ok_or("rom constituent main_width overflow")?;
          if m_w != expected_m_w || f_w != 1 {
            return Err(format!(
              "rom constituent {idx} shape mismatch: m_w={m_w}, f_w={f_w}, \
               words={words}, rom_vector={rom_vector} \
               (expected m_w={expected_m_w}, f_w=1)"
            ));
          }
          let eff_cap = rom_vector
            .checked_mul(c_rows)
            .ok_or("rom constituent effective capacity overflow")?;
          if let Some(cap_v) = c.get("capacity")
            && !cap_v.is_null()
          {
            let cap = natural(cap_v, "rom constituent.capacity")?;
            if cap != eff_cap {
              return Err(format!(
                "rom constituent {idx} capacity ({cap}) != rom_vector * rows ({eff_cap})"
              ));
            }
          }
          if !u64::try_from(eff_cap).is_ok_and(|cap| cap <= bound) {
            return Err(format!(
              "rom constituent {idx} effective capacity ({eff_cap}) exceeds bound ({bound})"
            ));
          }
          ConstituentKind::Rom { words, rom_vector }
        },
        other => {
          return Err(format!(
            "constituent {idx} has unsupported kind {other:?}"
          ));
        },
      };
      expected_m_off =
        expected_m_off.checked_add(m_w).ok_or("packed main width overflow")?;
      expected_f_off = expected_f_off
        .checked_add(f_w + usize::from(needs_act))
        .ok_or("packed fixed width overflow")?;
      constituents.push(Constituent {
        kind: c_kind,
        rows: c_rows,
        main_offset: m_off,
        main_width: m_w,
        fixed_offset: f_off,
        fixed_width: f_w,
        active_col,
      });
    }
    if expected_m_off != main_width || expected_f_off != fixed_width {
      return Err(format!(
        "constituent widths sum to ({expected_m_off} main, {expected_f_off} fixed), \
         expected ({main_width} main, {fixed_width} fixed)"
      ));
    }
    (LayoutKind::Wide { request, rom_vector: top_rom_vector }, constituents)
  } else {
    let shard_width = natural(&root["width"], "layout.width")?;
    if shard_width < 8 || !shard_width.is_multiple_of(4) {
      return Err(format!(
        "tiling-v2 shard width {shard_width} must be a multiple of 4 and >= 8"
      ));
    }
    let shards = natural(&root["shards"], "layout.shards")?;
    if shards == 0 {
      return Err("tiling-v2 shards must be positive".into());
    }
    let shard_fixed_width =
      natural(&root["fixed_width"], "layout.fixed_width")?;
    let places = natural(&root["places"], "layout.places")?;
    let ids_per_shard = root["ids_per_shard"]
      .as_u64()
      .ok_or("tiling-v2 layout missing u64 ids_per_shard")?;
    let caps: Vec<usize> = root["caps"]
      .as_array()
      .ok_or("tiling-v2 layout missing caps array")?
      .iter()
      .map(|x| natural(x, "caps"))
      .collect::<Result<_, _>>()?;

    let mut code_to_bus: FxHashMap<u64, (u64, u64, bool)> =
      FxHashMap::default();
    let mut bus_to_code: FxHashMap<(u64, u64), (u64, bool)> =
      FxHashMap::default();
    for (bi, b) in root["buses"]
      .as_array()
      .ok_or("tiling-v2 layout missing buses array")?
      .iter()
      .enumerate()
    {
      let arr = b.as_array().ok_or_else(|| format!("bus {bi} not array"))?;
      if arr.len() != 4 {
        return Err(format!(
          "bus {bi} must have 4 elements [tag, sub, code, lane]"
        ));
      }
      let tag = scalar(&arr[0], "bus.tag")?.as_canonical_u64();
      let sub = scalar(&arr[1], "bus.sub")?.as_canonical_u64();
      let code = scalar(&arr[2], "bus.code")?.as_canonical_u64();
      let lane = arr[3]
        .as_bool()
        .ok_or_else(|| format!("bus {bi} missing bool lane"))?;
      if code_to_bus.insert(code, (tag, sub, lane)).is_some() {
        return Err(format!("duplicate bus code {code}"));
      }
      if bus_to_code.insert((tag, sub), (code, lane)).is_some() {
        return Err(format!("duplicate bus ({tag}, {sub})"));
      }
    }

    let request: Vec<Vec<Val>> = root["request"]
      .as_array()
      .ok_or("tiling-v2 layout missing request array")?
      .iter()
      .map(|row| {
        row
          .as_array()
          .ok_or("tiling-v2 request entry not array")?
          .iter()
          .map(|x| scalar(x, "request"))
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    if request.is_empty() {
      return Err("tiling-v2 request array must be non-empty".into());
    }

    let raw_circuits = root["circuits"]
      .as_array()
      .ok_or("tiling-v2 layout missing circuits array")?;
    let raw_templates = root["templates"]
      .as_array()
      .ok_or("tiling-v2 layout missing templates array")?;
    if raw_circuits.len() != caps.len() || raw_templates.len() != caps.len() {
      return Err(format!(
        "tiling-v2 mismatch: {} circuits, {} templates, {} caps",
        raw_circuits.len(),
        raw_templates.len(),
        caps.len()
      ));
    }

    let mut circuits = Vec::with_capacity(raw_circuits.len());
    for (ci, c) in raw_circuits.iter().enumerate() {
      let chip = c["chip"]
        .as_str()
        .ok_or_else(|| format!("tiling-v2 circuit {ci} missing chip name"))?
        .to_owned();
      let unroll = c["unroll"].as_bool().unwrap_or(false);
      let unroll_stages = if unroll {
        let s = natural(&c["stages"], "circuit.stages")?;
        if s == 0 {
          return Err(format!("unrolled circuit {chip} has 0 stages"));
        }
        Some(s)
      } else {
        None
      };
      let wide_width = natural(&c["wide"]["width"], "circuit.wide.width")?;
      let wide_graph =
        if unroll { Some(parse_v2_wide_graph(&c["wide"])?) } else { None };
      circuits.push(V2CircuitMeta {
        chip,
        unroll_stages,
        wide_width,
        wide_graph,
      });
    }

    let mut templates = Vec::with_capacity(raw_templates.len());
    for (ti, t) in raw_templates.iter().enumerate() {
      templates
        .push(parse_v2_template(t, shard_width).map_err(|e| {
          format!("template {ti} ({}): {e}", circuits[ti].chip)
        })?);
    }

    let sum_places: usize = templates
      .iter()
      .zip(&caps)
      .try_fold(0usize, |acc, (t, &cap)| {
        acc.checked_add(cap.checked_mul(t.rows.len())?)
      })
      .ok_or("tiling-v2 places overflow")?;
    if sum_places != places {
      return Err(format!(
        "tiling-v2 places mismatch: sum(cap * template.rows)={sum_places} != places={places}"
      ));
    }
    let sum_caps: u64 = u64::try_from(caps.iter().sum::<usize>())
      .map_err(|e| format!("caps sum overflow: {e}"))?;
    if sum_caps != ids_per_shard {
      return Err(format!(
        "tiling-v2 ids_per_shard mismatch: sum(caps)={sum_caps} != ids_per_shard={ids_per_shard}"
      ));
    }

    let raw_compact = root["compact"]
      .as_array()
      .ok_or("tiling-v2 single_circuit requires compact tables metadata")?;

    let mut constituents = Vec::with_capacity(raw_constituents.len());
    let mut expected_m_off = 0usize;
    let mut expected_f_off = 0usize;
    let mut expected_shard = 0usize;
    for (idx, c) in raw_constituents.iter().enumerate() {
      let c_rows = natural(&c["rows"], "constituent.rows")?;
      let m_off = natural(&c["main_offset"], "constituent.main_offset")?;
      let m_w = natural(&c["main_width"], "constituent.main_width")?;
      let f_off = natural(&c["fixed_offset"], "constituent.fixed_offset")?;
      let f_w = natural(&c["fixed_width"], "constituent.fixed_width")?;
      let active_col = match c.get("active_col") {
        Some(v) if !v.is_null() => Some(natural(v, "constituent.active_col")?),
        _ => None,
      };
      if c_rows > rows {
        return Err(format!(
          "constituent {idx} rows ({c_rows}) exceeds packed rows ({rows})"
        ));
      }
      if m_off != expected_m_off || f_off != expected_f_off {
        return Err(format!(
          "constituent {idx} offset mismatch: got (m={m_off}, f={f_off}), \
           expected (m={expected_m_off}, f={expected_f_off})"
        ));
      }
      let needs_act = c_rows < rows;
      match (needs_act, active_col) {
        (true, Some(ac)) if ac == f_off + f_w => {},
        (false, None) => {},
        _ => {
          return Err(format!(
            "constituent {idx} active_col {active_col:?} disagrees with \
             rows={c_rows} vs packed_rows={rows} (f_off={f_off}, f_w={f_w})"
          ));
        },
      }
      let c_kind = match c["kind"].as_str() {
        Some("shard") => {
          let shard_index = natural(&c["index"], "shard constituent.index")?;
          if shard_index != expected_shard {
            return Err(format!(
              "shard constituent {idx} has index {shard_index}, expected {expected_shard}"
            ));
          }
          if c_rows != places || m_w != shard_width || f_w != shard_fixed_width
          {
            return Err(format!(
              "shard constituent {idx} shape ({c_rows} x {m_w} main, {f_w} fixed) \
               disagrees with layout ({places} x {shard_width} main, {shard_fixed_width} fixed)"
            ));
          }
          expected_shard += 1;
          ConstituentKind::Shard { shard_index }
        },
        Some("compact") => {
          let ci = natural(&c["index"], "compact constituent.index")?;
          let desc = raw_compact.get(ci).ok_or_else(|| {
            format!("compact constituent {idx} index {ci} out of range")
          })?;
          let d_rows = natural(&desc["rows"], "compact.rows")?;
          let d_mw = natural(&desc["main_width"], "compact.main_width")?;
          let d_fw = natural(&desc["fixed_width"], "compact.fixed_width")?;
          let d_nf = natural(&desc["n_fixed"], "compact.n_fixed")?;
          if c_rows != d_rows || m_w != d_mw || f_w != d_fw || d_fw != d_nf + 3
          {
            return Err(format!(
              "compact constituent {idx} disagrees with compact[{ci}] metadata"
            ));
          }
          match c["compact_kind"].as_str() {
            Some("maps") => {
              if d_nf != shard_width - 1 || m_w != 1 {
                return Err(format!(
                  "compact maps constituent {idx} shape mismatch (n_fixed={d_nf}, m_w={m_w}, W={shard_width})"
                ));
              }
              ConstituentKind::CompactMap
            },
            Some("roms") => {
              if d_nf != 1 || m_w != shard_width - 1 {
                return Err(format!(
                  "compact roms constituent {idx} shape mismatch (n_fixed={d_nf}, m_w={m_w}, W={shard_width})"
                ));
              }
              ConstituentKind::CompactRom
            },
            other => {
              return Err(format!(
                "compact constituent {idx} has unsupported compact_kind {other:?}"
              ));
            },
          }
        },
        other => {
          return Err(format!(
            "tiling-v2 constituent {idx} has unsupported kind {other:?}"
          ));
        },
      };
      expected_m_off =
        expected_m_off.checked_add(m_w).ok_or("packed main width overflow")?;
      expected_f_off = expected_f_off
        .checked_add(f_w + usize::from(needs_act))
        .ok_or("packed fixed width overflow")?;
      constituents.push(Constituent {
        kind: c_kind,
        rows: c_rows,
        main_offset: m_off,
        main_width: m_w,
        fixed_offset: f_off,
        fixed_width: f_w,
        active_col,
      });
    }
    if expected_shard != shards {
      return Err(format!(
        "tiling-v2 single_circuit has {expected_shard} shard constituents, expected {shards}"
      ));
    }
    if expected_m_off != main_width || expected_f_off != fixed_width {
      return Err(format!(
        "constituent widths sum to ({expected_m_off} main, {expected_f_off} fixed), \
         expected ({main_width} main, {fixed_width} fixed)"
      ));
    }
    (
      LayoutKind::TilingV2(Box::new(TilingV2Data {
        shard_width,
        shards,
        caps,
        places,
        ids_per_shard,
        request,
        code_to_bus,
        bus_to_code,
        circuits,
        templates,
      })),
      constituents,
    )
  };

  let (constraints, lookups) =
    parse_graph(&sc["circuit"], main_width, fixed_width)?;
  if constraints.len() != num_constraints {
    return Err(format!(
      "constraint count mismatch: graph has {}, metadata says {num_constraints}",
      constraints.len()
    ));
  }
  if lookups.len() != num_lookups {
    return Err(format!(
      "lookup count mismatch: graph has {}, metadata says {num_lookups}",
      lookups.len()
    ));
  }
  Ok(SingleCircuitLayout {
    kind,
    rows,
    main_width,
    fixed_width,
    num_constraints,
    num_lookups,
    bound,
    constituents,
    constraints,
    lookups,
  })
}

/// Read ONE `IXTLFX01` fixed-matrix block and enforce exact EOF and dimensions.
fn read_single_fixed_block(
  bytes: &[u8],
  expected_rows: usize,
  expected_width: usize,
) -> Result<RowMajorMatrix<Val>, String> {
  if bytes.len() < 24 || &bytes[..8] != FIXED_MAGIC {
    return Err("FIXED.bin does not begin with IXTLFX01 magic".into());
  }
  let read_u64 = |off: usize| -> Result<usize, String> {
    let raw = u64::from_le_bytes(
      bytes[off..off + 8].try_into().expect("8-byte header word"),
    );
    usize::try_from(raw)
      .map_err(|e| format!("FIXED.bin dimension {raw} overflows usize: {e}"))
  };
  let rows = read_u64(8)?;
  let width = read_u64(16)?;
  if rows != expected_rows || width != expected_width {
    return Err(format!(
      "FIXED.bin dimensions ({rows} x {width}) do not match single_circuit \
       ({expected_rows} x {expected_width})"
    ));
  }
  let cells = rows.checked_mul(width).ok_or("FIXED.bin cell count overflow")?;
  if cells > bytes.len() - 24 {
    return Err("truncated IXTLFX01 fixed matrix block".into());
  }
  let mut values = Vec::with_capacity(cells);
  let mut p = 24usize;
  for cell_idx in 0..cells {
    let len = usize::from(*bytes.get(p).ok_or("truncated FIXED.bin entry")?);
    if len > 8 || p + 1 + len > bytes.len() {
      return Err(format!("malformed FIXED.bin entry at cell {cell_idx}"));
    }
    let mut x = 0u64;
    for (i, &b) in bytes[p + 1..p + 1 + len].iter().enumerate() {
      x |= u64::from(b) << (8 * i);
    }
    if x >= Val::ORDER_U64 {
      return Err(format!(
        "FIXED.bin entry {x} at cell {cell_idx} is not below Goldilocks modulus"
      ));
    }
    values.push(Val::from_u64(x));
    p += 1 + len;
  }
  if p != bytes.len() {
    return Err(format!(
      "FIXED.bin has {} trailing bytes after single IXTLFX01 block",
      bytes.len() - p
    ));
  }
  Ok(RowMajorMatrix::new(values, width))
}

/// Validate `active_col` selectors, ROM addresses, and compact table descriptors in `fixed`.
fn validate_fixed_matrix(
  layout: &SingleCircuitLayout,
  fixed: &RowMajorMatrix<Val>,
) -> Result<(), String> {
  let fw = layout.fixed_width;
  for (idx, c) in layout.constituents.iter().enumerate() {
    if let Some(ac) = c.active_col {
      for r in 0..layout.rows {
        let got = fixed.values[r * fw + ac];
        let want = if r < c.rows { Val::ONE } else { Val::ZERO };
        if got != want {
          return Err(format!(
            "FIXED.bin active_col mismatch at constituent {idx} row {r}: \
             got {}, expected {}",
            got.as_canonical_u64(),
            want.as_canonical_u64()
          ));
        }
      }
    }
    match c.kind {
      ConstituentKind::Rom { rom_vector, .. } => {
        for r in 0..c.rows {
          let got = fixed.values[r * fw + c.fixed_offset];
          let expected_addr = rom_vector
            .checked_mul(r)
            .and_then(|a| u64::try_from(a).ok())
            .ok_or("FIXED.bin ROM base address overflow")?;
          let want = Val::from_u64(expected_addr);
          if got != want {
            return Err(format!(
              "FIXED.bin ROM addr mismatch at constituent {idx} row {r}: \
               got {}, expected {expected_addr} (rom_vector={rom_vector})",
              got.as_canonical_u64()
            ));
          }
        }
      },
      ConstituentKind::CompactMap | ConstituentKind::CompactRom => {
        let LayoutKind::TilingV2(v2) = &layout.kind else {
          return Err("compact constituent outside tiling-v2 layout".into());
        };
        let is_rom = matches!(c.kind, ConstituentKind::CompactRom);
        for r in 0..c.rows {
          let base = r * fw + c.fixed_offset;
          let sel_l = fixed.values[base];
          let sel_w = fixed.values[base + 1];
          let code = fixed.values[base + 2].as_canonical_u64();
          let &(tag, _sub, lane) = v2.code_to_bus.get(&code).ok_or_else(|| {
            format!(
              "FIXED.bin compact constituent {idx} row {r} has unknown bus code {code}"
            )
          })?;
          let want_sel =
            if lane { (Val::ONE, Val::ZERO) } else { (Val::ZERO, Val::ONE) };
          if (sel_l, sel_w) != want_sel {
            return Err(format!(
              "FIXED.bin compact constituent {idx} row {r} selectors ({}, {}) \
               disagree with bus lane={lane}",
              sel_l.as_canonical_u64(),
              sel_w.as_canonical_u64()
            ));
          }
          if is_rom && tag != ROM_TAG {
            return Err(format!(
              "FIXED.bin compact ROM constituent {idx} row {r} has non-ROM tag {tag}"
            ));
          }
        }
        for r in c.rows..layout.rows {
          let base = r * fw + c.fixed_offset;
          if fixed.values[base..base + c.fixed_width]
            .iter()
            .any(|&v| v != Val::ZERO)
          {
            return Err(format!(
              "FIXED.bin compact constituent {idx} inactive row {r} is nonzero"
            ));
          }
        }
      },
      _ => {},
    }
  }
  Ok(())
}

/// Choose the lowest-FFT-cost `lookup_group_size` within the blowup budget
/// without altering the certified lookup list order.
fn choose_lookup_group(
  graph: &ConstraintGraph<Val>,
  packed_rows: usize,
  log_blowup: usize,
  ext_degree: usize,
  requested: Option<usize>,
) -> Result<usize, String> {
  let blowup = 1usize << log_blowup;
  let max_allowed = blowup + 1;
  let c_deg = graph.max_constraint_degree as usize;
  if c_deg > max_allowed {
    return Err(format!(
      "constraint degree {c_deg} exceeds blowup capacity {max_allowed} \
       (increase --log-blowup above {log_blowup})"
    ));
  }
  let deg1 = logup_max_degree(graph, 1) as usize;
  if deg1 > max_allowed {
    return Err(format!(
      "lookup degree {deg1} exceeds blowup capacity {max_allowed} \
       (increase --log-blowup above {log_blowup})"
    ));
  }
  if let Some(g) = requested {
    if !(1..=MAX_LOOKUP_GROUP).contains(&g) {
      return Err(format!(
        "--lookup-group must be in 1..={MAX_LOOKUP_GROUP}, got {g}"
      ));
    }
    let d = c_deg.max(logup_max_degree(graph, g) as usize);
    let q = (d.max(2) - 1).next_power_of_two();
    if q > blowup {
      return Err(format!(
        "--lookup-group {g} yields degree {d} (quotient {q} > blowup {blowup})"
      ));
    }
    return Ok(g);
  }
  let h = packed_rows as u128;
  let b = blowup as u128;
  let ext = ext_degree as u128;
  let fft = |n: u128| n * u128::from(n.max(2).ilog2());
  let max_g = graph.lookups.len().clamp(1, MAX_LOOKUP_GROUP);
  let mut best_g = 1usize;
  let mut best_cost = u128::MAX;
  for g in 1..=max_g {
    let d = c_deg.max(logup_max_degree(graph, g) as usize);
    let q = (d.max(2) - 1).next_power_of_two();
    if q > blowup {
      continue;
    }
    let s2 = stage2_width(graph.lookups.len(), g, ext_degree) as u128;
    let q128 = q as u128;
    let cost =
      (b + 1) * s2 * fft(h) + ext * (fft(q128 * h) + q128 * fft(b * h));
    if cost < best_cost {
      best_cost = cost;
      best_g = g;
    }
  }
  Ok(best_g)
}

fn trim_trailing_zeros(v: &mut Vec<Val>) {
  while v.last() == Some(&Val::ZERO) {
    v.pop();
  }
}

/// Directly evaluate EVERY constraint on EVERY row and exact LogUp ledger
/// balance on the compiled certified `ConstraintGraph`.
fn check_packed_circuit(
  graph: &ConstraintGraph<Val>,
  main: &RowMajorMatrix<Val>,
  fixed: Option<&RowMajorMatrix<Val>>,
  claims: &[&[Val]],
  trim_zeros: bool,
) -> Result<(), String> {
  let rows = main.height();
  let main_w = main.width;
  let fixed_w = fixed.map_or(0, |f| f.width);

  let eval_row = |row_idx: usize,
                  buf: &mut Vec<Val>,
                  ledger: &mut FxHashMap<Vec<Val>, Val>|
   -> Result<(), String> {
    let next_idx = if row_idx + 1 == rows { 0 } else { row_idx + 1 };
    let main_cur = &main.values[row_idx * main_w..(row_idx + 1) * main_w];
    let main_nxt = &main.values[next_idx * main_w..(next_idx + 1) * main_w];
    let (pre_cur, pre_nxt): (&[Val], &[Val]) = match fixed {
      Some(f) if fixed_w > 0 => (
        &f.values[row_idx * fixed_w..(row_idx + 1) * fixed_w],
        &f.values[next_idx * fixed_w..(next_idx + 1) * fixed_w],
      ),
      _ => (&[], &[]),
    };
    let vars = VarValues {
      preprocessed: [pre_cur, pre_nxt],
      main: [main_cur, main_nxt],
      stage2: [&[], &[]],
      publics: &[],
      is_first_row: if row_idx == 0 { Val::ONE } else { Val::ZERO },
      is_last_row: if row_idx + 1 == rows { Val::ONE } else { Val::ZERO },
      is_transition: if row_idx + 1 < rows { Val::ONE } else { Val::ZERO },
    };
    graph.sweep(&vars, buf);
    for (ci, &z) in graph.zeros.iter().enumerate() {
      let val = buf[z.index()];
      if val != Val::ZERO {
        return Err(format!(
          "row {row_idx}: constraint {ci} is nonzero ({})",
          val.as_canonical_u64()
        ));
      }
    }
    for l in &graph.lookups {
      let mult = buf[l.multiplicity.index()];
      if mult != Val::ZERO {
        let mut tuple: Vec<Val> =
          l.args.iter().map(|&a| buf[a.index()]).collect();
        if trim_zeros {
          trim_trailing_zeros(&mut tuple);
        }
        let acc = ledger.entry(tuple).or_insert(Val::ZERO);
        *acc += mult;
      }
    }
    Ok(())
  };

  #[cfg(feature = "parallel")]
  let mut ledger: FxHashMap<Vec<Val>, Val> = (0..rows)
    .into_par_iter()
    .try_fold(
      || (Vec::with_capacity(graph.nodes.len()), FxHashMap::default()),
      |(mut buf, mut local), row_idx| {
        eval_row(row_idx, &mut buf, &mut local)?;
        Ok::<_, String>((buf, local))
      },
    )
    .try_reduce(
      || (Vec::new(), FxHashMap::default()),
      |(_, mut left), (_, right)| {
        for (k, v) in right {
          let e = left.entry(k).or_insert(Val::ZERO);
          *e += v;
        }
        Ok((Vec::new(), left))
      },
    )
    .map(|(_, m)| m)?;

  #[cfg(not(feature = "parallel"))]
  let mut ledger: FxHashMap<Vec<Val>, Val> = {
    let mut buf = Vec::with_capacity(graph.nodes.len());
    let mut acc = FxHashMap::default();
    for row_idx in 0..rows {
      eval_row(row_idx, &mut buf, &mut acc)?;
    }
    acc
  };

  // Each public claim tuple contributes +1 to the LogUp balance.
  for &claim in claims {
    let mut key = claim.to_vec();
    if trim_zeros {
      trim_trailing_zeros(&mut key);
    }
    let entry = ledger.entry(key).or_insert(Val::ZERO);
    *entry += Val::ONE;
  }

  let mut unbalanced = 0usize;
  let mut sample = String::new();
  for (tuple, net) in &ledger {
    if *net != Val::ZERO {
      if unbalanced == 0 {
        let words: Vec<u64> =
          tuple.iter().map(|v| v.as_canonical_u64()).collect();
        sample = format!("tuple={words:?} net={}", net.as_canonical_u64());
      }
      unbalanced += 1;
    }
  }
  if unbalanced > 0 {
    return Err(format!(
      "LogUp balance failed: {unbalanced} unbalanced message(s) (first: {sample})"
    ));
  }
  Ok(())
}

/// Horizontally pack all constituent main traces (`unit`, `map`, `rom`) into
/// one `rows x main_width` matrix matching `SingleCircuit.packMain`.
fn pack_main_matrix(
  layout: &SingleCircuitLayout,
  fixed: &RowMajorMatrix<Val>,
  plan: &TracePlan<'_, NativeField<Val>>,
  record: &aiur::Execution<NativeField<Val>>,
  trace: &aiur::trace::Trace<Val>,
) -> Result<RowMajorMatrix<Val>, String> {
  let packed_rows = layout.rows;
  let main_w = layout.main_width;
  let fixed_w = layout.fixed_width;

  let mut chip_index: FxHashMap<&str, usize> = FxHashMap::default();
  for (i, m) in trace.matrices.iter().enumerate() {
    chip_index.insert(m.chip.as_str(), i);
  }

  // Collect total execution + depth-range multiplicities for every static map row.
  let prog = plan.program().program();
  let n_funcs = prog.functions.len();
  let mut map_counts: Vec<Vec<u64>> = Vec::with_capacity(prog.maps.len());
  for mi in 0..prog.maps.len() {
    let counts = record
      .queries
      .fixed_counts(n_funcs + mi)
      .ok_or_else(|| format!("missing static map counts for map {mi}"))?;
    map_counts.push(counts.to_vec());
  }
  for (range_idx, global_callable) in plan.depth_range_tables() {
    let uses = trace.ranges.table(range_idx);
    let mi = global_callable
      .checked_sub(n_funcs)
      .ok_or("depth range callable index precedes maps")?;
    let counts =
      map_counts.get_mut(mi).ok_or("depth range map index out of range")?;
    if uses.len() > counts.len() {
      return Err("depth range counts exceed static map table".into());
    }
    for (c, &u) in counts.iter_mut().zip(uses) {
      *c = c
        .checked_add(u)
        .filter(|&v| v < Val::ORDER_U64)
        .ok_or("map multiplicity reaches Goldilocks characteristic")?;
    }
  }

  // Build map demand table: encoded claim `[CALL, callable, input..., output...] -> mult`.
  let mut map_demand: FxHashMap<Vec<Val>, u64> = FxHashMap::default();
  for (mi, map) in prog.maps.iter().enumerate() {
    let in_rows = &prog.tables[map.input].rows;
    let out_rows = &prog.tables[map.output].rows;
    let callable_val = Val::from_u64(
      u64::try_from(n_funcs + mi)
        .map_err(|e| format!("map callable overflows u64: {e}"))?,
    );
    for (row_idx, &count) in map_counts[mi].iter().enumerate() {
      if count == 0 {
        continue;
      }
      if count >= Val::ORDER_U64 {
        return Err(
          "map multiplicity reaches Goldilocks characteristic".into(),
        );
      }
      let in_row = &in_rows[row_idx];
      let out_row = &out_rows[row_idx];
      let mut claim = Vec::with_capacity(2 + in_row.len() + out_row.len());
      claim.push(Val::from_u64(CALL_TAG));
      claim.push(callable_val);
      claim.extend(in_row.iter().copied().map(Val::from_u64));
      claim.extend(out_row.iter().copied().map(Val::from_u64));
      let entry = map_demand.entry(claim).or_insert(0);
      *entry = entry
        .checked_add(count)
        .filter(|&v| v < Val::ORDER_U64)
        .ok_or("aggregated map multiplicity overflows field")?;
    }
  }

  let rom_counts: FxHashMap<usize, usize> =
    record.memory.width_counts().collect();

  let total_cells =
    packed_rows.checked_mul(main_w).ok_or("packed main trace size overflow")?;
  let mut packed = Val::zero_vec(total_cells);

  let mut packed_chips: FxHashSet<usize> = FxHashSet::default();
  let mut packed_roms: FxHashSet<usize> = FxHashSet::default();

  for (idx, c) in layout.constituents.iter().enumerate() {
    match &c.kind {
      ConstituentKind::Unit { chip } => {
        let &mi = chip_index.get(chip.as_str()).ok_or_else(|| {
          format!("constituent {idx}: unknown chip {chip:?} in package")
        })?;
        let matrix = &trace.matrices[mi];
        if matrix.width + 1 != c.main_width {
          return Err(format!(
            "unit {chip}: trace width + 1 ({}) != constituent main_width ({})",
            matrix.width + 1,
            c.main_width
          ));
        }
        if matrix.unpadded_height > c.rows {
          return Err(format!(
            "unit {chip}: execution needs {} rows, but layout capacity is {}",
            matrix.unpadded_height, c.rows
          ));
        }
        for r in 0..matrix.unpadded_height {
          let mult = matrix.multiplicities[r];
          if mult >= Val::ORDER_U64 {
            return Err(format!(
              "unit {chip} row {r}: multiplicity reaches field characteristic"
            ));
          }
          let dst = &mut packed[r * main_w + c.main_offset
            ..r * main_w + c.main_offset + c.main_width];
          dst[..matrix.width].copy_from_slice(matrix.row(r));
          dst[matrix.width] = Val::from_u64(mult);
        }
        packed_chips.insert(mi);
      },
      ConstituentKind::Map { length } => {
        for r in 0..c.rows {
          let f_base = r * fixed_w + c.fixed_offset;
          if fixed.values[f_base] == Val::ONE {
            let claim = &fixed.values[f_base + 1..f_base + 1 + *length];
            if let Some(count) = map_demand.remove(claim) {
              packed[r * main_w + c.main_offset] = Val::from_u64(count);
            }
          }
        }
      },
      ConstituentKind::Rom { words, rom_vector } => {
        let count = rom_counts.get(words).copied().unwrap_or(0);
        let capacity =
          c.rows.checked_mul(*rom_vector).ok_or("ROM capacity overflow")?;
        if count > capacity {
          return Err(format!(
            "ROM width {words}: execution uses {count} cells, \
             exceeding layout capacity {capacity} ({} rows x K={rom_vector})",
            c.rows
          ));
        }
        let lane_w = words + 1;
        for addr in 0..count {
          let entry = record
            .memory
            .get_by_width(*words, addr)
            .ok_or_else(|| format!("missing ROM cell ({words}, {addr})"))?;
          if entry.address != addr || entry.cell.value.len() != *words {
            return Err(format!(
              "ROM cell ({words}, {addr}) address/width mismatch"
            ));
          }
          if entry.multiplicity >= Val::ORDER_U64 {
            return Err(format!(
              "ROM cell ({words}, {addr}) multiplicity reaches field characteristic"
            ));
          }
          let r = addr / *rom_vector;
          let lane = addr % *rom_vector;
          let col_off = c.main_offset + lane * lane_w;
          let dst =
            &mut packed[r * main_w + col_off..r * main_w + col_off + lane_w];
          dst[0] = Val::from_u64(entry.multiplicity);
          dst[1..].copy_from_slice(entry.cell.value);
        }
        packed_roms.insert(*words);
      },
      ConstituentKind::Shard { .. }
      | ConstituentKind::CompactMap
      | ConstituentKind::CompactRom => {
        return Err(format!(
          "constituent {idx}: unexpected tiling-v2 constituent in wide layout"
        ));
      },
    }
  }

  for (i, m) in trace.matrices.iter().enumerate() {
    if m.unpadded_height > 0 && !packed_chips.contains(&i) {
      return Err(format!(
        "active chip {} ({} rows) is missing from single_circuit constituents",
        m.chip, m.unpadded_height
      ));
    }
  }
  if !map_demand.is_empty() {
    let sample = map_demand
      .keys()
      .next()
      .map(|k| k.iter().map(|v| v.as_canonical_u64()).collect::<Vec<_>>())
      .unwrap_or_default();
    return Err(format!(
      "{} demanded map claim(s) missing from FIXED.bin (first: {sample:?})",
      map_demand.len()
    ));
  }
  for (&width, &count) in &rom_counts {
    if count > 0 && !packed_roms.contains(&width) {
      return Err(format!(
        "active ROM width {width} ({count} cells) missing from single_circuit constituents"
      ));
    }
  }

  Ok(RowMajorMatrix::new(packed, main_w))
}

fn eval_v2_sum(k: Val, terms: &[V2Term], values: &[Val]) -> Val {
  terms.iter().fold(k, |acc, t| match *t {
    V2Term::Lin(c, s) => acc + c * values[s],
    V2Term::Prod(c, a, b) => acc + c * values[a] * values[b],
  })
}

fn v2_lane_value(lane: &V2Lane, v: &[Val]) -> Val {
  match lane {
    V2Lane::Gate { qm, q, qc, cells } => {
      let x = |i: usize| cells[i].map_or(Val::ZERO, |s| v[s]);
      *qm * x(0) * x(1)
        + q[0] * x(0)
        + q[1] * x(1)
        + q[2] * x(2)
        + q[3] * x(3)
        + *qc
    },
    V2Lane::Empty | V2Lane::Msg { .. } => Val::ZERO,
  }
}

fn v2_eval_slots(
  t: &V2Template,
  rows: &[&[Val]],
  wide_width: usize,
  zero: bool,
) -> Result<Vec<Val>, String> {
  let mut v = vec![Val::ZERO; t.slots.len()];
  for (s, def) in t.slots.iter().enumerate() {
    v[s] = match def {
      V2Slot::Column(c) => {
        if zero {
          Val::ZERO
        } else {
          let body = *c / wide_width;
          let col = *c % wide_width;
          let row = rows.get(body).ok_or_else(|| {
            format!("slot {s} column {c} references missing body {body}")
          })?;
          *row.get(col).ok_or_else(|| {
            format!("slot {s} column {c} out of range for width {wide_width}")
          })?
        }
      },
      V2Slot::Sum { k, terms } => eval_v2_sum(*k, terms, &v),
      V2Slot::Key | V2Slot::Invocation => Val::ZERO,
    };
  }
  Ok(v)
}

fn v2_msg_mult(mk: Val, mc: Val, mult_slot: Option<usize>, v: &[Val]) -> Val {
  mk + mult_slot.map_or(Val::ZERO, |s| mc * v[s])
}

fn v2_zero_instance_ok(
  t: &V2Template,
  wide_width: usize,
) -> Result<bool, String> {
  let v = v2_eval_slots(t, &[], wide_width, true)?;
  for row in &t.rows {
    match row {
      V2Row::Gate { lanes, spans } => {
        for &(start, len) in spans {
          let sum = lanes[start..start + len]
            .iter()
            .fold(Val::ZERO, |acc, l| acc + v2_lane_value(l, &v));
          if sum != Val::ZERO {
            return Ok(false);
          }
        }
        for lane in lanes {
          if let V2Lane::Msg { mk, mc, cells, .. } = lane
            && v2_msg_mult(*mk, *mc, cells[0], &v) != Val::ZERO
          {
            return Ok(false);
          }
        }
      },
      V2Row::Message { mk, mc, cells, .. } => {
        if v2_msg_mult(*mk, *mc, cells[0], &v) != Val::ZERO {
          return Ok(false);
        }
      },
    }
  }
  Ok(true)
}

fn extract_contiguous_payload(
  cells: &[Option<usize>],
  ctx: &str,
) -> Result<Vec<usize>, String> {
  let mut out = Vec::with_capacity(cells.len());
  let mut seen_none = false;
  for &c in cells {
    match c {
      Some(s) => {
        if seen_none {
          return Err(format!("{ctx}: non-contiguous payload cells"));
        }
        out.push(s);
      },
      None => seen_none = true,
    }
  }
  Ok(out)
}

fn eval_v2_wide_nodes(
  g: &V2WideGraph,
  row: &[Val],
  targets: &[usize],
) -> Vec<Val> {
  let last = targets.iter().copied().max().unwrap_or(0);
  let mut vals: Vec<Val> = Vec::with_capacity(last + 1);
  for node in &g.nodes[..=last] {
    let x = match *node {
      V2WideNode::Const(k) => k,
      V2WideNode::Var(c) => row[c],
      V2WideNode::Add(a, b) => vals[a] + vals[b],
      V2WideNode::Sub(a, b) => vals[a] - vals[b],
      V2WideNode::Mul(a, b) => vals[a] * vals[b],
      V2WideNode::Neg(a) => -vals[a],
    };
    vals.push(x);
  }
  targets.iter().map(|&idx| vals[idx]).collect()
}

fn v2_unroll_instances(
  meta: &V2CircuitMeta,
  callable_id: usize,
  wide_rows: &[Vec<Val>],
) -> Result<Vec<Vec<usize>>, String> {
  let Some(stages) = meta.unroll_stages else {
    return Ok((0..wide_rows.len()).map(|r| vec![r]).collect());
  };
  let g = meta.wide_graph.as_ref().ok_or_else(|| {
    format!("unrolled circuit {} missing wide graph", meta.chip)
  })?;
  let var_of = |idx: usize| -> Option<usize> {
    match g.nodes[idx] {
      V2WideNode::Var(c) => Some(c),
      V2WideNode::Sub(z, x) if matches!(g.nodes[z], V2WideNode::Const(k) if k == Val::ZERO) => {
        match g.nodes[x] {
          V2WideNode::Var(c) => Some(c),
          _ => None,
        }
      },
      V2WideNode::Neg(x) => match g.nodes[x] {
        V2WideNode::Var(c) => Some(c),
        _ => None,
      },
      _ => None,
    }
  };
  let const_of = |idx: usize| -> Option<u64> {
    match g.nodes[idx] {
      V2WideNode::Const(k) => Some(k.as_canonical_u64()),
      _ => None,
    }
  };
  let cid_u64 = u64::try_from(callable_id)
    .map_err(|e| format!("callable id overflows u64: {e}"))?;
  let selfcalls: Vec<usize> = (1..g.lookups.len())
    .filter(|&j| {
      g.lookups[j].1.get(1).and_then(|&a| const_of(a)) == Some(cid_u64)
    })
    .collect();
  let [selfcall] = selfcalls[..] else {
    return Err(format!(
      "unrolled circuit {}: expected 1 self-call, found {}",
      meta.chip,
      selfcalls.len()
    ));
  };
  let sel_col = var_of(g.lookups[selfcall].0)
    .ok_or_else(|| format!("{}: self-call mult not a column", meta.chip))?;
  let stage_col = var_of(g.lookups[0].1[2])
    .ok_or_else(|| format!("{}: stage arg not a column", meta.chip))?;
  let recv_mult_col = var_of(g.lookups[0].0)
    .ok_or_else(|| format!("{}: receive mult not a column", meta.chip))?;
  let act_col = meta
    .wide_width
    .checked_sub(2)
    .ok_or_else(|| format!("{}: wide width < 2", meta.chip))?;

  let recv_nodes = &g.lookups[0].1[2..];
  let call_nodes = &g.lookups[selfcall].1[2..];
  let mut by_payload: FxHashMap<Vec<Val>, usize> = FxHashMap::default();
  for (r, row) in wide_rows.iter().enumerate() {
    by_payload.insert(eval_v2_wide_nodes(g, row, recv_nodes), r);
  }
  let mut chains = Vec::new();
  for (r0, row) in wide_rows.iter().enumerate() {
    if row[stage_col] == Val::ZERO && row[act_col] == Val::ONE {
      let mut chain = Vec::with_capacity(stages);
      chain.push(r0);
      for s in 0..stages {
        let r = *chain.last().expect("non-empty chain");
        let want_sel = if s + 1 < stages { Val::ONE } else { Val::ZERO };
        if wide_rows[r][sel_col] != want_sel
          || wide_rows[r][act_col] != Val::ONE
          || (s > 0 && wide_rows[r][recv_mult_col] != Val::ONE)
        {
          return Err(format!(
            "{}: unrolled stage {s} row {r} does not match expected body flags",
            meta.chip
          ));
        }
        if s + 1 < stages {
          let next_payload = eval_v2_wide_nodes(g, &wide_rows[r], call_nodes);
          let &next_r = by_payload.get(&next_payload).ok_or_else(|| {
            format!(
              "{}: unrolled stage {s} self-call has no callee row",
              meta.chip
            )
          })?;
          chain.push(next_r);
        }
      }
      chains.push(chain);
    }
  }
  Ok(chains)
}

struct V2ExtractedReceive {
  chunked: bool,
  mk: Val,
  mc: Val,
  mult_slot: Option<usize>,
  payload_slots: Vec<usize>,
}

struct V2ChunkedSend {
  key_slot: usize,
  base_sub: usize,
  mk: Val,
  mc: Val,
  mult_slot: Option<usize>,
  payload_slots: Vec<usize>,
}

#[derive(Clone, Copy)]
enum V2EmitKind {
  Map,
  Rom,
}

struct V2EmitSpec {
  kind: V2EmitKind,
  ts: u64,
  mk: Val,
  mc: Val,
  mult_slot: Option<usize>,
  is_lane: bool,
  cells: Vec<Option<usize>>,
}

struct V2TemplateInfo {
  receive: V2ExtractedReceive,
  chunked_sends: Vec<V2ChunkedSend>,
  emits: Vec<V2EmitSpec>,
  call_or_rom_mults: Vec<(Val, Val, Option<usize>)>,
}

fn extract_v2_template_info(
  chip: &str,
  callable_id: usize,
  n_funcs: usize,
  t: &V2Template,
  code_to_bus: &FxHashMap<u64, (u64, u64, bool)>,
) -> Result<V2TemplateInfo, String> {
  let mut recv_chunks: Vec<(usize, Val, Val, Option<usize>, Vec<usize>)> =
    Vec::new();
  let mut unchunked_recv: Option<V2ExtractedReceive> = None;
  let mut keyed_sends: FxHashMap<
    usize,
    Vec<(usize, usize, Val, Val, Option<usize>, Vec<usize>)>,
  > = FxHashMap::default();
  let mut emits: Vec<V2EmitSpec> = Vec::new();
  let mut call_or_rom_mults: Vec<(Val, Val, Option<usize>)> = Vec::new();

  let neg_one = -Val::ONE;

  for (ri, row) in t.rows.iter().enumerate() {
    match row {
      V2Row::Gate { lanes, .. } => {
        for (li, lane) in lanes.iter().enumerate() {
          let V2Lane::Msg { ts, mk, mc, cells } = lane else { continue };
          let &(tag, sub, is_lane) = code_to_bus.get(ts).ok_or_else(|| {
            format!("{chip} row {ri} lane {li}: unknown bus code {ts}")
          })?;
          if !is_lane {
            return Err(format!(
              "{chip} row {ri} lane {li}: lane msg uses non-lane bus {ts}"
            ));
          }
          let base_sub = usize::try_from(sub % CHUNK_STRIDE)
            .map_err(|e| format!("bus sub overflows usize: {e}"))?;
          if tag == CALL_TAG
            && sub == u64::try_from(callable_id).unwrap_or(u64::MAX)
            && *mk == Val::ZERO
            && *mc == neg_one
          {
            let payload_slots =
              extract_contiguous_payload(&cells[1..], "lane receive")?;
            if unchunked_recv.is_some() {
              return Err(format!("{chip}: duplicate unchunked receive"));
            }
            unchunked_recv = Some(V2ExtractedReceive {
              chunked: false,
              mk: *mk,
              mc: *mc,
              mult_slot: cells[0],
              payload_slots,
            });
          } else if tag == CALL_TAG && base_sub < n_funcs {
            call_or_rom_mults.push((*mk, *mc, cells[0]));
          } else if tag == CALL_TAG {
            emits.push(V2EmitSpec {
              kind: V2EmitKind::Map,
              ts: *ts,
              mk: *mk,
              mc: *mc,
              mult_slot: cells[0],
              is_lane: true,
              cells: cells.to_vec(),
            });
          } else if tag == ROM_TAG {
            call_or_rom_mults.push((*mk, *mc, cells[0]));
            emits.push(V2EmitSpec {
              kind: V2EmitKind::Rom,
              ts: *ts,
              mk: *mk,
              mc: *mc,
              mult_slot: cells[0],
              is_lane: true,
              cells: cells.to_vec(),
            });
          } else {
            return Err(format!("{chip}: unsupported bus tag {tag}"));
          }
        }
      },
      V2Row::Message { ts, mk, mc, receive_key, cells } => {
        let &(tag, sub, is_lane) = code_to_bus
          .get(ts)
          .ok_or_else(|| format!("{chip} row {ri}: unknown bus code {ts}"))?;
        if is_lane {
          return Err(format!(
            "{chip} row {ri}: full-row message uses lane bus {ts}"
          ));
        }
        let base_sub = usize::try_from(sub % CHUNK_STRIDE)
          .map_err(|e| format!("bus sub overflows usize: {e}"))?;
        if *receive_key {
          if tag != CALL_TAG || base_sub != callable_id || sub < CHUNK_STRIDE {
            return Err(format!(
              "{chip} row {ri}: malformed chunked receive bus ({tag}, {sub})"
            ));
          }
          if cells[1].is_some() {
            return Err(format!(
              "{chip} row {ri}: chunked receive has non-null key cell"
            ));
          }
          let chunk_idx = usize::try_from(sub / CHUNK_STRIDE - 1)
            .map_err(|e| format!("chunk index overflows usize: {e}"))?;
          let payload_part =
            extract_contiguous_payload(&cells[2..], "chunked receive")?;
          recv_chunks.push((chunk_idx, *mk, *mc, cells[0], payload_part));
          continue;
        }
        // Check if this is an unchunked receive on a row bus.
        if tag == CALL_TAG
          && sub == u64::try_from(callable_id).unwrap_or(u64::MAX)
          && *mk == Val::ZERO
          && *mc == neg_one
        {
          let payload_slots =
            extract_contiguous_payload(&cells[1..], "row receive")?;
          if unchunked_recv.is_some() {
            return Err(format!("{chip}: duplicate unchunked receive"));
          }
          unchunked_recv = Some(V2ExtractedReceive {
            chunked: false,
            mk: *mk,
            mc: *mc,
            mult_slot: cells[0],
            payload_slots,
          });
          continue;
        }
        // Check if this is a chunked call/map send (cells[1] is a V2Slot::Key).
        if let Some(ks) = cells[1]
          && matches!(t.slots[ks], V2Slot::Key)
        {
          if tag != CALL_TAG || sub < CHUNK_STRIDE {
            return Err(format!(
              "{chip} row {ri}: key slot {ks} on non-chunked-call bus ({tag}, {sub})"
            ));
          }
          let chunk_idx = usize::try_from(sub / CHUNK_STRIDE - 1)
            .map_err(|e| format!("chunk index overflows usize: {e}"))?;
          let part = extract_contiguous_payload(&cells[2..], "chunked send")?;
          keyed_sends
            .entry(ks)
            .or_default()
            .push((chunk_idx, base_sub, *mk, *mc, cells[0], part));
        }
        // Record call/map/rom emit specs.
        if tag == CALL_TAG && base_sub < n_funcs {
          call_or_rom_mults.push((*mk, *mc, cells[0]));
        } else if tag == CALL_TAG {
          emits.push(V2EmitSpec {
            kind: V2EmitKind::Map,
            ts: *ts,
            mk: *mk,
            mc: *mc,
            mult_slot: cells[0],
            is_lane: false,
            cells: cells.clone(),
          });
        } else if tag == ROM_TAG {
          call_or_rom_mults.push((*mk, *mc, cells[0]));
          emits.push(V2EmitSpec {
            kind: V2EmitKind::Rom,
            ts: *ts,
            mk: *mk,
            mc: *mc,
            mult_slot: cells[0],
            is_lane: false,
            cells: cells.clone(),
          });
        } else {
          return Err(format!("{chip}: unsupported bus tag {tag}"));
        }
      },
    }
  }

  let receive = if !recv_chunks.is_empty() {
    if unchunked_recv.is_some() {
      return Err(format!("{chip}: has both chunked and unchunked receive"));
    }
    recv_chunks.sort_by_key(|x| x.0);
    let (_, mk0, mc0, ms0, _) = recv_chunks[0];
    let mut payload_slots = Vec::new();
    for (expected_idx, (c_idx, mk, mc, ms, part)) in
      recv_chunks.into_iter().enumerate()
    {
      if c_idx != expected_idx || mk != mk0 || mc != mc0 || ms != ms0 {
        return Err(format!("{chip}: inconsistent chunked receive rows"));
      }
      payload_slots.extend(part);
    }
    V2ExtractedReceive {
      chunked: true,
      mk: mk0,
      mc: mc0,
      mult_slot: ms0,
      payload_slots,
    }
  } else {
    unchunked_recv
      .ok_or_else(|| format!("{chip}: template has no receive message"))?
  };

  let mut chunked_sends = Vec::with_capacity(keyed_sends.len());
  for (key_slot, mut parts) in keyed_sends {
    parts.sort_by_key(|x| x.0);
    let (_, base_sub0, mk0, mc0, ms0, _) = parts[0];
    let mut payload_slots = Vec::new();
    for (expected_idx, (c_idx, base_sub, mk, mc, ms, part)) in
      parts.into_iter().enumerate()
    {
      if c_idx != expected_idx
        || base_sub != base_sub0
        || mk != mk0
        || mc != mc0
        || ms != ms0
      {
        return Err(format!(
          "{chip}: inconsistent chunked send rows for key slot {key_slot}"
        ));
      }
      payload_slots.extend(part);
    }
    chunked_sends.push(V2ChunkedSend {
      key_slot,
      base_sub: base_sub0,
      mk: mk0,
      mc: mc0,
      mult_slot: ms0,
      payload_slots,
    });
  }
  chunked_sends.sort_by_key(|s| s.key_slot);

  Ok(V2TemplateInfo { receive, chunked_sends, emits, call_or_rom_mults })
}

fn resolve_entry_callable(
  layout: &SingleCircuitLayout,
) -> Result<usize, String> {
  match &layout.kind {
    LayoutKind::Wide { request, .. } => {
      if request.len() < 2
        || request[0] != Val::from_u64(CALL_TAG)
        || request[2..].iter().any(|&v| v != Val::ZERO)
      {
        return Err(
          "LAYOUT.json request is not a valid [CALL, id, 0..] template".into(),
        );
      }
      usize::try_from(request[1].as_canonical_u64())
        .map_err(|e| format!("request callable overflows usize: {e}"))
    },
    LayoutKind::TilingV2(v2) => {
      let first =
        v2.request.first().ok_or("tiling-v2 request array is empty")?;
      if first.is_empty() {
        return Err("tiling-v2 request row 0 is empty".into());
      }
      let code0 = first[0].as_canonical_u64();
      let &(tag0, sub0, _lane0) =
        v2.code_to_bus.get(&code0).ok_or_else(|| {
          format!("tiling-v2 request[0] has unknown bus code {code0}")
        })?;
      if tag0 != CALL_TAG {
        return Err(format!(
          "tiling-v2 request[0] tag {tag0} is not CALL ({CALL_TAG})"
        ));
      }
      if v2.request.len() == 1 && sub0 < CHUNK_STRIDE {
        if first[1..].iter().any(|&v| v != Val::ZERO) {
          return Err(
            "tiling-v2 unchunked request template has nonzero payload".into(),
          );
        }
        usize::try_from(sub0)
          .map_err(|e| format!("request callable overflows usize: {e}"))
      } else {
        if sub0 < CHUNK_STRIDE {
          return Err("tiling-v2 multi-row request lacks chunk stride".into());
        }
        let base = sub0 - CHUNK_STRIDE;
        for (c, row) in v2.request.iter().enumerate() {
          if row.len() != v2.shard_width {
            return Err(format!(
              "tiling-v2 chunked request[{c}] len {} != shard width {}",
              row.len(),
              v2.shard_width
            ));
          }
          let code_c = row[0].as_canonical_u64();
          let &(tag_c, sub_c, lane_c) =
            v2.code_to_bus.get(&code_c).ok_or_else(|| {
              format!("tiling-v2 request[{c}] unknown bus code {code_c}")
            })?;
          let want_sub = base
            .checked_add(
              (u64::try_from(c)
                .map_err(|e| format!("chunk idx overflow: {e}"))?
                + 1)
                * CHUNK_STRIDE,
            )
            .ok_or("request chunk sub overflow")?;
          if tag_c != CALL_TAG || sub_c != want_sub || lane_c {
            return Err(format!(
              "tiling-v2 request[{c}] bus ({tag_c}, {sub_c}, lane={lane_c}) \
               does not match chunk {c} of callable {base}"
            ));
          }
          if row[1..].iter().any(|&v| v != Val::ZERO) {
            return Err(format!(
              "tiling-v2 chunked request[{c}] template has nonzero key/payload"
            ));
          }
        }
        usize::try_from(base)
          .map_err(|e| format!("request callable overflows usize: {e}"))
      }
    },
  }
}

fn encode_v2_claims(
  v2: &TilingV2Data,
  wide_claim: &[Val],
  root_key: Val,
) -> Result<Vec<Vec<Val>>, String> {
  if wide_claim.len() < 2 || wide_claim[0] != Val::from_u64(CALL_TAG) {
    return Err("wide claim does not start with [CALL, callable, ...]".into());
  }
  let w = v2.shard_width;
  let callable = wide_claim[1].as_canonical_u64();
  let payload = &wide_claim[2..];
  let rows = if payload.len() < w {
    let &(code, is_lane) = v2
      .bus_to_code
      .get(&(CALL_TAG, callable))
      .ok_or_else(|| format!("no v2 bus for entry callable {callable}"))?;
    let pad_len = if is_lane { 4 } else { w };
    let mut row = Vec::with_capacity(pad_len);
    row.push(Val::from_u64(code));
    row.extend_from_slice(payload);
    row.resize(pad_len, Val::ZERO);
    vec![row]
  } else {
    let per = w - 2;
    let mut out = Vec::new();
    for (c, chunk) in payload.chunks(per).enumerate() {
      let sub = callable
        + (u64::try_from(c).map_err(|e| format!("chunk idx overflow: {e}"))?
          + 1)
          * CHUNK_STRIDE;
      let &(code, is_lane) =
        v2.bus_to_code.get(&(CALL_TAG, sub)).ok_or_else(|| {
          format!("no v2 bus for entry callable {callable} chunk {c}")
        })?;
      if is_lane {
        return Err(format!(
          "chunked entry callable {callable} chunk {c} mapped to lane bus"
        ));
      }
      let mut row = Vec::with_capacity(w);
      row.push(Val::from_u64(code));
      row.push(root_key);
      row.extend_from_slice(chunk);
      row.resize(w, Val::ZERO);
      out.push(row);
    }
    out
  };
  if rows.len() != v2.request.len() {
    return Err(format!(
      "encoded narrow claim count ({}) disagrees with LAYOUT.json request ({})",
      rows.len(),
      v2.request.len()
    ));
  }
  let is_chunked = payload.len() >= w;
  for (c, (got, tmpl)) in rows.iter().zip(&v2.request).enumerate() {
    if got.len() != tmpl.len() || got[0] != tmpl[0] {
      return Err(format!(
        "encoded narrow claim[{c}] header/len disagrees with LAYOUT.json request"
      ));
    }
    if is_chunked && got[1] != tmpl[1] {
      return Err(format!(
        "encoded narrow claim[{c}] root key {} disagrees with LAYOUT.json request key {}",
        got[1].as_canonical_u64(),
        tmpl[1].as_canonical_u64()
      ));
    }
  }
  Ok(rows)
}

/// Horizontally pack all `ix-tiling-v2-layout-1` constituent main traces
/// (periodic narrow shards + compact map/ROM tables) into one `rows x main_width`
/// matrix matching `SingleCircuit.packMain`.
fn pack_tiling_v2_main_matrix(
  layout: &SingleCircuitLayout,
  v2: &TilingV2Data,
  fixed: &RowMajorMatrix<Val>,
  plan: &TracePlan<'_, NativeField<Val>>,
  record: &aiur::Execution<NativeField<Val>>,
  trace: &aiur::trace::Trace<Val>,
  wide_claim: &[Val],
) -> Result<(RowMajorMatrix<Val>, Vec<Vec<Val>>, Val), String> {
  let packed_rows = layout.rows;
  let main_w = layout.main_width;
  let fixed_w = layout.fixed_width;
  let w = v2.shard_width;
  let num_circuits = v2.circuits.len();
  let prog = plan.program().program();
  let n_funcs = prog.functions.len();

  let mut chip_index: FxHashMap<&str, usize> = FxHashMap::default();
  for (i, m) in trace.matrices.iter().enumerate() {
    chip_index.insert(m.chip.as_str(), i);
  }

  let mut circuit_callables = Vec::with_capacity(num_circuits);
  let mut callable_to_circuit: FxHashMap<usize, usize> = FxHashMap::default();
  let mut packed_chips: FxHashSet<usize> = FxHashSet::default();
  let mut wide_rows_by_circuit: Vec<Vec<Vec<Val>>> =
    Vec::with_capacity(num_circuits);

  for (k, meta) in v2.circuits.iter().enumerate() {
    let &mi = chip_index.get(meta.chip.as_str()).ok_or_else(|| {
      format!("tiling-v2 circuit {k}: unknown chip {:?} in package", meta.chip)
    })?;
    let matrix = &trace.matrices[mi];
    if matrix.width + 1 != meta.wide_width {
      return Err(format!(
        "chip {}: wide trace width + 1 ({}) != exported wide width ({})",
        meta.chip,
        matrix.width + 1,
        meta.wide_width
      ));
    }
    let cid = plan.callable_id(&meta.chip).ok_or_else(|| {
      format!("chip {} has no callable id in package", meta.chip)
    })?;
    circuit_callables.push(cid);
    callable_to_circuit.insert(cid, k);
    packed_chips.insert(mi);

    let mut rows_vec = Vec::with_capacity(matrix.unpadded_height);
    for r in 0..matrix.unpadded_height {
      let mult = matrix.multiplicities[r];
      if mult >= Val::ORDER_U64 {
        return Err(format!(
          "chip {} row {r}: multiplicity reaches field characteristic",
          meta.chip
        ));
      }
      let mut row = Vec::with_capacity(meta.wide_width);
      row.extend_from_slice(matrix.row(r));
      row.push(Val::from_u64(mult));
      rows_vec.push(row);
    }
    wide_rows_by_circuit.push(rows_vec);
  }

  for (i, m) in trace.matrices.iter().enumerate() {
    if m.unpadded_height > 0 && !packed_chips.contains(&i) {
      return Err(format!(
        "active chip {} ({} rows) is missing from tiling-v2 layout circuits",
        m.chip, m.unpadded_height
      ));
    }
  }

  let mut instances: Vec<Vec<Vec<usize>>> = Vec::with_capacity(num_circuits);
  let mut infos: Vec<V2TemplateInfo> = Vec::with_capacity(num_circuits);
  let mut copy_padding: Vec<bool> = Vec::with_capacity(num_circuits);
  let mut id_bases: Vec<u64> = Vec::with_capacity(num_circuits);
  let mut row_bases: Vec<usize> = Vec::with_capacity(num_circuits);
  let mut cur_id = 0u64;
  let mut cur_row = 0usize;

  for k in 0..num_circuits {
    let inst = v2_unroll_instances(
      &v2.circuits[k],
      circuit_callables[k],
      &wide_rows_by_circuit[k],
    )?;
    let total_cap =
      v2.caps[k].checked_mul(v2.shards).ok_or("tiling-v2 capacity overflow")?;
    if inst.len() > total_cap {
      return Err(format!(
        "chip {}: execution needs {} instance(s), exceeding layout capacity {} ({} per shard x {} shards)",
        v2.circuits[k].chip,
        inst.len(),
        total_cap,
        v2.caps[k],
        v2.shards
      ));
    }
    instances.push(inst);
    infos.push(extract_v2_template_info(
      &v2.circuits[k].chip,
      circuit_callables[k],
      n_funcs,
      &v2.templates[k],
      &v2.code_to_bus,
    )?);
    copy_padding
      .push(!v2_zero_instance_ok(&v2.templates[k], v2.circuits[k].wide_width)?);
    id_bases.push(cur_id);
    row_bases.push(cur_row);
    cur_id = cur_id
      .checked_add(
        u64::try_from(v2.caps[k])
          .map_err(|e| format!("cap overflows u64: {e}"))?,
      )
      .ok_or("id_base overflow")?;
    cur_row = cur_row
      .checked_add(
        v2.caps[k]
          .checked_mul(v2.templates[k].rows.len())
          .ok_or("row_base overflow")?,
      )
      .ok_or("row_base overflow")?;
  }

  let global_id = |k: usize, n: usize| -> Result<Val, String> {
    let per = v2.caps[k];
    let shard =
      u64::try_from(n / per).map_err(|e| format!("shard overflow: {e}"))?;
    let local =
      u64::try_from(n % per).map_err(|e| format!("local idx overflow: {e}"))?;
    let id = shard
      .checked_mul(v2.ids_per_shard)
      .and_then(|x| x.checked_add(id_bases[k]))
      .and_then(|x| x.checked_add(local))
      .filter(|&x| x < Val::ORDER_U64)
      .ok_or("global invocation id overflow")?;
    Ok(Val::from_u64(id))
  };

  let row_refs_of = |k: usize, idxs: &[usize]| -> Vec<&[Val]> {
    idxs.iter().map(|&r| wide_rows_by_circuit[k][r].as_slice()).collect()
  };

  // Swap root entry instance to index 0 so its invocation id is 0 (matching Part.request).
  let entry_callable = usize::try_from(wide_claim[1].as_canonical_u64())
    .map_err(|e| format!("entry callable overflow: {e}"))?;
  let &entry_k = callable_to_circuit.get(&entry_callable).ok_or_else(|| {
    format!("entry callable {entry_callable} not found in layout circuits")
  })?;
  let entry_recv = &infos[entry_k].receive;
  let mut root_pos = None;
  for (n, row_idxs) in instances[entry_k].iter().enumerate() {
    let refs = row_refs_of(entry_k, row_idxs);
    let vals = v2_eval_slots(
      &v2.templates[entry_k],
      &refs,
      v2.circuits[entry_k].wide_width,
      false,
    )?;
    if v2_msg_mult(entry_recv.mk, entry_recv.mc, entry_recv.mult_slot, &vals)
      != Val::ZERO
      && entry_recv.payload_slots.len() == wide_claim.len() - 2
      && entry_recv
        .payload_slots
        .iter()
        .map(|&s| vals[s])
        .eq(wide_claim[2..].iter().copied())
    {
      root_pos = Some(n);
      break;
    }
  }
  let root_pos = root_pos
    .ok_or("no instance of the entry chip receives the public claim")?;
  instances[entry_k].swap(0, root_pos);
  let root_key = global_id(entry_k, 0)?;
  let narrow_claims = encode_v2_claims(v2, wide_claim, root_key)?;

  // Build receive payload -> global invocation id map for every chunked callee.
  let mut call_keys: FxHashMap<usize, FxHashMap<Vec<Val>, Val>> =
    FxHashMap::default();
  for k in 0..num_circuits {
    let recv = &infos[k].receive;
    if !recv.chunked {
      continue;
    }
    let mut map: FxHashMap<Vec<Val>, Val> = FxHashMap::default();
    for (n, row_idxs) in instances[k].iter().enumerate() {
      let refs = row_refs_of(k, row_idxs);
      let vals = v2_eval_slots(
        &v2.templates[k],
        &refs,
        v2.circuits[k].wide_width,
        false,
      )?;
      if v2_msg_mult(recv.mk, recv.mc, recv.mult_slot, &vals) != Val::ZERO {
        let payload: Vec<Val> =
          recv.payload_slots.iter().map(|&s| vals[s]).collect();
        map.insert(payload, global_id(k, n)?);
      }
    }
    call_keys.insert(k, map);
  }

  // If any template has a chunked map send, reconstruct (map_callable, payload) -> key from FIXED.bin.
  let has_chunked_map_send = infos
    .iter()
    .any(|info| info.chunked_sends.iter().any(|s| s.base_sub >= n_funcs));
  let mut chunked_map_keys: FxHashMap<(usize, Vec<Val>), Val> =
    FxHashMap::default();
  if has_chunked_map_send {
    for c in &layout.constituents {
      if !matches!(c.kind, ConstituentKind::CompactMap) {
        continue;
      }
      let mut grouped: FxHashMap<(usize, u64), Vec<(usize, Vec<Val>)>> =
        FxHashMap::default();
      for r in 0..c.rows {
        let base = r * fixed_w + c.fixed_offset;
        let code = fixed.values[base + 2].as_canonical_u64();
        let &(tag, sub, _lane) =
          v2.code_to_bus.get(&code).ok_or_else(|| {
            format!("compact map row {r} unknown bus code {code}")
          })?;
        if tag == CALL_TAG && sub >= CHUNK_STRIDE {
          let base_sub = usize::try_from(sub % CHUNK_STRIDE)
            .map_err(|e| format!("map sub overflow: {e}"))?;
          let chunk_idx = usize::try_from(sub / CHUNK_STRIDE - 1)
            .map_err(|e| format!("map chunk idx overflow: {e}"))?;
          let key_u64 = fixed.values[base + 3].as_canonical_u64();
          let chunk_vals = fixed.values[base + 4..base + 3 + (w - 1)].to_vec();
          grouped
            .entry((base_sub, key_u64))
            .or_default()
            .push((chunk_idx, chunk_vals));
        }
      }
      for ((base_sub, key_u64), mut parts) in grouped {
        parts.sort_by_key(|x| x.0);
        let mi = base_sub
          .checked_sub(n_funcs)
          .ok_or("chunked map base_sub precedes maps")?;
        let map_def = prog
          .maps
          .get(mi)
          .ok_or_else(|| format!("chunked map index {mi} out of range"))?;
        let in_len =
          prog.tables[map_def.input].rows.first().map_or(0, Vec::len);
        let out_len =
          prog.tables[map_def.output].rows.first().map_or(0, Vec::len);
        let plen = in_len + out_len;
        let mut payload = Vec::with_capacity(plen);
        for (_, chunk) in parts {
          payload.extend(chunk);
        }
        payload.truncate(plen);
        chunked_map_keys.insert((base_sub, payload), Val::from_u64(key_u64));
      }
    }
  }

  let total_cells =
    packed_rows.checked_mul(main_w).ok_or("packed main trace size overflow")?;
  let mut packed = Val::zero_vec(total_cells);

  let mut map_tuple_demand: FxHashMap<Vec<Val>, Val> = FxHashMap::default();
  let mut rom_row_demand: FxHashMap<(u64, u64), Val> = FxHashMap::default();

  // Fill every shard constituent and tally narrow map/ROM demands.
  for c in &layout.constituents {
    let ConstituentKind::Shard { shard_index } = c.kind else { continue };
    for k in 0..num_circuits {
      let t = &v2.templates[k];
      let tr = t.rows.len();
      let per = v2.caps[k];
      let rbase = row_bases[k];
      let info = &infos[k];
      let wide_w = v2.circuits[k].wide_width;

      for i in 0..per {
        let n = shard_index * per + i;
        let mut v = if n < instances[k].len() {
          let refs = row_refs_of(k, &instances[k][n]);
          v2_eval_slots(t, &refs, wide_w, false)?
        } else if copy_padding[k] {
          let first_inst = instances[k].first().ok_or_else(|| {
            format!(
              "{}: copy padding requires at least one real instance",
              v2.circuits[k].chip
            )
          })?;
          let refs = row_refs_of(k, first_inst);
          let mut vals = v2_eval_slots(t, &refs, wide_w, false)?;
          if let Some(m_slot) = info.receive.mult_slot {
            vals[m_slot] = Val::ZERO;
            for (s, def) in t.slots.iter().enumerate() {
              if let V2Slot::Sum { k: sk, terms } = def {
                vals[s] = eval_v2_sum(*sk, terms, &vals);
              }
            }
          }
          if info
            .call_or_rom_mults
            .iter()
            .any(|&(mk, mc, ms)| v2_msg_mult(mk, mc, ms, &vals) != Val::ZERO)
          {
            return Err(format!(
              "{}: copy padding would emit call/ROM sends",
              v2.circuits[k].chip
            ));
          }
          vals
        } else {
          v2_eval_slots(t, &[], wide_w, true)?
        };

        // Populate key slots for chunked sends.
        for send in &info.chunked_sends {
          if v2_msg_mult(send.mk, send.mc, send.mult_slot, &v) == Val::ZERO {
            v[send.key_slot] = Val::ZERO;
            continue;
          }
          let payload: Vec<Val> =
            send.payload_slots.iter().map(|&s| v[s]).collect();
          v[send.key_slot] = if send.base_sub < n_funcs {
            let &callee_k =
              callable_to_circuit.get(&send.base_sub).ok_or_else(|| {
                format!(
                  "{}: chunked call target callable {} not in layout",
                  v2.circuits[k].chip, send.base_sub
                )
              })?;
            *call_keys.get(&callee_k).and_then(|m| m.get(&payload)).ok_or_else(
              || {
                format!(
                  "{}: chunked call to {} has no matching callee instance",
                  v2.circuits[k].chip, v2.circuits[callee_k].chip
                )
              },
            )?
          } else {
            *chunked_map_keys
              .get(&(send.base_sub, payload))
              .ok_or_else(|| {
                format!(
                  "{}: chunked map call to callable {} missing from compact map table",
                  v2.circuits[k].chip, send.base_sub
                )
              })?
          };
        }

        // Write physical template rows into packed shard slice.
        for (r, row) in t.rows.iter().enumerate() {
          let dst_row = rbase + i * tr + r;
          let dst = &mut packed[dst_row * main_w + c.main_offset
            ..dst_row * main_w + c.main_offset + w];
          for (j, cell_out) in dst.iter_mut().enumerate() {
            if let Some(slot) = row.cell(j) {
              *cell_out = v[slot];
            }
          }
        }

        // Tally emitted map and ROM lookup tuples for compact tables.
        for emit in &info.emits {
          let mult = v2_msg_mult(emit.mk, emit.mc, emit.mult_slot, &v);
          if mult == Val::ZERO {
            continue;
          }
          match emit.kind {
            V2EmitKind::Map => {
              let arity = if emit.is_lane { 3 } else { w - 1 };
              let mut tuple = Vec::with_capacity(1 + arity);
              tuple.push(Val::from_u64(emit.ts));
              for j in 0..arity {
                let val = emit
                  .cells
                  .get(1 + j)
                  .copied()
                  .flatten()
                  .map_or(Val::ZERO, |s| v[s]);
                tuple.push(val);
              }
              trim_trailing_zeros(&mut tuple);
              let acc = map_tuple_demand.entry(tuple).or_insert(Val::ZERO);
              *acc += mult;
            },
            V2EmitKind::Rom => {
              let addr = emit
                .cells
                .get(1)
                .copied()
                .flatten()
                .map_or(Val::ZERO, |s| v[s])
                .as_canonical_u64();
              let acc =
                rom_row_demand.entry((emit.ts, addr)).or_insert(Val::ZERO);
              *acc += mult;
            },
          }
        }
      }
    }
  }

  // Fill compact map & ROM table constituents from FIXED.bin descriptors.
  for c in &layout.constituents {
    match c.kind {
      ConstituentKind::CompactMap => {
        for r in 0..c.rows {
          let f_base = r * fixed_w + c.fixed_offset;
          let sel_l = fixed.values[f_base];
          let sel_w = fixed.values[f_base + 1];
          let code = fixed.values[f_base + 2];
          let arity = if sel_l == Val::ONE {
            3
          } else if sel_w == Val::ONE {
            w - 1
          } else {
            continue;
          };
          let mut tuple = Vec::with_capacity(1 + arity);
          tuple.push(code);
          tuple
            .extend_from_slice(&fixed.values[f_base + 3..f_base + 3 + arity]);
          trim_trailing_zeros(&mut tuple);
          if let Some(count) = map_tuple_demand.remove(&tuple) {
            packed[r * main_w + c.main_offset] = count;
          }
        }
      },
      ConstituentKind::CompactRom => {
        for r in 0..c.rows {
          let f_base = r * fixed_w + c.fixed_offset;
          let sel_l = fixed.values[f_base];
          let sel_w = fixed.values[f_base + 1];
          if sel_l == Val::ZERO && sel_w == Val::ZERO {
            continue;
          }
          let code = fixed.values[f_base + 2].as_canonical_u64();
          let addr_u64 = fixed.values[f_base + 3].as_canonical_u64();
          let &(tag, sub, _lane) =
            v2.code_to_bus.get(&code).ok_or_else(|| {
              format!("compact ROM row {r}: unknown bus code {code}")
            })?;
          if tag != ROM_TAG {
            return Err(format!("compact ROM row {r}: non-ROM tag {tag}"));
          }
          let width = usize::try_from(sub % CHUNK_STRIDE)
            .map_err(|e| format!("ROM width overflow: {e}"))?;
          let chunk_idx = usize::try_from(sub / CHUNK_STRIDE)
            .map_err(|e| format!("ROM chunk idx overflow: {e}"))?;
          let addr = usize::try_from(addr_u64)
            .map_err(|e| format!("ROM addr overflow: {e}"))?;
          let count =
            rom_row_demand.remove(&(code, addr_u64)).unwrap_or(Val::ZERO);
          let dst = &mut packed[r * main_w + c.main_offset
            ..r * main_w + c.main_offset + c.main_width];
          dst[0] = count;
          if let Some(entry) = record.memory.get_by_width(width, addr) {
            if entry.address != addr || entry.cell.value.len() != width {
              return Err(format!(
                "ROM cell ({width}, {addr}) address/width mismatch"
              ));
            }
            if width + 2 <= w {
              if chunk_idx != 0 {
                return Err(format!(
                  "unchunked ROM width {width} has nonzero chunk index {chunk_idx}"
                ));
              }
              dst[1..1 + width].copy_from_slice(entry.cell.value);
            } else {
              let per = w - 2;
              let start = chunk_idx * per;
              let end = (start + per).min(width);
              if start >= width {
                return Err(format!(
                  "ROM width {width} chunk {chunk_idx} starts past width"
                ));
              }
              dst[1..1 + (end - start)]
                .copy_from_slice(&entry.cell.value[start..end]);
            }
          } else if count != Val::ZERO {
            return Err(format!(
              "compact ROM row {r} references unallocated cell ({width}, {addr})"
            ));
          }
        }
      },
      _ => {},
    }
  }

  let unmatched_maps =
    map_tuple_demand.iter().filter(|(_, v)| **v != Val::ZERO).count();
  if unmatched_maps > 0 {
    let sample = map_tuple_demand
      .iter()
      .find(|(_, v)| **v != Val::ZERO)
      .map(|(k, _)| k.iter().map(|x| x.as_canonical_u64()).collect::<Vec<_>>())
      .unwrap_or_default();
    return Err(format!(
      "{unmatched_maps} demanded narrow map tuple(s) missing from compact map table (first: {sample:?})"
    ));
  }
  let unmatched_roms =
    rom_row_demand.iter().filter(|(_, v)| **v != Val::ZERO).count();
  if unmatched_roms > 0 {
    let sample =
      rom_row_demand.iter().find(|(_, v)| **v != Val::ZERO).map(|(&k, _)| k);
    return Err(format!(
      "{unmatched_roms} demanded narrow ROM row(s) missing from compact ROM table (first: {sample:?})"
    ));
  }

  Ok((RowMajorMatrix::new(packed, main_w), narrow_claims, root_key))
}

fn make_config(
  cli: &Cli,
) -> (CommitmentParameters, FriParameters, GoldilocksBlake3V6Config) {
  let commitment =
    CommitmentParameters { log_blowup: cli.log_blowup, cap_height: 0 };
  let fri = FriParameters {
    log_final_poly_len: cli.fri_lfp,
    max_log_arity: cli.fri_mla,
    num_queries: cli.num_queries,
    commit_proof_of_work_bits: cli.commit_pow,
    query_proof_of_work_bits: cli.query_pow,
  };
  let config = GoldilocksBlake3V6Config::with_device(
    commitment,
    fri,
    FriBatching::Tensor,
    None,
  );
  (commitment, fri, config)
}

fn find_tamper_main_cell(
  layout: &SingleCircuitLayout,
  main: &RowMajorMatrix<Val>,
) -> (usize, usize, Val, String) {
  let w = main.width;
  for c in &layout.constituents {
    if let ConstituentKind::Unit { chip } = &c.kind
      && c.main_width >= 2
    {
      let act_col = c.main_offset + c.main_width - 2;
      let mult_col = c.main_offset + c.main_width - 1;
      for r in 0..c.rows {
        if main.values[r * w + act_col] == Val::ONE
          && main.values[r * w + mult_col] != Val::ZERO
        {
          return (
            r,
            act_col,
            Val::ZERO,
            format!("unit {chip} row {r} activation col {act_col} (1 -> 0)"),
          );
        }
      }
    }
  }
  for c in &layout.constituents {
    if let ConstituentKind::Shard { shard_index } = c.kind {
      for r in 0..c.rows {
        for j in 0..c.main_width {
          let col = c.main_offset + j;
          if main.values[r * w + col] != Val::ZERO {
            return (
              r,
              col,
              main.values[r * w + col] + Val::ONE,
              format!("shard {shard_index} row {r} col {col} (+1)"),
            );
          }
        }
      }
    }
  }
  (0, 0, main.values[0] + Val::ONE, "packed_main(0, 0) (+1)".to_owned())
}

fn find_tamper_fixed_cell(
  layout: &SingleCircuitLayout,
  main: &RowMajorMatrix<Val>,
  fixed: &RowMajorMatrix<Val>,
) -> (usize, usize, Val, String) {
  let mw = main.width;
  let fw = fixed.width;
  for (idx, c) in layout.constituents.iter().enumerate() {
    match c.kind {
      ConstituentKind::Map { .. } => {
        for r in 0..c.rows {
          if main.values[r * mw + c.main_offset] != Val::ZERO {
            let col = c.fixed_offset + 1;
            let new_val = fixed.values[r * fw + col] + Val::ONE;
            return (
              r,
              col,
              new_val,
              format!("map constituent {idx} row {r} fixed col {col} (+1)"),
            );
          }
        }
      },
      ConstituentKind::CompactMap => {
        for r in 0..c.rows {
          if main.values[r * mw + c.main_offset] != Val::ZERO {
            let col = c.fixed_offset + 3;
            let new_val = fixed.values[r * fw + col] + Val::ONE;
            return (
              r,
              col,
              new_val,
              format!(
                "compact map constituent {idx} row {r} fixed col {col} (+1)"
              ),
            );
          }
        }
      },
      _ => {},
    }
  }
  for (idx, c) in layout.constituents.iter().enumerate() {
    match c.kind {
      ConstituentKind::Rom { words, rom_vector } => {
        let lane_w = words + 1;
        for r in 0..c.rows {
          let has_active_lane = (0..rom_vector).any(|j| {
            main.values[r * mw + c.main_offset + j * lane_w] != Val::ZERO
          });
          if has_active_lane {
            let col = c.fixed_offset;
            let new_val = fixed.values[r * fw + col] + Val::ONE;
            return (
              r,
              col,
              new_val,
              format!(
                "rom constituent {idx} row {r} addr col {col} (K={rom_vector}, +1)"
              ),
            );
          }
        }
      },
      ConstituentKind::CompactRom => {
        for r in 0..c.rows {
          if main.values[r * mw + c.main_offset] != Val::ZERO {
            let col = c.fixed_offset + 3;
            let new_val = fixed.values[r * fw + col] + Val::ONE;
            return (
              r,
              col,
              new_val,
              format!(
                "compact rom constituent {idx} row {r} addr col {col} (+1)"
              ),
            );
          }
        }
      },
      _ => {},
    }
  }
  for (idx, c) in layout.constituents.iter().enumerate() {
    if let ConstituentKind::Shard { shard_index } = c.kind
      && c.rows > 0
    {
      for j in 0..c.fixed_width {
        let col = c.fixed_offset + j;
        if fixed.values[col] != Val::ZERO {
          return (
            0,
            col,
            fixed.values[col] + Val::ONE,
            format!(
              "shard {shard_index} constituent {idx} row 0 fixed col {col} (+1)"
            ),
          );
        }
      }
    }
  }
  for (idx, c) in layout.constituents.iter().enumerate() {
    if let Some(ac) = c.active_col
      && main.values[c.main_offset + c.main_width - 1] != Val::ZERO
    {
      return (
        0,
        ac,
        Val::ZERO,
        format!("constituent {idx} row 0 active_col {ac} (1 -> 0)"),
      );
    }
  }
  (0, 0, fixed.values[0] + Val::ONE, "fixed(0, 0) (+1)".to_owned())
}

fn pack_single_circuit(
  layout: &SingleCircuitLayout,
  fixed: &RowMajorMatrix<Val>,
  plan: &TracePlan<'_, NativeField<Val>>,
  record: &aiur::Execution<NativeField<Val>>,
  entry: &str,
  address: &[Val],
) -> Result<
  (RowMajorMatrix<Val>, Vec<Val>, Vec<Vec<Val>>, Option<Val>, bool),
  String,
> {
  let public_args = plan.public_args(record, entry, address)?;
  let wide_claim = plan.public_claim(entry, &public_args, &record.output)?;
  let trace = plan.generate(record, entry, address, false)?;
  let (packed_main, proof_claims, root_key_opt, trim_zeros) = match &layout.kind
  {
    LayoutKind::Wide { request, .. } => {
      if wide_claim.len() != request.len() || wide_claim[..2] != request[..2] {
        return Err(format!(
          "public claim header/length (len={}, head={:?}) disagrees with \
           LAYOUT.json request (len={}, head={:?})",
          wide_claim.len(),
          wide_claim
            .iter()
            .take(2)
            .map(|v| v.as_canonical_u64())
            .collect::<Vec<_>>(),
          request.len(),
          request
            .iter()
            .take(2)
            .map(|v| v.as_canonical_u64())
            .collect::<Vec<_>>(),
        ));
      }
      let main = pack_main_matrix(layout, fixed, plan, record, &trace)?;
      (main, vec![wide_claim.clone()], None, false)
    },
    LayoutKind::TilingV2(v2) => {
      let (main, narrow_claims, root_key) = pack_tiling_v2_main_matrix(
        layout,
        v2,
        fixed,
        plan,
        record,
        &trace,
        &wide_claim,
      )?;
      (main, narrow_claims, Some(root_key), true)
    },
  };
  Ok((packed_main, wide_claim, proof_claims, root_key_opt, trim_zeros))
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli = parse_cli().map_err(std::io::Error::other)?;
  let total_start = Instant::now();

  // Step 1: Read PACKAGE.ixa and verify optional BLAKE3 pin BEFORE decoding.
  let prep_start = Instant::now();
  let (raw_bytes, digest) = artifact::read(Path::new(&cli.package))?;
  let pin_report = match &cli.pin {
    Some(pin_path) => check_pin(pin_path, &raw_bytes, digest)?,
    None => Value::Null,
  };

  // Step 1b: Parse LAYOUT.json and FIXED.bin.
  let layout_bytes = std::fs::read(&cli.layout)
    .map_err(|e| format!("failed to read {}: {e}", cli.layout))?;
  let layout = parse_layout(&layout_bytes)?;
  let fixed_bytes = std::fs::read(&cli.fixed)
    .map_err(|e| format!("failed to read {}: {e}", cli.fixed))?;
  let fixed =
    read_single_fixed_block(&fixed_bytes, layout.rows, layout.fixed_width)?;
  validate_fixed_matrix(&layout, &fixed)?;

  let log_height = usize::try_from(layout.rows.ilog2())?;
  if log_height + cli.log_blowup > 32 {
    return Err(
      format!(
        "domain 2^({log_height} + {}) exceeds Goldilocks 2-adicity 32",
        cli.log_blowup
      )
      .into(),
    );
  }
  if cli.fri_lfp > log_height {
    return Err(
      format!(
        "--fri-lfp {} exceeds trace log_height {log_height}",
        cli.fri_lfp
      )
      .into(),
    );
  }

  // Step 2a: Decode PACKAGE.ixa, optional --advice & --stark-io, and bind hints.
  let (package, embedded_args, embedded_hints, kind) =
    if raw_bytes.starts_with(PACKAGE_MAGIC) {
      let pkg = Package::decode(&raw_bytes)
        .map_err(|e| format!("invalid program package {}: {e}", cli.package))?;
      (pkg, Vec::new(), Vec::new(), "program")
    } else if raw_bytes.starts_with(EXECUTION_MAGIC) {
      let exec = ExecutionPackage::decode(&raw_bytes).map_err(|e| {
        format!("invalid execution package {}: {e}", cli.package)
      })?;
      (exec.package, exec.args, exec.hints, "execution")
    } else {
      return Err(format!(
        "unrecognized artifact magic in {} (expected IXAIURP\\0 or IXAIURX\\0)",
        cli.package
      )
      .into());
    };
  drop(raw_bytes);
  eprintln!("artifact {} ({kind}): blake3 {digest}", cli.package);

  let (program, trace_artifact) = package.traced()?;
  let mut program = program.check_field::<Val>()?;
  program.track_depth(&trace_artifact)?;
  let field = program.field();
  let plan = TracePlan::new(&program, trace_artifact)?;

  let req_callable = resolve_entry_callable(&layout)?;
  let entry = program
    .program()
    .entries
    .iter()
    .find(|e| {
      let chip_name =
        &plan.artifact().chips[plan.function_chips()[e.function]].name;
      plan.callable_id(chip_name) == Some(req_callable)
    })
    .or_else(|| program.program().entries.first())
    .ok_or("no selected entrypoint in package")?
    .name
    .clone();

  let (advice_raw_program, advice_digest) = match &cli.advice {
    Some(adv_path) => {
      let (adv_prog, adv_dig) = load_advice_program(adv_path)?;
      eprintln!("advice {adv_path}: blake3 {adv_dig}");
      (Some(adv_prog), Some(adv_dig))
    },
    None => (None, None),
  };

  let stark_io = match &cli.stark_io {
    Some((key_path, claims_path, proof_path)) => {
      let io = load_stark_io(key_path, claims_path, proof_path)?;
      eprintln!(
        "stark-io: key={} ({} B) claims={} ({} B) proof={} ({} B)",
        io.key_blake3,
        io.key.len(),
        io.claims_blake3,
        io.claims.len(),
        io.proof_blake3,
        io.proof.len(),
      );
      Some(io)
    },
    None => None,
  };

  let resolved_args = if let Some(args) = &cli.override_args {
    args.clone()
  } else if !embedded_args.is_empty() {
    embedded_args.clone()
  } else if let Some(io) = &stark_io {
    stark_io_default_args(&entry, io)
  } else {
    Vec::new()
  };
  let address = field.decode(&resolved_args)?;

  let (hints, guess_channels, _tamper_hits) = build_hints(
    &program,
    &embedded_hints,
    stark_io.as_ref(),
    advice_raw_program.as_ref(),
    cli.tamper_hint.as_deref(),
  )?;
  if !guess_channels.is_empty() {
    eprintln!("registered guess channels: {guess_channels:?}");
  }
  let prepare_ms = prep_start.elapsed().as_secs_f64() * 1000.0;

  // Step 3a: Build 1-circuit System directly from certified single_circuit.circuit.
  let setup_start = Instant::now();
  let ext_params = extension_params::<GoldilocksBlake3V6Config>();
  let mut circuit_input = CircuitInputs {
    main_width: layout.main_width,
    preprocessed: (layout.fixed_width > 0).then(|| fixed.clone()),
    constraints: layout.constraints.clone(),
    lookups: layout.lookups.clone(),
    ..Default::default()
  };
  let pre_graph = circuit_input
    .compile_graph(&ext_params)
    .map_err(|e| format!("single-circuit graph compilation failed: {e:?}"))?;
  let lookup_group_size = choose_lookup_group(
    &pre_graph,
    layout.rows,
    cli.log_blowup,
    ext_params.degree,
    cli.lookup_group,
  )?;
  circuit_input.lookup_group_size = lookup_group_size;

  let (commitment, fri, config) = make_config(&cli);
  let (system, key) = System::new(config, vec![circuit_input]);
  assert_eq!(system.circuits.len(), 1);
  let circuit = &system.circuits[0];
  let setup_ms = setup_start.elapsed().as_secs_f64() * 1000.0;

  // Step 2b: Execute and horizontally pack main trace (`packMain`).
  let exec_start = Instant::now();
  let record = hints.execute(&entry, address.clone())?;
  let execution_ms = exec_start.elapsed().as_secs_f64() * 1000.0;

  let pack_start = Instant::now();
  let (packed_main, wide_claim, proof_claims, root_key_opt, trim_zeros) =
    pack_single_circuit(&layout, &fixed, &plan, &record, &entry, &address)?;
  let claim_refs: Vec<&[Val]> =
    proof_claims.iter().map(Vec::as_slice).collect();
  let output_words: Vec<u64> =
    record.output.iter().map(|v| v.as_canonical_u64()).collect();
  let arg_words: Vec<u64> =
    address.iter().map(|v| v.as_canonical_u64()).collect();
  let claim_words: Vec<u64> =
    wide_claim.iter().map(|v| v.as_canonical_u64()).collect();
  let pack_ms = pack_start.elapsed().as_secs_f64() * 1000.0;

  // Step 3b: Verify every constraint and exact LogUp balance on certified graph.
  let check_start = Instant::now();
  if cli.check {
    check_packed_circuit(
      &circuit.graph,
      &packed_main,
      circuit.preprocessed.as_ref(),
      &claim_refs,
      trim_zeros,
    )?;
  }
  let check_ms = check_start.elapsed().as_secs_f64() * 1000.0;

  let layout_format = match &layout.kind {
    LayoutKind::Wide { .. } => WIDE_LAYOUT_FORMAT,
    LayoutKind::TilingV2(_) => TILING_V2_LAYOUT_FORMAT,
  };

  // Step 3c: Prove and verify 1-circuit STARK.
  eprintln!(
    "Proving certified 1-circuit STARK ({layout_format}): rows={} main_w={} fixed_w={} s2_w={} \
     q_deg={} lg={} constraints={} lookups={} claims={} fri(b={}, q={}, mla={}, lfp={})...",
    layout.rows,
    layout.main_width,
    layout.fixed_width,
    circuit.stage_2_width,
    circuit.quotient_degree(),
    circuit.lookup_group_size,
    layout.num_constraints,
    layout.num_lookups,
    claim_refs.len(),
    commitment.log_blowup,
    fri.num_queries,
    fri.max_log_arity,
    fri.log_final_poly_len,
  );
  let prove_start = Instant::now();
  let proof = system.prove_multiple_claims_streaming(
    &key,
    &claim_refs,
    vec![packed_main.clone()],
  );
  let prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

  let proof_bytes = proof.to_bytes()?;
  let decoded = Proof::from_bytes(&proof_bytes)?;
  let expected_log_deg = u8::try_from(log_height)?;
  if decoded.active != [true] || decoded.log_degrees != [expected_log_deg] {
    return Err(
      format!(
        "unexpected proof shape: active={:?} log_degrees={:?}",
        decoded.active, decoded.log_degrees
      )
      .into(),
    );
  }

  let verify_start = Instant::now();
  system
    .verify_multiple_claims(&claim_refs, &decoded)
    .map_err(|e| format!("1-circuit STARK verification failed: {e:?}"))?;
  let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;
  let total_ms = total_start.elapsed().as_secs_f64() * 1000.0;
  let rss_kb = peak_rss_kb();

  eprintln!(
    "single_circuit_prove: format={layout_format} num_circuits=1 rows={} main_width={} fixed_width={} \
     stage2_width={} quotient_degree={} lookup_group={} constraints={} lookups={} claims={} \
     log_blowup={} num_queries={} fri_mla={} fri_lfp={} proof_bytes={} prove_ms={:.2} verify_ms={:.2}",
    layout.rows,
    layout.main_width,
    layout.fixed_width,
    circuit.stage_2_width,
    circuit.quotient_degree(),
    circuit.lookup_group_size,
    layout.num_constraints,
    layout.num_lookups,
    claim_refs.len(),
    commitment.log_blowup,
    fri.num_queries,
    fri.max_log_arity,
    fri.log_final_poly_len,
    proof_bytes.len(),
    prove_ms,
    verify_ms,
  );

  // Step 5: Mandatory negative controls (--controls).
  let mut wrong_hint_controls = Vec::new();
  let controls_report = if cli.controls {
    eprintln!(
      "Running negative controls (forged output, tampered main, tampered fixed{})...",
      if advice_raw_program.is_some() && !guess_channels.is_empty() {
        ", wrong hints"
      } else {
        ""
      }
    );

    // Control 1: Forged output claim (flip LSB of last wide output word and re-encode).
    let mut forged_wide = wide_claim.clone();
    let last_idx = forged_wide.len() - 1;
    forged_wide[last_idx] =
      Val::from_u64(forged_wide[last_idx].as_canonical_u64() ^ 1);
    let forged_claims: Vec<Vec<Val>> = match &layout.kind {
      LayoutKind::Wide { .. } => vec![forged_wide],
      LayoutKind::TilingV2(v2) => {
        encode_v2_claims(v2, &forged_wide, root_key_opt.unwrap_or(Val::ZERO))?
      },
    };
    let forged_refs: Vec<&[Val]> =
      forged_claims.iter().map(Vec::as_slice).collect();
    let forged_verify_err = match system
      .verify_multiple_claims(&forged_refs, &decoded)
    {
      Ok(()) => {
        return Err("CONTROL FAILED: verifier accepted honest proof under forged output claim".into());
      },
      Err(e) => format!("{e:?}"),
    };
    let forged_proof = system.prove_multiple_claims_streaming(
      &key,
      &forged_refs,
      vec![packed_main.clone()],
    );
    let forged_reprove_err = match system
      .verify_multiple_claims(&forged_refs, &forged_proof)
    {
      Ok(()) => {
        return Err("CONTROL FAILED: verifier accepted forged proof for wrong output claim".into());
      },
      Err(e) => format!("{e:?}"),
    };

    // Control 2: Tampered main trace cell.
    let mut tampered_main = packed_main.clone();
    let (tm_r, tm_c, tm_val, tm_desc) =
      find_tamper_main_cell(&layout, &packed_main);
    tampered_main.values[tm_r * tampered_main.width + tm_c] = tm_val;
    let tampered_main_check_rejected = check_packed_circuit(
      &circuit.graph,
      &tampered_main,
      circuit.preprocessed.as_ref(),
      &claim_refs,
      trim_zeros,
    )
    .is_err();
    let tampered_main_proof = system.prove_multiple_claims_streaming(
      &key,
      &claim_refs,
      vec![tampered_main],
    );
    let tampered_main_err =
      match system.verify_multiple_claims(&claim_refs, &tampered_main_proof) {
        Ok(()) => {
          return Err(format!(
            "CONTROL FAILED: verifier accepted tampered main trace ({tm_desc})"
          )
          .into());
        },
        Err(e) => format!("{e:?}"),
      };

    // Control 3: Tampered fixed matrix cell.
    let (tf_desc, tampered_fixed_honest_vk_err, tampered_fixed_self_err) =
      if layout.fixed_width > 0 {
        let mut tampered_fixed = fixed.clone();
        let (tf_r, tf_c, tf_val, tf_desc) =
          find_tamper_fixed_cell(&layout, &packed_main, &fixed);
        tampered_fixed.values[tf_r * tampered_fixed.width + tf_c] = tf_val;
        let tampered_input = CircuitInputs {
          main_width: layout.main_width,
          preprocessed: Some(tampered_fixed),
          constraints: layout.constraints.clone(),
          lookups: layout.lookups.clone(),
          lookup_group_size,
          ..Default::default()
        };
        let (_, _, tampered_cfg) = make_config(&cli);
        let (tampered_system, tampered_key) =
          System::new(tampered_cfg, vec![tampered_input]);
        let tampered_fixed_proof = tampered_system
          .prove_multiple_claims_streaming(
            &tampered_key,
            &claim_refs,
            vec![packed_main],
          );
        let honest_vk_err = match system
          .verify_multiple_claims(&claim_refs, &tampered_fixed_proof)
        {
          Ok(()) => {
            return Err(format!(
              "CONTROL FAILED: honest verifier accepted proof with tampered fixed matrix ({tf_desc})"
            )
            .into());
          },
          Err(e) => format!("{e:?}"),
        };
        let self_err = match tampered_system
          .verify_multiple_claims(&claim_refs, &tampered_fixed_proof)
        {
          Ok(()) => {
            return Err(format!(
            "CONTROL FAILED: tampered-fixed system accepted broken relation ({tf_desc})"
          )
          .into());
          },
          Err(e) => format!("{e:?}"),
        };
        (tf_desc, honest_vk_err, self_err)
      } else {
        return Err(
          "CONTROL FAILED: cannot tamper fixed matrix because fixed_width == 0"
            .into(),
        );
      };

    // Control 4: Wrong-hint rejection for every active `"ixcc.guess.*"` channel.
    if cli.tamper_hint.is_none()
      && let Some(adv_raw) = &advice_raw_program
    {
      for ch in &guess_channels {
        let (bad_hints, _, hits_opt) = build_hints(
          &program,
          &embedded_hints,
          stark_io.as_ref(),
          Some(adv_raw),
          Some(ch),
        )?;
        let hits = hits_opt.expect("tamper counter present");
        match bad_hints.execute(&entry, address.clone()) {
          Err(error) => {
            wrong_hint_controls.push(json!({
              "tampered_channel": ch,
              "invocations": hits.load(Ordering::Relaxed),
              "rejected": true,
              "stage": "execute",
              "error": error.to_string(),
            }));
          },
          Ok(bad_record) => {
            let invoked = hits.load(Ordering::Relaxed);
            if invoked == 0 {
              wrong_hint_controls.push(json!({
                "tampered_channel": ch,
                "invocations": 0,
                "rejected": false,
                "stage": "not_invoked",
              }));
            } else {
              match pack_single_circuit(
                &layout,
                &fixed,
                &plan,
                &bad_record,
                &entry,
                &address,
              ) {
                Err(error) => {
                  wrong_hint_controls.push(json!({
                    "tampered_channel": ch,
                    "invocations": invoked,
                    "rejected": true,
                    "stage": "pack",
                    "error": error,
                  }));
                },
                Ok((bad_main, _, bad_claims, _, bad_trim)) => {
                  let bad_refs: Vec<&[Val]> =
                    bad_claims.iter().map(Vec::as_slice).collect();
                  match check_packed_circuit(
                    &circuit.graph,
                    &bad_main,
                    circuit.preprocessed.as_ref(),
                    &bad_refs,
                    bad_trim,
                  ) {
                    Err(error) => {
                      wrong_hint_controls.push(json!({
                        "tampered_channel": ch,
                        "invocations": invoked,
                        "rejected": true,
                        "stage": "trace_check",
                        "error": error,
                      }));
                    },
                    Ok(()) => {
                      let bad_proof = system.prove_multiple_claims_streaming(
                        &key,
                        &bad_refs,
                        vec![bad_main],
                      );
                      match system.verify_multiple_claims(&bad_refs, &bad_proof)
                      {
                        Err(error) => {
                          wrong_hint_controls.push(json!({
                            "tampered_channel": ch,
                            "invocations": invoked,
                            "rejected": true,
                            "stage": "stark_verify",
                            "error": format!("{error:?}"),
                          }));
                        },
                        Ok(()) => {
                          return Err(format!(
                            "CONTROL FAILED: single-circuit accepted tampered hint on \
                             channel {ch:?} ({invoked} invocations)"
                          )
                          .into());
                        },
                      }
                    },
                  }
                },
              }
            }
          },
        }
      }
    }

    let rejected_wrong_hints = wrong_hint_controls
      .iter()
      .filter(|entry| entry["rejected"].as_bool() == Some(true))
      .count();

    eprintln!(
      "Negative controls PASSED: forged_output=REJECTED, tampered_main({tm_desc})=REJECTED, \
       tampered_fixed({tf_desc})=REJECTED (honest VK & self), rejected_wrong_hints={rejected_wrong_hints}"
    );
    json!({
      "enabled": true,
      "all_passed": true,
      "forged_output_verify_rejected": true,
      "forged_output_verify_error": forged_verify_err,
      "forged_output_reprove_rejected": true,
      "forged_output_reprove_error": forged_reprove_err,
      "tampered_main_target": tm_desc,
      "tampered_main_check_rejected": tampered_main_check_rejected,
      "tampered_main_verify_rejected": true,
      "tampered_main_verify_error": tampered_main_err,
      "tampered_fixed_target": tf_desc,
      "tampered_fixed_honest_vk_rejected": true,
      "tampered_fixed_honest_vk_error": tampered_fixed_honest_vk_err,
      "tampered_fixed_self_rejected": true,
      "tampered_fixed_self_error": tampered_fixed_self_err,
      "rejected_wrong_hints": rejected_wrong_hints,
      "wrong_hint_controls": wrong_hint_controls,
    })
  } else {
    json!({ "enabled": false })
  };

  let rejected_wrong_hints = wrong_hint_controls
    .iter()
    .filter(|entry| entry["rejected"].as_bool() == Some(true))
    .count();

  if let Some(path) = &cli.proof_out {
    std::fs::write(path, &proof_bytes)?;
  }

  let stark_io_report = stark_io.as_ref().map(|io| {
    json!({
      "key_blake3": io.key_blake3,
      "key_bytes": io.key.len(),
      "claims_blake3": io.claims_blake3,
      "claims_bytes": io.claims.len(),
      "proof_blake3": io.proof_blake3,
      "proof_bytes": io.proof.len(),
    })
  });

  let mut report = json!({
    "layout_format": layout_format,
    "artifact_blake3": digest.to_string(),
    "pin": pin_report,
    "advice_blake3": advice_digest.map(|d| d.to_string()),
    "guess_channels": guess_channels,
    "stark_io": stark_io_report,
    "entry": entry,
    "args": arg_words,
    "output": output_words,
    "claim": claim_words,
    "num_claims": proof_claims.len(),
    "bound": layout.bound,
    "num_circuits": 1,
    "rows": layout.rows,
    "main_width": layout.main_width,
    "fixed_width": layout.fixed_width,
    "stage2_width": circuit.stage_2_width,
    "quotient_degree": circuit.quotient_degree(),
    "lookup_group_size": circuit.lookup_group_size,
    "constraints": layout.num_constraints,
    "lookups": layout.num_lookups,
    "constituents": layout.constituents.len(),
    "fri": {
      "log_blowup": commitment.log_blowup,
      "cap_height": commitment.cap_height,
      "num_queries": fri.num_queries,
      "commit_proof_of_work_bits": fri.commit_proof_of_work_bits,
      "query_proof_of_work_bits": fri.query_proof_of_work_bits,
      "max_log_arity": fri.max_log_arity,
      "log_final_poly_len": fri.log_final_poly_len,
    },
    "proof_bytes": proof_bytes.len(),
    "proof_kb": f64::from(u32::try_from(proof_bytes.len()).unwrap_or(u32::MAX)) / 1024.0,
    "prepare_ms": prepare_ms,
    "setup_ms": setup_ms,
    "execution_ms": execution_ms,
    "pack_ms": pack_ms,
    "check_ms": check_ms,
    "prove_ms": prove_ms,
    "verify_ms": verify_ms,
    "total_ms": total_ms,
    "peak_rss_kb": rss_kb,
    "verified": true,
    "rejected_wrong_hints": rejected_wrong_hints,
    "wrong_hint_controls": wrong_hint_controls,
    "controls": controls_report,
  });
  match &layout.kind {
    LayoutKind::Wide { rom_vector, .. } => {
      if let Some(obj) = report.as_object_mut() {
        obj.insert("rom_vector".to_owned(), json!(rom_vector));
      }
    },
    LayoutKind::TilingV2(v2) => {
      if let Some(obj) = report.as_object_mut() {
        let narrow_words: Vec<Vec<u64>> = proof_claims
          .iter()
          .map(|c| c.iter().map(|v| v.as_canonical_u64()).collect())
          .collect();
        obj.insert("shard_width".to_owned(), json!(v2.shard_width));
        obj.insert("shards".to_owned(), json!(v2.shards));
        obj.insert("places".to_owned(), json!(v2.places));
        obj.insert("narrow_claims".to_owned(), json!(narrow_words));
      }
    },
  }

  if let Some(path) = &cli.report_out {
    serde_json::to_writer_pretty(
      std::io::BufWriter::new(std::fs::File::create(path)?),
      &report,
    )?;
  }
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use aiur::bytecode::{Entry, Function, Instruction, VERSION};
  use aiur::value::IoType;

  #[test]
  fn stark_io_channels_serve_info_reads_and_goldilocks_inverse() {
    let key: Vec<u8> = (10u8..26u8).collect();
    let claims: Vec<u8> = (100u8..112u8).collect();
    let proof: Vec<u8> = (0u8..70u8).collect();
    let io = StarkIoFiles {
      key_blake3: blake3::hash(&key).to_hex().to_string(),
      claims_blake3: blake3::hash(&claims).to_hex().to_string(),
      proof_blake3: blake3::hash(&proof).to_hex().to_string(),
      key: key.clone(),
      claims: claims.clone(),
      proof: proof.clone(),
    };

    let pair = Type::Tuple { items: vec![Type::Field; 2] };
    let arr1 = Type::Tuple { items: vec![Type::Field; 1] };
    let arr8 = Type::Tuple { items: vec![Type::Field; 8] };
    let out_ty = Type::Tuple { items: vec![Type::Field; 12] };
    let prog = Program {
      version: VERSION,
      modulus: Val::ORDER_U64,
      functions: vec![Function {
        name: "Test::io".into(),
        params: vec![Type::Field],
        result: out_ty.clone(),
        registers: 18,
        code: vec![
          // reg 0: input x (invert via goldilocks.inverse -> reg 17)
          Instruction::Hint {
            channel: "goldilocks.inverse".into(),
            key_type: Type::Field,
            r#type: Type::Field,
            key: vec![0],
            dest: vec![17],
          },
          // reg 1 = 1 (key channel), reg 2 = 0 (subkey) -> info into (3, 4)
          Instruction::Literal { dest: 1, value: 1 },
          Instruction::Literal { dest: 2, value: 0 },
          Instruction::Hint {
            channel: "stark.io.info".into(),
            key_type: pair.clone(),
            r#type: pair.clone(),
            key: vec![1, 2],
            dest: vec![3, 4],
          },
          // read1 from channel 2 (claims) at offset 3 -> reg 7
          Instruction::Literal { dest: 5, value: 2 },
          Instruction::Literal { dest: 6, value: 3 },
          Instruction::Hint {
            channel: "stark.io.read1".into(),
            key_type: pair.clone(),
            r#type: arr1,
            key: vec![5, 6],
            dest: vec![7],
          },
          // read8 from channel 0 (proof) at offset 5 -> regs 9..17
          Instruction::Literal { dest: 8, value: 5 },
          Instruction::Hint {
            channel: "stark.io.read8".into(),
            key_type: pair,
            r#type: arr8,
            key: vec![2, 8],
            dest: (9..17).collect(),
          },
          // Return [info_off, info_len, read1_byte, read8_bytes(8), inv_x]
          Instruction::Ret {
            value: vec![3, 4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17],
          },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Test::io".into(),
        function: 0,
        inputs: vec![IoType::Field],
        output: Some(IoType::Tuple { items: vec![IoType::Field; 12] }),
      }],
    };
    let checked = prog.check_field::<Val>().unwrap();
    let (hints, _, _) =
      build_hints(&checked, &[], Some(&io), None, None).unwrap();
    let rec = hints.execute("Test::io", vec![Val::from_u64(7)]).unwrap();
    assert_eq!(rec.output[0], Val::ZERO);
    assert_eq!(rec.output[1], Val::from_usize(key.len()));
    assert_eq!(rec.output[2], Val::from_u64(u64::from(claims[3])));
    for i in 0..8 {
      assert_eq!(rec.output[3 + i], Val::from_u64(u64::from(proof[5 + i])));
    }
    assert_eq!(rec.output[11] * Val::from_u64(7), Val::ONE);

    // Default statement args match CompressWrap and MultiStark conventions.
    let cw_args = stark_io_default_args(COMPRESS_WRAP_ENTRY, &io);
    assert_eq!(cw_args.len(), 16);
    assert_eq!(&cw_args[..8], &[0u64; 8]);
    let ms_args = stark_io_default_args(MULTI_STARK_ENTRY, &io);
    assert_eq!(ms_args.len(), 16);
    assert_eq!(&ms_args[..8], digest_words(&key).as_slice());
    assert_eq!(&ms_args[8..], digest_words(&claims).as_slice());
  }

  #[test]
  fn parse_and_validate_vector_rom_layout_and_reject_mismatches() {
    let valid_json = json!({
      "format": WIDE_LAYOUT_FORMAT,
      "field": "goldilocks",
      "modulus": Val::ORDER_U64.to_string(),
      "bound": 1000,
      "rom_vector": 4,
      "request": ["1", "0"],
      "single_circuit": {
        "num_circuits": 1,
        "rows": 4,
        "main_width": 12,
        "fixed_width": 2,
        "num_constraints": 0,
        "num_lookups": 0,
        "constituents": [{
          "kind": "rom",
          "index": 0,
          "rows": 2,
          "main_offset": 0,
          "main_width": 12,
          "fixed_offset": 0,
          "fixed_width": 1,
          "active_col": 1,
          "words": 2,
          "rom_vector": 4,
          "capacity": 8
        }],
        "circuit": {
          "width": 12,
          "fixed_width": 2,
          "nodes": [],
          "zeros": [],
          "lookups": []
        }
      }
    });
    let layout =
      parse_layout(&serde_json::to_vec(&valid_json).unwrap()).unwrap();
    assert!(matches!(layout.kind, LayoutKind::Wide { rom_vector: 4, .. }));

    // Fixed matrix has [addr_base = 4*r, active_col = (r < 2)]
    let good_fixed = RowMajorMatrix::new(
      vec![
        Val::from_u64(0),
        Val::ONE,
        Val::from_u64(4),
        Val::ONE,
        Val::from_u64(8),
        Val::ZERO,
        Val::from_u64(12),
        Val::ZERO,
      ],
      2,
    );
    validate_fixed_matrix(&layout, &good_fixed).unwrap();

    // Scalar fixed address (1 instead of 4) on row 1 must be rejected!
    let mut bad_fixed = good_fixed;
    bad_fixed.values[2] = Val::from_u64(1);
    assert!(validate_fixed_matrix(&layout, &bad_fixed).is_err());

    // Mismatched constituent rom_vector or wrong capacity must fail closed!
    let mut bad_cap = valid_json.clone();
    bad_cap["single_circuit"]["constituents"][0]["capacity"] = json!(7);
    assert!(parse_layout(&serde_json::to_vec(&bad_cap).unwrap()).is_err());

    let mut zero_k = valid_json;
    zero_k["rom_vector"] = json!(0);
    assert!(parse_layout(&serde_json::to_vec(&zero_k).unwrap()).is_err());
  }
}
