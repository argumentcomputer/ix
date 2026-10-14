//! Export a trusted v5 profile and native verification vectors for Solidity.

use super::*;
use ark_bls12_381::{Fq, G1Affine, G1Projective, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::{
  config::ProofConfig,
  eval::VarValues,
  expr::{RowOffset, Source},
  graph::{ConstraintGraph, Node},
  prover::{Proof, observe_claims, sample_lookup_challenges},
  system::{System, SystemWitness},
  traits::{Algebra, EvaluationDomain, Pcs, Transcript},
};
use serde_json::{Value as Json, json};
use std::{fmt::Write as _, sync::Arc};

mod codegen;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn hex(bytes: &[u8]) -> String {
  let mut out = String::with_capacity(bytes.len() * 2);
  for byte in bytes {
    write!(&mut out, "{byte:02x}").unwrap();
  }
  out
}

fn hex_json(bytes: &[u8]) -> String {
  format!("0x{}", hex(bytes))
}

fn scalar(value: Scalar) -> String {
  hex_json(&value.0.into_bigint().to_bytes_be())
}

fn fq(value: Fq) -> Vec<u8> {
  value.into_bigint().to_bytes_be()
}

fn g1(point: G1Affine) -> Vec<u8> {
  if point.is_zero() {
    return vec![0; 128];
  }
  [vec![0; 16], fq(point.x), vec![0; 16], fq(point.y)].concat()
}

fn g2(point: G2Affine) -> Vec<u8> {
  if point.is_zero() {
    return vec![0; 256];
  }
  [point.x.c0, point.x.c1, point.y.c0, point.y.c1]
    .into_iter()
    .flat_map(|v| [vec![0; 16], fq(v)].concat())
    .collect()
}

fn compressed(point: &G1Affine) -> Vec<u8> {
  let mut bytes = vec![];
  point.serialize_compressed(&mut bytes).unwrap();
  bytes
}

fn hints(points: impl IntoIterator<Item = G1Affine>) -> Vec<u8> {
  points
    .into_iter()
    .flat_map(|p| if p.is_zero() { vec![0; 48] } else { fq(p.y) })
    .collect()
}

fn proof_points(proof: &Proof<KzgConfig>) -> Vec<G1Affine> {
  [
    &proof.commitments.stage_1_trace,
    &proof.commitments.stage_2_trace,
    &proof.commitments.quotient_chunks,
  ]
  .into_iter()
  .flat_map(|c| c.0.iter().flatten().copied())
  .chain(proof.opening_proof.0.iter().copied())
  .collect()
}

#[derive(Clone, Copy)]
struct GraphMatrix {
  index: usize,
  width: usize,
  rows: usize,
}

/// Opening windows indexed by the graph's three variable sources.
#[derive(Clone, Copy)]
struct GraphInputs {
  main: GraphMatrix,
  preprocessed: GraphMatrix,
  stage2: GraphMatrix,
  public_count: usize,
}

impl GraphInputs {
  fn for_circuit(system: &System<KzgConfig>, index: usize) -> Result<Self> {
    if index >= 2 {
      return Err("Solidity graph requires one of two circuits".into());
    }
    let c = system.circuits.get(index).ok_or("missing circuit")?;
    Ok(Self {
      main: GraphMatrix {
        index,
        width: c.main_width,
        rows: 1 + usize::from(system.opens_next_row(index, Source::Main)),
      },
      preprocessed: GraphMatrix {
        index: 6 + index,
        width: c.preprocessed_width,
        rows: 1
          + usize::from(system.opens_next_row(index, Source::Preprocessed)),
      },
      stage2: GraphMatrix { index: 2 + index, width: c.stage_2_width, rows: 2 },
      public_count: c.num_publics,
    })
  }

  fn matrix(self, source: Source) -> GraphMatrix {
    match source {
      Source::Main => self.main,
      Source::Preprocessed => self.preprocessed,
      Source::Stage2 => self.stage2,
    }
  }
}

/// Validated arithmetic with variable references resolved into opening windows.
#[derive(Clone, Copy)]
enum GraphInstruction {
  Constant(Scalar),
  Opening { matrix: usize, offset: usize },
  Public(usize),
  First,
  Last,
  Transition,
  Add(usize, usize),
  Sub(usize, usize),
  Mul(usize, usize),
  Neg(usize),
}

struct GraphProgram {
  instructions: Vec<GraphInstruction>,
  uses_proof: bool,
  uses_view: bool,
}

impl GraphProgram {
  fn compile(
    graph: &ConstraintGraph<Scalar>,
    inputs: GraphInputs,
  ) -> Result<Self> {
    if inputs.public_count != 4 {
      return Err("Solidity graph requires four circuit public scalars".into());
    }
    for m in [inputs.main, inputs.preprocessed, inputs.stage2] {
      if m.index >= 8 || !(1..=2).contains(&m.rows) {
        return Err("invalid Solidity graph opening window".into());
      }
    }
    let mut program = Self {
      instructions: Vec::with_capacity(graph.nodes.len()),
      uses_proof: false,
      uses_view: false,
    };
    for (index, node) in graph.nodes.iter().enumerate() {
      let child = |id: multi_stark::graph::NodeId| -> Result<usize> {
        let child = id.index();
        if child >= index {
          return Err("graph child must precede its parent".into());
        }
        Ok(child)
      };
      let instruction = match *node {
        Node::Const(value) => GraphInstruction::Constant(value),
        Node::Var(col) => {
          let matrix = inputs.matrix(col.source);
          let row = usize::from(col.offset == RowOffset::Next);
          let column = usize::try_from(col.index)?;
          if row >= matrix.rows || column >= matrix.width {
            return Err("graph column lies outside its opening window".into());
          }
          let offset = row
            .checked_mul(matrix.width)
            .and_then(|base| base.checked_add(column))
            .ok_or("graph opening offset overflow")?;
          program.uses_proof = true;
          GraphInstruction::Opening { matrix: matrix.index, offset }
        },
        Node::Public(index) => {
          let index = usize::try_from(index)?;
          if index >= inputs.public_count {
            return Err("graph public index out of range".into());
          }
          program.uses_view = true;
          GraphInstruction::Public(index)
        },
        Node::IsFirstRow => {
          program.uses_view = true;
          GraphInstruction::First
        },
        Node::IsLastRow => {
          program.uses_view = true;
          GraphInstruction::Last
        },
        Node::IsTransition => {
          program.uses_view = true;
          GraphInstruction::Transition
        },
        Node::Add(a, b) => GraphInstruction::Add(child(a)?, child(b)?),
        Node::Sub(a, b) => GraphInstruction::Sub(child(a)?, child(b)?),
        Node::Mul(a, b) => GraphInstruction::Mul(child(a)?, child(b)?),
        Node::Neg(a) => GraphInstruction::Neg(child(a)?),
      };
      program.instructions.push(instruction);
    }
    for root in
      graph.zeros.iter().chain(graph.lookups.iter().flat_map(|lookup| {
        std::iter::once(&lookup.multiplicity).chain(&lookup.args)
      }))
    {
      if root.index() >= graph.nodes.len() {
        return Err("graph root out of range".into());
      }
    }
    Ok(program)
  }

  fn write_function(&self, out: &mut String, circuit: usize) -> Result<()> {
    let proof = if self.uses_proof { " proof" } else { "" };
    let view = if self.uses_view { " view_" } else { "" };
    writeln!(
      out,
      "\n    function _evaluateCircuit{circuit}(Proof memory{proof}, EvaluationView memory{view})\n        private pure returns (uint256[] memory values) {{"
    )?;
    writeln!(
      out,
      "        values = new uint256[]({});",
      self.instructions.len()
    )?;
    for (index, instruction) in self.instructions.iter().enumerate() {
      let expression = match *instruction {
        GraphInstruction::Constant(value) => scalar(value),
        GraphInstruction::Opening { matrix, offset } => {
          let extra =
            if offset == 0 { String::new() } else { format!(" + {offset}") };
          format!("proof.values[proof.matrices[{matrix}].valueOffset{extra}]")
        },
        GraphInstruction::Public(index) => format!("view_.publics[{index}]"),
        GraphInstruction::First => "view_.first".into(),
        GraphInstruction::Last => "view_.last".into(),
        GraphInstruction::Transition => "view_.transition".into(),
        GraphInstruction::Add(a, b) => {
          format!("addmod(values[{a}], values[{b}], R)")
        },
        GraphInstruction::Sub(a, b) => {
          format!("Scalar.sub(values[{a}], values[{b}])")
        },
        GraphInstruction::Mul(a, b) => {
          format!("mulmod(values[{a}], values[{b}], R)")
        },
        GraphInstruction::Neg(a) => format!("Scalar.negate(values[{a}])"),
      };
      writeln!(out, "        values[{index}] = {expression};")?;
    }
    out.push_str("    }\n");
    Ok(())
  }
}

fn source(
  profile: &VerifierProfile,
  system: &System<KzgConfig>,
  test_fixture: bool,
) -> Result<String> {
  let openings = codegen::OpeningLayout::new(profile, system)?;
  if system.circuits.len() != 2 {
    return Err("Solidity export requires two circuits".into());
  }
  let graphs = system
    .circuits
    .iter()
    .enumerate()
    .map(|(i, c)| {
      GraphProgram::compile(&c.graph, GraphInputs::for_circuit(system, i)?)
    })
    .collect::<Result<Vec<_>>>()?;
  let mut out = String::from(concat!(
    "// SPDX-License-Identifier: MIT OR Apache-2.0\n",
    "pragma solidity ^0.8.28;\n\n",
    "import {KzgVerifier} from \"./KzgVerifier.sol\";\n",
    "import {Scalar} from \"./Scalar.sol\";\n\n",
    "/// Fixed verifier constants exported from an authenticated native v5 profile.\n",
    "contract GeneratedVerifier is KzgVerifier {\n",
    "    function _profile() internal pure override returns (Profile memory p) {\n",
  ));
  if test_fixture {
    out = out.replace(
      "/// Fixed verifier constants exported from an authenticated native v5 profile.",
      "/// Test-only conformance circuit; this does not prove a Lean library computation or an inner recursive proof.",
    );
  }
  writeln!(out, "        p.id = hex\"{}\";", hex(&profile.id()))?;
  writeln!(
    out,
    "        p.seed = hex\"{}\";",
    hex(system.config.transcript_seed())
  )?;
  for i in 0..2 {
    writeln!(out, "        p.circuits[{i}] = _circuit{i}();")?;
  }
  let fixed: Vec<_> = system
    .preprocessed_commit
    .as_ref()
    .ok_or("missing fixed commitments")?
    .0
    .iter()
    .flatten()
    .copied()
    .collect();
  let params = system.config.pcs().verifier_params();
  let inner = profile.keys()?;
  for (name, bytes) in [
    ("fixedCompressed", fixed.iter().flat_map(compressed).collect::<Vec<_>>()),
    ("fixedPoints", fixed.into_iter().flat_map(g1).collect()),
    ("generator", g1(params.g1[0])),
    ("outerH", g2(params.g2)),
    ("outerTauH", g2(params.tau_g2)),
    ("innerH", g2(inner[0])),
    ("innerTauH", g2(inner[1])),
  ] {
    writeln!(out, "        p.{name} = hex\"{}\";", hex(&bytes))?;
  }
  out.push_str("    }\n");
  for (i, c) in system.circuits.iter().enumerate() {
    writeln!(
      out,
      "\n    function _circuit{i}() private pure returns (Circuit memory c) {{"
    )?;
    for (name, value) in [
      ("logDegree", profile.heights[i].ilog2() as usize),
      ("mainWidth", c.main_width),
      ("stage2Width", c.stage_2_width),
      ("preprocessedWidth", c.preprocessed_width),
      ("quotientDegree", c.quotient_degree()),
      ("constraintCount", c.constraint_count()),
      ("maxConstraintDegree", c.max_constraint_degree()),
      ("lookupGroupSize", c.lookup_group_size),
    ] {
      writeln!(out, "        c.{name} = {value};")?;
    }
    writeln!(
      out,
      "        c.mainNext = {};",
      system.opens_next_row(i, Source::Main)
    )?;
    writeln!(
      out,
      "        c.preprocessedNext = {};",
      system.opens_next_row(i, Source::Preprocessed)
    )?;
    let domain =
      system.config.pcs().natural_domain_for_degree(profile.heights[i]);
    writeln!(out, "        c.omega = {};", scalar(domain.generator()))?;
    writeln!(out, "        c.zeros = new uint256[]({});", c.graph.zeros.len())?;
    for (j, node) in c.graph.zeros.iter().enumerate() {
      writeln!(out, "        c.zeros[{j}] = {};", node.index())?;
    }
    writeln!(
      out,
      "        c.lookups = new Lookup[]({});",
      c.graph.lookups.len()
    )?;
    for (j, lookup) in c.graph.lookups.iter().enumerate() {
      writeln!(
        out,
        "        c.lookups[{j}].multiplicity = {};",
        lookup.multiplicity.index()
      )?;
      writeln!(
        out,
        "        c.lookups[{j}].args = new uint256[]({});",
        lookup.args.len()
      )?;
      for (k, arg) in lookup.args.iter().enumerate() {
        writeln!(out, "        c.lookups[{j}].args[{k}] = {};", arg.index())?;
      }
    }
    out.push_str("    }\n");
  }
  out.push_str(concat!(
    "\n    function _evaluateGraph(Circuit memory, Proof memory proof, uint256 ci, EvaluationView memory view_)\n",
    "        internal pure override returns (uint256[] memory values) {\n",
    "        if (ci == 0) return _evaluateCircuit0(proof, view_);\n",
    "        if (ci == 1) return _evaluateCircuit1(proof, view_);\n",
    "        revert InvalidProfile();\n",
    "    }\n",
  ));
  for (i, graph) in graphs.iter().enumerate() {
    graph.write_function(&mut out, i)?;
  }
  openings.write_functions(&mut out)?;
  out.push_str("}\n");
  Ok(out)
}

struct Batch {
  z: Scalar,
  commitments: Vec<G1Affine>,
  values: Vec<Scalar>,
}

fn diagnostics(
  system: &System<KzgConfig>,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
) -> Result<Json> {
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  system
    .verify_multiple_claims(&refs, proof)
    .map_err(|e| format!("native proof: {e:?}"))?;
  let mut t = system.config.initialise_challenger();
  system.observe_shape(&mut t);
  for &active in &proof.active {
    t.observe_field(Scalar::from_bool(active));
  }
  t.observe_commitment(
    system.preprocessed_commit.clone().ok_or("missing fixed commitment")?,
  );
  t.observe_commitment(proof.commitments.stage_1_trace.clone());
  for &log in &proof.log_degrees {
    t.observe_field(Scalar::from_u8(log));
  }
  observe_claims::<KzgConfig>(&mut t, &refs);
  let (beta, gamma) = sample_lookup_challenges::<KzgConfig>(&mut t);
  let mut accumulator = claims
    .iter()
    .map(|row| {
      (beta
        + row
          .iter()
          .rev()
          .fold(Scalar::ZERO, |acc, value| acc * gamma + *value))
      .inverse()
    })
    .fold(Scalar::ZERO, |a, b| a + b);
  let public_accumulator = accumulator;
  t.observe_commitment(proof.commitments.stage_2_trace.clone());
  for &a in &proof.intermediate_accumulators {
    t.observe_challenge(a);
  }
  let alpha = t.sample_challenge();
  t.observe_commitment(proof.commitments.quotient_chunks.clone());
  let zeta = t.sample_challenge();
  let rounds = [
    (&proof.commitments.stage_1_trace, &proof.stage_1_opened_values),
    (&proof.commitments.stage_2_trace, &proof.stage_2_opened_values),
    (&proof.commitments.quotient_chunks, &proof.quotient_opened_values),
    (
      system.preprocessed_commit.as_ref().unwrap(),
      proof.preprocessed_opened_values.as_ref().unwrap(),
    ),
  ];
  for (commit, _) in &rounds {
    t.observe_commitment((*commit).clone());
    for &log in &proof.log_degrees {
      t.observe_canonical(&u64::from(log));
    }
  }
  let mut batches: Vec<Batch> = vec![];
  for (commit, values) in &rounds {
    for (i, rows) in values.iter().enumerate() {
      let domain = system
        .config
        .pcs()
        .natural_domain_for_degree(1 << proof.log_degrees[i]);
      for (row, values) in rows.iter().enumerate() {
        let z = if row == 0 { zeta } else { domain.next_point(zeta) };
        for &v in values {
          t.observe_challenge(v);
        }
        let index = match batches.iter().position(|b| b.z == z) {
          Some(index) => index,
          None => {
            batches.push(Batch { z, commitments: vec![], values: vec![] });
            batches.len() - 1
          },
        };
        batches[index].commitments.extend_from_slice(&commit.0[i]);
        batches[index].values.extend_from_slice(values);
      }
    }
  }
  let v = t.sample_challenge();
  for witness in &proof.opening_proof.0 {
    t.observe_canonical(witness);
  }
  let r = t.sample_challenge();
  if batches.len() != proof.opening_proof.0.len() {
    return Err("opening count mismatch".into());
  }
  let mut left = G1Projective::zero();
  let mut right = G1Projective::zero();
  let mut rp = Scalar::ONE;
  let generator = system.config.pcs().verifier_params().g1[0];
  for (batch, witness) in batches.iter().zip(&proof.opening_proof.0) {
    let mut folded = G1Projective::zero();
    let mut y = Scalar::ZERO;
    let mut vp = Scalar::ONE;
    for (c, value) in batch.commitments.iter().zip(&batch.values) {
      folded += *c * vp.0;
      y += *value * vp;
      vp *= v;
    }
    left += (folded - generator * y.0 + *witness * batch.z.0) * rp.0;
    right += *witness * rp.0;
    rp *= r;
  }
  let mut compositions = vec![];
  let mut quotients = vec![];
  for (i, c) in system.circuits.iter().enumerate() {
    let n = 1usize << proof.log_degrees[i];
    let domain = system.config.pcs().natural_domain_for_degree(n);
    let sels = domain.selectors_at_point(zeta);
    let next = proof.intermediate_accumulators[i];
    let publics = [beta, gamma, accumulator, next];
    let fixed = &proof.preprocessed_opened_values.as_ref().unwrap()[i];
    let main = &proof.stage_1_opened_values[i];
    let stage2 = &proof.stage_2_opened_values[i];
    let view = VarValues {
      preprocessed: [&fixed[0], fixed.get(1).map_or(&[][..], Vec::as_slice)],
      main: [&main[0], main.get(1).map_or(&[][..], Vec::as_slice)],
      stage2: [&stage2[0], &stage2[1]],
      publics: &publics,
      is_first_row: sels.is_first_row,
      is_last_row: sels.is_last_row,
      is_transition: sels.is_transition,
    };
    let mut values = vec![];
    c.graph.sweep(&view, &mut values);
    let mut constraints = c.graph.constraint_values(&values);
    let ext = multi_stark::system::extension_params::<KzgConfig>();
    let delta = (next - accumulator)
      * (Scalar::from_usize(n) * domain.generator()).inverse();
    multi_stark::lookup::logup_constraint_values(
      &c.graph.lookups,
      &values,
      &stage2[0],
      &stage2[1],
      &publics,
      &[delta],
      sels.is_last_row,
      ext.w,
      ext.degree,
      c.lookup_group_size.max(1),
      &mut constraints,
    );
    let composition = constraints
      .into_iter()
      .fold(Scalar::ZERO, |acc, value| acc * alpha + value);
    let zn = zeta.exp_power_of_2(usize::from(proof.log_degrees[i]));
    let quotient = proof.quotient_opened_values[i][0]
      .iter()
      .zip(zn.powers())
      .map(|(&value, power)| value * power)
      .fold(Scalar::ZERO, |a, b| a + b);
    if composition * sels.inv_vanishing != quotient {
      return Err("diagnostic quotient mismatch".into());
    }
    compositions.push(scalar(composition));
    quotients.push(scalar(quotient));
    accumulator = next;
  }
  Ok(json!({
    "challenges": ([beta, gamma, alpha, zeta, v, r].map(scalar)),
    "publicAccumulator": scalar(public_accumulator),
    "outerL": hex_json(&g1(left.into_affine())),
    "outerR": hex_json(&g1(right.into_affine())),
    "compositions": compositions,
    "quotients": quotients,
  }))
}

fn statement_words(packet: &[u8]) -> Result<[u64; 18]> {
  let bytes =
    packet.get(32..32 + 18 * 8).ok_or("truncated public statement")?;
  Ok(std::array::from_fn(|i| {
    u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap())
  }))
}

fn write_export(
  profile: &VerifierProfile,
  packet: &[u8],
  directory: &Path,
  solidity: &Path,
  name: &str,
  expect_valid_pairing: bool,
  test_fixture: bool,
) -> Result<()> {
  if profile.version != OUTER_PROFILE_VERSION {
    return Err("Solidity export requires a v5 profile".into());
  }
  let system = profile.system()?;
  let keys = profile.keys()?;
  let words = statement_words(packet)?;
  let (claims, offset) =
    packet_claims_for_statement(packet, &profile.id(), keys.len(), &words)?;
  let logs: Vec<_> =
    profile.heights.iter().map(|h| u8::try_from(h.ilog2()).unwrap()).collect();
  let proof =
    FixedProofCodec::new(&system, &logs)?.decode(&packet[offset..])?;
  let mut diagnostic = diagnostics(&system, &proof, &claims)?;
  let point_bytes = &packet[32 + 18 * 8..offset];
  if check_pairings(point_bytes, &keys).is_ok() != expect_valid_pairing {
    return Err("unexpected deferred pairing result".into());
  }
  let inner: Vec<_> = point_bytes
    .as_chunks::<48>()
    .0
    .iter()
    .map(|point| G1Affine::deserialize_compressed(point.as_slice()))
    .collect::<std::result::Result<_, _>>()?;
  let y_hints = hints(inner.into_iter().chain(proof_points(&proof)));
  diagnostic["scope"] = if test_fixture {
    "small-conformance-circuit-not-a-lean-library"
  } else {
    "trusted-exported-native-profile"
  }
  .into();
  diagnostic["setupClass"] =
    SetupClass::of(&profile.verifier_params()?).label().into();
  diagnostic["profileVersion"] = profile.version.into();
  diagnostic["expectedClaim"] = json!(words);
  diagnostic["packet"] = hex_json(packet).into();
  diagnostic["yHints"] = hex_json(&y_hints).into();
  diagnostic["profileId"] = hex_json(&profile.id()).into();
  diagnostic["packetBytes"] = packet.len().into();
  diagnostic["hintBytes"] = y_hints.len().into();
  diagnostic["nativeOuterVerified"] = true.into();
  diagnostic["nativeDeferredPairingVerified"] = expect_valid_pairing.into();
  diagnostic["traceHeights"] = json!(profile.heights);
  diagnostic["verifierDigestBlake3"] = blake3::hash(
    &bincode::serde::encode_to_vec(profile, bincode::config::standard())?,
  )
  .to_hex()
  .to_string()
  .into();
  let contract = source(profile, &system, test_fixture)?;
  fs::create_dir_all(directory)?;
  if let Some(parent) = solidity.parent() {
    fs::create_dir_all(parent)?;
  }
  fs::write(
    directory.join(format!("{name}.json")),
    serde_json::to_vec_pretty(&diagnostic)?,
  )?;
  fs::write(directory.join(format!("{name}.bin")), packet)?;
  fs::write(solidity, contract)?;
  Ok(())
}

/// Export constants from a trusted portable profile after native verification.
pub fn export_solidity_verifier(
  verifier: &Path,
  packet: &Path,
  expected_verifier_digest: &str,
  directory: &Path,
  solidity: &Path,
) -> Result<()> {
  let bytes = fs::read(verifier)?;
  if blake3::hash(&bytes).to_hex().as_str() != expected_verifier_digest {
    return Err("portable verifier digest mismatch".into());
  }
  let profile = VerifierProfile::from_bytes(&bytes)?;
  let packet = fs::read(packet)?;
  if profile.version != OUTER_PROFILE_VERSION {
    return Err("Solidity export requires a v5 profile".into());
  }
  profile.verify_with_claim(&packet, &statement_words(&packet)?)?;
  write_export(&profile, &packet, directory, solidity, "fixture", true, false)
}

/// Generate small Filecoin-backed outer-profile proofs for EVM conformance tests.
pub fn write_solidity_fixture(directory: &Path, solidity: &Path) -> Result<()> {
  use crate::kzg::srs::filecoin::{
    FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3, load_filecoin_cache,
  };
  use multi_stark::plonkish::CircuitBuilder;
  let cache = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("tests/fixtures/filecoin-prefix-2p8.bin");
  let anchors =
    load_filecoin_cache(&cache, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3, 2)?;
  let mut builder = CircuitBuilder::<Scalar>::new();
  let private = builder.input("private");
  let table = builder
    .fixed_table("range", (0..16).map(|n| vec![Scalar::from_u8(n)]).collect());
  builder.lookup(table, &[private]);
  let square = builder.mul(private, private);
  let forty_nine = builder.constant(Scalar::from_u8(49));
  builder.assert_equal(square, forty_nine);
  let publics: Vec<_> = (0..22)
    .map(|i| {
      let value = builder.input(format!("public{i}"));
      builder.expose_public(value);
      value
    })
    .collect();
  let circuit = builder.finish();
  let height = circuit.multi_stark_layout()?.main_height;
  if height > 256 {
    return Err("small fixture exceeds checked-in Filecoin prefix".into());
  }
  let compiled = circuit
    .lower_to_multi_stark_sharded(Scalar::from_u8(94), height)?
    .merge_table_traces(height)?;
  let srs =
    load_filecoin_cache(&cache, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3, height)?;
  let config =
    KzgConfig::new(Arc::new(srs), 2).with_transcript(TranscriptKind::Keccak256);
  let (system, key) =
    System::new(config, compiled.kzg_circuit_inputs(height, 2)?);
  if system.circuits.len() != 2 {
    return Err("fixture requires two circuits".into());
  }
  let fixed = system.preprocessed_commit.as_ref().unwrap();
  let mut setup = vec![];
  for (i, c) in system.circuits.iter().enumerate() {
    let mut portable: multi_stark::system::Circuit<Scalar> =
      decode(&bincode::serde::encode_to_vec(c, bincode::config::standard())?)?;
    portable.preprocessed = None;
    setup.push(bincode::serde::encode_to_vec(
      (portable, KzgCommitment(vec![fixed.0[i].clone()])),
      bincode::config::standard(),
    )?);
  }
  let mut pairings = vec![];
  vec![anchors.g2, anchors.tau_g2].serialize_compressed(&mut pairings)?;
  let profile = VerifierProfile {
    version: OUTER_PROFILE_VERSION,
    heights: [
      system.circuits[0].preprocessed_height,
      system.circuits[1].preprocessed_height,
    ],
    setup: setup.try_into().map_err(|_setup| "fixture setup count")?,
    pairings: bincode::serde::encode_to_vec(
      Pairings { keys: pairings },
      bincode::config::standard(),
    )?,
    parameters: system.config.pcs().verifier_params().to_bytes()?,
  };
  fs::create_dir_all(directory)?;
  fs::write(
    directory.join("verifier.bin"),
    bincode::serde::encode_to_vec(&profile, bincode::config::standard())?,
  )?;
  let first_words: [u64; 18] = std::array::from_fn(|i| match i {
    0 => 0,
    1 => 17,
    _ => 1000 + u64::try_from(i).unwrap(),
  });
  let second_words: [u64; 18] = std::array::from_fn(|i| match i {
    0 => 0,
    1 => 31,
    _ => 2000 + u64::try_from(i).unwrap(),
  });
  for (name, words, valid) in [
    ("fixture", first_words, true),
    ("fixture-other-statement", second_words, true),
    ("fixture-bad-pairing", first_words, false),
  ] {
    let first = if valid {
      anchors.g1[1]
    } else {
      (anchors.g1[1] + anchors.g1[0]).into_affine()
    };
    let second = -anchors.g1[0];
    let mut prefix = profile.id().to_vec();
    for word in words {
      prefix.extend(word.to_le_bytes());
    }
    prefix.extend(compressed(&first));
    prefix.extend(compressed(&second));
    let (claims, _) =
      packet_claims_for_statement(&prefix, &profile.id(), 2, &words)?;
    let mut witness = compiled.witness();
    witness.set(private, Scalar::from_u8(7))?;
    for (wire, claim) in publics.iter().zip(&claims[1..]) {
      witness.set(*wire, claim[3])?;
    }
    let assignment = witness.generate()?;
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(compiled.traces(&assignment)?, &system),
    );
    let codec = FixedProofCodec::new(&system, &proof.log_degrees)?;
    let mut packet = prefix;
    packet.extend(codec.encode(&proof)?);
    if valid {
      profile.verify_with_claim(&packet, &words)?;
    }
    write_export(&profile, &packet, directory, solidity, name, valid, true)?;
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{expr::ColRef, graph::NodeId, lookup::Lookup};

  fn graph_inputs(circuit: usize) -> GraphInputs {
    GraphInputs {
      main: GraphMatrix { index: circuit, width: 3, rows: 2 },
      preprocessed: GraphMatrix { index: 6 + circuit, width: 4, rows: 2 },
      stage2: GraphMatrix { index: 2 + circuit, width: 2, rows: 2 },
      public_count: 4,
    }
  }

  fn graph(nodes: Vec<Node<Scalar>>) -> ConstraintGraph<Scalar> {
    ConstraintGraph {
      degrees: vec![0; nodes.len()],
      nodes,
      zeros: vec![],
      lookups: vec![],
      lookup_prefix_len: 0,
      max_constraint_degree: 0,
    }
  }

  fn variable(source: Source, offset: RowOffset, index: u32) -> Node<Scalar> {
    Node::Var(ColRef { source, offset, index })
  }

  fn evaluate_program(
    program: &GraphProgram,
    openings: &[Vec<Scalar>; 8],
    view: &VarValues<'_, Scalar>,
  ) -> Vec<Scalar> {
    let mut values: Vec<Scalar> =
      Vec::with_capacity(program.instructions.len());
    for instruction in &program.instructions {
      let value = match *instruction {
        GraphInstruction::Constant(value) => value,
        GraphInstruction::Opening { matrix, offset } => {
          openings[matrix][offset]
        },
        GraphInstruction::Public(index) => view.publics[index],
        GraphInstruction::First => view.is_first_row,
        GraphInstruction::Last => view.is_last_row,
        GraphInstruction::Transition => view.is_transition,
        GraphInstruction::Add(a, b) => values[a] + values[b],
        GraphInstruction::Sub(a, b) => values[a] - values[b],
        GraphInstruction::Mul(a, b) => values[a] * values[b],
        GraphInstruction::Neg(a) => -values[a],
      };
      values.push(value);
    }
    values
  }

  #[test]
  fn graph_lowering_matches_native_evaluation_for_every_node_and_window()
  -> Result<()> {
    let graph = graph(vec![
      Node::Const(-Scalar::ONE),
      variable(Source::Main, RowOffset::Current, 0),
      variable(Source::Main, RowOffset::Next, 2),
      variable(Source::Preprocessed, RowOffset::Current, 1),
      variable(Source::Preprocessed, RowOffset::Next, 0),
      variable(Source::Stage2, RowOffset::Current, 1),
      variable(Source::Stage2, RowOffset::Next, 0),
      Node::Public(0),
      Node::Public(1),
      Node::Public(2),
      Node::Public(3),
      Node::IsFirstRow,
      Node::IsLastRow,
      Node::IsTransition,
      Node::Add(NodeId(0), NodeId(1)),
      Node::Sub(NodeId(2), NodeId(3)),
      Node::Mul(NodeId(14), NodeId(15)),
      Node::Neg(NodeId(16)),
    ]);
    for circuit in 0..2 {
      let inputs = graph_inputs(circuit);
      let program = GraphProgram::compile(&graph, inputs)?;
      assert!(program.uses_proof && program.uses_view);
      for trial in [0, 1, 17, 94] {
        let mut openings: [Vec<Scalar>; 8] = std::array::from_fn(|_| vec![]);
        for m in [inputs.main, inputs.preprocessed, inputs.stage2] {
          openings[m.index] = (0..m.rows * m.width)
            .map(|i| Scalar::from_usize(trial * m.index + i) - Scalar::ONE)
            .collect();
        }
        let rows = |m: GraphMatrix| {
          [&openings[m.index][..m.width], &openings[m.index][m.width..]]
        };
        let publics: [Scalar; 4] =
          std::array::from_fn(|i| Scalar::from_usize(trial + i) - Scalar::ONE);
        let view = VarValues {
          main: rows(inputs.main),
          preprocessed: rows(inputs.preprocessed),
          stage2: rows(inputs.stage2),
          publics: &publics,
          is_first_row: Scalar::from_usize(trial),
          is_last_row: Scalar::from_usize(trial) - Scalar::ONE,
          is_transition: -Scalar::from_usize(trial),
        };
        let mut native = vec![];
        graph.sweep(&view, &mut native);
        assert_eq!(evaluate_program(&program, &openings, &view), native);
      }
    }
    Ok(())
  }

  #[test]
  fn graph_lowering_rejects_forward_public_column_and_root_references() {
    let inputs = graph_inputs(0);
    for invalid in [1, 2, u32::MAX] {
      for node in [
        Node::Add(NodeId(invalid), NodeId(0)),
        Node::Add(NodeId(0), NodeId(invalid)),
        Node::Sub(NodeId(invalid), NodeId(0)),
        Node::Sub(NodeId(0), NodeId(invalid)),
        Node::Mul(NodeId(invalid), NodeId(0)),
        Node::Mul(NodeId(0), NodeId(invalid)),
        Node::Neg(NodeId(invalid)),
      ] {
        assert!(
          GraphProgram::compile(
            &graph(vec![Node::Const(Scalar::ONE), node]),
            inputs
          )
          .is_err()
        );
      }
    }
    for public in [4, u32::MAX] {
      assert!(
        GraphProgram::compile(&graph(vec![Node::Public(public)]), inputs)
          .is_err()
      );
    }
    for source in [Source::Main, Source::Preprocessed, Source::Stage2] {
      let width = u32::try_from(inputs.matrix(source).width).unwrap();
      for row in [RowOffset::Current, RowOffset::Next] {
        assert!(
          GraphProgram::compile(
            &graph(vec![variable(source, row, width)]),
            inputs
          )
          .is_err()
        );
      }
      let mut current_only = inputs;
      match source {
        Source::Main => current_only.main.rows = 1,
        Source::Preprocessed => current_only.preprocessed.rows = 1,
        Source::Stage2 => current_only.stage2.rows = 1,
      }
      assert!(
        GraphProgram::compile(
          &graph(vec![variable(source, RowOffset::Next, 0)]),
          current_only
        )
        .is_err()
      );
    }
    let mut malformed = graph(vec![Node::Const(Scalar::ONE)]);
    malformed.zeros.push(NodeId(1));
    assert!(GraphProgram::compile(&malformed, inputs).is_err());
    malformed.zeros.clear();
    malformed
      .lookups
      .push(Lookup { multiplicity: NodeId(1), args: vec![NodeId(0)] });
    assert!(GraphProgram::compile(&malformed, inputs).is_err());
    malformed.lookups[0] =
      Lookup { multiplicity: NodeId(0), args: vec![NodeId(1)] };
    assert!(GraphProgram::compile(&malformed, inputs).is_err());
  }

  #[test]
  fn graph_lowering_tracks_only_required_evaluation_inputs() -> Result<()> {
    let inputs = graph_inputs(0);
    for nodes in [vec![], vec![Node::Const(Scalar::ONE)]] {
      let program = GraphProgram::compile(&graph(nodes), inputs)?;
      assert!(!program.uses_proof && !program.uses_view);
    }
    let proof_only = GraphProgram::compile(
      &graph(vec![variable(Source::Main, RowOffset::Current, 0)]),
      inputs,
    )?;
    assert!(proof_only.uses_proof && !proof_only.uses_view);
    for node in
      [Node::Public(0), Node::IsFirstRow, Node::IsLastRow, Node::IsTransition]
    {
      let view_only = GraphProgram::compile(&graph(vec![node]), inputs)?;
      assert!(!view_only.uses_proof && view_only.uses_view);
    }
    Ok(())
  }

  #[test]
  fn filecoin_fixture_export_authenticates_profile_and_rejects_invalid_packets()
  -> Result<()> {
    let root = std::env::temp_dir()
      .join(format!("ix-solidity-export-{}", std::process::id()));
    fs::create_dir(&root)?;
    let data = root.join("data");
    let sol = root.join("GeneratedVerifier.sol");
    write_solidity_fixture(&data, &sol)?;
    let checked_in = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("../../contracts/kzg/testdata");
    for file in [
      "fixture.json",
      "fixture.bin",
      "fixture-bad-pairing.json",
      "fixture-bad-pairing.bin",
      "fixture-other-statement.json",
      "fixture-other-statement.bin",
      "verifier.bin",
    ] {
      assert_eq!(
        fs::read(data.join(file))?,
        fs::read(checked_in.join(file))?,
        "native fixture drift: {file}"
      );
    }
    let generated = fs::read_to_string(&sol)?;
    assert!(generated.contains("Test-only conformance circuit"));
    let checked_source =
      fs::read_to_string(checked_in.join("../src/GeneratedVerifier.sol"))?;
    let normalized_hash = |source: &str| {
      blake3::hash(source.split_whitespace().collect::<String>().as_bytes())
    };
    assert_eq!(
      normalized_hash(&generated),
      normalized_hash(&checked_source),
      "generated Solidity differs from its authenticated fixture profile"
    );
    let fixture: Json =
      serde_json::from_slice(&fs::read(data.join("fixture.json"))?)?;
    assert_eq!(
      fixture["scope"],
      "small-conformance-circuit-not-a-lean-library"
    );
    assert_eq!(fixture["setupClass"], "filecoin");
    assert_eq!(fixture["packetBytes"], 2181);
    assert_eq!(fixture["hintBytes"], 816);
    let other = fs::read(data.join("fixture-other-statement.bin"))?;
    let original = fs::read(data.join("fixture.bin"))?;
    let first_words = statement_words(&original)?;
    let second_words = statement_words(&other)?;
    assert_ne!(first_words, second_words);
    let profile =
      VerifierProfile::from_bytes(&fs::read(data.join("verifier.bin"))?)?;
    profile.verify_with_claim(&original, &first_words)?;
    profile.verify_with_claim(&other, &second_words)?;
    assert!(profile.verify_with_claim(&original, &second_words).is_err());
    assert!(profile.verify_with_claim(&other, &first_words).is_err());
    let digest = fixture["verifierDigestBlake3"].as_str().unwrap();
    let verifier = data.join("verifier.bin");
    let packet = data.join("fixture.bin");
    let exported = root.join("exported");
    let exported_sol = root.join("ExportedVerifier.sol");
    assert!(
      export_solidity_verifier(
        &verifier,
        &packet,
        &"00".repeat(32),
        &exported,
        &exported_sol
      )
      .is_err()
    );
    assert!(!exported.exists());
    export_solidity_verifier(
      &verifier,
      &packet,
      digest,
      &exported,
      &exported_sol,
    )?;
    let result: Json =
      serde_json::from_slice(&fs::read(exported.join("fixture.json"))?)?;
    for key in [
      "packet",
      "yHints",
      "challenges",
      "outerL",
      "outerR",
      "profileId",
      "expectedClaim",
    ] {
      assert_eq!(fixture[key], result[key]);
    }
    assert!(
      export_solidity_verifier(
        &verifier,
        &data.join("fixture-bad-pairing.bin"),
        digest,
        &exported,
        &exported_sol
      )
      .is_err()
    );
    let mut tampered = fs::read(&packet)?;
    *tampered.last_mut().unwrap() ^= 1;
    fs::write(root.join("tampered.bin"), tampered)?;
    assert!(
      export_solidity_verifier(
        &verifier,
        &root.join("tampered.bin"),
        digest,
        &exported,
        &exported_sol
      )
      .is_err()
    );
    fs::remove_dir_all(root)?;
    Ok(())
  }
}
