//! (De)serialization of the verifier's key: `System<AiurConfig>`.
//!
//! The verifier needs each circuit's *compiled* constraint data (the flat,
//! interned node vector, the constraint roots, the compiled lookups, and the
//! widths/degrees), the shared preprocessed commitment, the preprocessed
//! index map, and the commitment + FRI parameters (which seed the config's
//! challenger). The prover-only preprocessed *traces* (the large gadget
//! tables) are reconstructed/committed separately and are NOT serialized.
//!
//! This is a **hand-written, serde-free** codec against the public fields of
//! `System`, `system::Circuit`, `graph::ConstraintGraph`, `Node`, `NodeId`,
//! `ColRef`, `Lookup`, `CommitmentParameters`, `FriParameters`.
//!
//! The recursive verifier hashes every vk byte (digest binding) and parses
//! them in-circuit, so the format optimizes for density: u16 node ids
//! (per-circuit graphs are far below 65k nodes), the Var (source, offset)
//! packed into the tag byte, a small/big constant split, and u16 zeros and
//! lookup references. The logUp constraints are never serialized — they are
//! evaluated directly by both verifiers from the compiled lookups.
//! The in-circuit mirror lives in the formal MultiStark programs
//! (`MultiStark/MultiStark/Modules/SystemDeserialize.lean`); they must stay byte-identical.
//!
//! # Wire format (v6, Fp^3, dense)
//!
//! ```text
//! GLOBAL HEADER
//!   u16 LE       protocol_version = 6  (fail-closed; rejects v5!)
//!   u16 LE       extension_degree = 3  (Fp[X]/(X^3 - X - 1); rejects Fp^2!)
//!   u16 LE       fri_batching = 1      (1 = Tensor; rejects Horner!)
//!   32 bytes     vk_digest             (BLAKE3 derive_key("multi-stark/v6/vk"),
//!                                       recomputed & checked on decode)
//!   7 x u16 LE   commitment + FRI parameters (log_blowup, cap_height,
//!                log_final_poly_len, max_log_arity, num_queries,
//!                commit_proof_of_work_bits, query_proof_of_work_bits)
//!   u16          circuit count
//! PER-CIRCUIT RECORDS (circuit count times; no outer length prefix)
//!   u16 main_width, u16 preprocessed_width, u32 preprocessed_height,
//!   u16 max_constraint_degree (combined user + logUp),
//!   u8 lookup_group_size (k: lookups per chained accumulator step)
//!   u16 node_count, u16 lookup_prefix_len, then node_count nodes, each a u8 tag then payload:
//!     0  ConstSmall: u16 LE canonical value
//!     1  ConstBig:   u64 LE canonical value
//!     2  Public:     u8 index
//!     3 IsFirstRow · 4 IsLastRow · 5 IsTransition (no payload)
//!     6 Add · 7 Sub · 8 Mul: u16 LE, u16 LE child node ids
//!     9  Neg: u16 LE child node id
//!     10..=15  Var (tag = 10 + 2*source + offset; source 0 Preprocessed
//!              1 Main 2 Stage2, offset 0 current 1 next): u16 LE column
//!   u16 zero_count, then zero_count x u16 LE constraint-root node ids
//!   u16 lookup_count, then per lookup:
//!     u16 LE multiplicity node id
//!     u16 LE arg count, then arg_count x u16 LE arg node ids
//! TRAILER
//!   u8           preprocessed commit flag (0 = None / 1 = Some)
//!   [u16 + 32-byte digests]   MerkleCap, if flag = 1
//!   u16 x circuit count       preprocessed indices (0xFFFF = None)
//! ```
//!
//! Per-node `degrees` are NOT serialized: they are derived (Const/Public/
//! IsTransition = 0, Var/IsFirstRow/IsLastRow = 1, Add/Sub = max of children,
//! Mul = checked sum, Neg = child) and recomputed on decode in node order
//! (children precede parents in the compiled vector). Goldilocks constants are
//! written canonically and validated on read (values `>= P` or `<= u16::MAX`
//! encoded with `ConstBig` tag 1 are rejected).
//!
//! Every parameter that affects soundness is in the header, so it is covered
//! by the key's digest, and multi-stark also seeds the transcript with it.
//! [`from_bytes`] rejects a key whose parameters are below the Protocol v6
//! 128-bit security floor ([`security::check`]).

pub mod range;
pub mod security;

use multi_stark::{
  config::{ProofConfig, ProtocolVersion},
  expr::{ColRef, RowOffset, Source},
  graph::{ConstraintGraph, Node, NodeId},
  lookup::Lookup,
  p3_adapter::fri_batching::FriBatching,
  p3_field::{PrimeCharacteristicRing, PrimeField64, TwoAdicField},
  system::{Circuit, System, compute_vk_digest},
  types::{
    Commitment, CommitmentParameters, ExtVal3, FriParameters,
    GoldilocksBlake3V6Config as AiurConfig, Val,
  },
};

/// Wire protocol version required by production Ix (Protocol v6).
pub const PROTOCOL_VERSION: u16 = 6;
/// Wire extension degree required by production Ix (Fp^3 = Fp[X]/(X^3 - X - 1)).
pub const EXTENSION_DEGREE: u16 = 3;
/// Wire FRI batching tag required by production Ix (`FriBatching::Tensor`).
pub const FRI_BATCHING_TENSOR: u16 = 1;

/// Sentinel for `None` in the preprocessed-index trailer.
const NO_PREP_INDEX: u16 = u16::MAX;

// ════════════════════════════════════════════════════════════════════════════
// Encoder — System<AiurConfig> -> bytes
// ════════════════════════════════════════════════════════════════════════════

fn push_u16(buf: &mut Vec<u8>, v: usize) {
  let v = u16::try_from(v).expect("vk header field exceeds u16");
  buf.extend_from_slice(&v.to_le_bytes());
}

fn push_u32(buf: &mut Vec<u8>, v: usize) {
  let v = u32::try_from(v).expect("vk field exceeds u32");
  buf.extend_from_slice(&v.to_le_bytes());
}

/// Node ids on the wire are u16: per-circuit graphs are far below 65k
/// nodes (the whole kernel system is ~140k across 800+ circuits).
fn push_node_id(buf: &mut Vec<u8>, id: NodeId) {
  let id = u16::try_from(id.0).expect("node id exceeds u16 (vk wire format)");
  buf.extend_from_slice(&id.to_le_bytes());
}

fn push_node(buf: &mut Vec<u8>, node: &Node<Val>) {
  match node {
    Node::Const(c) => {
      // Small/big constant split: most constants (selector weights, small
      // literals) fit u16.
      let v = c.as_canonical_u64();
      if let Ok(small) = u16::try_from(v) {
        buf.push(0);
        buf.extend_from_slice(&small.to_le_bytes());
      } else {
        buf.push(1);
        buf.extend_from_slice(&v.to_le_bytes());
      }
    },
    Node::Var(col) => {
      // Var tag packs (source, offset): 10 + 2·source + offset.
      let source = match col.source {
        Source::Preprocessed => 0u8,
        Source::Main => 1,
        Source::Stage2 => 2,
      };
      let offset = match col.offset {
        RowOffset::Current => 0u8,
        RowOffset::Next => 1,
      };
      buf.push(10 + 2 * source + offset);
      let index = u16::try_from(col.index)
        .expect("column index exceeds u16 (vk wire format)");
      buf.extend_from_slice(&index.to_le_bytes());
    },
    Node::Public(i) => {
      buf.push(2);
      buf.push(u8::try_from(*i).expect("public index exceeds u8"));
    },
    Node::IsFirstRow => buf.push(3),
    Node::IsLastRow => buf.push(4),
    Node::IsTransition => buf.push(5),
    Node::Add(a, b) => {
      buf.push(6);
      push_node_id(buf, *a);
      push_node_id(buf, *b);
    },
    Node::Sub(a, b) => {
      buf.push(7);
      push_node_id(buf, *a);
      push_node_id(buf, *b);
    },
    Node::Mul(a, b) => {
      buf.push(8);
      push_node_id(buf, *a);
      push_node_id(buf, *b);
    },
    Node::Neg(a) => {
      buf.push(9);
      push_node_id(buf, *a);
    },
  }
}

/// One circuit record. Nothing derivable is serialized: `constraint_count`
/// (= zeros + ⌈L/k⌉·D), `stage_2_width` (= max(⌈L/k⌉, 1)·D), `num_publics`
/// (= 4·D),
/// and `lookup_prefix_len` (= 1 + max node id reachable from the lookups)
/// are all recomputed on decode, and the Lean reader derives the observed
/// shape limbs the same way.
fn encode_circuit(buf: &mut Vec<u8>, circuit: &Circuit<Val>) {
  let compiled = &circuit.graph;
  push_u16(buf, circuit.main_width);
  push_u16(buf, circuit.preprocessed_width);
  // u32: the Bytes2 table height is exactly 65536.
  push_u32(buf, circuit.preprocessed_height);
  // Combined max degree (user graph + analytic logUp), as observed. Not
  // derivable cheaply in-circuit (it would need a full degree pass).
  push_u16(buf, circuit.max_constraint_degree);
  // The lookup group size is a free per-circuit choice (it changes the
  // constraint structure, not just counts), so it must be serialized.
  buf
    .push(u8::try_from(circuit.lookup_group_size).expect("group size fits u8"));
  push_u16(buf, compiled.nodes.len());
  push_u16(buf, compiled.lookup_prefix_len);
  for node in &compiled.nodes {
    push_node(buf, node);
  }
  push_u16(buf, compiled.zeros.len());
  for &z in &compiled.zeros {
    push_node_id(buf, z);
  }
  push_u16(buf, compiled.lookups.len());
  for lookup in &compiled.lookups {
    push_node_id(buf, lookup.multiplicity);
    push_u16(buf, lookup.args.len());
    for &arg in &lookup.args {
      push_node_id(buf, arg);
    }
  }
}

/// Serialize the verifying key `System<AiurConfig>` (preprocessed traces are
/// skipped — see the module docs). The config's construction parameters are
/// passed alongside because [`AiurConfig`] doesn't expose them back; they are
/// written first so the decoder can rebuild the config.
pub fn to_bytes(
  system: &System<AiurConfig>,
  commitment_parameters: CommitmentParameters,
  fri_parameters: FriParameters,
) -> Vec<u8> {
  assert_eq!(
    system.config.protocol_version(),
    ProtocolVersion::V6,
    "stark-key only encodes Protocol v6 systems"
  );
  assert_eq!(
    system.config.fri_batching(),
    FriBatching::Tensor,
    "stark-key requires FriBatching::Tensor"
  );
  let mut buf = Vec::new();
  push_u16(&mut buf, usize::from(PROTOCOL_VERSION));
  push_u16(&mut buf, usize::from(EXTENSION_DEGREE));
  push_u16(&mut buf, usize::from(FRI_BATCHING_TENSOR));
  buf.extend_from_slice(&system.vk_digest);
  push_u16(&mut buf, commitment_parameters.log_blowup);
  push_u16(&mut buf, commitment_parameters.cap_height);
  push_u16(&mut buf, fri_parameters.log_final_poly_len);
  push_u16(&mut buf, fri_parameters.max_log_arity);
  push_u16(&mut buf, fri_parameters.num_queries);
  push_u16(&mut buf, fri_parameters.commit_proof_of_work_bits);
  push_u16(&mut buf, fri_parameters.query_proof_of_work_bits);
  push_u16(&mut buf, system.circuits.len());
  for circuit in &system.circuits {
    encode_circuit(&mut buf, circuit);
  }
  match &system.preprocessed_commit {
    None => buf.push(0),
    Some(c) => {
      buf.push(1);
      push_u16(&mut buf, c.roots().len());
      for digest in c.roots() {
        buf.extend_from_slice(digest);
      }
    },
  }
  for idx in &system.preprocessed_indices {
    match idx {
      None => buf.extend_from_slice(&NO_PREP_INDEX.to_le_bytes()),
      Some(i) => {
        let v = u16::try_from(*i).expect("preprocessed index exceeds u16");
        assert!(
          v != NO_PREP_INDEX,
          "preprocessed index collides with sentinel"
        );
        buf.extend_from_slice(&v.to_le_bytes());
      },
    }
  }
  buf
}

// ════════════════════════════════════════════════════════════════════════════
// Decoder — bytes -> System<AiurConfig>
// ════════════════════════════════════════════════════════════════════════════

/// Cursor over one byte region.
struct Seg<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> Seg<'a> {
  fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
    let end = self.pos.checked_add(n).ok_or("length overflow")?;
    if end > self.buf.len() {
      return Err(format!("eof: need {n} at offset {}", self.pos));
    }
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }
  fn u8(&mut self) -> Result<u8, String> {
    Ok(self.take(1)?[0])
  }
  fn u16(&mut self) -> Result<u16, String> {
    Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
  }
  fn u32_usize(&mut self) -> Result<usize, String> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize)
  }
  fn node_id(&mut self) -> Result<NodeId, String> {
    Ok(NodeId(u32::from(self.u16()?)))
  }
  fn u64(&mut self) -> Result<u64, String> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
  fn done(&self, what: &str) -> Result<(), String> {
    if self.pos != self.buf.len() {
      return Err(format!(
        "{what}: consumed {} of {} bytes",
        self.pos,
        self.buf.len()
      ));
    }
    Ok(())
  }
}

fn decode_node(seg: &mut Seg<'_>) -> Result<Node<Val>, String> {
  Ok(match seg.u8()? {
    0 => Node::Const(Val::from_u16(seg.u16()?)),
    1 => {
      let raw = seg.u64()?;
      if u16::try_from(raw).is_ok() {
        return Err(format!("non-canonical ConstBig encoding for {raw}"));
      }
      if raw >= Val::ORDER_U64 {
        return Err(format!("non-canonical Goldilocks constant {raw}"));
      }
      Node::Const(Val::from_u64(raw))
    },
    2 => Node::Public(u32::from(seg.u8()?)),
    3 => Node::IsFirstRow,
    4 => Node::IsLastRow,
    5 => Node::IsTransition,
    6 => Node::Add(seg.node_id()?, seg.node_id()?),
    7 => Node::Sub(seg.node_id()?, seg.node_id()?),
    8 => Node::Mul(seg.node_id()?, seg.node_id()?),
    9 => Node::Neg(seg.node_id()?),
    t @ 10..=15 => {
      let v = t - 10;
      let source = match v / 2 {
        0 => Source::Preprocessed,
        1 => Source::Main,
        _ => Source::Stage2,
      };
      let offset =
        if v % 2 == 0 { RowOffset::Current } else { RowOffset::Next };
      let index = u32::from(seg.u16()?);
      Node::Var(ColRef { source, offset, index })
    },
    t => return Err(format!("bad node tag {t}")),
  })
}

/// Recompute per-node degree multiples in node order (children precede parents
/// in the compiled vector).
fn recompute_degrees(nodes: &[Node<Val>]) -> Result<Vec<u32>, String> {
  let mut degrees: Vec<u32> = Vec::with_capacity(nodes.len());
  let get = |degrees: &[u32], id: NodeId| -> Result<u32, String> {
    degrees
      .get(id.0 as usize)
      .copied()
      .ok_or_else(|| format!("node child id {} out of topological order", id.0))
  };
  for node in nodes {
    let d = match *node {
      Node::Const(_) | Node::Public(_) | Node::IsTransition => 0,
      Node::Var(_) | Node::IsFirstRow | Node::IsLastRow => 1,
      Node::Add(a, b) | Node::Sub(a, b) => {
        get(&degrees, a)?.max(get(&degrees, b)?)
      },
      Node::Mul(a, b) => get(&degrees, a)?
        .checked_add(get(&degrees, b)?)
        .ok_or_else(|| "constraint node degree overflow".to_string())?,
      Node::Neg(a) => get(&degrees, a)?,
    };
    degrees.push(d);
  }
  Ok(degrees)
}

fn decode_circuit(seg: &mut Seg<'_>) -> Result<Circuit<Val>, String> {
  let main_width = seg.u16()? as usize;
  let preprocessed_width = seg.u16()? as usize;
  let preprocessed_height = seg.u32_usize()?;
  if preprocessed_height == 0 {
    if preprocessed_width != 0 {
      return Err(format!(
        "nonzero preprocessed_width {preprocessed_width} with zero preprocessed_height"
      ));
    }
  } else if !preprocessed_height.is_power_of_two() {
    return Err(format!(
      "preprocessed_height {preprocessed_height} is not a power of two"
    ));
  }
  let max_constraint_degree = seg.u16()? as usize;
  let lookup_group_size = seg.u8()? as usize;
  if !(1..=multi_stark::lookup::MAX_LOOKUP_GROUP).contains(&lookup_group_size) {
    return Err(format!("bad lookup group size {lookup_group_size}"));
  }
  let node_count = seg.u16()? as usize;
  let lookup_prefix_len = seg.u16()? as usize;
  if lookup_prefix_len > node_count {
    return Err(format!(
      "lookup_prefix_len {lookup_prefix_len} exceeds node_count {node_count}"
    ));
  }
  let mut nodes = Vec::with_capacity(node_count);
  for _ in 0..node_count {
    nodes.push(decode_node(seg)?);
  }
  let zero_count = seg.u16()? as usize;
  let mut zeros = Vec::with_capacity(zero_count);
  for _ in 0..zero_count {
    zeros.push(seg.node_id()?);
  }
  let lookup_count = seg.u16()? as usize;
  let mut lookups = Vec::with_capacity(lookup_count);
  for _ in 0..lookup_count {
    let multiplicity = seg.node_id()?;
    let arg_count = seg.u16()? as usize;
    let mut args = Vec::with_capacity(arg_count.min(1 << 16));
    for _ in 0..arg_count {
      args.push(seg.node_id()?);
    }
    lookups.push(Lookup { multiplicity, args });
  }

  let degrees = recompute_degrees(&nodes)?;
  let check_id = |id: NodeId| -> Result<usize, String> {
    let idx = id.0 as usize;
    if idx < nodes.len() {
      Ok(idx)
    } else {
      Err(format!("node id {} out of bounds ({})", id.0, nodes.len()))
    }
  };
  let ext_degree =
    <ExtVal3 as multi_stark::p3_field::BasedVectorSpace<Val>>::DIMENSION;
  let num_lookups = lookups.len();
  let stage_2_width = multi_stark::lookup::stage2_width(
    num_lookups,
    lookup_group_size,
    ext_degree,
  );
  let num_publics = multi_stark::lookup::num_publics(ext_degree);
  for node in &nodes {
    match *node {
      Node::Public(idx) if idx as usize >= num_publics => {
        return Err(format!(
          "public index {idx} out of bounds ({num_publics})"
        ));
      },
      Node::Var(col) => {
        let width = match col.source {
          Source::Preprocessed => preprocessed_width,
          Source::Main => main_width,
          Source::Stage2 => stage_2_width,
        };
        if col.index as usize >= width {
          return Err(format!(
            "{:?} column index {} out of bounds ({width})",
            col.source, col.index
          ));
        }
      },
      _ => {},
    }
  }
  // The graph's own max degree covers only the user roots (the serialized
  // `max_constraint_degree` is the combined user + analytic-logUp value).
  let mut user_max_degree = 0u32;
  for &z in &zeros {
    user_max_degree = user_max_degree.max(degrees[check_id(z)?]);
  }
  // Verify every lookup root lies within `lookup_prefix_len`.
  let mut min_lookup_prefix_len = 0;
  for l in &lookups {
    for id in std::iter::once(l.multiplicity).chain(l.args.iter().copied()) {
      min_lookup_prefix_len = min_lookup_prefix_len.max(check_id(id)? + 1);
    }
  }
  if lookup_prefix_len < min_lookup_prefix_len {
    return Err(format!(
      "lookup_prefix_len {lookup_prefix_len} smaller than required {min_lookup_prefix_len}"
    ));
  }
  check_compiler_contexts(&nodes, &zeros, lookup_prefix_len)?;
  let mut lookup_degree = 1u64;
  for group in lookups.chunks(lookup_group_size) {
    let mut m_degs = Vec::with_capacity(group.len());
    let mut sum = 0u64;
    for l in group {
      let md = l
        .args
        .iter()
        .map(|n| u64::from(degrees[n.0 as usize]))
        .max()
        .unwrap_or(0);
      sum = sum.checked_add(md).ok_or("lookup degree overflow")?;
      m_degs.push(md);
    }
    let product_term = sum.checked_add(1).ok_or("lookup degree overflow")?;
    lookup_degree = lookup_degree.max(product_term);
    for (l, &md) in group.iter().zip(&m_degs) {
      let mult_term = u64::from(degrees[l.multiplicity.0 as usize])
        .checked_add(sum - md)
        .ok_or("lookup degree overflow")?;
      lookup_degree = lookup_degree.max(mult_term);
    }
  }
  let expected_max_degree = u64::from(user_max_degree).max(lookup_degree);
  if expected_max_degree != max_constraint_degree as u64 {
    return Err(format!(
      "max_constraint_degree {max_constraint_degree} does not match derived {expected_max_degree}"
    ));
  }
  let graph = ConstraintGraph {
    nodes,
    degrees,
    zeros,
    lookups,
    lookup_prefix_len,
    max_constraint_degree: user_max_degree,
  };
  Ok(Circuit {
    graph,
    main_width,
    preprocessed: None,
    preprocessed_width,
    preprocessed_height,
    num_lookups,
    stage_2_width,
    num_publics,
    lookup_group_size,
    constraint_count: zeros_plus_logup(
      zero_count,
      num_lookups,
      lookup_group_size,
      ext_degree,
    ),
    max_constraint_degree,
  })
}

/// Reject graphs multi-stark's compiler cannot produce for an Aiur key:
/// - lookup expressions are compiled in a context that reads the preprocessed
///   and main traces only (`multi_stark::graph`, `Context::Lookup`): a public
///   value, a row selector or a stage-2 column there is a compile error. Every
///   node a lookup reaches lies in the prefix (lookup roots are inside it,
///   checked by the caller, and children precede parents), and the compiler
///   interns nothing else there, so the whole prefix is checked;
/// - a base constraint that reads stage 2 is a compile error
///   (`Stage2InBaseContext`), and Aiur keys carry no extension constraints,
///   so no constraint root may reach a stage-2 column.
fn check_compiler_contexts(
  nodes: &[Node<Val>],
  zeros: &[NodeId],
  lookup_prefix_len: usize,
) -> Result<(), String> {
  for (id, node) in nodes[..lookup_prefix_len].iter().enumerate() {
    let forbidden = match node {
      Node::Public(_) => Some("a public value"),
      Node::IsFirstRow | Node::IsLastRow | Node::IsTransition => {
        Some("a row selector")
      },
      Node::Var(col) if col.source == Source::Stage2 => {
        Some("a stage-2 column")
      },
      _ => None,
    };
    if let Some(what) = forbidden {
      return Err(format!(
        "lookup prefix node {id} reads {what}, which a lookup may not read"
      ));
    }
  }
  // Mark the nodes reachable from a constraint root; children precede parents
  // (checked by `recompute_degrees`), so one descending sweep suffices.
  let mut reached = vec![false; nodes.len()];
  for z in zeros {
    reached[z.0 as usize] = true;
  }
  for id in (0..nodes.len()).rev() {
    if !reached[id] {
      continue;
    }
    match nodes[id] {
      Node::Var(col) if col.source == Source::Stage2 => {
        return Err(format!(
          "constraint node {id} reads stage-2 column {}, which an Aiur constraint may not read",
          col.index
        ));
      },
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        reached[a.0 as usize] = true;
        reached[b.0 as usize] = true;
      },
      Node::Neg(a) => reached[a.0 as usize] = true,
      _ => {},
    }
  }
  Ok(())
}

/// The folded constraint count: user roots + the directly-evaluated logUp
/// values (mirrors `multi_stark::lookup::logup_constraint_count`).
fn zeros_plus_logup(
  zero_count: usize,
  num_lookups: usize,
  group_size: usize,
  d: usize,
) -> usize {
  zero_count
    + multi_stark::lookup::logup_constraint_count(num_lookups, group_size, d)
}

/// A decoded key: the system and its config's construction parameters, which
/// the `System` itself doesn't expose.
pub type Decoded = (System<AiurConfig>, CommitmentParameters, FriParameters);

/// Deserialize a `System<AiurConfig>` from [`to_bytes`] output, requiring that
/// every byte is consumed and that the parameters meet the security floor
/// ([`security::check`]).
pub fn from_bytes(bytes: &[u8]) -> Result<Decoded, String> {
  decode(bytes, true)
}

/// [`from_bytes`] without the security floor, for tests whose toy keys keep
/// recursive circuits small. A verifier must never trust a key decoded this way.
#[doc(hidden)]
pub fn from_bytes_below_floor(bytes: &[u8]) -> Result<Decoded, String> {
  decode(bytes, false)
}

fn decode(bytes: &[u8], floor: bool) -> Result<Decoded, String> {
  let mut r = Seg { buf: bytes, pos: 0 };
  let protocol_version = r.u16()?;
  if protocol_version != PROTOCOL_VERSION {
    return Err(format!(
      "unsupported protocol_version {protocol_version}: Protocol v{PROTOCOL_VERSION} (Fp^3) required"
    ));
  }
  let extension_degree = r.u16()?;
  if extension_degree != EXTENSION_DEGREE {
    return Err(format!(
      "unsupported extension_degree {extension_degree}: Fp^{EXTENSION_DEGREE} required"
    ));
  }
  let fri_batching = r.u16()?;
  if fri_batching != FRI_BATCHING_TENSOR {
    return Err(format!(
      "unsupported fri_batching {fri_batching}: Tensor ({FRI_BATCHING_TENSOR}) required"
    ));
  }
  let mut vk_digest = [0u8; 32];
  vk_digest.copy_from_slice(r.take(32)?);
  let commitment_parameters = CommitmentParameters {
    log_blowup: r.u16()? as usize,
    cap_height: r.u16()? as usize,
  };
  let fri_parameters = FriParameters {
    log_final_poly_len: r.u16()? as usize,
    max_log_arity: r.u16()? as usize,
    num_queries: r.u16()? as usize,
    commit_proof_of_work_bits: r.u16()? as usize,
    query_proof_of_work_bits: r.u16()? as usize,
  };
  if floor {
    security::check(&commitment_parameters, &fri_parameters)?;
  } else {
    // The waiver lifts the security floor only. Proof-of-work counts above
    // the cap would abort the verifier's grinding check (`sample_bits`), and
    // `log_blowup` outside `1..=Val::TWO_ADICITY` would underflow
    // `Val::TWO_ADICITY - log_blowup` or overflow `1 << log_blowup`, so both
    // are refused here too.
    if commitment_parameters.log_blowup == 0
      || commitment_parameters.log_blowup > Val::TWO_ADICITY
    {
      return Err(format!(
        "log_blowup {} is outside 1..={}",
        commitment_parameters.log_blowup,
        Val::TWO_ADICITY
      ));
    }
    for (phase, bits) in [
      ("commit", fri_parameters.commit_proof_of_work_bits),
      ("query", fri_parameters.query_proof_of_work_bits),
    ] {
      if bits > security::MAX_PROOF_OF_WORK_BITS {
        return Err(format!(
          "{phase} proof of work of {bits} bits exceeds {}",
          security::MAX_PROOF_OF_WORK_BITS
        ));
      }
    }
  }
  let n_circuits = r.u16()? as usize;
  let mut circuits = Vec::with_capacity(n_circuits);
  for _ in 0..n_circuits {
    circuits.push(decode_circuit(&mut r)?);
  }
  let computed_vk_digest = compute_vk_digest::<Val, ExtVal3>(&circuits);
  if vk_digest != computed_vk_digest {
    return Err(
      "vk_digest mismatch: serialized header digest does not match decoded circuits"
        .into(),
    );
  }
  let preprocessed_commit = match r.u8()? {
    0 => None,
    1 => {
      let n = r.u16()? as usize;
      let mut caps = Vec::with_capacity(n.min(1 << 16));
      for _ in 0..n {
        let mut d = [0u8; 32];
        d.copy_from_slice(r.take(32)?);
        caps.push(d);
      }
      // `Commitment::from` asserts a power-of-two root count; check it first
      // so a malformed key is an error, not an abort. The exact count is
      // checked against the parameters and heights below.
      if !n.is_power_of_two() {
        return Err(format!(
          "preprocessed commitment has {n} roots, not a power of two"
        ));
      }
      Some(Commitment::from(caps))
    },
    t => return Err(format!("bad Option tag {t}")),
  };
  // A circuit's preprocessed matrix is the `k`-th committed one, `k` its rank
  // among the circuits that have one: the in-circuit verifier reads it by slot,
  // multi-stark by rank, and the two agree only on keys in that form.
  let mut preprocessed_indices = Vec::with_capacity(n_circuits);
  let mut ranked = 0usize;
  for (ci, circuit) in circuits.iter().enumerate() {
    let v = r.u16()?;
    let has_prep = circuit.preprocessed_height > 0;
    preprocessed_indices.push(if v == NO_PREP_INDEX {
      if has_prep {
        return Err(format!(
          "circuit {ci} has preprocessed_height {} but no preprocessed index",
          circuit.preprocessed_height
        ));
      }
      None
    } else {
      if !has_prep {
        return Err(format!(
          "circuit {ci} has preprocessed index {v} but zero preprocessed_height"
        ));
      }
      if v as usize != ranked {
        return Err(format!(
          "preprocessed index {v} is not the circuit's rank {ranked}"
        ));
      }
      ranked += 1;
      Some(v as usize)
    });
  }
  match (&preprocessed_commit, ranked > 0) {
    (Some(commit), true) => {
      let max_prep_log = circuits
        .iter()
        .filter(|c| c.preprocessed_height > 0)
        .map(|c| c.preprocessed_height.ilog2() as usize)
        .max()
        .unwrap_or(0);
      let max_prep_lde_log = max_prep_log
        .checked_add(commitment_parameters.log_blowup)
        .ok_or("preprocessed LDE log height overflow")?;
      let shift =
        u32::try_from(commitment_parameters.cap_height.min(max_prep_lde_log))
          .map_err(|_overflow| "preprocessed cap root count overflow")?;
      let expected_roots = 1usize
        .checked_shl(shift)
        .ok_or("preprocessed cap root count overflow")?;
      if commit.roots().len() != expected_roots {
        return Err(format!(
          "preprocessed commitment has {} roots, expected {expected_roots}",
          commit.roots().len()
        ));
      }
    },
    (None, false) => {},
    (Some(_), false) => {
      return Err(
        "preprocessed commitment present with no preprocessed circuits".into(),
      );
    },
    (None, true) => {
      return Err(format!(
        "missing preprocessed commitment for {ranked} preprocessed circuits"
      ));
    },
  }
  r.done("vk")?;
  let system = System {
    config: AiurConfig::new(commitment_parameters, fri_parameters),
    circuits,
    preprocessed_commit,
    preprocessed_indices,
    vk_digest,
  };
  Ok((system, commitment_parameters, fri_parameters))
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    expr::Expr, p3_matrix::dense::RowMajorMatrix, system::CircuitInputs,
  };

  /// Protocol v6 default 128-bit parameters (`2, 128, 0, 20`).
  fn floor_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 2, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 128,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    };
    (cp, fp)
  }

  /// Two circuits: a constrained one with a lookup, and a preprocessed table
  /// with a grouped lookup, so the record and trailer paths are covered.
  fn test_system(
    cp: CommitmentParameters,
    fp: FriParameters,
  ) -> System<AiurConfig> {
    let x = Expr::main(0);
    let y = Expr::main(1);
    let one = Expr::constant(Val::ONE);
    let inputs = vec![
      CircuitInputs {
        main_width: 2,
        constraints: vec![x.clone() * x.clone() - y.clone()],
        lookups: vec![Lookup::pull(one.clone(), vec![one.clone(), x, y])],
        ..Default::default()
      },
      CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(
          (0..4).map(Val::from_u32).collect(),
        )),
        lookups: vec![
          Lookup::push(Expr::main(0), vec![one.clone(), Expr::preprocessed(0)]),
          Lookup::push(Expr::main(0), vec![one, Expr::preprocessed(0)]),
        ],
        lookup_group_size: 2,
        ..Default::default()
      },
    ];
    System::new(AiurConfig::new(cp, fp), inputs).0
  }

  fn encoded() -> Vec<u8> {
    let (cp, fp) = floor_parameters();
    to_bytes(&test_system(cp, fp), cp, fp)
  }

  #[test]
  fn round_trips() {
    let bytes = encoded();
    let (system, cp, fp) = from_bytes(&bytes).expect("decode");
    assert_eq!(to_bytes(&system, cp, fp), bytes);
    let fresh = test_system(cp, fp);
    assert_eq!(fresh.circuits.len(), system.circuits.len());
    for (a, b) in fresh.circuits.iter().zip(&system.circuits) {
      assert_eq!(a.graph.nodes, b.graph.nodes);
      assert_eq!(a.graph.zeros, b.graph.zeros);
      assert_eq!(a.main_width, b.main_width);
      assert_eq!(a.preprocessed_width, b.preprocessed_width);
      assert_eq!(a.preprocessed_height, b.preprocessed_height);
      assert_eq!(a.lookup_group_size, b.lookup_group_size);
      assert_eq!(a.stage_2_width, b.stage_2_width);
      assert_eq!(a.num_publics, b.num_publics);
      assert_eq!(a.constraint_count, b.constraint_count);
    }
  }

  /// A preprocessed index must be the circuit's rank among the circuits that
  /// have one: the in-circuit verifier reads by slot, multi-stark by rank.
  #[test]
  fn rejects_non_canonical_preprocessed_indices() {
    let (cp, fp) = floor_parameters();
    let mut system = test_system(cp, fp);
    let k = system
      .preprocessed_indices
      .iter()
      .position(Option::is_some)
      .expect("a circuit with a preprocessed matrix");
    system.preprocessed_indices[k] = Some(1);
    let err = from_bytes(&to_bytes(&system, cp, fp))
      .err()
      .expect("accepted a preprocessed index other than its rank");
    assert!(err.contains("rank"), "{err}");
  }

  #[test]
  fn rejects_trailing_bytes() {
    let mut bytes = encoded();
    bytes.push(0);
    assert!(from_bytes(&bytes).is_err(), "accepted trailing data");
    assert!(from_bytes_below_floor(&bytes).is_err());
  }

  /// Records carry no length prefix, so full consumption and read bounds are
  /// the malformation guards: every truncation must be rejected.
  #[test]
  fn rejects_truncation() {
    let bytes = encoded();
    for len in 0..bytes.len() {
      assert!(from_bytes(&bytes[..len]).is_err(), "accepted {len} bytes");
    }
  }

  /// Offset of the 7 u16 LE commitment/FRI parameters (after 6-byte protocol
  /// header + 32-byte vk_digest).
  const PARAM_HEADER_OFFSET: usize = 38;

  /// The parameter header fields are u16 LE starting at `PARAM_HEADER_OFFSET`.
  fn with_header(field: usize, value: u16) -> Vec<u8> {
    let mut bytes = encoded();
    let off = PARAM_HEADER_OFFSET + 2 * field;
    bytes[off..off + 2].copy_from_slice(&value.to_le_bytes());
    bytes
  }

  #[test]
  fn rejects_v5_fp2_horner_and_forged_vk_digest() {
    // Reject protocol_version != 6 (including legacy v5 keys starting with log_blowup 1..4).
    for v in [0u16, 1, 2, 3, 4, 5, 7] {
      let mut bytes = encoded();
      bytes[0..2].copy_from_slice(&v.to_le_bytes());
      let err =
        from_bytes(&bytes).err().expect("accepted wrong protocol_version");
      assert!(err.contains("protocol_version"), "{err}");
      assert!(from_bytes_below_floor(&bytes).is_err());
    }
    // Reject extension_degree != 3 (no Fp^2 downgrade!).
    for d in [1u16, 2, 4] {
      let mut bytes = encoded();
      bytes[2..4].copy_from_slice(&d.to_le_bytes());
      let err =
        from_bytes(&bytes).err().expect("accepted wrong extension_degree");
      assert!(err.contains("extension_degree"), "{err}");
      assert!(from_bytes_below_floor(&bytes).is_err());
    }
    // Reject fri_batching != 1 (no Horner downgrade!).
    for b in [0u16, 2] {
      let mut bytes = encoded();
      bytes[4..6].copy_from_slice(&b.to_le_bytes());
      let err = from_bytes(&bytes).err().expect("accepted wrong fri_batching");
      assert!(err.contains("fri_batching"), "{err}");
      assert!(from_bytes_below_floor(&bytes).is_err());
    }
    // Reject tampered vk_digest.
    let mut bytes = encoded();
    bytes[6] ^= 1;
    let err = from_bytes(&bytes).err().expect("accepted tampered vk_digest");
    assert!(err.contains("vk_digest"), "{err}");
    assert!(from_bytes_below_floor(&bytes).is_err());
  }

  #[test]
  fn rejects_keys_below_the_security_floor() {
    // (field, value): log_blowup 0, log_blowup 1 (with 128 queries -> 78b Johnson),
    // 100 queries (retired v5 default, 115.5b Johnson < 128b), 113 queries (127.9b Johnson),
    // 5 query PoW bits with 128 queries (127.2b Johnson < 128b), and 33 commit PoW bits.
    for (field, value) in [(0, 0), (0, 1), (4, 100), (4, 113), (6, 5), (5, 33)]
    {
      let bytes = with_header(field, value);
      let error = from_bytes(&bytes).err().expect("accepted a weak key");
      assert!(
        error.contains("floor")
          || error.contains("outside")
          || error.contains("exceeds"),
        "{error}"
      );
      // The waiver decodes the same bytes, for tests only, except proof of
      // work above the cap and invalid log_blowup, which it refuses too.
      if (field, value) == (5, 33) || (field, value) == (0, 0) {
        assert!(from_bytes_below_floor(&bytes).is_err());
      } else {
        from_bytes_below_floor(&bytes).unwrap();
      }
    }
    // Stronger parameters than the floor decode.
    from_bytes(&with_header(4, 130)).unwrap();
    from_bytes(&with_header(5, 16)).unwrap();
  }

  #[test]
  fn rejects_out_of_bounds_node_ids() {
    let (cp, fp) = floor_parameters();
    let mut system = test_system(cp, fp);
    let bad_id =
      NodeId(u32::try_from(system.circuits[0].graph.nodes.len()).unwrap() + 5);
    system.circuits[0].graph.zeros[0] = bad_id;
    let bytes = to_bytes(&system, cp, fp);
    let err = from_bytes(&bytes).err().expect("accepted out-of-bounds zero id");
    assert!(err.contains("out of bounds"), "{err}");

    let mut system = test_system(cp, fp);
    system.circuits[0].graph.nodes[0] = Node::Neg(NodeId(0));
    let bytes = to_bytes(&system, cp, fp);
    let err =
      from_bytes(&bytes).err().expect("accepted non-topological child id");
    assert!(err.contains("out of topological order"), "{err}");
  }

  /// Build raw wire bytes for a minimal 1-circuit verifying key with caller-chosen
  /// node records (after the global header and circuit metadata).
  fn raw_single_circuit_vk(
    main_width: u16,
    max_constraint_degree: u16,
    nodes_raw: &[(u8, &[u8])],
    zeros: &[u16],
  ) -> Vec<u8> {
    let (cp, fp) = floor_parameters();
    let mut buf = Vec::new();
    push_u16(&mut buf, usize::from(PROTOCOL_VERSION));
    push_u16(&mut buf, usize::from(EXTENSION_DEGREE));
    push_u16(&mut buf, usize::from(FRI_BATCHING_TENSOR));
    let digest_offset = buf.len();
    buf.extend_from_slice(&[0u8; 32]);
    for v in [
      cp.log_blowup,
      cp.cap_height,
      fp.log_final_poly_len,
      fp.max_log_arity,
      fp.num_queries,
      fp.commit_proof_of_work_bits,
      fp.query_proof_of_work_bits,
      1usize, // n_circuits
    ] {
      push_u16(&mut buf, v);
    }
    let circuit_offset = buf.len();
    push_u16(&mut buf, main_width as usize);
    push_u16(&mut buf, 0); // preprocessed_width
    push_u32(&mut buf, 0); // preprocessed_height
    push_u16(&mut buf, max_constraint_degree as usize);
    buf.push(1); // lookup_group_size
    push_u16(&mut buf, nodes_raw.len());
    push_u16(&mut buf, 0); // lookup_prefix_len
    for &(tag, payload) in nodes_raw {
      buf.push(tag);
      buf.extend_from_slice(payload);
    }
    push_u16(&mut buf, zeros.len());
    for &z in zeros {
      push_u16(&mut buf, z as usize);
    }
    push_u16(&mut buf, 0); // lookup_count
    // If the circuit decodes cleanly, populate its real canonical vk_digest so
    // valid-circuit boundary tests pass the vk_digest check.
    let mut probe = Seg { buf: &buf[circuit_offset..], pos: 0 };
    if let Ok(circ) = decode_circuit(&mut probe) {
      let digest = compute_vk_digest::<Val, ExtVal3>(&[circ]);
      buf[digest_offset..digest_offset + 32].copy_from_slice(&digest);
    }
    buf.push(0); // preprocessed_commit = None
    buf.extend_from_slice(&NO_PREP_INDEX.to_le_bytes());
    buf
  }

  #[test]
  fn rejects_degree_overflow_in_mul_dag() {
    // 1 variable (degree 1) followed by 32 squarings reaches degree 2^32,
    // which must fail with overflow rather than wrapping/panicking.
    let mut payloads: Vec<[u8; 4]> = Vec::new();
    let var_payload = 0u16.to_le_bytes();
    for i in 0..32u16 {
      let mut p = [0u8; 4];
      p[..2].copy_from_slice(&i.to_le_bytes());
      p[2..].copy_from_slice(&i.to_le_bytes());
      payloads.push(p);
    }
    let mut nodes_raw: Vec<(u8, &[u8])> = vec![(12, &var_payload)]; // Var(Main, Current, 0)
    for p in &payloads {
      nodes_raw.push((8, p.as_slice())); // Mul(i, i)
    }
    let bytes = raw_single_circuit_vk(1, 1, &nodes_raw, &[32]);
    let err = from_bytes(&bytes).err().expect("accepted degree-overflow DAG");
    assert!(err.contains("overflow"), "{err}");
    let err = from_bytes_below_floor(&bytes)
      .err()
      .expect("below_floor accepted degree-overflow DAG");
    assert!(err.contains("overflow"), "{err}");
  }

  #[test]
  fn rejects_non_canonical_constants() {
    // Tag 1 (ConstBig) must strictly encode values in (u16::MAX, Val::ORDER_U64).
    for bad in [
      0u64,
      1,
      u64::from(u16::MAX),
      Val::ORDER_U64,
      Val::ORDER_U64 + 1,
      u64::MAX,
    ] {
      let payload = bad.to_le_bytes();
      let bytes = raw_single_circuit_vk(1, 1, &[(1, &payload)], &[]);
      let err = from_bytes(&bytes)
        .err()
        .unwrap_or_else(|| panic!("accepted non-canonical ConstBig {bad}"));
      assert!(err.contains("non-canonical"), "{bad}: {err}");
      assert!(from_bytes_below_floor(&bytes).is_err());
    }
    // Canonical ConstBig boundary values decode and round-trip identically.
    for good in [u64::from(u16::MAX) + 1, Val::ORDER_U64 - 1] {
      let payload = good.to_le_bytes();
      let bytes = raw_single_circuit_vk(1, 1, &[(1, &payload)], &[]);
      let (sys, cp, fp) = from_bytes(&bytes)
        .unwrap_or_else(|e| panic!("rejected canonical ConstBig {good}: {e}"));
      assert_eq!(to_bytes(&sys, cp, fp), bytes);
    }
  }

  #[test]
  fn rejects_invalid_var_public_degree_and_preprocessed_metadata() {
    // Out-of-bounds Main var (index 1 with main_width 1).
    let idx1 = 1u16.to_le_bytes();
    let bytes = raw_single_circuit_vk(1, 1, &[(12, &idx1)], &[]);
    let err = from_bytes(&bytes).err().expect("accepted OOB Main var");
    assert!(err.contains("out of bounds"), "{err}");

    // Out-of-bounds Preprocessed var (index 0 with preprocessed_width 0).
    let idx0 = 0u16.to_le_bytes();
    let bytes = raw_single_circuit_vk(1, 1, &[(10, &idx0)], &[]);
    let err = from_bytes(&bytes).err().expect("accepted OOB Preprocessed var");
    assert!(err.contains("out of bounds"), "{err}");

    // Out-of-bounds Stage2 var (stage_2_width = 3 for 0 lookups, ext_degree 3).
    let idx3 = 3u16.to_le_bytes();
    let bytes = raw_single_circuit_vk(1, 1, &[(14, &idx3)], &[]);
    let err = from_bytes(&bytes).err().expect("accepted OOB Stage2 var");
    assert!(err.contains("out of bounds"), "{err}");

    // Out-of-bounds Public (num_publics = 12 for ext_degree 3).
    let pub12 = [12u8];
    let bytes = raw_single_circuit_vk(1, 1, &[(2, &pub12)], &[]);
    let err = from_bytes(&bytes).err().expect("accepted OOB Public");
    assert!(err.contains("out of bounds"), "{err}");

    // Mismatched max_constraint_degree (claims 2 when derived is 1).
    let bytes = raw_single_circuit_vk(1, 2, &[(12, &idx0)], &[0]);
    let err =
      from_bytes(&bytes).err().expect("accepted wrong max_constraint_degree");
    assert!(err.contains("max_constraint_degree"), "{err}");

    // Preprocessed commitment mismatches ranked > 0 or has extra cap roots.
    let (cp, fp) = floor_parameters();
    let mut system = test_system(cp, fp);
    system.preprocessed_commit = None;
    let err = from_bytes(&to_bytes(&system, cp, fp))
      .err()
      .expect("accepted missing preprocessed commit");
    assert!(err.contains("missing preprocessed commitment"), "{err}");

    let mut system = test_system(cp, fp);
    let root = system.preprocessed_commit.as_ref().unwrap().roots()[0];
    system.preprocessed_commit = Some(Commitment::from(vec![root, root]));
    let err = from_bytes(&to_bytes(&system, cp, fp))
      .err()
      .expect("accepted extra preprocessed cap roots");
    assert!(err.contains("roots"), "{err}");

    let mut system = test_system(cp, fp);
    system.preprocessed_indices[1] = None;
    let err = from_bytes(&to_bytes(&system, cp, fp))
      .err()
      .expect("accepted missing preprocessed index for preprocessed circuit");
    assert!(err.contains("preprocessed_height"), "{err}");
  }

  /// A preprocessed-commitment root count that is not a power of two (0, or
  /// 2^32 truncated to 0, or 3) used to reach `MerkleCap`'s assertion and
  /// abort; it must be an error, through
  /// both decoders.
  #[test]
  fn rejects_malformed_preprocessed_root_count_without_panicking() {
    let bytes = encoded();
    // Trailer: flag (1) + root count (2) + one 32-byte root + two u16 indices.
    let trailer = bytes.len() - (1 + 2 + 32 + 2 * 2);
    assert_eq!(bytes[trailer], 1, "preprocessed commit flag");
    let root = &bytes[trailer + 3..trailer + 35];
    let indices = &bytes[trailer + 35..];
    for n in [0u16, 3, 5] {
      let mut bad = bytes[..=trailer].to_vec();
      bad.extend_from_slice(&n.to_le_bytes());
      for _ in 0..n {
        bad.extend_from_slice(root);
      }
      bad.extend_from_slice(indices);
      let err =
        from_bytes(&bad).err().expect("accepted a malformed root count");
      assert!(err.contains("roots"), "{n}: {err}");
      let err = from_bytes_below_floor(&bad)
        .err()
        .expect("below_floor accepted a malformed root count");
      assert!(err.contains("roots"), "{n}: {err}");
    }
    // A power-of-two count other than the expected one is still refused.
    let mut bad = bytes[..=trailer].to_vec();
    bad.extend_from_slice(&2u16.to_le_bytes());
    bad.extend_from_slice(root);
    bad.extend_from_slice(root);
    bad.extend_from_slice(indices);
    let err = from_bytes(&bad).err().expect("accepted 2 roots for cap 0");
    assert!(err.contains("roots"), "{err}");
  }

  /// The below-floor decoder still refuses proof-of-work counts above
  /// the cap, which would abort the verifier's grinding check.
  #[test]
  fn below_floor_refuses_excessive_proof_of_work() {
    for (field, value) in [(5, 33u16), (6, 33), (5, u16::MAX), (6, 64)] {
      let bytes = with_header(field, value);
      let err = from_bytes_below_floor(&bytes)
        .err()
        .unwrap_or_else(|| panic!("accepted field {field} = {value}"));
      assert!(err.contains("exceeds"), "{err}");
      assert!(from_bytes(&bytes).is_err());
    }
  }

  /// The below-floor decoder bounds `log_blowup` to `1..=Val::TWO_ADICITY`
  /// so `Val::TWO_ADICITY - log_blowup` and `1 << log_blowup` cannot panic.
  #[test]
  fn below_floor_refuses_invalid_log_blowup() {
    for bad in [0u16, 33, 64, u16::MAX] {
      let bytes = with_header(0, bad);
      let err = from_bytes_below_floor(&bytes)
        .err()
        .unwrap_or_else(|| panic!("accepted log_blowup = {bad}"));
      assert!(err.contains("log_blowup"), "{bad}: {err}");
      assert!(from_bytes(&bytes).is_err());
    }
    for good in [1u16, 32] {
      let bytes = with_header(0, good);
      let (_, cp, _) = from_bytes_below_floor(&bytes)
        .unwrap_or_else(|e| panic!("rejected log_blowup = {good}: {e}"));
      assert_eq!(cp.log_blowup, usize::from(good));
    }
  }

  /// Lookup expressions may read only the preprocessed and main traces
  /// (multi-stark's `Context::Lookup`); constraint roots may not reach stage 2.
  #[test]
  fn rejects_graphs_the_compiler_forbids() {
    let (cp, fp) = floor_parameters();
    let base = test_system(cp, fp);
    let prefix_var = base.circuits[0].graph.nodes
      [..base.circuits[0].graph.lookup_prefix_len]
      .iter()
      .position(|n| matches!(n, Node::Var(c) if c.source == Source::Main))
      .expect("a main-trace variable in circuit 0's lookup prefix");
    let stage2 = Node::Var(ColRef {
      source: Source::Stage2,
      offset: RowOffset::Current,
      index: 0,
    });
    for replacement in [
      Node::Public(0),
      Node::IsFirstRow,
      Node::IsLastRow,
      Node::IsTransition,
      stage2,
    ] {
      let mut system = test_system(cp, fp);
      system.circuits[0].graph.nodes[prefix_var] = replacement;
      // A self-consistent key: its digest covers the changed graph.
      system.vk_digest = compute_vk_digest::<Val, ExtVal3>(&system.circuits);
      let err = from_bytes(&to_bytes(&system, cp, fp))
        .err()
        .unwrap_or_else(|| panic!("accepted {replacement:?} in a lookup"));
      assert!(err.contains("lookup prefix"), "{replacement:?}: {err}");
    }
    // A constraint root reading a stage-2 column.
    let idx0 = 0u16.to_le_bytes();
    let bytes = raw_single_circuit_vk(1, 1, &[(14, &idx0)], &[0]);
    let err =
      from_bytes(&bytes).err().expect("accepted stage 2 in a constraint");
    assert!(err.contains("stage-2"), "{err}");
    assert!(from_bytes_below_floor(&bytes).is_err());
    // Stage 2 reached through an operation, two levels down.
    let mul = [0u8, 0, 0, 0]; // Mul(0, 0)
    let neg = [1u8, 0]; // Neg(1)
    let bytes =
      raw_single_circuit_vk(1, 2, &[(14, &idx0), (8, &mul), (9, &neg)], &[2]);
    let err = from_bytes(&bytes).err().expect("accepted reachable stage 2");
    assert!(err.contains("stage-2"), "{err}");
    // An honest key, and selectors and publics in constraints, still decode.
    from_bytes(&encoded()).unwrap();
    let bytes = raw_single_circuit_vk(
      1,
      2,
      &[(12, &idx0), (3, &[]), (8, &[0, 0, 1, 0])],
      &[2],
    );
    from_bytes(&bytes).unwrap();
  }

  #[test]
  fn rejects_unsupported_structural_header_parameters() {
    // Field 1: cap_height != 0; field 2: log_final_poly_len != 0;
    // field 3: max_log_arity != 1.
    for (field, value, needle) in [
      (1, 1, "cap_height"),
      (1, u16::MAX, "cap_height"),
      (2, 1, "log_final_poly_len"),
      (2, u16::MAX, "log_final_poly_len"),
      (3, 0, "max_log_arity"),
      (3, 2, "max_log_arity"),
    ] {
      let bytes = with_header(field, value);
      let err = from_bytes(&bytes)
        .err()
        .unwrap_or_else(|| panic!("accepted field {field} = {value}"));
      assert!(err.contains(needle), "{err}");
    }
  }

  #[test]
  fn below_floor_validates_nonzero_cap_height_against_preprocessed_lde_height()
  {
    // Preprocessed trace height 2 (log 1) with log_blowup 2 has LDE height 8
    // (log 3), so cap_height 2 (> max_prep_log = 1) commits 4 roots and
    // cap_height 3 commits 8 roots.
    for (cap_height, expected_roots) in [(2usize, 4usize), (3, 8)] {
      let cp = CommitmentParameters { log_blowup: 2, cap_height };
      let (_, fp) = floor_parameters();
      let (mut system, _) = System::new(
        AiurConfig::new(cp, fp),
        [CircuitInputs {
          main_width: 1,
          preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; 2])),
          ..Default::default()
        }],
      );
      assert_eq!(
        system.preprocessed_commit.as_ref().unwrap().roots().len(),
        expected_roots
      );
      let bytes = to_bytes(&system, cp, fp);
      assert!(from_bytes(&bytes).is_err());
      let (decoded, dcp, dfp) =
        from_bytes_below_floor(&bytes).expect("below_floor rejected valid cap");
      assert_eq!(to_bytes(&decoded, dcp, dfp), bytes);

      // Truncating to 2 roots (the unblown height cap) must be rejected.
      let root = system.preprocessed_commit.as_ref().unwrap().roots()[0];
      system.preprocessed_commit = Some(Commitment::from(vec![root; 2]));
      let err = from_bytes_below_floor(&to_bytes(&system, cp, fp))
        .err()
        .expect("accepted wrong preprocessed cap root count");
      assert!(err.contains("roots"), "{err}");
    }
  }
}
