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
//! # Wire format (v5, dense)
//!
//! ```text
//! GLOBAL HEADER
//!   7 x u16 LE   commitment + FRI parameters (log_blowup, cap_height,
//!                log_final_poly_len, max_log_arity, num_queries,
//!                commit_proof_of_work_bits, query_proof_of_work_bits)
//!   u16          circuit count
//! PER-CIRCUIT RECORDS (circuit count times; no outer length prefix)
//!   u16 main_width, u16 preprocessed_width, u32 preprocessed_height,
//!   u16 max_constraint_degree (combined user + logUp),
//!   u8 lookup_group_size (k: lookups per chained accumulator step)
//!   u16 node_count, then node_count nodes, each a u8 tag then payload:
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
//! Mul = sum, Neg = child) and recomputed on decode in node order (children
//! precede parents in the compiled vector). Goldilocks constants are written
//! canonically and reduced on read.
//!
//! Every parameter that affects soundness is in the header, so it is covered
//! by the key's digest, and multi-stark also seeds the transcript with it.
//! [`from_bytes`] rejects a key whose parameters are below
//! [`security::MIN_CONJECTURED_BITS`].

pub mod range;
pub mod security;

use multi_stark::{
  expr::{ColRef, RowOffset, Source},
  graph::{ConstraintGraph, Node, NodeId},
  lookup::Lookup,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  system::{Circuit, System},
  types::{Commitment, CommitmentParameters, FriParameters, Val},
};

use multi_stark::types::GoldilocksBlake3Config as AiurConfig;

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
  let mut buf = Vec::new();
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
    1 => Node::Const(Val::from_u64(seg.u64()?)),
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
      Node::Mul(a, b) => get(&degrees, a)? + get(&degrees, b)?,
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
  let max_constraint_degree = seg.u16()? as usize;
  let lookup_group_size = seg.u8()? as usize;
  if !(1..=multi_stark::lookup::MAX_LOOKUP_GROUP).contains(&lookup_group_size) {
    return Err(format!("bad lookup group size {lookup_group_size}"));
  }
  let node_count = seg.u16()? as usize;
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
  // The graph's own max degree covers only the user roots (the serialized
  // `max_constraint_degree` is the combined user + analytic-logUp value).
  let mut user_max_degree = 0;
  for &z in &zeros {
    user_max_degree = user_max_degree.max(degrees[check_id(z)?]);
  }
  // The lookup prefix is exactly the nodes interned while compiling the
  // lookup expressions, all of which are reachable from (and bounded by)
  // the lookup roots — children always precede parents.
  let mut lookup_prefix_len = 0;
  for l in &lookups {
    for id in std::iter::once(l.multiplicity).chain(l.args.iter().copied()) {
      lookup_prefix_len = lookup_prefix_len.max(check_id(id)? + 1);
    }
  }
  let graph = ConstraintGraph {
    nodes,
    degrees,
    zeros,
    lookups,
    lookup_prefix_len,
    max_constraint_degree: user_max_degree,
  };
  let num_lookups = graph.lookups.len();
  let ext_degree =
    <multi_stark::types::ExtVal as multi_stark::p3_field::BasedVectorSpace<
      Val,
    >>::DIMENSION;
  Ok(Circuit {
    graph,
    main_width,
    preprocessed: None,
    preprocessed_width,
    preprocessed_height,
    num_lookups,
    stage_2_width: multi_stark::lookup::stage2_width(
      num_lookups,
      lookup_group_size,
      ext_degree,
    ),
    num_publics: multi_stark::lookup::num_publics(ext_degree),
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
  }
  let n_circuits = r.u16()? as usize;
  let mut circuits = Vec::with_capacity(n_circuits);
  for _ in 0..n_circuits {
    circuits.push(decode_circuit(&mut r)?);
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
      Some(Commitment::from(caps))
    },
    t => return Err(format!("bad Option tag {t}")),
  };
  let mut preprocessed_indices = Vec::with_capacity(n_circuits);
  for _ in 0..n_circuits {
    let v = r.u16()?;
    preprocessed_indices.push(if v == NO_PREP_INDEX {
      None
    } else {
      Some(v as usize)
    });
  }
  r.done("vk")?;
  let system = System {
    config: AiurConfig::new(commitment_parameters, fri_parameters),
    circuits,
    preprocessed_commit,
    preprocessed_indices,
  };
  Ok((system, commitment_parameters, fri_parameters))
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    expr::Expr, p3_matrix::dense::RowMajorMatrix, system::CircuitInputs,
  };

  /// Main's parameters, the lowest the floor admits.
  fn floor_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 2, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 100,
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

  /// The header fields are u16 LE at these offsets.
  fn with_header(field: usize, value: u16) -> Vec<u8> {
    let mut bytes = encoded();
    bytes[2 * field..2 * field + 2].copy_from_slice(&value.to_le_bytes());
    bytes
  }

  #[test]
  fn rejects_keys_below_the_security_floor() {
    // (field, value): log_blowup 0, log_blowup 1 (110 bits), 99 queries,
    // 19 query proof-of-work bits, and 33 commit proof-of-work bits.
    for (field, value) in [(0, 0), (0, 1), (4, 99), (6, 19), (5, 33)] {
      let bytes = with_header(field, value);
      let error = from_bytes(&bytes).err().expect("accepted a weak key");
      assert!(
        error.contains("floor")
          || error.contains("outside")
          || error.contains("exceeds"),
        "{error}"
      );
      // The waiver decodes the same bytes, for tests only.
      if field != 0 || value != 0 {
        from_bytes_below_floor(&bytes).unwrap();
      }
    }
    // Stronger parameters than the floor decode.
    from_bytes(&with_header(4, 101)).unwrap();
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
}
