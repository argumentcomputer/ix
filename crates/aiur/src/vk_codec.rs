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
//! # ⚠️ Wire format changed with the multi-stark constraint-IR migration
//!
//! The previous format serialized a per-circuit *symbolic* AIR
//! (`SymbolicExpression` trees + `LookupAir` + the `AiurCircuit` tag). The new
//! multi-stark compiles circuits to a flat base-field node graph, so this
//! codec now serializes that compiled form instead. **The Lean mirror
//! `Ix/MultiStark/SystemDeserialize.lean` must be rewritten to match this new
//! format** (it is NOT updated here). See "Wire format (v3)" below.
//!
//! # Wire format (v3)
//!
//! ```text
//! GLOBAL HEADER
//!   7 x u16 LE   commitment + FRI parameters (log_blowup, cap_height,
//!                log_final_poly_len, max_log_arity, num_queries,
//!                commit_proof_of_work_bits, query_proof_of_work_bits)
//!   u16          circuit count
//! PER-CIRCUIT RECORDS (circuit count times; each is `u32 LE len` + `len` bytes
//!                      so a record is a contiguous byte range)
//!   8 x u32 LE   main_width, preprocessed_width, preprocessed_height,
//!                num_publics, stage_2_width, max_constraint_degree,
//!                lookup_prefix_len, node_count
//!   node_count nodes, each:
//!     u8 tag  0 Const 1 Var 2 Public 3 IsFirstRow 4 IsLastRow
//!             5 IsTransition 6 Add 7 Sub 8 Mul 9 Neg
//!     Const:  u64 LE canonical value
//!     Var:    u8 source (0 Preprocessed 1 Main 2 Stage2), u8 offset
//!             (0 current 1 next), u32 LE column index
//!     Public: u32 LE index
//!     Add/Sub/Mul: u32 LE, u32 LE child node ids
//!     Neg:    u32 LE child node id
//!   u32 zero_count, then zero_count x u32 LE constraint-root node ids
//!   u32 lookup_count, then per lookup:
//!     u32 LE multiplicity node id
//!     u32 LE arg count, then arg_count x u32 LE arg node ids
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
//! as `as_canonical_u64()` and read back with `from_u64`.

// The codec is exercised by tests and wired to the FFI / Aiur port.
#![allow(dead_code)]

use multi_stark::{
  expr::{ColRef, RowOffset, Source},
  graph::{ConstraintGraph, Node, NodeId},
  lookup::Lookup,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  system::{Circuit, System},
  types::{Commitment, CommitmentParameters, FriParameters, Val},
};

use crate::synthesis::{AiurConfig, AiurSystem};

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

fn push_node_id(buf: &mut Vec<u8>, id: NodeId) {
  buf.extend_from_slice(&id.0.to_le_bytes());
}

fn push_node(buf: &mut Vec<u8>, node: &Node<Val>) {
  match node {
    Node::Const(c) => {
      buf.push(0);
      buf.extend_from_slice(&c.as_canonical_u64().to_le_bytes());
    },
    Node::Var(col) => {
      buf.push(1);
      let source = match col.source {
        Source::Preprocessed => 0u8,
        Source::Main => 1,
        Source::Stage2 => 2,
      };
      let offset = match col.offset {
        RowOffset::Current => 0u8,
        RowOffset::Next => 1,
      };
      buf.push(source);
      buf.push(offset);
      buf.extend_from_slice(&col.index.to_le_bytes());
    },
    Node::Public(i) => {
      buf.push(2);
      buf.extend_from_slice(&i.to_le_bytes());
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

fn encode_circuit(buf: &mut Vec<u8>, circuit: &Circuit<Val>) {
  let compiled = &circuit.graph;
  push_u32(buf, circuit.main_width);
  push_u32(buf, circuit.preprocessed_width);
  push_u32(buf, circuit.preprocessed_height);
  push_u32(buf, circuit.num_publics);
  push_u32(buf, circuit.stage_2_width);
  push_u32(buf, compiled.max_constraint_degree as usize);
  push_u32(buf, compiled.lookup_prefix_len);
  push_u32(buf, compiled.nodes.len());
  for node in &compiled.nodes {
    push_node(buf, node);
  }
  push_u32(buf, compiled.zeros.len());
  for &z in &compiled.zeros {
    push_node_id(buf, z);
  }
  push_u32(buf, compiled.lookups.len());
  for lookup in &compiled.lookups {
    push_node_id(buf, lookup.multiplicity);
    push_u32(buf, lookup.args.len());
    for &arg in &lookup.args {
      push_node_id(buf, arg);
    }
  }
}

/// Serialize the verifying key `System<AiurConfig>` (preprocessed traces are
/// skipped — see the module docs). The config's construction parameters are
/// passed alongside because [`AiurConfig`] doesn't expose them back; they are
/// written first so the decoder can rebuild the config.
pub(crate) fn to_bytes(
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
    let mut record = Vec::new();
    encode_circuit(&mut record, circuit);
    push_u32(&mut buf, record.len());
    buf.extend_from_slice(&record);
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

/// Convenience: serialize the verifying key of a built [`AiurSystem`].
pub fn aiur_system_to_bytes(sys: &AiurSystem) -> Result<Vec<u8>, String> {
  Ok(to_bytes(&sys.system, sys.commitment_parameters, sys.fri_parameters))
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
    Ok(NodeId(u32::from_le_bytes(self.take(4)?.try_into().unwrap())))
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
    0 => Node::Const(Val::from_u64(seg.u64()?)),
    1 => {
      let source = match seg.u8()? {
        0 => Source::Preprocessed,
        1 => Source::Main,
        2 => Source::Stage2,
        s => return Err(format!("bad source {s}")),
      };
      let offset = match seg.u8()? {
        0 => RowOffset::Current,
        1 => RowOffset::Next,
        o => return Err(format!("bad row offset {o}")),
      };
      let index = u32::from_le_bytes(seg.take(4)?.try_into().unwrap());
      Node::Var(ColRef { source, offset, index })
    },
    2 => Node::Public(u32::from_le_bytes(seg.take(4)?.try_into().unwrap())),
    3 => Node::IsFirstRow,
    4 => Node::IsLastRow,
    5 => Node::IsTransition,
    6 => Node::Add(seg.node_id()?, seg.node_id()?),
    7 => Node::Sub(seg.node_id()?, seg.node_id()?),
    8 => Node::Mul(seg.node_id()?, seg.node_id()?),
    9 => Node::Neg(seg.node_id()?),
    t => return Err(format!("bad node tag {t}")),
  })
}

/// Recompute per-node degree multiples in node order (children precede parents
/// in the compiled vector).
fn recompute_degrees(nodes: &[Node<Val>]) -> Vec<u32> {
  let mut degrees: Vec<u32> = Vec::with_capacity(nodes.len());
  for node in nodes {
    let d = match *node {
      Node::Const(_) | Node::Public(_) | Node::IsTransition => 0,
      Node::Var(_) | Node::IsFirstRow | Node::IsLastRow => 1,
      Node::Add(a, b) | Node::Sub(a, b) => {
        degrees[a.0 as usize].max(degrees[b.0 as usize])
      },
      Node::Mul(a, b) => degrees[a.0 as usize] + degrees[b.0 as usize],
      Node::Neg(a) => degrees[a.0 as usize],
    };
    degrees.push(d);
  }
  degrees
}

fn decode_circuit(bytes: &[u8]) -> Result<Circuit<Val>, String> {
  let mut seg = Seg { buf: bytes, pos: 0 };
  let main_width = seg.u32_usize()?;
  let preprocessed_width = seg.u32_usize()?;
  let preprocessed_height = seg.u32_usize()?;
  let num_publics = seg.u32_usize()?;
  let stage_2_width = seg.u32_usize()?;
  let max_constraint_degree =
    u32::try_from(seg.u32_usize()?).expect("degree exceeds u32");
  let lookup_prefix_len = seg.u32_usize()?;
  let node_count = seg.u32_usize()?;
  let mut nodes = Vec::with_capacity(node_count.min(1 << 20));
  for _ in 0..node_count {
    nodes.push(decode_node(&mut seg)?);
  }
  let zero_count = seg.u32_usize()?;
  let mut zeros = Vec::with_capacity(zero_count.min(1 << 20));
  for _ in 0..zero_count {
    zeros.push(seg.node_id()?);
  }
  let lookup_count = seg.u32_usize()?;
  let mut lookups = Vec::with_capacity(lookup_count.min(1 << 16));
  for _ in 0..lookup_count {
    let multiplicity = seg.node_id()?;
    let arg_count = seg.u32_usize()?;
    let mut args = Vec::with_capacity(arg_count.min(1 << 16));
    for _ in 0..arg_count {
      args.push(seg.node_id()?);
    }
    lookups.push(Lookup { multiplicity, args });
  }
  seg.done("circuit record")?;

  let degrees = recompute_degrees(&nodes);
  let graph = ConstraintGraph {
    nodes,
    degrees,
    zeros,
    lookups,
    lookup_prefix_len,
    max_constraint_degree,
  };
  let num_lookups = graph.lookups.len();
  Ok(Circuit {
    graph,
    main_width,
    preprocessed: None,
    preprocessed_width,
    preprocessed_height,
    num_lookups,
    stage_2_width,
    num_publics,
  })
}

/// Deserialize a `System<AiurConfig>` from [`to_bytes`] output, requiring that
/// every byte is consumed. Also returns the config's construction parameters,
/// which the `System` itself doesn't expose.
pub(crate) fn from_bytes(
  bytes: &[u8],
) -> Result<(System<AiurConfig>, CommitmentParameters, FriParameters), String> {
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
  let n_circuits = r.u16()? as usize;
  let mut circuits = Vec::with_capacity(n_circuits);
  for _ in 0..n_circuits {
    let len = r.u32_usize()?;
    let record = r.take(len)?;
    circuits.push(decode_circuit(record)?);
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
  use crate::gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2};
  use multi_stark::system::CircuitInputs;

  fn test_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    (cp, fp)
  }

  fn test_system() -> (System<AiurConfig>, CommitmentParameters, FriParameters)
  {
    let (cp, fp) = test_parameters();
    let inputs = [
      CircuitInputs {
        main_width: Bytes1.main_width(),
        preprocessed: Bytes1.preprocessed(),
        constraints: vec![],
        ext_constraints: vec![],
        lookups: Bytes1.lookups(),
      },
      CircuitInputs {
        main_width: Bytes2.main_width(),
        preprocessed: Bytes2.preprocessed(),
        constraints: vec![],
        ext_constraints: vec![],
        lookups: Bytes2.lookups(),
      },
    ];
    let (system, _key) = System::new(AiurConfig::new(cp, fp), inputs);
    (system, cp, fp)
  }

  /// Round-trip: decode(encode(x)) re-encodes to the same bytes, with matching
  /// compiled node graphs, constraint roots, and lookups.
  #[test]
  fn system_vk_round_trips() {
    let (system, cp, fp) = test_system();
    let bytes = to_bytes(&system, cp, fp);
    let (back, back_cp, back_fp) = from_bytes(&bytes).expect("decode");
    let reencoded = to_bytes(&back, back_cp, back_fp);
    assert_eq!(bytes, reencoded, "verifying-key codec round-trip mismatch");
    assert_eq!(system.circuits.len(), back.circuits.len());
    for (a, b) in system.circuits.iter().zip(&back.circuits) {
      assert_eq!(a.graph.nodes, b.graph.nodes, "nodes mismatch");
      assert_eq!(a.graph.zeros, b.graph.zeros, "zeros mismatch");
      assert_eq!(a.graph.lookups.len(), b.graph.lookups.len());
      for (la, lb) in a.graph.lookups.iter().zip(&b.graph.lookups) {
        assert_eq!(la.multiplicity, lb.multiplicity);
        assert_eq!(la.args, lb.args);
      }
      assert_eq!(a.main_width, b.main_width);
      assert_eq!(a.stage_2_width, b.stage_2_width);
      assert_eq!(a.num_publics, b.num_publics);
      assert_eq!(a.preprocessed_width, b.preprocessed_width);
      assert_eq!(a.preprocessed_height, b.preprocessed_height);
    }
  }

  #[test]
  fn rejects_trailing_bytes() {
    let (system, cp, fp) = test_system();
    let mut bytes = to_bytes(&system, cp, fp);
    bytes.push(0);
    assert!(from_bytes(&bytes).is_err(), "should reject trailing data");
  }

  /// A tampered per-circuit record length must be rejected (the record reader
  /// enforces exact consumption).
  #[test]
  fn rejects_bad_record_length() {
    let (system, cp, fp) = test_system();
    let mut bytes = to_bytes(&system, cp, fp);
    // First record length is the u32 right after the 16-byte global header.
    let len = u32::from_le_bytes(bytes[16..20].try_into().unwrap());
    bytes[16..20].copy_from_slice(&(len + 1).to_le_bytes());
    assert!(from_bytes(&bytes).is_err(), "should reject bad record length");
  }
}
