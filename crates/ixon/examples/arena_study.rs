//! ExprMeta arena encoding study.
//!
//! Streams §5 of an `.ixe` file (`Env::parse_lazy_index` +
//! `NamedMetaCursor`), decodes every `ConstantMeta` (primary and `original`)
//! with the production reader, and prices each metadata arena under several
//! child-reference encodings. Every price comes from one size function that
//! mirrors the arena writer; `--check-writer` compares it with the production
//! writer.
//!
//! Encodings (only the arena's integers differ; tag bytes, raw addresses and
//! the rest of the file are the same):
//!
//! * `v3`: absolute child indices, every integer `Tag0` (the v3 format);
//! * `abs`: absolute child indices, every integer TagN (`f = 0`) — the v4
//!   baseline once `Tag0` is replaced everywhere;
//! * `delta`: every child reference is the backward delta `i - 1 - c`
//!   (wrapping) as TagN, every other integer TagN;
//! * `implicit`: post-order implicit children. A structural child slot whose
//!   node is the one the post-order cursor expects is "fresh" and costs no
//!   bytes (one bit in the node tag); every other child reference is an
//!   explicit backward delta `i - 1 - c` (wrapping) as TagN
//!   (`docs/sharing-minimum-arena.md`);
//! * `implicit + hash-consing`: `implicit` after hash-consing each arena
//!   (identical nodes with identical children merged, first occurrence kept;
//!   nodes carrying a level-spelling patch are never merged).
//!
//! The tool also reports the child-delta distribution, the fraction of fresh
//! children, and the name-reference bytes inside arenas.
//!
//! ```text
//! cargo run --release -p ixon --example arena_study -- <file.ixe>
//!   [--check-writer]   compare every arena's predicted size under the
//!                      production writer's encoding with
//!                      `ExprMeta::put_with`, and round-trip it through the
//!                      production writer and reader
//!   [--writer v3|implicit]   the production writer's encoding (default
//!                      implicit)
//!   [--other-tagn]     the production writer writes every integer other
//!                      than child references as TagN (default Tag0)
//!   [--int-census]     instead: price every f = 0 integer outside constant
//!                      bodies under Tag0, TagN and TagN with a 4-byte rung,
//!                      self-checked against every §5 window
//! ```

#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_sign_loss)]
#![allow(clippy::needless_range_loop)]

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Instant;

use ix_common::address::Address;
use ix_common::env::ReducibilityHints;
use ixon::Env;
use ixon::TagN;
use ixon::constant::Constant;
use ixon::metadata::{
  CallSiteEntry, ConstantMeta, ConstantMetaInfo, DataValue, ExprMeta,
  ExprMetaData, NameGet, NameIndex, NamePut,
};
use ixon::serialize::{NamedMetaCursor, put_expr, put_named_indexed};
use ixon::univ::put_univ;

// ---------------------------------------------------------------------------
// Integer prices
// ---------------------------------------------------------------------------

/// Width of the v3 `Tag0` code.
fn tag0_w(v: u64) -> usize {
  if v < 128 { 1 } else { 1 + (8 - (v.leading_zeros() as usize) / 8) }
}

/// Width of TagN with a 0-bit flag.
fn tagn_w(v: u64) -> usize {
  TagN::byte_width(0, v)
}

fn code_w(tagn: bool, v: u64) -> usize {
  if tagn { tagn_w(v) } else { tag0_w(v) }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Enc {
  V3,
  Abs,
  Delta,
  Implicit,
}

const ENCS: [Enc; 4] = [Enc::V3, Enc::Abs, Enc::Delta, Enc::Implicit];

/// Integer codes per field family (`true` = TagN, `false` = Tag0). `names`
/// covers name indices (node names, mdata keys, `OfName` values), `mdata`
/// the mdata stack and map counts, `scalars` every other integer of the
/// arena (length prefix, call-site counts and scalars). Child references
/// follow `children`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Pricing {
  names: bool,
  mdata: bool,
  scalars: bool,
  children: Enc,
}

impl Pricing {
  fn of(enc: Enc) -> Pricing {
    let n = enc != Enc::V3;
    Pricing { names: n, mdata: n, scalars: n, children: enc }
  }
}

// ---------------------------------------------------------------------------
// Node structure
// ---------------------------------------------------------------------------

fn kind(n: &ExprMetaData) -> usize {
  match n {
    ExprMetaData::Leaf => 0,
    ExprMetaData::App { .. } => 1,
    ExprMetaData::Binder { .. } => 2,
    ExprMetaData::LetBinder { .. } => 3,
    ExprMetaData::Ref { .. } => 4,
    ExprMetaData::Prj { .. } => 5,
    ExprMetaData::Mdata { .. } => 6,
    ExprMetaData::CallSite { .. } => 7,
    ExprMetaData::EtaCallSite { .. } => 8,
  }
}

const KIND_NAMES: [&str; 9] = [
  "leaf",
  "app",
  "binder",
  "letBinder",
  "ref",
  "prj",
  "mdata",
  "callSite",
  "etaCallSite",
];

const SLOT_NAMES: [&str; 10] = [
  "App function",
  "App argument",
  "Binder type",
  "Binder body",
  "Let type",
  "Let value",
  "Let body",
  "Prj child",
  "Mdata child",
  "call-site references",
];

/// Structural child slots (the ones that can be implicit), in field order,
/// with their report slot ids.
fn slots(n: &ExprMetaData) -> Vec<(usize, u64)> {
  match n {
    ExprMetaData::App { children } => vec![(0, children[0]), (1, children[1])],
    ExprMetaData::Binder { children, .. } => {
      vec![(2, children[0]), (3, children[1])]
    },
    ExprMetaData::LetBinder { children, .. } => {
      vec![(4, children[0]), (5, children[1]), (6, children[2])]
    },
    ExprMetaData::Prj { child, .. } => vec![(7, *child)],
    ExprMetaData::Mdata { child, .. } => vec![(8, *child)],
    _ => vec![],
  }
}

/// Arena references of call-site nodes (always explicit), in write order.
fn callsite_refs(n: &ExprMetaData) -> Vec<u64> {
  let mut out = Vec::new();
  let ents = |es: &[CallSiteEntry], out: &mut Vec<u64>| {
    for e in es {
      match e {
        CallSiteEntry::Kept { meta, .. }
        | CallSiteEntry::Collapsed { meta, .. } => out.push(*meta),
      }
    }
  };
  match n {
    ExprMetaData::CallSite { entries, canon_meta, orig_head, .. } => {
      ents(entries, &mut out);
      out.extend_from_slice(canon_meta);
      if let Some((_, m)) = orig_head {
        out.push(*m);
      }
    },
    ExprMetaData::EtaCallSite { entries, canon_meta, wrapper_meta, .. } => {
      ents(entries, &mut out);
      out.extend_from_slice(canon_meta);
      out.push(*wrapper_meta);
    },
    _ => {},
  }
  out
}

/// The node's own name reference, if any.
fn node_name(n: &ExprMetaData) -> Option<&Address> {
  match n {
    ExprMetaData::Binder { name, .. }
    | ExprMetaData::LetBinder { name, .. }
    | ExprMetaData::Ref { name }
    | ExprMetaData::CallSite { name, .. }
    | ExprMetaData::EtaCallSite { name, .. } => Some(name),
    ExprMetaData::Prj { struct_name, .. } => Some(struct_name),
    _ => None,
  }
}

/// Bytes of a node excluding its child references and its own name
/// reference: tag byte, mdata payload, call-site scalars.
fn rest_w(n: &ExprMetaData, ix: &NameIndex, pr: Pricing) -> usize {
  let w = |v: u64| code_w(pr.scalars, v);
  let mw = |v: u64| code_w(pr.mdata, v);
  let name_w =
    |a: &Address| code_w(pr.names, *ix.get(a).expect("name in index"));
  let dv_w = |d: &DataValue| -> usize {
    1 + match d {
      DataValue::OfBool(_) => 1,
      DataValue::OfName(a) => name_w(a),
      _ => 32,
    }
  };
  let ents_w = |es: &[CallSiteEntry]| -> usize {
    w(es.len() as u64)
      + es
        .iter()
        .map(|e| match e {
          CallSiteEntry::Kept { canon_idx: x, .. }
          | CallSiteEntry::Collapsed { sharing_idx: x, .. } => 1 + w(*x),
        })
        .sum::<usize>()
  };
  1 + match n {
    ExprMetaData::Mdata { mdata, .. } => {
      mw(mdata.len() as u64)
        + mdata
          .iter()
          .map(|kv| {
            mw(kv.len() as u64)
              + kv.iter().map(|(k, d)| name_w(k) + dv_w(d)).sum::<usize>()
          })
          .sum::<usize>()
    },
    ExprMetaData::CallSite { entries, canon_meta, orig_head, .. } => {
      ents_w(entries)
        + w(canon_meta.len() as u64)
        + 1
        + orig_head.map_or(0, |(s, _)| w(s))
    },
    ExprMetaData::EtaCallSite { n_synth, entries, canon_meta, .. } => {
      w(*n_synth) + ents_w(entries) + w(canon_meta.len() as u64)
    },
    _ => 0,
  }
}

// ---------------------------------------------------------------------------
// The implicit (post-order cursor) encoding
// ---------------------------------------------------------------------------

/// Per node, the fresh mask over its structural slots: bit `s` set = slot
/// `s` is the node the post-order cursor expects and is not written. The
/// cursor starts at `i - 1`, visits the slots last to first, and after a
/// fresh child `c` moves to `lo[c] - 1`, where `lo[c]` is the first index of
/// `c`'s contiguous block (`lo[i] = cursor + 1` after `i`'s slots).
fn implicit_masks(nodes: &[ExprMetaData]) -> Vec<u8> {
  let mut lo: Vec<u64> = Vec::with_capacity(nodes.len());
  let mut masks = Vec::with_capacity(nodes.len());
  for (i, n) in nodes.iter().enumerate() {
    let sl = slots(n);
    let mut cur: i64 = i as i64 - 1;
    let mut mask = 0u8;
    for s in (0..sl.len()).rev() {
      let c = sl[s].1;
      if cur >= 0 && c == cur as u64 {
        mask |= 1 << s;
        cur = lo[c as usize] as i64 - 1;
      }
    }
    lo.push((cur + 1) as u64);
    masks.push(mask);
  }
  masks
}

/// Child-reference bytes of node `i` under `enc` (`mask` only for
/// `Implicit`).
fn child_w(n: &ExprMetaData, i: usize, mask: u8, enc: Enc) -> usize {
  let delta = |c: u64| (i as u64).wrapping_sub(1).wrapping_sub(c);
  let mut b = 0;
  for (s, (_, c)) in slots(n).into_iter().enumerate() {
    b += match enc {
      Enc::V3 => tag0_w(c),
      Enc::Abs => tagn_w(c),
      Enc::Delta => tagn_w(delta(c)),
      Enc::Implicit => {
        if mask & (1 << s) != 0 {
          0
        } else {
          tagn_w(delta(c))
        }
      },
    };
  }
  for c in callsite_refs(n) {
    b += match enc {
      Enc::V3 => tag0_w(c),
      Enc::Abs => tagn_w(c),
      Enc::Delta | Enc::Implicit => tagn_w(delta(c)),
    };
  }
  b
}

/// Bytes of node `i` (with its implicit mask) under `pr`.
fn node_w(
  n: &ExprMetaData,
  i: usize,
  mask: u8,
  ix: &NameIndex,
  pr: Pricing,
) -> usize {
  rest_w(n, ix, pr)
    + node_name(n).map_or(0, |a| code_w(pr.names, ix[a]))
    + child_w(n, i, mask, pr.children)
}

/// Predicted arena bytes (length prefix + nodes) under `pr`.
fn arena_w(nodes: &[ExprMetaData], ix: &NameIndex, pr: Pricing) -> usize {
  let masks = implicit_masks(nodes);
  let mut b = code_w(pr.scalars, nodes.len() as u64);
  for (i, n) in nodes.iter().enumerate() {
    b += node_w(n, i, masks[i], ix, pr);
  }
  b
}

/// Renumber every arena reference of a node.
fn map_refs(n: &mut ExprMetaData, f: &dyn Fn(u64) -> u64) {
  let ents = |es: &mut Vec<CallSiteEntry>| {
    for e in es.iter_mut() {
      match e {
        CallSiteEntry::Kept { meta, .. }
        | CallSiteEntry::Collapsed { meta, .. } => *meta = f(*meta),
      }
    }
  };
  match n {
    ExprMetaData::App { children } | ExprMetaData::Binder { children, .. } => {
      for c in children.iter_mut() {
        *c = f(*c);
      }
    },
    ExprMetaData::LetBinder { children, .. } => {
      for c in children.iter_mut() {
        *c = f(*c);
      }
    },
    ExprMetaData::Prj { child, .. } | ExprMetaData::Mdata { child, .. } => {
      *child = f(*child);
    },
    ExprMetaData::CallSite { entries, canon_meta, orig_head, .. } => {
      ents(entries);
      for c in canon_meta.iter_mut() {
        *c = f(*c);
      }
      if let Some((_, m)) = orig_head {
        *m = f(*m);
      }
    },
    ExprMetaData::EtaCallSite { entries, canon_meta, wrapper_meta, .. } => {
      ents(entries);
      for c in canon_meta.iter_mut() {
        *c = f(*c);
      }
      *wrapper_meta = f(*wrapper_meta);
    },
    ExprMetaData::Leaf | ExprMetaData::Ref { .. } => {},
  }
}

/// Hash-cons an arena: first occurrences in order, references renumbered;
/// nodes whose index carries a level-spelling patch stay distinct.
fn hash_cons(
  nodes: &[ExprMetaData],
  patched: &HashSet<u64>,
) -> (Vec<ExprMetaData>, Vec<u64>) {
  let mut map: HashMap<(Option<usize>, ExprMetaData), u64> = HashMap::new();
  let mut canon: Vec<u64> = Vec::with_capacity(nodes.len());
  let mut out: Vec<ExprMetaData> = Vec::new();
  for (i, n) in nodes.iter().enumerate() {
    let mut m = n.clone();
    // Non-backward references (none expected) are kept verbatim.
    map_refs(&mut m, &|c| canon.get(c as usize).copied().unwrap_or(c));
    let key = (patched.contains(&(i as u64)).then_some(i), m.clone());
    let id = *map.entry(key).or_insert_with(|| {
      out.push(m);
      (out.len() - 1) as u64
    });
    canon.push(id);
  }
  (out, canon)
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// TagN (`f = 0`) width buckets: 1, 2, 3, 5, 9 bytes.
fn wbucket(v: u64) -> usize {
  match tagn_w(v) {
    1 => 0,
    2 => 1,
    3 => 2,
    5 => 3,
    _ => 4,
  }
}

#[derive(Default)]
struct Stats {
  entries: u64,
  arenas: u64,
  orig_arenas: u64,
  nodes: u64,
  kind_nodes: [u64; 9],
  /// Bytes per encoding (index into `ENCS`), then `implicit + hash-consing`
  /// and `delta + hash-consing`.
  bytes: [u64; 6],
  /// Root and patch indices outside the arena (type/value/rule roots,
  /// level-spelling patch keys): count, TagN bytes before and after
  /// hash-consing, and how many point to a merged (redirected) node.
  roots: u64,
  root_bytes: u64,
  root_bytes_hc: u64,
  roots_redirected: u64,
  /// Call-site references redirected by hash-consing.
  cs_refs_redirected: u64,
  /// Node bytes per kind per encoding (length prefixes excluded).
  kind_bytes: [[u64; 9]; 4],
  slot_children: [u64; 10],
  slot_fresh: [u64; 10],
  slot_forward: [u64; 10],
  /// Δ = 0 (the immediately preceding node).
  slot_delta0: [u64; 10],
  slot_delta_w: [[u64; 5]; 10],
  slot_explicit_w: [[u64; 5]; 10],
  hc_nodes: u64,
  name_refs: u64,
  name_bytes_v3: u64,
  name_bytes_tagn: u64,
  name_distinct: u64,
  name_local_bytes: u64,
  writer_checked: u64,
  writer_size_mismatch: u64,
  writer_roundtrip_mismatch: u64,
  writer_bytes: u64,
  v3_node_mismatch: u64,
  /// Writer check: per-entry arena bytes written minus the same arenas priced
  /// in v3, and the §5 window and length-prefix bytes as written and as they
  /// would be with v3 arenas.
  entry_delta: i64,
  window_new: u64,
  window_v3: u64,
  prefix_new: u64,
  prefix_v3: u64,
}

fn arena_of(info: &ConstantMetaInfo) -> Option<&ExprMeta> {
  match info {
    ConstantMetaInfo::Def { arena, .. }
    | ConstantMetaInfo::Axio { arena, .. }
    | ConstantMetaInfo::Quot { arena, .. }
    | ConstantMetaInfo::Indc { arena, .. }
    | ConstantMetaInfo::Ctor { arena, .. }
    | ConstantMetaInfo::Rec { arena, .. } => Some(arena),
    ConstantMetaInfo::Empty | ConstantMetaInfo::Muts { .. } => None,
  }
}

/// Arena indices held outside the arena by the variant: type, value and
/// rule roots.
fn roots_of(info: &ConstantMetaInfo) -> Vec<u64> {
  match info {
    ConstantMetaInfo::Def { type_root, value_root, .. } => {
      vec![*type_root, *value_root]
    },
    ConstantMetaInfo::Axio { type_root, .. }
    | ConstantMetaInfo::Quot { type_root, .. }
    | ConstantMetaInfo::Indc { type_root, .. }
    | ConstantMetaInfo::Ctor { type_root, .. } => vec![*type_root],
    ConstantMetaInfo::Rec { type_root, rule_roots, .. } => {
      let mut v = vec![*type_root];
      v.extend_from_slice(rule_roots);
      v
    },
    ConstantMetaInfo::Empty | ConstantMetaInfo::Muts { .. } => vec![],
  }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Writer {
  V3,
  Implicit,
}

struct Opts {
  check_writer: bool,
  writer: Writer,
  /// Every integer of the production writer other than child references
  /// is TagN (`--other-tagn`, after the Tag0 removal) or Tag0.
  other_tagn: bool,
}

impl Opts {
  /// The pricing that matches the production writer.
  fn pricing(&self) -> Pricing {
    match self.writer {
      Writer::V3 => Pricing::of(Enc::V3),
      Writer::Implicit => Pricing {
        names: self.other_tagn,
        mdata: self.other_tagn,
        scalars: self.other_tagn,
        children: Enc::Implicit,
      },
    }
  }
}

fn study_arena(
  st: &mut Stats,
  cm: &ConstantMeta,
  ix: &NameIndex,
  rev: &Vec<Address>,
  orig: bool,
  opts: &Opts,
) {
  let Some(arena) = arena_of(&cm.info) else { return };
  let nodes = &arena.nodes;
  st.arenas += 1;
  if orig {
    st.orig_arenas += 1;
  }
  st.nodes += nodes.len() as u64;
  let masks = implicit_masks(nodes);
  for (e, enc) in ENCS.iter().enumerate() {
    st.bytes[e] += code_w(*enc != Enc::V3, nodes.len() as u64) as u64;
  }
  let mut names: HashMap<u64, u64> = HashMap::new();
  for (i, n) in nodes.iter().enumerate() {
    let k = kind(n);
    st.kind_nodes[k] += 1;
    for (e, enc) in ENCS.iter().enumerate() {
      let b = node_w(n, i, masks[i], ix, Pricing::of(*enc)) as u64;
      st.bytes[e] += b;
      st.kind_bytes[e][k] += b;
    }
    if opts.writer == Writer::V3 && opts.check_writer {
      // The v3 node writer is position-free: check every node alone.
      let predicted = node_w(n, i, 0, ix, Pricing::of(Enc::V3));
      let one = ExprMeta { nodes: vec![n.clone()] };
      let mut buf = Vec::new();
      one.put_with(NamePut::Indexed(ix), &mut buf).expect("put");
      // The one-node arena has a 1-byte length prefix.
      if buf.len() - 1 != predicted {
        st.v3_node_mismatch += 1;
      }
    }
    for (s, (slot, c)) in slots(n).iter().enumerate() {
      st.slot_children[*slot] += 1;
      if *c >= i as u64 {
        st.slot_forward[*slot] += 1;
      }
      let d = (i as u64).wrapping_sub(1).wrapping_sub(*c);
      st.slot_delta_w[*slot][wbucket(d)] += 1;
      if d == 0 {
        st.slot_delta0[*slot] += 1;
      }
      if masks[i] & (1 << s) != 0 {
        st.slot_fresh[*slot] += 1;
      } else {
        st.slot_explicit_w[*slot][wbucket(d)] += 1;
      }
    }
    for c in callsite_refs(n) {
      st.slot_children[9] += 1;
      if c >= i as u64 {
        st.slot_forward[9] += 1;
      }
      let d = (i as u64).wrapping_sub(1).wrapping_sub(c);
      st.slot_delta_w[9][wbucket(d)] += 1;
      st.slot_explicit_w[9][wbucket(d)] += 1;
      if d == 0 {
        st.slot_delta0[9] += 1;
      }
    }
    if let Some(a) = node_name(n) {
      let g = ix[a];
      st.name_refs += 1;
      st.name_bytes_v3 += tag0_w(g) as u64;
      st.name_bytes_tagn += tagn_w(g) as u64;
      let next = names.len() as u64;
      let local = *names.entry(g).or_insert(next);
      st.name_local_bytes += tagn_w(local) as u64;
    }
  }
  st.name_distinct += names.len() as u64;
  st.name_local_bytes += tagn_w(names.len() as u64) as u64
    + names.keys().map(|g| tagn_w(*g) as u64).sum::<u64>();
  let patched: HashSet<u64> =
    cm.univ_patches.iter().map(|p| p.arena_idx).collect();
  let (hc, canon) = hash_cons(nodes, &patched);
  st.hc_nodes += hc.len() as u64;
  st.bytes[4] += arena_w(&hc, ix, Pricing::of(Enc::Implicit)) as u64;
  st.bytes[5] += arena_w(&hc, ix, Pricing::of(Enc::Delta)) as u64;
  // Redirection: roots and patch keys outside the arena take the surviving
  // node's index; a reference is "redirected" when its node was merged
  // into an earlier one.
  // Class ids are assigned in first-occurrence order, so node i survives
  // iff its id equals the number of classes seen before it.
  let mut survives = Vec::with_capacity(canon.len());
  let mut seen = 0u64;
  for &k in &canon {
    survives.push(k == seen);
    if k == seen {
      seen += 1;
    }
  }
  let merged = |c: u64| survives.get(c as usize).is_some_and(|s| !s);
  let mut outside: Vec<u64> = roots_of(&cm.info);
  outside.extend(cm.univ_patches.iter().map(|p| p.arena_idx));
  for r in outside {
    st.roots += 1;
    st.root_bytes += tagn_w(r) as u64;
    let nr = canon.get(r as usize).copied().unwrap_or(r);
    st.root_bytes_hc += tagn_w(nr) as u64;
    if merged(r) {
      st.roots_redirected += 1;
    }
  }
  for n in nodes {
    for c in callsite_refs(n) {
      if merged(c) {
        st.cs_refs_redirected += 1;
      }
    }
  }
  if opts.check_writer {
    let predicted = arena_w(nodes, ix, opts.pricing());
    let mut buf = Vec::new();
    arena.put_with(NamePut::Indexed(ix), &mut buf).expect("arena put");
    st.writer_checked += 1;
    st.writer_bytes += buf.len() as u64;
    st.entry_delta +=
      buf.len() as i64 - arena_w(nodes, ix, Pricing::of(Enc::V3)) as i64;
    if buf.len() != predicted {
      st.writer_size_mismatch += 1;
    }
    let mut slice: &[u8] = &buf;
    match ExprMeta::get_with(&mut slice, NameGet::Indexed(rev)) {
      Ok(back) if back == *arena && slice.is_empty() => {},
      _ => st.writer_roundtrip_mismatch += 1,
    }
  }
}

fn pct(a: u64, b: u64) -> String {
  if b == 0 {
    "0".into()
  } else {
    format!("{:.2}%", a as f64 * 100.0 / b as f64)
  }
}

fn spct(a: i64, b: u64) -> String {
  if b == 0 {
    "0".into()
  } else {
    format!("{:+.2}%", a as f64 * 100.0 / b as f64)
  }
}

fn main() -> Result<(), String> {
  let mut args = std::env::args().skip(1);
  let path = args.next().ok_or(
    "usage: arena_study <file.ixe> [--check-writer] [--writer v3|implicit] [--other-tagn]",
  )?;
  let mut opts =
    Opts { check_writer: false, writer: Writer::Implicit, other_tagn: false };
  let mut census = false;
  while let Some(a) = args.next() {
    match a.as_str() {
      "--check-writer" => opts.check_writer = true,
      "--other-tagn" => opts.other_tagn = true,
      "--int-census" => census = true,
      "--writer" => {
        opts.writer = match args.next().as_deref() {
          Some("v3") => Writer::V3,
          Some("implicit") => Writer::Implicit,
          x => return Err(format!("bad --writer {x:?}")),
        }
      },
      x => return Err(format!("unknown argument {x}")),
    }
  }
  let t0 = Instant::now();
  let file = std::fs::File::open(&path).map_err(|e| e.to_string())?;
  // SAFETY: the corpus file is not modified while it is mapped.
  let mmap =
    Arc::new(unsafe { memmap2::Mmap::map(&file) }.map_err(|e| e.to_string())?);
  if census {
    println!("{}", int_census(&path, &mmap)?);
    return Ok(());
  }
  let index = Env::parse_lazy_index(&mmap)?;
  let ix: NameIndex = index
    .name_reverse_index
    .iter()
    .enumerate()
    .map(|(i, a)| (a.clone(), i as u64))
    .collect();
  eprintln!(
    "[arena_study] {path}: {} bytes, {} names, {} named entries; index in {} ms",
    mmap.len(),
    index.name_reverse_index.len(),
    index.named.len(),
    t0.elapsed().as_millis()
  );
  let const_addrs: Vec<Address> =
    index.consts.iter().map(|c| c.addr.clone()).collect();
  let (mut scratch, mut entry_buf) = (Vec::new(), Vec::new());
  let mut cursor = NamedMetaCursor::open(&mmap, &index)?;
  let mut st = Stats::default();
  while let Some((_, named)) = cursor.next_entry()? {
    st.entries += 1;
    st.entry_delta = 0;
    let meta = named.meta();
    study_arena(&mut st, &meta, &ix, &index.name_reverse_index, false, &opts);
    if let Some((_, o)) = named.original() {
      study_arena(&mut st, &o, &ix, &index.name_reverse_index, true, &opts);
    }
    if opts.check_writer {
      // The §5 window as the production writer emits it, and as it would
      // be with the same arenas in v3 (everything else in the window is
      // written by the same helpers).
      entry_buf.clear();
      put_named_indexed(
        &named,
        &ix,
        &const_addrs,
        &mut scratch,
        &mut entry_buf,
      )?;
      let new = scratch.len() as u64;
      let v3 = (new as i64 - st.entry_delta) as u64;
      st.window_new += new;
      st.window_v3 += v3;
      st.prefix_new += code_w(opts.other_tagn, new) as u64;
      st.prefix_v3 += code_w(opts.other_tagn, v3) as u64;
    }
    if st.entries % 100_000 == 0 {
      eprintln!(
        "[arena_study] {} entries, {} s",
        st.entries,
        t0.elapsed().as_secs()
      );
    }
  }
  let file = mmap.len() as u64;
  let mut md = String::new();
  md += &format!(
    "## Arena study: `{}`\n\n- File {} bytes; Named entries {}; arenas {} ({} in `original` metadata); nodes {}. Wall {} s.\n",
    path,
    file,
    st.entries,
    st.arenas,
    st.orig_arenas,
    st.nodes,
    t0.elapsed().as_secs()
  );
  if opts.check_writer {
    md += &format!(
      "- Writer check ({}, integers other than child references {}): {} arenas, {} bytes written; size mismatches **{}**, roundtrip mismatches **{}**.\n",
      match opts.writer {
        Writer::V3 => "v3",
        Writer::Implicit => "implicit",
      },
      if opts.other_tagn { "TagN" } else { "Tag0" },
      st.writer_checked,
      st.writer_bytes,
      st.writer_size_mismatch,
      st.writer_roundtrip_mismatch
    );
    if opts.writer == Writer::V3 {
      md += &format!(
        "- v3 node mirror vs production node writer: **{}** mismatches.\n",
        st.v3_node_mismatch
      );
    }
    let new = st.window_new + st.prefix_new;
    let v3 = st.window_v3 + st.prefix_v3;
    md += &format!(
      "- §5 metadata windows as written by the production writer: {} bytes + {} length-prefix bytes; with the same arenas in v3: {} + {}. Change: {:+} bytes ({} of the file).\n",
      st.window_new,
      st.prefix_new,
      st.window_v3,
      st.prefix_v3,
      new as i64 - v3 as i64,
      spct(new as i64 - v3 as i64, file)
    );
  }
  md += "\nArena bytes (length prefixes and nodes, primary and `original`) per encoding:\n\n| encoding | bytes | % of file | vs v3 | vs abs (v4 baseline) | change vs abs, % of file |\n|---|---:|---:|---:|---:|---:|\n";
  let enc_names = [
    "v3 (Tag0, absolute)",
    "abs (TagN, absolute)",
    "delta (TagN backward deltas)",
    "implicit (post-order cursor + TagN deltas)",
    "implicit + hash-consing (dedup first)",
    "delta + hash-consing (dedup first)",
  ];
  for (e, nm) in enc_names.iter().enumerate() {
    let b = st.bytes[e];
    md += &format!(
      "| {} | {} | {} | {} | {} | {} |\n",
      nm,
      b,
      pct(b, file),
      b as i64 - st.bytes[0] as i64,
      b as i64 - st.bytes[1] as i64,
      spct(b as i64 - st.bytes[1] as i64, file)
    );
  }
  md += &format!(
    "\n- Hash-consing keeps {} of {} nodes ({}); nodes carrying a level-spelling patch are never merged.\n- Redirection outside the arena (type/value/rule roots and patch keys): {} indices, {} redirected to an earlier surviving node; TagN bytes {} before, {} after hash-consing ({:+}). Call-site references redirected inside the arena: {} (priced in the arena rows).\n",
    st.hc_nodes,
    st.nodes,
    pct(st.hc_nodes, st.nodes),
    st.roots,
    st.roots_redirected,
    st.root_bytes,
    st.root_bytes_hc,
    st.root_bytes_hc as i64 - st.root_bytes as i64,
    st.cs_refs_redirected
  );
  md += "\nNode bytes by kind (length prefixes excluded):\n\n| kind | nodes | v3 | abs | delta | implicit | implicit B/node |\n|---|---:|---:|---:|---:|---:|---:|\n";
  for k in 0..9 {
    md += &format!(
      "| {} | {} | {} | {} | {} | {} | {:.2} |\n",
      KIND_NAMES[k],
      st.kind_nodes[k],
      st.kind_bytes[0][k],
      st.kind_bytes[1][k],
      st.kind_bytes[2][k],
      st.kind_bytes[3][k],
      if st.kind_nodes[k] == 0 {
        0.0
      } else {
        st.kind_bytes[3][k] as f64 / st.kind_nodes[k] as f64
      }
    );
  }
  md += "\nChild references per slot. Δ = parent − child − 1 (0 = the immediately preceding node); widths are TagN (`f = 0`) widths of Δ (1 B: Δ < 128, 2 B: < 16,512, 3 B: < 82,048, 5 B, 9 B). \"fresh\" = implicit under the post-order cursor (0 bytes); the explicit widths are for the other references.\n\n| slot | children | not backward | Δ = 0 | Δ 1 B | 2 B | 3 B | 5 B | 9 B | fresh | fresh % | explicit 1 B | 2 B | 3 B | 5 B | 9 B |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n";
  let mut tot = [0u64; 14];
  for s in 0..10 {
    let dw = st.slot_delta_w[s];
    let ew = st.slot_explicit_w[s];
    let row = [
      st.slot_children[s],
      st.slot_forward[s],
      st.slot_delta0[s],
      dw[0],
      dw[1],
      dw[2],
      dw[3],
      dw[4],
      st.slot_fresh[s],
      ew[0],
      ew[1],
      ew[2],
      ew[3],
      ew[4],
    ];
    for j in 0..14 {
      tot[j] += row[j];
    }
    md += &format!(
      "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
      SLOT_NAMES[s],
      row[0],
      row[1],
      row[2],
      row[3],
      row[4],
      row[5],
      row[6],
      row[7],
      row[8],
      pct(row[8], row[0]),
      row[9],
      row[10],
      row[11],
      row[12],
      row[13]
    );
  }
  md += &format!(
    "| **all** | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
    tot[0],
    tot[1],
    tot[2],
    tot[3],
    tot[4],
    tot[5],
    tot[6],
    tot[7],
    tot[8],
    pct(tot[8], tot[0]),
    tot[9],
    tot[10],
    tot[11],
    tot[12],
    tot[13]
  );
  md += &format!(
    "\nName references inside arenas (node names: binder, let, ref, prj, call-site): {} references; {} bytes as v3 `Tag0` global indices, {} as TagN global indices ({:+} bytes, {} of the file); {} distinct per arena (summed). With a per-arena local name table (count + distinct global indices + local indices, all TagN): {} bytes ({:+} vs TagN global, {} of the file).\n",
    st.name_refs,
    st.name_bytes_v3,
    st.name_bytes_tagn,
    st.name_bytes_tagn as i64 - st.name_bytes_v3 as i64,
    spct(st.name_bytes_tagn as i64 - st.name_bytes_v3 as i64, file),
    st.name_distinct,
    st.name_local_bytes,
    st.name_local_bytes as i64 - st.name_bytes_tagn as i64,
    spct(st.name_local_bytes as i64 - st.name_bytes_tagn as i64, file)
  );
  println!("{md}");
  Ok(())
}

// ---------------------------------------------------------------------------
// Integer census (`--int-census`): every f = 0 integer outside constant
// bodies, priced under Tag0, TagN and TagN with a 4-byte rung
// ---------------------------------------------------------------------------

/// TagN (`f = 0`) with one more rung: 1, 2, 3, 4, 5, 9 bytes (codes
/// `c = 0, 1, 2, 3` select 2, 3, 4, 8 following bytes).
fn tagn4_w(v: u64) -> usize {
  const R3: u64 = 82_048;
  const R4: u64 = R3 + (1 << 24);
  const R5: u64 = R4 + (1 << 32);
  if v < 128 {
    1
  } else if v < 16_512 {
    2
  } else if v < R3 {
    3
  } else if v < R4 {
    4
  } else if v < R5 {
    5
  } else {
    9
  }
}

const CENSUS_CLASSES: [&str; 17] = [
  "§1 blob count and lengths",
  "§2 constant count and lengths",
  "§3 hint count, rank deltas, fused hints",
  "§4 name count and component lengths",
  "§5 entry count and name keys",
  "§5 constant ranks",
  "§5 fused hints",
  "§5 metadata window lengths",
  "ConstantMetaInfo name indices",
  "ConstantMetaInfo counts and aux layout",
  "arena roots (type/value/rule)",
  "arena lengths",
  "arena node name indices (incl. mdata keys, OfName)",
  "arena explicit child deltas",
  "arena counts and call-site scalars",
  "ConstantMeta table counts and patches",
  "(unused)",
];

#[derive(Default, Clone, Copy)]
struct CensusRow {
  ints: u64,
  /// Integers in [82,048, 2^24): TagN 5 bytes, Tag0 4 bytes.
  in_gap: u64,
  tag0: u64,
  tagn: u64,
  tagn4: u64,
}

#[derive(Default)]
struct Census {
  rows: [CensusRow; 17],
  const_max_refs: usize,
  const_max_univs: usize,
  const_max_sharing: usize,
  consts_decoded: u64,
  windows: u64,
  window_mismatch: u64,
}

impl Census {
  fn add(&mut self, class: usize, v: u64) {
    let r = &mut self.rows[class];
    r.ints += 1;
    if (82_048..(1 << 24)).contains(&v) {
      r.in_gap += 1;
    }
    r.tag0 += tag0_w(v) as u64;
    r.tagn += tagn_w(v) as u64;
    r.tagn4 += tagn4_w(v) as u64;
  }

  fn idx_vec(&mut self, ix: &NameIndex, v: &[Address]) {
    self.add(9, v.len() as u64);
    for a in v {
      self.add(8, ix[a]);
    }
  }

  fn arena(&mut self, ix: &NameIndex, nodes: &[ExprMetaData]) {
    self.add(11, nodes.len() as u64);
    let masks = implicit_masks(nodes);
    for (i, n) in nodes.iter().enumerate() {
      if let Some(a) = node_name(n) {
        self.add(12, ix[a]);
      }
      let delta = |c: u64| (i as u64).wrapping_sub(1).wrapping_sub(c);
      for (s, (_, c)) in slots(n).into_iter().enumerate() {
        if masks[i] & (1 << s) == 0 {
          self.add(13, delta(c));
        }
      }
      for c in callsite_refs(n) {
        self.add(13, delta(c));
      }
      match n {
        ExprMetaData::Mdata { mdata, .. } => {
          self.add(14, mdata.len() as u64);
          for kv in mdata {
            self.add(14, kv.len() as u64);
            for (k, d) in kv {
              self.add(12, ix[k]);
              if let DataValue::OfName(a) = d {
                self.add(12, ix[a]);
              }
            }
          }
        },
        ExprMetaData::CallSite { entries, canon_meta, orig_head, .. } => {
          self.add(14, entries.len() as u64);
          for e in entries {
            match e {
              CallSiteEntry::Kept { canon_idx: x, .. }
              | CallSiteEntry::Collapsed { sharing_idx: x, .. } => {
                self.add(14, *x);
              },
            }
          }
          self.add(14, canon_meta.len() as u64);
          if let Some((s, _)) = orig_head {
            self.add(14, *s);
          }
        },
        ExprMetaData::EtaCallSite { n_synth, entries, canon_meta, .. } => {
          self.add(14, *n_synth);
          self.add(14, entries.len() as u64);
          for e in entries {
            match e {
              CallSiteEntry::Kept { canon_idx: x, .. }
              | CallSiteEntry::Collapsed { sharing_idx: x, .. } => {
                self.add(14, *x);
              },
            }
          }
          self.add(14, canon_meta.len() as u64);
        },
        _ => {},
      }
    }
  }

  fn meta(&mut self, ix: &NameIndex, cm: &ConstantMeta) {
    match &cm.info {
      ConstantMetaInfo::Empty => {},
      ConstantMetaInfo::Def { name, lvls, all, ctx, arena, .. } => {
        self.add(8, ix[name]);
        self.idx_vec(ix, lvls);
        self.idx_vec(ix, all);
        self.idx_vec(ix, ctx);
        self.arena(ix, &arena.nodes);
      },
      ConstantMetaInfo::Axio { name, lvls, arena, .. }
      | ConstantMetaInfo::Quot { name, lvls, arena, .. } => {
        self.add(8, ix[name]);
        self.idx_vec(ix, lvls);
        self.arena(ix, &arena.nodes);
      },
      ConstantMetaInfo::Indc { name, lvls, ctors, all, ctx, arena, .. } => {
        self.add(8, ix[name]);
        self.idx_vec(ix, lvls);
        self.idx_vec(ix, ctors);
        self.idx_vec(ix, all);
        self.idx_vec(ix, ctx);
        self.arena(ix, &arena.nodes);
      },
      ConstantMetaInfo::Ctor { name, lvls, induct, arena, .. } => {
        self.add(8, ix[name]);
        self.idx_vec(ix, lvls);
        self.add(8, ix[induct]);
        self.arena(ix, &arena.nodes);
      },
      ConstantMetaInfo::Rec {
        name,
        lvls,
        rules,
        all,
        ctx,
        arena,
        rule_roots,
        ..
      } => {
        self.add(8, ix[name]);
        self.idx_vec(ix, lvls);
        self.idx_vec(ix, rules);
        self.idx_vec(ix, all);
        self.idx_vec(ix, ctx);
        self.arena(ix, &arena.nodes);
        self.add(9, rule_roots.len() as u64);
      },
      ConstantMetaInfo::Muts { all, aux_layout } => {
        self.add(9, all.len() as u64);
        for cls in all {
          self.idx_vec(ix, cls);
        }
        if let Some(l) = aux_layout {
          self.add(9, l.perm.len() as u64);
          for &p in &l.perm {
            self.add(9, p as u64);
          }
          self.add(9, l.source_ctor_counts.len() as u64);
          for &c in &l.source_ctor_counts {
            self.add(9, c as u64);
          }
          self.add(9, l.evaporated.len() as u64);
        }
      },
    }
    for r in roots_of(&cm.info) {
      self.add(10, r);
    }
    self.add(15, cm.meta_sharing.len() as u64);
    self.add(15, cm.meta_refs.len() as u64);
    self.add(15, cm.meta_univs.len() as u64);
    self.add(15, cm.univ_patches.len() as u64);
    for p in &cm.univ_patches {
      self.add(15, p.arena_idx);
      self.add(15, p.univ_idxs.len() as u64);
      for &u in &p.univ_idxs {
        self.add(15, u);
      }
    }
  }
}

fn fused_opt_hint(h: Option<ReducibilityHints>) -> u64 {
  match h {
    None => 0,
    Some(ReducibilityHints::Opaque) => 1,
    Some(ReducibilityHints::Abbrev) => 2,
    Some(ReducibilityHints::Regular(x)) => u64::from(x) + 3,
  }
}

fn fused_hint(h: &ReducibilityHints) -> u64 {
  fused_opt_hint(Some(*h)) - 1
}

/// Run the census over a parsed file and render it.
fn int_census(path: &str, mmap: &[u8]) -> Result<String, String> {
  let (index, names) = Env::parse_lazy_index_with_names(mmap)?;
  let ix: NameIndex = index
    .name_reverse_index
    .iter()
    .enumerate()
    .map(|(i, a)| (a.clone(), i as u64))
    .collect();
  let const_addrs: Vec<Address> =
    index.consts.iter().map(|c| c.addr.clone()).collect();
  let mut c = Census::default();
  // §1-§4.
  c.add(0, index.blobs.len() as u64);
  for (_, b) in &index.blobs {
    c.add(0, b.len() as u64);
  }
  c.add(1, index.consts.len() as u64);
  for s in &index.consts {
    c.add(1, s.len as u64);
    if let Ok(k) = Constant::get(&mut &mmap[s.offset..s.offset + s.len]) {
      c.consts_decoded += 1;
      c.const_max_refs = c.const_max_refs.max(k.refs.len());
      c.const_max_univs = c.const_max_univs.max(k.univs.len());
      c.const_max_sharing = c.const_max_sharing.max(k.sharing.len());
    }
  }
  c.add(2, index.hints.len() as u64);
  let mut ranked: Vec<(u64, u64)> = index
    .hints
    .iter()
    .map(|(a, h)| {
      (
        const_addrs.binary_search(a).map_or(u64::MAX, |r| r as u64),
        fused_hint(h),
      )
    })
    .collect();
  ranked.sort_unstable();
  let mut prev = 0u64;
  for (rank, h) in ranked {
    c.add(2, rank + 1 - prev);
    c.add(2, h);
    prev = rank + 1;
  }
  c.add(3, index.name_reverse_index.len() as u64);
  for a in &index.name_reverse_index {
    if let Some(n) = names.get(a) {
      match n.as_data() {
        ix_common::env::NameData::Str(_, s, _) => c.add(3, s.len() as u64),
        ix_common::env::NameData::Num(_, n, _) => {
          c.add(3, n.to_le_bytes().len() as u64);
        },
        ix_common::env::NameData::Anonymous(_) => {},
      }
    }
  }
  // §5.
  c.add(4, index.named.len() as u64);
  let (mut scratch, mut entry_buf) = (Vec::new(), Vec::new());
  let mut cursor = NamedMetaCursor::open(mmap, &index)?;
  while let Some((name_addr, named)) = cursor.next_entry()? {
    c.add(4, ix[&name_addr]);
    c.add(
      5,
      const_addrs.binary_search(&named.addr).map_or(u64::MAX, |r| r as u64),
    );
    c.add(6, fused_opt_hint(named.hints()));
    entry_buf.clear();
    put_named_indexed(&named, &ix, &const_addrs, &mut scratch, &mut entry_buf)?;
    c.add(7, scratch.len() as u64);
    // Self-check: the window is exactly the census integers (TagN) plus
    // the non-integer bytes.
    let before: u64 = c.rows[8..16].iter().map(|r| r.tagn).sum();
    let meta = named.meta();
    c.meta(&ix, &meta);
    let mut nonint = meta_nonint_bytes(&meta) + 1;
    if let Some((_, o)) = named.original() {
      c.meta(&ix, &o);
      nonint += 32 + meta_nonint_bytes(&o);
    }
    let after: u64 = c.rows[8..16].iter().map(|r| r.tagn).sum();
    c.windows += 1;
    if after - before + nonint != scratch.len() as u64 {
      c.window_mismatch += 1;
    }
  }
  let file = mmap.len() as u64;
  let mut md = format!(
    "## Integer census (f = 0, outside constant bodies): `{path}`\n\n- File {file} bytes; {} names; {} constants ({} decoded: max refs table {}, max univs table {}, max sharing table {}).\n- Self-check: {} of {} §5 windows equal TagN-priced census integers plus non-integer bytes ({} mismatches).\n- Widths: Tag0 (v3); TagN as specified (1, 2, 3, 5, 9 bytes; 5 bytes from 82,048); TagN with a 4-byte rung (1, 2, 3, 4, 5, 9; 4 bytes for [82,048, 16,859,264)). \"In [82,048, 2^24)\" are the integers TagN writes one byte longer than Tag0.\n\n| field class | integers | in [82,048, 2^24) | Tag0 bytes | TagN bytes | TagN − Tag0 | TagN with 4-byte rung | rung saves |\n|---|---:|---:|---:|---:|---:|---:|---:|\n",
    index.name_reverse_index.len(),
    index.consts.len(),
    c.consts_decoded,
    c.const_max_refs,
    c.const_max_univs,
    c.const_max_sharing,
    c.windows - c.window_mismatch,
    c.windows,
    c.window_mismatch
  );
  let mut t = CensusRow::default();
  for (k, r) in c.rows.iter().enumerate().take(16) {
    t.ints += r.ints;
    t.in_gap += r.in_gap;
    t.tag0 += r.tag0;
    t.tagn += r.tagn;
    t.tagn4 += r.tagn4;
    md += &format!(
      "| {} | {} | {} | {} | {} | {:+} | {} | {} |\n",
      CENSUS_CLASSES[k],
      r.ints,
      r.in_gap,
      r.tag0,
      r.tagn,
      r.tagn as i64 - r.tag0 as i64,
      r.tagn4,
      r.tagn - r.tagn4
    );
  }
  md += &format!(
    "| **all** | {} | {} | {} | {} | {:+} ({}) | {} | {} ({}) |\n",
    t.ints,
    t.in_gap,
    t.tag0,
    t.tagn,
    t.tagn as i64 - t.tag0 as i64,
    spct(t.tagn as i64 - t.tag0 as i64, file),
    t.tagn4,
    t.tagn - t.tagn4,
    pct(t.tagn - t.tagn4, file)
  );
  Ok(md)
}

/// Non-integer bytes of a `ConstantMeta` (tags, raw addresses, booleans,
/// expression and universe payloads): with the census integers priced in
/// TagN this must add up to the production writer's bytes.
fn meta_nonint_bytes(cm: &ConstantMeta) -> u64 {
  let arena = |nodes: &[ExprMetaData]| -> u64 {
    let mut b = nodes.len() as u64;
    for n in nodes {
      match n {
        ExprMetaData::Mdata { mdata, .. } => {
          for kv in mdata {
            for (_, d) in kv {
              b += 1
                + match d {
                  DataValue::OfBool(_) => 1,
                  DataValue::OfName(_) => 0,
                  _ => 32,
                };
            }
          }
        },
        ExprMetaData::CallSite { entries, .. } => {
          b += entries.len() as u64 + 1;
        },
        ExprMetaData::EtaCallSite { entries, .. } => {
          b += entries.len() as u64;
        },
        _ => {},
      }
    }
    b
  };
  let mut b = 1 + arena_of(&cm.info).map_or(0, |a| arena(&a.nodes));
  if let ConstantMetaInfo::Muts { aux_layout, .. } = &cm.info {
    b += 1 + aux_layout.as_ref().map_or(0, |l| l.evaporated.len() as u64);
  }
  for e in &cm.meta_sharing {
    let mut buf = Vec::new();
    put_expr(e, &mut buf);
    b += buf.len() as u64;
  }
  b += 32 * cm.meta_refs.len() as u64;
  for u in &cm.meta_univs {
    let mut buf = Vec::new();
    put_univ(u, &mut buf);
    b += buf.len() as u64;
  }
  b
}
