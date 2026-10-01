//! Arena-based metadata for preserving Lean source information.
//!
//! Metadata types use Address internally, but serialize with u64 indices
//! into a global name index for space efficiency.
//!
//! The arena stores metadata as a tree of ExprMetaData nodes, allocated
//! bottom-up (children before parents). Each ConstantMeta variant stores
//! an ExprMeta arena plus root indices for each expression position.

#![allow(clippy::cast_possible_truncation)]

use std::collections::HashMap;
use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{self, BinderInfo, Name};

use super::env::AuxLayout;
use super::expr::Expr;
use super::serialize::{get_expr, put_expr};
use super::tag::TagN;
use super::univ::{Univ, get_univ, put_univ};

// ===========================================================================
// Types (use Address internally)
// ===========================================================================

/// Key-value map for Lean.Expr.mdata
pub type KVMap = Vec<(Address, DataValue)>;

/// Entry in a `CallSite` metadata node, representing one source-order argument.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CallSiteEntry {
  /// Argument exists in canonical form at App-spine position `canon_idx`.
  /// `meta` is the arena index for this argument's metadata subtree.
  Kept { canon_idx: u64, meta: u64 },
  /// Argument was collapsed. Expression stored in `ConstantMeta.meta_sharing[sharing_idx]`.
  /// `meta` is the arena index for this argument's metadata subtree
  /// (may differ from the representative's metadata — different names, refs, etc.).
  Collapsed { sharing_idx: u64, meta: u64 },
}

/// Arena node for per-expression metadata.
///
/// Nodes are allocated bottom-up (children before parents) in the arena.
/// Arena indices are u64 values pointing into `ExprMeta.nodes`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExprMetaData {
  /// Leaf node: Var, Sort, Nat, Str (no metadata)
  Leaf,
  /// Application: children = [fun, arg]
  App { children: [u64; 2] },
  /// Lambda/ForAll binder: children = [type, body]
  Binder { name: Address, info: BinderInfo, children: [u64; 2] },
  /// Let binder: children = [type, value, body]
  LetBinder { name: Address, children: [u64; 3] },
  /// Const reference (Ref or Rec): leaf in the arena
  Ref { name: Address },
  /// Projection: child = struct value
  Prj { struct_name: Address, child: u64 },
  /// Mdata wrapper: always a separate node, never absorbed into Binder/Ref/Prj
  Mdata { mdata: Vec<KVMap>, child: u64 },
  /// Surgered call-site. Replaces the entire App-spine metadata chain
  /// (outermost App down to the Ref head) with a single node. Entries are
  /// in SOURCE order. The corresponding Ixon expression is a normal App
  /// telescope — only the metadata changes shape.
  ///
  /// Sits at the outermost position so both compiler and decompiler see it
  /// first, avoiding the need to recurse through App nodes to discover surgery.
  CallSite {
    /// Name address of the referenced auxiliary (doubles as Ref name metadata).
    name: Address,
    /// Source-order entries for the argument telescope.
    entries: Vec<CallSiteEntry>,
    /// Canonical-order metadata roots, one per argument in the IXON App spine.
    ///
    /// This is separate from `entries` because some source arguments are
    /// represented by `Collapsed` entries even though compile-side surgery
    /// synthesized a canonical replacement argument. Kernel ingress needs the
    /// replacement argument's metadata by canonical position, while decompile
    /// needs the source-order `entries` to reconstruct the original spine.
    canon_meta: Vec<u64>,
    /// `Some((sharing_idx, meta))` when the call-site HEAD itself was
    /// rewritten (evaporated-aux recursors: `<all0>.rec_N` aliased to the
    /// external inductive's recursor, whose universe-level arity differs).
    /// Points at the ORIGINAL head expression in
    /// `ConstantMeta.meta_sharing`, exactly like a `Collapsed` argument —
    /// decompile uses it to restore the source head (name + original level
    /// args) instead of reading levels off the stored canonical head.
    orig_head: Option<(u64, u64)>,
  },
  /// Eta adapter for a partial plan-bearing reference. The corresponding
  /// Ixon expression is a synthesized lambda telescope whose body is a normal
  /// canonical `CallSite`. Decompile strips `n_synth` lambdas and rebuilds
  /// only the originally-applied source prefix from `entries`.
  ///
  /// `wrapper_meta` points at the ordinary Binder/CallSite metadata tree for
  /// the synthesized wrapper. Kernel meta-ingress follows it so binder-type
  /// references retain complete metadata; source decompile intentionally
  /// discards that wrapper tree.
  EtaCallSite {
    n_synth: u64,
    name: Address,
    entries: Vec<CallSiteEntry>,
    canon_meta: Vec<u64>,
    wrapper_meta: u64,
  },
}

/// Arena for expression metadata within a single constant.
///
/// Nodes are appended bottom-up. Arena indices are stable because the arena
/// is append-only and never reset during a constant's compilation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExprMeta {
  pub nodes: Vec<ExprMetaData>,
}

impl ExprMeta {
  /// Allocate a new node in the arena, returning its index.
  pub fn alloc(&mut self, node: ExprMetaData) -> u64 {
    let idx = self.nodes.len() as u64;
    self.nodes.push(node);
    idx
  }
}

/// Per-variant metadata payload for a constant.
///
/// Each variant stores an ExprMeta arena covering all expressions in
/// that constant, plus root indices pointing into the arena for each
/// expression position (type, value, rule RHS, etc.).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum ConstantMetaInfo {
  #[default]
  Empty,
  Def {
    name: Address,
    lvls: Vec<Address>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
    value_root: u64,
  },
  Axio {
    name: Address,
    lvls: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
  },
  Quot {
    name: Address,
    lvls: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
  },
  Indc {
    name: Address,
    lvls: Vec<Address>,
    ctors: Vec<Address>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
  },
  Ctor {
    name: Address,
    lvls: Vec<Address>,
    induct: Address,
    arena: ExprMeta,
    type_root: u64,
  },
  Rec {
    name: Address,
    lvls: Vec<Address>,
    rules: Vec<Address>,
    all: Vec<Address>,
    ctx: Vec<Address>,
    arena: ExprMeta,
    type_root: u64,
    rule_roots: Vec<u64>,
  },
  /// Synthetic metadata for a mutual block. Each inner `Vec` is an equivalence
  /// class of alpha-equivalent constants (same MutConst index), containing the
  /// name-hash addresses of all names in that class.
  ///
  /// `aux_layout` is the nested-auxiliary permutation sidecar for blocks
  /// that underwent nested-inductive expansion. Used by decompile to
  /// reconstruct the canonical aux layout without a fresh source walk
  /// (see `docs/ix_canonicity.md` §10.2 / §17.3). `None` for blocks
  /// with no nested auxes (the common case).
  ///
  /// The aux_layout is *metadata* — it lives in [`ConstantMeta`] (never
  /// entering any constant's content hash) and survives round-trip
  /// through [`Env::put`] / [`Env::get`] via the Muts variant below.
  Muts {
    all: Vec<Vec<Address>>,
    aux_layout: Option<AuxLayout>,
  },
}

impl ConstantMetaInfo {
  /// Returns a short kind name for diagnostics.
  pub fn kind_name(&self) -> &'static str {
    match self {
      Self::Empty => "empty",
      Self::Def { .. } => "def",
      Self::Axio { .. } => "axio",
      Self::Quot { .. } => "quot",
      Self::Indc { .. } => "indc",
      Self::Ctor { .. } => "ctor",
      Self::Rec { .. } => "rec",
      Self::Muts { .. } => "muts",
    }
  }
}

/// Per-occurrence original level-spelling patch (canonicity §10.6):
/// keyed by the metadata-arena node index of a `sort`/`ref`/`recur`
/// occurrence whose original level-index list differs from its
/// canonical one, carrying the FULL original list in the VIRTUAL univ
/// index space (idx < `univs.len()` → primary table entry, already
/// canonical; idx ≥ `univs.len()` → `meta_univs[idx - univs.len()]`,
/// the original spelling). `sort` occurrences carry a 1-element list.
/// Presentation-only: read by the decompiler and by META kernel
/// ingress (the stage-2 decoration source); anon ingress — the trust
/// boundary — never reads patches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnivPatch {
  pub arena_idx: u64,
  pub univ_idxs: Vec<u64>,
}

/// Per-constant metadata wrapper: variant payload + extension tables.
///
/// Extension tables (`meta_sharing`, `meta_refs`, `meta_univs`) form a
/// virtual address space extending the primary `Constant` tables. They are
/// used by `CallSite` nodes in the metadata arena for call-site surgery
/// roundtrip: collapsed argument expressions reference these tables via
/// `Share(idx)`, `Ref(idx)`, and universe indices — and by `univ_patches`
/// for original level spellings (canonicity §10.6).
///
/// At decompile time, extension tables are appended to the block cache,
/// creating a contiguous address space.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstantMeta {
  pub info: ConstantMetaInfo,
  /// Compiled Ixon expressions for collapsed call-site arguments.
  /// May contain `Share(idx)` references into the extended sharing table.
  pub meta_sharing: Vec<Arc<Expr>>,
  /// Extension refs table (addresses referenced by collapsed arg expressions).
  pub meta_refs: Vec<Address>,
  /// Extension univs table (universe terms in collapsed arg expressions,
  /// and original level spellings referenced by `univ_patches`).
  pub meta_univs: Vec<Arc<Univ>>,
  /// Original level-spelling patches, keyed by metadata-arena index
  /// (canonicity §10.6). Empty until the stage-2 compiler emits them.
  pub univ_patches: Vec<UnivPatch>,
}

impl Default for ConstantMeta {
  fn default() -> Self {
    Self {
      info: ConstantMetaInfo::Empty,
      meta_sharing: Vec::new(),
      meta_refs: Vec::new(),
      meta_univs: Vec::new(),
      univ_patches: Vec::new(),
    }
  }
}

impl ConstantMeta {
  /// Wrap a `ConstantMetaInfo` payload (no extension tables).
  pub fn new(info: ConstantMetaInfo) -> Self {
    Self {
      info,
      meta_sharing: Vec::new(),
      meta_refs: Vec::new(),
      meta_univs: Vec::new(),
      univ_patches: Vec::new(),
    }
  }

  /// Whether this metadata has any wrapper extension payload (surgery
  /// tables or level-spelling patches).
  pub fn has_extensions(&self) -> bool {
    !self.meta_sharing.is_empty()
      || !self.meta_refs.is_empty()
      || !self.meta_univs.is_empty()
      || !self.univ_patches.is_empty()
  }

  /// Enumerate every external address this metadata references,
  /// partitioned by the table that resolves it:
  ///
  /// - `names`: name-component addresses (resolved against
  ///   `Env.names`) — the variant's `name`/`lvls`/`all`/`ctx`/...
  ///   fields, arena binder/ref/proj/call-site names, and KVMap keys
  ///   plus `DataValue::OfName` payloads;
  /// - `blobs`: raw-byte payload addresses (`DataValue`
  ///   strings/nats/ints/syntax, resolved against `Env.blobs`);
  /// - `dag`: `meta_refs` extension-table addresses — constants or
  ///   blobs referenced by collapsed call-site argument expressions,
  ///   i.e. genuine value-DAG edges the primary `Constant.refs` walk
  ///   cannot see.
  ///
  /// Used by `Env::prune_to_closure` to carry a bundle's display
  /// metadata completely. Duplicates are not filtered; callers dedup.
  pub fn collect_deps(
    &self,
    names: &mut Vec<Address>,
    blobs: &mut Vec<Address>,
    dag: &mut Vec<Address>,
  ) {
    use ConstantMetaInfo as I;
    let mut arena: Option<&ExprMeta> = None;
    match &self.info {
      I::Empty => {},
      I::Def { name, lvls, all, ctx, arena: a, .. } => {
        names.push(name.clone());
        names.extend(lvls.iter().cloned());
        names.extend(all.iter().cloned());
        names.extend(ctx.iter().cloned());
        arena = Some(a);
      },
      I::Axio { name, lvls, arena: a, .. }
      | I::Quot { name, lvls, arena: a, .. } => {
        names.push(name.clone());
        names.extend(lvls.iter().cloned());
        arena = Some(a);
      },
      I::Indc { name, lvls, ctors, all, ctx, arena: a, .. } => {
        names.push(name.clone());
        names.extend(lvls.iter().cloned());
        names.extend(ctors.iter().cloned());
        names.extend(all.iter().cloned());
        names.extend(ctx.iter().cloned());
        arena = Some(a);
      },
      I::Ctor { name, lvls, induct, arena: a, .. } => {
        names.push(name.clone());
        names.extend(lvls.iter().cloned());
        names.push(induct.clone());
        arena = Some(a);
      },
      I::Rec { name, lvls, rules, all, ctx, arena: a, .. } => {
        names.push(name.clone());
        names.extend(lvls.iter().cloned());
        names.extend(rules.iter().cloned());
        names.extend(all.iter().cloned());
        names.extend(ctx.iter().cloned());
        arena = Some(a);
      },
      I::Muts { all, .. } => {
        for class in all {
          names.extend(class.iter().cloned());
        }
      },
    }
    if let Some(a) = arena {
      for node in &a.nodes {
        match node {
          ExprMetaData::Leaf | ExprMetaData::App { .. } => {},
          ExprMetaData::Binder { name, .. }
          | ExprMetaData::LetBinder { name, .. }
          | ExprMetaData::Ref { name }
          | ExprMetaData::CallSite { name, .. }
          | ExprMetaData::EtaCallSite { name, .. } => names.push(name.clone()),
          ExprMetaData::Prj { struct_name, .. } => {
            names.push(struct_name.clone());
          },
          ExprMetaData::Mdata { mdata, .. } => {
            for kv in mdata {
              for (key, value) in kv {
                names.push(key.clone());
                match value {
                  DataValue::OfName(a) => names.push(a.clone()),
                  DataValue::OfString(a)
                  | DataValue::OfNat(a)
                  | DataValue::OfInt(a)
                  | DataValue::OfSyntax(a) => blobs.push(a.clone()),
                  DataValue::OfBool(_) => {},
                }
              }
            }
          },
        }
      }
    }
    dag.extend(self.meta_refs.iter().cloned());
  }

  /// Delegate indexed serialization to the inner enum, then serialize
  /// extension tables.
  pub fn put_with(
    &self,
    idx: NamePut<'_>,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    self.info.put_with(idx, buf)?;
    // Extension tables (backward-compatible: 0-length for old constants)
    put_vec_len(self.meta_sharing.len(), buf);
    for expr in &self.meta_sharing {
      put_expr(expr, buf);
    }
    put_vec_len(self.meta_refs.len(), buf);
    for addr in &self.meta_refs {
      put_address_raw(addr, buf);
    }
    put_vec_len(self.meta_univs.len(), buf);
    for univ in &self.meta_univs {
      put_univ(univ, buf);
    }
    // Level-spelling patches (canonicity §10.6): per entry, TagN
    // arena_idx, TagN len, TagN virtual univ indices.
    put_vec_len(self.univ_patches.len(), buf);
    for patch in &self.univ_patches {
      TagN::put(0, 0, patch.arena_idx, buf);
      put_vec_len(patch.univ_idxs.len(), buf);
      for idx in &patch.univ_idxs {
        TagN::put(0, 0, *idx, buf);
      }
    }
    Ok(())
  }

  /// Self-contained encoding: name references as raw 32-byte addresses,
  /// no index required. This is the demoted in-memory form
  /// (see `env::DEMOTE`), NOT the `.ixe` named-section encoding —
  /// `Env::put` re-encodes through the name index.
  pub fn put_raw(&self, buf: &mut Vec<u8>) -> Result<(), String> {
    self.put_with(NamePut::Raw, buf)
  }

  /// Decode the [`Self::put_raw`] encoding.
  pub fn get_raw(buf: &mut &[u8]) -> Result<Self, String> {
    Self::get_with(buf, NameGet::Raw)
  }

  /// Delegate indexed deserialization, then deserialize extension tables.
  pub fn get_with(buf: &mut &[u8], rev: NameGet<'_>) -> Result<Self, String> {
    let info = ConstantMetaInfo::get_with(buf, rev)?;
    // Extension tables: always present (put_with always writes them,
    // even when empty — three zero-length vectors).
    let sharing_len = get_vec_len(buf)?;
    let mut meta_sharing = Vec::with_capacity(sharing_len);
    for _ in 0..sharing_len {
      meta_sharing.push(get_expr(buf)?);
    }
    let refs_len = get_vec_len(buf)?;
    let mut meta_refs = Vec::with_capacity(refs_len);
    for _ in 0..refs_len {
      meta_refs.push(get_address_raw(buf)?);
    }
    let univs_len = get_vec_len(buf)?;
    let mut meta_univs = Vec::with_capacity(univs_len);
    for _ in 0..univs_len {
      meta_univs.push(get_univ(buf)?);
    }
    let patches_len = get_vec_len(buf)?;
    let mut univ_patches = Vec::with_capacity(patches_len);
    for _ in 0..patches_len {
      let arena_idx = TagN::get(0, buf)?.value;
      let idxs_len = get_vec_len(buf)?;
      let mut univ_idxs = Vec::with_capacity(idxs_len);
      for _ in 0..idxs_len {
        univ_idxs.push(TagN::get(0, buf)?.value);
      }
      univ_patches.push(UnivPatch { arena_idx, univ_idxs });
    }
    Ok(Self { info, meta_sharing, meta_refs, meta_univs, univ_patches })
  }
}

/// Data values for KVMap metadata.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DataValue {
  OfString(Address),
  OfBool(bool),
  OfName(Address),
  OfNat(Address),
  OfInt(Address),
  OfSyntax(Address),
}

/// Resolve an Ixon KVMap (address-based) to Lean-level MData (name/value pairs).
///
/// Used by kernel ingress to convert expression metadata from the
/// content-addressed Ixon representation to the named kernel representation.
pub fn resolve_kvmap(
  kvm: &KVMap,
  ixon_env: &super::env::Env,
) -> Vec<(Name, env::DataValue)> {
  kvm
    .iter()
    .filter_map(|(addr, dv)| {
      let name = ixon_env.get_name(addr)?;
      let resolved = match dv {
        DataValue::OfString(a) => {
          let bytes = ixon_env.get_blob(a)?;
          env::DataValue::OfString(String::from_utf8(bytes).ok()?)
        },
        DataValue::OfBool(b) => env::DataValue::OfBool(*b),
        DataValue::OfName(a) => {
          let n = ixon_env.get_name(a)?;
          env::DataValue::OfName(n)
        },
        DataValue::OfNat(a) => {
          let bytes = ixon_env.get_blob(a)?;
          env::DataValue::OfNat(bignat::Nat::from_le_bytes(&bytes))
        },
        DataValue::OfInt(a) => {
          let bytes = ixon_env.get_blob(a)?;
          let int = deser_int(&bytes)?;
          env::DataValue::OfInt(int)
        },
        DataValue::OfSyntax(a) => {
          // Deserialize the Syntax tree from its blob. Mirrors
          // `compile.rs::serialize_syntax_inner`; the deserializer only
          // needs `Env::get_blob` + `Env::get_name`, so it lives here
          // rather than in `decompile.rs` (which depends on CompileState).
          let bytes = ixon_env.get_blob(a)?;
          let mut buf = bytes.as_slice();
          let syn = deser_syntax(&mut buf, ixon_env)?;
          env::DataValue::OfSyntax(Box::new(syn))
        },
      };
      Some((name, resolved))
    })
    .collect()
}

// ===========================================================================
// Syntax deserialization from blobs
// ===========================================================================
//
// These mirror the compile-side `serialize_syntax_inner` /
// `serialize_source_info` / `serialize_substring` / `serialize_preresolved`
// in `src/ix/compile.rs`. They live here (not `decompile.rs`) so that
// `resolve_kvmap` can materialize `DataValue::OfSyntax` entries during
// kernel ingress — the decompile-side helpers depend on `CompileState`,
// which isn't available in the ingress path. All we need is the `Env`
// (for blob + name lookups).

fn deser_u8(buf: &mut &[u8]) -> Option<u8> {
  let (&x, rest) = buf.split_first()?;
  *buf = rest;
  Some(x)
}

fn deser_tag0(buf: &mut &[u8]) -> Option<u64> {
  TagN::get(0, buf).ok().map(|t| t.value)
}

fn deser_addr(buf: &mut &[u8]) -> Option<Address> {
  if buf.len() < 32 {
    return None;
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).ok()
}

/// Deserialize a signed `Int` from bytes (mirrors compile-side encoding in
/// `compile_data_value` / `DataValue::OfInt`).
fn deser_int(bytes: &[u8]) -> Option<env::Int> {
  let (&tag, rest) = bytes.split_first()?;
  match tag {
    0 => Some(env::Int::OfNat(bignat::Nat::from_le_bytes(rest))),
    1 => Some(env::Int::NegSucc(bignat::Nat::from_le_bytes(rest))),
    _ => None,
  }
}

fn deser_substring(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::Substring> {
  let str_addr = deser_addr(buf)?;
  let s = String::from_utf8(ixon_env.get_blob(&str_addr)?).ok()?;
  let start_pos = bignat::Nat::from(deser_tag0(buf)?);
  let stop_pos = bignat::Nat::from(deser_tag0(buf)?);
  Some(env::Substring { str: s, start_pos, stop_pos })
}

fn deser_source_info(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::SourceInfo> {
  match deser_u8(buf)? {
    0 => {
      let leading = deser_substring(buf, ixon_env)?;
      let leading_pos = bignat::Nat::from(deser_tag0(buf)?);
      let trailing = deser_substring(buf, ixon_env)?;
      let trailing_pos = bignat::Nat::from(deser_tag0(buf)?);
      Some(env::SourceInfo::Original(
        leading,
        leading_pos,
        trailing,
        trailing_pos,
      ))
    },
    1 => {
      let start = bignat::Nat::from(deser_tag0(buf)?);
      let end = bignat::Nat::from(deser_tag0(buf)?);
      let canonical = deser_u8(buf)? != 0;
      Some(env::SourceInfo::Synthetic(start, end, canonical))
    },
    2 => Some(env::SourceInfo::None),
    _ => None,
  }
}

fn deser_preresolved(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::SyntaxPreresolved> {
  match deser_u8(buf)? {
    0 => {
      let name = ixon_env.get_name(&deser_addr(buf)?)?;
      Some(env::SyntaxPreresolved::Namespace(name))
    },
    1 => {
      let name = ixon_env.get_name(&deser_addr(buf)?)?;
      let count = deser_tag0(buf)? as usize;
      let mut fields = Vec::with_capacity(count);
      for _ in 0..count {
        let addr = deser_addr(buf)?;
        fields.push(String::from_utf8(ixon_env.get_blob(&addr)?).ok()?);
      }
      Some(env::SyntaxPreresolved::Decl(name, fields))
    },
    _ => None,
  }
}

fn deser_syntax(
  buf: &mut &[u8],
  ixon_env: &super::env::Env,
) -> Option<env::Syntax> {
  match deser_u8(buf)? {
    0 => Some(env::Syntax::Missing),
    1 => {
      let info = deser_source_info(buf, ixon_env)?;
      let kind = ixon_env.get_name(&deser_addr(buf)?)?;
      let arg_count = deser_tag0(buf)? as usize;
      let mut args = Vec::with_capacity(arg_count);
      for _ in 0..arg_count {
        args.push(deser_syntax(buf, ixon_env)?);
      }
      Some(env::Syntax::Node(info, kind, args))
    },
    2 => {
      let info = deser_source_info(buf, ixon_env)?;
      let val_addr = deser_addr(buf)?;
      let val = String::from_utf8(ixon_env.get_blob(&val_addr)?).ok()?;
      Some(env::Syntax::Atom(info, val))
    },
    3 => {
      let info = deser_source_info(buf, ixon_env)?;
      let raw_val = deser_substring(buf, ixon_env)?;
      let val = ixon_env.get_name(&deser_addr(buf)?)?;
      let pr_count = deser_tag0(buf)? as usize;
      let mut preresolved = Vec::with_capacity(pr_count);
      for _ in 0..pr_count {
        preresolved.push(deser_preresolved(buf, ixon_env)?);
      }
      Some(env::Syntax::Ident(info, raw_val, val, preresolved))
    },
    _ => None,
  }
}

// ===========================================================================
// Serialization helpers
// ===========================================================================

fn put_u8(x: u8, buf: &mut Vec<u8>) {
  buf.push(x);
}

fn get_u8(buf: &mut &[u8]) -> Result<u8, String> {
  match buf.split_first() {
    Some((&x, rest)) => {
      *buf = rest;
      Ok(x)
    },
    None => Err("get_u8: EOF".to_string()),
  }
}

fn put_bool(x: bool, buf: &mut Vec<u8>) {
  buf.push(if x { 1 } else { 0 });
}

fn get_bool(buf: &mut &[u8]) -> Result<bool, String> {
  match get_u8(buf)? {
    0 => Ok(false),
    1 => Ok(true),
    x => Err(format!("get_bool: invalid {x}")),
  }
}

/// Serialize a raw 32-byte address (for blob addresses not in the name index).
fn put_address_raw(addr: &Address, buf: &mut Vec<u8>) {
  buf.extend_from_slice(addr.as_bytes());
}

/// Deserialize a raw 32-byte address.
fn get_address_raw(buf: &mut &[u8]) -> Result<Address, String> {
  if buf.len() < 32 {
    return Err(format!("get_address_raw: need 32 bytes, have {}", buf.len()));
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes)
    .map_err(|_e| "get_address_raw: invalid".to_string())
}

fn put_u64(x: u64, buf: &mut Vec<u8>) {
  TagN::put(0, 0, x, buf);
}

fn get_u64(buf: &mut &[u8]) -> Result<u64, String> {
  Ok(TagN::get(0, buf)?.value)
}

pub(super) fn put_vec_len(len: usize, buf: &mut Vec<u8>) {
  TagN::put(0, 0, len as u64, buf);
}

pub(super) fn get_vec_len(buf: &mut &[u8]) -> Result<usize, String> {
  Ok(TagN::get(0, buf)?.value as usize)
}

// ===========================================================================
// BinderInfo and ReducibilityHints serialization
// ===========================================================================

/// Extension trait for serializing/deserializing small env-side enums whose
/// types live in `ix-types` (so we can't define inherent impls here).
pub trait IxonByteSerde: Sized {
  fn put_ser(&self, buf: &mut Vec<u8>);
  fn get_ser(buf: &mut &[u8]) -> Result<Self, String>;
}

impl IxonByteSerde for BinderInfo {
  fn put_ser(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Default => put_u8(0, buf),
      Self::Implicit => put_u8(1, buf),
      Self::StrictImplicit => put_u8(2, buf),
      Self::InstImplicit => put_u8(3, buf),
    }
  }

  fn get_ser(buf: &mut &[u8]) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Default),
      1 => Ok(Self::Implicit),
      2 => Ok(Self::StrictImplicit),
      3 => Ok(Self::InstImplicit),
      x => Err(format!("BinderInfo::get: invalid {x}")),
    }
  }
}

// `ReducibilityHints` has no `IxonByteSerde` impl: its only wire home
// is the env-level §3 section, which fuses the variant and height into
// a single TagN value (see `serialize.rs::fuse_hint`).

// ===========================================================================
// Indexed serialization (Address -> u64 index)
// ===========================================================================

/// Name index for serialization: Address -> u64
pub type NameIndex = HashMap<Address, u64>;

/// Reverse name index for deserialization: position -> Address
pub type NameReverseIndex = Vec<Address>;

/// How name references are written: compressed through the env-level
/// name index (the `.ixe` named-section form), or as raw 32-byte
/// addresses — a self-contained encoding that needs no index, used by
/// the demoted in-memory metadata form (see `env::DEMOTE`).
#[derive(Clone, Copy)]
pub enum NamePut<'a> {
  Indexed(&'a NameIndex),
  Raw,
}

/// Decoding counterpart of [`NamePut`].
#[derive(Clone, Copy)]
pub enum NameGet<'a> {
  Indexed(&'a NameReverseIndex),
  Raw,
}

pub(super) fn put_idx(
  addr: &Address,
  idx: NamePut<'_>,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  match idx {
    NamePut::Indexed(map) => {
      let i = map.get(addr).copied().ok_or_else(|| {
        format!(
          "put_idx: address {:?} not in name index (index has {} entries)",
          addr,
          map.len()
        )
      })?;
      put_u64(i, buf);
      Ok(())
    },
    NamePut::Raw => {
      put_address_raw(addr, buf);
      Ok(())
    },
  }
}

pub(super) fn get_idx(
  buf: &mut &[u8],
  rev: NameGet<'_>,
) -> Result<Address, String> {
  match rev {
    NameGet::Indexed(v) => {
      let i = get_u64(buf)? as usize;
      v.get(i)
        .cloned()
        .ok_or_else(|| format!("invalid name index {i}, max {}", v.len()))
    },
    NameGet::Raw => get_address_raw(buf),
  }
}

fn put_idx_vec(
  addrs: &[Address],
  idx: NamePut<'_>,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_vec_len(addrs.len(), buf);
  for a in addrs {
    put_idx(a, idx, buf)?;
  }
  Ok(())
}

fn get_idx_vec(
  buf: &mut &[u8],
  rev: NameGet<'_>,
) -> Result<Vec<Address>, String> {
  let len = get_vec_len(buf)?;
  let mut v = Vec::with_capacity(len);
  for _ in 0..len {
    v.push(get_idx(buf, rev)?);
  }
  Ok(v)
}

// ===========================================================================
// DataValue indexed serialization
// ===========================================================================

impl DataValue {
  pub fn put_with(
    &self,
    idx: NamePut<'_>,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    match self {
      // OfString, OfNat, OfInt, OfSyntax hold blob addresses (not in name index)
      Self::OfString(a) => {
        put_u8(0, buf);
        put_address_raw(a, buf);
      },
      Self::OfBool(b) => {
        put_u8(1, buf);
        put_bool(*b, buf);
      },
      // OfName holds a name address (in name index)
      Self::OfName(a) => {
        put_u8(2, buf);
        put_idx(a, idx, buf)?;
      },
      Self::OfNat(a) => {
        put_u8(3, buf);
        put_address_raw(a, buf);
      },
      Self::OfInt(a) => {
        put_u8(4, buf);
        put_address_raw(a, buf);
      },
      Self::OfSyntax(a) => {
        put_u8(5, buf);
        put_address_raw(a, buf);
      },
    }
    Ok(())
  }

  pub fn get_with(buf: &mut &[u8], rev: NameGet<'_>) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::OfString(get_address_raw(buf)?)),
      1 => Ok(Self::OfBool(get_bool(buf)?)),
      2 => Ok(Self::OfName(get_idx(buf, rev)?)),
      3 => Ok(Self::OfNat(get_address_raw(buf)?)),
      4 => Ok(Self::OfInt(get_address_raw(buf)?)),
      5 => Ok(Self::OfSyntax(get_address_raw(buf)?)),
      x => Err(format!("DataValue::get: invalid tag {x}")),
    }
  }
}

// ===========================================================================
// KVMap and mdata indexed serialization
// ===========================================================================

fn put_kvmap_indexed(
  kvmap: &KVMap,
  idx: NamePut<'_>,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_vec_len(kvmap.len(), buf);
  for (k, v) in kvmap {
    put_idx(k, idx, buf)?;
    v.put_with(idx, buf)?;
  }
  Ok(())
}

fn get_kvmap_indexed(
  buf: &mut &[u8],
  rev: NameGet<'_>,
) -> Result<KVMap, String> {
  let len = get_vec_len(buf)?;
  let mut kvmap = Vec::with_capacity(len);
  for _ in 0..len {
    kvmap.push((get_idx(buf, rev)?, DataValue::get_with(buf, rev)?));
  }
  Ok(kvmap)
}

fn put_mdata_stack_indexed(
  mdata: &[KVMap],
  idx: NamePut<'_>,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_vec_len(mdata.len(), buf);
  for kv in mdata {
    put_kvmap_indexed(kv, idx, buf)?;
  }
  Ok(())
}

fn get_mdata_stack_indexed(
  buf: &mut &[u8],
  rev: NameGet<'_>,
) -> Result<Vec<KVMap>, String> {
  let len = get_vec_len(buf)?;
  let mut mdata = Vec::with_capacity(len);
  for _ in 0..len {
    mdata.push(get_kvmap_indexed(buf, rev)?);
  }
  Ok(mdata)
}

// ===========================================================================
// ExprMeta (arena) indexed serialization
// ===========================================================================
//
// Wire format of an arena (`docs/Ixon.md`, "ExprMeta Arena"):
//
//   arena  := len node_0 … node_{len-1}
//   node_i := tag payload,   tag = kind << 3 | mask
//
// Kinds: 0 Leaf, 1 App, 2..5 Binder (2 + BinderInfo), 6 LetBinder, 7 Ref,
// 8 Prj, 9 Mdata, 10 CallSite, 11 EtaCallSite. The payload is the node's
// fields in declaration order. Child references are never absolute:
//
// * The *structural* slots (App fun/arg, Binder type/body, Let
//   type/value/body, Prj child, Mdata child) may be **implicit**: bit `s` of
//   `mask` set means slot `s` is not written and refers to the node the
//   post-order cursor expects. The cursor `top` starts at `i` and visits the
//   slots last to first; an implicit slot is node `top - 1`, after which
//   `top` becomes `lo[top - 1]`; `lo[i]` is `top` after the last slot (the
//   first index of node `i`'s contiguous post-order block; `lo[i] = i` for a
//   node without structural slots). A tree allocated bottom-up in post-order
//   writes no child references at all.
// * Every other reference (a structural slot whose bit is clear, and every
//   call-site reference) is **explicit**: TagN (`f = 0`) of the backward
//   delta `(i - 1 - c) mod 2^64`. Forward references are representable
//   (wrapping), so every arena of `u64` indices has an encoding.
//
// The writer marks a slot implicit exactly when its child is `top - 1`, and
// the reader rejects an explicit slot equal to `top - 1` and an implicit
// slot with `top = 0`, so each arena has exactly one encoding. Mirrors
// `Ixon.putExprMetaArenaIndexed` / `getExprMetaArenaIndexed`.

const EM_LEAF: u8 = 0;
const EM_APP: u8 = 1;
const EM_BINDER: u8 = 2;
const EM_LET: u8 = 6;
const EM_REF: u8 = 7;
const EM_PRJ: u8 = 8;
const EM_MDATA: u8 = 9;
const EM_CALL_SITE: u8 = 10;
const EM_ETA_CALL_SITE: u8 = 11;

/// Number of structural (possibly implicit) child slots of a node kind.
fn em_slot_count(kind: u8) -> Option<u32> {
  match kind {
    EM_LEAF | EM_REF | EM_CALL_SITE | EM_ETA_CALL_SITE => Some(0),
    EM_APP | 2..=5 => Some(2),
    EM_LET => Some(3),
    EM_PRJ | EM_MDATA => Some(1),
    _ => None,
  }
}

impl ExprMetaData {
  /// The structural child slots, in field order.
  fn structural_slots(&self) -> &[u64] {
    match self {
      Self::App { children } | Self::Binder { children, .. } => children,
      Self::LetBinder { children, .. } => children,
      Self::Prj { child, .. } | Self::Mdata { child, .. } => {
        std::slice::from_ref(child)
      },
      Self::Leaf
      | Self::Ref { .. }
      | Self::CallSite { .. }
      | Self::EtaCallSite { .. } => &[],
    }
  }
}

/// The implicit-slot mask of node `i` and its block start `lo[i]`.
fn em_implicit_mask(node: &ExprMetaData, i: u64, lo: &[u64]) -> (u8, u64) {
  let mut top = i;
  let mut mask = 0u8;
  for (s, &c) in node.structural_slots().iter().enumerate().rev() {
    if top > 0 && c == top - 1 {
      mask |= 1 << s;
      top = lo[(top - 1) as usize];
    }
  }
  (mask, top)
}

/// Explicit reference from node `i` to node `c`: the backward delta
/// `(i - 1 - c) mod 2^64` as a TagN (`f = 0`) integer.
fn put_em_ref(i: u64, c: u64, buf: &mut Vec<u8>) {
  put_u64(i.wrapping_sub(1).wrapping_sub(c), buf);
}

fn get_em_ref(i: u64, buf: &mut &[u8]) -> Result<u64, String> {
  Ok(i.wrapping_sub(1).wrapping_sub(get_u64(buf)?))
}

/// Structural slot `s` of node `i`: written only when not implicit.
fn put_em_slot(i: u64, mask: u8, s: u32, c: u64, buf: &mut Vec<u8>) {
  if mask & (1 << s) == 0 {
    put_em_ref(i, c, buf);
  }
}

/// Structural slot `s` of node `i`: read when explicit, a placeholder
/// (resolved by [`em_resolve_slots`]) when implicit.
fn get_em_slot(
  i: u64,
  mask: u8,
  s: u32,
  buf: &mut &[u8],
) -> Result<u64, String> {
  if mask & (1 << s) == 0 { get_em_ref(i, buf) } else { Ok(0) }
}

/// Resolve the implicit slots of node `i` in place and return `lo[i]`.
fn em_resolve_slots(
  slots: &mut [u64],
  mask: u8,
  i: u64,
  lo: &[u64],
) -> Result<u64, String> {
  let mut top = i;
  for s in (0..slots.len()).rev() {
    if mask & (1 << s) != 0 {
      if top == 0 {
        return Err(format!(
          "ExprMeta::get: node {i}: implicit child slot {s} with no \
           preceding node"
        ));
      }
      slots[s] = top - 1;
      top = lo[(top - 1) as usize];
    } else if top > 0 && slots[s] == top - 1 {
      return Err(format!(
        "ExprMeta::get: node {i}: explicit child slot {s} refers to the \
         implicit position {} (noncanonical)",
        top - 1
      ));
    }
  }
  Ok(top)
}

fn put_em_entries(i: u64, entries: &[CallSiteEntry], buf: &mut Vec<u8>) {
  put_vec_len(entries.len(), buf);
  for entry in entries {
    match entry {
      CallSiteEntry::Kept { canon_idx, meta } => {
        put_u8(0, buf);
        put_u64(*canon_idx, buf);
        put_em_ref(i, *meta, buf);
      },
      CallSiteEntry::Collapsed { sharing_idx, meta } => {
        put_u8(1, buf);
        put_u64(*sharing_idx, buf);
        put_em_ref(i, *meta, buf);
      },
    }
  }
}

fn get_em_entries(
  i: u64,
  buf: &mut &[u8],
) -> Result<Vec<CallSiteEntry>, String> {
  let n_entries = get_vec_len(buf)?;
  let mut entries = Vec::with_capacity(n_entries.min(buf.len()));
  for _ in 0..n_entries {
    let entry = match get_u8(buf)? {
      0 => {
        let canon_idx = get_u64(buf)?;
        let meta = get_em_ref(i, buf)?;
        CallSiteEntry::Kept { canon_idx, meta }
      },
      1 => {
        let sharing_idx = get_u64(buf)?;
        let meta = get_em_ref(i, buf)?;
        CallSiteEntry::Collapsed { sharing_idx, meta }
      },
      x => return Err(format!("CallSiteEntry::get: invalid tag {x}")),
    };
    entries.push(entry);
  }
  Ok(entries)
}

fn put_em_refs(i: u64, refs: &[u64], buf: &mut Vec<u8>) {
  put_vec_len(refs.len(), buf);
  for &c in refs {
    put_em_ref(i, c, buf);
  }
}

fn get_em_refs(i: u64, buf: &mut &[u8]) -> Result<Vec<u64>, String> {
  let len = get_vec_len(buf)?;
  let mut v = Vec::with_capacity(len.min(buf.len()));
  for _ in 0..len {
    v.push(get_em_ref(i, buf)?);
  }
  Ok(v)
}

impl ExprMetaData {
  /// Write node `i` with its implicit-slot `mask` (see the module comment
  /// above).
  fn put_node(
    &self,
    i: u64,
    mask: u8,
    idx: NamePut<'_>,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    match self {
      Self::Leaf => put_u8(EM_LEAF << 3, buf),
      Self::App { children } => {
        put_u8((EM_APP << 3) | mask, buf);
        put_em_slot(i, mask, 0, children[0], buf);
        put_em_slot(i, mask, 1, children[1], buf);
      },
      Self::Binder { name, info, children } => {
        let kind = EM_BINDER
          + match info {
            BinderInfo::Default => 0u8,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
          };
        put_u8((kind << 3) | mask, buf);
        put_idx(name, idx, buf)?;
        put_em_slot(i, mask, 0, children[0], buf);
        put_em_slot(i, mask, 1, children[1], buf);
      },
      Self::LetBinder { name, children } => {
        put_u8((EM_LET << 3) | mask, buf);
        put_idx(name, idx, buf)?;
        put_em_slot(i, mask, 0, children[0], buf);
        put_em_slot(i, mask, 1, children[1], buf);
        put_em_slot(i, mask, 2, children[2], buf);
      },
      Self::Ref { name } => {
        put_u8(EM_REF << 3, buf);
        put_idx(name, idx, buf)?;
      },
      Self::Prj { struct_name, child } => {
        put_u8((EM_PRJ << 3) | mask, buf);
        put_idx(struct_name, idx, buf)?;
        put_em_slot(i, mask, 0, *child, buf);
      },
      Self::Mdata { mdata, child } => {
        put_u8((EM_MDATA << 3) | mask, buf);
        put_mdata_stack_indexed(mdata, idx, buf)?;
        put_em_slot(i, mask, 0, *child, buf);
      },
      Self::CallSite { name, entries, canon_meta, orig_head } => {
        put_u8(EM_CALL_SITE << 3, buf);
        put_idx(name, idx, buf)?;
        put_em_entries(i, entries, buf);
        put_em_refs(i, canon_meta, buf);
        match orig_head {
          None => put_u8(0, buf),
          Some((sharing_idx, meta)) => {
            put_u8(1, buf);
            put_u64(*sharing_idx, buf);
            put_em_ref(i, *meta, buf);
          },
        }
      },
      Self::EtaCallSite {
        n_synth,
        name,
        entries,
        canon_meta,
        wrapper_meta,
      } => {
        put_u8(EM_ETA_CALL_SITE << 3, buf);
        put_u64(*n_synth, buf);
        put_idx(name, idx, buf)?;
        put_em_entries(i, entries, buf);
        put_em_refs(i, canon_meta, buf);
        put_em_ref(i, *wrapper_meta, buf);
      },
    }
    Ok(())
  }

  /// Read node `i`, given the block starts `lo[0..i]`; returns the node
  /// and `lo[i]`.
  fn get_node(
    buf: &mut &[u8],
    rev: NameGet<'_>,
    i: u64,
    lo: &[u64],
  ) -> Result<(Self, u64), String> {
    let tag = get_u8(buf)?;
    let kind = tag >> 3;
    let mask = tag & 7;
    match em_slot_count(kind) {
      Some(n) if u32::from(mask) < (1 << n) => {},
      _ => return Err(format!("ExprMetaData::get: invalid tag {tag}")),
    }
    let mut node = match kind {
      EM_LEAF => Self::Leaf,
      EM_APP => {
        let c0 = get_em_slot(i, mask, 0, buf)?;
        let c1 = get_em_slot(i, mask, 1, buf)?;
        Self::App { children: [c0, c1] }
      },
      2..=5 => {
        let info = match kind {
          2 => BinderInfo::Default,
          3 => BinderInfo::Implicit,
          4 => BinderInfo::StrictImplicit,
          _ => BinderInfo::InstImplicit,
        };
        let name = get_idx(buf, rev)?;
        let c0 = get_em_slot(i, mask, 0, buf)?;
        let c1 = get_em_slot(i, mask, 1, buf)?;
        Self::Binder { name, info, children: [c0, c1] }
      },
      EM_LET => {
        let name = get_idx(buf, rev)?;
        let c0 = get_em_slot(i, mask, 0, buf)?;
        let c1 = get_em_slot(i, mask, 1, buf)?;
        let c2 = get_em_slot(i, mask, 2, buf)?;
        Self::LetBinder { name, children: [c0, c1, c2] }
      },
      EM_REF => Self::Ref { name: get_idx(buf, rev)? },
      EM_PRJ => {
        let struct_name = get_idx(buf, rev)?;
        let child = get_em_slot(i, mask, 0, buf)?;
        Self::Prj { struct_name, child }
      },
      EM_MDATA => {
        let mdata = get_mdata_stack_indexed(buf, rev)?;
        let child = get_em_slot(i, mask, 0, buf)?;
        Self::Mdata { mdata, child }
      },
      EM_CALL_SITE => {
        let name = get_idx(buf, rev)?;
        let entries = get_em_entries(i, buf)?;
        let canon_meta = get_em_refs(i, buf)?;
        let orig_head = match get_u8(buf)? {
          0 => None,
          1 => {
            let sharing_idx = get_u64(buf)?;
            let meta = get_em_ref(i, buf)?;
            Some((sharing_idx, meta))
          },
          x => {
            return Err(format!("CallSite::get: invalid orig_head tag {x}"));
          },
        };
        Self::CallSite { name, entries, canon_meta, orig_head }
      },
      _ => {
        let n_synth = get_u64(buf)?;
        let name = get_idx(buf, rev)?;
        let entries = get_em_entries(i, buf)?;
        let canon_meta = get_em_refs(i, buf)?;
        let wrapper_meta = get_em_ref(i, buf)?;
        Self::EtaCallSite { n_synth, name, entries, canon_meta, wrapper_meta }
      },
    };
    let top = match &mut node {
      Self::App { children } | Self::Binder { children, .. } => {
        em_resolve_slots(children, mask, i, lo)?
      },
      Self::LetBinder { children, .. } => {
        em_resolve_slots(children, mask, i, lo)?
      },
      Self::Prj { child, .. } | Self::Mdata { child, .. } => {
        em_resolve_slots(std::slice::from_mut(child), mask, i, lo)?
      },
      Self::Leaf
      | Self::Ref { .. }
      | Self::CallSite { .. }
      | Self::EtaCallSite { .. } => i,
    };
    Ok((node, top))
  }
}

impl ExprMeta {
  pub fn put_with(
    &self,
    idx: NamePut<'_>,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    put_vec_len(self.nodes.len(), buf);
    let mut lo: Vec<u64> = Vec::with_capacity(self.nodes.len());
    for (i, node) in self.nodes.iter().enumerate() {
      let i = i as u64;
      let (mask, top) = em_implicit_mask(node, i, &lo);
      node.put_node(i, mask, idx, buf)?;
      lo.push(top);
    }
    Ok(())
  }

  pub fn get_with(buf: &mut &[u8], rev: NameGet<'_>) -> Result<Self, String> {
    let len = get_vec_len(buf)?;
    // Every node takes at least one byte.
    let cap = len.min(buf.len());
    let mut nodes = Vec::with_capacity(cap);
    let mut lo: Vec<u64> = Vec::with_capacity(cap);
    for i in 0..len {
      let (node, top) = ExprMetaData::get_node(buf, rev, i as u64, &lo)?;
      nodes.push(node);
      lo.push(top);
    }
    Ok(ExprMeta { nodes })
  }
}

fn put_u64_vec(v: &[u64], buf: &mut Vec<u8>) {
  put_vec_len(v.len(), buf);
  for &x in v {
    put_u64(x, buf);
  }
}

fn get_u64_vec(buf: &mut &[u8]) -> Result<Vec<u64>, String> {
  let len = get_vec_len(buf)?;
  let mut v = Vec::with_capacity(len);
  for _ in 0..len {
    v.push(get_u64(buf)?);
  }
  Ok(v)
}

// ===========================================================================
// ConstantMeta indexed serialization
// ===========================================================================

impl ConstantMetaInfo {
  pub fn put_with(
    &self,
    idx: NamePut<'_>,
    buf: &mut Vec<u8>,
  ) -> Result<(), String> {
    match self {
      Self::Empty => put_u8(255, buf),
      Self::Def { name, lvls, all, ctx, arena, type_root, value_root } => {
        put_u8(0, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx_vec(all, idx, buf)?;
        put_idx_vec(ctx, idx, buf)?;
        arena.put_with(idx, buf)?;
        put_u64(*type_root, buf);
        put_u64(*value_root, buf);
      },
      Self::Axio { name, lvls, arena, type_root } => {
        put_u8(1, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        arena.put_with(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Quot { name, lvls, arena, type_root } => {
        put_u8(2, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        arena.put_with(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        put_u8(3, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx_vec(ctors, idx, buf)?;
        put_idx_vec(all, idx, buf)?;
        put_idx_vec(ctx, idx, buf)?;
        arena.put_with(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Ctor { name, lvls, induct, arena, type_root } => {
        put_u8(4, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx(induct, idx, buf)?;
        arena.put_with(idx, buf)?;
        put_u64(*type_root, buf);
      },
      Self::Rec {
        name,
        lvls,
        rules,
        all,
        ctx,
        arena,
        type_root,
        rule_roots,
      } => {
        put_u8(5, buf);
        put_idx(name, idx, buf)?;
        put_idx_vec(lvls, idx, buf)?;
        put_idx_vec(rules, idx, buf)?;
        put_idx_vec(all, idx, buf)?;
        put_idx_vec(ctx, idx, buf)?;
        arena.put_with(idx, buf)?;
        put_u64(*type_root, buf);
        put_u64_vec(rule_roots, buf);
      },
      Self::Muts { all, aux_layout } => {
        put_u8(6, buf);
        put_u64(all.len() as u64, buf);
        for cls in all {
          put_idx_vec(cls, idx, buf)?;
        }
        // Option<AuxLayout>: 0 tag = None, 1 tag = Some(perm_vec,
        // ctor_vec, evaporated_vec). The usize vecs are written as
        // Vec<u64> via TagN so the serialized form is target-word-size
        // independent; `evaporated` is one u8 (0/1) per entry.
        match aux_layout {
          None => put_u8(0, buf),
          Some(layout) => {
            put_u8(1, buf);
            put_u64(layout.perm.len() as u64, buf);
            for &p in &layout.perm {
              put_u64(p as u64, buf);
            }
            put_u64(layout.source_ctor_counts.len() as u64, buf);
            for &c in &layout.source_ctor_counts {
              put_u64(c as u64, buf);
            }
            put_u64(layout.evaporated.len() as u64, buf);
            for &b in &layout.evaporated {
              put_u8(u8::from(b), buf);
            }
          },
        }
      },
    }
    Ok(())
  }

  pub fn get_with(buf: &mut &[u8], rev: NameGet<'_>) -> Result<Self, String> {
    match get_u8(buf)? {
      255 => Ok(Self::Empty),
      0 => Ok(Self::Def {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_with(buf, rev)?,
        type_root: get_u64(buf)?,
        value_root: get_u64(buf)?,
      }),
      1 => Ok(Self::Axio {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_with(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      2 => Ok(Self::Quot {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_with(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      3 => Ok(Self::Indc {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        ctors: get_idx_vec(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_with(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      4 => Ok(Self::Ctor {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        induct: get_idx(buf, rev)?,
        arena: ExprMeta::get_with(buf, rev)?,
        type_root: get_u64(buf)?,
      }),
      5 => Ok(Self::Rec {
        name: get_idx(buf, rev)?,
        lvls: get_idx_vec(buf, rev)?,
        rules: get_idx_vec(buf, rev)?,
        all: get_idx_vec(buf, rev)?,
        ctx: get_idx_vec(buf, rev)?,
        arena: ExprMeta::get_with(buf, rev)?,
        type_root: get_u64(buf)?,
        rule_roots: get_u64_vec(buf)?,
      }),
      6 => {
        let n = get_u64(buf)? as usize;
        let mut all = Vec::with_capacity(n);
        for _ in 0..n {
          all.push(get_idx_vec(buf, rev)?);
        }
        let aux_layout = match get_u8(buf)? {
          0 => None,
          1 => {
            let n_perm = get_u64(buf)? as usize;
            let mut perm = Vec::with_capacity(n_perm);
            for _ in 0..n_perm {
              perm.push(get_u64(buf)? as usize);
            }
            let n_counts = get_u64(buf)? as usize;
            let mut source_ctor_counts = Vec::with_capacity(n_counts);
            for _ in 0..n_counts {
              source_ctor_counts.push(get_u64(buf)? as usize);
            }
            let n_evap = get_u64(buf)? as usize;
            let mut evaporated = Vec::with_capacity(n_evap);
            for _ in 0..n_evap {
              evaporated.push(match get_u8(buf)? {
                0 => false,
                1 => true,
                x => {
                  return Err(format!(
                    "Muts.aux_layout: invalid evaporated flag {x}"
                  ));
                },
              });
            }
            Some(AuxLayout { perm, source_ctor_counts, evaporated })
          },
          x => return Err(format!("Muts.aux_layout: invalid tag {x}")),
        };
        Ok(Self::Muts { all, aux_layout })
      },
      x => Err(format!("ConstantMetaInfo::get: invalid tag {x}")),
    }
  }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_binder_info_roundtrip() {
    for bi in [
      BinderInfo::Default,
      BinderInfo::Implicit,
      BinderInfo::StrictImplicit,
      BinderInfo::InstImplicit,
    ] {
      let mut buf = Vec::new();
      bi.put_ser(&mut buf);
      assert_eq!(BinderInfo::get_ser(&mut buf.as_slice()).unwrap(), bi);
    }
  }

  #[test]
  fn test_constant_meta_indexed_roundtrip() {
    // Create test addresses
    let addr1 = Address::from_slice(&[1u8; 32]).unwrap();
    let addr2 = Address::from_slice(&[2u8; 32]).unwrap();
    let addr3 = Address::from_slice(&[3u8; 32]).unwrap();

    // Build index
    let mut idx = NameIndex::new();
    idx.insert(addr1.clone(), 0);
    idx.insert(addr2.clone(), 1);
    idx.insert(addr3.clone(), 2);

    // Build reverse index
    let rev: NameReverseIndex =
      vec![addr1.clone(), addr2.clone(), addr3.clone()];

    // Test Def variant with arena
    let mut arena = ExprMeta::default();
    let leaf = arena.alloc(ExprMetaData::Leaf);
    let binder = arena.alloc(ExprMetaData::Binder {
      name: addr1.clone(),
      info: BinderInfo::Default,
      children: [leaf, leaf],
    });

    let mut meta = ConstantMeta::new(ConstantMetaInfo::Def {
      name: addr1.clone(),
      lvls: vec![addr2.clone(), addr3.clone()],
      all: vec![addr1.clone()],
      ctx: vec![addr2.clone()],
      arena,
      type_root: binder,
      value_root: leaf,
    });
    // Wrapper extension payload incl. level-spelling patches (§10.6).
    meta.meta_univs =
      vec![Univ::succ(Univ::var(0)), Univ::max(Univ::zero(), Univ::var(1))];
    meta.univ_patches = vec![
      UnivPatch { arena_idx: 1, univ_idxs: vec![0, 2] },
      UnivPatch { arena_idx: 4, univ_idxs: vec![3] },
    ];

    let mut buf = Vec::new();
    meta.put_with(NamePut::Indexed(&idx), &mut buf).unwrap();
    let recovered =
      ConstantMeta::get_with(&mut buf.as_slice(), NameGet::Indexed(&rev))
        .unwrap();
    assert_eq!(meta, recovered);

    // Raw (self-contained) encoding roundtrips the same value without
    // any index, and re-encoding the recovered value through the index
    // matches the indexed bytes exactly.
    let mut raw = Vec::new();
    meta.put_raw(&mut raw).unwrap();
    let from_raw = ConstantMeta::get_raw(&mut raw.as_slice()).unwrap();
    assert_eq!(meta, from_raw);
    let mut reindexed = Vec::new();
    from_raw.put_with(NamePut::Indexed(&idx), &mut reindexed).unwrap();
    assert_eq!(buf, reindexed);
  }

  #[test]
  fn test_muts_aux_layout_roundtrip() {
    let addr = Address::from_slice(&[7u8; 32]).unwrap();
    // The unified encoding serializes `evaporated` verbatim under one
    // Some tag (no all-false special case): all-false, mixed, and empty
    // flag vectors each roundtrip exactly.
    for evaporated in [vec![false, false], vec![true, false], vec![]] {
      let meta = ConstantMeta::new(ConstantMetaInfo::Muts {
        all: vec![vec![addr.clone()]],
        aux_layout: Some(AuxLayout {
          perm: vec![1, 0],
          source_ctor_counts: vec![2, 3],
          evaporated,
        }),
      });
      let mut buf = Vec::new();
      meta.put_raw(&mut buf).unwrap();
      let recovered = ConstantMeta::get_raw(&mut buf.as_slice()).unwrap();
      assert_eq!(meta, recovered);
    }
    let none = ConstantMeta::new(ConstantMetaInfo::Muts {
      all: vec![vec![addr]],
      aux_layout: None,
    });
    let mut buf = Vec::new();
    none.put_raw(&mut buf).unwrap();
    let recovered = ConstantMeta::get_raw(&mut buf.as_slice()).unwrap();
    assert_eq!(none, recovered);
  }

  #[test]
  fn test_expr_meta_arena_roundtrip() {
    let addr1 = Address::from_slice(&[1u8; 32]).unwrap();

    let mut idx = NameIndex::new();
    idx.insert(addr1.clone(), 0);
    let rev: NameReverseIndex = vec![addr1.clone()];

    let mut arena = ExprMeta::default();
    let leaf = arena.alloc(ExprMetaData::Leaf);
    let ref_node = arena.alloc(ExprMetaData::Ref { name: addr1.clone() });
    let app = arena.alloc(ExprMetaData::App { children: [leaf, ref_node] });
    let mdata = arena.alloc(ExprMetaData::Mdata {
      mdata: vec![vec![(addr1.clone(), DataValue::OfBool(true))]],
      child: app,
    });
    let _eta = arena.alloc(ExprMetaData::EtaCallSite {
      n_synth: 3,
      name: addr1.clone(),
      entries: vec![
        CallSiteEntry::Kept { canon_idx: 0, meta: leaf },
        CallSiteEntry::Collapsed { sharing_idx: 2, meta: ref_node },
      ],
      canon_meta: vec![leaf, ref_node],
      wrapper_meta: mdata,
    });

    let mut buf = Vec::new();
    arena.put_with(NamePut::Indexed(&idx), &mut buf).unwrap();
    let recovered =
      ExprMeta::get_with(&mut buf.as_slice(), NameGet::Indexed(&rev)).unwrap();
    assert_eq!(arena, recovered);
  }

  /// Names for the arena byte vectors: index 0 and 1 (one-byte indices in
  /// every integer code).
  fn vec_names() -> (Address, Address, NameIndex, NameReverseIndex) {
    let a = Address::from_slice(&[1u8; 32]).unwrap();
    let b = Address::from_slice(&[2u8; 32]).unwrap();
    let mut idx = NameIndex::new();
    idx.insert(a.clone(), 0);
    idx.insert(b.clone(), 1);
    (a.clone(), b.clone(), idx, vec![a, b])
  }

  fn arena_bytes(arena: &ExprMeta, idx: &NameIndex) -> Vec<u8> {
    let mut buf = Vec::new();
    arena.put_with(NamePut::Indexed(idx), &mut buf).unwrap();
    buf
  }

  fn arena_from(
    bytes: &[u8],
    rev: &NameReverseIndex,
  ) -> Result<ExprMeta, String> {
    let mut slice = bytes;
    let arena = ExprMeta::get_with(&mut slice, NameGet::Indexed(rev))?;
    assert!(slice.is_empty(), "trailing bytes");
    Ok(arena)
  }

  /// Check `arena` against its expected bytes in both directions.
  fn check_vector(arena: &ExprMeta, bytes: &[u8]) {
    let (_, _, idx, rev) = vec_names();
    assert_eq!(arena_bytes(arena, &idx), bytes);
    assert_eq!(&arena_from(bytes, &rev).unwrap(), arena);
  }

  /// A post-order tree (`fun (x : T) => f x`): every child is implicit and
  /// no reference is written.
  #[test]
  fn arena_vector_post_order_tree() {
    let (f, t, _, _) = vec_names();
    let arena = ExprMeta {
      nodes: vec![
        ExprMetaData::Ref { name: t },
        ExprMetaData::Ref { name: f.clone() },
        ExprMetaData::Leaf,
        ExprMetaData::App { children: [1, 2] },
        ExprMetaData::Binder {
          name: f,
          info: BinderInfo::Default,
          children: [0, 3],
        },
      ],
    };
    check_vector(
      &arena,
      &[0x05, 0x38, 0x01, 0x38, 0x00, 0x00, 0x0B, 0x13, 0x00],
    );
  }

  /// Shared nodes: explicit backward deltas next to implicit slots.
  #[test]
  fn arena_vector_dag() {
    let (a, b, _, _) = vec_names();
    let arena = ExprMeta {
      nodes: vec![
        ExprMetaData::Leaf,
        // arg implicit (node 0); fun explicit: Δ = 1 - 1 - 0 = 0.
        ExprMetaData::App { children: [0, 0] },
        // value implicit (node 1); type and body explicit (Δ = 1).
        ExprMetaData::LetBinder { name: a, children: [0, 1, 0] },
        // child 1 is not the cursor (2): explicit, Δ = 1.
        ExprMetaData::Prj { struct_name: b, child: 1 },
        ExprMetaData::Mdata { mdata: vec![], child: 3 },
      ],
    };
    check_vector(
      &arena,
      &[
        0x05, 0x00, 0x0A, 0x00, 0x32, 0x00, 0x01, 0x01, 0x40, 0x01, 0x01, 0x49,
        0x00,
      ],
    );
  }

  /// Call-site references are always explicit; a forward reference wraps
  /// to a 9-byte TagN delta.
  #[test]
  fn arena_vector_call_sites_and_forward() {
    let (a, b, _, _) = vec_names();
    let arena = ExprMeta {
      nodes: vec![
        ExprMetaData::Leaf,
        ExprMetaData::CallSite {
          name: a.clone(),
          entries: vec![
            CallSiteEntry::Kept { canon_idx: 0, meta: 0 },
            CallSiteEntry::Collapsed { sharing_idx: 1, meta: 0 },
          ],
          canon_meta: vec![0],
          orig_head: Some((2, 0)),
        },
        ExprMetaData::EtaCallSite {
          n_synth: 1,
          name: b,
          entries: vec![CallSiteEntry::Kept { canon_idx: 0, meta: 1 }],
          canon_meta: vec![1],
          wrapper_meta: 1,
        },
        // Δ = 3 - 1 - 7 wraps to 2^64 - 5.
        ExprMetaData::Prj { struct_name: a, child: 7 },
      ],
    };
    check_vector(
      &arena,
      &[
        0x04, 0x00, // leaf
        0x50, 0x00, 0x02, 0x00, 0x00, 0x00, 0x01, 0x01, 0x00, 0x01, 0x00, 0x01,
        0x02, 0x00, // callSite
        0x58, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, // eta
        0x40, 0x00, 0xC3, 0x7B, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF,
        0xFF, // prj (TagN f = 0 rung 6: 2^64 - 5 - R5 = 0xFFFFFFFE_FEFEBF7B)
      ],
    );
  }

  /// The reader accepts exactly the writer's encoding.
  #[test]
  fn arena_rejects_noncanonical() {
    let (_, _, _, rev) = vec_names();
    // App with both slots explicit, the argument at the implicit position.
    assert!(arena_from(&[0x02, 0x00, 0x08, 0x00, 0x00], &rev).is_err());
    // Implicit slot with no preceding node.
    assert!(arena_from(&[0x01, 0x09, 0x00], &rev).is_err());
    // Mask bits beyond the kind's slots, and unknown kinds.
    assert!(arena_from(&[0x01, 0x01], &rev).is_err());
    assert!(arena_from(&[0x02, 0x00, 0x0C], &rev).is_err());
    assert!(arena_from(&[0x01, 0x39, 0x00], &rev).is_err());
    assert!(arena_from(&[0x01, 0x60], &rev).is_err());
    // The same arenas, written canonically, are accepted.
    assert!(arena_from(&[0x02, 0x00, 0x0A, 0x00], &rev).is_ok());
  }

  /// Pseudo-random arenas (every kind, arbitrary references including
  /// forward and self references) roundtrip, and re-encoding the decoded
  /// arena reproduces the bytes.
  #[test]
  fn arena_random_roundtrip() {
    let (a, b, idx, rev) = vec_names();
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = |m: u64| {
      s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
      (s >> 33) % m
    };
    for _ in 0..2000 {
      let n = next(24);
      let mut nodes = Vec::new();
      for i in 0..n {
        // Mostly post-order-ish (just below), sometimes anywhere.
        let r = |next: &mut dyn FnMut(u64) -> u64| match next(4) {
          0 => next(n + 2),
          _ => i.saturating_sub(1 + next(3)),
        };
        let name = if next(2) == 0 { a.clone() } else { b.clone() };
        let node = match next(9) {
          0 => ExprMetaData::Leaf,
          1 => ExprMetaData::App { children: [r(&mut next), r(&mut next)] },
          2 => ExprMetaData::Binder {
            name,
            info: BinderInfo::InstImplicit,
            children: [r(&mut next), r(&mut next)],
          },
          3 => ExprMetaData::LetBinder {
            name,
            children: [r(&mut next), r(&mut next), r(&mut next)],
          },
          4 => ExprMetaData::Ref { name },
          5 => ExprMetaData::Prj { struct_name: name, child: r(&mut next) },
          6 => ExprMetaData::Mdata {
            mdata: vec![vec![(name, DataValue::OfBool(true))]],
            child: r(&mut next),
          },
          7 => ExprMetaData::CallSite {
            name,
            entries: vec![CallSiteEntry::Kept {
              canon_idx: 3,
              meta: r(&mut next),
            }],
            canon_meta: vec![r(&mut next), r(&mut next)],
            orig_head: Some((4, r(&mut next))),
          },
          _ => ExprMetaData::EtaCallSite {
            n_synth: 2,
            name,
            entries: vec![CallSiteEntry::Collapsed {
              sharing_idx: 5,
              meta: r(&mut next),
            }],
            canon_meta: vec![],
            wrapper_meta: r(&mut next),
          },
        };
        nodes.push(node);
      }
      let arena = ExprMeta { nodes };
      let bytes = arena_bytes(&arena, &idx);
      let back = arena_from(&bytes, &rev).unwrap();
      assert_eq!(back, arena);
      assert_eq!(arena_bytes(&back, &idx), bytes);
    }
  }
}
