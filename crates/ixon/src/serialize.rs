//! Serialization for Ixon types.
//!
//! This module provides serialization/deserialization for all Ixon types
//! using the Tag4/Tag2/Tag0 encoding schemes.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::map_err_ignore)]
#![allow(clippy::needless_pass_by_value)]

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind, ReducibilityHints};

use super::constant::{
  Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
  Definition, DefinitionProj, Inductive, InductiveProj, MutConst, Quotient,
  Recursor, RecursorProj, RecursorRule,
};
use super::expr::Expr;
use super::metadata::IxonByteSerde;
use super::tag::{Tag0, Tag4};
use super::univ::{Univ, get_univ, put_univ};

// ============================================================================
// Primitive helpers
// ============================================================================

/// Cap capacity for Vec allocation during deserialization.
/// Prevents OOM from malicious/malformed input claiming huge sizes.
/// Each item requires at least 1 byte, so capacity can never exceed buffer length.
#[inline]
fn capped_capacity(count: u64, buf: &[u8]) -> usize {
  (count as usize).min(buf.len())
}

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

fn put_u64(x: u64, buf: &mut Vec<u8>) {
  Tag0::new(x).put(buf);
}

fn get_u64(buf: &mut &[u8]) -> Result<u64, String> {
  Ok(Tag0::get(buf)?.size)
}

fn put_bytes(bytes: &[u8], buf: &mut Vec<u8>) {
  buf.extend_from_slice(bytes);
}

fn put_address(a: &Address, buf: &mut Vec<u8>) {
  put_bytes(a.as_bytes(), buf);
}

/// Read the optional trailing `anon_hints` section written by `Env::put`.
/// No-op when no bytes remain after the comms section — backward-compatible
/// with `.ixe` that have no hints or predate the section. Inserts into
/// `env.anon_hints` (overwriting any value harvested from a Named section,
/// with the identical value, so the order of harvest vs. section is moot).
fn read_anon_hints_section(
  buf: &mut &[u8],
  env: &mut Env,
) -> Result<(), String> {
  if buf.is_empty() {
    return Ok(());
  }
  let n = get_u64(buf)?;
  for _ in 0..n {
    let addr = get_address(buf)?;
    let hints = ReducibilityHints::get_ser(buf)?;
    env.anon_hints.insert(addr, hints);
  }
  Ok(())
}

fn get_address(buf: &mut &[u8]) -> Result<Address, String> {
  if buf.len() < 32 {
    return Err(format!("get_address: need 32 bytes, have {}", buf.len()));
  }
  let (bytes, rest) = buf.split_at(32);
  *buf = rest;
  Address::from_slice(bytes).map_err(|_| "get_address: invalid".to_string())
}

/// Pack up to 8 bools into a u8.
pub fn pack_bools<I>(bools: I) -> u8
where
  I: IntoIterator<Item = bool>,
{
  let mut acc: u8 = 0;
  for (i, b) in bools.into_iter().take(8).enumerate() {
    if b {
      acc |= 1u8 << (i as u32);
    }
  }
  acc
}

/// Unpack up to n bools from a u8.
pub fn unpack_bools(n: usize, b: u8) -> Vec<bool> {
  (0..8).map(|i: u32| (b & (1u8 << i)) != 0).take(n.min(8)).collect()
}

// ============================================================================
// Expression serialization
// ============================================================================

/// Serialize an expression to bytes (iterative to avoid stack overflow).
pub fn put_expr(e: &Expr, buf: &mut Vec<u8>) {
  let mut stack: Vec<&Expr> = vec![e];

  while let Some(curr) = stack.pop() {
    match curr {
      Expr::Sort(univ_idx) => {
        Tag4::new(Expr::FLAG_SORT, *univ_idx).put(buf);
      },
      Expr::Var(idx) => {
        Tag4::new(Expr::FLAG_VAR, *idx).put(buf);
      },
      Expr::Ref(ref_idx, univ_indices) => {
        Tag4::new(Expr::FLAG_REF, univ_indices.len() as u64).put(buf);
        put_u64(*ref_idx, buf);
        for idx in univ_indices {
          put_u64(*idx, buf);
        }
      },
      Expr::Rec(rec_idx, univ_indices) => {
        Tag4::new(Expr::FLAG_REC, univ_indices.len() as u64).put(buf);
        put_u64(*rec_idx, buf);
        for idx in univ_indices {
          put_u64(*idx, buf);
        }
      },
      Expr::Prj(type_ref_idx, field_idx, val) => {
        Tag4::new(Expr::FLAG_PRJ, *field_idx).put(buf);
        put_u64(*type_ref_idx, buf);
        stack.push(val);
      },
      Expr::Str(ref_idx) => {
        Tag4::new(Expr::FLAG_STR, *ref_idx).put(buf);
      },
      Expr::Nat(ref_idx) => {
        Tag4::new(Expr::FLAG_NAT, *ref_idx).put(buf);
      },
      Expr::App(..) => {
        // Telescope compression: count nested apps
        let count = curr.app_telescope_count();
        Tag4::new(Expr::FLAG_APP, count).put(buf);
        // Collect function and args
        let mut e = curr;
        let mut args = Vec::with_capacity(count as usize);
        while let Expr::App(func, arg) = e {
          args.push(arg.as_ref());
          e = func.as_ref();
        }
        // Push in reverse order: args (reversed back to normal), then func
        for arg in &args {
          stack.push(*arg);
        }
        stack.push(e); // func last, processed first
      },
      Expr::Lam(..) => {
        // Telescope compression: count nested lambdas
        let count = curr.lam_telescope_count();
        Tag4::new(Expr::FLAG_LAM, count).put(buf);
        // Collect types and body
        let mut e = curr;
        let mut types = Vec::with_capacity(count as usize);
        while let Expr::Lam(t, b) = e {
          types.push(t.as_ref());
          e = b.as_ref();
        }
        // Push body first (processed last), then types in reverse order
        stack.push(e); // body
        for ty in types.into_iter().rev() {
          stack.push(ty);
        }
      },
      Expr::All(..) => {
        // Telescope compression: count nested foralls
        let count = curr.all_telescope_count();
        Tag4::new(Expr::FLAG_ALL, count).put(buf);
        // Collect types and body
        let mut e = curr;
        let mut types = Vec::with_capacity(count as usize);
        while let Expr::All(t, b) = e {
          types.push(t.as_ref());
          e = b.as_ref();
        }
        // Push body first (processed last), then types in reverse order
        stack.push(e); // body
        for ty in types.into_iter().rev() {
          stack.push(ty);
        }
      },
      Expr::Let(non_dep, ty, val, body) => {
        // size=0 for dep, size=1 for non_dep
        Tag4::new(Expr::FLAG_LET, if *non_dep { 1 } else { 0 }).put(buf);
        stack.push(body); // Process body last
        stack.push(val);
        stack.push(ty); // Process ty first
      },
      Expr::Share(idx) => {
        Tag4::new(Expr::FLAG_SHARE, *idx).put(buf);
      },
    }
  }
}

/// Frame for iterative expression deserialization.
enum GetExprFrame {
  /// Parse an expression from the buffer
  Parse,
  /// Build Prj with stored idx, pop val and typ
  BuildPrj(u64, u64), // type_ref_idx, field_idx
  /// Build App: pop func and arg, push App(func, arg)
  BuildApp,
  /// Collect n more args for App telescope, then wrap
  CollectApps(u64),
  /// Collect remaining Lam types: have `collected`, need `remaining` more
  CollectLamType { collected: Vec<Arc<Expr>>, remaining: u64 },
  /// Build Lam telescope: wrap body in Lams using stored types
  BuildLams(Vec<Arc<Expr>>),
  /// Collect remaining All types: have `collected`, need `remaining` more
  CollectAllType { collected: Vec<Arc<Expr>>, remaining: u64 },
  /// Build All telescope: wrap body in Alls using stored types
  BuildAlls(Vec<Arc<Expr>>),
  /// Build Let with stored non_dep flag
  BuildLet(bool),
}

/// Deserialize an expression from bytes (iterative to avoid stack overflow).
pub fn get_expr(buf: &mut &[u8]) -> Result<Arc<Expr>, String> {
  let mut work: Vec<GetExprFrame> = vec![GetExprFrame::Parse];
  let mut results: Vec<Arc<Expr>> = Vec::new();

  while let Some(frame) = work.pop() {
    match frame {
      GetExprFrame::Parse => {
        let tag = Tag4::get(buf)?;
        match tag.flag {
          Expr::FLAG_SORT => {
            results.push(Expr::sort(tag.size));
          },
          Expr::FLAG_VAR => {
            results.push(Expr::var(tag.size));
          },
          Expr::FLAG_REF => {
            let ref_idx = get_u64(buf)?;
            let mut univ_indices =
              Vec::with_capacity(capped_capacity(tag.size, buf));
            for _ in 0..tag.size {
              univ_indices.push(get_u64(buf)?);
            }
            results.push(Expr::reference(ref_idx, univ_indices));
          },
          Expr::FLAG_REC => {
            let rec_idx = get_u64(buf)?;
            let mut univ_indices =
              Vec::with_capacity(capped_capacity(tag.size, buf));
            for _ in 0..tag.size {
              univ_indices.push(get_u64(buf)?);
            }
            results.push(Expr::rec(rec_idx, univ_indices));
          },
          Expr::FLAG_PRJ => {
            let type_ref_idx = get_u64(buf)?;
            // Parse val, then build Prj
            work.push(GetExprFrame::BuildPrj(type_ref_idx, tag.size));
            work.push(GetExprFrame::Parse); // val
          },
          Expr::FLAG_STR => {
            results.push(Expr::str(tag.size));
          },
          Expr::FLAG_NAT => {
            results.push(Expr::nat(tag.size));
          },
          Expr::FLAG_APP => {
            if tag.size == 0 {
              return Err("get_expr: App with zero args".to_string());
            }
            // Parse func, then collect args and wrap
            work.push(GetExprFrame::CollectApps(tag.size));
            work.push(GetExprFrame::Parse); // func
          },
          Expr::FLAG_LAM => {
            if tag.size == 0 {
              return Err("get_expr: Lam with zero binders".to_string());
            }
            // Start collecting types
            work.push(GetExprFrame::CollectLamType {
              collected: Vec::new(),
              remaining: tag.size,
            });
            work.push(GetExprFrame::Parse); // first type
          },
          Expr::FLAG_ALL => {
            if tag.size == 0 {
              return Err("get_expr: All with zero binders".to_string());
            }
            // Start collecting types
            work.push(GetExprFrame::CollectAllType {
              collected: Vec::new(),
              remaining: tag.size,
            });
            work.push(GetExprFrame::Parse); // first type
          },
          Expr::FLAG_LET => {
            // size=0 for dep, size=1 for non_dep
            let non_dep = tag.size != 0;
            work.push(GetExprFrame::BuildLet(non_dep));
            work.push(GetExprFrame::Parse); // body
            work.push(GetExprFrame::Parse); // val
            work.push(GetExprFrame::Parse); // ty
          },
          Expr::FLAG_SHARE => {
            results.push(Expr::share(tag.size));
          },
          f => return Err(format!("get_expr: invalid flag {f}")),
        }
      },
      GetExprFrame::BuildPrj(type_ref_idx, field_idx) => {
        let val = results.pop().ok_or("get_expr: missing val for Prj")?;
        results.push(Expr::prj(type_ref_idx, field_idx, val));
      },
      GetExprFrame::BuildApp => {
        let arg = results.pop().ok_or("get_expr: missing arg for App")?;
        let func = results.pop().ok_or("get_expr: missing func for App")?;
        results.push(Expr::app(func, arg));
      },
      GetExprFrame::CollectApps(remaining) => {
        if remaining == 0 {
          // All args collected, result is already on stack
        } else {
          // Parse next arg, apply to current func
          work.push(GetExprFrame::CollectApps(remaining - 1));
          work.push(GetExprFrame::BuildApp);
          work.push(GetExprFrame::Parse); // arg
        }
      },
      GetExprFrame::CollectLamType { mut collected, remaining } => {
        // Pop the just-parsed type
        let ty = results.pop().ok_or("get_expr: missing type for Lam")?;
        collected.push(ty);

        if remaining > 1 {
          // More types to collect
          work.push(GetExprFrame::CollectLamType {
            collected,
            remaining: remaining - 1,
          });
          work.push(GetExprFrame::Parse); // next type
        } else {
          // All types collected, now parse body
          work.push(GetExprFrame::BuildLams(collected));
          work.push(GetExprFrame::Parse); // body
        }
      },
      GetExprFrame::BuildLams(types) => {
        let mut body = results.pop().ok_or("get_expr: missing body for Lam")?;
        for ty in types.into_iter().rev() {
          body = Expr::lam(ty, body);
        }
        results.push(body);
      },
      GetExprFrame::CollectAllType { mut collected, remaining } => {
        // Pop the just-parsed type
        let ty = results.pop().ok_or("get_expr: missing type for All")?;
        collected.push(ty);

        if remaining > 1 {
          // More types to collect
          work.push(GetExprFrame::CollectAllType {
            collected,
            remaining: remaining - 1,
          });
          work.push(GetExprFrame::Parse); // next type
        } else {
          // All types collected, now parse body
          work.push(GetExprFrame::BuildAlls(collected));
          work.push(GetExprFrame::Parse); // body
        }
      },
      GetExprFrame::BuildAlls(types) => {
        let mut body = results.pop().ok_or("get_expr: missing body for All")?;
        for ty in types.into_iter().rev() {
          body = Expr::all(ty, body);
        }
        results.push(body);
      },
      GetExprFrame::BuildLet(non_dep) => {
        let body = results.pop().ok_or("get_expr: missing body for Let")?;
        let val = results.pop().ok_or("get_expr: missing val for Let")?;
        let ty = results.pop().ok_or("get_expr: missing ty for Let")?;
        results.push(Expr::let_(non_dep, ty, val, body));
      },
    }
  }

  results.pop().ok_or_else(|| "get_expr: no result".to_string())
}

// ============================================================================
// Constant serialization
// ============================================================================

impl DefKind {
  fn to_u8(self) -> u8 {
    match self {
      Self::Definition => 0,
      Self::Opaque => 1,
      Self::Theorem => 2,
    }
  }

  fn from_u8(x: u8) -> Result<Self, String> {
    match x {
      0 => Ok(Self::Definition),
      1 => Ok(Self::Opaque),
      2 => Ok(Self::Theorem),
      x => Err(format!("DefKind::from_u8: invalid {x}")),
    }
  }
}

fn definition_safety_to_u8(s: DefinitionSafety) -> u8 {
  match s {
    DefinitionSafety::Unsafe => 0,
    DefinitionSafety::Safe => 1,
    DefinitionSafety::Partial => 2,
  }
}

fn definition_safety_from_u8(x: u8) -> Result<DefinitionSafety, String> {
  match x {
    0 => Ok(DefinitionSafety::Unsafe),
    1 => Ok(DefinitionSafety::Safe),
    2 => Ok(DefinitionSafety::Partial),
    x => Err(format!("DefinitionSafety::from_u8: invalid {x}")),
  }
}

/// Pack DefKind (2 bits) and DefinitionSafety (2 bits) into a single byte.
fn pack_def_kind_safety(kind: DefKind, safety: DefinitionSafety) -> u8 {
  (kind.to_u8() << 2) | definition_safety_to_u8(safety)
}

/// Unpack DefKind and DefinitionSafety from a single byte.
fn unpack_def_kind_safety(
  b: u8,
) -> Result<(DefKind, DefinitionSafety), String> {
  let kind = DefKind::from_u8(b >> 2)?;
  let safety = definition_safety_from_u8(b & 0x3)?;
  Ok((kind, safety))
}

impl IxonByteSerde for QuotKind {
  fn put_ser(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Type => put_u8(0, buf),
      Self::Ctor => put_u8(1, buf),
      Self::Lift => put_u8(2, buf),
      Self::Ind => put_u8(3, buf),
    }
  }

  fn get_ser(buf: &mut &[u8]) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Type),
      1 => Ok(Self::Ctor),
      2 => Ok(Self::Lift),
      3 => Ok(Self::Ind),
      x => Err(format!("QuotKind::get: invalid {x}")),
    }
  }
}

fn put_sharing(sharing: &[Arc<Expr>], buf: &mut Vec<u8>) {
  put_u64(sharing.len() as u64, buf);
  for s in sharing {
    put_expr(s, buf);
  }
}

fn get_sharing(buf: &mut &[u8]) -> Result<Vec<Arc<Expr>>, String> {
  let num = get_u64(buf)?;
  let mut sharing = Vec::with_capacity(capped_capacity(num, buf));
  for _ in 0..num {
    sharing.push(get_expr(buf)?);
  }
  Ok(sharing)
}

impl Definition {
  pub fn put(&self, buf: &mut Vec<u8>) {
    // Pack DefKind + DefinitionSafety into single byte
    put_u8(pack_def_kind_safety(self.kind, self.safety), buf);
    put_u64(self.lvls, buf);
    put_expr(&self.typ, buf);
    put_expr(&self.value, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let (kind, safety) = unpack_def_kind_safety(get_u8(buf)?)?;
    let lvls = get_u64(buf)?;
    let typ = get_expr(buf)?;
    let value = get_expr(buf)?;
    Ok(Definition { kind, safety, lvls, typ, value })
  }
}

impl RecursorRule {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u64(self.fields, buf);
    put_expr(&self.rhs, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let fields = get_u64(buf)?;
    let rhs = get_expr(buf)?;
    Ok(RecursorRule { fields, rhs })
  }
}

impl Recursor {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u8(pack_bools([self.k, self.is_unsafe]), buf);
    put_u64(self.lvls, buf);
    put_u64(self.params, buf);
    put_u64(self.indices, buf);
    put_u64(self.motives, buf);
    put_u64(self.minors, buf);
    put_expr(&self.typ, buf);
    put_u64(self.rules.len() as u64, buf);
    for rule in &self.rules {
      rule.put(buf);
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let bools = unpack_bools(2, get_u8(buf)?);
    let lvls = get_u64(buf)?;
    let params = get_u64(buf)?;
    let indices = get_u64(buf)?;
    let motives = get_u64(buf)?;
    let minors = get_u64(buf)?;
    let typ = get_expr(buf)?;
    let num_rules = get_u64(buf)?;
    let mut rules = Vec::with_capacity(capped_capacity(num_rules, buf));
    for _ in 0..num_rules {
      rules.push(RecursorRule::get(buf)?);
    }
    Ok(Recursor {
      k: bools[0],
      is_unsafe: bools[1],
      lvls,
      params,
      indices,
      motives,
      minors,
      typ,
      rules,
    })
  }
}

impl Axiom {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_bool(self.is_unsafe, buf);
    put_u64(self.lvls, buf);
    put_expr(&self.typ, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let is_unsafe = get_bool(buf)?;
    let lvls = get_u64(buf)?;
    let typ = get_expr(buf)?;
    Ok(Axiom { is_unsafe, lvls, typ })
  }
}

impl Quotient {
  pub fn put(&self, buf: &mut Vec<u8>) {
    self.kind.put_ser(buf);
    put_u64(self.lvls, buf);
    put_expr(&self.typ, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let kind = QuotKind::get_ser(buf)?;
    let lvls = get_u64(buf)?;
    let typ = get_expr(buf)?;
    Ok(Quotient { kind, lvls, typ })
  }
}

impl Constructor {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_bool(self.is_unsafe, buf);
    put_u64(self.lvls, buf);
    put_u64(self.cidx, buf);
    put_u64(self.params, buf);
    put_u64(self.fields, buf);
    put_expr(&self.typ, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let is_unsafe = get_bool(buf)?;
    let lvls = get_u64(buf)?;
    let cidx = get_u64(buf)?;
    let params = get_u64(buf)?;
    let fields = get_u64(buf)?;
    let typ = get_expr(buf)?;
    Ok(Constructor { is_unsafe, lvls, cidx, params, fields, typ })
  }
}

impl Inductive {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u8(pack_bools([self.is_unsafe]), buf);
    put_u64(self.lvls, buf);
    put_u64(self.params, buf);
    put_u64(self.indices, buf);
    put_expr(&self.typ, buf);
    put_u64(self.ctors.len() as u64, buf);
    for ctor in &self.ctors {
      ctor.put(buf);
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let bools = unpack_bools(1, get_u8(buf)?);
    let lvls = get_u64(buf)?;
    let params = get_u64(buf)?;
    let indices = get_u64(buf)?;
    let typ = get_expr(buf)?;
    let num_ctors = get_u64(buf)?;
    let mut ctors = Vec::with_capacity(capped_capacity(num_ctors, buf));
    for _ in 0..num_ctors {
      ctors.push(Constructor::get(buf)?);
    }
    Ok(Inductive { is_unsafe: bools[0], lvls, params, indices, typ, ctors })
  }
}

impl InductiveProj {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u64(self.idx, buf);
    put_address(&self.block, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let idx = get_u64(buf)?;
    let block = get_address(buf)?;
    Ok(InductiveProj { idx, block })
  }
}

impl ConstructorProj {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u64(self.idx, buf);
    put_u64(self.cidx, buf);
    put_address(&self.block, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let idx = get_u64(buf)?;
    let cidx = get_u64(buf)?;
    let block = get_address(buf)?;
    Ok(ConstructorProj { idx, cidx, block })
  }
}

impl RecursorProj {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u64(self.idx, buf);
    put_address(&self.block, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let idx = get_u64(buf)?;
    let block = get_address(buf)?;
    Ok(RecursorProj { idx, block })
  }
}

impl DefinitionProj {
  pub fn put(&self, buf: &mut Vec<u8>) {
    put_u64(self.idx, buf);
    put_address(&self.block, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let idx = get_u64(buf)?;
    let block = get_address(buf)?;
    Ok(DefinitionProj { idx, block })
  }
}

impl MutConst {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Defn(d) => {
        put_u8(0, buf);
        d.put(buf);
      },
      Self::Indc(i) => {
        put_u8(1, buf);
        i.put(buf);
      },
      Self::Recr(r) => {
        put_u8(2, buf);
        r.put(buf);
      },
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    match get_u8(buf)? {
      0 => Ok(Self::Defn(Definition::get(buf)?)),
      1 => Ok(Self::Indc(Inductive::get(buf)?)),
      2 => Ok(Self::Recr(Recursor::get(buf)?)),
      x => Err(format!("MutConst::get: invalid tag {x}")),
    }
  }
}

impl ConstantInfo {
  /// Serialize a non-Muts ConstantInfo (Muts is handled separately in Constant::put)
  pub fn put(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Defn(d) => d.put(buf),
      Self::Recr(r) => r.put(buf),
      Self::Axio(a) => a.put(buf),
      Self::Quot(q) => q.put(buf),
      Self::CPrj(c) => c.put(buf),
      Self::RPrj(r) => r.put(buf),
      Self::IPrj(i) => i.put(buf),
      Self::DPrj(d) => d.put(buf),
      Self::Muts(_) => unreachable!("Muts handled in Constant::put"),
    }
  }

  /// Deserialize a non-Muts ConstantInfo (Muts is handled separately with FLAG_MUTS)
  pub fn get(variant: u64, buf: &mut &[u8]) -> Result<Self, String> {
    match variant {
      Self::CONST_DEFN => Ok(Self::Defn(Definition::get(buf)?)),
      Self::CONST_RECR => Ok(Self::Recr(Recursor::get(buf)?)),
      Self::CONST_AXIO => Ok(Self::Axio(Axiom::get(buf)?)),
      Self::CONST_QUOT => Ok(Self::Quot(Quotient::get(buf)?)),
      Self::CONST_CPRJ => Ok(Self::CPrj(ConstructorProj::get(buf)?)),
      Self::CONST_RPRJ => Ok(Self::RPrj(RecursorProj::get(buf)?)),
      Self::CONST_IPRJ => Ok(Self::IPrj(InductiveProj::get(buf)?)),
      Self::CONST_DPRJ => Ok(Self::DPrj(DefinitionProj::get(buf)?)),
      x => Err(format!("ConstantInfo::get: invalid variant {x}")),
    }
  }
}

fn put_refs(refs: &[Address], buf: &mut Vec<u8>) {
  put_u64(refs.len() as u64, buf);
  for r in refs {
    put_address(r, buf);
  }
}

fn get_refs(buf: &mut &[u8]) -> Result<Vec<Address>, String> {
  let num = get_u64(buf)?;
  let mut refs = Vec::with_capacity(capped_capacity(num, buf));
  for _ in 0..num {
    refs.push(get_address(buf)?);
  }
  Ok(refs)
}

fn put_univs(univs: &[Arc<Univ>], buf: &mut Vec<u8>) {
  put_u64(univs.len() as u64, buf);
  for u in univs {
    put_univ(u, buf);
  }
}

fn get_univs(buf: &mut &[u8]) -> Result<Vec<Arc<Univ>>, String> {
  let num = get_u64(buf)?;
  let mut univs = Vec::with_capacity(capped_capacity(num, buf));
  for _ in 0..num {
    univs.push(get_univ(buf)?);
  }
  Ok(univs)
}

impl Constant {
  pub fn put(&self, buf: &mut Vec<u8>) {
    match &self.info {
      ConstantInfo::Muts(mutuals) => {
        // Use FLAG_MUTS (0xC) with entry count in size field
        Tag4::new(Self::FLAG_MUTS, mutuals.len() as u64).put(buf);
        // Entries directly (no length prefix - it's in the tag)
        for m in mutuals {
          m.put(buf);
        }
      },
      _ => {
        // Use FLAG (0xD) with variant in size field (always 0-7, fits in 1 byte)
        Tag4::new(Self::FLAG, self.info.variant().unwrap()).put(buf);
        self.info.put(buf);
      },
    }
    put_sharing(&self.sharing, buf);
    put_refs(&self.refs, buf);
    put_univs(&self.univs, buf);
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let tag = Tag4::get(buf)?;
    let info = match tag.flag {
      Self::FLAG_MUTS => {
        // Muts: size field is entry count
        let mut mutuals = Vec::with_capacity(capped_capacity(tag.size, buf));
        for _ in 0..tag.size {
          mutuals.push(MutConst::get(buf)?);
        }
        ConstantInfo::Muts(mutuals)
      },
      Self::FLAG => {
        // Non-Muts: size field is variant
        ConstantInfo::get(tag.size, buf)?
      },
      _ => {
        return Err(format!(
          "Constant::get: expected flag {} or {}, got {}",
          Self::FLAG,
          Self::FLAG_MUTS,
          tag.flag
        ));
      },
    };
    let sharing = get_sharing(buf)?;
    let refs = get_refs(buf)?;
    let univs = get_univs(buf)?;
    Ok(Constant { info, sharing, refs, univs })
  }

  /// Serialize a constant and compute its content address.
  pub fn commit(&self) -> (Address, Vec<u8>) {
    let mut buf = Vec::new();
    self.put(&mut buf);
    let addr = Address::hash(&buf);
    (addr, buf)
  }
}

// ============================================================================
// Name serialization
// ============================================================================

use bignat::Nat;
use ix_common::env::{Name, NameData};
use rustc_hash::FxHashMap;

/// Serialize a Name to bytes (full recursive serialization, for standalone use).
pub fn put_name(name: &Name, buf: &mut Vec<u8>) {
  match name.as_data() {
    NameData::Anonymous(_) => {
      put_u8(0, buf);
    },
    NameData::Str(parent, s, _) => {
      put_u8(1, buf);
      put_name(parent, buf);
      put_u64(s.len() as u64, buf);
      buf.extend_from_slice(s.as_bytes());
    },
    NameData::Num(parent, n, _) => {
      put_u8(2, buf);
      put_name(parent, buf);
      let bytes = n.to_le_bytes();
      put_u64(bytes.len() as u64, buf);
      buf.extend_from_slice(&bytes);
    },
  }
}

/// Deserialize a Name from bytes (full recursive deserialization).
pub fn get_name(buf: &mut &[u8]) -> Result<Name, String> {
  match get_u8(buf)? {
    0 => Ok(Name::anon()),
    1 => {
      let parent = get_name(buf)?;
      let len = get_u64(buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "get_name: need {} bytes for string, have {}",
          len,
          buf.len()
        ));
      }
      let (s_bytes, rest) = buf.split_at(len);
      *buf = rest;
      let s = String::from_utf8(s_bytes.to_vec())
        .map_err(|_| "get_name: invalid UTF-8")?;
      Ok(Name::str(parent, s))
    },
    2 => {
      let parent = get_name(buf)?;
      let len = get_u64(buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "get_name: need {} bytes for nat, have {}",
          len,
          buf.len()
        ));
      }
      let (n_bytes, rest) = buf.split_at(len);
      *buf = rest;
      let n = Nat::from_le_bytes(n_bytes);
      Ok(Name::num(parent, n))
    },
    x => Err(format!("get_name: invalid tag {x}")),
  }
}

/// Serialize a Name component (references parent by address).
/// Format: tag (1 byte) + parent_addr (32 bytes) + data
fn put_name_component(name: &Name, buf: &mut Vec<u8>) {
  match name.as_data() {
    NameData::Anonymous(_) => {
      put_u8(0, buf);
    },
    NameData::Str(parent, s, _) => {
      put_u8(1, buf);
      put_bytes(parent.get_hash().as_bytes(), buf);
      put_u64(s.len() as u64, buf);
      buf.extend_from_slice(s.as_bytes());
    },
    NameData::Num(parent, n, _) => {
      put_u8(2, buf);
      put_bytes(parent.get_hash().as_bytes(), buf);
      let bytes = n.to_le_bytes();
      put_u64(bytes.len() as u64, buf);
      buf.extend_from_slice(&bytes);
    },
  }
}

/// Deserialize a Name component using a lookup table for parents.
fn get_name_component(
  buf: &mut &[u8],
  names: &FxHashMap<Address, Name>,
) -> Result<Name, String> {
  match get_u8(buf)? {
    0 => Ok(Name::anon()),
    1 => {
      let parent_addr = get_address(buf)?;
      let parent = names.get(&parent_addr).cloned().ok_or_else(|| {
        format!("get_name_component: missing parent {:?}", parent_addr)
      })?;
      let len = get_u64(buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "get_name_component: need {} bytes, have {}",
          len,
          buf.len()
        ));
      }
      let (s_bytes, rest) = buf.split_at(len);
      *buf = rest;
      let s = String::from_utf8(s_bytes.to_vec())
        .map_err(|_| "get_name_component: invalid UTF-8")?;
      Ok(Name::str(parent, s))
    },
    2 => {
      let parent_addr = get_address(buf)?;
      let parent = names.get(&parent_addr).cloned().ok_or_else(|| {
        format!("get_name_component: missing parent {:?}", parent_addr)
      })?;
      let len = get_u64(buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "get_name_component: need {} bytes, have {}",
          len,
          buf.len()
        ));
      }
      let (n_bytes, rest) = buf.split_at(len);
      *buf = rest;
      let n = Nat::from_le_bytes(n_bytes);
      Ok(Name::num(parent, n))
    },
    x => Err(format!("get_name_component: invalid tag {x}")),
  }
}

// ============================================================================
// Named serialization
// ============================================================================

use super::env::{AuxLayout, Named};
use super::metadata::{ConstantMeta, NameIndex, NameReverseIndex};

/// Serialize an `AuxLayout` side-table entry.
///
/// Encoding: two Vec<u64> telescopes. `usize` is written/read as `u64`
/// (via `put_u64` / `Tag0`) to avoid target-word-size divergence in
/// cross-platform serialized envs.
pub fn put_aux_layout(layout: &AuxLayout, buf: &mut Vec<u8>) {
  put_u64(layout.perm.len() as u64, buf);
  for &p in &layout.perm {
    put_u64(p as u64, buf);
  }
  put_u64(layout.source_ctor_counts.len() as u64, buf);
  for &c in &layout.source_ctor_counts {
    put_u64(c as u64, buf);
  }
}

/// Deserialize an `AuxLayout` side-table entry.
pub fn get_aux_layout(buf: &mut &[u8]) -> Result<AuxLayout, String> {
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
  Ok(AuxLayout { perm, source_ctor_counts })
}

/// Serialize a Named entry with indexed metadata.
pub fn put_named_indexed(
  named: &Named,
  idx: &NameIndex,
  buf: &mut Vec<u8>,
) -> Result<(), String> {
  put_address(&named.addr, buf);
  named.meta.put_indexed(idx, buf)?;
  // Serialize original as Option: 0 = None, 1 = Some(addr, meta)
  match &named.original {
    None => buf.push(0),
    Some((addr, meta)) => {
      buf.push(1);
      put_address(addr, buf);
      meta.put_indexed(idx, buf)?;
    },
  }
  Ok(())
}

/// Deserialize a Named entry with indexed metadata.
pub fn get_named_indexed(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<Named, String> {
  let addr = get_address(buf)?;
  let meta = ConstantMeta::get_indexed(buf, rev)?;
  let original = match get_u8(buf)? {
    0 => None,
    1 => {
      let orig_addr = get_address(buf)?;
      let orig_meta = ConstantMeta::get_indexed(buf, rev)?;
      Some((orig_addr, orig_meta))
    },
    x => return Err(format!("Named.original: invalid tag {x}")),
  };
  Ok(Named { addr, meta, original })
}

// ============================================================================
// Env serialization
// ============================================================================

use super::comm::Comm;
use super::env::{Env, LazyConstSlice, LazyIndex, LazyNamed};
use super::merkle::{merkle_root_canonical, zero_address};

impl Env {
  /// Tag4 flag for Env (0xE), variant 0.
  pub const FLAG: u8 = 0xE;

  /// Serialize an Env to bytes.
  ///
  /// Streaming design: for each section, collect only the *keys* from the
  /// underlying DashMap, sort them (in parallel for the big ones), then
  /// look up each value via `DashMap::get` and serialize it. The `Ref`
  /// guard returned by `get` drops at the end of each loop iteration, so
  /// at most one value is held live beyond the DashMap's own storage —
  /// peak RAM stays close to the steady-state env size instead of 2×.
  ///
  /// Why not just iterate the DashMap directly? Serialization requires a
  /// canonical order (byte-determinism across runs and across different
  /// insertion orders), and DashMap iteration order is shard-dependent.
  /// Sorting the keys is the minimum work to guarantee that.
  pub fn put(&self, buf: &mut Vec<u8>) -> Result<(), String> {
    #[cfg(not(target_arch = "riscv64"))]
    use rayon::slice::ParallelSliceMut;

    // Chatty per-section logging gated on IX_QUIET=1 (disables) so we can
    // diagnose serialization stalls on huge envs (Mathlib: ~1M consts).
    let quiet = std::env::var("IX_QUIET").is_ok();
    let overall_start = std::time::Instant::now();

    // Header: Tag4 with flag=0xE, size=0 (Env variant)
    Tag4::new(Self::FLAG, 0).put(buf);

    // ─────────────────────────────────────────────────────────────────────
    // Canonical merkle root over consts.keys()
    //
    // Hoisted before section 1 so we can sort const_addrs once and reuse
    // it for section 2 below. Always 32 bytes (non-optional) — empty
    // const sets serialize as `zero_address()` (a fixed sentinel that
    // cannot collide with any non-empty canonical root since
    // `merkle_root_canonical` always returns a Blake3 hash for n>=1).
    // Verifiers recompute on deserialize and reject mismatches.
    // ─────────────────────────────────────────────────────────────────────
    let mut const_addrs: Vec<Address> =
      self.consts.iter().map(|e| e.key().clone()).collect();
    #[cfg(not(target_arch = "riscv64"))]
    const_addrs.par_sort_unstable();
    #[cfg(target_arch = "riscv64")]
    const_addrs.sort_unstable();
    let root = merkle_root_canonical(&const_addrs).unwrap_or_else(zero_address);
    put_address(&root, buf);

    // ─────────────────────────────────────────────────────────────────────
    // Section 1: Blobs (Address -> bytes)
    // ─────────────────────────────────────────────────────────────────────
    let sec_start = std::time::Instant::now();
    if !quiet {
      eprintln!("[Env::put] section 1/5 blobs: {} entries", self.blobs.len(),);
    }
    let mut blob_addrs: Vec<Address> =
      self.blobs.iter().map(|e| e.key().clone()).collect();
    #[cfg(not(target_arch = "riscv64"))]
    blob_addrs.par_sort_unstable();
    #[cfg(target_arch = "riscv64")]
    blob_addrs.sort_unstable();
    put_u64(blob_addrs.len() as u64, buf);
    for addr in &blob_addrs {
      if let Some(entry) = self.blobs.get(addr) {
        let bytes = entry.value();
        put_address(addr, buf);
        put_u64(bytes.len() as u64, buf);
        buf.extend_from_slice(bytes);
      }
    }
    if !quiet {
      eprintln!(
        "[Env::put] section 1/5 blobs done in {:.1}s ({} bytes so far)",
        sec_start.elapsed().as_secs_f64(),
        buf.len(),
      );
    }

    // ─────────────────────────────────────────────────────────────────────
    // Section 2: Consts (Address -> Constant)
    //
    // Reuses the already-collected+sorted `const_addrs` from the merkle
    // root computation above.
    // ─────────────────────────────────────────────────────────────────────
    let sec_start = std::time::Instant::now();
    if !quiet {
      eprintln!("[Env::put] section 2/5 consts: {} entries", self.consts.len(),);
    }
    if !quiet {
      eprintln!(
        "[Env::put] section 2/5 consts: collected+sorted in {:.1}s, \
         streaming put...",
        sec_start.elapsed().as_secs_f64(),
      );
    }
    let put_start = std::time::Instant::now();
    put_u64(const_addrs.len() as u64, buf);
    for addr in &const_addrs {
      if let Some(entry) = self.consts.get(addr) {
        put_address(addr, buf);
        // Length-prefix sidecar (Tag0) so lazy loaders can slice each
        // constant without parsing its Tag4 envelope. The length is
        // NOT part of the content-addressed bytes — `Address::hash` is
        // computed only over `raw_bytes()`.
        let bytes = entry.value().raw_bytes();
        Tag0::new(bytes.len() as u64).put(buf);
        buf.extend_from_slice(bytes);
      }
    }
    if !quiet {
      eprintln!(
        "[Env::put] section 2/5 consts done: put in {:.1}s, total {:.1}s \
         ({} bytes so far)",
        put_start.elapsed().as_secs_f64(),
        sec_start.elapsed().as_secs_f64(),
        buf.len(),
      );
    }

    // ─────────────────────────────────────────────────────────────────────
    // Section 3: Names (Address -> Name component, topologically sorted)
    // ─────────────────────────────────────────────────────────────────────
    // Topological sort ensures parents come before children so the name
    // index assigned during serialization is valid for all references that
    // follow (e.g., in metadata). `topological_sort_names` handles the
    // parallel key sort + DFS; see that function for details.
    let sec_start = std::time::Instant::now();
    if !quiet {
      eprintln!(
        "[Env::put] section 3/5 names: topo-sorting {} entries",
        self.names.len(),
      );
    }
    let sorted_names = topological_sort_names(&self.names);
    if !quiet {
      eprintln!(
        "[Env::put] section 3/5 names: topo-sorted in {:.1}s, serializing...",
        sec_start.elapsed().as_secs_f64(),
      );
    }
    let put_start = std::time::Instant::now();
    let mut name_index: NameIndex = NameIndex::new();
    put_u64(sorted_names.len() as u64, buf);
    for (i, (addr, name)) in sorted_names.iter().enumerate() {
      name_index.insert(addr.clone(), i as u64);
      put_address(addr, buf);
      put_name_component(name, buf);
    }
    if !quiet {
      eprintln!(
        "[Env::put] section 3/5 names done: put in {:.1}s, total {:.1}s \
         ({} bytes so far)",
        put_start.elapsed().as_secs_f64(),
        sec_start.elapsed().as_secs_f64(),
        buf.len(),
      );
    }

    // ─────────────────────────────────────────────────────────────────────
    // Section 4: Named (Name -> Named metadata with indexed addresses)
    // ─────────────────────────────────────────────────────────────────────
    // Named values are the *largest* per-entry (each carries a ConstantMeta
    // with metadata arenas), so the streaming pattern's win is greatest
    // here: on Mathlib, avoiding the clone-into-Vec saves ~30 GB peak RAM.
    //
    // Key clone cost: a `Name` is `Arc<NameData>`, so each clone is a
    // single atomic refcount increment (<1s for 733k).
    let sec_start = std::time::Instant::now();
    if !quiet {
      eprintln!("[Env::put] section 4/5 named: {} entries", self.named.len(),);
    }
    let mut named_keys: Vec<Name> =
      self.named.iter().map(|e| e.key().clone()).collect();
    // Sort by the cached name hash bytes (same key used by every existing
    // Section 4 ordering guarantee). `par_sort_unstable_by` uses rayon to
    // parallelize the compare across all cores.
    #[cfg(not(target_arch = "riscv64"))]
    named_keys.par_sort_unstable_by(|a, b| {
      a.get_hash().as_bytes().cmp(b.get_hash().as_bytes())
    });
    #[cfg(target_arch = "riscv64")]
    named_keys.sort_unstable_by(|a, b| {
      a.get_hash().as_bytes().cmp(b.get_hash().as_bytes())
    });
    if !quiet {
      eprintln!(
        "[Env::put] section 4/5 named: collected+sorted in {:.1}s, \
         streaming put...",
        sec_start.elapsed().as_secs_f64(),
      );
    }
    let put_start = std::time::Instant::now();
    put_u64(named_keys.len() as u64, buf);
    for name in &named_keys {
      if let Some(entry) = self.named.get(name) {
        put_bytes(name.get_hash().as_bytes(), buf);
        put_named_indexed(entry.value(), &name_index, buf)?;
      }
    }
    if !quiet {
      eprintln!(
        "[Env::put] section 4/5 named done: put in {:.1}s, total {:.1}s \
         ({} bytes so far)",
        put_start.elapsed().as_secs_f64(),
        sec_start.elapsed().as_secs_f64(),
        buf.len(),
      );
    }

    // ─────────────────────────────────────────────────────────────────────
    // Section 5: Comms (Address -> Comm) — typically empty on compile path
    // ─────────────────────────────────────────────────────────────────────
    let sec_start = std::time::Instant::now();
    if !quiet {
      eprintln!("[Env::put] section 5/5 comms: {} entries", self.comms.len(),);
    }
    let mut comm_addrs: Vec<Address> =
      self.comms.iter().map(|e| e.key().clone()).collect();
    #[cfg(not(target_arch = "riscv64"))]
    comm_addrs.par_sort_unstable();
    #[cfg(target_arch = "riscv64")]
    comm_addrs.sort_unstable();
    put_u64(comm_addrs.len() as u64, buf);
    for addr in &comm_addrs {
      if let Some(entry) = self.comms.get(addr) {
        put_address(addr, buf);
        entry.value().put(buf);
      }
    }
    if !quiet {
      eprintln!(
        "[Env::put] section 5/5 comms done in {:.1}s ({} bytes so far)",
        sec_start.elapsed().as_secs_f64(),
        buf.len(),
      );
    }

    // Optional trailing section: anon_hints (Address -> ReducibilityHints).
    // `get_anon` normally HARVESTS hints from the Named section; a closure
    // sub-env (built for shard injection) DROPS that section, which would
    // force the kernel to `Regular(0)` and add a def-eq overhead vs whole-env
    // proving. Carrying the hints here lets the guest reproduce vanilla kernel
    // behavior exactly. Written only when populated, so compiler-produced
    // `.ixe` (empty map) are byte-identical to before; loaders read it only if
    // bytes remain after comms. Hints are performance-only (the `Regular(0)`
    // fallback is always correct), so this section is intentionally NOT covered
    // by the consts merkle root.
    if !self.anon_hints.is_empty() {
      let mut hint_addrs: Vec<Address> =
        self.anon_hints.keys().cloned().collect();
      hint_addrs.sort_unstable();
      put_u64(hint_addrs.len() as u64, buf);
      for addr in &hint_addrs {
        put_address(addr, buf);
        self.anon_hints[addr].put_ser(buf);
      }
    }

    if !quiet {
      eprintln!(
        "[Env::put] ALL DONE: {} bytes in {:.1}s",
        buf.len(),
        overall_start.elapsed().as_secs_f64(),
      );
    }
    Ok(())
  }

  /// Deserialize an Env from bytes.
  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    // Header
    let tag = Tag4::get(buf)?;
    if tag.flag != Self::FLAG {
      return Err(format!(
        "Env::get: expected flag 0x{:X}, got 0x{:X}",
        Self::FLAG,
        tag.flag
      ));
    }
    if tag.size != 0 {
      return Err(format!(
        "Env::get: expected Env variant 0, got {}",
        tag.size
      ));
    }

    // Canonical merkle root (fixed 32 bytes). For empty const sets the
    // stored value is `zero_address()`. Verified against the
    // recomputed value at the end of deserialization.
    let stored_root = get_address(buf)?;

    #[cfg_attr(not(target_arch = "riscv64"), allow(unused_mut))]
    let mut env = Env::new();

    // Section 1: Blobs
    let num_blobs = get_u64(buf)?;
    for _ in 0..num_blobs {
      let addr = get_address(buf)?;
      let len = get_u64(buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "Env::get: need {} bytes for blob, have {}",
          len,
          buf.len()
        ));
      }
      let (bytes, rest) = buf.split_at(len);
      *buf = rest;
      env.blobs.insert(addr, bytes.to_vec());
    }

    // Section 2: Consts (lazy: read length prefix, slice bytes, defer parse)
    let num_consts = get_u64(buf)?;
    for i in 0..num_consts {
      let addr = get_address(buf)?;
      let len = Tag0::get(buf)?.size as usize;
      if buf.len() < len {
        return Err(format!(
          "Env::get: need {} bytes for constant, have {}",
          len,
          buf.len()
        ));
      }
      let (bytes, rest) = buf.split_at(len);
      *buf = rest;
      // Per-entry integrity: hash the bytes and compare with the
      // stored address. The env-level merkle root over `consts.keys()`
      // catches missing/extra entries but not byte-tampering of a
      // constant whose key is intact; without this check, corruption
      // would slip past `Env::get` and surface much later as a
      // misleading parse error inside `LazyConstant::get`.
      let computed = Address::hash(bytes);
      if computed != addr {
        return Err(format!(
          "Env::get: const at idx {i} bytes hash to {} but stored under {}",
          computed.hex(),
          addr.hex()
        ));
      }
      env
        .consts
        .insert(addr, crate::lazy::LazyConstant::from_bytes(bytes.into()));
    }

    // Section 3: Names (build lookup table and reverse index for metadata)
    let num_names = get_u64(buf)?;
    let mut names_lookup: FxHashMap<Address, Name> = FxHashMap::default();
    let mut name_reverse_index: NameReverseIndex =
      Vec::with_capacity(num_names as usize + 1);
    // Anonymous name is serialized first (index 0) — read it from the stream
    // along with all other names below. But pre-seed the lookup so name
    // reconstruction works for names whose parent is anonymous.
    let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
    names_lookup.insert(anon_addr.clone(), Name::anon());
    env.names.insert(anon_addr, Name::anon());
    for _ in 0..num_names {
      let addr = get_address(buf)?;
      let name = get_name_component(buf, &names_lookup)?;
      name_reverse_index.push(addr.clone());
      names_lookup.insert(addr.clone(), name.clone());
      env.names.insert(addr, name);
    }

    // Section 4: Named (use indexed deserialization for metadata)
    let num_named = get_u64(buf)?;
    for _ in 0..num_named {
      let name_addr = get_address(buf)?;
      let named = get_named_indexed(buf, &name_reverse_index)?;
      let name = names_lookup.get(&name_addr).cloned().ok_or_else(|| {
        format!("Env::get: missing name for addr {:?}", name_addr)
      })?;
      env.named.insert(name, named);
    }

    // Section 5: Comms
    let num_comms = get_u64(buf)?;
    for _ in 0..num_comms {
      let addr = get_address(buf)?;
      let comm = Comm::get(buf)?;
      env.comms.insert(addr, comm);
    }

    // Optional trailing anon_hints section (see `Env::put`).
    read_anon_hints_section(buf, &mut env)?;

    // Verify the stored merkle root matches what we'd compute from
    // env.consts. Empty const set → expected = zero_address().
    // Rejects any tampering with the header.
    let mut const_addrs: Vec<Address> =
      env.consts.iter().map(|e| e.key().clone()).collect();
    const_addrs.sort_unstable();
    let computed_root =
      merkle_root_canonical(&const_addrs).unwrap_or_else(zero_address);
    if computed_root != stored_root {
      return Err(format!(
        "Env::get: merkle root mismatch (stored={}, computed={})",
        stored_root.hex(),
        computed_root.hex(),
      ));
    }

    Ok(env)
  }

  /// Parse an `.ixe` buffer into a metadata-light, **zero-copy** index for the
  /// anon/lazy check path (see [`LazyIndex`]). Mirrors [`Env::get`]'s section
  /// walk and reuses the same battle-tested parsers (so every metadata variant
  /// — e.g. `CallSite` — is handled), but:
  ///
  /// - constants are recorded as `(addr, offset, len)` windows into `data`
  ///   rather than copied/stored, and their bodies are never parsed here;
  /// - the `names` table and each `Named`'s `ExprMetaArena` are parsed only to
  ///   advance the cursor and are then dropped, keeping just `name → addr` and
  ///   the per-`Defn` reducibility hint;
  /// - `comms` are skipped entirely.
  ///
  /// `data` must be the whole buffer (offsets are relative to its start). The
  /// env-level merkle root over const addresses is still re-verified.
  pub fn parse_lazy_index(data: &[u8]) -> Result<LazyIndex, String> {
    let mut buf: &[u8] = data;

    // Header: Tag4 (flag/variant) + canonical merkle root.
    let tag = Tag4::get(&mut buf)?;
    if tag.flag != Self::FLAG {
      return Err(format!(
        "parse_lazy_index: expected flag 0x{:X}, got 0x{:X}",
        Self::FLAG,
        tag.flag
      ));
    }
    if tag.size != 0 {
      return Err(format!(
        "parse_lazy_index: expected Env variant 0, got {}",
        tag.size
      ));
    }
    let stored_root = get_address(&mut buf)?;

    let mut index = LazyIndex::default();

    // Section 1: Blobs (copied — small, and the kernel ingests their bytes).
    let num_blobs = get_u64(&mut buf)?;
    for _ in 0..num_blobs {
      let addr = get_address(&mut buf)?;
      let len = get_u64(&mut buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "parse_lazy_index: need {} bytes for blob, have {}",
          len,
          buf.len()
        ));
      }
      let (bytes, rest) = buf.split_at(len);
      buf = rest;
      index.blobs.push((addr, bytes.to_vec()));
    }

    // Section 2: Consts — record offset windows, never parse the bodies.
    let num_consts = get_u64(&mut buf)?;
    for _ in 0..num_consts {
      let addr = get_address(&mut buf)?;
      let len = Tag0::get(&mut buf)?.size as usize;
      // Position of the body within `data` = bytes consumed so far.
      let offset = data.len() - buf.len();
      if buf.len() < len {
        return Err(format!(
          "parse_lazy_index: need {} bytes for constant, have {}",
          len,
          buf.len()
        ));
      }
      buf = &buf[len..];
      index.consts.push(LazyConstSlice { addr, offset, len });
    }

    // Section 3: Names — parsed to build the index for metadata decoding, then
    // dropped (the check never consults the name component table).
    let num_names = get_u64(&mut buf)?;
    let mut names_lookup: FxHashMap<Address, Name> = FxHashMap::default();
    let mut name_reverse_index: NameReverseIndex =
      Vec::with_capacity(num_names as usize + 1);
    let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
    names_lookup.insert(anon_addr, Name::anon());
    for _ in 0..num_names {
      let addr = get_address(&mut buf)?;
      let name = get_name_component(&mut buf, &names_lookup)?;
      name_reverse_index.push(addr.clone());
      names_lookup.insert(addr, name);
    }

    // Section 4: Named — keep `name → addr` and the Defn reducibility hint; the
    // full ConstantMeta (arena, CallSite, ...) is parsed then discarded.
    let num_named = get_u64(&mut buf)?;
    for _ in 0..num_named {
      let name_addr = get_address(&mut buf)?;
      let named = get_named_indexed(&mut buf, &name_reverse_index)?;
      let name = names_lookup.get(&name_addr).cloned().ok_or_else(|| {
        format!("parse_lazy_index: missing name for addr {:?}", name_addr)
      })?;
      let hint = match &named.meta.info {
        super::metadata::ConstantMetaInfo::Def { hints, .. } => Some(*hints),
        _ => None,
      };
      index.named.push(LazyNamed { name, addr: named.addr, hint });
    }

    // Section 5 (comms) is skipped: not needed by the check path.

    // Re-verify the merkle root over const addresses (header integrity).
    let mut const_addrs: Vec<Address> =
      index.consts.iter().map(|c| c.addr.clone()).collect();
    const_addrs.sort_unstable();
    let computed_root =
      merkle_root_canonical(&const_addrs).unwrap_or_else(zero_address);
    if computed_root != stored_root {
      return Err(format!(
        "parse_lazy_index: merkle root mismatch (stored={}, computed={})",
        stored_root.hex(),
        computed_root.hex(),
      ));
    }

    Ok(index)
  }

  /// Anonymous-only deserialization: read the header + blobs +
  /// consts sections, parse-and-discard the metadata sections
  /// (names / named / comms).
  ///
  /// Returns an `Env` with populated `consts` (lazy) and `blobs`, and
  /// **empty** `named` / `names` / `comms`. The merkle-root header is
  /// re-verified against the recomputed root over `consts.keys()`,
  /// exactly as in [`Env::get`].
  ///
  /// Why "parse and discard"? Sections 3-5 lack a section-level length
  /// prefix today (only section 2 has one), so we can't byte-skip
  /// them without parsing. Parsing into local scopes that drop on
  /// return still wins us the steady-state memory: the returned `Env`
  /// is metadata-free, and the temporary lookup tables / parsed
  /// metadata values are reclaimed before this function returns.
  ///
  /// Used by the anon-mode kernel path so a verifier holding only
  /// content addresses doesn't pay the long-term cost of metadata
  /// sections it will never consult.
  pub fn get_anon(buf: &mut &[u8]) -> Result<Self, String> {
    // Header (same as Env::get)
    let tag = Tag4::get(buf)?;
    if tag.flag != Self::FLAG {
      return Err(format!(
        "Env::get_anon: expected flag 0x{:X}, got 0x{:X}",
        Self::FLAG,
        tag.flag
      ));
    }
    if tag.size != 0 {
      return Err(format!(
        "Env::get_anon: expected Env variant 0, got {}",
        tag.size
      ));
    }
    let stored_root = get_address(buf)?;

    let mut env = Env::new();

    // Section 1: Blobs (kept)
    let num_blobs = get_u64(buf)?;
    for _ in 0..num_blobs {
      let addr = get_address(buf)?;
      let len = get_u64(buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "Env::get_anon: need {} bytes for blob, have {}",
          len,
          buf.len()
        ));
      }
      let (bytes, rest) = buf.split_at(len);
      *buf = rest;
      env.blobs.insert(addr, bytes.to_vec());
    }

    // Section 2: Consts (kept, lazy)
    let num_consts = get_u64(buf)?;
    for i in 0..num_consts {
      let addr = get_address(buf)?;
      let len = Tag0::get(buf)?.size as usize;
      if buf.len() < len {
        return Err(format!(
          "Env::get_anon: need {} bytes for constant, have {}",
          len,
          buf.len()
        ));
      }
      let (bytes, rest) = buf.split_at(len);
      *buf = rest;
      let computed = Address::hash(bytes);
      if computed != addr {
        return Err(format!(
          "Env::get_anon: const at idx {i} bytes hash to {} but stored under {}",
          computed.hex(),
          addr.hex()
        ));
      }
      env
        .consts
        .insert(addr, crate::lazy::LazyConstant::from_bytes(bytes.into()));
    }

    // Section 3: Names — parse and DISCARD. We still need a populated
    // `names_lookup` and `name_reverse_index` so section 4's indexed
    // metadata parses correctly, but both go out of scope before
    // returning so the steady-state `Env` carries no name data.
    let num_names = get_u64(buf)?;
    let mut names_lookup: FxHashMap<Address, Name> = FxHashMap::default();
    let mut name_reverse_index: NameReverseIndex =
      Vec::with_capacity(num_names as usize + 1);
    let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
    names_lookup.insert(anon_addr, Name::anon());
    for _ in 0..num_names {
      let addr = get_address(buf)?;
      let name = get_name_component(buf, &names_lookup)?;
      name_reverse_index.push(addr.clone());
      names_lookup.insert(addr, name);
    }

    // Section 4: Named — parse and mostly discard, but harvest
    // `ReducibilityHints` from each `Def` variant into `env.anon_hints`.
    // Hints are performance advice (lazy-delta tiebreak); the kernel's
    // anon-mode correctness model is preserved either way. Without
    // them, every Definition is forced to `Regular(0)` and the kernel
    // can chew through `MAX_WHNF_FUEL` on definitions Lean would have
    // marked `Abbrev`/`Regular(h)`.
    let num_named = get_u64(buf)?;
    for _ in 0..num_named {
      let _name_addr = get_address(buf)?;
      let named = get_named_indexed(buf, &name_reverse_index)?;
      if let super::metadata::ConstantMetaInfo::Def { hints, .. } =
        &named.meta.info
      {
        env.anon_hints.insert(named.addr.clone(), *hints);
      }
    }

    // Section 5: Comms — parse and DISCARD.
    let num_comms = get_u64(buf)?;
    for _ in 0..num_comms {
      let _addr = get_address(buf)?;
      let _comm = Comm::get(buf)?;
    }

    // Optional trailing anon_hints section (see `Env::put`). For a closure
    // sub-env this carries the hints the dropped Named section would have, so
    // the kernel reproduces vanilla behavior with no def-eq overhead.
    read_anon_hints_section(buf, &mut env)?;

    drop(names_lookup);
    drop(name_reverse_index);

    // Verify merkle root over loaded consts.
    let mut const_addrs: Vec<Address> =
      env.consts.iter().map(|e| e.key().clone()).collect();
    const_addrs.sort_unstable();
    let computed_root =
      merkle_root_canonical(&const_addrs).unwrap_or_else(zero_address);
    if computed_root != stored_root {
      return Err(format!(
        "Env::get_anon: merkle root mismatch (stored={}, computed={})",
        stored_root.hex(),
        computed_root.hex(),
      ));
    }

    Ok(env)
  }

  /// Memory-mapped sibling of [`Env::get_anon`]. Opens the `.ixe`
  /// file with `mmap`, parses the header + section layout, and stores
  /// every Section-2 constant as a [`LazyConstant`] window into the
  /// mapping. No heap copy of constant bytes — the OS page cache is
  /// the source of truth, paged in on demand.
  ///
  /// The returned `Env` carries an internal `Arc<Mmap>` (via each
  /// `LazyConstant`'s [`super::lazy::BytesSource::Mmap`] variant), so
  /// the mapping stays alive as long as any consumer holds the env or
  /// any clone of a `LazyConstant` from it.
  ///
  /// Sections 1 (blobs), 3 (names), 4 (named), and 5 (comms) are
  /// handled the same way as `get_anon`: blobs are heap-copied (they
  /// are small and consumed eagerly), names and named are
  /// parse-and-discard (with hints harvested into `env.anon_hints`),
  /// comms are skipped.
  ///
  /// On Linux, the kernel's adaptive readahead handles the linear
  /// scan during section parsing efficiently; subsequent random
  /// access from worker kernel-check threads pages in as needed.
  #[cfg(not(target_arch = "riscv64"))]
  pub fn get_anon_mmap(path: &std::path::Path) -> Result<Self, String> {
    let file = std::fs::File::open(path).map_err(|e| {
      format!("Env::get_anon_mmap: open {}: {e}", path.display())
    })?;
    // Capture the file size at open so we can validate the mapping
    // covers the bytes we believe we're parsing. The kernel will
    // happily map MAP_PRIVATE with a smaller size than we expect (if
    // the file was truncated between `open` and `mmap`); without
    // this check our cursor-vs-len bounds tests in the section
    // parsers would still catch most mismatches, but anyone reading
    // past the truncation point through a `LazyConstant` window
    // later would SIGBUS with no diagnostic. If `metadata()` fails
    // we proceed without the check — better to attempt the mmap
    // than to fail open on a transient stat error.
    //
    // Caveat: this is a snapshot at-open. If the file is replaced
    // (rather than truncated in-place) while we hold the mmap, our
    // pages remain valid (mmap pins the inode). If it's truncated
    // in-place, subsequent page faults beyond the new EOF SIGBUS;
    // we accept that as a contract violation (don't rewrite the
    // .ixe underneath a running check) and document it.
    let expected_len = file.metadata().ok().map(|m| m.len() as usize);
    // SAFETY: We treat the mapping as read-only and never alias it
    // mutably. Other processes truncating or replacing the file while
    // it is mapped would invalidate our slices; that is a contract
    // the caller is expected to honor (don't modify the .ixe
    // underfoot). See the `expected_len` check below for the
    // open-time size sanity guard.
    let mmap = unsafe {
      memmap2::Mmap::map(&file).map_err(|e| {
        format!("Env::get_anon_mmap: mmap {}: {e}", path.display())
      })?
    };
    if let Some(expected) = expected_len
      && mmap.len() != expected
    {
      return Err(format!(
        "Env::get_anon_mmap: file size changed under us \
         (stat={expected} bytes, mmap={} bytes); refuse to load",
        mmap.len()
      ));
    }
    let mmap = Arc::new(mmap);

    // `buf` is a moving cursor over `mmap[..]`. We compute byte
    // offsets via `mmap.len() - buf.len()` so we can record per-const
    // (offset, len) windows for `LazyConstant::from_mmap_slice`.
    let mmap_full: &[u8] = &mmap[..];
    let mut buf: &[u8] = mmap_full;

    // Header (same shape as Env::get_anon)
    let tag = Tag4::get(&mut buf)?;
    if tag.flag != Self::FLAG {
      return Err(format!(
        "Env::get_anon_mmap: expected flag 0x{:X}, got 0x{:X}",
        Self::FLAG,
        tag.flag
      ));
    }
    if tag.size != 0 {
      return Err(format!(
        "Env::get_anon_mmap: expected Env variant 0, got {}",
        tag.size
      ));
    }
    let stored_root = get_address(&mut buf)?;

    let mut env = Env::new();

    // Section 1: Blobs (heap-copied; small, eagerly consumed)
    let num_blobs = get_u64(&mut buf)?;
    for _ in 0..num_blobs {
      let addr = get_address(&mut buf)?;
      let len = get_u64(&mut buf)? as usize;
      if buf.len() < len {
        return Err(format!(
          "Env::get_anon_mmap: need {} bytes for blob, have {}",
          len,
          buf.len()
        ));
      }
      let (bytes, rest) = buf.split_at(len);
      buf = rest;
      env.blobs.insert(addr, bytes.to_vec());
    }

    // Section 2: Consts (mmap-backed lazy windows)
    let num_consts = get_u64(&mut buf)?;
    for i in 0..num_consts {
      let addr = get_address(&mut buf)?;
      let len = Tag0::get(&mut buf)?.size as usize;
      if buf.len() < len {
        return Err(format!(
          "Env::get_anon_mmap: need {} bytes for constant, have {}",
          len,
          buf.len()
        ));
      }
      // `buf` is a suffix of `mmap_full`; the constant's bytes start
      // at the current cursor and span `len` bytes.
      let offset = mmap_full.len() - buf.len();
      let bytes = &mmap_full[offset..offset + len];
      let computed = Address::hash(bytes);
      if computed != addr {
        return Err(format!(
          "Env::get_anon_mmap: const at idx {i} bytes hash to {} but stored under {}",
          computed.hex(),
          addr.hex()
        ));
      }
      env.consts.insert(
        addr,
        crate::lazy::LazyConstant::from_mmap_slice(
          Arc::clone(&mmap),
          offset,
          len,
        ),
      );
      buf = &buf[len..];
    }

    // Section 3: Names — parse and DISCARD (needed transiently so
    // section 4's indexed metadata can be decoded).
    let num_names = get_u64(&mut buf)?;
    let mut names_lookup: FxHashMap<Address, Name> = FxHashMap::default();
    let mut name_reverse_index: NameReverseIndex =
      Vec::with_capacity(num_names as usize + 1);
    let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
    names_lookup.insert(anon_addr, Name::anon());
    for _ in 0..num_names {
      let addr = get_address(&mut buf)?;
      let name = get_name_component(&mut buf, &names_lookup)?;
      name_reverse_index.push(addr.clone());
      names_lookup.insert(addr, name);
    }

    // Section 4: Named — harvest `ReducibilityHints` from `Def`
    // entries into `env.anon_hints`; discard the rest. See `get_anon`
    // for the rationale.
    let num_named = get_u64(&mut buf)?;
    for _ in 0..num_named {
      let _name_addr = get_address(&mut buf)?;
      let named = get_named_indexed(&mut buf, &name_reverse_index)?;
      if let super::metadata::ConstantMetaInfo::Def { hints, .. } =
        &named.meta.info
      {
        env.anon_hints.insert(named.addr.clone(), *hints);
      }
    }

    // Section 5: Comms — parse and DISCARD.
    let num_comms = get_u64(&mut buf)?;
    for _ in 0..num_comms {
      let _addr = get_address(&mut buf)?;
      let _comm = Comm::get(&mut buf)?;
    }

    // Optional trailing anon_hints section (see `Env::put`).
    read_anon_hints_section(&mut buf, &mut env)?;

    drop(names_lookup);
    drop(name_reverse_index);

    // Verify merkle root over loaded consts (same as get_anon).
    let mut const_addrs: Vec<Address> =
      env.consts.iter().map(|e| e.key().clone()).collect();
    const_addrs.sort_unstable();
    let computed_root =
      merkle_root_canonical(&const_addrs).unwrap_or_else(zero_address);
    if computed_root != stored_root {
      return Err(format!(
        "Env::get_anon_mmap: merkle root mismatch (stored={}, computed={})",
        stored_root.hex(),
        computed_root.hex(),
      ));
    }

    Ok(env)
  }

  /// Calculate the serialized size of an Env.
  pub fn serialized_size(&self) -> Result<usize, String> {
    let mut buf = Vec::new();
    self.put(&mut buf)?;
    Ok(buf.len())
  }

  /// Calculate serialized size with breakdown by section.
  pub fn serialized_size_breakdown(
    &self,
  ) -> Result<(usize, usize, usize, usize, usize, usize), String> {
    let mut buf = Vec::new();

    // Header + merkle root (matches Env::put layout; root is always
    // 32 bytes, with `zero_address()` as the empty-env sentinel).
    Tag4::new(Self::FLAG, 0).put(&mut buf);
    let mut const_addrs: Vec<Address> =
      self.consts.iter().map(|e| e.key().clone()).collect();
    const_addrs.sort_unstable();
    let root = merkle_root_canonical(&const_addrs).unwrap_or_else(zero_address);
    put_address(&root, &mut buf);
    let header_size = buf.len();

    // Section 1: Blobs
    put_u64(self.blobs.len() as u64, &mut buf);
    for entry in self.blobs.iter() {
      put_address(entry.key(), &mut buf);
      put_u64(entry.value().len() as u64, &mut buf);
      buf.extend_from_slice(entry.value());
    }
    let blobs_size = buf.len() - header_size;

    // Section 2: Consts (length-prefixed)
    let before_consts = buf.len();
    put_u64(self.consts.len() as u64, &mut buf);
    for entry in self.consts.iter() {
      put_address(entry.key(), &mut buf);
      let bytes = entry.value().raw_bytes();
      Tag0::new(bytes.len() as u64).put(&mut buf);
      buf.extend_from_slice(bytes);
    }
    let consts_size = buf.len() - before_consts;

    // Section 3: Names (also build name index)
    let before_names = buf.len();
    let sorted_names = topological_sort_names(&self.names);
    let mut name_index: NameIndex = NameIndex::new();
    put_u64(sorted_names.len() as u64, &mut buf);
    for (i, (addr, name)) in sorted_names.iter().enumerate() {
      name_index.insert(addr.clone(), i as u64);
      put_address(addr, &mut buf);
      put_name_component(name, &mut buf);
    }
    let names_size = buf.len() - before_names;

    // Section 4: Named (use indexed serialization)
    let before_named = buf.len();
    put_u64(self.named.len() as u64, &mut buf);
    for entry in self.named.iter() {
      put_bytes(entry.key().get_hash().as_bytes(), &mut buf);
      put_named_indexed(entry.value(), &name_index, &mut buf)?;
    }
    let named_size = buf.len() - before_named;

    // Section 5: Comms
    let before_comms = buf.len();
    put_u64(self.comms.len() as u64, &mut buf);
    for entry in self.comms.iter() {
      put_address(entry.key(), &mut buf);
      entry.value().put(&mut buf);
    }
    let comms_size = buf.len() - before_comms;

    Ok((
      header_size,
      blobs_size,
      consts_size,
      names_size,
      named_size,
      comms_size,
    ))
  }
}

/// Topologically sort names so parents come before children.
///
/// Collects `(Address, Name)` pairs up front (cheap: Arc clone + 32-byte
/// address clone), parallel-sorts by address for canonical DFS order, then
/// walks each entry via the Arc parent chain in `NameData::Str`/`Num`. The
/// DFS recurses through those Arc pointers — parents are NOT looked up in
/// the DashMap, which is why the result retains `Name` values rather than
/// just addresses (ancestor names may not be stored as explicit DashMap
/// keys).
///
/// We tried a keys-only streaming variant (collect `Vec<Address>` and look
/// up each Name via `DashMap::get` in the DFS loop). It was 22s slower on
/// Mathlib because 4.7M shard-lock acquisitions dominate vs the one-time
/// ~150 MB tuple-clone allocation.
fn topological_sort_names(
  names: &crate::map::IxonMap<Address, Name>,
) -> Vec<(Address, Name)> {
  #[cfg(not(target_arch = "riscv64"))]
  use rayon::slice::ParallelSliceMut;
  use rustc_hash::FxHashSet;

  let mut result = Vec::with_capacity(names.len() + 1);
  let mut visited: FxHashSet<Address> = FxHashSet::default();

  // Include anonymous name first so it gets index 0 in the name index.
  // Arena nodes frequently reference it as a binder name.
  let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
  result.push((anon_addr.clone(), Name::anon()));
  visited.insert(anon_addr);

  fn visit(
    name: &Name,
    visited: &mut FxHashSet<Address>,
    result: &mut Vec<(Address, Name)>,
  ) {
    let addr = Address::from_blake3_hash(*name.get_hash());
    if visited.contains(&addr) {
      return;
    }

    // Visit parent first
    match name.as_data() {
      NameData::Anonymous(_) => {},
      NameData::Str(parent, _, _) | NameData::Num(parent, _, _) => {
        visit(parent, visited, result);
      },
    }

    visited.insert(addr.clone());
    result.push((addr, name.clone()));
  }

  // Clone-collect entries for direct iteration (avoids 4.7M DashMap lookups
  // during DFS). Parallel sort uses rayon over address bytes.
  let mut sorted_entries: Vec<(Address, Name)> =
    names.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
  #[cfg(not(target_arch = "riscv64"))]
  sorted_entries.par_sort_unstable_by(|a, b| a.0.cmp(&b.0));
  #[cfg(target_arch = "riscv64")]
  sorted_entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
  for (_, name) in &sorted_entries {
    visit(name, &mut visited, &mut result);
  }

  result
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::constant::tests::gen_constant;
  use crate::tests::gen_range;
  use quickcheck::{Arbitrary, Gen};
  use quickcheck_macros::quickcheck;

  #[quickcheck]
  fn prop_pack_bools_roundtrip(x: Vec<bool>) -> bool {
    let mut bools = x;
    bools.truncate(8);
    bools == unpack_bools(bools.len(), pack_bools(bools.clone()))
  }

  #[test]
  fn test_pack_bools_specific() {
    assert_eq!(pack_bools([true, false, true]), 0b101);
    assert_eq!(pack_bools([false, false, false, false, true]), 0b10000);
    assert_eq!(unpack_bools(3, 0b101), vec![true, false, true]);
    assert_eq!(
      unpack_bools(5, 0b10000),
      vec![false, false, false, false, true]
    );
  }

  #[test]
  fn test_name_roundtrip() {
    let names = vec![
      Name::anon(),
      Name::str(Name::anon(), "foo".to_string()),
      Name::num(Name::anon(), Nat::from(42u64)),
      Name::str(Name::str(Name::anon(), "a".to_string()), "b".to_string()),
      Name::num(Name::str(Name::anon(), "x".to_string()), Nat::from(123u64)),
    ];

    for name in names {
      let mut buf = Vec::new();
      put_name(&name, &mut buf);
      let recovered = get_name(&mut buf.as_slice()).unwrap();
      assert_eq!(name, recovered, "Name roundtrip failed");
    }
  }

  #[test]
  fn test_env_roundtrip_empty() {
    let env = Env::new();
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let recovered = Env::get(&mut buf.as_slice()).unwrap();
    assert_eq!(env.blobs.len(), recovered.blobs.len());
    assert_eq!(env.consts.len(), recovered.consts.len());
    assert_eq!(env.named.len(), recovered.named.len());
    assert_eq!(env.comms.len(), recovered.comms.len());
  }

  // ========== Arbitrary generators for Env ==========

  fn gen_string(g: &mut Gen) -> String {
    let len = gen_range(g, 1..20);
    (0..len)
      .map(|_| {
        let c: u8 = Arbitrary::arbitrary(g);
        let idx = c % 62;
        // ASCII letters/numbers only: a-z (0-25), A-Z (26-51), 0-9 (52-61)
        let ch = if idx < 26 {
          b'a' + idx
        } else if idx < 52 {
          b'A' + (idx - 26)
        } else {
          b'0' + (idx - 52)
        };
        ch as char
      })
      .collect()
  }

  fn gen_name(g: &mut Gen, depth: usize) -> Name {
    if depth == 0 {
      Name::anon()
    } else {
      let parent = gen_name(g, depth - 1);
      let use_str: bool = Arbitrary::arbitrary(g);
      if use_str {
        Name::str(parent, gen_string(g))
      } else {
        let n: u64 = Arbitrary::arbitrary(g);
        Name::num(parent, Nat::from(n))
      }
    }
  }

  fn gen_blob(g: &mut Gen) -> Vec<u8> {
    let len = gen_range(g, 1..100);
    (0..len).map(|_| Arbitrary::arbitrary(g)).collect()
  }

  fn gen_env(g: &mut Gen) -> Env {
    let env = Env::new();

    // Generate blobs
    let num_blobs = gen_range(g, 0..10);
    for _ in 0..num_blobs {
      let blob = gen_blob(g);
      env.store_blob(blob);
    }

    // Generate names (with varying depths)
    let num_names = gen_range(g, 1..20);
    let mut names: Vec<Name> = Vec::new();
    for _ in 0..num_names {
      let depth = gen_range(g, 1..5);
      let name = gen_name(g, depth);
      let addr = Address::from_blake3_hash(*name.get_hash());
      env.names.insert(addr, name.clone());
      names.push(name);
    }

    // Generate constants and named entries
    let num_consts = gen_range(g, 0..10);
    for i in 0..num_consts {
      let constant = gen_constant(g);
      let mut buf = Vec::new();
      constant.put(&mut buf);
      let addr = Address::hash(&buf);
      env.store_const(addr.clone(), constant);

      // Create a named entry for this constant
      if !names.is_empty() {
        let name = names[i % names.len()].clone();
        let meta = ConstantMeta::default();
        // Sometimes generate a Named.original to exercise that serialization path.
        let original = if bool::arbitrary(g) {
          // Store the original constant under its true content address —
          // `Env::get` verifies `Address::hash(bytes) == addr` per entry,
          // so a random `Address::arbitrary` would be rejected on load.
          let orig_constant = gen_constant(g);
          let mut orig_buf = Vec::new();
          orig_constant.put(&mut orig_buf);
          let orig_addr = Address::hash(&orig_buf);
          env.store_const(orig_addr.clone(), orig_constant);
          Some((orig_addr, ConstantMeta::default()))
        } else {
          None
        };
        let named = Named { addr: addr.clone(), meta, original };
        env.named.insert(name, named);
      }
    }

    // Generate comms
    let num_comms = gen_range(g, 0..5);
    for _ in 0..num_comms {
      let comm = Comm::arbitrary(g);
      let addr = Address::arbitrary(g);
      env.comms.insert(addr, comm);
    }

    env
  }

  #[derive(Debug, Clone)]
  struct ArbitraryEnv(Env);

  impl Arbitrary for ArbitraryEnv {
    fn arbitrary(g: &mut Gen) -> Self {
      ArbitraryEnv(gen_env(g))
    }
  }

  fn env_roundtrip(env: &Env) -> bool {
    let mut buf = Vec::new();
    if let Err(e) = env.put(&mut buf) {
      eprintln!("Env::put failed: {}", e);
      return false;
    }
    match Env::get(&mut buf.as_slice()) {
      Ok(recovered) => {
        // Check counts match
        if env.blobs.len() != recovered.blobs.len() {
          eprintln!(
            "blobs mismatch: {} vs {}",
            env.blobs.len(),
            recovered.blobs.len()
          );
          return false;
        }
        if env.consts.len() != recovered.consts.len() {
          eprintln!(
            "consts mismatch: {} vs {}",
            env.consts.len(),
            recovered.consts.len()
          );
          return false;
        }
        if env.named.len() != recovered.named.len() {
          eprintln!(
            "named mismatch: {} vs {}",
            env.named.len(),
            recovered.named.len()
          );
          return false;
        }
        if env.comms.len() != recovered.comms.len() {
          eprintln!(
            "comms mismatch: {} vs {}",
            env.comms.len(),
            recovered.comms.len()
          );
          return false;
        }

        // Check blobs content
        for entry in env.blobs.iter() {
          match recovered.blobs.get(entry.key()) {
            Some(v) if v.value() == entry.value() => {},
            _ => {
              eprintln!("blob content mismatch for {:?}", entry.key());
              return false;
            },
          }
        }

        // Check consts content
        for entry in env.consts.iter() {
          match recovered.consts.get(entry.key()) {
            Some(v) if v.value() == entry.value() => {},
            _ => {
              eprintln!("const content mismatch for {:?}", entry.key());
              return false;
            },
          }
        }

        // Check named content
        for entry in env.named.iter() {
          match recovered.named.get(entry.key()) {
            Some(v) if v.addr == entry.value().addr => {},
            _ => {
              eprintln!("named content mismatch for {:?}", entry.key());
              return false;
            },
          }
        }

        // Check comms content
        for entry in env.comms.iter() {
          match recovered.comms.get(entry.key()) {
            Some(v) if v.value() == entry.value() => {},
            _ => {
              eprintln!("comm content mismatch for {:?}", entry.key());
              return false;
            },
          }
        }

        true
      },
      Err(e) => {
        eprintln!("env_roundtrip error: {}", e);
        false
      },
    }
  }

  #[quickcheck]
  fn prop_env_roundtrip(env: ArbitraryEnv) -> bool {
    env_roundtrip(&env.0)
  }

  #[test]
  fn test_env_roundtrip_with_data() {
    let mut g = Gen::new(20);
    for _ in 0..10 {
      let env = gen_env(&mut g);
      assert!(env_roundtrip(&env), "Env roundtrip failed");
    }
  }

  // ---------- Env merkle root tests ----------

  fn defn_const(refs: Vec<Address>) -> Constant {
    defn_const_discriminator(refs, 0)
  }

  fn defn_const_discriminator(refs: Vec<Address>, lvls: u64) -> Constant {
    use crate::constant::{DefKind, Definition};
    use ix_common::env::DefinitionSafety;
    Constant::with_tables(
      ConstantInfo::Defn(Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        lvls,
        typ: Expr::sort(0),
        value: Expr::var(0),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  /// Store `c` at its true content address; returns the address.
  /// Tests that serialize+deserialize through `Env::put`/`Env::get`
  /// must use canonical addresses because the load path verifies
  /// `Address::hash(bytes) == addr` per entry.
  fn store_canonical(env: &Env, c: Constant) -> Address {
    let (addr, _) = c.commit();
    env.store_const(addr.clone(), c);
    addr
  }

  /// Extract the stored merkle root from a serialized env. The Tag4
  /// header byte (`0xE0` for env) is followed by exactly 32 bytes of
  /// root (no opt-tag).
  fn parse_stored_root(buf: &[u8]) -> Vec<u8> {
    assert_eq!(buf[0], 0xE0, "env header byte should be 0xE0");
    buf[1..33].to_vec()
  }

  #[test]
  fn env_root_empty_env_is_zero_address() {
    use crate::merkle::zero_address;
    let env = Env::new();
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let root = parse_stored_root(&buf);
    assert_eq!(
      root,
      zero_address().as_bytes().to_vec(),
      "empty env root should be zero_address sentinel"
    );
  }

  #[test]
  fn env_root_present_when_consts_nonempty() {
    use crate::merkle::zero_address;
    let env = Env::new();
    env.store_const(Address::hash(b"a"), defn_const(vec![]));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let root = parse_stored_root(&buf);
    // Non-empty env root must NOT be the zero sentinel.
    assert_ne!(root, zero_address().as_bytes().to_vec());
  }

  #[test]
  fn env_root_invariant_under_insertion_order() {
    let env1 = Env::new();
    let env2 = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    env1.store_const(a.clone(), defn_const(vec![]));
    env1.store_const(b.clone(), defn_const(vec![]));
    env1.store_const(c.clone(), defn_const(vec![]));
    env2.store_const(c, defn_const(vec![]));
    env2.store_const(b, defn_const(vec![]));
    env2.store_const(a, defn_const(vec![]));

    let mut buf1 = Vec::new();
    let mut buf2 = Vec::new();
    env1.put(&mut buf1).unwrap();
    env2.put(&mut buf2).unwrap();

    assert_eq!(parse_stored_root(&buf1), parse_stored_root(&buf2));
  }

  #[test]
  fn env_root_changes_with_extra_const() {
    let env = Env::new();
    env.store_const(Address::hash(b"a"), defn_const(vec![]));
    let mut buf1 = Vec::new();
    env.put(&mut buf1).unwrap();
    env.store_const(Address::hash(b"b"), defn_const(vec![]));
    let mut buf2 = Vec::new();
    env.put(&mut buf2).unwrap();

    assert_ne!(parse_stored_root(&buf1), parse_stored_root(&buf2));
  }

  #[test]
  fn env_root_mismatch_rejected() {
    let env = Env::new();
    env.store_const(Address::hash(b"a"), defn_const(vec![]));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    // Tamper with a byte in the root (offset 1..33).
    buf[10] ^= 0xFF;
    let res = Env::get(&mut buf.as_slice());
    assert!(res.is_err(), "tampered root should be rejected");
  }

  /// Flip a byte inside the first const's payload bytes (not its
  /// stored address): merkle still validates over `consts.keys()`, so
  /// the per-entry `Address::hash(bytes) == addr` check is what must
  /// reject this corruption. Without that check, `Env::get` would
  /// succeed and the failure would surface much later inside
  /// `LazyConstant::get` with a misleading parse error.
  ///
  /// Header layout for an env with empty blobs and one const:
  ///   [0]      Tag4 (0xE0)
  ///   [1..33)  merkle root (32 bytes)
  ///   [33]     Section 1 (blobs) count = 0 (Tag0)
  ///   [34]     Section 2 (consts) count = 1 (Tag0)
  ///   [35..67) const address (32 bytes)
  ///   [67]     Tag0 length of const bytes
  ///   [68..]   const bytes (target for tampering)
  #[test]
  fn env_const_bytes_tampering_rejected_by_get() {
    let env = Env::new();
    env.store_const(Address::hash(b"a"), defn_const(vec![]));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    // Flip a byte well inside the const payload.
    let off = 68 + 3;
    assert!(off < buf.len(), "expected const bytes at offset {off}");
    buf[off] ^= 0xFF;
    let res = Env::get(&mut buf.as_slice());
    let err = res.expect_err("tampered const bytes should be rejected");
    assert!(
      err.contains("bytes hash to") && err.contains("but stored under"),
      "expected per-entry verify error, got: {err}"
    );
  }

  #[test]
  fn env_const_bytes_tampering_rejected_by_get_anon() {
    let env = Env::new();
    env.store_const(Address::hash(b"a"), defn_const(vec![]));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let off = 68 + 3;
    assert!(off < buf.len());
    buf[off] ^= 0xFF;
    let res = Env::get_anon(&mut buf.as_slice());
    let err = res.expect_err("tampered const bytes should be rejected");
    assert!(
      err.contains("bytes hash to") && err.contains("but stored under"),
      "expected per-entry verify error, got: {err}"
    );
  }

  #[test]
  fn env_const_bytes_tampering_rejected_by_get_anon_mmap() {
    use std::io::Write;
    let env = Env::new();
    env.store_const(Address::hash(b"a"), defn_const(vec![]));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let off = 68 + 3;
    assert!(off < buf.len());
    buf[off] ^= 0xFF;
    // mmap requires a real file
    let tmp = std::env::temp_dir().join("ix_env_tamper_mmap_test.ixe");
    {
      let mut f = std::fs::File::create(&tmp).unwrap();
      f.write_all(&buf).unwrap();
    }
    let res = Env::get_anon_mmap(&tmp);
    let err = res.expect_err("tampered const bytes should be rejected");
    assert!(
      err.contains("bytes hash to") && err.contains("but stored under"),
      "expected per-entry verify error, got: {err}"
    );
    std::fs::remove_file(&tmp).ok();
  }

  // ---------------------------------------------------------------------------
  // Env::get_anon — anonymous-only deserialization
  // ---------------------------------------------------------------------------

  #[test]
  fn get_anon_keeps_consts_drops_metadata() {
    use crate::env::Named;
    let env = Env::new();
    // Round-trip tests must use canonical addresses (see store_canonical
    // helper); `Env::get`/`get_anon` reject entries whose bytes don't
    // hash to their stored address.
    let a = store_canonical(&env, defn_const(vec![]));
    let b = store_canonical(&env, defn_const(vec![a.clone()]));
    // Populate metadata sections so we can verify they get dropped.
    let blob_addr = env.store_blob(b"hello world".to_vec());
    env.register_name(
      Name::str(Name::anon(), "MyConst".to_string()),
      Named::with_addr(a.clone()),
    );

    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let loaded = Env::get_anon(&mut buf.as_slice()).unwrap();

    // Anonymous sections preserved
    assert_eq!(loaded.const_count(), 2);
    assert!(loaded.consts.get(&a).is_some());
    assert!(loaded.consts.get(&b).is_some());
    assert_eq!(loaded.get_blob(&blob_addr), Some(b"hello world".to_vec()));

    // Metadata sections empty
    assert_eq!(loaded.named_count(), 0, "named should be empty after get_anon");
    assert_eq!(loaded.name_count(), 0, "names should be empty after get_anon");
    assert_eq!(loaded.comm_count(), 0, "comms should be empty after get_anon");
  }

  #[test]
  fn get_anon_merkle_root_verified() {
    let env = Env::new();
    store_canonical(&env, defn_const(vec![]));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    // Tamper with the root.
    buf[10] ^= 0xFF;
    let res = Env::get_anon(&mut buf.as_slice());
    assert!(res.is_err(), "get_anon must reject tampered root");
  }

  #[test]
  fn get_anon_empty_env_roundtrip() {
    let env = Env::new();
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let loaded = Env::get_anon(&mut buf.as_slice()).unwrap();
    assert_eq!(loaded.const_count(), 0);
    assert_eq!(loaded.named_count(), 0);
  }

  #[test]
  fn get_anon_consts_match_get() {
    // Build an env, serialize, then load via both get and get_anon.
    // The `consts` map should agree (same addresses, same Constant
    // when materialized). Use a discriminator per const so they're
    // content-distinct (otherwise 5 identical Defns would collapse
    // to one entry).
    let env = Env::new();
    for i in 0..5u8 {
      store_canonical(&env, defn_const_discriminator(vec![], u64::from(i)));
    }
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let full = Env::get(&mut buf.as_slice()).unwrap();
    let anon = Env::get_anon(&mut buf.as_slice()).unwrap();
    assert_eq!(full.const_count(), anon.const_count());
    for entry in full.consts.iter() {
      let addr = entry.key();
      let from_full = full.get_const(addr).unwrap();
      let from_anon = anon.get_const(addr).unwrap();
      assert_eq!(*from_full, *from_anon);
    }
  }

  /// Lock in the mmap inode-retention invariant: after `get_anon_mmap`
  /// opens and maps the file, removing the path from the filesystem
  /// MUST NOT invalidate the mapping. On Linux this works because
  /// `unlink` only decrements the directory link count; the inode
  /// stays alive while any open fd or mmap reference exists, and
  /// `MAP_PRIVATE` keeps its pages.
  ///
  /// This is the invariant our SIGBUS analysis relies on. A future
  /// change that, say, switched to `mmap_anonymous` or copied bytes
  /// into a tmpfile would break this — making the test fail loudly
  /// instead of letting workers SIGBUS in production.
  #[test]
  fn get_anon_mmap_survives_file_unlink() {
    let env = Env::new();
    let a = store_canonical(&env, defn_const(vec![]));
    let b = store_canonical(&env, defn_const_discriminator(vec![], 1));
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();

    let tmp = std::env::temp_dir().join("ix_get_anon_mmap_unlink_test.ixe");
    {
      use std::io::Write;
      let mut f = std::fs::File::create(&tmp).unwrap();
      f.write_all(&buf).unwrap();
    }

    let mmap_env =
      Env::get_anon_mmap(&tmp).expect("open should succeed before unlink");
    // Materializing once before unlink makes sure we have known-good
    // baseline behavior; the real test is materializing AFTER unlink.
    let pre_a = mmap_env.get_const(&a).expect("pre-unlink fetch of `a`");

    std::fs::remove_file(&tmp).expect("unlink should succeed");

    // After unlink, the mmap'd pages must still be readable. We
    // didn't yet touch `b`'s bytes — if they hadn't been faulted in
    // before, the OS still pages them from the now-unlinked inode
    // because we hold a clone of `Arc<Mmap>` (via the env's
    // `LazyConstant`s).
    let post_a = mmap_env.get_const(&a).expect("post-unlink fetch of `a`");
    let post_b = mmap_env.get_const(&b).expect("post-unlink fetch of `b`");

    assert_eq!(pre_a, post_a, "`a` content should be stable across unlink");
    assert_ne!(post_a, post_b, "discriminators should still differentiate");
  }
}
