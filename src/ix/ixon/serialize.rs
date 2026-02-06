//! Serialization for Ixon types.
//!
//! This module provides serialization/deserialization for all Ixon types
//! using the Tag4/Tag2/Tag0 encoding schemes.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::map_err_ignore)]
#![allow(clippy::needless_pass_by_value)]

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, QuotKind};

use super::constant::{
  Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
  Definition, DefinitionProj, Inductive, InductiveProj, MutConst, Quotient,
  Recursor, RecursorProj, RecursorRule,
};
use super::expr::Expr;
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

impl DefinitionSafety {
  fn to_u8(self) -> u8 {
    match self {
      Self::Unsafe => 0,
      Self::Safe => 1,
      Self::Partial => 2,
    }
  }

  fn from_u8(x: u8) -> Result<Self, String> {
    match x {
      0 => Ok(Self::Unsafe),
      1 => Ok(Self::Safe),
      2 => Ok(Self::Partial),
      x => Err(format!("DefinitionSafety::from_u8: invalid {x}")),
    }
  }
}

/// Pack DefKind (2 bits) and DefinitionSafety (2 bits) into a single byte.
fn pack_def_kind_safety(kind: DefKind, safety: DefinitionSafety) -> u8 {
  (kind.to_u8() << 2) | safety.to_u8()
}

/// Unpack DefKind and DefinitionSafety from a single byte.
fn unpack_def_kind_safety(
  b: u8,
) -> Result<(DefKind, DefinitionSafety), String> {
  let kind = DefKind::from_u8(b >> 2)?;
  let safety = DefinitionSafety::from_u8(b & 0x3)?;
  Ok((kind, safety))
}

impl QuotKind {
  pub fn put_ser(&self, buf: &mut Vec<u8>) {
    match self {
      Self::Type => put_u8(0, buf),
      Self::Ctor => put_u8(1, buf),
      Self::Lift => put_u8(2, buf),
      Self::Ind => put_u8(3, buf),
    }
  }

  pub fn get_ser(buf: &mut &[u8]) -> Result<Self, String> {
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
    put_u8(pack_bools([self.recr, self.refl, self.is_unsafe]), buf);
    put_u64(self.lvls, buf);
    put_u64(self.params, buf);
    put_u64(self.indices, buf);
    put_u64(self.nested, buf);
    put_expr(&self.typ, buf);
    put_u64(self.ctors.len() as u64, buf);
    for ctor in &self.ctors {
      ctor.put(buf);
    }
  }

  pub fn get(buf: &mut &[u8]) -> Result<Self, String> {
    let bools = unpack_bools(3, get_u8(buf)?);
    let lvls = get_u64(buf)?;
    let params = get_u64(buf)?;
    let indices = get_u64(buf)?;
    let nested = get_u64(buf)?;
    let typ = get_expr(buf)?;
    let num_ctors = get_u64(buf)?;
    let mut ctors = Vec::with_capacity(capped_capacity(num_ctors, buf));
    for _ in 0..num_ctors {
      ctors.push(Constructor::get(buf)?);
    }
    Ok(Inductive {
      recr: bools[0],
      refl: bools[1],
      is_unsafe: bools[2],
      lvls,
      params,
      indices,
      nested,
      typ,
      ctors,
    })
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

use crate::ix::env::{Name, NameData};
use crate::lean::nat::Nat;
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

use super::env::Named;
use super::metadata::{ConstantMeta, NameIndex, NameReverseIndex};

/// Serialize a Named entry with indexed metadata.
pub fn put_named_indexed(named: &Named, idx: &NameIndex, buf: &mut Vec<u8>) {
  put_address(&named.addr, buf);
  named.meta.put_indexed(idx, buf);
}

/// Deserialize a Named entry with indexed metadata.
pub fn get_named_indexed(
  buf: &mut &[u8],
  rev: &NameReverseIndex,
) -> Result<Named, String> {
  let addr = get_address(buf)?;
  let meta = ConstantMeta::get_indexed(buf, rev)?;
  Ok(Named { addr, meta })
}

// ============================================================================
// Env serialization
// ============================================================================

use super::comm::Comm;
use super::env::Env;

impl Env {
  /// Tag4 flag for Env (0xE), variant 0.
  pub const FLAG: u8 = 0xE;

  /// Serialize an Env to bytes.
  pub fn put(&self, buf: &mut Vec<u8>) {
    // Header: Tag4 with flag=0xE, size=0 (Env variant)
    Tag4::new(Self::FLAG, 0).put(buf);

    // Section 1: Blobs (Address -> bytes)
    // Sort by address for deterministic serialization (matches Lean)
    let mut blobs: Vec<_> =
      self.blobs.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    blobs.sort_by(|a, b| a.0.cmp(&b.0));
    put_u64(blobs.len() as u64, buf);
    for (addr, bytes) in &blobs {
      put_address(addr, buf);
      put_u64(bytes.len() as u64, buf);
      buf.extend_from_slice(bytes);
    }

    // Section 2: Consts (Address -> Constant)
    // Sort by address for deterministic serialization (matches Lean)
    let mut consts: Vec<_> = self
      .consts
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    consts.sort_by(|a, b| a.0.cmp(&b.0));
    put_u64(consts.len() as u64, buf);
    for (addr, constant) in &consts {
      put_address(addr, buf);
      constant.put(buf);
    }

    // Section 3: Names (Address -> Name component)
    // Topologically sorted so parents come before children
    // Also build name index for metadata serialization
    let sorted_names = topological_sort_names(&self.names);
    let mut name_index: NameIndex = NameIndex::new();
    put_u64(sorted_names.len() as u64, buf);
    for (i, (addr, name)) in sorted_names.iter().enumerate() {
      name_index.insert(addr.clone(), i as u64);
      put_address(addr, buf);
      put_name_component(name, buf);
    }

    // Section 4: Named (name Address -> Named)
    // Sort by name hash for deterministic serialization (matches Lean)
    // Use indexed serialization for metadata (saves ~24 bytes per address)
    let mut named: Vec<_> =
      self.named.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    named
      .sort_by(|a, b| a.0.get_hash().as_bytes().cmp(b.0.get_hash().as_bytes()));
    put_u64(named.len() as u64, buf);
    for (name, named_entry) in &named {
      put_bytes(name.get_hash().as_bytes(), buf);
      put_named_indexed(named_entry, &name_index, buf);
    }

    // Section 5: Comms (Address -> Comm)
    // Sort by address for deterministic serialization (matches Lean)
    let mut comms: Vec<_> =
      self.comms.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    comms.sort_by(|a, b| a.0.cmp(&b.0));
    put_u64(comms.len() as u64, buf);
    for (addr, comm) in &comms {
      put_address(addr, buf);
      comm.put(buf);
    }
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

    let env = Env::new();

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

    // Section 2: Consts
    let num_consts = get_u64(buf)?;
    for _ in 0..num_consts {
      let addr = get_address(buf)?;
      let constant = Constant::get(buf)?;
      env.consts.insert(addr, constant);
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
      env.addr_to_name.insert(named.addr.clone(), name.clone());
      env.named.insert(name, named);
    }

    // Section 5: Comms
    let num_comms = get_u64(buf)?;
    for _ in 0..num_comms {
      let addr = get_address(buf)?;
      let comm = Comm::get(buf)?;
      env.comms.insert(addr, comm);
    }

    Ok(env)
  }

  /// Calculate the serialized size of an Env.
  pub fn serialized_size(&self) -> usize {
    let mut buf = Vec::new();
    self.put(&mut buf);
    buf.len()
  }

  /// Calculate serialized size with breakdown by section.
  pub fn serialized_size_breakdown(
    &self,
  ) -> (usize, usize, usize, usize, usize, usize) {
    let mut buf = Vec::new();

    // Header
    Tag4::new(Self::FLAG, 0).put(&mut buf);
    let header_size = buf.len();

    // Section 1: Blobs
    put_u64(self.blobs.len() as u64, &mut buf);
    for entry in self.blobs.iter() {
      put_address(entry.key(), &mut buf);
      put_u64(entry.value().len() as u64, &mut buf);
      buf.extend_from_slice(entry.value());
    }
    let blobs_size = buf.len() - header_size;

    // Section 2: Consts
    let before_consts = buf.len();
    put_u64(self.consts.len() as u64, &mut buf);
    for entry in self.consts.iter() {
      put_address(entry.key(), &mut buf);
      entry.value().put(&mut buf);
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
      put_named_indexed(entry.value(), &name_index, &mut buf);
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

    (header_size, blobs_size, consts_size, names_size, named_size, comms_size)
  }
}

/// Topologically sort names so parents come before children.
fn topological_sort_names(
  names: &dashmap::DashMap<Address, Name>,
) -> Vec<(Address, Name)> {
  use std::collections::HashSet;

  let mut result = Vec::with_capacity(names.len() + 1);
  let mut visited: HashSet<Address> = HashSet::new();

  // Include anonymous name first so it gets index 0 in the name index.
  // Arena nodes frequently reference it as a binder name.
  let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
  result.push((anon_addr.clone(), Name::anon()));
  visited.insert(anon_addr);

  fn visit(
    name: &Name,
    visited: &mut HashSet<Address>,
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

  // Sort entries by address before DFS for deterministic order (matches Lean)
  let mut sorted_entries: Vec<_> =
    names.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
  sorted_entries.sort_by(|a, b| a.0.cmp(&b.0));
  for (_, name) in &sorted_entries {
    visit(name, &mut visited, &mut result);
  }

  result
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::ixon::constant::tests::gen_constant;
  use crate::ix::ixon::tests::gen_range;
  use quickcheck::{Arbitrary, Gen};

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
    env.put(&mut buf);
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
      env.consts.insert(addr.clone(), constant);

      // Create a named entry for this constant
      if !names.is_empty() {
        let name = names[i % names.len()].clone();
        let meta = ConstantMeta::default();
        let named = Named { addr: addr.clone(), meta };
        env.addr_to_name.insert(addr, name.clone());
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
    env.put(&mut buf);
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
}
