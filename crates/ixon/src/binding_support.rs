//! Host packing availability for an artifact's exact binding. This does not
//! admit role specifications or proof evidence; the certified consumer does.

use std::collections::VecDeque;

use ix_common::address::Address;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::constant::{Constant, ConstantInfo as CI, MutConst, Recursor};
use crate::env::Env;
use crate::expr::Expr;
use crate::lazy::ConstVariantTag;
use crate::role_table::{Evidence, Role, RoleTable};

/// Decode genuine bytes, independently of a caller-supplied materialized cache.
pub(crate) fn raw_constant(
  env: &Env,
  address: &Address,
) -> Result<Constant, String> {
  let bytes = env.get_const_bytes(address).ok_or_else(|| {
    format!("binding support: missing constant {}", address.hex())
  })?;
  if Address::hash(&bytes) != *address {
    return Err(format!(
      "binding support: bad constant hash {}",
      address.hex()
    ));
  }
  let mut input = bytes.as_ref();
  let constant = Constant::get(&mut input)?;
  let mut canonical = Vec::new();
  constant.put(&mut canonical);
  if !input.is_empty() || canonical.as_slice() != bytes.as_ref() {
    return Err(format!(
      "binding support: noncanonical constant {}",
      address.hex()
    ));
  }
  Ok(constant)
}

#[derive(Clone)]
struct Member {
  block: Address,
  index: usize,
  constructor: bool,
}

/// Reader.resolveSource's physical member resolution; no role or name guesses.
fn resolve(env: &Env, address: &Address) -> Option<Member> {
  let c = raw_constant(env, address).ok()?;
  let (block, index, kind, constructor) = match &c.info {
    CI::Defn(_) | CI::Recr(_) | CI::Axio(_) | CI::Quot(_) => {
      return Some(Member {
        block: address.clone(),
        index: 0,
        constructor: false,
      });
    },
    CI::IPrj(p) => (&p.block, p.idx, 0, None),
    CI::CPrj(p) => (&p.block, p.idx, 0, Some(p.cidx)),
    CI::RPrj(p) => (&p.block, p.idx, 1, None),
    CI::DPrj(p) => (&p.block, p.idx, 2, None),
    CI::Muts(_) => return None,
  };
  if !c.refs.is_empty() || !c.sharing.is_empty() || !c.univs.is_empty() {
    return None;
  }
  let owner = raw_constant(env, block).ok()?;
  let CI::Muts(members) = &owner.info else {
    return None;
  };
  let index = usize::try_from(index).ok()?;
  match (kind, members.get(index)?) {
    (0, MutConst::Indc(i)) => {
      if let Some(k) = constructor
        && i.ctors.get(usize::try_from(k).ok()?)?.cidx != k
      {
        return None;
      }
    },
    (1, MutConst::Recr(_)) | (2, MutConst::Defn(_)) => {},
    _ => return None,
  }
  Some(Member {
    block: block.clone(),
    index,
    constructor: constructor.is_some(),
  })
}

// Reader.unshare/stripAll/stripAllFull/appHead use these same syntactic bounds.
const SPINE_FUEL: usize = 1 << 20;
fn unshare<'a>(c: &'a Constant, mut e: &'a Expr) -> &'a Expr {
  for _ in 0..=c.sharing.len() {
    let Expr::Share(i) = e else {
      break;
    };
    let Some(next) = usize::try_from(*i).ok().and_then(|i| c.sharing.get(i))
    else {
      break;
    };
    e = next;
  }
  e
}
fn strip<'a>(
  c: &'a Constant,
  mut e: &'a Expr,
  count: u64,
) -> Option<(Vec<&'a Expr>, &'a Expr)> {
  let mut domains = Vec::new();
  let mut seen = FxHashSet::default();
  for _ in 0..count {
    let node = unshare(c, e);
    if !seen.insert(std::ptr::from_ref(node)) {
      return None;
    }
    let Expr::All(_, _, domain, body) = node else {
      return None;
    };
    domains.push(domain.as_ref());
    e = body;
  }
  Some((domains, e))
}
fn last_domain<'a>(c: &'a Constant, mut e: &'a Expr) -> Option<&'a Expr> {
  let mut last = None;
  let mut seen = FxHashSet::default();
  for _ in 0..SPINE_FUEL {
    let node = unshare(c, e);
    if !seen.insert(std::ptr::from_ref(node)) {
      return None;
    }
    let Expr::All(_, _, domain, body) = node else {
      break;
    };
    last = Some(domain.as_ref());
    e = body;
  }
  last
}
fn head<'a>(c: &'a Constant, mut e: &'a Expr) -> Option<&'a Expr> {
  let mut seen = FxHashSet::default();
  for _ in 0..SPINE_FUEL {
    let node = unshare(c, e);
    if !seen.insert(std::ptr::from_ref(node)) {
      return None;
    }
    match node {
      Expr::App(f, _) => e = f,
      e => return Some(e),
    }
  }
  Some(e)
}
fn head_ref(
  env: &Env,
  owner: &Address,
  c: &Constant,
  e: &Expr,
) -> Option<Member> {
  match head(c, e)? {
    Expr::Ref(i, _) => resolve(env, c.refs.get(usize::try_from(*i).ok()?)?),
    Expr::Rec(i, _) => {
      let index = usize::try_from(*i).ok()?;
      let size = match &c.info {
        CI::Muts(ms) => ms.len(),
        _ => 1,
      };
      (index < size).then(|| Member {
        block: owner.clone(),
        index,
        constructor: false,
      })
    },
    _ => None,
  }
}

/// Reader.analyseRecursor and buildIndex's carrier checks. Keep every matching
/// candidate owner, without imposing a new uniqueness domain or choosing a pin.
fn recursor_block(
  env: &Env,
  owner: &Address,
  c: &Constant,
  r: &Recursor,
) -> Option<Address> {
  let depth = r
    .params
    .checked_add(r.motives)?
    .checked_add(r.minors)?
    .checked_add(r.indices)?
    .checked_add(1)?;
  let (domains, body) = strip(c, &r.typ, depth)?;
  let Expr::Var(k) = head(c, body)? else {
    return None;
  };
  if *k >= depth {
    return None;
  }
  let motive = depth - 1 - k;
  if motive < r.params || motive >= r.params.checked_add(r.motives)? {
    return None;
  }
  let mut carriers = Vec::new();
  for domain in domains
    .iter()
    .skip(usize::try_from(r.params).ok()?)
    .take(usize::try_from(r.motives).ok()?)
  {
    carriers.push(head_ref(env, owner, c, last_domain(c, domain)?)?);
  }
  head_ref(env, owner, c, domains.last()?)?;
  let first = carriers.first()?;
  if first.constructor {
    return None;
  }
  let block = raw_constant(env, &first.block).ok()?;
  let CI::Muts(ms) = &block.info else {
    return None;
  };
  let inds: FxHashSet<usize> = ms
    .iter()
    .enumerate()
    .filter_map(|(i, m)| matches!(m, MutConst::Indc(_)).then_some(i))
    .collect();
  if inds.is_empty() || carriers.len() < inds.len() {
    return None;
  }
  let mut seen = FxHashSet::default();
  for carrier in carriers.iter().take(inds.len()) {
    if carrier.constructor
      || carrier.block != first.block
      || !inds.contains(&carrier.index)
      || !seen.insert(carrier.index)
    {
      return None;
    }
  }
  Some(first.block.clone())
}

pub(crate) struct BindingSupport {
  roles: FxHashMap<Role, Address>,
  roots: Vec<Address>,
  recursors: FxHashMap<Address, Vec<Address>>,
  required: FxHashSet<Address>,
}

impl BindingSupport {
  pub(crate) fn new(env: &Env) -> Result<Option<Self>, String> {
    let Some(binding) = &env.role_binding else {
      return Ok(None);
    };
    binding.check_hash()?;
    let table = RoleTable::from_bytes(&binding.bytes)?;
    let roles: FxHashMap<_, _> = table.bound.into_iter().collect();
    let mut roots: Vec<_> = roles.values().cloned().collect();
    roots.extend(table.evidence.into_iter().flat_map(|(_, es)| es).filter_map(
      |e| match e {
        Evidence::Proof(a) => Some(a),
        Evidence::DefEq => None,
      },
    ));
    for address in &roots {
      raw_constant(env, address)?;
      if resolve(env, address).is_none() {
        return Err(format!(
          "binding support: unresolved bound member/proof {}",
          address.hex()
        ));
      }
    }
    let mut recursors: FxHashMap<Address, Vec<Address>> = FxHashMap::default();
    let keys: Vec<_> =
      env.consts.iter().map(|entry| entry.key().clone()).collect();
    for owner in keys {
      let candidate = env.consts.get(&owner).is_some_and(|entry| {
        matches!(
          entry.peek_variant(),
          Ok(ConstVariantTag::Recr | ConstVariantTag::Muts)
        )
      });
      if !candidate {
        continue;
      }
      // Unused malformed records do not invalidate an unrelated packing root.
      let Ok(c) = raw_constant(env, &owner) else {
        continue;
      };
      let rs: Vec<_> = match &c.info {
        CI::Recr(r) => vec![r],
        CI::Muts(ms) => ms
          .iter()
          .filter_map(|m| match m {
            MutConst::Recr(r) => Some(r),
            _ => None,
          })
          .collect(),
        _ => Vec::new(),
      };
      for r in rs {
        if let Some(block) = recursor_block(env, &owner, &c, r) {
          let entries = recursors.entry(block).or_default();
          if !entries.contains(&owner) {
            entries.push(owner.clone());
          }
        }
      }
    }
    Ok(Some(Self { roles, roots, recursors, required: FxHashSet::default() }))
  }

  /// Structural and reader-only edges are mandatory for every carried record.
  fn extra(
    &self,
    env: &Env,
    address: &Address,
    c: &Constant,
  ) -> Result<Vec<Address>, String> {
    let mut edges = Vec::new();
    Env::closure_edges(address, c, &mut edges);
    drop(edges.drain(..c.refs.len()));
    if matches!(c.info, CI::IPrj(_) | CI::CPrj(_) | CI::RPrj(_) | CI::DPrj(_))
      && resolve(env, address).is_none()
    {
      return Err(format!(
        "binding support: invalid projection {}",
        address.hex()
      ));
    }
    if matches!(&c.info, CI::Muts(ms) if ms.iter().any(|m| matches!(m, MutConst::Indc(_))))
    {
      let rs = self.recursors.get(address).ok_or_else(|| {
        format!("binding support: inductive {} has no recursor", address.hex())
      })?;
      edges.extend(rs.iter().cloned());
    }
    let mut expressions: Vec<&Expr> =
      c.sharing.iter().map(AsRef::as_ref).collect();
    match &c.info {
      CI::Defn(d) => expressions.extend([d.typ.as_ref(), d.value.as_ref()]),
      CI::Axio(a) => expressions.push(&a.typ),
      CI::Quot(q) => expressions.push(&q.typ),
      CI::Recr(r) => {
        expressions.push(&r.typ);
        expressions.extend(r.rules.iter().map(|rule| rule.rhs.as_ref()));
      },
      CI::Muts(ms) => {
        for m in ms {
          match m {
            MutConst::Defn(d) => {
              expressions.extend([d.typ.as_ref(), d.value.as_ref()])
            },
            MutConst::Indc(i) => {
              expressions.push(&i.typ);
              expressions.extend(i.ctors.iter().map(|ctor| ctor.typ.as_ref()));
            },
            MutConst::Recr(r) => {
              expressions.push(&r.typ);
              expressions.extend(r.rules.iter().map(|rule| rule.rhs.as_ref()));
            },
          }
        }
      },
      _ => {},
    }
    let (mut nat, mut string) = (false, false);
    while let Some(e) = expressions.pop() {
      match e {
        Expr::Nat(i) | Expr::Str(i) => {
          nat = true;
          string |= matches!(e, Expr::Str(_));
          let blob = usize::try_from(*i)
            .ok()
            .and_then(|i| c.refs.get(i))
            .ok_or_else(|| {
              format!(
                "binding support: missing literal reference slot {i} in {}",
                address.hex()
              )
            })?;
          if !env.blobs.contains_key(blob) {
            return Err(format!(
              "binding support: missing literal blob {}",
              blob.hex()
            ));
          }
          edges.push(blob.clone());
        },
        Expr::Prj(_, _, v) => expressions.push(v),
        Expr::App(f, a) | Expr::Lam(_, f, a) | Expr::All(_, _, f, a) => {
          expressions.extend([f.as_ref(), a.as_ref()])
        },
        Expr::Let(_, t, v, b) => {
          expressions.extend([t.as_ref(), v.as_ref(), b.as_ref()])
        },
        _ => {},
      }
    }
    let literals = if string {
      &[
        Role::Nat,
        Role::NatZero,
        Role::NatSucc,
        Role::String,
        Role::StringOfList,
        Role::List,
        Role::ListNil,
        Role::ListCons,
        Role::Char,
        Role::CharOfNat,
      ][..]
    } else if nat {
      &[Role::Nat, Role::NatZero, Role::NatSucc][..]
    } else {
      &[]
    };
    for role in literals {
      edges.push(
        self
          .roles
          .get(role)
          .ok_or_else(|| {
            format!("binding support: missing literal role {role:?}")
          })?
          .clone(),
      );
    }
    Ok(edges)
  }

  pub(crate) fn seed(
    &mut self,
    env: &Env,
    assumed: &FxHashSet<Address>,
    visited: &mut FxHashSet<Address>,
    pending: &mut VecDeque<Address>,
  ) -> Result<(), String> {
    self.require(env, self.roots.clone(), assumed, visited, pending)
  }

  pub(crate) fn expand(
    &mut self,
    env: &Env,
    address: &Address,
    c: &Constant,
    assumed: &FxHashSet<Address>,
    visited: &mut FxHashSet<Address>,
    pending: &mut VecDeque<Address>,
  ) -> Result<(), String> {
    self.require(env, self.extra(env, address, c)?, assumed, visited, pending)
  }

  pub(crate) fn finish(
    &self,
    source: &Env,
    packed: &Env,
  ) -> Result<(), String> {
    if packed.role_binding != source.role_binding {
      return Err("binding support: binding changed during packing".into());
    }
    for address in &self.required {
      if (source.consts.contains_key(address)
        && !packed.consts.contains_key(address))
        || (source.blobs.contains_key(address)
          && !packed.blobs.contains_key(address))
        || packed.assumptions.contains(address)
      {
        return Err(format!(
          "binding support: required payload {} was not carried",
          address.hex()
        ));
      }
    }
    Ok(())
  }

  /// Upgrade support independently of the ordinary visited set: a metadata
  /// round can discover that an already visited/cut address is mandatory.
  fn require(
    &mut self,
    env: &Env,
    mut roots: Vec<Address>,
    assumed: &FxHashSet<Address>,
    visited: &mut FxHashSet<Address>,
    pending: &mut VecDeque<Address>,
  ) -> Result<(), String> {
    while let Some(address) = roots.pop() {
      if assumed.contains(&address) {
        return Err(format!(
          "binding support: mandatory address {} cannot be assumed",
          address.hex()
        ));
      }
      if !self.required.insert(address.clone()) {
        continue;
      }
      let constant = if env.consts.contains_key(&address) {
        Some(raw_constant(env, &address)?)
      } else {
        None
      };
      let blob = env.get_blob(&address);
      if let Some(bytes) = &blob
        && Address::hash(bytes) != address
      {
        return Err(format!(
          "binding support: bad blob hash {}",
          address.hex()
        ));
      }
      if let Some(c) = constant {
        Env::closure_edges(&address, &c, &mut roots);
        roots.extend(self.extra(env, &address, &c)?);
      } else if blob.is_none() {
        return Err(format!(
          "binding support: missing required data {}",
          address.hex()
        ));
      }
      if visited.insert(address.clone()) {
        pending.push_back(address);
      }
    }
    Ok(())
  }
}
