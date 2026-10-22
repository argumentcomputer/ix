//! Unwired original-data finalization. No checker or scheduler reads receipts.

use std::{cmp::Ordering, sync::Arc};

use ix_common::{
  address::Address,
  env::{Name, NameData, ReducibilityHints},
};
use ixon::{Constant, ConstantInfo, DefKind, Env, LazyConstant, MutConst};
use rustc_hash::FxHashMap;

#[derive(Clone, Debug)]
pub struct Payload {
  pub addr: Address,
  pub bytes: Arc<[u8]>,
}

/// `None` means unavailable; `Some(None)` is a known absent hint. Publication
/// and original addresses bind the data to the final owner of this exact name.
#[derive(Clone, Debug)]
pub struct Receipt {
  pub name: Name,
  pub published: Address,
  pub original: Payload,
  pub hints: Option<Option<ReducibilityHints>>,
  pub block: Option<Payload>,
}

pub type OriginalStaging = Vec<Receipt>;

enum Member {
  Defn(DefKind),
  Indc(usize),
  Recr,
}
enum Projection {
  Defn,
  Indc,
  Recr,
  Ctor(u64),
}
enum Shape {
  Plain,
  Defn(DefKind),
  Block(Vec<Member>),
  Projection(Address, u64, Projection),
}

#[derive(Default)]
struct Tables {
  originals: FxHashMap<Address, Arc<[u8]>>,
  hints: FxHashMap<Name, Option<ReducibilityHints>>,
}

// Name's Ord compares only its root digest. Confirm ties structurally, as
// Lean's nameCompareExact does; never use a digest collision as name equality.
fn raw_name_order(a: &Name, b: &Name) -> Ordering {
  use NameData::{Anonymous, Num, Str};
  match (a.as_data(), b.as_data()) {
    (Anonymous(x), Anonymous(y)) => x.as_bytes().cmp(y.as_bytes()),
    (Anonymous(_), _) | (Str(..), Num(..)) => Ordering::Less,
    (_, Anonymous(_)) | (Num(..), Str(..)) => Ordering::Greater,
    (Str(ap, av, ah), Str(bp, bv, bh)) => raw_name_order(ap, bp)
      .then_with(|| av.cmp(bv))
      .then_with(|| ah.as_bytes().cmp(bh.as_bytes())),
    (Num(ap, av, ah), Num(bp, bv, bh)) => raw_name_order(ap, bp)
      .then_with(|| av.cmp(bv))
      .then_with(|| ah.as_bytes().cmp(bh.as_bytes())),
  }
}

fn inspect(a: &Address, bytes: &[u8]) -> Result<Shape, String> {
  if Address::hash(bytes) != *a {
    return Err(format!("original data: hash mismatch at {}", a.hex()));
  }
  let mut input = bytes;
  let c = Constant::get(&mut input)?;
  let mut canonical = Vec::new();
  c.put(&mut canonical);
  if !input.is_empty() || canonical != bytes {
    return Err(format!("original data: noncanonical bytes at {}", a.hex()));
  }
  Ok(match c.info {
    ConstantInfo::Defn(d) => Shape::Defn(d.kind),
    ConstantInfo::DPrj(p) => {
      Shape::Projection(p.block, p.idx, Projection::Defn)
    },
    ConstantInfo::IPrj(p) => {
      Shape::Projection(p.block, p.idx, Projection::Indc)
    },
    ConstantInfo::RPrj(p) => {
      Shape::Projection(p.block, p.idx, Projection::Recr)
    },
    ConstantInfo::CPrj(p) => {
      Shape::Projection(p.block, p.idx, Projection::Ctor(p.cidx))
    },
    ConstantInfo::Muts(ms) => Shape::Block(
      ms.into_iter()
        .map(|m| match m {
          MutConst::Defn(d) => Member::Defn(d.kind),
          MutConst::Indc(i) => Member::Indc(i.ctors.len()),
          MutConst::Recr(_) => Member::Recr,
        })
        .collect(),
    ),
    _ => Shape::Plain,
  })
}

fn requires_hint(
  views: &FxHashMap<Address, Shape>,
  name: &Name,
  rows: &[&Receipt],
  shape: &Shape,
) -> Result<bool, String> {
  let fail = |what| format!("original data: {what} for {}", name.pretty());
  let Shape::Projection(block, index, kind) = shape else {
    if rows.iter().any(|r| r.block.is_some()) {
      return Err(fail("unexpected projection block"));
    }
    return Ok(matches!(shape, Shape::Defn(DefKind::Definition)));
  };
  if rows.iter().any(|r| r.block.is_none()) {
    return Err(fail("missing projection block"));
  }
  if rows.iter().any(|r| r.block.as_ref().map(|b| &b.addr) != Some(block)) {
    return Err(fail("mismatched projection block"));
  }
  let Some(Shape::Block(members)) = views.get(block) else {
    return Err(fail("projection block is not mutual"));
  };
  let member = usize::try_from(*index)
    .ok()
    .and_then(|i| members.get(i))
    .ok_or_else(|| fail("projection index out of range"))?;
  match (kind, member) {
    (Projection::Defn, Member::Defn(k)) => Ok(*k == DefKind::Definition),
    (Projection::Indc, Member::Indc(_)) | (Projection::Recr, Member::Recr) => {
      Ok(false)
    },
    (Projection::Ctor(i), Member::Indc(count)) => {
      if usize::try_from(*i).ok().is_none_or(|i| i >= *count) {
        return Err(fail("constructor index out of range"));
      }
      Ok(false)
    },
    _ => Err(fail("projection member kind mismatch")),
  }
}

fn prepare(staging: &[Receipt], base: &Env) -> Result<Tables, String> {
  let mut targets = FxHashMap::default();
  for entry in base.named.iter() {
    if let Some((original, _)) = entry.value().original_checked()? {
      targets.insert(
        entry.key().clone(),
        (entry.value().addr.clone(), original, entry.value().hints()),
      );
    }
  }
  let mut by_name: FxHashMap<Name, Vec<&Receipt>> = FxHashMap::default();
  let mut payloads = Vec::new();
  for row in staging {
    if targets.get(&row.name).is_some_and(|(published, original, _)| {
      *published == row.published && *original == row.original.addr
    }) {
      by_name.entry(row.name.clone()).or_default().push(row);
      payloads.push(&row.original);
      if let Some(block) = &row.block {
        payloads.push(block);
      }
    }
  }
  payloads.sort_unstable_by(|a, b| a.addr.cmp(&b.addr));
  let mut bytes: FxHashMap<Address, Arc<[u8]>> = FxHashMap::default();
  for raw in payloads {
    if let Some(old) = bytes.get(&raw.addr) {
      if *old != raw.bytes {
        return Err(format!(
          "original data: conflicting captured bytes at {}",
          raw.addr.hex()
        ));
      }
    } else {
      bytes.insert(raw.addr.clone(), raw.bytes.clone());
    }
  }
  let mut bytes: Vec<_> = bytes.into_iter().collect();
  bytes.sort_unstable_by(|a, b| a.0.cmp(&b.0));
  let mut views = FxHashMap::default();
  let mut out = Tables::default();
  for (a, raw) in bytes {
    if let Some(stored) = base.consts.get(&a)
      && stored.raw_bytes() != raw.as_ref()
    {
      return Err(format!(
        "original data: conflicting canonical bytes at {}",
        a.hex()
      ));
    }
    views.insert(a.clone(), inspect(&a, &raw)?);
    if !base.consts.contains_key(&a) {
      out.originals.insert(a, raw);
    }
  }
  let mut targets: Vec<_> = targets.into_iter().collect();
  targets.sort_unstable_by(|a, b| {
    a.0.cmp(&b.0).then_with(|| raw_name_order(&a.0, &b.0))
  });
  for (name, (_, _, final_hint)) in targets {
    let fail = |what| format!("original data: {what} for {}", name.pretty());
    let rows = by_name.get(&name).ok_or_else(|| fail("missing receipt"))?;
    let first = rows.first().ok_or_else(|| fail("missing receipt"))?;
    let shape = views
      .get(&first.original.addr)
      .ok_or_else(|| fail("missing captured record"))?;
    if rows.iter().any(|r| r.hints.is_none()) {
      return Err(fail("unavailable original hints"));
    }
    let hint = first.hints.ok_or_else(|| fail("unavailable original hints"))?;
    if requires_hint(&views, &name, rows, shape)?
      && rows.iter().any(|r| r.hints == Some(None))
    {
      return Err(fail("missing definition hints"));
    }
    if rows.iter().any(|r| r.hints != Some(hint)) {
      return Err(fail("conflicting original hints"));
    }
    if hint != final_hint {
      out.hints.insert(name, hint);
    }
  }
  Ok(out)
}

/// Recompute only the two unchecked tables. All validation precedes mutation;
/// errors preserve even the old original-data tables. No driver calls this yet.
pub fn finalize_originals(
  staging: &[Receipt],
  env: &mut Env,
) -> Result<(), String> {
  let tables = prepare(staging, env)?;
  env.originals.clear();
  for (a, bytes) in tables.originals {
    env.originals.insert(a, LazyConstant::from_bytes(bytes));
  }
  env.original_hint_overrides.clear();
  for (n, hint) in tables.hints {
    env.original_hint_overrides.insert(n, hint);
  }
  Ok(())
}
