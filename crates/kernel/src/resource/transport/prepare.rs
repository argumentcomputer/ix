//! Logical metadata rebuilt from authenticated raw bytes, independently of profiles.
use super::*;
use ix_common::{address::Address, env::DefinitionSafety};
use ixon::resource::addressed::{AddressedProgram, STANDARD_AXIOMS};
use ixon::{
  constant::{
    Constant, ConstantInfo, Constructor as RawConstructor, DefKind, Definition,
    Inductive as RawInductive, MutConst, Recursor as RawRecursor,
    ctor_proj_constant, defn_proj_constant, indc_proj_constant,
    recr_proj_constant,
  },
  env::Env,
};
use std::collections::HashMap;

#[derive(Clone)]
struct Source {
  constant: Arc<Constant>,
  members: Vec<Address>,
  typ: Term,
  body: Option<Term>,
  kind: Kind,
  levels: usize,
  unsafe_primitive: bool,
  inductive: Option<RawInductive>,
  constructor: Option<(Address, RawConstructor)>,
  recursor: Option<RawRecursor>,
}
fn plain(
  c: Arc<Constant>,
  members: Vec<Address>,
  typ: Term,
  kind: Kind,
  levels: u64,
) -> Source {
  Source {
    constant: c,
    members,
    typ,
    body: None,
    kind,
    levels: levels as usize,
    unsafe_primitive: false,
    inductive: None,
    constructor: None,
    recursor: None,
  }
}
fn definition(
  c: Arc<Constant>,
  members: Vec<Address>,
  d: &Definition,
) -> Source {
  let kind = if d.safety != DefinitionSafety::Safe || d.kind == DefKind::Opaque
  {
    Kind::Opaque
  } else if d.kind == DefKind::Theorem {
    Kind::Theorem
  } else {
    Kind::Definition
  };
  let mut s = plain(c, members, d.typ.clone(), kind, d.lvls);
  s.body = Some(d.value.clone());
  s
}
fn recursor(
  c: Arc<Constant>,
  members: Vec<Address>,
  r: &RawRecursor,
) -> Source {
  let mut s = plain(c, members, r.typ.clone(), Kind::Recursor, r.lvls);
  s.unsafe_primitive = r.is_unsafe;
  s.recursor = Some(r.clone());
  s
}
fn member_wrapper(block: &Address, index: u64, m: &MutConst) -> Constant {
  match m {
    MutConst::Defn(_) => defn_proj_constant(index, block.clone()),
    MutConst::Indc(_) => indc_proj_constant(index, block.clone()),
    MutConst::Recr(_) => recr_proj_constant(index, block.clone()),
  }
}
fn source(
  constants: &HashMap<Address, Arc<Constant>>,
  address: &Address,
) -> Result<Source, String> {
  let c = constants
    .get(address)
    .ok_or("transport adapter: missing source constant")?;
  match &c.info {
    ConstantInfo::Defn(d) => {
      return Ok(definition(c.clone(), vec![address.clone()], d));
    },
    ConstantInfo::Recr(r) => {
      return Ok(recursor(c.clone(), vec![address.clone()], r));
    },
    ConstantInfo::Axio(a) => {
      return Ok(plain(
        c.clone(),
        vec![],
        a.typ.clone(),
        Kind::Axiom {
          standard: STANDARD_AXIOMS.contains(&address.hex().as_str()),
        },
        a.lvls,
      ));
    },
    ConstantInfo::Quot(q) => {
      return Ok(plain(
        c.clone(),
        vec![],
        q.typ.clone(),
        Kind::Quotient,
        q.lvls,
      ));
    },
    _ => {},
  }
  let (block, index, ctor) = match &c.info {
    ConstantInfo::DPrj(p) => (p.block.clone(), p.idx, None),
    ConstantInfo::IPrj(p) => (p.block.clone(), p.idx, None),
    ConstantInfo::RPrj(p) => (p.block.clone(), p.idx, None),
    ConstantInfo::CPrj(p) => (p.block.clone(), p.idx, Some(p.cidx)),
    _ => return Err("transport adapter: unexpected source wrapper".into()),
  };
  let parent =
    constants.get(&block).ok_or("transport adapter: missing mutual parent")?;
  let ConstantInfo::Muts(members) = &parent.info else {
    return Err("transport adapter: invalid mutual parent".into());
  };
  let addresses = members
    .iter()
    .enumerate()
    .map(|(i, m)| member_wrapper(&block, i as u64, m).commit().0)
    .collect::<Vec<_>>();
  let member = members
    .get(index as usize)
    .ok_or("transport adapter: invalid mutual member")?;
  Ok(match (member, ctor) {
    (MutConst::Defn(d), None) => definition(parent.clone(), addresses, d),
    (MutConst::Recr(r), None) => recursor(parent.clone(), addresses, r),
    (MutConst::Indc(ind), None) => {
      let mut s = plain(
        parent.clone(),
        addresses,
        ind.typ.clone(),
        Kind::Inductive,
        ind.lvls,
      );
      s.unsafe_primitive = ind.is_unsafe;
      s.inductive = Some(ind.clone());
      s
    },
    (MutConst::Indc(ind), Some(j)) => {
      let ctor = ind
        .ctors
        .get(j as usize)
        .ok_or("transport adapter: invalid constructor ordinal")?;
      let family = addresses[index as usize].clone();
      let mut s = plain(
        parent.clone(),
        addresses,
        ctor.typ.clone(),
        Kind::Constructor,
        ctor.lvls,
      );
      s.unsafe_primitive = ctor.is_unsafe || ind.is_unsafe;
      s.constructor = Some((family, ctor.clone()));
      s
    },
    _ => return Err("transport adapter: wrapper kind mismatch".into()),
  })
}
fn index(
  map: &HashMap<Address, u64>,
  address: &Address,
) -> Result<u64, String> {
  map
    .get(address)
    .copied()
    .ok_or_else(|| "transport adapter: missing reference".into())
}
struct Tables<'a> {
  source: &'a Source,
  indices: &'a HashMap<Address, u64>,
  blobs: &'a HashMap<Address, u64>,
  shares: usize,
  levels: usize,
}
impl Tables<'_> {
  fn reference(&self, i: u64) -> Result<&Address, String> {
    self
      .source
      .constant
      .refs
      .get(i as usize)
      .ok_or_else(|| "transport adapter: bad reference".into())
  }
  fn level(&self, i: u64) -> Result<u64, String> {
    if i as usize >= self.source.constant.univs.len() {
      return Err("transport adapter: universe index".into());
    }
    u64::try_from(self.levels)
      .ok()
      .and_then(|n| n.checked_add(i))
      .ok_or_else(|| "transport adapter: level overflow".into())
  }
  fn remap(&self, fuel: usize, e: &Term) -> Result<Term, String> {
    let fuel =
      fuel.checked_sub(1).ok_or("transport adapter: expression depth")?;
    Ok(Arc::new(match e.as_ref() {
      Expr::Var(_) => return Ok(e.clone()),
      Expr::Sort(i) => Expr::Sort(self.level(*i)?),
      Expr::Ref(i, levels) => Expr::Ref(
        index(self.indices, self.reference(*i)?)?,
        levels.iter().map(|i| self.level(*i)).collect::<Result<_, _>>()?,
      ),
      Expr::Rec(i, levels) => Expr::Ref(
        index(
          self.indices,
          self
            .source
            .members
            .get(*i as usize)
            .ok_or("transport adapter: recursive index")?,
        )?,
        levels.iter().map(|i| self.level(*i)).collect::<Result<_, _>>()?,
      ),
      Expr::Nat(i) => Expr::Nat(index(self.blobs, self.reference(*i)?)?),
      Expr::Str(i) => Expr::Str(index(self.blobs, self.reference(*i)?)?),
      Expr::Share(i) => {
        if *i as usize >= self.source.constant.sharing.len() {
          return Err("transport adapter: sharing index".into());
        }
        Expr::Share(
          u64::try_from(self.shares)
            .ok()
            .and_then(|n| n.checked_add(*i))
            .ok_or("transport adapter: sharing overflow")?,
        )
      },
      Expr::Prj(i, f, v) => Expr::Prj(
        index(self.indices, self.reference(*i)?)?,
        *f,
        self.remap(fuel, v)?,
      ),
      Expr::App(f, a) => Expr::App(self.remap(fuel, f)?, self.remap(fuel, a)?),
      Expr::Lam(c, a, b) => {
        Expr::Lam(*c, self.remap(fuel, a)?, self.remap(fuel, b)?)
      },
      Expr::All(c, r, a, b) => {
        Expr::All(*c, *r, self.remap(fuel, a)?, self.remap(fuel, b)?)
      },
      Expr::Let(c, a, v, b) => Expr::Let(
        *c,
        self.remap(fuel, a)?,
        self.remap(fuel, v)?,
        self.remap(fuel, b)?,
      ),
    }))
  }
}
pub(super) fn prepare(
  env: &Env,
  resolved: &AddressedProgram,
  limits: Limits,
) -> Result<(Program, Metadata), String> {
  let mut constants = HashMap::new();
  for entry in &env.consts {
    let raw = entry.value().raw_bytes();
    let mut input = raw;
    let c = Constant::get(&mut input)?;
    let mut canonical = vec![];
    c.put(&mut canonical);
    if !input.is_empty() || canonical != raw || c.commit().0 != *entry.key() {
      return Err("transport adapter: noncanonical source constant".into());
    }
    constants.insert(entry.key().clone(), Arc::new(c));
  }
  let indices = resolved
    .addresses
    .iter()
    .enumerate()
    .map(|(i, a)| (a.clone(), i as u64))
    .collect::<HashMap<_, _>>();
  let mut blobs = HashMap::new();
  let mut metadata = Metadata::default();
  let mut entries = env
    .blobs
    .iter()
    .map(|e| (e.key().clone(), e.value().clone()))
    .collect::<Vec<_>>();
  entries.sort_by(|a, b| a.0.cmp(&b.0));
  for (address, bytes) in entries {
    let i = blobs.len() as u64;
    blobs.insert(address, i);
    metadata.naturals.push((i, BigUint::from_bytes_le(&bytes)));
  }
  let prim = crate::primitive::PrimAddrs::new();
  metadata.nat_type =
    indices.get(&prim.nat).map(|i| Expr::reference(*i, vec![]));
  metadata.string_type =
    indices.get(&prim.string).map(|i| Expr::reference(*i, vec![]));
  metadata.eq_type = indices.get(&prim.eq).copied();
  let mut p =
    Program { groups: resolved.program.groups.clone(), ..Program::default() };
  let mut offsets = HashMap::new();
  let mut recursors = vec![];
  for (i, address) in resolved.addresses.iter().enumerate() {
    let source = source(&constants, address)?;
    if source.unsafe_primitive {
      metadata.unsafe_primitives.push(i);
    }
    let parent = source.constant.commit().0;
    let (shares, levels) = offsets
      .get(&parent)
      .copied()
      .unwrap_or((p.sharing.len(), metadata.universes.len()));
    let tables = Tables {
      source: &source,
      indices: &indices,
      blobs: &blobs,
      shares,
      levels,
    };
    if !offsets.contains_key(&parent) {
      offsets.insert(parent.clone(), (shares, levels));
      metadata.universes.extend(source.constant.univs.iter().cloned());
      for e in &source.constant.sharing {
        p.sharing.push(tables.remap(limits.depth, e)?);
      }
    }
    p.declarations.push(Declaration {
      typ: tables.remap(limits.depth, &source.typ)?,
      body: source
        .body
        .as_ref()
        .map(|b| tables.remap(limits.depth, b))
        .transpose()?,
      kind: resolved.program.declarations[i].kind,
    });
    metadata.kinds.push(source.kind.clone());
    metadata.level_arities.push(source.levels);
    if let Some(ind) = &source.inductive {
      let ordinal =
        source.members.iter().position(|a| a == address).unwrap_or(0);
      let constructors = (0..ind.ctors.len())
        .map(|j| {
          index(
            &indices,
            &ctor_proj_constant(ordinal as u64, j as u64, parent.clone())
              .commit()
              .0,
          )
        })
        .collect::<Result<Vec<_>, _>>()?;
      metadata.inductives.push(Inductive {
        index: i as u64,
        params: ind.params as usize,
        indices: ind.indices as usize,
        constructors,
      });
    }
    if let Some((owner, ctor)) = &source.constructor {
      metadata.constructors.push(Constructor {
        index: i as u64,
        family: index(&indices, owner)?,
        position: ctor.cidx as usize,
        params: ctor.params as usize,
        fields: ctor.fields as usize,
      });
    }
    if let Some(rec) = &source.recursor {
      let rules = rec
        .rules
        .iter()
        .map(|r| {
          Ok(Rule {
            fields: r.fields as usize,
            rhs: tables.remap(limits.depth, &r.rhs)?,
          })
        })
        .collect::<Result<Vec<_>, String>>()?;
      for r in &rules {
        p.auxiliary.push((i, r.rhs.clone()));
      }
      recursors.push((i, rec.clone(), rules));
    }
  }
  p = source_program(&metadata, &p);
  for (i, rec, rules) in recursors {
    let family = {
      let mut c =
        TransportChecker::new(&p, &resolved.program, &metadata, limits);
      let mut typ = p.declarations[i].typ.clone();
      for _ in 0..(rec.params + rec.motives + rec.minors + rec.indices) {
        typ = c.arrow(limits.depth, &typ).map_err(|e| e.to_string())?.3;
      }
      let major = c.arrow(limits.depth, &typ).map_err(|e| e.to_string())?.2;
      let major = c.whnf(limits.depth, &major).map_err(|e| e.to_string())?;
      let (head, _) =
        c.split_app(limits.depth, &major).map_err(|e| e.to_string())?;
      let Expr::Ref(family, _) = head.as_ref() else {
        return Err(
          "transport adapter: recursor major family not exposed".into(),
        );
      };
      *family
    };
    metadata.recursors.push(Recursor {
      index: i as u64,
      family,
      k: rec.k,
      params: rec.params as usize,
      motives: rec.motives as usize,
      minors: rec.minors as usize,
      indices: rec.indices as usize,
      rules,
    });
  }
  metadata.resource_sensitive =
    resource_sensitivity(&p, &resolved.program, limits)
      .map_err(|e| e.to_string())?;
  Ok((p, metadata))
}
