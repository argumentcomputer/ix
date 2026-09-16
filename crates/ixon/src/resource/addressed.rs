//! Addressed resource interfaces. Mirrors `Ix/Resource/Addressed.lean`.
//! Resource admission and erased typing are separate prerequisites; `prepare`
//! resolves bytes and interfaces but deliberately creates no certificate.

use super::*;
use crate::constant::{
  Constant, ConstantInfo, Definition, MutConst, Recursor, ctor_proj_constant,
  defn_proj_constant, indc_proj_constant, recr_proj_constant,
};
use crate::env::Env;
use crate::tag::Tag0;
use ix_common::address::Address;
use ix_common::env::DefinitionSafety;
use rustc_hash::FxHashMap;

pub const VALIDATOR_ID: &str = "ixon-v3/resource-v1";

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Profile {
  pub assumptions: Vec<Address>,
  pub shareable_types: Vec<Address>,
  pub choices: Vec<Address>,
  pub nat_type: Option<Address>,
  pub string_type: Option<Address>,
  pub limits: Limits,
}

impl Profile {
  pub fn validate(&self) -> Result<(), String> {
    for list in [&self.assumptions, &self.shareable_types, &self.choices] {
      if list.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(
          "resource profile: address lists must be strictly increasing".into(),
        );
      }
    }
    if self.choices.iter().any(|c| !self.assumptions.contains(c)) {
      return Err(
        "resource profile: selection primitive must be an explicit assumption"
          .into(),
      );
    }
    if self.limits.depth == 0 || self.limits.steps == 0 {
      return Err("resource profile: invalid checker limits".into());
    }
    Ok(())
  }

  pub fn bytes(&self) -> Vec<u8> {
    let mut bytes = format!("{VALIDATOR_ID}/profile\0").into_bytes();
    for list in [&self.assumptions, &self.shareable_types, &self.choices] {
      Tag0::new(list.len() as u64).put(&mut bytes);
      for address in list {
        bytes.extend_from_slice(address.as_bytes());
      }
    }
    for address in [&self.nat_type, &self.string_type] {
      match address {
        None => bytes.push(0),
        Some(address) => {
          bytes.push(1);
          bytes.extend_from_slice(address.as_bytes());
        },
      }
    }
    Tag0::new(self.limits.depth as u64).put(&mut bytes);
    Tag0::new(self.limits.steps as u64).put(&mut bytes);
    bytes
  }

  pub fn address(&self) -> Result<Address, String> {
    self.validate()?;
    Ok(Address::hash(&self.bytes()))
  }

  pub fn from_bytes(mut bytes: &[u8]) -> Result<Self, String> {
    let prefix = format!("{VALIDATOR_ID}/profile\0");
    bytes = bytes
      .strip_prefix(prefix.as_bytes())
      .ok_or("resource profile: wrong validator identifier")?;
    fn list(bytes: &mut &[u8]) -> Result<Vec<Address>, String> {
      let count = Tag0::get(bytes)?.size;
      if count > (bytes.len() / 32) as u64 {
        return Err("resource profile: impossible address count".into());
      }
      let mut result = vec![];
      for _ in 0..count {
        let (head, tail) = bytes.split_at(32);
        result.push(
          Address::from_slice(head)
            .map_err(|_error| "resource profile: invalid address")?,
        );
        *bytes = tail;
      }
      Ok(result)
    }
    fn optional(bytes: &mut &[u8]) -> Result<Option<Address>, String> {
      match crate::serialize::get_u8(bytes)? {
        0 => Ok(None),
        1 => {
          let (head, tail) = bytes
            .split_at_checked(32)
            .ok_or("resource profile: truncated address")?;
          *bytes = tail;
          Ok(Some(
            Address::from_slice(head)
              .map_err(|_error| "resource profile: invalid address")?,
          ))
        },
        _ => Err("resource profile: invalid optional address tag".into()),
      }
    }
    let profile = Self {
      assumptions: list(&mut bytes)?,
      shareable_types: list(&mut bytes)?,
      choices: list(&mut bytes)?,
      nat_type: optional(&mut bytes)?,
      string_type: optional(&mut bytes)?,
      limits: Limits {
        depth: usize::try_from(Tag0::get(&mut bytes)?.size)
          .map_err(|_error| "resource profile: depth overflow")?,
        steps: usize::try_from(Tag0::get(&mut bytes)?.size)
          .map_err(|_error| "resource profile: steps overflow")?,
      },
    };
    if !bytes.is_empty() {
      return Err("resource profile: trailing bytes".into());
    }
    profile.validate()?;
    Ok(profile)
  }
}

#[derive(Clone, Debug)]
pub struct AddressedProgram {
  pub program: Program,
  pub policy: Policy,
  pub addresses: Vec<Address>,
  pub profile_address: Address,
}

struct Pending {
  address: Address,
  parent: Address,
  constant: Arc<Constant>,
  members: Vec<Address>,
  declaration: Declaration,
  auxiliary: Vec<Term>,
}

fn definition(d: &Definition) -> Declaration {
  Declaration {
    typ: d.typ.clone(),
    body: Some(d.value.clone()),
    kind: if d.safety == DefinitionSafety::Safe {
      DeclKind::Definition
    } else {
      DeclKind::Assumption
    },
  }
}

fn recursor(d: &Recursor) -> Declaration {
  Declaration { typ: d.typ.clone(), body: None, kind: DeclKind::Assumption }
}

fn member_wrapper(block: &Address, index: u64, member: &MutConst) -> Constant {
  match member {
    MutConst::Defn(_) => defn_proj_constant(index, block.clone()),
    MutConst::Indc(_) => indc_proj_constant(index, block.clone()),
    MutConst::Recr(_) => recr_proj_constant(index, block.clone()),
  }
}

fn require_wrapper(
  constants: &FxHashMap<Address, Arc<Constant>>,
  expected: &Constant,
) -> Result<Address, String> {
  let address = expected.commit().0;
  match constants.get(&address) {
    Some(actual) if actual.as_ref() == expected => Ok(address),
    _ => Err(format!(
      "resource adapter: missing or invalid canonical projection {address:?}"
    )),
  }
}

fn index(
  indices: &FxHashMap<Address, u64>,
  address: &Address,
) -> Result<u64, String> {
  indices.get(address).copied().ok_or_else(|| {
    format!("resource adapter: missing typed interface {address:?}")
  })
}

fn native_index(index: u64) -> Result<usize, String> {
  usize::try_from(index)
    .map_err(|_error| "resource adapter: index overflow".into())
}

struct Tables<'a> {
  refs: &'a [Address],
  members: &'a [Address],
  indices: &'a FxHashMap<Address, u64>,
  kinds: &'a [DeclKind],
  blobs: &'a FxHashMap<Address, u64>,
  univ_count: usize,
  share_count: usize,
  share_offset: usize,
}

impl Tables<'_> {
  fn reference(&self, i: u64) -> Result<&Address, String> {
    let i = usize::try_from(i)
      .map_err(|_error| "resource adapter: reference index overflow")?;
    self
      .refs
      .get(i)
      .ok_or_else(|| "resource adapter: reference index out of bounds".into())
  }

  fn universes(&self, levels: &[u64]) -> Result<(), String> {
    if levels.iter().any(|l| *l >= self.univ_count as u64) {
      return Err("resource adapter: universe index out of bounds".into());
    }
    Ok(())
  }

  fn remap(&self, fuel: usize, e: &Term) -> Result<Term, String> {
    let fuel = fuel
      .checked_sub(1)
      .ok_or("resource adapter: expression depth exceeded")?;
    Ok(Arc::new(match e.as_ref() {
      Expr::Var(_) => return Ok(e.clone()),
      Expr::Sort(level) => {
        self.universes(&[*level])?;
        return Ok(e.clone());
      },
      Expr::Ref(i, levels) => {
        self.universes(levels)?;
        Expr::Ref(index(self.indices, self.reference(*i)?)?, levels.clone())
      },
      Expr::Rec(i, levels) => {
        self.universes(levels)?;
        let i = usize::try_from(*i)
          .map_err(|_error| "resource adapter: recursive index overflow")?;
        let address = self
          .members
          .get(i)
          .ok_or("resource adapter: recursive index out of bounds")?;
        Expr::Ref(index(self.indices, address)?, levels.clone())
      },
      Expr::Nat(i) | Expr::Str(i) => {
        let address = self.reference(*i)?;
        let id = *self.blobs.get(address).ok_or_else(|| {
          format!("resource adapter: missing literal blob {address:?}")
        })?;
        match e.as_ref() {
          Expr::Nat(_) => Expr::Nat(id),
          _ => Expr::Str(id),
        }
      },
      Expr::Share(i) => {
        let i = usize::try_from(*i)
          .map_err(|_error| "resource adapter: sharing index overflow")?;
        if i >= self.share_count {
          return Err("resource adapter: sharing index out of bounds".into());
        }
        Expr::Share(
          self
            .share_offset
            .checked_add(i)
            .and_then(|n| u64::try_from(n).ok())
            .ok_or("resource adapter: index overflow")?,
        )
      },
      Expr::Prj(i, field, value) => {
        let id = index(self.indices, self.reference(*i)?)?;
        if self.kinds.get(native_index(id)?) != Some(&DeclKind::TypeConstructor)
        {
          return Err(
            "resource adapter: projection owner is not an inductive type"
              .into(),
          );
        }
        Expr::Prj(id, *field, self.remap(fuel, value)?)
      },
      Expr::App(f, a) => Expr::App(self.remap(fuel, f)?, self.remap(fuel, a)?),
      Expr::Lam(c, t, b) => {
        Expr::Lam(*c, self.remap(fuel, t)?, self.remap(fuel, b)?)
      },
      Expr::All(c, r, t, b) => {
        Expr::All(*c, *r, self.remap(fuel, t)?, self.remap(fuel, b)?)
      },
      Expr::Let(c, t, v, b) => Expr::Let(
        *c,
        self.remap(fuel, t)?,
        self.remap(fuel, v)?,
        self.remap(fuel, b)?,
      ),
    }))
  }
}

fn closed(
  checker: &mut Checker<'_>,
  fuel: usize,
  depth: u64,
  e: &Term,
) -> Result<bool, Error> {
  let fuel = checker.tick(fuel)?;
  Ok(match e.as_ref() {
    Expr::Var(i) => *i < depth,
    Expr::Share(i) => closed(checker, fuel, depth, &checker.expansion(*i)?)?,
    Expr::Rec(..) => false,
    Expr::App(f, a) => {
      closed(checker, fuel, depth, f)? && closed(checker, fuel, depth, a)?
    },
    Expr::Lam(_, t, b) | Expr::All(_, _, t, b) => {
      closed(checker, fuel, depth, t)? && closed(checker, fuel, depth + 1, b)?
    },
    Expr::Let(_, t, v, b) => {
      closed(checker, fuel, depth, t)?
        && closed(checker, fuel, depth, v)?
        && closed(checker, fuel, depth + 1, b)?
    },
    Expr::Prj(_, _, v) => closed(checker, fuel, depth, v)?,
    _ => true,
  })
}

fn fields(
  program: &Program,
  limits: Limits,
  type_ref: u64,
  ctor: u64,
  count: u64,
) -> Result<Vec<Field>, Error> {
  let mut checker = Checker::new(program, limits);
  let mut typ = checker.declaration(ctor)?.typ.clone();
  let mut fields = vec![];
  for index in 0..count {
    typ = checker.whnf(limits.depth, &typ)?;
    let Expr::All(input, _, domain, body) = typ.as_ref() else {
      return Err(Error::Unsupported("constructor field telescope"));
    };
    if input.uses != Uses::Many
      || !closed(&mut checker, limits.depth, 0, domain)?
    {
      return Err(Error::Unsupported(
        "dependent or finite-use projection field",
      ));
    }
    fields.push(Field {
      type_ref,
      index,
      typ: domain.clone(),
      contract: input.value,
    });
    typ = body.clone();
  }
  Ok(fields)
}

pub fn prepare(
  env: &Env,
  profile: &Profile,
) -> Result<AddressedProgram, String> {
  let profile_address = profile.address()?;
  let mut entries: Vec<_> =
    env.consts.iter().map(|r| (r.key().clone(), r.value().clone())).collect();
  entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
  let mut constants = FxHashMap::default();
  for (address, lazy) in &entries {
    let raw = lazy.raw_bytes();
    if Address::hash(raw) != *address {
      return Err(format!(
        "resource adapter: constant hash mismatch {address:?}"
      ));
    }
    let mut input = raw;
    let constant = Constant::get(&mut input)?;
    let mut canonical = vec![];
    constant.put(&mut canonical);
    if !input.is_empty() || canonical != raw {
      return Err(format!(
        "resource adapter: noncanonical constant {address:?}"
      ));
    }
    constants.insert(address.clone(), Arc::new(constant));
  }
  let mut pending = vec![];
  let mut groups = vec![];
  let mut field_specs = vec![];
  for (address, _) in &entries {
    let constant = &constants[address];
    let parent = address.clone();
    let mut push = |address: Address,
                    members: Vec<Address>,
                    declaration: Declaration,
                    auxiliary: Vec<Term>| {
      pending.push(Pending {
        address,
        parent: parent.clone(),
        constant: constant.clone(),
        members,
        declaration,
        auxiliary,
      });
    };
    match &constant.info {
      ConstantInfo::Defn(d) => {
        push(address.clone(), vec![address.clone()], definition(d), vec![])
      },
      ConstantInfo::Recr(r) => push(
        address.clone(),
        vec![address.clone()],
        recursor(r),
        r.rules.iter().map(|r| r.rhs.clone()).collect(),
      ),
      ConstantInfo::Axio(a) => push(
        address.clone(),
        vec![],
        Declaration {
          typ: a.typ.clone(),
          body: None,
          kind: DeclKind::Assumption,
        },
        vec![],
      ),
      ConstantInfo::Quot(q) => push(
        address.clone(),
        vec![],
        Declaration {
          typ: q.typ.clone(),
          body: None,
          kind: DeclKind::Assumption,
        },
        vec![],
      ),
      ConstantInfo::Muts(members) => {
        if members.is_empty() {
          return Err("resource adapter: empty mutual block".into());
        }
        let addresses = members
          .iter()
          .enumerate()
          .map(|(i, m)| {
            require_wrapper(&constants, &member_wrapper(address, i as u64, m))
          })
          .collect::<Result<Vec<_>, _>>()?;
        let mut group = addresses.clone();
        for (i, member) in members.iter().enumerate() {
          let addr = &addresses[i];
          match member {
            MutConst::Defn(d) => {
              push(addr.clone(), addresses.clone(), definition(d), vec![])
            },
            MutConst::Recr(r) => push(
              addr.clone(),
              addresses.clone(),
              recursor(r),
              r.rules.iter().map(|r| r.rhs.clone()).collect(),
            ),
            MutConst::Indc(ind) => {
              push(
                addr.clone(),
                addresses.clone(),
                Declaration {
                  typ: ind.typ.clone(),
                  body: None,
                  kind: if ind.is_unsafe {
                    DeclKind::Assumption
                  } else {
                    DeclKind::TypeConstructor
                  },
                },
                vec![],
              );
              for (j, ctor) in ind.ctors.iter().enumerate() {
                let ctor_addr = require_wrapper(
                  &constants,
                  &ctor_proj_constant(i as u64, j as u64, address.clone()),
                )?;
                if ctor.cidx != j as u64
                  || ctor.params != ind.params
                  || ctor.lvls != ind.lvls
                {
                  return Err(
                    "resource adapter: inconsistent constructor header".into(),
                  );
                }
                push(
                  ctor_addr.clone(),
                  addresses.clone(),
                  Declaration {
                    typ: ctor.typ.clone(),
                    body: None,
                    kind: if ctor.is_unsafe {
                      DeclKind::Assumption
                    } else {
                      DeclKind::Constructor
                    },
                  },
                  vec![],
                );
                group.push(ctor_addr.clone());
                if !ind.is_unsafe
                  && !ctor.is_unsafe
                  && ind.params == 0
                  && ind.indices == 0
                  && ind.ctors.len() == 1
                {
                  field_specs.push((addr.clone(), ctor_addr, ctor.fields));
                }
              }
            },
          }
        }
        groups.push(group);
      },
      _ => {},
    }
  }
  pending.sort_unstable_by(|a, b| a.address.cmp(&b.address));
  let mut indices = FxHashMap::default();
  let mut addresses = vec![];
  for (i, p) in pending.iter().enumerate() {
    if indices.insert(p.address.clone(), i as u64).is_some() {
      return Err("resource adapter: duplicate resolved declaration".into());
    }
    addresses.push(p.address.clone());
  }
  for (address, constant) in &constants {
    if matches!(
      constant.info,
      ConstantInfo::DPrj(_)
        | ConstantInfo::IPrj(_)
        | ConstantInfo::RPrj(_)
        | ConstantInfo::CPrj(_)
    ) && !indices.contains_key(address)
    {
      return Err(format!(
        "resource adapter: invalid or orphan projection {address:?}"
      ));
    }
  }
  let mut blob_entries: Vec<_> =
    env.blobs.iter().map(|r| (r.key().clone(), r.value().clone())).collect();
  blob_entries.sort_unstable_by(|a, b| a.0.cmp(&b.0));
  let mut blobs = FxHashMap::default();
  for (address, bytes) in blob_entries {
    if Address::hash(&bytes) != address {
      return Err(format!("resource adapter: blob hash mismatch {address:?}"));
    }
    blobs.insert(address, blobs.len() as u64);
  }
  let kinds: Vec<_> = pending.iter().map(|p| p.declaration.kind).collect();
  let mut program = Program::default();
  let mut offsets = FxHashMap::default();
  for p in &pending {
    let tables = Tables {
      refs: &p.constant.refs,
      members: &p.members,
      indices: &indices,
      kinds: &kinds,
      blobs: &blobs,
      univ_count: p.constant.univs.len(),
      share_count: p.constant.sharing.len(),
      share_offset: offsets
        .get(&p.parent)
        .copied()
        .unwrap_or(program.sharing.len()),
    };
    if offsets.insert(p.parent.clone(), tables.share_offset).is_none() {
      for e in &p.constant.sharing {
        program.sharing.push(tables.remap(profile.limits.depth, e)?);
      }
    }
    let i = program.declarations.len();
    program.declarations.push(Declaration {
      typ: tables.remap(profile.limits.depth, &p.declaration.typ)?,
      body: p
        .declaration
        .body
        .as_ref()
        .map(|e| tables.remap(profile.limits.depth, e))
        .transpose()?,
      kind: p.declaration.kind,
    });
    for e in &p.auxiliary {
      program.auxiliary.push((i, tables.remap(profile.limits.depth, e)?));
    }
  }
  program.groups = groups
    .iter()
    .map(|g| {
      g.iter().map(|a| index(&indices, a).and_then(native_index)).collect()
    })
    .collect::<Result<_, _>>()?;
  let resolve = |list: &[Address]| {
    list.iter().map(|a| index(&indices, a)).collect::<Result<Vec<_>, String>>()
  };
  let assumptions = resolve(&profile.assumptions)?;
  let shareable = resolve(&profile.shareable_types)?;
  let choices = resolve(&profile.choices)?;
  let literal_type = |a: &Address| -> Result<Term, String> {
    let i = index(&indices, a)?;
    if kinds.get(native_index(i)?) != Some(&DeclKind::TypeConstructor) {
      return Err(
        "resource adapter: literal type must be a checked nominal type".into(),
      );
    }
    Ok(Expr::reference(i, vec![]))
  };
  program.nat_type = profile.nat_type.as_ref().map(literal_type).transpose()?;
  program.string_type =
    profile.string_type.as_ref().map(literal_type).transpose()?;
  program.shareable_types = shareable.clone();
  program.choices = choices.clone();
  for (typ, ctor, count) in field_specs {
    if let Ok(derived) = fields(
      &program,
      profile.limits,
      index(&indices, &typ)?,
      index(&indices, &ctor)?,
      count,
    ) {
      program.fields.extend(derived);
    }
  }
  Ok(AddressedProgram {
    program,
    addresses,
    profile_address,
    policy: Policy {
      assumptions: assumptions
        .into_iter()
        .map(native_index)
        .collect::<Result<_, _>>()?,
      shareable_types: shareable
        .into_iter()
        .map(native_index)
        .collect::<Result<_, _>>()?,
      choices: choices
        .into_iter()
        .map(native_index)
        .collect::<Result<_, _>>()?,
    },
  })
}

/// Resource-only admission; the combined validator also checks erased typing.
pub fn check_resources(
  env: &Env,
  profile: &Profile,
) -> Result<AddressedProgram, String> {
  let resolved = prepare(env, profile)?;
  admit_program(&resolved.program, &resolved.policy, profile.limits).map_err(
    |error| {
      format!(
        "resource admission {:?}: {:?}",
        error.declaration.and_then(|i| resolved.addresses.get(i)),
        error.error
      )
    },
  )?;
  Ok(resolved)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::constant::{Axiom, Constructor, DefKind, Inductive, RecursorRule};
  use crate::univ::Univ;

  fn store(env: &Env, c: Constant) -> Address {
    let addr = c.commit().0;
    env.store_const(addr.clone(), c);
    addr
  }
  fn unit_block() -> Constant {
    Constant::with_tables(
      ConstantInfo::Muts(vec![MutConst::Indc(Inductive {
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        typ: Expr::sort(0),
        ctors: vec![Constructor {
          is_unsafe: false,
          lvls: 0,
          cidx: 0,
          params: 0,
          fields: 0,
          typ: Expr::rec(0, vec![]),
        }],
      })]),
      vec![],
      vec![],
      vec![Univ::zero()],
    )
  }
  fn unit_env() -> (Env, Address) {
    let env = Env::new();
    let block = store(&env, unit_block());
    let typ = store(&env, indc_proj_constant(0, block.clone()));
    store(&env, ctor_proj_constant(0, 0, block));
    (env, typ)
  }
  fn linear_local() -> BinderContract {
    BinderContract { uses: Uses::Linear, value: ValueContract::local_shared() }
  }
  fn identity(
    unit: &Address,
    input: BinderContract,
    result: ValueContract,
  ) -> Constant {
    Constant::with_tables(
      ConstantInfo::Defn(Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        lvls: 0,
        typ: Expr::all_contract(
          input,
          result,
          Expr::reference(0, vec![]),
          Expr::reference(0, vec![]),
        ),
        value: Expr::lam_contract(
          input,
          Expr::reference(0, vec![]),
          Expr::share(0),
        ),
      }),
      vec![Expr::var(0)],
      vec![unit.clone()],
      vec![],
    )
  }
  fn profile(unit: &Address) -> Profile {
    Profile {
      nat_type: Some(unit.clone()),
      shareable_types: vec![unit.clone()],
      ..Default::default()
    }
  }

  #[test]
  fn interfaces_profiles_and_integrity() {
    let (env, unit) = unit_env();
    let p = profile(&unit);
    let id_const =
      identity(&unit, linear_local(), ValueContract::local_shared());
    let id = store(&env, id_const.clone());
    let prepared = check_resources(&env, &p).unwrap();
    assert_eq!(prepared.program.declarations.len(), 3);
    assert_eq!(prepared.program.groups.len(), 1);
    assert!(
      prepare(&env, &Profile { nat_type: Some(id.clone()), ..p.clone() })
        .is_err()
    );
    assert!(
      Profile {
        shareable_types: vec![unit.clone(), unit.clone()],
        ..p.clone()
      }
      .address()
      .is_err()
    );
    assert!(
      Profile { choices: vec![id.clone()], ..p.clone() }.address().is_err()
    );
    let (bad_escape, _) = unit_env();
    store(
      &bad_escape,
      identity(&unit, linear_local(), ValueContract::shared()),
    );
    assert!(check_resources(&bad_escape, &p).is_err());
    let missing = Env::new();
    store(&missing, id_const.clone());
    assert!(prepare(&missing, &p).is_err());
    let bad_hash = env.clone();
    bad_hash.store_const(Address::hash(&[9]), id_const.clone());
    assert!(prepare(&bad_hash, &p).is_err());
    let (trailing, _) = unit_env();
    let mut raw = id_const.commit().1;
    raw.push(0);
    trailing.store_const_lazy(Address::hash(&raw), raw.into());
    assert!(prepare(&trailing, &p).is_err());
    let (orphan, _) = unit_env();
    store(&orphan, indc_proj_constant(99, unit_block().commit().0));
    assert!(prepare(&orphan, &p).is_err());
    let (missing_ctor, _) = unit_env();
    missing_ctor
      .consts
      .remove(&ctor_proj_constant(0, 0, unit_block().commit().0).commit().0);
    assert!(prepare(&missing_ctor, &p).is_err());
    let (extra_tables, _) = unit_env();
    let mut wrapper = indc_proj_constant(0, unit_block().commit().0);
    wrapper.univs.push(Univ::zero());
    store(&extra_tables, wrapper);
    assert!(prepare(&extra_tables, &p).is_err());
  }

  #[test]
  fn explicit_assumptions_and_rule_dependencies() {
    let (env, unit) = unit_env();
    let mut p = profile(&unit);
    let external = Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: 0,
        typ: Expr::all_contract(
          linear_local(),
          ValueContract::shared(),
          Expr::reference(0, vec![]),
          Expr::reference(0, vec![]),
        ),
      }),
      vec![],
      vec![unit.clone()],
      vec![],
    );
    let external = store(&env, external);
    assert!(check_resources(&env, &p).is_err());
    p.assumptions.push(external);
    check_resources(&env, &p).unwrap();
    let (rec_env, _) = unit_env();
    let rec = Constant::with_tables(
      ConstantInfo::Recr(Recursor {
        k: false,
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        motives: 0,
        minors: 0,
        typ: Expr::reference(0, vec![]),
        rules: vec![RecursorRule {
          fields: 0,
          rhs: Expr::lam_contract(
            linear_local(),
            Expr::reference(0, vec![]),
            Expr::var(0),
          ),
        }],
      }),
      vec![],
      vec![unit.clone()],
      vec![],
    );
    let rec = store(&rec_env, rec);
    assert!(check_resources(&rec_env, &profile(&unit)).is_err());
    check_resources(
      &rec_env,
      &Profile { assumptions: vec![rec], ..profile(&unit) },
    )
    .unwrap();
  }

  #[test]
  fn global_blob_identities_and_integrity() {
    let (env, unit) = unit_env();
    for byte in [0, 1] {
      let blob = env.store_blob(vec![byte]);
      store(
        &env,
        Constant::with_tables(
          ConstantInfo::Defn(Definition {
            kind: DefKind::Definition,
            safety: DefinitionSafety::Safe,
            lvls: 0,
            typ: Expr::reference(0, vec![]),
            value: Expr::nat(1),
          }),
          vec![],
          vec![unit.clone(), blob],
          vec![],
        ),
      );
    }
    let resolved = prepare(&env, &profile(&unit)).unwrap();
    let bodies: Vec<_> = resolved
      .program
      .declarations
      .iter()
      .filter_map(|d| d.body.as_ref())
      .collect();
    assert_eq!(bodies.len(), 2);
    assert_ne!(bodies[0], bodies[1]);
    env.blobs.insert(Address::hash(&[9]), vec![0]);
    assert!(prepare(&env, &profile(&unit)).is_err());
  }

  #[test]
  fn mutual_recursive_interfaces() {
    let (env, unit) = unit_env();
    let input =
      BinderContract { uses: Uses::Linear, value: ValueContract::unique() };
    let typ = Expr::all_contract(
      input,
      ValueContract::unique(),
      Expr::reference(0, vec![]),
      Expr::reference(0, vec![]),
    );
    let members = [1, 0]
      .map(|i| {
        MutConst::Defn(Definition {
          kind: DefKind::Definition,
          safety: DefinitionSafety::Safe,
          lvls: 0,
          typ: typ.clone(),
          value: Expr::lam_contract(
            input,
            Expr::reference(0, vec![]),
            Expr::app(Expr::rec(i, vec![]), Expr::var(0)),
          ),
        })
      })
      .to_vec();
    let block = store(
      &env,
      Constant::with_tables(
        ConstantInfo::Muts(members),
        vec![],
        vec![unit.clone()],
        vec![],
      ),
    );
    store(&env, defn_proj_constant(0, block.clone()));
    store(&env, defn_proj_constant(1, block));
    let resolved = check_resources(&env, &profile(&unit)).unwrap();
    assert_eq!(resolved.program.groups.len(), 2);
  }

  #[test]
  fn fields_are_derived_from_constructor_interfaces() {
    let (env, unit) = unit_env();
    let unique =
      BinderContract { uses: Uses::Many, value: ValueContract::unique() };
    let typ = Expr::all_contract(
      unique,
      ValueContract::unique(),
      Expr::reference(0, vec![]),
      Expr::rec(0, vec![]),
    );
    let block = store(
      &env,
      Constant::with_tables(
        ConstantInfo::Muts(vec![MutConst::Indc(Inductive {
          is_unsafe: false,
          lvls: 0,
          params: 0,
          indices: 0,
          typ: Expr::sort(0),
          ctors: vec![Constructor {
            is_unsafe: false,
            lvls: 0,
            cidx: 0,
            params: 0,
            fields: 1,
            typ,
          }],
        })]),
        vec![],
        vec![unit.clone()],
        vec![Univ::zero()],
      ),
    );
    let nominal = store(&env, indc_proj_constant(0, block.clone()));
    store(&env, ctor_proj_constant(0, 0, block));
    let resolved = check_resources(&env, &profile(&unit)).unwrap();
    assert_eq!(resolved.program.fields.len(), 1);
    let field = &resolved.program.fields[0];
    assert_eq!(
      resolved.addresses[usize::try_from(field.type_ref).unwrap()],
      nominal
    );
    assert_eq!(field.contract, ValueContract::unique());
  }

  #[test]
  fn canonical_cross_language_fixtures() {
    let (_, unit) = unit_env();
    let cases = [
      ("unit", unit_block()),
      (
        "identity",
        identity(&unit, linear_local(), ValueContract::local_shared()),
      ),
      (
        "identity_unique",
        identity(
          &unit,
          BinderContract { uses: Uses::Linear, value: ValueContract::unique() },
          ValueContract::unique(),
        ),
      ),
    ];
    let fixture =
      include_str!("../../../../Tests/Fixtures/ixon-v3/addressed.tsv");
    for (name, constant) in cases {
      let (address, bytes) = constant.commit();
      let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
      let line = format!("{name}\t{}\t{hex}", address.hex());
      assert!(fixture.lines().any(|s| s == line), "fixture mismatch: {line}");
    }
    let p = profile(&unit);
    let hex: String = p.bytes().iter().map(|b| format!("{b:02x}")).collect();
    let line = format!("profile\t{}\t{hex}", p.address().unwrap().hex());
    assert!(
      fixture.lines().any(|s| s == line),
      "profile fixture mismatch: {line}"
    );
    let bytes = p.bytes();
    assert_eq!(Profile::from_bytes(&bytes).unwrap(), p);
    for length in 0..bytes.len() {
      assert!(Profile::from_bytes(&bytes[..length]).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(Profile::from_bytes(&trailing).is_err());
    let mut wrong_validator = bytes;
    wrong_validator[0] ^= 1;
    assert!(Profile::from_bytes(&wrong_validator).is_err());
  }
}
