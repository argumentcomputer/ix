//! Combined resource and erased-type validation for addressed Ixon.
//! Kernel typechecking on its own makes no resource promise.

use crate::anon_work::build_anon_work;
#[cfg(test)]
use crate::env::KEnv;
#[cfg(test)]
use crate::id::KId;
#[cfg(test)]
use crate::mode::Anon;
use crate::primitive::PrimAddrs;
#[cfg(test)]
use crate::tc::TypeChecker;
use ixon::env::Env;
use ixon::resource::addressed::{AddressedProgram, Profile, check_resources};

/// Minimal built-in profile, restricted to interfaces present in the closure.
///
/// Its shareable types (Nat, Bool, String) make usage contracts cross call
/// and closure boundaries on those types: the profile relies on the named
/// assumption that the linearity of a shareable immediate has no run-time
/// meaning (docs/resource-checking.md, "Named assumptions"). A profile source
/// with `literals` instead of `standard` (profiles/lean-core-strict.profile)
/// keeps the literal types without any shareable type.
pub fn standard_profile(env: &Env) -> Profile {
  let p = PrimAddrs::new();
  let mut shareable_types: Vec<_> =
    [p.nat.clone(), p.bool_type.clone(), p.string.clone()]
      .into_iter()
      .filter(|a| env.consts.contains_key(a))
      .collect();
  shareable_types.sort_unstable();
  Profile {
    nat_type: env.consts.contains_key(&p.nat).then_some(p.nat),
    string_type: env.consts.contains_key(&p.string).then_some(p.string),
    shareable_types,
    ..Default::default()
  }
}

pub fn check_literal_profile(profile: &Profile) -> Result<(), String> {
  let p = PrimAddrs::new();
  for (selected, actual) in [
    (&profile.nat_type, &p.nat),
    (&profile.string_type, &p.string),
    (&profile.eq_type, &p.eq),
  ] {
    if selected.as_ref().is_some_and(|selected| selected != actual) {
      return Err("resource validator: literal type differs from the kernel primitive identity".into());
    }
  }
  Ok(())
}

/// One packed input/result contract byte from a token in source prefix
/// syntax: `INPUT[:RESULT]`, where `INPUT` uses the binder atoms `0`, `1`,
/// `&`, `!`, `~` and `RESULT` the atoms `!`, `~`; `_` is the default.
fn contract_byte(token: &str) -> Option<u8> {
  use ixon::contract::{
    BinderContract, Locality, ValueContract, pack_all_contract,
  };
  use ixon::expr::{Owned, Uses};
  let (input, result) = token.split_once(':').unwrap_or((token, "_"));
  let value = |atoms: &str, allow_uses: bool| {
    let mut uses = None;
    let mut owned = Owned::Shared;
    let mut locality = Locality::Unrestricted;
    if atoms != "_" {
      if atoms.is_empty() {
        return None;
      }
      for c in atoms.chars() {
        match c {
          '0' | '1' | '&' if allow_uses && uses.is_none() => {
            uses = Some(match c {
              '0' => Uses::Erased,
              '1' => Uses::Linear,
              _ => Uses::Affine,
            });
          },
          '!' if owned == Owned::Shared => owned = Owned::Unique,
          '~' if locality == Locality::Unrestricted => {
            locality = Locality::Local;
          },
          _ => return None,
        }
      }
    }
    Some((uses.unwrap_or(Uses::Many), ValueContract { owned, locality }))
  };
  let (uses, input) = value(input, true)?;
  let (_, result) = value(result, false)?;
  Some(pack_all_contract(BinderContract { uses, value: input }, result))
}

/// Build a profile from its source text (`ix compile --profile FILE`). Each
/// line is a directive; `#` starts a comment:
///
/// - `standard`: the standard profile's literal and shareable types;
/// - `literals`: the standard profile's literal types (Nat, String) only, with
///   no shareable type, so usage contracts never cross (the strict profile);
/// - `shareable NAME`, `assume NAME`, `choice NAME` (a choice is also an
///   assumption);
/// - `interface NAME C…`: an admitted interface, one contract token per
///   leading arrow (see `contract_byte`); also an assumption;
/// - `cases`: recursor case splits, bound case definitions and
///   beta-redexes;
/// - `case NAME`: a case definition (`casesOn`, a matcher) whose
///   alternatives are taken by need (`ix compile` generates these);
/// - `equation NAME THEOREM`: check `NAME` through the unfolding equation
///   `THEOREM` (`∀ xs, NAME xs = rhs`), which the consumer runs;
/// - `limits DEPTH STEPS`;
/// - `crossing plain`: usage crossing on plain data (the plain profile): a
///   `1`/`&` contract on a value of a plain-data type is not enforced;
/// - `linear NAME`: opt the type `NAME` out of usage crossing (a capability
///   token whose single use the consumer relies on);
/// - `generated`: the end of the written source. `case` and `equation` are
///   generated directives: they are accepted only after this line, which
///   `ix compile` appends to a written profile before the lines it
///   generates, and nothing else may follow it. A second `generated` line
///   is rejected, so a written file cannot open the section itself without
///   also failing on the compiler's own marker.
///
/// Lines are separated by `\n` (one trailing `\r` is dropped), and words by
/// spaces and tabs. In the written source (before `generated`) the text of a
/// directive (before `#`) may contain only printable ASCII and tabs: any
/// other character (a vertical tab, a form feed, a no-break space, any other
/// control or non-ASCII character) is rejected, so this tokenization agrees
/// with the Lean side's (`Ix.Compile.ResourceProfile.checkWritten`, second
/// review R2-4). Generated lines may name non-ASCII constants but contain no
/// whitespace or control character other than spaces and tabs.
///
/// `resolve` maps a dotted name to the address it compiled to. Entries whose
/// constant is not in the closure are omitted, as the standard profile omits
/// absent primitives; the profile commits to addresses only.
pub fn profile_from_source(
  text: &str,
  env: &Env,
  resolve: &dyn Fn(&str) -> Option<ix_common::address::Address>,
) -> Result<Profile, String> {
  use std::collections::{BTreeMap, BTreeSet};
  let mut assumptions = BTreeSet::new();
  let mut shareable = BTreeSet::new();
  let mut scalar = BTreeSet::new();
  let mut choices = BTreeSet::new();
  let mut interfaces = BTreeMap::new();
  let mut equations = BTreeMap::new();
  let mut case_definitions = BTreeSet::new();
  let mut linear_types = BTreeSet::new();
  let mut profile = Profile::default();
  let mut generated = false;
  for (n, raw) in text.split('\n').enumerate() {
    let raw = raw.strip_suffix('\r').unwrap_or(raw);
    let error = |message: &str| {
      format!("resource profile source, line {}: {message}", n + 1)
    };
    let line = raw.split('#').next().unwrap_or("");
    // The written source: printable ASCII and tabs only. The generated lines
    // name Lean constants, which may be non-ASCII (`x₁`): there only
    // whitespace and control characters other than spaces and tabs are
    // refused.
    let refused = |c: &char| {
      if generated {
        *c != ' ' && *c != '\t' && (c.is_whitespace() || c.is_control())
      } else {
        *c != '\t' && !(' '..='~').contains(c)
      }
    };
    if let Some(c) = line.chars().find(refused) {
      return Err(error(&format!(
        "character U+{:04X} in a directive: only printable ASCII, spaces and tabs are allowed",
        c as u32
      )));
    }
    let words: Vec<&str> =
      line.split([' ', '\t']).filter(|word| !word.is_empty()).collect();
    if words.is_empty() {
      continue;
    }
    match (words[0], generated) {
      ("generated", true) => {
        return Err(error("a second `generated` line"));
      },
      ("generated", false) if words.len() == 1 => {
        generated = true;
        continue;
      },
      ("case" | "equation", false) => {
        return Err(error(
          "`case` and `equation` directives are generated by `ix compile`, not written in a profile",
        ));
      },
      ("case" | "equation", true) => {},
      (_, true) => {
        return Err(error("only generated directives may follow `generated`"));
      },
      _ => {},
    }
    let present = |name: &str| {
      resolve(name).filter(|address| env.consts.contains_key(address))
    };
    match (words[0], words.len()) {
      ("standard", 1) => {
        let standard = standard_profile(env);
        profile.nat_type = standard.nat_type;
        profile.string_type = standard.string_type;
        shareable.extend(standard.shareable_types);
      },
      ("literals", 1) => {
        let standard = standard_profile(env);
        profile.nat_type = standard.nat_type;
        profile.string_type = standard.string_type;
      },
      ("shareable", 2) => shareable.extend(present(words[1])),
      ("scalar", 2) => scalar.extend(present(words[1])),
      ("crossing", 2) if words[1] == "plain" => profile.crossing = true,
      ("linear", 2) => linear_types.extend(present(words[1])),
      ("assume", 2) => assumptions.extend(present(words[1])),
      ("choice", 2) => {
        if let Some(address) = present(words[1]) {
          assumptions.insert(address.clone());
          choices.insert(address);
        }
      },
      ("interface", 3..) => {
        let mask = words[2..]
          .iter()
          .map(|token| contract_byte(token))
          .collect::<Option<Vec<_>>>()
          .ok_or_else(|| error("invalid contract token"))?;
        if let Some(address) = present(words[1]) {
          assumptions.insert(address.clone());
          if interfaces.insert(address, mask).is_some() {
            return Err(error("duplicate interface"));
          }
        }
      },
      ("cases", 1) => profile.cases = true,
      ("case", 2) => case_definitions.extend(present(words[1])),
      ("equation", 3) => {
        if let (Some(definition), Some(equation)) =
          (present(words[1]), present(words[2]))
          && equations.insert(definition, equation).is_some()
        {
          return Err(error("duplicate equation"));
        }
      },
      ("limits", 3) => {
        let parse = |word: &str| {
          word.parse::<usize>().map_err(|_error| error("invalid limit"))
        };
        profile.limits.depth = parse(words[1])?;
        profile.limits.steps = parse(words[2])?;
      },
      _ => return Err(error("unknown directive")),
    }
  }
  profile.assumptions = assumptions.into_iter().collect();
  profile.shareable_types = shareable.into_iter().collect();
  profile.scalar_types = scalar.into_iter().collect();
  profile.choices = choices.into_iter().collect();
  profile.interfaces = interfaces.into_iter().collect();
  profile.case_definitions = case_definitions.into_iter().collect();
  profile.linear_types = linear_types.into_iter().collect();
  if !equations.is_empty() {
    let eq = PrimAddrs::new().eq;
    if !env.consts.contains_key(&eq) {
      return Err(
        "resource profile source: equations need Eq in the closure".into(),
      );
    }
    profile.eq_type = Some(eq);
    profile.equations = equations.into_iter().collect();
  }
  profile.validate()?;
  Ok(profile)
}

/// Validate both resources and erased types of the same canonical addressed
/// closure. A caller advertising a resource claim must bind the returned
/// profile address and this validator's identity to its subject.
pub fn validate(
  env: &Env,
  profile: &Profile,
) -> Result<AddressedProgram, String> {
  check_literal_profile(profile)?;
  let resolved = check_resources(env, profile)?;
  let work = build_anon_work(env)?;
  let mut checker = crate::ixon_checker::IxonChecker::new(env);
  for item in work {
    checker.check_const(item.primary()).map_err(|error| {
      format!(
        "resource validator: erased typing failed at {}: {error:?}",
        item.primary().hex()
      )
    })?;
    // Retain structural declarations but keep reduction caches local to one
    // work item, as in the existing anonymous driver.
    checker.clear_reduction_caches();
  }
  Ok(resolved)
}

pub fn check_claim(
  env: &Env,
  profile: &Profile,
  claim: &ixon::proof::Claim,
) -> Result<AddressedProgram, String> {
  let ixon::proof::Claim::Resource { root, profile: expected_profile } = claim
  else {
    return Err("resource validator: claim uses a different validator".into());
  };
  let leaves: Vec<_> =
    env.consts.iter().map(|entry| entry.key().clone()).collect();
  if ixon::merkle::merkle_root_canonical(&leaves).as_ref() != Some(root) {
    return Err("resource validator: claim subject differs from the complete constant set".into());
  }
  if &profile.address()? != expected_profile {
    return Err(
      "resource validator: claim profile differs from the supplied policy"
        .into(),
    );
  }
  validate(env, profile)
}

pub fn make_claim(
  env: &Env,
  profile: &Profile,
) -> Result<ixon::proof::Claim, String> {
  let leaves: Vec<_> =
    env.consts.iter().map(|entry| entry.key().clone()).collect();
  let root = ixon::merkle::merkle_root_canonical(&leaves)
    .ok_or("resource validator: empty claim subject")?;
  let claim =
    ixon::proof::Claim::Resource { root, profile: profile.address()? };
  check_claim(env, profile, &claim)?;
  Ok(claim)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::address::Address;
  use ix_common::env::DefinitionSafety;
  use ixon::constant::{
    Constant, ConstantInfo, Constructor, DefKind, Definition, Inductive,
    MutConst, ctor_proj_constant, indc_proj_constant,
  };
  use ixon::contract::{BinderContract, ValueContract};
  use ixon::expr::{Expr, Uses};
  use ixon::univ::Univ;

  fn store(env: &Env, c: Constant) -> Address {
    let a = c.commit().0;
    env.store_const(a.clone(), c);
    a
  }

  #[test]
  fn cross_language_consumer_handoff() {
    let profile = Profile::from_bytes(include_bytes!(
      "../../../Tests/Fixtures/ixon-v4/handoff/profile.bin"
    ))
    .unwrap();
    let claim = ixon::proof::Claim::from_bytes(include_bytes!(
      "../../../Tests/Fixtures/ixon-v4/handoff/accepted.claim"
    ))
    .unwrap();
    let accepted = Env::get(
      &mut include_bytes!(
        "../../../Tests/Fixtures/ixon-v4/handoff/accepted.ixe"
      )
      .as_slice(),
    )
    .unwrap();
    let rejected = Env::get(
      &mut include_bytes!(
        "../../../Tests/Fixtures/ixon-v4/handoff/rejected-local-escape.ixe"
      )
      .as_slice(),
    )
    .unwrap();
    check_claim(&accepted, &profile, &claim).unwrap();
    assert!(check_claim(&rejected, &profile, &claim).is_err());
    assert!(validate(&rejected, &profile).is_err());
    // The counterexample is well typed after erasure; its rejection is
    // specifically a resource obligation, not a wire or Lean typing failure.
    let mut kernel = KEnv::<Anon>::new();
    for item in build_anon_work(&rejected).unwrap() {
      let id = KId { addr: item.primary().clone(), name: () };
      TypeChecker::new_with_lazy_anon(&mut kernel, &rejected)
        .check_const(&id)
        .unwrap();
    }
  }

  fn base() -> (Env, Address) {
    let env = Env::new();
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
            fields: 0,
            typ: Expr::rec(0, vec![]),
          }],
        })]),
        vec![],
        vec![],
        vec![Univ::zero()],
      ),
    );
    let typ = store(&env, indc_proj_constant(0, block.clone()));
    store(&env, ctor_proj_constant(0, 0, block));
    (env, typ)
  }
  #[test]
  fn combines_independent_resource_and_type_checks() {
    let (env, typ) = base();
    let c = BinderContract {
      uses: Uses::Linear,
      value: ValueContract::local_shared(),
    };
    store(
      &env,
      Constant::with_tables(
        ConstantInfo::Defn(Definition {
          kind: DefKind::Definition,
          safety: DefinitionSafety::Safe,
          lvls: 0,
          typ: Expr::all_contract(
            c,
            ValueContract::local_shared(),
            Expr::reference(0, vec![]),
            Expr::reference(0, vec![]),
          ),
          value: Expr::lam_contract(
            c,
            Expr::reference(0, vec![]),
            Expr::var(0),
          ),
        }),
        vec![],
        vec![typ.clone()],
        vec![],
      ),
    );
    validate(&env, &Profile::default()).unwrap();
    let claim = make_claim(&env, &Profile::default()).unwrap();
    assert!(check_claim(&env, &Profile::default(), &claim).is_ok());
    let mut changed_profile = Profile::default();
    changed_profile.limits.steps += 1;
    assert!(check_claim(&env, &changed_profile, &claim).is_err());
    assert!(
      check_claim(
        &env,
        &Profile::default(),
        &ixon::proof::Claim::CheckEnv {
          root: Address::hash(b"subject"),
          assumptions: None
        }
      )
      .is_err()
    );
    assert!(
      validate(&env, &Profile { nat_type: Some(typ), ..Default::default() })
        .is_err()
    );
    let malformed = env.clone();
    store(
      &malformed,
      Constant::with_tables(
        ConstantInfo::Defn(Definition {
          kind: DefKind::Definition,
          safety: DefinitionSafety::Safe,
          lvls: 0,
          typ: Expr::sort(0),
          value: Expr::var(0),
        }),
        vec![],
        vec![],
        vec![Univ::zero()],
      ),
    );
    // This ordinary component has no resource annotation. It still must typecheck.
    assert!(check_resources(&malformed, &Profile::default()).is_ok());
    assert!(validate(&malformed, &Profile::default()).is_err());
  }

  #[test]
  fn profile_sources_resolve_names_in_the_closure() {
    use ixon::contract::{
      BinderContract, Locality, ValueContract, pack_all_contract,
    };
    use ixon::expr::{Owned, Uses};
    let (env, unit) = base();
    let absent = Address::hash(b"absent");
    let resolve = |name: &str| match name {
      "Unit" => Some(unit.clone()),
      "Absent" => Some(absent.clone()),
      _ => None,
    };
    let source = "# comment\nchoice Unit\ninterface Unit _ ~:!\ncases\n\
      shareable Absent # outside the closure\nassume Missing\nlimits 64 1000\r\n\
      generated\ncase Unit\ncase Missing\n";
    let profile = profile_from_source(source, &env, &resolve).unwrap();
    assert_eq!(profile.assumptions, vec![unit.clone()]);
    assert_eq!(profile.choices, vec![unit.clone()]);
    assert!(profile.shareable_types.is_empty());
    assert!(profile.cases);
    assert_eq!(profile.case_definitions, vec![unit.clone()]);
    let local =
      ValueContract { owned: Owned::Shared, locality: Locality::Local };
    assert_eq!(
      profile.interfaces,
      vec![(
        unit.clone(),
        vec![
          pack_all_contract(BinderContract::default(), ValueContract::shared()),
          pack_all_contract(
            BinderContract { uses: Uses::Many, value: local },
            ValueContract::unique()
          ),
        ]
      )]
    );
    assert_eq!((profile.limits.depth, profile.limits.steps), (64, 1000));
    // `literals` selects the literal types without any shareable type (the
    // strict profile), unlike `standard`.
    let literals = profile_from_source("literals\n", &env, &resolve).unwrap();
    let standard = standard_profile(&env);
    assert!(literals.shareable_types.is_empty());
    assert_eq!(
      (&literals.nat_type, &literals.string_type),
      (&standard.nat_type, &standard.string_type)
    );
    assert!(profile_from_source("literals Unit", &env, &resolve).is_err());
    // `crossing plain` selects plain-data crossing; `linear NAME` opts a
    // type out of it (the plain profile, setting S6).
    let plain = profile_from_source(
      "literals\ncrossing plain\nlinear Unit\nlinear Absent\n",
      &env,
      &resolve,
    )
    .unwrap();
    assert!(plain.crossing);
    assert_eq!(plain.linear_types, vec![unit.clone()]);
    for bad in ["crossing", "crossing full", "linear", "linear Unit Unit"] {
      assert!(profile_from_source(bad, &env, &resolve).is_err(), "{bad}");
    }
    let scalar = profile_from_source(
      "scalar Unit\nscalar Unit\nscalar Absent\n",
      &env,
      &resolve,
    )
    .unwrap();
    assert_eq!(scalar.scalar_types, vec![unit.clone()]);
    assert!(scalar.shareable_types.is_empty() && !scalar.crossing);
    for bad in ["scalar", "scalar Unit Unit", "generated\nscalar Unit"] {
      assert!(profile_from_source(bad, &env, &resolve).is_err(), "{bad}");
    }
    for source in [
      include_str!("../../../profiles/lean-core.profile"),
      include_str!("../../../profiles/lean-core-strict.profile"),
      include_str!("../../../profiles/lean-core-plain.profile"),
    ] {
      assert!(
        profile_from_source(source, &env, &resolve)
          .unwrap()
          .scalar_types
          .is_empty()
      );
    }
    // Equations need Eq in the closure (not in this one).
    for bad in [
      "frobnicate",
      "interface Unit ?",
      "limits 0 0",
      "choice",
      "generated\nequation Unit Unit",
      // Case definitions need case behavior.
      "generated\ncase Unit",
      // Generated directives only after `generated`, which ends the
      // written source (second review R2-4).
      "cases\ncase Unit",
      "cases\nequation Unit Unit",
      "cases\ngenerated\ngenerated\ncase Unit",
      "cases\ngenerated\ncase Unit\nassume Unit",
      "cases\ngenerated extra\ncase Unit",
      // Only printable ASCII, spaces and tabs in a directive: a vertical
      // tab, a form feed or a no-break space before a generated directive
      // must not hide it from either tokenizer.
      "cases\n\x0bcase Unit",
      "cases\n\x0ccase Unit",
      "cases\n\u{a0}case Unit",
      "cases\nassume\u{a0}Unit",
      "cases\rassume Unit",
      "cases\ngenerated\n\u{a0}case Unit",
      "cases\ngenerated\ncase\x0bUnit",
    ] {
      assert!(profile_from_source(bad, &env, &resolve).is_err(), "{bad}");
    }
    // Generated lines may name non-ASCII constants.
    assert!(
      profile_from_source("cases\ngenerated\ncase x\u{2081}\n", &env, &resolve)
        .is_ok()
    );
    // Comments may contain any character.
    assert!(
      profile_from_source("cases # a no-break\u{a0}space\n", &env, &resolve)
        .is_ok()
    );
  }
}
