//! Conversion from env types to kernel types.
//!
//! Converts `env::Expr`/`Level`/`ConstantInfo` (Name-based) to
//! `KExpr`/`KLevel`/`KConstantInfo` (Address-based with positional params).

use rustc_hash::FxHashMap;

use crate::ix::address::Address;
use crate::ix::env::{self, ConstantInfo, Name};

use super::types::{MetaMode, *};

/// Read-only conversion context (like Lean's ConvertEnv).
struct ConvertCtx<'a> {
  /// Map from level param name hash to positional index.
  level_param_map: FxHashMap<blake3::Hash, usize>,
  /// Map from constant name hash to address.
  name_to_addr: &'a FxHashMap<blake3::Hash, Address>,
}

/// Expression cache: expr blake3 hash → converted KExpr (like Lean's ConvertState).
type ExprCache<M> = FxHashMap<blake3::Hash, KExpr<M>>;

/// Convert a `env::Level` to a `KLevel`.
fn convert_level<M: MetaMode>(
  level: &env::Level,
  ctx: &ConvertCtx<'_>,
) -> Result<KLevel<M>, String> {
  match level.as_data() {
    env::LevelData::Zero(_) => Ok(KLevel::zero()),
    env::LevelData::Succ(inner, _) => {
      Ok(KLevel::succ(convert_level(inner, ctx)?))
    }
    env::LevelData::Max(a, b, _) => {
      Ok(KLevel::max(convert_level(a, ctx)?, convert_level(b, ctx)?))
    }
    env::LevelData::Imax(a, b, _) => {
      Ok(KLevel::imax(convert_level(a, ctx)?, convert_level(b, ctx)?))
    }
    env::LevelData::Param(name, _) => {
      let hash = *name.get_hash();
      let idx = ctx.level_param_map.get(&hash).copied().ok_or_else(|| {
        format!("unknown level parameter '{name}' (hash not in level_param_map)")
      })?;
      Ok(KLevel::param(idx, M::mk_field(name.clone())))
    }
    env::LevelData::Mvar(name, _) => {
      Err(format!("unexpected metavariable level '{name}' in kernel expression"))
    }
  }
}

/// Convert a `env::Expr` to a `KExpr`, with caching.
fn convert_expr<M: MetaMode>(
  expr: &env::Expr,
  ctx: &ConvertCtx<'_>,
  cache: &mut ExprCache<M>,
) -> Result<KExpr<M>, String> {
  // Skip cache for bvars (trivial, no recursion)
  if let env::ExprData::Bvar(n, _) = expr.as_data() {
    let idx = n.to_u64().unwrap_or(0) as usize;
    return Ok(KExpr::bvar(idx, M::Field::<Name>::default()));
  }

  // Check cache
  let hash = *expr.get_hash();
  if let Some(cached) = cache.get(&hash) {
    return Ok(cached.clone()); // Rc clone = O(1)
  }

  let result = match expr.as_data() {
    env::ExprData::Bvar(_, _) => unreachable!(),
    env::ExprData::Sort(level, _) => {
      KExpr::sort(convert_level(level, ctx)?)
    }
    env::ExprData::Const(name, levels, _) => {
      let h = *name.get_hash();
      let addr = ctx
        .name_to_addr
        .get(&h)
        .cloned()
        .unwrap_or_else(|| Address::from_blake3_hash(h));
      let k_levels: Vec<_> =
        levels.iter().map(|l| convert_level(l, ctx)).collect::<Result<_, _>>()?;
      KExpr::cnst(MetaId::new(addr, M::mk_field(name.clone())), k_levels)
    }
    env::ExprData::App(f, a, _) => {
      KExpr::app(
        convert_expr(f, ctx, cache)?,
        convert_expr(a, ctx, cache)?,
      )
    }
    env::ExprData::Lam(name, ty, body, bi, _) => KExpr::lam(
      convert_expr(ty, ctx, cache)?,
      convert_expr(body, ctx, cache)?,
      M::mk_field(name.clone()),
      M::mk_field(bi.clone()),
    ),
    env::ExprData::ForallE(name, ty, body, bi, _) => {
      KExpr::forall_e(
        convert_expr(ty, ctx, cache)?,
        convert_expr(body, ctx, cache)?,
        M::mk_field(name.clone()),
        M::mk_field(bi.clone()),
      )
    }
    env::ExprData::LetE(name, ty, val, body, nd, _) => KExpr::let_e_nd(
      convert_expr(ty, ctx, cache)?,
      convert_expr(val, ctx, cache)?,
      convert_expr(body, ctx, cache)?,
      M::mk_field(name.clone()),
      *nd,
    ),
    env::ExprData::Lit(l, _) => KExpr::lit(l.clone()),
    env::ExprData::Proj(name, idx, strct, _) => {
      let h = *name.get_hash();
      let addr = ctx
        .name_to_addr
        .get(&h)
        .cloned()
        .unwrap_or_else(|| Address::from_blake3_hash(h));
      let idx = idx.to_u64().unwrap_or(0) as usize;
      KExpr::proj(MetaId::new(addr, M::mk_field(name.clone())), idx, convert_expr(strct, ctx, cache)?)
    }
    env::ExprData::Fvar(_, _) | env::ExprData::Mvar(_, _) => {
      // Fvars and Mvars shouldn't appear in kernel expressions
      KExpr::bvar(0, M::Field::<Name>::default())
    }
    env::ExprData::Mdata(kvs, inner, _) => {
      // Collect mdata layers and attach to inner expression
      let mut mdata_layers: Vec<KMData> = vec![kvs.clone()];
      let mut cur = inner;
      while let env::ExprData::Mdata(kvs2, inner2, _) = cur.as_data() {
        mdata_layers.push(kvs2.clone());
        cur = inner2;
      }
      let inner_result = convert_expr(cur, ctx, cache)?;
      let result = inner_result.add_mdata(mdata_layers);
      cache.insert(hash, result.clone());
      return Ok(result);
    }
  };

  // Insert into cache
  cache.insert(hash, result.clone());
  Ok(result)
}

/// Convert a `env::ConstantVal` to `KConstantVal`.
fn convert_constant_val<M: MetaMode>(
  cv: &env::ConstantVal,
  ctx: &ConvertCtx<'_>,
  cache: &mut ExprCache<M>,
) -> Result<KConstantVal<M>, String> {
  Ok(KConstantVal {
    num_levels: cv.level_params.len(),
    typ: convert_expr(&cv.typ, ctx, cache)?,
    name: M::mk_field(cv.name.clone()),
    level_params: M::mk_field(cv.level_params.clone()),
  })
}

/// Build a `ConvertCtx` for a constant with given level params and the
/// name→address map.
fn make_ctx<'a>(
  level_params: &[Name],
  name_to_addr: &'a FxHashMap<blake3::Hash, Address>,
) -> ConvertCtx<'a> {
  let mut level_param_map = FxHashMap::default();
  for (idx, name) in level_params.iter().enumerate() {
    level_param_map.insert(*name.get_hash(), idx);
  }
  ConvertCtx {
    level_param_map,
    name_to_addr,
  }
}

/// Resolve a Name to a MetaId using the name→address map.
fn resolve_name<M: MetaMode>(
  name: &Name,
  name_to_addr: &FxHashMap<blake3::Hash, Address>,
) -> MetaId<M> {
  let hash = *name.get_hash();
  let addr = name_to_addr
    .get(&hash)
    .cloned()
    .unwrap_or_else(|| Address::from_blake3_hash(hash));
  MetaId::new(addr, M::mk_field(name.clone()))
}

/// Convert an entire `env::Env` to a `(KEnv, Primitives, quot_init)`.
pub fn convert_env<M: MetaMode>(
  env: &env::Env,
) -> Result<(KEnv<M>, Primitives<M>, bool), String> {
  // Phase 1: Build name → address map
  let mut name_to_addr: FxHashMap<blake3::Hash, Address> =
    FxHashMap::default();
  for (name, ci) in env {
    let addr = Address::from_blake3_hash(ci.get_hash());
    name_to_addr.insert(*name.get_hash(), addr);
  }

  // Phase 2: Convert all constants
  let mut kenv: KEnv<M> = KEnv::default();
  let mut quot_init = false;

  for (name, ci) in env {
    let id: MetaId<M> = resolve_name(name, &name_to_addr);
    let level_params = ci.cnst_val().level_params.clone();
    let ctx = make_ctx(&level_params, &name_to_addr);

    // Fresh cache per constant: the cache is keyed by expr hash, but
    // level param→index mappings differ per constant, so a cached
    // subexpression from one constant would have wrong KLevel::param
    // indices when reused by another constant.
    let mut cache: ExprCache<M> = FxHashMap::default();

    let kci = match ci {
      ConstantInfo::AxiomInfo(v) => {
        KConstantInfo::Axiom(KAxiomVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          is_unsafe: v.is_unsafe,
        })
      }
      ConstantInfo::DefnInfo(v) => {
        let value_kexpr = convert_expr(&v.value, &ctx, &mut cache)?;
        KConstantInfo::Definition(KDefinitionVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          value: value_kexpr,
          hints: v.hints,
          safety: v.safety,
          lean_all: M::mk_field(v
            .all
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect()),
          // FFI path: no Ixon canonical block available.
          // Populated from Ixon conversion when checking compiled constants.
          canonical_block: vec![],
        })
      }
      ConstantInfo::ThmInfo(v) => {
        KConstantInfo::Theorem(KTheoremVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          value: convert_expr(&v.value, &ctx, &mut cache)?,
          lean_all: M::mk_field(v
            .all
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect()),
          canonical_block: vec![],
        })
      }
      ConstantInfo::OpaqueInfo(v) => {
        KConstantInfo::Opaque(KOpaqueVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          value: convert_expr(&v.value, &ctx, &mut cache)?,
          is_unsafe: v.is_unsafe,
          lean_all: M::mk_field(v
            .all
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect()),
          canonical_block: vec![],
        })
      }
      ConstantInfo::QuotInfo(v) => {
        quot_init = true;
        KConstantInfo::Quotient(KQuotVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          kind: v.kind,
        })
      }
      ConstantInfo::InductInfo(v) => {
        KConstantInfo::Inductive(KInductiveVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          num_params: v.num_params.to_u64().unwrap_or(0) as usize,
          num_indices: v.num_indices.to_u64().unwrap_or(0) as usize,
          lean_all: M::mk_field(v
            .all
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect()),
          canonical_block: vec![],
          ctors: v
            .ctors
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect(),
          num_nested: v.num_nested.to_u64().unwrap_or(0) as usize,
          is_rec: v.is_rec,
          is_unsafe: v.is_unsafe,
          is_reflexive: v.is_reflexive,
        })
      }
      ConstantInfo::CtorInfo(v) => {
        KConstantInfo::Constructor(KConstructorVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          induct: resolve_name(&v.induct, &name_to_addr),
          cidx: v.cidx.to_u64().unwrap_or(0) as usize,
          num_params: v.num_params.to_u64().unwrap_or(0) as usize,
          num_fields: v.num_fields.to_u64().unwrap_or(0) as usize,
          is_unsafe: v.is_unsafe,
        })
      }
      ConstantInfo::RecInfo(v) => {
        let rules: Result<Vec<_>, String> = v
          .rules
          .iter()
          .map(|r| Ok(KRecursorRule {
            ctor: resolve_name(&r.ctor, &name_to_addr),
            nfields: r.n_fields.to_u64().unwrap_or(0) as usize,
            rhs: convert_expr(&r.rhs, &ctx, &mut cache)?,
          }))
          .collect();
        KConstantInfo::Recursor(KRecursorVal {
          cv: convert_constant_val(&v.cnst, &ctx, &mut cache)?,
          lean_all: M::mk_field(v
            .all
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect()),
          canonical_block: vec![],
          induct_block: v
            .all
            .iter()
            .map(|n| resolve_name(n, &name_to_addr))
            .collect(),
          num_params: v.num_params.to_u64().unwrap_or(0) as usize,
          num_indices: v.num_indices.to_u64().unwrap_or(0) as usize,
          num_motives: v.num_motives.to_u64().unwrap_or(0) as usize,
          num_minors: v.num_minors.to_u64().unwrap_or(0) as usize,
          rules: rules?,
          k: v.k,
          is_unsafe: v.is_unsafe,
        })
      }
    };

    kenv.insert(id, kci);
  }

  // Phase 3: Build Primitives
  let prims = build_primitives(env, &name_to_addr);

  Ok((kenv, prims, quot_init))
}

/// Build the Primitives struct by resolving known names to addresses.
fn build_primitives<M: MetaMode>(
  _env: &env::Env,
  name_to_addr: &FxHashMap<blake3::Hash, Address>,
) -> Primitives<M> {
  let mut prims = Primitives::default();

  let lookup = |s: &str| -> Option<MetaId<M>> {
    let name = str_to_name(s);
    let hash = *name.get_hash();
    let addr = name_to_addr.get(&hash).cloned()?;
    Some(MetaId::new(addr, M::mk_field(name)))
  };

  prims.nat = lookup("Nat");
  prims.nat_zero = lookup("Nat.zero");
  prims.nat_succ = lookup("Nat.succ");
  prims.nat_add = lookup("Nat.add");
  prims.nat_pred = lookup("Nat.pred");
  prims.nat_sub = lookup("Nat.sub");
  prims.nat_mul = lookup("Nat.mul");
  prims.nat_pow = lookup("Nat.pow");
  prims.nat_gcd = lookup("Nat.gcd");
  prims.nat_mod = lookup("Nat.mod");
  prims.nat_div = lookup("Nat.div");
  prims.nat_bitwise = lookup("Nat.bitwise");
  prims.nat_beq = lookup("Nat.beq");
  prims.nat_ble = lookup("Nat.ble");
  prims.nat_land = lookup("Nat.land");
  prims.nat_lor = lookup("Nat.lor");
  prims.nat_xor = lookup("Nat.xor");
  prims.nat_shift_left = lookup("Nat.shiftLeft");
  prims.nat_shift_right = lookup("Nat.shiftRight");
  prims.bool_type = lookup("Bool");
  prims.bool_true = lookup("Bool.true");
  prims.bool_false = lookup("Bool.false");
  prims.string = lookup("String");
  prims.string_mk = lookup("String.mk");
  prims.char_type = lookup("Char");
  prims.char_mk = lookup("Char.mk");
  prims.string_of_list = lookup("String.ofList");
  prims.list = lookup("List");
  prims.list_nil = lookup("List.nil");
  prims.list_cons = lookup("List.cons");
  prims.eq = lookup("Eq");
  prims.eq_refl = lookup("Eq.refl");
  prims.quot_type = lookup("Quot");
  prims.quot_ctor = lookup("Quot.mk");
  prims.quot_lift = lookup("Quot.lift");
  prims.quot_ind = lookup("Quot.ind");
  prims.reduce_bool = lookup("Lean.reduceBool").or_else(|| lookup("reduceBool"));
  prims.reduce_nat = lookup("Lean.reduceNat").or_else(|| lookup("reduceNat"));
  prims.eager_reduce = lookup("eagerReduce");
  prims.system_platform_num_bits = lookup("System.Platform.numBits");

  prims
}

/// Convert a dotted string like "Nat.add" to a `Name`.
pub fn str_to_name(s: &str) -> Name {
  let parts: Vec<&str> = s.split('.').collect();
  let mut name = Name::anon();
  for part in parts {
    name = Name::str(name, part.to_string());
  }
  name
}

/// Helper trait to access common constant fields.
trait CnstVal {
  fn cnst_val(&self) -> &env::ConstantVal;
}

impl CnstVal for ConstantInfo {
  fn cnst_val(&self) -> &env::ConstantVal {
    match self {
      ConstantInfo::AxiomInfo(v) => &v.cnst,
      ConstantInfo::DefnInfo(v) => &v.cnst,
      ConstantInfo::ThmInfo(v) => &v.cnst,
      ConstantInfo::OpaqueInfo(v) => &v.cnst,
      ConstantInfo::QuotInfo(v) => &v.cnst,
      ConstantInfo::InductInfo(v) => &v.cnst,
      ConstantInfo::CtorInfo(v) => &v.cnst,
      ConstantInfo::RecInfo(v) => &v.cnst,
    }
  }
}

/// Verify that a converted KEnv structurally matches the source env::Env.
/// Returns a list of (constant_name, mismatch_description) for any discrepancies.
pub fn verify_conversion<M: MetaMode>(
  env: &env::Env,
  kenv: &KEnv<M>,
) -> Vec<(String, String)> {
  let mut errors = Vec::new();

  let nat = |n: &crate::lean::nat::Nat| -> usize {
    n.to_u64().unwrap_or(0) as usize
  };

  for (name, ci) in env {
    let pretty = name.pretty();
    let addr = Address::from_blake3_hash(ci.get_hash());
    let kci = match kenv.find_by_addr(&addr) {
      Some(kci) => kci,
      None => {
        errors.push((pretty, "missing from kenv".to_string()));
        continue;
      }
    };

    // Check num_levels
    if ci.cnst_val().level_params.len() != kci.cv().num_levels {
      errors.push((
        pretty.clone(),
        format!(
          "num_levels: {} vs {}",
          ci.cnst_val().level_params.len(),
          kci.cv().num_levels
        ),
      ));
    }

    // Check kind + kind-specific fields
    match (ci, kci) {
      (ConstantInfo::AxiomInfo(v), KConstantInfo::Axiom(kv)) => {
        if v.is_unsafe != kv.is_unsafe {
          errors.push((pretty, format!("is_unsafe: {} vs {}", v.is_unsafe, kv.is_unsafe)));
        }
      }
      (ConstantInfo::DefnInfo(v), KConstantInfo::Definition(kv)) => {
        if v.safety != kv.safety {
          errors.push((pretty.clone(), format!("safety: {:?} vs {:?}", v.safety, kv.safety)));
        }
        if let Some(kv_all) = M::field_ref(&kv.lean_all) {
          if v.all.len() != kv_all.len() {
            errors.push((pretty, format!("all.len: {} vs {}", v.all.len(), kv_all.len())));
          }
        }
      }
      (ConstantInfo::ThmInfo(v), KConstantInfo::Theorem(kv)) => {
        if let Some(kv_all) = M::field_ref(&kv.lean_all) {
          if v.all.len() != kv_all.len() {
            errors.push((pretty, format!("all.len: {} vs {}", v.all.len(), kv_all.len())));
          }
        }
      }
      (ConstantInfo::OpaqueInfo(v), KConstantInfo::Opaque(kv)) => {
        if v.is_unsafe != kv.is_unsafe {
          errors.push((pretty.clone(), format!("is_unsafe: {} vs {}", v.is_unsafe, kv.is_unsafe)));
        }
        if let Some(kv_all) = M::field_ref(&kv.lean_all) {
          if v.all.len() != kv_all.len() {
            errors.push((pretty, format!("all.len: {} vs {}", v.all.len(), kv_all.len())));
          }
        }
      }
      (ConstantInfo::QuotInfo(v), KConstantInfo::Quotient(kv)) => {
        if v.kind != kv.kind {
          errors.push((pretty, format!("kind: {:?} vs {:?}", v.kind, kv.kind)));
        }
      }
      (ConstantInfo::InductInfo(v), KConstantInfo::Inductive(kv)) => {
        let checks: &[(&str, usize, usize)] = &[
          ("num_params", nat(&v.num_params), kv.num_params),
          ("num_indices", nat(&v.num_indices), kv.num_indices),
          ("all.len", v.all.len(), M::field_ref(&kv.lean_all).map_or(0, |a| a.len())),
          ("ctors.len", v.ctors.len(), kv.ctors.len()),
          ("num_nested", nat(&v.num_nested), kv.num_nested),
        ];
        for (field, expected, got) in checks {
          if expected != got {
            errors.push((pretty.clone(), format!("{field}: {expected} vs {got}")));
          }
        }
        let bools: &[(&str, bool, bool)] = &[
          ("is_rec", v.is_rec, kv.is_rec),
          ("is_unsafe", v.is_unsafe, kv.is_unsafe),
          ("is_reflexive", v.is_reflexive, kv.is_reflexive),
        ];
        for (field, expected, got) in bools {
          if expected != got {
            errors.push((pretty.clone(), format!("{field}: {expected} vs {got}")));
          }
        }
      }
      (ConstantInfo::CtorInfo(v), KConstantInfo::Constructor(kv)) => {
        let checks: &[(&str, usize, usize)] = &[
          ("cidx", nat(&v.cidx), kv.cidx),
          ("num_params", nat(&v.num_params), kv.num_params),
          ("num_fields", nat(&v.num_fields), kv.num_fields),
        ];
        for (field, expected, got) in checks {
          if expected != got {
            errors.push((pretty.clone(), format!("{field}: {expected} vs {got}")));
          }
        }
        if v.is_unsafe != kv.is_unsafe {
          errors.push((pretty, format!("is_unsafe: {} vs {}", v.is_unsafe, kv.is_unsafe)));
        }
      }
      (ConstantInfo::RecInfo(v), KConstantInfo::Recursor(kv)) => {
        let checks: &[(&str, usize, usize)] = &[
          ("num_params", nat(&v.num_params), kv.num_params),
          ("num_indices", nat(&v.num_indices), kv.num_indices),
          ("num_motives", nat(&v.num_motives), kv.num_motives),
          ("num_minors", nat(&v.num_minors), kv.num_minors),
          ("all.len", v.all.len(), kv.induct_block.len()),
          ("rules.len", v.rules.len(), kv.rules.len()),
        ];
        for (field, expected, got) in checks {
          if expected != got {
            errors.push((pretty.clone(), format!("{field}: {expected} vs {got}")));
          }
        }
        if v.k != kv.k {
          errors.push((pretty.clone(), format!("k: {} vs {}", v.k, kv.k)));
        }
        if v.is_unsafe != kv.is_unsafe {
          errors.push((pretty.clone(), format!("is_unsafe: {} vs {}", v.is_unsafe, kv.is_unsafe)));
        }
        // Check rule nfields
        for (i, (r, kr)) in v.rules.iter().zip(kv.rules.iter()).enumerate() {
          if nat(&r.n_fields) != kr.nfields {
            errors.push((pretty.clone(), format!("rules[{i}].nfields: {} vs {}", nat(&r.n_fields), kr.nfields)));
          }
        }
      }
      _ => {
        let env_kind = match ci {
          ConstantInfo::AxiomInfo(_) => "axiom",
          ConstantInfo::DefnInfo(_) => "definition",
          ConstantInfo::ThmInfo(_) => "theorem",
          ConstantInfo::OpaqueInfo(_) => "opaque",
          ConstantInfo::QuotInfo(_) => "quotient",
          ConstantInfo::InductInfo(_) => "inductive",
          ConstantInfo::CtorInfo(_) => "constructor",
          ConstantInfo::RecInfo(_) => "recursor",
        };
        errors.push((
          pretty,
          format!("kind mismatch: env={} kenv={}", env_kind, kci.kind_name()),
        ));
      }
    }
  }

  // Check for constants in kenv that aren't in env
  if kenv.len() != env.len() {
    errors.push((
      "<env>".to_string(),
      format!("size mismatch: env={} kenv={}", env.len(), kenv.len()),
    ));
  }

  errors
}

/// Build the Primitives struct by scanning a KEnv for known constant names.
/// Used by the Ixon→KEnv path where we don't have a name→addr map from
/// the Lean env.
pub fn build_primitives_from_kenv<M: MetaMode>(
  kenv: &KEnv<M>,
) -> Primitives<M> {
  // Build a name→MetaId lookup from the KEnv
  let mut name_to_id: FxHashMap<blake3::Hash, MetaId<M>> =
    FxHashMap::default();
  for (id, ci) in kenv.iter() {
    if let Some(name) = M::field_ref(ci.name()) {
      name_to_id.insert(*name.get_hash(), id.clone());
    }
  }

  let mut prims = Primitives::default();

  let lookup = |s: &str| -> Option<MetaId<M>> {
    let name = str_to_name(s);
    let hash = *name.get_hash();
    name_to_id.get(&hash).cloned()
  };

  prims.nat = lookup("Nat");
  prims.nat_zero = lookup("Nat.zero");
  prims.nat_succ = lookup("Nat.succ");
  prims.nat_add = lookup("Nat.add");
  prims.nat_pred = lookup("Nat.pred");
  prims.nat_sub = lookup("Nat.sub");
  prims.nat_mul = lookup("Nat.mul");
  prims.nat_pow = lookup("Nat.pow");
  prims.nat_gcd = lookup("Nat.gcd");
  prims.nat_mod = lookup("Nat.mod");
  prims.nat_div = lookup("Nat.div");
  prims.nat_bitwise = lookup("Nat.bitwise");
  prims.nat_beq = lookup("Nat.beq");
  prims.nat_ble = lookup("Nat.ble");
  prims.nat_land = lookup("Nat.land");
  prims.nat_lor = lookup("Nat.lor");
  prims.nat_xor = lookup("Nat.xor");
  prims.nat_shift_left = lookup("Nat.shiftLeft");
  prims.nat_shift_right = lookup("Nat.shiftRight");
  prims.bool_type = lookup("Bool");
  prims.bool_true = lookup("Bool.true");
  prims.bool_false = lookup("Bool.false");
  prims.string = lookup("String");
  prims.string_mk = lookup("String.mk");
  prims.char_type = lookup("Char");
  prims.char_mk = lookup("Char.mk");
  prims.string_of_list = lookup("String.ofList");
  prims.list = lookup("List");
  prims.list_nil = lookup("List.nil");
  prims.list_cons = lookup("List.cons");
  prims.eq = lookup("Eq");
  prims.eq_refl = lookup("Eq.refl");
  prims.quot_type = lookup("Quot");
  prims.quot_ctor = lookup("Quot.mk");
  prims.quot_lift = lookup("Quot.lift");
  prims.quot_ind = lookup("Quot.ind");
  prims.reduce_bool = lookup("Lean.reduceBool").or_else(|| lookup("reduceBool"));
  prims.reduce_nat = lookup("Lean.reduceNat").or_else(|| lookup("reduceNat"));
  prims.eager_reduce = lookup("eagerReduce");
  prims.system_platform_num_bits = lookup("System.Platform.numBits");

  prims
}
