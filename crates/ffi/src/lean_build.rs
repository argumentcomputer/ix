//! Encode Rust `ix_common::env` values as real Lean kernel objects.
//!
//! The reverse of `lean_env.rs`: where that module decodes Lean's in-memory
//! C representation into the Rust `Name` / `Level` / `Expr` / `ConstantInfo`
//! types, this one constructs genuine `Lean.Name` / `Lean.Level` /
//! `Lean.Expr` / `Lean.ConstantInfo` objects from those Rust values, for
//! FFI entries that hand decompiled constants back to Lean (the
//! materialization path behind `import_ixe`).
//!
//! `Name`, `Level`, and `Expr` carry `@[computed_field]` data words (hash,
//! loose-bvar depth, has-fvar flags, …) that MUST be computed by Lean's own
//! algorithms, so those three types are built exclusively through the
//! toolchain's exported constructors (`lean_name_mk_*`, `lean_level_mk_*`,
//! `lean_expr_mk_*` — the `mk*Ex` exports in `Lean/Expr.lean` and
//! `Lean/Level.lean`). Plain structures (`Literal`, the `*Val` payloads,
//! `ConstantInfo` itself, `Syntax`, …) have no computed fields and are
//! allocated directly through the `LeanIx*` layout types, whose field
//! orders are pinned by `lean_env.rs::decode_constant_info`.
//!
//! Sharing: `ExprData` / `LevelData` / `NameData` live behind `Arc`s that
//! the decompiler dedups aggressively; the encode cache keys on those Arc
//! data pointers so shared Rust subterms become shared Lean objects. One
//! cache should span a whole marshaling batch (sharing crosses constant
//! boundaries).
//!
//! Expression encoding is iterative (explicit frame stack): Init-scale
//! terms overflow default runtime stacks (same reason
//! `Ix/Tc/EgressLean.lean` uses a stack machine).
//!
//! Known hole, deliberate: `DataValue::OfInt` inside mdata is rejected
//! with an error. Lean's runtime `Int` is scalar-or-mpz (no exported
//! constructor symbol), and the decode direction's ctor-read of an `Int`
//! would have crashed on any real env carrying one — empirically the case
//! never occurs in kernel constants.

use ix_common::env::{
  BinderInfo, ConstantInfo, ConstantVal, DataValue, DefinitionSafety, Expr,
  ExprData, Level, LevelData, Literal, Name, NameData, QuotKind, RecursorRule,
  ReducibilityHints, SourceInfo, Substring, Syntax, SyntaxPreresolved,
};
use lean_ffi::include::lean_object;
use lean_ffi::object::{LeanArray, LeanList, LeanNat, LeanOwned, LeanString};
use rustc_hash::FxHashMap;

use crate::lean::{
  LeanIxAxiomVal, LeanIxConstantInfo, LeanIxConstantVal, LeanIxConstructorVal,
  LeanIxDataValue, LeanIxDefinitionVal, LeanIxInductiveVal, LeanIxLiteral,
  LeanIxOpaqueVal, LeanIxQuotVal, LeanIxRecursorRule, LeanIxRecursorVal,
  LeanIxReducibilityHints, LeanIxSourceInfo, LeanIxSubstring, LeanIxSyntax,
  LeanIxSyntaxPreresolved, LeanIxTheoremVal,
};

unsafe extern "C" {
  // Lean/Level.lean `mkLevel*Ex` exports (computed-field data word done by
  // Lean). `lean_level_mk_zero : Unit → Level` takes the unit box.
  fn lean_name_mk_string(
    parent: *mut lean_object,
    part: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_name_mk_numeral(
    parent: *mut lean_object,
    part: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_level_mk_zero(unit: *mut lean_object) -> *mut lean_object;
  fn lean_level_mk_succ(l: *mut lean_object) -> *mut lean_object;
  fn lean_level_mk_max(
    a: *mut lean_object,
    b: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_level_mk_imax(
    a: *mut lean_object,
    b: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_level_mk_param(name: *mut lean_object) -> *mut lean_object;
  fn lean_level_mk_mvar(id: *mut lean_object) -> *mut lean_object;
  // Lean/Expr.lean `mk*Ex` exports. `BinderInfo` and `Bool` pass unboxed
  // as `uint8_t` per Lean's C ABI for scalar enums.
  fn lean_expr_mk_bvar(idx: *mut lean_object) -> *mut lean_object;
  fn lean_expr_mk_fvar(fvar_id: *mut lean_object) -> *mut lean_object;
  fn lean_expr_mk_mvar(mvar_id: *mut lean_object) -> *mut lean_object;
  fn lean_expr_mk_sort(level: *mut lean_object) -> *mut lean_object;
  fn lean_expr_mk_const(
    name: *mut lean_object,
    levels: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_expr_mk_app(
    f: *mut lean_object,
    a: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_expr_mk_lambda(
    name: *mut lean_object,
    ty: *mut lean_object,
    body: *mut lean_object,
    bi: u8,
  ) -> *mut lean_object;
  fn lean_expr_mk_forall(
    name: *mut lean_object,
    ty: *mut lean_object,
    body: *mut lean_object,
    bi: u8,
  ) -> *mut lean_object;
  fn lean_expr_mk_let(
    name: *mut lean_object,
    ty: *mut lean_object,
    value: *mut lean_object,
    body: *mut lean_object,
    nondep: u8,
  ) -> *mut lean_object;
  fn lean_expr_mk_lit(lit: *mut lean_object) -> *mut lean_object;
  fn lean_expr_mk_mdata(
    kvmap: *mut lean_object,
    e: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_expr_mk_proj(
    type_name: *mut lean_object,
    idx: *mut lean_object,
    e: *mut lean_object,
  ) -> *mut lean_object;
}

/// Cache of already-encoded nodes, keyed by the Rust `Arc` data pointer.
/// Each entry holds one owned reference; hits hand out a fresh
/// `to_owned_ref` (refcount-incremented) copy.
#[derive(Default)]
pub struct LeanEncodeCache {
  names: FxHashMap<*const NameData, LeanOwned>,
  levels: FxHashMap<*const LevelData, LeanOwned>,
  exprs: FxHashMap<*const ExprData, LeanOwned>,
}

/// Encode a `Name` as a real `Lean.Name` (hash computed field done by the
/// exported constructors). Names are shallow; plain recursion is fine.
pub fn encode_name(cache: &mut LeanEncodeCache, name: &Name) -> LeanOwned {
  if matches!(name.as_data(), NameData::Anonymous(_)) {
    return LeanOwned::box_usize(0);
  }
  let key = std::sync::Arc::as_ptr(&name.0);
  if let Some(cached) = cache.names.get(&key) {
    return cached.borrow().to_owned_ref();
  }
  let obj = match name.as_data() {
    NameData::Anonymous(_) => unreachable!("handled above"),
    NameData::Str(parent, s, _) => {
      let parent = encode_name(cache, parent);
      let part = LeanString::new(s);
      unsafe {
        LeanOwned::from_raw(lean_name_mk_string(
          parent.into_raw(),
          part.into_raw(),
        ))
      }
    },
    NameData::Num(parent, n, _) => {
      let parent = encode_name(cache, parent);
      let part = LeanNat::from_nat(n);
      unsafe {
        LeanOwned::from_raw(lean_name_mk_numeral(
          parent.into_raw(),
          part.into_raw(),
        ))
      }
    },
  };
  let out = obj.borrow().to_owned_ref();
  cache.names.insert(key, obj);
  out
}

/// Encode a `Level` as a real `Lean.Level`. Levels are shallow (depth =
/// syntactic level size); plain recursion mirrors `decode_level`.
pub fn encode_level(cache: &mut LeanEncodeCache, level: &Level) -> LeanOwned {
  let key = std::sync::Arc::as_ptr(&level.0);
  if let Some(cached) = cache.levels.get(&key) {
    return cached.borrow().to_owned_ref();
  }
  let obj = match level.as_data() {
    LevelData::Zero(_) => unsafe {
      LeanOwned::from_raw(lean_level_mk_zero(
        LeanOwned::box_usize(0).into_raw(),
      ))
    },
    LevelData::Succ(inner, _) => {
      let inner = encode_level(cache, inner);
      unsafe { LeanOwned::from_raw(lean_level_mk_succ(inner.into_raw())) }
    },
    LevelData::Max(a, b, _) => {
      let a = encode_level(cache, a);
      let b = encode_level(cache, b);
      unsafe {
        LeanOwned::from_raw(lean_level_mk_max(a.into_raw(), b.into_raw()))
      }
    },
    LevelData::Imax(a, b, _) => {
      let a = encode_level(cache, a);
      let b = encode_level(cache, b);
      unsafe {
        LeanOwned::from_raw(lean_level_mk_imax(a.into_raw(), b.into_raw()))
      }
    },
    LevelData::Param(name, _) => {
      let name = encode_name(cache, name);
      unsafe { LeanOwned::from_raw(lean_level_mk_param(name.into_raw())) }
    },
    // LMVarId is a trivial structure over Name: runtime repr is the Name.
    LevelData::Mvar(name, _) => {
      let name = encode_name(cache, name);
      unsafe { LeanOwned::from_raw(lean_level_mk_mvar(name.into_raw())) }
    },
  };
  let out = obj.borrow().to_owned_ref();
  cache.levels.insert(key, obj);
  out
}

fn encode_substring(s: &Substring) -> LeanOwned {
  let obj = LeanIxSubstring::alloc(0);
  obj.set_obj(0, LeanString::new(&s.str));
  obj.set_obj(1, LeanNat::from_nat(&s.start_pos));
  obj.set_obj(2, LeanNat::from_nat(&s.stop_pos));
  obj.into()
}

fn encode_source_info(si: &SourceInfo) -> LeanOwned {
  match si {
    SourceInfo::Original(leading, pos, trailing, end_pos) => {
      let obj = LeanIxSourceInfo::alloc(0);
      obj.set_obj(0, encode_substring(leading));
      obj.set_obj(1, LeanNat::from_nat(pos));
      obj.set_obj(2, encode_substring(trailing));
      obj.set_obj(3, LeanNat::from_nat(end_pos));
      obj.into()
    },
    SourceInfo::Synthetic(pos, end_pos, canonical) => {
      let obj = LeanIxSourceInfo::alloc(1);
      obj.set_obj(0, LeanNat::from_nat(pos));
      obj.set_obj(1, LeanNat::from_nat(end_pos));
      obj.set_num_8(0, u8::from(*canonical));
      obj.into()
    },
    SourceInfo::None => LeanOwned::box_usize(2),
  }
}

fn encode_syntax_preresolved(
  cache: &mut LeanEncodeCache,
  p: &SyntaxPreresolved,
) -> LeanOwned {
  match p {
    SyntaxPreresolved::Namespace(name) => {
      let obj = LeanIxSyntaxPreresolved::alloc(0);
      obj.set_obj(0, encode_name(cache, name));
      obj.into()
    },
    SyntaxPreresolved::Decl(name, fields) => {
      let obj = LeanIxSyntaxPreresolved::alloc(1);
      obj.set_obj(0, encode_name(cache, name));
      obj.set_obj(
        1,
        fields.iter().map(|f| LeanString::new(f)).collect::<LeanList<_>>(),
      );
      obj.into()
    },
  }
}

fn encode_syntax(cache: &mut LeanEncodeCache, syn: &Syntax) -> LeanOwned {
  match syn {
    Syntax::Missing => LeanOwned::box_usize(0),
    Syntax::Node(info, kind, args) => {
      let obj = LeanIxSyntax::alloc(1);
      obj.set_obj(0, encode_source_info(info));
      obj.set_obj(1, encode_name(cache, kind));
      let arr = LeanArray::alloc(args.len());
      for (i, a) in args.iter().enumerate() {
        arr.set(i, encode_syntax(cache, a));
      }
      obj.set_obj(2, arr);
      obj.into()
    },
    Syntax::Atom(info, val) => {
      let obj = LeanIxSyntax::alloc(2);
      obj.set_obj(0, encode_source_info(info));
      obj.set_obj(1, LeanString::new(val));
      obj.into()
    },
    Syntax::Ident(info, raw_val, val, preresolved) => {
      let obj = LeanIxSyntax::alloc(3);
      obj.set_obj(0, encode_source_info(info));
      obj.set_obj(1, encode_substring(raw_val));
      obj.set_obj(2, encode_name(cache, val));
      obj.set_obj(
        3,
        preresolved
          .iter()
          .map(|p| encode_syntax_preresolved(cache, p))
          .collect::<LeanList<_>>(),
      );
      obj.into()
    },
  }
}

fn encode_data_value(
  cache: &mut LeanEncodeCache,
  dv: &DataValue,
) -> Result<LeanOwned, String> {
  Ok(match dv {
    DataValue::OfString(s) => {
      let obj = LeanIxDataValue::alloc(0);
      obj.set_obj(0, LeanString::new(s));
      obj.into()
    },
    DataValue::OfBool(b) => {
      let obj = LeanIxDataValue::alloc(1);
      obj.set_num_8(0, u8::from(*b));
      obj.into()
    },
    DataValue::OfName(n) => {
      let obj = LeanIxDataValue::alloc(2);
      obj.set_obj(0, encode_name(cache, n));
      obj.into()
    },
    DataValue::OfNat(n) => {
      let obj = LeanIxDataValue::alloc(3);
      obj.set_obj(0, LeanNat::from_nat(n));
      obj.into()
    },
    DataValue::OfInt(_) => {
      return Err(
        "encode_data_value: DataValue.ofInt in kernel-constant mdata is \
         not supported (Lean's runtime Int has no exported constructor)"
          .to_string(),
      );
    },
    DataValue::OfSyntax(syn) => {
      let obj = LeanIxDataValue::alloc(5);
      obj.set_obj(0, encode_syntax(cache, syn));
      obj.into()
    },
  })
}

/// Encode an mdata payload as a runtime `MData` (= `KVMap`, whose
/// single-field-structure runtime repr is the bare
/// `List (Name × DataValue)` — see `decode_expr` tag 10).
fn encode_kvmap(
  cache: &mut LeanEncodeCache,
  kv: &[(Name, DataValue)],
) -> Result<LeanOwned, String> {
  let mut pairs: Vec<LeanOwned> = Vec::with_capacity(kv.len());
  for (name, dv) in kv {
    let name_obj = encode_name(cache, name);
    let dv_obj = encode_data_value(cache, dv)?;
    pairs.push(lean_ffi::object::LeanProd::new(name_obj, dv_obj).into());
  }
  Ok(pairs.into_iter().collect::<LeanList<_>>().into())
}

fn encode_literal(lit: &Literal) -> LeanOwned {
  match lit {
    Literal::NatVal(n) => {
      let obj = LeanIxLiteral::alloc(0);
      obj.set_obj(0, LeanNat::from_nat(n));
      obj.into()
    },
    Literal::StrVal(s) => {
      let obj = LeanIxLiteral::alloc(1);
      obj.set_obj(0, LeanString::new(s));
      obj.into()
    },
  }
}

const fn binder_info_byte(bi: &BinderInfo) -> u8 {
  match bi {
    BinderInfo::Default => 0,
    BinderInfo::Implicit => 1,
    BinderInfo::StrictImplicit => 2,
    BinderInfo::InstImplicit => 3,
  }
}

/// Frames for the iterative expression encoder. `Build` re-matches the
/// node once its children sit on the value stack.
enum EFrame<'a> {
  Process(&'a Expr),
  Build(&'a Expr),
}

/// Encode an `Expr` as a real `Lean.Expr`, iterative with an explicit
/// frame stack and value stack. Shared subterms (Arc identity) encode
/// once via the cache.
pub fn encode_expr(
  cache: &mut LeanEncodeCache,
  root: &Expr,
) -> Result<LeanOwned, String> {
  let mut stack: Vec<EFrame<'_>> = vec![EFrame::Process(root)];
  let mut values: Vec<LeanOwned> = Vec::new();

  // Insert into the cache and push an incremented handle onto `values`.
  fn finish(
    cache: &mut LeanEncodeCache,
    values: &mut Vec<LeanOwned>,
    key: *const ExprData,
    obj: LeanOwned,
  ) {
    let out = obj.borrow().to_owned_ref();
    cache.exprs.insert(key, obj);
    values.push(out);
  }

  while let Some(frame) = stack.pop() {
    match frame {
      EFrame::Process(e) => {
        let key = std::sync::Arc::as_ptr(&e.0);
        if let Some(cached) = cache.exprs.get(&key) {
          values.push(cached.borrow().to_owned_ref());
          continue;
        }
        match e.as_data() {
          ExprData::Bvar(idx, _) => {
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_bvar(
                LeanNat::from_nat(idx).into_raw(),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          // FVarId / MVarId are trivial structures over Name: runtime
          // repr is the Name itself.
          ExprData::Fvar(name, _) => {
            let name = encode_name(cache, name);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_fvar(name.into_raw()))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Mvar(name, _) => {
            let name = encode_name(cache, name);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_mvar(name.into_raw()))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Sort(level, _) => {
            let level = encode_level(cache, level);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_sort(level.into_raw()))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Const(name, levels, _) => {
            let name = encode_name(cache, name);
            let levels = levels
              .iter()
              .map(|l| encode_level(cache, l))
              .collect::<LeanList<_>>();
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_const(
                name.into_raw(),
                LeanOwned::from(levels).into_raw(),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Lit(lit, _) => {
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_lit(
                encode_literal(lit).into_raw(),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::App(f, a, _) => {
            stack.push(EFrame::Build(e));
            stack.push(EFrame::Process(a));
            stack.push(EFrame::Process(f));
          },
          ExprData::Lam(_, ty, body, _, _)
          | ExprData::ForallE(_, ty, body, _, _) => {
            stack.push(EFrame::Build(e));
            stack.push(EFrame::Process(body));
            stack.push(EFrame::Process(ty));
          },
          ExprData::LetE(_, ty, value, body, _, _) => {
            stack.push(EFrame::Build(e));
            stack.push(EFrame::Process(body));
            stack.push(EFrame::Process(value));
            stack.push(EFrame::Process(ty));
          },
          ExprData::Mdata(_, inner, _) | ExprData::Proj(_, _, inner, _) => {
            stack.push(EFrame::Build(e));
            stack.push(EFrame::Process(inner));
          },
        }
      },
      EFrame::Build(e) => {
        let key = std::sync::Arc::as_ptr(&e.0);
        match e.as_data() {
          ExprData::App(..) => {
            let a = values.pop().expect("app arg on value stack");
            let f = values.pop().expect("app fn on value stack");
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_app(f.into_raw(), a.into_raw()))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Lam(name, _, _, bi, _) => {
            let body = values.pop().expect("lam body on value stack");
            let ty = values.pop().expect("lam ty on value stack");
            let name = encode_name(cache, name);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_lambda(
                name.into_raw(),
                ty.into_raw(),
                body.into_raw(),
                binder_info_byte(bi),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::ForallE(name, _, _, bi, _) => {
            let body = values.pop().expect("forall body on value stack");
            let ty = values.pop().expect("forall ty on value stack");
            let name = encode_name(cache, name);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_forall(
                name.into_raw(),
                ty.into_raw(),
                body.into_raw(),
                binder_info_byte(bi),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::LetE(name, _, _, _, nondep, _) => {
            let body = values.pop().expect("let body on value stack");
            let value = values.pop().expect("let value on value stack");
            let ty = values.pop().expect("let ty on value stack");
            let name = encode_name(cache, name);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_let(
                name.into_raw(),
                ty.into_raw(),
                value.into_raw(),
                body.into_raw(),
                u8::from(*nondep),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Mdata(kv, _, _) => {
            let inner = values.pop().expect("mdata inner on value stack");
            let kvmap = encode_kvmap(cache, kv)?;
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_mdata(
                kvmap.into_raw(),
                inner.into_raw(),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          ExprData::Proj(type_name, idx, _, _) => {
            let inner = values.pop().expect("proj struct on value stack");
            let type_name = encode_name(cache, type_name);
            let obj = unsafe {
              LeanOwned::from_raw(lean_expr_mk_proj(
                type_name.into_raw(),
                LeanNat::from_nat(idx).into_raw(),
                inner.into_raw(),
              ))
            };
            finish(cache, &mut values, key, obj);
          },
          _ => unreachable!("leaf variants never get Build frames"),
        }
      },
    }
  }

  match (values.pop(), values.is_empty()) {
    (Some(v), true) => Ok(v),
    (Some(_), false) => Err("encode_expr: unbalanced value stack".to_string()),
    (None, _) => Err("encode_expr: empty result stack".to_string()),
  }
}

fn encode_name_list(cache: &mut LeanEncodeCache, names: &[Name]) -> LeanOwned {
  names.iter().map(|n| encode_name(cache, n)).collect::<LeanList<_>>().into()
}

fn encode_constant_val(
  cache: &mut LeanEncodeCache,
  cv: &ConstantVal,
) -> Result<LeanOwned, String> {
  let obj = LeanIxConstantVal::alloc(0);
  obj.set_obj(0, encode_name(cache, &cv.name));
  obj.set_obj(1, encode_name_list(cache, &cv.level_params));
  obj.set_obj(2, encode_expr(cache, &cv.typ)?);
  Ok(obj.into())
}

fn encode_reducibility_hints(hints: &ReducibilityHints) -> LeanOwned {
  match hints {
    ReducibilityHints::Opaque => LeanOwned::box_usize(0),
    ReducibilityHints::Abbrev => LeanOwned::box_usize(1),
    ReducibilityHints::Regular(n) => {
      let obj = LeanIxReducibilityHints::alloc(2);
      obj.set_num_32(0, *n);
      obj.into()
    },
  }
}

const fn definition_safety_byte(safety: &DefinitionSafety) -> u8 {
  match safety {
    DefinitionSafety::Unsafe => 0,
    DefinitionSafety::Safe => 1,
    DefinitionSafety::Partial => 2,
  }
}

const fn quot_kind_byte(kind: &QuotKind) -> u8 {
  match kind {
    QuotKind::Type => 0,
    QuotKind::Ctor => 1,
    QuotKind::Lift => 2,
    QuotKind::Ind => 3,
  }
}

fn encode_recursor_rule(
  cache: &mut LeanEncodeCache,
  rule: &RecursorRule,
) -> Result<LeanOwned, String> {
  let obj = LeanIxRecursorRule::alloc(0);
  obj.set_obj(0, encode_name(cache, &rule.ctor));
  obj.set_obj(1, LeanNat::from_nat(&rule.n_fields));
  obj.set_obj(2, encode_expr(cache, &rule.rhs)?);
  Ok(obj.into())
}

/// Encode a `ConstantInfo` as a real `Lean.ConstantInfo`. Field orders and
/// scalar placements mirror `lean_env.rs::decode_constant_info` exactly.
pub fn encode_constant_info(
  cache: &mut LeanEncodeCache,
  ci: &ConstantInfo,
) -> Result<LeanOwned, String> {
  let (tag, inner): (u8, LeanOwned) = match ci {
    ConstantInfo::AxiomInfo(v) => {
      let obj = LeanIxAxiomVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_num_8(0, u8::from(v.is_unsafe));
      (0, obj.into())
    },
    ConstantInfo::DefnInfo(v) => {
      let obj = LeanIxDefinitionVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_obj(1, encode_expr(cache, &v.value)?);
      obj.set_obj(2, encode_reducibility_hints(&v.hints));
      obj.set_obj(3, encode_name_list(cache, &v.all));
      obj.set_num_8(0, definition_safety_byte(&v.safety));
      (1, obj.into())
    },
    ConstantInfo::ThmInfo(v) => {
      let obj = LeanIxTheoremVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_obj(1, encode_expr(cache, &v.value)?);
      obj.set_obj(2, encode_name_list(cache, &v.all));
      (2, obj.into())
    },
    ConstantInfo::OpaqueInfo(v) => {
      let obj = LeanIxOpaqueVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_obj(1, encode_expr(cache, &v.value)?);
      obj.set_obj(2, encode_name_list(cache, &v.all));
      obj.set_num_8(0, u8::from(v.is_unsafe));
      (3, obj.into())
    },
    ConstantInfo::QuotInfo(v) => {
      let obj = LeanIxQuotVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_num_8(0, quot_kind_byte(&v.kind));
      (4, obj.into())
    },
    ConstantInfo::InductInfo(v) => {
      let obj = LeanIxInductiveVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_obj(1, LeanNat::from_nat(&v.num_params));
      obj.set_obj(2, LeanNat::from_nat(&v.num_indices));
      obj.set_obj(3, encode_name_list(cache, &v.all));
      obj.set_obj(4, encode_name_list(cache, &v.ctors));
      obj.set_obj(5, LeanNat::from_nat(&v.num_nested));
      obj.set_num_8(0, u8::from(v.is_rec));
      obj.set_num_8(1, u8::from(v.is_unsafe));
      obj.set_num_8(2, u8::from(v.is_reflexive));
      (5, obj.into())
    },
    ConstantInfo::CtorInfo(v) => {
      let obj = LeanIxConstructorVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_obj(1, encode_name(cache, &v.induct));
      obj.set_obj(2, LeanNat::from_nat(&v.cidx));
      obj.set_obj(3, LeanNat::from_nat(&v.num_params));
      obj.set_obj(4, LeanNat::from_nat(&v.num_fields));
      obj.set_num_8(0, u8::from(v.is_unsafe));
      (6, obj.into())
    },
    ConstantInfo::RecInfo(v) => {
      let obj = LeanIxRecursorVal::alloc(0);
      obj.set_obj(0, encode_constant_val(cache, &v.cnst)?);
      obj.set_obj(1, encode_name_list(cache, &v.all));
      obj.set_obj(2, LeanNat::from_nat(&v.num_params));
      obj.set_obj(3, LeanNat::from_nat(&v.num_indices));
      obj.set_obj(4, LeanNat::from_nat(&v.num_motives));
      obj.set_obj(5, LeanNat::from_nat(&v.num_minors));
      let mut rules: Vec<LeanOwned> = Vec::with_capacity(v.rules.len());
      for rule in &v.rules {
        rules.push(encode_recursor_rule(cache, rule)?);
      }
      obj.set_obj(6, rules.into_iter().collect::<LeanList<_>>());
      obj.set_num_8(0, u8::from(v.k));
      obj.set_num_8(1, u8::from(v.is_unsafe));
      (7, obj.into())
    },
  };
  let outer = LeanIxConstantInfo::alloc(tag);
  outer.set_obj(0, inner);
  Ok(outer.into())
}
