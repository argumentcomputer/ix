use std::ffi::c_void;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::{
  ix::compile::compile_env,
  ix::decompile::{check_decompile, decompile_env},
  ix::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
    DefinitionSafety, DefinitionVal, Env, Expr, InductiveVal, Int, Level,
    Literal, Name, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
    ReducibilityHints, SourceInfo, Substring, Syntax, SyntaxPreresolved,
    TheoremVal,
  },
  lean::{
    ListIterator, array::LeanArrayObject, as_ref_unsafe, collect_list,
    collect_list_with, ctor::LeanCtorObject, lean_is_scalar, nat::Nat,
    string::LeanStringObject,
  },
  lean_unbox,
};

#[derive(Default)]
struct Cache {
  univs: FxHashMap<*const c_void, Level>,
  exprs: FxHashMap<*const c_void, Expr>,
  names: FxHashMap<*const c_void, Name>,
}

fn lean_ptr_to_level(ptr: *const c_void, cache: &mut Cache) -> Level {
  if let Some(cached) = cache.univs.get(&ptr) {
    return cached.clone();
  }
  let level = if lean_is_scalar(ptr) {
    Level::zero()
  } else {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
      1 => {
        let [u] = ctor.objs().map(|ptr| lean_ptr_to_level(ptr, cache));
        Level::succ(u)
      },
      2 => {
        let [u, v] = ctor.objs().map(|ptr| lean_ptr_to_level(ptr, cache));
        Level::max(u, v)
      },
      3 => {
        let [u, v] = ctor.objs().map(|ptr| lean_ptr_to_level(ptr, cache));
        Level::imax(u, v)
      },
      4 => {
        let [name] = ctor.objs().map(|ptr| lean_ptr_to_name(ptr, cache));
        Level::param(name)
      },
      5 => {
        let [name] = ctor.objs().map(|ptr| lean_ptr_to_name(ptr, cache));
        Level::mvar(name)
      },
      _ => unreachable!(),
    }
  };
  cache.univs.insert(ptr, level.clone());
  level
}

fn lean_ptr_to_substring(ptr: *const c_void) -> Substring {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [str_ptr, start_pos_ptr, stop_pos_ptr] = ctor.objs();
  let str: &LeanStringObject = as_ref_unsafe(str_ptr.cast());
  let str = str.as_string();
  let start_pos = Nat::from_ptr(start_pos_ptr);
  let stop_pos = Nat::from_ptr(stop_pos_ptr);
  Substring { str, start_pos, stop_pos }
}

fn lean_ptr_to_source_info(ptr: *const c_void) -> SourceInfo {
  if lean_is_scalar(ptr) {
    return SourceInfo::None;
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      let [leading_ptr, pos_ptr, trailing_ptr, end_pos_ptr] = ctor.objs();
      let leading = lean_ptr_to_substring(leading_ptr);
      let pos = Nat::from_ptr(pos_ptr);
      let trailing = lean_ptr_to_substring(trailing_ptr);
      let end_pos = Nat::from_ptr(end_pos_ptr);
      SourceInfo::Original(leading, pos, trailing, end_pos)
    },
    1 => {
      let [pos_ptr, end_pos_ptr, canonical_ptr] = ctor.objs();
      let pos = Nat::from_ptr(pos_ptr);
      let end_pos = Nat::from_ptr(end_pos_ptr);
      let canonical = canonical_ptr as usize == 1;
      SourceInfo::Synthetic(pos, end_pos, canonical)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_syntax_preresolved(
  ptr: *const c_void,
  cache: &mut Cache,
) -> SyntaxPreresolved {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      let [name_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache);
      SyntaxPreresolved::Namespace(name)
    },
    1 => {
      let [name_ptr, fields_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache);
      let fields = collect_list(fields_ptr, |ptr| {
        let str: &LeanStringObject = as_ref_unsafe(ptr.cast());
        str.as_string()
      });
      SyntaxPreresolved::Decl(name, fields)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_syntax(ptr: *const c_void, cache: &mut Cache) -> Syntax {
  if lean_is_scalar(ptr) {
    return Syntax::Missing;
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    1 => {
      let [info_ptr, kind_ptr, args_ptr] = ctor.objs();
      let info = lean_ptr_to_source_info(info_ptr);
      let kind = lean_ptr_to_name(kind_ptr, cache);
      let args_array: &LeanArrayObject = as_ref_unsafe(args_ptr.cast());
      let args = args_array.to_vec_with(lean_ptr_to_syntax, cache);
      Syntax::Node(info, kind, args)
    },
    2 => {
      let [info_ptr, val_ptr] = ctor.objs();
      let info = lean_ptr_to_source_info(info_ptr);
      let val_str: &LeanStringObject = as_ref_unsafe(val_ptr.cast());
      Syntax::Atom(info, val_str.as_string())
    },
    3 => {
      let [info_ptr, raw_val_ptr, val_ptr, preresolved_ptr] = ctor.objs();
      let info = lean_ptr_to_source_info(info_ptr);
      let raw_val = lean_ptr_to_substring(raw_val_ptr);
      let val = lean_ptr_to_name(val_ptr, cache);
      let preresolved = collect_list_with(
        preresolved_ptr,
        lean_ptr_to_syntax_preresolved,
        cache,
      );
      Syntax::Ident(info, raw_val, val, preresolved)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_name_data_value(
  ptr: *const c_void,
  cache: &mut Cache,
) -> (Name, DataValue) {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [name_ptr, data_value_ptr] = ctor.objs();
  let name = lean_ptr_to_name(name_ptr, cache);
  let data_value_ctor: &LeanCtorObject = as_ref_unsafe(data_value_ptr.cast());
  let [inner_ptr] = data_value_ctor.objs();
  let data_value = match data_value_ctor.tag() {
    0 => {
      let str: &LeanStringObject = as_ref_unsafe(inner_ptr.cast());
      DataValue::OfString(str.as_string())
    },
    1 => DataValue::OfBool(inner_ptr as usize == 1),
    2 => DataValue::OfName(lean_ptr_to_name(inner_ptr, cache)),
    3 => DataValue::OfNat(Nat::from_ptr(inner_ptr)),
    4 => {
      let int_ctor: &LeanCtorObject = as_ref_unsafe(inner_ptr.cast());
      let [nat_ptr] = int_ctor.objs();
      let nat = Nat::from_ptr(nat_ptr);
      let int = match int_ctor.tag() {
        0 => Int::OfNat(nat),
        1 => Int::NegSucc(nat),
        _ => unreachable!(),
      };
      DataValue::OfInt(int)
    },
    5 => DataValue::OfSyntax(lean_ptr_to_syntax(inner_ptr, cache).into()),
    _ => unreachable!(),
  };
  (name, data_value)
}

fn lean_ptr_to_expr(ptr: *const c_void, cache: &mut Cache) -> Expr {
  if let Some(cached) = cache.exprs.get(&ptr) {
    return cached.clone();
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let expr = match ctor.tag() {
    0 => {
      let [nat_ptr, _hash_ptr] = ctor.objs();
      let nat = Nat::from_ptr(nat_ptr.cast());
      Expr::bvar(nat)
    },
    1 => {
      let [name_ptr, _hash_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache);
      Expr::fvar(name)
    },
    2 => {
      let [name_ptr, _hash_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache);
      Expr::mvar(name)
    },
    3 => {
      let [u_ptr, _hash_ptr] = ctor.objs();
      let u = lean_ptr_to_level(u_ptr, cache);
      Expr::sort(u)
    },
    4 => {
      let [name_ptr, levels_ptr, _hash_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache);
      let levels = collect_list_with(levels_ptr, lean_ptr_to_level, cache);
      Expr::cnst(name, levels)
    },
    5 => {
      let [f_ptr, a_ptr, _hash_ptr] = ctor.objs();
      let f = lean_ptr_to_expr(f_ptr, cache);
      let a = lean_ptr_to_expr(a_ptr, cache);
      Expr::app(f, a)
    },
    6 => {
      let [
        binder_name_ptr,
        binder_typ_ptr,
        body_ptr,
        _hash_ptr,
        binder_info_ptr,
      ] = ctor.objs();
      let binder_name = lean_ptr_to_name(binder_name_ptr, cache);
      let binder_typ = lean_ptr_to_expr(binder_typ_ptr, cache);
      let body = lean_ptr_to_expr(body_ptr, cache);
      let binder_info = match binder_info_ptr as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Expr::lam(binder_name, binder_typ, body, binder_info)
    },
    7 => {
      let [
        binder_name_ptr,
        binder_typ_ptr,
        body_ptr,
        _hash_ptr,
        binder_info_ptr,
      ] = ctor.objs();
      let binder_name = lean_ptr_to_name(binder_name_ptr, cache);
      let binder_typ = lean_ptr_to_expr(binder_typ_ptr, cache);
      let body = lean_ptr_to_expr(body_ptr, cache);
      let binder_info = match binder_info_ptr as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Expr::all(binder_name, binder_typ, body, binder_info)
    },
    8 => {
      let [decl_name_ptr, typ_ptr, value_ptr, body_ptr, _hash_ptr, nondep_ptr] =
        ctor.objs();
      let decl_name = lean_ptr_to_name(decl_name_ptr, cache);
      let typ = lean_ptr_to_expr(typ_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let body = lean_ptr_to_expr(body_ptr, cache);
      let nondep = nondep_ptr as usize == 1;
      Expr::letE(decl_name, typ, value, body, nondep)
    },
    9 => {
      let [literal_ptr, _hash_ptr] = ctor.objs();
      let literal: &LeanCtorObject = as_ref_unsafe(literal_ptr.cast());
      let [inner_ptr] = literal.objs();
      match literal.tag() {
        0 => {
          let nat = Nat::from_ptr(inner_ptr);
          Expr::lit(Literal::NatVal(nat))
        },
        1 => {
          let str: &LeanStringObject = as_ref_unsafe(inner_ptr.cast());
          Expr::lit(Literal::StrVal(str.as_string()))
        },
        _ => unreachable!(),
      }
    },
    10 => {
      let [data_ptr, expr_ptr] = ctor.objs();
      let kv_map =
        collect_list_with(data_ptr, lean_ptr_to_name_data_value, cache);
      let expr = lean_ptr_to_expr(expr_ptr, cache);
      Expr::mdata(kv_map, expr)
    },
    11 => {
      let [typ_name_ptr, idx_ptr, struct_ptr] = ctor.objs();
      let typ_name = lean_ptr_to_name(typ_name_ptr, cache);
      let idx = Nat::from_ptr(idx_ptr);
      let struct_expr = lean_ptr_to_expr(struct_ptr, cache);
      Expr::proj(typ_name, idx, struct_expr)
    },
    _ => unreachable!(),
  };
  cache.exprs.insert(ptr, expr.clone());
  expr
}

fn lean_ptr_to_recursor_rule(
  ptr: *const c_void,
  cache: &mut Cache,
) -> RecursorRule {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [ctor_ptr, n_fields_ptr, rhs_ptr] = ctor.objs();
  let ctor = lean_ptr_to_name(ctor_ptr, cache);
  let n_fields = Nat::from_ptr(n_fields_ptr);
  let rhs = lean_ptr_to_expr(rhs_ptr, cache);
  RecursorRule { ctor, n_fields, rhs }
}

fn lean_ptr_to_constant_val(
  ptr: *const c_void,
  cache: &mut Cache,
) -> ConstantVal {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [name_ptr, level_params_ptr, typ_ptr] = ctor.objs();
  let name = lean_ptr_to_name(name_ptr, cache);
  let level_params =
    collect_list_with(level_params_ptr, lean_ptr_to_name, cache);
  let typ = lean_ptr_to_expr(typ_ptr, cache);
  ConstantVal { name, level_params, typ }
}

fn lean_ptr_to_constant_info(
  ptr: *const c_void,
  cache: &mut Cache,
) -> ConstantInfo {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [inner_val_ptr] = ctor.objs();
  let inner_val: &LeanCtorObject = as_ref_unsafe(inner_val_ptr.cast());
  match ctor.tag() {
    0 => {
      let [constant_val_ptr, is_unsafe_ptr] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let is_unsafe = is_unsafe_ptr as usize == 1;
      let axiom_val = AxiomVal { cnst: constant_val, is_unsafe };
      ConstantInfo::AxiomInfo(axiom_val)
    },
    1 => {
      let [constant_val_ptr, value_ptr, hints_ptr, all_ptr, safety_ptr] =
        inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let hints = if lean_is_scalar(hints_ptr) {
        match lean_unbox!(usize, hints_ptr) {
          0 => ReducibilityHints::Opaque,
          1 => ReducibilityHints::Abbrev,
          _ => unreachable!(),
        }
      } else {
        let hints_ctor: &LeanCtorObject = as_ref_unsafe(hints_ptr.cast());
        let [height_ptr] = hints_ctor.objs();
        ReducibilityHints::Regular(height_ptr as u32)
      };
      let all = collect_list_with(all_ptr, lean_ptr_to_name, cache);
      let safety = match safety_ptr as usize {
        0 => DefinitionSafety::Unsafe,
        1 => DefinitionSafety::Safe,
        2 => DefinitionSafety::Partial,
        _ => unreachable!(),
      };
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: constant_val,
        value,
        hints,
        safety,
        all,
      })
    },
    2 => {
      let [constant_val_ptr, value_ptr, all_ptr] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let all = collect_list_with(all_ptr, lean_ptr_to_name, cache);
      ConstantInfo::ThmInfo(TheoremVal { cnst: constant_val, value, all })
    },
    3 => {
      let [constant_val_ptr, value_ptr, all_ptr, is_unsafe_ptr] =
        inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let all = collect_list_with(all_ptr, lean_ptr_to_name, cache);
      let is_unsafe = is_unsafe_ptr as usize == 1;
      ConstantInfo::OpaqueInfo(OpaqueVal {
        cnst: constant_val,
        value,
        is_unsafe,
        all,
      })
    },
    4 => {
      let [constant_val_ptr, kind_ptr] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let kind = match kind_ptr as usize {
        0 => QuotKind::Type,
        1 => QuotKind::Ctor,
        2 => QuotKind::Lift,
        3 => QuotKind::Ind,
        _ => unreachable!(),
      };
      ConstantInfo::QuotInfo(QuotVal { cnst: constant_val, kind })
    },
    5 => {
      let [
        constant_val_ptr,
        num_params_ptr,
        num_indices_ptr,
        all_ptr,
        ctors_ptr,
        num_nested_ptr,
        bools_ptr,
      ] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let num_params = Nat::from_ptr(num_params_ptr);
      let num_indices = Nat::from_ptr(num_indices_ptr);
      let all = collect_list_with(all_ptr, lean_ptr_to_name, cache);
      let ctors = collect_list_with(ctors_ptr, lean_ptr_to_name, cache);
      let num_nested = Nat::from_ptr(num_nested_ptr);
      let [is_rec, is_unsafe, is_reflexive, ..] =
        (bools_ptr as usize).to_le_bytes().map(|b| b == 1);
      ConstantInfo::InductInfo(InductiveVal {
        cnst: constant_val,
        num_params,
        num_indices,
        all,
        ctors,
        num_nested,
        is_rec,
        is_unsafe,
        is_reflexive,
      })
    },
    6 => {
      let [
        constant_val_ptr,
        induct_ptr,
        cidx_ptr,
        num_params_ptr,
        num_fields_ptr,
        is_unsafe_ptr,
      ] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let induct = lean_ptr_to_name(induct_ptr, cache);
      let cidx = Nat::from_ptr(cidx_ptr);
      let num_params = Nat::from_ptr(num_params_ptr);
      let num_fields = Nat::from_ptr(num_fields_ptr);
      let is_unsafe = is_unsafe_ptr as usize == 1;
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: constant_val,
        induct,
        cidx,
        num_params,
        num_fields,
        is_unsafe,
      })
    },
    7 => {
      let [
        constant_val_ptr,
        all_ptr,
        num_params_ptr,
        num_indices_ptr,
        num_motives_ptr,
        num_minors_ptr,
        rules_ptr,
        bools_ptr,
      ] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let all = collect_list_with(all_ptr, lean_ptr_to_name, cache);
      let num_params = Nat::from_ptr(num_params_ptr);
      let num_indices = Nat::from_ptr(num_indices_ptr);
      let num_motives = Nat::from_ptr(num_motives_ptr);
      let num_minors = Nat::from_ptr(num_minors_ptr);
      let rules = ListIterator(rules_ptr)
        .map(|rule_ptr| lean_ptr_to_recursor_rule(rule_ptr, cache))
        .collect();
      let [k, is_unsafe, ..] =
        (bools_ptr as usize).to_le_bytes().map(|b| b == 1);
      ConstantInfo::RecInfo(RecursorVal {
        cnst: constant_val,
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        k,
        is_unsafe,
      })
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_name(ptr: *const c_void, cache: &mut Cache) -> Name {
  if let Some(name) = cache.names.get(&ptr) {
    return name.clone();
  }
  let name = if lean_is_scalar(ptr) {
    Name::anon()
  } else {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [pre_ptr, pos_ptr] = ctor.objs();
    let pre = lean_ptr_to_name(pre_ptr, cache);
    match ctor.tag() {
      1 => {
        let str_obj: &LeanStringObject = as_ref_unsafe(pos_ptr.cast());
        Name::str(pre, str_obj.as_string())
      },
      2 => Name::num(pre, Nat::from_ptr(pos_ptr)),
      _ => unreachable!(),
    }
  };
  cache.names.insert(ptr, name.clone());
  name
}

fn lean_ptr_to_name_constant_info(
  ptr: *const c_void,
  cache: &mut Cache,
) -> (Name, ConstantInfo) {
  let prod_ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [name_ptr, constant_info_ptr] = prod_ctor.objs();
  let name = lean_ptr_to_name(name_ptr, cache);
  let constant_info = lean_ptr_to_constant_info(constant_info_ptr, cache);
  (name, constant_info)
}

fn lean_ptr_to_env(ptr: *const c_void) -> Env {
  let mut cache = Cache::default();
  let mut env = Env::default();
  for ptr in ListIterator(ptr) {
    let (name, constant_info) = lean_ptr_to_name_constant_info(ptr, &mut cache);
    env.insert(name.clone(), constant_info);
  }
  env
}

#[unsafe(no_mangle)]
extern "C" fn rs_tmp_decode_const_map(ptr: *const c_void) -> usize {
  let start_decoding = std::time::SystemTime::now();
  let env = lean_ptr_to_env(ptr);
  let env = Arc::new(env);
  println!("Decoding: {:.2}s", start_decoding.elapsed().unwrap().as_secs_f32());
  let res = compile_env(&env);
  match res {
    Ok(stt) => {
      println!("Compile OK: {:?}", stt.stats());
      match decompile_env(&stt) {
        Ok(dstt) => {
          println!("Decompile OK: {:?}", dstt.stats());
          match check_decompile(env.as_ref(), &stt, &dstt) {
            Ok(()) => println!("Roundtrip OK"),
            Err(e) => println!("Roundtrip ERR: {:?}", e),
          }
        },
        Err(e) => println!("Decompile ERR: {:?}", e),
      }
    },
    Err(e) => println!("Compile ERR: {:?}", e),
  }
  println!("Total: {:.2}s", start_decoding.elapsed().unwrap().as_secs_f32());
  env.as_ref().len()
}
