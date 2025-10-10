use std::{ffi::c_void, sync::Arc};

use rustc_hash::FxHashMap;

use crate::{
    lean::{
        array::LeanArrayObject, as_ref_unsafe, collect_list, collect_list_with,
        ctor::LeanCtorObject, lean_is_scalar, nat::Nat, string::LeanStringObject,
    },
    lean_env::{
        AxiomVal, BinderInfo, ConstMap, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
        DefinitionSafety, DefinitionVal, Expr, InductiveVal, Int, Level, Literal, Name, OpaqueVal,
        QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints, SourceInfo, Substring,
        Syntax, SyntaxPreresolved, TheoremVal,
    },
    lean_unbox,
};

// TODO: does caching more help?
type ExprCache = FxHashMap<*const c_void, Arc<Expr>>;

fn lean_ptr_to_level(ptr: *const c_void) -> Level {
    if lean_is_scalar(ptr) {
        return Level::Zero;
    }
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
        1 => {
            let [u] = ctor.objs().map(lean_ptr_to_level);
            Level::Succ(u.into())
        }
        2 => {
            let [u, v] = ctor.objs().map(lean_ptr_to_level);
            Level::Max(u.into(), v.into())
        }
        3 => {
            let [u, v] = ctor.objs().map(lean_ptr_to_level);
            Level::Imax(u.into(), v.into())
        }
        4 => {
            let [name] = ctor.objs().map(lean_ptr_to_name);
            Level::Param(name)
        }
        5 => {
            let [name] = ctor.objs().map(lean_ptr_to_name);
            Level::Mvar(name)
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_substring(ptr: *const c_void) -> Substring {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [str_ptr, start_pos_ptr, stop_pos_ptr] = ctor.objs();
    let str: &LeanStringObject = as_ref_unsafe(str_ptr.cast());
    let str = str.as_string();
    let start_pos = Nat::from_ptr(start_pos_ptr);
    let stop_pos = Nat::from_ptr(stop_pos_ptr);
    Substring {
        str,
        start_pos,
        stop_pos,
    }
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
        }
        1 => {
            let [pos_ptr, end_pos_ptr, canonical_ptr] = ctor.objs();
            let pos = Nat::from_ptr(pos_ptr);
            let end_pos = Nat::from_ptr(end_pos_ptr);
            let canonical = canonical_ptr as usize == 1;
            SourceInfo::Synthetic(pos, end_pos, canonical)
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_syntax_preresolved(ptr: *const c_void) -> SyntaxPreresolved {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
        0 => {
            let [name_ptr] = ctor.objs();
            let name = lean_ptr_to_name(name_ptr);
            SyntaxPreresolved::Namespace(name)
        }
        1 => {
            let [name_ptr, fields_ptr] = ctor.objs();
            let name = lean_ptr_to_name(name_ptr);
            let fields = collect_list(fields_ptr, |ptr| {
                let str: &LeanStringObject = as_ref_unsafe(ptr.cast());
                str.as_string()
            });
            SyntaxPreresolved::Decl(name, fields)
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_syntax(ptr: *const c_void) -> Syntax {
    if lean_is_scalar(ptr) {
        return Syntax::Missing;
    }
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
        1 => {
            let [info_ptr, kind_ptr, args_ptr] = ctor.objs();
            let info = lean_ptr_to_source_info(info_ptr);
            let kind = lean_ptr_to_name(kind_ptr);
            let args_array: &LeanArrayObject = as_ref_unsafe(args_ptr.cast());
            let args = args_array.to_vec(lean_ptr_to_syntax);
            Syntax::Node(info, kind, args)
        }
        2 => {
            let [info_ptr, val_ptr] = ctor.objs();
            let info = lean_ptr_to_source_info(info_ptr);
            let val_str: &LeanStringObject = as_ref_unsafe(val_ptr.cast());
            Syntax::Atom(info, val_str.as_string())
        }
        3 => {
            let [info_ptr, raw_val_ptr, val_ptr, preresolved_ptr] = ctor.objs();
            let info = lean_ptr_to_source_info(info_ptr);
            let raw_val = lean_ptr_to_substring(raw_val_ptr);
            let val = lean_ptr_to_name(val_ptr);
            let preresolved = collect_list(preresolved_ptr, lean_ptr_to_syntax_preresolved);
            Syntax::Ident(info, raw_val, val, preresolved)
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_name_data_value(ptr: *const c_void) -> (Name, DataValue) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [name_ptr, data_value_ptr] = ctor.objs();
    let name = lean_ptr_to_name(name_ptr);
    let data_value_ctor: &LeanCtorObject = as_ref_unsafe(data_value_ptr.cast());
    let [inner_ptr] = data_value_ctor.objs();
    let data_value = match data_value_ctor.tag() {
        0 => {
            let str: &LeanStringObject = as_ref_unsafe(inner_ptr.cast());
            DataValue::OfString(str.as_string())
        }
        1 => DataValue::OfBool(inner_ptr as usize == 1),
        2 => DataValue::OfName(lean_ptr_to_name(inner_ptr)),
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
        }
        5 => DataValue::OfSyntax(lean_ptr_to_syntax(inner_ptr).into()),
        _ => unreachable!(),
    };
    (name, data_value)
}

fn lean_ptr_to_expr(ptr: *const c_void, cache: &mut ExprCache) -> Arc<Expr> {
    if let Some(e) = cache.get(&ptr) {
        return e.clone();
    }
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let expr: Expr = match ctor.tag() {
        0 => {
            let [nat_ptr, hash_ptr] = ctor.objs();
            let nat = Nat::from_ptr(nat_ptr.cast());
            let hash = hash_ptr as u64;
            Expr::Bvar(nat, hash)
        }
        1 => {
            let [name_ptr, hash_ptr] = ctor.objs();
            let name = lean_ptr_to_name(name_ptr);
            let hash = hash_ptr as u64;
            Expr::Fvar(name, hash)
        }
        2 => {
            let [name_ptr, hash_ptr] = ctor.objs();
            let name = lean_ptr_to_name(name_ptr);
            let hash = hash_ptr as u64;
            Expr::Mvar(name, hash)
        }
        3 => {
            let [u_ptr, hash_ptr] = ctor.objs();
            let u = lean_ptr_to_level(u_ptr);
            let hash = hash_ptr as u64;
            Expr::Sort(u, hash)
        }
        4 => {
            let [name_ptr, levels_ptr, hash_ptr] = ctor.objs();
            let name = lean_ptr_to_name(name_ptr);
            let levels = collect_list(levels_ptr, lean_ptr_to_level);
            let hash = hash_ptr as u64;
            Expr::Const(name, levels, hash)
        }
        5 => {
            let [f_ptr, a_ptr, hash_ptr] = ctor.objs();
            let f = lean_ptr_to_expr(f_ptr, cache);
            let a = lean_ptr_to_expr(a_ptr, cache);
            let hash = hash_ptr as u64;
            Expr::App(f, a, hash)
        }
        6 => {
            let [
                binder_name_ptr,
                binder_typ_ptr,
                body_ptr,
                hash_ptr,
                binder_info_ptr,
            ] = ctor.objs();
            let binder_name = lean_ptr_to_name(binder_name_ptr);
            let binder_typ = lean_ptr_to_expr(binder_typ_ptr, cache);
            let body = lean_ptr_to_expr(body_ptr, cache);
            let hash = hash_ptr as u64;
            let binder_info = match binder_info_ptr as usize {
                0 => BinderInfo::Default,
                1 => BinderInfo::Implicit,
                2 => BinderInfo::StrictImplicit,
                3 => BinderInfo::InstImplicit,
                _ => unreachable!(),
            };
            Expr::Lam(binder_name, binder_typ, body, binder_info, hash)
        }
        7 => {
            let [
                binder_name_ptr,
                binder_typ_ptr,
                body_ptr,
                hash_ptr,
                binder_info_ptr,
            ] = ctor.objs();
            let binder_name = lean_ptr_to_name(binder_name_ptr);
            let binder_typ = lean_ptr_to_expr(binder_typ_ptr, cache);
            let body = lean_ptr_to_expr(body_ptr, cache);
            let hash = hash_ptr as u64;
            let binder_info = match binder_info_ptr as usize {
                0 => BinderInfo::Default,
                1 => BinderInfo::Implicit,
                2 => BinderInfo::StrictImplicit,
                3 => BinderInfo::InstImplicit,
                _ => unreachable!(),
            };
            Expr::ForallE(binder_name, binder_typ, body, binder_info, hash)
        }
        8 => {
            let [
                decl_name_ptr,
                typ_ptr,
                value_ptr,
                body_ptr,
                hash_ptr,
                nondep_ptr,
            ] = ctor.objs();
            let decl_name = lean_ptr_to_name(decl_name_ptr);
            let typ = lean_ptr_to_expr(typ_ptr, cache);
            let value = lean_ptr_to_expr(value_ptr, cache);
            let body = lean_ptr_to_expr(body_ptr, cache);
            let hash = hash_ptr as u64;
            let nondep = nondep_ptr as usize == 1;
            Expr::LetE(decl_name, typ, value, body, nondep, hash)
        }
        9 => {
            let [literal_ptr, hash_ptr] = ctor.objs();
            let literal: &LeanCtorObject = as_ref_unsafe(literal_ptr.cast());
            let [inner_ptr] = literal.objs();
            let hash = hash_ptr as u64;
            match literal.tag() {
                0 => {
                    let nat = Nat::from_ptr(inner_ptr);
                    Expr::Lit(Literal::NatVal(nat), hash)
                }
                1 => {
                    let str: &LeanStringObject = as_ref_unsafe(inner_ptr.cast());
                    Expr::Lit(Literal::StrVal(str.as_string()), hash)
                }
                _ => unreachable!(),
            }
        }
        10 => {
            let [data_ptr, expr_ptr, hash_ptr] = ctor.objs();
            let kv_map = collect_list(data_ptr, lean_ptr_to_name_data_value);
            let expr = lean_ptr_to_expr(expr_ptr, cache);
            let hash = hash_ptr as u64;
            Expr::Mdata(kv_map, expr, hash)
        }
        11 => {
            let [typ_name_ptr, idx_ptr, struct_ptr, hash_ptr] = ctor.objs();
            let typ_name = lean_ptr_to_name(typ_name_ptr);
            let idx = Nat::from_ptr(idx_ptr);
            let struct_expr = lean_ptr_to_expr(struct_ptr, cache);
            let hash = hash_ptr as u64;
            Expr::Proj(typ_name, idx, struct_expr, hash)
        }
        _ => unreachable!(),
    };
    let expr_arc = Arc::new(expr);
    cache.insert(ptr, expr_arc.clone());
    expr_arc
}

fn lean_ptr_to_recursor_rule(ptr: *const c_void, cache: &mut ExprCache) -> RecursorRule {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [ctor_ptr, n_fields_ptr, rhs_ptr] = ctor.objs();
    let ctor = lean_ptr_to_name(ctor_ptr);
    let n_fields = Nat::from_ptr(n_fields_ptr);
    let rhs = lean_ptr_to_expr(rhs_ptr, cache);
    RecursorRule {
        ctor,
        n_fields,
        rhs,
    }
}

fn lean_ptr_to_constant_val(ptr: *const c_void, cache: &mut ExprCache) -> ConstantVal {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [name_ptr, level_params_ptr, typ_ptr] = ctor.objs();
    let name = lean_ptr_to_name(name_ptr);
    let level_params = collect_list(level_params_ptr, lean_ptr_to_name);
    let typ = lean_ptr_to_expr(typ_ptr, cache);
    ConstantVal {
        name,
        level_params,
        typ,
    }
}

fn lean_ptr_to_constant_info(ptr: *const c_void, cache: &mut ExprCache) -> ConstantInfo {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [inner_val_ptr] = ctor.objs();
    let inner_val: &LeanCtorObject = as_ref_unsafe(inner_val_ptr.cast());
    match ctor.tag() {
        0 => {
            let [constant_val_ptr, is_unsafe_ptr] = inner_val.objs();
            let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
            let is_unsafe = is_unsafe_ptr as usize == 1;
            let axiom_val = AxiomVal {
                constant_val,
                is_unsafe,
            };
            ConstantInfo::AxiomInfo(axiom_val)
        }
        1 => {
            let [constant_val_ptr, value_ptr, hints_ptr, all_ptr, safety_ptr] = inner_val.objs();
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
            let all = collect_list(all_ptr, lean_ptr_to_name);
            let safety = match safety_ptr as usize {
                0 => DefinitionSafety::Unsafe,
                1 => DefinitionSafety::Safe,
                2 => DefinitionSafety::Partial,
                _ => unreachable!(),
            };
            ConstantInfo::DefnInfo(DefinitionVal {
                constant_val,
                value,
                hints,
                safety,
                all,
            })
        }
        2 => {
            let [constant_val_ptr, value_ptr, all_ptr] = inner_val.objs();
            let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
            let value = lean_ptr_to_expr(value_ptr, cache);
            let all = collect_list(all_ptr, lean_ptr_to_name);
            ConstantInfo::ThmInfo(TheoremVal {
                constant_val,
                value,
                all,
            })
        }
        3 => {
            let [constant_val_ptr, value_ptr, all_ptr, is_unsafe_ptr] = inner_val.objs();
            let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
            let value = lean_ptr_to_expr(value_ptr, cache);
            let all = collect_list(all_ptr, lean_ptr_to_name);
            let is_unsafe = is_unsafe_ptr as usize == 1;
            ConstantInfo::OpaqueInfo(OpaqueVal {
                constant_val,
                value,
                is_unsafe,
                all,
            })
        }
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
            ConstantInfo::QuotInfo(QuotVal { constant_val, kind })
        }
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
            let all = collect_list(all_ptr, lean_ptr_to_name);
            let ctors = collect_list(ctors_ptr, lean_ptr_to_name);
            let num_nested = Nat::from_ptr(num_nested_ptr);
            let [is_rec, is_unsafe, is_reflexive, ..] =
                (bools_ptr as usize).to_le_bytes().map(|b| b == 1);
            ConstantInfo::InductInfo(InductiveVal {
                constant_val,
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_unsafe,
                is_reflexive,
            })
        }
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
            let induct = lean_ptr_to_name(induct_ptr);
            let cidx = Nat::from_ptr(cidx_ptr);
            let num_params = Nat::from_ptr(num_params_ptr);
            let num_fields = Nat::from_ptr(num_fields_ptr);
            let is_unsafe = is_unsafe_ptr as usize == 1;
            ConstantInfo::CtorInfo(ConstructorVal {
                constant_val,
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            })
        }
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
            let all = collect_list(all_ptr, lean_ptr_to_name);
            let num_params = Nat::from_ptr(num_params_ptr);
            let num_indices = Nat::from_ptr(num_indices_ptr);
            let num_motives = Nat::from_ptr(num_motives_ptr);
            let num_minors = Nat::from_ptr(num_minors_ptr);
            let rules = collect_list_with(rules_ptr, lean_ptr_to_recursor_rule, cache);
            let [k, is_unsafe, ..] = (bools_ptr as usize).to_le_bytes().map(|b| b == 1);
            ConstantInfo::RecInfo(RecursorVal {
                constant_val,
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
            })
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_name(ptr: *const c_void) -> Name {
    if lean_is_scalar(ptr) {
        return Name::Anonymous;
    }
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [pre_ptr, pos_ptr] = ctor.objs();
    let pre = lean_ptr_to_name(pre_ptr).into();
    match ctor.tag() {
        1 => {
            let str_obj: &LeanStringObject = as_ref_unsafe(pos_ptr.cast());
            Name::Str(pre, str_obj.as_string())
        }
        2 => Name::Num(pre, Nat::from_ptr(pos_ptr)),
        _ => unreachable!(),
    }
}

fn lean_ptr_to_name_constant_info(
    ptr: *const c_void,
    cache: &mut ExprCache,
) -> (Name, ConstantInfo) {
    let prod_ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [name_ptr, constant_info_ptr] = prod_ctor.objs();
    let name = lean_ptr_to_name(name_ptr);
    let constant_info = lean_ptr_to_constant_info(constant_info_ptr, cache);
    (name, constant_info)
}

fn lean_ptr_to_const_map(ptr: *const c_void) -> ConstMap {
    let array: &LeanArrayObject = as_ref_unsafe(ptr.cast());
    let mut cache = ExprCache::default();
    let pairs = array.to_vec_with(lean_ptr_to_name_constant_info, &mut cache);
    ConstMap::from_iter(pairs)
}

#[unsafe(no_mangle)]
fn rs_tmp_decode_const_map(ptr: *const c_void) -> usize {
    let map = lean_ptr_to_const_map(ptr);
    map.len()
}
