use blake3::Hash;
use num_bigint::BigUint;
use std::ffi::c_void;

use crate::{
    ixon::{
        Ixon,
        address::Address,
        claim::{CheckClaim, Claim, Env, EvalClaim, Proof},
        constant::{
            Axiom, Comm, Constructor, ConstructorProj, DefKind, DefSafety, Definition,
            DefinitionProj, Inductive, InductiveProj, QuotKind, Quotient, Recursor, RecursorProj,
            RecursorRule,
        },
        meta::{BinderInfo, Metadata, Metadatum, ReducibilityHints},
        name::{Name, NamePart},
        nat::Nat,
        serialize::Serialize,
        univ::Univ,
    },
    lean::{
        array::LeanArrayObject, as_ref_unsafe, ctor::LeanCtorObject, lean_is_scalar,
        lean_unbox_u32, sarray::LeanSArrayObject, string::LeanStringObject,
    },
    lean_unbox,
};

fn lean_ctor_to_univ(ctor: &LeanCtorObject) -> Univ {
    match ctor.tag() {
        0 => {
            let [val] = ctor.objs();
            Univ::Const(val as u64)
        }
        1 => {
            let [idx] = ctor.objs();
            Univ::Var(idx as u64)
        }
        2 => {
            let [b_ptr, a_idx] = ctor.objs();
            let a_idx = a_idx as u64;
            let b = lean_ctor_to_univ(as_ref_unsafe(b_ptr.cast()));
            Univ::Add(a_idx, b.into())
        }
        3 => {
            let [a_ptr, b_ptr] = ctor.objs();
            let a = lean_ctor_to_univ(as_ref_unsafe(a_ptr.cast()));
            let b = lean_ctor_to_univ(as_ref_unsafe(b_ptr.cast()));
            Univ::Max(a.into(), b.into())
        }
        4 => {
            let [a_ptr, b_ptr] = ctor.objs();
            let a = lean_ctor_to_univ(as_ref_unsafe(a_ptr.cast()));
            let b = lean_ctor_to_univ(as_ref_unsafe(b_ptr.cast()));
            Univ::IMax(a.into(), b.into())
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_address(ptr: *const c_void) -> Address {
    let sarray: &LeanSArrayObject = as_ref_unsafe(ptr.cast());
    let hash = Hash::from_slice(sarray.data()).unwrap();
    Address { hash }
}

fn lean_ptr_to_univs(ptr: *const c_void) -> Vec<Univ> {
    let univs: &LeanArrayObject = as_ref_unsafe(ptr.cast());
    univs.to_vec(|ptr| lean_ctor_to_univ(as_ref_unsafe(ptr.cast())))
}

fn lean_ptr_to_nat(ptr: *const c_void) -> Nat {
    let nat_bytes: &LeanSArrayObject = as_ref_unsafe(ptr.cast());
    Nat(BigUint::from_bytes_le(nat_bytes.data()))
}

fn lean_ptr_to_definition(ptr: *const c_void) -> Definition {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [lvls, typ, value, mode_safety] = ctor.objs();
    let lvls = lean_ptr_to_nat(lvls);
    let typ = lean_ptr_to_address(typ);
    let value = lean_ptr_to_address(value);
    let [kind, safety, ..] = (mode_safety as usize).to_le_bytes();
    let kind = match kind {
        0 => DefKind::Definition,
        1 => DefKind::Opaque,
        2 => DefKind::Theorem,
        _ => unreachable!(),
    };
    let safety = match safety {
        0 => DefSafety::Unsafe,
        1 => DefSafety::Safe,
        2 => DefSafety::Partial,
        _ => unreachable!(),
    };
    Definition {
        lvls,
        typ,
        kind,
        value,
        safety,
    }
}

fn lean_ptr_to_constructor(ptr: *const c_void) -> Constructor {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [lvls, typ, cidx, params, fields, is_unsafe] = ctor.objs();
    let lvls = lean_ptr_to_nat(lvls);
    let typ = lean_ptr_to_address(typ);
    let cidx = lean_ptr_to_nat(cidx);
    let params = lean_ptr_to_nat(params);
    let fields = lean_ptr_to_nat(fields);
    let is_unsafe = is_unsafe as usize == 1;
    Constructor {
        lvls,
        typ,
        cidx,
        params,
        fields,
        is_unsafe,
    }
}

fn lean_ptr_to_recursor_rule(ptr: *const c_void) -> RecursorRule {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [fields, rhs] = ctor.objs();
    let fields = lean_ptr_to_nat(fields);
    let rhs = lean_ptr_to_address(rhs);
    RecursorRule { fields, rhs }
}

fn lean_ptr_to_recursor(ptr: *const c_void) -> Recursor {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [
        lvls,
        typ,
        params,
        indices,
        motives,
        minors,
        rules,
        k_isunsafe,
    ] = ctor.objs();
    let lvls = lean_ptr_to_nat(lvls);
    let typ = lean_ptr_to_address(typ);
    let params = lean_ptr_to_nat(params);
    let indices = lean_ptr_to_nat(indices);
    let motives = lean_ptr_to_nat(motives);
    let minors = lean_ptr_to_nat(minors);
    let rules: &LeanArrayObject = as_ref_unsafe(rules.cast());
    let rules = rules.to_vec(lean_ptr_to_recursor_rule);
    let [k, is_unsafe, ..] = (k_isunsafe as usize).to_le_bytes();
    let k = k == 1;
    let is_unsafe = is_unsafe == 1;
    Recursor {
        lvls,
        typ,
        params,
        indices,
        motives,
        minors,
        rules,
        k,
        is_unsafe,
    }
}

fn lean_ptr_to_inductive(ptr: *const c_void) -> Inductive {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [
        lvls,
        typ,
        params,
        indices,
        ctors,
        recrs,
        nested,
        recr_refl_isunsafe,
    ] = ctor.objs();
    let lvls = lean_ptr_to_nat(lvls);
    let typ = lean_ptr_to_address(typ);
    let params = lean_ptr_to_nat(params);
    let indices = lean_ptr_to_nat(indices);
    let ctors: &LeanArrayObject = as_ref_unsafe(ctors.cast());
    let ctors = ctors.to_vec(lean_ptr_to_constructor);
    let recrs: &LeanArrayObject = as_ref_unsafe(recrs.cast());
    let recrs = recrs.to_vec(lean_ptr_to_recursor);
    let nested = lean_ptr_to_nat(nested);
    let [recr, refl, is_unsafe, ..] = (recr_refl_isunsafe as usize).to_le_bytes();
    let recr = recr == 1;
    let refl = refl == 1;
    let is_unsafe = is_unsafe == 1;
    Inductive {
        lvls,
        typ,
        params,
        indices,
        ctors,
        recrs,
        nested,
        recr,
        refl,
        is_unsafe,
    }
}

fn lean_ptr_to_name_parts(ptr: *const c_void) -> Vec<NamePart> {
    if lean_is_scalar(ptr) {
        Vec::new()
    } else {
        let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
        match ctor.tag() {
            1 => {
                let [prefix_ptr, str_ptr] = ctor.objs();
                let mut parts = lean_ptr_to_name_parts(prefix_ptr);
                let str_obj: &LeanStringObject = as_ref_unsafe(str_ptr.cast());
                parts.push(NamePart::Str(str_obj.as_string()));
                parts
            }
            2 => {
                let [prefix_ptr, num_ptr] = ctor.objs();
                let mut parts = lean_ptr_to_name_parts(prefix_ptr);
                parts.push(NamePart::Num(lean_ptr_to_nat(num_ptr)));
                parts
            }
            _ => unreachable!(),
        }
    }
}

fn lean_ptr_to_name(ptr: *const c_void) -> Name {
    let mut parts = lean_ptr_to_name_parts(ptr);
    parts.reverse();
    Name { parts }
}

fn lean_ptr_to_metadatum(ptr: *const c_void) -> Metadatum {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
        0 => {
            let [name] = ctor.objs();
            let name = lean_ptr_to_name(name);
            Metadatum::Name(name)
        }
        1 => {
            let [info] = ctor.objs();
            let info = match info as usize {
                0 => BinderInfo::Default,
                1 => BinderInfo::Implicit,
                2 => BinderInfo::StrictImplicit,
                3 => BinderInfo::InstImplicit,
                _ => unreachable!(),
            };
            Metadatum::Info(info)
        }
        2 => {
            let [addr] = ctor.objs();
            let addr = lean_ptr_to_address(addr);
            Metadatum::Link(addr)
        }
        3 => {
            let [hints] = ctor.objs();
            let hints = if lean_is_scalar(hints) {
                match lean_unbox!(usize, hints) {
                    0 => ReducibilityHints::Opaque,
                    1 => ReducibilityHints::Abbrev,
                    _ => unreachable!(),
                }
            } else {
                let ctor: &LeanCtorObject = as_ref_unsafe(hints.cast());
                let [x] = ctor.objs();
                let x = lean_unbox_u32(x);
                ReducibilityHints::Regular(x)
            };
            Metadatum::Hints(hints)
        }
        4 => {
            let [all] = ctor.objs();
            let all: &LeanArrayObject = as_ref_unsafe(all.cast());
            let all = all.to_vec(lean_ptr_to_name);
            Metadatum::All(all)
        }
        5 => {
            let [mut_ctx] = ctor.objs();
            let mut_ctx: &LeanArrayObject = as_ref_unsafe(mut_ctx.cast());
            let mut_ctx = mut_ctx.to_vec(|names| {
                let names: &LeanArrayObject = as_ref_unsafe(names.cast());
                names.to_vec(lean_ptr_to_name)
            });
            Metadatum::MutCtx(mut_ctx)
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_metadata_entry(ptr: *const c_void) -> (Nat, Vec<Metadatum>) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [fst, snd] = ctor.objs();
    let fst = lean_ptr_to_nat(fst);
    let snd: &LeanArrayObject = as_ref_unsafe(snd.cast());
    let snd = snd.to_vec(lean_ptr_to_metadatum);
    (fst, snd)
}

fn lean_ptr_to_env_entry(ptr: *const c_void) -> (Address, Address) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [fst, snd] = ctor.objs().map(lean_ptr_to_address);
    (fst, snd)
}

fn lean_ptr_to_eval_claim(ptr: *const c_void) -> EvalClaim {
    let evals: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [lvls, input, output, typ] = evals.objs().map(lean_ptr_to_address);
    EvalClaim {
        lvls,
        typ,
        input,
        output,
    }
}

fn lean_ptr_to_check_claim(ptr: *const c_void) -> CheckClaim {
    let checks: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [lvls, typ, value] = checks.objs().map(lean_ptr_to_address);
    CheckClaim { lvls, typ, value }
}

fn lean_ptr_to_ixon(ptr: *const c_void) -> Ixon {
    lean_ctor_to_ixon(as_ref_unsafe(ptr.cast()))
}

fn lean_ctor_to_ixon(ctor: &LeanCtorObject) -> Ixon {
    match ctor.tag() {
        0 => {
            let [idx] = ctor.objs();
            Ixon::Vari(idx as u64)
        }
        1 => {
            let [univ_ptr] = ctor.objs();
            let univ_ctor = as_ref_unsafe(univ_ptr.cast());
            Ixon::Sort(lean_ctor_to_univ(univ_ctor).into())
        }
        2 => {
            let [addr_ptr, univs_ptr] = ctor.objs();
            let addr = lean_ptr_to_address(addr_ptr);
            Ixon::Refr(addr, lean_ptr_to_univs(univs_ptr))
        }
        3 => {
            let [univs_ptr, idx] = ctor.objs();
            Ixon::Recr(idx as u64, lean_ptr_to_univs(univs_ptr))
        }
        4 => {
            let [f, x, xs] = ctor.objs();
            let f = lean_ptr_to_ixon(f).into();
            let x = lean_ptr_to_ixon(x).into();
            let xs_array: &LeanArrayObject = as_ref_unsafe(xs.cast());
            let xs = xs_array.to_vec(lean_ptr_to_ixon);
            Ixon::Apps(f, x, xs)
        }
        5 => {
            let [xs, x] = ctor.objs();
            let xs_array: &LeanArrayObject = as_ref_unsafe(xs.cast());
            let xs = xs_array.to_vec(lean_ptr_to_ixon);
            let x = lean_ptr_to_ixon(x);
            Ixon::Lams(xs, x.into())
        }
        6 => {
            let [xs, x] = ctor.objs();
            let xs_array: &LeanArrayObject = as_ref_unsafe(xs.cast());
            let xs = xs_array.to_vec(lean_ptr_to_ixon);
            let x = lean_ptr_to_ixon(x).into();
            Ixon::Alls(xs, x)
        }
        7 => {
            let [addr_ptr, ptr, idx] = ctor.objs();
            let addr = lean_ptr_to_address(addr_ptr);
            let term = lean_ptr_to_ixon(ptr).into();
            Ixon::Proj(addr, idx as u64, term)
        }
        8 => {
            let [str_ptr] = ctor.objs();
            let str: &LeanStringObject = as_ref_unsafe(str_ptr.cast());
            Ixon::Strl(str.as_string())
        }
        9 => {
            let [nat_bytes_ptr] = ctor.objs();
            Ixon::Natl(lean_ptr_to_nat(nat_bytes_ptr))
        }
        10 => {
            let [v, t, b, x] = ctor.objs();
            let v = lean_ptr_to_ixon(v).into();
            let t = lean_ptr_to_ixon(t).into();
            let b = lean_ptr_to_ixon(b).into();
            Ixon::LetE(x as usize == 1, v, t, b)
        }
        11 => {
            let [xs] = ctor.objs();
            let xs: &LeanArrayObject = as_ref_unsafe(xs.cast());
            Ixon::List(xs.to_vec(lean_ptr_to_ixon))
        }
        12 => {
            let [defn_ptr] = ctor.objs();
            Ixon::Defn(lean_ptr_to_definition(defn_ptr))
        }
        13 => {
            let [axio_ptr] = ctor.objs();
            let axio_ctor: &LeanCtorObject = as_ref_unsafe(axio_ptr.cast());
            let [lvls, typ, is_unsafe] = axio_ctor.objs();
            let lvls = lean_ptr_to_nat(lvls);
            let typ = lean_ptr_to_address(typ);
            let is_unsafe = is_unsafe as usize == 1;
            Ixon::Axio(Axiom {
                lvls,
                typ,
                is_unsafe,
            })
        }
        14 => {
            let [quot_ptr] = ctor.objs();
            let quot_ctor: &LeanCtorObject = as_ref_unsafe(quot_ptr.cast());
            let [lvls, typ, kind] = quot_ctor.objs();
            let lvls = lean_ptr_to_nat(lvls);
            let typ = lean_ptr_to_address(typ);
            let kind = match kind as usize {
                0 => QuotKind::Type,
                1 => QuotKind::Ctor,
                2 => QuotKind::Lift,
                3 => QuotKind::Ind,
                _ => unreachable!(),
            };
            Ixon::Quot(Quotient { lvls, typ, kind })
        }
        15 => {
            let [cprj_ptr] = ctor.objs();
            let cprj_ctor: &LeanCtorObject = as_ref_unsafe(cprj_ptr.cast());
            let [block, idx, cidx] = cprj_ctor.objs();
            let block = lean_ptr_to_address(block);
            let idx = lean_ptr_to_nat(idx);
            let cidx = lean_ptr_to_nat(cidx);
            Ixon::CPrj(ConstructorProj { block, idx, cidx })
        }
        16 => {
            let [rprj_ptr] = ctor.objs();
            let rprj_ctor: &LeanCtorObject = as_ref_unsafe(rprj_ptr.cast());
            let [block, idx, ridx] = rprj_ctor.objs();
            let block = lean_ptr_to_address(block);
            let idx = lean_ptr_to_nat(idx);
            let ridx = lean_ptr_to_nat(ridx);
            Ixon::RPrj(RecursorProj { block, idx, ridx })
        }
        17 => {
            let [iprj_ptr] = ctor.objs();
            let iprj_ctor: &LeanCtorObject = as_ref_unsafe(iprj_ptr.cast());
            let [block, idx] = iprj_ctor.objs();
            let block = lean_ptr_to_address(block);
            let idx = lean_ptr_to_nat(idx);
            Ixon::IPrj(InductiveProj { block, idx })
        }
        18 => {
            let [dprj_ptr] = ctor.objs();
            let dprj_ctor: &LeanCtorObject = as_ref_unsafe(dprj_ptr.cast());
            let [block, idx] = dprj_ctor.objs();
            let block = lean_ptr_to_address(block);
            let idx = lean_ptr_to_nat(idx);
            Ixon::DPrj(DefinitionProj { block, idx })
        }
        19 => {
            let [inds_ptr] = ctor.objs();
            let inds: &LeanArrayObject = as_ref_unsafe(inds_ptr.cast());
            let inds = inds.to_vec(lean_ptr_to_inductive);
            Ixon::Inds(inds)
        }
        20 => {
            let [defs_ptr] = ctor.objs();
            let defs: &LeanArrayObject = as_ref_unsafe(defs_ptr.cast());
            let defs = defs.to_vec(lean_ptr_to_definition);
            Ixon::Defs(defs)
        }
        21 => {
            let [pairs_ptr] = ctor.objs();
            let pairs: &LeanArrayObject = as_ref_unsafe(pairs_ptr.cast());
            let map = pairs.to_vec(lean_ptr_to_metadata_entry);
            Ixon::Meta(Metadata { map })
        }
        22 => {
            let [proof] = ctor.objs();
            let proof: &LeanCtorObject = as_ref_unsafe(proof.cast());
            let [claim, bin] = proof.objs();
            let claim: &LeanCtorObject = as_ref_unsafe(claim.cast());
            let claim = match claim.tag() {
                0 => {
                    let [evals] = claim.objs();
                    Claim::Evals(lean_ptr_to_eval_claim(evals))
                }
                1 => {
                    let [checks] = claim.objs();
                    Claim::Checks(lean_ptr_to_check_claim(checks))
                }
                _ => unreachable!(),
            };
            let bin: &LeanSArrayObject = as_ref_unsafe(bin.cast());
            Ixon::Prof(Proof {
                claim,
                proof: bin.data().to_vec(),
            })
        }
        23 => {
            let [evals] = ctor.objs();
            Ixon::Eval(lean_ptr_to_eval_claim(evals))
        }
        24 => {
            let [checks] = ctor.objs();
            Ixon::Chck(lean_ptr_to_check_claim(checks))
        }
        25 => {
            let [comm] = ctor.objs();
            let comm: &LeanCtorObject = as_ref_unsafe(comm.cast());
            let [secret, payload] = comm.objs().map(lean_ptr_to_address);
            Ixon::Comm(Comm { secret, payload })
        }
        26 => {
            let [map_ptr] = ctor.objs();
            let map: &LeanArrayObject = as_ref_unsafe(map_ptr.cast());
            let env = map.to_vec(lean_ptr_to_env_entry);
            Ixon::Envn(Env { env })
        }
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_eq_lean_rust_serialization(
    ixon: &LeanCtorObject,
    bytes: &LeanSArrayObject,
) -> bool {
    let mut buf = Vec::new();
    lean_ctor_to_ixon(ixon).put(&mut buf);
    buf == bytes.data()
}
