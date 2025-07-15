// TODO: remove
#![allow(dead_code)]

use p3_field::integers::QuotientMap;
use p3_goldilocks::Goldilocks as G;
use std::ffi::c_void;

use crate::{
    aiur2::bytecode::{Block, CircuitLayout, Ctrl, Function, FxIndexMap, Op, Toplevel, ValIdx},
    lean::{
        array::LeanArrayObject,
        ctor::LeanCtorObject,
        ffi::{as_ref_unsafe, lean_is_scalar},
    },
    lean_unbox,
};

fn lean_unbox_nat_as_usize(ptr: *const c_void) -> usize {
    assert!(lean_is_scalar(ptr));
    lean_unbox!(usize, ptr)
}

fn lean_unbox_nat_as_g(ptr: *const c_void) -> G {
    assert!(lean_is_scalar(ptr));
    unsafe { G::from_canonical_unchecked(lean_unbox!(u64, ptr)) }
}

fn lean_ptr_to_vec_val_idx(ptr: *const c_void) -> Vec<ValIdx> {
    let array: &LeanArrayObject = as_ref_unsafe(ptr.cast());
    array.to_vec(lean_unbox_nat_as_usize)
}

fn lean_ptr_to_op(ptr: *const c_void) -> Op {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
        0 => {
            let [const_val_ptr] = ctor.objs();
            Op::Const(lean_unbox_nat_as_g(const_val_ptr))
        }
        1 => {
            let [a_ptr, b_ptr] = ctor.objs();
            Op::Add(
                lean_unbox_nat_as_usize(a_ptr),
                lean_unbox_nat_as_usize(b_ptr),
            )
        }
        2 => {
            let [a_ptr, b_ptr] = ctor.objs();
            Op::Sub(
                lean_unbox_nat_as_usize(a_ptr),
                lean_unbox_nat_as_usize(b_ptr),
            )
        }
        3 => {
            let [a_ptr, b_ptr] = ctor.objs();
            Op::Mul(
                lean_unbox_nat_as_usize(a_ptr),
                lean_unbox_nat_as_usize(b_ptr),
            )
        }
        4 => {
            let [fun_idx_ptr, val_idxs_ptr] = ctor.objs();
            let fun_idx = lean_unbox_nat_as_usize(fun_idx_ptr);
            let val_idxs = lean_ptr_to_vec_val_idx(val_idxs_ptr);
            Op::Call(fun_idx, val_idxs)
        }
        5 => {
            let [val_idxs_ptr] = ctor.objs();
            Op::Store(lean_ptr_to_vec_val_idx(val_idxs_ptr))
        }
        6 => {
            let [width_ptr, val_idx_ptr] = ctor.objs();
            Op::Load(
                lean_unbox_nat_as_usize(width_ptr),
                lean_unbox_nat_as_usize(val_idx_ptr),
            )
        }
        _ => unreachable!(),
    }
}

fn lean_ptr_to_g_block_pair(ptr: *const c_void) -> (G, Block) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [g_ptr, block_ptr] = ctor.objs();
    let g = lean_unbox_nat_as_g(g_ptr);
    let block = lean_ctor_to_block(as_ref_unsafe(block_ptr.cast()));
    (g, block)
}

fn lean_ctor_to_ctrl(ctor: &LeanCtorObject) -> Ctrl {
    match ctor.tag() {
        0 => {
            let [val_idx_ptr, cases_ptr, default_ptr] = ctor.objs();
            let val_idx = lean_unbox_nat_as_usize(val_idx_ptr);
            let cases_array: &LeanArrayObject = as_ref_unsafe(cases_ptr.cast());
            let vec_cases = cases_array.to_vec(lean_ptr_to_g_block_pair);
            let cases = FxIndexMap::from_iter(vec_cases);
            let default = if lean_is_scalar(default_ptr) {
                None
            } else {
                let default_ctor: &LeanCtorObject = as_ref_unsafe(default_ptr.cast());
                let [block_ptr] = default_ctor.objs();
                let block = lean_ctor_to_block(as_ref_unsafe(block_ptr.cast()));
                Some(Box::new(block))
            };
            Ctrl::Match(val_idx, cases, default)
        }
        1 => {
            let [sel_idx_ptr, val_idxs_ptr] = ctor.objs();
            let sel_idx = lean_unbox_nat_as_usize(sel_idx_ptr);
            let val_idxs = lean_ptr_to_vec_val_idx(val_idxs_ptr);
            Ctrl::Return(sel_idx, val_idxs)
        }
        _ => unreachable!(),
    }
}

fn lean_ctor_to_block(ctor: &LeanCtorObject) -> Block {
    let [
        ops_ptr,
        ctrl_ptr,
        min_sel_included_ptr,
        max_sel_excluded_ptr,
    ] = ctor.objs();
    let ops_array: &LeanArrayObject = as_ref_unsafe(ops_ptr.cast());
    let ops = ops_array.to_vec(lean_ptr_to_op);
    let ctrl = lean_ctor_to_ctrl(as_ref_unsafe(ctrl_ptr.cast()));
    let min_sel_included = lean_unbox_nat_as_usize(min_sel_included_ptr);
    let max_sel_excluded = lean_unbox_nat_as_usize(max_sel_excluded_ptr);
    Block {
        ops,
        ctrl,
        min_sel_included,
        max_sel_excluded,
    }
}

fn lean_ctor_to_circuit_layout(ctor: &LeanCtorObject) -> CircuitLayout {
    let [selectors_ptr, auxiliaries_ptr, shared_constraints_ptr] = ctor.objs();
    CircuitLayout {
        selectors: lean_unbox_nat_as_usize(selectors_ptr),
        auxiliaries: lean_unbox_nat_as_usize(auxiliaries_ptr),
        shared_constraints: lean_unbox_nat_as_usize(shared_constraints_ptr),
    }
}

fn lean_ptr_to_function(ptr: *const c_void) -> Function {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [
        input_size_ptr,
        output_size_ptr,
        body_ptr,
        circuit_layout_ptr,
    ] = ctor.objs();
    let input_size = lean_unbox_nat_as_usize(input_size_ptr);
    let output_size = lean_unbox_nat_as_usize(output_size_ptr);
    let body = lean_ctor_to_block(as_ref_unsafe(body_ptr.cast()));
    let circuit_layout = lean_ctor_to_circuit_layout(as_ref_unsafe(circuit_layout_ptr.cast()));
    Function {
        input_size,
        output_size,
        body,
        circuit_layout,
    }
}

fn lean_ctor_to_toplevel(ctor: &LeanCtorObject) -> Toplevel {
    let [functions_ptr, memory_widths_ptr] = ctor.objs();
    let functions_array: &LeanArrayObject = as_ref_unsafe(functions_ptr.cast());
    let functions = functions_array.to_vec(lean_ptr_to_function);
    let memory_widths_array: &LeanArrayObject = as_ref_unsafe(memory_widths_ptr.cast());
    let memory_widths = memory_widths_array.to_vec(lean_unbox_nat_as_usize);
    Toplevel {
        functions,
        memory_widths,
    }
}
