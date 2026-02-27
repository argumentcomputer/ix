use std::ffi::c_void;

use multi_stark::p3_field::PrimeCharacteristicRing;

use crate::{
  FxIndexMap,
  aiur::{
    G,
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel, ValIdx},
  },
  lean::{
    ffi::aiur::{lean_unbox_g, lean_unbox_nat_as_usize},
    lean_array_to_vec, lean_ctor_objs, lean_is_scalar, lean_obj_to_string,
    lean_tag,
  },
};

fn lean_ptr_to_vec_val_idx(ptr: *const c_void) -> Vec<ValIdx> {
  lean_array_to_vec(ptr, lean_unbox_nat_as_usize)
}

fn lean_ptr_to_op(ptr: *const c_void) -> Op {
  match lean_tag(ptr) {
    0 => {
      let [const_val_ptr] = lean_ctor_objs(ptr);
      Op::Const(G::from_u64(const_val_ptr as u64))
    },
    1 => {
      let [a_ptr, b_ptr] = lean_ctor_objs(ptr);
      Op::Add(lean_unbox_nat_as_usize(a_ptr), lean_unbox_nat_as_usize(b_ptr))
    },
    2 => {
      let [a_ptr, b_ptr] = lean_ctor_objs(ptr);
      Op::Sub(lean_unbox_nat_as_usize(a_ptr), lean_unbox_nat_as_usize(b_ptr))
    },
    3 => {
      let [a_ptr, b_ptr] = lean_ctor_objs(ptr);
      Op::Mul(lean_unbox_nat_as_usize(a_ptr), lean_unbox_nat_as_usize(b_ptr))
    },
    4 => {
      let [a_ptr] = lean_ctor_objs(ptr);
      Op::EqZero(lean_unbox_nat_as_usize(a_ptr))
    },
    5 => {
      let [fun_idx_ptr, val_idxs_ptr, output_size_ptr] = lean_ctor_objs(ptr);
      let fun_idx = lean_unbox_nat_as_usize(fun_idx_ptr);
      let val_idxs = lean_ptr_to_vec_val_idx(val_idxs_ptr);
      let output_size = lean_unbox_nat_as_usize(output_size_ptr);
      Op::Call(fun_idx, val_idxs, output_size)
    },
    6 => {
      let [val_idxs_ptr] = lean_ctor_objs(ptr);
      Op::Store(lean_ptr_to_vec_val_idx(val_idxs_ptr))
    },
    7 => {
      let [width_ptr, val_idx_ptr] = lean_ctor_objs(ptr);
      Op::Load(
        lean_unbox_nat_as_usize(width_ptr),
        lean_unbox_nat_as_usize(val_idx_ptr),
      )
    },
    8 => {
      let [as_ptr, bs_ptr] = lean_ctor_objs(ptr);
      Op::AssertEq(
        lean_ptr_to_vec_val_idx(as_ptr),
        lean_ptr_to_vec_val_idx(bs_ptr),
      )
    },
    9 => {
      let [key_ptr] = lean_ctor_objs(ptr);
      Op::IOGetInfo(lean_ptr_to_vec_val_idx(key_ptr))
    },
    10 => {
      let [key_ptr, idx_ptr, len_ptr] = lean_ctor_objs(ptr);
      Op::IOSetInfo(
        lean_ptr_to_vec_val_idx(key_ptr),
        lean_unbox_nat_as_usize(idx_ptr),
        lean_unbox_nat_as_usize(len_ptr),
      )
    },
    11 => {
      let [idx_ptr, len_ptr] = lean_ctor_objs(ptr);
      Op::IORead(
        lean_unbox_nat_as_usize(idx_ptr),
        lean_unbox_nat_as_usize(len_ptr),
      )
    },
    12 => {
      let [data_ptr] = lean_ctor_objs(ptr);
      Op::IOWrite(lean_ptr_to_vec_val_idx(data_ptr))
    },
    13 => {
      let [byte_ptr] = lean_ctor_objs(ptr);
      Op::U8BitDecomposition(lean_unbox_nat_as_usize(byte_ptr))
    },
    14 => {
      let [byte_ptr] = lean_ctor_objs(ptr);
      Op::U8ShiftLeft(lean_unbox_nat_as_usize(byte_ptr))
    },
    15 => {
      let [byte_ptr] = lean_ctor_objs(ptr);
      Op::U8ShiftRight(lean_unbox_nat_as_usize(byte_ptr))
    },
    16 => {
      let [i, j] = lean_ctor_objs::<2>(ptr).map(lean_unbox_nat_as_usize);
      Op::U8Xor(i, j)
    },
    17 => {
      let [i, j] = lean_ctor_objs::<2>(ptr).map(lean_unbox_nat_as_usize);
      Op::U8Add(i, j)
    },
    18 => {
      let [i, j] = lean_ctor_objs::<2>(ptr).map(lean_unbox_nat_as_usize);
      Op::U8Sub(i, j)
    },
    19 => {
      let [i, j] = lean_ctor_objs::<2>(ptr).map(lean_unbox_nat_as_usize);
      Op::U8And(i, j)
    },
    20 => {
      let [i, j] = lean_ctor_objs::<2>(ptr).map(lean_unbox_nat_as_usize);
      Op::U8Or(i, j)
    },
    21 => {
      let [i, j] = lean_ctor_objs::<2>(ptr).map(lean_unbox_nat_as_usize);
      Op::U8LessThan(i, j)
    },
    22 => {
      let [label_ptr, idxs_ptr] = lean_ctor_objs(ptr);
      let label = lean_obj_to_string(label_ptr);
      let idxs = if lean_is_scalar(idxs_ptr) {
        None
      } else {
        let [idxs_ptr] = lean_ctor_objs(idxs_ptr);
        Some(lean_array_to_vec(idxs_ptr, lean_unbox_nat_as_usize))
      };
      Op::Debug(label, idxs)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_g_block_pair(ptr: *const c_void) -> (G, Block) {
  let [g_ptr, block_ptr] = lean_ctor_objs(ptr);
  let g = lean_unbox_g(g_ptr);
  let block = lean_ptr_to_block(block_ptr);
  (g, block)
}

fn lean_ptr_to_ctrl(ptr: *const c_void) -> Ctrl {
  match lean_tag(ptr) {
    0 => {
      let [val_idx_ptr, cases_ptr, default_ptr] = lean_ctor_objs(ptr);
      let val_idx = lean_unbox_nat_as_usize(val_idx_ptr);
      let vec_cases = lean_array_to_vec(cases_ptr, lean_ptr_to_g_block_pair);
      let cases = FxIndexMap::from_iter(vec_cases);
      let default = if lean_is_scalar(default_ptr) {
        None
      } else {
        let [block_ptr] = lean_ctor_objs(default_ptr);
        let block = lean_ptr_to_block(block_ptr);
        Some(Box::new(block))
      };
      Ctrl::Match(val_idx, cases, default)
    },
    1 => {
      let [sel_idx_ptr, val_idxs_ptr] = lean_ctor_objs(ptr);
      let sel_idx = lean_unbox_nat_as_usize(sel_idx_ptr);
      let val_idxs = lean_ptr_to_vec_val_idx(val_idxs_ptr);
      Ctrl::Return(sel_idx, val_idxs)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_block(ptr: *const c_void) -> Block {
  let [ops_ptr, ctrl_ptr, min_sel_included_ptr, max_sel_excluded_ptr] =
    lean_ctor_objs(ptr);
  let ops = lean_array_to_vec(ops_ptr, lean_ptr_to_op);
  let ctrl = lean_ptr_to_ctrl(ctrl_ptr);
  let min_sel_included = lean_unbox_nat_as_usize(min_sel_included_ptr);
  let max_sel_excluded = lean_unbox_nat_as_usize(max_sel_excluded_ptr);
  Block { ops, ctrl, min_sel_included, max_sel_excluded }
}

fn lean_ptr_to_function_layout(ptr: *const c_void) -> FunctionLayout {
  let [input_size_ptr, selectors_ptr, auxiliaries_ptr, lookups_ptr] =
    lean_ctor_objs(ptr);
  FunctionLayout {
    input_size: lean_unbox_nat_as_usize(input_size_ptr),
    selectors: lean_unbox_nat_as_usize(selectors_ptr),
    auxiliaries: lean_unbox_nat_as_usize(auxiliaries_ptr),
    lookups: lean_unbox_nat_as_usize(lookups_ptr),
  }
}

fn lean_ptr_to_function(ptr: *const c_void) -> Function {
  let [body_ptr, layout_ptr, unconstrained_ptr] = lean_ctor_objs(ptr);
  let body = lean_ptr_to_block(body_ptr);
  let layout = lean_ptr_to_function_layout(layout_ptr);
  let unconstrained = unconstrained_ptr as usize != 0;
  Function { body, layout, unconstrained }
}

pub(crate) fn lean_ptr_to_toplevel(ptr: *const c_void) -> Toplevel {
  let [functions_ptr, memory_sizes_ptr] = lean_ctor_objs(ptr);
  let functions = lean_array_to_vec(functions_ptr, lean_ptr_to_function);
  let memory_sizes =
    lean_array_to_vec(memory_sizes_ptr, lean_unbox_nat_as_usize);
  Toplevel { functions, memory_sizes }
}
