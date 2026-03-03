use multi_stark::p3_field::PrimeCharacteristicRing;

use lean_sys::object::LeanObject;

use crate::{
  FxIndexMap,
  aiur::{
    G,
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel, ValIdx},
  },
};

use crate::ffi::aiur::{lean_unbox_g, lean_unbox_nat_as_usize};

fn lean_ptr_to_vec_val_idx(obj: LeanObject) -> Vec<ValIdx> {
  obj.as_array().map(lean_unbox_nat_as_usize)
}

fn lean_ptr_to_op(obj: LeanObject) -> Op {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let [const_val] = ctor.objs::<1>();
      Op::Const(G::from_u64(const_val.as_ptr() as u64))
    },
    1 => {
      let [a, b] = ctor.objs::<2>();
      Op::Add(lean_unbox_nat_as_usize(a), lean_unbox_nat_as_usize(b))
    },
    2 => {
      let [a, b] = ctor.objs::<2>();
      Op::Sub(lean_unbox_nat_as_usize(a), lean_unbox_nat_as_usize(b))
    },
    3 => {
      let [a, b] = ctor.objs::<2>();
      Op::Mul(lean_unbox_nat_as_usize(a), lean_unbox_nat_as_usize(b))
    },
    4 => {
      let [a] = ctor.objs::<1>();
      Op::EqZero(lean_unbox_nat_as_usize(a))
    },
    5 => {
      let [fun_idx, val_idxs, output_size] = ctor.objs::<3>();
      let fun_idx = lean_unbox_nat_as_usize(fun_idx);
      let val_idxs = lean_ptr_to_vec_val_idx(val_idxs);
      let output_size = lean_unbox_nat_as_usize(output_size);
      Op::Call(fun_idx, val_idxs, output_size)
    },
    6 => {
      let [val_idxs] = ctor.objs::<1>();
      Op::Store(lean_ptr_to_vec_val_idx(val_idxs))
    },
    7 => {
      let [width, val_idx] = ctor.objs::<2>();
      Op::Load(lean_unbox_nat_as_usize(width), lean_unbox_nat_as_usize(val_idx))
    },
    8 => {
      let [a, b] = ctor.objs::<2>();
      Op::AssertEq(lean_ptr_to_vec_val_idx(a), lean_ptr_to_vec_val_idx(b))
    },
    9 => {
      let [key] = ctor.objs::<1>();
      Op::IOGetInfo(lean_ptr_to_vec_val_idx(key))
    },
    10 => {
      let [key, idx, len] = ctor.objs::<3>();
      Op::IOSetInfo(
        lean_ptr_to_vec_val_idx(key),
        lean_unbox_nat_as_usize(idx),
        lean_unbox_nat_as_usize(len),
      )
    },
    11 => {
      let [idx, len] = ctor.objs::<2>();
      Op::IORead(lean_unbox_nat_as_usize(idx), lean_unbox_nat_as_usize(len))
    },
    12 => {
      let [data] = ctor.objs::<1>();
      Op::IOWrite(lean_ptr_to_vec_val_idx(data))
    },
    13 => {
      let [byte] = ctor.objs::<1>();
      Op::U8BitDecomposition(lean_unbox_nat_as_usize(byte))
    },
    14 => {
      let [byte] = ctor.objs::<1>();
      Op::U8ShiftLeft(lean_unbox_nat_as_usize(byte))
    },
    15 => {
      let [byte] = ctor.objs::<1>();
      Op::U8ShiftRight(lean_unbox_nat_as_usize(byte))
    },
    16 => {
      let [i, j] = ctor.objs::<2>().map(lean_unbox_nat_as_usize);
      Op::U8Xor(i, j)
    },
    17 => {
      let [i, j] = ctor.objs::<2>().map(lean_unbox_nat_as_usize);
      Op::U8Add(i, j)
    },
    18 => {
      let [i, j] = ctor.objs::<2>().map(lean_unbox_nat_as_usize);
      Op::U8Sub(i, j)
    },
    19 => {
      let [i, j] = ctor.objs::<2>().map(lean_unbox_nat_as_usize);
      Op::U8And(i, j)
    },
    20 => {
      let [i, j] = ctor.objs::<2>().map(lean_unbox_nat_as_usize);
      Op::U8Or(i, j)
    },
    21 => {
      let [i, j] = ctor.objs::<2>().map(lean_unbox_nat_as_usize);
      Op::U8LessThan(i, j)
    },
    22 => {
      let [label_obj, idxs_obj] = ctor.objs::<2>();
      let label = label_obj.as_string().to_string();
      let idxs = if idxs_obj.is_scalar() {
        None
      } else {
        let inner_ctor = idxs_obj.as_ctor();
        Some(inner_ctor.get(0).as_array().map(lean_unbox_nat_as_usize))
      };
      Op::Debug(label, idxs)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_g_block_pair(obj: LeanObject) -> (G, Block) {
  let ctor = obj.as_ctor();
  let [g_obj, block_obj] = ctor.objs::<2>();
  let g = lean_unbox_g(g_obj);
  let block = lean_ptr_to_block(block_obj);
  (g, block)
}

fn lean_ptr_to_ctrl(obj: LeanObject) -> Ctrl {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let [val_idx_obj, cases_obj, default_obj] = ctor.objs::<3>();
      let val_idx = lean_unbox_nat_as_usize(val_idx_obj);
      let vec_cases = cases_obj.as_array().map(lean_ptr_to_g_block_pair);
      let cases = FxIndexMap::from_iter(vec_cases);
      let default = if default_obj.is_scalar() {
        None
      } else {
        let inner_ctor = default_obj.as_ctor();
        let block = lean_ptr_to_block(inner_ctor.get(0));
        Some(Box::new(block))
      };
      Ctrl::Match(val_idx, cases, default)
    },
    1 => {
      let [sel_idx_obj, val_idxs_obj] = ctor.objs::<2>();
      let sel_idx = lean_unbox_nat_as_usize(sel_idx_obj);
      let val_idxs = lean_ptr_to_vec_val_idx(val_idxs_obj);
      Ctrl::Return(sel_idx, val_idxs)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_block(obj: LeanObject) -> Block {
  let ctor = obj.as_ctor();
  let [ops_obj, ctrl_obj, min_sel_obj, max_sel_obj] = ctor.objs::<4>();
  let ops = ops_obj.as_array().map(lean_ptr_to_op);
  let ctrl = lean_ptr_to_ctrl(ctrl_obj);
  let min_sel_included = lean_unbox_nat_as_usize(min_sel_obj);
  let max_sel_excluded = lean_unbox_nat_as_usize(max_sel_obj);
  Block { ops, ctrl, min_sel_included, max_sel_excluded }
}

fn lean_ptr_to_function_layout(obj: LeanObject) -> FunctionLayout {
  let ctor = obj.as_ctor();
  let [input_size, selectors, auxiliaries, lookups] = ctor.objs::<4>();
  FunctionLayout {
    input_size: lean_unbox_nat_as_usize(input_size),
    selectors: lean_unbox_nat_as_usize(selectors),
    auxiliaries: lean_unbox_nat_as_usize(auxiliaries),
    lookups: lean_unbox_nat_as_usize(lookups),
  }
}

fn lean_ptr_to_function(obj: LeanObject) -> Function {
  let ctor = obj.as_ctor();
  let [body_obj, layout_obj, unconstrained_obj] = ctor.objs::<3>();
  let body = lean_ptr_to_block(body_obj);
  let layout = lean_ptr_to_function_layout(layout_obj);
  let unconstrained = unconstrained_obj.as_ptr() as usize != 0;
  Function { body, layout, unconstrained }
}

pub(crate) fn decode_toplevel(obj: LeanObject) -> Toplevel {
  let ctor = obj.as_ctor();
  let [functions_obj, memory_sizes_obj] = ctor.objs::<2>();
  let functions = functions_obj.as_array().map(lean_ptr_to_function);
  let memory_sizes = memory_sizes_obj.as_array().map(lean_unbox_nat_as_usize);
  Toplevel { functions, memory_sizes }
}
