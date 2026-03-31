use multi_stark::p3_field::PrimeCharacteristicRing;

use lean_ffi::object::{LeanBorrowed, LeanCtor, LeanRef};

use crate::{
  FxIndexMap,
  aiur::{
    G,
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel, ValIdx},
  },
  lean::LeanAiurToplevel,
};

use crate::ffi::aiur::{lean_unbox_g, lean_unbox_nat_as_usize};

fn decode_vec_val_idx(obj: LeanBorrowed<'_>) -> Vec<ValIdx> {
  obj.as_array().map(|x| lean_unbox_nat_as_usize(&x))
}

fn decode_op(ctor: LeanCtor<LeanBorrowed<'_>>) -> Op {
  match ctor.tag() {
    0 => {
      let [const_val] = ctor.objs::<1>();
      Op::Const(G::from_u64(const_val.as_enum_tag() as u64))
    },
    1 => {
      let [a, b] = ctor.objs::<2>();
      Op::Add(lean_unbox_nat_as_usize(&a), lean_unbox_nat_as_usize(&b))
    },
    2 => {
      let [a, b] = ctor.objs::<2>();
      Op::Sub(lean_unbox_nat_as_usize(&a), lean_unbox_nat_as_usize(&b))
    },
    3 => {
      let [a, b] = ctor.objs::<2>();
      Op::Mul(lean_unbox_nat_as_usize(&a), lean_unbox_nat_as_usize(&b))
    },
    4 => {
      let [a] = ctor.objs::<1>();
      Op::EqZero(lean_unbox_nat_as_usize(&a))
    },
    5 => {
      let [fun_idx, val_idxs, output_size] = ctor.objs::<3>();
      let fun_idx = lean_unbox_nat_as_usize(&fun_idx);
      let val_idxs = decode_vec_val_idx(val_idxs);
      let output_size = lean_unbox_nat_as_usize(&output_size);
      Op::Call(fun_idx, val_idxs, output_size)
    },
    6 => {
      let [fun_idx, val_idxs, output_size] = ctor.objs::<3>();
      let fun_idx = lean_unbox_nat_as_usize(&fun_idx);
      let val_idxs = decode_vec_val_idx(val_idxs);
      let output_size = lean_unbox_nat_as_usize(&output_size);
      Op::CallUnconstrained(fun_idx, val_idxs, output_size)
    },
    7 => {
      let [val_idxs] = ctor.objs::<1>();
      Op::Store(decode_vec_val_idx(val_idxs))
    },
    8 => {
      let [width, val_idx] = ctor.objs::<2>();
      Op::Load(
        lean_unbox_nat_as_usize(&width),
        lean_unbox_nat_as_usize(&val_idx),
      )
    },
    9 => {
      let [a, b] = ctor.objs::<2>();
      Op::AssertEq(decode_vec_val_idx(a), decode_vec_val_idx(b))
    },
    10 => {
      let [key] = ctor.objs::<1>();
      Op::IOGetInfo(decode_vec_val_idx(key))
    },
    11 => {
      let [key, idx, len] = ctor.objs::<3>();
      Op::IOSetInfo(
        decode_vec_val_idx(key),
        lean_unbox_nat_as_usize(&idx),
        lean_unbox_nat_as_usize(&len),
      )
    },
    12 => {
      let [idx, len] = ctor.objs::<2>();
      Op::IORead(lean_unbox_nat_as_usize(&idx), lean_unbox_nat_as_usize(&len))
    },
    13 => {
      let [data] = ctor.objs::<1>();
      Op::IOWrite(decode_vec_val_idx(data))
    },
    14 => {
      let [byte] = ctor.objs::<1>();
      Op::U8BitDecomposition(lean_unbox_nat_as_usize(&byte))
    },
    15 => {
      let [byte] = ctor.objs::<1>();
      Op::U8ShiftLeft(lean_unbox_nat_as_usize(&byte))
    },
    16 => {
      let [byte] = ctor.objs::<1>();
      Op::U8ShiftRight(lean_unbox_nat_as_usize(&byte))
    },
    17 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U8Xor(i, j)
    },
    18 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U8Add(i, j)
    },
    19 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U8Sub(i, j)
    },
    20 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U8And(i, j)
    },
    21 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U8Or(i, j)
    },
    22 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U8LessThan(i, j)
    },
    23 => {
      let [i, j] = ctor.objs::<2>().map(|x| lean_unbox_nat_as_usize(&x));
      Op::U32LessThan(i, j)
    },
    24 => {
      let [label_obj, idxs_obj] = ctor.objs::<2>();
      let label = label_obj.as_string().to_string();
      let idxs = if idxs_obj.is_scalar() {
        None
      } else {
        let inner_ctor = idxs_obj.as_ctor();
        Some(inner_ctor.get(0).as_array().map(|x| lean_unbox_nat_as_usize(&x)))
      };
      Op::Debug(label, idxs)
    },
    _ => unreachable!(),
  }
}

fn decode_g_block_pair(ctor: LeanCtor<LeanBorrowed<'_>>) -> (G, Block) {
  let [g_obj, block_obj] = ctor.objs::<2>();
  let g = lean_unbox_g(&g_obj);
  let block = decode_block(block_obj.as_ctor());
  (g, block)
}

fn decode_ctrl(ctor: LeanCtor<LeanBorrowed<'_>>) -> Ctrl {
  match ctor.tag() {
    0 => {
      let [val_idx_obj, cases_obj, default_obj] = ctor.objs::<3>();
      let val_idx = lean_unbox_nat_as_usize(&val_idx_obj);
      let vec_cases =
        cases_obj.as_array().map(|o| decode_g_block_pair(o.as_ctor()));
      let cases = FxIndexMap::from_iter(vec_cases);
      let default = if default_obj.is_scalar() {
        None
      } else {
        let inner_ctor = default_obj.as_ctor();
        let block = decode_block(inner_ctor.get(0).as_ctor());
        Some(Box::new(block))
      };
      Ctrl::Match(val_idx, cases, default)
    },
    1 => {
      let [sel_idx_obj, val_idxs_obj] = ctor.objs::<2>();
      let sel_idx = lean_unbox_nat_as_usize(&sel_idx_obj);
      let val_idxs = decode_vec_val_idx(val_idxs_obj);
      Ctrl::Return(sel_idx, val_idxs)
    },
    _ => unreachable!(),
  }
}

fn decode_block(ctor: LeanCtor<LeanBorrowed<'_>>) -> Block {
  let [ops_obj, ctrl_obj, min_sel_obj, max_sel_obj] = ctor.objs::<4>();
  let ops = ops_obj.as_array().map(|o| decode_op(o.as_ctor()));
  let ctrl = decode_ctrl(ctrl_obj.as_ctor());
  let min_sel_included = lean_unbox_nat_as_usize(&min_sel_obj);
  let max_sel_excluded = lean_unbox_nat_as_usize(&max_sel_obj);
  Block { ops, ctrl, min_sel_included, max_sel_excluded }
}

fn decode_function_layout(ctor: LeanCtor<LeanBorrowed<'_>>) -> FunctionLayout {
  let [input_size, selectors, auxiliaries, lookups] = ctor.objs::<4>();
  FunctionLayout {
    input_size: lean_unbox_nat_as_usize(&input_size),
    selectors: lean_unbox_nat_as_usize(&selectors),
    auxiliaries: lean_unbox_nat_as_usize(&auxiliaries),
    lookups: lean_unbox_nat_as_usize(&lookups),
  }
}

fn decode_function(ctor: LeanCtor<LeanBorrowed<'_>>) -> Function {
  let [body_obj, layout_obj, entry_obj] = ctor.objs::<3>();
  let body = decode_block(body_obj.as_ctor());
  let layout = decode_function_layout(layout_obj.as_ctor());
  let entry = entry_obj.as_enum_tag() != 0;
  Function { body, layout, entry }
}

pub(crate) fn decode_toplevel(
  obj: &LeanAiurToplevel<impl LeanRef>,
) -> Toplevel {
  let ctor = obj.as_ctor();
  let [functions_obj, memory_sizes_obj] = ctor.objs::<2>();
  let functions =
    functions_obj.as_array().map(|o| decode_function(o.as_ctor()));
  let memory_sizes =
    memory_sizes_obj.as_array().map(|x| lean_unbox_nat_as_usize(&x));
  Toplevel { functions, memory_sizes }
}
