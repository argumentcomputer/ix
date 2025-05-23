use binius_field::BinaryField128b;

use crate::{
    archon::{OracleIdx, arith_expr::ArithExpr},
    lean::{ctor::LeanCtorObject, ffi::as_ref_unsafe, sarray::LeanSArrayObject},
};

use super::{boxed_usize_ptr_to_oracle_idx, external_ptr_to_u128};

pub(super) fn lean_ctor_to_arith_expr(ctor: &LeanCtorObject) -> ArithExpr {
    match ctor.tag() {
        0 => {
            // Const
            let [u128_ptr] = ctor.objs();
            let u128 = external_ptr_to_u128(u128_ptr);
            ArithExpr::Const(BinaryField128b::new(u128))
        }
        1 => {
            // Var
            let [ptr_as_usize] = ctor.objs();
            ArithExpr::Var(ptr_as_usize as usize)
        }
        2 => {
            // Oracle
            let [ptr] = ctor.objs();
            ArithExpr::Oracle(boxed_usize_ptr_to_oracle_idx(ptr))
        }
        3 => {
            // Add
            let [x, y] = ctor.objs();
            let x = lean_ctor_to_arith_expr(as_ref_unsafe(x.cast()));
            let y = lean_ctor_to_arith_expr(as_ref_unsafe(y.cast()));
            ArithExpr::Add(Box::new(x), Box::new(y))
        }
        4 => {
            // Mul
            let [x, y] = ctor.objs();
            let x = lean_ctor_to_arith_expr(as_ref_unsafe(x.cast()));
            let y = lean_ctor_to_arith_expr(as_ref_unsafe(y.cast()));
            ArithExpr::Mul(Box::new(x), Box::new(y))
        }
        5 => {
            // Pow
            let [x, e] = ctor.objs();
            let x = lean_ctor_to_arith_expr(as_ref_unsafe(x.cast()));
            ArithExpr::Pow(Box::new(x), e as u64)
        }
        _ => panic!("Invalid ctor tag"),
    }
}

fn arith_expr_from_bytes(bytes: &[u8]) -> ArithExpr {
    match bytes[0] {
        0 => {
            let mut slice = [0; size_of::<u128>()];
            slice.copy_from_slice(&bytes[1..size_of::<u128>() + 1]);
            let u = u128::from_le_bytes(slice);
            ArithExpr::Const(BinaryField128b::new(u))
        }
        1 => {
            let mut slice = [0; size_of::<usize>()];
            slice.copy_from_slice(&bytes[1..size_of::<usize>() + 1]);
            let u = usize::from_le_bytes(slice);
            ArithExpr::Var(u)
        }
        2 => {
            let mut slice = [0; size_of::<usize>()];
            slice.copy_from_slice(&bytes[1..size_of::<usize>() + 1]);
            let idx = usize::from_le_bytes(slice);
            ArithExpr::Oracle(OracleIdx(idx))
        }
        3 => {
            let x_size = bytes[1] as usize;
            let x = arith_expr_from_bytes(&bytes[2..x_size + 2]);
            let y = arith_expr_from_bytes(&bytes[x_size + 2..]);
            ArithExpr::Add(Box::new(x), Box::new(y))
        }
        4 => {
            let x_size = bytes[1] as usize;
            let x = arith_expr_from_bytes(&bytes[2..x_size + 2]);
            let y = arith_expr_from_bytes(&bytes[x_size + 2..]);
            ArithExpr::Mul(Box::new(x), Box::new(y))
        }
        5 => {
            let u64_start = bytes.len() - size_of::<u64>();
            let mut u64_bytes = [0; size_of::<u64>()];
            u64_bytes.copy_from_slice(&bytes[u64_start..]);
            let e = u64::from_le_bytes(u64_bytes);
            let x = arith_expr_from_bytes(&bytes[1..u64_start]);
            ArithExpr::Pow(Box::new(x), e)
        }
        _ => panic!("Invalid ctor tag"),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_arith_expr_is_equivalent_to_bytes(
    arith_expr: &LeanCtorObject,
    bytes: &LeanSArrayObject,
) -> bool {
    lean_ctor_to_arith_expr(arith_expr) == arith_expr_from_bytes(bytes.data())
}
