use binius_field::BinaryField128b;

use crate::{
    archon::{OracleIdx, circuit::OracleOrConst},
    lean::{
        ctor::LeanCtorObject,
        ffi::{archon::boxed_usize_ptr_to_oracle_idx, as_ref_unsafe, external_ptr_to_u128},
        sarray::LeanSArrayObject,
    },
};

pub(super) fn lean_ctor_ptr_to_oracle_or_const(ctor: *const LeanCtorObject) -> OracleOrConst {
    let ctor = as_ref_unsafe(ctor);
    match ctor.tag() {
        0 => {
            let [oracle_idx_ptr] = ctor.objs();
            OracleOrConst::Oracle(boxed_usize_ptr_to_oracle_idx(oracle_idx_ptr))
        }
        1 => {
            let [base_ptr, tower_level_ptr] = ctor.objs();
            let base = BinaryField128b::new(external_ptr_to_u128(base_ptr));
            let tower_level = tower_level_ptr as usize;
            OracleOrConst::Const { base, tower_level }
        }
        _ => unreachable!(),
    }
}

fn oracle_or_const_from_bytes(bytes: &[u8]) -> OracleOrConst {
    match bytes[0] {
        0 => {
            let mut oracle_idx_bytes = [0; size_of::<usize>()];
            oracle_idx_bytes.copy_from_slice(&bytes[1..]);
            let oracle_idx = OracleIdx(usize::from_le_bytes(oracle_idx_bytes));
            OracleOrConst::Oracle(oracle_idx)
        }
        1 => {
            let mut base_u128_bytes = [0; size_of::<u128>()];
            base_u128_bytes.copy_from_slice(&bytes[1..size_of::<u128>() + 1]);
            let base = BinaryField128b::new(u128::from_le_bytes(base_u128_bytes));
            let tower_level = bytes[size_of::<u128>() + 1] as usize;
            OracleOrConst::Const { base, tower_level }
        }
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_oracle_or_const_is_equivalent_to_bytes(
    oracle_or_const_ptr: *const LeanCtorObject,
    bytes: &LeanSArrayObject,
) -> bool {
    lean_ctor_ptr_to_oracle_or_const(oracle_or_const_ptr)
        == oracle_or_const_from_bytes(bytes.data())
}
