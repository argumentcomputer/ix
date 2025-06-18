use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
};
use rayon::iter::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator};

use crate::{
    archon::{
        OracleIdx,
        witness::{EntryId, Witness, WitnessModule, compile_witness_modules},
    },
    lean::{
        CArray,
        array::LeanArrayObject,
        ctor::LeanCtorObject,
        ffi::{
            archon::module_mode::lean_ctor_ptr_to_module_mode, drop_raw, external_ptr_to_u128,
            lean_unbox_u32, lean_unbox_u64, to_raw,
        },
        sarray::LeanSArrayObject,
    },
    lean_unbox,
};

/// Also holds a reference to the witness modules vector, which lives in the heap
/// and needs to be deallocated manually.
pub(crate) struct WitnessWrap {
    pub(crate) witness_modules: &'static Vec<WitnessModule>,
    pub(crate) witness: Witness<'static>,
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_free(ptr: *mut WitnessWrap) {
    let witness_wrap = unsafe { Box::from_raw(ptr) };
    let modules =
        witness_wrap.witness_modules as *const Vec<WitnessModule> as *mut Vec<WitnessModule>;
    drop_raw(modules);
    drop(witness_wrap);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_free(ptr: *mut WitnessModule) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_add_entry(witness_module: &mut WitnessModule) -> EntryId {
    witness_module.new_entry()
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_add_entry_with_capacity(
    witness_module: &mut WitnessModule,
    log_bits: u8,
) -> EntryId {
    witness_module.new_entry_with_capacity(log_bits)
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_bind_oracle_to(
    witness_module: &mut WitnessModule,
    oracle_idx: OracleIdx,
    entry_id: EntryId,
    tower_level: u8,
) {
    match tower_level {
        0 => witness_module.bind_oracle_to::<B1>(oracle_idx, entry_id),
        1 => witness_module.bind_oracle_to::<B2>(oracle_idx, entry_id),
        2 => witness_module.bind_oracle_to::<B4>(oracle_idx, entry_id),
        3 => witness_module.bind_oracle_to::<B8>(oracle_idx, entry_id),
        4 => witness_module.bind_oracle_to::<B16>(oracle_idx, entry_id),
        5 => witness_module.bind_oracle_to::<B32>(oracle_idx, entry_id),
        6 => witness_module.bind_oracle_to::<B64>(oracle_idx, entry_id),
        7 => witness_module.bind_oracle_to::<B128>(oracle_idx, entry_id),
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_push_u8s_to(
    witness_module: &mut WitnessModule,
    u8s: &LeanArrayObject,
    entry_id: EntryId,
) {
    let u8s = u8s.to_vec(|ptr| lean_unbox!(u8, ptr));
    witness_module.push_u8s_to(u8s, entry_id);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_push_u16s_to(
    witness_module: &mut WitnessModule,
    u16s: &LeanArrayObject,
    entry_id: EntryId,
) {
    let u16s = u16s.to_vec(|ptr| lean_unbox!(u16, ptr));
    witness_module.push_u16s_to(u16s, entry_id);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_push_u32s_to(
    witness_module: &mut WitnessModule,
    u32s: &LeanArrayObject,
    entry_id: EntryId,
) {
    let u32s = u32s.to_vec(lean_unbox_u32);
    witness_module.push_u32s_to(u32s, entry_id);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_push_u64s_to(
    witness_module: &mut WitnessModule,
    u64s: &LeanArrayObject,
    entry_id: EntryId,
) {
    let u64s = u64s.to_vec(lean_unbox_u64);
    witness_module.push_u64s_to(u64s, entry_id);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_push_u128s_to(
    witness_module: &mut WitnessModule,
    u128s: &LeanArrayObject,
    entry_id: EntryId,
) {
    let u128s = u128s.to_vec(external_ptr_to_u128);
    witness_module.push_u128s_to(u128s, entry_id);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_populate(
    witness_module: &mut WitnessModule,
    mode: &LeanCtorObject,
) {
    let mode = lean_ctor_ptr_to_module_mode(mode);
    witness_module
        .populate(mode)
        .expect("WitnessModule::populate failure");
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_par_populate(
    witness_modules: &CArray<*mut WitnessModule>,
    modes: &LeanArrayObject,
) {
    let modes = modes.to_vec(|ptr| lean_ctor_ptr_to_module_mode(ptr.cast()));
    let mut witness_modules = witness_modules
        .slice(modes.len())
        .iter()
        .map(|&ptr| unsafe { &mut *ptr })
        .collect::<Vec<_>>();
    witness_modules
        .par_iter_mut()
        .zip(modes)
        .enumerate()
        .for_each(|(i, (w, m))| {
            if let Err(e) = w.populate(m) {
                panic!("rs_witness_module_par_populate failure at index {i}: {e}");
            }
        });
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_get_data_num_bytes(
    witness_module: &WitnessModule,
    oracle_idx: OracleIdx,
) -> usize {
    witness_module.get_data_num_bytes(&oracle_idx)
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_module_get_data(
    witness_module: &WitnessModule,
    oracle_idx: OracleIdx,
    bytes: &mut LeanSArrayObject,
) {
    bytes.set_data(&witness_module.get_data(&oracle_idx));
}

#[unsafe(no_mangle)]
extern "C" fn rs_compile_witness_modules(
    modules_ptrs: &CArray<*mut WitnessModule>,
    modes: &LeanArrayObject,
) -> *const WitnessWrap {
    let modes = modes.to_vec(|ptr| lean_ctor_ptr_to_module_mode(ptr.cast()));
    let witness_modules = modules_ptrs
        .slice(modes.len())
        .iter()
        .map(|&ptr| std::mem::take(unsafe { &mut *ptr }))
        .collect::<Vec<_>>();
    let witness_modules = Box::leak(Box::new(witness_modules));
    let witness =
        compile_witness_modules(witness_modules, modes).expect("compile_witness_modules failure");
    to_raw(WitnessWrap {
        witness_modules,
        witness,
    })
}
