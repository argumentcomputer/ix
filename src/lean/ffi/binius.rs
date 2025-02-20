#![allow(clippy::missing_safety_doc)]

use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::constraint_system::channel::ChannelId;

#[no_mangle]
pub extern "C" fn rs_constraint_system_builder_init<'a>() -> *const ConstraintSystemBuilder<'a> {
    Box::into_raw(Box::new(ConstraintSystemBuilder::new()))
}

#[no_mangle]
pub unsafe extern "C" fn rs_constraint_system_builder_free(ptr: *mut ConstraintSystemBuilder) {
    if ptr.is_null() {
        panic!("Double-free attempt");
    }
    let builder = unsafe { Box::from_raw(ptr) };
    drop(builder);
}

#[no_mangle]
pub unsafe extern "C" fn rs_constraint_system_builder_add_channel(
    ptr: *mut ConstraintSystemBuilder,
) -> ChannelId {
    unsafe { (*ptr).add_channel() }
}
