use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::constraint_system::{channel::ChannelId, ConstraintSystem};
use binius_field::BinaryField128b;

#[inline]
fn to_raw<T>(t: T) -> *const T {
    Box::into_raw(Box::new(t))
}

#[inline]
fn drop_raw<T>(ptr: *mut T) {
    if ptr.is_null() {
        panic!("Double-free attempt");
    }
    let t = unsafe { Box::from_raw(ptr) };
    drop(t);
}

/* --- ConstraintSystem --- */

#[no_mangle]
extern "C" fn rs_constraint_system_free(ptr: *mut ConstraintSystem<BinaryField128b>) {
    drop_raw(ptr);
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_build(
    builder: &mut ConstraintSystemBuilder,
) -> *const ConstraintSystem<BinaryField128b> {
    let builder = std::mem::take(builder);
    to_raw(
        builder
            .build()
            .expect("ConstraintSystemBuilder build failure"),
    )
}

/* --- ConstraintSystemBuilder --- */

#[no_mangle]
extern "C" fn rs_constraint_system_builder_init<'a>() -> *const ConstraintSystemBuilder<'a> {
    to_raw(ConstraintSystemBuilder::new())
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_free(ptr: *mut ConstraintSystemBuilder) {
    drop_raw(ptr);
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_add_channel(
    builder: &mut ConstraintSystemBuilder,
) -> ChannelId {
    builder.add_channel()
}
