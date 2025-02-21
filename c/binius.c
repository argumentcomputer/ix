#include "lean/lean.h"
#include "linear.h"
#include "rust.h"

extern lean_obj_res c_constraint_system_builder_init() {
    linear_object *linear = linear_object_init(
        rs_constraint_system_builder_init(),
        &rs_constraint_system_builder_free
    );
    return alloc_lean_linear_object(linear);
}

extern lean_obj_res c_constraint_system_builder_add_channel(lean_obj_arg l_csb) {
    linear_object *linear = to_linear_object(lean_get_external_data(l_csb));
    assert_linearity(linear);

    size_t channel_id = rs_constraint_system_builder_add_channel(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(channel_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}
