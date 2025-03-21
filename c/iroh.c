#include "lean/lean.h"
#include "common.h"
#include "linear.h"
#include "rust.h"

extern lean_obj_res c_rs_iroh_send(b_lean_obj_arg bytes)
{
    c_result *result = rs_iroh_send(bytes);
    lean_object *except;
    if (result->is_ok)
    {
        except = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(except, 0, lean_box(0));
    }
    else
    {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }
    rs__c_result_unit_string_free(result);

    return except;
}

extern lean_obj_res c_rs_iroh_recv(b_lean_obj_arg ticket, size_t buffer_capacity)
{
    char const *ticket_str = lean_string_cstr(ticket);
    // Buffer is allocated optimistically, but if the download fails it must be freed explicitly
    lean_object *buffer = lean_alloc_sarray(1, 0, buffer_capacity);
    c_result *result = rs_iroh_recv(ticket_str, buffer, buffer_capacity);

    lean_object *except;
    if (result->is_ok)
    {
        except = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(except, 0, lean_byte_array_mk(result->data));
    }
    else
    {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
        free(buffer);
    }
    rs__c_result_unit_string_free(result);

    return except;
}
