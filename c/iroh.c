#include "lean/lean.h"
#include "rust.h"

//extern lean_obj_res c_rs_iroh_send(b_lean_obj_arg bytes) {
//    c_result *result = rs_iroh_send(bytes);
//
//    lean_object *except;
//    if (result->is_ok) {
//        except = lean_alloc_ctor(1, 1, 0);
//        lean_ctor_set(except, 0, lean_box(0));
//    } else {
//        except = lean_alloc_ctor(0, 1, 0);
//        lean_ctor_set(except, 0, lean_mk_string(result->data));
//    }
//    rs__c_result_unit_string_free(result);
//
//    return except;
//}

//extern lean_obj_res c_rs_iroh_recv(b_lean_obj_arg ticket, size_t buffer_capacity) {
//    char const *ticket_str = lean_string_cstr(ticket);
//    // Buffer is allocated optimistically, but if the download fails it must be freed explicitly
//    lean_object *buffer = lean_alloc_sarray(1, 0, buffer_capacity);
//    c_result *result = rs_iroh_recv(ticket_str, buffer, buffer_capacity);
//
//    lean_object *except;
//    if (result->is_ok) {
//        except = lean_alloc_ctor(1, 1, 0);
//        lean_ctor_set(except, 0, buffer);
//    } else {
//        except = lean_alloc_ctor(0, 1, 0);
//        lean_ctor_set(except, 0, lean_mk_string(result->data));
//        lean_free_object(buffer);
//    }
//    rs__c_result_unit_string_free(result);
//
//    return except;
//}
extern lean_obj_res c_rs_iroh_put(b_lean_obj_arg node_id, b_lean_obj_arg addrs, b_lean_obj_arg relay_url, b_lean_obj_arg file_path) {
    char const *node_id_str = lean_string_cstr(node_id);
    char const *relay_url_str = lean_string_cstr(relay_url);
    char const *file_path_str = lean_string_cstr(file_path);

    c_result *result = rs_iroh_put(node_id_str, addrs, relay_url_str, file_path_str);

    lean_object *except;
    if (result->is_ok) {
        except = lean_alloc_ctor(1, 1, 0);
        //lean_ctor_set(except, 0, lean_mk_string(result->data));
        lean_ctor_set(except, 0, lean_box(0));
    } else {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }

    rs__c_result_unit_string_free(result);
    return except;
}

extern lean_obj_res c_rs_iroh_get(b_lean_obj_arg node_id, b_lean_obj_arg addrs, b_lean_obj_arg relay_url, b_lean_obj_arg hash) {
    char const *node_id_str = lean_string_cstr(node_id);
    char const *relay_url_str = lean_string_cstr(relay_url);
    char const *hash_str = lean_string_cstr(hash);

    c_result *result = rs_iroh_get(node_id_str, addrs, relay_url_str, hash_str);

    lean_object *except;
    if (result->is_ok) {
        except = lean_alloc_ctor(1, 1, 0);
        //lean_ctor_set(except, 0, lean_mk_string(result->data));
        lean_ctor_set(except, 0, lean_box(0));
    } else {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }

    rs__c_result_unit_string_free(result);
    return except;
}