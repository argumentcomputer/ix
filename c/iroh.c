#include "lean/lean.h"
#include "rust.h"

typedef struct {
    char *message;
    char *hash;
} put_response_ffi;

extern lean_obj_res c_rs_iroh_put(b_lean_obj_arg node_id, b_lean_obj_arg addrs, b_lean_obj_arg relay_url, b_lean_obj_arg file_path) {
    char const *node_id_str = lean_string_cstr(node_id);
    char const *relay_url_str = lean_string_cstr(relay_url);
    char const *file_path_str = lean_string_cstr(file_path);

    c_result *result = rs_iroh_put(node_id_str, addrs, relay_url_str, file_path_str);

    lean_object *except;
    if (result->is_ok) {
        put_response_ffi *put_response = result->data;
        lean_object *message = lean_mk_string(put_response->message);
        lean_object *hash = lean_mk_string(put_response->hash);

        lean_object *put_response_ctor = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(put_response_ctor, 0, message);
        lean_ctor_set(put_response_ctor, 1, hash);

        except = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(except, 0, put_response_ctor);
        // except = lean_alloc_ctor(1, 1, 0);
        // lean_ctor_set(except, 0, lean_alloc_external(get_iroh_response_class, result->data));
    } else {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }

    rs__c_result_iroh_put_response_string_free(result);
    return except;
}

typedef struct {
    char *message;
    char *hash;
    bytes_data *bytes;
} get_response_ffi;

extern lean_obj_res c_rs_iroh_get(b_lean_obj_arg node_id, b_lean_obj_arg addrs, b_lean_obj_arg relay_url, b_lean_obj_arg hash) {
    char const *node_id_str = lean_string_cstr(node_id);
    char const *relay_url_str = lean_string_cstr(relay_url);
    char const *hash_str = lean_string_cstr(hash);

    c_result *result = rs_iroh_get(node_id_str, addrs, relay_url_str, hash_str);

    lean_object *except;
    if (result->is_ok) {
        get_response_ffi *get_response = result->data;
        lean_object *message = lean_mk_string(get_response->message);
        lean_object *hash = lean_mk_string(get_response->hash);

        bytes_data *rs_bytes = get_response->bytes;
        size_t bytes_size = rs_bytes->size;
        lean_object *byte_array = lean_alloc_sarray(1, bytes_size, bytes_size);
        rs_move_bytes(rs_bytes, byte_array);

        lean_object *get_response_ctor = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(get_response_ctor, 0, message);
        lean_ctor_set(get_response_ctor, 1, hash);
        lean_ctor_set(get_response_ctor, 2, byte_array);

        except = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(except, 0, get_response_ctor);

        //lean_ctor_set(except, 0, lean_mk_string(result->data));
        // lean_ctor_set(except, 0, lean_box(0));
    } else {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }

    rs__c_result_iroh_get_response_string_free(result);
    return except;
}