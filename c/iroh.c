#include "lean/lean.h"
#include "common.h"
#include "linear.h"
#include "rust.h"

extern size_t c_rs_iroh_send(b_lean_obj_arg path)
{
    char const *path_str = lean_string_cstr(path);
    return rs_iroh_send(path_str);
}

extern size_t c_rs_iroh_recv(b_lean_obj_arg path, b_lean_obj_arg ticket)
{
    char const *path_str = lean_string_cstr(path);
    char const *ticket_str = lean_string_cstr(ticket);
    return rs_iroh_recv(path_str, ticket_str);
}
