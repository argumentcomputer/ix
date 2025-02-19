#include "lean/lean.h"
#include "rust.h"

extern uint32_t add_u32s_indirect(uint32_t a, uint32_t b) {
    return add_u32s(a, b);
}
