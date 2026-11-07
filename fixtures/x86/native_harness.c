#include <stdint.h>

#ifndef EXPECTED_RESULT
#error "EXPECTED_RESULT must be defined"
#endif

extern uint64_t ixcc_main(void);

uint64_t ixcc_rt_allocate(uint64_t size, uint64_t alignment) {
  return size == 16 && alignment == 8 ? 0x2000 : 0;
}

int main(void) {
  return ixcc_main() == (uint64_t)EXPECTED_RESULT ? 0 : 1;
}
