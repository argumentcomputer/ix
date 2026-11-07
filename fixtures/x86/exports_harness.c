/*
 * Native harness for an object with two exported symbols (untrusted test
 * code): the entry symbol ixcc_main and a further export,
 * ixcc_forty, each called directly by name through the linker.
 */
#include <stdint.h>

#ifndef EXPECTED_RESULT
#error "EXPECTED_RESULT must be defined"
#endif

extern uint64_t ixcc_main(void);
extern uint64_t ixcc_forty(void);

int main(void) {
  return ixcc_main() == (uint64_t)EXPECTED_RESULT && ixcc_forty() == 40 ? 0 : 1;
}
