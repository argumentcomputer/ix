/*
 * Native harness for an object with two exported symbols (untrusted test
 * code): the entry symbol compilatrix_main and a further export,
 * compilatrix_forty, each called directly by name through the linker.
 */
#include <stdint.h>

#ifndef EXPECTED_RESULT
#error "EXPECTED_RESULT must be defined"
#endif

extern uint64_t compilatrix_main(void);
extern uint64_t compilatrix_forty(void);

int main(void) {
  return compilatrix_main() == (uint64_t)EXPECTED_RESULT && compilatrix_forty() == 40 ? 0 : 1;
}
