/*
 * The runner's adapter for the diagnostic clang-tagged row (untrusted
 * measurement code): tag the arguments (n -> 2n + 1), call the tagged twin
 * (benchmarks/meas4/twins.c for fib, sum-loop and gcd; tagged.c for
 * ackermann, tak and the four from the scalar corpus, all at -O2), untag the result.
 * FIXTURE_<name> selects the twin.
 */
#include <stdint.h>

uint64_t twin_fib(uint64_t n);
uint64_t twin_sum_loop(uint64_t n);
uint64_t twin_gcd(uint64_t a, uint64_t b);
uint64_t twin_ack(uint64_t m, uint64_t n);
uint64_t twin_tak(uint64_t f, uint64_t x, uint64_t y, uint64_t z);
uint64_t twin_collatz(uint64_t limit);
uint64_t twin_prime_count(uint64_t n);
int twin_is_even(uint64_t n);
uint64_t twin_sfib(uint64_t n);

static uint64_t tag(uint64_t n) { return 2 * n + 1; }

void row_init(void) {}

uint64_t row_entry(const uint64_t *a) {
#if defined(FIXTURE_fib)
  return twin_fib(tag(a[0])) >> 1;
#elif defined(FIXTURE_sum_loop)
  return twin_sum_loop(tag(a[0])) >> 1;
#elif defined(FIXTURE_ackermann)
  return twin_ack(tag(a[0]), tag(a[1])) >> 1;
#elif defined(FIXTURE_tak)
  return twin_tak(tag(a[0]), tag(a[1]), tag(a[2]), tag(a[3])) >> 1;
#elif defined(FIXTURE_gcd)
  return twin_gcd(tag(a[0]), tag(a[1])) >> 1;
#elif defined(FIXTURE_collatz)
  return twin_collatz(tag(a[0])) >> 1;
#elif defined(FIXTURE_prime_count)
  return twin_prime_count(tag(a[0])) >> 1;
#elif defined(FIXTURE_even_odd)
  return twin_is_even(tag(a[0])) ? 1 : 0;
#elif defined(FIXTURE_sfib)
  return twin_sfib(tag(a[0])) >> 1;
#else
#error "no tagged twin for this fixture"
#endif
}

uint64_t row_heap(void) { return UINT64_MAX; }
