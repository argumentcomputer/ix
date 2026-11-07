/*
 * The runner's adapter for the clang-O2 and clang-O3 rows (untrusted
 * measurement code): the fixture's natural C twin, unchanged, included into
 * this file with its `main` renamed, so that the twin's own (static)
 * function is called in place of reading argv. The file is compiled at the
 * row's level, so the twin is compiled exactly as the process profile
 * compiles it, apart from flags recorded in build.json. TWIN_SOURCE is the
 * twin's path and FIXTURE_<name> selects the call (the fixture's name with
 * '-' as '_').
 *
 * Only the K1 twins (the original five and the MT.2 corpus four) are wired
 * here; a fixture without a case does not build, and the runner leaves the
 * row out of its entry profile.
 */
#define main twin_main
#include TWIN_SOURCE
#undef main

void row_init(void) {}

uint64_t row_entry(const uint64_t *a) {
#if defined(FIXTURE_fib)
  return fib(a[0]);
#elif defined(FIXTURE_sum_loop)
  return sum_loop(a[0]);
#elif defined(FIXTURE_ackermann)
  return ack(a[0], a[1]);
#elif defined(FIXTURE_tak)
  return tak(a[0], a[1], a[2], a[3]);
#elif defined(FIXTURE_gcd)
  return gcd(a[0], a[1]);
#elif defined(FIXTURE_collatz)
  return collatz_sum(a[0]);
#elif defined(FIXTURE_prime_count)
  return prime_count(a[0]);
#elif defined(FIXTURE_even_odd)
  return is_even(a[0]) ? 1 : 0;
#elif defined(FIXTURE_sfib)
  return sfib(a[0]);
#else
#error "no idiomatic entry for this fixture"
#endif
}

uint64_t row_heap(void) { return UINT64_MAX; }
