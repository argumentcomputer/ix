/*
 * The early backend probe's adapter for the tagged C twin rows (untrusted measurement code):
 * tag the arguments (n -> 2n + 1), call twins.c, untag the result. With
 * -DNATURAL it calls the fixtures' untagged algorithms instead.
 */
#include <stdint.h>

#ifdef NATURAL
uint64_t natural_fib(uint64_t n);
uint64_t natural_sum_loop(uint64_t n);
uint64_t natural_gcd(uint64_t a, uint64_t b);

void row_init(void) {}
uint64_t row_fib(uint64_t n) { return natural_fib(n); }
uint64_t row_sum_loop(uint64_t n) { return natural_sum_loop(n); }
uint64_t row_gcd(uint64_t a, uint64_t b) { return natural_gcd(a, b); }
#else
uint64_t twin_fib(uint64_t n);
uint64_t twin_sum_loop(uint64_t n);
uint64_t twin_gcd(uint64_t a, uint64_t b);

void row_init(void) {}
uint64_t row_fib(uint64_t n) { return twin_fib(2 * n + 1) >> 1; }
uint64_t row_sum_loop(uint64_t n) { return twin_sum_loop(2 * n + 1) >> 1; }
uint64_t row_gcd(uint64_t a, uint64_t b) { return twin_gcd(2 * a + 1, 2 * b + 1) >> 1; }
#endif
