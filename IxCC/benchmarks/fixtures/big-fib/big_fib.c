/* K5 big-fib: idiomatic C + GMP twin of BigFib.lean (fast doubling F(n)). */
#include <gmp.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t bignum_digest(const mpz_t v) {
  if (mpz_sgn(v) == 0) return 0;
  uint64_t bl = (uint64_t)mpz_sizeinbase(v, 2);
  uint64_t top;
  if (bl > 32) {
    mpz_t tmp;
    mpz_init(tmp);
    mpz_fdiv_q_2exp(tmp, v, bl - 32);
    top = (uint64_t)mpz_get_ui(tmp);
    mpz_clear(tmp);
  } else {
    top = (uint64_t)mpz_get_ui(v);
  }
  uint64_t rem = (uint64_t)mpz_fdiv_ui(v, 1000000007UL);
  return bl * 1000000007ULL + ((rem * 31ULL + top) % 1000000007ULL);
}

static void fib_pair(uint64_t n, mpz_t out_a, mpz_t out_b) {
  if (n == 0) {
    mpz_set_ui(out_a, 0);
    mpz_set_ui(out_b, 1);
    return;
  }
  mpz_t a, b, t, c, d;
  mpz_inits(a, b, t, c, d, NULL);
  fib_pair(n / 2, a, b);
  /* c = a * (2*b - a) */
  mpz_mul_2exp(t, b, 1);
  mpz_sub(t, t, a);
  mpz_mul(c, a, t);
  /* d = a*a + b*b */
  mpz_mul(d, a, a);
  mpz_mul(t, b, b);
  mpz_add(d, d, t);
  if ((n & 1ULL) == 0) {
    mpz_set(out_a, c);
    mpz_set(out_b, d);
  } else {
    mpz_set(out_a, d);
    mpz_add(out_b, c, d);
  }
  mpz_clears(a, b, t, c, d, NULL);
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: big-fib N\n"); return 1; }
  uint64_t n = strtoull(argv[1], NULL, 10);
  mpz_t a, b;
  mpz_inits(a, b, NULL);
  fib_pair(n, a, b);
  printf("%" PRIu64 "\n", bignum_digest(a));
  mpz_clears(a, b, NULL);
  return 0;
}
