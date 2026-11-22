/* K5 factorial: idiomatic C + GMP twin of Factorial.lean (binary-splitting n!). */
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

static void prod_range(uint64_t lo, uint64_t hi, mpz_t out) {
  if (lo > hi) {
    mpz_set_ui(out, 1);
    return;
  }
  if (lo == hi) {
    mpz_set_ui(out, (unsigned long)lo);
    return;
  }
  if (lo + 1 == hi) {
    mpz_set_ui(out, (unsigned long)lo);
    mpz_mul_ui(out, out, (unsigned long)hi);
    return;
  }
  uint64_t mid = lo + (hi - lo) / 2;
  mpz_t left, right;
  mpz_inits(left, right, NULL);
  prod_range(lo, mid, left);
  prod_range(mid + 1, hi, right);
  mpz_mul(out, left, right);
  mpz_clears(left, right, NULL);
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: factorial N\n"); return 1; }
  uint64_t n = strtoull(argv[1], NULL, 10);
  mpz_t res;
  mpz_init(res);
  if (n <= 1) mpz_set_ui(res, 1);
  else prod_range(1, n, res);
  printf("%" PRIu64 "\n", bignum_digest(res));
  mpz_clear(res);
  return 0;
}
