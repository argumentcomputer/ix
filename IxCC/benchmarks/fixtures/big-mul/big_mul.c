/* K5 big-mul: idiomatic C + GMP twin of BigMul.lean. */
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

static uint64_t lcg(uint64_t s) {
  return (s * 1103515245ULL + 12345ULL) & 0x7fffffffULL;
}

static uint64_t mk_limb(uint64_t seed) {
  uint64_t s1 = lcg(seed & 0x7fffffffULL);
  uint64_t s2 = lcg(s1);
  uint64_t hi31 = (s1 & 0x3fffffffULL) + 0x40000000ULL;
  uint64_t lo31 = s2 | 1ULL;
  return (hi31 << 31) + lo31;
}

static void mk_big(uint64_t seed, uint64_t limbs, mpz_t out) {
  if (limbs <= 1) {
    mpz_set_ui(out, (unsigned long)mk_limb(seed));
    return;
  }
  uint64_t half = limbs / 2;
  mpz_t lo, hi;
  mpz_inits(lo, hi, NULL);
  mk_big(seed, half, lo);
  mk_big((seed + half * 2654435761ULL) & 0x7fffffffULL, limbs - half, hi);
  mpz_mul_2exp(hi, hi, (mp_bitcnt_t)(half * 64));
  mpz_add(out, hi, lo);
  mpz_clears(lo, hi, NULL);
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: big-mul LIMBS REPS\n"); return 1; }
  uint64_t limbs = strtoull(argv[1], NULL, 10);
  uint64_t reps = strtoull(argv[2], NULL, 10);
  if (limbs == 0) limbs = 1;
  mp_bitcnt_t bits = (mp_bitcnt_t)(limbs * 64 - 1);

  mpz_t a, b, p, lo, hi;
  mpz_inits(a, b, p, lo, hi, NULL);
  mk_big(17, limbs, a);
  mk_big(53, limbs, b);

  for (uint64_t r = 0; r < reps; r++) {
    mpz_mul(p, a, b);
    mpz_tdiv_r_2exp(lo, p, bits);
    mpz_tdiv_q_2exp(hi, p, bits);
    mpz_xor(a, lo, hi);
    mpz_tdiv_r_2exp(a, a, bits);
    mpz_setbit(a, bits - 1);
    mpz_setbit(a, 0);
  }

  printf("%" PRIu64 "\n", bignum_digest(a));
  mpz_clears(a, b, p, lo, hi, NULL);
  return 0;
}
