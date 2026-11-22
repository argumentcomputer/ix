/* K5 pi-digits: idiomatic C + GMP twin of PiDigits.lean (CLBG/Gibbons spigot). */
#include <gmp.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t pi_digits(uint64_t n) {
  mpz_t num, den, acc, tmp1, tmp2;
  mpz_inits(num, den, acc, tmp1, tmp2, NULL);
  mpz_set_ui(num, 1);
  mpz_set_ui(den, 1);
  mpz_set_ui(acc, 0);

  uint64_t k = 0;
  uint64_t emitted = 0;
  uint64_t last9 = 0;
  uint64_t h = 0;

  while (emitted < n) {
    k++;
    unsigned long k2 = (unsigned long)(2 * k + 1);
    mpz_addmul_ui(acc, num, 2);
    mpz_mul_ui(acc, acc, k2);
    mpz_mul_ui(den, den, k2);
    mpz_mul_ui(num, num, (unsigned long)k);

    if (mpz_cmp(num, acc) > 0) continue;

    /* d3 = (3*num + acc) / den */
    mpz_mul_ui(tmp1, num, 3);
    mpz_add(tmp1, tmp1, acc);
    mpz_tdiv_q(tmp2, tmp1, den);
    unsigned long d3 = mpz_get_ui(tmp2);

    /* d4 = (4*num + acc) / den */
    mpz_add(tmp1, tmp1, num);
    mpz_tdiv_q(tmp2, tmp1, den);
    unsigned long d4 = mpz_get_ui(tmp2);

    if (d3 != d4) continue;

    last9 = (last9 * 10ULL + (uint64_t)d3) % 1000000000ULL;
    h = (h * 31ULL + (uint64_t)d3) % 1000000007ULL;
    emitted++;

    mpz_submul_ui(acc, den, d3);
    mpz_mul_ui(acc, acc, 10);
    mpz_mul_ui(num, num, 10);
  }

  mpz_clears(num, den, acc, tmp1, tmp2, NULL);
  return last9 * 1000000007ULL + h;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: pi-digits N\n"); return 1; }
  printf("%" PRIu64 "\n", pi_digits(strtoull(argv[1], NULL, 10)));
  return 0;
}
