/* K4 array-qsort: idiomatic C99 in-place quicksort twin of ArrayQsort.lean. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static inline void swap_u32(uint32_t *a, size_t i, size_t j) {
  uint32_t tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

static size_t partition(uint32_t *a, size_t lo, size_t hi) {
  size_t mid = lo + (hi - lo) / 2;
  if (a[mid] < a[lo]) swap_u32(a, lo, mid);
  if (a[hi] < a[lo]) swap_u32(a, lo, hi);
  if (a[hi] < a[mid]) swap_u32(a, mid, hi);
  uint32_t pivot = a[mid];
  size_t i = lo, j = hi;
  for (;;) {
    while (a[i] < pivot) i++;
    while (a[j] > pivot) j--;
    if (i >= j) return j;
    swap_u32(a, i, j);
    i++;
    j--;
  }
}

static void qsort_u32(uint32_t *a, size_t lo, size_t hi) {
  while (lo < hi) {
    size_t p = partition(a, lo, hi);
    if (p - lo < hi - p) {
      qsort_u32(a, lo, p);
      lo = p + 1;
    } else {
      qsort_u32(a, p + 1, hi);
      hi = p;
    }
  }
}

static uint64_t entry(uint64_t n) {
  uint32_t *a = (uint32_t *)malloc((n > 0 ? (size_t)n : 1) * sizeof(uint32_t));
  if (!a) return 0;
  uint32_t s = 123456789u;
  for (uint64_t i = 0; i < n; i++) {
    s = s * 1664525u + 1013904223u;
    a[i] = s;
  }
  if (n > 1) qsort_u32(a, 0, (size_t)(n - 1));
  int sorted = 1;
  for (uint64_t i = 0; i + 1 < n; i++) {
    if (a[i] > a[i + 1]) { sorted = 0; break; }
  }
  uint64_t res = 0;
  if (sorted) {
    uint64_t h = 0;
    for (uint64_t i = 0; i < n; i++) {
      h = (h * 31ULL + (uint64_t)a[i]) % 1000000007ULL;
    }
    res = n * 1000000007ULL + h;
  }
  free(a);
  return res;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: array-qsort N\n"); return 1; }
  printf("%" PRIu64 "\n", entry(strtoull(argv[1], NULL, 10)));
  return 0;
}
