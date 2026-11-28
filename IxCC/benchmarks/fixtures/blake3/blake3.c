/* K4 blake3: idiomatic portable scalar C99 twin of Blake3.lean
 * (standard unkeyed 32-byte BLAKE3 on buf[i] = i % 251). */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint32_t IV[8] = {
  0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au,
  0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u
};

static const uint8_t MSG_SCHED[7][16] = {
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
  {2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8},
  {3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1},
  {10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6},
  {12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4},
  {9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7},
  {11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13}
};

static inline uint32_t rotr32(uint32_t w, unsigned c) {
  return (w >> c) | (w << (32u - c));
}

static inline void g(uint32_t st[16], size_t a, size_t b, size_t c, size_t d,
                     uint32_t mx, uint32_t my) {
  st[a] = st[a] + st[b] + mx;
  st[d] = rotr32(st[d] ^ st[a], 16);
  st[c] = st[c] + st[d];
  st[b] = rotr32(st[b] ^ st[c], 12);
  st[a] = st[a] + st[b] + my;
  st[d] = rotr32(st[d] ^ st[a], 8);
  st[c] = st[c] + st[d];
  st[b] = rotr32(st[b] ^ st[c], 7);
}

static void compress(const uint32_t cv[8], const uint32_t msg[16],
                     uint64_t counter, uint32_t block_len, uint32_t flags,
                     uint32_t out[8]) {
  uint32_t st[16];
  for (int i = 0; i < 8; i++) st[i] = cv[i];
  st[8] = IV[0];
  st[9] = IV[1];
  st[10] = IV[2];
  st[11] = IV[3];
  st[12] = (uint32_t)counter;
  st[13] = (uint32_t)(counter >> 32);
  st[14] = block_len;
  st[15] = flags;
  for (int r = 0; r < 7; r++) {
    const uint8_t *s = MSG_SCHED[r];
    g(st, 0, 4, 8, 12, msg[s[0]], msg[s[1]]);
    g(st, 1, 5, 9, 13, msg[s[2]], msg[s[3]]);
    g(st, 2, 6, 10, 14, msg[s[4]], msg[s[5]]);
    g(st, 3, 7, 11, 15, msg[s[6]], msg[s[7]]);
    g(st, 0, 5, 10, 15, msg[s[8]], msg[s[9]]);
    g(st, 1, 6, 11, 12, msg[s[10]], msg[s[11]]);
    g(st, 2, 7, 8, 13, msg[s[12]], msg[s[13]]);
    g(st, 3, 4, 9, 14, msg[s[14]], msg[s[15]]);
  }
  for (int i = 0; i < 8; i++) out[i] = st[i] ^ st[i + 8];
}

static void block_words(const uint8_t *buf, size_t len, uint32_t out[16]) {
  uint8_t tmp[64];
  memset(tmp, 0, 64);
  if (len > 0) memcpy(tmp, buf, len);
  for (int i = 0; i < 16; i++) {
    out[i] = (uint32_t)tmp[4 * i]
           | ((uint32_t)tmp[4 * i + 1] << 8)
           | ((uint32_t)tmp[4 * i + 2] << 16)
           | ((uint32_t)tmp[4 * i + 3] << 24);
  }
}

typedef struct {
  uint32_t cv[8];
  uint32_t block[16];
  uint32_t block_len;
  uint64_t counter;
  uint32_t flags;
} Output;

static void chaining_value(const Output *o, uint32_t out[8]) {
  compress(o->cv, o->block, o->counter, o->block_len, o->flags, out);
}

static void chunk_output(const uint8_t *buf, size_t len, uint64_t counter, Output *out) {
  uint32_t cv[8];
  memcpy(cv, IV, sizeof(cv));
  int is_start = 1;
  size_t off = 0;
  while (len - off > 64) {
    uint32_t words[16];
    block_words(buf + off, 64, words);
    uint32_t next[8];
    compress(cv, words, counter, 64, is_start ? 1u : 0u, next);
    memcpy(cv, next, sizeof(cv));
    is_start = 0;
    off += 64;
  }
  memcpy(out->cv, cv, sizeof(cv));
  block_words(buf + off, len - off, out->block);
  out->block_len = (uint32_t)(len - off);
  out->counter = counter;
  out->flags = (is_start ? 1u : 0u) | 2u;
}

static size_t largest_pow2_lt(size_t n) {
  size_t p = 1;
  while (p * 2 < n) p *= 2;
  return p;
}

static void subtree(const uint8_t *buf, size_t len, uint64_t counter, Output *out) {
  if (len <= 1024) {
    chunk_output(buf, len, counter, out);
    return;
  }
  size_t split = largest_pow2_lt(len);
  Output left, right;
  subtree(buf, split, counter, &left);
  subtree(buf + split, len - split, counter + (uint64_t)(split / 1024), &right);
  memcpy(out->cv, IV, sizeof(IV));
  chaining_value(&left, out->block);
  chaining_value(&right, out->block + 8);
  out->block_len = 64;
  out->counter = 0;
  out->flags = 4u;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: blake3 N\n");
    return 1;
  }
  size_t n = (size_t)strtoull(argv[1], NULL, 10);
  uint8_t *buf = (uint8_t *)malloc(n > 0 ? n : 1);
  if (!buf) return 1;
  for (size_t i = 0; i < n; i++) buf[i] = (uint8_t)(i % 251);
  Output root;
  subtree(buf, n, 0, &root);
  uint32_t digest[8];
  compress(root.cv, root.block, 0, root.block_len, root.flags | 8u, digest);
  for (int i = 0; i < 8; i++) {
    uint32_t w = digest[i];
    printf("%02x%02x%02x%02x",
           w & 0xffu, (w >> 8) & 0xffu, (w >> 16) & 0xffu, (w >> 24) & 0xffu);
  }
  putchar('\n');
  free(buf);
  return 0;
}
