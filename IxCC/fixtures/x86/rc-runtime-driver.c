/* Untrusted, independent native RC controls. Reuse the existing tested stack
 * trampoline and callee-saved sentinels. All allocation/release is generated
 * Lir. C initializes fixture fields and independently checks complete values. */
#define main legacy_runtime_main
#include "fixtures/x86/runtime_driver.c"
#undef main

extern void cx_rc_alloc2(void);
extern void cx_rc_alloc31(void);
extern void cx_rc_alloc0(void);
extern void cx_rc_alloc32(void);
extern void cx_rc_inc(void);
extern void cx_rc_dec(void);

static void *test_top;
static const uint64_t test_budget = 65536 - 4096;
static unsigned assertions;

static void require(int condition, const char *label) {
  ++assertions;
  if (!condition) { fprintf(stderr, "FAIL %s\n", label); exit(1); }
}

static uint64_t word(uint64_t p) {
  uint64_t v;
  require(readable(p, 8), "bounded fixture read");
  memcpy(&v, (void *)(uintptr_t)p, 8);
  return v;
}

static void putword(uint64_t p, uint64_t v) {
  require(readable(p, 8), "bounded fixture write");
  memcpy((void *)(uintptr_t)p, &v, 8);
}

static uint64_t context_at(int offset) {
  return (uint64_t)(uintptr_t)(region + 64 + offset);
}

static struct result invoke(void (*fn)(void), uint64_t a, uint64_t b) {
  const uint64_t args[6] = {(uint64_t)(uintptr_t)region, a, b, 0, 0, 0};
  struct result r;
  call_on_stack(args, &r, fn, test_top);
  require(saved_ok(&r), "native callee-saved registers and stack pointer");
  return r;
}

static uint64_t ok(void (*fn)(void), uint64_t arg) {
  struct result r = invoke(fn, arg, 0);
  require(r.rax == 0, "native success status");
  return r.rdx;
}

static void status(void (*fn)(void), uint64_t arg, uint64_t expected) {
  struct result r = invoke(fn, arg, 0);
  require(r.rax == expected, "native failure status");
}

static uint64_t fresh(uint64_t capacity) {
  putword(context_at(-48), test_budget);
  struct result r = invoke(cx_init, region_size, test_budget);
  require(r.rax == 0, "cx_init succeeds");
  uint64_t start = ctx_field(-40);
  require(start % 64 == 0 && readable(start, capacity), "object region");
  putword(context_at(-32), start + capacity);
  return start;
}

static void fields(uint64_t p, uint64_t a, uint64_t b) {
  require(word(p) == UINT64_C(66306), "new unique scanned class3 tag1 header");
  putword(p + 8, a); putword(p + 16, b);
}

static void list_value(uint64_t p, const uint64_t *values, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    require(!(p & 7) && p != 0, "list pointer alignment");
    uint64_t h = word(p);
    require((h & UINT64_C(0xffffffff)) == UINT64_C(66306), "complete live list layout");
    require((h >> 32) < UINT64_C(0x80000000), "positive dynamic list count");
    require(word(p + 8) == 2 * values[i] + 1, "full list element and order");
    p = word(p + 16);
  }
  require(p == 1, "exact list length and nil");
}

static void cycles(void) {
  uint64_t start = fresh(48);
  for (unsigned j = 0; j < 50; ++j) {
    uint64_t a = ok(cx_rc_alloc2, 0); fields(a, 7, 1);
    uint64_t b = ok(cx_rc_alloc2, 0); fields(b, 15, a);
    require(a != b && (a == start || a == start + 24) &&
      (b == start || b == start + 24), "exact two-cell address reuse");
    const uint64_t values[] = {7, 3}, tail[] = {3};
    list_value(b, values, 2);
    ok(cx_rc_inc, b);
    require(word(b) == UINT64_C(4295033602), "increment exact count");
    ok(cx_rc_dec, b);
    require(word(b) == UINT64_C(66306), "shared decrement preserves live body");
    list_value(b, values, 2); list_value(a, tail, 1);
    ok(cx_rc_dec, b);
    require(ctx_field(24) == b && word(b) == a && word(a) == 0,
      "completed parent then child free chain");
    require(ctx_field(-40) == start + 48, "same-region bump never reset or advanced");
  }
  puts("PASS 50 same-region two-cell cycles, full values, exact free-chain reuse");
}

static void aliases(void) {
  for (unsigned external = 0; external < 2; ++external) {
    uint64_t start = fresh(48);
    uint64_t child = ok(cx_rc_alloc2, 0); fields(child, 87, 1);
    ok(cx_rc_inc, child);
    if (external) ok(cx_rc_inc, child);
    uint64_t parent = ok(cx_rc_alloc2, 0); fields(parent, child, child);
    ok(cx_rc_dec, parent);
    if (external) {
      const uint64_t values[] = {43};
      list_value(child, values, 1);
      require(word(child) == UINT64_C(66306), "external alias remains unique");
      require(ctx_field(24) == parent && word(parent) == 0, "only parent freed");
      ok(cx_rc_dec, child);
      require(ctx_field(24) == child && word(child) == parent && word(parent) == 0,
        "external output drop reclaims both");
    } else {
      require(ctx_field(24) == parent && word(parent) == child && word(child) == 0,
        "two repeated edges free child exactly once");
    }
    require(ctx_field(-40) == start + 48, "alias case allocation count");
  }
  puts("PASS repeated edges and external shared-child preservation/release");
}

static void deep_list(void) {
  uint64_t start = fresh(64 * 24), p = 1;
  for (unsigned i = 0; i < 64; ++i) {
    uint64_t a = ok(cx_rc_alloc2, 0); fields(a, 2 * i + 1, p); p = a;
  }
  uint64_t values[64];
  for (unsigned i = 0; i < 64; ++i) values[i] = 63 - i;
  list_value(p, values, 64);
  ok(cx_rc_dec, p);
  uint64_t cursor = ctx_field(24);
  for (unsigned i = 0; i < 64; ++i) {
    require(cursor == start + 24 * (63 - i), "deep free-chain exact order");
    cursor = word(cursor);
  }
  require(cursor == 0, "deep chain finite and all64 reclaimed");
  puts("PASS iterative64-cell release and complete constructor values");
}

static void boundaries(void) {
  uint64_t start = fresh(23);
  status(cx_rc_alloc2, 0, 1);
  require(ctx_field(-40) == start && ctx_field(24) == 0, "short allocation unchanged");
  putword(context_at(-32), start + 24);
  uint64_t p = ok(cx_rc_alloc2, 0); fields(p, 7, 1);
  require(p == start && ctx_field(-40) == start + 24, "exact24-byte fit");
  ok(cx_rc_dec, p);
  require(ok(cx_rc_alloc2, 0) == p, "recycle succeeds at exhausted bump limit");
  fields(p, 7, 1);
  putword(p, UINT64_C(0x7fffffff00010302));
  status(cx_rc_inc, p, 1);
  require(word(p) == UINT64_C(0x7fffffff00010302) && word(p + 8) == 7 && word(p + 16) == 1,
    "overflow preserves full live cell");
  putword(p, UINT64_C(0x8000000000010302));
  ok(cx_rc_inc, p); ok(cx_rc_dec, p);
  require(word(p) == UINT64_C(0x8000000000010302) && word(p + 8) == 7 && word(p + 16) == 1,
    "static operations preserve full cell");
  uint64_t bump = ctx_field(-40), head = ctx_field(24);
  ok(cx_rc_inc, 1); ok(cx_rc_dec, 1);
  require(ctx_field(-40) == bump && ctx_field(24) == head, "immediate operations no-op");
  status(cx_rc_alloc0, 0, 4); status(cx_rc_alloc32, 0, 4);
  require(ctx_field(-40) == bump && ctx_field(24) == head, "unsupported layouts trap before mutation");
  putword(context_at(-48), 0);
  status(cx_rc_inc, p, 2);
  require(word(p) == UINT64_C(0x8000000000010302), "stack refusal preserves cell");
  putword(context_at(-48), test_budget);
  start = fresh(256);
  p = ok(cx_rc_alloc31, 0);
  require(p == start && ctx_field(-40) == start + 256 && word(p) == UINT64_C(73759),
    "class32 exact256-byte allocation");
  for (unsigned i = 0; i < 31; ++i) putword(p + 8 + 8 * i, 2 * i + 1);
  ok(cx_rc_dec, p);
  require(ctx_field(256) == p && word(p) == 0, "class32 reclamation");
  puts("PASS exact/short heap, count overflow, static/immediate, layout and stack boundaries");
}

int main(void) {
  region_size = 8192;
  region = mmap(NULL, region_size, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  require(region != MAP_FAILED, "region mmap");
  uint8_t *stack = mmap(NULL, 65536 + GUARD, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  require(stack != MAP_FAILED && mprotect(stack, GUARD, PROT_NONE) == 0, "guarded native stack");
  test_top = stack + GUARD + 65536;
  cycles(); aliases(); deep_list(); boundaries();
  printf("PASS native H2 procedures: %u independent assertions\n", assertions);
  require(munmap(region, region_size) == 0 && munmap(stack, 65536 + GUARD) == 0, "unmap");
  return 0;
}
