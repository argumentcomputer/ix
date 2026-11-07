/* Independent scratch behavior oracle. The context is initialized ONCE.
 * Real source roots and generated Lir release procedures perform every object
 * allocation, write, and reclamation. C maps the bounded region and reads
 * complete results/free chains; it does not write allocator metadata after
 * cx_init. Preserve the production ABI trampoline. */
#define main legacy_runtime_main
#include "fixtures/x86/runtime_driver.c"
#undef main

extern void cx_drop(void);

static unsigned long checks, calls;

static void require(int condition, const char *label) {
  ++checks;
  if (!condition) {
    fprintf(stderr, "FAIL call %lu: %s\n", calls, label);
    exit(1);
  }
}

static uint64_t load_word(uint64_t p) {
  uint64_t v;
  require(readable(p, 8), "bounded independent word read");
  memcpy(&v, (void *)(uintptr_t)p, 8);
  return v;
}

static void print_dump(uint64_t start, uint64_t bump) {
  uint64_t base = (uint64_t)(uintptr_t)region;
  require(start <= bump && readable(start, bump - start), "bounded full object dump");
  printf("dump %llu %llu %llu ", (unsigned long long)base,
    (unsigned long long)start, (unsigned long long)bump);
  for (uint64_t p = start; p < bump; ++p) printf("%02x", region[p - base]);
  putchar('\n');
}

static void all_reclaimed(uint64_t start, uint64_t bump, uint64_t capacity) {
  require(bump == start + capacity && capacity % 24 == 0,
    "same tight arena: bump stable at capacity without reinitialization");
  require(ctx_field(-32) == (uint64_t)(uintptr_t)region + region_size,
    "cx_init arena limit unchanged");
  unsigned char seen[4096] = {0};
  uint64_t n = capacity / 24, p = ctx_field(24), count = 0;
  require(n <= sizeof seen, "bounded independent free-chain oracle");
  while (p != 0) {
    require(p >= start && p < bump && (p - start) % 24 == 0,
      "free cell is an exact allocated address");
    uint64_t index = (p - start) / 24;
    require(!seen[index], "no duplicate free cell or cycle");
    seen[index] = 1;
    ++count;
    p = load_word(p);
  }
  require(count == n, "every allocated cell is reclaimed exactly once");
  for (uint64_t i = 0; i < n; ++i) require(seen[i], "no leaked allocated address");
  for (int c = 1; c <= 71; ++c)
    if (c != 3) require(ctx_field(8 * c) == 0, "other size classes remain empty");
}

int main(int argc, char **argv) {
  uint64_t stack_size = 1048576, capacity = 0;
  const char *type = NULL, *sig = "";
  region_size = 131072;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--capacity") && i + 1 < argc) capacity = strtoull(argv[++i], NULL, 0);
    else if (!strcmp(argv[i], "--type") && i + 1 < argc) type = argv[++i];
    else if (!strcmp(argv[i], "--sig") && i + 1 < argc) sig = argv[++i];
    else { fprintf(stderr, "unexpected reuse-driver option\n"); return 2; }
  }
  require(type && capacity && capacity <= 24 * 4096, "bounded typed reuse case");
  region_size = capacity + 640;
  if (region_size < 4096) region_size = 4096;
  const char *end;
  int ty = parse_ty(type, &end);
  require(ty >= -1 && *end == 0 && parse_sig(sig) == 0, "valid independent decoder type");
  region = mmap(NULL, region_size, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  require(region != MAP_FAILED, "private arena mapping");
  uint8_t *stack = mmap(NULL, stack_size + GUARD, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK, -1, 0);
  require(stack != MAP_FAILED && mprotect(stack, GUARD, PROT_NONE) == 0,
    "guarded native stack");
  void *top = stack + GUARD + stack_size;
  uint64_t budget = stack_size - RESERVE;
  memcpy(region + 16, &budget, 8);
  const uint64_t init_args[6] = {(uint64_t)(uintptr_t)region, region_size, budget, 0, 0, 0};
  struct result r;
  call_on_stack(init_args, &r, cx_init, top);
  require(r.rax == 0 && saved_ok(&r), "single initialization status and ABI");
  uint64_t start = ctx_field(-40), limit = ctx_field(-32);
  require(start % 64 == 0 && readable(start, capacity) && start + capacity <= limit,
    "bounded actual cx_init arena contains expected high water");
  require(limit == (uint64_t)(uintptr_t)region + region_size,
    "actual cx_init limit matches mapped region");
  char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    ++calls;
    uint64_t args[6] = {(uint64_t)(uintptr_t)region, 0, 0, 0, 0, 0};
    char *cursor = line, *next;
    for (int i = 1; i < 6; ++i) {
      uint64_t value = strtoull(cursor, &next, 0);
      if (next == cursor) break;
      args[i] = value; cursor = next;
    }
    call_on_stack(args, &r, ENTRY, top);
    require(r.rax == 0 && saved_ok(&r), "actual source root status and ABI");
    uint64_t result = r.rdx, bump = ctx_field(-40);
    str_t value = {NULL, 0, 0};
    require(decode(result, ty, region_size / 8, &value) == 0, "complete constructor-tree decoding");
    if (!(result & 1)) require((load_word(result) >> 32) == 0, "dynamically unique output root");
    printf("0 %llu 1 %s\n", (unsigned long long)result, value.buf);
    free(value.buf);
    print_dump(start, bump);
    const uint64_t drop_args[6] = {(uint64_t)(uintptr_t)region, result, 0, 0, 0, 0};
    call_on_stack(drop_args, &r, cx_drop, top);
    require(r.rax == 0 && r.rdx == 1 && saved_ok(&r), "generated complete output-drop status and ABI");
    require(ctx_field(-40) == bump, "release does not change bump");
    all_reclaimed(start, bump, capacity);
    /* A second ordinary protocol row carries the actual free head and full
     * post-release memory for the independent Lean address-set oracle. */
    printf("0 %llu 1 #0\n", (unsigned long long)ctx_field(24));
    print_dump(start, bump);
    fflush(stdout);
  }
  require(calls >= 50, "at least fifty real-source calls in one arena");
  fprintf(stderr, "PASS init=1 calls=%lu capacity=%llu region=%llu checks=%lu; complete values, all cells reclaimed, stable bump, no C metadata writes after init\n",
    calls, (unsigned long long)capacity, (unsigned long long)region_size, checks);
  require(munmap(region, region_size) == 0 && munmap(stack, stack_size + GUARD) == 0,
    "release fixture mappings");
  return 0;
}
