/*
 * The Phase 1 runtime driver (design note plans/x86-v2/04-runtime.md §6,
 * §8.1; untrusted, pinned in the trust ledger).
 *
 * It links with an object that Backend.compile makes from Rt.lower's
 * output. The object exports
 *
 *     cx_result cx_init(void *region, uint64_t size, uint64_t stack_budget);
 *     cx_result ENTRY(void *region, uint64_t a1, ..., uint64_t a5);
 *
 * (ENTRY is the root's wrapper, -DENTRY=cx_<root>), each returning
 * {status, value} in rax:rdx: 0 ok, 1 heap, 2 stack, 3 natOverflow, 4 trap.
 *
 * The driver maps one private, writable region (--region BYTES, default
 * 64 MiB) and one stack for the program (--stack BYTES, default 8 MiB, with
 * a guard page below it). For each input line "a1 ... a5" it stores
 * stack_budget = the stack size less 4 KiB at region + 16 (ctx - 48, where
 * every export wrapper reads it), calls cx_init on the whole region with
 * that budget, then the root, both on the mapped stack with the same stack
 * pointer and return address and with sentinels in rbx, rbp and r12-r15,
 * and prints
 *
 *     status value ok [obs] [ns]
 *
 * where ok is 1 when the six sentinels and rsp came back unchanged. With
 * --type T --sig S (the text forms of Rt.FoTy.encode and Rt.Sig.encode) it
 * decodes the value as a C mirror of Rt.readback (fuel (limit - base)/8)
 * and prints the observation as Rt.renderObs does ("-" if it does not read
 * back, or the status is not 0); like the model's readback, the decoder
 * reads only the region from region + 16. With --time it prints the root call's wall
 * time in nanoseconds. With --dump it then prints
 *
 *     dump base start bump hex
 *
 * with the object area [start, bump) in hex, so a test can read the value
 * back in Lean and compare with the C decoder.
 *
 * Contract (ledgered): the region is private, writable, untouched between
 * cx_init and the root's return, and disjoint from .rodata and from the
 * stack; the stack budget leaves at least 4 KiB above the guard page for
 * the wrapper frame and the 64-byte slack of the largest frameless leaf.
 * Recheck.sound's model of these calls is X86.Driver and X86.Linked (a
 * specification assumption in docs/trusted-extern-ledger.md).
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>

#ifndef ENTRY
#error "ENTRY must name the root's exported wrapper"
#endif

struct result {
  uint64_t rax, rdx, rbx, rbp, r12, r13, r14, r15, rsp_before, rsp_after;
};

extern void ENTRY(void);
extern void cx_init(void);
void call_on_stack(const uint64_t *args, struct result *out, void (*fn)(void), void *top);

/* rdi = args (region, a1..a5), rsi = out, rdx = fn, rcx = stack top
 * (16-aligned). The C stack pointer and out are kept on the new stack. */
__asm__(
    ".text\n"
    ".globl call_on_stack\n"
    ".type call_on_stack, @function\n"
    "call_on_stack:\n"
    "  push %rbx\n"
    "  push %rbp\n"
    "  push %r12\n"
    "  push %r13\n"
    "  push %r14\n"
    "  push %r15\n"
    "  mov %rsp, %rax\n"
    "  mov %rcx, %rsp\n"
    "  push %rax\n"
    "  push %rsi\n"
    "  mov %rsp, 64(%rsi)\n"
    "  mov %rdx, %rax\n"
    "  mov 40(%rdi), %r9\n"
    "  mov 32(%rdi), %r8\n"
    "  mov 24(%rdi), %rcx\n"
    "  mov 16(%rdi), %rdx\n"
    "  mov 8(%rdi), %rsi\n"
    "  mov 0(%rdi), %rdi\n"
    "  movabs $0x1111111111111111, %rbx\n"
    "  movabs $0x2222222222222222, %rbp\n"
    "  movabs $0x3333333333333333, %r12\n"
    "  movabs $0x4444444444444444, %r13\n"
    "  movabs $0x5555555555555555, %r14\n"
    "  movabs $0x6666666666666666, %r15\n"
    "  call *%rax\n"
    "  mov (%rsp), %rcx\n"
    "  mov %rax, 0(%rcx)\n"
    "  mov %rdx, 8(%rcx)\n"
    "  mov %rbx, 16(%rcx)\n"
    "  mov %rbp, 24(%rcx)\n"
    "  mov %r12, 32(%rcx)\n"
    "  mov %r13, 40(%rcx)\n"
    "  mov %r14, 48(%rcx)\n"
    "  mov %r15, 56(%rcx)\n"
    "  mov %rsp, 72(%rcx)\n"
    "  mov 8(%rsp), %rsp\n"
    "  pop %r15\n"
    "  pop %r14\n"
    "  pop %r13\n"
    "  pop %r12\n"
    "  pop %rbp\n"
    "  pop %rbx\n"
    "  ret\n"
    ".size call_on_stack, .-call_on_stack\n");

#define GUARD ((size_t)4096)
#define RESERVE ((uint64_t)4096)

static uint8_t *region;
static uint64_t region_size;

static int saved_ok(const struct result *r) {
  return r->rbx == 0x1111111111111111ULL && r->rbp == 0x2222222222222222ULL &&
         r->r12 == 0x3333333333333333ULL && r->r13 == 0x4444444444444444ULL &&
         r->r14 == 0x5555555555555555ULL && r->r15 == 0x6666666666666666ULL &&
         r->rsp_after == r->rsp_before;
}

static uint64_t ctx_field(int offset) {
  uint64_t v;
  memcpy(&v, region + 64 + offset, 8);
  return v;
}

/* ---- The type descriptor (Rt.FoTy.encode, Rt.Sig.encode) ---- */

typedef struct {
  int n;
  int *fields; /* -1: Nat, k >= 0: inductive k */
} ctor_t;

typedef struct {
  int n;
  ctor_t *ctors;
} ind_t;

static ind_t *inds;
static int ninds;

static int parse_ty(const char *s, const char **end) {
  if (*s == 'n') {
    *end = s + 1;
    return -1;
  }
  if (*s == 'i') {
    char *e;
    long k = strtol(s + 1, &e, 10);
    if (e == s + 1 || k < 0) return -2;
    *end = e;
    return (int)k;
  }
  return -2;
}

/* "()()/(n,n)/()(n)": inductives by '/', constructors in parentheses. */
static int parse_sig(const char *s) {
  ninds = 0;
  inds = NULL;
  if (*s == 0) return 0;
  for (;;) {
    inds = realloc(inds, sizeof(ind_t) * (size_t)(ninds + 1));
    ind_t *ind = &inds[ninds++];
    ind->n = 0;
    ind->ctors = NULL;
    while (*s == '(') {
      s++;
      ind->ctors = realloc(ind->ctors, sizeof(ctor_t) * (size_t)(ind->n + 1));
      ctor_t *c = &ind->ctors[ind->n++];
      c->n = 0;
      c->fields = NULL;
      while (*s != ')') {
        const char *e;
        int t = parse_ty(s, &e);
        if (t < -1) return -1;
        c->fields = realloc(c->fields, sizeof(int) * (size_t)(c->n + 1));
        c->fields[c->n++] = t;
        s = e;
        if (*s == ',') s++;
        else if (*s != ')') return -1;
      }
      s++;
    }
    if (*s == 0) return 0;
    if (*s != '/') return -1;
    s++;
  }
}

/* ---- The C mirror of Rt.readback ---- */

typedef struct {
  char *buf;
  size_t len, cap;
} str_t;

static void put(str_t *o, const char *s) {
  size_t n = strlen(s);
  if (o->len + n + 1 > o->cap) {
    o->cap = 2 * (o->len + n + 1);
    o->buf = realloc(o->buf, o->cap);
  }
  memcpy(o->buf + o->len, s, n + 1);
  o->len += n;
}

/* The part of the region Lir uses, from region + 16: the first 16 bytes
 * (entrySp, stackLimit) are the wrappers', and Rt.readback in the model
 * (X86.Driver.lirView) does not read them either. */
#define WRAPPER_BYTES ((uint64_t)16)

static int readable(uint64_t a, uint64_t n) {
  if (region_size < WRAPPER_BYTES) return 0;
  uint64_t base = (uint64_t)(uintptr_t)region + WRAPPER_BYTES, size = region_size - WRAPPER_BYTES;
  return a >= base && a - base <= size && n <= size - (a - base);
}

static int decode(uint64_t w, int ty, uint64_t fuel, str_t *o) {
  char tmp[32];
  if (ty == -1) {
    if (!(w & 1)) return -1;
    snprintf(tmp, sizeof tmp, "%llu", (unsigned long long)(w >> 1));
    put(o, tmp);
    return 0;
  }
  if (ty < 0 || ty >= ninds) return -1;
  ind_t *ind = &inds[ty];
  if (w & 1) {
    uint64_t tag = w >> 1;
    if (tag >= (uint64_t)ind->n || ind->ctors[tag].n != 0) return -1;
    snprintf(tmp, sizeof tmp, "#%llu", (unsigned long long)tag);
    put(o, tmp);
    return 0;
  }
  if (fuel == 0 || !readable(w, 8)) return -1;
  uint64_t h;
  memcpy(&h, (void *)(uintptr_t)w, 8);
  uint64_t tag = (h >> 16) & 0xFFFF, scan = h & 0xFF;
  if (tag >= (uint64_t)ind->n) return -1;
  ctor_t *c = &ind->ctors[tag];
  if ((uint64_t)c->n != scan || scan == 0) return -1;
  snprintf(tmp, sizeof tmp, "#%llu(", (unsigned long long)tag);
  put(o, tmp);
  for (int j = 0; j < c->n; j++) {
    uint64_t a = w + 8 + 8 * (uint64_t)j, v;
    if (!readable(a, 8)) return -1;
    memcpy(&v, (void *)(uintptr_t)a, 8);
    if (j > 0) put(o, ",");
    if (decode(v, c->fields[j], fuel - 1, o) != 0) return -1;
  }
  put(o, ")");
  return 0;
}

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000ULL + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
  uint64_t stack_size = (uint64_t)8 << 20;
  const char *type = NULL, *sig = "";
  int dump = 0, timing = 0;
  region_size = (uint64_t)64 << 20;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--region") && i + 1 < argc) region_size = strtoull(argv[++i], NULL, 0);
    else if (!strcmp(argv[i], "--stack") && i + 1 < argc) stack_size = strtoull(argv[++i], NULL, 0);
    else if (!strcmp(argv[i], "--type") && i + 1 < argc) type = argv[++i];
    else if (!strcmp(argv[i], "--sig") && i + 1 < argc) sig = argv[++i];
    else if (!strcmp(argv[i], "--dump")) dump = 1;
    else if (!strcmp(argv[i], "--time")) timing = 1;
    else {
      fprintf(stderr, "usage: %s [--region BYTES] [--stack BYTES] [--type T --sig S] [--dump] [--time]\n", argv[0]);
      return 2;
    }
  }
  int ty = 0;
  if (type) {
    const char *e;
    ty = parse_ty(type, &e);
    if (ty < -1 || *e != 0 || parse_sig(sig) != 0) {
      fprintf(stderr, "bad type descriptor\n");
      return 2;
    }
  }
  if (stack_size < 2 * RESERVE || stack_size % 16 != 0) {
    fprintf(stderr, "the stack must be a multiple of 16 of at least %llu bytes\n", (unsigned long long)(2 * RESERVE));
    return 2;
  }
  region = mmap(NULL, region_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) {
    perror("mmap region");
    return 2;
  }
  uint8_t *stack = mmap(NULL, stack_size + GUARD, PROT_READ | PROT_WRITE,
                        MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_STACK, -1, 0);
  if (stack == MAP_FAILED) {
    perror("mmap stack");
    return 2;
  }
  if (mprotect(stack, GUARD, PROT_NONE) != 0) {
    perror("mprotect guard");
    return 2;
  }
  void *top = stack + GUARD + stack_size;
  uint64_t budget = stack_size - RESERVE;
  char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    uint64_t args[6] = {(uint64_t)(uintptr_t)region, 0, 0, 0, 0, 0};
    char *cursor = line, *end;
    for (int i = 1; i < 6; i++) {
      uint64_t value = strtoull(cursor, &end, 0);
      if (end == cursor) break;
      args[i] = value;
      cursor = end;
    }
    uint64_t init_args[6] = {(uint64_t)(uintptr_t)region, region_size, budget, 0, 0, 0};
    /* The stack budget at region + 16 (ctx - 48), where every export
     * wrapper, cx_init's included, reads it (X86.Driver.initBytes). */
    memcpy(region + 16, &budget, 8);
    struct result r;
    call_on_stack(init_args, &r, cx_init, top);
    if (r.rax != 0 || !saved_ok(&r)) {
      printf("init %llu %llu %d\n", (unsigned long long)r.rax, (unsigned long long)r.rdx, saved_ok(&r));
      fflush(stdout);
      continue;
    }
    uint64_t t0 = now_ns();
    call_on_stack(args, &r, ENTRY, top);
    uint64_t t1 = now_ns();
    printf("%llu %llu %d", (unsigned long long)r.rax, (unsigned long long)r.rdx, saved_ok(&r));
    if (type) {
      str_t o = {NULL, 0, 0};
      uint64_t base = (uint64_t)(uintptr_t)region;
      uint64_t fuel = (ctx_field(-32) - base) / 8;
      if (r.rax == 0 && decode(r.rdx, ty, fuel, &o) == 0) printf(" %s", o.buf);
      else printf(" -");
      free(o.buf);
    }
    if (timing) printf(" %llu", (unsigned long long)(t1 - t0));
    printf("\n");
    if (dump) {
      uint64_t base = (uint64_t)(uintptr_t)region;
      /* cx_init's first object address (Rt.objectsStart) and the final bump */
      uint64_t start = (base + 640 + 63) / 64 * 64, bump = ctx_field(-40);
      printf("dump %llu %llu %llu ", (unsigned long long)base, (unsigned long long)start, (unsigned long long)bump);
      for (uint64_t a = start; a < bump; a++) printf("%02x", region[a - base]);
      printf("\n");
    }
    fflush(stdout);
  }
  return 0;
}
