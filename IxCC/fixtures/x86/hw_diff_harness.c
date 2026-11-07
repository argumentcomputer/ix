/*
 * Native executor for the x86 hardware-differential gate (x86-64 Linux).
 *
 * Each input line is one case:
 *   <id> <code-hex> <rax> <rcx> <rdx> <rbx> <rsp> <rbp> <rsi> <rdi>
 *        <r8> ... <r15> <flags> <seed>
 * (registers and flags in hex; flags bits: 0 CF, 6 ZF, 7 SF, 11 OF).
 * The case's instruction bytes are placed at CODE_TEST. Execution starts
 * there with the given registers and arithmetic flags; control ends at one
 * of two exits:
 *   EXIT_FALL  directly after the instruction (fall-through), or
 *   EXIT_TAKEN at a fixed address that branch/call/ret cases target.
 * Two fixed pages are mapped read/write: DATA_PAGE and STACK_PAGE. Both start
 * filled with the deterministic pattern pattern(seed, address). Every other
 * address is unmapped, so out-of-window accesses fault.
 *
 * Output per case:
 *   <id> ok <exit> <16 registers> <flags> <n> <address>=<byte> ...
 *   <id> fault <signal>
 * where the byte list is every page byte that differs from its initial
 * pattern, in increasing address order. The Lean driver computes the same
 * observations from the local byte model and compares them.
 *
 * The harness is test evidence for the ISA model; it is not part of any
 * compiled program.
 */
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define TRAMPOLINE ((uint8_t *)0x40000000UL)
#define DATA_PAGE ((uint8_t *)0x40100000UL)
#define STACK_PAGE ((uint8_t *)0x40200000UL)
#define PAGE 4096UL

/* Fixed trampoline layout (offsets from TRAMPOLINE). */
#define OFF_STATE 0x000   /* in regs[16], in flags, out regs[16], out flags, host rsp, exit */
#define OFF_ENTRY 0x200
#define OFF_TEST 0x800    /* CODE_TEST; up to MAX_CODE bytes (a short instruction sequence) */
#define MAX_CODE 64
#define OFF_TAKEN 0xc00   /* EXIT_TAKEN */

struct state {
  uint64_t in_regs[16];
  uint64_t in_flags;
  uint64_t out_regs[16];
  uint64_t out_flags;
  uint64_t host_rsp;
  uint64_t exit;
};

static sigjmp_buf recover;
static volatile sig_atomic_t fault_signal;

static void on_fault(int signal, siginfo_t *info, void *context) {
  (void)info;
  (void)context;
  fault_signal = signal;
  siglongjmp(recover, 1);
}

static uint8_t pattern(uint64_t seed, uint64_t address) {
  uint64_t x = seed ^ (address * 0x9e3779b97f4a7c15ULL);
  x ^= x >> 29;
  x *= 0xbf58476d1ce4e5b9ULL;
  x ^= x >> 32;
  return (uint8_t)x;
}

static void fill(uint64_t seed) {
  for (uint64_t i = 0; i < PAGE; i++) {
    DATA_PAGE[i] = pattern(seed, (uint64_t)(uintptr_t)DATA_PAGE + i);
    STACK_PAGE[i] = pattern(seed, (uint64_t)(uintptr_t)STACK_PAGE + i);
  }
}

/* Emit helpers for the trampoline. */
static uint8_t *emit(uint8_t *at, const uint8_t *bytes, size_t n) {
  memcpy(at, bytes, n);
  return at + n;
}

/* mov r64, [rip+disp32] / mov [rip+disp32], r64 with register number reg. */
static uint8_t *mov_rip(uint8_t *at, int store, int reg, uint8_t *target) {
  uint8_t rex = 0x48 | ((reg & 8) ? 4 : 0);
  uint8_t op = store ? 0x89 : 0x8b;
  uint8_t modrm = (uint8_t)(0x05 | ((reg & 7) << 3));
  int32_t disp = (int32_t)(target - (at + 7));
  uint8_t bytes[7] = {rex, op, modrm};
  memcpy(bytes + 3, &disp, 4);
  return emit(at, bytes, 7);
}

/* Save all registers and arithmetic flags without touching the test stack,
 * record the exit, restore the host stack and callee-saved registers, ret. */
static uint8_t *epilogue(uint8_t *at, struct state *s, uint64_t exit_code) {
  for (int r = 0; r < 16; r++) at = mov_rip(at, 1, r, (uint8_t *)&s->out_regs[r]);
  /* lahf (AH = SF ZF 0 AF 0 PF 1 CF); seto al; store ax */
  static const uint8_t flags[] = {0x9f, 0x0f, 0x90, 0xc0};
  at = emit(at, flags, sizeof flags);
  {
    /* mov [rip+disp32], ax  = 66 89 05 disp32 */
    int32_t disp = (int32_t)((uint8_t *)&s->out_flags - (at + 7));
    uint8_t bytes[7] = {0x66, 0x89, 0x05};
    memcpy(bytes + 3, &disp, 4);
    at = emit(at, bytes, 7);
  }
  {
    /* mov qword [rip+disp32], imm32 (exit code) = 48 c7 05 disp32 imm32 */
    int32_t disp = (int32_t)((uint8_t *)&s->exit - (at + 11));
    uint8_t bytes[11] = {0x48, 0xc7, 0x05};
    memcpy(bytes + 3, &disp, 4);
    uint32_t code = (uint32_t)exit_code;
    memcpy(bytes + 7, &code, 4);
    at = emit(at, bytes, 11);
  }
  at = mov_rip(at, 0, 4, (uint8_t *)&s->host_rsp); /* mov rsp, [host_rsp] */
  static const uint8_t restore[] = {0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5d, 0x5b, 0xc3};
  return emit(at, restore, sizeof restore);
}

static void build_entry(struct state *s) {
  uint8_t *at = TRAMPOLINE + OFF_ENTRY;
  /* push rbx, rbp, r12..r15 */
  static const uint8_t save[] = {0x53, 0x55, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57};
  at = emit(at, save, sizeof save);
  at = mov_rip(at, 1, 4, (uint8_t *)&s->host_rsp); /* mov [host_rsp], rsp */
  /* push qword [rip+in_flags]; popfq */
  {
    int32_t disp = (int32_t)((uint8_t *)&s->in_flags - (at + 6));
    uint8_t bytes[6] = {0xff, 0x35};
    memcpy(bytes + 2, &disp, 4);
    at = emit(at, bytes, 6);
    static const uint8_t popf[] = {0x9d};
    at = emit(at, popf, 1);
  }
  /* Load every register except rsp, then rsp last; mov does not change flags. */
  for (int r = 0; r < 16; r++)
    if (r != 4) at = mov_rip(at, 0, r, (uint8_t *)&s->in_regs[r]);
  at = mov_rip(at, 0, 4, (uint8_t *)&s->in_regs[4]);
  /* jmp rel32 to CODE_TEST */
  {
    int32_t disp = (int32_t)((TRAMPOLINE + OFF_TEST) - (at + 5));
    uint8_t bytes[5] = {0xe9};
    memcpy(bytes + 1, &disp, 4);
    emit(at, bytes, 5);
  }
}

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

int main(void) {
  if (mmap(TRAMPOLINE, PAGE, PROT_READ | PROT_WRITE | PROT_EXEC,
           MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0) != TRAMPOLINE ||
      mmap(DATA_PAGE, PAGE, PROT_READ | PROT_WRITE,
           MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0) != DATA_PAGE ||
      mmap(STACK_PAGE, PAGE, PROT_READ | PROT_WRITE,
           MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0) != STACK_PAGE) {
    perror("mmap");
    return 2;
  }
  struct state *s = (struct state *)(TRAMPOLINE + OFF_STATE);
  build_entry(s);
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = on_fault;
  /* Faults happen on the test stack, so handlers run on their own stack. */
  static uint8_t alternate[1 << 16];
  stack_t signal_stack = {.ss_sp = alternate, .ss_size = sizeof alternate, .ss_flags = 0};
  sigaltstack(&signal_stack, NULL);
  action.sa_flags = SA_SIGINFO | SA_NODEFER | SA_ONSTACK;
  sigemptyset(&action.sa_mask);
  sigaction(SIGSEGV, &action, NULL);
  sigaction(SIGBUS, &action, NULL);
  sigaction(SIGFPE, &action, NULL);
  sigaction(SIGILL, &action, NULL);

  char line[4096];
  printf("layout %lx %lx %lx %lx\n", (unsigned long)(uintptr_t)(TRAMPOLINE + OFF_TEST),
         (unsigned long)(uintptr_t)(TRAMPOLINE + OFF_TAKEN),
         (unsigned long)(uintptr_t)DATA_PAGE, (unsigned long)(uintptr_t)STACK_PAGE);
  while (fgets(line, sizeof line, stdin)) {
    char id[128], code_hex[2 * MAX_CODE + 2];
    unsigned long long regs[16], flags, seed;
    int fields = sscanf(line,
                        "%127s %129s %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx",
                        id, code_hex, &regs[0], &regs[1], &regs[2], &regs[3], &regs[4], &regs[5], &regs[6],
                        &regs[7], &regs[8], &regs[9], &regs[10], &regs[11], &regs[12], &regs[13], &regs[14],
                        &regs[15], &flags, &seed);
    if (fields != 20) {
      fprintf(stderr, "malformed case: %s", line);
      return 2;
    }
    size_t code_len = strlen(code_hex) / 2;
    if (code_len == 0 || code_len > MAX_CODE) {
      fprintf(stderr, "bad code length in %s\n", id);
      return 2;
    }
    /* Reset the trampoline code regions and install this case. */
    memset(TRAMPOLINE + OFF_TEST, 0xcc, OFF_TAKEN - OFF_TEST);
    for (size_t i = 0; i < code_len; i++) {
      int hi = hexval(code_hex[2 * i]), lo = hexval(code_hex[2 * i + 1]);
      if (hi < 0 || lo < 0) {
        fprintf(stderr, "bad hex in %s\n", id);
        return 2;
      }
      TRAMPOLINE[OFF_TEST + i] = (uint8_t)(hi * 16 + lo);
    }
    epilogue(TRAMPOLINE + OFF_TEST + code_len, s, 0);
    epilogue(TRAMPOLINE + OFF_TAKEN, s, 1);
    __builtin___clear_cache((char *)TRAMPOLINE, (char *)(TRAMPOLINE + PAGE));
    fill(seed);
    for (int r = 0; r < 16; r++) s->in_regs[r] = regs[r];
    /* Only CF ZF SF OF are inputs; keep reserved bit 1 and IF (bit 9) set. */
    s->in_flags = (flags & 0x8c1ULL) | 0x202ULL;
    s->exit = 99;
    fault_signal = 0;
    if (sigsetjmp(recover, 1) == 0) {
      ((void (*)(void))(TRAMPOLINE + OFF_ENTRY))();
    } else {
      printf("%s fault %d\n", id, (int)fault_signal);
      continue;
    }
    /* out_flags: AH = SF ZF - AF - PF 1 CF, AL = OF */
    uint64_t ah = (s->out_flags >> 8) & 0xff, al = s->out_flags & 0xff;
    uint64_t out_flags = (ah & 1) | (ah & 0x40) | (ah & 0x80) | (al ? 0x800 : 0);
    printf("%s ok %llu", id, (unsigned long long)s->exit);
    for (int r = 0; r < 16; r++) printf(" %llx", (unsigned long long)s->out_regs[r]);
    printf(" %llx", (unsigned long long)out_flags);
    unsigned changed = 0;
    for (uint64_t i = 0; i < PAGE; i++) {
      if (DATA_PAGE[i] != pattern(seed, (uint64_t)(uintptr_t)DATA_PAGE + i)) changed++;
      if (STACK_PAGE[i] != pattern(seed, (uint64_t)(uintptr_t)STACK_PAGE + i)) changed++;
    }
    printf(" %u", changed);
    for (uint64_t i = 0; i < PAGE; i++)
      if (DATA_PAGE[i] != pattern(seed, (uint64_t)(uintptr_t)DATA_PAGE + i))
        printf(" %llx=%02x", (unsigned long long)((uintptr_t)DATA_PAGE + i), DATA_PAGE[i]);
    for (uint64_t i = 0; i < PAGE; i++)
      if (STACK_PAGE[i] != pattern(seed, (uint64_t)(uintptr_t)STACK_PAGE + i))
        printf(" %llx=%02x", (unsigned long long)((uintptr_t)STACK_PAGE + i), STACK_PAGE[i]);
    printf("\n");
  }
  return 0;
}
