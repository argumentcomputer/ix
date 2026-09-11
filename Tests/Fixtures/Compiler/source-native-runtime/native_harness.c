#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAX_LENGTH = 64, HEADER_WORDS = 10, CELL_WORDS = 4 };
enum { CURSOR, CAPACITY, ALLOCS, FREES, REUSES, LIVE, PEAK, RCOPS, PAYLOAD, RESERVATIONS };

typedef struct {
    uint64_t header[HEADER_WORDS];
    uint64_t cells[][CELL_WORDS];
} Arena;

extern uint64_t compilatrix_runtime_reverse(Arena *, uint64_t);
extern uint64_t compilatrix_runtime_drop(Arena *, uint64_t);

static void need(int condition, const char *message) {
    if (!condition) {
        fprintf(stderr, "native runtime harness: %s\n", message);
        exit(1);
    }
}

/* Volatile register operands force the checks to observe the physical saved
   registers on each side of the call. The fixture is built with frame-pointer
   omission so rbp is available along with all other System V saved registers. */
__attribute__((noinline))
static uint64_t checked_call(uint64_t (*entry)(Arena *, uint64_t), Arena *arena, uint64_t root) {
    register uint64_t bx __asm__("rbx") = UINT64_C(0x1020304050607080);
    register uint64_t bp __asm__("rbp") = UINT64_C(0x2131415161718191);
    register uint64_t r12 __asm__("r12") = UINT64_C(0x32425262728292a2);
    register uint64_t r13 __asm__("r13") = UINT64_C(0x435363738393a3b3);
    register uint64_t r14 __asm__("r14") = UINT64_C(0x5464748494a4b4c4);
    register uint64_t r15 __asm__("r15") = UINT64_C(0x65758595a5b5c5d5);
    uintptr_t before, after;
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    __asm__ volatile("mov %%rsp, %0" : "=r"(before));
    uint64_t result = entry(arena, root);
    __asm__ volatile("mov %%rsp, %0" : "=r"(after));
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    need(before == after, "stack pointer changed");
    need(bx == UINT64_C(0x1020304050607080) && bp == UINT64_C(0x2131415161718191) &&
         r12 == UINT64_C(0x32425262728292a2) && r13 == UINT64_C(0x435363738393a3b3) &&
         r14 == UINT64_C(0x5464748494a4b4c4) && r15 == UINT64_C(0x65758595a5b5c5d5),
         "callee-saved register changed");
    return result;
}

static const uint64_t canary = UINT64_C(0xfedcba9876543210);

static void canaries(const uint64_t *storage, size_t words) {
    need(storage[0] == canary && storage[1] == ~canary &&
         storage[words + 2] == canary && storage[words + 3] == ~canary,
         "write escaped the arena");
}

static size_t index_of(const Arena *arena, size_t capacity, uint64_t pointer) {
    uintptr_t base = (uintptr_t)&arena->cells[0];
    need(pointer >= base && pointer < base + capacity * sizeof arena->cells[0], "pointer escaped arena");
    need((pointer - base) % sizeof arena->cells[0] == 0, "misaligned cell pointer");
    return (size_t)((pointer - base) / sizeof arena->cells[0]);
}

static void headers(const Arena *arena, size_t length, int reclaimed) {
    const uint64_t expected[HEADER_WORDS] = {
        32 * (length + 2), 32 * (length + 2), length + 2,
        reclaimed ? length + 2 : 1, length, reclaimed ? 0 : length + 1,
        length + 2, 0, 2 * length, 0
    };
    need(memcmp(arena->header, expected, sizeof expected) == 0, "heap counters disagree");
}

static void print_heap(const Arena *arena, size_t capacity) {
    printf("{\"header\":[");
    for (size_t field = 0; field < HEADER_WORDS; ++field)
        printf("%s%" PRIu64, field ? "," : "", arena->header[field]);
    printf("],\"cells\":[");
    for (size_t index = 0; index < capacity; ++index) {
        const uint64_t *cell = arena->cells[index];
        printf("%s[%" PRIu64 ",%" PRIu64 ",", index ? "," : "", cell[0], cell[1]);
        if (cell[2] == 0) printf("null");
        else printf("%zu", index_of(arena, capacity, cell[2]));
        printf(",%" PRIu64 "]", cell[3]);
    }
    printf("]}");
}

typedef struct { const char *name; size_t length; uint64_t values[MAX_LENGTH]; } Input;
/* The checker generates this table from the independently reviewed report. */
#include "runtime_cases.h"

static void prepare(Arena *arena, size_t length, const uint64_t *values) {
    memset(arena, 0, (HEADER_WORDS + CELL_WORDS * (length + 2)) * sizeof(uint64_t));
    arena->header[CURSOR] = 32 * (length + 1);
    arena->header[CAPACITY] = 32 * (length + 2);
    arena->header[ALLOCS] = arena->header[LIVE] = arena->header[PEAK] = length + 1;
    for (size_t index = 1; index <= length; ++index) {
        arena->cells[index][0] = 1;
        arena->cells[index][1] = values[length - index];
        arena->cells[index][2] = (uintptr_t)arena->cells[index - 1];
    }
}

static void run_case(const Input *input) {
    size_t length = input->length, capacity = length + 2;
    size_t words = HEADER_WORDS + CELL_WORDS * capacity;
    uint64_t *storage = calloc(words + 4, sizeof *storage);
    need(storage != NULL, "allocation failed");
    storage[0] = storage[words + 2] = canary;
    storage[1] = storage[words + 3] = ~canary;
    Arena *arena = (Arena *)(storage + 2);
    prepare(arena, length, input->values);
    printf("{\"name\":\"%s\",\"input\":", input->name);
    print_heap(arena, capacity);
    uint64_t root = checked_call(compilatrix_runtime_reverse, arena, length);
    need(root != 0 && index_of(arena, capacity, root) == 1, "wrong result root");
    headers(arena, length, 0);
    canaries(storage, words);
    unsigned char visited[MAX_LENGTH + 2] = {0};
    uint64_t pointer = root, values[MAX_LENGTH] = {0};
    for (size_t offset = 0; offset <= length; ++offset) {
        size_t index = index_of(arena, capacity, pointer);
        need(!visited[index], "cyclic or aliased list");
        visited[index] = 1;
        const uint64_t *cell = arena->cells[index];
        need(cell[3] == 0, "nonzero cell padding");
        if (offset < length) {
            need(cell[0] == 1 && cell[1] == input->values[length - offset - 1], "wrong reversed payload");
            values[offset] = cell[1];
            pointer = cell[2];
        } else need(cell[0] == 0 && cell[1] == 0 && cell[2] == 0, "invalid nil");
    }
    for (size_t index = 0; index < capacity; ++index) {
        if (visited[index]) continue;
        need(index == 0 && arena->cells[index][0] == 3 && arena->cells[index][1] == 0 &&
             arena->cells[index][2] == 0 && arena->cells[index][3] == 0, "unowned live allocation");
    }
    printf(",\"root\":1,\"value\":[");
    for (size_t index = 0; index < length; ++index) printf("%s%" PRIu64, index ? "," : "", values[index]);
    printf("],\"returned\":");
    print_heap(arena, capacity);
    need(checked_call(compilatrix_runtime_drop, arena, root) == 0, "release returned nonzero");
    headers(arena, length, 1);
    canaries(storage, words);
    for (size_t index = 0; index < capacity; ++index)
        need(arena->cells[index][0] == 3 && arena->cells[index][1] == 0 &&
             arena->cells[index][2] == 0 && arena->cells[index][3] == 0, "incomplete reclamation");
    printf(",\"reclaimed\":");
    print_heap(arena, capacity);
    const char *rejections[] = {
        "length-sixty-five", "length-word-max", "null-descriptor", "misaligned-descriptor", "wrong-cursor",
        "insufficient-capacity", "zero-capacity", "excess-capacity", "misaligned-capacity",
        "wrong-allocs", "wrong-frees", "wrong-reuses", "wrong-live", "wrong-peak", "wrong-rcops",
        "wrong-payload", "wrong-reservations", "nil-tag", "nil-head", "nil-tail", "nil-padding",
        "cons-tag", "cons-self-tail", "cons-null-tail", "cons-outside-tail", "cons-padding"
    };
    unsigned char *original = malloc(words * sizeof *storage);
    need(original != NULL, "snapshot allocation failed");
    printf(",\"rejections\":[");
    size_t rejected = length == 0 ? 21 : 26;
    for (size_t test = 0; test < rejected; ++test) {
        prepare(arena, length, input->values);
        Arena *descriptor = arena;
        uint64_t count = length;
        switch (test) {
        case 0: count = 65; break;
        case 1: count = UINT64_MAX; break;
        case 2: descriptor = NULL; break;
        case 3: descriptor = (Arena *)((unsigned char *)arena + 1); break;
        case 4: arena->header[CURSOR] = 1; break;
        case 5: arena->header[CAPACITY] = 32 * (length + 1); break;
        case 6: arena->header[CAPACITY] = 0; break;
        case 7: arena->header[CAPACITY] = 2144; break;
        case 8: arena->header[CAPACITY] = 32 * (length + 2) + 1; break;
        case 21: arena->cells[length][0] = 0; break;
        case 22: arena->cells[length][2] = (uintptr_t)arena->cells[length]; break;
        case 23: arena->cells[length][2] = 0; break;
        case 24: arena->cells[length][2] = UINT64_MAX; break;
        case 25: arena->cells[length][3] = 1; break;
        default:
            if (test < 17) arena->header[test - 7] += 1;
            else arena->cells[0][test - 17] = 1;
        }
        memcpy(original, arena, words * sizeof *storage);
        need(checked_call(compilatrix_runtime_reverse, descriptor, count) == 0, "malformed input accepted");
        need(memcmp(original, arena, words * sizeof *storage) == 0, "rejection wrote memory");
        canaries(storage, words);
        printf("%s\"%s\"", test ? "," : "", rejections[test]);
    }
    printf("]}");
    free(original);
    free(storage);
}

int main(void) {
    printf("[");
    for (size_t index = 0; index < sizeof inputs / sizeof inputs[0]; ++index) {
        if (index) printf(",");
        run_case(&inputs[index]);
    }
    printf("]\n");
    return 0;
}
