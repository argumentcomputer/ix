// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Stage-one row population on the GPU for the trace plans exported with the
// circuits of the verified Aiur compiler.
//
// Each row is filled by interpreting its function's compiled population plan
// (the same dataflow graph the host `FillPlan` runs): guarded arithmetic,
// inverses, branch and failure witnesses, the U8 library's byte tables, the
// U32/U64 word hints, and calls resolved from the callee's recorded queries
// through a device hash index. Then the function's placement in its physical
// circuit is applied: column writes, selector, group writes and multiplicity.
// Plans needing host-only state (memory stores and loads, stream hints) are
// never encoded, so their circuits stay on the host. Between the column
// writes and the placement, each row fills its depth columns (Track A, H1):
// its query's height, and for each enabled gap or external call slot the
// callee's recorded height, split into range-checked limbs for a gap. A
// separate counting pass tallies those limbs for the fixed range tables.
//
// Every value is a canonical Goldilocks word. The encoding is produced by
// `crates/aiur/src/trace/stark/gpu.rs`; keep the two in sync.

#include <cuda_runtime.h>
#include <goldilocks.cuh>

#include <cstddef>
#include <cstdint>

using namespace multi_stark_cuda;

namespace {

// Plan opcodes.
constexpr uint32_t OP_ADD = 0, OP_SUB = 1, OP_MUL = 2, OP_SELECT = 3,
                   OP_INVERSE = 4, OP_CHOICE = 5, OP_FAILURE = 6, OP_MAP = 7,
                   OP_CALL = 8, OP_HINT = 9;
// Byte-table maps of the U8 library.
constexpr uint32_t MAP_FROM_FIELD = 0, MAP_BITS = 1, MAP_RANGE_PAIR = 2,
                   MAP_XOR = 3, MAP_AND = 4, MAP_OR = 5, MAP_LT = 6,
                   MAP_ADD = 7, MAP_SUB = 8, MAP_MUL = 9, MAP_XOR_SPLIT4 = 10,
                   MAP_XOR_SPLIT7 = 11, MAP_SUM_BYTE = 12;
// Word hints.
constexpr uint32_t HINT_U32_BYTES = 0, HINT_U32_SUB = 1, HINT_U32_ADD = 2,
                   HINT_U32_ADD3 = 3, HINT_U32_LT = 4, HINT_BYTES_LE = 5;
// Group-write polynomial tokens.
constexpr uint32_t POLY_CONST = 0, POLY_VAR = 1, POLY_ADD = 2, POLY_SUB = 3,
                   POLY_MUL = 4;
// Population failures, reported with the first failing row.
constexpr int32_t ERROR_ZERO_INVERSE = 1, ERROR_NO_ARM = 2,
                  ERROR_NO_FAILURE = 3, ERROR_MAP_DOMAIN = 4,
                  ERROR_MISSING_CALLEE = 5, ERROR_HINT_DOMAIN = 6,
                  ERROR_ENCODING = 7, ERROR_POLY_STACK = 8, ERROR_DEPTH = 9;
constexpr uint32_t CONSTANT = 0x80000000u;
// A function without a depth column.
constexpr uint32_t NO_COLUMN = 0xFFFFFFFFu;
constexpr uint32_t EMPTY = 0;
constexpr int POLY_STACK = 64;
// Operands and results of byte maps and word hints (at most 12).
constexpr uint32_t SMALL = 16;

}  // namespace

// Layouts shared with `gpu.rs` (`#[repr(C)]`).
// A member function of a circuit. Its recorded queries are `count` rows of
// `stride` words (inputs, then outputs), filling circuit rows from `first`.
struct AiurFunction {
    const uint32_t* code;
    const uint64_t* constants;
    const uint64_t* rows;
    const uint64_t* multiplicities;
    const uint64_t* depths;  // each query's height, or null when untracked
    uint64_t count;
    uint64_t first;
    uint32_t code_len;
    uint32_t scratch;
    uint32_t inputs;
    uint32_t outputs;
    uint32_t stride;
    uint32_t pad;
};

// A function whose recorded outputs calls read, indexed by input.
struct AiurCallee {
    const uint64_t* rows;
    const uint32_t* index;
    const uint64_t* depths;
    uint64_t count;
    uint32_t mask;
    uint32_t inputs;
    uint32_t outputs;
    uint32_t stride;
};

struct AiurCircuit {
    const AiurFunction* members;
    const AiurCallee* callees;
    uint64_t real;
    uint32_t member_count;
    uint32_t width;
    uint32_t scratch;
    uint32_t pad;
};

struct AiurPopulationError {
    int32_t code;
    uint32_t op;
    uint64_t row;
};

namespace {

// One hash for stored keys and for keys read from plan operands.
__device__ __forceinline__ uint64_t hash_step(uint64_t h, uint64_t word) {
    h ^= word;
    h *= 0x100000001b3ULL;
    return h ^ (h >> 29);
}
__device__ __forceinline__ uint64_t hash_finish(uint64_t h) {
    h ^= h >> 32;
    h *= 0xd6e8feb86659fd93ULL;
    return h ^ (h >> 32);
}
__device__ __forceinline__ uint64_t key_hash(const uint64_t* words, uint32_t width) {
    uint64_t h = 0x9e3779b97f4a7c15ULL ^ width;
    for (uint32_t i = 0; i < width; ++i) h = hash_step(h, words[i]);
    return hash_finish(h);
}

__device__ void fail(AiurPopulationError* error, int32_t code, uint32_t op, uint64_t row) {
    if (atomicCAS(&error->code, 0, code) == 0) {
        error->op = op;
        error->row = row;
    }
}

__device__ __forceinline__ uint64_t inverse(uint64_t value) {
    return goldilocks_pow(value, GOLDILOCKS_P - 2);
}

struct Scratch {
    uint64_t* base;
    size_t stride;
    __device__ __forceinline__ uint64_t& operator[](uint32_t slot) const {
        return base[size_t(slot) * stride];
    }
};

__device__ __forceinline__ uint64_t value_of(uint32_t value, const uint64_t* constants,
                                             const Scratch& scratch) {
    return (value & CONSTANT) ? constants[value & ~CONSTANT] : scratch[value];
}

// A callee query whose recorded input equals the plan operands `key`.
__device__ int64_t find_query(const AiurCallee& callee, const uint32_t* key,
                              const uint64_t* constants, const Scratch& scratch) {
    uint64_t h = 0x9e3779b97f4a7c15ULL ^ callee.inputs;
    for (uint32_t i = 0; i < callee.inputs; ++i)
        h = hash_step(h, value_of(key[i], constants, scratch));
    uint64_t slot = hash_finish(h) & callee.mask;
    for (uint64_t probe = 0; probe <= callee.mask; ++probe) {
        const uint32_t entry = callee.index[slot];
        if (entry == EMPTY) return -1;
        const uint64_t query = entry - 1;
        const uint64_t* stored = callee.rows + query * callee.stride;
        bool equal = true;
        for (uint32_t i = 0; i < callee.inputs && equal; ++i)
            equal = stored[i] == value_of(key[i], constants, scratch);
        if (equal) return int64_t(query);
        slot = (slot + 1) & callee.mask;
    }
    return -1;
}

__device__ bool evaluate_map(uint32_t kind, const uint64_t* in, uint64_t* out) {
    const uint64_t a = in[0];
    switch (kind) {
    case MAP_FROM_FIELD:
        if (a >= 256) return false;
        out[0] = a;
        return true;
    case MAP_BITS:
        if (a >= 256) return false;
        for (int i = 0; i < 8; ++i) out[i] = (a >> i) & 1;
        return true;
    case MAP_SUM_BYTE:
        if (a >= 768) return false;
        out[0] = a & 255;
        return true;
    default:
        break;
    }
    const uint64_t b = in[1];
    if ((a | b) > 255) return false;
    switch (kind) {
    case MAP_RANGE_PAIR: return true;
    case MAP_XOR: out[0] = a ^ b; return true;
    case MAP_AND: out[0] = a & b; return true;
    case MAP_OR: out[0] = a | b; return true;
    case MAP_LT: out[0] = a < b ? 1 : 0; return true;
    case MAP_ADD: out[0] = (a + b) & 255; out[1] = (a + b) >> 8; return true;
    case MAP_SUB: out[0] = (a - b) & 255; out[1] = a < b ? 1 : 0; return true;
    case MAP_MUL: out[0] = (a * b) & 255; out[1] = (a * b) >> 8; return true;
    case MAP_XOR_SPLIT4: out[0] = (a ^ b) >> 4; out[1] = ((a ^ b) & 15) << 4; return true;
    case MAP_XOR_SPLIT7: out[0] = (a ^ b) >> 7; out[1] = ((a ^ b) & 127) << 1; return true;
    default: return false;
    }
}

__device__ __forceinline__ void word_bytes(uint32_t word, uint64_t* out) {
    for (int i = 0; i < 4; ++i) out[i] = (word >> (8 * i)) & 255;
}

__device__ bool evaluate_hint(uint32_t kind, const uint64_t* in, uint32_t nargs, uint64_t* out) {
    switch (kind) {
    case HINT_U32_BYTES:
        word_bytes(uint32_t(in[0]), out);
        return true;
    case HINT_U32_SUB:
        word_bytes(uint32_t(in[0]) - uint32_t(in[1]), out);
        return true;
    case HINT_U32_ADD:
    case HINT_U32_ADD3: {
        uint32_t sum = 0;
        for (uint32_t word = 0; word < nargs / 4; ++word) {
            uint32_t value = 0;
            for (int i = 0; i < 4; ++i) {
                const uint64_t byte = in[4 * word + i];
                if (byte > 255) return false;
                value |= uint32_t(byte) << (8 * i);
            }
            sum += value;
        }
        word_bytes(sum, out);
        return true;
    }
    case HINT_U32_LT: {
        const uint32_t a = uint32_t(in[0]), b = uint32_t(in[1]);
        word_bytes(a, out);
        word_bytes(a - b, out + 4);
        word_bytes(b, out + 8);
        return true;
    }
    case HINT_BYTES_LE:
        for (int i = 0; i < 8; ++i) out[i] = (in[0] >> (8 * i)) & 255;
        return true;
    default:
        return false;
    }
}


// Evaluates `count` polynomial tokens (pairs of token and payload) over
// `row` into `out`. Returns 0 or a population error code.
__device__ int32_t eval_tokens(const uint32_t* tokens, uint32_t count, const uint64_t* constants,
                               const uint64_t* row, uint64_t* out) {
    uint64_t stack[POLY_STACK];
    int depth = 0;
    for (uint32_t t = 0; t < count; ++t) {
        const uint32_t token = tokens[2 * t];
        const uint32_t payload = tokens[2 * t + 1];
        if (token == POLY_CONST || token == POLY_VAR) {
            if (depth == POLY_STACK) return ERROR_POLY_STACK;
            stack[depth++] = token == POLY_CONST ? constants[payload] : row[payload];
        } else {
            if (depth < 2) return ERROR_POLY_STACK;
            const uint64_t b = stack[--depth], a = stack[--depth];
            if (token == POLY_ADD) stack[depth++] = goldilocks_add(a, b);
            else if (token == POLY_SUB) stack[depth++] = goldilocks_sub(a, b);
            else if (token == POLY_MUL) stack[depth++] = goldilocks_mul(a, b);
            else return ERROR_ENCODING;
        }
    }
    if (depth != 1) return ERROR_POLY_STACK;
    *out = stack[0];
    return 0;
}

// The callee query whose recorded input is the values of the `nargs`
// encoded polynomials at `args` (each a token count, then its tokens) over
// `row`, or -1. Sets `*status` to an error code when a polynomial fails.
__device__ int64_t find_row(const AiurCallee& callee, const uint32_t* args, uint32_t nargs,
                            const uint64_t* constants, const uint64_t* row, int32_t* status) {
    if (nargs != callee.inputs) return -1;
    uint64_t h = 0x9e3779b97f4a7c15ULL ^ callee.inputs;
    const uint32_t* arg = args;
    for (uint32_t i = 0; i < nargs; ++i) {
        uint64_t value = 0;
        *status = eval_tokens(arg + 1, arg[0], constants, row, &value);
        if (*status != 0) return -1;
        h = hash_step(h, value);
        arg += 1 + 2 * arg[0];
    }
    uint64_t slot = hash_finish(h) & callee.mask;
    for (uint64_t probe = 0; probe <= callee.mask; ++probe) {
        const uint32_t entry = callee.index[slot];
        if (entry == EMPTY) return -1;
        const uint64_t query = entry - 1;
        const uint64_t* stored = callee.rows + query * callee.stride;
        bool equal = true;
        arg = args;
        for (uint32_t i = 0; i < nargs && equal; ++i) {
            uint64_t value = 0;
            eval_tokens(arg + 1, arg[0], constants, row, &value);
            equal = stored[i] == value;
            arg += 1 + 2 * arg[0];
        }
        if (equal) return int64_t(query);
        slot = (slot + 1) & callee.mask;
    }
    return -1;
}

// Fills a row's depth columns (Track A, H1) from its circuit columns; see
// the depth section in `gpu.rs`. With `ranges`, also counts the gap limbs'
// range-table uses. Returns 0 or a population error code.
__device__ int32_t fill_depth(const AiurFunction& f, const AiurCallee* callees, uint64_t query,
                              const uint32_t* code, uint32_t& pc, uint64_t* row,
                              uint64_t* ranges) {
    const uint64_t* constants = f.constants;
    const uint32_t depth_column = code[pc++];
    const uint64_t depth = f.depths ? f.depths[query] : 0;
    if (depth_column != NO_COLUMN) {
        if (!f.depths) return ERROR_ENCODING;
        row[depth_column] = canonicalize(depth);
    }
    const uint32_t slots = code[pc++];
    for (uint32_t s = 0; s < slots; ++s) {
        const uint32_t external = code[pc++];
        const uint32_t columns = code[pc++];
        const uint32_t* triples = code + pc;  // (column, width, range offset)
        pc += 3 * columns;
        const uint32_t ncallees = code[pc++];
        const uint32_t* ids = code + pc;
        pc += ncallees;
        const uint32_t* enable = code + pc;
        pc += 1 + 2 * enable[0];
        const uint32_t nargs = code[pc++];
        const uint32_t* args = code + pc;
        for (uint32_t a = 0; a < nargs; ++a) pc += 1 + 2 * code[pc];
        uint64_t on = 0;
        int32_t status = eval_tokens(enable + 1, enable[0], constants, row, &on);
        if (status != 0) return status;
        if (on != 1) continue;
        int64_t found = -1;
        const AiurCallee* callee = nullptr;
        for (uint32_t c = 0; c < ncallees && found < 0; ++c) {
            callee = &callees[ids[c]];
            found = find_row(*callee, args, nargs, constants, row, &status);
            if (status != 0) return status;
        }
        if (found < 0) return ERROR_MISSING_CALLEE;
        const uint64_t height = callee->depths ? callee->depths[found] : 0;
        if (external) {
            if (columns != 1) return ERROR_ENCODING;
            row[triples[0]] = canonicalize(height);
            continue;
        }
        if (depth <= height) return ERROR_DEPTH;
        uint64_t rest = depth - 1 - height;
        for (uint32_t i = 0; i < columns; ++i) {
            const uint32_t width = triples[3 * i + 1];
            const uint64_t limb = rest & ((uint64_t(1) << width) - 1);
            rest >>= width;
            row[triples[3 * i]] = limb;
            if (ranges)
                atomicAdd(reinterpret_cast<unsigned long long*>(&ranges[triples[3 * i + 2] + limb]),
                          1ull);
        }
        if (rest != 0) return ERROR_DEPTH;
    }
    return 0;
}

// Interprets one function's plan for one query into `row`. Returns false on
// a population failure, which `fail` has recorded. With `ranges`, counts the
// row's depth range-table uses.
__device__ bool fill_row(const AiurFunction& f, const AiurCallee* callees, uint64_t query,
                         uint64_t row_index, const Scratch& scratch, uint64_t* row,
                         uint32_t width, uint64_t* ranges, AiurPopulationError* error) {
    const uint64_t* constants = f.constants;
    const uint64_t* recorded = f.rows + query * f.stride;
    for (uint32_t i = 0; i < f.inputs + f.outputs; ++i) scratch[i] = recorded[i];
    uint64_t buffer[SMALL];
    const uint32_t* code = f.code;
    uint32_t pc = 0;
    const uint32_t kernels = code[pc++];
    for (uint32_t k = 0; k < kernels; ++k) {
        const uint32_t op = code[pc++];
        const uint32_t guard = code[pc++];
        const uint32_t start = code[pc++];
        const uint32_t width_k = code[pc++];
        const uint32_t size = code[pc++];  // words that follow, so inactive kernels skip them
        const uint32_t body = pc;
        pc += size;
        if (value_of(guard, constants, scratch) != 1) {
            for (uint32_t i = 0; i < width_k; ++i) scratch[start + i] = 0;
            continue;
        }
        const uint32_t* args = code + body;
        switch (op) {
        case OP_ADD:
            scratch[start] = goldilocks_add(value_of(args[0], constants, scratch),
                                            value_of(args[1], constants, scratch));
            break;
        case OP_SUB:
            scratch[start] = goldilocks_sub(value_of(args[0], constants, scratch),
                                            value_of(args[1], constants, scratch));
            break;
        case OP_MUL:
            scratch[start] = goldilocks_mul(value_of(args[0], constants, scratch),
                                            value_of(args[1], constants, scratch));
            break;
        case OP_SELECT:
            scratch[start] = value_of(args[0], constants, scratch) == 1
                                 ? value_of(args[1], constants, scratch)
                                 : value_of(args[2], constants, scratch);
            break;
        case OP_INVERSE: {
            const uint64_t v = value_of(args[0], constants, scratch);
            if (v == 0) { fail(error, ERROR_ZERO_INVERSE, k, row_index); return false; }
            scratch[start] = inverse(v);
            break;
        }
        case OP_CHOICE: {
            for (uint32_t i = 0; i < width_k; ++i) scratch[start + i] = 0;
            uint32_t at = 0;
            const uint32_t tests = args[at++];
            int64_t selected = -1;
            for (uint32_t t = 0; t < tests; ++t) {
                const uint32_t len = args[at++];
                bool zero = true;
                for (uint32_t i = 0; i < len; ++i)
                    zero = zero && value_of(args[at + i], constants, scratch) == 0;
                at += len;
                if (zero && selected < 0) selected = t;
            }
            if (selected < 0) { fail(error, ERROR_NO_ARM, k, row_index); return false; }
            scratch[start + uint32_t(selected)] = 1;
            break;
        }
        case OP_FAILURE: {
            for (uint32_t i = 0; i < width_k; ++i) scratch[start + i] = 0;
            const uint32_t len = args[0];
            int64_t found = -1;
            uint64_t witness = 0;
            for (uint32_t i = 0; i < len && found < 0; ++i) {
                const uint64_t x = value_of(args[1 + i], constants, scratch);
                if (x != 0) { found = i; witness = x; }
            }
            if (found < 0) { fail(error, ERROR_NO_FAILURE, k, row_index); return false; }
            scratch[start + uint32_t(found)] = inverse(witness);
            break;
        }
        case OP_MAP:
        case OP_HINT: {
            const uint32_t target = args[0];
            const uint32_t nargs = args[1];
            if (nargs > SMALL || width_k > SMALL) {
                fail(error, ERROR_ENCODING, k, row_index);
                return false;
            }
            for (uint32_t i = 0; i < nargs; ++i)
                buffer[i] = value_of(args[2 + i], constants, scratch);
            uint64_t out[SMALL];
            const bool ok = op == OP_MAP ? evaluate_map(target, buffer, out)
                                         : evaluate_hint(target, buffer, nargs, out);
            if (!ok) {
                fail(error, op == OP_MAP ? ERROR_MAP_DOMAIN : ERROR_HINT_DOMAIN, k, row_index);
                return false;
            }
            for (uint32_t i = 0; i < width_k; ++i) scratch[start + i] = out[i];
            break;
        }
        case OP_CALL: {
            const AiurCallee& callee = callees[args[0]];
            if (args[1] != callee.inputs || width_k != callee.outputs) {
                fail(error, ERROR_ENCODING, k, row_index);
                return false;
            }
            const int64_t found = find_query(callee, args + 2, constants, scratch);
            if (found < 0) {
                fail(error, ERROR_MISSING_CALLEE, k, row_index);
                return false;
            }
            const uint64_t* values = callee.rows + uint64_t(found) * callee.stride + callee.inputs;
            for (uint32_t i = 0; i < width_k; ++i) scratch[start + i] = values[i];
            break;
        }
        default:
            fail(error, ERROR_ENCODING, k, row_index);
            return false;
        }
    }
    // Column writes, already mapped to the physical circuit.
    const uint32_t writes = code[pc++];
    for (uint32_t w = 0; w < writes; ++w) {
        const uint32_t guard = code[pc++], column = code[pc++], value = code[pc++];
        if (value_of(guard, constants, scratch) == 1)
            row[column] = value_of(value, constants, scratch);
    }
    // The selector, then the depth columns, from the circuit columns just
    // written (slot enables read the selector).
    const uint32_t selector = code[pc++];
    row[selector] = 1;
    const int32_t depth_status = fill_depth(f, callees, query, code, pc, row, ranges);
    if (depth_status != 0) { fail(error, depth_status, 0, row_index); return false; }
    // Placement: group writes over the row, multiplicity.
    const uint32_t group_writes = code[pc++];
    for (uint32_t g = 0; g < group_writes; ++g) {
        const uint32_t column = code[pc++];
        const uint32_t tokens = code[pc++];
        uint64_t value = 0;
        const int32_t status = eval_tokens(code + pc, tokens, constants, row, &value);
        pc += 2 * tokens;
        if (status != 0) { fail(error, status, g, row_index); return false; }
        row[column] = value;
    }
    row[width - 1] = f.multiplicities[query];
    return true;
}

// Row `r` of the output is circuit row `base + (first + r) % height`: a
// shard of `height` rows starting at `base`, wrapped for lookup halos.
__global__ void populate_kernel(AiurCircuit circuit, uint64_t* output, uint64_t base,
                                uint64_t first, uint64_t rows, uint64_t height,
                                uint64_t* scratch_base, AiurPopulationError* error) {
    const uint64_t threads = uint64_t(gridDim.x) * blockDim.x;
    const uint64_t thread = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    const Scratch scratch{scratch_base + thread, size_t(threads)};
    for (uint64_t r = thread; r < rows; r += threads) {
        uint64_t* row = output + r * circuit.width;
        for (uint32_t c = 0; c < circuit.width; ++c) row[c] = 0;
        const uint64_t index = base + (first + r) % height;
        if (index >= circuit.real) continue;
        uint32_t member = 0;
        while (member + 1 < circuit.member_count && circuit.members[member + 1].first <= index)
            ++member;
        const AiurFunction& f = circuit.members[member];
        fill_row(f, circuit.callees, index - f.first, index, scratch, row, circuit.width, nullptr,
                 error);
    }
}

// Fills every real row of `circuit` once into a per-thread row buffer, only
// to count the depth range-table uses into `ranges`.
__global__ void count_kernel(AiurCircuit circuit, uint64_t* rows, uint64_t* scratch_base,
                             uint64_t* ranges, AiurPopulationError* error) {
    const uint64_t threads = uint64_t(gridDim.x) * blockDim.x;
    const uint64_t thread = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    const Scratch scratch{scratch_base + thread, size_t(threads)};
    uint64_t* row = rows + thread * circuit.width;
    for (uint64_t index = thread; index < circuit.real; index += threads) {
        for (uint32_t c = 0; c < circuit.width; ++c) row[c] = 0;
        uint32_t member = 0;
        while (member + 1 < circuit.member_count && circuit.members[member + 1].first <= index)
            ++member;
        const AiurFunction& f = circuit.members[member];
        fill_row(f, circuit.callees, index - f.first, index, scratch, row, circuit.width, ranges,
                 error);
    }
}

__global__ void canonicalize_kernel(uint64_t* words, uint64_t count) {
    const uint64_t stride = uint64_t(gridDim.x) * blockDim.x;
    for (uint64_t i = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x; i < count; i += stride)
        words[i] = canonicalize(words[i]);
}

__global__ void index_kernel(const uint64_t* rows, uint64_t count, uint32_t inputs,
                             uint32_t row_stride, uint32_t* index, uint32_t mask) {
    const uint64_t stride = uint64_t(gridDim.x) * blockDim.x;
    for (uint64_t q = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x; q < count; q += stride) {
        uint64_t slot = key_hash(rows + q * row_stride, inputs) & mask;
        while (atomicCAS(&index[slot], EMPTY, uint32_t(q + 1)) != EMPTY) slot = (slot + 1) & mask;
    }
}

constexpr unsigned BLOCK = 128;

unsigned blocks_for(uint64_t work, unsigned limit) {
    const uint64_t blocks = (work + BLOCK - 1) / BLOCK;
    return unsigned(blocks == 0 ? 1 : (blocks < limit ? blocks : limit));
}

}  // namespace

extern "C" {

// Threads a population launch uses at most; the caller sizes the scratch
// buffer as `aiur_gpu_population_threads() * circuit.scratch` words.
uint64_t aiur_gpu_population_threads() { return uint64_t(BLOCK) * 512; }

int aiur_gpu_malloc(int device, size_t bytes, void** output) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess) return status;
    return cudaMalloc(output, bytes == 0 ? 8 : bytes);
}

int aiur_gpu_free(int device, void* pointer) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess) return status;
    return cudaFree(pointer);
}

int aiur_gpu_upload(int device, void* destination, const void* source, size_t bytes) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess || bytes == 0) return status;
    return cudaMemcpy(destination, source, bytes, cudaMemcpyHostToDevice);
}

int aiur_gpu_download(int device, void* destination, const void* source, size_t bytes) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess || bytes == 0) return status;
    return cudaMemcpy(destination, source, bytes, cudaMemcpyDeviceToHost);
}

int aiur_gpu_canonicalize(int device, uint64_t* words, uint64_t count) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess || count == 0) return status;
    canonicalize_kernel<<<blocks_for(count, 4096), BLOCK>>>(words, count);
    status = cudaGetLastError();
    if (status != cudaSuccess) return status;
    return cudaStreamSynchronize(cudaStreamPerThread);
}

int aiur_gpu_build_index(int device, const uint64_t* rows, uint64_t count, uint32_t inputs,
                         uint32_t row_stride, uint32_t* index, uint32_t mask) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess) return status;
    status = cudaMemsetAsync(index, 0, (uint64_t(mask) + 1) * sizeof(uint32_t),
                             cudaStreamPerThread);
    if (status != cudaSuccess || count == 0) {
        return status != cudaSuccess ? status : cudaStreamSynchronize(cudaStreamPerThread);
    }
    index_kernel<<<blocks_for(count, 4096), BLOCK>>>(rows, count, inputs, row_stride, index, mask);
    status = cudaGetLastError();
    if (status != cudaSuccess) return status;
    return cudaStreamSynchronize(cudaStreamPerThread);
}

// Fills `rows` rows of the shard of `circuit` that starts at row `base` and
// has `height` rows, starting at shard row `first` and wrapping, into
// `output` (row-major device memory), synchronously on the calling thread's
// default stream. `scratch` holds `aiur_gpu_population_threads() *
// circuit->scratch` words; `error` must start zeroed and reports the first
// failing row.
int aiur_gpu_populate(int device, const AiurCircuit* circuit, uint64_t* output, uint64_t base,
                      uint64_t first, uint64_t rows, uint64_t height, uint64_t* scratch,
                      AiurPopulationError* error) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess || rows == 0) return status;
    const unsigned blocks = blocks_for(rows, unsigned(aiur_gpu_population_threads() / BLOCK));
    // Scratch is laid out for the full thread count the kernel strides by.
    populate_kernel<<<blocks, BLOCK>>>(*circuit, output, base, first, rows, height, scratch,
                                       error);
    status = cudaGetLastError();
    if (status != cudaSuccess) return status;
    return cudaStreamSynchronize(cudaStreamPerThread);
}

// Counts the depth range-table uses of every real row of `circuit` into
// `ranges`, with `threads` threads (a multiple of the block size). `rows`
// holds `threads * circuit->width` words and `scratch` `threads *
// circuit->scratch` words; `error` must start zeroed.
int aiur_gpu_count_ranges(int device, const AiurCircuit* circuit, uint64_t threads, uint64_t* rows,
                          uint64_t* scratch, uint64_t* ranges, AiurPopulationError* error) {
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess || circuit->real == 0) return status;
    const unsigned blocks = unsigned(threads / BLOCK);
    count_kernel<<<blocks == 0 ? 1 : blocks, BLOCK>>>(*circuit, rows, scratch, ranges, error);
    status = cudaGetLastError();
    if (status != cudaSuccess) return status;
    return cudaStreamSynchronize(cudaStreamPerThread);
}

const char* aiur_gpu_error_string(int status) {
    return cudaGetErrorString(static_cast<cudaError_t>(status));
}

}  // extern "C"
