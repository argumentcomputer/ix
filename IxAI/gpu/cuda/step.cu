// One SGD step of `IxAICore.Model.step` with fixed-width integer arithmetic.
//
// Every kernel implements one function of `IxAIGpu/Step.lean`, named in its comment. Values are raw
// fixed-point integers (`Fx.raw`) in row-major int64 buffers. Each of the five products of the step
// is a GEMM `out[r][c] = Σ_k a[r][k] · b[c][k]` (both operands row-major along `k`), written to the
// step's key buffer, followed by an elementwise epilogue. A GEMM runs on one of two paths, which
// return the same int64 sums:
//
// * CUDA cores (`dot_kernel`): one warp per output, `IxAIGpu.blockReduce ⟨5⟩`. Products are exact
//   128-bit values (`mul.lo`/`mul.hi`), accumulated in 128 bits (`add.cc`/`addc`).
// * Tensor cores (`limb_gemm`): operands below 2^31 in magnitude are split into int8 limb planes
//   (`IxAIGpu.limbs`) and multiplied by int8 MMAs with int32 accumulation, in chunks short enough that
//   no int32 partial sum can overflow; the chunks are recombined with weights 256^(p+q) in 128 bits
//   (`IxAIGpu.tileReduce`). Used for GEMMs large enough to amortise the split.
//
// Integer addition is associative and commutative, so every order gives the exact sum. No operation
// may leave its width, or the result would leave the Lean model's `Int` semantics; every check below
// detects a real overflow of the exact value (`IxAIGpu.StepGuard`): a 128-bit accumulator add that
// overflows, a sum that does not fit the int64 it is stored in, or an int64 add, subtraction or
// product that overflows. Lanes of the shuffle tree whose sums are discarded add nothing. A
// violation sets the context's flag and the host rejects the step.

#include <cstdint>
#include <cuda_runtime.h>

typedef long long i64;
typedef unsigned long long u64;

namespace {

constexpr int kLogLanes = 5;
constexpr int kLanes = 1 << kLogLanes;
constexpr int kWarpsPerBlock = 8;

__device__ __forceinline__ void raise(int* flag) { atomicOr(flag, 1); }

// int64 operations with exact overflow detection: an add overflows iff both operands have the
// sign the result lacks; a product fits iff the high word of the 128-bit product is the sign
// extension of the low word.
__device__ __forceinline__ i64 add_checked(i64 a, i64 b, int* flag) {
  i64 s = (i64)((u64)a + (u64)b);
  if (((a ^ s) & (b ^ s)) < 0) raise(flag);
  return s;
}

__device__ __forceinline__ i64 sub_checked(i64 a, i64 b, int* flag) {
  i64 s = (i64)((u64)a - (u64)b);
  if (((a ^ b) & (a ^ s)) < 0) raise(flag);
  return s;
}

__device__ __forceinline__ i64 mul_checked(i64 a, i64 b, int* flag) {
  i64 lo = (i64)((u64)a * (u64)b);
  if (__mul64hi(a, b) != (lo >> 63)) raise(flag);
  return lo;
}

// A 128-bit two's-complement integer `hi · 2^64 + lo`.
struct I128 {
  u64 lo;
  i64 hi;
};

__device__ __forceinline__ I128 widen(i64 v) { return {(u64)v, v >> 63}; }

// The exact product of two int64 values.
__device__ __forceinline__ I128 mul_wide(i64 a, i64 b) { return {(u64)a * (u64)b, __mul64hi(a, b)}; }

// `a + b` with carry from the low word; `ov` is set on signed overflow. `%0` is written before the
// second instruction reads `%3` and `%5`, so it is early-clobber and cannot share their register.
__device__ __forceinline__ I128 add_wide(I128 a, I128 b, bool& ov) {
  I128 s;
  asm("add.cc.u64 %0, %2, %4;\n\taddc.u64 %1, %3, %5;"
      : "=&l"(s.lo), "=l"(s.hi)
      : "l"(a.lo), "l"(a.hi), "l"(b.lo), "l"(b.hi));
  ov |= ((a.hi ^ s.hi) & (b.hi ^ s.hi)) < 0;
  return s;
}

__device__ __forceinline__ bool fits64(I128 v) { return v.hi == ((i64)v.lo >> 63); }

// `>>> 8` on `Int`: floor division by 256 (arithmetic shift of a two's-complement int64).
__device__ __forceinline__ i64 shr8(i64 v) { return v >> 8; }

// `relu` on raw values, as `Fx.relu`.
__device__ __forceinline__ i64 relu(i64 v) { return v > 0 ? v : 0; }

__device__ __forceinline__ I128 shfl_down(I128 v, int s) {
  return {__shfl_down_sync(0xffffffffu, v.lo, s), __shfl_down_sync(0xffffffffu, v.hi, s)};
}

// The halving tree of `blockReduce`: lane `t < s` adds lane `t + s`, for `s = 16, 8, 4, 2, 1`.
// Lane 0 holds the result; the other lanes' sums are discarded, so they add nothing.
__device__ __forceinline__ I128 warp_tree(I128 acc, int lane, bool& ov) {
  for (int s = kLanes / 2; s > 0; s >>= 1) {
    I128 other = shfl_down(acc, s);
    if (lane < s) acc = add_wide(acc, other, ov);
  }
  return acc;
}

// Raise the flag if any accumulator add of the warp overflowed or lane 0's sum leaves int64.
__device__ __forceinline__ i64 narrow(I128 acc, int lane, bool ov, int* flag) {
  if (__any_sync(0xffffffffu, ov) && lane == 0) raise(flag);
  if (lane == 0 && !fits64(acc)) raise(flag);
  return (i64)acc.lo;
}

// `IxAIGpu.blockReduce ⟨5⟩ f K` for `f k = a[k] * b[k]`: lane `t` accumulates terms `t, t + 32, …`
// in increasing order (`threadSum`), then `warp_tree`.
__device__ i64 warp_dot(const i64* a, const i64* b, int k_len, int lane, int* flag) {
  I128 acc{0, 0};
  bool ov = false;
  for (int k = lane; k < k_len; k += kLanes) acc = add_wide(acc, mul_wide(a[k], b[k]), ov);
  return narrow(warp_tree(acc, lane, ov), lane, ov, flag);
}

// `IxAIGpu.blockReduce ⟨5⟩ f K` for `f k = a[k]`.
__device__ i64 warp_sum(const i64* a, int k_len, int lane, int* flag) {
  I128 acc{0, 0};
  bool ov = false;
  for (int k = lane; k < k_len; k += kLanes) acc = add_wide(acc, widen(a[k]), ov);
  return narrow(warp_tree(acc, lane, ov), lane, ov, flag);
}

// Output index `(r, c)` of the warp running this lane, in an `rows × cols` grid of warps.
struct WarpTask {
  int r, c, lane;
  bool active;
};

__device__ WarpTask warp_task(int rows, int cols) {
  long long warp = ((long long)blockIdx.x * blockDim.x + threadIdx.x) / kLanes;
  WarpTask t;
  t.lane = threadIdx.x % kLanes;
  t.active = warp < (long long)rows * cols;
  t.r = t.active ? (int)(warp / cols) : 0;
  t.c = t.active ? (int)(warp % cols) : 0;
  return t;
}

// The GEMM on CUDA cores: `out[r][c] = blockReduce (fun k => a[r][k] * b[c][k]) k_len`.
__global__ void dot_kernel(const i64* a, const i64* b, int rows, int cols, int k_len, i64* out,
                           int* flag) {
  WarpTask t = warp_task(rows, cols);
  if (!t.active) return;
  i64 s = warp_dot(a + (size_t)t.r * k_len, b + (size_t)t.c * k_len, k_len, t.lane, flag);
  if (t.lane == 0) out[(size_t)t.r * cols + t.c] = s;
}

__device__ __forceinline__ long long thread_index() {
  return (long long)blockIdx.x * blockDim.x + threadIdx.x;
}

// `IxAIGpu.hiddenZ` from its key `key[b][j] = Σ_i w1[j][i] · x[b][i]`: `z = key >>> 8 + b1[j]`,
// and `h = relu z`.
__global__ void hidden_epilogue(const i64* key, const i64* b1, int n_hidden, long long n, i64* z,
                                i64* h, int* flag) {
  long long i = thread_index();
  if (i >= n) return;
  i64 zj = add_checked(shr8(key[i]), b1[i % n_hidden], flag);
  z[i] = zj;
  h[i] = relu(zj);
}

// `IxAIGpu.outputDelta` from its key `Σ_j w2[k][j] · h[b][j]`: `key >>> 8 + b2[k] − t[b][k]`.
__global__ void output_epilogue(const i64* key, const i64* b2, const i64* tgt, int n_out, long long n,
                                i64* dout, int* flag) {
  long long i = thread_index();
  if (i >= n) return;
  dout[i] = sub_checked(add_checked(shr8(key[i]), b2[i % n_out], flag), tgt[i], flag);
}

// `IxAIGpu.dzK` from its key `Σ_k w2T[j][k] · dout[b][k]`: `if z > 0 then key >>> 8 else 0`. The key
// is formed for every `j`: it is a `fx.shr8` key whatever the sign of `z`.
__global__ void dz_epilogue(const i64* key, const i64* z, long long n, i64* dz) {
  long long i = thread_index();
  if (i >= n) return;
  dz[i] = z[i] > 0 ? shr8(key[i]) : 0;
}

// `IxAIGpu.updateW` from its gradient sum `key_sum`: `w −= (lr · (key_sum >>> 8)) >>> 8`, in place.
// `key_lr` is the product `lr · g`, a `fx.shr8` key.
__global__ void update_w_epilogue(i64* w, const i64* key_sum, long long n, i64 lr, i64* key_lr,
                                  int* flag) {
  long long i = thread_index();
  if (i >= n) return;
  i64 p = mul_checked(lr, shr8(key_sum[i]), flag);
  key_lr[i] = p;
  w[i] = sub_checked(w[i], shr8(p), flag);
}

// `IxAIGpu.transposeK`: `dst[c][r] = src[r][c]`, as `transposeN`.
__global__ void transpose_kernel(const i64* src, int rows, int cols, i64* dst) {
  long long i = thread_index();
  if (i >= (long long)rows * cols) return;
  int r = (int)(i / cols), c = (int)(i % cols);
  dst[(size_t)c * rows + r] = src[i];
}

// `IxAIGpu.updateB`: `bias[r] −= (lr · Σ_b gT[r][b]) >>> 8`, in place. `key_lr` is `lr · Σ`.
__global__ void update_b_kernel(i64* bias, const i64* gt, int rows, int n_batch, i64 lr, i64* key_lr,
                                int* flag) {
  WarpTask t = warp_task(rows, 1);
  if (!t.active) return;
  i64 s = warp_sum(gt + (size_t)t.r * n_batch, n_batch, t.lane, flag);
  if (t.lane == 0) {
    i64 p = mul_checked(lr, s, flag);
    key_lr[t.r] = p;
    bias[t.r] = sub_checked(bias[t.r], shr8(p), flag);
  }
}

/* ---- Tensor cores ---------------------------------------------------------------------------- */

// Block tile: `kTile` rows of `a` by `kTile` rows of `b`, `kStep` values of `k` per shared-memory
// stage. Eight warps, each 16 rows × 32 columns: one m16 tile by four n8 tiles of `m16n8k32`.
constexpr int kTile = 64;
constexpr int kStep = 64;
// Shared-memory row pitch: 16-byte aligned, and the fragment loads of a warp hit distinct banks.
constexpr int kPitch = kStep + 16;
// Values of `k` per int32 accumulation. A limb product is at most 255² in magnitude and an
// accumulator sums the products of at most 4 limb pairs, so `kChunk · 4 · 255² < 2^31`
// (`IxAIGpu.chunk_fits32`).
constexpr int kChunk = 8192;
// Limbs per operand: 4 limbs cover `[-2^31, 2^31)`.
constexpr int kMaxLimbs = 4;

// The largest `x ≥ 0 ? x : ~x` of `a`, into `*out` (zero before the first launch): `a` fits `k + 1`
// limbs iff it is below `2^(8k + 7)`.
__global__ void magnitude_kernel(const i64* a, long long n, u64* out) {
  u64 m = 0;
  for (long long i = thread_index(); i < n; i += (long long)gridDim.x * blockDim.x) {
    i64 x = a[i];
    u64 v = (u64)(x ^ (x >> 63));
    m = v > m ? v : m;
  }
  for (int s = kLanes / 2; s > 0; s >>= 1) {
    u64 o = __shfl_down_sync(0xffffffffu, m, s);
    m = o > m ? o : m;
  }
  if (threadIdx.x % kLanes == 0 && m) atomicMax(out, m);
}

// Limb planes of a `rows × k_len` matrix, zero-padded to `rows_pad × k_pad`: plane `p` holds
// `limb (n_limbs - 1) p x`, the byte `x >>> 8p` (unsigned below the top limb, signed at the top).
// Each thread writes four consecutive bytes of every plane.
__global__ void split_kernel(const i64* src, int rows, int k_len, int n_limbs, int rows_pad, int k_pad,
                             uint8_t* dst) {
  long long i = thread_index() * 4;
  long long plane = (long long)rows_pad * k_pad;
  if (i >= plane) return;
  int r = (int)(i / k_pad), c = (int)(i % k_pad);
  i64 x[4];
  for (int e = 0; e < 4; e++)
    x[e] = (r < rows && c + e < k_len) ? src[(size_t)r * k_len + c + e] : 0;
  for (int p = 0; p < n_limbs; p++) {
    uint32_t word = 0;
    for (int e = 0; e < 4; e++) word |= (uint32_t)(uint8_t)(x[e] >> (8 * p)) << (8 * e);
    *(uint32_t*)(dst + p * plane + i) = word;
  }
}

// `c += a · b` on one `m16n8k32` tile; the top limb is signed, the others unsigned. The int32
// accumulation wraps, which `kChunk` rules out.
template <bool SignedA, bool SignedB>
__device__ __forceinline__ void mma(int (&c)[4], const unsigned (&a)[4], const unsigned (&b)[2]) {
#define IXAI_MMA(TA, TB)                                                                          \
  asm volatile("mma.sync.aligned.m16n8k32.row.col.s32." TA "." TB ".s32 "                      \
               "{%0, %1, %2, %3}, {%4, %5, %6, %7}, {%8, %9}, {%0, %1, %2, %3};"               \
               : "+r"(c[0]), "+r"(c[1]), "+r"(c[2]), "+r"(c[3])                                 \
               : "r"(a[0]), "r"(a[1]), "r"(a[2]), "r"(a[3]), "r"(b[0]), "r"(b[1]))
  if constexpr (SignedA && SignedB) IXAI_MMA("s8", "s8");
  else if constexpr (SignedA) IXAI_MMA("s8", "u8");
  else if constexpr (SignedB) IXAI_MMA("u8", "s8");
  else IXAI_MMA("u8", "u8");
#undef IXAI_MMA
}

// `v · 2^sh` for `0 ≤ sh < 64`.
__device__ __forceinline__ I128 shifted(int v, int sh) {
  i64 x = v;
  return {(u64)x << sh, sh ? x >> (64 - sh) : x >> 63};
}

// Limb pairs `(p, q)` with `p ≤ KA`, `q ≤ KB` and `p + q = s`, unrolled at compile time.
template <int KA, int KB, int P = 0, int Q = 0>
__device__ __forceinline__ void mma_pairs(int (&acc)[KA + KB + 1][4][4],
                                          const unsigned (&af)[KA + 1][4],
                                          const unsigned (&bf)[KB + 1][4][2]) {
  if constexpr (P <= KA) {
    if constexpr (Q <= KB) {
#pragma unroll
      for (int j = 0; j < 4; j++) mma<P == KA, Q == KB>(acc[P + Q][j], af[P], bf[Q][j]);
      mma_pairs<KA, KB, P, Q + 1>(acc, af, bf);
    } else {
      mma_pairs<KA, KB, P + 1, 0>(acc, af, bf);
    }
  }
}

// The GEMM on tensor cores, `IxAIGpu.tileReduce KA KB kChunk`: `a` has `KA + 1` limb planes of
// `rows_pad × k_pad` bytes, `b` has `KB + 1` planes of `cols_pad × k_pad`. For each chunk of
// `kChunk` values of `k`, accumulator `s` sums the limb products of the pairs with `p + q = s`;
// at the end of the chunk it is added to the 128-bit sums with weight `256^s`.
//
// The limb counts are chosen on the host before the operands' magnitudes are known there, so the
// kernel checks them against `mag` (the `magnitude_kernel` maxima of `a` and `b`): if an operand
// does not fit its planes, every block computes its tile from the int64 operands `a` and `b` on
// CUDA cores, as `dot_kernel` does. Otherwise block 0 counts one tensor-core GEMM in `tensor`.
template <int KA, int KB>
__global__ void __launch_bounds__(256)
    limb_gemm(const uint8_t* ap, const uint8_t* bp, const i64* a, const i64* b, const u64* mag, int rows,
              int cols, int k_len, int rows_pad, int cols_pad, int k_pad, i64* out, int* flag,
              int* tensor) {
  constexpr int S = KA + KB + 1;
  __shared__ __align__(16) uint8_t as[KA + 1][kTile][kPitch];
  __shared__ __align__(16) uint8_t bs[KB + 1][kTile][kPitch];
  const int tid = threadIdx.x, warp = tid / kLanes, lane = tid % kLanes;
  const int g = lane >> 2, t4 = lane & 3;
  const int wm = warp >> 1, wn = warp & 1;
  // A flat grid of tiles, row-major: `gridDim.y` would cap the rows at 65535 tiles.
  const int col_tiles = cols_pad / kTile;
  const int row0 = (int)(blockIdx.x / col_tiles) * kTile, col0 = (int)(blockIdx.x % col_tiles) * kTile;
  if (!(mag[0] < (1ULL << (8 * KA + 7)) && mag[1] < (1ULL << (8 * KB + 7)))) {
    for (int o = warp; o < kTile * kTile; o += kWarpsPerBlock) {
      const int r = row0 + o / kTile, c = col0 + o % kTile;
      if (r >= rows || c >= cols) continue;
      i64 s = warp_dot(a + (size_t)r * k_len, b + (size_t)c * k_len, k_len, lane, flag);
      if (lane == 0) out[(size_t)r * cols + c] = s;
    }
    return;
  }
  if (blockIdx.x == 0 && tid == 0) atomicAdd(tensor, 1);
  const size_t a_plane = (size_t)rows_pad * k_pad, b_plane = (size_t)cols_pad * k_pad;
  const int load_row = tid >> 2, load_col = (tid & 3) * 16;

  int acc[S][4][4];
  I128 wide[4][4];
#pragma unroll
  for (int j = 0; j < 4; j++)
#pragma unroll
    for (int e = 0; e < 4; e++) {
      wide[j][e] = {0, 0};
#pragma unroll
      for (int s = 0; s < S; s++) acc[s][j][e] = 0;
    }
  bool ov = false;

  for (int k0 = 0; k0 < k_pad; k0 += kStep) {
    __syncthreads();
#pragma unroll
    for (int p = 0; p <= KA; p++)
      *(int4*)&as[p][load_row][load_col] =
          *(const int4*)(ap + p * a_plane + (size_t)(row0 + load_row) * k_pad + k0 + load_col);
#pragma unroll
    for (int q = 0; q <= KB; q++)
      *(int4*)&bs[q][load_row][load_col] =
          *(const int4*)(bp + q * b_plane + (size_t)(col0 + load_row) * k_pad + k0 + load_col);
    __syncthreads();
#pragma unroll
    for (int kk = 0; kk < kStep; kk += 32) {
      unsigned af[KA + 1][4];
      unsigned bf[KB + 1][4][2];
      const int ar = 16 * wm + g;
#pragma unroll
      for (int p = 0; p <= KA; p++) {
        af[p][0] = *(const unsigned*)&as[p][ar][kk + 4 * t4];
        af[p][1] = *(const unsigned*)&as[p][ar + 8][kk + 4 * t4];
        af[p][2] = *(const unsigned*)&as[p][ar][kk + 16 + 4 * t4];
        af[p][3] = *(const unsigned*)&as[p][ar + 8][kk + 16 + 4 * t4];
      }
#pragma unroll
      for (int q = 0; q <= KB; q++)
#pragma unroll
        for (int j = 0; j < 4; j++) {
          const int br = 32 * wn + 8 * j + g;
          bf[q][j][0] = *(const unsigned*)&bs[q][br][kk + 4 * t4];
          bf[q][j][1] = *(const unsigned*)&bs[q][br][kk + 16 + 4 * t4];
        }
      mma_pairs<KA, KB>(acc, af, bf);
    }
    if ((k0 + kStep) % kChunk == 0 || k0 + kStep >= k_pad) {
#pragma unroll
      for (int s = 0; s < S; s++)
#pragma unroll
        for (int j = 0; j < 4; j++)
#pragma unroll
          for (int e = 0; e < 4; e++) {
            wide[j][e] = add_wide(wide[j][e], shifted(acc[s][j][e], 8 * s), ov);
            acc[s][j][e] = 0;
          }
    }
  }
  if (ov) raise(flag);
#pragma unroll
  for (int j = 0; j < 4; j++)
#pragma unroll
    for (int e = 0; e < 4; e++) {
      const int r = row0 + 16 * wm + g + (e >= 2 ? 8 : 0);
      const int c = col0 + 32 * wn + 8 * j + 2 * t4 + (e & 1);
      if (r < rows && c < cols) {
        if (!fits64(wide[j][e])) raise(flag);
        out[(size_t)r * cols + c] = (i64)wide[j][e].lo;
      }
    }
}

typedef void (*LimbGemm)(const uint8_t*, const uint8_t*, const i64*, const i64*, const u64*, int, int,
                         int, int, int, int, i64*, int*, int*);

const LimbGemm kLimbGemms[kMaxLimbs][kMaxLimbs] = {
    {limb_gemm<0, 0>, limb_gemm<0, 1>, limb_gemm<0, 2>, limb_gemm<0, 3>},
    {limb_gemm<1, 0>, limb_gemm<1, 1>, limb_gemm<1, 2>, limb_gemm<1, 3>},
    {limb_gemm<2, 0>, limb_gemm<2, 1>, limb_gemm<2, 2>, limb_gemm<2, 3>},
    {limb_gemm<3, 0>, limb_gemm<3, 1>, limb_gemm<3, 2>, limb_gemm<3, 3>}};

unsigned warp_blocks(long long warps) {
  return (unsigned)((warps + kWarpsPerBlock - 1) / kWarpsPerBlock);
}

unsigned flat_blocks(long long n) { return (unsigned)((n + 255) / 256); }

long long round_up(long long n, long long m) { return (n + m - 1) / m * m; }

}  // namespace

// Which path runs a GEMM: by shape (the default), CUDA cores only, or tensor cores whenever the
// operands fit the limb planes.
enum IxaiGpuPath { kPathAuto = 0, kPathCuda = 1, kPathTensor = 2 };

// The GEMMs of a step, in order.
constexpr int kGemms = 5;

// What a step reports to the host, cleared at its start and read once at its end: the bound flag,
// the number of GEMMs run on tensor cores, and each tensor-core GEMM's operand magnitudes.
struct IxaiGpuStatus {
  int flag;
  int tensor;
  u64 magnitude[kGemms][2];
};

// Device buffers of one model shape. Weights stay on the device across steps. The model is one
// buffer `w1 ++ b1 ++ w2 ++ b2`, and a step's keys are one buffer in the order of `ixai_gpu_keys`,
// laid out for that step's batch, so that each crosses to the host in a single copy.
//
// `limbs[i]` is GEMM `i`'s limb counts minus one, from its operands' magnitudes in the last step
// that measured them, or -1 before that. A tensor-core GEMM uses them without waiting for the
// current magnitudes, which `limb_gemm` checks on the device.
struct IxaiGpu {
  int n_in, n_hidden, n_out, max_batch;
  i64 *model, *w1, *b1, *w2, *b2;
  i64 *keys, *key_h, *key_o, *key_dz, *z, *key_gw1, *key_gw2, *key_p1, *key_pb1, *key_p2, *key_pb2;
  i64 *x, *t, *xt, *h, *ht, *dout, *doutt, *w2t, *dz, *dzt;
  IxaiGpuStatus* status;
  int limbs[kGemms][2];
  bool measured[kGemms];
  uint8_t *planes_a, *planes_b;
  size_t planes_a_size, planes_b_size;
  int last_batch;
  int path;
  int tensor_gemms;
  float kernel_ms;
  cudaEvent_t start, stop;
};

namespace {

// A GEMM below this many multiply-adds stays on CUDA cores under `kPathAuto`: the limb split costs
// more than it saves.
constexpr long long kTensorMinWork = 1LL << 24;

// The first CUDA error of the running entry point on this thread, reported by `ixai_gpu_error`.
// A launch error is visible only through `cudaGetLastError`, which also clears it, so it is kept
// here once read.
thread_local cudaError_t last_error = cudaSuccess;

bool ok(cudaError_t e) {
  if (e != cudaSuccess && last_error == cudaSuccess) last_error = e;
  return e == cudaSuccess;
}

// Start an entry point: forget the previous entry point's error and any launch error that other
// code left on this thread. A sticky error is not cleared and fails the calls that follow.
void begin() {
  last_error = cudaSuccess;
  (void)cudaGetLastError();
}

size_t model_length(const IxaiGpu* g) {
  size_t I = g->n_in, H = g->n_hidden, O = g->n_out;
  return H * I + H + O * H + O;
}

size_t keys_length(const IxaiGpu* g, size_t B) {
  size_t I = g->n_in, H = g->n_hidden, O = g->n_out;
  return 3 * B * H + B * O + 2 * H * I + 2 * O * H + H + O;
}

// Point the key slices at their offsets in `keys` for a batch of `B`.
void place_keys(IxaiGpu* g, size_t B) {
  size_t I = g->n_in, H = g->n_hidden, O = g->n_out;
  g->key_h = g->keys;
  g->key_o = g->key_h + B * H;
  g->key_dz = g->key_o + B * O;
  g->z = g->key_dz + B * H;
  g->key_gw1 = g->z + B * H;
  g->key_gw2 = g->key_gw1 + H * I;
  g->key_p1 = g->key_gw2 + O * H;
  g->key_pb1 = g->key_p1 + H * I;
  g->key_p2 = g->key_pb1 + H;
  g->key_pb2 = g->key_p2 + O * H;
}

bool grow(uint8_t** buf, size_t* size, size_t need) {
  if (*size >= need) return true;
  cudaFree(*buf);
  *buf = nullptr;
  *size = 0;
  if (!ok(cudaMalloc(buf, need))) return false;
  *size = need;
  return true;
}

// Limbs minus one needed by values of magnitude `m` (`magnitude_kernel`), or `kMaxLimbs` if they do
// not fit `kMaxLimbs` limbs.
int limb_top(u64 m) {
  for (int k = 0; k < kMaxLimbs; k++)
    if (m < (1ULL << (8 * k + 7))) return k;
  return kMaxLimbs;
}

void magnitude(const i64* a, long long n, u64* out) {
  long long blocks = (n + 255) / 256;
  magnitude_kernel<<<(unsigned)(blocks < 1024 ? (blocks ? blocks : 1) : 1024), 256>>>(a, n, out);
}

// GEMM `i` of the step: `out[r][c] = Σ_k a[r][k] · b[c][k]` for `a` of `rows × k_len` and `b` of
// `cols × k_len`. A CUDA failure is recorded in `last_error`.
void gemm(IxaiGpu* g, int i, const i64* a, int rows, const i64* b, int cols, int k_len, i64* out) {
  long long work = (long long)rows * cols * k_len;
  bool tensor = k_len > 0 && (g->path == kPathTensor || (g->path == kPathAuto && work >= kTensorMinWork));
  if (tensor) {
    u64* mag = g->status->magnitude[i];
    magnitude(a, (long long)rows * k_len, mag);
    magnitude(b, (long long)cols * k_len, mag + 1);
    g->measured[i] = true;
    int ka = g->limbs[i][0], kb = g->limbs[i][1];
    if (ka < 0) {
      // No earlier magnitudes: wait for these.
      u64 m[2];
      if (!ok(cudaMemcpy(m, mag, sizeof m, cudaMemcpyDeviceToHost))) return;
      ka = limb_top(m[0]);
      kb = limb_top(m[1]);
    }
    if (ka < kMaxLimbs && kb < kMaxLimbs) {
      long long rows_pad = round_up(rows, kTile), cols_pad = round_up(cols, kTile);
      long long k_pad = round_up(k_len, kStep);
      if (!grow(&g->planes_a, &g->planes_a_size, (size_t)(ka + 1) * rows_pad * k_pad) ||
          !grow(&g->planes_b, &g->planes_b_size, (size_t)(kb + 1) * cols_pad * k_pad))
        return;
      split_kernel<<<flat_blocks(rows_pad * k_pad / 4), 256>>>(a, rows, k_len, ka + 1, (int)rows_pad,
                                                               (int)k_pad, g->planes_a);
      split_kernel<<<flat_blocks(cols_pad * k_pad / 4), 256>>>(b, cols, k_len, kb + 1, (int)cols_pad,
                                                               (int)k_pad, g->planes_b);
      unsigned tiles = (unsigned)((rows_pad / kTile) * (cols_pad / kTile));
      kLimbGemms[ka][kb]<<<tiles, 256>>>(g->planes_a, g->planes_b, a, b, mag, rows, cols, k_len,
                                         (int)rows_pad, (int)cols_pad, (int)k_pad, out,
                                         &g->status->flag, &g->status->tensor);
      return;
    }
  }
  dot_kernel<<<warp_blocks((long long)rows * cols), kWarpsPerBlock * kLanes>>>(a, b, rows, cols, k_len,
                                                                               out, &g->status->flag);
}

}  // namespace

extern "C" {

// The message of the CUDA error that made the last failing entry point on this thread fail.
const char* ixai_gpu_error() { return cudaGetErrorString(last_error); }

void ixai_gpu_destroy(IxaiGpu* g);

IxaiGpu* ixai_gpu_create(int n_in, int n_hidden, int n_out, int max_batch) {
  begin();
  IxaiGpu* g = new IxaiGpu{};
  g->n_in = n_in;
  g->n_hidden = n_hidden;
  g->n_out = n_out;
  g->max_batch = max_batch;
  size_t I = n_in, H = n_hidden, O = n_out, B = max_batch;
  struct { i64** p; size_t n; } bufs[] = {
      {&g->model, model_length(g)}, {&g->keys, keys_length(g, B)},
      {&g->x, B * I}, {&g->t, B * O}, {&g->xt, I * B}, {&g->h, B * H}, {&g->ht, H * B},
      {&g->dout, B * O}, {&g->doutt, O * B}, {&g->w2t, H * O}, {&g->dz, B * H}, {&g->dzt, H * B}};
  bool good = ok(cudaEventCreate(&g->start)) && ok(cudaEventCreate(&g->stop));
  for (auto& b : bufs) good = good && ok(cudaMalloc(b.p, (b.n ? b.n : 1) * sizeof(i64)));
  good = good && ok(cudaMalloc(&g->status, sizeof(IxaiGpuStatus)));
  if (!good) {
    ixai_gpu_destroy(g);
    return nullptr;
  }
  g->w1 = g->model;
  g->b1 = g->w1 + H * I;
  g->w2 = g->b1 + H;
  g->b2 = g->w2 + O * H;
  place_keys(g, B);
  for (auto& l : g->limbs) l[0] = l[1] = -1;
  return g;
}

void ixai_gpu_destroy(IxaiGpu* g) {
  if (!g) return;
  for (i64* p : {g->model, g->keys, g->x, g->t, g->xt, g->h, g->ht, g->dout, g->doutt, g->w2t, g->dz,
                 g->dzt})
    cudaFree(p);
  cudaFree(g->status);
  cudaFree(g->planes_a);
  cudaFree(g->planes_b);
  if (g->start) cudaEventDestroy(g->start);
  if (g->stop) cudaEventDestroy(g->stop);
  delete g;
}

// Select the GEMM path (`IxaiGpuPath`). Returns -1 for an unknown path.
int ixai_gpu_set_path(IxaiGpu* g, int path) {
  if (path < kPathAuto || path > kPathTensor) return -1;
  g->path = path;
  return 0;
}

// The last step's number of GEMMs run on tensor cores, and its device time in milliseconds from
// the first kernel to the last (uploads excluded).
int ixai_gpu_tensor_gemms(IxaiGpu* g) { return g->tensor_gemms; }
float ixai_gpu_kernel_ms(IxaiGpu* g) { return g->kernel_ms; }

// Upload the model `w1 ++ b1 ++ w2 ++ b2` (`w1` is H×I, `w2` is O×H). Returns 0, or -1 on a CUDA
// error.
int ixai_gpu_set_model(IxaiGpu* g, const i64* model) {
  begin();
  return ok(cudaMemcpy(g->model, model, model_length(g) * sizeof(i64), cudaMemcpyHostToDevice)) ? 0 : -1;
}

// Download the model, as `ixai_gpu_set_model` takes it.
int ixai_gpu_get_model(IxaiGpu* g, i64* model) {
  begin();
  return ok(cudaMemcpy(model, g->model, model_length(g) * sizeof(i64), cudaMemcpyDeviceToHost)) ? 0 : -1;
}

// `IxAIGpu.gpuStep ⟨5⟩ ⟨lr⟩ m batch` on the device's model, with the batch's inputs `x` (B×I) and
// targets `t` (B×O). Returns 0, 1 if a fixed-width bound was violated (the model is then invalid),
// or -1 on a CUDA error. An empty batch leaves the model unchanged, as `Model.step` does.
int ixai_gpu_step(IxaiGpu* g, const i64* x, const i64* t, int n_batch, i64 lr) {
  begin();
  g->tensor_gemms = 0;
  g->kernel_ms = 0;
  if (n_batch < 0 || n_batch > g->max_batch) return -1;
  g->last_batch = n_batch;
  if (n_batch == 0) return 0;
  const int I = g->n_in, H = g->n_hidden, O = g->n_out, B = n_batch;
  place_keys(g, B);
  for (bool& m : g->measured) m = false;
  if (!ok(cudaMemcpy(g->x, x, (size_t)B * I * sizeof(i64), cudaMemcpyHostToDevice)) ||
      !ok(cudaMemcpy(g->t, t, (size_t)B * O * sizeof(i64), cudaMemcpyHostToDevice)) ||
      !ok(cudaMemset(g->status, 0, sizeof(IxaiGpuStatus))) || !ok(cudaEventRecord(g->start)))
    return -1;
  int* flag = &g->status->flag;
  const long long BH = (long long)B * H, BO = (long long)B * O;
  if (H > 0) {
    gemm(g, 0, g->x, B, g->w1, H, I, g->key_h);
    hidden_epilogue<<<flat_blocks(BH), 256>>>(g->key_h, g->b1, H, BH, g->z, g->h, flag);
  }
  if (O > 0) {
    gemm(g, 1, g->h, B, g->w2, O, H, g->key_o);
    output_epilogue<<<flat_blocks(BO), 256>>>(g->key_o, g->b2, g->t, O, BO, g->dout, flag);
  }
  if (O > 0 && H > 0) transpose_kernel<<<flat_blocks((long long)O * H), 256>>>(g->w2, O, H, g->w2t);
  if (H > 0) {
    gemm(g, 2, g->dout, B, g->w2t, H, O, g->key_dz);
    dz_epilogue<<<flat_blocks(BH), 256>>>(g->key_dz, g->z, BH, g->dz);
  }
  if (H > 0) transpose_kernel<<<flat_blocks(BH), 256>>>(g->dz, B, H, g->dzt);
  if (I > 0) transpose_kernel<<<flat_blocks((long long)B * I), 256>>>(g->x, B, I, g->xt);
  if (H > 0) transpose_kernel<<<flat_blocks(BH), 256>>>(g->h, B, H, g->ht);
  if (O > 0) transpose_kernel<<<flat_blocks(BO), 256>>>(g->dout, B, O, g->doutt);
  // `gpuStep` computes every gradient from the old weights: the `dz` GEMM above used `w2t`, a copy
  // of the old `w2`, so `w2` may now be updated in place.
  if (H > 0 && I > 0) {
    gemm(g, 3, g->dzt, H, g->xt, I, B, g->key_gw1);
    update_w_epilogue<<<flat_blocks((long long)H * I), 256>>>(g->w1, g->key_gw1, (long long)H * I, lr,
                                                              g->key_p1, flag);
  }
  if (H > 0)
    update_b_kernel<<<warp_blocks(H), kWarpsPerBlock * kLanes>>>(g->b1, g->dzt, H, B, lr, g->key_pb1,
                                                                 flag);
  if (O > 0 && H > 0) {
    gemm(g, 4, g->doutt, O, g->ht, H, B, g->key_gw2);
    update_w_epilogue<<<flat_blocks((long long)O * H), 256>>>(g->w2, g->key_gw2, (long long)O * H, lr,
                                                              g->key_p2, flag);
  }
  if (O > 0)
    update_b_kernel<<<warp_blocks(O), kWarpsPerBlock * kLanes>>>(g->b2, g->doutt, O, B, lr, g->key_pb2,
                                                                 flag);
  ok(cudaGetLastError());
  ok(cudaEventRecord(g->stop));
  // The copy waits for every kernel of the step, on this thread's stream.
  IxaiGpuStatus status;
  ok(cudaMemcpy(&status, g->status, sizeof status, cudaMemcpyDeviceToHost));
  if (last_error != cudaSuccess) return -1;
  for (int i = 0; i < kGemms; i++)
    if (g->measured[i])
      for (int j = 0; j < 2; j++) g->limbs[i][j] = limb_top(status.magnitude[i][j]);
  g->tensor_gemms = status.tensor;
  if (cudaEventElapsedTime(&g->kernel_ms, g->start, g->stop) != cudaSuccess) g->kernel_ms = 0;
  return status.flag ? 1 : 0;
}

// Copy the last step's keys to `out`: per example `h`, `o`, `dz` and `z` sums (B×H, B×O, B×H,
// B×H), then the gradient sums of `w1` and `w2`, then the products `lr · g` of `w1`, `b1`, `w2`,
// `b2`; `3BH + BO + 2HI + 2OH + H + O` values for the last step's batch `B`. Returns 0, or -1 on a
// CUDA error.
int ixai_gpu_keys(IxaiGpu* g, i64* out) {
  begin();
  size_t n = g->last_batch ? keys_length(g, g->last_batch) : 0;
  if (n == 0) return 0;
  return ok(cudaMemcpy(out, g->keys, n * sizeof(i64), cudaMemcpyDeviceToHost)) ? 0 : -1;
}

}  // extern "C"
