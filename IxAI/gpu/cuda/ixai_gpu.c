/* The Lean object ABI of the GPU step (`IxAIGpuHost/FFI.lean`), over the C entry points of
   `step.cu`.

   A context is a Lean external object owning one `IxaiGpu` (device buffers of one model shape);
   Lean's finalizer releases it. Every buffer crosses the boundary as a `ByteArray` of int64
   values, little-endian, in the row-major order of `step.cu`. Lean checks the values' range when
   it packs them; this file checks only the lengths. */

#include <dlfcn.h>
#include <lean/lean.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct IxaiGpu IxaiGpu;

extern const char *ixai_gpu_error(void);
extern IxaiGpu *ixai_gpu_create(int n_in, int n_hidden, int n_out, int max_batch);
extern void ixai_gpu_destroy(IxaiGpu *g);
extern int ixai_gpu_set_model(IxaiGpu *g, const int64_t *model);
extern int ixai_gpu_get_model(IxaiGpu *g, int64_t *model);
extern int ixai_gpu_step(IxaiGpu *g, const int64_t *x, const int64_t *t, int n_batch, int64_t lr);
extern int ixai_gpu_keys(IxaiGpu *g, int64_t *out);
extern int ixai_gpu_set_path(IxaiGpu *g, int path);
extern int ixai_gpu_tensor_gemms(IxaiGpu *g);
extern float ixai_gpu_kernel_ms(IxaiGpu *g);

typedef struct {
    IxaiGpu *gpu;
    size_t n_in, n_hidden, n_out, max_batch, last_batch;
} context;

static void context_finalize(void *p) {
    context *c = p;
    ixai_gpu_destroy(c->gpu);
    free(c);
}

static void context_foreach(void *p, b_lean_obj_arg f) {
    (void)p;
    (void)f;
}

/* Lean tasks may create contexts concurrently, so the one-time setup below runs under
   `pthread_once`. */
static lean_external_class *the_context_class = NULL;

static void register_context_class(void) {
    the_context_class = lean_register_external_class(context_finalize, context_foreach);
}

static lean_external_class *context_class(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, register_context_class);
    return the_context_class;
}

static context *context_of(b_lean_obj_arg obj) { return lean_get_external_data(obj); }

static lean_obj_res fail(const char *what) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

static lean_obj_res cuda_fail(const char *what) {
    char message[512];
    snprintf(message, sizeof message, "%s: CUDA error: %s", what, ixai_gpu_error());
    return fail(message);
}

static size_t model_length(const context *c) {
    return c->n_hidden * c->n_in + c->n_hidden + c->n_out * c->n_hidden + c->n_out;
}

static int64_t *words(b_lean_obj_arg bytes) { return (int64_t *)lean_sarray_cptr(bytes); }

static size_t word_count(b_lean_obj_arg bytes) { return lean_sarray_size(bytes) / 8; }

static lean_obj_res alloc_words(size_t n) {
    return lean_alloc_sarray(1, 8 * n, 8 * n);
}

/* The CUDA runtime finds the driver with `dlopen("libcuda.so.1")`. A Lean executable runs under
   the dynamic loader of Lean's toolchain, which on a non-NixOS host does not search the system's
   library directories, so the driver is loaded here first, by absolute path; the runtime's
   `dlopen` then matches it by soname. `IXAI_LIBCUDA` names the driver explicitly. */
static void load_driver_once(void) {
    const char *configured = getenv("IXAI_LIBCUDA");
    const char *candidates[] = {configured, "libcuda.so.1", "/usr/lib/x86_64-linux-gnu/libcuda.so.1",
                                "/usr/lib64/libcuda.so.1", "/run/opengl-driver/lib/libcuda.so.1"};
    for (size_t i = 0; i < sizeof candidates / sizeof candidates[0]; i++)
        if (candidates[i] != NULL && dlopen(candidates[i], RTLD_NOW | RTLD_GLOBAL) != NULL) return;
}

static void load_driver(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, load_driver_once);
}

/* Context.create (nIn nHidden nOut maxBatch : UInt32) : IO Context */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_create(uint32_t n_in, uint32_t n_hidden, uint32_t n_out,
                                              uint32_t max_batch, lean_obj_arg world) {
    (void)world;
    if (n_in > INT32_MAX || n_hidden > INT32_MAX || n_out > INT32_MAX || max_batch > INT32_MAX)
        return fail("model shape out of range");
    load_driver();
    IxaiGpu *gpu = ixai_gpu_create((int)n_in, (int)n_hidden, (int)n_out, (int)max_batch);
    if (gpu == NULL) return cuda_fail("allocating device buffers");
    context *c = malloc(sizeof(context));
    if (c == NULL) {
        ixai_gpu_destroy(gpu);
        return fail("out of host memory");
    }
    *c = (context){gpu, n_in, n_hidden, n_out, max_batch, 0};
    return lean_io_result_mk_ok(lean_alloc_external(context_class(), c));
}

/* Context.setModel (ctx : @& Context) (model : @& ByteArray) : IO Unit
   `model` is `w1 ++ b1 ++ w2 ++ b2`. */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_set_model(b_lean_obj_arg ctx, b_lean_obj_arg model,
                                                 lean_obj_arg world) {
    (void)world;
    context *c = context_of(ctx);
    if (lean_sarray_size(model) != 8 * model_length(c))
        return fail("model does not have the context's shape");
    if (ixai_gpu_set_model(c->gpu, words(model)) != 0) return cuda_fail("uploading the model");
    return lean_io_result_mk_ok(lean_box(0));
}

/* Context.model (ctx : @& Context) : IO ByteArray */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_model(b_lean_obj_arg ctx, lean_obj_arg world) {
    (void)world;
    context *c = context_of(ctx);
    lean_object *out = alloc_words(model_length(c));
    if (ixai_gpu_get_model(c->gpu, words(out)) != 0) {
        lean_dec(out);
        return cuda_fail("downloading the model");
    }
    return lean_io_result_mk_ok(out);
}

/* Context.step (ctx : @& Context) (x t : @& ByteArray) (batch : UInt32) (lr : UInt64) : IO Bool
   `x` is `batch × nIn` and `t` is `batch × nOut`. False when an intermediate value left its fixed
   width; the device's model is then invalid. */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_step(b_lean_obj_arg ctx, b_lean_obj_arg x, b_lean_obj_arg t,
                                            uint32_t batch, uint64_t lr, lean_obj_arg world) {
    (void)world;
    context *c = context_of(ctx);
    if (batch > c->max_batch || word_count(x) != batch * c->n_in ||
        word_count(t) != batch * c->n_out || lean_sarray_size(x) % 8 || lean_sarray_size(t) % 8)
        return fail("batch does not have the context's shape");
    c->last_batch = batch;
    switch (ixai_gpu_step(c->gpu, words(x), words(t), (int)batch, (int64_t)lr)) {
    case 0: return lean_io_result_mk_ok(lean_box(1));
    case 1: return lean_io_result_mk_ok(lean_box(0));
    default: return cuda_fail("running the step");
    }
}

/* Context.keys (ctx : @& Context) : IO ByteArray
   The last step's key buffers, concatenated in the order of `ixai_gpu_keys`. */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_keys(b_lean_obj_arg ctx, lean_obj_arg world) {
    (void)world;
    context *c = context_of(ctx);
    size_t I = c->n_in, H = c->n_hidden, O = c->n_out, B = c->last_batch;
    if (B == 0) return fail("no step with a non-empty batch has been run");
    lean_object *out = alloc_words(3 * B * H + B * O + 2 * H * I + 2 * O * H + H + O);
    if (ixai_gpu_keys(c->gpu, words(out)) != 0) {
        lean_dec(out);
        return cuda_fail("downloading the hint keys");
    }
    return lean_io_result_mk_ok(out);
}

/* Context.setPath (ctx : @& Context) (path : UInt32) : IO Unit
   0: tensor cores for large GEMMs, 1: CUDA cores only, 2: tensor cores whenever the operands fit. */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_set_path(b_lean_obj_arg ctx, uint32_t path, lean_obj_arg world) {
    (void)world;
    if (path > 2 || ixai_gpu_set_path(context_of(ctx)->gpu, (int)path) != 0) return fail("unknown GEMM path");
    return lean_io_result_mk_ok(lean_box(0));
}

/* Context.tensorGemms (ctx : @& Context) : IO UInt32 */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_tensor_gemms(b_lean_obj_arg ctx, lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)ixai_gpu_tensor_gemms(context_of(ctx)->gpu)));
}

/* Context.kernelMs (ctx : @& Context) : IO Float */
LEAN_EXPORT lean_obj_res ixai_lean_gpu_kernel_ms(b_lean_obj_arg ctx, lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_float((double)ixai_gpu_kernel_ms(context_of(ctx)->gpu)));
}
