// CUDA error reporting of the C entry points of `step.cu`: a failing call returns -1 (or a null
// context) and `ixai_gpu_error` names the CUDA error that caused it, and a failure does not leak
// into the calls after it. Built and run by `gpu/error-test.sh`.
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

struct IxaiGpu;
extern "C" {
const char* ixai_gpu_error();
IxaiGpu* ixai_gpu_create(int n_in, int n_hidden, int n_out, int max_batch);
void ixai_gpu_destroy(IxaiGpu* g);
int ixai_gpu_set_model(IxaiGpu* g, const int64_t* model);
int ixai_gpu_get_model(IxaiGpu* g, int64_t* model);
int ixai_gpu_step(IxaiGpu* g, const int64_t* x, const int64_t* t, int n_batch, int64_t lr);
int ixai_gpu_keys(IxaiGpu* g, int64_t* out);
}

static int failures = 0;

static void expect(bool cond, const char* what) {
  printf("%s: %s\n", cond ? "ok" : "FAIL", what);
  if (!cond) failures++;
}

int main() {
  const int I = 2, H = 3, O = 2, B = 4;
  std::vector<int64_t> model(H * I + H + O * H + O, 1), x(B * I, 2), t(B * O, 3), out(model.size());
  std::vector<int64_t> keys(3 * B * H + B * O + 2 * H * I + 2 * O * H + H + O);

  IxaiGpu* g = ixai_gpu_create(I, H, O, B);
  expect(g != nullptr, "create a small context");
  if (!g) return 1;

  // A null host buffer makes the upload fail with `cudaErrorInvalidValue`.
  int rc = ixai_gpu_set_model(g, nullptr);
  printf("set_model(null) = %d, error \"%s\"\n", rc, ixai_gpu_error());
  expect(rc == -1 && !strcmp(ixai_gpu_error(), "invalid argument"), "a failed upload reports its error");

  rc = ixai_gpu_step(g, nullptr, t.data(), B, 1);
  printf("step(x = null) = %d, error \"%s\"\n", rc, ixai_gpu_error());
  expect(rc == -1 && !strcmp(ixai_gpu_error(), "invalid argument"), "a failed step reports its error");

  rc = ixai_gpu_set_model(g, model.data());
  expect(rc == 0, "the next upload succeeds");
  rc = ixai_gpu_step(g, x.data(), t.data(), B, 1);
  printf("step = %d, error \"%s\"\n", rc, ixai_gpu_error());
  expect(rc == 0 && !strcmp(ixai_gpu_error(), "no error"), "the next step succeeds and reports no error");
  expect(ixai_gpu_keys(g, keys.data()) == 0 && ixai_gpu_get_model(g, out.data()) == 0,
         "keys and model download");
  ixai_gpu_destroy(g);

  // About 8 TB of weights: the allocation fails.
  IxaiGpu* huge = ixai_gpu_create(1 << 20, 1 << 20, 1, 1);
  printf("create(2^20 × 2^20) = %s, error \"%s\"\n", huge ? "context" : "null", ixai_gpu_error());
  expect(huge == nullptr && !strcmp(ixai_gpu_error(), "out of memory"), "a failed allocation reports its error");
  ixai_gpu_destroy(huge);

  printf("%s\n", failures ? "error reporting: FAILED" : "error reporting: all checks passed");
  return failures ? 1 : 0;
}
