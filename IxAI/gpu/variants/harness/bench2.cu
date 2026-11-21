// Timing and equality harness for gpu/cuda/step.cu (compiled with -DSTEP_CU="path").
// The blocking runtime calls of the step are redirected through timers, so a step's wall time
// splits into time blocked in synchronising calls and the rest (enqueueing and host work).
//   bench full PROBLEM REPS                 the deployed run (600 steps), digest of every step
//   bench shape I H O B REPS PATH           one step at a shape, best/mean, digest
//   bench trace I H O B STEPS PATH          per-kernel device time per step (CUPTI activity)
//   bench sweep                             digests of fixed + random shapes, 3 paths, 2 steps each
//   bench miss I H O B X1 X2                limb-count cache misses against CUDA cores
#include <cuda_runtime.h>
#include <cupti.h>
#include <cxxabi.h>
#include <time.h>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <string>
#include <vector>

static double now_us() {
  timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e6 + t.tv_nsec / 1e3;
}
static double g_sync_us = 0;
static int g_sync_calls = 0;
#define TIMED(call)              \
  ({                             \
    double t0_ = now_us();       \
    auto r_ = call;              \
    g_sync_us += now_us() - t0_; \
    g_sync_calls++;              \
    r_;                          \
  })
static cudaError_t h_memcpy(void* d, const void* s, size_t n, cudaMemcpyKind k) { return TIMED(cudaMemcpy(d, s, n, k)); }
static cudaError_t h_memset(void* d, int v, size_t n) { return TIMED(cudaMemset(d, v, n)); }
static cudaError_t h_devsync() { return TIMED(cudaDeviceSynchronize()); }
static cudaError_t h_streamsync(cudaStream_t s) { return TIMED(cudaStreamSynchronize(s)); }
static cudaError_t h_eventsync(cudaEvent_t e) { return TIMED(cudaEventSynchronize(e)); }
#undef cudaMemcpy
#undef cudaMemset
#undef cudaStreamSynchronize
#define cudaMemcpy h_memcpy
#define cudaMemset h_memset
#define cudaDeviceSynchronize h_devsync
#define cudaStreamSynchronize h_streamsync
#define cudaEventSynchronize h_eventsync
#include STEP_CU
#undef cudaMemcpy
#undef cudaMemset
#undef cudaDeviceSynchronize
#undef cudaStreamSynchronize
#undef cudaEventSynchronize

static size_t keys_len(size_t I, size_t H, size_t O, size_t B) {
  return 3 * B * H + B * O + 2 * H * I + 2 * O * H + H + O;
}

static u64 fnv(u64 h, const std::vector<i64>& v) {
  for (i64 x : v)
    for (int b = 0; b < 8; b++) h = (h ^ (u64)((x >> (8 * b)) & 0xff)) * 1099511628211ULL;
  return h;
}

struct Stats {
  std::vector<double> wall, dev, sync, keys, model;
  int syncs = 0;
};

static double median(std::vector<double> v) {
  std::sort(v.begin(), v.end());
  return v.empty() ? 0 : v[v.size() / 2];
}
static double mean(const std::vector<double>& v) {
  double s = 0;
  for (double x : v) s += x;
  return v.empty() ? 0 : s / v.size();
}
static double minimum(const std::vector<double>& v) { return v.empty() ? 0 : *std::min_element(v.begin(), v.end()); }

static void report(const char* what, Stats& s) {
  printf("%s: step wall mean %.1f us median %.1f min %.1f | device span mean %.1f us | blocked in sync calls mean %.1f us, %d sync calls per step | keys %.1f us | model %.1f us\n",
         what, mean(s.wall), median(s.wall), minimum(s.wall), mean(s.dev), mean(s.sync), s.syncs,
         mean(s.keys), mean(s.model));
}

static std::vector<i64> read_ints(char*& p, int n) {
  std::vector<i64> v(n);
  for (int i = 0; i < n; i++) v[i] = strtoll(p, &p, 10);
  return v;
}

static char* expect(char* p, const char* tag) {
  while (*p == ' ' || *p == '\n') p++;
  size_t n = strlen(tag);
  if (strncmp(p, tag, n)) { fprintf(stderr, "expected %s\n", tag); exit(1); }
  return p + n;
}

int run_full(const char* path, int reps) {
  FILE* f = fopen(path, "rb");
  if (!f) return 1;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  std::string text(n, 0);
  if (fread(&text[0], 1, n, f) != (size_t)n) return 1;
  fclose(f);
  char* p = &text[0];
  p = expect(p, "problem");
  int I = strtol(p, &p, 10), H = strtol(p, &p, 10), O = strtol(p, &p, 10);
  i64 lr = strtoll(p, &p, 10);
  int steps = strtol(p, &p, 10);
  p = expect(p, "w1"); auto w1 = read_ints(p, H * I);
  p = expect(p, "b1"); auto b1 = read_ints(p, H);
  p = expect(p, "w2"); auto w2 = read_ints(p, O * H);
  p = expect(p, "b2"); auto b2 = read_ints(p, O);
  std::vector<std::vector<i64>> xs, ts;
  int maxb = 1;
  for (int s = 0; s < steps; s++) {
    p = expect(p, "batch");
    int B = strtol(p, &p, 10);
    p = expect(p, "x"); xs.push_back(read_ints(p, B * I));
    p = expect(p, "t"); ts.push_back(read_ints(p, B * O));
    maxb = std::max(maxb, B);
  }
  IxaiGpu* g = ixai_gpu_create(I, H, O, maxb);
  if (!g) { fprintf(stderr, "create: %s\n", ixai_gpu_error()); return 1; }
  printf("full: I %d H %d O %d max batch %d, %d steps, %d reps\n", I, H, O, maxb, steps, reps);
  Stats s;
  u64 h = 1469598103934665603ULL;
  std::vector<i64> keys, mm(H * I + H + O * H + O), init;
  init.insert(init.end(), w1.begin(), w1.end()); init.insert(init.end(), b1.begin(), b1.end());
  init.insert(init.end(), w2.begin(), w2.end()); init.insert(init.end(), b2.begin(), b2.end());
  double total_step = 0, total_all = 0;
  for (int r = 0; r < reps; r++) {
    ixai_gpu_set_model(g, init.data());
    double run0 = now_us(), steps_only = 0;
    for (int i = 0; i < steps; i++) {
      int B = xs[i].size() / I;
      g_sync_us = 0; g_sync_calls = 0;
      double t0 = now_us();
      int rc = ixai_gpu_step(g, xs[i].data(), ts[i].data(), B, lr);
      double t1 = now_us();
      double sync = g_sync_us; int calls = g_sync_calls;
      if (rc != 0) { fprintf(stderr, "step %d: %d %s\n", i, rc, ixai_gpu_error()); return 1; }
      keys.assign(keys_len(I, H, O, B), 0);
      ixai_gpu_keys(g, keys.data());
      double t2 = now_us();
      ixai_gpu_get_model(g, mm.data());
      double t3 = now_us();
      steps_only += t1 - t0;
      if (r == reps - 1) { h = fnv(h, keys); h = fnv(h, mm); }
      if (r > 0) {
        s.wall.push_back(t1 - t0); s.dev.push_back(1000 * ixai_gpu_kernel_ms(g)); s.sync.push_back(sync);
        s.keys.push_back(t2 - t1); s.model.push_back(t3 - t2); s.syncs = calls;
      }
    }
    if (r > 0) { total_step += steps_only; total_all += now_us() - run0; }
  }
  report("full", s);
  printf("full: per run of %d steps: steps only %.2f ms, steps + keys + model %.2f ms (mean of %d warm runs)\n", steps,
         total_step / 1e3 / (reps - 1), total_all / 1e3 / (reps - 1), reps - 1);
  printf("full: digest of every step's keys and model %016llx\n", h);
  ixai_gpu_destroy(g);
  return 0;
}

static std::vector<i64> random_words(u64& s, size_t n, i64 bound) {
  std::vector<i64> out(n);
  u64 span = 2 * (u64)bound + 1;
  for (size_t i = 0; i < n; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    out[i] = (i64)(s % span) - bound;
  }
  return out;
}

int run_shape(int I, int H, int O, int B, int reps, int path) {
  u64 s = 0x9E3779B97F4A7C15ULL;
  auto model = random_words(s, (size_t)H * I + H + (size_t)O * H + O, 128);
  auto x = random_words(s, (size_t)B * I, 256);
  auto t = random_words(s, (size_t)B * O, 256);
  IxaiGpu* g = ixai_gpu_create(I, H, O, B);
  if (!g) { fprintf(stderr, "create: %s\n", ixai_gpu_error()); return 1; }
  ixai_gpu_set_path(g, path);
  Stats st;
  std::vector<i64> keys(keys_len(I, H, O, B)), mm(model.size());
  for (int r = 0; r < reps; r++) {
    ixai_gpu_set_model(g, model.data());
    g_sync_us = 0; g_sync_calls = 0;
    double t0 = now_us();
    int rc = ixai_gpu_step(g, x.data(), t.data(), B, 1);
    double t1 = now_us();
    double sync = g_sync_us; int calls = g_sync_calls;
    if (rc != 0) { fprintf(stderr, "step: %d %s\n", rc, ixai_gpu_error()); return 1; }
    ixai_gpu_keys(g, keys.data());
    double t2 = now_us();
    ixai_gpu_get_model(g, mm.data());
    double t3 = now_us();
    if (r > 0) {
      st.wall.push_back(t1 - t0); st.dev.push_back(1000 * ixai_gpu_kernel_ms(g)); st.sync.push_back(sync);
      st.keys.push_back(t2 - t1); st.model.push_back(t3 - t2); st.syncs = calls;
    }
  }
  u64 h = 1469598103934665603ULL;
  h = fnv(h, keys); h = fnv(h, mm);
  char what[128];
  snprintf(what, sizeof what, "shape %dx%dx%d batch %d path %d (%d tensor GEMMs)", I, H, O, B, path,
           ixai_gpu_tensor_gemms(g));
  report(what, st);
  printf("%s: digest of keys and model %016llx\n", what, h);
  ixai_gpu_destroy(g);
  return 0;
}

/* ---- CUPTI activity trace ---------------------------------------------------------------------- */

struct Agg { double ns = 0; long n = 0; };
static std::map<std::string, Agg> g_kern;
static Agg g_h2d, g_d2h, g_memset;

static std::string short_name(const char* mangled) {
  int st = 0;
  char* d = abi::__cxa_demangle(mangled, nullptr, nullptr, &st);
  std::string s = st == 0 && d ? d : mangled;
  free(d);
  size_t p = s.find('(');
  if (p != std::string::npos) s = s.substr(0, p);
  const char* ns = "(anonymous namespace)::";
  size_t q = s.find(ns);
  if (q != std::string::npos) s.erase(q, strlen(ns));
  return s;
}

static void CUPTIAPI buf_req(uint8_t** buf, size_t* size, size_t* maxrec) {
  *size = 16 << 20;
  *buf = (uint8_t*)aligned_alloc(8, *size);
  *maxrec = 0;
}

static void CUPTIAPI buf_done(CUcontext, uint32_t, uint8_t* buf, size_t, size_t valid) {
  CUpti_Activity* r = nullptr;
  while (cuptiActivityGetNextRecord(buf, valid, &r) == CUPTI_SUCCESS) {
    if (r->kind == CUPTI_ACTIVITY_KIND_CONCURRENT_KERNEL) {
      auto* k = (CUpti_ActivityKernel12*)r;
      Agg& a = g_kern[short_name(k->name)];
      a.ns += k->end - k->start; a.n++;
    } else if (r->kind == CUPTI_ACTIVITY_KIND_MEMCPY) {
      auto* m = (CUpti_ActivityMemcpy6*)r;
      Agg& a = m->copyKind == CUPTI_ACTIVITY_MEMCPY_KIND_HTOD ? g_h2d : g_d2h;
      a.ns += m->end - m->start; a.n++;
    } else if (r->kind == CUPTI_ACTIVITY_KIND_MEMSET) {
      auto* m = (CUpti_ActivityMemset4*)r;
      g_memset.ns += m->end - m->start; g_memset.n++;
    }
  }
  free(buf);
}

int run_trace(int I, int H, int O, int B, int steps, int path) {
  u64 s = 0x9E3779B97F4A7C15ULL;
  auto model = random_words(s, (size_t)H * I + H + (size_t)O * H + O, 128);
  auto x = random_words(s, (size_t)B * I, 256);
  auto t = random_words(s, (size_t)B * O, 256);
  IxaiGpu* g = ixai_gpu_create(I, H, O, B);
  if (!g) { fprintf(stderr, "create: %s\n", ixai_gpu_error()); return 1; }
  ixai_gpu_set_path(g, path);
  ixai_gpu_set_model(g, model.data());
  for (int i = 0; i < 3; i++) ixai_gpu_step(g, x.data(), t.data(), B, 1);
  cudaDeviceSynchronize();
  if (cuptiActivityRegisterCallbacks(buf_req, buf_done) != CUPTI_SUCCESS ||
      cuptiActivityEnable(CUPTI_ACTIVITY_KIND_CONCURRENT_KERNEL) != CUPTI_SUCCESS) {
    printf("trace: CUPTI unavailable\n");
    return 0;
  }
  cuptiActivityEnable(CUPTI_ACTIVITY_KIND_MEMCPY);
  cuptiActivityEnable(CUPTI_ACTIVITY_KIND_MEMSET);
  double t0 = now_us();
  for (int i = 0; i < steps; i++) ixai_gpu_step(g, x.data(), t.data(), B, 1);
  double wall = (now_us() - t0) / steps;
  cudaDeviceSynchronize();
  cuptiActivityFlushAll(1);
  cuptiActivityDisable(CUPTI_ACTIVITY_KIND_CONCURRENT_KERNEL);
  cuptiActivityDisable(CUPTI_ACTIVITY_KIND_MEMCPY);
  cuptiActivityDisable(CUPTI_ACTIVITY_KIND_MEMSET);
  double total = 0;
  long launches = 0;
  for (auto& [k, a] : g_kern) { total += a.ns; launches += a.n; }
  printf("trace %dx%dx%d batch %d path %d: %.1f launches per step, kernel time %.1f us per step, wall %.1f us per step (traced); H2D %.1f us (%ld), D2H %.1f us (%ld), memset %.1f us (%ld) per step\n",
         I, H, O, B, path, (double)launches / steps, total / 1e3 / steps, wall, g_h2d.ns / 1e3 / steps,
         g_h2d.n / steps, g_d2h.ns / 1e3 / steps, g_d2h.n / steps, g_memset.ns / 1e3 / steps, g_memset.n / steps);
  std::vector<std::pair<double, std::string>> rows;
  for (auto& [k, a] : g_kern) rows.push_back({a.ns, k});
  std::sort(rows.rbegin(), rows.rend());
  for (auto& [ns, k] : rows)
    printf("  %-40s %6.2f per step  %9.2f us per step  %8.2f us each\n", k.c_str(), (double)g_kern[k].n / steps,
           ns / 1e3 / steps, ns / 1e3 / g_kern[k].n);
  g_kern.clear(); g_h2d = g_d2h = g_memset = Agg{};
  ixai_gpu_destroy(g);
  return 0;
}

/* ---- equality across shapes, paths and limb-count changes ------------------------------------- */

struct Outcome { int rc, tensor; u64 digest; };

// Two steps from the same model at one shape and path; the second batch has a different magnitude,
// so the limb counts cached by the first step may not fit it.
static Outcome two_steps(int path, int I, int H, int O, int B, i64 x1, i64 x2, u64 seed) {
  u64 s = seed;
  auto model = random_words(s, (size_t)H * I + H + (size_t)O * H + O, 128);
  auto a = random_words(s, (size_t)B * I, x1);
  auto b = random_words(s, (size_t)B * I, x2);
  auto t = random_words(s, (size_t)B * O, 256);
  IxaiGpu* g = ixai_gpu_create(I, H, O, B);
  if (!g) { printf("create failed: %s\n", ixai_gpu_error()); return {-2, 0, 0}; }
  ixai_gpu_set_path(g, path);
  ixai_gpu_set_model(g, model.data());
  u64 h = 1469598103934665603ULL;
  std::vector<i64> keys(keys_len(I, H, O, B)), m(model.size());
  int rc = 0;
  for (auto* x : {&a, &b}) {
    rc = ixai_gpu_step(g, x->data(), t.data(), B, 1);
    if (rc != 0) break;
    ixai_gpu_keys(g, keys.data());
    ixai_gpu_get_model(g, m.data());
    h = fnv(fnv(h, keys), m);
  }
  Outcome o{rc, ixai_gpu_tensor_gemms(g), rc == 0 ? h : 0};
  ixai_gpu_destroy(g);
  return o;
}

int run_sweep() {
  struct S { int I, H, O, B; };
  std::vector<S> shapes = {{1, 1, 1, 1},       {3, 5, 2, 4},       {8, 16, 11, 20},     {33, 65, 31, 17},
                           {70, 130, 66, 67},  {64, 64, 64, 64},   {1, 300, 1, 129},    {129, 1, 257, 65},
                           {256, 512, 128, 300}, {500, 300, 200, 1000}, {1024, 32, 10, 2000}, {17, 2049, 3, 5},
                           {31, 33, 32, 1},    {96, 32, 31, 33},   {2, 1000, 1000, 2}};
  u64 r = 20261120;
  for (int i = 0; i < 25; i++) {
    auto v = random_words(r, 4, 300);
    shapes.push_back({(int)(llabs(v[0]) + 1), (int)(llabs(v[1]) * 2 + 1), (int)(llabs(v[2]) + 1), (int)(llabs(v[3]) * 2 + 1)});
  }
  const i64 mags[3] = {256, 1048576, 2147483653LL};
  int bad = 0, n = 0;
  for (size_t k = 0; k < shapes.size(); k++) {
    S sh = shapes[k];
    i64 x1 = mags[k % 3], x2 = mags[(k + 1) % 3];
    Outcome o[3];
    for (int p = 0; p < 3; p++) o[p] = two_steps(p, sh.I, sh.H, sh.O, sh.B, x1, x2, 1000 + k);
    bool same = o[0].rc == o[1].rc && o[1].rc == o[2].rc && o[0].digest == o[1].digest && o[1].digest == o[2].digest;
    printf("sweep %dx%dx%d batch %d |x| %lld then %lld: rc %d, digest %016llx, tensor GEMMs %d/%d/%d; paths %s\n", sh.I,
           sh.H, sh.O, sh.B, x1, x2, o[1].rc, o[1].digest, o[0].tensor, o[1].tensor, o[2].tensor,
           same ? "agree" : "DIFFER");
    bad += !same; n++;
  }
  printf("sweep: %d shapes, %d with paths disagreeing\n", n, bad);
  return bad ? 1 : 0;
}

int main(int argc, char** argv) {
  if (argc >= 4 && !strcmp(argv[1], "full")) return run_full(argv[2], atoi(argv[3]));
  if (argc >= 8 && !strcmp(argv[1], "shape"))
    return run_shape(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]));
  if (argc >= 8 && !strcmp(argv[1], "trace"))
    return run_trace(atoi(argv[2]), atoi(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]));
  if (argc >= 2 && !strcmp(argv[1], "sweep")) return run_sweep();
  fprintf(stderr, "usage\n");
  return 2;
}
