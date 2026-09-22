// CUDA 13.3 activity collector. CPU and GPU timestamps use CLOCK_REALTIME ns.
#include <cupti.h>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <mutex>
#include <string>
#include <unistd.h>

static CUpti_SubscriberHandle subscriber;
static FILE *output;
static std::mutex output_mutex;
static uint64_t records = 0;
static uint64_t dropped = 0;
static uint64_t invalid = 0;

static void check(CUptiResult status) {
  if (status == CUPTI_SUCCESS) return;
  const char *message = nullptr;
  cuptiGetResultString(status, &message);
  fprintf(stderr, "[cupti] %s\n", message ? message : "unknown error");
  std::abort();
}

static std::string quote(const char *name) {
  std::string result = "\"";
  for (const unsigned char *p = reinterpret_cast<const unsigned char *>(name ? name : ""); *p; ++p) {
    if (*p == '"' || *p == '\\') { result += '\\'; result += *p; }
    else if (*p < 32) {
      char escaped[7];
      snprintf(escaped, sizeof escaped, "\\u%04x", *p);
      result += escaped;
    } else result += *p;
  }
  return result + '"';
}

static void gpu_record(const char *kind, const char *name, uint64_t start, uint64_t end,
                       uint32_t device, uint32_t stream, uint32_t correlation,
                       uint64_t bytes = 0, unsigned copy_kind = 0) {
  if (!start || end < start) ++invalid;
  fprintf(output, "{\"kind\":\"%s\",\"name\":%s,\"start\":%llu,\"end\":%llu,"
          "\"device\":%u,\"stream\":%u,\"correlation\":%u,\"bytes\":%llu,\"copy_kind\":%u}\n",
          kind, quote(name).c_str(), (unsigned long long)start, (unsigned long long)end,
          device, stream, correlation, (unsigned long long)bytes, copy_kind);
}

static void CUPTIAPI request_buffer(uint8_t **buffer, size_t *size, size_t *max_records,
                                    CUpti_BufferCallbackRequestInfo *) {
  *size = 8 * 1024 * 1024;
  *max_records = 0;
  if (posix_memalign(reinterpret_cast<void **>(buffer), 8, *size)) std::abort();
}

static void CUPTIAPI complete_buffer(uint8_t *buffer, size_t, size_t valid,
                                     CUpti_BufferCallbackCompleteInfo *) {
  std::lock_guard<std::mutex> guard(output_mutex);
  CUpti_Activity *record = nullptr;
  while (valid) {
    auto status = cuptiActivityGetNextRecord_v2(subscriber, buffer, valid, &record);
    if (status == CUPTI_ERROR_MAX_LIMIT_REACHED || status == CUPTI_ERROR_INVALID_KIND) break;
    check(status);
    ++records;
    switch (record->kind) {
      case CUPTI_ACTIVITY_KIND_CONCURRENT_KERNEL: {
        auto *r = reinterpret_cast<CUpti_ActivityKernel12 *>(record);
        gpu_record("kernel", r->name, r->start, r->end, r->deviceId, r->streamId, r->correlationId);
        break;
      }
      case CUPTI_ACTIVITY_KIND_MEMCPY: {
        auto *r = reinterpret_cast<CUpti_ActivityMemcpy6 *>(record);
        gpu_record("memcpy", "memcpy", r->start, r->end, r->deviceId, r->streamId,
                   r->correlationId, r->bytes, r->copyKind);
        break;
      }
      case CUPTI_ACTIVITY_KIND_MEMSET: {
        auto *r = reinterpret_cast<CUpti_ActivityMemset4 *>(record);
        gpu_record("memset", "memset", r->start, r->end, r->deviceId, r->streamId, r->correlationId, r->bytes);
        break;
      }
      case CUPTI_ACTIVITY_KIND_MEMORY2: {
        auto *r = reinterpret_cast<CUpti_ActivityMemory4 *>(record);
        fprintf(output, "{\"kind\":\"memory\",\"timestamp\":%llu,\"operation\":%u,"
                "\"memory_kind\":%u,\"bytes\":%llu,\"address\":%llu,\"device\":%u,\"async\":%u}\n",
                (unsigned long long)r->timestamp, r->memoryOperationType, r->memoryKind,
                (unsigned long long)r->bytes, (unsigned long long)r->address, r->deviceId, r->isAsync);
        break;
      }
      case CUPTI_ACTIVITY_KIND_DRIVER:
      case CUPTI_ACTIVITY_KIND_RUNTIME: {
        auto *r = reinterpret_cast<CUpti_ActivityAPI *>(record);
        const char *name = nullptr;
        const bool driver = r->kind == CUPTI_ACTIVITY_KIND_DRIVER;
        check(cuptiGetCallbackName(driver ? CUPTI_CB_DOMAIN_DRIVER_API : CUPTI_CB_DOMAIN_RUNTIME_API,
                                  r->cbid, &name));
        if (!r->start || r->end < r->start) ++invalid;
        fprintf(output, "{\"kind\":\"%s\",\"name\":%s,\"start\":%llu,\"end\":%llu,"
                "\"tid\":%u,\"pid\":%u,\"correlation\":%u}\n", driver ? "driver" : "runtime",
                quote(name).c_str(), (unsigned long long)r->start, (unsigned long long)r->end,
                r->threadId, r->processId, r->correlationId);
        break;
      }
      default: break;
    }
  }
  size_t lost = 0;
  check(cuptiActivityGetNumDroppedRecords_v2(subscriber, nullptr, 0, &lost));
  dropped += lost;
  fflush(output);
  free(buffer);
}

static void finish() {
  check(cuptiActivityFlushAll(CUPTI_ACTIVITY_FLAG_FLUSH_FORCED));
  std::lock_guard<std::mutex> guard(output_mutex);
  fprintf(output, "{\"kind\":\"summary\",\"records\":%llu,\"dropped\":%llu,\"invalid\":%llu}\n",
          (unsigned long long)records, (unsigned long long)dropped, (unsigned long long)invalid);
  fflush(output);
  fprintf(stderr, "[cupti] %llu records, %llu dropped, %llu invalid\n",
          (unsigned long long)records, (unsigned long long)dropped, (unsigned long long)invalid);
}

static void CUPTIAPI callback(void *, CUpti_CallbackDomain, CUpti_CallbackId, const void *) {}

extern "C" int InitializeInjection() {
  static std::once_flag once;
  std::call_once(once, [] {
    const char *path = getenv("AIUR_CUDA_PROFILE");
    if (!path || !(output = fopen(path, "wx"))) {
      fprintf(stderr, "[cupti] AIUR_CUDA_PROFILE must name a new writable file\n");
      std::abort();
    }
    CUpti_SubscriberParams params = {sizeof(CUpti_SubscriberParams), nullptr, nullptr, 0, 0, 0};
    check(cuptiSubscribe_v2(&subscriber, callback, nullptr, &params));
    check(cuptiActivityRegisterCallbacks_v2(subscriber, request_buffer, complete_buffer));
    for (auto kind : {CUPTI_ACTIVITY_KIND_CONCURRENT_KERNEL, CUPTI_ACTIVITY_KIND_MEMCPY,
                      CUPTI_ACTIVITY_KIND_MEMSET, CUPTI_ACTIVITY_KIND_RUNTIME, CUPTI_ACTIVITY_KIND_DRIVER,
                      CUPTI_ACTIVITY_KIND_MEMORY2}) {
      check(cuptiActivityEnable_v2(subscriber, kind, nullptr));
    }
    fprintf(output, "{\"kind\":\"metadata\",\"pid\":%d,\"clock\":\"CLOCK_REALTIME\"}\n", getpid());
    fflush(output);
    std::atexit(finish);
  });
  return 1;
}
