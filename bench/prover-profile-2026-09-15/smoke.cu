#include <cuda_runtime.h>
#include <cassert>

__global__ void profile_smoke(int *value) { *value = 42; }

int main() {
  int *device, host = 0;
  assert(cudaMalloc(&device, sizeof(int)) == cudaSuccess);
  assert(cudaMemcpy(device, &host, sizeof(int), cudaMemcpyHostToDevice) == cudaSuccess);
  profile_smoke<<<1, 1>>>(device);
  assert(cudaMemcpy(&host, device, sizeof(int), cudaMemcpyDeviceToHost) == cudaSuccess);
  assert(cudaFree(device) == cudaSuccess);
  assert(host == 42);
}
