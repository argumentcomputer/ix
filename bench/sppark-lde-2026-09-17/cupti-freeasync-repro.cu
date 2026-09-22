#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
__global__ void touch(unsigned long long* p, size_t n) { size_t i = blockIdx.x * (size_t)blockDim.x + threadIdx.x; if (i < n) p[i] += 1; }
int main(int argc, char** argv) {
    const char* mode = argc > 1 ? argv[1] : "freeasync";
    cudaSetDevice(0);
    int l2 = 0; cudaDeviceGetAttribute(&l2, cudaDevAttrL2CacheSize, 0);
    unsigned long long* p = nullptr; size_t n = 1 << 16;
    if (!strcmp(mode, "mallocasync")) cudaMallocAsync((void**)&p, n * 8, cudaStreamPerThread); else cudaMalloc((void**)&p, n * 8);
    touch<<<(unsigned)((n + 255) / 256), 256, 0, cudaStreamPerThread>>>(p, n);
    cudaError_t e;
    if (!strcmp(mode, "free")) { cudaStreamSynchronize(cudaStreamPerThread); e = cudaFree(p); }
    else if (!strcmp(mode, "freeasync0")) e = cudaFreeAsync(p, 0);
    else e = cudaFreeAsync(p, cudaStreamPerThread);
    cudaError_t s = cudaStreamSynchronize(cudaStreamPerThread);
    printf("%s: free %d sync %d\n", mode, (int)e, (int)s);
    return 0;
}
