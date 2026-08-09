// GPU grid-sync simulation of the weight-stationary systolic array.
//
// Extends systolic_gpu.cu past the single-block (N<=32) limit: one array now
// spans MANY blocks, so the N*N PEs are distributed across all the GPU's SMs
// and a grid-wide barrier (cooperative groups grid.sync()) replaces
// __syncthreads() between the read and latch phases each cycle.
//
// This is the configuration that actually exercises the whole GPU — the
// single-block PoC used only one SM.  State lives in GLOBAL memory (a grid
// spans SMs, so shared memory can't hold shared state); the two grid.sync()
// per cycle order the read phase before the latch phase across all blocks.
//
//   nvcc -O3 -std=c++17 -arch=sm_89 -rdc=true -o systolic_gpu_grid systolic_gpu_grid.cu
//   ./systolic_gpu_grid <N> <cycles>
//
// -rdc=true (relocatable device code) is required for cooperative-groups grid
// sync.  cudaLaunchCooperativeKernel is used instead of <<<>>> so the driver
// guarantees all blocks are co-resident (a prerequisite for grid.sync()).

#include "systolic_common.h"
#include <cstdio>
#include <cstdlib>
#include <cuda_runtime.h>
#include <cooperative_groups.h>
namespace cg = cooperative_groups;

// a/p are global arrays of length N*N, double-buffered (cur, nxt) so the read
// phase never sees a half-updated array.  Each thread owns one PE; the grid is
// sized so that gridDim.x*blockDim.x >= N*N.
__global__ void systolic_grid_kernel(
    const int8_t* __restrict__ w,
    const int32_t* __restrict__ ain,
    int32_t* __restrict__ a0, int32_t* __restrict__ p0,
    int32_t* __restrict__ a1, int32_t* __restrict__ p1,
    int32_t* __restrict__ p_out_final,
    int N, long cycles)
{
  cg::grid_group grid = cg::this_grid();
  int tid = blockIdx.x * blockDim.x + threadIdx.x;
  int total = N * N;
  int i = (tid < total) ? tid / N : 0;
  int j = (tid < total) ? tid % N : 0;

  if (tid < total) { a0[tid] = 0; p0[tid] = 0; }
  grid.sync();

  int32_t* a_cur = a0; int32_t* p_cur = p0;
  int32_t* a_nxt = a1; int32_t* p_nxt = p1;

  for (long c = 0; c < cycles; ++c) {
    if (tid < total) {
      int32_t a_in = (j == 0) ? ain[i] : a_cur[i * N + (j - 1)];
      int32_t p_in = (i == 0) ? 0      : p_cur[(i - 1) * N + j];
      a_nxt[tid] = a_in;                              // a_out = a_in
      p_nxt[tid] = p_in + a_in * (int32_t)w[tid];
    }
    grid.sync();                                       // all reads done
    // swap cur/nxt (every thread computes the same pointers — no write race)
    int32_t* ta = a_cur; a_cur = a_nxt; a_nxt = ta;
    int32_t* tp = p_cur; p_cur = p_nxt; p_nxt = tp;
    grid.sync();                                       // latch visible to all
  }

  if (tid < total && i == N - 1) p_out_final[j] = p_cur[tid];
}

int main(int argc, char** argv) {
  int  N      = (argc > 1) ? atoi(argv[1]) : 64;
  long cycles = (argc > 2) ? atol(argv[2]) : 100000;
  int  total  = N * N;

  SystolicState s;
  systolic_init(s, N);

  int8_t*  d_w;   cudaMalloc((void**)&d_w,   total * sizeof(int8_t));
  int32_t* d_ain; cudaMalloc((void**)&d_ain, N * sizeof(int32_t));
  int32_t* d_out; cudaMalloc((void**)&d_out, N * sizeof(int32_t));
  int32_t *d_a0, *d_p0, *d_a1, *d_p1;
  cudaMalloc((void**)&d_a0, total * sizeof(int32_t));
  cudaMalloc((void**)&d_p0, total * sizeof(int32_t));
  cudaMalloc((void**)&d_a1, total * sizeof(int32_t));
  cudaMalloc((void**)&d_p1, total * sizeof(int32_t));
  cudaMemcpy(d_w,   s.w.data(),   total * sizeof(int8_t),  cudaMemcpyHostToDevice);
  cudaMemcpy(d_ain, s.ain.data(), N * sizeof(int32_t),     cudaMemcpyHostToDevice);

  // Grid sizing: cooperative launch requires all blocks co-resident.  Pick a
  // block size, compute the grid to cover N*N, then verify it fits the device
  // (max co-resident blocks = SMs * blocks/SM for this kernel).
  int blockSize = 256;
  int gridSize  = (total + blockSize - 1) / blockSize;

  int dev; cudaGetDevice(&dev);
  int numBlocksPerSm = 0;
  cudaOccupancyMaxActiveBlocksPerMultiprocessor(
      &numBlocksPerSm, systolic_grid_kernel, blockSize, 0);
  cudaDeviceProp prop; cudaGetDeviceProperties(&prop, dev);
  int maxCoresident = numBlocksPerSm * prop.multiProcessorCount;
  if (gridSize > maxCoresident) {
    printf("GPU-grid N=%-3d  SKIP (needs %d co-resident blocks, device fits %d "
           "[%d/SM x %d SMs])\n",
           N, gridSize, maxCoresident, numBlocksPerSm, prop.multiProcessorCount);
    return 0;
  }

  long one = 1;
  void* argsW[] = { &d_w, &d_ain, &d_a0, &d_p0, &d_a1, &d_p1, &d_out, &N, &one };
  cudaLaunchCooperativeKernel((void*)systolic_grid_kernel,
                              gridSize, blockSize, argsW, 0, 0);
  cudaDeviceSynchronize();  // warm-up

  cudaEvent_t e0, e1; cudaEventCreate(&e0); cudaEventCreate(&e1);
  void* args[] = { &d_w, &d_ain, &d_a0, &d_p0, &d_a1, &d_p1, &d_out, &N, &cycles };
  cudaEventRecord(e0);
  cudaError_t le = cudaLaunchCooperativeKernel((void*)systolic_grid_kernel,
                              gridSize, blockSize, args, 0, 0);
  cudaEventRecord(e1);
  cudaEventSynchronize(e1);
  cudaError_t se = cudaDeviceSynchronize();
  if (le != cudaSuccess || se != cudaSuccess) {
    printf("GPU-grid N=%-3d  launch=%s sync=%s\n", N,
           cudaGetErrorString(le), cudaGetErrorString(se));
    return 1;
  }
  float ms = 0; cudaEventElapsedTime(&ms, e0, e1);

  std::vector<int32_t> out(N);
  cudaMemcpy(out.data(), d_out, N * sizeof(int32_t), cudaMemcpyDeviceToHost);
  int64_t chk = 0;
  for (int j = 0; j < N; ++j) chk = chk * 1000003 + out[j];

  double secs = ms / 1e3;
  double cps  = cycles / secs;
  double peps = cps * (double)total;
  printf("GPU-grid N=%-3d cycles=%-9ld  %.3f s  %.3e cyc/s  %.3e PE-upd/s  "
         "checksum=%lld  [grid=%d blk=%d]\n",
         N, cycles, secs, cps, peps, (long long)chk, gridSize, blockSize);

  cudaFree(d_w); cudaFree(d_ain); cudaFree(d_out);
  cudaFree(d_a0); cudaFree(d_p0); cudaFree(d_a1); cudaFree(d_p1);
  return 0;
}
