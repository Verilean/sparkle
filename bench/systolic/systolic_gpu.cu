// GPU persistent-kernel simulation of the weight-stationary systolic array —
// the "Strategy 4" scheduler: 1 PE = 1 thread, one thread block per array,
// __syncthreads() between the read phase and the latch phase each cycle.
//
// This is the scheduler that CANNOT be replaced by adding machines: it makes a
// SINGLE array instance faster by running its N*N PEs concurrently, which is
// the whole point of the PoC.  Contrast systolic_cpu.cpp (serial per cycle).
//
//   nvcc -O3 -std=c++17 -o systolic_gpu systolic_gpu.cu
//   ./systolic_gpu <N> <cycles>
//
// Block-size constraint: one block owns the whole array, so __syncthreads()
// synchronises all PEs.  A block is capped at 1024 threads, so N<=32 here
// (16x16=256, 32x32=1024).  N=64 (4096 PEs) needs a grid-wide barrier
// (cooperative groups) or a multi-block tiling — deliberately left as the next
// step; this PoC answers "does PE-per-thread + syncthreads scale 16->32?".

#include "systolic_common.h"
#include <cstdio>
#include <cstdlib>
#include <cuda_runtime.h>

// State lives in global memory; the block loads it into shared once, iterates
// all cycles in shared with a barrier per phase, then writes back.  This keeps
// the per-cycle cost to two __syncthreads() and no global traffic.
__global__ void systolic_persistent_kernel(
    const int8_t* __restrict__ w,
    const int32_t* __restrict__ ain,
    int32_t* __restrict__ p_out_final,
    int N, long cycles)
{
  extern __shared__ int32_t sm[];      // 2*N*N : [a | p]
  int32_t* a = sm;
  int32_t* p = sm + N * N;

  int tid = threadIdx.x;               // 0 .. N*N-1
  int total = N * N;
  int i = tid / N, j = tid % N;

  // Init shared state (only the N*N active threads).
  if (tid < total) { a[tid] = 0; p[tid] = 0; }
  __syncthreads();

  for (long c = 0; c < cycles; ++c) {
    int32_t a_out = 0, p_out = 0;
    if (tid < total) {
      int32_t a_in = (j == 0) ? ain[i] : a[i * N + (j - 1)];
      int32_t p_in = (i == 0) ? 0      : p[(i - 1) * N + j];
      p_out = p_in + a_in * (int32_t)w[tid];
      a_out = a_in;
    }
    __syncthreads();                   // all reads of old a/p done
    if (tid < total) { a[tid] = a_out; p[tid] = p_out; }
    __syncthreads();                   // new values latched before next read
  }

  if (tid < total && i == N - 1) p_out_final[j] = p[tid];  // bottom row
}

int main(int argc, char** argv) {
  int  N      = (argc > 1) ? atoi(argv[1]) : 32;
  long cycles = (argc > 2) ? atol(argv[2]) : 100000;

  if (N * N > 1024) {
    printf("GPU  N=%-3d  SKIP (%d PEs > 1024/block; needs grid-sync, see header)\n",
           N, N * N);
    return 0;
  }

  SystolicState s;
  systolic_init(s, N);

  int8_t*  d_w;   cudaMalloc((void**)&d_w,   N * N * sizeof(int8_t));
  int32_t* d_ain; cudaMalloc((void**)&d_ain, N * sizeof(int32_t));
  int32_t* d_out; cudaMalloc((void**)&d_out, N * sizeof(int32_t));
  cudaMemcpy(d_w,   s.w.data(),   N * N * sizeof(int8_t),  cudaMemcpyHostToDevice);
  cudaMemcpy(d_ain, s.ain.data(), N * sizeof(int32_t),     cudaMemcpyHostToDevice);

  size_t shmem = 2 * N * N * sizeof(int32_t);

  // Warm-up (JIT/launch overhead out of the timed region).
  systolic_persistent_kernel<<<1, N * N, shmem>>>(d_w, d_ain, d_out, N, 1);
  cudaDeviceSynchronize();

  cudaEvent_t e0, e1; cudaEventCreate(&e0); cudaEventCreate(&e1);
  cudaEventRecord(e0);
  systolic_persistent_kernel<<<1, N * N, shmem>>>(d_w, d_ain, d_out, N, cycles);
  cudaEventRecord(e1);
  cudaEventSynchronize(e1);
  float ms = 0; cudaEventElapsedTime(&ms, e0, e1);

  std::vector<int32_t> out(N);
  cudaMemcpy(out.data(), d_out, N * sizeof(int32_t), cudaMemcpyDeviceToHost);

  // Recompute checksum with the same fold as the CPU (over bottom row).
  int64_t chk = 0;
  for (int j = 0; j < N; ++j) chk = chk * 1000003 + out[j];

  double secs = ms / 1e3;
  double cps  = cycles / secs;
  double peps = cps * (double)N * N;
  printf("GPU  N=%-3d cycles=%-9ld  %.3f s  %.3e cyc/s  %.3e PE-upd/s  checksum=%lld\n",
         N, cycles, secs, cps, peps, (long long)chk);

  cudaFree(d_w); cudaFree(d_ain); cudaFree(d_out);
  return 0;
}
