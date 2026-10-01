// CPU baseline: single-thread serial simulation of the weight-stationary
// systolic array — the CSim-equivalent scheduler (one thread walks every PE
// each cycle).  Prints cyc/s and the output checksum for cross-check.
//
//   g++ -O3 -std=c++17 -o systolic_cpu systolic_cpu.cpp
//   ./systolic_cpu <N> <cycles>

#include "systolic_common.h"
#include <cstdio>
#include <cstdlib>
#include <ctime>

int main(int argc, char** argv) {
  int   N      = (argc > 1) ? atoi(argv[1]) : 32;
  long  cycles = (argc > 2) ? atol(argv[2]) : 100000;

  SystolicState s;
  systolic_init(s, N);

  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  for (long c = 0; c < cycles; ++c) systolic_step_cpu(s);
  clock_gettime(CLOCK_MONOTONIC, &t1);

  double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
  double cps  = cycles / secs;
  // PE-updates/s is the fair "work done" metric across array sizes.
  double peps = cps * (double)N * N;

  printf("CPU  N=%-3d cycles=%-9ld  %.3f s  %.3e cyc/s  %.3e PE-upd/s  checksum=%lld\n",
         N, cycles, secs, cps, peps, (long long)systolic_output_checksum(s));
  return 0;
}
