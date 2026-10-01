// Weight-stationary int8 MAC systolic array — shared cycle semantics.
//
// This header defines the *reference* cycle behaviour that both the CPU
// (systolic_cpu.cpp) and GPU (systolic_gpu.cu) implementations must match
// bit-for-bit.  It is the single source of truth for "what one clock cycle
// does", so the PoC compares two *schedulers* of the same circuit, not two
// different circuits.
//
// Array (N x N PEs), weight-stationary:
//   - PE[i][j] holds a fixed int8 weight w[i][j].
//   - Each cycle, PE[i][j] reads an activation a_in from its LEFT neighbour
//     (column j-1; the left edge j=0 reads the streamed input row) and a
//     partial sum p_in from its TOP neighbour (row i-1; the top edge i=0
//     reads 0).
//   - It computes  p_out = p_in + (int32)a_in * (int32)w[i][j]
//     and passes a_in to the RIGHT (a_out = a_in) and p_out DOWN.
//   - Bottom-edge p_out (row i=N-1) is the column's accumulated result.
//
// State per PE: {a, p} both int32 (the value currently latched on its output
// registers).  One cycle = combational compute from neighbours' *previous*
// registered outputs, then latch.  That two-phase (read-all-then-latch)
// structure is exactly what forces a __syncthreads() between phases on the GPU.

#pragma once
#include <cstdint>
#include <vector>

struct SystolicDims {
  int N;          // array is N x N PEs
};

// Flattened PE state: row-major, index = i*N + j.
struct SystolicState {
  int N;
  std::vector<int8_t>  w;   // N*N  fixed weights
  std::vector<int32_t> a;   // N*N  latched activation-passthrough register
  std::vector<int32_t> p;   // N*N  latched partial-sum register
  // Left-edge activation input per row, for the current cycle (length N).
  std::vector<int32_t> ain; // N
};

// Advance one clock cycle on the host, in place.  This is the golden model.
// Read phase uses the *old* a/p; write phase latches new values.
static inline void systolic_step_cpu(SystolicState& s) {
  const int N = s.N;
  std::vector<int32_t> na(N * N), np(N * N);
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      int32_t a_in = (j == 0) ? s.ain[i] : s.a[i * N + (j - 1)];
      int32_t p_in = (i == 0) ? 0        : s.p[(i - 1) * N + j];
      int32_t p_out = p_in + a_in * (int32_t)s.w[i * N + j];
      na[i * N + j] = a_in;      // a_out = a_in
      np[i * N + j] = p_out;
    }
  }
  s.a.swap(na);
  s.p.swap(np);
}

// A cheap deterministic fill so CPU and GPU start from identical state
// without needing Math.random / a seed file.
static inline void systolic_init(SystolicState& s, int N) {
  s.N = N;
  s.w.assign(N * N, 0);
  s.a.assign(N * N, 0);
  s.p.assign(N * N, 0);
  s.ain.assign(N, 0);
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j)
      s.w[i * N + j] = (int8_t)(((i * 7 + j * 3) % 5) - 2);  // -2..2
    s.ain[i] = (int32_t)((i % 8) - 3);                       // -3..4
  }
}

// A tiny checksum over the bottom row's accumulated results (the array output),
// used to confirm CPU and GPU agree.
static inline int64_t systolic_output_checksum(const SystolicState& s) {
  const int N = s.N;
  int64_t acc = 0;
  for (int j = 0; j < N; ++j) acc = acc * 1000003 + s.p[(N - 1) * N + j];
  return acc;
}
