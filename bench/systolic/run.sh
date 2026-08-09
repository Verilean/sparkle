#!/usr/bin/env bash
# Systolic-array SIM PoC: CPU serial vs GPU persistent-kernel (PE-per-thread).
#
# Answers: does 1-PE-per-thread + __syncthreads() make a SINGLE array
# instance faster as the array grows (16x16 -> 32x32)?  The batch backend
# (PR #115) can't do this — it parallelises across instances, not within one.
#
#   ./run.sh            # builds what it can, runs the sweep
#   CYCLES=200000 ./run.sh
set -u
cd "$(dirname "$0")"
CYCLES="${CYCLES:-100000}"
# GPU SM architecture (RTX 4070 Ti = sm_89).  Override for other GPUs.
ARCH="${ARCH:-sm_89}"
# On NixOS the real driver libcuda.so.1 lives here, not on the default loader
# path; cudart_static dlopens it at run time, so a CUDA binary silently fails
# with "driver version insufficient" unless this is on LD_LIBRARY_PATH.
# Harmless (and skipped) where the dir doesn't exist.
if [ -d /run/opengl-driver/lib ]; then
  export LD_LIBRARY_PATH="/run/opengl-driver/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
fi

echo "== build =="
g++ -O3 -std=c++17 -o systolic_cpu systolic_cpu.cpp && echo "  cpu: ok" || { echo "  cpu: FAILED"; exit 1; }
HAVE_GPU=0 HAVE_GRID=0
if command -v nvcc >/dev/null 2>&1; then
  if nvcc -O3 -std=c++17 -arch="$ARCH" -o systolic_gpu systolic_gpu.cu 2>/tmp/nvcc.err; then
    HAVE_GPU=1; echo "  gpu 1-block: ok (arch=$ARCH)"
  else
    echo "  gpu 1-block: nvcc failed:"; sed 's/^/    /' /tmp/nvcc.err
  fi
  # grid-sync kernel needs relocatable device code for cooperative groups.
  if nvcc -O3 -std=c++17 -arch="$ARCH" -rdc=true -o systolic_gpu_grid systolic_gpu_grid.cu 2>/tmp/nvcc.err; then
    HAVE_GRID=1; echo "  gpu grid  : ok (arch=$ARCH, -rdc=true)"
  else
    echo "  gpu grid  : nvcc failed:"; sed 's/^/    /' /tmp/nvcc.err
  fi
else
  echo "  gpu: nvcc not found — CPU-only run (see header for what GPU adds)"
fi

echo
echo "== sweep (cycles=$CYCLES) =="
for N in 16 32 64 128 256; do
  ./systolic_cpu "$N" "$CYCLES"
  [ "$HAVE_GPU" = 1 ]  && ./systolic_gpu      "$N" "$CYCLES"   # 1-block (N<=32)
  [ "$HAVE_GRID" = 1 ] && ./systolic_gpu_grid "$N" "$CYCLES"   # grid-sync (any N)
done

echo
echo "Cross-check: all 'checksum=' for a given N must match (CPU is golden)."
echo "PE-upd/s = work done; cyc/s = how fast one run advances."
echo "1-block wins cyc/s for small N; grid-sync scales PE-upd/s with PE count."
