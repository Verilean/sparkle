/-
  GPU co-simulation of the lattice-Boltzmann lattices (`IP/Fluid/LBM.lean`,
  emitted by `#writeCudaIntraDesign` when `Tests.FluidLbmTest` is built):
  one GPU thread per lattice site.

  For each emitted `.cu` a C `main` is appended that runs the CSim CPU
  reference (the host side of the same `__host__ __device__` functions) and
  the intra kernel side by side, at ω = 1.9 (low viscosity, so the vortex
  is still turning after thousands of steps):
    * the load cycle and 64 single-cycle launches — every population of
      every site must match after every cycle;
    * one 1000-cycle launch — every population must match and the flow must
      still be moving;
    * one 200 000-cycle launch, timed on both sides — every population must
      match, and the total mass on the GPU must equal the initial mass
      exactly; both rates and the kernel used (block / grid) are printed.
  Compile + run needs nvcc and a GPU: gated on SPARKLE_CUDA=1 (otherwise
  the files are only checked to exist).
-/
import Tests.FluidLbmTest

/-- `outWords`: 32-bit words of the packed output (9 per site). -/
def cosimMain (topC : String) (outWords cycles midCycles perfCycles : Nat) : String :=
  String.intercalate "\n"
    [ ""
    , "// ── Generated co-simulation main (CPU golden vs intra kernel) ──"
    , "#include <ctime>"
    , "#define LBM_OMEGA 31876710u  /* 1.9 in Q7.24 */"
    , s!"static int cmp(struct {topC}* ref, void* h, long c) \{"
    , "  int fail = 0;"
    , s!"  for (int k = 0; k < {outWords}; ++k) \{"
    , "    uint32_t g = (uint32_t)jit_cuda_get_output(h, 0, k);"
    , "    if (g != (uint32_t)ref->out[k]) {"
    , "      if (!fail) printf(\"MISMATCH cycle %ld word %d: gpu=%u cpu=%u\\n\", c, k, g, (unsigned)ref->out[k]);"
    , "      fail = 1; }"
    , "  }"
    , "  return fail;"
    , "}"
    , "// total mass: the sum of all populations (wraps like the hardware does)"
    , s!"static uint32_t gpuMass(void* h) \{ uint32_t m = 0; for (int k = 0; k < {outWords}; ++k) m += (uint32_t)jit_cuda_get_output(h, 0, k); return m; }"
    , "// x-momentum of site 0 row 1 … a population that the vortex keeps changing"
    , "static void both(struct " ++ topC ++ "* ref, void* h, int load) {"
    , "  ref->_gen_omega = LBM_OMEGA; ref->_gen_load = (uint8_t)load;"
    , "  jit_cuda_set_input(h, 0, 0, LBM_OMEGA); jit_cuda_set_input(h, 0, 1, (uint64_t)load);"
    , "}"
    , "int main() {"
    , s!"  struct {topC}* ref = (struct {topC}*)calloc(1, sizeof(struct {topC}));"
    , "  void* h = jit_cuda_alloc(1);"
    , "  int fail = 0;"
    , "  both(ref, h, 1);"
    , s!"  sparkle_{topC}_eval_tick(ref); jit_intra_run(h, 1);"
    , "  both(ref, h, 0);"
    , s!"  sparkle_{topC}_eval_tick(ref); jit_intra_run(h, 1);"
    , "  fail |= cmp(ref, h, 0);"
    , "  uint32_t mass0 = gpuMass(h);"
    , s!"  uint32_t first[{outWords}]; for (int k = 0; k < {outWords}; ++k) first[k] = ref->out[k];"
    , s!"  for (long c = 1; c <= {cycles}; ++c) \{"
    , s!"    sparkle_{topC}_eval_tick(ref);"
    , "    jit_intra_run(h, 1);"
    , "    fail |= cmp(ref, h, c);"
    , "  }"
    , "  // one launch while the vortex is still turning"
    , s!"  for (long c = 0; c < {midCycles}; ++c) sparkle_{topC}_eval_tick(ref);"
    , "  uint32_t before[8]; for (int k = 0; k < 8; ++k) before[k] = (uint32_t)jit_cuda_get_output(h, 0, 9 + k);"
    , s!"  jit_intra_run(h, {midCycles});"
    , "  fail |= cmp(ref, h, -1);"
    , s!"  sparkle_{topC}_eval_tick(ref); jit_intra_run(h, 1);"
    , "  fail |= cmp(ref, h, -2);"
    , "  int moving = 0; for (int k = 0; k < 8; ++k) moving |= (before[k] != (uint32_t)jit_cuda_get_output(h, 0, 9 + k));"
    , s!"  int changed = 0; for (int k = 0; k < {outWords}; ++k) changed |= (first[k] != ref->out[k]);"
    , "  if (!moving || !changed) { printf(\"FLOW DEAD: the lattice stopped changing\\n\"); fail = 1; }"
    , "  // one long launch, timed on both sides (the flow has decayed by the"
    , "  // end of it; the arithmetic per step is the same)"
    , "  struct timespec t0, t1;"
    , s!"  const long perfCycles = {perfCycles};"
    , "  clock_gettime(CLOCK_MONOTONIC, &t0);"
    , s!"  for (long c = 0; c < perfCycles; ++c) sparkle_{topC}_eval_tick(ref);"
    , "  clock_gettime(CLOCK_MONOTONIC, &t1);"
    , "  double cpuSecs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;"
    , "  clock_gettime(CLOCK_MONOTONIC, &t0);"
    , "  jit_intra_run(h, perfCycles);"
    , "  clock_gettime(CLOCK_MONOTONIC, &t1);"
    , "  double gpuSecs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;"
    , "  fail |= cmp(ref, h, -3);"
    , "  uint32_t mass1 = gpuMass(h);"
    , "  if (mass1 != mass0) { printf(\"MASS CHANGED on the GPU: %u -> %u\\n\", mass0, mass1); fail = 1; }"
    , s!"  printf(\"[perf] {topC} (%d sites, %s kernel): CPU %.3e steps/s, GPU %.3e steps/s, GPU/CPU %.2f; mass %u == %u\\n\","
    , s!"         (int){topC}_intra_M, jit_intra_last_kernel() == 1 ? \"block\" : \"grid\","
    , "         perfCycles / cpuSecs, perfCycles / gpuSecs, cpuSecs / gpuSecs, mass0, mass1);"
    , "  jit_cuda_free(h);"
    , s!"  printf(fail ? \"COSIM FAIL ({topC})\\n\" : \"COSIM PASS ({topC}: {cycles} single-cycle launches, one {midCycles}-cycle and one {perfCycles}-cycle launch)\\n\");"
    , "  return fail;"
    , "}"
    , "" ]

def main : IO Unit := do
  let dir := ".lake/build/gen/cuda"
  -- (emitted file, top struct, output words, long-launch cycles)
  let designs : List (String × String × Nat × Nat) :=
    [ ("lbm_tg16", "Sparkle_Tests_FluidLbmTest_tg16Top", 16 * 16 * 9, 200000)
    , ("lbm_tg32", "Sparkle_Tests_FluidLbmTest_tg32Top", 32 * 32 * 9, 200000) ]
  let mut sources : List (String × String) := []
  for (file, topC, outW, perf) in designs do
    let path := s!"{dir}/{file}.cu"
    if !(← System.FilePath.pathExists path) then
      IO.eprintln s!"[fluid-cosim] {path} is missing — build Tests.FluidLbmTest (lake build fluid-lbm-test)"
      IO.Process.exit 1
    let cu ← IO.FS.readFile path
    let out := s!"{dir}/{file}_cosim.cu"
    IO.FS.writeFile out (cu ++ cosimMain topC outW 64 1000 perf)
    IO.println s!"[fluid-cosim] {path}: {cu.length} chars"
    sources := sources ++ [(file, out)]
  if (← IO.getEnv "SPARKLE_CUDA") != some "1" then
    IO.println "[fluid-cosim] SPARKLE_CUDA != 1 — emit-only (compile+run needs nvcc + GPU)"
    IO.println "\nALL PASS (emit-only)"
    return
  let arch := (← IO.getEnv "CUDA_ARCH").getD "sm_89"
  let ldExtra := "/run/opengl-driver/lib"
  let ldPath := (← IO.getEnv "LD_LIBRARY_PATH").getD "" |> fun cur =>
    if cur.isEmpty then ldExtra else s!"{ldExtra}:{cur}"
  for (file, src) in sources do
    let bin := s!"{dir}/{file}_cosim"
    let r ← IO.Process.output {
      cmd := "nvcc",
      args := #["-O2", "-std=c++17", s!"-arch={arch}", "-rdc=true", "-o", bin, src] }
    if r.exitCode != 0 then
      IO.eprintln s!"[fluid-cosim] nvcc failed ({file}):\n{r.stderr.take 4000}"
      IO.Process.exit 1
    let rr ← IO.Process.output {
      cmd := bin, args := #[], env := #[("LD_LIBRARY_PATH", some ldPath)] }
    IO.print rr.stdout
    if rr.exitCode != 0 then
      IO.eprintln s!"[fluid-cosim] FAILED ({file}): {rr.stderr}"
      IO.Process.exit 1
  IO.println "\nALL PASS"
