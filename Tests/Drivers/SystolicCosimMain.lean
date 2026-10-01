/-
  GPU co-simulation of the DSL-generated systolic arrays
  (`IP/Systolic/MatVec.lean`, emitted by `#writeCudaIntraDesign` when
  `Tests.SystolicTest` is built).

  For each emitted `.cu` a C `main` is appended that runs the CSim CPU
  reference (the host side of the same `__host__ __device__` functions) and
  the intra kernel side by side:
    * 64 single-cycle launches, with new activations every 8 cycles —
      every packed output word must match after every cycle;
    * one 10⁶-cycle launch against 10⁶ reference cycles — outputs must
      match, and both rates are printed.
  Compile + run needs nvcc and a GPU: gated on SPARKLE_CUDA=1 (otherwise
  the files are only checked to exist).
-/
import Tests.SystolicTest

/-- `inWords` / `outWords`: 32-bit words of the packed input / output. -/
def cosimMain (topC : String) (inWords outWords cycles perfCycles : Nat) : String :=
  let refIn := if inWords == 1 then "ref->_gen_a = v;" else "ref->_gen_a[k] = v;"
  let refOut := if outWords == 1 then "ref->out" else "ref->out[k]"
  String.intercalate "\n"
    [ ""
    , "// ── Generated co-simulation main (CPU golden vs intra kernel) ──"
    , "#include <ctime>"
    , s!"static void poke(struct {topC}* ref, void* h, unsigned seed) \{"
    , s!"  for (int k = 0; k < {inWords}; ++k) \{"
    , "    uint32_t v = 0x9E3779B9u * (seed + 1u) + 0x7F4A7C15u * (unsigned)k;"
    , s!"    {refIn}"
    , "    jit_cuda_set_input(h, 0, k, v);"
    , "  }"
    , "}"
    , s!"static int cmp(struct {topC}* ref, void* h, long c) \{"
    , "  int fail = 0;"
    , s!"  for (int k = 0; k < {outWords}; ++k) \{"
    , "    uint32_t g = (uint32_t)jit_cuda_get_output(h, 0, k);"
    , s!"    if (g != (uint32_t){refOut}) \{"
    , s!"      if (!fail) printf(\"MISMATCH cycle %ld word %d: gpu=%u cpu=%u\\n\", c, k, g, (unsigned){refOut});"
    , "      fail = 1; }"
    , "  }"
    , "  return fail;"
    , "}"
    , "int main() {"
    , s!"  struct {topC} refS; struct {topC}* ref = &refS; memset(ref, 0, sizeof refS);"
    , "  void* h = jit_cuda_alloc(1);"
    , "  int fail = 0;"
    , s!"  for (long c = 0; c < {cycles}; ++c) \{"
    , "    if (c % 8 == 0) poke(ref, h, (unsigned)c);"
    , s!"    sparkle_{topC}_eval_tick(ref);"
    , "    jit_intra_run(h, 1);"
    , "    fail |= cmp(ref, h, c);"
    , "  }"
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
    , "  fail |= cmp(ref, h, -1);"
    , s!"  printf(\"[perf] {topC} (%d PEs): CPU %.3e cyc/s, GPU %.3e cyc/s, GPU/CPU %.2f\\n\","
    , s!"         (int){topC}_intra_M, perfCycles / cpuSecs, perfCycles / gpuSecs, cpuSecs / gpuSecs);"
    , "  jit_cuda_free(h);"
    , s!"  printf(fail ? \"COSIM FAIL ({topC})\\n\" : \"COSIM PASS ({topC}: {cycles} single-cycle launches + one {perfCycles}-cycle launch)\\n\");"
    , "  return fail;"
    , "}"
    , "" ]

def main : IO Unit := do
  let dir := ".lake/build/gen/cuda"
  -- (emitted file, top struct, input words, output words)
  let designs : List (String × String × Nat × Nat) :=
    [ ("systolic_matvec4", "Sparkle_IP_Systolic_matVec4", 1, 4)
    , ("systolic_matvec16", "Sparkle_IP_Systolic_matVec16", 4, 16) ]
  let mut sources : List (String × String) := []
  for (file, topC, inW, outW) in designs do
    let path := s!"{dir}/{file}.cu"
    if !(← System.FilePath.pathExists path) then
      IO.eprintln s!"[systolic-cosim] {path} is missing — build Tests.SystolicTest (lake build systolic-test)"
      IO.Process.exit 1
    let cu ← IO.FS.readFile path
    let out := s!"{dir}/{file}_cosim.cu"
    IO.FS.writeFile out (cu ++ cosimMain topC inW outW 64 1000000)
    IO.println s!"[systolic-cosim] {path}: {cu.length} chars"
    sources := sources ++ [(file, out)]
  if (← IO.getEnv "SPARKLE_CUDA") != some "1" then
    IO.println "[systolic-cosim] SPARKLE_CUDA != 1 — emit-only (compile+run needs nvcc + GPU)"
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
      IO.eprintln s!"[systolic-cosim] nvcc failed ({file}):\n{r.stderr}"
      IO.Process.exit 1
    let rr ← IO.Process.output {
      cmd := bin, args := #[], env := #[("LD_LIBRARY_PATH", some ldPath)] }
    IO.print rr.stdout
    if rr.exitCode != 0 then
      IO.eprintln s!"[systolic-cosim] FAILED ({file}): {rr.stderr}"
      IO.Process.exit 1
  IO.println "\nALL PASS"
