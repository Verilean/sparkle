import Sparkle.Backend.CudaIntra
import Tests.TestCudaSim

/-  Layer 3 of the CUDA intra backend tests: co-simulation against CSim on a
    real GPU.

    The emitted `.cu`'s module functions are `__host__ __device__`, so the
    same translation unit runs BOTH sides: the CPU golden reference calls
    `sparkle_<Top>_eval_tick(&ref)` directly on the host (that IS CSim's
    sequential semantics), and the GPU side drives the public JIT API
    (`jit_cuda_alloc` / `jit_cuda_set_input` / `jit_intra_run` /
    `jit_cuda_get_output`).  Outputs are compared cycle-by-cycle, then once
    more after a multi-cycle single launch (validates the in-kernel loop).

    Needs `nvcc` + a GPU, so the compile/run half is gated on SPARKLE_CUDA=1
    and skips cleanly otherwise (the emit half always runs, so a generation
    regression still fails without a GPU). -/

open Sparkle.Backend.CudaIntra
open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Parametric N×N weight-stationary mesh over the shared `PE` fixture
    (`Tests.TestCudaSim.peModule`): activations stream from the left edge,
    partial sums flow down, bottom row is observed on `result_j`. -/
def meshTop (n : Nat) : Module := Id.run do
  let mut inputs : List Port := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩]
  let mut outputs : List Port := []
  let mut wires : List Port := [⟨"zero32", .bitVector 32⟩]
  let mut body : List Stmt := [.assign "zero32" (.const 0 32)]
  for i in [0:n] do
    inputs := inputs ++ [⟨s!"ain_{i}", .bitVector 32⟩]
  for i in [0:n] do
    for j in [0:n] do
      inputs := inputs ++ [⟨s!"w_{i}_{j}", .bitVector 32⟩]
      wires := wires ++ [⟨s!"aout_{i}_{j}", .bitVector 32⟩,
                         ⟨s!"pout_{i}_{j}", .bitVector 32⟩]
  for i in [0:n] do
    for j in [0:n] do
      let aSrc := if j == 0 then s!"ain_{i}" else s!"aout_{i}_{j-1}"
      let pSrc := if i == 0 then "zero32" else s!"pout_{i-1}_{j}"
      body := body ++ [.inst "PE" s!"pe_{i}_{j}"
        [ ("clk", .ref "clk"), ("rst", .ref "rst")
        , ("a_in", .ref aSrc), ("p_in", .ref pSrc)
        , ("w", .ref s!"w_{i}_{j}")
        , ("a_out", .ref s!"aout_{i}_{j}"), ("p_out", .ref s!"pout_{i}_{j}") ]]
  for j in [0:n] do
    outputs := outputs ++ [⟨s!"result_{j}", .bitVector 32⟩]
    body := body ++ [.assign s!"result_{j}" (.ref s!"pout_{n-1}_{j}")]
  return { name := s!"Mesh{n}x{n}", inputs, outputs, wires, body
         , isPrimitive := false }

def meshDesignN (n : Nat) : Design :=
  { topModule := s!"Mesh{n}x{n}"
  , modules := [Sparkle.Test.CudaSim.peModule, meshTop n] }

/-- Deterministic stimulus (same shape as bench/systolic): weights −2..2,
    edge activations −3..4, both masked to uint32. -/
def wVal (i j : Nat) : Nat :=
  let v : Int := Int.ofNat ((i*7 + j*3) % 5) - 2
  (((v % 4294967296) + 4294967296) % 4294967296).toNat
def aVal (i : Nat) : Nat :=
  let v : Int := Int.ofNat (i % 8) - 3
  (((v % 4294967296) + 4294967296) % 4294967296).toNat

/-- The generated C `main` appended to the emitted `.cu`.  Port indices for
    `jit_cuda_set_input` follow CSim's convention: all inputs except `clk`,
    in declaration order — rst=0, ain_i=1+i, w_i_j=1+N+i*N+j.  Outputs are
    32-bit, one slot each: result_j = slot j. -/
def cosimMain (n cycles : Nat) : String := Id.run do
  let topC := s!"Mesh{n}x{n}"
  let mut pokeRef : List String := []
  let mut pokeGpu : List String := []
  for i in [0:n] do
    pokeRef := pokeRef ++ [s!"  r->ain_{i} = {aVal i}u;"]
    pokeGpu := pokeGpu ++ [s!"  jit_cuda_set_input(h, 0, {1+i}, {aVal i}ull);"]
  for i in [0:n] do
    for j in [0:n] do
      pokeRef := pokeRef ++ [s!"  r->w_{i}_{j} = {wVal i j}u;"]
      pokeGpu := pokeGpu ++
        [s!"  jit_cuda_set_input(h, 0, {1+n+i*n+j}, {wVal i j}ull);"]
  let mut cmps : List String := []
  for j in [0:n] do
    cmps := cmps ++
      [ s!"  \{ unsigned long long g = jit_cuda_get_output(h, 0, {j});"
      , s!"    if ((uint32_t)g != r->result_{j}) \{"
      , s!"      printf(\"MISMATCH c=%d result_{j}: gpu=%llu cpu=%u\\n\", c, g, (unsigned)r->result_{j});"
      , "      fail = 1; } }" ]
  return String.intercalate "\n" <|
    [ ""
    , "// ── Generated co-simulation main (CPU golden vs intra kernel) ──"
    , "#include <ctime>"
    , s!"static void poke_ref(struct {topC}* r) \{" ]
    ++ pokeRef ++
    [ "}"
    , "static void poke_gpu(void* h) {" ]
    ++ pokeGpu ++
    [ "}"
    , s!"static int cmp_outputs(void* h, struct {topC}* r, int c) \{"
    , "  int fail = 0;" ]
    ++ cmps ++
    [ "  return fail;"
    , "}"
    , "int main() {"
    , s!"  struct {topC} ref; memset(&ref, 0, sizeof ref); poke_ref(&ref);"
    , "  void* h = jit_cuda_alloc(1); poke_gpu(h);"
    , "  int fail = 0;"
    , "  // cycle-by-cycle: CPU golden (host side of the same functions) vs GPU"
    , s!"  for (int c = 0; c < {cycles}; ++c) \{"
    , s!"    sparkle_{topC}_eval_tick(&ref);"
    , "    jit_intra_run(h, 1);"
    , "    fail |= cmp_outputs(h, &ref, c);"
    , "  }"
    , "  // multi-cycle single launch: validates the in-kernel loop"
    , s!"  struct {topC} ref2; memset(&ref2, 0, sizeof ref2); poke_ref(&ref2);"
    , s!"  for (int c = 0; c < {cycles}; ++c) sparkle_{topC}_eval_tick(&ref2);"
    , "  void* h2 = jit_cuda_alloc(1); poke_gpu(h2);"
    , s!"  jit_intra_run(h2, {cycles});"
    , "  { void* h = h2; struct " ++ topC ++ "* r = &ref2; int c = -1;"
    , "    fail |= cmp_outputs(h, r, c); }"
    , "  // informational timing (one launch)"
    , "  struct timespec t0, t1;"
    , "  clock_gettime(CLOCK_MONOTONIC, &t0);"
    , "  jit_intra_run(h2, 100000);"
    , "  clock_gettime(CLOCK_MONOTONIC, &t1);"
    , "  double secs = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;"
    , s!"  printf(\"[perf] {topC}: 100000 cycles in %.3f s = %.3e cyc/s\\n\", secs, 100000.0 / secs);"
    , "  jit_cuda_free(h); jit_cuda_free(h2);"
    , s!"  printf(fail ? \"COSIM FAIL\\n\" : \"COSIM PASS ({topC}, \{0} + one-launch cycles)\\n\");".replace "{0}" (toString cycles)
    , "  return fail;"
    , "}"
    , "" ]

def emitOne (n cycles : Nat) (dir : String) : IO String := do
  match toCudaIntraDesign (meshDesignN n) with
  | .error e =>
    IO.eprintln s!"[cosim] emit error (N={n}): {e}"
    IO.Process.exit 1
  | .ok cu =>
    let path := s!"{dir}/intra_cosim_{n}.cu"
    IO.FS.writeFile path (cu ++ cosimMain n cycles)
    IO.println s!"[cosim] emitted {path} ({cu.length} chars, {n*n} PEs)"
    return path

def main : IO Unit := do
  let dir := ".lake/build/gen/cuda"
  IO.FS.createDirAll dir
  -- Emission always runs (a generation regression fails without a GPU).
  let p2 ← emitOne 2 64 dir
  let p16 ← emitOne 16 64 dir
  if (← IO.getEnv "SPARKLE_CUDA") != some "1" then
    IO.println "[cosim] SPARKLE_CUDA != 1 — emit-only (compile+run needs nvcc + GPU)"
    IO.println "\nALL PASS (emit-only)"
    return
  let arch := (← IO.getEnv "CUDA_ARCH").getD "sm_89"
  -- NixOS keeps the real driver libcuda.so.1 off the default loader path.
  let ldExtra := "/run/opengl-driver/lib"
  let ldPath := (← IO.getEnv "LD_LIBRARY_PATH").getD "" |> fun cur =>
    if cur.isEmpty then ldExtra else s!"{ldExtra}:{cur}"
  for (path, n) in [(p2, 2), (p16, 16)] do
    let bin := s!"{dir}/intra_cosim_{n}"
    let r ← IO.Process.output {
      cmd := "nvcc",
      args := #["-O2", "-std=c++17", s!"-arch={arch}", "-rdc=true", "-o", bin, path] }
    if r.exitCode != 0 then
      IO.eprintln s!"[cosim] nvcc failed (N={n}):\n{r.stderr}"
      IO.Process.exit 1
    let rr ← IO.Process.output {
      cmd := bin,
      args := #[],
      env := #[("LD_LIBRARY_PATH", some ldPath)] }
    IO.print rr.stdout
    if rr.exitCode != 0 then
      IO.eprintln s!"[cosim] FAILED (N={n}): {rr.stderr}"
      IO.Process.exit 1
  IO.println "\nALL PASS"
