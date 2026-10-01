/-
  D2Q9 lattice-Boltzmann fluid (`IP/Fluid/LBM.lean`) on a periodic lattice
  generated with `torus_grid%`.

  Reference model (pure Lean, the same fixed-point arithmetic):
    1. total mass and total momentum are constant, exactly, over hundreds
       of steps (rounding included), while the flow decays;
    2. physics: a shear wave decays with the viscosity ν = (1/ω − 1/2)/3
       the method promises, for three values of ω — the fixed-point model
       against the same method in double precision (arithmetic), and
       double precision against theory (the method's own error, which
       must shrink four-fold when the lattice is refined);
    3. physics: a Taylor–Green vortex decays at the rate 2νk².
  Circuit:
    4. 4 × 4 lattice, `Signal.val`, every cycle == the reference model;
    5. 16 × 16 lattice, JIT-compiled, == the reference model at checkpoints
       up to 200 steps (every population of every site);
    6. hierarchical Verilog (one cell module, R·C instances) and the GPU
       intra kernel are emitted.
  GPU co-simulation of the emitted kernel: `lake exe fluid-cosim`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Fluid.LBM

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Sim
open Sparkle.IP.Fluid.LBM

namespace Sparkle.Tests.FluidLbmTest

/-- The lattices at the default clock domain (what `#sim` compiles). -/
def tg4Top (omega : Signal defaultDomain (BitVec 32)) (load : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 4608) := tg4 omega load

def tg16Top (omega : Signal defaultDomain (BitVec 32)) (load : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 73728) := tg16 omega load

noncomputable def tg32Top (omega : Signal defaultDomain (BitVec 32)) (load : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 294912) := tg32 omega load

section SynthesisChecks
#synthesizeVerilogDesign tg4Top
set_option maxRecDepth 100000 in
#writeCudaIntraDesign tg16Top ".lake/build/gen/cuda/lbm_tg16.cu"
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
#writeCudaIntraDesign tg32Top ".lake/build/gen/cuda/lbm_tg32.cu"
end SynthesisChecks

set_option maxRecDepth 100000 in
#sim tg16Top

/-! ### Measurements on the reference model -/

def toF (x : BitVec 32) : Float := Float.ofInt x.toInt / 16777216.0

def pi : Float := 3.141592653589793

/-- Amplitude of the fundamental shear mode: (2/R)·Σᵢ jx(i, 0)·sin(2πi/R). -/
def shearAmplitude (l : Lattice) : Float :=
  let r := l.rows.toFloat
  (List.range l.rows).foldl (fun acc i =>
    acc + toF (l.get i 0).jx * Float.sin (2.0 * pi * i.toFloat / r)) 0.0 * 2.0 / r

/-- Amplitude of the Taylor–Green mode: (4/n²)·Σ jx·(−cos kx · sin ky). -/
def tgAmplitude (l : Lattice) : Float :=
  let n := l.rows.toFloat
  (List.range l.rows).foldl (fun acc i =>
    (List.range l.cols).foldl (fun acc j =>
      acc + toF (l.get i j).jx *
        (-(Float.cos (2.0 * pi * j.toFloat / n) * Float.sin (2.0 * pi * i.toFloat / n)))) acc)
    0.0 * 4.0 / (n * n)

/-! ### The same method in floating point

A double-precision lattice-Boltzmann shear wave (`rows` × 1, periodic),
to separate the two sources of error: the METHOD's own discretisation
error (float vs. theory, second order in the lattice spacing) and the
ARITHMETIC (fixed point vs. float). -/

def cxF : Array Float := #[0, 1, 0, -1, 0, 1, -1, -1, 1]
def cyF : Array Float := #[0, 0, 1, 0, -1, 1, 1, -1, -1]
def cyN : Array Int := #[0, 0, 1, 0, -1, 1, 1, -1, -1]
def wF : Array Float :=
  #[4.0 / 9.0, 1.0 / 9.0, 1.0 / 9.0, 1.0 / 9.0, 1.0 / 9.0,
    1.0 / 36.0, 1.0 / 36.0, 1.0 / 36.0, 1.0 / 36.0]

def eqF (rho jx jy : Float) (d : Nat) : Float :=
  let cj := cxF[d]! * jx + cyF[d]! * jy
  wF[d]! * (rho + 3.0 * cj + 4.5 * cj * cj - 1.5 * (jx * jx + jy * jy))

/-- One step on a `rows` × 1 lattice (population d of row i at `i*9 + d`). -/
def stepF (rows : Nat) (omega : Float) (g : Array Float) : Array Float :=
  Array.ofFn (n := rows * 9) fun idx =>
    let i := idx.val / 9
    let d := idx.val % 9
    let from_ (e : Nat) : Float :=
      g[(((Int.ofNat i - cyN[e]!) % Int.ofNat rows).toNat) * 9 + e]!
    let f : Array Float := Array.ofFn (n := 9) fun e => from_ e.val
    let rho := f.foldl (· + ·) 0.0
    let jx := (List.range 9).foldl (fun a e => a + cxF[e]! * f[e]!) 0.0
    let jy := (List.range 9).foldl (fun a e => a + cyF[e]! * f[e]!) 0.0
    f[d]! + omega * (eqF rho jx jy d - f[d]!)

def ampF (rows : Nat) (g : Array Float) : Float :=
  (List.range rows).foldl (fun acc i =>
    let jx := (List.range 9).foldl (fun a e => a + cxF[e]! * g[i * 9 + e]!) 0.0
    acc + jx * Float.sin (2.0 * pi * i.toFloat / rows.toFloat)) 0.0 * 2.0 / rows.toFloat

/-- Viscosity measured on the floating-point shear wave. -/
def nuFloat (rows : Nat) (omega : Float) (steps : Nat) : Float :=
  let g0 : Array Float := Array.ofFn (n := rows * 9) fun idx =>
    eqF 0.0 (toF (shearJx rows (idx.val / 9))) 0.0 (idx.val % 9)
  let g := (List.range steps).foldl (fun g _ => stepF rows omega g) g0
  let k := 2.0 * pi / rows.toFloat
  Float.log (ampF rows g0 / ampF rows g) / (k * k * steps.toFloat)

/-- Viscosity the method promises for collision frequency ω. -/
def nuTheory (omega : Float) : Float := (1.0 / omega - 0.5) / 3.0

def check (label : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then IO.println s!"  PASS {label}" else IO.println s!"  FAIL {label} {detail}"
  return ok

/-- A float with a few decimals, without trailing zeros. -/
def fmt (x : Float) : String :=
  let s := toString ((x * 100000.0).round / 100000.0)
  if s.contains '.' then
    let t := (s.toList.reverse.dropWhile (· == '0')).reverse
    String.ofList (if t.getLast? == some '.' then t.dropLast else t)
  else s

def main : IO Unit := do
  IO.println "--- Lattice-Boltzmann fluid ---"
  let mut ok := true
  let t0 ← IO.monoMsNow
  let omega125 := omegaOf 4 5        -- τ = 0.8, ω = 1.25, ν = 0.1

  -- 1. conservation on the reference model
  do
    let l0 := tgLattice 16
    let l := l0.run omega125 300
    ok := (← check "mass is constant over 300 steps (exactly)" (l.mass == l0.mass)
      s!"{l0.mass.toInt} → {l.mass.toInt}") && ok
    ok := (← check "momentum is constant over 300 steps (exactly)" (l.momentum == l0.momentum)
      s!"{repr l0.momentum} → {repr l.momentum}") && ok
    ok := (← check "… while the flow itself has decayed (the lattice is not frozen)"
      (tgAmplitude l < 0.5 * tgAmplitude l0 && tgAmplitude l > 0.0)) && ok

  -- 2. shear wave: measured viscosity against ν = (1/ω − 1/2)/3.
  --    Two separate claims:
  --    (a) arithmetic — the fixed-point model agrees with the same method
  --        in double precision;
  --    (b) method — double precision agrees with theory, and its error
  --        shrinks about four-fold from 32 to 64 rows (second order).
  for (tauN, tauD, steps) in [(1, 1, 60), (4, 5, 100), (5, 8, 200)] do
    let omega := omegaOf tauN tauD
    let omegaF := toF omega
    let theory := nuTheory omegaF
    let fixed (rows steps : Nat) : Float :=
      let l0 := shearLattice rows 2
      let l := l0.run omega steps
      let k := 2.0 * pi / rows.toFloat
      Float.log (shearAmplitude l0 / shearAmplitude l) / (k * k * steps.toFloat)
    let nuX32 := fixed 32 steps
    let nuX64 := fixed 64 (4 * steps)
    let nuF32 := nuFloat 32 omegaF steps
    let nuF64 := nuFloat 64 omegaF (4 * steps)
    let arith := max (nuX32 / nuF32 - 1.0).abs (nuX64 / nuF64 - 1.0).abs
    let e32 := (nuF32 / theory - 1.0).abs
    let e64 := (nuF64 / theory - 1.0).abs
    ok := (← check s!"shear wave, ω = {fmt omegaF}: ν = {fmt nuX32} (fixed point), theory {fmt theory}; fixed vs double {fmt (arith * 100.0)} %"
      (arith < 0.00005)) && ok
    ok := (← check s!"  method error vs theory: {fmt (e32 * 100.0)} % at 32 rows, {fmt (e64 * 100.0)} % at 64 rows"
      (e32 < 0.015 && (e32 < 0.0005 || e64 < e32 / 3.0))) && ok

  -- 3. Taylor–Green vortex: amplitude decays as exp(−2νk²t)
  do
    let l0 := tgLattice 32
    let steps := 100
    let l := l0.run omega125 steps
    let k := 2.0 * pi / 32.0
    let rate := Float.log (tgAmplitude l0 / tgAmplitude l) / steps.toFloat
    let theory := 2.0 * nuTheory (toF omega125) * k * k
    let err := (rate / theory - 1.0).abs
    ok := (← check s!"Taylor–Green 32×32: decay rate {fmt rate}, theory 2νk² = {fmt theory} ({fmt (err * 100.0)} % off)"
      (err < 0.01)) && ok

  let t1 ← IO.monoMsNow
  -- 4. the 4 × 4 circuit, every cycle, against the model.
  --    `load` is high in cycle 0, so the registers hold the initial
  --    condition in cycle 1 and step t−1 of the model in cycle t.
  do
    let omegaS : Signal defaultDomain (BitVec 32) := Signal.pure omega125
    let loadS : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
    let lat := tg4Top omegaS loadS
    let got := (List.range 5).map fun t => (lat.val (t + 1)).toNat
    let model := (List.range 5).map fun t => ((tgLattice 4).run omega125 t).pack
    ok := (← check "4×4 circuit == model, cycles 1..5 (every population)" (got == model)) && ok
    ok := (← check "4×4 circuit: the lattice is not at rest and not frozen"
      (got.head? != some 0 && got.head? != got.getLast?)) && ok

  let t2 ← IO.monoMsNow
  -- 5. the 16 × 16 circuit, JIT-compiled.  `read` after the k-th `step`
  --    returns the outputs before that clock edge: cycle k−1.
  do
    let sim ← tg16Top.Sim.load
    let l0 := tgLattice 16
    let mut model := l0
    let mut modelStep := 0
    let mut good := true
    let mut checked := 0
    for k in [1:203] do
      Sim.step sim ({ _gen_omega := omega125, _gen_load := if k == 1 then 1 else 0 } :
        tg16Top.Sim.SimInput)
      -- after step k the outputs are cycle k−1 = model step k−2
      if k ≥ 2 then
        let want := k - 2
        while modelStep < want do
          model := model.step omega125
          modelStep := modelStep + 1
        if want ∈ [0, 1, 2, 3, 10, 50, 100, 200] then
          let o ← Sim.read sim
          checked := checked + 1
          if o.out.toNat != model.pack then
            good := false
            IO.println s!"    mismatch at model step {want}"
    Sim.destroy sim
    ok := (← check s!"16×16 circuit (JIT) == model at {checked} checkpoints up to step 200" good) && ok
    ok := (← check "16×16: mass after 200 steps == initial mass" (model.mass == l0.mass)) && ok

  let t3 ← IO.monoMsNow
  IO.println s!"  (model {t1 - t0} ms, Signal.val {t2 - t1} ms, JIT {t3 - t2} ms)"
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.FluidLbmTest
