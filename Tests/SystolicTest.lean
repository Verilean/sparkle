/-
  Systolic matrix–vector array (`IP/Systolic/MatVec.lean`), generated with
  `systolic_grid%`.

    1. Simulation: with the activations held, the packed output settles to
       y = Wᵀ·a (`matVecRef`), for 4 × 4 and 16 × 16, including negative
       activations and weights.
    2. Cross-check: the 2 × 2 array written with the macro equals the same
       array with its four PEs written out by hand, cycle by cycle.
    3. Synthesis: hierarchical Verilog (one `pe` module, R·C instances) and
       the GPU intra kernel (`#writeCudaIntraDesign`) — the packed input is
       sliced at the top level and the packed output concatenated there,
       which the intra backend accepts.
    GPU co-simulation of the emitted kernels: `lake exe systolic-cosim`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Systolic.MatVec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Systolic

namespace Sparkle.Tests.SystolicTest

/-- 2 × 2 with the macro … -/
def matVec2 {dom : DomainConfig} (a : Signal dom (BitVec 16)) : Signal dom (BitVec 64) :=
  systolic_grid% 2 2
    (cell i j left up => pe left up (Signal.pure (weight i j)))
    (right := aOut) (down := pOut)
    (leftEdge i => activation a i)
    (topEdge j => Signal.pure 0#32)

/-- … and written out by hand. -/
def matVec2Manual {dom : DomainConfig} (a : Signal dom (BitVec 16)) : Signal dom (BitVec 64) :=
  let zero : Signal dom (BitVec 32) := Signal.pure 0#32
  let p00 := pe (activation a 0) zero (Signal.pure (weight 0 0))
  let p01 := pe p00.aOut zero (Signal.pure (weight 0 1))
  let p10 := pe (activation a 1) p00.pOut (Signal.pure (weight 1 0))
  let p11 := pe p10.aOut p01.pOut (Signal.pure (weight 1 1))
  p11.pOut ++ p10.pOut

section SynthesisChecks
#synthesizeVerilogDesign matVec2
#synthesizeVerilogDesign matVec4
#writeCudaIntraDesign matVec4 ".lake/build/gen/cuda/systolic_matvec4.cu"
#writeCudaIntraDesign matVec16 ".lake/build/gen/cuda/systolic_matvec16.cu"
set_option maxRecDepth 100000 in
#writeCudaIntraDesign matVec32 ".lake/build/gen/cuda/systolic_matvec32.cu"
end SynthesisChecks

def check (label : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then IO.println s!"  PASS {label}" else IO.println s!"  FAIL {label} {detail}"
  return ok

def main : IO Unit := do
  IO.println "--- Systolic matrix-vector array ---"
  let mut ok := true
  -- 4 × 4: activations 3, −2, 7, −128 (packed, row 0 in the low byte)
  let a4 : BitVec 32 := 0x8007fe03#32
  let y4 := (matVec4 (dom := defaultDomain) (Signal.pure a4)).val 12
  let got4 := (List.range 4).map fun j => (column y4 j).toNat
  let exp4 := (List.range 4).map fun j => (matVecRef 4 a4 j).toNat
  ok := (← check "4x4 settles to Wᵀ·a" (got4 == exp4) s!"got {got4} expected {exp4}") && ok
  -- before the array has filled, the result differs (the pipeline is real)
  let early := (matVec4 (dom := defaultDomain) (Signal.pure a4)).val 2
  ok := (← check "4x4 has not settled after 2 cycles"
    ((List.range 4).map (fun j => (column early j).toNat) != exp4)) && ok
  -- 16 × 16: activation i = (i·37 + 11) mod 256, so both signs occur
  let a16 : BitVec 128 := (List.range 16).foldl
    (fun acc i => acc ||| (BitVec.ofNat 128 ((i * 37 + 11) % 256) <<< (8 * i))) 0#128
  let y16 := (matVec16 (dom := defaultDomain) (Signal.pure a16)).val 40
  let got16 := (List.range 16).map fun j => (column y16 j).toNat
  let exp16 := (List.range 16).map fun j => (matVecRef 16 a16 j).toNat
  ok := (← check "16x16 settles to Wᵀ·a" (got16 == exp16) s!"got {got16} expected {exp16}") && ok
  -- macro vs hand-written, every cycle, with a changing input
  let aT : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 2749 + 5)⟩
  let viaMacro := (List.range 12).map fun t => ((matVec2 aT).val t).toNat
  let byHand := (List.range 12).map fun t => ((matVec2Manual aT).val t).toNat
  ok := (← check "2x2 macro == hand-written (12 cycles)" (viaMacro == byHand)
    s!"macro {viaMacro} hand {byHand}") && ok
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.SystolicTest
