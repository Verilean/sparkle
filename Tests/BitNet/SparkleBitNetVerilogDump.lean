/-
  Dump Sparkle BitNet spec values to files for cross-validation.

  Note: Verilog generation now uses #synthesizeVerilog on Signal DSL definitions
  (compile-time macro). CircuitM build* functions have been removed.
  This file only dumps spec reference values.
-/

import IP.BitNet.Config
import IP.BitNet.Types

open Sparkle.IP.BitNet

def main : IO Unit := do
  let outDir := "/tmp/bitnet_cross_validation/sparkle"
  IO.FS.createDirAll outDir

  -- Spec values (CircuitM-independent reference implementations)
  let acc : BitVec 48 := BitVec.ofNat 48 0x10000
  let scale : BitVec 32 := BitVec.ofNat 32 0x01000000
  IO.FS.writeFile s!"{outDir}/spec_values.txt" (
    s!"fixedPointScale(1.0,1.0) = {(fixedPointScale acc scale).toNat}\n" ++
    s!"reluSquared(2.0) = {(reluSquared (BitVec.ofNat 32 0x20000)).toNat}\n" ++
    s!"residualAdd(1.0,1.0) = {(residualAdd (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0x10000)).toNat}\n" ++
    s!"elemMul(2.0,3.0) = {(elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0x30000)).toNat}\n" ++
    s!"quantizeToInt8(1.0,10) = {(quantizeToInt8 (BitVec.ofNat 32 0x10000) 10).toInt}\n" ++
    s!"int8DotProduct([1,2,3],[4,5,6]) = {int8DotProduct #[BitVec.ofInt 8 1, BitVec.ofInt 8 2, BitVec.ofInt 8 3] #[BitVec.ofInt 8 4, BitVec.ofInt 8 5, BitVec.ofInt 8 6]}\n"
  )

  IO.println s!"Sparkle BitNet spec values dumped to {outDir}/"
  IO.println "Note: For Verilog generation, use #synthesizeVerilog on Signal DSL definitions."
