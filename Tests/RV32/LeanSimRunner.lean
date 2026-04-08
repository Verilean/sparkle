/-
  Lean-native SoC simulation runner (standalone subprocess)

  Runs rv32iSoCSimulateFull for a small number of cycles and prints PC values.
  Used by TestFlow.lean as a subprocess to work around macOS stack size limits.

  Output format (stdout):
    PC@0=0x00000000
    PC@5=0x00000014
    ...
    LEAN_SIM_OK

  Usage:
    lake exe rv32-lean-sim-runner [firmware.hex] [cycles]
-/

import IP.RV32.SoC
import Sparkle.Utils.HexLoader

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.SoC
open Sparkle.Utils.HexLoader

def main (args : List String) : IO UInt32 := do
  let hexPath := args.head? |>.getD "firmware/firmware.hex"
  let maxCycles := (args[1]? |>.bind String.toNat?) |>.getD 50

  let fileExists ← System.FilePath.pathExists hexPath
  unless fileExists do
    IO.eprintln s!"Error: firmware file not found: {hexPath}"
    return 1

  let firmware ← loadHex hexPath
  let initFn := arrayToInitFn firmware

  let soc ← @rv32iSoCSimulateFull domain50MHz initFn
  let pcSig := projN! soc 122 0

  for cycle in [:maxCycles] do
    let pc := pcSig.atTime cycle
    IO.println s!"PC@{cycle}=0x{pc.toHex}"

  IO.println "LEAN_SIM_OK"
  return 0
