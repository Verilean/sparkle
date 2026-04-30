/-
  BitNetMmioProbe — diagnose why MMIO read of BitNet returns input.

  Loads a tiny firmware that does:
      sw  s2, 0(t0)    where t0 = 0x40000004, s2 = 0x10000
      nop x4
      lw  s4, 0(t0)    where t0 = 0x40000008
      ... loop forever

  Then steps the JIT cycle-by-cycle and dumps every BitNet pipeline
  wire on every cycle PC is in the load region. Compare values
  against the Lean unit-test golden (input 0x10000 → output 0x410000).
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Utils.HexLoader

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Utils.HexLoader

private def hex32 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  IO.println s!"Loading {cppPath}..."
  let h ← JIT.compileAndLoad cppPath

  -- Resolve all BitNet pipeline wires.
  let wireNames := #[
    "_gen_pcReg",            -- 0
    "_gen_aiInputReg",       -- 1
    "_gen_gateAcc",          -- 2
    "_gen_gateScaled",       -- 3
    "_gen_gateActivated",    -- 4
    "_gen_upAcc",            -- 5
    "_gen_upScaled",         -- 6
    "_gen_elemResult",       -- 7
    "_gen_downScaled"        -- 8
  ]
  let widx ← wireNames.mapM fun n => do
    match (← JIT.findWire h n) with
    | some i => pure i
    | none   => throw (IO.userError s!"wire {n} missing")

  -- Reset first, then load IMEM (Sparkle's JIT.reset clears all memory).
  JIT.reset h
  let firmware ← loadHex "firmware/opensbi/boot.hex"
  let memSize := min firmware.size 1024
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem h 0 i.toUInt32 word.toNat.toUInt32

  IO.println "\nRunning 30000 cycles. Dump on aiInputReg change OR every 500 cycles."
  let prevInputRef ← IO.mkRef (0xDEADBEEF : UInt64)
  for cycle in [:30000] do
    JIT.eval h
    JIT.tick h
    let vals ← widx.mapM fun i => JIT.getWire h i
    let inp := vals[1]?.getD 0
    let prevInp ← prevInputRef.get
    let inputChanged := inp != prevInp
    let periodic := cycle % 500 == 0 && cycle > 0
    if inputChanged || periodic then
      let pc := vals[0]?.getD 0
      let tag := if inputChanged then "INPUT-CHANGE" else "tick"
      IO.println s!"cycle {cycle} [{tag}]: pc=0x{hex32 pc.toNat} aiInputReg=0x{hex32 inp.toNat}"
      if inputChanged then
        IO.println s!"  gateAcc=0x{hex32 (vals[2]?.getD 0).toNat} gateScaled=0x{hex32 (vals[3]?.getD 0).toNat} gateActivated=0x{hex32 (vals[4]?.getD 0).toNat}"
        IO.println s!"  upAcc=0x{hex32 (vals[5]?.getD 0).toNat} upScaled=0x{hex32 (vals[6]?.getD 0).toNat}"
        IO.println s!"  elemResult=0x{hex32 (vals[7]?.getD 0).toNat} downScaled=0x{hex32 (vals[8]?.getD 0).toNat}"
        prevInputRef.set inp

  JIT.destroy h
  return 0
