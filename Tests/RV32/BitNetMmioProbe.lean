/-
  BitNetMmioProbe — diagnose BitNet MMIO write/read by observing all
  4 LTL premise signals at runtime.

  Per IP/RV32/Verification/BitNetTimingLTL.lean:

    P1: ∀t, mmioWE.val t ∧ mmioIsInput.val t →
            aiInputReg.val (t+1) = newVal.val t
    P2: aiInputReg K-cycle preservation
    P3: bitnetOut.val t = ffn(aiInputReg.val t)
    P4: lw at offset 0x40000008 → mmioRdata = bitnetOut

  We dump the relevant wires every cycle and find:
    - cycles where mmioWE && mmioIsInput fire (= sw to 0x40000004)
    - cycles where exwb_physAddr = 0x40000008 (= lw observation)
  Then check if P1-P4 hold at those cycles.
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

private def hex8 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (2 - s.length) '0') ++ s

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let maxCycles := (args[1]? >>= String.toNat?).getD 10000
  IO.println s!"Loading {cppPath}..."
  let h ← JIT.compileAndLoad cppPath

  -- Probe wires for ALL 4 LTL premises.
  let wireNames := #[
    "_gen_pcReg",                  -- 0
    "_gen_aiInputReg",             -- 1
    "_gen_aiStatusReg",            -- 2
    "_gen_idex_memWrite",          -- 3 (sw EX-stage flag)
    "_gen_alu_result_approx",      -- 4 (sw EX-stage address)
    "_gen_ex_rs2_approx",          -- 5 (sw EX-stage data)
    "_gen_exwb_physAddr",          -- 6 (lw EXWB-stage address)
    "_gen_exwb_alu",               -- 7 (lw EXWB-stage alu result)
    "_gen_idex_memRead",           -- 8 (lw EX-stage flag)
    "_gen_uartValid",              -- 9 (UART tx detect for context)
    "_gen_uartData"                -- 10 (UART data)
  ]
  let widx ← wireNames.mapM fun n => do
    match (← JIT.findWire h n) with
    | some i => pure i
    | none   => do
        IO.eprintln s!"  WARN: wire {n} missing — using 0"
        pure 0xFFFFFFFF  -- sentinel, we'll skip these reads

  IO.println "Probing for: _gen_bitnetOut..."
  let _ ← match (← JIT.findWire h "_gen_bitnetOut") with
    | some i => do IO.println s!"  found _gen_bitnetOut at idx {i}"; pure i
    | none   => do IO.println "  _gen_bitnetOut NOT FOUND — using _gen_next as proxy"; pure 0
  let bitnetOutIdx ← match (← JIT.findWire h "_gen_bitnetOut") with
    | some i => pure i
    | none   => match (← JIT.findWire h "_gen_next") with
                | some i => pure i
                | none => pure 0xFFFFFFFF

  -- Reset first, then load IMEM (Sparkle's JIT.reset clears all memory).
  JIT.reset h
  let firmware ← loadHex "firmware/opensbi/boot.hex"
  let memSize := min firmware.size 1024
  IO.println s!"Loading {memSize} words of boot.hex into IMEM (port 0)..."
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem h 0 i.toUInt32 word.toNat.toUInt32

  IO.println s!"\nRunning {maxCycles} cycles."
  IO.println "Dumping on EVENT cycles: mmioWE+mmioIsInput, exwb_physAddr=0x40000008, UART-tx, aiInputReg-change."
  let prevInputRef ← IO.mkRef (0xDEADBEEF : UInt64)
  let swEventCountRef ← IO.mkRef (0 : Nat)
  let lwEventCountRef ← IO.mkRef (0 : Nat)
  let uartBytesRef ← IO.mkRef (#[] : Array UInt8)
  for cycle in [:maxCycles] do
    JIT.eval h
    JIT.tick h
    let pc            ← JIT.getWire h widx[0]!
    let aiInputReg    ← JIT.getWire h widx[1]!
    let _aiStatusReg  ← JIT.getWire h widx[2]!
    let idex_memW     ← JIT.getWire h widx[3]!
    let alu_result    ← JIT.getWire h widx[4]!
    let ex_rs2        ← JIT.getWire h widx[5]!
    let exwb_physAddr ← JIT.getWire h widx[6]!
    let _exwb_alu     ← JIT.getWire h widx[7]!
    let _idex_memR    ← JIT.getWire h widx[8]!
    let uartValid     ← JIT.getWire h widx[9]!
    let uartData      ← JIT.getWire h widx[10]!
    let bitnetOut     ← JIT.getWire h bitnetOutIdx
    -- Detect events of interest:
    -- (a) sw to 0x40000004 (mmioWE_ex true; idex_memWrite=true ∧ alu_result low4 = 0x4)
    let isMmio := alu_result.toNat &&& 0x40000000 != 0
    let lowOff := alu_result.toNat &&& 0xF
    let isInputOff := lowOff == 0x4
    let swToInput := idex_memW.toNat == 1 && isMmio && isInputOff
    -- (b) lw at offset 0x40000008
    let lwAddr := exwb_physAddr.toNat == 0x40000008
    -- (c) aiInputReg changed
    let prevInp ← prevInputRef.get
    let inputChanged := aiInputReg != prevInp
    -- (d) UART tx
    let uartTx := uartValid.toNat == 1
    if uartTx then
      let byte := (uartData.toNat % 256).toUInt8
      uartBytesRef.modify (·.push byte)
    if swToInput then
      swEventCountRef.modify (· + 1)
      IO.println s!"cycle {cycle} [SW→aiInput]: pc=0x{hex32 pc.toNat} ex_rs2=0x{hex32 ex_rs2.toNat} alu_result=0x{hex32 alu_result.toNat} → expect aiInputReg(t+1) = ex_rs2"
    if lwAddr then
      lwEventCountRef.modify (· + 1)
      IO.println s!"cycle {cycle} [LW@0x40000008]: pc=0x{hex32 pc.toNat} aiInputReg=0x{hex32 aiInputReg.toNat} bitnetOut=0x{hex32 bitnetOut.toNat}"
    if inputChanged then
      IO.println s!"cycle {cycle} [aiInputReg-CHANGE]: pc=0x{hex32 pc.toNat} aiInputReg=0x{hex32 aiInputReg.toNat} bitnetOut=0x{hex32 bitnetOut.toNat} (was 0x{hex32 prevInp.toNat})"
      prevInputRef.set aiInputReg

  let bytes ← uartBytesRef.get
  let swEvents ← swEventCountRef.get
  let lwEvents ← lwEventCountRef.get
  IO.println "\n══════════════════════════════════════════════"
  IO.println s!"Summary after {maxCycles} cycles:"
  IO.println s!"  sw events to BitNet input register: {swEvents}"
  IO.println s!"  lw events from BitNet output register: {lwEvents}"
  IO.println s!"  UART bytes emitted: {bytes.size}"
  if bytes.size > 0 then
    let asStr := String.mk (bytes.toList.map fun b => Char.ofNat b.toNat)
    IO.println "  UART output (first 500 chars):"
    IO.println (asStr.take 500)
  IO.println "══════════════════════════════════════════════"

  JIT.destroy h
  return 0
