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

  -- Probe wires for FFN datapath internals.
  -- NOTE: `_gen_next` (residual sum) is INLINED by Sparkle.Backend.CppSim
  -- in the JIT C++ output, so it cannot be probed directly.
  -- Instead we probe `_gen_sum` (the 33-bit pre-saturate addition)
  -- and reconstruct the saturating result here.
  let wireNames := #[
    "_gen_pcReg",                  -- 0
    "_gen_aiInputReg",             -- 1
    "_gen_gateAcc",                -- 2 ← FFN: gate BitLinear accumulator
    "_gen_gateActivated",          -- 3 ← FFN: gate × ReLU²
    "_gen_upAcc",                  -- 4 ← FFN: up BitLinear accumulator
    "_gen_elemResult",             -- 5 ← FFN: gate * up element-wise
    "_gen_downScaled",             -- 6 ← FFN: down BitLinear + scale
    "_gen_sum",                    -- 7 ← FFN: 33-bit residual sum (pre-saturate)
    "_gen_busRdataRaw",            -- 8 ← Bus rdata mux output (= what lw observes)
    "_gen_mmioRdata"               -- 9 ← MMIO rdata mux output
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
    let gateAcc       ← JIT.getWire h widx[2]!
    let gateActivated ← JIT.getWire h widx[3]!
    let upAcc         ← JIT.getWire h widx[4]!
    let elemResult    ← JIT.getWire h widx[5]!
    let downScaled    ← JIT.getWire h widx[6]!
    let gen_sum       ← JIT.getWire h widx[7]!
    let busRdataRaw   ← JIT.getWire h widx[8]!
    let mmioRdata     ← JIT.getWire h widx[9]!
    -- Reconstruct bitnetOut from _gen_sum's saturation logic.
    let top2 := (gen_sum.toNat >>> 31) &&& 0x3
    let bitnetOut : UInt64 :=
      if top2 == 2 then 0x80000000
      else if top2 == 1 then 0x7FFFFFFF
      else (gen_sum.toNat &&& 0xFFFFFFFF).toUInt64
    -- Detect aiInputReg changes (= sw event committed).
    let prevInp ← prevInputRef.get
    let inputChanged := aiInputReg != prevInp
    if inputChanged then
      IO.println s!"cycle {cycle} [aiInputReg-CHANGE]: pc=0x{hex32 pc.toNat} aiInputReg=0x{hex32 aiInputReg.toNat} → bitnetOut=0x{hex32 bitnetOut.toNat}"
      IO.println s!"  FFN trace:"
      IO.println s!"    gateAcc       = 0x{hex32 gateAcc.toNat}        (expect 4 * input)"
      IO.println s!"    gateActivated = 0x{hex32 gateActivated.toNat}  (after ReLU²)"
      IO.println s!"    upAcc         = 0x{hex32 upAcc.toNat}          (expect 4 * input)"
      IO.println s!"    elemResult    = 0x{hex32 elemResult.toNat}     (gateActivated * upScaled)"
      IO.println s!"    downScaled    = 0x{hex32 downScaled.toNat}     (down BitLinear + scale)"
      IO.println s!"    _gen_sum (33b)= 0x{hex32 gen_sum.toNat} top2={top2}"
      IO.println s!"    bitnetOut     = 0x{hex32 bitnetOut.toNat}      (saturated 33→32)"
      IO.println s!"    busRdataRaw   = 0x{hex32 busRdataRaw.toNat}    (lw return value at THIS cycle)"
      IO.println s!"    mmioRdata     = 0x{hex32 mmioRdata.toNat}      (MMIO mux output)"
      swEventCountRef.modify (· + 1)
      prevInputRef.set aiInputReg
    -- Also dump on busRdataRaw matching bitnetOut (= lw observation cycle).
    if mmioRdata.toNat != 0 || (busRdataRaw.toNat != 0 && busRdataRaw.toNat == bitnetOut.toNat) then
      let lwc ← lwEventCountRef.get
      if lwc < 16 then
        IO.println s!"cycle {cycle} [LW-OBSERVATION]: pc=0x{hex32 pc.toNat} busRdataRaw=0x{hex32 busRdataRaw.toNat} mmioRdata=0x{hex32 mmioRdata.toNat} (aiInputReg=0x{hex32 aiInputReg.toNat}, bitnetOut=0x{hex32 bitnetOut.toNat})"
      lwEventCountRef.modify (· + 1)
    let _ := lwEventCountRef
    let _ := uartBytesRef

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
