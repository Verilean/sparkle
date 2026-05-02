/-
  JIT Linux Boot Test — OpenSBI + Linux 6.6 on Sparkle RV32IMA SoC

  Loads OpenSBI fw_jump.bin + DTB + Linux kernel Image into DRAM via JIT,
  boots with timer-compare oracle, and monitors UART text output.

  Prerequisites:
    cd firmware/opensbi && bash setup.sh

  Usage:
    lake exe rv32-jit-linux-boot-test [jit.cpp] [max_cycles]
-/

import Sparkle.Core.JIT
import Sparkle.Core.JITLoop
import Sparkle.Core.Oracle
import Sparkle.Utils.HexLoader
import IP.RV32.SoC
import IP.RV32.JITDebug

set_option maxRecDepth 4096

open Sparkle.Core.JIT
open Sparkle.Core.JITLoop
open Sparkle.Core.Oracle
open Sparkle.Utils.HexLoader
open Sparkle.IP.RV32.SoC

def toHex32 (v : Nat) : String :=
  let hexStr := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (8 - hexStr.length) '0') ++ hexStr

def main (args : List String) : IO UInt32 := do
  let cppPath := args[0]? |>.getD "verilator/generated_soc_jit.cpp"
  let maxCycles := (args[1]? >>= String.toNat?).getD 100_000_000

  -- Firmware paths (configurable via env vars)
  let bootHex ← do
    match ← IO.getEnv "SPARKLE_BOOT_HEX" with
    | some p => pure p
    | none   => pure "firmware/opensbi/boot.hex"
  let opensbiPath ← do
    match ← IO.getEnv "SPARKLE_OPENSBI_BIN" with
    | some p => pure p
    | none   => pure "/tmp/opensbi/build/platform/generic/firmware/fw_jump.bin"
  let dtbPath ← do
    match ← IO.getEnv "SPARKLE_DTB" with
    | some p => pure p
    | none   => pure "firmware/opensbi/sparkle-soc.dtb"
  let kernelPath ← do
    match ← IO.getEnv "SPARKLE_KERNEL_IMAGE" with
    | some p => pure p
    | none   => pure "/tmp/linux/arch/riscv/boot/Image"

  IO.println "============================================="
  IO.println "  JIT Linux Boot Test — OpenSBI + Linux 6.6"
  IO.println "============================================="

  -- Check firmware files exist
  for (name, path) in [("boot.hex", bootHex), ("OpenSBI", opensbiPath),
                        ("DTB", dtbPath), ("Linux Image", kernelPath)] do
    unless ← System.FilePath.pathExists path do
      IO.eprintln s!"ERROR: {name} not found at: {path}"
      IO.eprintln "Run: cd firmware/opensbi && bash setup.sh"
      return 1

  -- Compile and load JIT
  IO.println s!"\nCompiling {cppPath}..."
  let handle ← JIT.compileAndLoad cppPath
  IO.println "Loaded JIT module"

  -- Resolve wire indices
  let wireIndices ← JIT.resolveWires handle SoCOutput.wireNames
  IO.println s!"Resolved {wireIndices.size} wire indices"

  -- Load boot.hex into IMEM (memory index 0)
  IO.println s!"\nLoading {bootHex} into IMEM..."
  let firmware ← loadHex bootHex
  let memSize := min firmware.size (1 <<< 12)
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32
  IO.println s!"  {memSize} words loaded into IMEM"

  -- Load OpenSBI fw_jump.bin into DRAM @ 0x80000000 → word addr 0x000000
  IO.println s!"Loading {opensbiPath} into DRAM @ 0x000000..."
  let opensbiWords ← loadBinaryToDRAM handle opensbiPath 0x000000
  IO.println s!"  {opensbiWords} words loaded"

  -- Load Linux kernel into DRAM @ 0x80400000 → word addr 0x100000
  -- DRAM is 8M words (32MB). Kernel at word 0x100000 can use up to 7M words (28MB).
  IO.println s!"Loading {kernelPath} into DRAM @ 0x100000..."
  let kernelBytes ← IO.FS.readBinFile kernelPath
  let kernelTotalWords := (kernelBytes.size + 3) / 4
  let kernelWords ← loadBinaryToDRAM handle kernelPath 0x100000
  IO.println s!"  {kernelWords} words loaded (file: {kernelTotalWords} words, {kernelBytes.size} bytes)"
  if kernelWords < kernelTotalWords then
    IO.println s!"  WARNING: Kernel truncated! {kernelTotalWords - kernelWords} words did not fit in DRAM"

  -- Load DTB into DRAM @ 0x81F00000 → word addr 0x7C0000
  -- MUST be loaded AFTER kernel — kernel at 0x100000 extends to 0x800000 and overlaps DTB region
  IO.println s!"Loading {dtbPath} into DRAM @ 0x7C0000..."
  let dtbWords ← loadBinaryToDRAM handle dtbPath 0x7C0000
  IO.println s!"  {dtbWords} words loaded"

  -- Verify DRAM loading by reading back first 8 words from ifetch byte lanes
  IO.println "\n--- Memory Readback Verification ---"
  IO.println "First 8 words from DRAM ifetch byte lanes (should match OpenSBI entry):"
  let opensbiBytes ← IO.FS.readBinFile opensbiPath
  for i in [:8] do
    let b0 ← JIT.getMem handle 7  i.toUInt32
    let b1 ← JIT.getMem handle 8  i.toUInt32
    let b2 ← JIT.getMem handle 9  i.toUInt32
    let b3 ← JIT.getMem handle 10 i.toUInt32
    let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
    -- Compare with actual file bytes
    let fb0 := if h : 4*i < opensbiBytes.size then opensbiBytes[4*i].toNat else 0
    let fb1 := if h : 4*i+1 < opensbiBytes.size then opensbiBytes[4*i+1].toNat else 0
    let fb2 := if h : 4*i+2 < opensbiBytes.size then opensbiBytes[4*i+2].toNat else 0
    let fb3 := if h : 4*i+3 < opensbiBytes.size then opensbiBytes[4*i+3].toNat else 0
    let fileWord := (fb3 <<< 24) ||| (fb2 <<< 16) ||| (fb1 <<< 8) ||| fb0
    let match_ := if word == fileWord then "OK" else "MISMATCH"
    IO.println s!"  word[{i}]: ifetch=0x{toHex32 word} file=0x{toHex32 fileWord} {match_}"

  IO.println "\nFirst 8 words from DRAM data byte lanes:"
  for i in [:8] do
    let b0 ← JIT.getMem handle 1 i.toUInt32
    let b1 ← JIT.getMem handle 2 i.toUInt32
    let b2 ← JIT.getMem handle 3 i.toUInt32
    let b3 ← JIT.getMem handle 4 i.toUInt32
    let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
    IO.println s!"  word[{i}]: data=0x{toHex32 word}"

  -- Verify DTB at word address 0x7C0000
  IO.println "\nFirst 4 words from DTB region (DRAM data @ 0x7C0000, should match DTB header):"
  let dtbBytes ← IO.FS.readBinFile dtbPath
  for i in [:4] do
    let addr := (0x7C0000 + i).toUInt32
    let b0 ← JIT.getMem handle 1 addr
    let b1 ← JIT.getMem handle 2 addr
    let b2 ← JIT.getMem handle 3 addr
    let b3 ← JIT.getMem handle 4 addr
    let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
    let fb0 := if h : 4*i < dtbBytes.size then dtbBytes[4*i].toNat else 0
    let fb1 := if h : 4*i+1 < dtbBytes.size then dtbBytes[4*i+1].toNat else 0
    let fb2 := if h : 4*i+2 < dtbBytes.size then dtbBytes[4*i+2].toNat else 0
    let fb3 := if h : 4*i+3 < dtbBytes.size then dtbBytes[4*i+3].toNat else 0
    let fileWord := (fb3 <<< 24) ||| (fb2 <<< 16) ||| (fb1 <<< 8) ||| fb0
    let match_ := if word == fileWord then "OK" else "MISMATCH"
    IO.println s!"  dtb[{i}]: data=0x{toHex32 word} file=0x{toHex32 fileWord} {match_}"

  IO.println "\nFirst 4 words from IMEM:"
  for i in [:4] do
    let word ← JIT.getMem handle 0 i.toUInt32
    IO.println s!"  imem[{i}]: 0x{toHex32 word.toNat}"

  let uartBytesRef ← IO.mkRef (#[] : Array UInt8)
  let uartLineRef ← IO.mkRef ("" : String)
  -- Trap / SATP / PTW tracer (matches Verilator tb_soc.cpp visibility).
  -- Default ON because debugging silent boots is the common case; set
  -- SPARKLE_TRACE=0 to skip per-cycle observation entirely (~2x faster).
  let traceRef ← Sparkle.IP.RV32.JITDebug.mkTracer
  let traceEnabled := (← IO.getEnv "SPARKLE_TRACE").getD "1" != "0"
  let verbosePTW := (← IO.getEnv "SPARKLE_TRACE_PTW").isSome
  -- PC ring: record last 200 PCs while we're inside early_init_dt_verify
  -- (0xc0823200..0xc0823300). This range covers the 'B' ecall through the
  -- function epilogue and enough slop for the failure-branch PC at 0xc082325c.
  Sparkle.IP.RV32.JITDebug.setPCWindow traceRef 0xc0002430 0xc0002600 1000

  -- Per-cycle wire snapshots while PC is in the danger zone (verify body).
  -- Resolve the new wire indices for direct getWire access.
  -- Shadow wires only available in patched JIT cpp (see linux-patches/jit-shadow-wires.diff).
  -- Skip if they aren't there (after JIT regen the shadows get dropped).
  IO.println "About to call resolveWires for extra shadows..."
  let wireExtraIndices : Array UInt32 ←
    try
      JIT.resolveWires handle
        #["_shadow_idex_pc", "_shadow_stall", "_shadow_squash",
          "_shadow_ifetchStall", "_shadow_alu_result",
          "_shadow_idex_regWrite", "_shadow_idex_rd", "_gen_exwb_rd",
          "_shadow_dmem_we", "_shadow_dmem_write_addr",
          "_shadow_effectiveAddr_ex",
          "_shadow_fetchPC", "_shadow_ifid_pc", "_shadow_ifid_inst",
          "_shadow_stallDelay", "_shadow_freezeIDEX", "_shadow_pcReg",
          "_shadow_mmuState", "_shadow_ptwState", "_shadow_dTLBMiss",
          "_shadow_anyTLBHit", "_shadow_isMMUFault",
          "_shadow_dMissPC", "_shadow_dMissVaddr", "_shadow_dMissIsStore",
          "_shadow_pendingWriteEn", "_shadow_exwb_isAMO",
          "_shadow_idex_isAMO", "_shadow_exwb_isAMOrw",
          "_shadow_dmem_rdata", "_shadow_dmem_read_addr",
          "_shadow_tlb0VPN", "_shadow_tlb0PPN", "_shadow_tlb0Valid", "_shadow_tlb0Mega",
          "_shadow_tlb1VPN", "_shadow_tlb1PPN", "_shadow_tlb1Valid", "_shadow_tlb1Mega",
          "_shadow_tlb2VPN", "_shadow_tlb2PPN", "_shadow_tlb2Valid", "_shadow_tlb2Mega",
          "_shadow_tlb3VPN", "_shadow_tlb3PPN", "_shadow_tlb3Valid", "_shadow_tlb3Mega",
          "_shadow_dmem_write_data"]
    catch e =>
      IO.println s!"resolveWires extra failed: {e.toString}"
      pure (#[] : Array UInt32)
  IO.println s!"Resolved {wireExtraIndices.size} extra wire indices (incl MMU)"
  let snapCounterRef : IO.Ref Nat ← IO.mkRef 0
  let hasShadows := wireExtraIndices.size > 0
  -- Monitor sp register across cycles. Print when sp changes.
  let lastSpRef : IO.Ref UInt32 ← IO.mkRef 0
  let spChangeCounterRef : IO.Ref Nat ← IO.mkRef 0

  -- Create boot oracle with timer-compare skipping
  let config : SelfLoopConfig := {
    threshold := 200
    skipAmount := 1000
    pcWireArrayIdx := 0
    mtimeLoRegIdx := 54
    mtimeHiRegIdx := 55
    mtimecmpLoRegIdx := 56
    mtimecmpHiRegIdx := 57
    skipToTimerCompare := true
    maxSkip := 10_000_000
    pcTolerance := 8
  }
  let (oracle, oracleStateRef) ← mkSelfLoopOracle config

  -- The self-loop oracle uses threshold=50, so only loops executing the same PC
  -- for 50+ consecutive cycles get skipped.  OpenSBI's productive init loops have
  -- varying PCs and won't trigger.  The WFI idle loop is the target for skipping.
  IO.println s!"\nOracle active from cycle 0 (threshold={config.threshold}, maxSkip={config.maxSkip})"

  -- Early-cycle PC trace (first 20 cycles)
  IO.println "\n--- Early-Cycle PC Trace ---"
  let earlyTraceRef ← IO.mkRef (#[] : Array (Nat × Nat))
  let _traceRun ← JIT.runOptimized handle 20 wireIndices
    (fun _ _ _ => pure none)
    fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      let trace ← earlyTraceRef.get
      earlyTraceRef.set (trace.push (cycle, out.pc.toNat))
      return true
  let earlyTrace ← earlyTraceRef.get
  for (c, pc) in earlyTrace do
    IO.println s!"  cycle {c}: PC=0x{toHex32 pc}"

  -- Reset JIT for main run (reload memories)
  JIT.reset handle
  for i in [:memSize] do
    let word := if h : i < firmware.size then firmware[i] else 0#32
    JIT.setMem handle 0 i.toUInt32 word.toNat.toUInt32
  let _opensbiWords2 ← loadBinaryToDRAM handle opensbiPath 0x000000
  let _kernelWords2 ← loadBinaryToDRAM handle kernelPath 0x100000
  let _dtbWords2 ← loadBinaryToDRAM handle dtbPath 0x7C0000

  -- Run simulation
  IO.println s!"\nRunning JIT Linux boot for {maxCycles} cycles...\n"
  let startTime ← IO.monoNanosNow

  let actualCycles ← JIT.runOptimized handle maxCycles wireIndices oracle
    fun cycle vals => do
      let out := SoCOutput.fromWireValues vals
      -- Verilator-equivalent trap/SATP/(optional)PTW logging.
      if traceEnabled then
        Sparkle.IP.RV32.JITDebug.observe traceRef cycle out (verbose := verbosePTW)
      -- Track every kernel-mode store to swapper_pg_dir entries
      -- (PA 0x81ca2000 + N*4 = word 0x728800 + N).  PT is 1024 entries
      -- so word range = 0x728800..0x728c00.
      if hasShadows then
        let we ← JIT.getWire handle wireExtraIndices[8]!
        let waddr ← JIT.getWire handle wireExtraIndices[9]!
        let waddrN := waddr.toNat
        let pcN := out.pc.toNat
        if we.toNat == 1 && waddrN >= 0x728800 && waddrN < 0x728c00 && pcN >= 0xc0000000 then
          IO.println s!"PGD-WRITE c={cycle} PC=0x{toHex32 pcN} wordAddr=0x{toHex32 waddrN} (entry [{(waddrN - 0x728800)}])"

      -- Trace __of_device_is_compatible entry: print a1 at idexPc=c0471ebc
      if hasShadows && wireExtraIndices.size >= 31 then
        let pcN := out.pc.toNat
        let idexPcN ← (do let v ← JIT.getWire handle wireExtraIndices[0]!; pure v.toNat)
        if idexPcN == 0xc0471ebc then
          let a1 ← JIT.getMem handle 5 11
          let s3' ← JIT.getMem handle 5 19
          IO.println s!"DICX c={cycle} idexPc=0x{toHex32 idexPcN} a1=0x{toHex32 a1.toNat} s3=0x{toHex32 s3'.toNat}"
        if pcN == 0xc0471ebc then
          let a1 ← JIT.getMem handle 5 11
          let s3 ← JIT.getMem handle 5 19
          let ra ← JIT.getMem handle 5 1
          let sp ← JIT.getMem handle 5 2
          IO.println s!"DIC c={cycle} PC=0x{toHex32 pcN} a1=0x{toHex32 a1.toNat} s3=0x{toHex32 s3.toNat} ra=0x{toHex32 ra.toNat} sp=0x{toHex32 sp.toNat}"
        -- Trace strcasecmp entry to capture s3 of caller
        if pcN == 0xc04a27ec then
          let a0 ← JIT.getMem handle 5 10
          let a1 ← JIT.getMem handle 5 11
          let s3 ← JIT.getMem handle 5 19
          let ra ← JIT.getMem handle 5 1
          let sp ← JIT.getMem handle 5 2
          IO.println s!"SCC c={cycle} a0=0x{toHex32 a0.toNat} a1=0x{toHex32 a1.toNat} s3=0x{toHex32 s3.toNat} ra=0x{toHex32 ra.toNat} sp=0x{toHex32 sp.toNat}"
        -- Dump TLB at the cycle where wrong PA was returned
        if cycle == 9149025 then
          let t0V ← JIT.getWire handle wireExtraIndices[31]!
          let t0P ← JIT.getWire handle wireExtraIndices[32]!
          let t0Vd ← JIT.getWire handle wireExtraIndices[33]!
          let t0M ← JIT.getWire handle wireExtraIndices[34]!
          let t1V ← JIT.getWire handle wireExtraIndices[35]!
          let t1P ← JIT.getWire handle wireExtraIndices[36]!
          let t1Vd ← JIT.getWire handle wireExtraIndices[37]!
          let t1M ← JIT.getWire handle wireExtraIndices[38]!
          let t2V ← JIT.getWire handle wireExtraIndices[39]!
          let t2P ← JIT.getWire handle wireExtraIndices[40]!
          let t2Vd ← JIT.getWire handle wireExtraIndices[41]!
          let t2M ← JIT.getWire handle wireExtraIndices[42]!
          let t3V ← JIT.getWire handle wireExtraIndices[43]!
          let t3P ← JIT.getWire handle wireExtraIndices[44]!
          let t3Vd ← JIT.getWire handle wireExtraIndices[45]!
          let t3M ← JIT.getWire handle wireExtraIndices[46]!
          IO.println s!"TLB c={cycle}"
          IO.println s!"  T0 V={t0Vd.toNat} M={t0M.toNat} VPN=0x{toHex32 t0V.toNat} PPN=0x{toHex32 t0P.toNat}"
          IO.println s!"  T1 V={t1Vd.toNat} M={t1M.toNat} VPN=0x{toHex32 t1V.toNat} PPN=0x{toHex32 t1P.toNat}"
          IO.println s!"  T2 V={t2Vd.toNat} M={t2M.toNat} VPN=0x{toHex32 t2V.toNat} PPN=0x{toHex32 t2P.toNat}"
          IO.println s!"  T3 V={t3Vd.toNat} M={t3M.toNat} VPN=0x{toHex32 t3V.toNat} PPN=0x{toHex32 t3P.toNat}"

        -- Trace lw ra at riscv_get_intc_hwnode epilogue (PC c00026bc)
        if cycle >= 9149015 && cycle <= 9149040 then
          let idexPcA ← JIT.getWire handle wireExtraIndices[0]!
          let aluA ← JIT.getWire handle wireExtraIndices[4]!
          let dmemRdataA ← JIT.getWire handle wireExtraIndices[29]!
          let dmemRaddrA ← JIT.getWire handle wireExtraIndices[30]!
          let raPaA := 0x80000000 + (dmemRaddrA.toNat <<< 2)
          let ra' ← JIT.getMem handle 5 1
          let mmuSt ← JIT.getWire handle wireExtraIndices[17]!
          let ptwSt ← JIT.getWire handle wireExtraIndices[18]!
          let dMiss ← JIT.getWire handle wireExtraIndices[19]!
          let tHit ← JIT.getWire handle wireExtraIndices[20]!
          IO.println s!"L c={cycle} idexPc=0x{toHex32 idexPcA.toNat} alu=0x{toHex32 aluA.toNat} rAddr=0x{toHex32 raPaA} rdata=0x{toHex32 dmemRdataA.toNat} mmu={mmuSt.toNat} ptw={ptwSt.toNat} dMiss={dMiss.toNat} tHit={tHit.toNat}"
        if cycle >= 9148960 && cycle <= 9148990 then
          let s3 ← JIT.getMem handle 5 19
          let idexPc2 ← JIT.getWire handle wireExtraIndices[0]!
          let pc2 := out.pc.toNat
          let alu ← JIT.getWire handle wireExtraIndices[4]!
          let dmemRdata ← JIT.getWire handle wireExtraIndices[29]!
          let dmemRaddr ← JIT.getWire handle wireExtraIndices[30]!
          let raPaN := 0x80000000 + (dmemRaddr.toNat <<< 2)
          IO.println s!"FULL c={cycle} PC=0x{toHex32 pc2} idexPc=0x{toHex32 idexPc2.toNat} alu=0x{toHex32 alu.toNat} rAddr=0x{toHex32 raPaN} rdata=0x{toHex32 dmemRdata.toNat} s3=0x{toHex32 s3.toNat}"

        -- Watch every store of value 0xfffffdfb anywhere
        let dmemWeS ← JIT.getWire handle wireExtraIndices[8]!
        if dmemWeS.toNat == 1 then
          let aluS ← JIT.getWire handle wireExtraIndices[4]!
          let dmemAddrS ← JIT.getWire handle wireExtraIndices[9]!
          let waddrNS := dmemAddrS.toNat
          -- The store data isn't directly shadow; check via heuristic on rs2 (rs2_byte0..3 not shadow either)
          -- So we filter on store target PA = 0x809e7e7c (= where 0xfffffdfb appeared)
          let paS := 0x80000000 + (waddrNS <<< 2)
          if paS == 0x809e7e7c || paS == 0x809e7e8c || paS == 0x805e7e8c then
            let idexPcS ← JIT.getWire handle wireExtraIndices[0]!
            let wdataS ← JIT.getWire handle wireExtraIndices[47]!
            IO.println s!"STORE_TARGET c={cycle} idexPc=0x{toHex32 idexPcS.toNat} alu=0x{toHex32 aluS.toNat} PA=0x{toHex32 paS} data=0x{toHex32 wdataS.toNat}"

        -- Dump TLB state at the faulting cycle (around 9149123)
        if cycle == 9149123 then
          let t0V ← JIT.getWire handle wireExtraIndices[31]!
          let t0P ← JIT.getWire handle wireExtraIndices[32]!
          let t0Vd ← JIT.getWire handle wireExtraIndices[33]!
          let t0M ← JIT.getWire handle wireExtraIndices[34]!
          let t1V ← JIT.getWire handle wireExtraIndices[35]!
          let t1P ← JIT.getWire handle wireExtraIndices[36]!
          let t1Vd ← JIT.getWire handle wireExtraIndices[37]!
          let t1M ← JIT.getWire handle wireExtraIndices[38]!
          let t2V ← JIT.getWire handle wireExtraIndices[39]!
          let t2P ← JIT.getWire handle wireExtraIndices[40]!
          let t2Vd ← JIT.getWire handle wireExtraIndices[41]!
          let t2M ← JIT.getWire handle wireExtraIndices[42]!
          let t3V ← JIT.getWire handle wireExtraIndices[43]!
          let t3P ← JIT.getWire handle wireExtraIndices[44]!
          let t3Vd ← JIT.getWire handle wireExtraIndices[45]!
          let t3M ← JIT.getWire handle wireExtraIndices[46]!
          IO.println s!"TLB c={cycle}"
          IO.println s!"  T0 V={t0Vd.toNat} M={t0M.toNat} VPN=0x{toHex32 t0V.toNat} PPN=0x{toHex32 t0P.toNat}"
          IO.println s!"  T1 V={t1Vd.toNat} M={t1M.toNat} VPN=0x{toHex32 t1V.toNat} PPN=0x{toHex32 t1P.toNat}"
          IO.println s!"  T2 V={t2Vd.toNat} M={t2M.toNat} VPN=0x{toHex32 t2V.toNat} PPN=0x{toHex32 t2P.toNat}"
          IO.println s!"  T3 V={t3Vd.toNat} M={t3M.toNat} VPN=0x{toHex32 t3V.toNat} PPN=0x{toHex32 t3P.toNat}"
        -- Trace the cycles right before the fault with everything
        if cycle >= 9148950 && cycle < 9149150 then
          let dmemWe ← JIT.getWire handle wireExtraIndices[8]!
          let pwe ← JIT.getWire handle wireExtraIndices[25]!
          let dmemAddr ← JIT.getWire handle wireExtraIndices[9]!
          let waddrN := dmemAddr.toNat
          let alu ← JIT.getWire handle wireExtraIndices[4]!
          let idexPc ← JIT.getWire handle wireExtraIndices[0]!
          let dmemRdata ← JIT.getWire handle wireExtraIndices[29]!
          let dmemRaddr ← JIT.getWire handle wireExtraIndices[30]!
          let paN := 0x80000000 + (waddrN <<< 2)
          let raPaN := 0x80000000 + (dmemRaddr.toNat <<< 2)
          IO.println s!"X c={cycle} idexPc=0x{toHex32 idexPc.toNat} alu=0x{toHex32 alu.toNat} we={dmemWe.toNat} pwe={pwe.toNat} wAddr=0x{toHex32 paN} rAddr=0x{toHex32 raPaN} rdata=0x{toHex32 dmemRdata.toNat}"

      -- AMO bug diagnostics around raw_amoadd in __free_pages_core (use idex_pc)
      if false && hasShadows && wireExtraIndices.size >= 29 then
        let idexPcRaw ← JIT.getWire handle wireExtraIndices[0]!
        let idexPcN := idexPcRaw.toNat
        if idexPcN >= 0xc0172500 && idexPcN <= 0xc0172900 then
          let pcN := out.pc.toNat
          let alu ← JIT.getWire handle wireExtraIndices[4]!
          let stl ← JIT.getWire handle wireExtraIndices[1]!
          let sq ← JIT.getWire handle wireExtraIndices[2]!
          let dmemWe ← JIT.getWire handle wireExtraIndices[8]!
          let dmemAddr ← JIT.getWire handle wireExtraIndices[9]!
          let effA ← JIT.getWire handle wireExtraIndices[10]!
          let pwe ← JIT.getWire handle wireExtraIndices[25]!
          let exAMO ← JIT.getWire handle wireExtraIndices[26]!
          let idAMO ← JIT.getWire handle wireExtraIndices[27]!
          let exAMOrw ← JIT.getWire handle wireExtraIndices[28]!
          IO.println s!"AMO c={cycle} PC=0x{toHex32 pcN} idexPc=0x{toHex32 idexPcN} alu=0x{toHex32 alu.toNat} st={stl.toNat} sq={sq.toNat} dmemWe={dmemWe.toNat} dmemAddr=0x{toHex32 dmemAddr.toNat} effA=0x{toHex32 effA.toNat} pwe={pwe.toNat} exAMO={exAMO.toNat} idAMO={idAMO.toNat} exAMOrw={exAMOrw.toNat}"

      -- MMU diagnostics around paging_init store fault (legacy)
      if false && hasShadows && wireExtraIndices.size >= 25 then
        let pcN := out.pc.toNat
        if pcN >= 0xc08049a0 && pcN <= 0xc08049d0 then
          let mmuSt ← JIT.getWire handle wireExtraIndices[17]!
          let ptwSt ← JIT.getWire handle wireExtraIndices[18]!
          let dMiss ← JIT.getWire handle wireExtraIndices[19]!
          let tHit ← JIT.getWire handle wireExtraIndices[20]!
          let mmuF ← JIT.getWire handle wireExtraIndices[21]!
          let dmPC ← JIT.getWire handle wireExtraIndices[22]!
          let dmVA ← JIT.getWire handle wireExtraIndices[23]!
          let dmIS ← JIT.getWire handle wireExtraIndices[24]!
          let alu ← JIT.getWire handle wireExtraIndices[4]!
          let idexPc ← JIT.getWire handle wireExtraIndices[0]!
          let stl ← JIT.getWire handle wireExtraIndices[1]!
          let sq ← JIT.getWire handle wireExtraIndices[2]!
          IO.println s!"MMU c={cycle} PC=0x{toHex32 pcN} idexPc=0x{toHex32 idexPc.toNat} alu=0x{toHex32 alu.toNat} st={stl.toNat} sq={sq.toNat} mmuSt={mmuSt.toNat} ptwSt={ptwSt.toNat} dMiss={dMiss.toNat} tHit={tHit.toNat} mmuF={mmuF.toNat} dmPC=0x{toHex32 dmPC.toNat} dmVA=0x{toHex32 dmVA.toNat} dmIS={dmIS.toNat}"

      if hasShadows then
        let spNow ← JIT.getMem handle 5 2
        -- Look at strcmp body (c04b3c54-c04b3c70) when called from
        -- early_init_dt_scan_memory to compare type=="memory".
        let pcN := out.pc.toNat
        if pcN >= 0xc04b3c50 && pcN < 0xc04b3c80 then
          let idexPc ← JIT.getWire handle wireExtraIndices[0]!
          let stall ← JIT.getWire handle wireExtraIndices[1]!
          let squash ← JIT.getWire handle wireExtraIndices[2]!
          let ifs ← JIT.getWire handle wireExtraIndices[3]!
          let alu ← JIT.getWire handle wireExtraIndices[4]!
          let idexRegW ← JIT.getWire handle wireExtraIndices[5]!
          let idexRd ← JIT.getWire handle wireExtraIndices[6]!
          let exwbRd ← JIT.getWire handle wireExtraIndices[7]!
          let fetchPCv ← JIT.getWire handle wireExtraIndices[11]!
          let ifidPcV ← JIT.getWire handle wireExtraIndices[12]!
          let ifidInstV ← JIT.getWire handle wireExtraIndices[13]!
          let stDly ← JIT.getWire handle wireExtraIndices[14]!
          let frzIDEX ← JIT.getWire handle wireExtraIndices[15]!
          let pcRegV ← JIT.getWire handle wireExtraIndices[16]!
          IO.println s!"CYC c={cycle} PC=0x{toHex32 out.pc.toNat} pcReg=0x{toHex32 pcRegV.toNat} fetchPC=0x{toHex32 fetchPCv.toNat} ifidPc=0x{toHex32 ifidPcV.toNat} ifidInst=0x{toHex32 ifidInstV.toNat} idexPc=0x{toHex32 idexPc.toNat} st={stall.toNat} sd={stDly.toNat} sq={squash.toNat} fz={frzIDEX.toNat} ifs={ifs.toNat} alu=0x{toHex32 alu.toNat} idexRW={idexRegW.toNat} idexRd={idexRd.toNat} exwbRd={exwbRd.toNat} sp=0x{toHex32 spNow.toNat}"
          lastSpRef.set spNow

      -- Snapshot wires when PC is in the trap handler. Record FIRST 600
      -- snapshots only — these are the earliest traps which haven't been
      -- corrupted yet, so we can see where sp first goes wrong.
      let pcN := out.pc.toNat
      if hasShadows && ((pcN >= 0xc0002430 && pcN < 0xc0002600) || (pcN >= 0xc0823200 && pcN < 0xc0823350)) then
        let nSoFar ← snapCounterRef.get
        if nSoFar < 2000 then
          let ex ← JIT.getWire handle wireExtraIndices[0]!
          let pa ← JIT.getWire handle wireExtraIndices[1]!
          let en ← JIT.getWire handle wireExtraIndices[2]!
          let br ← JIT.getWire handle wireExtraIndices[3]!
          let dr ← JIT.getWire handle wireExtraIndices[4]!
          let da ← JIT.getWire handle wireExtraIndices[5]!
          let ea ← JIT.getWire handle wireExtraIndices[6]!
          let pd ← JIT.getWire handle wireExtraIndices[7]!
          let wr ← JIT.getWire handle wireExtraIndices[8]!
          let we ← JIT.getWire handle wireExtraIndices[9]!
          let rd ← JIT.getWire handle wireExtraIndices[10]!
          let sp_rf ← JIT.getMem handle 5 2  -- rf_rs1_raw[x2 = sp]
          let s2_rf ← JIT.getMem handle 5 18 -- rf_rs1_raw[x18 = s2]
          IO.println s!"WIRE c={cycle} PC=0x{toHex32 pcN} ex=0x{toHex32 ex.toNat} pE={en.toNat} bR=0x{toHex32 br.toNat} dR=0x{toHex32 dr.toNat} eA=0x{toHex32 ea.toNat} pD=0x{toHex32 pd.toNat} wbR=0x{toHex32 wr.toNat} wbE={we.toNat} rd={rd.toNat} sp=0x{toHex32 sp_rf.toNat} s2=0x{toHex32 s2_rf.toNat}"
          snapCounterRef.set (nSoFar + 1)
      if out.uartValid then
        let byte := (out.uartData.toNat % 256).toUInt8
        let bytes ← uartBytesRef.get
        uartBytesRef.set (bytes.push byte)
        -- Accumulate line, print on newline
        let ch := Char.ofNat byte.toNat
        if ch == '\n' then
          let line ← uartLineRef.get
          IO.println line
          uartLineRef.set ""
        else
          let line ← uartLineRef.get
          uartLineRef.set (line.push ch)
      -- Periodically report PC for progress
      if cycle < 1_000_000 then
        if cycle % 100_000 == 0 then
          IO.println s!"  [cycle {cycle}] PC=0x{toHex32 out.pc.toNat}"
          -- Print timer state at 100K for diagnostics
          if cycle == 100_000 then
            let mtimeLo ← JIT.getReg handle 54
            let mtimeHi ← JIT.getReg handle 55
            let mtimecmpLo ← JIT.getReg handle 56
            let mtimecmpHi ← JIT.getReg handle 57
            let mstatusReg ← JIT.getReg handle 58
            let mieReg ← JIT.getReg handle 59
            IO.println s!"    mtime=0x{toHex32 mtimeHi.toNat}{toHex32 mtimeLo.toNat}"
            IO.println s!"    mtimecmp=0x{toHex32 mtimecmpHi.toNat}{toHex32 mtimecmpLo.toNat}"
            IO.println s!"    mstatus=0x{toHex32 mstatusReg.toNat} mie=0x{toHex32 mieReg.toNat}"
      else if cycle % 1_000_000 == 0 then
        IO.println s!"  [cycle {cycle}] PC=0x{toHex32 out.pc.toNat}"
        -- Print timer state at 3M, 5M, 10M for post-kernel diagnostics
        if cycle == 3_000_000 || cycle == 5_000_000 || cycle == 10_000_000 then
          let mtimeLo ← JIT.getReg handle 54
          let mtimeHi ← JIT.getReg handle 55
          let mtimecmpLo ← JIT.getReg handle 56
          let mtimecmpHi ← JIT.getReg handle 57
          let mstatusReg ← JIT.getReg handle 58
          let mieReg ← JIT.getReg handle 59
          IO.println s!"    mtime=0x{toHex32 mtimeHi.toNat}{toHex32 mtimeLo.toNat}"
          IO.println s!"    mtimecmp=0x{toHex32 mtimecmpHi.toNat}{toHex32 mtimecmpLo.toNat}"
          IO.println s!"    mstatus=0x{toHex32 mstatusReg.toNat} mie=0x{toHex32 mieReg.toNat}"
      return true

  let endTime ← IO.monoNanosNow
  let elapsed_ms := (endTime - startTime) / 1_000_000

  -- Flush any remaining partial line
  let remainingLine ← uartLineRef.get
  if !remainingLine.isEmpty then
    IO.println remainingLine

  -- Gather results
  let uartBytes ← uartBytesRef.get
  let oracleState ← oracleStateRef.get

  -- Report
  IO.println "\n============================================="
  IO.println "  JIT Linux Boot Results"
  IO.println "============================================="
  IO.println s!"  Cycles executed:   {actualCycles}"
  IO.println s!"  Oracle triggers:   {oracleState.triggerCount}"
  IO.println s!"  Total skipped:     {oracleState.totalSkipped}"
  IO.println s!"  UART bytes:        {uartBytes.size}"
  -- Dump full UART byte stream as a single string for non-newline traces.
  let raw := String.mk (uartBytes.toList.map fun b => Char.ofNat b.toNat)
  IO.println s!"  UART raw stream: ===8<==="
  IO.println raw
  IO.println "  ===8<==="
  -- Last 32 bytes as hex (so we can see what '?' really is)
  IO.println "  Last UART bytes (hex):"
  let n := uartBytes.size
  let start := if n > 32 then n - 32 else 0
  for i in [start:n] do
    let b := uartBytes[i]!.toNat
    let hi := b >>> 4
    let lo := b &&& 0xF
    let hexCh (v : Nat) : Char :=
      if v < 10 then Char.ofNat (48 + v) else Char.ofNat (97 + v - 10)
    IO.print s!" {hexCh hi}{hexCh lo}"
  IO.println ""
  IO.println s!"  Wall-clock time:   {elapsed_ms} ms"
  if elapsed_ms > 0 then
    let effectiveCycPerSec := actualCycles * 1000 / elapsed_ms
    IO.println s!"  Effective cyc/s:   {effectiveCycPerSec}"

  -- Dump active page tables on exit. We dump:
  --   * the trampoline_pg_dir (first SATP value seen, at PA 0x81ca9000
  --     in our build) — this is what was active during the very first
  --     instruction-page-fault, so it's the most diagnostic
  --   * the swapper_pg_dir (final SATP value) — what's active at exit
  if traceEnabled then
    let finalVals ← wireIndices.mapM fun idx => JIT.getWire handle idx
    let finalOut := SoCOutput.fromWireValues finalVals
    let satp := finalOut.satp.toNat
    let mode := (satp >>> 31) &&& 1
    let ppn  := satp &&& 0x3FFFFF
    let ptPA := ppn <<< 12
    IO.println s!"\nFinal SATP = 0x{Sparkle.IP.RV32.JITDebug.hex32 satp} \
                 (mode={mode} PPN=0x{Sparkle.IP.RV32.JITDebug.hex32 ppn} \
                 → PT base PA = 0x{Sparkle.IP.RV32.JITDebug.hex32 ptPA})"
    if mode == 1 then
      Sparkle.IP.RV32.JITDebug.dumpPageTable handle ptPA "swapper_pg_dir (final)"
    -- Trampoline PT — typically at 0x81ca9000 for our build, but allow
    -- override via env var in case the kernel layout shifts.
    let trampPA := match (← IO.getEnv "SPARKLE_TRAMP_PT").bind String.toNat? with
      | some n => n
      | none   => 0x81ca9000
    Sparkle.IP.RV32.JITDebug.dumpPageTable handle trampPA "trampoline_pg_dir (early boot)"

    -- Dump the PC ring buffer for early_init_dt_verify.
    Sparkle.IP.RV32.JITDebug.dumpPCRing traceRef
    let totalSnaps ← snapCounterRef.get
    IO.println s!"\n=== Wire snapshots: {totalSnaps} (printed inline above with WIRE prefix) ==="
    -- Dump "memory" string at PA 0x814b3974 (word 0x52ce5d)
    IO.println "\n=== \"memory\" string at PA 0x814b3974 ==="
    for i in [:3] do
      let waddr := (0x52ce5d + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +{i*4}: 0x{toHex32 word} '{Char.ofNat b0.toNat}{Char.ofNat b1.toNat}{Char.ofNat b2.toNat}{Char.ofNat b3.toNat}'"
    -- Dump struct memblock (PA 0x81004980, word 0x401260, ~40 bytes)
    IO.println "\n=== memblock @ PA 0x81004980 (40 bytes) ==="
    for i in [:10] do
      let waddr := (0x401260 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word}"
    -- Dump first 4 entries of memblock_memory_init_regions (PA 0x810049c4, word 0x401271, 4*12=48 bytes)
    IO.println "\n=== memblock_memory_init_regions[0..3] (4 regions × 12 bytes) ==="
    for i in [:12] do
      let waddr := (0x401271 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      let region := i / 3
      let field := match i % 3 with | 0 => "base" | 1 => "size" | _ => "flags"
      IO.println s!"  region[{region}].{field}: 0x{toHex32 word}"
    -- Dump swapper_pg_dir entries [768]-[775] to see the missing [771]
    IO.println "\n=== swapper_pg_dir [768..775] at exit ==="
    for i in [:8] do
      let entry := 768 + i
      -- PA = 0x81ca2000 + entry*4. Word addr = (0x1ca2000 + entry*4) / 4
      --     = 0x728800 + entry
      let waddr := (0x728800 + entry).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  [{entry}]: 0x{toHex32 word}"
    -- Dump verify's stack frame at exit (8 words around sp).
    -- VA c1801eb0 → PA 0x81C01EB0 → word addr (0x1C01EB0 / 4) = 0x7007AC.
    -- Dump __timer_of_table entry 0 (suniv) full struct at PA 0x808f7488
    IO.println "\n=== entry0 of_device_id at PA 0x808f7488 (49 words = 196 bytes) ==="
    for i in [:50] do
      let waddr := (0x023dd22 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      let asAscii := String.mk [Char.ofNat (b0.toNat % 256), Char.ofNat (b1.toNat % 256), Char.ofNat (b2.toNat % 256), Char.ofNat (b3.toNat % 256)]
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word} '{asAscii}'"

    -- Dump __timer_of_table entry 4 compatible field at PA 0x808f77d8 (16 words)
    IO.println "\n=== entry4_compat at PA 0x808f77d8 (16 words / 64 bytes) ==="
    for i in [:16] do
      let waddr := (0x023ddf6 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      let asAscii := String.mk [Char.ofNat (b0.toNat % 256), Char.ofNat (b1.toNat % 256), Char.ofNat (b2.toNat % 256), Char.ofNat (b3.toNat % 256)]
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word} '{asAscii}'"

    -- Dump __timer_of_table sentinel at VA 0xc04f785c → PA 0x808f785c
    IO.println "\n=== __timer_of_table_sentinel at PA 0x808f785c (16 words) ==="
    for i in [:16] do
      let waddr := (0x023de17 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word}"

    IO.println "\n=== DRAM @ PA 0x81C01EB0 (verify stack frame) at exit ==="
    for i in [:8] do
      let waddr := (0x7007AC + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +0x{toHex32 (i*4)} (sp+{i*4}): 0x{toHex32 word}"
    -- Also check translation by reading several PAs around the suspected sp+12 = 0x81C01EBC
    IO.println "\n=== DRAM around PA 0x81C01EBC ==="
    for i in [:4] do
      let waddr := (0x7007AE + i).toUInt32  -- 0x7007AE * 4 = 0x1C01EB8
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      let pa := 0x81C01EB8 + i*4
      IO.println s!"  PA 0x{toHex32 pa}: 0x{toHex32 word}"

    -- Dump first 8 words at PA 0x81f00000 (where DTB was loaded) to see
    -- if it's still intact at exit, vs. having been overwritten.
    IO.println "\n=== DRAM @ PA 0x81f00000 (DTB region) at exit ==="
    for i in [:8] do
      let waddr := (0x7C0000 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word}"
    -- Dump dtb_early_va variable: VA c0c01008 → PA 0x81001008 → word addr 0x400402
    IO.println "\n=== DRAM @ PA 0x81001008 (dtb_early_va) at exit ==="
    for i in [:2] do
      let waddr := (0x400402 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word}"
    -- Dump first 8 words at PA 0x81C07580 (init_task — to inspect task->stack
    -- which is at offset 8). Kernel is loaded at PA 0x80400000 with virt_addr
    -- 0xc0000000, so VA 0xc1807580 → PA 0x80400000 + (0xc1807580 - 0xc0000000)
    --                              = 0x81C07580. Word addr = 0x1C07580/4 = 0x701D60.
    IO.println "\n=== DRAM @ PA 0x81C07580 (init_task) at exit ==="
    for i in [:8] do
      let waddr := (0x701D60 + i).toUInt32
      let b0 ← JIT.getMem handle 1 waddr
      let b1 ← JIT.getMem handle 2 waddr
      let b2 ← JIT.getMem handle 3 waddr
      let b3 ← JIT.getMem handle 4 waddr
      let word := (b3.toNat <<< 24) ||| (b2.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b0.toNat
      IO.println s!"  +0x{toHex32 (i*4)}: 0x{toHex32 word}"

  JIT.destroy handle
  return 0
