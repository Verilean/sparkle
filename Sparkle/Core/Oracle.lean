/-
  Oracle — Self-Loop Detection for JIT Cycle-Skipping

  Detects when the CPU is stuck in a tight loop by monitoring the PC wire
  for N consecutive cycles within a narrow address range. When triggered,
  skips forward by advancing the cycle counter and CLINT timer registers.

  Handles multi-instruction halt loops (e.g., `wfi; j _halt` or similar)
  where the PC cycles through a small set of addresses. The detector
  considers PCs within `pcTolerance` bytes of an anchor PC as "the same"
  for detection purposes.

  Usage:
    let (oracle, stateRef) ← mkSelfLoopOracle config
    let cycles ← JIT.runOptimized handle 10_000_000 wireIndices oracle callback
    let stats ← stateRef.get
    IO.println s!"Skipped {stats.totalSkipped} cycles in {stats.triggerCount} triggers"
-/

import Sparkle.Core.JIT

namespace Sparkle.Core.Oracle

open Sparkle.Core.JIT

/-- Configuration for the self-loop detector -/
structure SelfLoopConfig where
  /-- Cycles of near-same PC before triggering (>34 for divider safety) -/
  threshold : Nat := 50
  /-- Cycles to skip per trigger -/
  skipAmount : Nat := 1000
  /-- Index of PC wire in the wireValues array passed to the oracle -/
  pcWireArrayIdx : Nat := 0
  /-- Max byte distance from anchor PC to consider "same location".
      12 covers loops up to 4 instructions. Sequential execution resets
      every 4 instructions (16 bytes > 12), preventing false triggers. -/
  pcTolerance : UInt64 := 12
  /-- Register index for CLINT mtimeLo (SoCState field 46, offset by 8 divider regs = 54) -/
  mtimeLoRegIdx : UInt32 := 54
  /-- Register index for CLINT mtimeHi (SoCState field 47, offset by 8 divider regs = 55) -/
  mtimeHiRegIdx : UInt32 := 55
  /-- Register index for CLINT mtimecmpLo (SoCState field 48 + 8 divider regs = 56) -/
  mtimecmpLoRegIdx : UInt32 := 56
  /-- Register index for CLINT mtimecmpHi (SoCState field 49 + 8 divider regs = 57) -/
  mtimecmpHiRegIdx : UInt32 := 57
  /-- When true, skip to mtimecmp instead of fixed skipAmount, and reset
      sameCount after each trigger so timer interrupt can fire -/
  skipToTimerCompare : Bool := false
  /-- Maximum cycles to skip per trigger (caps skipToTimerCompare distance) -/
  maxSkip : Nat := 10_000_000

/-- Mutable state for the self-loop detector -/
structure SelfLoopState where
  /-- Anchor PC — the PC at the start of a suspected self-loop -/
  anchorPC : UInt64 := 0xFFFFFFFF_FFFFFFFF
  /-- Count of consecutive cycles with PC near the anchor -/
  sameCount : Nat := 0
  totalSkipped : Nat := 0
  triggerCount : Nat := 0

/-- Create a self-loop detection oracle.
    Returns the oracle function (for `JIT.runOptimized`) and an IORef to
    the internal state (for post-run statistics).

    The oracle monitors the PC wire. When PC stays within `pcTolerance`
    bytes of an anchor PC for `config.threshold` consecutive cycles, it
    skips forward by `config.skipAmount` cycles, advancing the CLINT
    timer to match. The oracle receives the JITHandle per-call and
    handles all state mutations (setReg) internally. -/
def mkSelfLoopOracle (config : SelfLoopConfig)
    : IO ((JITHandle → Nat → Array UInt64 → IO (Option Nat)) × IO.Ref SelfLoopState) := do
  let stateRef ← IO.mkRef ({} : SelfLoopState)

  let oracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) := fun handle _cycle vals => do
    let pc := vals[config.pcWireArrayIdx]?.getD 0
    let st ← stateRef.get

    -- Check if PC is within tolerance of anchor (handles multi-instruction loops)
    let pcDiff := if pc >= st.anchorPC then pc - st.anchorPC else st.anchorPC - pc
    let isNearAnchor := pcDiff <= config.pcTolerance

    if isNearAnchor then
      let newCount := st.sameCount + 1
      if newCount >= config.threshold then
        -- Self-loop detected — skip forward
        -- Read current CLINT timer values
        let oldLo ← JIT.getReg handle config.mtimeLoRegIdx
        let oldHi ← JIT.getReg handle config.mtimeHiRegIdx
        let mtime64 := (oldHi.toNat <<< 32) ||| oldLo.toNat

        -- Compute skip amount
        let skipN ← if config.skipToTimerCompare then do
            let cmpLo ← JIT.getReg handle config.mtimecmpLoRegIdx
            let cmpHi ← JIT.getReg handle config.mtimecmpHiRegIdx
            let mtimecmp64 := (cmpHi.toNat <<< 32) ||| cmpLo.toNat
            if mtimecmp64 > mtime64 then
              pure (min (mtimecmp64 - mtime64) config.maxSkip)
            else
              pure config.skipAmount  -- timer already past compare, use default
          else
            pure config.skipAmount

        -- Advance 64-bit timer split across two 32-bit registers
        let newTime := mtime64 + skipN
        let newLo := (newTime % (2 ^ 32)).toUInt64
        let newHi := (newTime / (2 ^ 32)).toUInt64

        -- Apply timer updates directly
        JIT.setReg handle config.mtimeLoRegIdx newLo
        JIT.setReg handle config.mtimeHiRegIdx newHi

        -- Reset sameCount when skipToTimerCompare so threshold normal
        -- cycles run after skip, allowing timer interrupt to fire
        let newSameCount := if config.skipToTimerCompare then 0 else newCount
        stateRef.set {
          anchorPC := st.anchorPC
          sameCount := newSameCount
          totalSkipped := st.totalSkipped + skipN
          triggerCount := st.triggerCount + 1
        }

        return some skipN
      else
        stateRef.set { st with sameCount := newCount }
        return none
    else
      stateRef.set { st with anchorPC := pc, sameCount := 0 }
      return none

  return (oracle, stateRef)

/-- Create a boot-optimized oracle for Linux boot idle-loop skipping.
    Uses timer-compare-aware skipping with wider PC tolerance (32 bytes).
    Resets sameCount after each trigger so the timer interrupt can fire. -/
def mkBootOracle (config : SelfLoopConfig := {})
    : IO ((JITHandle → Nat → Array UInt64 → IO (Option Nat)) × IO.Ref SelfLoopState) :=
  mkSelfLoopOracle {
    threshold := config.threshold
    skipAmount := config.skipAmount
    pcWireArrayIdx := config.pcWireArrayIdx
    pcTolerance := if config.pcTolerance == 12 then 32 else config.pcTolerance
    mtimeLoRegIdx := config.mtimeLoRegIdx
    mtimeHiRegIdx := config.mtimeHiRegIdx
    mtimecmpLoRegIdx := config.mtimecmpLoRegIdx
    mtimecmpHiRegIdx := config.mtimecmpHiRegIdx
    skipToTimerCompare := true
    maxSkip := config.maxSkip
  }

end Sparkle.Core.Oracle
