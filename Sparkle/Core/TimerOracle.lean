/-
  Timer Oracle — Auto-Generated Cycle Skip from Countdown Timer Detection

  Uses RTL pattern detection (PatternDetect) to find countdown timers,
  then generates a JIT oracle that skips cycles when a timer is counting
  down to zero with no other activity.

  This is "proof-driven" optimization: the countdown pattern guarantees
  that timer_value will reach 0 after exactly N cycles (when enabled),
  so we can safely skip N cycles and set timer_value = 0 directly.

  Combined with the existing SelfLoopOracle (PC-based idle detection),
  this provides two complementary skip mechanisms:
  - SelfLoopOracle: detects CPU idle loops (WFI, halt)
  - TimerOracle: detects timer countdown (skip to timer expiry)
-/

import Sparkle.Core.JIT
import Sparkle.IR.PatternDetect

namespace Sparkle.Core.TimerOracle

open Sparkle.Core.JIT
open Sparkle.IR.PatternDetect

/-- Configuration for a single countdown timer skip rule -/
structure TimerSkipRule where
  /-- Name of the countdown register (for logging) -/
  regName : String
  /-- JIT register index for this timer -/
  regIdx : UInt32
  /-- Minimum value before triggering skip (avoid skipping small counts) -/
  minSkipThreshold : Nat := 100
  /-- Maximum cycles to skip per trigger -/
  maxSkip : Nat := 10_000_000

/-- Configuration for the timer oracle -/
structure TimerOracleConfig where
  /-- Timer skip rules (auto-generated from PatternDetect) -/
  rules : List TimerSkipRule
  /-- Require self-loop detection before timer skip (safety: only skip when idle) -/
  requireIdlePC : Bool := true
  /-- PC wire index for idle detection -/
  pcWireIdx : Nat := 0
  /-- PC tolerance for idle detection -/
  pcTolerance : UInt64 := 12
  /-- Consecutive same-PC cycles required before timer skip -/
  idleThreshold : Nat := 10

/-- Mutable state for the timer oracle -/
structure TimerOracleState where
  anchorPC : UInt64 := 0xFFFFFFFF_FFFFFFFF
  sameCount : Nat := 0
  totalSkipped : Nat := 0
  triggerCount : Nat := 0
  /-- Per-rule trigger counts -/
  ruleTriggers : List (String × Nat) := []

/-- Create a timer oracle from auto-detected countdown patterns.
    Returns the oracle function and a state reference for statistics. -/
def mkTimerOracle (config : TimerOracleConfig)
    : IO ((JITHandle → Nat → Array UInt64 → IO (Option Nat)) × IO.Ref TimerOracleState) := do
  let stateRef ← IO.mkRef ({} : TimerOracleState)

  let oracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) := fun handle _cycle vals => do
    let st ← stateRef.get

    -- Optional: check if CPU is idle (PC not changing)
    if config.requireIdlePC then
      let pc := vals[config.pcWireIdx]?.getD 0
      let pcDiff := if pc >= st.anchorPC then pc - st.anchorPC else st.anchorPC - pc
      let isNearAnchor := pcDiff <= config.pcTolerance
      if isNearAnchor then
        let newCount := st.sameCount + 1
        if newCount < config.idleThreshold then
          stateRef.set { st with sameCount := newCount }
          return none
        -- CPU is idle, proceed to check timers
        stateRef.set { st with sameCount := newCount }
      else
        stateRef.set { st with anchorPC := pc, sameCount := 0 }
        return none

    -- Check each timer rule: find the one with the smallest non-zero value
    let mut bestSkip : Option (Nat × String) := none
    for rule in config.rules do
      let val ← JIT.getReg handle rule.regIdx
      let v := val.toNat
      if v >= rule.minSkipThreshold then
        let skip := min v rule.maxSkip
        match bestSkip with
        | none => bestSkip := some (skip, rule.regName)
        | some (currentBest, _) =>
          -- Take the minimum skip (most conservative)
          if skip < currentBest then bestSkip := some (skip, rule.regName)

    match bestSkip with
    | none => return none
    | some (skipN, ruleName) =>
      -- Apply skip: set all countdown timers to their post-skip values
      for rule in config.rules do
        let val ← JIT.getReg handle rule.regIdx
        let v := val.toNat
        if v >= skipN then
          JIT.setReg handle rule.regIdx (val - skipN.toUInt64)
        else if v > 0 then
          JIT.setReg handle rule.regIdx 0

      -- Update statistics
      let newRuleTriggers := st.ruleTriggers.map fun (name, count) =>
        if name == ruleName then (name, count + 1) else (name, count)
      let newRuleTriggers := if newRuleTriggers.any (·.1 == ruleName) then newRuleTriggers
        else newRuleTriggers ++ [(ruleName, 1)]
      stateRef.set {
        anchorPC := st.anchorPC
        sameCount := if config.requireIdlePC then 0 else st.sameCount
        totalSkipped := st.totalSkipped + skipN
        triggerCount := st.triggerCount + 1
        ruleTriggers := newRuleTriggers
      }

      return some skipN

  return (oracle, stateRef)

/-- Create a combined oracle that tries the self-loop oracle first,
    then falls back to the timer oracle. -/
def mkCombinedOracle
    (primary : JITHandle → Nat → Array UInt64 → IO (Option Nat))
    (fallback : JITHandle → Nat → Array UInt64 → IO (Option Nat))
    : JITHandle → Nat → Array UInt64 → IO (Option Nat) :=
  fun handle cycle vals => do
    match ← primary handle cycle vals with
    | some n => return some n
    | none => fallback handle cycle vals

/-- Auto-generate TimerSkipRules from PatternDetect results.
    Requires a JITHandle to resolve register names → indices.
    Only includes timers with width ≥ 16 bits (small counters not worth skipping). -/
def autoGenerateRules (handle : JITHandle) (timers : List CountdownTimer)
    (minWidth : Nat := 16) : IO (List TimerSkipRule) := do
  let mut rules : List TimerSkipRule := []
  let numRegs ← JIT.numRegs handle
  for timer in timers do
    if timer.width >= minWidth then
      -- Try to find the register index by name
      let mut found := false
      for i in List.range numRegs.toNat do
        let name ← JIT.regName handle i.toUInt32
        if name == timer.regName then
          rules := rules ++ [{
            regName := timer.regName
            regIdx := i.toUInt32
            minSkipThreshold := if timer.width >= 32 then 1000 else 100
            maxSkip := min (2 ^ timer.width - 1) 10_000_000
          }]
          found := true
          break
      if !found then
        -- Try sanitized name
        let sName := timer.regName.replace "." "_"
        for i in List.range numRegs.toNat do
          let name ← JIT.regName handle i.toUInt32
          if name == sName then
            rules := rules ++ [{
              regName := timer.regName
              regIdx := i.toUInt32
              minSkipThreshold := if timer.width >= 32 then 1000 else 100
              maxSkip := min (2 ^ timer.width - 1) 10_000_000
            }]
            break
  return rules

end Sparkle.Core.TimerOracle
