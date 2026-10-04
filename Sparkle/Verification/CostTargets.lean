/-
  Sparkle.Verification.CostTargets — FPGA resource profiles.

  Each `Target` records the published resource ceilings of a
  specific FPGA part: LUT count, FF count, block-SRAM count
  (in 9 Kb units), and DSP multiplier-block count.  A
  `#verify_cost myDesign target` check passes iff the
  estimated resource usage stays below all four ceilings.

  These ceilings are **physical part limits** (Gowin /
  Sipeed published numbers).  Real designs typically need to
  stay below ~80% to leave routing headroom and account for
  Sparkle's coarse estimation; use `Target.withMargin` to
  apply a percentage haircut.

  Caveat: this is a static **upper-bound check on whether
  the design fits at all**, not a substitute for running
  Gowin EDA's place-and-route.  Timing closure, routing
  congestion, and clock-domain crossings are NOT modelled.
-/
import Sparkle.Verification.Cost

namespace Sparkle.Verification.Cost.Targets

/-- A physical FPGA part's resource ceilings.  All fields
    are *absolute counts* — to apply a margin (e.g. only
    use 80% of LUTs), use `Target.withMargin`.

    `picoSecPerUnit` is a coarse per-cost-unit delay
    (picoseconds, integer-arithmetic-friendly) used to
    estimate Fmax from combinational depth.  Numbers come
    from Gowin's published typical LUT4 + routing delays
    times a safety factor.  Don't trust the absolute
    value — this is a "桁感が合ってるか" check, not a
    substitute for Gowin EDA's timing report. -/
structure Target where
  name      : String
  /-- LUT4-equivalent count. -/
  maxLUT    : Nat
  /-- Total dedicated flip-flop count. -/
  maxFF     : Nat
  /-- Block SRAM count in 9 Kb units (Gowin BSRAM standard). -/
  maxBSRAM9k : Nat
  /-- 18×18 hardware multiplier block count. -/
  maxDSP18x18 : Nat
  /-- Typical delay per cost unit in picoseconds.  Used to
      estimate Fmax = 10^12 / (depth × picoSecPerUnit) Hz. -/
  picoSecPerUnit : Nat
  deriving Repr

/-! ### Tang Nano 9K — Gowin GW1NR-LV9QN88PC6/I5.

    Published spec (Gowin datasheet, Sipeed wiki):
      LUT4:       8,640
      FF:         6,480
      BSRAM 9Kb:  26   (234 Kbit total)
      18×18 mul:  0    (multipliers synthesised from LUTs) -/
def tangNano9K : Target :=
  { name        := "Tang Nano 9K (GW1NR-LV9)"
  , maxLUT      := 8640
  , maxFF       := 6480
  , maxBSRAM9k  := 26
  , maxDSP18x18 := 0
  , picoSecPerUnit := 3500 }   -- ~3.5 ns/unit (LUT4 + routing, conservative)

/-! ### Tang Nano 50K — Gowin GW5AT-LV60PG484C.

    Published spec (Sipeed Tang Nano 50K product page):
      LUT4 equiv: 60,768
      FF:         45,576
      BSRAM 9Kb:  140  (~1.26 Mbit)
      18×18 mul:  240 -/
def tangNano50K : Target :=
  { name        := "Tang Nano 50K (GW5AT-LV60)"
  , maxLUT      := 60768
  , maxFF       := 45576
  , maxBSRAM9k  := 140
  , maxDSP18x18 := 240
  , picoSecPerUnit := 2500 }   -- ~2.5 ns/unit (newer process, faster LUT4)

/-! ### Tang Nano 20K — Gowin GW2AR-LV18QN88C8/I7.

    Published spec (Gowin GW2A-18 datasheet, Sipeed wiki):
      LUT4:       20,736
      FF:         15,552
      BSRAM 18Kb: 46   (828 Kbit = 92 × 9 Kb units)
      18×18 mul:  48
    Note: BSRAM blocks are 18 Kb here (vs 9 Kb on the GW1N 9K),
    so the 9 Kb-equivalent count is 46 × 2 = 92. -/
def tangNano20K : Target :=
  { name        := "Tang Nano 20K (GW2AR-18)"
  , maxLUT      := 20736
  , maxFF       := 15552
  , maxBSRAM9k  := 92
  , maxDSP18x18 := 48
  , picoSecPerUnit := 3000 }   -- ~3.0 ns/unit (GW2A: between GW1N 9K and GW5A 50K)

/-- Apply a percentage haircut (0..100) to every ceiling.
    Use to leave routing/timing headroom — e.g.
    `tangNano9K.withMargin 80` budgets only 80% of each
    resource, mirroring "we want ≤80% utilisation before
    place-and-route gets unhappy". -/
def Target.withMargin (t : Target) (pct : Nat) : Target :=
  let scale (x : Nat) : Nat := x * pct / 100
  { name           := s!"{t.name} ({pct}% margin)"
  , maxLUT         := scale t.maxLUT
  , maxFF          := scale t.maxFF
  , maxBSRAM9k     := scale t.maxBSRAM9k
  , maxDSP18x18    := scale t.maxDSP18x18
  , picoSecPerUnit := t.picoSecPerUnit }

end Sparkle.Verification.Cost.Targets
