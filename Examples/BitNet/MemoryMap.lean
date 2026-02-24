/-
  Hespera Memory Map

  ROM address calculation for weight and scale ROMs.
  Single-bank sequential read for this first PR.
-/

import Examples.BitNet.Config

namespace Sparkle.Examples.BitNet

/-- Compute weight ROM address from row index and group index.
    address = row * groupsPerRow + group -/
def weightRomAddr (cfg : BitLinearConfig) (row : Nat) (group : Nat) : Nat :=
  row * cfg.groupsPerRow + group

/-- Compute scale ROM address (= row index) -/
def scaleRomAddr (_cfg : BitLinearConfig) (row : Nat) : Nat :=
  row

/-- Validate that a row/group pair is within bounds -/
def validWeightAddr (cfg : BitLinearConfig) (row : Nat) (group : Nat) : Bool :=
  row < cfg.outDim && group < cfg.groupsPerRow

/-- Total weight ROM size in words (256-bit words) -/
def weightRomWords (cfg : BitLinearConfig) : Nat :=
  cfg.romDepth

/-- Total weight ROM size in bytes -/
def weightRomBytes (cfg : BitLinearConfig) : Nat :=
  weightRomWords cfg * (romWordBits / 8)

/-- Total scale ROM size in words (32-bit words) -/
def scaleRomWords (cfg : BitLinearConfig) : Nat :=
  cfg.outDim

end Sparkle.Examples.BitNet
