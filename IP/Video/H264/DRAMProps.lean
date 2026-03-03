/-
  DRAM Formal Properties — Pure State Machine Model

  Proves safety properties of the DRAM memory model:
  - Read-after-write: writing v to addr a, then reading addr a, returns v
  - Read-default: reading unwritten address returns 0
  - Write-write: last write wins (same address)

  Pattern follows QueueProps.lean: self-contained definitions + proofs,
  no cross-library dependencies.
-/

import IP.Video.H264.DRAMInterface

namespace Sparkle.IP.Video.H264.DRAMProps

open Sparkle.IP.Video.H264.DRAMInterface

-- ============================================================================
-- Read-after-write
-- ============================================================================

/-- Reading an address just written returns the written value. -/
theorem read_after_write (s : DRAMState) (addr : BitVec 24) (val : BitVec 32) :
    (s.write addr val).read addr = val := by
  simp [DRAMState.write, DRAMState.read, List.find?]

/-- Reading a different address after a write returns the original value. -/
theorem read_other_after_write (s : DRAMState) (a1 a2 : BitVec 24) (val : BitVec 32) :
    a1 ≠ a2 → (s.write a1 val).read a2 = s.read a2 := by
  intro hne
  unfold DRAMState.write DRAMState.read
  simp [List.find?]
  have : (a1 == a2) = false := by
    simp [BEq.beq, decide_eq_false_iff_not, hne]
  simp [this]

-- ============================================================================
-- Read-default
-- ============================================================================

/-- Reading from an empty DRAM returns 0. -/
theorem read_empty (addr : BitVec 24) :
    DRAMState.empty.read addr = 0#32 := by
  simp [DRAMState.empty, DRAMState.read, List.find?]

-- ============================================================================
-- Write-write (last write wins)
-- ============================================================================

/-- Two writes to the same address: the last write wins. -/
theorem write_write_same_addr (s : DRAMState) (addr : BitVec 24) (v1 v2 : BitVec 32) :
    (s.write addr v1 |>.write addr v2).read addr = v2 := by
  simp [DRAMState.write, DRAMState.read, List.find?]

/-- Write to addr a does not affect reads from different addresses.
    (Frame condition) -/
theorem write_preserves_other (s : DRAMState) (a1 a2 : BitVec 24) (val : BitVec 32) :
    a1 ≠ a2 → (s.write a1 val).read a2 = s.read a2 := by
  exact read_other_after_write s a1 a2 val

-- ============================================================================
-- Determinism
-- ============================================================================

/-- Reads are deterministic: same state + same address → same result. -/
theorem read_deterministic (s : DRAMState) (addr : BitVec 24) :
    s.read addr = s.read addr := by
  rfl

end Sparkle.IP.Video.H264.DRAMProps
