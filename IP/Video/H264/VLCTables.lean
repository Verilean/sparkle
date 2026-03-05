/-
  H.264 CAVLC VLC Table Builders

  Host-side utility functions that build packed VLC table arrays from
  the existing pure lookup functions in CAVLC.lean. Each entry packs
  `(length << 16) | code` into a single 32-bit value.

  These tables are loaded into hardware memories by the JIT test host.

  Reference: ITU-T H.264 Section 9.2.1
-/

import IP.Video.H264.CAVLC

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.Video.H264.VLCTables

open Sparkle.IP.Video.H264.CAVLC

-- ============================================================================
-- Pack VLC entry: (length << 16) | code
-- ============================================================================

/-- Pack a VLC entry into a single UInt32: bits [20:16] = length, bits [15:0] = code -/
private def packVLC (code : BitVec 16) (len : BitVec 5) : UInt32 :=
  (len.toNat <<< 16 ||| code.toNat).toUInt32

-- ============================================================================
-- coeff_token table (68 entries)
-- Address = totalCoeff * 4 + trailingOnes
-- totalCoeff: 0-16, trailingOnes: 0-3
-- ============================================================================

/-- Build coeff_token VLC table (68 entries, nC=0 table).
    Address = totalCoeff * 4 + trailingOnes -/
def buildCoeffTokenTable : Array UInt32 := Id.run do
  let mut table : Array UInt32 := #[]
  for tc in [:17] do
    for t1 in [:4] do
      let (code, len) := coeffTokenLookup tc t1
      table := table.push (packVLC code len)
  table

-- ============================================================================
-- total_zeros table (96 entries)
-- Address = (totalCoeff - 1) * 16 + totalZeros
-- totalCoeff: 1-6 (existing tables), totalZeros: 0-15
-- ============================================================================

/-- Build total_zeros VLC table (96 entries).
    Address = (totalCoeff - 1) * 16 + totalZeros
    Only covers totalCoeff 1-6 (sufficient for typical blocks). -/
def buildTotalZerosTable : Array UInt32 := Id.run do
  let mut table : Array UInt32 := #[]
  for tc in [1, 2, 3, 4, 5, 6] do
    for tz in [:16] do
      let (code, len) := totalZerosLookup tc tz
      table := table.push (packVLC code len)
  table

-- ============================================================================
-- run_before table (49 entries)
-- Address = (zerosLeft - 1) * 7 + runBefore
-- zerosLeft: 1-7, runBefore: 0-6
-- ============================================================================

/-- Build run_before VLC table (49 entries).
    Address = (zerosLeft - 1) * 7 + runBefore -/
def buildRunBeforeTable : Array UInt32 := Id.run do
  let mut table : Array UInt32 := #[]
  for zl in [1, 2, 3, 4, 5, 6, 7] do
    for rb in [:7] do
      let (code, len) := runBeforeLookup zl rb
      table := table.push (packVLC code len)
  table

-- ============================================================================
-- Full coeff_token table (272 entries = 4 × 68, all nC ranges)
-- Address = tableSelect * 68 + totalCoeff * 4 + trailingOnes
-- tableSelect: 0 = nC<2, 1 = 2≤nC<4, 2 = 4≤nC<8, 3 = nC≥8
-- ============================================================================

/-- Build full coeff_token VLC table (272 entries, all 4 nC-range tables).
    Address = tableSelect * 68 + totalCoeff * 4 + trailingOnes
    where tableSelect ∈ {0, 1, 2, 3}.
    tableSelect 0 → nC<2, 1 → 2≤nC<4, 2 → 4≤nC<8, 3 → nC≥8 -/
def buildCoeffTokenTableFull : Array UInt32 := Id.run do
  let nCValues := #[0, 2, 4, 8]  -- representative nC for each table
  let mut table : Array UInt32 := #[]
  for tableIdx in [:4] do
    let nC := if h : tableIdx < nCValues.size then nCValues[tableIdx] else 0
    for tc in [:17] do
      for t1 in [:4] do
        let (code, len) := coeffTokenLookupNC nC tc t1
        table := table.push (packVLC code len)
  table

-- ============================================================================
-- Verification
-- ============================================================================

#eval do
  let ct := buildCoeffTokenTable
  IO.println s!"coeff_token table: {ct.size} entries"
  -- Verify tc=0,t1=0 → (1, 1) → packed = (1 << 16) | 1 = 65537
  IO.println s!"  [0] (tc=0,t1=0): {ct[0]!} (expected 65537)"
  -- Verify tc=1,t1=1 → (1, 2) → packed = (2 << 16) | 1 = 131073
  IO.println s!"  [5] (tc=1,t1=1): {ct[5]!} (expected 131073)"

  let tz := buildTotalZerosTable
  IO.println s!"total_zeros table: {tz.size} entries"

  let rb := buildRunBeforeTable
  IO.println s!"run_before table: {rb.size} entries"
  -- Verify zl=1,rb=0 → (1, 1) → packed = (1 << 16) | 1 = 65537
  IO.println s!"  [0] (zl=1,rb=0): {rb[0]!} (expected 65537)"

  let ctFull := buildCoeffTokenTableFull
  IO.println s!"coeff_token full table: {ctFull.size} entries (expected 272)"

end Sparkle.IP.Video.H264.VLCTables
