/-
  H.264 CAVLC Encoder — Fully Synthesizable Module

  Multi-cycle FSM that reads 16 quantized coefficients and produces a
  packed CAVLC bitstream using VLC table memories (loaded by host).

  Architecture:
    - 6 memories: coefficients, 3 VLC tables, scanned levels, scan positions
    - ~30 state registers via declare_signal_state
    - FSM phases: IDLE → SCAN → EMIT_CT → EMIT_T1S → EMIT_LEVEL → EMIT_TZ → EMIT_RB → DONE

  Interface:
    Inputs: start, coeff write port, 3 VLC table write ports
    Outputs: bitstreamData(64), bitLen(7), done

  Reference: ITU-T H.264 Section 9.2.1
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 8192
set_option maxHeartbeats 6400000

namespace Sparkle.IP.Video.H264.CAVLCSynth

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

-- ============================================================================
-- State definition (~30 registers)
-- ============================================================================

declare_signal_state CAVLCSynthState
  | fsmState     : BitVec 4  := 0#4     -- FSM phase
  | scanIdx      : BitVec 5  := 0#5     -- scan counter (0-17)
  | totalCoeff   : BitVec 5  := 0#5     -- non-zero coefficient count
  | trailingOnes : BitVec 3  := 0#3     -- trailing ±1 count (max 3)
  | totalZeros   : BitVec 5  := 0#5     -- total zeros before last NZ
  | lastNzPos    : BitVec 5  := 0#5     -- position of last non-zero
  | levelIdx     : BitVec 5  := 0#5     -- current level index for emission
  | runIdx       : BitVec 5  := 0#5     -- current run index for emission
  | suffixLen    : BitVec 3  := 0#3     -- Exp-Golomb suffix length
  | zerosLeft    : BitVec 5  := 0#5     -- remaining zeros for run_before
  | bitBuffer    : BitVec 64 := 0#64    -- packed output bitstream (64-bit to avoid overflow)
  | bitPos       : BitVec 7  := 0#7     -- current bit position (7-bit for 0-63 range)
  | t1Signs      : BitVec 3  := 0#3     -- trailing ones sign bits
  | t1Idx        : BitVec 3  := 0#3     -- trailing ones emission index
  | nzCount      : BitVec 5  := 0#5     -- non-zero count during scan
  | prevNzPos    : BitVec 5  := 0#5     -- previous NZ position (for run_before)
  | curLevel     : BitVec 16 := 0#16    -- current level being read
  | curPos       : BitVec 5  := 0#5     -- current position being read
  | prevPos      : BitVec 5  := 0#5     -- previous position for run_before
  | outValid     : Bool       := false   -- output valid
  | done         : Bool       := false   -- encoding complete
  | rbSubState   : BitVec 2  := 0#2     -- run_before sub-state (read prev, compute)
  | levelSubState : BitVec 2 := 0#2     -- level encoding sub-state

-- FSM state constants
private def FSM_IDLE       : BitVec 4 := 0#4
private def FSM_SCAN       : BitVec 4 := 1#4
private def FSM_EMIT_CT    : BitVec 4 := 2#4
private def FSM_EMIT_T1S   : BitVec 4 := 3#4
private def FSM_EMIT_LEVEL : BitVec 4 := 4#4
private def FSM_EMIT_TZ    : BitVec 4 := 5#4
private def FSM_EMIT_RB    : BitVec 4 := 6#4
private def FSM_OUTPUT     : BitVec 4 := 7#4
private def FSM_DONE       : BitVec 4 := 8#4
private def FSM_RB_INIT    : BitVec 4 := 9#4
private def FSM_LEVEL_READ : BitVec 4 := 10#4

-- ============================================================================
-- Zig-zag scan table (pure Lean, used to build host-side init data)
-- ============================================================================

def zigzagTable : Array UInt32 :=
  #[0, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15]

-- ============================================================================
-- Pure reference (reuses CAVLC.lean)
-- ============================================================================

-- Import pure reference from CAVLC module
-- def cavlcSynthRef := CAVLC.cavlcEncodeFull

-- ============================================================================
-- FSM body
-- ============================================================================

/-- CAVLC synthesizable encoder FSM body.
    Uses 6 memories: coefficients, 3 VLC tables, scanned levels, scan positions. -/
private def cavlcSynthBody {dom : DomainConfig}
    (start : Signal dom Bool)
    -- Coefficient memory read data (combo-read, addressed by zig-zag index)
    (coeffReadData : Signal dom (BitVec 16))
    -- VLC table combo-read data
    (ctTableData : Signal dom (BitVec 32))    -- coeff_token table
    (tzTableData : Signal dom (BitVec 32))    -- total_zeros table
    (rbTableData : Signal dom (BitVec 32))    -- run_before table
    -- Level memory combo-read data (scanned non-zero levels)
    (levelReadData : Signal dom (BitVec 16))
    -- Position memory combo-read data (scanned non-zero positions)
    (posReadData : Signal dom (BitVec 16))
    -- State
    (state : Signal dom CAVLCSynthState)
    : Signal dom CAVLCSynthState :=
  -- Extract current state
  let fsmState     := CAVLCSynthState.fsmState state
  let scanIdx      := CAVLCSynthState.scanIdx state
  let totalCoeff   := CAVLCSynthState.totalCoeff state
  let trailingOnes := CAVLCSynthState.trailingOnes state
  let totalZeros   := CAVLCSynthState.totalZeros state
  let lastNzPos    := CAVLCSynthState.lastNzPos state
  let levelIdx     := CAVLCSynthState.levelIdx state
  let runIdx       := CAVLCSynthState.runIdx state
  let suffixLen    := CAVLCSynthState.suffixLen state
  let zerosLeft    := CAVLCSynthState.zerosLeft state
  let bitBuffer    := CAVLCSynthState.bitBuffer state
  let bitPos       := CAVLCSynthState.bitPos state
  let t1Signs      := CAVLCSynthState.t1Signs state
  let t1Idx        := CAVLCSynthState.t1Idx state
  let nzCount      := CAVLCSynthState.nzCount state
  let prevNzPos    := CAVLCSynthState.prevNzPos state
  let curLevel     := CAVLCSynthState.curLevel state
  let curPos       := CAVLCSynthState.curPos state
  let prevPos      := CAVLCSynthState.prevPos state
  let _outValid    := CAVLCSynthState.outValid state
  let _done        := CAVLCSynthState.done state
  let rbSubState   := CAVLCSynthState.rbSubState state
  let levelSubState := CAVLCSynthState.levelSubState state

  -- FSM state comparisons
  let isIdle     := fsmState === (FSM_IDLE : Signal dom _)
  let isScan     := fsmState === (FSM_SCAN : Signal dom _)
  let isEmitCT   := fsmState === (FSM_EMIT_CT : Signal dom _)
  let isEmitT1S  := fsmState === (FSM_EMIT_T1S : Signal dom _)
  let isEmitLevel := fsmState === (FSM_EMIT_LEVEL : Signal dom _)
  let isLevelRead := fsmState === (FSM_LEVEL_READ : Signal dom _)
  let isEmitTZ   := fsmState === (FSM_EMIT_TZ : Signal dom _)
  let isRBInit   := fsmState === (FSM_RB_INIT : Signal dom _)
  let isEmitRB   := fsmState === (FSM_EMIT_RB : Signal dom _)
  let isOutput   := fsmState === (FSM_OUTPUT : Signal dom _)
  let isDone     := fsmState === (FSM_DONE : Signal dom _)

  let startAndIdle := start &&& isIdle

  -- ================================================================
  -- SCAN phase: process coefficients (16 cycles: 0-15, combo-read = immediate data)
  -- With memoryComboRead, data at zigzag[scanIdx] is available in the same cycle.
  -- scanIdx 0-15: process positions 0-15. scanIdx 16: scanDone fires.
  -- ================================================================
  let scanDone := isScan &&& (scanIdx === (16#5 : Signal dom _))
  let scanDataValid := isScan &&& ~~~scanDone
  let processingPos := scanIdx

  -- Check coefficient properties
  let dataIsNonZero := ~~~(coeffReadData === (0#16 : Signal dom _))
  let isPositiveOne := coeffReadData === (1#16 : Signal dom _)
  let isNegativeOne := coeffReadData === (0xFFFF#16 : Signal dom _)
  let dataIsT1 := isPositiveOne ||| isNegativeOne
  let dataSignBit := coeffReadData.map (BitVec.extractLsb' 15 1 ·)
  let dataSign := ~~~(dataSignBit === (0#1 : Signal dom _))

  -- Scan accumulation
  let incTC := scanDataValid &&& dataIsNonZero
  let isT1Hit := scanDataValid &&& dataIsNonZero &&& dataIsT1
  let isNonT1Hit := scanDataValid &&& dataIsNonZero &&& ~~~dataIsT1

  -- ================================================================
  -- EMIT_CT: Read coeff_token from table (combo-read, single cycle)
  -- Address = totalCoeff * 4 + trailingOnes (already set in table read addr)
  -- ================================================================
  -- Extract code and length from packed table entry: bits[15:0] = code, bits[20:16] = length
  let ctCode := ctTableData.map (BitVec.extractLsb' 0 16 ·)
  let ctLen  := ctTableData.map (BitVec.extractLsb' 16 6 ·)

  -- Shift code into bit buffer: buffer |= (code64 << (64 - bitPos - len))
  let ctCode64 := 0#48 ++ ctCode
  let ctLen7 := 0#1 ++ ctLen
  let ctShift  := (64#7 - bitPos) - ctLen7
  let ctShift64 := 0#57 ++ ctShift
  let ctShifted := ctCode64 <<< ctShift64
  let ctNewBuf := bitBuffer ||| ctShifted
  let ctNewPos := bitPos + ctLen7

  -- ================================================================
  -- EMIT_T1S: Emit trailing ones sign bits (1 cycle)
  -- ================================================================
  -- Emit t1Idx sign bits from t1Signs register (bit 0 = last T1, bit 1 = 2nd last, etc.)
  -- Each sign is 1 bit (0=positive, 1=negative)
  -- Extract sign bit at t1Idx position: shift t1Signs right by t1Idx, check bit 0
  let t1ShiftedSigns := t1Signs >>> t1Idx
  let t1SignBit0 := t1ShiftedSigns.map (BitVec.extractLsb' 0 1 ·)
  let t1SignBit := ~~~(t1SignBit0 === (0#1 : Signal dom _))
  let t1Code64 := Signal.mux t1SignBit (Signal.pure 1#64) (Signal.pure 0#64)
  let t1Shift  := (64#7 - bitPos) - 1#7
  let t1Shift64 := 0#57 ++ t1Shift
  let t1Shifted := t1Code64 <<< t1Shift64
  let t1NewBuf := bitBuffer ||| t1Shifted
  let t1NewPos := bitPos + 1#7

  let t1IdxInc := t1Idx + 1#3
  let t1EmitDone := t1IdxInc === trailingOnes

  -- ================================================================
  -- EMIT_LEVEL: Two-phase level encoding
  -- Phase 0 (LEVEL_READ): Read level from memory, compute encoding
  -- Phase 1 (EMIT_LEVEL): Emit prefix+suffix into buffer
  -- ================================================================
  -- Level is stored as signed 16-bit in memory. Need to compute Exp-Golomb code.
  -- levelCode = if level > 0 then 2*level-2 else -2*level-1
  -- If first level and T1 < 3: levelCode -= 2

  -- Use curLevel (loaded during LEVEL_READ phase) instead of levelReadData
  -- (levelReadData reads from addr 0 during EMIT_LEVEL since levelReadIdx is not set)
  let levelSigned := curLevel
  let levelSignBit := levelSigned.map (BitVec.extractLsb' 15 1 ·)
  let levelIsNeg := levelSignBit === (1#1 : Signal dom _)
  let levelAbs := Signal.mux levelIsNeg
    (0#16 - levelSigned)
    levelSigned
  let levelAbs32 := 0#16 ++ levelAbs

  -- levelCode computation
  let lcPos := (levelAbs32 + levelAbs32) - 2#32
  let lcNeg := (levelAbs32 + levelAbs32) - 1#32
  let levelCode0 := Signal.mux levelIsNeg lcNeg lcPos

  -- Adjust for first emitted level when T1 < 3
  -- Levels emit in reverse: levelIdx starts at numLevels-1, so the first emitted level is at numLevels-1
  let numLevelsEarly := totalCoeff - (0#2 ++ trailingOnes)
  let firstLevelIdx := numLevelsEarly - 1#5
  let isFirstLevel := levelIdx === firstLevelIdx
  let t1LessThan3 := ~~~(trailingOnes === (3#3 : Signal dom _))
  let adjustFirst := isFirstLevel &&& t1LessThan3
  let levelCode := Signal.mux adjustFirst
    (levelCode0 - 2#32)
    levelCode0

  -- ================================================================
  -- Prefix and suffix computation per H.264 Section 9.2.2
  -- Three regimes:
  --   Normal:     suffixLen>0 && rawPfx<15, or suffixLen=0 && lc<14
  --   MidEscape:  suffixLen=0 && 14<=lc<30  → pfx=14, suffBits=4
  --   FullEscape: suffixLen=0 && lc>=30, or suffixLen>0 && rawPfx>=15  → pfx=15, suffBits=12
  -- ================================================================
  let slExt := 0#29 ++ suffixLen
  let rawPrefix := levelCode >>> slExt
  let slIsZero := suffixLen === (0#3 : Signal dom _)

  -- rawPrefix >= 15 detection (for suffixLen > 0)
  let pfxHigh := rawPrefix.map (BitVec.extractLsb' 4 28 ·)
  let pfxIsExact15 := rawPrefix === 15#32
  let pfxHighNonZero := ~~~(pfxHigh === (0#28 : Signal dom _))
  let prefixGe15Raw := pfxHighNonZero ||| pfxIsExact15

  -- For suffixLen=0: detect levelCode >= 14 and >= 30
  let lcMinus14 := levelCode - 14#32
  let lcGe14Sign := lcMinus14.map (BitVec.extractLsb' 31 1 ·)
  let lcGe14 := lcGe14Sign === (0#1 : Signal dom _)  -- unsigned: no borrow means >= 14
  let lcMinus30 := levelCode - 30#32
  let lcGe30Sign := lcMinus30.map (BitVec.extractLsb' 31 1 ·)
  let lcGe30 := lcGe30Sign === (0#1 : Signal dom _)

  -- Regime detection
  let isMidEscape := slIsZero &&& lcGe14 &&& ~~~lcGe30
  let isFullEscape := Signal.mux slIsZero lcGe30 prefixGe15Raw

  -- Corrected prefix
  let correctedPrefix := Signal.mux isFullEscape (Signal.pure 15#32)
    (Signal.mux isMidEscape (Signal.pure 14#32) rawPrefix)

  -- prefixBits = prefix + 1 (number of bits: prefix zeros + 1 one)
  let prefixBits := correctedPrefix + 1#32
  let prefixBits6 := prefixBits.map (BitVec.extractLsb' 0 6 ·)
  let prefixBits7 := 0#1 ++ prefixBits6

  -- Normal suffix: levelCode & ((1 << suffixLen) - 1)
  let slMask := (1#32 - slExt) <<< 1#32
  let normalSuffix := levelCode &&& slMask
  -- Escape suffix: levelCode - 15*(1 << suffixLen)  (works for suffixLen=0 too: lc-15)
  let shifted15 := 15#32 <<< slExt
  let escapeSuffix := levelCode - shifted15
  -- Mid-escape suffix: levelCode - 14
  let midEscapeSuffix := lcMinus14

  -- Select suffix and suffix bits
  let correctedSuffix := Signal.mux isFullEscape escapeSuffix
    (Signal.mux isMidEscape midEscapeSuffix normalSuffix)
  let normalHasSuffix := ~~~slIsZero
  let correctedHasSuffix := isFullEscape ||| isMidEscape ||| normalHasSuffix
  let normalSuffBits7 := 0#4 ++ suffixLen
  let correctedSuffBits7 := Signal.mux isFullEscape (Signal.pure 12#7)
    (Signal.mux isMidEscape (Signal.pure 4#7) normalSuffBits7)

  -- Emit prefix: a 1 bit at position (prefix zeros already counted by shift)
  let pfxShift := (64#7 - bitPos) - prefixBits7
  let pfxShift64 := 0#57 ++ pfxShift
  let pfxCode := 1#64 <<< pfxShift64
  let lvlBuf1 := bitBuffer ||| pfxCode
  let lvlPos1 := bitPos + prefixBits7

  -- Emit suffix (if any)
  let suffix64 := 0#32 ++ correctedSuffix
  let sfxShift := (64#7 - lvlPos1) - correctedSuffBits7
  let sfxShift64 := 0#57 ++ sfxShift
  let sfxCode := suffix64 <<< sfxShift64
  let lvlBuf2 := lvlBuf1 ||| sfxCode
  let lvlPos2 := lvlPos1 + correctedSuffBits7
  let lvlNewBuf := Signal.mux correctedHasSuffix lvlBuf2 lvlBuf1
  let lvlNewPos := Signal.mux correctedHasSuffix lvlPos2 lvlPos1

  -- Update suffixLen based on level magnitude
  -- if suffixLen == 0: suffixLen = 1
  -- else if absLevel > 3 * (1 << (suffixLen-1)) && suffixLen < 6: suffixLen + 1
  let slIsZero := suffixLen === 0#3
  let slInc := suffixLen + 1#3
  -- suffixLen < 6 for 3-bit value: anything except 6 or 7
  let slIs6 := suffixLen === (6#3 : Signal dom _)
  let slIs7 := suffixLen === (7#3 : Signal dom _)
  let slLt6 := (~~~slIs6) &&& (~~~slIs7)
  -- Threshold = 3 * (1 << (suffixLen - 1)) = 3, 6, 12, 24, 48
  let slDec := suffixLen - 1#3
  let slDecExt := 0#29 ++ slDec
  let threshold := 3#32 * (1#32 <<< slDecExt)
  -- exceedsThreshold: levelAbs > threshold
  -- Use subtraction: if levelAbs - threshold - 1 has no borrow (i.e., result < 2^32 and high bit clear)
  -- Simpler: check if (levelAbs - threshold) != 0 and sign bit of (threshold - levelAbs) is set
  let diffAbsThr := levelAbs32 - threshold
  let thrDiffHigh := diffAbsThr.map (BitVec.extractLsb' 31 1 ·)
  let diffNonZero := ~~~(diffAbsThr === (0#32 : Signal dom _))
  let thrDiffSignIsZero := thrDiffHigh === (0#1 : Signal dom _)
  let exceedsThreshold := diffNonZero &&& thrDiffSignIsZero
  let shouldIncSL := ~~~slIsZero &&& exceedsThreshold &&& slLt6
  let newSuffixLen := Signal.mux slIsZero (Signal.pure 1#3)
    (Signal.mux shouldIncSL slInc suffixLen)

  -- Level emission complete check: levelIdx reaches totalCoeff - trailingOnes - 1
  let numLevels := totalCoeff - (0#2 ++ trailingOnes)
  let levelIdxInc := levelIdx + 1#5
  -- levelEmitDone: true when levelIdx has been decremented to 0 (all levels emitted)
  let levelEmitDone := levelIdx === (0#5 : Signal dom _)
  let hasLevels := ~~~(numLevels === (0#5 : Signal dom _))

  -- ================================================================
  -- EMIT_TZ: Read total_zeros from table (single cycle)
  -- Address = (totalCoeff - 1) * 16 + totalZeros (already set)
  -- ================================================================
  let tzCode := tzTableData.map (BitVec.extractLsb' 0 16 ·)
  let tzLen  := tzTableData.map (BitVec.extractLsb' 16 6 ·)
  let tzCode64 := 0#48 ++ tzCode
  let tzLen7 := 0#1 ++ tzLen
  let tzShift  := (64#7 - bitPos) - tzLen7
  let tzShift64 := 0#57 ++ tzShift
  let tzShifted := tzCode64 <<< tzShift64
  let tzNewBuf := bitBuffer ||| tzShifted
  let tzNewPos := bitPos + tzLen7
  let needTZ := ~~~(totalCoeff === (16#5 : Signal dom _))

  -- ================================================================
  -- EMIT_RB: Read run_before from table
  -- Sub-state 0: Read pos[runIdx] into curPos (the "lower" position)
  -- Sub-state 1: Compute rb = prevPos - curPos - 1, emit VLC, set prevPos = curPos
  -- prevPos starts as the "higher" position from RB_INIT
  -- ================================================================
  -- run_before = prevPos - curPos - 1 (prevPos is the later/higher position)
  let runBefore := (prevPos - curPos) - 1#5
  -- Table address = (zerosLeft - 1) * 7 + runBefore
  -- rbTableData already has the result at this address
  let rbCode := rbTableData.map (BitVec.extractLsb' 0 16 ·)
  let rbLen  := rbTableData.map (BitVec.extractLsb' 16 6 ·)
  let rbCode64 := 0#48 ++ rbCode
  let rbLen7 := 0#1 ++ rbLen
  let rbShift  := (64#7 - bitPos) - rbLen7
  let rbShift64 := 0#57 ++ rbShift
  let rbShifted := rbCode64 <<< rbShift64
  let rbNewBuf := bitBuffer ||| rbShifted
  let rbNewPos := bitPos + rbLen7
  let rbNewZerosLeft := zerosLeft - runBefore
  let hasZerosLeft := ~~~(zerosLeft === (0#5 : Signal dom _))

  -- Run index for run_before: goes from totalCoeff-2 down to 0
  let runIdxDec := runIdx - 1#5
  -- Done when runIdx reaches 0 (last pair processed) or zerosLeft exhausted
  let rbEmitDone := (runIdx === (0#5 : Signal dom _)) ||| ~~~hasZerosLeft
  let isRBSub0 := rbSubState === (0#2 : Signal dom _)
  let isRBSub1 := rbSubState === (1#2 : Signal dom _)

  -- ================================================================
  -- FSM Next State logic
  -- ================================================================
  -- After SCAN → EMIT_CT
  -- After EMIT_CT → EMIT_T1S if trailingOnes > 0, else skip
  -- After EMIT_T1S → EMIT_LEVEL if numLevels > 0, else skip
  -- After EMIT_LEVEL → EMIT_TZ if totalCoeff < 16, else skip
  -- After EMIT_TZ → RB_INIT if totalCoeff > 1 and totalZeros > 0, else OUTPUT
  -- After EMIT_RB → OUTPUT when done
  let hasT1 := ~~~(trailingOnes === (0#3 : Signal dom _))
  let tcIs0 := totalCoeff === (0#5 : Signal dom _)
  let tcIs1 := totalCoeff === (1#5 : Signal dom _)
  let hasRB := (~~~tcIs0) &&& (~~~tcIs1)
  let hasTZ := ~~~(totalZeros === (0#5 : Signal dom _))

  -- Level read done
  let isLvlSub0 := levelSubState === (0#2 : Signal dom _)

  -- After EMIT_CT: go to EMIT_T1S if has trailing ones, else check levels
  let afterCT := Signal.mux hasT1 (FSM_EMIT_T1S : Signal dom _)
    (Signal.mux hasLevels (FSM_LEVEL_READ : Signal dom _)
      (Signal.mux needTZ (FSM_EMIT_TZ : Signal dom _)
        (FSM_OUTPUT : Signal dom _)))

  -- After EMIT_T1S (all T1 signs emitted)
  let afterT1S := Signal.mux hasLevels (FSM_LEVEL_READ : Signal dom _)
    (Signal.mux needTZ (FSM_EMIT_TZ : Signal dom _)
      (FSM_OUTPUT : Signal dom _))

  -- After all levels emitted
  let afterLevels := Signal.mux needTZ (FSM_EMIT_TZ : Signal dom _)
    (FSM_OUTPUT : Signal dom _)

  -- After total_zeros emitted
  let afterTZ := Signal.mux (hasRB &&& hasTZ) (FSM_RB_INIT : Signal dom _)
    (FSM_OUTPUT : Signal dom _)

  -- Zero coefficient special case: skip all encoding
  let tcIsZero := totalCoeff === (0#5 : Signal dom _)

  let fsmNext := hw_cond fsmState
    | startAndIdle => (FSM_SCAN : Signal dom _)
    | scanDone     => (FSM_EMIT_CT : Signal dom _)
    | isEmitCT     => Signal.mux tcIsZero (FSM_OUTPUT : Signal dom _) afterCT
    | (isEmitT1S &&& t1EmitDone) => afterT1S
    | isEmitT1S    => fsmState  -- continue emitting T1 signs
    | isLevelRead  => (FSM_EMIT_LEVEL : Signal dom _)
    | (isEmitLevel &&& levelEmitDone) => afterLevels
    | isEmitLevel  => (FSM_LEVEL_READ : Signal dom _)
    | isEmitTZ     => afterTZ
    | isRBInit     => (FSM_EMIT_RB : Signal dom _)
    | (isEmitRB &&& isRBSub1 &&& rbEmitDone) => (FSM_OUTPUT : Signal dom _)
    | (isEmitRB &&& isRBSub1) => fsmState  -- next RB iteration
    | isEmitRB     => fsmState  -- sub-state progression
    | isOutput     => (FSM_DONE : Signal dom _)
    | isDone       => (FSM_IDLE : Signal dom _)

  -- ================================================================
  -- Register updates
  -- ================================================================

  -- scanIdx
  let scanIdxNext := hw_cond (0#5 : Signal dom _)
    | startAndIdle => (0#5 : Signal dom _)
    | isScan       => scanIdx + 1#5

  -- totalCoeff (must hold value after scan)
  let tcInc := totalCoeff + 1#5
  let totalCoeffNext := hw_cond totalCoeff
    | startAndIdle => (0#5 : Signal dom _)
    | incTC        => tcInc
    | isScan       => totalCoeff

  -- trailingOnes (accumulated during scan using reset-on-non-T1 pattern, hold after scan)
  -- Forward scan: reset to 0 on non-T1 non-zero, increment on T1 (cap at 3)
  let t1Cap := ~~~(trailingOnes === (3#3 : Signal dom _))
  let t1Inc := trailingOnes + 1#3
  let trailingOnesNext := hw_cond trailingOnes
    | startAndIdle => (0#3 : Signal dom _)
    | isNonT1Hit   => (0#3 : Signal dom _)
    | (isT1Hit &&& t1Cap) => t1Inc
    | isT1Hit      => trailingOnes
    | isScan       => trailingOnes

  -- t1Signs (shift register for trailing one signs, hold after scan)
  let shiftedSigns := t1Signs <<< 1#3
  let newSignBit := Signal.mux dataSign
    (shiftedSigns ||| 1#3)
    shiftedSigns
  let t1SignsNext := hw_cond t1Signs
    | startAndIdle => (0#3 : Signal dom _)
    | isNonT1Hit   => (0#3 : Signal dom _)
    | isT1Hit      => newSignBit
    | isScan       => t1Signs

  -- lastNzPos (hold after scan)
  let lastNzPosNext := hw_cond lastNzPos
    | startAndIdle => (0#5 : Signal dom _)
    | incTC        => processingPos
    | isScan       => lastNzPos

  -- totalZeros (computed at end of scan, hold after)
  let totalZerosNext := hw_cond totalZeros
    | startAndIdle => (0#5 : Signal dom _)
    | scanDone     => (lastNzPos + 1#5) - totalCoeff
    | isScan       => totalZeros

  -- nzCount (for writing levels/positions during scan, hold after scan)
  let nzCountInc := nzCount + 1#5
  let nzCountNext := hw_cond nzCount
    | startAndIdle => (0#5 : Signal dom _)
    | incTC        => nzCountInc
    | isScan       => nzCount

  -- prevNzPos (for position tracking during scan, hold after)
  let prevNzPosNext := hw_cond prevNzPos
    | startAndIdle => (0#5 : Signal dom _)
    | incTC        => processingPos

  -- t1Idx (trailing ones emission index, hold value)
  let t1IdxNext := hw_cond t1Idx
    | startAndIdle => (0#3 : Signal dom _)
    | isEmitCT     => (0#3 : Signal dom _)
    | isEmitT1S    => t1IdxInc

  -- levelIdx (level emission index, counts from numLevels-1 down to 0)
  -- Levels are stored in mem4 in forward scan order
  -- We emit them in REVERSE order: start from numLevels-1, go down to 0
  let levelIdxNext := hw_cond levelIdx
    | startAndIdle => (0#5 : Signal dom _)
    | isEmitCT     => numLevels - 1#5
    | isEmitLevel  => levelIdx - 1#5

  -- suffixLen (hold value between level emissions)
  -- tc > 10: subtract 11, check if no underflow (bit 4 is 0)
  let tcMinus11 := totalCoeff - 11#5
  let tcMinus11Sign := tcMinus11.map (BitVec.extractLsb' 4 1 ·)
  let tcGt10 := tcMinus11Sign === (0#1 : Signal dom _)
  let t1Lt3 := ~~~(trailingOnes === (3#3 : Signal dom _))
  let initSuffixLen := Signal.mux (tcGt10 &&& t1Lt3)
    (Signal.pure 1#3) (Signal.pure 0#3)
  let suffixLenNext := hw_cond suffixLen
    | startAndIdle => (0#3 : Signal dom _)
    | isEmitCT     => initSuffixLen
    | isEmitLevel  => newSuffixLen

  -- zerosLeft (hold value between RB emissions)
  let zerosLeftNext := hw_cond zerosLeft
    | startAndIdle => (0#5 : Signal dom _)
    | isEmitTZ     => totalZeros
    | (isEmitRB &&& isRBSub1) => rbNewZerosLeft

  -- runIdx (starts at totalCoeff-1, decrements, hold value)
  let runIdxNext := hw_cond runIdx
    | startAndIdle => (0#5 : Signal dom _)
    | isRBInit     => totalCoeff - 2#5
    | (isEmitRB &&& isRBSub1) => runIdxDec

  -- rbSubState (hold value)
  let rbSubStateNext := hw_cond rbSubState
    | startAndIdle => (0#2 : Signal dom _)
    | isRBInit     => (0#2 : Signal dom _)
    | (isEmitRB &&& isRBSub0) => (1#2 : Signal dom _)
    | (isEmitRB &&& isRBSub1) => (0#2 : Signal dom _)

  -- levelSubState (hold value)
  let levelSubStateNext := hw_cond levelSubState
    | startAndIdle => (0#2 : Signal dom _)
    | isLevelRead  => (0#2 : Signal dom _)

  -- curPos / prevPos (for run_before computation, hold value)
  let curPosNext := hw_cond curPos
    | startAndIdle => (0#5 : Signal dom _)
    | (isEmitRB &&& isRBSub0) => posReadData.map (BitVec.extractLsb' 0 5 ·)

  let prevPosNext := hw_cond prevPos
    | startAndIdle => (0#5 : Signal dom _)
    | (isEmitRB &&& isRBSub1) => curPos  -- advance: prevPos ← curPos for next iteration
    | isRBInit => posReadData.map (BitVec.extractLsb' 0 5 ·)  -- init: prevPos ← pos[tc-1]

  -- curLevel (hold value)
  let curLevelNext := hw_cond curLevel
    | startAndIdle => (0#16 : Signal dom _)
    | isLevelRead  => levelReadData

  -- bitBuffer
  let bitBufferNext := hw_cond bitBuffer
    | startAndIdle => (0#64 : Signal dom _)
    | isEmitCT     => ctNewBuf
    | isEmitT1S    => t1NewBuf
    | isEmitLevel  => lvlNewBuf
    | isEmitTZ     => tzNewBuf
    | (isEmitRB &&& isRBSub1) => rbNewBuf

  -- bitPos
  let bitPosNext := hw_cond bitPos
    | startAndIdle => (0#7 : Signal dom _)
    | isEmitCT     => ctNewPos
    | isEmitT1S    => t1NewPos
    | isEmitLevel  => lvlNewPos
    | isEmitTZ     => tzNewPos
    | (isEmitRB &&& isRBSub1) => rbNewPos

  -- Output signals
  let validOutNext := isOutput
  let doneNext := isDone

  -- Bundle next state
  bundleAll! [
    Signal.register FSM_IDLE fsmNext,
    Signal.register 0#5  scanIdxNext,
    Signal.register 0#5  totalCoeffNext,
    Signal.register 0#3  trailingOnesNext,
    Signal.register 0#5  totalZerosNext,
    Signal.register 0#5  lastNzPosNext,
    Signal.register 0#5  levelIdxNext,
    Signal.register 0#5  runIdxNext,
    Signal.register 0#3  suffixLenNext,
    Signal.register 0#5  zerosLeftNext,
    Signal.register 0#64 bitBufferNext,
    Signal.register 0#7  bitPosNext,
    Signal.register 0#3  t1SignsNext,
    Signal.register 0#3  t1IdxNext,
    Signal.register 0#5  nzCountNext,
    Signal.register 0#5  prevNzPosNext,
    Signal.register 0#16 curLevelNext,
    Signal.register 0#5  curPosNext,
    Signal.register 0#5  prevPosNext,
    Signal.register false validOutNext,
    Signal.register false doneNext,
    Signal.register 0#2  rbSubStateNext,
    Signal.register 0#2  levelSubStateNext
  ]

-- ============================================================================
-- Top-level synthesizable module
-- ============================================================================

/-- Synthesizable CAVLC encoder with VLC table memories.

    Input ports:
      0: start
      1: nCTableSelect(2)    — selects coeff_token table (0=nC<2, 1=2≤nC<4, 2=4≤nC<8, 3=nC≥8)
      2: coeffWriteEn        6: ctTableWriteEn      10: tzTableWriteEn
      3: coeffWriteAddr(4)    7: ctTableWriteAddr(9) 11: tzTableWriteAddr(7)
      4: coeffWriteData(16)   8: ctTableWriteData(32) 12: tzTableWriteData(32)
      5: (unused)             9: (unused)            13: rbTableWriteEn
                                                     14: rbTableWriteAddr(6)
                                                     15: rbTableWriteData(32)
    Output: (bitstreamData(64), bitLen(32), done(32), valid(32)) -/
def cavlcSynthModule {dom : DomainConfig}
    (start : Signal dom Bool)
    (nCTableSelect : Signal dom (BitVec 2))
    (coeffWriteEn : Signal dom Bool)
    (coeffWriteAddr : Signal dom (BitVec 4))
    (coeffWriteData : Signal dom (BitVec 16))
    (ctTableWriteEn : Signal dom Bool)
    (ctTableWriteAddr : Signal dom (BitVec 9))
    (ctTableWriteData : Signal dom (BitVec 32))
    (tzTableWriteEn : Signal dom Bool)
    (tzTableWriteAddr : Signal dom (BitVec 7))
    (tzTableWriteData : Signal dom (BitVec 32))
    (rbTableWriteEn : Signal dom Bool)
    (rbTableWriteAddr : Signal dom (BitVec 6))
    (rbTableWriteData : Signal dom (BitVec 32))
    (zzTableWriteEn : Signal dom Bool)
    (zzTableWriteAddr : Signal dom (BitVec 4))
    (zzTableWriteData : Signal dom (BitVec 16))
    : Signal dom (BitVec 64 × BitVec 32 × BitVec 32 × BitVec 32) :=
  let state := Signal.loop fun state =>
    let fsmState := CAVLCSynthState.fsmState state
    let scanIdx  := CAVLCSynthState.scanIdx state
    let totalCoeff := CAVLCSynthState.totalCoeff state
    let trailingOnes := CAVLCSynthState.trailingOnes state
    let totalZeros := CAVLCSynthState.totalZeros state
    let nzCount  := CAVLCSynthState.nzCount state
    let levelIdx := CAVLCSynthState.levelIdx state
    let runIdx   := CAVLCSynthState.runIdx state
    let zerosLeft := CAVLCSynthState.zerosLeft state
    let rbSubState := CAVLCSynthState.rbSubState state

    let isScan := fsmState === FSM_SCAN
    let isIdle := fsmState === FSM_IDLE
    let isEmitCT := fsmState === FSM_EMIT_CT
    let isEmitTZ := fsmState === FSM_EMIT_TZ
    let isRBInit := fsmState === FSM_RB_INIT
    let isEmitRB := fsmState === FSM_EMIT_RB
    let isLevelRead := fsmState === FSM_LEVEL_READ
    let isRBSub0 := rbSubState === 0#2

    -- === Memory 6: Zig-zag table (16×16-bit, combo-read, loaded by host) ===
    let zzReadAddr := scanIdx.map (BitVec.extractLsb' 0 4 ·)
    let zzData := Signal.memoryComboRead zzTableWriteAddr zzTableWriteData zzTableWriteEn zzReadAddr
    let zigzagAddr := zzData.map (BitVec.extractLsb' 0 4 ·)

    -- === Memory 0: Input coefficients (16×16-bit) ===
    -- Read address: zig-zag lookup during scan
    let coeffReadAddr := Signal.mux (isScan ||| (isIdle &&& start))
      zigzagAddr (Signal.pure 0#4)
    let coeffReadData := Signal.memoryComboRead coeffWriteAddr coeffWriteData coeffWriteEn coeffReadAddr

    -- === Memory 1: coeff_token VLC table (272×32-bit, 4 nC-range tables) ===
    -- Read address = nCBase + totalCoeff * 4 + trailingOnes (9-bit)
    -- nCBase = nCTableSelect * 68
    let nCSel9 := 0#7 ++ nCTableSelect
    let nCBase9 := nCSel9 * 68#9
    let tc9 := 0#4 ++ totalCoeff
    let t1_9 := 0#6 ++ trailingOnes
    let ctAddr := nCBase9 + ((tc9 + 4#9) * t1_9)
    let ctReadAddr := Signal.mux isEmitCT ctAddr (Signal.pure 0#9)
    let ctTableData := Signal.memoryComboRead ctTableWriteAddr ctTableWriteData ctTableWriteEn ctReadAddr

    -- === Memory 2: total_zeros VLC table (96×32-bit) ===
    -- Read address = (totalCoeff - 1) * 16 + totalZeros
    let tcMinus1 := totalCoeff - 1#5
    let tcm7 := 0#2 ++ tcMinus1
    let tz7 := 0#2 ++ totalZeros
    let tzAddr := (tcm7 + 16#7) * tz7
    let tzReadAddr := Signal.mux isEmitTZ tzAddr (Signal.pure 0#7)
    let tzTableData := Signal.memoryComboRead tzTableWriteAddr tzTableWriteData tzTableWriteEn tzReadAddr

    -- === Memory 3: run_before VLC table (49×32-bit) ===
    -- Read address = (zerosLeft - 1) * 7 + runBefore
    -- runBefore = curPos - prevPos - 1 (computed in body)
    let zlMinus1 := zerosLeft - 1#5
    let zlm6 := zlMinus1.map (BitVec.extractLsb' 0 6 ·)
    let curPos := CAVLCSynthState.curPos state
    let prevPos := CAVLCSynthState.prevPos state
    let runBefore := (prevPos - curPos) - 1#5
    let rb6 := runBefore.map (BitVec.extractLsb' 0 6 ·)
    let rbAddr := (zlm6 + 7#6) * rb6
    let rbReadAddr := Signal.mux isEmitRB rbAddr (Signal.pure 0#6)
    let rbTableData := Signal.memoryComboRead rbTableWriteAddr rbTableWriteData rbTableWriteEn rbReadAddr

    -- === Memory 4: Scanned non-zero levels (16×16-bit) ===
    -- Written during SCAN, read during EMIT_LEVEL
    let coeffIsNZ := ~~~(coeffReadData === 0#16)
    let scanNotDone := ~~~(scanIdx === 16#5)
    let scanNzDetect := isScan &&& coeffIsNZ &&& scanNotDone
    let levelWriteAddr := nzCount.map (BitVec.extractLsb' 0 4 ·)
    let levelReadIdx := Signal.mux isLevelRead
      (levelIdx.map (BitVec.extractLsb' 0 4 ·))
      (Signal.pure 0#4)
    let levelReadData := Signal.memoryComboRead levelWriteAddr coeffReadData scanNzDetect levelReadIdx

    -- === Memory 5: Scanned non-zero positions (16×16-bit, lower 5 bits used) ===
    -- Written during SCAN, read during EMIT_RB
    let scanPos16 := 0#11 ++ scanIdx
    let runIdx4 := runIdx.map (BitVec.extractLsb' 0 4 ·)
    let tcMinus1_4 := (totalCoeff - 1#5).map (BitVec.extractLsb' 0 4 ·)
    let runIdxMinus1_4 := (runIdx - 1#5).map (BitVec.extractLsb' 0 4 ·)
    let notRBSub0 := ~~~isRBSub0
    let posReadIdx := Signal.mux (isEmitRB &&& isRBSub0) runIdx4
      (Signal.mux isRBInit tcMinus1_4
        (Signal.mux (isEmitRB &&& notRBSub0) runIdxMinus1_4
          (Signal.pure 0#4)))
    let posReadData := Signal.memoryComboRead levelWriteAddr scanPos16 scanNzDetect posReadIdx

    cavlcSynthBody start coeffReadData ctTableData tzTableData rbTableData
      levelReadData posReadData state

  -- Extract outputs
  let bitBuffer := CAVLCSynthState.bitBuffer state
  let bitPos := CAVLCSynthState.bitPos state
  let done := CAVLCSynthState.done state
  let validOut := CAVLCSynthState.outValid state

  let bitPosU32 := 0#25 ++ bitPos
  let doneU32 := Signal.mux done (Signal.pure 1#32) (Signal.pure 0#32)
  let validU32 := Signal.mux validOut (Signal.pure 1#32) (Signal.pure 0#32)

  bundleAll! [bitBuffer, bitPosU32, doneU32, validU32]

-- ============================================================================
-- Generate SystemVerilog + CppSim + JIT
-- ============================================================================

#writeDesign cavlcSynthModule ".lake/build/gen/h264/cavlc_synth.sv" ".lake/build/gen/h264/cavlc_synth_cppsim.h"

end Sparkle.IP.Video.H264.CAVLCSynth
