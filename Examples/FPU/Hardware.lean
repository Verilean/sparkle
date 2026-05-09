-- =============================================================================
-- IEEE 754 Single-Precision Floating Point Arithmetic Unit
-- Sparkle Signal DSL Implementation (synthesizable to SystemVerilog)
-- =============================================================================

import Sparkle
import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Sparkle.Core.StateMacro
import Sparkle.Compiler.Elab

open Sparkle.Core.Signal
open Sparkle.Core.Domain

namespace FPU.Hardware

-- =========================================================================
-- Field Extraction as Signal Combinators
-- =========================================================================

/-- Extract sign bit from a 32-bit float signal -/
def signS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom (BitVec 1) :=
  (fun v => v.extractLsb' 31 1) <$> x

/-- Extract exponent field (bits 30:23) -/
def exponentS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom (BitVec 8) :=
  (fun v => v.extractLsb' 23 8) <$> x

/-- Extract mantissa field (bits 22:0) -/
def mantissaS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom (BitVec 23) :=
  (fun v => v.extractLsb' 0 23) <$> x

/-- Full mantissa with implicit leading 1 (24 bits) -/
def fullMantissaS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom (BitVec 24) :=
  (fun v =>
    let exp := v.extractLsb' 23 8
    let mant := v.extractLsb' 0 23
    if exp == 0#8 then (0#1 ++ mant) else (1#1 ++ mant)
  ) <$> x

-- =========================================================================
-- Special Value Detectors as Signals
-- =========================================================================

/-- Is the float signal zero? -/
def isZeroS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom Bool :=
  (fun v => v.extractLsb' 23 8 == 0#8 && v.extractLsb' 0 23 == 0#23) <$> x

/-- Is the float signal infinity? -/
def isInfS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom Bool :=
  (fun v => v.extractLsb' 23 8 == 255#8 && v.extractLsb' 0 23 == 0#23) <$> x

/-- Is the float signal NaN? -/
def isNaNS {dom : DomainConfig} (x : Signal dom (BitVec 32)) : Signal dom Bool :=
  (fun v => v.extractLsb' 23 8 == 255#8 && v.extractLsb' 0 23 != 0#23) <$> x

-- =========================================================================
-- Constants as Signals
-- =========================================================================

def posInfS {dom : DomainConfig} : Signal dom (BitVec 32) := Signal.pure 0x7F800000#32
def negInfS {dom : DomainConfig} : Signal dom (BitVec 32) := Signal.pure 0xFF800000#32
def qNaNC   {dom : DomainConfig} : Signal dom (BitVec 32) := Signal.pure 0x7FC00000#32
def posZeroS {dom : DomainConfig} : Signal dom (BitVec 32) := Signal.pure 0x00000000#32

-- =========================================================================
-- Pack combinator
-- =========================================================================

/-- Pack sign, exponent, mantissa signals into a 32-bit float signal -/
def packS {dom : DomainConfig}
    (s : Signal dom (BitVec 1))
    (e : Signal dom (BitVec 8))
    (m : Signal dom (BitVec 23)) : Signal dom (BitVec 32) :=
  (fun sv ev mv => sv ++ ev ++ mv) <$> s <*> e <*> m

-- =========================================================================
-- FP Addition/Subtraction (3-stage pipeline using Signal.loop)
-- =========================================================================

-- State for the add/sub pipeline
-- We use a flat tuple for Signal.loop compatibility

/-- Combinational FP add/sub core (pure function lifted into Signal) -/
def fpAddSubComb (a b : BitVec 32) (isSub : Bool) : BitVec 32 :=
  let signA := a.extractLsb' 31 1
  let signB_raw := b.extractLsb' 31 1
  -- Flip B's sign for subtraction
  let signB := if isSub then ~~~signB_raw else signB_raw

  let expA  := a.extractLsb' 23 8
  let expB  := b.extractLsb' 23 8
  let mantA := if expA == 0#8 then (0#1 ++ a.extractLsb' 0 23) else (1#1 ++ a.extractLsb' 0 23)
  let mantB := if expB == 0#8 then (0#1 ++ b.extractLsb' 0 23) else (1#1 ++ b.extractLsb' 0 23)

  -- Special cases
  let aNaN  := expA == 255#8 && a.extractLsb' 0 23 != 0#23
  let bNaN  := expB == 255#8 && b.extractLsb' 0 23 != 0#23
  let aInf  := expA == 255#8 && a.extractLsb' 0 23 == 0#23
  let bInf  := expB == 255#8 && b.extractLsb' 0 23 == 0#23
  let aZero := expA == 0#8 && a.extractLsb' 0 23 == 0#23
  let bZero := expB == 0#8 && b.extractLsb' 0 23 == 0#23

  if aNaN || bNaN then 0x7FC00000#32
  else if aInf && bInf then
    if signA == signB then
      if signA == 1#1 then 0xFF800000#32 else 0x7F800000#32
    else 0x7FC00000#32  -- Inf - Inf = NaN
  else if aInf then
    if signA == 1#1 then 0xFF800000#32 else 0x7F800000#32
  else if bInf then
    if signB == 1#1 then 0xFF800000#32 else 0x7F800000#32
  else if aZero && bZero then
    if signA == 1#1 && signB == 1#1 then 0x80000000#32 else 0x00000000#32
  else if aZero then
    -- Return b with potentially flipped sign
    if isSub then ~~~signB_raw ++ expB ++ b.extractLsb' 0 23
    else b
  else if bZero then a
  else
    -- General aligned addition
    -- Extend mantissas to 27 bits (24 + 3 guard/round/sticky)
    let mantAExt : BitVec 27 := (mantA ++ (0#3 : BitVec 3))
    let mantBExt : BitVec 27 := (mantB ++ (0#3 : BitVec 3))

    -- Align exponents
    let (alignedA, alignedB, commonExp) :=
      if expA.toNat >= expB.toNat then
        let diff := expA.toNat - expB.toNat
        let shifted := if diff >= 27 then 0#27 else mantBExt >>> diff
        (mantAExt, shifted, expA)
      else
        let diff := expB.toNat - expA.toNat
        let shifted := if diff >= 27 then 0#27 else mantAExt >>> diff
        (shifted, mantBExt, expB)

    -- Add or subtract based on effective sign
    let (resultMant, resultSign) :=
      if signA == signB then
        -- Same sign: add mantissas
        let sum : BitVec 28 := (0#1 ++ alignedA) + (0#1 ++ alignedB)
        (sum, signA)
      else
        -- Different signs: subtract
        if alignedA.toNat >= alignedB.toNat then
          let diff : BitVec 28 := (0#1 ++ alignedA) - (0#1 ++ alignedB)
          (diff, signA)
        else
          let diff : BitVec 28 := (0#1 ++ alignedB) - (0#1 ++ alignedA)
          (diff, signB)

    -- Normalize
    if resultMant == 0#28 then
      0x00000000#32  -- Result is zero
    else
      -- Simple normalization: find leading 1
      let (normMant, normExp) :=
        if resultMant.extractLsb' 27 1 == 1#1 then
          -- Overflow: shift right
          (resultMant >>> 1, commonExp.toNat + 1)
        else
          -- Find leading 1 and shift left
          let lzc := -- Count leading zeros (simplified for key cases)
            if resultMant.extractLsb' 26 1 == 1#1 then 0
            else if resultMant.extractLsb' 25 1 == 1#1 then 1
            else if resultMant.extractLsb' 24 1 == 1#1 then 2
            else if resultMant.extractLsb' 23 1 == 1#1 then 3
            else if resultMant.extractLsb' 22 1 == 1#1 then 4
            else if resultMant.extractLsb' 21 1 == 1#1 then 5
            else if resultMant.extractLsb' 20 1 == 1#1 then 6
            else 7  -- Simplified; full impl uses priority encoder
          if lzc > commonExp.toNat then
            (resultMant <<< commonExp.toNat, 0)
          else
            (resultMant <<< lzc, commonExp.toNat - lzc)
      -- Round (round to nearest even)
      let guard  := normMant.extractLsb' 2 1
      let round  := normMant.extractLsb' 1 1
      let sticky := normMant.extractLsb' 0 1
      let rawMant := normMant.extractLsb' 3 23
      let roundUp := guard == 1#1 && (round == 1#1 || sticky == 1#1 || rawMant.extractLsb' 0 1 == 1#1)
      let roundedMant := if roundUp then rawMant.toNat + 1 else rawMant.toNat

      -- Check for exponent overflow/underflow
      if normExp >= 255 then
        if resultSign == 1#1 then 0xFF800000#32 else 0x7F800000#32  -- Overflow → Inf
      else if normExp == 0 then
        0x00000000#32  -- Underflow → zero (simplified)
      else
        let finalMant : BitVec 23 := BitVec.ofNat 23 (roundedMant % (2^23))
        let finalExp  : BitVec 8  := BitVec.ofNat 8 normExp
        resultSign ++ finalExp ++ finalMant

/-- FP Add/Sub as a Signal combinator (single-cycle combinational) -/
def fpAddSubS {dom : DomainConfig}
    (a b : Signal dom (BitVec 32))
    (isSub : Signal dom Bool) : Signal dom (BitVec 32) :=
  (fun av bv isSubV => fpAddSubComb av bv isSubV) <$> a <*> b <*> isSub

/-- FP Add/Sub with pipeline registers (3-stage) -/
def fpAddSubPipelined {dom : DomainConfig}
    (a b : Signal dom (BitVec 32))
    (isSub : Signal dom Bool) : Signal dom (BitVec 32) :=
  -- Stage 0 → Stage 1 register
  let stage0Result := fpAddSubS a b isSub
  let stage1 := Signal.register 0#32 stage0Result
  -- Stage 1 → Stage 2 register
  let stage2 := Signal.register 0#32 stage1
  -- Stage 2 → Output register
  Signal.register 0#32 stage2

-- =========================================================================
-- FP Multiplication
-- =========================================================================

/-- Combinational FP multiplication core -/
def fpMulComb (a b : BitVec 32) : BitVec 32 :=
  let signA := a.extractLsb' 31 1
  let signB := b.extractLsb' 31 1
  let expA  := a.extractLsb' 23 8
  let expB  := b.extractLsb' 23 8
  let mantA := if expA == 0#8 then (0#1 ++ a.extractLsb' 0 23) else (1#1 ++ a.extractLsb' 0 23)
  let mantB := if expB == 0#8 then (0#1 ++ b.extractLsb' 0 23) else (1#1 ++ b.extractLsb' 0 23)
  let resultSign := signA ^^^ signB

  -- Special cases
  let aNaN  := expA == 255#8 && a.extractLsb' 0 23 != 0#23
  let bNaN  := expB == 255#8 && b.extractLsb' 0 23 != 0#23
  let aInf  := expA == 255#8 && a.extractLsb' 0 23 == 0#23
  let bInf  := expB == 255#8 && b.extractLsb' 0 23 == 0#23
  let aZero := expA == 0#8 && a.extractLsb' 0 23 == 0#23
  let bZero := expB == 0#8 && b.extractLsb' 0 23 == 0#23

  if aNaN || bNaN then 0x7FC00000#32
  else if (aInf && bZero) || (bInf && aZero) then 0x7FC00000#32
  else if aInf || bInf then
    if resultSign == 1#1 then 0xFF800000#32 else 0x7F800000#32
  else if aZero || bZero then
    if resultSign == 1#1 then 0x80000000#32 else 0x00000000#32
  else
    -- General multiplication: mantissa product
    let product : Nat := mantA.toNat * mantB.toNat  -- 24×24 = up to 48 bits

    -- Biased exponent calculation: (expA - 127) + (expB - 127) + 127 = expA + expB - 127
    let rawExp : Int := expA.toNat + expB.toNat - 127

    -- Normalize: product is in range [2^46, 2^48)
    -- If bit 47 is set, shift right; otherwise use as-is
    let (normProduct, normExp) :=
      if product >= (2^47 : Nat) then
        (product / 2, rawExp + 1)
      else
        (product, rawExp)

    -- Extract mantissa (bits 46:24 of normalized product) and round
    let rawMant := (normProduct / (2^23)) % (2^23)
    let guard   := (normProduct / (2^22)) % 2
    let round   := (normProduct / (2^21)) % 2
    let sticky  := if normProduct % (2^21) != 0 then 1 else 0

    let roundUp := guard == 1 && (round == 1 || sticky == 1 || rawMant % 2 == 1)
    let roundedMant := if roundUp then rawMant + 1 else rawMant

    -- Handle rounding overflow
    let (finalMant, finalExp) :=
      if roundedMant >= (2^23 : Nat) then
        (roundedMant / 2, normExp + 1)
      else
        (roundedMant, normExp)

    if finalExp >= 255 then
      if resultSign == 1#1 then 0xFF800000#32 else 0x7F800000#32
    else if finalExp <= 0 then
      if resultSign == 1#1 then 0x80000000#32 else 0x00000000#32
    else
      let mant23 : BitVec 23 := BitVec.ofNat 23 (finalMant % (2^23))
      let exp8   : BitVec 8  := BitVec.ofNat 8 finalExp.toNat
      resultSign ++ exp8 ++ mant23

/-- FP Multiply as a Signal combinator -/
def fpMulS {dom : DomainConfig}
    (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  (fun av bv => fpMulComb av bv) <$> a <*> b

/-- FP Multiply with pipeline registers (3-stage) -/
def fpMulPipelined {dom : DomainConfig}
    (a b : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let stage0Result := fpMulS a b
  let stage1 := Signal.register 0#32 stage0Result
  let stage2 := Signal.register 0#32 stage1
  Signal.register 0#32 stage2

-- =========================================================================
-- Top-Level FPU (2-bit op select: 00=ADD, 01=SUB, 10=MUL)
-- =========================================================================

/-- Top-level FPU: selects between add, sub, mul based on op code -/
def fpu {dom : DomainConfig}
    (a b : Signal dom (BitVec 32))
    (op  : Signal dom (BitVec 2)) : Signal dom (BitVec 32) :=
  let isSub := op === 1#2
  --let isAdd := op === 0#2
  --let isMul := op === 2#2

  let addSubResult := fpAddSubPipelined a b isSub
  let mulResult    := fpMulPipelined a b

  -- Output mux: select result based on registered op code
  let opDelayed := Signal.register 0#2 (Signal.register 0#2 (Signal.register 0#2 op))

  let selectMul := opDelayed === 2#2

  Signal.mux selectMul mulResult addSubResult

-- =========================================================================
-- Verilog Generation
-- =========================================================================

-- Uncomment to generate SystemVerilog:
-- #synthesizeVerilog fpu

end FPU.Hardware
