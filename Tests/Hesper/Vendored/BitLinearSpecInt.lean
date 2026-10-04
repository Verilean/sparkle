/-
  Vendored from Verilean/hesper:Hesper/Layers/BitLinearSpec.lean.

  Source repo: https://github.com/Verilean/hesper
  Source file: Hesper/Layers/BitLinearSpec.lean (commit @ tip of master, 2026-05-05)
  License:     MIT

  ## Why vendored

  Hesper's full library pulls in a WebGPU + WGSL stack we don't need.
  We only want the BitLinear math model. Rather than depend on the
  whole framework, we copy the relevant defs here and **port `Float`
  to `Int`** so the equivalence proof against Sparkle's `BitVec`-based
  hardware lives in a clean integer setting.

  The Float ↔ Int bridge is closed separately in
  `Tests/Hesper/BitLinearEquivalence.lean` (Layer 2) via per-fixture
  `native_decide` — see `docs/Hesper_Equivalence.md`.

  ## What changes from upstream

    - `Float` → `Int` everywhere (decode result, accumulator, scale).
    - `Float.toFloat / 1.0` → integer arithmetic (codes 0,1,2 → -1,0,+1).
    - Otherwise the algorithm is byte-for-byte identical: same i2_s
      packing, same `byteOffset` arithmetic, same loop structure.
-/

namespace Sparkle.Tests.Hesper.Vendored.BitLinearSpecInt

/-- Decode a single ternary element from a packed i2_s byte array,
    returning an `Int` in `{-1, 0, +1}`. Mirrors Hesper's `decodeI2S`
    exactly except for the result type.

    `rowStartByte` is the byte offset where this output row starts
    (typically `outRow * inDim / 4`). `col` is the input-dim index
    within that row.

    Encoding:
      - Codes 0, 1, 2 ↔ ternary -1, 0, +1.
      - 4 codes per byte; 32 bytes per group-of-128 elements.
      - Within a group-of-128, the 4 sub-rows are at shifts 6, 4, 2, 0.
    See upstream `BitLinearSpec.lean` header for the full layout. -/
def decodeI2SInt (packed : ByteArray) (rowStartByte : Nat) (col : Nat) : Int :=
  let group128   := col / 128
  let colInGroup := col % 128
  let bytePos    := colInGroup % 32
  let shiftIdx   := colInGroup / 32
  let byteOffset := rowStartByte + group128 * 32 + bytePos
  if byteOffset < packed.size then
    let b      : UInt8 := packed.get! byteOffset
    let shift  : UInt8 := 6 - UInt8.ofNat (shiftIdx * 2)
    let code   : UInt8 := (b >>> shift) &&& 0x03
    (code.toNat : Int) - 1
  else
    0

/-- Single-row BitLinear forward, Int version of Hesper's `forwardRow`.
    `y[i] = scale * Σ_j W[i, j] * x[j]`. -/
def forwardRowInt (packed : ByteArray) (scale : Int) (inDim outDim : Nat)
    (input : Array Int) : Array Int := Id.run do
  let bytesPerRow := inDim / 4
  let mut out := Array.replicate outDim 0
  for i in [:outDim] do
    let rowStartByte := i * bytesPerRow
    let mut acc : Int := 0
    for j in [:inDim] do
      let w := decodeI2SInt packed rowStartByte j
      acc := acc + w * input.getD j 0
    out := out.set! i (scale * acc)
  pure out

/-- Pack an `Array Int` of ternary values into an i2_s `ByteArray`.
    Identical to Hesper's `packI2S` apart from the value-domain
    coercion (we accept the same `Array Int` either way). -/
def packI2SInt (ternary : Array Int) (inDim outDim : Nat) : ByteArray := Id.run do
  let bytesPerRow := inDim / 4
  let totalBytes  := outDim * bytesPerRow
  let mut bytes : ByteArray := ByteArray.mk (Array.replicate totalBytes 0)
  for i in [:outDim] do
    let rowStartByte := i * bytesPerRow
    for j in [:inDim] do
      let t := ternary.getD (i * inDim + j) 0
      let code : UInt8 :=
        if t == (-1 : Int) then 0
        else if t == 0 then 1
        else 2
      let group128   := j / 128
      let colInGroup := j % 128
      let bytePos    := colInGroup % 32
      let shiftIdx   := colInGroup / 32
      let byteOffset := rowStartByte + group128 * 32 + bytePos
      let shift   : UInt8 := 6 - UInt8.ofNat (shiftIdx * 2)
      let old     : UInt8 := bytes.get! byteOffset
      let mask    : UInt8 := (0x03 : UInt8) <<< shift
      let cleared : UInt8 := old &&& ((0xFF : UInt8) ^^^ mask)
      let merged  : UInt8 := cleared ||| (code <<< shift)
      bytes := bytes.set! byteOffset merged
  pure bytes

/-! ## Sanity checks (round-trip + small fixtures)

  Hesper's i2_s layout assumes groups of 128 elements packed into 32
  bytes (4 elements share one byte at shifts 6/4/2/0, where the four
  elements are 32 columns apart inside the group). Because of that,
  the minimum legal `inDim` for round-trip tests is **128**: smaller
  rows leave most elements on top of each other at `bytePos = j % 32`,
  `shiftIdx = j / 32 = 0`. We therefore test with `inDim = 128`. -/

/-- Build a deterministic `inDim = 128` ternary row pattern: the i-th
    element is `((i % 3) - 1)` (so the row is `-1, 0, 1, -1, 0, 1, …`). -/
def patternRow (n : Nat) : Array Int :=
  (Array.range n).map (fun i => ((i % 3 : Nat) : Int) - 1)

example : decodeI2SInt (packI2SInt (patternRow 128) 128 1) 0   0 = -1 := by native_decide
example : decodeI2SInt (packI2SInt (patternRow 128) 128 1) 0   1 =  0 := by native_decide
example : decodeI2SInt (packI2SInt (patternRow 128) 128 1) 0   2 =  1 := by native_decide
example : decodeI2SInt (packI2SInt (patternRow 128) 128 1) 0  31 =  0 := by native_decide
example : decodeI2SInt (packI2SInt (patternRow 128) 128 1) 0  32 =  1 := by native_decide
example : decodeI2SInt (packI2SInt (patternRow 128) 128 1) 0 127 =  0 := by native_decide

end Sparkle.Tests.Hesper.Vendored.BitLinearSpecInt
