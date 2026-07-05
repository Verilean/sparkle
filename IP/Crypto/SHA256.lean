/-
  IP.Crypto.SHA256 — FIPS 180-4 SHA-256.

  This file lands the **pure-data SHA-256 algorithm** in
  Lean, validated against NIST test vectors at sim time.
  The Signal-side hardware engine (iterative 64-cycle
  compressor with a 64×32-bit message-schedule register
  file) follows in Phase L.1.b — but having the pure-data
  reference here gives Ed25519 / secp256k1 / HMAC-SHA256 a
  callable hash to wire into their own sim tests in the
  meantime, and provides the spec the HW engine will be
  cross-checked against.

  Layout (per FIPS 180-4 §6.2):
    * 8 working-state words a..h (each 32 bits)
    * 64 round constants K[t]
    * 64 message-schedule words W[t]: first 16 come from
      the input block (512-bit message block = 16 ×
      32-bit), rest computed via the schedule recurrence.

  Per-round update (t = 0..63):
    T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]
    T2 = Σ₀(a) + Maj(a,b,c)
    (a, b, c, d, e, f, g, h) :=
      (T1 + T2, a, b, c, d + T1, e, f, g)

  Helpers:
    Ch(x,y,z)  = (x ∧ y) ⊕ (¬x ∧ z)
    Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)
    Σ₀(x) = ROTR(x, 2) ⊕ ROTR(x, 13) ⊕ ROTR(x, 22)
    Σ₁(x) = ROTR(x, 6) ⊕ ROTR(x, 11) ⊕ ROTR(x, 25)
    σ₀(x) = ROTR(x, 7) ⊕ ROTR(x, 18) ⊕ SHR(x, 3)
    σ₁(x) = ROTR(x, 17) ⊕ ROTR(x, 19) ⊕ SHR(x, 10)
-/

import Sparkle
import Sparkle.Core.Lut

open Sparkle.Core (kLutMacro)

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Crypto.SHA256

/-! ### Pure-data helpers. -/

/-- 32-bit rotate-right: ROTR(x, n) = (x >>> n) | (x <<< (32-n)). -/
@[inline] def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> (BitVec.ofNat 32 n)) ||| (x <<< (BitVec.ofNat 32 (32 - n)))

@[inline] def shr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  x >>> (BitVec.ofNat 32 n)

@[inline] def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 2) ^^^ (rotr32 x 13) ^^^ (rotr32 x 22)

@[inline] def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 6) ^^^ (rotr32 x 11) ^^^ (rotr32 x 25)

@[inline] def smallSigma0 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 7) ^^^ (rotr32 x 18) ^^^ (shr32 x 3)

@[inline] def smallSigma1 (x : BitVec 32) : BitVec 32 :=
  (rotr32 x 17) ^^^ (rotr32 x 19) ^^^ (shr32 x 10)

@[inline] def chFn (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

@[inline] def majFn (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-! ### K table — 64 round constants. -/

def kTable : Array (BitVec 32) := #[
  0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
  0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
  0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
  0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
  0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
  0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
  0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
  0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
  0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
  0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
  0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
  0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
  0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
  0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
  0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
  0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32
]

/-- Initial hash values H0..H7 (FIPS 180-4 §5.3.3). -/
def initH : Array (BitVec 32) := #[
  0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
  0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32
]

/-! ### Pure-data single-block compression. -/

/-- Compute W[t] (t = 0..63) given an array of 16 input
    32-bit words. -/
def expandW (block : Array (BitVec 32)) : Array (BitVec 32) := Id.run do
  let mut w : Array (BitVec 32) := Array.replicate 64 (0#32)
  for i in [:16] do
    w := w.set! i (block.getD i 0#32)
  for i in [16:64] do
    let s0 := smallSigma0 (w.getD (i - 15) 0#32)
    let s1 := smallSigma1 (w.getD (i - 2) 0#32)
    let v := s1 + w.getD (i - 7) 0#32 + s0 + w.getD (i - 16) 0#32
    w := w.set! i v
  return w

/-- Pure-data SHA-256 single-block compression.  Takes
    initial state H (8 words) and a 16-word message block,
    returns the post-compression state. -/
def compressBlock (h : Array (BitVec 32)) (block : Array (BitVec 32)) :
    Array (BitVec 32) := Id.run do
  let w := expandW block
  let mut a := h.getD 0 0#32
  let mut b := h.getD 1 0#32
  let mut c := h.getD 2 0#32
  let mut d := h.getD 3 0#32
  let mut e := h.getD 4 0#32
  let mut f := h.getD 5 0#32
  let mut g := h.getD 6 0#32
  let mut hh := h.getD 7 0#32
  for t in [:64] do
    let t1 := hh + bigSigma1 e + chFn e f g + kTable.getD t 0#32 + w.getD t 0#32
    let t2 := bigSigma0 a + majFn a b c
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h.getD 0 0#32 + a, h.getD 1 0#32 + b, h.getD 2 0#32 + c, h.getD 3 0#32 + d,
           h.getD 4 0#32 + e, h.getD 5 0#32 + f, h.getD 6 0#32 + g, h.getD 7 0#32 + hh]

/-- Pure-data SHA-256 of a list of pre-padded message
    blocks.  Each block is a 16-word array.  Padding is
    the caller's responsibility for now (FIPS 180-4 §5.1.1
    — append 1 bit + zeros + 64-bit length). -/
def hashBlocks (blocks : List (Array (BitVec 32))) : Array (BitVec 32) :=
  blocks.foldl compressBlock initH

/-- Pure-data SHA-256 of a byte array.  Performs the
    FIPS 180-4 padding internally. -/
def sha256OfBytes (input : Array UInt8) : Array (BitVec 32) := Id.run do
  -- Append 0x80, then zeros, then 64-bit length (in bits).
  let bitLen : Nat := input.size * 8
  let mut lenBytes : Array UInt8 := #[]
  for i in [:8] do
    let shift := (7 - i) * 8
    let byte := (bitLen >>> shift) &&& 0xFF
    lenBytes := lenBytes.push (UInt8.ofNat byte)
  -- Append 0x80 + as many zero bytes as needed so total
  -- (input + 0x80 + zeros + 8 length-bytes) is a multiple
  -- of 64.
  let mut padded : Array UInt8 := input
  padded := padded.push 0x80
  while padded.size % 64 ≠ 56 do
    padded := padded.push 0x00
  for b in lenBytes do
    padded := padded.push b
  -- Convert padded to 16-word blocks.
  let nBlocks := padded.size / 64
  let mut blocks : List (Array (BitVec 32)) := []
  for blk in [:nBlocks] do
    let mut words : Array (BitVec 32) := #[]
    for i in [:16] do
      let off := blk * 64 + i * 4
      let w0 := (padded.getD off 0).toNat
      let w1 := (padded.getD (off + 1) 0).toNat
      let w2 := (padded.getD (off + 2) 0).toNat
      let w3 := (padded.getD (off + 3) 0).toNat
      let word : Nat := (w0 <<< 24) ||| (w1 <<< 16) ||| (w2 <<< 8) ||| w3
      words := words.push (BitVec.ofNat 32 word)
    blocks := blocks ++ [words]
  return hashBlocks blocks

/-! ### Signal-side helpers — Sparkle-synth-friendly. -/

/-- Signal-side 32-bit rotate-right by a compile-time
    constant `n`.  Built from `>>>` and `<<<` over 32-bit
    BitVec constants, both recognised by Sparkle's IR
    elaborator. -/
@[inline] def rotr32Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 32)) (n : Nat) :
    Signal dom (BitVec 32) :=
  let nBv  : BitVec 32 := BitVec.ofNat 32 n
  let nBv' : BitVec 32 := BitVec.ofNat 32 (32 - n)
  -- (x >>> n) ||| (x <<< (32 - n))
  let pn  : Signal dom (BitVec 32) := Signal.pure nBv
  let pn' : Signal dom (BitVec 32) := Signal.pure nBv'
  let rs : Signal dom (BitVec 32) := (· >>> ·) <$> x <*> pn
  let ls : Signal dom (BitVec 32) := (· <<< ·) <$> x <*> pn'
  (· ||| ·) <$> rs <*> ls

@[inline] def shr32Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 32)) (n : Nat) :
    Signal dom (BitVec 32) :=
  let nBv : BitVec 32 := BitVec.ofNat 32 n
  let pn : Signal dom (BitVec 32) := Signal.pure nBv
  (· >>> ·) <$> x <*> pn

@[inline] def bigSigma0Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let a := rotr32Sig x 2
  let b := rotr32Sig x 13
  let c := rotr32Sig x 22
  let ab := (· ^^^ ·) <$> a <*> b
  (· ^^^ ·) <$> ab <*> c

@[inline] def bigSigma1Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let a := rotr32Sig x 6
  let b := rotr32Sig x 11
  let c := rotr32Sig x 25
  let ab := (· ^^^ ·) <$> a <*> b
  (· ^^^ ·) <$> ab <*> c

@[inline] def smallSigma0Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let a := rotr32Sig x 7
  let b := rotr32Sig x 18
  let c := shr32Sig x 3
  let ab := (· ^^^ ·) <$> a <*> b
  (· ^^^ ·) <$> ab <*> c

@[inline] def smallSigma1Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let a := rotr32Sig x 17
  let b := rotr32Sig x 19
  let c := shr32Sig x 10
  let ab := (· ^^^ ·) <$> a <*> b
  (· ^^^ ·) <$> ab <*> c

@[inline] def chFnSig {dom : DomainConfig}
    (x y z : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let xy   : Signal dom (BitVec 32) := (· &&& ·) <$> x <*> y
  let nx   : Signal dom (BitVec 32) := (~~~ ·) <$> x
  let nxz  : Signal dom (BitVec 32) := (· &&& ·) <$> nx <*> z
  (· ^^^ ·) <$> xy <*> nxz

@[inline] def majFnSig {dom : DomainConfig}
    (x y z : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let xy  : Signal dom (BitVec 32) := (· &&& ·) <$> x <*> y
  let xz  : Signal dom (BitVec 32) := (· &&& ·) <$> x <*> z
  let yz  : Signal dom (BitVec 32) := (· &&& ·) <$> y <*> z
  let t1  : Signal dom (BitVec 32) := (· ^^^ ·) <$> xy <*> xz
  (· ^^^ ·) <$> t1 <*> yz

/-! ### K-table mux: pick K[t] from a 7-bit counter. -/

@[hardware_module] def kMux {dom : DomainConfig}
    (cntSig : Signal dom (BitVec 7)) : Signal dom (BitVec 32) :=
  -- Use the `kLut!` macro to expand a 64-way constant-table
  -- mux into a fully-unrolled `Signal.mux` chain at term-
  -- elab time.  An `Id.run do`-based loop here would have
  -- left a `let mut` Lean expression the IR elaborator
  -- can't unfold ("Cannot synthesise Id.run").  See
  -- `Sparkle/Core/Lut.lean` for the macro definition.
  kLut! cntSig [
    Signal.pure 0x428a2f98#32, Signal.pure 0x71374491#32, Signal.pure 0xb5c0fbcf#32, Signal.pure 0xe9b5dba5#32,
    Signal.pure 0x3956c25b#32, Signal.pure 0x59f111f1#32, Signal.pure 0x923f82a4#32, Signal.pure 0xab1c5ed5#32,
    Signal.pure 0xd807aa98#32, Signal.pure 0x12835b01#32, Signal.pure 0x243185be#32, Signal.pure 0x550c7dc3#32,
    Signal.pure 0x72be5d74#32, Signal.pure 0x80deb1fe#32, Signal.pure 0x9bdc06a7#32, Signal.pure 0xc19bf174#32,
    Signal.pure 0xe49b69c1#32, Signal.pure 0xefbe4786#32, Signal.pure 0x0fc19dc6#32, Signal.pure 0x240ca1cc#32,
    Signal.pure 0x2de92c6f#32, Signal.pure 0x4a7484aa#32, Signal.pure 0x5cb0a9dc#32, Signal.pure 0x76f988da#32,
    Signal.pure 0x983e5152#32, Signal.pure 0xa831c66d#32, Signal.pure 0xb00327c8#32, Signal.pure 0xbf597fc7#32,
    Signal.pure 0xc6e00bf3#32, Signal.pure 0xd5a79147#32, Signal.pure 0x06ca6351#32, Signal.pure 0x14292967#32,
    Signal.pure 0x27b70a85#32, Signal.pure 0x2e1b2138#32, Signal.pure 0x4d2c6dfc#32, Signal.pure 0x53380d13#32,
    Signal.pure 0x650a7354#32, Signal.pure 0x766a0abb#32, Signal.pure 0x81c2c92e#32, Signal.pure 0x92722c85#32,
    Signal.pure 0xa2bfe8a1#32, Signal.pure 0xa81a664b#32, Signal.pure 0xc24b8b70#32, Signal.pure 0xc76c51a3#32,
    Signal.pure 0xd192e819#32, Signal.pure 0xd6990624#32, Signal.pure 0xf40e3585#32, Signal.pure 0x106aa070#32,
    Signal.pure 0x19a4c116#32, Signal.pure 0x1e376c08#32, Signal.pure 0x2748774c#32, Signal.pure 0x34b0bcb5#32,
    Signal.pure 0x391c0cb3#32, Signal.pure 0x4ed8aa4a#32, Signal.pure 0x5b9cca4f#32, Signal.pure 0x682e6ff3#32,
    Signal.pure 0x748f82ee#32, Signal.pure 0x78a5636f#32, Signal.pure 0x84c87814#32, Signal.pure 0x8cc70208#32,
    Signal.pure 0x90befffa#32, Signal.pure 0xa4506ceb#32, Signal.pure 0xbef9a3f7#32, Signal.pure 0xc67178f2#32
  ]

/-! ### SHA-256 HW engine — iterative 64-cycle compressor.

    Pipeline contract:
      cycle 0     : `start` pulse; `blockIn` carries the
                    full 512-bit message block (W0 in MSB).
      cycle 1..64 : compression round t = 0..63, fed by the
                    rolling 16-word W buffer.
      cycle 65    : add a..h into H0..H7 and pulse `done`.
      cycle ≥66   : output `hash` holds the final 256-bit
                    digest; `done` returns to 0.

    Buffer strategy: keep a single 512-bit register
    representing W[t-16..t-1] (MSB = oldest = W[t-16],
    LSB = newest = W[t-1]).  Each cycle:
      - Read W[t] from the MSB position (or from the new
        slot for t < 16: directly from `blockIn[t]`).
      - Compute next W (only used for t < 48 since the
        last 16 rounds don't generate new W values, but
        the shift is harmless).
      - Shift the buffer left by 32 bits, place new W in
        the low 32 bits. -/

structure SHA256Out (dom : DomainConfig) where
  /-- 256-bit packed hash output (H0 in MSB). -/
  hash : Signal dom (BitVec 256)
  /-- Pulses high for one cycle after the 64-round
      compression completes. -/
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SHA256Out dom) dom := ⟨⟩

def sha256Block {dom : DomainConfig}
    (start : Signal dom Bool)
    (blockIn : Signal dom (BitVec 512))
    (first : Signal dom Bool := Signal.pure true) :
    SHA256Out dom :=
  circuit do
    -- 7-bit round counter (0..65, plus idle at 0).
    let cnt ← Signal.reg (0#7)
    -- 8 working-state registers — initialised to initH on
    -- the start pulse.
    let aR ← Signal.reg (0#32)
    let bR ← Signal.reg (0#32)
    let cR ← Signal.reg (0#32)
    let dR ← Signal.reg (0#32)
    let eR ← Signal.reg (0#32)
    let fR ← Signal.reg (0#32)
    let gR ← Signal.reg (0#32)
    let hR ← Signal.reg (0#32)
    -- 8 final-hash registers (carry IV plus accumulated
    -- block deltas).
    let h0R ← Signal.reg (0x6a09e667#32)
    let h1R ← Signal.reg (0xbb67ae85#32)
    let h2R ← Signal.reg (0x3c6ef372#32)
    let h3R ← Signal.reg (0xa54ff53a#32)
    let h4R ← Signal.reg (0x510e527f#32)
    let h5R ← Signal.reg (0x9b05688c#32)
    let h6R ← Signal.reg (0x1f83d9ab#32)
    let h7R ← Signal.reg (0x5be0cd19#32)
    -- W-buffer: 16 × 32-bit slots, MSB = oldest.
    let wBuf ← Signal.reg (0#512)
    -- `done` strobe.
    let doneR ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 7))
    let aSig := (aR : Signal dom (BitVec 32))
    let bSig := (bR : Signal dom (BitVec 32))
    let cSig := (cR : Signal dom (BitVec 32))
    let dSig := (dR : Signal dom (BitVec 32))
    let eSig := (eR : Signal dom (BitVec 32))
    let fSig := (fR : Signal dom (BitVec 32))
    let gSig := (gR : Signal dom (BitVec 32))
    let hSig := (hR : Signal dom (BitVec 32))
    let h0Sig := (h0R : Signal dom (BitVec 32))
    let h1Sig := (h1R : Signal dom (BitVec 32))
    let h2Sig := (h2R : Signal dom (BitVec 32))
    let h3Sig := (h3R : Signal dom (BitVec 32))
    let h4Sig := (h4R : Signal dom (BitVec 32))
    let h5Sig := (h5R : Signal dom (BitVec 32))
    let h6Sig := (h6R : Signal dom (BitVec 32))
    let h7Sig := (h7R : Signal dom (BitVec 32))
    let wBufSig := (wBuf : Signal dom (BitVec 512))

    -- W-buffer layout: 16 slots × 32 bits = 512 bits.
    -- slot k = bits [ (15-k)*32 .. (16-k)*32 - 1 ] from LSB.
    -- So slot 0 occupies the TOP 32 bits (high end of the
    -- 512-bit reg), slot 15 the BOTTOM 32 bits.
    --
    -- Convention while running round t (using the original
    -- FIPS naming where we're computing W[t+16] from W[t]..
    -- W[t+15] still in the buffer):
    --   slot 0  = W[t]      ← consumed this round as W input
    --   slot 1  = W[t+1]    = W[(t+16)-15]   for σ₀
    --   slot 9  = W[t+9]    = W[(t+16)-7]    direct addend
    --   slot 14 = W[t+14]   = W[(t+16)-2]    for σ₁
    --   slot 15 = W[t+15]   = W[(t+16)-1]    (unused)
    -- SHA-256 bit functions are FULLY INLINED at their call sites
    -- below.  A named top-level `Signal → Signal` def (`rotr32Sig`,
    -- `bigSigma1Sig`, …) is opaque to the synth elaborator
    -- ("not inlinable"), AND wrapping the applicative body in a
    -- local `let f := fun x => …` lambda that RETURNS a `<$>/<*>`
    -- chain also fails ("Cannot instantiate Seq.seq") — the
    -- elaborator only lowers applicative expressions written
    -- directly, not returned from a lambda.  So each Σ/σ/Ch/Maj is
    -- spelled out inline where it is consumed (see `sig1`, `sig0`,
    -- `chv`, `majv`, `newW1`, `newW2`).  `rotrK x n` and `shrK x n`
    -- macros would help but the elaborator needs the literal form.

    -- Convert "slot k" → `BitVec.extractLsb' ((15-k)*32) 32`.
    let wt    := wBufSig.map (BitVec.extractLsb' 480 32 ·)  -- slot 0
    let wTm15 := wBufSig.map (BitVec.extractLsb' 448 32 ·)  -- slot 1
    let wTm7  := wBufSig.map (BitVec.extractLsb' 192 32 ·)  -- slot 9
    let wTm2  := wBufSig.map (BitVec.extractLsb'  32 32 ·)  -- slot 14
    let wTm16 := wt  -- alias for clarity in the recurrence

    -- Round-counter predicates.
    let p0_7   := (Signal.pure 0#7  : Signal dom (BitVec 7))
    let p1_7   := (Signal.pure 1#7  : Signal dom (BitVec 7))
    let p65_7  := (Signal.pure 65#7 : Signal dom (BitVec 7))
    let isIdle   := (· == ·) <$> cntSig <*> p0_7
    let isFinish := (· == ·) <$> cntSig <*> p65_7

    -- Compute T1, T2, next-state.  Round t runs at cnt = t+1 (cnt 1..64), so
    -- the round constant is K[cnt-1] — feed cnt-1 (NOT cnt) to the K table.
    let kt    := kMux ((· - ·) <$> cntSig <*> (Signal.pure 1#7 : Signal dom (BitVec 7)))
    -- Σ₁(e) = ROTR(e,6) ⊕ ROTR(e,11) ⊕ ROTR(e,25), inlined.
    let e6  := ((· >>> ·) <$> eSig <*> (Signal.pure 6#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let e6l := ((· <<< ·) <$> eSig <*> (Signal.pure 26#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let rE6 := ((· ||| ·) <$> e6 <*> e6l : Signal dom (BitVec 32))
    let e11  := ((· >>> ·) <$> eSig <*> (Signal.pure 11#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let e11l := ((· <<< ·) <$> eSig <*> (Signal.pure 21#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let rE11 := ((· ||| ·) <$> e11 <*> e11l : Signal dom (BitVec 32))
    let e25  := ((· >>> ·) <$> eSig <*> (Signal.pure 25#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let e25l := ((· <<< ·) <$> eSig <*> (Signal.pure 7#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let rE25 := ((· ||| ·) <$> e25 <*> e25l : Signal dom (BitVec 32))
    let sig1ab := ((· ^^^ ·) <$> rE6 <*> rE11 : Signal dom (BitVec 32))
    let sig1  := ((· ^^^ ·) <$> sig1ab <*> rE25 : Signal dom (BitVec 32))
    -- Σ₀(a) = ROTR(a,2) ⊕ ROTR(a,13) ⊕ ROTR(a,22), inlined.
    let a2  := ((· >>> ·) <$> aSig <*> (Signal.pure 2#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let a2l := ((· <<< ·) <$> aSig <*> (Signal.pure 30#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let rA2 := ((· ||| ·) <$> a2 <*> a2l : Signal dom (BitVec 32))
    let a13  := ((· >>> ·) <$> aSig <*> (Signal.pure 13#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let a13l := ((· <<< ·) <$> aSig <*> (Signal.pure 19#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let rA13 := ((· ||| ·) <$> a13 <*> a13l : Signal dom (BitVec 32))
    let a22  := ((· >>> ·) <$> aSig <*> (Signal.pure 22#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let a22l := ((· <<< ·) <$> aSig <*> (Signal.pure 10#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let rA22 := ((· ||| ·) <$> a22 <*> a22l : Signal dom (BitVec 32))
    let sig0ab := ((· ^^^ ·) <$> rA2 <*> rA13 : Signal dom (BitVec 32))
    let sig0  := ((· ^^^ ·) <$> sig0ab <*> rA22 : Signal dom (BitVec 32))
    -- Ch(e,f,g) = (e ∧ f) ⊕ (¬e ∧ g), inlined.
    let chXy  := ((· &&& ·) <$> eSig <*> fSig : Signal dom (BitVec 32))
    let chNx  := ((~~~ ·) <$> eSig : Signal dom (BitVec 32))
    let chNxz := ((· &&& ·) <$> chNx <*> gSig : Signal dom (BitVec 32))
    let chv   := ((· ^^^ ·) <$> chXy <*> chNxz : Signal dom (BitVec 32))
    -- Maj(a,b,c) = (a∧b) ⊕ (a∧c) ⊕ (b∧c), inlined.
    let mjXy := ((· &&& ·) <$> aSig <*> bSig : Signal dom (BitVec 32))
    let mjXz := ((· &&& ·) <$> aSig <*> cSig : Signal dom (BitVec 32))
    let mjYz := ((· &&& ·) <$> bSig <*> cSig : Signal dom (BitVec 32))
    let mjT1 := ((· ^^^ ·) <$> mjXy <*> mjXz : Signal dom (BitVec 32))
    let majv  := ((· ^^^ ·) <$> mjT1 <*> mjYz : Signal dom (BitVec 32))
    let t1a := (· + ·) <$> hSig <*> sig1
    let t1b := (· + ·) <$> t1a <*> chv
    let t1c := (· + ·) <$> t1b <*> kt
    let t1  := (· + ·) <$> t1c <*> wt
    let t2  := (· + ·) <$> sig0 <*> majv

    -- Next-cycle round registers.  When in a compression
    -- round (cnt 1..64), shift a→b→c→d, e gets d+t1, etc.
    -- On start, reload a..h from H-state (so a 2nd block
    -- continues from H0..H7, not from initH — initH is
    -- pre-loaded into the H regs at reset time).
    -- On a `first` block, load a..h from the SHA-256 IV (initH) instead of the
    -- carried H-state, so the module hashes a fresh message.  (Enables re-use
    -- for the many independent hashes in HMAC / RFC-6979 without a hard reset.)
    let firstSig := (first : Signal dom Bool)
    let aLoad := Signal.mux firstSig (Signal.pure 0x6a09e667#32) h0Sig
    let bLoad := Signal.mux firstSig (Signal.pure 0xbb67ae85#32) h1Sig
    let cLoad := Signal.mux firstSig (Signal.pure 0x3c6ef372#32) h2Sig
    let dLoad := Signal.mux firstSig (Signal.pure 0xa54ff53a#32) h3Sig
    let eLoad := Signal.mux firstSig (Signal.pure 0x510e527f#32) h4Sig
    let fLoad := Signal.mux firstSig (Signal.pure 0x9b05688c#32) h5Sig
    let gLoad := Signal.mux firstSig (Signal.pure 0x1f83d9ab#32) h6Sig
    let hLoadV := Signal.mux firstSig (Signal.pure 0x5be0cd19#32) h7Sig
    let aNext := (· + ·) <$> t1 <*> t2
    let eNext := (· + ·) <$> dSig <*> t1

    aR <~ Signal.mux start aLoad
            (Signal.mux isIdle aSig aNext)
    bR <~ Signal.mux start bLoad
            (Signal.mux isIdle bSig aSig)
    cR <~ Signal.mux start cLoad
            (Signal.mux isIdle cSig bSig)
    dR <~ Signal.mux start dLoad
            (Signal.mux isIdle dSig cSig)
    eR <~ Signal.mux start eLoad
            (Signal.mux isIdle eSig eNext)
    fR <~ Signal.mux start fLoad
            (Signal.mux isIdle fSig eSig)
    gR <~ Signal.mux start gLoad
            (Signal.mux isIdle gSig fSig)
    hR <~ Signal.mux start hLoadV
            (Signal.mux isIdle hSig gSig)

    -- H0..H7 update: at cycle 65 (isFinish), add a..h into
    -- H0..H7.  Hold otherwise (initH already loaded on
    -- reset).
    let h0Acc := (· + ·) <$> h0Sig <*> aSig
    let h1Acc := (· + ·) <$> h1Sig <*> bSig
    let h2Acc := (· + ·) <$> h2Sig <*> cSig
    let h3Acc := (· + ·) <$> h3Sig <*> dSig
    let h4Acc := (· + ·) <$> h4Sig <*> eSig
    let h5Acc := (· + ·) <$> h5Sig <*> fSig
    let h6Acc := (· + ·) <$> h6Sig <*> gSig
    let h7Acc := (· + ·) <$> h7Sig <*> hSig
    -- On a `first`-block start, (re)load H0..H7 with the IV so the finish-time
    -- accumulation `H += a..h` starts from initH.  Otherwise carry / accumulate.
    let startFirst := ((· && ·) <$> start <*> firstSig : Signal dom Bool)
    h0R <~ Signal.mux startFirst (Signal.pure 0x6a09e667#32) (Signal.mux isFinish h0Acc h0Sig)
    h1R <~ Signal.mux startFirst (Signal.pure 0xbb67ae85#32) (Signal.mux isFinish h1Acc h1Sig)
    h2R <~ Signal.mux startFirst (Signal.pure 0x3c6ef372#32) (Signal.mux isFinish h2Acc h2Sig)
    h3R <~ Signal.mux startFirst (Signal.pure 0xa54ff53a#32) (Signal.mux isFinish h3Acc h3Sig)
    h4R <~ Signal.mux startFirst (Signal.pure 0x510e527f#32) (Signal.mux isFinish h4Acc h4Sig)
    h5R <~ Signal.mux startFirst (Signal.pure 0x9b05688c#32) (Signal.mux isFinish h5Acc h5Sig)
    h6R <~ Signal.mux startFirst (Signal.pure 0x1f83d9ab#32) (Signal.mux isFinish h6Acc h6Sig)
    h7R <~ Signal.mux startFirst (Signal.pure 0x5be0cd19#32) (Signal.mux isFinish h7Acc h7Sig)

    -- W-buffer update: on start, load with the first 16
    -- words from blockIn.  During cnt 1..48, compute
    -- newW = σ₁(wTm2) + wTm7 + σ₀(wTm15) + wTm16, shift
    -- the buffer left by 32 bits, place newW in the bottom.
    -- During cnt 49..64 we still shift; the consumed wt
    -- is what we use this round.  Stop shifting at finish.
    -- σ₁(wTm2) = ROTR(x,17) ⊕ ROTR(x,19) ⊕ SHR(x,10), inlined.
    let w2r17  := ((· >>> ·) <$> wTm2 <*> (Signal.pure 17#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w2r17l := ((· <<< ·) <$> wTm2 <*> (Signal.pure 15#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w2R17  := ((· ||| ·) <$> w2r17 <*> w2r17l : Signal dom (BitVec 32))
    let w2r19  := ((· >>> ·) <$> wTm2 <*> (Signal.pure 19#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w2r19l := ((· <<< ·) <$> wTm2 <*> (Signal.pure 13#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w2R19  := ((· ||| ·) <$> w2r19 <*> w2r19l : Signal dom (BitVec 32))
    let w2s10  := ((· >>> ·) <$> wTm2 <*> (Signal.pure 10#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w2ab   := ((· ^^^ ·) <$> w2R17 <*> w2R19 : Signal dom (BitVec 32))
    let newW1  := ((· ^^^ ·) <$> w2ab <*> w2s10 : Signal dom (BitVec 32))
    -- σ₀(wTm15) = ROTR(x,7) ⊕ ROTR(x,18) ⊕ SHR(x,3), inlined.
    let w15r7  := ((· >>> ·) <$> wTm15 <*> (Signal.pure 7#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w15r7l := ((· <<< ·) <$> wTm15 <*> (Signal.pure 25#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w15R7  := ((· ||| ·) <$> w15r7 <*> w15r7l : Signal dom (BitVec 32))
    let w15r18  := ((· >>> ·) <$> wTm15 <*> (Signal.pure 18#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w15r18l := ((· <<< ·) <$> wTm15 <*> (Signal.pure 14#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w15R18  := ((· ||| ·) <$> w15r18 <*> w15r18l : Signal dom (BitVec 32))
    let w15s3  := ((· >>> ·) <$> wTm15 <*> (Signal.pure 3#32 : Signal dom (BitVec 32)) : Signal dom (BitVec 32))
    let w15ab  := ((· ^^^ ·) <$> w15R7 <*> w15R18 : Signal dom (BitVec 32))
    let newW2  := ((· ^^^ ·) <$> w15ab <*> w15s3 : Signal dom (BitVec 32))
    let n1n2  := (· + ·) <$> newW1 <*> wTm7
    let n3    := (· + ·) <$> n1n2 <*> newW2
    let newW  := (· + ·) <$> n3 <*> wTm16
    -- Shift the buffer left by 32 (drop the top 32 bits),
    -- then prepend new word into low position.
    -- Extract bits [479:0] (= old bits [479:0], shifted to
    -- [511:32]) and append newW [31:0].
    let bufLow := wBufSig.map (BitVec.extractLsb' 0 480 ·)
    let shiftedBuf := (· ++ ·) <$> bufLow <*> newW
    wBuf <~ Signal.mux start blockIn
              (Signal.mux ((fun b => !b) <$> isIdle) shiftedBuf wBufSig)

    -- Counter: 0 → 1 on start, +1 each cycle while non-zero,
    -- 0 again after finish (cycle 65).
    let cntInc := (· + ·) <$> cntSig <*> p1_7
    cnt <~ Signal.mux start p1_7
            (Signal.mux isFinish p0_7
              (Signal.mux isIdle p0_7 cntInc))
    doneR <~ isFinish

    -- Pack hash output.
    let h01 := (· ++ ·) <$> h0Sig <*> h1Sig
    let h23 := (· ++ ·) <$> h2Sig <*> h3Sig
    let h45 := (· ++ ·) <$> h4Sig <*> h5Sig
    let h67 := (· ++ ·) <$> h6Sig <*> h7Sig
    let h0123 := (· ++ ·) <$> h01 <*> h23
    let h4567 := (· ++ ·) <$> h45 <*> h67
    let hAll  := (· ++ ·) <$> h0123 <*> h4567

    return ({ hash := hAll
            , done := (doneR : Signal dom Bool)
            } : SHA256Out dom)

end Sparkle.IP.Crypto.SHA256
