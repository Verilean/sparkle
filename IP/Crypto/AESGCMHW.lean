/-
  IP.Crypto.AESGCMHW — AES-GCM specific HW pieces.

  AES-GCM = AES-CTR (confidentiality) + GHASH (integrity).
  Both the AES-128 block encryptor and the GHASH multi-block
  hasher already ship as separate HW modules:

    * `IP.Crypto.AESHW.aes128BlockHW`
    * `IP.Crypto.GHASHHW.ghashFullHW`

  This file closes the **GCM-specific** glue that isn't inside
  either of those:

    1. `gcmCounterHW` — 32-bit counter register with `inc32`
       semantics on the low 32 bits of a 128-bit counter block.
       Latches the initial J_0 on `start`, then increments on
       each `step` pulse (fired once per AES encryption).

    2. `gcmTagAccumulatorHW` — XOR the current ciphertext block
       into a 128-bit accumulator (Y_i) and hand off to the
       external GHASH multi-cycle multiplier.  Same shape as
       the ghashFullHW's IDLE/BUSY handshake, but with an extra
       "pre-XOR" combinational stage that the ghashFullHW alone
       doesn't cover.

  These two + the existing AES / GHASH HW give a complete
  AEAD_AES_128_GCM datapath.  The behavioural test in
  `Tests/IP/Crypto/AESGCMHWTest.lean` sweeps the pure-data
  reference across NIST GCM Test Case 2 (32-byte plaintext,
  16-byte tag).
-/
import Sparkle
import IP.Crypto.Codec.AESGCM

namespace Sparkle.IP.Crypto.AESGCMHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### GCM counter block. -/

structure CounterOut (dom : DomainConfig) where
  /-- Current counter block (128 bits, high 96 = IV, low 32 = ctr). -/
  counter : Signal dom (BitVec 128)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (CounterOut dom) dom := ⟨⟩

/-- GCM counter block generator.

    On `start`, latch `j0In` (the initial 128-bit counter block).
    On each `step` pulse, add 1 (mod 2^32) to the low 32 bits.
    The high 96 bits are preserved. -/
def gcmCounterHW {dom : DomainConfig}
    (start step : Signal dom Bool)
    (j0In : Signal dom (BitVec 128)) :
    CounterOut dom :=
  circuit do
    let ctrR ← Signal.reg (0#128)
    let ctrSig := (ctrR : Signal dom (BitVec 128))

    -- Low 32 bits = ctr[31:0].
    let lo32 := ctrSig.map (fun v => BitVec.extractLsb' 0 32 v)
    -- High 96 bits = ctr[127:32].
    let hi96 := ctrSig.map (fun v => BitVec.extractLsb' 32 96 v)
    -- lo32 + 1 (32-bit wrap).
    let p1_32 := (Signal.pure 1#32 : Signal dom (BitVec 32))
    let loInc := ((· + ·) <$> lo32 <*> p1_32 : Signal dom (BitVec 32))
    -- Concatenate hi96 ++ loInc (96 + 32 = 128 bits).
    let next := ((· ++ ·) <$> hi96 <*> loInc : Signal dom (BitVec 128))

    ctrR <~ Signal.mux start j0In
              (Signal.mux step next ctrSig)

    return ({ counter := ctrSig } : CounterOut dom)

/-! ### GCM tag accumulator.

    Model: on each ciphertext block C_i:
      Y_{i-1} XOR C_i  (this XOR)
      → gmul(·, H)       (external GHASH multiplier)
      → Y_i             (latched here)

    Interface hits both sides of the boundary:
      * `blockIn` = the ciphertext block C_i.
      * `mulResult` / `mulDone` = external gmul output.
      * `mulX` = the multiplier's X operand (Y_{i-1} XOR C_i).
      * `fire` = pulse asking the external multiplier to start.

    This lets the caller reuse `IP.Crypto.GHASHHW.gmulHW` as the
    multiplier without also owning its FSM. -/

structure TagOut (dom : DomainConfig) where
  /-- Current Y accumulator (128 bits). -/
  y      : Signal dom (BitVec 128)
  /-- X operand for the external GF(2^128) multiplier. -/
  mulX   : Signal dom (BitVec 128)
  /-- Pulse asking the external multiplier to start a new round. -/
  fire   : Signal dom Bool
  /-- High when a new blockValid can be accepted (i.e. not currently
      waiting on the multiplier). -/
  ready  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TagOut dom) dom := ⟨⟩

/-- GCM tag accumulator FSM.

    Same shape as `IP.Crypto.GHASHHW.ghashFullHW` but exposes
    the multiplier operand and handshake so callers can wire
    the multiplier's `done` back in.  For pure GHASH (no AEAD
    wrapper), use `ghashFullHW` directly.

    On `start`, y ← 0.  On `blockValid` (accepted only when
    ready): fire = 1, mulX = y XOR blockIn.  Externally the
    caller instantiates gmulHW with (fire, mulX, hIn) and
    routes its `.done` back to `mulDone`; on `mulDone`, we
    latch `mulResult` into y and go back to ready. -/
def gcmTagAccumulatorHW {dom : DomainConfig}
    (start blockValid mulDone : Signal dom Bool)
    (blockIn mulResult : Signal dom (BitVec 128)) :
    TagOut dom :=
  circuit do
    let yR ← Signal.reg (0#128)
    let stR ← Signal.reg false   -- false = IDLE, true = BUSY

    let ySig := (yR : Signal dom (BitVec 128))
    let stSig := (stR : Signal dom Bool)

    let isIdle := ((fun b => !b) <$> stSig : Signal dom Bool)
    let fire := ((· && ·) <$> isIdle <*> blockValid : Signal dom Bool)
    let mulX := ((· ^^^ ·) <$> ySig <*> blockIn : Signal dom (BitVec 128))

    let p0c := (Signal.pure 0#128 : Signal dom (BitVec 128))
    yR <~ Signal.mux start p0c
            (Signal.mux mulDone mulResult ySig)
    stR <~ Signal.mux start (Signal.pure false : Signal dom Bool)
              (Signal.mux fire (Signal.pure true : Signal dom Bool)
                (Signal.mux mulDone (Signal.pure false : Signal dom Bool) stSig))

    return ({ y := ySig
            , mulX := mulX
            , fire := fire
            , ready := isIdle
            } : TagOut dom)

end Sparkle.IP.Crypto.AESGCMHW
