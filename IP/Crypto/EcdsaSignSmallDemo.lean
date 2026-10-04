/-
  IP.Crypto.EcdsaSignSmallDemo — UART front-end + baked private key for the
  area-optimized secp256k1 signer (`EcdsaSignSmall.signCtrl`).

  Protocol (115200 8-N-1): host sends 64 bytes  k‖z  (big-endian, k first),
  the device signs with the BAKED-IN private key `d` and streams back 64 bytes
  r‖s.  `G` and `d` are constants in the bitstream; only k and z arrive over
  the wire.  (k/z-over-UART is the demo stage; RFC-6979 k + Keccak z come next.)
-/
import Sparkle
import IP.Crypto.EcdsaSignSmall
import IP.Crypto.Proof.Secp256k1PointJac
import IP.Net.UART

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmall
open Sparkle.IP.Net.UART (uartRxHW uartTxHW RxOut TxOut)

namespace Sparkle.IP.Crypto.EcdsaSignSmallDemo

/-! ## UART wrappers (`@[hardware_module]` so they instantiate once). -/
@[hardware_module] def wRx {dom : DomainConfig}
    (rxLine : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : RxOut dom :=
  uartRxHW rxLine bitDiv
@[hardware_module] def wTx {dom : DomainConfig}
    (txByte : Signal dom (BitVec 8)) (txValid : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : TxOut dom :=
  uartTxHW txByte txValid bitDiv

/-! ## Curve base point as bitvector constants. -/
def bvBaseX : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.Secp256k1PointJac.baseX
def bvBaseY : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.Secp256k1PointJac.baseY

/-- Simple `(start,d,k,z) → (rOut,sOut,done)` façade over `signCtrl`, hiding the
    register-file load / probe protocol.  Loads G(r3,4,5), d(r40), z(r41),
    k(r42), pulses the signer, then reads r(r35)/s(r37) back out. -/
structure SignSmallOut (dom : DomainConfig) where
  rOut : Signal dom (BitVec 256)
  sOut : Signal dom (BitVec 256)
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SignSmallOut dom) dom := ⟨⟩

@[hardware_module] def signCoreSmall {dom : DomainConfig}
    (start : Signal dom Bool) (d k z : Signal dom (BitVec 256)) : SignSmallOut dom :=
  circuit do
    -- State: 0 idle · 1-6 load G.x/G.y/G.z/d/z/k · 7 go · 8 wait-halt
    --        9-12 read-r (probe 35) · 13-16 read-s (probe 37, capture+done)
    let stR ← Signal.reg (0#5)
    let rR  ← Signal.reg (0#256)
    let sR  ← Signal.reg (0#256)
    let dnR ← Signal.reg false
    let st := (stR : Signal dom (BitVec 5))
    let is0  := (st === 0#5)
    let is1  := (st === 1#5)
    let is2  := (st === 2#5)
    let is3  := (st === 3#5)
    let is4  := (st === 4#5)
    let is5  := (st === 5#5)
    let is6  := (st === 6#5)
    let is7  := (st === 7#5)
    let is8  := (st === 8#5)
    let is9  := (st === 9#5)
    let is10 := (st === 10#5)
    let is11 := (st === 11#5)
    let is12 := (st === 12#5)
    let is13 := (st === 13#5)
    let is14 := (st === 14#5)
    let is15 := (st === 15#5)
    let is16 := (st === 16#5)

    -- load port: enabled in states 1..6, addr/data selected per state.
    let ldEn := (is1 ||| (is2 ||| (is3 ||| (is4 ||| (is5 ||| is6)))) : Signal dom Bool)
    let ldAddr :=
      (Signal.mux is1 (Signal.pure 3#6)
        (Signal.mux is2 (Signal.pure 4#6)
          (Signal.mux is3 (Signal.pure 5#6)
            (Signal.mux is4 (Signal.pure 40#6)
              (Signal.mux is5 (Signal.pure 41#6)
                (Signal.pure 42#6)))))  : Signal dom (BitVec 6))
    let ldData :=
      (Signal.mux is1 (Signal.pure bvBaseX)
        (Signal.mux is2 (Signal.pure bvBaseY)
          (Signal.mux is3 (Signal.pure 1#256)
            (Signal.mux is4 d
              (Signal.mux is5 z
                k))))  : Signal dom (BitVec 256))
    let sStart := is7
    -- probe r35 during 9..12, r37 during 13..16.
    let inRR := (is9 ||| (is10 ||| (is11 ||| is12)) : Signal dom Bool)
    let inRS := (is13 ||| (is14 ||| (is15 ||| is16)) : Signal dom Bool)
    let probeAddr :=
      (Signal.mux inRR (Signal.pure 35#6)
        (Signal.mux inRS (Signal.pure 37#6)
          (Signal.pure 0#6)) : Signal dom (BitVec 6))

    let sc := signCtrl sStart ldEn ldAddr ldData k probeAddr

    -- capture: r at end of read-r window (st==12), s at st==16.
    rR <~ Signal.mux is12 sc.probeVal rR
    sR <~ Signal.mux is16 sc.probeVal sR
    dnR <~ is16

    -- next state.
    let inc := (st + (Signal.pure 1#5 : Signal dom (BitVec 5)) : Signal dom (BitVec 5))
    let stNext :=
      Signal.mux is0 (Signal.mux start (Signal.pure 1#5 : Signal dom (BitVec 5)) (Signal.pure 0#5))
      <| Signal.mux is8 (Signal.mux sc.halted (Signal.pure 9#5 : Signal dom (BitVec 5)) (Signal.pure 8#5))
        (Signal.mux is16 (Signal.pure 0#5 : Signal dom (BitVec 5)) inc)
    stR <~ stNext

    return ({ rOut := (rR : Signal dom (BitVec 256))
            , sOut := (sR : Signal dom (BitVec 256))
            , done := (dnR : Signal dom Bool) } : SignSmallOut dom)

/-- Shift a byte into the low end of a 512-bit accumulator. -/
@[inline] private def shiftIn512 {dom : DomainConfig}
    (acc : Signal dom (BitVec 512)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 512) :=
  (acc <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    ||| (b.map (fun v => BitVec.append (0#504) v) : Signal dom (BitVec 512))

structure DemoOut (dom : DomainConfig) where
  uartTx   : Signal dom Bool
  signDone : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (DemoOut dom) dom := ⟨⟩

/-- UART signing demo with a baked private key `dKey`.  Host sends 64 bytes
    k‖z; device replies 64 bytes r‖s. -/
def signSmallDemo {dom : DomainConfig}
    (dKey : BitVec 256)
    (uartRx : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : DemoOut dom :=
  circuit do
    let accR   ← Signal.reg (0#512)   -- RX accumulator k‖z (64 bytes)
    let rxCntR ← Signal.reg (0#7)
    let kR     ← Signal.reg (0#256)
    let zR     ← Signal.reg (0#256)
    let startR ← Signal.reg false
    let txDataR ← Signal.reg (0#512)   -- TX shift r‖s (MSB byte first)
    let remR    ← Signal.reg (0#7)      -- bytes left to send
    let sendingR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 512))
    let rxCntSig := (rxCntR : Signal dom (BitVec 7))
    let kSig := (kR : Signal dom (BitVec 256))
    let zSig := (zR : Signal dom (BitVec 256))
    let txDataSig := (txDataR : Signal dom (BitVec 512))
    let remSig := (remR : Signal dom (BitVec 7))
    let sendingSig := (sendingR : Signal dom Bool)

    -- ===== UART RX: assemble 64 bytes =====
    let rx := wRx uartRx bitDiv
    let gotByte := rx.rxValid
    let accNext := shiftIn512 accSig rx.rxByte
    let rxInc := (rxCntSig + (Signal.pure 1#7 : Signal dom (BitVec 7)))
    let atLast := rxCntSig === 63#7
    let lastByte := (gotByte &&& atLast : Signal dom Bool)
    accR <~ Signal.mux gotByte accNext accSig
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#7 : Signal dom (BitVec 7))
                (Signal.mux gotByte rxInc rxCntSig)
    -- k in high 256, z in low 256 (k sent first).
    let kSlice := (accNext.map (fun v => BitVec.extractLsb' 256 256 v) : Signal dom (BitVec 256))
    let zSlice := (accNext.map (fun v => BitVec.extractLsb' 0 256 v) : Signal dom (BitVec 256))
    kR <~ Signal.mux lastByte kSlice kSig
    zR <~ Signal.mux lastByte zSlice zSig
    startR <~ lastByte

    -- ===== signer (baked key) =====
    let core := signCoreSmall (startR : Signal dom Bool) (Signal.pure dKey) kSig zSig

    -- ===== UART TX: on `core.done` load r‖s, then pump 64 bytes =====
    -- `wantSend` is a level (high while bytes remain); `wTx` latches a byte on
    -- the cycle it is both asserted and idle.  `accepted` is exactly that
    -- cycle, so we shift/decrement in lock-step and clear `sending` on the
    -- last byte.  `tx.txReady` is registered inside `wTx`, so referencing it
    -- in `accepted` after `tx` closes no combinational loop.
    let wantSend := sendingSig     -- `sending` is the sole gate; `rem` only triggers the clear below
    let tx := wTx
                (txDataSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                wantSend bitDiv
    let accepted := (wantSend &&& tx.txReady : Signal dom Bool)
    let rsConcat := (core.rOut ++ core.sOut : Signal dom (BitVec 512))
    let txShift := (txDataSig <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    txDataR <~ Signal.mux core.done rsConcat (Signal.mux accepted txShift txDataSig)
    let remDec := (remSig - (Signal.pure 1#7 : Signal dom (BitVec 7)))
    remR <~ Signal.mux core.done (Signal.pure 64#7 : Signal dom (BitVec 7))
              (Signal.mux accepted remDec remSig)
    let lastByte := (accepted &&& (remSig === 1#7) : Signal dom Bool)
    sendingR <~ Signal.mux core.done (Signal.pure true : Signal dom Bool)
                  (Signal.mux lastByte (Signal.pure false : Signal dom Bool) sendingSig)

    return ({ uartTx := tx.txLine, signDone := core.done } : DemoOut dom)

/-- bitDiv for 115200 baud at the Tang Nano 20k's 27 MHz crystal. -/
def bitDiv27M115200 : BitVec 16 := BitVec.ofNat 16 (27000000 / 115200 - 1)   -- ≈ 233

end Sparkle.IP.Crypto.EcdsaSignSmallDemo
