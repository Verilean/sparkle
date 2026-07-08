/-
  IP.Crypto.EcdsaSignMsgSmall — the area-optimized secp256k1 signer with the
  full on-chip secret path: the private key `d` is baked, the nonce `k` is
  derived on-chip via RFC-6979, and (step 2) the hash `z` is computed on-chip
  via Keccak-256.  NOTHING secret crosses the wire — the host provides only
  the message; `k` never leaves the die (a leaked `k` would recover `d` via
  `d = (s·k − z)·r⁻¹ mod n`).

  Two cores (baked demo key `d = 12345`):

    * `signZSmallDemo start z` — chains `rfc6979HW` (k on-chip) into
      `signCoreSmall`.  Given a 256-bit big-endian hash `z`, produces the
      deterministic `(r,s)` = `Rfc6979.signDeterministic 12345 z`.

    * `signMsgSmallDemo start nBlocks m0..m33` — prepends the Keccak-256
      sponge: `z = keccak256(message)` (host sends the padded lanes), then
      `signZSmallDemo`.  (Step 2, added below.)

  RFC-6979 is baked to a specific key via `wRfc` because `rfc6979HW`'s key is
  a compile-time `BitVec` (not a Signal port), so it can only be instantiated
  as a hardware sub-module through a key-baking `@[hardware_module]` wrapper —
  same pattern as `PolicySignDemoM2.wSponge`/`wSignCore`.
-/
import Sparkle
import IP.Crypto.EcdsaSignSmallDemo
import IP.Crypto.Rfc6979HW
import IP.Crypto.Keccak256Sponge

namespace Sparkle.IP.Crypto.EcdsaSignMsgSmall

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignSmallDemo (signCoreSmall SignSmallOut)
open Sparkle.IP.Crypto.Rfc6979HW (rfc6979HW NonceOut)
open Sparkle.IP.Crypto.Keccak256Sponge (keccak256SpongeHW SpongeOut)
open Sparkle.IP.Crypto.Keccak256HW (keccakF1600HW KeccakFOut)

/-- Baked demo private key. -/
def demoKey : BitVec 256 := BitVec.ofNat 256 12345

/-- `@[hardware_module]` wrapper baking the key into the RFC-6979 nonce core,
    so it can be driven as a sub-module (its key is a compile-time constant,
    not a Signal port). -/
@[hardware_module] def wRfc {dom : DomainConfig}
    (start : Signal dom Bool) (z : Signal dom (BitVec 256)) : NonceOut dom :=
  rfc6979HW demoKey start z

/-- Sign a hash `z` with the baked key, deriving the RFC-6979 nonce on-chip.
    Sequence: latch `z` → run `wRfc` (k) → run `signCoreSmall` (r,s).
    `@[hardware_module]` so `signMsgSmallDemo` can drive it as a sub-module. -/
@[hardware_module] def signZSmallDemo {dom : DomainConfig}
    (start : Signal dom Bool) (z : Signal dom (BitVec 256)) : SignSmallOut dom :=
  circuit do
    -- FSM: 0 idle · 1 rfc-issue · 2 rfc-wait · 3 sign-issue · 4 sign-wait
    let stR ← Signal.reg (0#3)
    let zR  ← Signal.reg (0#256)   -- latched hash, held for rfc + sign
    let kR  ← Signal.reg (0#256)   -- latched nonce from rfc
    let rR  ← Signal.reg (0#256)
    let sR  ← Signal.reg (0#256)
    let dnR ← Signal.reg false
    let st := (stR : Signal dom (BitVec 3))
    let zSig := (zR : Signal dom (BitVec 256))
    let kSig := (kR : Signal dom (BitVec 256))

    let is0 := (st === 0#3)
    let is1 := (st === 1#3)
    let is2 := (st === 2#3)
    let is3 := (st === 3#3)
    let is4 := (st === 4#3)

    -- Latch z on `start` (idle → issue rfc).
    zR <~ Signal.mux ((· && ·) <$> is0 <*> start) z zSig

    -- RFC-6979 nonce core (k on-chip).  One-cycle start in state 1.
    let rfc := wRfc is1 zSig
    let capK := ((· && ·) <$> is2 <*> rfc.done : Signal dom Bool)
    kR <~ Signal.mux capK rfc.k kSig

    -- Signing core (r,s from d,k,z).  One-cycle start in state 3.
    let sc := signCoreSmall is3 (Signal.pure demoKey : Signal dom (BitVec 256)) kSig zSig
    let capRS := ((· && ·) <$> is4 <*> sc.done : Signal dom Bool)
    rR <~ Signal.mux capRS sc.rOut (rR : Signal dom (BitVec 256))
    sR <~ Signal.mux capRS sc.sOut (sR : Signal dom (BitVec 256))
    dnR <~ capRS

    -- Next state.
    let stNext :=
      Signal.mux is0 (Signal.mux start (Signal.pure 1#3 : Signal dom (BitVec 3)) (Signal.pure 0#3))
      <| Signal.mux is1 (Signal.pure 2#3 : Signal dom (BitVec 3))
      <| Signal.mux is2 (Signal.mux rfc.done (Signal.pure 3#3 : Signal dom (BitVec 3)) (Signal.pure 2#3))
      <| Signal.mux is3 (Signal.pure 4#3 : Signal dom (BitVec 3))
        (Signal.mux is4 (Signal.mux sc.done (Signal.pure 0#3 : Signal dom (BitVec 3)) (Signal.pure 4#3))
          (Signal.pure 0#3))
    stR <~ stNext

    return ({ rOut := (rR : Signal dom (BitVec 256))
            , sOut := (sR : Signal dom (BitVec 256))
            , done := (dnR : Signal dom Bool) } : SignSmallOut dom)

/-- `@[hardware_module]` wrapper around the Keccak-256 sponge. -/
@[hardware_module] def wSponge {dom : DomainConfig}
    (start : Signal dom Bool) (nBlocks : Signal dom (BitVec 2))
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
     : Signal dom (BitVec 64)) : SpongeOut dom :=
  keccak256SpongeHW start nBlocks
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
    m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33

/-- Byte-reverse a 64-bit digest lane (little-endian sponge lane → the
    big-endian bytes ECDSA reads).  Fully inlined `append`-of-single-extract
    (the only shape the synth pass lowers). -/
@[inline] private def revLane {dom : DomainConfig}
    (d : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  ((BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) <*> (BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) <*> (BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) <*> (BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) <*> (BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) <*> (BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) <*> (BitVec.append <$> (d.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) <*> (d.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))

/-- Full on-chip message signer: `z = keccak256(message)` then `signZSmallDemo`.
    The host sends the padded Keccak lanes `m0..m33` (block-major, ≤2 blocks)
    and `nBlocks`; the device returns the deterministic ECDSA `(r,s)` over the
    hash.  With the baked key, NOTHING secret (d, k, or even z) crosses the
    wire — only the message the host wants signed.

    `@[hardware_module]` so a UART front-end can drive it and project its
    `(r,s,done)` outputs (see `EcdsaSignMsgDemo`). -/
@[hardware_module] def signMsgSmallDemo {dom : DomainConfig}
    (start : Signal dom Bool) (nBlocks : Signal dom (BitVec 2))
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
     : Signal dom (BitVec 64)) : SignSmallOut dom :=
  circuit do
    -- FSM: 0 idle · 1 sponge-issue · 2 sponge-wait · 3 sign-issue · 4 sign-wait
    -- (r,s) are NOT re-latched here — `signZSmallDemo` already holds them past
    -- its done, so we forward `sz.rOut/sz.sOut` directly (saves two 256-bit regs).
    let stR ← Signal.reg (0#3)
    let zR  ← Signal.reg (0#256)
    let dnR ← Signal.reg false
    let st := (stR : Signal dom (BitVec 3))
    let zSig := (zR : Signal dom (BitVec 256))

    let is0 := (st === 0#3)
    let is1 := (st === 1#3)
    let is2 := (st === 2#3)
    let is3 := (st === 3#3)
    let is4 := (st === 4#3)

    -- Keccak sponge: one-cycle start in state 1.
    let sponge := wSponge is1 nBlocks
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
      m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
    -- Assemble the 256-bit big-endian hash z = revLane(d0)‖…‖revLane(d3).
    let z :=
      (BitVec.append <$> revLane sponge.d0 <*>
        (BitVec.append <$> revLane sponge.d1 <*>
          (BitVec.append <$> revLane sponge.d2 <*> revLane sponge.d3
            : Signal dom (BitVec 128)) : Signal dom (BitVec 192))
        : Signal dom (BitVec 256))
    let capZ := ((· && ·) <$> is2 <*> sponge.done : Signal dom Bool)
    zR <~ Signal.mux capZ z zSig

    -- Nonce+sign core (k on-chip): one-cycle start in state 3, fed the hash.
    let sz := signZSmallDemo is3 zSig
    let capRS := ((· && ·) <$> is4 <*> sz.done : Signal dom Bool)
    dnR <~ capRS

    let stNext :=
      Signal.mux is0 (Signal.mux start (Signal.pure 1#3 : Signal dom (BitVec 3)) (Signal.pure 0#3))
      <| Signal.mux is1 (Signal.pure 2#3 : Signal dom (BitVec 3))
      <| Signal.mux is2 (Signal.mux sponge.done (Signal.pure 3#3 : Signal dom (BitVec 3)) (Signal.pure 2#3))
      <| Signal.mux is3 (Signal.pure 4#3 : Signal dom (BitVec 3))
        (Signal.mux is4 (Signal.mux sz.done (Signal.pure 0#3 : Signal dom (BitVec 3)) (Signal.pure 4#3))
          (Signal.pure 0#3))
    stR <~ stNext

    -- `sz` holds (r,s) past its done, so forward them; our `dnR` re-times the
    -- done pulse to this FSM's frame.  Valid on the cycle `dnR` is high (the
    -- UART TX loads r‖s then) and held after (until the next sign overwrites).
    return ({ rOut := sz.rOut
            , sOut := sz.sOut
            , done := (dnR : Signal dom Bool) } : SignSmallOut dom)

/-- `@[hardware_module]` wrapper around the raw 24-round Keccak-f[1600]. -/
@[hardware_module] def wKf1600 {dom : DomainConfig}
    (start : Signal dom Bool)
    (in0  in1  in2  in3  in4  in5  in6  in7  in8  in9
     in10 in11 in12 in13 in14 in15 in16 in17 in18 in19
     in20 in21 in22 in23 in24 : Signal dom (BitVec 64)) : KeccakFOut dom :=
  keccakF1600HW start
    in0  in1  in2  in3  in4  in5  in6  in7  in8  in9
    in10 in11 in12 in13 in14 in15 in16 in17 in18 in19
    in20 in21 in22 in23 in24

/-- SINGLE-BLOCK on-chip message signer (area-reduced for the ≤135-byte UART
    demo).  A one-rate-block Keccak-256 is just `keccak-f(block ‖ 0^capacity)`
    read out at lanes 0..3 — so this drives `keccakF1600HW` DIRECTLY, dropping
    the sponge's separate 1600-bit running state and its 25-lane absorb/capture
    mux bank (the bulk of the multi-block sponge's area).  The host sends the
    17 padded block lanes `m0..m16`; capacity lanes 17..24 are 0.

    `@[hardware_module]` so the UART front-end can drive it and project (r,s,done). -/
@[hardware_module] def signMsg1SmallDemo {dom : DomainConfig}
    (start : Signal dom Bool)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     : Signal dom (BitVec 64)) : SignSmallOut dom :=
  circuit do
    -- FSM: 0 idle · 1 kf-issue · 2 kf-wait · 3 sign-issue · 4 sign-wait
    let stR ← Signal.reg (0#3)
    let zR  ← Signal.reg (0#256)
    let dnR ← Signal.reg false
    let st := (stR : Signal dom (BitVec 3))
    let zSig := (zR : Signal dom (BitVec 256))
    let z64 := (Signal.pure 0#64 : Signal dom (BitVec 64))

    let is0 := (st === 0#3)
    let is1 := (st === 1#3)
    let is2 := (st === 2#3)
    let is3 := (st === 3#3)
    let is4 := (st === 4#3)

    -- Keccak-f directly on the padded block (capacity lanes 0).  One-cycle
    -- start in state 1.
    let kf := wKf1600 is1
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
      z64 z64 z64 z64 z64 z64 z64 z64
    -- Digest z = revLane(l0)‖revLane(l1)‖revLane(l2)‖revLane(l3), big-endian.
    let z :=
      (BitVec.append <$> revLane kf.l0 <*>
        (BitVec.append <$> revLane kf.l1 <*>
          (BitVec.append <$> revLane kf.l2 <*> revLane kf.l3
            : Signal dom (BitVec 128)) : Signal dom (BitVec 192))
        : Signal dom (BitVec 256))
    let capZ := ((· && ·) <$> is2 <*> kf.done : Signal dom Bool)
    zR <~ Signal.mux capZ z zSig

    let sz := signZSmallDemo is3 zSig
    let capRS := ((· && ·) <$> is4 <*> sz.done : Signal dom Bool)
    dnR <~ capRS

    let stNext :=
      Signal.mux is0 (Signal.mux start (Signal.pure 1#3 : Signal dom (BitVec 3)) (Signal.pure 0#3))
      <| Signal.mux is1 (Signal.pure 2#3 : Signal dom (BitVec 3))
      <| Signal.mux is2 (Signal.mux kf.done (Signal.pure 3#3 : Signal dom (BitVec 3)) (Signal.pure 2#3))
      <| Signal.mux is3 (Signal.pure 4#3 : Signal dom (BitVec 3))
        (Signal.mux is4 (Signal.mux sz.done (Signal.pure 0#3 : Signal dom (BitVec 3)) (Signal.pure 4#3))
          (Signal.pure 0#3))
    stR <~ stNext

    return ({ rOut := sz.rOut
            , sOut := sz.sOut
            , done := (dnR : Signal dom Bool) } : SignSmallOut dom)

end Sparkle.IP.Crypto.EcdsaSignMsgSmall
