/-
  IP.Crypto.Keccak256Sponge — full Keccak-256 sponge FSM.

  `keccakF1600HW` (IP.Crypto.Keccak256HW) is only the 24-round
  permutation.  This module wraps it in the sponge construction —
  multi-block absorb — that a real hash needs:

    state ← 0
    for each rate block b (17 lanes of 64 bits = 136 bytes):
      state[0..16] ^= b
      state ← keccak-f(state)
    digest ← state[0..3]   (256 bits)

  Padding (`0x01 … 0x80`) and byte→lane packing are done by the
  CALLER at buffer-assembly time (the message length is known
  there, so pad shape is a fixed combinational function — see
  `Keccak256.padEthereum`).  This keeps the FSM a clean absorb
  loop with no branchy pad logic inside `circuit do`.  The caller
  passes:

    * `msgLanes` — the padded message already packed into 64-bit
      little-endian lanes, laid out block-major: lane
      `blk*17 + i` is lane `i` of block `blk`.  Length 34 covers
      up to 2 rate blocks (272 bytes of padded input), which is
      ample for an EIP-1559 native-ETH signing preimage.
    * `nBlocks` — 1 or 2, latched on `start`.

  Cycle schedule (per block, driving the black-box permutation):

    T0        : start pulse.  Load state = block-0 lanes XOR 0 into
                s0..s16 (s17..s24 = 0); pulse kf.start; blk = 0.
    T1..T25   : permutation runs (kf holds its own 24-round FSM).
                Sponge holds kf.start low and waits for kf.done.
    Tdone     : kf.done pulses (kf round counter hit 24).  The
                permuted state lands in kf's lane registers on the
                FOLLOWING cycle, so we delay by one: `kfDonePrev`.
    Tdone+1   : `kfDonePrev` high → latch kf.lanes into s0..s24.
                If blk+1 < nBlocks: XOR block-(blk+1) into s0..s16,
                pulse kf.start again, blk++.  Else: pulse `done`.

  Because the deep 25-lane × 64-bit `Signal.val` recursion times
  out the pure-Lean simulator (documented in Keccak256HWTest), the
  behavioural validation is done at the pure-data level (the block
  loop is cross-checked against `Keccak256.keccak256OfBytes`), and
  the HW is validated by instantiation + `#synthesizeVerilog`.
-/
import Sparkle
import IP.Crypto.Proof.Keccak256
import IP.Crypto.Keccak256HW

namespace Sparkle.IP.Crypto.Keccak256Sponge

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Keccak256HW (KeccakFOut Lanes25 keccakF1600HW)

/-- Number of 64-bit lanes in one rate block (136 bytes / 8). -/
def rateLanes : Nat := 17

/-- Max supported message length in rate blocks (34 lanes). -/
def maxBlocks : Nat := 2

/-- Sponge output: the 256-bit digest as four little-endian lanes
    (`d0` = state lane 0 = digest bytes 0..7, etc.), plus a `done`
    pulse.  Emitted as four separate scalar signals rather than a
    Vector/tuple, per the IR elaborator's output-shape rules. -/
structure SpongeOut (dom : DomainConfig) where
  d0 : Signal dom (BitVec 64)
  d1 : Signal dom (BitVec 64)
  d2 : Signal dom (BitVec 64)
  d3 : Signal dom (BitVec 64)
  /-- Pulses one cycle after the final block's permutation is
      absorbed; `d0..d3` are valid on that cycle and held after. -/
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SpongeOut dom) dom := ⟨⟩

/-- Thin `@[hardware_module]` wrapper around the permutation so the
    sponge can drive it as a sub-module instance and project
    `.lanes` / `.done`. -/
@[hardware_module] def wKeccakF {dom : DomainConfig}
    (start : Signal dom Bool)
    (in0  in1  in2  in3  in4  in5  in6  in7  in8  in9
     in10 in11 in12 in13 in14 in15 in16 in17 in18 in19
     in20 in21 in22 in23 in24 : Signal dom (BitVec 64)) :
    KeccakFOut dom :=
  keccakF1600HW start
    in0  in1  in2  in3  in4  in5  in6  in7  in8  in9
    in10 in11 in12 in13 in14 in15 in16 in17 in18 in19
    in20 in21 in22 in23 in24

/-- The multi-block absorb FSM. -/
def keccak256SpongeHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (nBlocks : Signal dom (BitVec 2))
    (m0  m1  m2  m3  m4  m5  m6  m7  m8  m9
     m10 m11 m12 m13 m14 m15 m16 m17 m18 m19
     m20 m21 m22 m23 m24 m25 m26 m27 m28 m29
     m30 m31 m32 m33 : Signal dom (BitVec 64)) :
    SpongeOut dom :=
  circuit do
    -- Running sponge state: 25 lanes, unrolled (no Vector reg).
    let s0  ← Signal.reg (0#64); let s1  ← Signal.reg (0#64)
    let s2  ← Signal.reg (0#64); let s3  ← Signal.reg (0#64)
    let s4  ← Signal.reg (0#64); let s5  ← Signal.reg (0#64)
    let s6  ← Signal.reg (0#64); let s7  ← Signal.reg (0#64)
    let s8  ← Signal.reg (0#64); let s9  ← Signal.reg (0#64)
    let s10 ← Signal.reg (0#64); let s11 ← Signal.reg (0#64)
    let s12 ← Signal.reg (0#64); let s13 ← Signal.reg (0#64)
    let s14 ← Signal.reg (0#64); let s15 ← Signal.reg (0#64)
    let s16 ← Signal.reg (0#64); let s17 ← Signal.reg (0#64)
    let s18 ← Signal.reg (0#64); let s19 ← Signal.reg (0#64)
    let s20 ← Signal.reg (0#64); let s21 ← Signal.reg (0#64)
    let s22 ← Signal.reg (0#64); let s23 ← Signal.reg (0#64)
    let s24 ← Signal.reg (0#64)
    -- Block index (0 or 1), latched block count, done strobe, and a
    -- one-cycle delay of the permutation's `done`.
    let blkR       ← Signal.reg (0#2)
    let nBlkR      ← Signal.reg (0#2)
    let doneR      ← Signal.reg false
    -- kf.done delayed one cycle (the cycle the permuted state is
    -- valid on kf.lanes → we CAPTURE it into sSig) and two cycles
    -- (the cycle sSig holds the permuted state → we LAUNCH the next
    -- block's absorb, reading only registered state, no comb loop).
    let kfDonePrev ← Signal.reg false
    let kfDoneP2   ← Signal.reg false

    let sSig := (#[ (s0 : Signal dom (BitVec 64)),  (s1 : Signal dom (BitVec 64))
       , (s2 : Signal dom (BitVec 64)),  (s3 : Signal dom (BitVec 64))
       , (s4 : Signal dom (BitVec 64)),  (s5 : Signal dom (BitVec 64))
       , (s6 : Signal dom (BitVec 64)),  (s7 : Signal dom (BitVec 64))
       , (s8 : Signal dom (BitVec 64)),  (s9 : Signal dom (BitVec 64))
       , (s10 : Signal dom (BitVec 64)), (s11 : Signal dom (BitVec 64))
       , (s12 : Signal dom (BitVec 64)), (s13 : Signal dom (BitVec 64))
       , (s14 : Signal dom (BitVec 64)), (s15 : Signal dom (BitVec 64))
       , (s16 : Signal dom (BitVec 64)), (s17 : Signal dom (BitVec 64))
       , (s18 : Signal dom (BitVec 64)), (s19 : Signal dom (BitVec 64))
       , (s20 : Signal dom (BitVec 64)), (s21 : Signal dom (BitVec 64))
       , (s22 : Signal dom (BitVec 64)), (s23 : Signal dom (BitVec 64))
       , (s24 : Signal dom (BitVec 64)) ] : Array (Signal dom (BitVec 64)))
    let blkSig  := (blkR  : Signal dom (BitVec 2))
    let nBlkSig := (nBlkR : Signal dom (BitVec 2))

    let p0_2 := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let z64  := (Signal.pure 0#64 : Signal dom (BitVec 64))

    -- The block currently being absorbed:
    --   * on `start`, that's block 0 (blkR still 0);
    --   * on a permutation-complete continuation, that's blkR+1
    --     (the value blkR will hold next cycle).  We pre-compute the
    --     "block to absorb next" index and select its 17 lanes.
    let blkNext := ((· + ·) <$> blkSig <*> p1_2 : Signal dom (BitVec 2))
    -- Lane i of block b is msgLanes[b*17 + i].  Split into two
    -- `if`-free selectors (a runtime if-then-else does not lower):
    --   startLane i — block 0's lane i (used on `start`)
    --   contLane  i — the continuation block's lane i, selected by
    --                 blkNext (0 or 1; with maxBlocks=2, ==1 here)
    -- Selects the continuation block (0 or 1) when XORing the next
    -- block in; with maxBlocks=2 this is 1 whenever we continue.
    let isOne := ((· == ·) <$> blkNext <*> p1_2 : Signal dom Bool)

    -- Are we going to run another block after this permutation?
    -- `blkNext < nBlocks` (with maxBlocks=2, "is there a block 1 and
    -- did we just finish block 0").
    let moreBlocks := ((BitVec.ult · ·) <$> blkNext <*> nBlkSig : Signal dom Bool)

    -- CAPTURE cycle: one after kf.done, kf.lanes holds the permuted
    -- state → latch it into sSig.
    let capture := (kfDonePrev : Signal dom Bool)
    -- LAUNCH-next cycle: one after capture, sSig now holds the
    -- permuted state → XOR the next block in and pulse start.  Only
    -- when there IS a next block.
    let kfContinue := ((· && ·) <$> (kfDoneP2 : Signal dom Bool) <*> moreBlocks
                        : Signal dom Bool)
    let kfStart := ((· || ·) <$> start <*> kfContinue : Signal dom Bool)

    -- State fed to the permutation, built ONLY from registered state
    -- (`sSig`) — no combinational loop through `kf`:
    --   * on `start`      → block-0 lanes XOR 0 (sSig is being reset)
    --   * on `kfContinue` → sSig (permuted state) XOR blkNext lanes
    --   * otherwise       → don't-care (start is low, kf ignores it)
    -- Rate lanes (0..16): on start → block-0 lane; on continue →
    -- registered state XOR blkNext lane.  Capacity lanes (17..24):
    -- on start → 0; else → registered state.  Built as two explicit
    -- ranges then appended so there is NO per-element `if` in the
    -- signal graph (the synth elaborator can't lower a runtime
    -- if-then-else over a lane index).
    -- Feed the 25 state-in lanes to the permutation as SEPARATE scalar
    -- signals, each fully INLINED (no `let`-bound lambdas — the synth
    -- pass can't inline those).  Rate lanes 0..16: on start → block-0
    -- lane `msgLanes[i]`; else → registered state `sSig[i]` XOR the
    -- continuation block's lane (`msgLanes[17+i]` when blkNext==1, else
    -- `msgLanes[i]`).  Capacity lanes 17..24: on start → 0; else →
    -- registered state.  Indices are literal, so `getD` reduces.
    let kf := wKeccakF kfStart
      (Signal.mux start m0 ((· ^^^ ·) <$> (s0 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m17 m0) : Signal dom (BitVec 64)))  (Signal.mux start m1 ((· ^^^ ·) <$> (s1 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m18 m1) : Signal dom (BitVec 64)))  (Signal.mux start m2 ((· ^^^ ·) <$> (s2 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m19 m2) : Signal dom (BitVec 64)))  (Signal.mux start m3 ((· ^^^ ·) <$> (s3 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m20 m3) : Signal dom (BitVec 64)))  (Signal.mux start m4 ((· ^^^ ·) <$> (s4 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m21 m4) : Signal dom (BitVec 64)))
      (Signal.mux start m5 ((· ^^^ ·) <$> (s5 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m22 m5) : Signal dom (BitVec 64)))  (Signal.mux start m6 ((· ^^^ ·) <$> (s6 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m23 m6) : Signal dom (BitVec 64)))  (Signal.mux start m7 ((· ^^^ ·) <$> (s7 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m24 m7) : Signal dom (BitVec 64)))  (Signal.mux start m8 ((· ^^^ ·) <$> (s8 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m25 m8) : Signal dom (BitVec 64)))  (Signal.mux start m9 ((· ^^^ ·) <$> (s9 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m26 m9) : Signal dom (BitVec 64)))
      (Signal.mux start m10 ((· ^^^ ·) <$> (s10 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m27 m10) : Signal dom (BitVec 64)))  (Signal.mux start m11 ((· ^^^ ·) <$> (s11 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m28 m11) : Signal dom (BitVec 64)))  (Signal.mux start m12 ((· ^^^ ·) <$> (s12 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m29 m12) : Signal dom (BitVec 64)))  (Signal.mux start m13 ((· ^^^ ·) <$> (s13 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m30 m13) : Signal dom (BitVec 64)))  (Signal.mux start m14 ((· ^^^ ·) <$> (s14 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m31 m14) : Signal dom (BitVec 64)))
      (Signal.mux start m15 ((· ^^^ ·) <$> (s15 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m32 m15) : Signal dom (BitVec 64)))  (Signal.mux start m16 ((· ^^^ ·) <$> (s16 : Signal dom (BitVec 64)) <*> (Signal.mux isOne m33 m16) : Signal dom (BitVec 64)))  (Signal.mux start z64 (s17 : Signal dom (BitVec 64)))  (Signal.mux start z64 (s18 : Signal dom (BitVec 64)))  (Signal.mux start z64 (s19 : Signal dom (BitVec 64)))
      (Signal.mux start z64 (s20 : Signal dom (BitVec 64)))  (Signal.mux start z64 (s21 : Signal dom (BitVec 64)))  (Signal.mux start z64 (s22 : Signal dom (BitVec 64)))  (Signal.mux start z64 (s23 : Signal dom (BitVec 64)))  (Signal.mux start z64 (s24 : Signal dom (BitVec 64)))
    -- The permutation output now exposes 25 NAMED scalar lane fields
    -- (l0..l24) instead of an `Array`, because the synth elaborator
    -- can project a hardware-module's output only through named
    -- Next-state for each sponge lane, INLINED (no `let`-bound
    -- lambdas / array getD — the synth pass can't lower those):
    --   on start → 0 (fresh state); on capture → the permuted lane
    --   kf.l{i}; else hold.  `kf` output is projected by named field.
    s0 <~ Signal.mux start z64 (Signal.mux capture kf.l0 (s0 : Signal dom (BitVec 64)))
    s1 <~ Signal.mux start z64 (Signal.mux capture kf.l1 (s1 : Signal dom (BitVec 64)))
    s2 <~ Signal.mux start z64 (Signal.mux capture kf.l2 (s2 : Signal dom (BitVec 64)))
    s3 <~ Signal.mux start z64 (Signal.mux capture kf.l3 (s3 : Signal dom (BitVec 64)))
    s4 <~ Signal.mux start z64 (Signal.mux capture kf.l4 (s4 : Signal dom (BitVec 64)))
    s5 <~ Signal.mux start z64 (Signal.mux capture kf.l5 (s5 : Signal dom (BitVec 64)))
    s6 <~ Signal.mux start z64 (Signal.mux capture kf.l6 (s6 : Signal dom (BitVec 64)))
    s7 <~ Signal.mux start z64 (Signal.mux capture kf.l7 (s7 : Signal dom (BitVec 64)))
    s8 <~ Signal.mux start z64 (Signal.mux capture kf.l8 (s8 : Signal dom (BitVec 64)))
    s9 <~ Signal.mux start z64 (Signal.mux capture kf.l9 (s9 : Signal dom (BitVec 64)))
    s10 <~ Signal.mux start z64 (Signal.mux capture kf.l10 (s10 : Signal dom (BitVec 64)))
    s11 <~ Signal.mux start z64 (Signal.mux capture kf.l11 (s11 : Signal dom (BitVec 64)))
    s12 <~ Signal.mux start z64 (Signal.mux capture kf.l12 (s12 : Signal dom (BitVec 64)))
    s13 <~ Signal.mux start z64 (Signal.mux capture kf.l13 (s13 : Signal dom (BitVec 64)))
    s14 <~ Signal.mux start z64 (Signal.mux capture kf.l14 (s14 : Signal dom (BitVec 64)))
    s15 <~ Signal.mux start z64 (Signal.mux capture kf.l15 (s15 : Signal dom (BitVec 64)))
    s16 <~ Signal.mux start z64 (Signal.mux capture kf.l16 (s16 : Signal dom (BitVec 64)))
    s17 <~ Signal.mux start z64 (Signal.mux capture kf.l17 (s17 : Signal dom (BitVec 64)))
    s18 <~ Signal.mux start z64 (Signal.mux capture kf.l18 (s18 : Signal dom (BitVec 64)))
    s19 <~ Signal.mux start z64 (Signal.mux capture kf.l19 (s19 : Signal dom (BitVec 64)))
    s20 <~ Signal.mux start z64 (Signal.mux capture kf.l20 (s20 : Signal dom (BitVec 64)))
    s21 <~ Signal.mux start z64 (Signal.mux capture kf.l21 (s21 : Signal dom (BitVec 64)))
    s22 <~ Signal.mux start z64 (Signal.mux capture kf.l22 (s22 : Signal dom (BitVec 64)))
    s23 <~ Signal.mux start z64 (Signal.mux capture kf.l23 (s23 : Signal dom (BitVec 64)))
    s24 <~ Signal.mux start z64 (Signal.mux capture kf.l24 (s24 : Signal dom (BitVec 64)))

    -- Block index: 0 on start; +1 when we launch a continuation.
    blkR <~ Signal.mux start p0_2 (Signal.mux kfContinue blkNext blkSig)
    -- Latch block count on start.
    nBlkR <~ Signal.mux start nBlocks nBlkSig
    -- kf.done delayed by one cycle (capture) and two (launch-next).
    kfDonePrev <~ kf.done
    kfDoneP2   <~ (kfDonePrev : Signal dom Bool)
    -- Overall done: `finish` is high on the CAPTURE cycle of the last
    -- block (kfDonePrev high AND no more blocks).  Both `doneR` and the
    -- `sSig` digest regs are assigned from `finish`/`capture` this
    -- cycle, so `done` pulses and `d0..d3` become valid together on the
    -- FOLLOWING cycle, and are held after.
    let noMore := ((fun b => !b) <$> moreBlocks : Signal dom Bool)
    let finish := ((· && ·) <$> capture <*> noMore : Signal dom Bool)
    doneR <~ finish

    return ({ d0 := (s0 : Signal dom (BitVec 64))
            , d1 := (s1 : Signal dom (BitVec 64))
            , d2 := (s2 : Signal dom (BitVec 64))
            , d3 := (s3 : Signal dom (BitVec 64))
            , done := (doneR : Signal dom Bool)
            } : SpongeOut dom)

end Sparkle.IP.Crypto.Keccak256Sponge
