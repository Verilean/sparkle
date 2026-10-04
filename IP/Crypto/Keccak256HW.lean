/-
  IP.Crypto.Keccak256HW — Keccak-f[1600] iterative permutation
  (Signal DSL).

  The state is 25 lanes × 64 bits = 1600 bits, held as 25
  separate `Signal dom (BitVec 64)` registers (indexed by
  (x, y) with `state[x + 5*y]`).  A 5-bit round counter walks
  the 24 rounds, and one full θ→ρ→π→χ→ι round is computed
  combinationally per cycle.

  A full sponge (absorb + squeeze + padding) would sit on top,
  wiring `keccakF1600HW` to a rate/byte-input FSM; for wave 1
  we focus on the permutation and validate against
  `IP.Crypto.Keccak256.keccakF` on a hand-picked input.

  Only 25 × BitVec 64 register slots are exposed; the caller
  packs/unpacks to whatever byte order the ambient sponge
  uses.

  A stand-alone `#synthesizeVerilog` on the top-level FSM's
  first-lane output demonstrates the elaborator can produce
  Verilog for the whole 24-round round-serial engine.
-/
import Sparkle
import Sparkle.Core.Lut
import IP.Crypto.Proof.Keccak256

open Sparkle.Core (kLutMacro)

namespace Sparkle.IP.Crypto.Keccak256HW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Keccak256 (rc rotOffsets)

/-! ### Rotation constant lookup.

    24 round constants — the ι step XORs the constant into
    lane (0,0).  Round counter is 0..23; we use a 5-bit
    counter and pad to 32 slots. -/

@[hardware_module] def keccakRcHW {dom : DomainConfig}
    (round : Signal dom (BitVec 5)) : Signal dom (BitVec 64) :=
  kLut! round [
    Signal.pure 0x0000000000000001#64, Signal.pure 0x0000000000008082#64,
    Signal.pure 0x800000000000808a#64, Signal.pure 0x8000000080008000#64,
    Signal.pure 0x000000000000808b#64, Signal.pure 0x0000000080000001#64,
    Signal.pure 0x8000000080008081#64, Signal.pure 0x8000000000008009#64,
    Signal.pure 0x000000000000008a#64, Signal.pure 0x0000000000000088#64,
    Signal.pure 0x0000000080008009#64, Signal.pure 0x000000008000000a#64,
    Signal.pure 0x000000008000808b#64, Signal.pure 0x800000000000008b#64,
    Signal.pure 0x8000000000008089#64, Signal.pure 0x8000000000008003#64,
    Signal.pure 0x8000000000008002#64, Signal.pure 0x8000000000000080#64,
    Signal.pure 0x000000000000800a#64, Signal.pure 0x800000008000000a#64,
    Signal.pure 0x8000000080008081#64, Signal.pure 0x8000000000008080#64,
    Signal.pure 0x0000000080000001#64, Signal.pure 0x8000000080008008#64,
    -- Pad to 32 entries (5-bit index).
    Signal.pure 0#64, Signal.pure 0#64, Signal.pure 0#64, Signal.pure 0#64,
    Signal.pure 0#64, Signal.pure 0#64, Signal.pure 0#64, Signal.pure 0#64
  ]

/-! ### Left-rotate by a compile-time constant. -/

@[reducible, inline] def rotL64Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) (n : Nat) : Signal dom (BitVec 64) :=
  -- NB: no `if m = 0` special-case.  When m = 0 the general form
  -- already yields `x`: `x <<< 0 = x` and `x >>> 64 = 0` in BitVec 64,
  -- so `(x<<<0) ||| (x>>>64) = x`.  Dropping the branch keeps the
  -- expression a pure signal graph (a runtime if-then-else does not
  -- lower through `#synthesizeVerilog`).
  let m := n % 64
  let sn  : BitVec 64 := BitVec.ofNat 64 m
  let sn' : BitVec 64 := BitVec.ofNat 64 ((64 - m) % 64)
  let ls := (x <<< (Signal.pure sn  : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
  let rs := (x >>> (Signal.pure sn' : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
  ls ||| rs

/-! ### Keccak-f[1600] iterative FSM.

    Because the state is 25 × 64 bits, we expose *all 25 lanes*
    as separate output signals for callers, avoiding a
    1600-bit-wide monolithic BitVec.  Each lane has its own
    register in the module. -/

structure KeccakFOut (dom : DomainConfig) where
  /-- The 25 lanes, exposed as NAMED SCALAR fields (l0..l24) rather
      than an `Array`.  Indexed the same way as pure-data
      `IP.Crypto.Keccak256.State`: lane (x, y) = field `l{x + 5*y}`.
      Named scalars are required because the synth elaborator can
      project a hardware-module's output record only through named
      fields, not through a runtime `Array.getD`. -/
  l0  : Signal dom (BitVec 64)
  l1  : Signal dom (BitVec 64)
  l2  : Signal dom (BitVec 64)
  l3  : Signal dom (BitVec 64)
  l4  : Signal dom (BitVec 64)
  l5  : Signal dom (BitVec 64)
  l6  : Signal dom (BitVec 64)
  l7  : Signal dom (BitVec 64)
  l8  : Signal dom (BitVec 64)
  l9  : Signal dom (BitVec 64)
  l10 : Signal dom (BitVec 64)
  l11 : Signal dom (BitVec 64)
  l12 : Signal dom (BitVec 64)
  l13 : Signal dom (BitVec 64)
  l14 : Signal dom (BitVec 64)
  l15 : Signal dom (BitVec 64)
  l16 : Signal dom (BitVec 64)
  l17 : Signal dom (BitVec 64)
  l18 : Signal dom (BitVec 64)
  l19 : Signal dom (BitVec 64)
  l20 : Signal dom (BitVec 64)
  l21 : Signal dom (BitVec 64)
  l22 : Signal dom (BitVec 64)
  l23 : Signal dom (BitVec 64)
  l24 : Signal dom (BitVec 64)
  /-- Round counter (0 = idle, 1..24 = running, 25 = done). -/
  round : Signal dom (BitVec 5)
  /-- Pulses one cycle after the last round completes. -/
  done  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (KeccakFOut dom) dom := ⟨⟩

/-- 25 lane signals as NAMED scalar fields.  `keccakRoundHW` returns
    this (rather than an `Array`) so `keccakF1600HW` can project each
    next-lane signal by name — a runtime `Array.getD`/`[i]!` on an
    opaque function result does not reduce through the synth
    elaborator, whereas a structure projection does. -/
structure Lanes25 (dom : DomainConfig) where
  f0  : Signal dom (BitVec 64)
  f1  : Signal dom (BitVec 64)
  f2  : Signal dom (BitVec 64)
  f3  : Signal dom (BitVec 64)
  f4  : Signal dom (BitVec 64)
  f5  : Signal dom (BitVec 64)
  f6  : Signal dom (BitVec 64)
  f7  : Signal dom (BitVec 64)
  f8  : Signal dom (BitVec 64)
  f9  : Signal dom (BitVec 64)
  f10 : Signal dom (BitVec 64)
  f11 : Signal dom (BitVec 64)
  f12 : Signal dom (BitVec 64)
  f13 : Signal dom (BitVec 64)
  f14 : Signal dom (BitVec 64)
  f15 : Signal dom (BitVec 64)
  f16 : Signal dom (BitVec 64)
  f17 : Signal dom (BitVec 64)
  f18 : Signal dom (BitVec 64)
  f19 : Signal dom (BitVec 64)
  f20 : Signal dom (BitVec 64)
  f21 : Signal dom (BitVec 64)
  f22 : Signal dom (BitVec 64)
  f23 : Signal dom (BitVec 64)
  f24 : Signal dom (BitVec 64)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Full 24-round Keccak-f[1600] permutation as a `circuit do` FSM.
    25 lane registers unrolled; one θ→ρ→π→χ→ι round per cycle, cnt=1..24.
    The round is written INLINE (fully expanded, no helper lambdas /
    `Id.run do`) so `#synthesizeVerilog` can lower it — the synth pass
    can't inline let-bound signal lambdas or reduce monadic loops.

    Cycle 0     : start pulse, latch input lanes (in0..in24).
    Cycle 1..24 : one round per cycle.
    Cycle 24    : done pulse; state held. -/
def keccakF1600HW {dom : DomainConfig}
    (start : Signal dom Bool)
    (in0  in1  in2  in3  in4  in5  in6  in7  in8  in9
     in10 in11 in12 in13 in14 in15 in16 in17 in18 in19
     in20 in21 in22 in23 in24 : Signal dom (BitVec 64)) :
    KeccakFOut dom :=
  circuit do
    let l0  ← Signal.reg (0#64); let l1  ← Signal.reg (0#64)
    let l2  ← Signal.reg (0#64); let l3  ← Signal.reg (0#64)
    let l4  ← Signal.reg (0#64); let l5  ← Signal.reg (0#64)
    let l6  ← Signal.reg (0#64); let l7  ← Signal.reg (0#64)
    let l8  ← Signal.reg (0#64); let l9  ← Signal.reg (0#64)
    let l10 ← Signal.reg (0#64); let l11 ← Signal.reg (0#64)
    let l12 ← Signal.reg (0#64); let l13 ← Signal.reg (0#64)
    let l14 ← Signal.reg (0#64); let l15 ← Signal.reg (0#64)
    let l16 ← Signal.reg (0#64); let l17 ← Signal.reg (0#64)
    let l18 ← Signal.reg (0#64); let l19 ← Signal.reg (0#64)
    let l20 ← Signal.reg (0#64); let l21 ← Signal.reg (0#64)
    let l22 ← Signal.reg (0#64); let l23 ← Signal.reg (0#64)
    let l24 ← Signal.reg (0#64)
    let cntR ← Signal.reg (0#5)
    let doneR ← Signal.reg false

    let lanes := (#[
      (l0 : Signal dom (BitVec 64)), (l1 : Signal dom (BitVec 64)),
      (l2 : Signal dom (BitVec 64)), (l3 : Signal dom (BitVec 64)),
      (l4 : Signal dom (BitVec 64)), (l5 : Signal dom (BitVec 64)),
      (l6 : Signal dom (BitVec 64)), (l7 : Signal dom (BitVec 64)),
      (l8 : Signal dom (BitVec 64)), (l9 : Signal dom (BitVec 64)),
      (l10 : Signal dom (BitVec 64)), (l11 : Signal dom (BitVec 64)),
      (l12 : Signal dom (BitVec 64)), (l13 : Signal dom (BitVec 64)),
      (l14 : Signal dom (BitVec 64)), (l15 : Signal dom (BitVec 64)),
      (l16 : Signal dom (BitVec 64)), (l17 : Signal dom (BitVec 64)),
      (l18 : Signal dom (BitVec 64)), (l19 : Signal dom (BitVec 64)),
      (l20 : Signal dom (BitVec 64)), (l21 : Signal dom (BitVec 64)),
      (l22 : Signal dom (BitVec 64)), (l23 : Signal dom (BitVec 64)),
      (l24 : Signal dom (BitVec 64))
    ] : Array (Signal dom (BitVec 64)))
    let cntSig := (cntR : Signal dom (BitVec 5))
    let p0_5  := (Signal.pure 0#5 : Signal dom (BitVec 5))
    let p1_5  := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let p24_5 := (Signal.pure 24#5 : Signal dom (BitVec 5))
    let isIdle   := (cntSig === p0_5 : Signal dom Bool)
    let isFinish := (cntSig === p24_5 : Signal dom Bool)
    let isRun := (~~~isIdle : Signal dom Bool)

    -- Combinational one-round update, fully INLINED (c0..c4 θ-parities,
    -- d0..d4 diffusion, pi0..pi24 ρ+π, nl0..nl24 χ+ι).
    let z := (Signal.pure 0#64 : Signal dom (BitVec 64))
    let c0 := (((((l0 : Signal dom (BitVec 64)) ^^^ (l5 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l10 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l15 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l20 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let c1 := (((((l1 : Signal dom (BitVec 64)) ^^^ (l6 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l11 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l16 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l21 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let c2 := (((((l2 : Signal dom (BitVec 64)) ^^^ (l7 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l12 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l17 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l22 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let c3 := (((((l3 : Signal dom (BitVec 64)) ^^^ (l8 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l13 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l18 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l23 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let c4 := (((((l4 : Signal dom (BitVec 64)) ^^^ (l9 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l14 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l19 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ (l24 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let d0 := (c4 ^^^ ((c1 <<< (Signal.pure (1#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (c1 >>> (Signal.pure (63#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let d1 := (c0 ^^^ ((c2 <<< (Signal.pure (1#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (c2 >>> (Signal.pure (63#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let d2 := (c1 ^^^ ((c3 <<< (Signal.pure (1#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (c3 >>> (Signal.pure (63#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let d3 := (c2 ^^^ ((c4 <<< (Signal.pure (1#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (c4 >>> (Signal.pure (63#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let d4 := (c3 ^^^ ((c0 <<< (Signal.pure (1#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (c0 >>> (Signal.pure (63#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi0 := ((((l0 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) <<< (Signal.pure (0#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l0 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) >>> (Signal.pure (0#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi1 := ((((l6 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) <<< (Signal.pure (44#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l6 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) >>> (Signal.pure (20#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi2 := ((((l12 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) <<< (Signal.pure (43#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l12 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) >>> (Signal.pure (21#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi3 := ((((l18 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) <<< (Signal.pure (21#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l18 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) >>> (Signal.pure (43#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi4 := ((((l24 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) <<< (Signal.pure (14#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l24 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) >>> (Signal.pure (50#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi5 := ((((l3 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) <<< (Signal.pure (28#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l3 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) >>> (Signal.pure (36#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi6 := ((((l9 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) <<< (Signal.pure (20#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l9 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) >>> (Signal.pure (44#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi7 := ((((l10 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) <<< (Signal.pure (3#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l10 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) >>> (Signal.pure (61#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi8 := ((((l16 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) <<< (Signal.pure (45#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l16 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) >>> (Signal.pure (19#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi9 := ((((l22 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) <<< (Signal.pure (61#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l22 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) >>> (Signal.pure (3#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi10 := ((((l1 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) <<< (Signal.pure (1#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l1 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) >>> (Signal.pure (63#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi11 := ((((l7 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) <<< (Signal.pure (6#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l7 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) >>> (Signal.pure (58#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi12 := ((((l13 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) <<< (Signal.pure (25#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l13 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) >>> (Signal.pure (39#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi13 := ((((l19 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) <<< (Signal.pure (8#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l19 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) >>> (Signal.pure (56#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi14 := ((((l20 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) <<< (Signal.pure (18#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l20 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) >>> (Signal.pure (46#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi15 := ((((l4 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) <<< (Signal.pure (27#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l4 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) >>> (Signal.pure (37#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi16 := ((((l5 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) <<< (Signal.pure (36#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l5 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) >>> (Signal.pure (28#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi17 := ((((l11 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) <<< (Signal.pure (10#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l11 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) >>> (Signal.pure (54#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi18 := ((((l17 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) <<< (Signal.pure (15#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l17 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) >>> (Signal.pure (49#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi19 := ((((l23 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) <<< (Signal.pure (56#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l23 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) >>> (Signal.pure (8#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi20 := ((((l2 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) <<< (Signal.pure (62#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l2 : Signal dom (BitVec 64)) ^^^ d2 : Signal dom (BitVec 64)) >>> (Signal.pure (2#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi21 := ((((l8 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) <<< (Signal.pure (55#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l8 : Signal dom (BitVec 64)) ^^^ d3 : Signal dom (BitVec 64)) >>> (Signal.pure (9#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi22 := ((((l14 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) <<< (Signal.pure (39#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l14 : Signal dom (BitVec 64)) ^^^ d4 : Signal dom (BitVec 64)) >>> (Signal.pure (25#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi23 := ((((l15 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) <<< (Signal.pure (41#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l15 : Signal dom (BitVec 64)) ^^^ d0 : Signal dom (BitVec 64)) >>> (Signal.pure (23#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let pi24 := ((((l21 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) <<< (Signal.pure (2#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ||| (((l21 : Signal dom (BitVec 64)) ^^^ d1 : Signal dom (BitVec 64)) >>> (Signal.pure (62#64 : BitVec 64) : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let rcVal := keccakRcHW (cntSig - (Signal.pure 1#5 : Signal dom (BitVec 5)))
    let nl0 := ((pi0 ^^^ ((~~~pi1 : Signal dom (BitVec 64)) &&& pi2 : Signal dom (BitVec 64)) : Signal dom (BitVec 64)) ^^^ rcVal : Signal dom (BitVec 64))
    let nl1 := (pi1 ^^^ ((~~~pi2 : Signal dom (BitVec 64)) &&& pi3 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl2 := (pi2 ^^^ ((~~~pi3 : Signal dom (BitVec 64)) &&& pi4 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl3 := (pi3 ^^^ ((~~~pi4 : Signal dom (BitVec 64)) &&& pi0 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl4 := (pi4 ^^^ ((~~~pi0 : Signal dom (BitVec 64)) &&& pi1 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl5 := (pi5 ^^^ ((~~~pi6 : Signal dom (BitVec 64)) &&& pi7 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl6 := (pi6 ^^^ ((~~~pi7 : Signal dom (BitVec 64)) &&& pi8 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl7 := (pi7 ^^^ ((~~~pi8 : Signal dom (BitVec 64)) &&& pi9 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl8 := (pi8 ^^^ ((~~~pi9 : Signal dom (BitVec 64)) &&& pi5 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl9 := (pi9 ^^^ ((~~~pi5 : Signal dom (BitVec 64)) &&& pi6 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl10 := (pi10 ^^^ ((~~~pi11 : Signal dom (BitVec 64)) &&& pi12 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl11 := (pi11 ^^^ ((~~~pi12 : Signal dom (BitVec 64)) &&& pi13 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl12 := (pi12 ^^^ ((~~~pi13 : Signal dom (BitVec 64)) &&& pi14 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl13 := (pi13 ^^^ ((~~~pi14 : Signal dom (BitVec 64)) &&& pi10 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl14 := (pi14 ^^^ ((~~~pi10 : Signal dom (BitVec 64)) &&& pi11 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl15 := (pi15 ^^^ ((~~~pi16 : Signal dom (BitVec 64)) &&& pi17 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl16 := (pi16 ^^^ ((~~~pi17 : Signal dom (BitVec 64)) &&& pi18 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl17 := (pi17 ^^^ ((~~~pi18 : Signal dom (BitVec 64)) &&& pi19 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl18 := (pi18 ^^^ ((~~~pi19 : Signal dom (BitVec 64)) &&& pi15 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl19 := (pi19 ^^^ ((~~~pi15 : Signal dom (BitVec 64)) &&& pi16 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl20 := (pi20 ^^^ ((~~~pi21 : Signal dom (BitVec 64)) &&& pi22 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl21 := (pi21 ^^^ ((~~~pi22 : Signal dom (BitVec 64)) &&& pi23 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl22 := (pi22 ^^^ ((~~~pi23 : Signal dom (BitVec 64)) &&& pi24 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl23 := (pi23 ^^^ ((~~~pi24 : Signal dom (BitVec 64)) &&& pi20 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let nl24 := (pi24 ^^^ ((~~~pi20 : Signal dom (BitVec 64)) &&& pi21 : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    -- Per-lane register update: on start ⇒ latch stateIn scalar; else
    -- on isRun ⇒ round output; else hold the current lane.
    l0  <~ Signal.mux start in0  (Signal.mux isRun nl0  (l0  : Signal dom (BitVec 64)))
    l1  <~ Signal.mux start in1  (Signal.mux isRun nl1  (l1  : Signal dom (BitVec 64)))
    l2  <~ Signal.mux start in2  (Signal.mux isRun nl2  (l2  : Signal dom (BitVec 64)))
    l3  <~ Signal.mux start in3  (Signal.mux isRun nl3  (l3  : Signal dom (BitVec 64)))
    l4  <~ Signal.mux start in4  (Signal.mux isRun nl4  (l4  : Signal dom (BitVec 64)))
    l5  <~ Signal.mux start in5  (Signal.mux isRun nl5  (l5  : Signal dom (BitVec 64)))
    l6  <~ Signal.mux start in6  (Signal.mux isRun nl6  (l6  : Signal dom (BitVec 64)))
    l7  <~ Signal.mux start in7  (Signal.mux isRun nl7  (l7  : Signal dom (BitVec 64)))
    l8  <~ Signal.mux start in8  (Signal.mux isRun nl8  (l8  : Signal dom (BitVec 64)))
    l9  <~ Signal.mux start in9  (Signal.mux isRun nl9  (l9  : Signal dom (BitVec 64)))
    l10 <~ Signal.mux start in10 (Signal.mux isRun nl10 (l10 : Signal dom (BitVec 64)))
    l11 <~ Signal.mux start in11 (Signal.mux isRun nl11 (l11 : Signal dom (BitVec 64)))
    l12 <~ Signal.mux start in12 (Signal.mux isRun nl12 (l12 : Signal dom (BitVec 64)))
    l13 <~ Signal.mux start in13 (Signal.mux isRun nl13 (l13 : Signal dom (BitVec 64)))
    l14 <~ Signal.mux start in14 (Signal.mux isRun nl14 (l14 : Signal dom (BitVec 64)))
    l15 <~ Signal.mux start in15 (Signal.mux isRun nl15 (l15 : Signal dom (BitVec 64)))
    l16 <~ Signal.mux start in16 (Signal.mux isRun nl16 (l16 : Signal dom (BitVec 64)))
    l17 <~ Signal.mux start in17 (Signal.mux isRun nl17 (l17 : Signal dom (BitVec 64)))
    l18 <~ Signal.mux start in18 (Signal.mux isRun nl18 (l18 : Signal dom (BitVec 64)))
    l19 <~ Signal.mux start in19 (Signal.mux isRun nl19 (l19 : Signal dom (BitVec 64)))
    l20 <~ Signal.mux start in20 (Signal.mux isRun nl20 (l20 : Signal dom (BitVec 64)))
    l21 <~ Signal.mux start in21 (Signal.mux isRun nl21 (l21 : Signal dom (BitVec 64)))
    l22 <~ Signal.mux start in22 (Signal.mux isRun nl22 (l22 : Signal dom (BitVec 64)))
    l23 <~ Signal.mux start in23 (Signal.mux isRun nl23 (l23 : Signal dom (BitVec 64)))
    l24 <~ Signal.mux start in24 (Signal.mux isRun nl24 (l24 : Signal dom (BitVec 64)))

    let cntInc := (cntSig + p1_5 : Signal dom (BitVec 5))
    cntR <~ Signal.mux start p1_5
              (Signal.mux isFinish p0_5
                (Signal.mux isIdle p0_5 cntInc))
    doneR <~ isFinish

    return ({ l0  := (l0  : Signal dom (BitVec 64))
            , l1  := (l1  : Signal dom (BitVec 64))
            , l2  := (l2  : Signal dom (BitVec 64))
            , l3  := (l3  : Signal dom (BitVec 64))
            , l4  := (l4  : Signal dom (BitVec 64))
            , l5  := (l5  : Signal dom (BitVec 64))
            , l6  := (l6  : Signal dom (BitVec 64))
            , l7  := (l7  : Signal dom (BitVec 64))
            , l8  := (l8  : Signal dom (BitVec 64))
            , l9  := (l9  : Signal dom (BitVec 64))
            , l10 := (l10 : Signal dom (BitVec 64))
            , l11 := (l11 : Signal dom (BitVec 64))
            , l12 := (l12 : Signal dom (BitVec 64))
            , l13 := (l13 : Signal dom (BitVec 64))
            , l14 := (l14 : Signal dom (BitVec 64))
            , l15 := (l15 : Signal dom (BitVec 64))
            , l16 := (l16 : Signal dom (BitVec 64))
            , l17 := (l17 : Signal dom (BitVec 64))
            , l18 := (l18 : Signal dom (BitVec 64))
            , l19 := (l19 : Signal dom (BitVec 64))
            , l20 := (l20 : Signal dom (BitVec 64))
            , l21 := (l21 : Signal dom (BitVec 64))
            , l22 := (l22 : Signal dom (BitVec 64))
            , l23 := (l23 : Signal dom (BitVec 64))
            , l24 := (l24 : Signal dom (BitVec 64))
            , round := cntSig
            , done  := (doneR : Signal dom Bool)
            } : KeccakFOut dom)

end Sparkle.IP.Crypto.Keccak256HW
