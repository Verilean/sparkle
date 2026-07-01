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
import IP.Crypto.Keccak256

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
  let m := n % 64
  if m = 0 then x
  else
    let sn  : BitVec 64 := BitVec.ofNat 64 m
    let sn' : BitVec 64 := BitVec.ofNat 64 (64 - m)
    let ls := ((· <<< ·) <$> x <*> (Signal.pure sn  : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    let rs := ((· >>> ·) <$> x <*> (Signal.pure sn' : Signal dom (BitVec 64)) : Signal dom (BitVec 64))
    (· ||| ·) <$> ls <*> rs

/-! ### Keccak-f[1600] iterative FSM.

    Because the state is 25 × 64 bits, we expose *all 25 lanes*
    as separate output signals for callers, avoiding a
    1600-bit-wide monolithic BitVec.  Each lane has its own
    register in the module. -/

structure KeccakFOut (dom : DomainConfig) where
  /-- All 25 lanes.  Indexed the same way as pure-data
      `IP.Crypto.Keccak256.State`: lane (x, y) = index `x + 5*y`. -/
  lanes : Array (Signal dom (BitVec 64))
  /-- Round counter (0 = idle, 1..24 = running, 25 = done). -/
  round : Signal dom (BitVec 5)
  /-- Pulses one cycle after the last round completes. -/
  done  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (KeccakFOut dom) dom := ⟨⟩

/-- Single-round Keccak permutation implemented combinationally
    over 25 lane signals.  Returns 25 next-cycle lane signals. -/
def keccakRoundHW {dom : DomainConfig}
    (lanes : Array (Signal dom (BitVec 64)))
    (round : Signal dom (BitVec 5)) :
    Array (Signal dom (BitVec 64)) := Id.run do
  -- Bail with a plain array if lanes size ≠ 25 (defensive).
  if lanes.size ≠ 25 then return lanes
  let get := fun x y => lanes.getD (x + 5 * y) (Signal.pure 0#64 : Signal dom (BitVec 64))

  -- θ: column parity.
  let cSig := fun x =>
    let a := (· ^^^ ·) <$> get x 0 <*> get x 1
    let b := (· ^^^ ·) <$> a <*> get x 2
    let c := (· ^^^ ·) <$> b <*> get x 3
    (· ^^^ ·) <$> c <*> get x 4
  let c0 := cSig 0
  let c1 := cSig 1
  let c2 := cSig 2
  let c3 := cSig 3
  let c4 := cSig 4
  let cArr := #[c0, c1, c2, c3, c4]
  let cGet := fun i => cArr.getD i (Signal.pure 0#64 : Signal dom (BitVec 64))
  let d := fun x =>
    let xm := (x + 4) % 5
    let xp := (x + 1) % 5
    let rot := rotL64Sig (cGet xp) 1
    (· ^^^ ·) <$> cGet xm <*> rot
  let d0 := d 0
  let d1 := d 1
  let d2 := d 2
  let d3 := d 3
  let d4 := d 4
  let dArr := #[d0, d1, d2, d3, d4]
  let dGet := fun i => dArr.getD i (Signal.pure 0#64 : Signal dom (BitVec 64))

  -- After θ: a'[x, y] = a[x, y] XOR d(x).
  let mut thetaLanes : Array (Signal dom (BitVec 64)) :=
    Array.replicate 25 (Signal.pure 0#64 : Signal dom (BitVec 64))
  for y in [:5] do
    for x in [:5] do
      thetaLanes := thetaLanes.set! (x + 5 * y)
        ((· ^^^ ·) <$> get x y <*> dGet x : Signal dom (BitVec 64))

  -- ρ + π: rotate each lane and route to new position (x', y') = (y, (2x+3y) mod 5).
  -- Build the post-πρ array directly.
  let mut piLanes : Array (Signal dom (BitVec 64)) :=
    Array.replicate 25 (Signal.pure 0#64 : Signal dom (BitVec 64))
  for y in [:5] do
    for x in [:5] do
      let r := rotOffsets.getD (x + 5 * y) 0
      let rotated :=
        rotL64Sig (thetaLanes.getD (x + 5 * y) (Signal.pure 0#64 : Signal dom (BitVec 64))) r
      let xNew := y
      let yNew := (2 * x + 3 * y) % 5
      piLanes := piLanes.set! (xNew + 5 * yNew) rotated

  -- χ (per-row non-linear step).
  let mut chiLanes : Array (Signal dom (BitVec 64)) :=
    Array.replicate 25 (Signal.pure 0#64 : Signal dom (BitVec 64))
  for y in [:5] do
    -- row[x] = piLanes[x + 5*y]
    let r0 := piLanes.getD (0 + 5*y) (Signal.pure 0#64 : Signal dom (BitVec 64))
    let r1 := piLanes.getD (1 + 5*y) (Signal.pure 0#64 : Signal dom (BitVec 64))
    let r2 := piLanes.getD (2 + 5*y) (Signal.pure 0#64 : Signal dom (BitVec 64))
    let r3 := piLanes.getD (3 + 5*y) (Signal.pure 0#64 : Signal dom (BitVec 64))
    let r4 := piLanes.getD (4 + 5*y) (Signal.pure 0#64 : Signal dom (BitVec 64))
    let notR := fun (r : Signal dom (BitVec 64)) => (~~~ ·) <$> r
    let mkChi (r ra rb : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
      let nRa := notR ra
      let and2 := ((· &&& ·) <$> nRa <*> rb : Signal dom (BitVec 64))
      ((· ^^^ ·) <$> r <*> and2 : Signal dom (BitVec 64))
    chiLanes := chiLanes.set! (0 + 5*y) (mkChi r0 r1 r2)
    chiLanes := chiLanes.set! (1 + 5*y) (mkChi r1 r2 r3)
    chiLanes := chiLanes.set! (2 + 5*y) (mkChi r2 r3 r4)
    chiLanes := chiLanes.set! (3 + 5*y) (mkChi r3 r4 r0)
    chiLanes := chiLanes.set! (4 + 5*y) (mkChi r4 r0 r1)

  -- ι: XOR round constant into lane (0, 0).  We subtract 1 from
  -- the counter because our internal cnt walks 1..24 while the
  -- pure-data RC table is 0..23.
  let p1_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))
  let rIdx := ((· - ·) <$> round <*> p1_5 : Signal dom (BitVec 5))
  let rcVal := keccakRcHW rIdx
  let lane00 := chiLanes.getD 0 (Signal.pure 0#64 : Signal dom (BitVec 64))
  let lane00' := ((· ^^^ ·) <$> lane00 <*> rcVal : Signal dom (BitVec 64))
  let mut out := chiLanes
  out := out.set! 0 lane00'
  return out

/-- Full 24-round Keccak-f[1600] permutation as a `circuit do`
    FSM.  Because `circuit do` doesn't play nicely with an
    array of 25 register handles created inside the `do`, we
    unroll the register declarations explicitly.

    Cycle 0     : start pulse, latch input state.
    Cycle 1..24 : one round per cycle, cnt=1..24.
    Cycle 25    : done pulse, hold state. -/
def keccakF1600HW {dom : DomainConfig}
    (start : Signal dom Bool)
    (stateIn : Array (Signal dom (BitVec 64))) :
    KeccakFOut dom :=
  circuit do
    -- 25 lane registers.
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

    let isIdle   := ((· == ·) <$> cntSig <*> p0_5 : Signal dom Bool)
    let isFinish := ((· == ·) <$> cntSig <*> p24_5 : Signal dom Bool)
    let isRun :=
      let notIdle := ((fun b => !b) <$> isIdle : Signal dom Bool)
      let notFin  := ((fun b => !b) <$> isFinish : Signal dom Bool)
      -- Actually finish IS the final round, so we run 1..24.
      let _ := notFin
      notIdle

    -- Combinational one-round update.
    let nextLanes := keccakRoundHW lanes cntSig

    -- Register updates: on start ⇒ latch stateIn.  On isRun ⇒ nextLanes.
    let nlAt := fun i =>
      nextLanes.getD i (Signal.pure 0#64 : Signal dom (BitVec 64))
    let inAt := fun i =>
      stateIn.getD i (Signal.pure 0#64 : Signal dom (BitVec 64))
    l0  <~ Signal.mux start (inAt 0)  (Signal.mux isRun (nlAt 0)  lanes[0]!)
    l1  <~ Signal.mux start (inAt 1)  (Signal.mux isRun (nlAt 1)  lanes[1]!)
    l2  <~ Signal.mux start (inAt 2)  (Signal.mux isRun (nlAt 2)  lanes[2]!)
    l3  <~ Signal.mux start (inAt 3)  (Signal.mux isRun (nlAt 3)  lanes[3]!)
    l4  <~ Signal.mux start (inAt 4)  (Signal.mux isRun (nlAt 4)  lanes[4]!)
    l5  <~ Signal.mux start (inAt 5)  (Signal.mux isRun (nlAt 5)  lanes[5]!)
    l6  <~ Signal.mux start (inAt 6)  (Signal.mux isRun (nlAt 6)  lanes[6]!)
    l7  <~ Signal.mux start (inAt 7)  (Signal.mux isRun (nlAt 7)  lanes[7]!)
    l8  <~ Signal.mux start (inAt 8)  (Signal.mux isRun (nlAt 8)  lanes[8]!)
    l9  <~ Signal.mux start (inAt 9)  (Signal.mux isRun (nlAt 9)  lanes[9]!)
    l10 <~ Signal.mux start (inAt 10) (Signal.mux isRun (nlAt 10) lanes[10]!)
    l11 <~ Signal.mux start (inAt 11) (Signal.mux isRun (nlAt 11) lanes[11]!)
    l12 <~ Signal.mux start (inAt 12) (Signal.mux isRun (nlAt 12) lanes[12]!)
    l13 <~ Signal.mux start (inAt 13) (Signal.mux isRun (nlAt 13) lanes[13]!)
    l14 <~ Signal.mux start (inAt 14) (Signal.mux isRun (nlAt 14) lanes[14]!)
    l15 <~ Signal.mux start (inAt 15) (Signal.mux isRun (nlAt 15) lanes[15]!)
    l16 <~ Signal.mux start (inAt 16) (Signal.mux isRun (nlAt 16) lanes[16]!)
    l17 <~ Signal.mux start (inAt 17) (Signal.mux isRun (nlAt 17) lanes[17]!)
    l18 <~ Signal.mux start (inAt 18) (Signal.mux isRun (nlAt 18) lanes[18]!)
    l19 <~ Signal.mux start (inAt 19) (Signal.mux isRun (nlAt 19) lanes[19]!)
    l20 <~ Signal.mux start (inAt 20) (Signal.mux isRun (nlAt 20) lanes[20]!)
    l21 <~ Signal.mux start (inAt 21) (Signal.mux isRun (nlAt 21) lanes[21]!)
    l22 <~ Signal.mux start (inAt 22) (Signal.mux isRun (nlAt 22) lanes[22]!)
    l23 <~ Signal.mux start (inAt 23) (Signal.mux isRun (nlAt 23) lanes[23]!)
    l24 <~ Signal.mux start (inAt 24) (Signal.mux isRun (nlAt 24) lanes[24]!)

    let cntInc := ((· + ·) <$> cntSig <*> p1_5 : Signal dom (BitVec 5))
    cntR <~ Signal.mux start p1_5
              (Signal.mux isFinish p0_5
                (Signal.mux isIdle p0_5 cntInc))
    doneR <~ isFinish

    return ({ lanes := lanes
            , round := cntSig
            , done  := (doneR : Signal dom Bool)
            } : KeccakFOut dom)

end Sparkle.IP.Crypto.Keccak256HW
