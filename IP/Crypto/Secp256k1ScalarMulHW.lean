/-
  IP.Crypto.Secp256k1ScalarMulHW — constant-time scalar
  multiplication k·P on secp256k1 via a Montgomery ladder over
  Jacobian coordinates, driving `Secp256k1PointOpHW.pointOpHW`
  (which in turn drives the bit-serial field multiplier).

  Montgomery ladder (MSB-first over 256 bits, invariant R1 = R0 + P):

      R0 = ∞ ; R1 = P
      for i = 255 downto 0:
        if bit_i = 0:  R1 = R0 + R1 ;  R0 = 2·R0
        if bit_i = 1:  R0 = R0 + R1 ;  R1 = 2·R1

  The two point operations per bit (one generic add, one double)
  are issued sequentially to a single shared `pointOpHW` instance:
  add first, then double, each awaited via `pointOpHW.done`.  After
  the last bit, `R0 = k·P` (in Jacobian coords) and `done` pulses.
  Conversion to affine (the single field inversion of the whole
  scalar-mul) is left to the caller / the sign FSM.

  Infinity handling.  `pointOpHW`'s add uses the *generic*
  add-2007-bl branch, which is invalid when an operand is ∞ or
  when the two operands are equal.  In a correct ladder R0 and R1
  differ by exactly P, so they are never equal (except at the
  measure-zero near-order edge k = n−1, which a real signer never
  encounters).  The only ∞ operand arises in the leading-zero
  prefix while R0 is still ∞; that window is handled *at the
  ladder level* by a `r0Inf` flag that muxes the point-op results
  (R0=∞ ⇒ 2·R0 = ∞ and R0+R1 = R1) instead of trusting the
  generic add.  Once the first set bit is consumed R0 becomes a
  real point and the flag clears for good.

  Composition.  This module does NOT instantiate the point-op
  engine (and therefore not the multiplier either).  Just as
  `pointOpHW` takes the multiplier over a flat start/done
  handshake rather than instantiating a record-returning
  sub-module (which `#synthesizeVerilog` rejects), `scalarMulHW`
  drives the *point-op* over a flat handshake: it exposes
  `poStart`/`poOpDouble`/`poX1..poZ2` driver outputs and takes
  the point-op's `poResX/Y/Z`/`poResDone` back as inputs.  The
  caller wires one `pointOpHW` (and one `mulHW`) across those
  ports.  This keeps every module a pure register-FSM whose
  outputs are combinational functions of its inputs — the only
  shape the Verilog elaborator accepts.

  Interface:
    inputs  start (Bool pulse)      — latch k + P, begin
            k (BitVec 256)          — scalar (MSB-first scan)
            px,py,pz (BitVec 256)   — base point P (Jacobian)
            poResX,poResY,poResZ    — point-op result coords in
            poResDone (Bool)        — point-op done in
    outputs xOut,yOut,zOut          — k·P (Jacobian, valid at done)
            done (Bool pulse)       — result ready
            poStart (Bool)          — pulse the point-op engine
            poOpDouble (Bool)       — point-op selector (double/add)
            poX1,poY1,poZ1          — point-op operand 1
            poX2,poY2,poZ2          — point-op operand 2

  Cycle cost ≈ 256 · (add + double) ≈ 256 · (16 + 7) muls ·
  ~260 cyc/mul ≈ 1.53 M cycles per scalar-mul with the 258-cyc
  bit-serial multiplier.  Dropping in the throughput-track
  Montgomery multiplier (~76 cyc/mul) cuts that ~3.4×.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1Field
import IP.Crypto.Secp256k1FieldHW
import IP.Crypto.Proof.Secp256k1PointJac
import IP.Crypto.Secp256k1PointOpHW

namespace Sparkle.IP.Crypto.Secp256k1ScalarMulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1PointOpHW

/-- Output record. -/
structure ScalarMulOut (dom : DomainConfig) where
  /-- Result X coordinate (Jacobian), valid at `done`. -/
  xOut : Signal dom (BitVec 256)
  /-- Result Y coordinate (Jacobian), valid at `done`. -/
  yOut : Signal dom (BitVec 256)
  /-- Result Z coordinate (Jacobian), valid at `done`. -/
  zOut : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the scalar-mul finishes. -/
  done : Signal dom Bool
  /-- Pulse to trigger the external point-op engine. -/
  poStart : Signal dom Bool
  /-- Point-op selector: true = double, false = add. -/
  poOpDouble : Signal dom Bool
  /-- Point-op operand 1 (X,Y,Z). -/
  poX1 : Signal dom (BitVec 256)
  poY1 : Signal dom (BitVec 256)
  poZ1 : Signal dom (BitVec 256)
  /-- Point-op operand 2 (X,Y,Z) — used for ADD. -/
  poX2 : Signal dom (BitVec 256)
  poY2 : Signal dom (BitVec 256)
  poZ2 : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ScalarMulOut dom) dom := ⟨⟩

/-- Bit `i` of a 256-bit scalar signal, as a Bool. -/
private def bitOf {dom : DomainConfig}
    (k : Signal dom (BitVec 256)) (iSig : Signal dom (BitVec 256)) :
    Signal dom Bool :=
  let sh := ((· >>> ·) <$> k <*> iSig : Signal dom (BitVec 256))
  let lo := (sh.map (fun v => v &&& 1#256) : Signal dom (BitVec 256))
  ((· == ·) <$> lo <*> (Signal.pure 1#256 : Signal dom (BitVec 256)))

/-- The scalar-mul ladder FSM. -/
def scalarMulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (k : Signal dom (BitVec 256))
    (px py pz : Signal dom (BitVec 256))
    (poResX poResY poResZ : Signal dom (BitVec 256))
    (poResDone : Signal dom Bool) :
    ScalarMulOut dom :=
  circuit do
    -- Phase: 0 idle, 1 issue-add, 2 wait-add, 3 issue-dbl, 4 wait-dbl, 5 complete.
    let phR ← Signal.reg (0#3)
    -- Bit index i, counts 255 downto 0 (stored as a BitVec 256 so it can
    -- feed the shifter directly).  Loop is done once we've processed bit 0.
    let biR ← Signal.reg (0#256)
    -- Latched scalar.
    let kR ← Signal.reg (0#256)
    -- Latched base point P.
    let pxR ← Signal.reg (0#256)
    let pyR ← Signal.reg (0#256)
    let pzR ← Signal.reg (0#256)
    -- Ladder points R0, R1 (Jacobian).
    let r0xR ← Signal.reg (0#256)
    let r0yR ← Signal.reg (0#256)
    let r0zR ← Signal.reg (0#256)
    let r1xR ← Signal.reg (0#256)
    let r1yR ← Signal.reg (0#256)
    let r1zR ← Signal.reg (0#256)
    -- R0 == ∞ flag (true until the first set bit is consumed).
    let r0InfR ← Signal.reg true
    -- Done pulse.
    let doneR ← Signal.reg false

    let phSig  := (phR : Signal dom (BitVec 3))
    let biSig  := (biR : Signal dom (BitVec 256))
    let kSig   := (kR : Signal dom (BitVec 256))
    let r0x := (r0xR : Signal dom (BitVec 256))
    let r0y := (r0yR : Signal dom (BitVec 256))
    let r0z := (r0zR : Signal dom (BitVec 256))
    let r1x := (r1xR : Signal dom (BitVec 256))
    let r1y := (r1yR : Signal dom (BitVec 256))
    let r1z := (r1zR : Signal dom (BitVec 256))
    let r0Inf := (r0InfR : Signal dom Bool)

    -- Phase constants.
    let ph1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let ph2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let ph3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let ph4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let ph5 := (Signal.pure 5#3 : Signal dom (BitVec 3))

    let isAddIssue := ((· == ·) <$> phSig <*> ph1 : Signal dom Bool)
    let isAddWait  := ((· == ·) <$> phSig <*> ph2 : Signal dom Bool)
    let isDblIssue := ((· == ·) <$> phSig <*> ph3 : Signal dom Bool)
    let isDblWait  := ((· == ·) <$> phSig <*> ph4 : Signal dom Bool)

    -- Current scalar bit.
    let bit := bitOf kSig biSig

    -- ==================================================================
    -- Single shared point-op instance.
    --
    -- The ladder issues an ADD then a DOUBLE per bit.  Both are the
    -- SAME `pointOpHW` instance; we drive its `start`, `opDouble` and
    -- operand inputs from the current phase.
    --
    --   ADD    (phase 1): opDouble=false, operands (R0)+(R1)
    --   DOUBLE (phase 3): opDouble=true.  The point being doubled
    --                     depends on the bit:
    --                       bit=0 ⇒ double R0
    --                       bit=1 ⇒ double R1
    --
    -- pointOpHW's `start` must pulse for exactly one cycle at the
    -- issue phase.  `opStart` = (isAddIssue || isDblIssue).
    -- ==================================================================
    let opStart := ((· || ·) <$> isAddIssue <*> isDblIssue : Signal dom Bool)
    let opDouble := isDblIssue          -- true only when issuing the double
    -- DOUBLE operand: bit ? R1 : R0.
    let dblX := (Signal.mux bit r1x r0x : Signal dom (BitVec 256))
    let dblY := (Signal.mux bit r1y r0y : Signal dom (BitVec 256))
    let dblZ := (Signal.mux bit r1z r0z : Signal dom (BitVec 256))
    -- Point-op operand-1 (used for both add's first operand and the
    -- double's operand): on a double, feed dbl{X,Y,Z}; on an add,
    -- feed R0.
    let op1x := (Signal.mux opDouble dblX r0x : Signal dom (BitVec 256))
    let op1y := (Signal.mux opDouble dblY r0y : Signal dom (BitVec 256))
    let op1z := (Signal.mux opDouble dblZ r0z : Signal dom (BitVec 256))
    -- Point-op operand-2 (add's second operand; ignored on a double).
    let op2x := r1x
    let op2y := r1y
    let op2z := r1z

    -- The point-op engine is external: we DRIVE it via opStart/opDouble
    -- + the operand ports, and CONSUME its result over the input ports.
    let poDone := poResDone
    let poX := poResX
    let poY := poResY
    let poZ := poResZ

    -- Acks: the point-op completed in the wait phase.
    let addAck := ((· && ·) <$> isAddWait <*> poDone : Signal dom Bool)
    let dblAck := ((· && ·) <$> isDblWait <*> poDone : Signal dom Bool)

    -- Are we at the last bit (i = 0)?
    let atBit0 := ((· == ·) <$> biSig <*> (Signal.pure 0#256 : Signal dom (BitVec 256))
                    : Signal dom Bool)

    -- ==================================================================
    -- Point-register updates.
    --
    -- ADD result (phase-2 ack): the sum R0+R1.  With the r0Inf flag:
    --   R0=∞ ⇒ R0+R1 = R1  (mux the point-op result away)
    -- The add writes into:  bit=0 ⇒ R1 := sum ;  bit=1 ⇒ R0 := sum.
    --
    -- DOUBLE result (phase-4 ack): 2·(bit ? R1 : R0).  With r0Inf:
    --   doubling R0=∞ ⇒ ∞ (result unused; R0 stays ∞ via flag).
    -- The double writes into: bit=0 ⇒ R0 := dbl ; bit=1 ⇒ R1 := dbl.
    -- ==================================================================

    -- ADD sum, with ∞ correction: if R0 was ∞, the sum R0+R1 = R1.
    let addSumX := (Signal.mux r0Inf r1x poX : Signal dom (BitVec 256))
    let addSumY := (Signal.mux r0Inf r1y poY : Signal dom (BitVec 256))
    let addSumZ := (Signal.mux r0Inf r1z poZ : Signal dom (BitVec 256))

    -- On addAck: write sum into R1 (bit=0) or R0 (bit=1).
    let wrAddR0 := ((· && ·) <$> addAck <*> bit : Signal dom Bool)          -- bit=1
    let wrAddR1 := ((fun a b => a && !b) <$> addAck <*> bit : Signal dom Bool) -- bit=0
    -- On dblAck: write dbl into R0 (bit=0) or R1 (bit=1).
    let wrDblR0 := ((fun a b => a && !b) <$> dblAck <*> bit : Signal dom Bool) -- bit=0
    let wrDblR1 := ((· && ·) <$> dblAck <*> bit : Signal dom Bool)            -- bit=1

    -- R0 register: start ⇒ ∞ sentinel (0,0,0); addAck&bit ⇒ sum; dblAck&!bit ⇒ dbl.
    r0xR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
              (Signal.mux wrAddR0 addSumX
                (Signal.mux wrDblR0 poX r0x))
    r0yR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
              (Signal.mux wrAddR0 addSumY
                (Signal.mux wrDblR0 poY r0y))
    r0zR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
              (Signal.mux wrAddR0 addSumZ
                (Signal.mux wrDblR0 poZ r0z))

    -- R1 register: start ⇒ P; addAck&!bit ⇒ sum; dblAck&bit ⇒ dbl.
    r1xR <~ Signal.mux start px
              (Signal.mux wrAddR1 addSumX
                (Signal.mux wrDblR1 poX r1x))
    r1yR <~ Signal.mux start py
              (Signal.mux wrAddR1 addSumY
                (Signal.mux wrDblR1 poY r1y))
    r1zR <~ Signal.mux start pz
              (Signal.mux wrAddR1 addSumZ
                (Signal.mux wrDblR1 poZ r1z))

    -- r0Inf flag: set on start; cleared once we consume the first set
    -- bit (an add-ack with bit=1 promotes R0 from ∞ to R1).
    let clearInf := ((· && ·) <$> wrAddR0 <*> r0Inf : Signal dom Bool)
    r0InfR <~ Signal.mux start (Signal.pure true : Signal dom Bool)
                (Signal.mux clearInf (Signal.pure false : Signal dom Bool) r0Inf)

    -- ==================================================================
    -- Phase / bit-index sequencing.
    --   start          ⇒ phase=1 (issue add), bi=255
    --   isAddIssue     ⇒ phase=2 (wait add)
    --   addAck         ⇒ phase=3 (issue dbl)
    --   isDblIssue     ⇒ phase=4 (wait dbl)
    --   dblAck & bi>0  ⇒ phase=1 (next bit), bi--
    --   dblAck & bi=0  ⇒ phase=5 (complete)
    -- ==================================================================
    let biDec := ((· - ·) <$> biSig <*> (Signal.pure 1#256 : Signal dom (BitVec 256))
                    : Signal dom (BitVec 256))
    let nextBit := ((fun d b0 => d && !b0) <$> dblAck <*> atBit0 : Signal dom Bool)
    let finish  := ((· && ·) <$> dblAck <*> atBit0 : Signal dom Bool)

    phR <~ Signal.mux start ph1
             (Signal.mux isAddIssue ph2
               (Signal.mux addAck ph3
                 (Signal.mux isDblIssue ph4
                   (Signal.mux nextBit ph1
                     (Signal.mux finish ph5 phSig)))))

    biR <~ Signal.mux start (Signal.pure 255#256 : Signal dom (BitVec 256))
             (Signal.mux nextBit biDec biSig)

    -- Latch scalar + base point on start.
    kR  <~ Signal.mux start k kSig
    pxR <~ Signal.mux start px (pxR : Signal dom (BitVec 256))
    pyR <~ Signal.mux start py (pyR : Signal dom (BitVec 256))
    pzR <~ Signal.mux start pz (pzR : Signal dom (BitVec 256))

    -- Done pulse when finishing the last bit.
    doneR <~ finish

    return ({ xOut := r0x
            , yOut := r0y
            , zOut := r0z
            , done := (doneR : Signal dom Bool)
            , poStart := opStart
            , poOpDouble := opDouble
            , poX1 := op1x
            , poY1 := op1y
            , poZ1 := op1z
            , poX2 := op2x
            , poY2 := op2y
            , poZ2 := op2z
            } : ScalarMulOut dom)

end Sparkle.IP.Crypto.Secp256k1ScalarMulHW
