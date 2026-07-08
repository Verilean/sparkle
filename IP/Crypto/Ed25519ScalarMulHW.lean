/-
  IP.Crypto.Ed25519ScalarMulHW — scalar multiplication k·P on
  Ed25519 in extended twisted-Edwards coordinates, driving
  `Ed25519PointOpHW.pointOpHW` (which drives the field mul).

  Double-and-add, MSB-first over 256 bits:

      R = identity (0,1,1,0)
      for i = 255 downto 0:
        R = 2·R                       (double)
        if bit_i = 1:  R = R + P      (add)

  Edwards addition is *complete* — correct for R = identity and
  for R = P — so, unlike the Weierstrass ladder, NO infinity flag
  or equal-point special-casing is needed.  Each bit issues a
  DOUBLE, then (only if the bit is set) an ADD, to a single shared
  `pointOpHW` instance, each awaited via `pointOpHW.done`.  After
  bit 0, `R = k·P` (extended coords) and `done` pulses.  Conversion
  to affine (the single field inverse of the whole scalar-mul) is
  left to the caller / sign FSM.

  Composition: like `Secp256k1ScalarMulHW`, this does NOT
  instantiate the point-op engine.  It exposes `poStart`/
  `poOpDouble`/`poX1..poT2` driver outputs and takes the point-op
  result (`poResX/Y/Z/T`, `poResDone`) as inputs; the caller wires
  one `pointOpHW` (and one `mulHW`) across those ports.

  Interface:
    inputs  start (Bool pulse), k (BitVec 256),
            px,py,pz,pt (base point P, extended coords),
            poResX,poResY,poResZ,poResT, poResDone
    outputs xOut,yOut,zOut,tOut (k·P extended, valid at done),
            done (Bool pulse),
            poStart, poOpDouble, poX1..poZ1,poT1, poX2..poZ2,poT2

  Cycle cost ≈ 256·(double + ~½·add) ≈ 256·(8 + ~4.5)·260 cyc
  ≈ 0.83 M cycles (avg) with the 258-cyc bit-serial multiplier.
-/
import Sparkle
import IP.Crypto.Proof.Ed25519Field
import IP.Crypto.Proof.Ed25519PointExt
import IP.Crypto.Ed25519PointOpHW

namespace Sparkle.IP.Crypto.Ed25519ScalarMulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Ed25519PointOpHW

/-- Output record. -/
structure ScalarMulOut (dom : DomainConfig) where
  xOut : Signal dom (BitVec 256)
  yOut : Signal dom (BitVec 256)
  zOut : Signal dom (BitVec 256)
  tOut : Signal dom (BitVec 256)
  done : Signal dom Bool
  poStart : Signal dom Bool
  poOpDouble : Signal dom Bool
  poX1 : Signal dom (BitVec 256)
  poY1 : Signal dom (BitVec 256)
  poZ1 : Signal dom (BitVec 256)
  poT1 : Signal dom (BitVec 256)
  poX2 : Signal dom (BitVec 256)
  poY2 : Signal dom (BitVec 256)
  poZ2 : Signal dom (BitVec 256)
  poT2 : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ScalarMulOut dom) dom := ⟨⟩

/-- Bit `i` of a 256-bit scalar signal, as a Bool. -/
private def bitOf {dom : DomainConfig}
    (k : Signal dom (BitVec 256)) (iSig : Signal dom (BitVec 256)) :
    Signal dom Bool :=
  let sh := (k >>> iSig : Signal dom (BitVec 256))
  let lo := (sh.map (fun v => v &&& 1#256) : Signal dom (BitVec 256))
  (lo === (Signal.pure 1#256 : Signal dom (BitVec 256)))

/-- The double-and-add scalar-mul FSM. -/
def scalarMulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (k : Signal dom (BitVec 256))
    (px py pz pt : Signal dom (BitVec 256))
    (poResX poResY poResZ poResT : Signal dom (BitVec 256))
    (poResDone : Signal dom Bool) :
    ScalarMulOut dom :=
  circuit do
    -- Phase: 0 idle, 1 issue-dbl, 2 wait-dbl, 3 issue-add, 4 wait-add, 5 complete.
    -- (Add is skipped when the current bit is 0.)
    let phR ← Signal.reg (0#3)
    let biR ← Signal.reg (0#256)          -- bit index 255..0
    let kR ← Signal.reg (0#256)
    -- Accumulator R (extended coords), init identity (0,1,1,0).
    let rxR ← Signal.reg (0#256)
    let ryR ← Signal.reg (1#256)
    let rzR ← Signal.reg (1#256)
    let rtR ← Signal.reg (0#256)
    -- Latched base point P (extended coords).
    let pxR ← Signal.reg (0#256); let pyR ← Signal.reg (0#256)
    let pzR ← Signal.reg (0#256); let ptR ← Signal.reg (0#256)
    let doneR ← Signal.reg false

    let phSig := (phR : Signal dom (BitVec 3))
    let biSig := (biR : Signal dom (BitVec 256))
    let kSig  := (kR : Signal dom (BitVec 256))
    let rx := (rxR : Signal dom (BitVec 256)); let ry := (ryR : Signal dom (BitVec 256))
    let rz := (rzR : Signal dom (BitVec 256)); let rt := (rtR : Signal dom (BitVec 256))
    let pxS := (pxR : Signal dom (BitVec 256)); let pyS := (pyR : Signal dom (BitVec 256))
    let pzS := (pzR : Signal dom (BitVec 256)); let ptS := (ptR : Signal dom (BitVec 256))

    let ph1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let ph2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let ph3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let ph4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let ph5 := (Signal.pure 5#3 : Signal dom (BitVec 3))

    let isDblIssue := (phSig === ph1 : Signal dom Bool)
    let isDblWait  := (phSig === ph2 : Signal dom Bool)
    let isAddIssue := (phSig === ph3 : Signal dom Bool)
    let isAddWait  := (phSig === ph4 : Signal dom Bool)

    let bit := bitOf kSig biSig

    -- Point-op driver: DOUBLE issues in phase 1 (operand = R),
    -- ADD issues in phase 3 (operands R + P).
    let opStart := (isDblIssue ||| isAddIssue : Signal dom Bool)
    let opDouble := isDblIssue

    -- Point-op result / acks.
    let poDone := poResDone
    let dblAck := (isDblWait &&& poDone : Signal dom Bool)
    let addAck := (isAddWait &&& poDone : Signal dom Bool)

    let atBit0 := (biSig === (Signal.pure 0#256 : Signal dom (BitVec 256))
                    : Signal dom Bool)

    -- R register updates: double writes R on dblAck; add writes R on addAck.
    rxR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
              (Signal.mux dblAck poResX (Signal.mux addAck poResX rx))
    ryR <~ Signal.mux start (Signal.pure 1#256 : Signal dom (BitVec 256))
              (Signal.mux dblAck poResY (Signal.mux addAck poResY ry))
    rzR <~ Signal.mux start (Signal.pure 1#256 : Signal dom (BitVec 256))
              (Signal.mux dblAck poResZ (Signal.mux addAck poResZ rz))
    rtR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
              (Signal.mux dblAck poResT (Signal.mux addAck poResT rt))

    -- ==================================================================
    -- Phase sequencing:
    --   start                    ⇒ ph1 (issue dbl), bi=255
    --   isDblIssue               ⇒ ph2 (wait dbl)
    --   dblAck & bit=1           ⇒ ph3 (issue add)
    --   dblAck & bit=0 & bi>0    ⇒ ph1 (next bit), bi--
    --   dblAck & bit=0 & bi=0    ⇒ ph5 (complete)
    --   isAddIssue               ⇒ ph4 (wait add)
    --   addAck & bi>0            ⇒ ph1 (next bit), bi--
    --   addAck & bi=0            ⇒ ph5 (complete)
    -- ==================================================================
    let biDec := (biSig - (Signal.pure 1#256 : Signal dom (BitVec 256))
                    : Signal dom (BitVec 256))
    -- After a double: go to add if bit set, else advance/finish.
    let dblToAdd := (dblAck &&& bit : Signal dom Bool)
    let dblSkip  := ((fun a b => a && !b) <$> dblAck <*> bit : Signal dom Bool)  -- bit=0
    let dblNext  := (dblSkip &&& ((fun b => !b) <$> atBit0) : Signal dom Bool)
    let dblFin   := (dblSkip &&& atBit0 : Signal dom Bool)
    -- After an add: advance/finish.
    let addNext  := (addAck &&& ((fun b => !b) <$> atBit0) : Signal dom Bool)
    let addFin   := (addAck &&& atBit0 : Signal dom Bool)

    let goNext := (dblNext ||| addNext : Signal dom Bool)
    let goFin  := (dblFin ||| addFin : Signal dom Bool)

    phR <~ Signal.mux start ph1
             (Signal.mux isDblIssue ph2
               (Signal.mux dblToAdd ph3
                 (Signal.mux isAddIssue ph4
                   (Signal.mux goNext ph1
                     (Signal.mux goFin ph5 phSig)))))

    biR <~ Signal.mux start (Signal.pure 255#256 : Signal dom (BitVec 256))
             (Signal.mux goNext biDec biSig)

    kR  <~ Signal.mux start k kSig
    pxR <~ Signal.mux start px pxS
    pyR <~ Signal.mux start py pyS
    pzR <~ Signal.mux start pz pzS
    ptR <~ Signal.mux start pt ptS

    doneR <~ goFin

    return ({ xOut := rx, yOut := ry, zOut := rz, tOut := rt
            , done := (doneR : Signal dom Bool)
            , poStart := opStart
            , poOpDouble := opDouble
            , poX1 := rx, poY1 := ry, poZ1 := rz, poT1 := rt
            , poX2 := pxS, poY2 := pyS, poZ2 := pzS, poT2 := ptS
            } : ScalarMulOut dom)

end Sparkle.IP.Crypto.Ed25519ScalarMulHW
