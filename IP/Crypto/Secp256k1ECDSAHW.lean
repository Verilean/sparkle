/-
  IP.Crypto.Secp256k1ECDSAHW — ECDSA sign orchestrator FSM for
  secp256k1 (SIGN only; no verify).

  Computes, for private key `d`, nonce `k`, message hash `z`:

      (X, Y, Z) = k · G                       -- scalar-mul (Jacobian)
      Zinv      = Z^(p-2) mod p               -- Fermat inverse mod p
      x1        = X · Zinv²      mod p         -- affine x of k·G
      r         = x1 mod n                     -- (single conditional −n)
      kInv      = k^(n-2) mod n               -- Fermat inverse mod n
      rd        = r · d          mod n
      zrd       = (z + rd)       mod n
      s         = kInv · zrd     mod n
      signature = (r, s)

  matching the pure-data reference `Secp256k1ECDSA.sign` (which a
  caller cross-checks against).  The `r = 0` / `s = 0` retry
  conditions are the caller's responsibility (a real signer picks a
  fresh nonce); this FSM just produces (r, s).

  Composition.  The heavy sub-engines are external, driven over
  flat start/done handshakes (the same shape the whole stack uses,
  because `#synthesizeVerilog` rejects a def that instantiates and
  projects a record-returning sub-module):

    * scalar-mul engine   — computes k·G.  Driven by `smStart`/`smK`
      + base-point ports; result read from `smX/smY/smZ`/`smDone`.
    * mod-p inverse+mul    — Fermat inverse mod p (for Zinv) and the
      two mod-p multiplies (Zinv², X·Zinv²).  Driven by `pInvStart`
      / `pMulStart` + operand ports; results from `pRes`/`pDone`.
    * mod-n inverse+mul    — Fermat inverse mod n (for kInv) and the
      mod-n multiplies (r·d, kInv·zrd).  Driven by `nInvStart`
      / `nMulStart` + operand ports; results from `nRes`/`nDone`.

  To keep the port surface manageable the FSM asks the caller for a
  *combined* mod-p arithmetic engine that can do either a multiply
  or a Fermat inverse (`pRes`/`pDone` with `pMulStart`/`pInvStart`
  selecting which), and likewise a mod-n engine.  In practice the
  caller wires `ModInvHW.modInvHW` (for the inverse) and the
  bit-serial multiplier (for the multiply) behind a small mux on
  those start lines; the testbench / integration layer owns that
  wiring.  This module is the pure sequencing FSM + the local
  reductions (r's conditional −n, zrd's add).

  Interface:
    inputs  start (Bool pulse)   — latch d,k,z, begin
            d k z (BitVec 256)   — private key, nonce, hash
            smX smY smZ          — scalar-mul result (Jacobian) in
            smDone (Bool)        — scalar-mul done in
            pRes (BitVec 256)    — mod-p engine result in
            pDone (Bool)         — mod-p engine done in
            nRes (BitVec 256)    — mod-n engine result in
            nDone (Bool)         — mod-n engine done in
    outputs rOut sOut (BitVec 256) — the signature (valid at done)
            done (Bool pulse)      — signature ready
            smStart (Bool)         — pulse scalar-mul (with k=smK)
            smK (BitVec 256)       — scalar for k·G
            pInvStart pMulStart    — mod-p engine triggers
            pA pB (BitVec 256)     — mod-p operands (pB unused by inv)
            pExp (BitVec 256)      — mod-p inverse exponent (p-2)
            nInvStart nMulStart    — mod-n engine triggers
            nA nB (BitVec 256)     — mod-n operands
            nExp (BitVec 256)      — mod-n inverse exponent (n-2)

  Cycle cost per sign (bit-serial engines):
    k·G          ≈ 1.53 M   (scalar-mul)
    Zinv         ≈ 132 k    (Fermat mod p)
    Zinv², X·..  ≈ 2·258
    kInv         ≈ 132 k    (Fermat mod n)
    r·d, kInv·.. ≈ 2·258
    ≈ 1.8 M cycles / sign — CPU-class latency, single shared engines.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1Field
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.Proof.Secp256k1PointJac

namespace Sparkle.IP.Crypto.Secp256k1ECDSAHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- The base-field prime as a 257-bit constant (for r's conditional
    reduction and general mod-p headroom). -/
def pBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Secp256k1Field.p

/-- The curve order n as a 257-bit constant. -/
def nBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-- Reduce a 256-bit value mod n by a single conditional subtract
    (valid when the input is < 2n; x1 < p < 2n holds). -/
private def condSubN {dom : DomainConfig}
    (a : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let nP := (Signal.pure nBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> nP <*> aw : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> aw <*> nP) aw : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Field add mod n (combinational): widen to 257, add, single
    conditional subtract of n. -/
private def addModN {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := ((· + ·) <$> aw <*> bw : Signal dom (BitVec 257))
  let nP := (Signal.pure nBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> nP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> nP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Output record. -/
structure SignOut (dom : DomainConfig) where
  /-- Signature component r (valid at `done`). -/
  rOut : Signal dom (BitVec 256)
  /-- Signature component s (valid at `done`). -/
  sOut : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the signature is ready. -/
  done : Signal dom Bool
  /-- Pulse the scalar-mul engine. -/
  smStart : Signal dom Bool
  /-- Scalar for k·G. -/
  smK : Signal dom (BitVec 256)
  /-- Trigger a mod-p Fermat inverse. -/
  pInvStart : Signal dom Bool
  /-- Trigger a mod-p multiply. -/
  pMulStart : Signal dom Bool
  /-- mod-p operands. -/
  pA : Signal dom (BitVec 256)
  pB : Signal dom (BitVec 256)
  /-- mod-p inverse exponent (p-2). -/
  pExp : Signal dom (BitVec 256)
  /-- Trigger a mod-n Fermat inverse. -/
  nInvStart : Signal dom Bool
  /-- Trigger a mod-n multiply. -/
  nMulStart : Signal dom Bool
  /-- mod-n operands. -/
  nA : Signal dom (BitVec 256)
  nB : Signal dom (BitVec 256)
  /-- mod-n inverse exponent (n-2). -/
  nExp : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SignOut dom) dom := ⟨⟩

/-- `stSig == k` as a Bool signal (step-index compare helper). -/
@[inline] private def stepEq {dom : DomainConfig}
    (stSig : Signal dom (BitVec 5)) (kk : Nat) : Signal dom Bool :=
  ((· == ·) <$> stSig <*> (Signal.pure (BitVec.ofNat 5 kk) : Signal dom (BitVec 5)))

/-- OR of two Bool signals. -/
@[inline] private def or2 {dom : DomainConfig}
    (a b : Signal dom Bool) : Signal dom Bool :=
  ((· || ·) <$> a <*> b)

/-- The ECDSA sign orchestrator FSM.

    Steps (each awaits the previous sub-engine's done):
      0 idle
      1 issue k·G          2 wait k·G
      3 issue Zinv (inv p) 4 wait Zinv
      5 issue Zinv² (mul p)6 wait Zinv²
      7 issue X·Zinv²(mul p)8 wait → latch x1, compute r=x1 mod n
      9 issue kInv(inv n) 10 wait kInv
     11 issue r·d (mul n) 12 wait → latch rd, compute zrd=(z+rd) mod n
     13 issue kInv·zrd(mul n)14 wait → latch s
     15 complete -/
def signHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (d k z : Signal dom (BitVec 256))
    (smX smY smZ : Signal dom (BitVec 256))
    (smDone : Signal dom Bool)
    (pRes : Signal dom (BitVec 256))
    (pDone : Signal dom Bool)
    (nRes : Signal dom (BitVec 256))
    (nDone : Signal dom Bool) :
    SignOut dom :=
  circuit do
    -- Step register (0..15).
    let stR ← Signal.reg (0#5)
    -- Latched inputs.
    let dR ← Signal.reg (0#256)
    let kR ← Signal.reg (0#256)
    let zR ← Signal.reg (0#256)
    -- Latched intermediates.
    let xR ← Signal.reg (0#256)     -- k·G Jacobian X
    let zjR ← Signal.reg (0#256)    -- k·G Jacobian Z
    let zinvR ← Signal.reg (0#256)  -- Z^(p-2) mod p
    let zinv2R ← Signal.reg (0#256) -- Zinv² mod p
    let rR ← Signal.reg (0#256)     -- signature r
    let kinvR ← Signal.reg (0#256)  -- k^(n-2) mod n
    let rdR ← Signal.reg (0#256)    -- r·d mod n
    let sR ← Signal.reg (0#256)     -- signature s
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 5))
    let dSig := (dR : Signal dom (BitVec 256))
    let kSig := (kR : Signal dom (BitVec 256))
    let zSig := (zR : Signal dom (BitVec 256))
    let xSig := (xR : Signal dom (BitVec 256))
    let zjSig := (zjR : Signal dom (BitVec 256))
    let zinvSig := (zinvR : Signal dom (BitVec 256))
    let zinv2Sig := (zinv2R : Signal dom (BitVec 256))
    let rSig := (rR : Signal dom (BitVec 256))
    let kinvSig := (kinvR : Signal dom (BitVec 256))
    let rdSig := (rdR : Signal dom (BitVec 256))
    let sSig := (sR : Signal dom (BitVec 256))

    let isSmIssue  := stepEq stSig 1
    let isSmWait   := stepEq stSig 2
    let isZiIssue  := stepEq stSig 3
    let isZiWait   := stepEq stSig 4
    let isZi2Issue := stepEq stSig 5
    let isZi2Wait  := stepEq stSig 6
    let isX1Issue  := stepEq stSig 7
    let isX1Wait   := stepEq stSig 8
    let isKiIssue  := stepEq stSig 9
    let isKiWait   := stepEq stSig 10
    let isRdIssue  := stepEq stSig 11
    let isRdWait   := stepEq stSig 12
    let isSIssue   := stepEq stSig 13
    let isSWait    := stepEq stSig 14

    -- Acks.
    let smAck := ((· && ·) <$> isSmWait <*> smDone : Signal dom Bool)
    let ziAck := ((· && ·) <$> isZiWait <*> pDone : Signal dom Bool)
    let zi2Ack := ((· && ·) <$> isZi2Wait <*> pDone : Signal dom Bool)
    let x1Ack := ((· && ·) <$> isX1Wait <*> pDone : Signal dom Bool)
    let kiAck := ((· && ·) <$> isKiWait <*> nDone : Signal dom Bool)
    let rdAck := ((· && ·) <$> isRdWait <*> nDone : Signal dom Bool)
    let sAck := ((· && ·) <$> isSWait <*> nDone : Signal dom Bool)

    -- ============ combinational derived values ============
    -- zrd = (z + rd) mod n.
    let zrdComb := addModN zSig rdSig

    -- ============ mod-p engine driving ============
    -- Inverse (Zinv): operand = Z (zjSig), exponent p-2.
    -- Multiplies: Zinv² = zinv·zinv ; X·Zinv² = xR·zinv2.
    let pInvStart := isZiIssue
    let pMulStart := ((· || ·) <$> isZi2Issue <*> isX1Issue : Signal dom Bool)
    -- mod-p operand A: inverse feeds Z; Zinv² feeds zinv; X·Zinv² feeds X.
    let pA := (Signal.mux isZiIssue zjSig
                (Signal.mux isZi2Issue zinvSig xSig) : Signal dom (BitVec 256))
    let pB := (Signal.mux isZi2Issue zinvSig zinv2Sig : Signal dom (BitVec 256))
    let pExp := (Signal.pure (BitVec.ofNat 256 (Sparkle.IP.Crypto.Secp256k1Field.p - 2)) : Signal dom (BitVec 256))

    -- ============ mod-n engine driving ============
    -- Inverse (kInv): operand = k, exponent n-2.
    -- Multiplies: r·d = rR·dR ; kInv·zrd = kinv·zrd.
    let nInvStart := isKiIssue
    let nMulStart := ((· || ·) <$> isRdIssue <*> isSIssue : Signal dom Bool)
    let nA := (Signal.mux isKiIssue kSig
                (Signal.mux isRdIssue rSig kinvSig) : Signal dom (BitVec 256))
    let nB := (Signal.mux isRdIssue dSig zrdComb : Signal dom (BitVec 256))
    let nExp := (Signal.pure (BitVec.ofNat 256 (Sparkle.IP.Crypto.Secp256k1ECDSA.n - 2)) : Signal dom (BitVec 256))

    -- ============ register updates ============
    -- Latch inputs on start.
    dR <~ Signal.mux start d dSig
    kR <~ Signal.mux start k kSig
    zR <~ Signal.mux start z zSig

    -- X, Z (Jacobian) latched at k·G ack.
    xR <~ Signal.mux start (Signal.pure 0#256 : Signal dom (BitVec 256))
            (Signal.mux smAck smX
              (Signal.mux x1Ack pRes xSig))   -- x1 overwrites X at the X·Zinv² ack
    zjR <~ Signal.mux smAck smZ zjSig

    -- Zinv latched at inverse ack.
    zinvR <~ Signal.mux ziAck pRes zinvSig
    -- Zinv² latched at its ack.
    zinv2R <~ Signal.mux zi2Ack pRes zinv2Sig
    -- r = x1 mod n, latched at the X1 ack (x1 = pRes).
    let x1AtAck := condSubN pRes
    rR <~ Signal.mux x1Ack x1AtAck rSig
    -- kInv latched at its ack.
    kinvR <~ Signal.mux kiAck nRes kinvSig
    -- rd latched at its ack.
    rdR <~ Signal.mux rdAck nRes rdSig
    -- s latched at its ack.
    sR <~ Signal.mux sAck nRes sSig

    -- ============ step sequencing ============
    let advanceIssue :=  -- issue phases always advance to their wait next cycle
      or2 isSmIssue (or2 isZiIssue (or2 isZi2Issue (or2 isX1Issue
        (or2 isKiIssue (or2 isRdIssue isSIssue)))))
    let anyAck :=
      or2 smAck (or2 ziAck (or2 zi2Ack (or2 x1Ack
        (or2 kiAck (or2 rdAck sAck)))))
    let stInc := ((· + ·) <$> stSig <*> (Signal.pure 1#5 : Signal dom (BitVec 5)) : Signal dom (BitVec 5))
    let advance := ((· || ·) <$> advanceIssue <*> anyAck : Signal dom Bool)
    stR <~ Signal.mux start (Signal.pure 1#5 : Signal dom (BitVec 5))
             (Signal.mux advance stInc stSig)

    -- Done pulse at the s ack (entering step 15).
    doneR <~ sAck

    return ({ rOut := rSig
            , sOut := sSig
            , done := (doneR : Signal dom Bool)
            , smStart := isSmIssue
            , smK := kSig
            , pInvStart := pInvStart
            , pMulStart := pMulStart
            , pA := pA
            , pB := pB
            , pExp := pExp
            , nInvStart := nInvStart
            , nMulStart := nMulStart
            , nA := nA
            , nB := nB
            , nExp := nExp
            } : SignOut dom)

end Sparkle.IP.Crypto.Secp256k1ECDSAHW
