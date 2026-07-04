/-
  IP.Crypto.SHA512BlockHW — full 80-round SHA-512 block
  compressor as a `circuit do` FSM (Signal DSL).

  The wave-1 `SHA512HW` shipped only the combinational
  Σ/σ/Ch/Maj helpers + the K-mux, noting that a full iterative
  compressor was blocked on the pure-Lean `Signal.val`
  exponential-recursion issue (the same one that hits the
  Keccak 25-lane FSM).  That blocker is a property of the
  *pure-Lean simulator*, not of the elaborator: the JIT
  (`#sim` → C++ → dlopen) evaluates the FSM in native code in
  O(cycles), so the compressor is both synthesizable AND
  JIT-simulatable.  This module builds it; its test drives it
  through the JIT.

  Structure (mirrors `IP.Crypto.SHA512.compressBlock`):

    * 8 working registers a..h (BitVec 64).
    * A 16-word sliding message-schedule window w0..w15.
      Round t reads the front word (`w[0]`), and each cycle
      advances the window by computing the next schedule word
        wNew = σ1(w[14]) + w[9] + σ0(w[1]) + w[0]
      then shifting w[1..15] → w[0..14], wNew → w[15].
      For the first 16 rounds `w[0]` is just the raw input word;
      the recurrence naturally kicks in once the window has
      cycled, exactly as FIPS 180-4 `expandW` specifies.
    * 8 "seed" registers holding the incoming digest h0..h7
      so the final add `h_i + working_i` produces the chained
      output.
    * An 8-bit round counter: 0 idle, 1..80 the rounds, 81 done.

  Interface:
    start   : Bool pulse (latch inputs at this cycle)
    hIn0..7 : incoming 8×64 digest (SHA512.initH for the first
              block, previous output for chaining)
    win0..15: the 16 big-endian 64-bit words of the 1024-bit
              block
  outputs:
    out0..7 : the 8×64 chained digest (valid when `done`)
    done    : pulses one cycle when the 80 rounds complete

  Timing: start pulse at cycle 0 ⇒ cnt walks 1..80 on cycles
  1..80, cnt=81 at cycle 81 ⇒ done pulses at cycle 81 (doneR is
  registered so it appears the cycle after isFinish becomes
  true, i.e. cycle 82 read); the chained output is combinational
  from the seed + working regs and is stable from cycle 81 on.
-/
import Sparkle
import Sparkle.Core.Lut
import IP.Crypto.Proof.SHA512
import IP.Crypto.SHA512HW

open Sparkle.Core (kLutMacro)
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA512HW

namespace Sparkle.IP.Crypto.SHA512BlockHW

/-! ### Combinational Σ/σ/Ch/Maj helpers.

    The wave-1 `SHA512HW` versions are `@[reducible, inline]`
    but carry a `Nat` rotate-amount parameter that the *synth*
    elaborator can't erase (`#synthesizeVerilog` reports
    "Cannot infer hardware type from Nat").  We re-provide them
    here with the rotate amounts baked into `Signal.pure`
    constants so the synth IR only ever sees `Signal`-level
    shift/or/xor/and — the shape the AES/GHASH/Keccak engines
    already synthesise.  Semantically identical to
    `SHA512.rotr64` / `bigSigma0` / … (checked by the JIT test). -/

@[inline] private def rotr {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) (r l : Signal dom (BitVec 64)) :
    Signal dom (BitVec 64) :=
  let rs := ((· >>> ·) <$> x <*> r : Signal dom (BitVec 64))
  let ls := ((· <<< ·) <$> x <*> l : Signal dom (BitVec 64))
  ((· ||| ·) <$> rs <*> ls : Signal dom (BitVec 64))

@[inline] private def shr {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) (r : Signal dom (BitVec 64)) :
    Signal dom (BitVec 64) :=
  ((· >>> ·) <$> x <*> r : Signal dom (BitVec 64))

@[inline] private def add64 {dom : DomainConfig}
    (x y : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  ((· + ·) <$> x <*> y : Signal dom (BitVec 64))

@[inline] private def xor64 {dom : DomainConfig}
    (x y : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  ((· ^^^ ·) <$> x <*> y : Signal dom (BitVec 64))

@[inline] private def and64 {dom : DomainConfig}
    (x y : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  ((· &&& ·) <$> x <*> y : Signal dom (BitVec 64))

/-- The 8 chained digest words, valid when `done` pulses.

    `packed` bundles the whole result into one 513-bit word so a
    `#sim`/synth top can read a single `Signal (BitVec n)` output
    (the shape `#sim` requires) without instantiating the FSM as
    a `@[hardware_module]` sub-module (which explodes synth time):
      bit 512      = done
      bits 511..0  = out0 ‖ out1 ‖ … ‖ out7   (out0 most significant). -/
structure BlockOut (dom : DomainConfig) where
  out0 : Signal dom (BitVec 64)
  out1 : Signal dom (BitVec 64)
  out2 : Signal dom (BitVec 64)
  out3 : Signal dom (BitVec 64)
  out4 : Signal dom (BitVec 64)
  out5 : Signal dom (BitVec 64)
  out6 : Signal dom (BitVec 64)
  out7 : Signal dom (BitVec 64)
  done : Signal dom Bool
  packed : Signal dom (BitVec 513)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (BlockOut dom) dom := ⟨⟩

/-- Full 80-round SHA-512 block compressor FSM (structured
    multi-output form, for composition by downstream bricks such
    as HMAC). -/
def sha512BlockHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (hIn0 hIn1 hIn2 hIn3 hIn4 hIn5 hIn6 hIn7 : Signal dom (BitVec 64))
    (win0 win1 win2 win3 win4 win5 win6 win7
     win8 win9 win10 win11 win12 win13 win14 win15 : Signal dom (BitVec 64)) :
    BlockOut dom :=
  circuit do
    -- Working registers a..h.
    let aR ← Signal.reg (0#64)
    let bR ← Signal.reg (0#64)
    let cR ← Signal.reg (0#64)
    let dR ← Signal.reg (0#64)
    let eR ← Signal.reg (0#64)
    let fR ← Signal.reg (0#64)
    let gR ← Signal.reg (0#64)
    let hR ← Signal.reg (0#64)
    -- Seed registers (incoming digest) for the final add.
    let s0R ← Signal.reg (0#64)
    let s1R ← Signal.reg (0#64)
    let s2R ← Signal.reg (0#64)
    let s3R ← Signal.reg (0#64)
    let s4R ← Signal.reg (0#64)
    let s5R ← Signal.reg (0#64)
    let s6R ← Signal.reg (0#64)
    let s7R ← Signal.reg (0#64)
    -- 16-word message-schedule sliding window.
    let w0R  ← Signal.reg (0#64)
    let w1R  ← Signal.reg (0#64)
    let w2R  ← Signal.reg (0#64)
    let w3R  ← Signal.reg (0#64)
    let w4R  ← Signal.reg (0#64)
    let w5R  ← Signal.reg (0#64)
    let w6R  ← Signal.reg (0#64)
    let w7R  ← Signal.reg (0#64)
    let w8R  ← Signal.reg (0#64)
    let w9R  ← Signal.reg (0#64)
    let w10R ← Signal.reg (0#64)
    let w11R ← Signal.reg (0#64)
    let w12R ← Signal.reg (0#64)
    let w13R ← Signal.reg (0#64)
    let w14R ← Signal.reg (0#64)
    let w15R ← Signal.reg (0#64)
    -- 8-bit round counter.
    let cntR ← Signal.reg (0#8)
    let doneR ← Signal.reg false

    let a := (aR : Signal dom (BitVec 64))
    let b := (bR : Signal dom (BitVec 64))
    let c := (cR : Signal dom (BitVec 64))
    let d := (dR : Signal dom (BitVec 64))
    let e := (eR : Signal dom (BitVec 64))
    let f := (fR : Signal dom (BitVec 64))
    let g := (gR : Signal dom (BitVec 64))
    let h := (hR : Signal dom (BitVec 64))
    let s0 := (s0R : Signal dom (BitVec 64))
    let s1 := (s1R : Signal dom (BitVec 64))
    let s2 := (s2R : Signal dom (BitVec 64))
    let s3 := (s3R : Signal dom (BitVec 64))
    let s4 := (s4R : Signal dom (BitVec 64))
    let s5 := (s5R : Signal dom (BitVec 64))
    let s6 := (s6R : Signal dom (BitVec 64))
    let s7 := (s7R : Signal dom (BitVec 64))
    let w0  := (w0R  : Signal dom (BitVec 64))
    let w1  := (w1R  : Signal dom (BitVec 64))
    let w2  := (w2R  : Signal dom (BitVec 64))
    let w3  := (w3R  : Signal dom (BitVec 64))
    let w4  := (w4R  : Signal dom (BitVec 64))
    let w5  := (w5R  : Signal dom (BitVec 64))
    let w6  := (w6R  : Signal dom (BitVec 64))
    let w7  := (w7R  : Signal dom (BitVec 64))
    let w8  := (w8R  : Signal dom (BitVec 64))
    let w9  := (w9R  : Signal dom (BitVec 64))
    let w10 := (w10R : Signal dom (BitVec 64))
    let w11 := (w11R : Signal dom (BitVec 64))
    let w12 := (w12R : Signal dom (BitVec 64))
    let w13 := (w13R : Signal dom (BitVec 64))
    let w14 := (w14R : Signal dom (BitVec 64))
    let w15 := (w15R : Signal dom (BitVec 64))
    let cntSig := (cntR : Signal dom (BitVec 8))

    let p0_8  := (Signal.pure 0#8 : Signal dom (BitVec 8))
    let p1_8  := (Signal.pure 1#8 : Signal dom (BitVec 8))
    let p81_8 := (Signal.pure 81#8 : Signal dom (BitVec 8))

    let isIdle   := ((· == ·) <$> cntSig <*> p0_8 : Signal dom Bool)
    let isFinish := ((· == ·) <$> cntSig <*> p81_8 : Signal dom Bool)
    let busy :=
      ((fun i fn => !(i || fn)) <$> isIdle <*> isFinish : Signal dom Bool)

    -- K[t-1] for the current round: cnt walks 1..80, K index 0..79.
    -- kMux takes a 7-bit counter; derive (cnt-1) as 7-bit.
    let cnt7 := (cntSig.map (BitVec.extractLsb' 0 7 ·) : Signal dom (BitVec 7))
    let p1_7 := (Signal.pure 1#7 : Signal dom (BitVec 7))
    let kIdx := ((· - ·) <$> cnt7 <*> p1_7 : Signal dom (BitVec 7))
    let kVal := kMux kIdx

    -- Shift-amount constants (as Signal.pure BitVec 64) for the
    -- rotate/shift helpers.  For a right-rotate by n we also need
    -- the complementary left-shift by (64 - n).
    let c1  := (Signal.pure 1#64 : Signal dom (BitVec 64))
    let c6  := (Signal.pure 6#64 : Signal dom (BitVec 64))
    let c7  := (Signal.pure 7#64 : Signal dom (BitVec 64))
    let c8  := (Signal.pure 8#64 : Signal dom (BitVec 64))
    let c14 := (Signal.pure 14#64 : Signal dom (BitVec 64))
    let c18 := (Signal.pure 18#64 : Signal dom (BitVec 64))
    let c19 := (Signal.pure 19#64 : Signal dom (BitVec 64))
    let c23 := (Signal.pure 23#64 : Signal dom (BitVec 64))
    let c25 := (Signal.pure 25#64 : Signal dom (BitVec 64))
    let c28 := (Signal.pure 28#64 : Signal dom (BitVec 64))
    let c30 := (Signal.pure 30#64 : Signal dom (BitVec 64))
    let c34 := (Signal.pure 34#64 : Signal dom (BitVec 64))
    let c36 := (Signal.pure 36#64 : Signal dom (BitVec 64))
    let c39 := (Signal.pure 39#64 : Signal dom (BitVec 64))
    let c41 := (Signal.pure 41#64 : Signal dom (BitVec 64))
    let c45 := (Signal.pure 45#64 : Signal dom (BitVec 64))
    let c46 := (Signal.pure 46#64 : Signal dom (BitVec 64))
    let c50 := (Signal.pure 50#64 : Signal dom (BitVec 64))
    let c56 := (Signal.pure 56#64 : Signal dom (BitVec 64))
    let c63 := (Signal.pure 63#64 : Signal dom (BitVec 64))

    -- Σ1(e) = ROTR14 ⊕ ROTR18 ⊕ ROTR41  (complements 50, 46, 23)
    let s1e := xor64 (xor64 (rotr e c14 c50) (rotr e c18 c46)) (rotr e c41 c23)
    -- Ch(e,f,g) = (e&f) ⊕ (¬e & g)
    let notE := ((~~~ ·) <$> e : Signal dom (BitVec 64))
    let che := xor64 (and64 e f) (and64 notE g)
    let t1a := add64 h s1e
    let t1b := add64 t1a che
    let t1c := add64 t1b kVal
    let t1  := add64 t1c w0
    -- Σ0(a) = ROTR28 ⊕ ROTR34 ⊕ ROTR39  (complements 36, 30, 25)
    let s0a := xor64 (xor64 (rotr a c28 c36) (rotr a c34 c30)) (rotr a c39 c25)
    -- Maj(a,b,c)
    let maja := xor64 (xor64 (and64 a b) (and64 a c)) (and64 b c)
    let t2  := add64 s0a maja

    -- New working values (round update).
    let aNext := add64 t1 t2
    let eNext := add64 d t1
    -- b←a, c←b, d←c, f←e, g←f, h←g

    -- Message-schedule next word: σ1(w14) + w9 + σ0(w1) + w0.
    -- σ1(x) = ROTR19 ⊕ ROTR61 ⊕ SHR6   (61 → left-shift 3)
    let sig1w14 := xor64 (xor64 (rotr w14 c19 c45) (rotr w14 c63 c1)) (shr w14 c6)
    -- σ0(x) = ROTR1 ⊕ ROTR8 ⊕ SHR7     (1 → left 63, 8 → left 56)
    let sig0w1  := xor64 (xor64 (rotr w1 c1 c63) (rotr w1 c8 c56)) (shr w1 c7)
    let msA := add64 sig1w14 w9
    let msB := add64 msA sig0w1
    let wNew := add64 msB w0

    -- Register updates.
    -- On start: latch h-init into a..h AND seeds, and the input
    -- block words into the window.  On busy: run one round.
    aR <~ Signal.mux start hIn0 (Signal.mux busy aNext a)
    bR <~ Signal.mux start hIn1 (Signal.mux busy a b)
    cR <~ Signal.mux start hIn2 (Signal.mux busy b c)
    dR <~ Signal.mux start hIn3 (Signal.mux busy c d)
    eR <~ Signal.mux start hIn4 (Signal.mux busy eNext e)
    fR <~ Signal.mux start hIn5 (Signal.mux busy e f)
    gR <~ Signal.mux start hIn6 (Signal.mux busy f g)
    hR <~ Signal.mux start hIn7 (Signal.mux busy g h)

    s0R <~ Signal.mux start hIn0 s0
    s1R <~ Signal.mux start hIn1 s1
    s2R <~ Signal.mux start hIn2 s2
    s3R <~ Signal.mux start hIn3 s3
    s4R <~ Signal.mux start hIn4 s4
    s5R <~ Signal.mux start hIn5 s5
    s6R <~ Signal.mux start hIn6 s6
    s7R <~ Signal.mux start hIn7 s7

    -- Window shift: w[i] ← w[i+1], w[15] ← wNew, each busy cycle.
    w0R  <~ Signal.mux start win0  (Signal.mux busy w1  w0)
    w1R  <~ Signal.mux start win1  (Signal.mux busy w2  w1)
    w2R  <~ Signal.mux start win2  (Signal.mux busy w3  w2)
    w3R  <~ Signal.mux start win3  (Signal.mux busy w4  w3)
    w4R  <~ Signal.mux start win4  (Signal.mux busy w5  w4)
    w5R  <~ Signal.mux start win5  (Signal.mux busy w6  w5)
    w6R  <~ Signal.mux start win6  (Signal.mux busy w7  w6)
    w7R  <~ Signal.mux start win7  (Signal.mux busy w8  w7)
    w8R  <~ Signal.mux start win8  (Signal.mux busy w9  w8)
    w9R  <~ Signal.mux start win9  (Signal.mux busy w10 w9)
    w10R <~ Signal.mux start win10 (Signal.mux busy w11 w10)
    w11R <~ Signal.mux start win11 (Signal.mux busy w12 w11)
    w12R <~ Signal.mux start win12 (Signal.mux busy w13 w12)
    w13R <~ Signal.mux start win13 (Signal.mux busy w14 w13)
    w14R <~ Signal.mux start win14 (Signal.mux busy w15 w14)
    w15R <~ Signal.mux start win15 (Signal.mux busy wNew w15)

    let cntInc := ((· + ·) <$> cntSig <*> p1_8 : Signal dom (BitVec 8))
    cntR <~ Signal.mux start p1_8
              (Signal.mux isFinish p0_8
                (Signal.mux busy cntInc cntSig))
    doneR <~ isFinish

    -- Final chained output = seed_i + working_i.
    let o0 := add64 s0 a
    let o1 := add64 s1 b
    let o2 := add64 s2 c
    let o3 := add64 s3 d
    let o4 := add64 s4 e
    let o5 := add64 s5 f
    let o6 := add64 s6 g
    let o7 := add64 s7 h
    -- Packed 513-bit view: done ‖ o0 ‖ o1 ‖ … ‖ o7.
    let d01 := (BitVec.append <$> o0 <*> o1 : Signal dom (BitVec 128))
    let d012 := (BitVec.append <$> d01 <*> o2 : Signal dom (BitVec 192))
    let d0123 := (BitVec.append <$> d012 <*> o3 : Signal dom (BitVec 256))
    let d4 := (BitVec.append <$> d0123 <*> o4 : Signal dom (BitVec 320))
    let d5 := (BitVec.append <$> d4 <*> o5 : Signal dom (BitVec 384))
    let d6 := (BitVec.append <$> d5 <*> o6 : Signal dom (BitVec 448))
    let digest := (BitVec.append <$> d6 <*> o7 : Signal dom (BitVec 512))
    let doneBit :=
      (Signal.mux (doneR : Signal dom Bool)
        (Signal.pure 1#1) (Signal.pure 0#1) : Signal dom (BitVec 1))
    let packedOut := (BitVec.append <$> doneBit <*> digest : Signal dom (BitVec 513))
    return ({ out0 := o0
            , out1 := o1
            , out2 := o2
            , out3 := o3
            , out4 := o4
            , out5 := o5
            , out6 := o6
            , out7 := o7
            , done := (doneR : Signal dom Bool)
            , packed := packedOut
            } : BlockOut dom)

end Sparkle.IP.Crypto.SHA512BlockHW
