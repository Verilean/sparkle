/-
  IP.Crypto.EcdsaSignSmall — area-optimized secp256k1 signer.

  The fast `EcdsaSignDemo` holds every 256-bit temporary (wPointOp's
  m0..m15, the ladder's R0/R1, the sign intermediates) in flip-flops —
  ~47 K register bits, ~3× the Tang Nano 20k's ~15.5 K FFs.

  This variant trades the (huge) 1-second timing budget for area: all
  256-bit temporaries live in a single BRAM register file
  (`Signal.memory`), and shared bit-serial engines are driven by a
  sequencer.  FF usage collapses to a few thousand + a couple of BRAMs.

  LAYER 1 (this file so far):
    * `regFile`  — 64×256 BRAM register file (single R/W port), wrapped
      as a `@[hardware_module]` so it is instantiated ONCE (an inline
      `Signal.memory` inside a `circuit do` is duplicated per SSA copy).
    * `bignumALU` — a 2-operand modular ALU over the register file.
      One instruction `reg[dst] = reg[srcA] OP reg[srcB]` where OP ∈
      { mul mod p, mul mod n, add or sub mod p, add or sub mod n }, plus an external
      load port to seed the register file (from UART, or a testbench).

  The full ECDSA microcode (point-op schedules → ladder → inversions →
  s) is layered on top of this ALU in later milestones.
-/
import Sparkle
import IP.Crypto.Secp256k1FieldHW
import IP.Crypto.Secp256k1OrderHW
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1ECDSA

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Crypto.EcdsaSignSmall

/-! ## Modulus constants (257-bit: headroom for a+b and a+m-b < 2m). -/

def pBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Secp256k1Field.p
def nBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-! ## Shared bit-serial multipliers (mod p and mod n). -/

/-- `@[hardware_module]` wrapper: mod-p bit-serial multiplier. -/
@[hardware_module] def wMulP {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256)) :
    Sparkle.IP.Crypto.Secp256k1FieldHW.MulOut dom :=
  Sparkle.IP.Crypto.Secp256k1FieldHW.mulHW start aIn bIn

/-- `@[hardware_module]` wrapper: mod-n bit-serial multiplier. -/
@[hardware_module] def wMulN {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256)) :
    Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut dom :=
  Sparkle.IP.Crypto.Secp256k1OrderHW.mulModNHW start aIn bIn

/-- 258-bit modulus constants (headroom for the 2·acc + a intermediate < 3p). -/
def pBv258 : BitVec 258 := BitVec.ofNat 258 Sparkle.IP.Crypto.Secp256k1Field.p
def nBv258 : BitVec 258 := BitVec.ofNat 258 Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-- Bit-serial modular multiplier with a **runtime** 258-bit modulus.  A single
    instance replaces the separate mod-p and mod-n multipliers — the caller
    muxes `modBv` between p and n per opcode, halving the multiplier area.
    Generalizes `Secp256k1FieldHW.mulHW` (identical but for `pP := modBv`). -/
@[hardware_module] def wMulMod {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256))
    (modBv : Signal dom (BitVec 258)) :
    Sparkle.IP.Crypto.Secp256k1FieldHW.MulOut dom :=
  circuit do
    let accR ← Signal.reg (0#258)
    let aR ← Signal.reg (0#256)
    let bR ← Signal.reg (0#256)
    let cntR ← Signal.reg (0#9)
    let doneR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 258))
    let aSig   := (aR : Signal dom (BitVec 256))
    let bSig   := (bR : Signal dom (BitVec 256))
    let cntSig := (cntR : Signal dom (BitVec 9))

    let p0_9   := (Signal.pure 0#9   : Signal dom (BitVec 9))
    let p1_9   := (Signal.pure 1#9   : Signal dom (BitVec 9))
    let pP     := modBv                                    -- runtime modulus

    let isIdle   := cntSig === 0#9
    let isFinish := cntSig === 257#9
    let busy     := ((fun i f => !(i || f)) <$> isIdle <*> isFinish : Signal dom Bool)

    let aWide := (aSig.map (fun v => BitVec.append (0#2) v) : Signal dom (BitVec 258))
    let bHi    := ((· >>> ·) <$> bSig <*> (Signal.pure 255#256 : Signal dom (BitVec 256)) : Signal dom (BitVec 256))
    let bMsb   := ((fun z => !z) <$> (bHi === 0#256) : Signal dom Bool)

    let accDbl    := ((· <<< ·) <$> accSig <*> (Signal.pure 1#258 : Signal dom (BitVec 258)) : Signal dom (BitVec 258))
    let dblGe     := ((BitVec.ule · ·) <$> pP <*> accDbl : Signal dom Bool)
    let accDblRed := (Signal.mux dblGe ((· - ·) <$> accDbl <*> pP) accDbl : Signal dom (BitVec 258))
    let accPlusA  := ((· + ·) <$> accDblRed <*> aWide : Signal dom (BitVec 258))
    let addGe     := ((BitVec.ule · ·) <$> pP <*> accPlusA : Signal dom Bool)
    let accAddRed := (Signal.mux addGe ((· - ·) <$> accPlusA <*> pP) accPlusA : Signal dom (BitVec 258))
    let accNext   := (Signal.mux bMsb accAddRed accDblRed : Signal dom (BitVec 258))

    let bShl := ((· <<< ·) <$> bSig <*> (Signal.pure 1#256 : Signal dom (BitVec 256)) : Signal dom (BitVec 256))
    let cntInc := ((· + ·) <$> cntSig <*> p1_9 : Signal dom (BitVec 9))

    accR <~ Signal.mux start (Signal.pure 0#258 : Signal dom (BitVec 258)) (Signal.mux busy accNext accSig)
    aR   <~ Signal.mux start aIn aSig
    bR   <~ Signal.mux start bIn (Signal.mux busy bShl bSig)
    cntR <~ Signal.mux start p1_9 (Signal.mux isFinish p0_9 (Signal.mux busy cntInc cntSig))
    doneR <~ isFinish

    let resOut := ((BitVec.extractLsb' 0 256 ·) <$> accSig : Signal dom (BitVec 256))
    return ({ result := resOut, done := (doneR : Signal dom Bool) }
            : Sparkle.IP.Crypto.Secp256k1FieldHW.MulOut dom)

/-! ## BRAM register file. -/

/-- Register-file read-port output.  Two fields: the synth elaborator's
    multi-output sub-module projection only fires for records with ≥2
    `Signal` fields, so we expose a (registered) write echo alongside the
    read data.  Without the sub-module wrapping, an inline `Signal.memory`
    inside a `circuit do` is emitted once per SSA copy of the body. -/
structure RfOut (dom : DomainConfig) where
  /-- Registered read data (2-cycle latency: BRAM read + this register). -/
  rdata : Signal dom (BitVec 256)
  /-- Registered echo of `writeEnable` (unused; keeps the record multi-output). -/
  wecho : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (RfOut dom) dom := ⟨⟩

/-- 64×256 BRAM register file, single read + single write port. -/
@[hardware_module] def regFile {dom : DomainConfig}
    (writeAddr : Signal dom (BitVec 6)) (writeData : Signal dom (BitVec 256))
    (writeEnable : Signal dom Bool) (readAddr : Signal dom (BitVec 6)) :
    RfOut dom :=
  circuit do
    let rdReg ← Signal.reg (0#256)
    let vR ← Signal.reg false
    let raw := Signal.memory writeAddr writeData writeEnable readAddr
    rdReg <~ raw
    vR <~ writeEnable
    return ({ rdata := (rdReg : Signal dom (BitVec 256))
            , wecho := (vR : Signal dom Bool) } : RfOut dom)

/-! ## Combinational modular add / sub (modulus supplied as 257-bit). -/

/-- `(a + b) mod m`: widen to 257, add, single conditional subtract. -/
private def faddModM {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) (m257 : Signal dom (BitVec 257)) :
    Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := ((· + ·) <$> aw <*> bw : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> m257 <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> m257) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- `(a - b) mod m`: compute a + m - b in 257 bits (always in [0, 2m)),
    then one conditional subtract. -/
private def fsubModM {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) (m257 : Signal dom (BitVec 257)) :
    Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let apb := ((· + ·) <$> aw <*> m257 : Signal dom (BitVec 257))
  let s   := ((· - ·) <$> apb <*> bw : Signal dom (BitVec 257))
  let ge  := ((BitVec.ule · ·) <$> m257 <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> m257) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Unified modular add/sub `(isSub ? a-b : a+b) mod m` sharing ONE datapath.
    `sel = isSub ? m-b : b` (both < m keep `t = a+sel` in [0,2m)), then a single
    conditional `t-m`.  Uses 3 wide adds instead of `faddModM`+`fsubModM`'s
    combined 5 — both of which the µ-engine used to instantiate every cycle. -/
private def faddsubModM {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) (m257 : Signal dom (BitVec 257))
    (isSub : Signal dom Bool) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let mb := ((· - ·) <$> m257 <*> bw : Signal dom (BitVec 257))     -- m - b
  let sel := (Signal.mux isSub mb bw : Signal dom (BitVec 257))
  let t  := ((· + ·) <$> aw <*> sel : Signal dom (BitVec 257))       -- a + sel ∈ [0,2m)
  let ge := ((BitVec.ule · ·) <$> m257 <*> t : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> t <*> m257) t : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-! ## The modular ALU.

    Opcodes (3-bit):  0 MULP · 1 MULN · 2 ADDP · 3 SUBP · 4 ADDN · 5 SUBN.
    A single op is `reg[dst] = reg[srcA] OP reg[srcB]`.  The register file
    has one read port (2-cycle latency), so the two operands are fetched
    sequentially; the extra cycles are free against the 1-second budget. -/

structure AluOut (dom : DomainConfig) where
  /-- Register-file readback of `dst` (valid at `done`). -/
  outVal : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the op (or a load) completes. -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (AluOut dom) dom := ⟨⟩

/-- Modular ALU over the BRAM register file.

    Inputs held stable by the caller for the duration of one op:
      `op` (3-bit opcode), `srcA` `srcB` `dst` (6-bit reg indices).
    External load port (writes `reg[loadAddr] = loadData` in idle):
      `loadEn` `loadAddr` `loadData`.

    Phases: 0 idle → 1 → 2 (latch opA) → 3 (start mul / compute add-sub)
      → 4 (mul wait, or pass-through for add/sub) → 5 (writeback)
      → 6 (read latency) → 7 (readback + done) → 0. -/
def bignumALU {dom : DomainConfig}
    (start : Signal dom Bool)
    (op : Signal dom (BitVec 3))
    (srcA srcB dst : Signal dom (BitVec 6))
    (loadEn : Signal dom Bool)
    (loadAddr : Signal dom (BitVec 6))
    (loadData : Signal dom (BitVec 256)) :
    AluOut dom :=
  circuit do
    let phR   ← Signal.reg (0#3)
    let opAR  ← Signal.reg (0#256)   -- latched operand A (= reg[srcA])
    let prodR ← Signal.reg (0#256)   -- op result (mul product or add/sub)
    let outR  ← Signal.reg (0#256)   -- register-file readback
    let rbR   ← Signal.reg false     -- readback-pending (set in P7, capture in P0)
    let doneR ← Signal.reg false

    let phSig   := (phR : Signal dom (BitVec 3))
    let opASig  := (opAR : Signal dom (BitVec 256))
    let prodSig := (prodR : Signal dom (BitVec 256))

    let ph0 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let ph1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let ph2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let ph3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let ph4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let ph5 := (Signal.pure 5#3 : Signal dom (BitVec 3))
    let ph6 := (Signal.pure 6#3 : Signal dom (BitVec 3))
    let ph7 := (Signal.pure 7#3 : Signal dom (BitVec 3))

    let inP0 := (phSig === ph0)
    let inP1 := (phSig === ph1)
    let inP2 := (phSig === ph2)
    let inP3 := (phSig === ph3)
    let inP4 := (phSig === ph4)
    let inP5 := (phSig === ph5)
    let inP6 := (phSig === ph6)
    let inP7 := (phSig === ph7)

    let notLoad := ((fun b => !b) <$> loadEn : Signal dom Bool)
    let doLoad  := ((· && ·) <$> inP0 <*> loadEn : Signal dom Bool)
    let goStart := ((· && ·) <$> inP0 <*>
                     ((· && ·) <$> start <*> notLoad) : Signal dom Bool)

    -- ===== opcode decode =====
    -- isMul = op < 2 ; isMulN = op == 1 ; SUB = op ∈ {3,5} ; mod n = op ≥ 4.
    -- Every combinational form is a two-signal applicative (the only map
    -- shape the synth elaborator lowers).
    let isMul  := ((BitVec.ult · ·) <$> op <*> (Signal.pure 2#3 : Signal dom (BitVec 3)) : Signal dom Bool)
    let isMulN := (op === 1#3)
    let eq3    := (op === 3#3)
    let eq5    := (op === 5#3)
    let isSub  := ((· || ·) <$> eq3 <*> eq5 : Signal dom Bool)           -- op ∈ {3,5} → SUB
    let useN   := ((BitVec.ule · ·) <$> (Signal.pure 4#3 : Signal dom (BitVec 3)) <*> op : Signal dom Bool)

    -- ===== register file =====
    let readAddr :=
      Signal.mux goStart srcA
        (Signal.mux inP1 srcB
          (Signal.mux inP5 dst dst))
    let writeAddr := Signal.mux doLoad loadAddr dst
    let writeData := Signal.mux doLoad loadData prodSig
    let wrEn := ((· || ·) <$> doLoad <*> inP5 : Signal dom Bool)
    let rf := regFile writeAddr writeData wrEn readAddr
    let rdSig := rf.rdata                 -- 2-cycle-latency read

    -- ===== shared multipliers =====
    let notMulN := ((fun b => !b) <$> isMulN : Signal dom Bool)
    let isMulP  := ((· && ·) <$> isMul <*> notMulN : Signal dom Bool)   -- op == 0
    let mulStartP := ((· && ·) <$> inP3 <*> isMulP : Signal dom Bool)
    let mulStartN := ((· && ·) <$> inP3 <*> isMulN : Signal dom Bool)
    let mulP := wMulP mulStartP opASig rdSig
    let mulN := wMulN mulStartN opASig rdSig
    let mulResult := (Signal.mux isMulN mulN.result mulP.result : Signal dom (BitVec 256))
    let mulDone := ((· || ·) <$> mulP.done <*> mulN.done : Signal dom Bool)

    -- ===== combinational add/sub =====
    let modBv := (Signal.mux useN (Signal.pure nBv257 : Signal dom (BitVec 257))
                    (Signal.pure pBv257 : Signal dom (BitVec 257)) : Signal dom (BitVec 257))
    let addRes := faddModM opASig rdSig modBv
    let subRes := fsubModM opASig rdSig modBv
    let addsubRes := (Signal.mux isSub subRes addRes : Signal dom (BitVec 256))

    -- ===== operand A latch (reg[srcA] in rdSig during P2) =====
    opAR <~ Signal.mux inP2 rdSig opASig

    -- ===== result latch =====
    --   add/sub: latch the combinational result in P3.
    --   mul:     latch the product on the multiplier's done pulse.
    let latchAddSub := ((· && ·) <$> inP3 <*> ((fun m => !m) <$> isMul) : Signal dom Bool)
    let mulAck := ((· && ·) <$> inP4 <*> mulDone : Signal dom Bool)
    prodR <~ Signal.mux latchAddSub addsubRes
               (Signal.mux mulAck mulResult prodSig)

    -- ===== output readback =====
    -- reg[dst] is written in P5; with the 2-cycle read latency the value
    -- only appears on rdSig the cycle AFTER P7 (back in P0).  Capture it
    -- there via a one-cycle "readback pending" flag set in P7.
    rbR <~ inP7
    let rbSig := (rbR : Signal dom Bool)
    outR <~ Signal.mux rbSig rdSig outR

    -- ===== phase sequencing =====
    -- P4 advances to P5 immediately for add/sub, or on mulAck for mul.
    let advP4 := (Signal.mux isMul mulAck inP4 : Signal dom Bool)
    phR <~ Signal.mux goStart ph1
             (Signal.mux inP1 ph2
               (Signal.mux inP2 ph3
                 (Signal.mux inP3 ph4
                   (Signal.mux advP4 ph5
                     (Signal.mux inP5 ph6
                       (Signal.mux inP6 ph7
                         (Signal.mux inP7 ph0 phSig)))))))

    -- done pulses when the readback is captured (op complete), and also
    -- acknowledges a load.
    doneR <~ ((· || ·) <$> rbSig <*> doLoad : Signal dom Bool)

    return ({ outVal := (outR : Signal dom (BitVec 256))
            , done := (doneR : Signal dom Bool) } : AluOut dom)

/-- Diagnostic: bare combinational mod-p add (`(a + b) mod p`), to test
    the JIT's wide (>64-bit) add/reduce path in isolation. -/
def addModPPub {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  faddModM a b (Signal.pure pBv257)

/-- Diagnostic: the ALU with NO multipliers — FSM + register file +
    combinational mod-p add only (`reg[dst] = reg[srcA] + reg[srcB] mod p`).
    Used to isolate whether a JIT failure is in the FSM/regfile driving or
    in the wide multiplier submodules. -/
def bignumALUlite {dom : DomainConfig}
    (start : Signal dom Bool)
    (srcA srcB dst : Signal dom (BitVec 6))
    (loadEn : Signal dom Bool)
    (loadAddr : Signal dom (BitVec 6))
    (loadData : Signal dom (BitVec 256)) :
    AluOut dom :=
  circuit do
    let phR   ← Signal.reg (0#3)
    let opAR  ← Signal.reg (0#256)
    let prodR ← Signal.reg (0#256)
    let outR  ← Signal.reg (0#256)
    let rbR   ← Signal.reg false
    let doneR ← Signal.reg false

    let phSig   := (phR : Signal dom (BitVec 3))
    let opASig  := (opAR : Signal dom (BitVec 256))
    let prodSig := (prodR : Signal dom (BitVec 256))

    let ph0 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let ph1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let ph2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let ph3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let ph4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let ph5 := (Signal.pure 5#3 : Signal dom (BitVec 3))
    let ph6 := (Signal.pure 6#3 : Signal dom (BitVec 3))
    let ph7 := (Signal.pure 7#3 : Signal dom (BitVec 3))

    let inP0 := (phSig === ph0)
    let inP1 := (phSig === ph1)
    let inP2 := (phSig === ph2)
    let inP3 := (phSig === ph3)
    let inP5 := (phSig === ph5)
    let inP6 := (phSig === ph6)
    let inP7 := (phSig === ph7)

    let notLoad := ((fun b => !b) <$> loadEn : Signal dom Bool)
    let doLoad  := ((· && ·) <$> inP0 <*> loadEn : Signal dom Bool)
    let goStart := ((· && ·) <$> inP0 <*> ((· && ·) <$> start <*> notLoad) : Signal dom Bool)

    let readAddr :=
      Signal.mux goStart srcA (Signal.mux inP1 srcB (Signal.mux inP5 dst dst))
    let writeAddr := Signal.mux doLoad loadAddr dst
    let writeData := Signal.mux doLoad loadData prodSig
    let wrEn := ((· || ·) <$> doLoad <*> inP5 : Signal dom Bool)
    let rf := regFile writeAddr writeData wrEn readAddr
    let rdSig := rf.rdata

    let pP := (Signal.pure pBv257 : Signal dom (BitVec 257))
    let addRes := faddModM opASig rdSig pP

    opAR <~ Signal.mux inP2 rdSig opASig
    prodR <~ Signal.mux inP3 addRes prodSig
    outR <~ Signal.mux (rbR : Signal dom Bool) rdSig outR
    rbR <~ inP7
    doneR <~ ((· || ·) <$> (rbR : Signal dom Bool) <*> doLoad : Signal dom Bool)

    phR <~ Signal.mux goStart ph1
             (Signal.mux inP1 ph2
               (Signal.mux inP2 ph3
                 (Signal.mux inP3 ph5          -- add/sub: skip mul-wait
                   (Signal.mux inP5 ph6
                     (Signal.mux inP6 ph7
                       (Signal.mux inP7 ph0 phSig))))))

    return ({ outVal := (outR : Signal dom (BitVec 256))
            , done := (doneR : Signal dom Bool) } : AluOut dom)

/-! ## Microcoded point-double engine (milestone: first microcode).

    A tiny sequencer (PC + microcode ROM) drives the register file and the
    shared mod-p multiplier to evaluate Jacobian point doubling
    (`Secp256k1PointJac.double`, dbl-2009-l) entirely out of BRAM — the
    exact "store temporaries in RAM" idea that shrinks the fast signer.

    Register convention: r0=X, r1=Y, r2=Z (pre-loaded); r63 stays 0.
    Result: X3=r11, Y3=r14, Z3=r16.  Opcodes: 0 MULP · 2 ADDP · 3 SUBP ·
    7 HALT. -/

/-- One microcode instruction: (op, srcA, srcB, dst). -/
abbrev UInstr := BitVec 3 × BitVec 6 × BitVec 6 × BitVec 6

/-- The point-double program (21 field ops + halt). -/
def pdProgram : List UInstr :=
  [ (0, 0, 0, 3)    -- A  = X*X            r3
  , (0, 1, 1, 4)    -- B  = Y*Y            r4
  , (0, 4, 4, 5)    -- C  = B*B            r5
  , (2, 0, 4, 6)    -- X+B                 r6
  , (0, 6, 6, 6)    -- (X+B)^2             r6
  , (3, 6, 3, 6)    -- -A                  r6
  , (3, 6, 5, 6)    -- -C  => (X+B)^2-A-C  r6
  , (2, 6, 6, 7)    -- D  = 2*(...)        r7
  , (2, 3, 3, 8)    -- 2A                  r8
  , (2, 8, 3, 8)    -- 3A = E              r8
  , (0, 8, 8, 9)    -- F  = E*E            r9
  , (2, 7, 7, 10)   -- 2D                  r10
  , (3, 9, 10, 11)  -- X3 = F-2D           r11
  , (3, 7, 11, 12)  -- D-X3                r12
  , (0, 8, 12, 12)  -- E*(D-X3)            r12
  , (2, 5, 5, 13)   -- 2C                  r13
  , (2, 13, 13, 13) -- 4C                  r13
  , (2, 13, 13, 13) -- 8C                  r13
  , (3, 12, 13, 14) -- Y3 = E(D-X3)-8C     r14
  , (0, 1, 2, 15)   -- Y*Z                 r15
  , (2, 15, 15, 16) -- Z3 = 2*Y*Z          r16
  , (7, 0, 0, 0) ]  -- HALT

/-- Build a combinational ROM field selected by `pc`. -/
private def romField {dom : DomainConfig} {w : Nat}
    (pc : Signal dom (BitVec 8)) (vals : List (BitVec w)) (dflt : BitVec w) :
    Signal dom (BitVec w) :=
  (vals.zipIdx).foldr
    (fun (v, i) acc =>
      Signal.mux (pc === BitVec.ofNat 8 i)
        (Signal.pure v : Signal dom (BitVec w)) acc)
    (Signal.pure dflt : Signal dom (BitVec w))

/-- Output of the point-double engine. -/
structure PdOut (dom : DomainConfig) where
  /-- Register-file read at `probeAddr` (valid a few cycles after `halted`). -/
  probeVal : Signal dom (BitVec 256)
  /-- High while the sequencer is idle/finished (low while running). -/
  halted   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PdOut dom) dom := ⟨⟩

/-- Microcoded point-double engine.

    Pre-load r0/r1/r2 with X/Y/Z via the external load port (in idle),
    pulse `runStart`, wait for `halted`, then read results by driving
    `probeAddr` (r11=X3, r14=Y3, r16=Z3).  Per-instruction microphases
    mirror the verified `bignumALU` (2-cycle BRAM read latency). -/
def microEngine {dom : DomainConfig}
    (program : List UInstr)
    (runStart : Signal dom Bool)
    (loadEn : Signal dom Bool) (loadAddr : Signal dom (BitVec 6))
    (loadData : Signal dom (BitVec 256))
    (probeAddr : Signal dom (BitVec 6))
    (progStart : Signal dom (BitVec 8) := Signal.pure 0#8) :
    PdOut dom :=
  circuit do
    let runR  ← Signal.reg false
    let pcR   ← Signal.reg (0#8)
    let phR   ← Signal.reg (0#3)     -- microphase 0..7 within an instruction
    let opAR  ← Signal.reg (0#256)
    let prodR ← Signal.reg (0#256)

    let runSig  := (runR : Signal dom Bool)
    let pcSig   := (pcR : Signal dom (BitVec 8))
    let phSig   := (phR : Signal dom (BitVec 3))
    let opASig  := (opAR : Signal dom (BitVec 256))
    let prodSig := (prodR : Signal dom (BitVec 256))

    -- ROM decode of the current instruction.
    let opSig := romField pcSig (program.map (·.1)) 7
    let aSig  := romField pcSig (program.map (·.2.1)) 0
    let bSig  := romField pcSig (program.map (·.2.2.1)) 0
    let dSig  := romField pcSig (program.map (·.2.2.2)) 0
    let isHalt := (opSig === 7#3)
    -- Opcodes: 0 MULP · 1 MULN · 2 ADDP · 3 SUBP · 4 ADDN · 5 SUBN · 7 HALT.
    let isMulP := (opSig === 0#3)
    let isMulN := (opSig === 1#3)
    let isMul  := ((· || ·) <$> isMulP <*> isMulN : Signal dom Bool)         -- MULP or MULN
    let isSubP := (opSig === 3#3)
    let isSubN := (opSig === 5#3)
    let isSub  := ((· || ·) <$> isSubP <*> isSubN : Signal dom Bool)         -- SUBP or SUBN
    let isAddN := (opSig === 4#3)
    let isModN := ((· || ·) <$> isAddN <*> isSubN : Signal dom Bool)         -- add/sub mod n

    let inM0 := (phSig === 0#3)
    let inM1 := (phSig === 1#3)
    let inM2 := (phSig === 2#3)  -- latch opA
    let inM3 := (phSig === 3#3)  -- start mul / add-sub
    let inM4 := (phSig === 4#3)  -- mul wait
    let inM5 := (phSig === 5#3)  -- writeback
    let inM6 := (phSig === 6#3)  -- pc advance

    -- Kick off a run.
    let goRun := ((· && ·) <$> ((fun r => !r) <$> runSig) <*> runStart : Signal dom Bool)
    -- Active instruction execution (running and not halted).
    let exec := ((· && ·) <$> runSig <*> ((fun h => !h) <$> isHalt) : Signal dom Bool)

    -- ===== register file =====
    -- readAddr: srcA in M0/M6-entry, srcB in M1, else dst; when idle, the
    -- external probe address (so results can be read out after halt).
    let runReadAddr :=
      Signal.mux inM1 bSig (Signal.mux inM0 aSig dSig)
    let readAddr := Signal.mux runSig runReadAddr probeAddr
    -- write port: external load in idle, else the op result in writeback.
    let doLoad := ((· && ·) <$> ((fun r => !r) <$> runSig) <*> loadEn : Signal dom Bool)
    let wrEn := ((· || ·) <$> doLoad <*> ((· && ·) <$> exec <*> inM5) : Signal dom Bool)
    let wrAddr := Signal.mux doLoad loadAddr dSig
    let wrData := Signal.mux doLoad loadData prodSig
    let rf := regFile wrAddr wrData wrEn readAddr
    let rdSig := rf.rdata

    -- ===== single shared modular multiplier, runtime modulus (mod p or n) =====
    -- One `wMulMod` handles both MULP and MULN; `isMulN` selects the 258-bit
    -- modulus.  (Was two full multipliers — halved the largest LUT consumer.)
    let mulStart := ((· && ·) <$> ((· && ·) <$> exec <*> inM3) <*> isMul : Signal dom Bool)
    let modSel := (Signal.mux isMulN (Signal.pure nBv258) (Signal.pure pBv258) : Signal dom (BitVec 258))
    let mul := wMulMod mulStart opASig rdSig modSel
    let mulDone   := mul.done
    let mulResult := mul.result
    let mulAck := ((· && ·) <$> inM4 <*> mulDone : Signal dom Bool)

    -- ===== combinational add/sub, modulus selected by opcode (p or n) =====
    let mSel := (Signal.mux isModN (Signal.pure nBv257) (Signal.pure pBv257) : Signal dom (BitVec 257))
    -- ONE shared modular add/sub unit (was `mux isSub (fsubModM …) (faddModM …)`,
    -- which instantiated both — ~2 wide adders of dead logic every cycle).
    let addsubRes := faddsubModM opASig rdSig mSel isSub

    -- opA latch (reg[srcA] in rdSig during M2).
    opAR <~ Signal.mux ((· && ·) <$> exec <*> inM2) rdSig opASig
    -- result latch: add/sub in M3, mul on mulAck.
    let latchAdd := ((· && ·) <$> ((· && ·) <$> exec <*> inM3) <*> ((fun m => !m) <$> isMul) : Signal dom Bool)
    prodR <~ Signal.mux latchAdd addsubRes (Signal.mux mulAck mulResult prodSig)

    -- microphase sequencing (add/sub skip the mul-wait M4→M5 gate).
    let advM4 := (Signal.mux isMul mulAck inM4 : Signal dom Bool)
    let phNextExec :=
      Signal.mux inM0 (Signal.pure 1#3 : Signal dom (BitVec 3))
        (Signal.mux inM1 (Signal.pure 2#3)
          (Signal.mux inM2 (Signal.pure 3#3)
            (Signal.mux inM3 (Signal.pure 4#3)
              (Signal.mux advM4 (Signal.pure 5#3)
                (Signal.mux inM5 (Signal.pure 6#3)
                  (Signal.mux inM6 (Signal.pure 0#3) phSig))))))
    phR <~ Signal.mux goRun (Signal.pure 0#3 : Signal dom (BitVec 3))
             (Signal.mux exec phNextExec phSig)

    -- pc advances at M6 of each executed instruction.
    let stepDone := ((· && ·) <$> exec <*> inM6 : Signal dom Bool)
    let pcInc := ((· + ·) <$> pcSig <*> (Signal.pure 1#8 : Signal dom (BitVec 8)) : Signal dom (BitVec 8))
    pcR <~ Signal.mux goRun progStart
             (Signal.mux stepDone pcInc pcSig)

    -- running clears when we reach HALT.
    let hitHalt := ((· && ·) <$> runSig <*> isHalt : Signal dom Bool)
    runR <~ Signal.mux goRun (Signal.pure true : Signal dom Bool)
              (Signal.mux hitHalt (Signal.pure false : Signal dom Bool) runSig)

    return ({ probeVal := rdSig
            , halted := ((fun r => !r) <$> runSig : Signal dom Bool) } : PdOut dom)

/-- Point-double engine (r0=X r1=Y r2=Z → X3=r11 Y3=r14 Z3=r16). -/
def pdEngine {dom : DomainConfig}
    (runStart loadEn : Signal dom Bool) (loadAddr : Signal dom (BitVec 6))
    (loadData : Signal dom (BitVec 256)) (probeAddr : Signal dom (BitVec 6)) : PdOut dom :=
  microEngine pdProgram runStart loadEn loadAddr loadData probeAddr

/-- Jacobian point-add program (add-2007-bl, generic u₁≠u₂ case).
    Inputs r0..r5 = X1 Y1 Z1 X2 Y2 Z2.  Result X3=r18 Y3=r23 Z3=r26. -/
def addProgram : List UInstr :=
  [ (0, 2, 2, 6)     -- z1z1 = Z1*Z1        r6
  , (0, 5, 5, 7)     -- z2z2 = Z2*Z2        r7
  , (0, 0, 7, 8)     -- u1   = X1*z2z2      r8
  , (0, 3, 6, 9)     -- u2   = X2*z1z1      r9
  , (0, 5, 7, 10)    -- Z2*z2z2             r10
  , (0, 1, 10, 10)   -- s1   = Y1*(Z2 z2z2) r10
  , (0, 2, 6, 11)    -- Z1*z1z1             r11
  , (0, 4, 11, 11)   -- s2   = Y2*(Z1 z1z1) r11
  , (3, 9, 8, 12)    -- h    = u2-u1        r12
  , (2, 12, 12, 13)  -- 2h                  r13
  , (0, 13, 13, 13)  -- i    = (2h)^2       r13
  , (0, 12, 13, 14)  -- j    = h*i          r14
  , (3, 11, 10, 15)  -- s2-s1               r15
  , (2, 15, 15, 15)  -- rr   = 2(s2-s1)     r15
  , (0, 8, 13, 16)   -- v    = u1*i         r16
  , (0, 15, 15, 17)  -- rr^2                r17
  , (3, 17, 14, 18)  -- rr^2 - j            r18
  , (2, 16, 16, 19)  -- 2v                  r19
  , (3, 18, 19, 18)  -- x3   = rr^2-j-2v    r18
  , (3, 16, 18, 20)  -- v-x3                r20
  , (0, 15, 20, 20)  -- rr*(v-x3)           r20
  , (0, 10, 14, 21)  -- s1*j                r21
  , (2, 21, 21, 22)  -- 2*s1j               r22
  , (3, 20, 22, 23)  -- y3   = rr(v-x3)-2s1j r23
  , (2, 2, 5, 24)    -- Z1+Z2               r24
  , (0, 24, 24, 24)  -- (Z1+Z2)^2           r24
  , (3, 24, 6, 25)   -- -z1z1               r25
  , (3, 25, 7, 25)   -- -z2z2 => zzt        r25
  , (0, 25, 12, 26)  -- z3   = zzt*h        r26
  , (7, 0, 0, 0) ]   -- HALT

/-- Point-add engine (r0..r5 = P,Q → X3=r18 Y3=r23 Z3=r26). -/
def addEngine {dom : DomainConfig}
    (runStart loadEn : Signal dom Bool) (loadAddr : Signal dom (BitVec 6))
    (loadData : Signal dom (BitVec 256)) (probeAddr : Signal dom (BitVec 6)) : PdOut dom :=
  microEngine addProgram runStart loadEn loadAddr loadData probeAddr

/-! ## Scalar-multiply ladder.

    Register layout shared across subroutines: acc = (r0,r1,r2),
    base P = (r3,r4,r5), scratch r6.. , r63 = 0 (never written).  Each
    subroutine updates acc IN PLACE.  MSB-first double-and-add with an
    "acc = ∞" flag so the add formula never sees the point at infinity
    (the first set bit copies base into acc instead of adding). -/

/-- In-place point double: acc = 2·acc.  (25 instr.) -/
def dblIP : List UInstr :=
  [ (0, 0, 0, 6), (0, 1, 1, 7), (0, 7, 7, 8), (2, 0, 7, 9), (0, 9, 9, 9)
  , (3, 9, 6, 9), (3, 9, 8, 9), (2, 9, 9, 10), (2, 6, 6, 11), (2, 11, 6, 11)
  , (0, 11, 11, 12), (2, 10, 10, 13), (3, 12, 13, 14), (3, 10, 14, 15)
  , (0, 11, 15, 15), (2, 8, 8, 16), (2, 16, 16, 16), (2, 16, 16, 16)
  , (3, 15, 16, 17), (0, 1, 2, 18), (2, 18, 18, 19)
  , (2, 14, 63, 0), (2, 17, 63, 1), (2, 19, 63, 2)   -- writeback X3,Y3,Z3 → acc
  , (7, 0, 0, 0) ]

/-- In-place point add: acc = acc + base.  (33 instr.) -/
def addIP : List UInstr :=
  [ (0, 2, 2, 6), (0, 5, 5, 7), (0, 0, 7, 8), (0, 3, 6, 9), (0, 5, 7, 10)
  , (0, 1, 10, 10), (0, 2, 6, 11), (0, 4, 11, 11), (3, 9, 8, 12), (2, 12, 12, 13)
  , (0, 13, 13, 13), (0, 12, 13, 14), (3, 11, 10, 15), (2, 15, 15, 15), (0, 8, 13, 16)
  , (0, 15, 15, 17), (3, 17, 14, 18), (2, 16, 16, 19), (3, 18, 19, 18), (3, 16, 18, 20)
  , (0, 15, 20, 20), (0, 10, 14, 21), (2, 21, 21, 22), (3, 20, 22, 23), (2, 2, 5, 24)
  , (0, 24, 24, 24), (3, 24, 6, 25), (3, 25, 7, 25), (0, 25, 12, 26)
  , (2, 18, 63, 0), (2, 23, 63, 1), (2, 26, 63, 2)   -- writeback X3,Y3,Z3 → acc
  , (7, 0, 0, 0) ]

/-- Copy base into acc (for the first set bit).  (4 instr.) -/
def copyIP : List UInstr :=
  [ (2, 3, 63, 0), (2, 4, 63, 1), (2, 5, 63, 2), (7, 0, 0, 0) ]

/-! ### Field-exponentiation subroutines (for Fermat inversion).
    `acc = r0`, `base = r3`.  Square/multiply come in mod-p (MULP=0) and
    mod-n (MULN=1) variants; the copy (`r0 = r3`, via ADDP r3+r63) is shared
    with `copyIP` since it is modulus-agnostic.  Each is 2 instr (op+HALT). -/
def sqrP : List UInstr := [ (0, 0, 0, 0), (7, 0, 0, 0) ]   -- r0 = r0·r0 mod p
def mulPp : List UInstr := [ (0, 0, 3, 0), (7, 0, 0, 0) ]   -- r0 = r0·r3 mod p
def sqrN : List UInstr := [ (1, 0, 0, 0), (7, 0, 0, 0) ]   -- r0 = r0·r0 mod n
def mulNn : List UInstr := [ (1, 0, 3, 0), (7, 0, 0, 0) ]   -- r0 = r0·r3 mod n

/-! ### Straight-line sign programs (driven once each by the orchestrator).
    Persistent regs (survive engine runs): r30 X · r35 r · r36 kInv · r37 s
    · r40 d · r41 z · r42 k.  Temps r0..r26.  These match `runSignMicro` in the
    pure-model cross-check. -/
/-- After the ladder: save X→r30, move Z (r2)→r3 (base for the mod-p inverse). -/
def prepProg : List UInstr := [ (2,0,63,30), (2,2,63,3), (7,0,0,0) ]
/-- With r0 = Z⁻¹: xaff = X·Z⁻² ; r = xaff mod n → r35. -/
def affineProg : List UInstr := [ (0,0,0,10), (0,30,10,0), (4,0,63,35), (7,0,0,0) ]
/-- Move k (r42)→r3 (base for the mod-n inverse). -/
def prepKProg : List UInstr := [ (2,42,63,3), (7,0,0,0) ]
/-- With r0 = k⁻¹: kInv→r36 ; s = k⁻¹·(z + r·d) mod n → r37. -/
def sProg : List UInstr := [ (2,0,63,36), (1,35,40,11), (4,41,11,11), (1,36,11,37), (7,0,0,0) ]

/-- Combined ROM: point ops, exp subroutines, then the sign programs. -/
def ladderRom : List UInstr :=
  dblIP ++ addIP ++ copyIP ++ sqrP ++ mulPp ++ sqrN ++ mulNn
  ++ prepProg ++ affineProg ++ prepKProg ++ sProg

def offDBL : Nat := 0
def offADD : Nat := dblIP.length
def offCOPY : Nat := dblIP.length + addIP.length
def offSQRP : Nat := offCOPY + copyIP.length
def offMULP : Nat := offSQRP + sqrP.length
def offSQRN : Nat := offMULP + mulPp.length
def offMULN : Nat := offSQRN + sqrN.length
def offPREP : Nat := offMULN + mulNn.length
def offAFFINE : Nat := offPREP + prepProg.length
def offPREPK : Nat := offAFFINE + affineProg.length
def offS : Nat := offPREPK + prepKProg.length

/-- The shared micro-engine with the ladder ROM baked in, as a
    `@[hardware_module]` so the ladder controller instantiates it once
    (a `microEngine` with a `List` program argument is not inlinable at
    synth time). -/
@[hardware_module] def ladderEngine {dom : DomainConfig}
    (runStart loadEn : Signal dom Bool) (loadAddr : Signal dom (BitVec 6))
    (loadData : Signal dom (BitVec 256)) (probeAddr : Signal dom (BitVec 6))
    (progStart : Signal dom (BitVec 8)) : PdOut dom :=
  microEngine ladderRom runStart loadEn loadAddr loadData probeAddr progStart

structure LadderOut (dom : DomainConfig) where
  probeVal : Signal dom (BitVec 256)
  halted   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (LadderOut dom) dom := ⟨⟩

/-- Output of the unified engine controller. -/
structure OpOut (dom : DomainConfig) where
  probeVal : Signal dom (BitVec 256)
  busy     : Signal dom Bool          -- high from `opStart` until the op completes

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (OpOut dom) dom := ⟨⟩

/-- Unified controller owning the *single* shared micro-engine.  Two modes:

    * **loop** (`isLoop`): MSB-first square-and-multiply over the 256-bit
      `scalar`, using offsets `offSq`/`offMu`/`offCp` (square each bit, multiply
      on set bits, copy base→acc on the first set bit).  Drives the EC ladder
      and Fermat inversion.
    * **single** (`!isLoop`): run the straight-line program at `singleProg`
      once, to completion — the short affine / r / s sequences.

    Pulse `opStart` while idle to begin; `busy` stays high until done.  Loads
    (`extLoad*`) and the scalar (`scalarLoad*`) pass through while idle.

    Pulse `opStart` while idle to begin.  `@[hardware_module]` so the
    orchestrator instantiates it once as a sub-module (its `OpOut` has two
    Signal fields, enabling the multi-output projection). -/
@[hardware_module] def opCtrl {dom : DomainConfig}
    (isLoop : Signal dom Bool) (singleProg : Signal dom (BitVec 8))
    (offSq offMu offCp : Signal dom (BitVec 8))
    (opStart : Signal dom Bool)
    (extLoadEn : Signal dom Bool) (extLoadAddr : Signal dom (BitVec 6))
    (extLoadData : Signal dom (BitVec 256))
    (scalarLoadEn : Signal dom Bool) (scalarIn : Signal dom (BitVec 256))
    (probeAddr : Signal dom (BitVec 6)) :
    OpOut dom :=
  circuit do
    -- 0 idle · 1 sq-issue · 2 sq-wait · 3 mul-issue · 4 mul-wait · 5 next
    -- 6 done · 7 single-issue · 8 single-wait
    let cstR    ← Signal.reg (0#4)
    let kR      ← Signal.reg (0#256)
    let biR     ← Signal.reg (0#9)
    let accInfR ← Signal.reg true

    let cstSig := (cstR : Signal dom (BitVec 4))
    let kSig   := (kR : Signal dom (BitVec 256))
    let biSig  := (biR : Signal dom (BitVec 9))
    let accInf := (accInfR : Signal dom Bool)

    let cIdle     := (cstSig === 0#4)
    let cDblIssue := (cstSig === 1#4)
    let cDblWait  := (cstSig === 2#4)
    let cAddIssue := (cstSig === 3#4)
    let cAddWait  := (cstSig === 4#4)
    let cNext     := (cstSig === 5#4)
    let cDone     := (cstSig === 6#4)
    let cSngIssue := (cstSig === 7#4)
    let cSngWait  := (cstSig === 8#4)

    let goStart  := ((· && ·) <$> cIdle <*> opStart : Signal dom Bool)
    let goLoop   := ((· && ·) <$> goStart <*> isLoop : Signal dom Bool)
    let goSingle := ((· && ·) <$> goStart <*> ((fun b => !b) <$> isLoop) : Signal dom Bool)
    let kMsb := ((fun k => BitVec.extractLsb' 255 1 k) <$> kSig : Signal dom (BitVec 1))
    let bit := (kMsb === 1#1)
    let notInf := ((fun b => !b) <$> accInf : Signal dom Bool)

    -- ===== drive the shared micro-engine =====
    -- Loop: square in sq-issue (unless acc=∞); multiply/copy in mul-issue only
    -- when the bit is set.  Single: issue `singleProg` in single-issue.
    let engRunStart :=
      ((· || ·) <$>
        (((· || ·) <$> ((· && ·) <$> cDblIssue <*> notInf)
                   <*> ((· && ·) <$> cAddIssue <*> bit)) : Signal dom Bool)
        <*> cSngIssue : Signal dom Bool)
    let addProg := (Signal.mux accInf offCp offMu : Signal dom (BitVec 8))
    let loopProg := (Signal.mux cDblIssue offSq addProg : Signal dom (BitVec 8))
    let engProgStart := (Signal.mux cSngIssue singleProg loopProg : Signal dom (BitVec 8))
    let engLoadEn := ((· && ·) <$> cIdle <*> extLoadEn : Signal dom Bool)

    let eng := ladderEngine engRunStart engLoadEn extLoadAddr extLoadData probeAddr engProgStart
    let engHalted := eng.halted

    -- ===== controller sequencing =====
    let atLastBit := (biSig === 255#9)
    let cstNext :=
      Signal.mux cDone (Signal.pure (BitVec.ofNat 4 0) : Signal dom (BitVec 4))
      <| Signal.mux goLoop (Signal.pure (BitVec.ofNat 4 1) : Signal dom (BitVec 4))
      <| Signal.mux goSingle (Signal.pure (BitVec.ofNat 4 7) : Signal dom (BitVec 4))
        (Signal.mux cDblIssue
           (Signal.mux accInf (Signal.pure (BitVec.ofNat 4 3) : Signal dom (BitVec 4)) (Signal.pure (BitVec.ofNat 4 2) : Signal dom (BitVec 4)))
           (Signal.mux ((· && ·) <$> cDblWait <*> engHalted) (Signal.pure (BitVec.ofNat 4 3) : Signal dom (BitVec 4))
             (Signal.mux cAddIssue
                (Signal.mux bit (Signal.pure (BitVec.ofNat 4 4) : Signal dom (BitVec 4)) (Signal.pure (BitVec.ofNat 4 5) : Signal dom (BitVec 4)))
                (Signal.mux ((· && ·) <$> cAddWait <*> engHalted) (Signal.pure (BitVec.ofNat 4 5) : Signal dom (BitVec 4))
                  (Signal.mux cNext
                     (Signal.mux atLastBit (Signal.pure (BitVec.ofNat 4 6) : Signal dom (BitVec 4)) (Signal.pure (BitVec.ofNat 4 1) : Signal dom (BitVec 4)))
                     (Signal.mux cSngIssue (Signal.pure (BitVec.ofNat 4 8) : Signal dom (BitVec 4))
                       (Signal.mux ((· && ·) <$> cSngWait <*> engHalted) (Signal.pure (BitVec.ofNat 4 6) : Signal dom (BitVec 4))
                         cstSig)))))))
    cstR <~ cstNext

    let doCopy := ((· && ·) <$> ((· && ·) <$> cAddIssue <*> bit) <*> accInf : Signal dom Bool)
    accInfR <~ Signal.mux goStart (Signal.pure true : Signal dom Bool)
                 (Signal.mux doCopy (Signal.pure false : Signal dom Bool) accInf)

    let kInit := Signal.mux scalarLoadEn scalarIn kSig
    let kShift := ((· <<< ·) <$> kSig <*> (Signal.pure 1#256 : Signal dom (BitVec 256)) : Signal dom (BitVec 256))
    kR <~ Signal.mux cNext kShift kInit

    let biInc := ((· + ·) <$> biSig <*> (Signal.pure 1#9 : Signal dom (BitVec 9)) : Signal dom (BitVec 9))
    biR <~ Signal.mux goStart (Signal.pure 0#9 : Signal dom (BitVec 9))
             (Signal.mux cNext biInc biSig)

    return ({ probeVal := eng.probeVal
            , busy := ((fun b => !b) <$> cIdle : Signal dom Bool) } : OpOut dom)

/-- EC scalar-multiply ladder: `acc = scalar · P` (P in r3/r4/r5). -/
def ladderCtrl {dom : DomainConfig}
    (ladderStart : Signal dom Bool)
    (extLoadEn : Signal dom Bool) (extLoadAddr : Signal dom (BitVec 6))
    (extLoadData : Signal dom (BitVec 256))
    (scalarLoadEn : Signal dom Bool) (scalarIn : Signal dom (BitVec 256))
    (probeAddr : Signal dom (BitVec 6)) :
    LadderOut dom :=
  let o := opCtrl (Signal.pure true) (Signal.pure 0#8)
    (Signal.pure (BitVec.ofNat 8 offDBL)) (Signal.pure (BitVec.ofNat 8 offADD))
    (Signal.pure (BitVec.ofNat 8 offCOPY))
    ladderStart extLoadEn extLoadAddr extLoadData scalarLoadEn scalarIn probeAddr
  { probeVal := o.probeVal, halted := ((fun b => !b) <$> o.busy : Signal dom Bool) }

/-- Fermat modular inversion: `acc = base^exponent mod m` (base in r3,
    `exponent` supplied as the scalar).  `modN` selects the modulus.  For `a⁻¹`
    pass `exponent = m-2`.  Result in `acc` (r0). -/
def expCtrl {dom : DomainConfig}
    (modN : Signal dom Bool)
    (expStart : Signal dom Bool)
    (extLoadEn : Signal dom Bool) (extLoadAddr : Signal dom (BitVec 6))
    (extLoadData : Signal dom (BitVec 256))
    (scalarLoadEn : Signal dom Bool) (scalarIn : Signal dom (BitVec 256))
    (probeAddr : Signal dom (BitVec 6)) :
    LadderOut dom :=
  let offSq := (Signal.mux modN (Signal.pure (BitVec.ofNat 8 offSQRN)) (Signal.pure (BitVec.ofNat 8 offSQRP)) : Signal dom (BitVec 8))
  let offMu := (Signal.mux modN (Signal.pure (BitVec.ofNat 8 offMULN)) (Signal.pure (BitVec.ofNat 8 offMULP)) : Signal dom (BitVec 8))
  let o := opCtrl (Signal.pure true) (Signal.pure 0#8) offSq offMu (Signal.pure (BitVec.ofNat 8 offCOPY))
    expStart extLoadEn extLoadAddr extLoadData scalarLoadEn scalarIn probeAddr
  { probeVal := o.probeVal, halted := ((fun b => !b) <$> o.busy : Signal dom Bool) }

/-! ## Top-level sign orchestrator. -/

/-- Constant exponents for Fermat inversion (baked into the bitstream). -/
def pMinus2Bv : BitVec 256 := BitVec.ofNat 256 (Sparkle.IP.Crypto.Secp256k1Field.p - 2)
def nMinus2Bv : BitVec 256 := BitVec.ofNat 256 (Sparkle.IP.Crypto.Secp256k1ECDSA.n - 2)

/-- ECDSA sign orchestrator.  Pre-load (while idle) via the external port:
    base G→r3,r4,r5 · d→r40 · z→r41 · k→r42, and hold `kIn = k`.  Pulse
    `signStart`; when `halted` pulses read `r=reg35`, `s=reg37` via `probeAddr`.

    Sequences seven engine ops through the shared `opCtrl`:
    L(k·G) → PREP → invZ → AFFINE(r) → PREPk → invK → S(s).

    `@[hardware_module]` so callers (UART wrapper, area harness) can instantiate
    it inside a `circuit do` and project its `LadderOut`. -/
@[hardware_module] def signCtrl {dom : DomainConfig}
    (signStart : Signal dom Bool)
    (extLoadEn : Signal dom Bool) (extLoadAddr : Signal dom (BitVec 6))
    (extLoadData : Signal dom (BitVec 256))
    (kIn : Signal dom (BitVec 256))
    (probeAddr : Signal dom (BitVec 6)) :
    LadderOut dom :=
  circuit do
    -- Macro sequence (each op = ISSUE then WAIT):
    -- 0 idle · 1/2 L · 3/4 PREP · 5/6 invZ · 7/8 AFFINE · 9/10 PREPk
    -- 11/12 invK · 13/14 S · 15 done
    let mcR ← Signal.reg (0#4)
    let mcSig := (mcR : Signal dom (BitVec 4))
    let mIdle := mcSig === 0#4
    let mDone := mcSig === 15#4
    -- ISSUE states are the odd values 1,3,5,7,9,11,13 (15 is done, also odd).
    let mOdd := (((fun m => BitVec.extractLsb' 0 1 m) <$> mcSig) === 1#1)
    let mIssue := ((· && ·) <$> mOdd <*> ((fun b => !b) <$> mDone) : Signal dom Bool)

    -- Phase index `(mcst-1)>>1`, STABLE across a phase's ISSUE+WAIT pair
    -- (L=0 PREP=1 invZ=2 AFFINE=3 PREPk=4 invK=5 S=6).  The op selects below
    -- MUST use this — `opCtrl` samples `engProgStart`/offsets one cycle after
    -- ISSUE, when `mcst` is already in the WAIT state; keying on the raw ISSUE
    -- value would fall through to the mux default there.
    let phSig := ((· >>> ·) <$> ((· - ·) <$> mcSig <*> (Signal.pure 1#4 : Signal dom (BitVec 4))) <*> (Signal.pure 1#4 : Signal dom (BitVec 4)) : Signal dom (BitVec 4))
    let phL  := (phSig === 0#4)
    let phIZ := (phSig === 2#4)
    let phIK := (phSig === 5#4)
    let isLoopPh := ((· || ·) <$> ((· || ·) <$> phL <*> phIZ) <*> phIK : Signal dom Bool)

    let opStart := mIssue
    let opIsLoop := isLoopPh
    -- scalar (exponent) is latched by opCtrl at goStart, so load only at ISSUE.
    let opScalarLoadEn := ((· && ·) <$> mIssue <*> isLoopPh : Signal dom Bool)
    let opScalarIn :=
      (Signal.mux phL kIn
        (Signal.mux phIZ (Signal.pure pMinus2Bv : Signal dom (BitVec 256))
          (Signal.pure nMinus2Bv : Signal dom (BitVec 256))) : Signal dom (BitVec 256))
    let opOffSq :=
      (Signal.mux phL (Signal.pure (BitVec.ofNat 8 offDBL))
        (Signal.mux phIZ (Signal.pure (BitVec.ofNat 8 offSQRP))
          (Signal.pure (BitVec.ofNat 8 offSQRN))) : Signal dom (BitVec 8))
    let opOffMu :=
      (Signal.mux phL (Signal.pure (BitVec.ofNat 8 offADD))
        (Signal.mux phIZ (Signal.pure (BitVec.ofNat 8 offMULP))
          (Signal.pure (BitVec.ofNat 8 offMULN))) : Signal dom (BitVec 8))
    let opSingleProg :=
      (Signal.mux ((phSig === 1#4)) (Signal.pure (BitVec.ofNat 8 offPREP))
        (Signal.mux ((phSig === 3#4)) (Signal.pure (BitVec.ofNat 8 offAFFINE))
          (Signal.mux ((phSig === 4#4)) (Signal.pure (BitVec.ofNat 8 offPREPK))
            (Signal.pure (BitVec.ofNat 8 offS)))) : Signal dom (BitVec 8))
    -- external loads pass through only while the whole signer is idle.
    let opLoadEn := ((· && ·) <$> mIdle <*> extLoadEn : Signal dom Bool)

    let op := opCtrl opIsLoop opSingleProg opOffSq opOffMu (Signal.pure (BitVec.ofNat 8 offCOPY))
      opStart opLoadEn extLoadAddr extLoadData opScalarLoadEn opScalarIn probeAddr
    let opBusy := op.busy

    -- macro next-state.
    let mcInc := ((· + ·) <$> mcSig <*> (Signal.pure 1#4 : Signal dom (BitVec 4)) : Signal dom (BitVec 4))
    let mcNext :=
      Signal.mux mIdle (Signal.mux signStart (Signal.pure 1#4 : Signal dom (BitVec 4)) (Signal.pure 0#4))
      <| Signal.mux mDone (Signal.pure 0#4 : Signal dom (BitVec 4))
        (Signal.mux mIssue mcInc                                   -- ISSUE → WAIT
          (Signal.mux ((fun b => !b) <$> opBusy) mcInc mcSig))     -- WAIT → next when op done
    mcR <~ mcNext

    return ({ probeVal := op.probeVal
            , halted := mDone } : LadderOut dom)

end Sparkle.IP.Crypto.EcdsaSignSmall
