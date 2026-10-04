/-
  C2 sim-cost localizer.

  Strategy: build progressively more SHA-like designs and see
  which structural feature causes `Signal.val 0` to blow up.

  All designs use the same dom + start/idle predicates as the
  real SHA engine so we can rule those out cheaply.
-/
import Sparkle
import IP.Crypto.SHA256

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA256

namespace SimCost

abbrev D := defaultDomain

def blockIn : Signal D (BitVec 512) := ⟨fun _ => 0#512⟩
def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩

-- =====================================================================
-- Bench 1: 16 cross-dependent 32-bit registers, kMux call, NO 512-bit reg
-- =====================================================================
def bench1 (start : Signal D Bool) : Signal D (BitVec 32) := circuit do
  let cnt ← Signal.reg (0#7)
  let aR ← Signal.reg (0#32)
  let bR ← Signal.reg (0#32)
  let cR ← Signal.reg (0#32)
  let dR ← Signal.reg (0#32)
  let eR ← Signal.reg (0#32)
  let fR ← Signal.reg (0#32)
  let gR ← Signal.reg (0#32)
  let hR ← Signal.reg (0#32)
  let cntSig := (cnt : Signal D (BitVec 7))
  let aSig := (aR : Signal D (BitVec 32))
  let bSig := (bR : Signal D (BitVec 32))
  let cSig := (cR : Signal D (BitVec 32))
  let dSig := (dR : Signal D (BitVec 32))
  let eSig := (eR : Signal D (BitVec 32))
  let fSig := (fR : Signal D (BitVec 32))
  let gSig := (gR : Signal D (BitVec 32))
  let hSig := (hR : Signal D (BitVec 32))
  let p0_7 := (Signal.pure 0#7 : Signal D (BitVec 7))
  let p1_7 := (Signal.pure 1#7 : Signal D (BitVec 7))
  let isIdle := (· == ·) <$> cntSig <*> p0_7
  let kt := kMux cntSig
  let aNext := (· + ·) <$> aSig <*> kt
  cnt <~ ((· + ·) <$> cntSig <*> p1_7)
  aR <~ Signal.mux start hSig (Signal.mux isIdle aSig aNext)
  bR <~ Signal.mux start aSig (Signal.mux isIdle bSig aSig)
  cR <~ Signal.mux start bSig (Signal.mux isIdle cSig bSig)
  dR <~ Signal.mux start cSig (Signal.mux isIdle dSig cSig)
  eR <~ Signal.mux start dSig (Signal.mux isIdle eSig dSig)
  fR <~ Signal.mux start eSig (Signal.mux isIdle fSig eSig)
  gR <~ Signal.mux start fSig (Signal.mux isIdle gSig fSig)
  hR <~ Signal.mux start gSig (Signal.mux isIdle hSig gSig)
  return aSig

-- =====================================================================
-- Bench 2: bench1 + a 512-bit wide register (no slicing)
-- =====================================================================
def bench2 (start : Signal D Bool) (blockIn : Signal D (BitVec 512))
    : Signal D (BitVec 32) := circuit do
  let cnt ← Signal.reg (0#7)
  let aR ← Signal.reg (0#32)
  let bR ← Signal.reg (0#32)
  let cR ← Signal.reg (0#32)
  let dR ← Signal.reg (0#32)
  let eR ← Signal.reg (0#32)
  let fR ← Signal.reg (0#32)
  let gR ← Signal.reg (0#32)
  let hR ← Signal.reg (0#32)
  let wBuf ← Signal.reg (0#512)
  let cntSig := (cnt : Signal D (BitVec 7))
  let aSig := (aR : Signal D (BitVec 32))
  let bSig := (bR : Signal D (BitVec 32))
  let cSig := (cR : Signal D (BitVec 32))
  let dSig := (dR : Signal D (BitVec 32))
  let eSig := (eR : Signal D (BitVec 32))
  let fSig := (fR : Signal D (BitVec 32))
  let gSig := (gR : Signal D (BitVec 32))
  let hSig := (hR : Signal D (BitVec 32))
  let wBufSig := (wBuf : Signal D (BitVec 512))
  let p0_7 := (Signal.pure 0#7 : Signal D (BitVec 7))
  let p1_7 := (Signal.pure 1#7 : Signal D (BitVec 7))
  let isIdle := (· == ·) <$> cntSig <*> p0_7
  let kt := kMux cntSig
  let aNext := (· + ·) <$> aSig <*> kt
  cnt <~ ((· + ·) <$> cntSig <*> p1_7)
  aR <~ Signal.mux start hSig (Signal.mux isIdle aSig aNext)
  bR <~ Signal.mux start aSig (Signal.mux isIdle bSig aSig)
  cR <~ Signal.mux start bSig (Signal.mux isIdle cSig bSig)
  dR <~ Signal.mux start cSig (Signal.mux isIdle dSig cSig)
  eR <~ Signal.mux start dSig (Signal.mux isIdle eSig dSig)
  fR <~ Signal.mux start eSig (Signal.mux isIdle fSig eSig)
  gR <~ Signal.mux start fSig (Signal.mux isIdle gSig fSig)
  hR <~ Signal.mux start gSig (Signal.mux isIdle hSig gSig)
  wBuf <~ Signal.mux start blockIn wBufSig
  return aSig

-- =====================================================================
-- Bench 3: bench2 + 4 slices off the 512-bit register
-- =====================================================================
def bench3 (start : Signal D Bool) (blockIn : Signal D (BitVec 512))
    : Signal D (BitVec 32) := circuit do
  let cnt ← Signal.reg (0#7)
  let aR ← Signal.reg (0#32)
  let bR ← Signal.reg (0#32)
  let cR ← Signal.reg (0#32)
  let dR ← Signal.reg (0#32)
  let eR ← Signal.reg (0#32)
  let fR ← Signal.reg (0#32)
  let gR ← Signal.reg (0#32)
  let hR ← Signal.reg (0#32)
  let wBuf ← Signal.reg (0#512)
  let cntSig := (cnt : Signal D (BitVec 7))
  let aSig := (aR : Signal D (BitVec 32))
  let bSig := (bR : Signal D (BitVec 32))
  let cSig := (cR : Signal D (BitVec 32))
  let dSig := (dR : Signal D (BitVec 32))
  let eSig := (eR : Signal D (BitVec 32))
  let fSig := (fR : Signal D (BitVec 32))
  let gSig := (gR : Signal D (BitVec 32))
  let hSig := (hR : Signal D (BitVec 32))
  let wBufSig := (wBuf : Signal D (BitVec 512))
  let wt := wBufSig.map (BitVec.extractLsb' 480 32 ·)
  let wTm15 := wBufSig.map (BitVec.extractLsb' 448 32 ·)
  let wTm7 := wBufSig.map (BitVec.extractLsb' 192 32 ·)
  let wTm2 := wBufSig.map (BitVec.extractLsb' 32 32 ·)
  let p0_7 := (Signal.pure 0#7 : Signal D (BitVec 7))
  let p1_7 := (Signal.pure 1#7 : Signal D (BitVec 7))
  let isIdle := (· == ·) <$> cntSig <*> p0_7
  let kt := kMux cntSig
  let s1 := (· + ·) <$> aSig <*> kt
  let s2 := (· + ·) <$> s1 <*> wt
  let s3 := (· + ·) <$> s2 <*> wTm15
  let s4 := (· + ·) <$> wTm7 <*> wTm2
  let aNext := (· + ·) <$> s3 <*> s4
  cnt <~ ((· + ·) <$> cntSig <*> p1_7)
  aR <~ Signal.mux start hSig (Signal.mux isIdle aSig aNext)
  bR <~ Signal.mux start aSig (Signal.mux isIdle bSig aSig)
  cR <~ Signal.mux start bSig (Signal.mux isIdle cSig bSig)
  dR <~ Signal.mux start cSig (Signal.mux isIdle dSig cSig)
  eR <~ Signal.mux start dSig (Signal.mux isIdle eSig dSig)
  fR <~ Signal.mux start eSig (Signal.mux isIdle fSig eSig)
  gR <~ Signal.mux start fSig (Signal.mux isIdle gSig fSig)
  hR <~ Signal.mux start gSig (Signal.mux isIdle hSig gSig)
  wBuf <~ Signal.mux start blockIn wBufSig
  return aSig

def runBench (name : String) (sig : Signal D (BitVec 32)) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := sig.val 0
  let t1 ← IO.monoMsNow
  IO.println s!"  [{name}] val 0 = {v.toNat} elapsed = {t1 - t0}ms"

-- =====================================================================
-- Bench 4: 19 regs (matches SHA: cnt + 8 a-h + 8 H + wBuf + done),
-- multi-output record return, 8 state-update muxes, kMux,
-- 4 wBuf slices, H-accumulate muxes.
-- =====================================================================
structure ShaLikeOut (dom : DomainConfig) where
  hash : Signal dom (BitVec 256)
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ShaLikeOut dom) dom := ⟨⟩

def bench4 (start : Signal D Bool) (blockIn : Signal D (BitVec 512))
    : ShaLikeOut D :=
  circuit do
    let cnt ← Signal.reg (0#7)
    let aR ← Signal.reg (0#32)
    let bR ← Signal.reg (0#32)
    let cR ← Signal.reg (0#32)
    let dR ← Signal.reg (0#32)
    let eR ← Signal.reg (0#32)
    let fR ← Signal.reg (0#32)
    let gR ← Signal.reg (0#32)
    let hR ← Signal.reg (0#32)
    let h0R ← Signal.reg (0#32)
    let h1R ← Signal.reg (0#32)
    let h2R ← Signal.reg (0#32)
    let h3R ← Signal.reg (0#32)
    let h4R ← Signal.reg (0#32)
    let h5R ← Signal.reg (0#32)
    let h6R ← Signal.reg (0#32)
    let h7R ← Signal.reg (0#32)
    let wBuf ← Signal.reg (0#512)
    let doneR ← Signal.reg false
    let cntSig := (cnt : Signal D (BitVec 7))
    let aSig := (aR : Signal D (BitVec 32))
    let bSig := (bR : Signal D (BitVec 32))
    let cSig := (cR : Signal D (BitVec 32))
    let dSig := (dR : Signal D (BitVec 32))
    let eSig := (eR : Signal D (BitVec 32))
    let fSig := (fR : Signal D (BitVec 32))
    let gSig := (gR : Signal D (BitVec 32))
    let hSig := (hR : Signal D (BitVec 32))
    let h0Sig := (h0R : Signal D (BitVec 32))
    let h1Sig := (h1R : Signal D (BitVec 32))
    let h2Sig := (h2R : Signal D (BitVec 32))
    let h3Sig := (h3R : Signal D (BitVec 32))
    let h4Sig := (h4R : Signal D (BitVec 32))
    let h5Sig := (h5R : Signal D (BitVec 32))
    let h6Sig := (h6R : Signal D (BitVec 32))
    let h7Sig := (h7R : Signal D (BitVec 32))
    let wBufSig := (wBuf : Signal D (BitVec 512))
    let wt := wBufSig.map (BitVec.extractLsb' 480 32 ·)
    let wTm15 := wBufSig.map (BitVec.extractLsb' 448 32 ·)
    let wTm7 := wBufSig.map (BitVec.extractLsb' 192 32 ·)
    let wTm2 := wBufSig.map (BitVec.extractLsb' 32 32 ·)
    let p0_7 := (Signal.pure 0#7 : Signal D (BitVec 7))
    let p1_7 := (Signal.pure 1#7 : Signal D (BitVec 7))
    let p65_7 := (Signal.pure 65#7 : Signal D (BitVec 7))
    let isIdle := (· == ·) <$> cntSig <*> p0_7
    let isFinish := (· == ·) <$> cntSig <*> p65_7
    let kt := kMux cntSig
    let t1a := (· + ·) <$> hSig <*> kt
    let t1 := (· + ·) <$> t1a <*> wt
    let aNext := (· + ·) <$> t1 <*> aSig
    let eNext := (· + ·) <$> dSig <*> t1
    aR <~ Signal.mux start h0Sig (Signal.mux isIdle aSig aNext)
    bR <~ Signal.mux start h1Sig (Signal.mux isIdle bSig aSig)
    cR <~ Signal.mux start h2Sig (Signal.mux isIdle cSig bSig)
    dR <~ Signal.mux start h3Sig (Signal.mux isIdle dSig cSig)
    eR <~ Signal.mux start h4Sig (Signal.mux isIdle eSig eNext)
    fR <~ Signal.mux start h5Sig (Signal.mux isIdle fSig eSig)
    gR <~ Signal.mux start h6Sig (Signal.mux isIdle gSig fSig)
    hR <~ Signal.mux start h7Sig (Signal.mux isIdle hSig gSig)
    let h0Acc := (· + ·) <$> h0Sig <*> aSig
    let h1Acc := (· + ·) <$> h1Sig <*> bSig
    let h2Acc := (· + ·) <$> h2Sig <*> cSig
    let h3Acc := (· + ·) <$> h3Sig <*> dSig
    let h4Acc := (· + ·) <$> h4Sig <*> eSig
    let h5Acc := (· + ·) <$> h5Sig <*> fSig
    let h6Acc := (· + ·) <$> h6Sig <*> gSig
    let h7Acc := (· + ·) <$> h7Sig <*> hSig
    h0R <~ Signal.mux isFinish h0Acc h0Sig
    h1R <~ Signal.mux isFinish h1Acc h1Sig
    h2R <~ Signal.mux isFinish h2Acc h2Sig
    h3R <~ Signal.mux isFinish h3Acc h3Sig
    h4R <~ Signal.mux isFinish h4Acc h4Sig
    h5R <~ Signal.mux isFinish h5Acc h5Sig
    h6R <~ Signal.mux isFinish h6Acc h6Sig
    h7R <~ Signal.mux isFinish h7Acc h7Sig
    let n1n2 := (· + ·) <$> wTm2 <*> wTm7
    let n3 := (· + ·) <$> n1n2 <*> wTm15
    let newW := (· + ·) <$> n3 <*> wt
    let bufLow := wBufSig.map (BitVec.extractLsb' 0 480 ·)
    let shiftedBuf := (· ++ ·) <$> bufLow <*> newW
    wBuf <~ Signal.mux start blockIn
              (Signal.mux ((fun b => !b) <$> isIdle) shiftedBuf wBufSig)
    let cntInc := (· + ·) <$> cntSig <*> p1_7
    cnt <~ Signal.mux start p1_7
            (Signal.mux isFinish p0_7
              (Signal.mux isIdle p0_7 cntInc))
    doneR <~ isFinish
    let h01 := (· ++ ·) <$> h0Sig <*> h1Sig
    let h23 := (· ++ ·) <$> h2Sig <*> h3Sig
    let h45 := (· ++ ·) <$> h4Sig <*> h5Sig
    let h67 := (· ++ ·) <$> h6Sig <*> h7Sig
    let h0123 := (· ++ ·) <$> h01 <*> h23
    let h4567 := (· ++ ·) <$> h45 <*> h67
    let hAll := (· ++ ·) <$> h0123 <*> h4567
    return ({ hash := hAll, done := (doneR : Signal D Bool) } : ShaLikeOut D)

-- =====================================================================
-- Scaling benches: same shape, different N (number of registers).
-- Each register is independent (next = self + 1), so no cross-deps.
-- =====================================================================
def chain5 : Signal D (BitVec 32) := circuit do
  let r0 ← Signal.reg (0#32)
  let r1 ← Signal.reg (0#32)
  let r2 ← Signal.reg (0#32)
  let r3 ← Signal.reg (0#32)
  let r4 ← Signal.reg (0#32)
  let s0 := (r0 : Signal D (BitVec 32))
  let s1 := (r1 : Signal D (BitVec 32))
  let s2 := (r2 : Signal D (BitVec 32))
  let s3 := (r3 : Signal D (BitVec 32))
  let s4 := (r4 : Signal D (BitVec 32))
  let p1 := (Signal.pure 1#32 : Signal D (BitVec 32))
  r0 <~ ((· + ·) <$> s0 <*> p1)
  r1 <~ ((· + ·) <$> s1 <*> p1)
  r2 <~ ((· + ·) <$> s2 <*> p1)
  r3 <~ ((· + ·) <$> s3 <*> p1)
  r4 <~ ((· + ·) <$> s4 <*> p1)
  return s0

def chain10 : Signal D (BitVec 32) := circuit do
  let r0 ← Signal.reg (0#32)
  let r1 ← Signal.reg (0#32)
  let r2 ← Signal.reg (0#32)
  let r3 ← Signal.reg (0#32)
  let r4 ← Signal.reg (0#32)
  let r5 ← Signal.reg (0#32)
  let r6 ← Signal.reg (0#32)
  let r7 ← Signal.reg (0#32)
  let r8 ← Signal.reg (0#32)
  let r9 ← Signal.reg (0#32)
  let s0 := (r0 : Signal D (BitVec 32))
  let s1 := (r1 : Signal D (BitVec 32))
  let s2 := (r2 : Signal D (BitVec 32))
  let s3 := (r3 : Signal D (BitVec 32))
  let s4 := (r4 : Signal D (BitVec 32))
  let s5 := (r5 : Signal D (BitVec 32))
  let s6 := (r6 : Signal D (BitVec 32))
  let s7 := (r7 : Signal D (BitVec 32))
  let s8 := (r8 : Signal D (BitVec 32))
  let s9 := (r9 : Signal D (BitVec 32))
  let p1 := (Signal.pure 1#32 : Signal D (BitVec 32))
  r0 <~ ((· + ·) <$> s0 <*> p1)
  r1 <~ ((· + ·) <$> s1 <*> p1)
  r2 <~ ((· + ·) <$> s2 <*> p1)
  r3 <~ ((· + ·) <$> s3 <*> p1)
  r4 <~ ((· + ·) <$> s4 <*> p1)
  r5 <~ ((· + ·) <$> s5 <*> p1)
  r6 <~ ((· + ·) <$> s6 <*> p1)
  r7 <~ ((· + ·) <$> s7 <*> p1)
  r8 <~ ((· + ·) <$> s8 <*> p1)
  r9 <~ ((· + ·) <$> s9 <*> p1)
  return s0

def chain12 : Signal D (BitVec 32) := circuit do
  let r0 ← Signal.reg (0#32); let r1 ← Signal.reg (0#32)
  let r2 ← Signal.reg (0#32); let r3 ← Signal.reg (0#32)
  let r4 ← Signal.reg (0#32); let r5 ← Signal.reg (0#32)
  let r6 ← Signal.reg (0#32); let r7 ← Signal.reg (0#32)
  let r8 ← Signal.reg (0#32); let r9 ← Signal.reg (0#32)
  let r10 ← Signal.reg (0#32); let r11 ← Signal.reg (0#32)
  let s0 := (r0 : Signal D (BitVec 32))
  let s1 := (r1 : Signal D (BitVec 32))
  let s2 := (r2 : Signal D (BitVec 32))
  let s3 := (r3 : Signal D (BitVec 32))
  let s4 := (r4 : Signal D (BitVec 32))
  let s5 := (r5 : Signal D (BitVec 32))
  let s6 := (r6 : Signal D (BitVec 32))
  let s7 := (r7 : Signal D (BitVec 32))
  let s8 := (r8 : Signal D (BitVec 32))
  let s9 := (r9 : Signal D (BitVec 32))
  let s10 := (r10 : Signal D (BitVec 32))
  let s11 := (r11 : Signal D (BitVec 32))
  let p1 := (Signal.pure 1#32 : Signal D (BitVec 32))
  r0 <~ ((· + ·) <$> s0 <*> p1); r1 <~ ((· + ·) <$> s1 <*> p1)
  r2 <~ ((· + ·) <$> s2 <*> p1); r3 <~ ((· + ·) <$> s3 <*> p1)
  r4 <~ ((· + ·) <$> s4 <*> p1); r5 <~ ((· + ·) <$> s5 <*> p1)
  r6 <~ ((· + ·) <$> s6 <*> p1); r7 <~ ((· + ·) <$> s7 <*> p1)
  r8 <~ ((· + ·) <$> s8 <*> p1); r9 <~ ((· + ·) <$> s9 <*> p1)
  r10 <~ ((· + ·) <$> s10 <*> p1); r11 <~ ((· + ·) <$> s11 <*> p1)
  return s0

def chain13 : Signal D (BitVec 32) := circuit do
  let r0 ← Signal.reg (0#32); let r1 ← Signal.reg (0#32)
  let r2 ← Signal.reg (0#32); let r3 ← Signal.reg (0#32)
  let r4 ← Signal.reg (0#32); let r5 ← Signal.reg (0#32)
  let r6 ← Signal.reg (0#32); let r7 ← Signal.reg (0#32)
  let r8 ← Signal.reg (0#32); let r9 ← Signal.reg (0#32)
  let r10 ← Signal.reg (0#32); let r11 ← Signal.reg (0#32)
  let r12 ← Signal.reg (0#32)
  let s0 := (r0 : Signal D (BitVec 32))
  let s1 := (r1 : Signal D (BitVec 32))
  let s2 := (r2 : Signal D (BitVec 32))
  let s3 := (r3 : Signal D (BitVec 32))
  let s4 := (r4 : Signal D (BitVec 32))
  let s5 := (r5 : Signal D (BitVec 32))
  let s6 := (r6 : Signal D (BitVec 32))
  let s7 := (r7 : Signal D (BitVec 32))
  let s8 := (r8 : Signal D (BitVec 32))
  let s9 := (r9 : Signal D (BitVec 32))
  let s10 := (r10 : Signal D (BitVec 32))
  let s11 := (r11 : Signal D (BitVec 32))
  let s12 := (r12 : Signal D (BitVec 32))
  let p1 := (Signal.pure 1#32 : Signal D (BitVec 32))
  r0 <~ ((· + ·) <$> s0 <*> p1); r1 <~ ((· + ·) <$> s1 <*> p1)
  r2 <~ ((· + ·) <$> s2 <*> p1); r3 <~ ((· + ·) <$> s3 <*> p1)
  r4 <~ ((· + ·) <$> s4 <*> p1); r5 <~ ((· + ·) <$> s5 <*> p1)
  r6 <~ ((· + ·) <$> s6 <*> p1); r7 <~ ((· + ·) <$> s7 <*> p1)
  r8 <~ ((· + ·) <$> s8 <*> p1); r9 <~ ((· + ·) <$> s9 <*> p1)
  r10 <~ ((· + ·) <$> s10 <*> p1); r11 <~ ((· + ·) <$> s11 <*> p1)
  r12 <~ ((· + ·) <$> s12 <*> p1)
  return s0

def chain15 : Signal D (BitVec 32) := circuit do
  let r0 ← Signal.reg (0#32); let r1 ← Signal.reg (0#32)
  let r2 ← Signal.reg (0#32); let r3 ← Signal.reg (0#32)
  let r4 ← Signal.reg (0#32); let r5 ← Signal.reg (0#32)
  let r6 ← Signal.reg (0#32); let r7 ← Signal.reg (0#32)
  let r8 ← Signal.reg (0#32); let r9 ← Signal.reg (0#32)
  let r10 ← Signal.reg (0#32); let r11 ← Signal.reg (0#32)
  let r12 ← Signal.reg (0#32); let r13 ← Signal.reg (0#32)
  let r14 ← Signal.reg (0#32)
  let s0 := (r0 : Signal D (BitVec 32))
  let s1 := (r1 : Signal D (BitVec 32))
  let s2 := (r2 : Signal D (BitVec 32))
  let s3 := (r3 : Signal D (BitVec 32))
  let s4 := (r4 : Signal D (BitVec 32))
  let s5 := (r5 : Signal D (BitVec 32))
  let s6 := (r6 : Signal D (BitVec 32))
  let s7 := (r7 : Signal D (BitVec 32))
  let s8 := (r8 : Signal D (BitVec 32))
  let s9 := (r9 : Signal D (BitVec 32))
  let s10 := (r10 : Signal D (BitVec 32))
  let s11 := (r11 : Signal D (BitVec 32))
  let s12 := (r12 : Signal D (BitVec 32))
  let s13 := (r13 : Signal D (BitVec 32))
  let s14 := (r14 : Signal D (BitVec 32))
  let p1 := (Signal.pure 1#32 : Signal D (BitVec 32))
  r0 <~ ((· + ·) <$> s0 <*> p1); r1 <~ ((· + ·) <$> s1 <*> p1)
  r2 <~ ((· + ·) <$> s2 <*> p1); r3 <~ ((· + ·) <$> s3 <*> p1)
  r4 <~ ((· + ·) <$> s4 <*> p1); r5 <~ ((· + ·) <$> s5 <*> p1)
  r6 <~ ((· + ·) <$> s6 <*> p1); r7 <~ ((· + ·) <$> s7 <*> p1)
  r8 <~ ((· + ·) <$> s8 <*> p1); r9 <~ ((· + ·) <$> s9 <*> p1)
  r10 <~ ((· + ·) <$> s10 <*> p1); r11 <~ ((· + ·) <$> s11 <*> p1)
  r12 <~ ((· + ·) <$> s12 <*> p1); r13 <~ ((· + ·) <$> s13 <*> p1)
  r14 <~ ((· + ·) <$> s14 <*> p1)
  return s0

def chain19 : Signal D (BitVec 32) := circuit do
  let r0 ← Signal.reg (0#32); let r1 ← Signal.reg (0#32)
  let r2 ← Signal.reg (0#32); let r3 ← Signal.reg (0#32)
  let r4 ← Signal.reg (0#32); let r5 ← Signal.reg (0#32)
  let r6 ← Signal.reg (0#32); let r7 ← Signal.reg (0#32)
  let r8 ← Signal.reg (0#32); let r9 ← Signal.reg (0#32)
  let r10 ← Signal.reg (0#32); let r11 ← Signal.reg (0#32)
  let r12 ← Signal.reg (0#32); let r13 ← Signal.reg (0#32)
  let r14 ← Signal.reg (0#32); let r15 ← Signal.reg (0#32)
  let r16 ← Signal.reg (0#32); let r17 ← Signal.reg (0#32)
  let r18 ← Signal.reg (0#32)
  let s0 := (r0 : Signal D (BitVec 32))
  let s1 := (r1 : Signal D (BitVec 32))
  let s2 := (r2 : Signal D (BitVec 32))
  let s3 := (r3 : Signal D (BitVec 32))
  let s4 := (r4 : Signal D (BitVec 32))
  let s5 := (r5 : Signal D (BitVec 32))
  let s6 := (r6 : Signal D (BitVec 32))
  let s7 := (r7 : Signal D (BitVec 32))
  let s8 := (r8 : Signal D (BitVec 32))
  let s9 := (r9 : Signal D (BitVec 32))
  let s10 := (r10 : Signal D (BitVec 32))
  let s11 := (r11 : Signal D (BitVec 32))
  let s12 := (r12 : Signal D (BitVec 32))
  let s13 := (r13 : Signal D (BitVec 32))
  let s14 := (r14 : Signal D (BitVec 32))
  let s15 := (r15 : Signal D (BitVec 32))
  let s16 := (r16 : Signal D (BitVec 32))
  let s17 := (r17 : Signal D (BitVec 32))
  let s18 := (r18 : Signal D (BitVec 32))
  let p1 := (Signal.pure 1#32 : Signal D (BitVec 32))
  r0 <~ ((· + ·) <$> s0 <*> p1); r1 <~ ((· + ·) <$> s1 <*> p1)
  r2 <~ ((· + ·) <$> s2 <*> p1); r3 <~ ((· + ·) <$> s3 <*> p1)
  r4 <~ ((· + ·) <$> s4 <*> p1); r5 <~ ((· + ·) <$> s5 <*> p1)
  r6 <~ ((· + ·) <$> s6 <*> p1); r7 <~ ((· + ·) <$> s7 <*> p1)
  r8 <~ ((· + ·) <$> s8 <*> p1); r9 <~ ((· + ·) <$> s9 <*> p1)
  r10 <~ ((· + ·) <$> s10 <*> p1); r11 <~ ((· + ·) <$> s11 <*> p1)
  r12 <~ ((· + ·) <$> s12 <*> p1); r13 <~ ((· + ·) <$> s13 <*> p1)
  r14 <~ ((· + ·) <$> s14 <*> p1); r15 <~ ((· + ·) <$> s15 <*> p1)
  r16 <~ ((· + ·) <$> s16 <*> p1); r17 <~ ((· + ·) <$> s17 <*> p1)
  r18 <~ ((· + ·) <$> s18 <*> p1)
  return s0

def runBoolBench (name : String) (sig : Signal D Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := sig.val 0
  let t1 ← IO.monoMsNow
  IO.println s!"  [{name}] val 0 = {v} elapsed = {t1 - t0}ms"

def main : IO Unit := do
  IO.println "=== C2 SHA-like localizer ==="

  IO.println "Bench 1 (9 regs, kMux, no 512-bit reg):"
  runBench "b1" (bench1 startSig)

  IO.println "Bench 2 (bench1 + 512-bit wBuf, no slices):"
  runBench "b2" (bench2 startSig blockIn)

  IO.println "Bench 3 (bench2 + 4 slices into aNext):"
  runBench "b3" (bench3 startSig blockIn)

  IO.println "Bench 4 (SHA-shape clone, 19 regs, multi-output record):"
  let b4 := bench4 startSig blockIn
  runBoolBench "b4.done t=0" b4.done
  for t in [1, 2, 5, 10] do
    let t0 ← IO.monoMsNow
    let v := b4.done.val t
    let t1 ← IO.monoMsNow
    IO.println s!"  [b4.done t={t}] = {v} elapsed = {t1 - t0}ms"

  -- Scaling: independent counter regs, all writing self+1.
  IO.println "Scaling chain (independent regs):"
  for (n, sig) in [(5, chain5), (10, chain10), (12, chain12), (13, chain13), (15, chain15), (19, chain19)] do
    let t0 ← IO.monoMsNow
    let v := sig.val 2
    let t1 ← IO.monoMsNow
    IO.println s!"  [chain N={n} val 2] = {v.toNat} elapsed = {t1 - t0}ms"

  -- Real SHA-256 HW engine — previously hung at done.val 0.
  IO.println "Real sha256Block (the original C2 blocker):"
  let sha := sha256Block startSig blockIn
  for t in [0, 1, 5, 10, 65, 70] do
    let t0 ← IO.monoMsNow
    let v := sha.done.val t
    let t1 ← IO.monoMsNow
    IO.println s!"  [sha.done t={t}] = {v} elapsed = {t1 - t0}ms"

end SimCost

def main : IO Unit := SimCost.main
