/-
  Test for `IP.Crypto.HMACSHA512HW.hmacSha512HW` — the HMAC-SHA-512
  FSM specialised to the BIP-32 CKDpriv shape (32-byte key,
  37-byte message, driving the SHA-512 block compressor 4×).

  Coverage:

  1. **Schedule cross-check** (`main`): `hmacSpec` re-executes the
     EXACT block-word construction the FSM performs — the ipad /
     opad key words, the two padded message blocks (msg ‖ 0x80 ‖
     len165 ; inner ‖ 0x80 ‖ len192), and the four `compressBlock`
     calls with the right chaining `hIn` — and confirms the
     result equals the pure-data `Bip39.hmacSha512` on several
     (key, msg) pairs.  This pins the numeric spec.  (A closed-loop
     cycle co-sim of the controller against a real block engine
     hangs in the interpreter — the known multi-output-FSM
     `Signal.val` slowdown — so we validate the datapath logic,
     and let `#synthesizeVerilog` prove the circuit elaborates.)

  2. **Synth check** (`SynthesisChecks`): `#synthesizeVerilog` on
     representative outputs (out0, done, blkStart, a bWin word).
-/
import IP.Crypto.Bip39
import IP.Crypto.SHA512
import IP.Crypto.HMACSHA512HW

open Sparkle.IP.Crypto.Bip39 (hmacSha512)
open Sparkle.IP.Crypto.SHA512 (initH compressBlock)

namespace Sparkle.Tests.IP.Crypto.HMACSHA512HWTest

private def ipadRep : BitVec 64 := 0x3636363636363636
private def opadRep : BitVec 64 := 0x5c5c5c5c5c5c5c5c

/-- Pure-data transcription of `hmacSha512HW`'s block-word
    construction + 4 `compressBlock` calls (32-byte key words
    k0..k3, msg words m0..m3 + m4 = msg[32:37] in the top 5 bytes). -/
private def hmacSpec (k0 k1 k2 k3 m0 m1 m2 m3 m4 : BitVec 64) :
    Array (BitVec 64) := Id.run do
  let z : BitVec 64 := 0
  let ib1 : Array (BitVec 64) :=
    #[k0 ^^^ ipadRep, k1 ^^^ ipadRep, k2 ^^^ ipadRep, k3 ^^^ ipadRep,
      ipadRep, ipadRep, ipadRep, ipadRep, ipadRep, ipadRep, ipadRep, ipadRep,
      ipadRep, ipadRep, ipadRep, ipadRep]
  let d1 := compressBlock initH ib1
  let m4pad := m4 ||| 0x0000000000800000
  let ib2 : Array (BitVec 64) :=
    #[m0, m1, m2, m3, m4pad, z, z, z, z, z, z, z, z, z, z, (1320 : BitVec 64)]
  let inner := compressBlock d1 ib2
  let ob1 : Array (BitVec 64) :=
    #[k0 ^^^ opadRep, k1 ^^^ opadRep, k2 ^^^ opadRep, k3 ^^^ opadRep,
      opadRep, opadRep, opadRep, opadRep, opadRep, opadRep, opadRep, opadRep,
      opadRep, opadRep, opadRep, opadRep]
  let d3 := compressBlock initH ob1
  let ob2 : Array (BitVec 64) :=
    #[inner.getD 0 0, inner.getD 1 0, inner.getD 2 0, inner.getD 3 0,
      inner.getD 4 0, inner.getD 5 0, inner.getD 6 0, inner.getD 7 0,
      (0x8000000000000000 : BitVec 64), z, z, z, z, z, z, (1536 : BitVec 64)]
  compressBlock d3 ob2

private def bytesToWords (bs : Array UInt8) : Array (BitVec 64) := Id.run do
  let mut ws : Array (BitVec 64) := #[]
  for i in [:bs.size / 8] do
    let mut w : Nat := 0
    for j in [:8] do w := (w <<< 8) ||| (bs.getD (i * 8 + j) 0).toNat
    ws := ws.push (BitVec.ofNat 64 w)
  return ws

def main : IO Unit := do
  IO.println "=== HMAC-SHA-512 FSM (BIP-32 shape) schedule check ==="
  let mut ok := true
  -- (key32, msg37) test pairs, keyed to the BIP-32 hardened form.
  let cases : List (Array UInt8 × Array UInt8) :=
    [ (Array.replicate 32 0x11, #[0x00] ++ Array.replicate 32 0x22 ++ #[0x80,0,0,0])
    , (Array.replicate 32 0x00, #[0x00] ++ Array.replicate 32 0x01 ++ #[0,0,0,1])
    , ((List.range 32).toArray.map (fun i => UInt8.ofNat i),
       #[0x00] ++ ((List.range 32).toArray.map (fun i => UInt8.ofNat (i+64))) ++ #[0xFF,0xFF,0xFF,0xFF]) ]
  for (key, msg) in cases do
    let kw := bytesToWords key
    -- m4 = msg bytes 32..36 in the top 5 bytes → pad msg to 40 bytes.
    let mw := bytesToWords (msg ++ #[0,0,0])
    let got := hmacSpec (kw.getD 0 0) (kw.getD 1 0) (kw.getD 2 0) (kw.getD 3 0)
                (mw.getD 0 0) (mw.getD 1 0) (mw.getD 2 0) (mw.getD 3 0) (mw.getD 4 0)
    let ref := bytesToWords (hmacSha512 key msg)
    if got == ref then
      IO.println s!"  ok hmac matches Bip39.hmacSha512 (out0={(got.getD 0 0).toNat})"
    else
      IO.println s!"  MISMATCH hmac"
      ok := false
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.HMACSHA512HWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.HMACSHA512HW

private def synth_hmac_out0
    (start : Signal defaultDomain Bool)
    (k0 k1 k2 k3 m0 m1 m2 m3 m4 : Signal defaultDomain (BitVec 64))
    (b0 b1 b2 b3 b4 b5 b6 b7 : Signal defaultDomain (BitVec 64))
    (bd : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 64) :=
  (hmacSha512HW start k0 k1 k2 k3 m0 m1 m2 m3 m4 b0 b1 b2 b3 b4 b5 b6 b7 bd).out0

#synthesizeVerilog synth_hmac_out0

private def synth_hmac_blkStart
    (start : Signal defaultDomain Bool)
    (k0 k1 k2 k3 m0 m1 m2 m3 m4 : Signal defaultDomain (BitVec 64))
    (b0 b1 b2 b3 b4 b5 b6 b7 : Signal defaultDomain (BitVec 64))
    (bd : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  (hmacSha512HW start k0 k1 k2 k3 m0 m1 m2 m3 m4 b0 b1 b2 b3 b4 b5 b6 b7 bd).blkStart

#synthesizeVerilog synth_hmac_blkStart

private def synth_hmac_bWin15
    (start : Signal defaultDomain Bool)
    (k0 k1 k2 k3 m0 m1 m2 m3 m4 : Signal defaultDomain (BitVec 64))
    (b0 b1 b2 b3 b4 b5 b6 b7 : Signal defaultDomain (BitVec 64))
    (bd : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 64) :=
  (hmacSha512HW start k0 k1 k2 k3 m0 m1 m2 m3 m4 b0 b1 b2 b3 b4 b5 b6 b7 bd).bWin15

#synthesizeVerilog synth_hmac_bWin15

private def synth_hmac_done
    (start : Signal defaultDomain Bool)
    (k0 k1 k2 k3 m0 m1 m2 m3 m4 : Signal defaultDomain (BitVec 64))
    (b0 b1 b2 b3 b4 b5 b6 b7 : Signal defaultDomain (BitVec 64))
    (bd : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  (hmacSha512HW start k0 k1 k2 k3 m0 m1 m2 m3 m4 b0 b1 b2 b3 b4 b5 b6 b7 bd).done

#synthesizeVerilog synth_hmac_done

end SynthesisChecks
