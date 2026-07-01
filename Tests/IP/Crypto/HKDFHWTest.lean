/-
  Sim test for IP.Crypto.HKDFHW.hkdfExpandHW.

  RFC 5869 Test Case 1 (HKDF-SHA256):

      IKM  = 0x0b × 22
      salt = 0x000102030405060708090a0b0c
      info = 0xf0f1f2f3f4f5f6f7f8f9
      L    = 42
      PRK  = 0x077709362c2e32df0ddc3f0dc47bba63
             90b6c73bb50f9c3122ec844ad7c2b3e5
      OKM  = 0x3cb25f25faacd57a90434f64d0362f2a
             2d2d0a90cf1a5a4c5db02d56ecc4c5bf
             34007208d5b887185865   (42 bytes)

  The HW piece here is the counter FSM (`hkdfExpandHW`).  We
  drive it with pre-computed T(1), T(2), T(3) values from the
  pure-data `hmacSha256` reference (L = 42 needs ⌈42/32⌉ = 2
  blocks; we push 3 for FSM stress) and confirm the FSM's
  counter/state trajectory + emits `done`.

  The full pure-data HKDF-SHA-256 is separately validated in
  `Tests/IP/Crypto/HKDFTest.lean`; this HW test focuses on the
  FSM shape.
-/

import IP.Crypto.HKDF
import IP.Crypto.HKDFHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.HKDFHW
open Sparkle.IP.Crypto.HKDF
  (hmacSha256 hkdfExtract hkdfExpand)

namespace Sparkle.Tests.IP.Crypto.HKDFHWTest

abbrev D := defaultDomain

private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

private def pulses (ts : List Nat) : Signal D Bool :=
  ⟨fun t => decide (t ∈ ts)⟩

private def bvSchedule (sched : List (Nat × BitVec 256)) (default : BitVec 256) :
    Signal D (BitVec 256) :=
  ⟨fun t =>
    match sched.find? (fun (u, _) => u = t) with
    | some (_, v) => v
    | none => default⟩

private def bytesToBv256 (bs : Array UInt8) : BitVec 256 := Id.run do
  let mut acc : Nat := 0
  for b in bs do
    acc := (acc <<< 8) ||| b.toNat
  return BitVec.ofNat 256 acc

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

def main : IO Unit := do
  IO.println "=== HKDF-Expand counter HW vs pure-data ==="
  let mut ok := true

  -- RFC 5869 Test Case 1 inputs.
  let ikm : Array UInt8 := Array.replicate 22 0x0b
  let salt : Array UInt8 :=
    #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
      0x08, 0x09, 0x0a, 0x0b, 0x0c]
  let info : Array UInt8 :=
    #[0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
  let expectedPrk : Array UInt8 :=
    #[0x07, 0x77, 0x09, 0x36, 0x2c, 0x2e, 0x32, 0xdf,
      0x0d, 0xdc, 0x3f, 0x0d, 0xc4, 0x7b, 0xba, 0x63,
      0x90, 0xb6, 0xc7, 0x3b, 0xb5, 0x0f, 0x9c, 0x31,
      0x22, 0xec, 0x84, 0x4a, 0xd7, 0xc2, 0xb3, 0xe5]
  let expectedOkm : Array UInt8 :=
    #[0x3c, 0xb2, 0x5f, 0x25, 0xfa, 0xac, 0xd5, 0x7a,
      0x90, 0x43, 0x4f, 0x64, 0xd0, 0x36, 0x2f, 0x2a,
      0x2d, 0x2d, 0x0a, 0x90, 0xcf, 0x1a, 0x5a, 0x4c,
      0x5d, 0xb0, 0x2d, 0x56, 0xec, 0xc4, 0xc5, 0xbf,
      0x34, 0x00, 0x72, 0x08, 0xd5, 0xb8, 0x87, 0x18, 0x58, 0x65]

  -- Pure-data check: hkdfExtract + hkdfExpand must reproduce RFC 5869 Case 1.
  let prk := hkdfExtract salt ikm
  let okm := hkdfExpand prk info 42
  IO.println s!"  pure-data PRK = {hexOfBytes prk}"
  IO.println s!"  pure-data OKM = {hexOfBytes okm}"
  if prk = expectedPrk then
    IO.println "  ok PRK matches RFC 5869 Case 1"
  else
    IO.println s!"  MISMATCH PRK ≠ RFC 5869 Case 1 (expected {hexOfBytes expectedPrk})"
    ok := false
  if okm = expectedOkm then
    IO.println "  ok OKM matches RFC 5869 Case 1"
  else
    IO.println s!"  MISMATCH OKM ≠ RFC 5869 Case 1 (expected {hexOfBytes expectedOkm})"
    ok := false

  -- HW piece: FSM sweeps nBlocks = 2 (L=42 rounds up to 2 T-blocks).
  -- Pre-compute T(1), T(2) via hmacSha256:
  --   T(1) = HMAC(PRK, info || 0x01)
  --   T(2) = HMAC(PRK, T(1) || info || 0x02)
  let t1 := hmacSha256 prk (info ++ #[0x01])
  let t2 := hmacSha256 prk (t1 ++ info ++ #[0x02])
  let t1Bv := bytesToBv256 t1
  let t2Bv := bytesToBv256 t2
  IO.println s!"  T(1) = {hexOfBytes t1}"
  IO.println s!"  T(2) = {hexOfBytes t2}"

  -- Timing plan:
  --   cycle 0 : start pulse, nBlocks = 2
  --   cycle 1 : FSM enters isTrig (hmacTrig=1)
  --   cycle 2 : FSM enters isWait ; test ack with blockDone + T(1)
  --   cycle 3 : FSM latches T(1), moves to isTrig for round 2
  --   cycle 4 : FSM enters isWait; test ack with blockDone + T(2)
  --   cycle 5 : FSM done
  let startSig := pulses [0]
  let doneAckAt : List Nat := [2, 4]
  let blockDoneSig := pulses doneAckAt
  let blockInSig :=
    bvSchedule [(2, t1Bv), (4, t2Bv)] 0#256

  let engine := hkdfExpandHW startSig (constSig 2#8) blockInSig blockDoneSig

  for t in [:8] do
    let c := (engine.counter.val t).toNat
    let tp := engine.tPrev.val t
    let trg := engine.hmacTrig.val t
    let dn := engine.done.val t
    IO.println s!"  t={t}: cnt={c} hmacTrig={trg} done={dn} tPrev=0x{Nat.toDigits 16 tp.toNat |> String.ofList}"

  -- After ack at t=4, we expect done=true at t=5, and tPrev = T(2).
  let doneAt5 := engine.done.val 5
  let tPrevAt5 := engine.tPrev.val 5
  let tMatches := decide (tPrevAt5 = t2Bv)
  if doneAt5 && tMatches then
    IO.println "  ✓ FSM signals done + latches final T(2)"
  else
    IO.println s!"  ✗ done@5 = {doneAt5}, tPrev@5 == T(2) = {tMatches}"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.HKDFHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.HKDFHW

private def synth_hkdfCounter
    (start : Signal defaultDomain Bool)
    (nBlocks : Signal defaultDomain (BitVec 8))
    (blockIn : Signal defaultDomain (BitVec 256))
    (blockDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (hkdfExpandHW start nBlocks blockIn blockDone).counter

#synthesizeVerilog synth_hkdfCounter

private def synth_hkdfDone
    (start : Signal defaultDomain Bool)
    (nBlocks : Signal defaultDomain (BitVec 8))
    (blockIn : Signal defaultDomain (BitVec 256))
    (blockDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (hkdfExpandHW start nBlocks blockIn blockDone).done

#synthesizeVerilog synth_hkdfDone

private def synth_hkdfTrig
    (start : Signal defaultDomain Bool)
    (nBlocks : Signal defaultDomain (BitVec 8))
    (blockIn : Signal defaultDomain (BitVec 256))
    (blockDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (hkdfExpandHW start nBlocks blockIn blockDone).hmacTrig

#synthesizeVerilog synth_hkdfTrig

end SynthesisChecks
