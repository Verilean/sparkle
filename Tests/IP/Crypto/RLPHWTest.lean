/-
  Sim test for IP.Crypto.RLPHW.rlpHeaderHW.

  Behavioural half: sweep three representative lengths — a
  short (≤ 55) byte string, a mid string (56..255), and a
  long string (256..2047) — and confirm the HW emits the
  same prefix bytes as `RLP.encode (.bytes …)` (truncated
  to the header length).

  Synth via #synthesizeVerilog at the bottom.

  Bonus target case: encoding `["cat", "dog"]` (RLP examples
  §B.1) — cat/dog are single low bytes so each is encoded as
  the byte itself (no prefix), and the list wrapper is
  0xc8 (0xc0 + 8 payload bytes).  This is checked in software
  against `RLP.encode`; the HW piece only handles the list
  wrapper cycle.
-/

import IP.Crypto.RLP
import IP.Crypto.RLPHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.RLPHW
open Sparkle.IP.Crypto.RLP (encode encodeBytes encodeLength Item)

namespace Sparkle.Tests.IP.Crypto.RLPHWTest

abbrev D := defaultDomain

/-- Signal that pulses high only at cycle 0. -/
private def startSig : Signal D Bool :=
  ⟨fun t => decide (t = 0)⟩

/-- Constant Signal. -/
private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

/-- Sample the header bytes emitted between cycle 0 and
    cycle (K-1) inclusive. -/
private def sampleHeader (out : HeaderOut D) (kMax : Nat) : Array UInt8 := Id.run do
  let mut acc : Array UInt8 := #[]
  for t in [:kMax] do
    if out.headerValid.val t then
      acc := acc.push (UInt8.ofNat (out.headerByte.val t).toNat)
  return acc

/-- Reference: expected header bytes.  For byte-string form we
    encode `Array.replicate len 0` and drop the payload.  For
    the list form the HW emits just the list-*wrapper* header,
    which is exactly `encodeLength len 0xc0`. -/
private def refPrefix (len : Nat) (isList : Bool) : Array UInt8 :=
  if isList then
    encodeLength len 0xc0
  else
    let dummy : Array UInt8 := Array.replicate len 0
    let enc := encodeBytes dummy
    enc.extract 0 (enc.size - len)

def main : IO Unit := do
  IO.println "=== RLP header-emitter HW vs pure-data ==="
  let mut ok := true

  let cases : List (Nat × Bool × String) :=
    [ (0,   false, "empty byte string")
    , (1,   false, "1-byte string  (short-form uses low byte itself; here forced via 1-byte header)")
    , (55,  false, "55-byte string (max short form)")
    , (56,  false, "56-byte string (2-byte header)")
    , (200, false, "200-byte string (2-byte header)")
    , (256, false, "256-byte string (3-byte header)")
    , (2000, false, "2000-byte string (3-byte header)")
    , (0,   true,  "empty list")
    , (55,  true,  "55-byte list (max short form)")
    , (56,  true,  "56-byte list (2-byte header)")
    , (300, true,  "300-byte list (3-byte header)") ]

  for (len, isList, label) in cases do
    -- For bytes-form we can't compute refPrefix for len=1 correctly
    -- (RLP short-cut for single low byte); skip that case since it's
    -- not what the header HW handles.  All other rows have a real
    -- prefix header.
    let refBytes := refPrefix len isList
    -- Skip cases where the reference has no header (the single-low-byte cut).
    if refBytes.size = 0 then
      IO.println s!"  (skip {label} — no header emitted by pure encoder)"
      continue
    let out := rlpHeaderHW startSig (constSig (BitVec.ofNat 11 len)) (constSig isList)
    let hwBytes := sampleHeader out (refBytes.size + 2)
    let toHex (bs : Array UInt8) := String.join <|
      bs.toList.map (fun b => Nat.toDigits 16 b.toNat |> String.ofList
                              |> fun s => if s.length = 1 then "0" ++ s else s)
    let hOk := hwBytes = refBytes
    let mark := if hOk then "ok" else "MISMATCH"
    IO.println s!"  [{mark}] {label} (len={len}, isList={isList})"
    IO.println s!"    ref: {toHex refBytes}"
    IO.println s!"    hw : {toHex hwBytes}"
    if !hOk then ok := false

  -- Bonus: verify `RLP.encode` produces the expected classic value
  -- for ["cat","dog"] against the Ethereum wiki example.
  IO.println "-- classic [\"cat\",\"dog\"] check --"
  let cat : Array UInt8 := "cat".toUTF8.toList.toArray
  let dog : Array UInt8 := "dog".toUTF8.toList.toArray
  let expected : Array UInt8 :=
    #[0xc8, 0x83, 0x63, 0x61, 0x74, 0x83, 0x64, 0x6f, 0x67]
  let got := encode (.list [.bytes cat, .bytes dog])
  if got = expected then
    IO.println "  ok pure encoder matches Ethereum wiki value"
  else
    IO.println "  MISMATCH pure encoder ≠ Ethereum wiki value"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.RLPHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.RLPHW

private def synth_rlpHeaderByte
    (start : Signal defaultDomain Bool)
    (lenIn : Signal defaultDomain (BitVec 11))
    (isList : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (rlpHeaderHW start lenIn isList).headerByte

#synthesizeVerilog synth_rlpHeaderByte

private def synth_rlpHeaderValid
    (start : Signal defaultDomain Bool)
    (lenIn : Signal defaultDomain (BitVec 11))
    (isList : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (rlpHeaderHW start lenIn isList).headerValid

#synthesizeVerilog synth_rlpHeaderValid

private def synth_rlpHeaderDone
    (start : Signal defaultDomain Bool)
    (lenIn : Signal defaultDomain (BitVec 11))
    (isList : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (rlpHeaderHW start lenIn isList).done

#synthesizeVerilog synth_rlpHeaderDone

end SynthesisChecks
