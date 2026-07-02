/-
  Sim + synth test for
  `IP.Crypto.Eip1559EnvelopeHW.eip1559EnvelopeHW`.

  Behavioural: for several RLP-body lengths spanning the three
  RLP length-prefix classes (≤55, 56..255, 256..2047), confirm
  the HW emits the complete EIP-1559 envelope *header* stream

      0x02 ‖ <rlp list header bytes>

  identical to the pure-data reference

      #[0x02] ++ RLP.encodeLength bodyLen 0xc0

  which is the leading slice of `Eip1559Tx.encodeSigned`
  (`#[0x02] ++ encode (.list body)`) before the body payload.

  Synth: `#synthesizeVerilog` on the byte / valid / done outputs.
-/
import IP.Crypto.RLP
import IP.Crypto.Eip1559EnvelopeHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Eip1559EnvelopeHW
open Sparkle.IP.Crypto.RLP (encodeLength)

namespace Sparkle.Tests.IP.Crypto.Eip1559EnvelopeHWTest

abbrev D := defaultDomain

private def startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

/-- Sample the emitted envelope-header bytes over the first
    `kMax` cycles (bytes where `headerValid` is high). -/
private def sampleHeader (out : EnvOut D) (kMax : Nat) : Array UInt8 := Id.run do
  let mut acc : Array UInt8 := #[]
  for t in [:kMax] do
    if out.headerValid.val t then
      acc := acc.push (UInt8.ofNat (out.headerByte.val t).toNat)
  return acc

/-- Reference envelope header: 0x02 type byte + RLP list wrapper. -/
private def refHeader (bodyLen : Nat) : Array UInt8 :=
  #[0x02] ++ encodeLength bodyLen 0xc0

private def toHex (bs : Array UInt8) : String :=
  String.join <| bs.toList.map (fun b =>
    let s := Nat.toDigits 16 b.toNat |> String.ofList
    if s.length = 1 then "0" ++ s else s)

def main : IO Unit := do
  IO.println "=== EIP-1559 envelope-header HW vs pure-data ==="
  let mut ok := true

  let cases : List (Nat × String) :=
    [ (10,   "short body (1-byte RLP header)")
    , (55,   "max short-form body")
    , (56,   "2-byte RLP header body")
    , (200,  "2-byte RLP header body")
    , (256,  "3-byte RLP header body")
    , (1000, "3-byte RLP header body") ]

  for (bodyLen, label) in cases do
    let ref := refHeader bodyLen
    let out := eip1559EnvelopeHW startSig (constSig (BitVec.ofNat 11 bodyLen))
    -- header is at most 1 (type) + 3 (rlp) = 4 bytes; sample generously.
    let hw := sampleHeader out (ref.size + 4)
    let hOk := hw = ref
    let mark := if hOk then "ok" else "MISMATCH"
    IO.println s!"  [{mark}] {label} (bodyLen={bodyLen})"
    IO.println s!"    ref: {toHex ref}"
    IO.println s!"    hw : {toHex hw}"
    if !hOk then ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Eip1559EnvelopeHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Eip1559EnvelopeHW

private def synth_envByte
    (start : Signal defaultDomain Bool)
    (bodyLen : Signal defaultDomain (BitVec 11)) :
    Signal defaultDomain (BitVec 8) :=
  (eip1559EnvelopeHW start bodyLen).headerByte

#synthesizeVerilog synth_envByte

private def synth_envValid
    (start : Signal defaultDomain Bool)
    (bodyLen : Signal defaultDomain (BitVec 11)) :
    Signal defaultDomain Bool :=
  (eip1559EnvelopeHW start bodyLen).headerValid

#synthesizeVerilog synth_envValid

private def synth_envDone
    (start : Signal defaultDomain Bool)
    (bodyLen : Signal defaultDomain (BitVec 11)) :
    Signal defaultDomain Bool :=
  (eip1559EnvelopeHW start bodyLen).done

#synthesizeVerilog synth_envDone

end SynthesisChecks
