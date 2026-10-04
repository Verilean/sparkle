import IP.Net.ICMP
import IP.Net.IPv4
import Sparkle
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Net.ICMP Sparkle.IP.Net.IPv4

private def reqIdent : BitVec 16 := 0x1234#16
private def reqSeq   : BitVec 16 := 0x5678#16
private def reqChk   : BitVec 16 := icmpEchoChecksum icmpTypeReq reqIdent reqSeq

private def requestBytes : List (BitVec 8) :=
  [ icmpTypeReq, icmpCode
  , BitVec.extractLsb' 8 8 reqChk, BitVec.extractLsb' 0 8 reqChk
  , BitVec.extractLsb' 8 8 reqIdent, BitVec.extractLsb' 0 8 reqIdent
  , BitVec.extractLsb' 8 8 reqSeq,   BitVec.extractLsb' 0 8 reqSeq ]

private def byte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => if t < 8 then (requestBytes[t]?).getD 0#8 else 0#8⟩
private def valid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 8)⟩
private def sop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩
private def out : IcmpResponderOut defaultDomain := icmpEchoResponder byte valid sop

def main : IO Unit := do
  for t in [:30] do
    let b := out.txByte.val t
    let v := out.txValid.val t
    IO.println s!"cycle {t}: byte={b.toNat} valid={v}"
