import IP.Net.ARP
import Sparkle
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Net.ARP

private def clientMac : BitVec 48 := 0x010203040506#48
private def clientIp  : BitVec 32 := 0x0A00000A#32
private def serverMac : BitVec 48 := 0xAABBCCDDEEFF#48
private def serverIp  : BitVec 32 := 0x0A000014#32

private def macBytes (m : BitVec 48) : List (BitVec 8) :=
  List.range 6 |>.map (fun k => BitVec.extractLsb' ((5 - k) * 8) 8 m)
private def ipBytes (ip : BitVec 32) : List (BitVec 8) :=
  List.range 4 |>.map (fun k => BitVec.extractLsb' ((3 - k) * 8) 8 ip)
private def operBytes (op : BitVec 16) : List (BitVec 8) :=
  [BitVec.extractLsb' 8 8 op, BitVec.extractLsb' 0 8 op]
private def fixedHdr : List (BitVec 8) :=
  [ 0x00#8, 0x01#8, 0x08#8, 0x00#8, 0x06#8, 0x04#8 ]
def arpBytes (op : BitVec 16) (sha : BitVec 48) (spa : BitVec 32)
    (tha : BitVec 48) (tpa : BitVec 32) : List (BitVec 8) :=
  fixedHdr ++ operBytes op ++ macBytes sha ++ ipBytes spa
           ++ macBytes tha ++ ipBytes tpa

private def requestBytes : List (BitVec 8) :=
  arpBytes 1#16 clientMac clientIp 0#48 serverIp

private def rxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => if t < 28 then (requestBytes[t]?).getD 0#8 else 0#8⟩
private def rxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 28)⟩
private def sopArp : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def serverMacSig : Signal defaultDomain (BitVec 48) := ⟨fun _ => serverMac⟩
private def serverIpSig  : Signal defaultDomain (BitVec 32) := ⟨fun _ => serverIp⟩

private def out : ArpResponderOut defaultDomain :=
  arpResponder rxByte rxValid sopArp serverMacSig serverIpSig

def main : IO Unit := do
  for t in [:60] do
    let b := out.payloadByte.val t
    let v := out.payloadValid.val t
    IO.println s!"cycle {t}: byte={b.toNat} valid={v}"
