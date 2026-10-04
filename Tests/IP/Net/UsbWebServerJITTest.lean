/-
  JIT-backed sim test for the USB→SLIP→IPv4→TCP→HTTP chain.

  Composes scalar projection wrappers around the multi-output
  sub-modules so each `.gotRequest` / `.done` / `.outValid`
  projection reaches the elaborator on its known path.
-/

import IP.Net.UART
import IP.Net.SLIP
import IP.Net.IPv4
import IP.Net.TCP
import IP.Net.HTTP
import Sparkle.Core.JIT
import Sparkle.Core.SimTyped

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Net.SLIP

namespace Sparkle.Tests.IP.Net.UsbWebServerJITTest

abbrev D := defaultDomain

@[hardware_module] def ever (s : Signal D Bool) : Signal D Bool :=
  circuit do
    let seen ← Signal.reg false
    let seenSig := (seen : Signal D Bool)
    seen <~ Signal.mux s (Signal.pure true) seenSig
    return Signal.mux s (Signal.pure true) seenSig

@[hardware_module] def firstPulse (s : Signal D Bool) : Signal D Bool :=
  circuit do
    let seen ← Signal.reg false
    let seenSig := (seen : Signal D Bool)
    seen <~ Signal.mux s (Signal.pure true) seenSig
    return Signal.mux s
      (Signal.mux seenSig (Signal.pure false) (Signal.pure true))
      (Signal.pure false)

@[hardware_module] def slipDeframerOutByteSig
    (wireByte : Signal D (BitVec 8))
    (wireValid : Signal D Bool) : Signal D (BitVec 8) :=
  (slipDeframerHW wireByte wireValid).outByte

@[hardware_module] def slipDeframerOutValidSig
    (wireByte : Signal D (BitVec 8))
    (wireValid : Signal D Bool) : Signal D Bool :=
  (slipDeframerHW wireByte wireValid).outValid

@[hardware_module] def ipv4DoneSig
    (defByte : Signal D (BitVec 8))
    (defValid : Signal D Bool)
    (sopIp : Signal D Bool) : Signal D Bool :=
  (Sparkle.IP.Net.IPv4.ipv4RxParser defByte defValid sopIp).done

@[hardware_module] def tcpDoneSig
    (tcpByte : Signal D (BitVec 8))
    (tcpValid : Signal D Bool)
    (sopTcp : Signal D Bool) : Signal D Bool :=
  (Sparkle.IP.Net.TCP.tcpRxParser tcpByte tcpValid sopTcp).done

@[hardware_module] def httpGotSig
    (httpByte : Signal D (BitVec 8))
    (httpValid : Signal D Bool) : Signal D Bool :=
  (Sparkle.IP.Net.HTTP.httpRequestParser httpByte httpValid).gotRequest

@[hardware_module] def pack4 (ov ip tc ht : Signal D Bool) : Signal D (BitVec 4) :=
  let ovBit := Signal.mux ov (Signal.pure 8#4) (Signal.pure 0#4)
  let ipBit := Signal.mux ip (Signal.pure 4#4) (Signal.pure 0#4)
  let tcBit := Signal.mux tc (Signal.pure 2#4) (Signal.pure 0#4)
  let htBit := Signal.mux ht (Signal.pure 1#4) (Signal.pure 0#4)
  let or01 := (fun a b => a ||| b) <$> ovBit <*> ipBit
  let or012 := (fun a b => a ||| b) <$> or01 <*> tcBit
  (fun a b => a ||| b) <$> or012 <*> htBit

def usbWebServerTop
    (wireByte  : Signal D (BitVec 8))
    (wireValid : Signal D Bool) :
    Signal D (BitVec 4) :=
  let dv := slipDeframerOutValidSig wireByte wireValid
  let db := slipDeframerOutByteSig wireByte wireValid
  let sopIp := firstPulse dv
  let ipDone := ipv4DoneSig db dv sopIp
  let ipDoneEver := ever ipDone
  let tcpValid : Signal D Bool := (fun a b => a && b) <$> dv <*> ipDoneEver
  let sopTcp := firstPulse tcpValid
  let tcpDone := tcpDoneSig db tcpValid sopTcp
  let tcpDoneEver := ever tcpDone
  let httpValid : Signal D Bool := (fun a b => a && b) <$> dv <*> tcpDoneEver
  let httpGot := httpGotSig db httpValid
  pack4 dv ipDone tcpDone httpGot

#sim usbWebServerTop

private def ipv4Header (totalLen : Nat) (srcIp dstIp : Nat) : List UInt8 :=
  [0x45, 0x00, (totalLen >>> 8).toUInt8, (totalLen &&& 0xFF).toUInt8
  , 0x00, 0x01, 0x40, 0x00, 0x40, 0x06, 0x00, 0x00
  , ((srcIp >>> 24) &&& 0xFF).toUInt8, ((srcIp >>> 16) &&& 0xFF).toUInt8
  , ((srcIp >>> 8) &&& 0xFF).toUInt8, (srcIp &&& 0xFF).toUInt8
  , ((dstIp >>> 24) &&& 0xFF).toUInt8, ((dstIp >>> 16) &&& 0xFF).toUInt8
  , ((dstIp >>> 8) &&& 0xFF).toUInt8, (dstIp &&& 0xFF).toUInt8 ]

private def tcpHeader (srcPort dstPort : Nat) : List UInt8 :=
  [(srcPort >>> 8).toUInt8, (srcPort &&& 0xFF).toUInt8
  , (dstPort >>> 8).toUInt8, (dstPort &&& 0xFF).toUInt8
  , 0, 0, 0, 0, 0, 0, 0, 0, 0x50, 0x18, 0xFF, 0xFF, 0, 0, 0, 0]

private def httpGet : List UInt8 :=
  "GET / HTTP/1.0\r\n\r\n".toUTF8.toList.toArray.toList.map (fun c => c.toNat.toUInt8)

private def buildRequestFrame : List UInt8 :=
  let payload := httpGet
  let totalLen := 20 + 20 + payload.length
  let ip := ipv4Header totalLen 0xC0A80701 0xC0A80702
  encodeFrame (ip ++ tcpHeader 12345 80 ++ payload)

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  USB→SLIP→IPv4→TCP→HTTP JIT sim        ║"
  IO.println "╚════════════════════════════════════════╝"

  let frame := buildRequestFrame
  let frameArr := frame.toArray
  IO.println s!"  SLIP-encoded frame size: {frame.length} bytes"

  let sim ← usbWebServerTop.Sim.load
  let horizon := frame.length + 30

  let mut ipDoneAt : Option Nat := none
  let mut tcpDoneAt : Option Nat := none
  let mut httpGotAt : Option Nat := none

  let t0 ← IO.monoMsNow
  for t in [0:horizon] do
    let valid : BitVec 1 := if t < frameArr.size then 1#1 else 0#1
    let byte  : BitVec 8 :=
      if t < frameArr.size then BitVec.ofNat 8 frameArr[t]!.toNat else 0#8
    let inp : usbWebServerTop.Sim.SimInput :=
      { _gen_wireByte := byte, _gen_wireValid := valid }
    Sparkle.Core.Sim.Sim.step sim inp
    let out ← Sparkle.Core.Sim.Sim.read sim
    let bits := out.out.toNat
    let ipDone   := (bits >>> 2) &&& 1 = 1
    let tcpDone  := (bits >>> 1) &&& 1 = 1
    let httpGot  := bits &&& 1 = 1
    if ipDone ∧ ipDoneAt.isNone then ipDoneAt := some t
    if tcpDone ∧ tcpDoneAt.isNone then tcpDoneAt := some t
    if httpGot ∧ httpGotAt.isNone then httpGotAt := some t
  let t1 ← IO.monoMsNow

  Sparkle.Core.Sim.Sim.destroy sim
  IO.println s!"  {horizon} cycles in {t1 - t0} ms"

  let mut ok := true
  match ipDoneAt with
  | some c => IO.println s!"  ✓ ipv4 done at cycle {c}"
  | none => IO.println "  ✗ ipv4 done never pulsed"; ok := false
  match tcpDoneAt with
  | some c => IO.println s!"  ✓ tcp done at cycle {c}"
  | none => IO.println "  ✗ tcp done never pulsed"; ok := false
  match httpGotAt with
  | some c => IO.println s!"  ✓ http gotRequest at cycle {c}"
  | none => IO.println "  ✗ http gotRequest never pulsed"; ok := false

  if ok then IO.println "\nALL PASS"
  else IO.println "\nFAIL"; IO.Process.exit 1

end Sparkle.Tests.IP.Net.UsbWebServerJITTest
