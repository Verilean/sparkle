/-
  Sim test for IP.Bus.DroneCAN.

  Covers single-frame transfer encode/decode:
    * 29-bit CAN ID round-trip (message + service shapes)
    * Tail byte encode/decode
    * NodeStatus broadcast
    * ESC RawCommand single-frame
    * CRC-16-CCITT-FALSE KAT against well-known vectors
-/

import IP.Bus.DroneCAN

open Sparkle.IP.Bus.CAN (Frame FrameKind)
open Sparkle.IP.Bus.DroneCAN

namespace Sparkle.Tests.IP.Bus.DroneCANTest

def main : IO Unit := do
  IO.println "=== DroneCAN (UAVCAN v0) sim ==="

  let mut ok := true

  -- ────────────────────────────────────────────────
  IO.println "\n1. Tail byte encode/decode round-trip"
  let tb : TailByte :=
    { sot := true, eot := false, toggle := true, transferId := 21 }
  let byte := tb.toByte
  let tb' := TailByte.ofByte byte
  if tb.sot = tb'.sot ∧ tb.eot = tb'.eot
     ∧ tb.toggle = tb'.toggle ∧ tb.transferId = tb'.transferId then
    IO.println s!"  ✓ SOT=1 EOT=0 toggle=1 tid=21 → byte=0x{Nat.toDigits 16 byte.toNat |> String.ofList}, round-trip OK"
  else
    IO.println "  ✗ tail byte round-trip failed"
    ok := false

  -- ────────────────────────────────────────────────
  IO.println "\n2. Message CAN ID round-trip"
  -- Priority 7, msg type 341 (NodeStatus), src node 0x42.
  let mid := messageCanId 7 341 0x42
  let dec := decodeCanId mid
  if !dec.isService ∧ dec.priority = 7 ∧ dec.typeId = 341
     ∧ dec.srcNodeId = 0x42 then
    IO.println s!"  ✓ message CAN ID 0x{Nat.toDigits 16 mid |> String.ofList} decodes to prio=7 type=341 src=0x42"
  else
    IO.println s!"  ✗ decode mismatch: {repr dec}"
    ok := false

  -- ────────────────────────────────────────────────
  IO.println "\n3. Service CAN ID round-trip"
  let sid := serviceCanId 4 1 true 0x10 0x20
  let dec' := decodeCanId sid
  if dec'.isService ∧ dec'.priority = 4 ∧ dec'.typeId = 1
     ∧ dec'.isRequest ∧ dec'.dstNodeId = 0x10 ∧ dec'.srcNodeId = 0x20 then
    IO.println s!"  ✓ service CAN ID 0x{Nat.toDigits 16 sid |> String.ofList} decodes correctly"
  else
    IO.println s!"  ✗ decode mismatch: {repr dec'}"
    ok := false

  -- ────────────────────────────────────────────────
  IO.println "\n4. NodeStatus broadcast (7-byte payload)"
  let f := buildNodeStatus 0x42 0 12345 .ok .operational
                          (vendorCode := 0xABCD)
  if f.kind = .extended ∧ f.data.size = 8 then
    IO.println s!"  ✓ NodeStatus frame: 8 bytes (7 payload + tail)"
  else
    IO.println "  ✗ NodeStatus frame size wrong"
    ok := false
  match parseSingleFrame f with
  | none =>
    IO.println "  ✗ parseSingleFrame returned none"
    ok := false
  | some (dec, tail, payload) =>
    if dec.typeId = 341 ∧ dec.srcNodeId = 0x42 ∧
       tail.sot ∧ tail.eot ∧ payload.size = 7 then
      -- Spot-check the payload bytes.
      -- uptime LSB first: 12345 = 0x3039
      if payload[0]! = 0x39 ∧ payload[1]! = 0x30 ∧
         payload[2]! = 0 ∧ payload[3]! = 0 ∧
         -- mode-health byte: health=0(OK), mode=0(operational), sub=0 ⇒ 0
         payload[4]! = 0 ∧
         -- vendor code LSB first: 0xABCD
         payload[5]! = 0xCD ∧ payload[6]! = 0xAB then
        IO.println "  ✓ payload bytes match expected encoding"
      else
        IO.println s!"  ✗ payload mismatch: {payload.toList}"
        ok := false
    else
      IO.println s!"  ✗ field mismatch: typeId={dec.typeId} src={dec.srcNodeId}"
      ok := false

  -- ────────────────────────────────────────────────
  IO.println "\n5. ESC RawCommand (3 channels)"
  -- Throttle: ch0=8191 (max), ch1=-8191 (max reverse), ch2=0
  let escPayload := encodeEscRawCommand3 8191 (-8191) 0
  IO.println s!"  payload = {escPayload.toList}"
  match buildBroadcastSingle 7 msgTypeIdEscRawCommand 0x10 5 escPayload with
  | none =>
    IO.println "  ✗ build returned none"
    ok := false
  | some esc =>
    if esc.kind = .extended ∧ esc.data.size = 7 then
      IO.println s!"  ✓ ESC RawCommand frame, {esc.data.size} bytes"
    else
      IO.println "  ✗ ESC frame size wrong"
      ok := false
    match parseSingleFrame esc with
    | some (dec, tail, payload) =>
      if dec.typeId = 1030 ∧ dec.srcNodeId = 0x10 ∧
         tail.transferId = 5 ∧ payload.size = 6 then
        IO.println "  ✓ round-trip parseSingleFrame OK"
      else
        IO.println s!"  ✗ parsed fields: {repr dec} {repr tail}"
        ok := false
    | none =>
      IO.println "  ✗ ESC parse returned none"
      ok := false

  -- ────────────────────────────────────────────────
  IO.println "\n6. CRC-16-CCITT-FALSE KAT"
  -- Well-known: CRC-16-CCITT-FALSE("123456789") = 0x29B1
  let kat := "123456789".toUTF8.toList.toArray
  let crc := crc16Ccitt kat
  if crc = 0x29B1 then
    IO.println s!"  ✓ CRC-16-CCITT-FALSE(\"123456789\") = 0x{Nat.toDigits 16 crc |> String.ofList}"
  else
    IO.println s!"  ✗ got 0x{Nat.toDigits 16 crc |> String.ofList}, expected 0x29B1"
    ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Bus.DroneCANTest
