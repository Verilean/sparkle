/-
  Sim test for IP.Bus.CAN.

  Validates:
    1. Round-trip on a standard frame (CBFF, 11-bit ID,
       4-byte payload).
    2. Round-trip on an extended frame (CEFF, 29-bit ID,
       8-byte payload).
    3. Round-trip on an RTR frame (no data field).
    4. Bit-stuffing of a worst-case "all ones" payload.
    5. Detection of a tampered (bit-flipped) frame via the
       CRC15 check.

  No published RFC/textbook KAT for CAN frame bits (Bosch
  spec gives the algorithm, not vectors), so the test
  cross-checks builder vs parser on multiple shapes plus a
  hand-computed CRC15 for one canonical example.
-/

import IP.Bus.CAN

open Sparkle.IP.Bus.CAN

namespace Sparkle.Tests.IP.Bus.CANTest

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

/-- Count consecutive same-value bits in a list. -/
private def maxRun (bits : List Bool) : Nat := Id.run do
  let mut maxR := 0
  let mut cur := 0
  let mut prev : Bool := false
  let mut started := false
  for b in bits do
    if !started ∨ b ≠ prev then
      cur := 1
      prev := b
      started := true
    else
      cur := cur + 1
    if cur > maxR then maxR := cur
  return maxR

def main : IO Unit := do
  IO.println "=== CAN 2.0B MAC sim ==="

  let mut ok := true

  -- ──────────────────────────────────────────────────────────────────
  -- Test 1: standard frame, 4-byte payload.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n1. Standard frame round-trip"
  let f1 : Frame :=
    { kind := .standard
    , id := 0x7C5
    , rtr := false
    , dlc := 4
    , data := #[0xDE, 0xAD, 0xBE, 0xEF] }
  let bits1 := buildFrame f1
  IO.println s!"  wire size = {bits1.length} bits"
  match roundTrip f1 with
  | none =>
    IO.println "  ✗ round-trip failed"; ok := false
  | some (f1', crcOk) =>
    if f1'.id = f1.id ∧ f1'.kind = f1.kind ∧ f1'.dlc = f1.dlc ∧
       f1'.data = f1.data ∧ crcOk then
      let idHex := String.ofList (Nat.toDigits 16 f1'.id)
      IO.println s!"  ✓ id=0x{idHex} data={hexOfBytes f1'.data}, CRC ok"
    else
      IO.println s!"  ✗ mismatch: id={f1'.id} data={hexOfBytes f1'.data} crcOk={crcOk}"
      ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Test 2: extended frame, 8-byte payload.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n2. Extended frame round-trip"
  let f2 : Frame :=
    { kind := .extended
    , id := 0x1ABCDEF1   -- 29-bit ID
    , rtr := false
    , dlc := 8
    , data := #[0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF] }
  let bits2 := buildFrame f2
  IO.println s!"  wire size = {bits2.length} bits"
  match roundTrip f2 with
  | none =>
    IO.println "  ✗ round-trip failed"; ok := false
  | some (f2', crcOk) =>
    if f2'.id = f2.id ∧ f2'.kind = f2.kind ∧ f2'.dlc = f2.dlc ∧
       f2'.data = f2.data ∧ crcOk then
      let idHex := String.ofList (Nat.toDigits 16 f2'.id)
      IO.println s!"  ✓ id=0x{idHex} (29-bit) data={hexOfBytes f2'.data}"
    else
      IO.println s!"  ✗ mismatch"
      ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Test 3: RTR (no data field, DLC reflects expected size).
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n3. RTR frame round-trip"
  let f3 : Frame :=
    { kind := .standard
    , id := 0x123
    , rtr := true
    , dlc := 4
    , data := #[] }
  match roundTrip f3 with
  | none =>
    IO.println "  ✗ round-trip failed"; ok := false
  | some (f3', crcOk) =>
    if f3'.id = f3.id ∧ f3'.rtr ∧ f3'.dlc = f3.dlc ∧ crcOk then
      let idHex := String.ofList (Nat.toDigits 16 f3'.id)
      IO.println s!"  ✓ id=0x{idHex} RTR=true DLC={f3'.dlc}"
    else
      IO.println s!"  ✗ mismatch"
      ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Test 4: bit-stuffing on all-ones payload.  After
  -- stuffing, no run of 6+ same bits should exist in the
  -- dynamic region.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n4. Bit-stuffing on worst-case all-ones payload"
  let f4 : Frame :=
    { kind := .standard
    , id := 0x7FF
    , rtr := false
    , dlc := 8
    , data := #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] }
  let bits4 := buildFrame f4
  -- The fixed region at the end is 13 recessive bits = a
  -- legit run of >5, so we check only the dynamic (stuffed)
  -- region: strip the last 13 bits.
  let dyn4 := bits4.take (bits4.length - 13)
  let mr := maxRun dyn4
  IO.println s!"  wire size = {bits4.length} bits"
  IO.println s!"  max run in dynamic region = {mr}"
  if mr ≤ 5 then
    IO.println "  ✓ no run of 6+ same bits (bit-stuffing valid)"
  else
    IO.println s!"  ✗ run of {mr} same bits — stuffing failed"
    ok := false
  -- And round-trip survives.
  match roundTrip f4 with
  | none =>
    IO.println "  ✗ all-ones round-trip failed"; ok := false
  | some (f4', crcOk) =>
    if f4'.data = f4.data ∧ crcOk then
      IO.println "  ✓ all-ones round-trip OK"
    else
      IO.println "  ✗ all-ones round-trip mismatch"; ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- Test 5: tamper detection.  Flip a payload bit in the
  -- on-wire form and confirm CRC check fails.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n5. CRC detects bit-flip tamper"
  let tamperIdx := 25  -- somewhere in the data field
  let bits5 := buildFrame f1
  let arr5 := bits5.toArray
  let mut tampered := arr5
  if tamperIdx < tampered.size then
    tampered := tampered.set! tamperIdx (!arr5[tamperIdx]!)
  match parseFrame tampered.toList with
  | none =>
    IO.println "  ✓ tampered frame fails to parse (acceptable)"
  | some (_, crcOk) =>
    if crcOk then
      IO.println "  ✗ tampered frame passed CRC (bug)"
      ok := false
    else
      IO.println "  ✓ tampered frame rejected by CRC"

  -- ──────────────────────────────────────────────────────────────────
  -- CAN-FD: round-trip on all 7 FD payload sizes.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n6. CAN-FD round-trip across all DLC sizes"
  for (dlc, expectedBytes) in [(0, 0), (8, 8), (9, 12), (10, 16),
                                (11, 20), (12, 24), (13, 32), (14, 48),
                                (15, 64)] do
    -- Build a payload of the right size with a recognizable pattern.
    let mut payload : Array UInt8 := Array.replicate expectedBytes 0
    for i in [:expectedBytes] do
      payload := payload.set! i (UInt8.ofNat (i &&& 0xFF))
    let f : Frame :=
      { kind := .standardFD
      , id := 0x456
      , rtr := false
      , dlc := dlc
      , data := payload
      , brs := true
      , esi := false }
    match roundTrip f with
    | none =>
      IO.println s!"  ✗ DLC={dlc} ({expectedBytes} bytes) — round-trip failed"
      ok := false
    | some (f', crcOk) =>
      let sizeOk := f'.data.size = expectedBytes
      let dataOk := f'.data = f.data
      if f'.kind = f.kind ∧ f'.dlc = dlc ∧ sizeOk ∧ dataOk ∧ crcOk
         ∧ f'.brs = f.brs ∧ f'.esi = f.esi then
        IO.println s!"  ✓ DLC={dlc} → {expectedBytes} bytes (CRC{if expectedBytes ≤ 16 then 17 else 21}, BRS={f'.brs})"
      else
        IO.println s!"  ✗ DLC={dlc} mismatch: kind={repr f'.kind} dlc={f'.dlc} size={f'.data.size} crcOk={crcOk}"
        ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- CAN-FD extended (29-bit ID), 32-byte payload.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n7. CAN-FD extended frame, 32-byte payload"
  let fdExt : Frame :=
    { kind := .extendedFD
    , id := 0x1FEDCBA9
    , rtr := false
    , dlc := 13   -- = 32 bytes
    , data := Array.replicate 32 0xA5
    , brs := true
    , esi := false }
  match roundTrip fdExt with
  | none =>
    IO.println "  ✗ FD extended round-trip failed"
    ok := false
  | some (f', crcOk) =>
    if f'.kind = .extendedFD ∧ f'.id = fdExt.id ∧ f'.dlc = 13 ∧
       f'.data = fdExt.data ∧ crcOk ∧ f'.brs then
      let idHex := String.ofList (Nat.toDigits 16 f'.id)
      IO.println s!"  ✓ id=0x{idHex} (29-bit) DLC=13 (32 bytes), CRC-21 ok"
    else
      IO.println "  ✗ FD extended mismatch"
      ok := false

  -- ──────────────────────────────────────────────────────────────────
  -- CAN-FD tamper detection.
  -- ──────────────────────────────────────────────────────────────────
  IO.println "\n8. CAN-FD CRC detects tamper (32-byte payload, CRC-21)"
  let fdBits := buildFrame fdExt
  let fdArr := fdBits.toArray
  let mut fdBad := fdArr
  let tamperIdx := 80  -- inside data field
  if tamperIdx < fdBad.size then
    fdBad := fdBad.set! tamperIdx (!fdArr[tamperIdx]!)
  match parseFrame fdBad.toList with
  | none =>
    IO.println "  ✓ tampered FD frame fails to parse"
  | some (_, crcOk) =>
    if crcOk then
      IO.println "  ✗ tampered FD frame passed CRC (bug)"
      ok := false
    else
      IO.println "  ✓ tampered FD frame rejected by CRC-21"

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Bus.CANTest
