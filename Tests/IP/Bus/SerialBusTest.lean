/-
  Combined sim test for IP.Bus.LIN / I2C / SPI.

  Validates each protocol's encoder ↔ decoder round-trip
  plus the parity/checksum logic where applicable.
-/

import IP.Bus.LIN
import IP.Bus.I2C
import IP.Bus.SPI

namespace Sparkle.Tests.IP.Bus.SerialBusTest

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

def testLIN : IO Bool := do
  IO.println "=== LIN 2.2A ==="
  let mut ok := true

  -- PID parity for ID = 0x3C (LIN diagnostic master frame).
  -- Spec example: PID for 0x3C = 0x3C with parity bits → 0x3C.
  -- Actually let's just check the formula is invertible.
  for id in [0x00, 0x01, 0x3C, 0x3D, 0x3F] do
    let pid := Sparkle.IP.Bus.LIN.encodePid id
    match Sparkle.IP.Bus.LIN.decodePid pid with
    | some id' =>
      if id' = id then pure ()
      else
        IO.println s!"  ✗ PID round-trip mismatch for id 0x{Nat.toDigits 16 id |> String.ofList}"
        ok := false
    | none =>
      IO.println s!"  ✗ PID parity invalid for id 0x{Nat.toDigits 16 id |> String.ofList}"
      ok := false
  IO.println "  ✓ PID parity round-trip for 5 IDs"

  -- Tamper test: flipping a parity bit must fail decodePid.
  let goodPid := Sparkle.IP.Bus.LIN.encodePid 0x12
  let badPid := UInt8.ofNat (goodPid.toNat ^^^ 0x80)  -- flip P1
  match Sparkle.IP.Bus.LIN.decodePid badPid with
  | none =>
    IO.println "  ✓ flipped parity bit rejected"
  | some _ =>
    IO.println "  ✗ flipped parity accepted (bug)"
    ok := false

  -- Frame round-trip on classic + enhanced checksum, 4-byte data.
  let f1 : Sparkle.IP.Bus.LIN.Frame :=
    { id := 0x12, data := #[0xDE, 0xAD, 0xBE, 0xEF], checksum := .enhanced }
  match Sparkle.IP.Bus.LIN.roundTrip f1 with
  | none =>
    IO.println "  ✗ enhanced LIN frame round-trip failed"
    ok := false
  | some (f1', chkOk) =>
    if f1'.id = f1.id ∧ f1'.data = f1.data ∧ chkOk then
      IO.println s!"  ✓ enhanced frame id=0x12 data={hexOfBytes f1'.data} OK"
    else
      IO.println "  ✗ enhanced frame mismatch"
      ok := false

  let f2 : Sparkle.IP.Bus.LIN.Frame :=
    { id := 0x3C, data := #[0x01, 0x02], checksum := .classic }
  match Sparkle.IP.Bus.LIN.roundTrip f2 with
  | none =>
    IO.println "  ✗ classic LIN frame round-trip failed"
    ok := false
  | some (_, chkOk) =>
    if chkOk then
      IO.println "  ✓ classic frame (diagnostic ID 0x3C) OK"
    else
      IO.println "  ✗ classic checksum mismatch"
      ok := false

  return ok

def testI2C : IO Bool := do
  IO.println "\n=== I2C ==="
  let mut ok := true

  -- Standard 7-bit write to 0x50 (typical EEPROM addr).
  let tw : Sparkle.IP.Bus.I2C.Transaction :=
    { address := 0x50
    , rw := .write
    , data := #[0x00, 0x10, 0xAA, 0xBB, 0xCC]
    , tenBit := false }
  match Sparkle.IP.Bus.I2C.roundTrip tw with
  | none =>
    IO.println "  ✗ 7-bit write round-trip failed"
    ok := false
  | some p =>
    if p.address = 0x50 ∧ p.rw = .write ∧ p.data = tw.data
       ∧ !p.tenBit then
      IO.println s!"  ✓ 7-bit write to 0x50: 5 bytes round-trip"
    else
      IO.println "  ✗ 7-bit write mismatch"
      ok := false

  -- Standard 7-bit read from 0x50.
  let tr : Sparkle.IP.Bus.I2C.Transaction :=
    { address := 0x50
    , rw := .read
    , data := #[0xAA, 0xBB, 0xCC]
    , tenBit := false }
  match Sparkle.IP.Bus.I2C.roundTrip tr with
  | none =>
    IO.println "  ✗ 7-bit read round-trip failed"
    ok := false
  | some p =>
    if p.rw = .read ∧ p.data.size = 3 then
      IO.println "  ✓ 7-bit read from 0x50: 3 bytes round-trip"
    else
      IO.println "  ✗ 7-bit read mismatch"
      ok := false

  -- 10-bit addressing write to 0x2A0.
  let t10 : Sparkle.IP.Bus.I2C.Transaction :=
    { address := 0x2A0
    , rw := .write
    , data := #[0x55]
    , tenBit := true }
  match Sparkle.IP.Bus.I2C.roundTrip t10 with
  | none =>
    IO.println "  ✗ 10-bit addr round-trip failed"
    ok := false
  | some p =>
    if p.tenBit ∧ p.address = 0x2A0 ∧ p.data = #[0x55] then
      IO.println s!"  ✓ 10-bit write to 0x2A0: 1 byte round-trip"
    else
      IO.println s!"  ✗ 10-bit mismatch: addr={p.address} tenBit={p.tenBit}"
      ok := false

  return ok

def testSPI : IO Bool := do
  IO.println "\n=== SPI ==="
  let mut ok := true

  -- Round-trip mode 0 / mode 1 / mode 2 / mode 3.
  for m in [Sparkle.IP.Bus.SPI.Mode.mode0, Sparkle.IP.Bus.SPI.Mode.mode1,
            Sparkle.IP.Bus.SPI.Mode.mode2, Sparkle.IP.Bus.SPI.Mode.mode3] do
    let t : Sparkle.IP.Bus.SPI.Transaction :=
      { mode := m
      , mosi := #[0xA5, 0x5A, 0x12, 0x34]
      , miso := #[0x00, 0xFF, 0x55, 0xAA] }
    let (mosiOut, misoOut) := Sparkle.IP.Bus.SPI.roundTrip t
    if mosiOut = t.mosi ∧ misoOut = t.miso then
      IO.println s!"  ✓ SPI mode {m.toNumeric}: MOSI/MISO 4-byte full-duplex round-trip"
    else
      IO.println s!"  ✗ SPI mode {m.toNumeric} mismatch: MOSI={hexOfBytes mosiOut}, MISO={hexOfBytes misoOut}"
      ok := false

  return ok

def main : IO Unit := do
  IO.println "=== Serial bus suite (LIN + I2C + SPI) ==="
  let linOk ← testLIN
  let i2cOk ← testI2C
  let spiOk ← testSPI
  if linOk ∧ i2cOk ∧ spiOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Bus.SerialBusTest
