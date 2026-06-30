/-
  Sim test for IP.TLS.KeySchedule.

  Validates the TLS 1.3 key schedule against RFC 8448 §3
  "Simple 1-RTT Handshake" trace.  Every intermediate secret
  is published in the RFC, so we can check each Derive-Secret
  / HKDF-Extract step independently rather than only the
  final outputs.
-/

import IP.TLS.KeySchedule
import IP.Crypto.HKDF

open Sparkle.IP.TLS.KeySchedule
open Sparkle.IP.Crypto.HKDF (sha256)

namespace Sparkle.Tests.IP.TLS.KeyScheduleTest

private def bytesOfHex (s : String) : Array UInt8 := Id.run do
  let chars := s.toList.toArray
  let nibble (c : Char) : Nat :=
    if c.isDigit then c.toNat - 0x30
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 0x61 + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 0x41 + 10
    else 0
  let mut out : Array UInt8 := #[]
  let n := chars.size / 2
  for i in [:n] do
    let hi := nibble chars[2 * i]!
    let lo := nibble chars[2 * i + 1]!
    out := out.push (UInt8.ofNat (hi * 16 + lo))
  return out

private def hexOfBytes (bs : Array UInt8) : String := Id.run do
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  let mut out := ""
  for b in bs do
    let n := b.toNat
    out := out.push (digit ((n >>> 4) &&& 0xF))
    out := out.push (digit (n &&& 0xF))
  return out

private def check (label : String) (got : Array UInt8) (expectedHex : String)
    (ok : IO.Ref Bool) : IO Unit := do
  let gotHex := hexOfBytes got
  let okV := gotHex = expectedHex
  IO.println s!"  {if okV then "✓" else "✗"} {label}"
  if !okV then
    IO.println s!"    expected: {expectedHex}"
    IO.println s!"    got     : {gotHex}"
    ok.set false

def main : IO Unit := do
  IO.println "=== TLS 1.3 key schedule (RFC 8448 §3 trace) ==="

  let ok ← IO.mkRef true

  -- RFC 8448 §3 — Simple 1-RTT Handshake values.
  let dheSecret := bytesOfHex "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"
  let chShHash  := bytesOfHex "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"

  -- 1. Early Secret (no PSK → PSK = 0).
  let esExp := "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"
  let es := earlySecret #[]
  check "Early Secret" es esExp ok

  -- 2. Handshake Secret stage.
  let hs := deriveHandshakeStage es dheSecret chShHash
  check "Handshake Secret" hs.handshakeSecret
    "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac" ok
  check "client_handshake_traffic_secret" hs.cHsTrafficSecret
    "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21" ok
  check "server_handshake_traffic_secret" hs.sHsTrafficSecret
    "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38" ok

  -- 3. Per-record key + iv from server handshake traffic secret.
  let serverKeys := deriveRecordKeys hs.sHsTrafficSecret
  check "server handshake write_key"  serverKeys.key
    "3fce516009c21727d0f2e4e86ee403bc" ok
  check "server handshake write_iv"   serverKeys.iv
    "5d313eb2671276ee13000b30" ok

  -- 4. Per-record key + iv from client handshake traffic secret.
  let clientKeys := deriveRecordKeys hs.cHsTrafficSecret
  check "client handshake write_key"  clientKeys.key
    "dbfaa693d1762c5b666af5d950258d01" ok
  check "client handshake write_iv"   clientKeys.iv
    "5bd3c71b836e0b76bb73265f" ok

  -- 5. Master Secret + application secrets.
  -- Transcript hash through server Finished (RFC 8448 §3).
  let chSfHash := bytesOfHex "9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13"
  let app := deriveApplicationStage hs.handshakeSecret chSfHash
  check "Master Secret" app.masterSecret
    "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919" ok
  check "client_application_traffic_secret_0" app.cApTrafficSecret
    "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5" ok
  check "server_application_traffic_secret_0" app.sApTrafficSecret
    "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643" ok

  if (← ok.get) then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.TLS.KeyScheduleTest
