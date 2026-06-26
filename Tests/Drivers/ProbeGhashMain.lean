/-
  Profiling probe: time .val k for gmulHW alone at increasing k.
  Used to measure baseline per-cycle cost before/after C-FFI tuning.
-/
import Sparkle
import IP.Crypto.GHASH
import IP.Crypto.GHASHHW

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.GHASH (bytesToBlock blockToBytes)
open Sparkle.IP.Crypto.GHASHHW

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

abbrev D := defaultDomain

def main : IO Unit := do
  let h : BitVec 128 := bytesToBlock (bytesOfHex "66e94bd4ef8a2c3b884cfa59ca342b2e")
  let c : BitVec 128 := bytesToBlock (bytesOfHex "0388dace60b6a392f328c2b971b2fe78")
  let startSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let cSig : Signal D (BitVec 128) := ⟨fun _ => c⟩
  let hSig : Signal D (BitVec 128) := ⟨fun _ => h⟩

  -- 1) gmulHW alone (single Signal.loop)
  IO.println "=== gmulHW alone ==="
  (← IO.getStdout).flush
  let mulEngine := gmulHW startSig cSig hSig
  for t in [10, 100, 128, 129, 130, 200, 500, 1000] do
    let t0 ← IO.monoMsNow
    let n := (mulEngine.result.val t).toNat
    let t1 ← IO.monoMsNow
    IO.println s!"  gmulHW.result.val {t}: lastByte={n &&& 0xFF} ({t1 - t0}ms)"
    (← IO.getStdout).flush

  -- 2) ghashFullHW (nested gmulHW)
  IO.println "\n=== ghashFullHW (nested) ==="
  (← IO.getStdout).flush
  let blockSig : Signal D (BitVec 128) := ⟨fun t => if t = 1 then c else 0⟩
  let validSig : Signal D Bool := ⟨fun t => decide (t = 1)⟩
  let engine := ghashFullHW startSig hSig blockSig validSig
  let t0 ← IO.monoMsNow
  let n := (engine.result.val 131).toNat
  let t1 ← IO.monoMsNow
  IO.println s!"  ghashFullHW.result.val 131: lastByte={n &&& 0xFF} ({t1 - t0}ms)"
