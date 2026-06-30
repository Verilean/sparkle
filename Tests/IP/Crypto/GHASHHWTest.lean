/-
  Sim test for IP.Crypto.GHASHHW.gmulHW — cycle-accurate
  GF(2^128) multiplier in Sparkle Signal DSL.

  Two checks:
    1. Cross-validate vs the pure-data `GHASH.gmul`
       reference on the NIST GCM Test Case 2 inputs
       (H × C_1, both 128-bit).
    2. Confirm the pipeline timing: start at cycle 0,
       done pulses at cycle 129 (= start + 128 round
       cycles + 1 strobe cycle).

  This is the first crypto HW block that uses the post-C2
  fix — the simulator now reaches all 129 cycles in O(N)
  time instead of timing out.
-/
import Sparkle
import IP.Crypto.GHASH
import IP.Crypto.GHASHHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.GHASH (gmul bytesToBlock blockToBytes)
open Sparkle.IP.Crypto.GHASHHW

namespace Sparkle.Tests.IP.Crypto.GHASHHWTest

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

abbrev D := defaultDomain

/-- Build a Signal that holds a constant after start pulse:
    val 0 = v0, val t (t ≥ 1) = v1. -/
private def constSig {α : Type} (v : α) : Signal D α :=
  ⟨fun _ => v⟩

/-- start pulses true only at cycle 0. -/
private def startSig : Signal D Bool :=
  ⟨fun t => decide (t = 0)⟩

def main : IO Unit := do
  IO.println "=== GHASH multi-cycle HW multiplier sim ==="
  (← IO.getStdout).flush

  let mut ok := true

  -- NIST GCM Test Case 2: H × C_1
  --   H  = 66e94bd4ef8a2c3b884cfa59ca342b2e
  --   C1 = 0388dace60b6a392f328c2b971b2fe78
  let h : BitVec 128 := bytesToBlock (bytesOfHex "66e94bd4ef8a2c3b884cfa59ca342b2e")
  let c : BitVec 128 := bytesToBlock (bytesOfHex "0388dace60b6a392f328c2b971b2fe78")

  -- Reference (pure-data) product.  We are multiplying
  -- the GHASH state Y_1 = (0 XOR C_1) × H = C_1 × H.
  let expected : BitVec 128 := gmul c h
  IO.println s!"  reference gmul(c, h) = {hexOfBytes (blockToBytes expected)}"

  -- HW circuit: feed start at cycle 0, hold c on xIn, h on yIn.
  let engine := gmulHW startSig (constSig c) (constSig h)

  -- Done should pulse at cycle 129 (start at 0 ⇒ cnt reaches 128 at cycle 129).
  for t in [0, 1, 2, 128, 129, 130] do
    let d := engine.done.val t
    let r := engine.result.val t
    IO.println s!"  t={t}: done={d}, result={hexOfBytes (blockToBytes r)}"

  -- Pipeline check: done MUST pulse exactly at cycle 129.
  if engine.done.val 128 then
    IO.println "  ✗ done pulsed early (t=128)"
    ok := false
  else
    IO.println "  ✓ done not asserted at t=128"
  if engine.done.val 129 then
    IO.println "  ✓ done asserted at t=129"
  else
    IO.println "  ✗ done missed t=129"
    ok := false

  -- Correctness check: at cycle 129 the result should equal `expected`.
  let hwResult := engine.result.val 129
  if hwResult = expected then
    IO.println s!"  ✓ HW result matches pure-data gmul"
  else
    IO.println s!"  ✗ HW result {hexOfBytes (blockToBytes hwResult)} ≠ expected {hexOfBytes (blockToBytes expected)}"
    ok := false

  if !ok then
    IO.println "\nFAIL (gmulHW)"
    IO.Process.exit 1

  -- Multi-block ghashFullHW is validated in the separate
  -- `probe-ghash` exe (Tests/Drivers/ProbeGhashMain.lean) —
  -- combining gmulHW.val(small) AND ghashFullHW.val(131) in
  -- ONE exe still hangs even with the C2 fix (T.6.HW.c
  -- partial: root cause = interactions between multiple
  -- concurrent Signal.loop instances when one has been used
  -- for sampling before another is queried).  Until that's
  -- fully nailed, validate each HW block in its own exe.

  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.GHASHHWTest

-- Synthesis checks live in Tests/IP/Crypto/GHASHHWSynth.lean.
--
-- T.6.HW.c note: the `ghash-hw-test` exe (this file's main) has a
-- known startup-time issue — the linked binary takes minutes to
-- initialize, regardless of test content.  The standalone
-- `probe-ghash` exe (Tests/Drivers/ProbeGhashMain.lean) validates
-- both gmulHW and ghashFullHW in <2s.  Use that for CI / quick
-- regression; this file's main is kept as documentation.
