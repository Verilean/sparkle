/-
  Sim + synth tests for IP.Net.HFTQuote (Chapter 14's quoting engine).

  Simulation: drive a 14-cycle tape — rising then falling mid price with a
  fill pattern that pushes the inventory INTO the ±qMax clamp — and assert
  the circuit's (inv, bid, ask) equal the pure-data reference (`runQuote`)
  cycle-by-cycle via `Signal.val`.

  The tape deliberately exercises:
    * quotes skewing DOWN as inventory builds up (the mean-reversion
      mechanism the ℝ proof relies on),
    * the position limit: 5 consecutive buys against qMax = 3 lots must
      pin the inventory at exactly 3.0 (clamp-by-construction),
    * simultaneous buy+sell (dq = 0).

  Synthesis: the three single-output wrappers under `section
  SynthesisChecks` (record tops don't synthesize; see CLAUDE.md).
-/
import IP.Net.HFTQuote
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPoint
open Sparkle.IP.Net.HFTQuote

namespace Sparkle.Tests.IP.Net.HFTQuoteTest

/-- Tight limit (±3 lots) so the tape actually hits the clamp. -/
private def testParams : QuoteParams :=
  { k1         := BitVec.ofNat 32 32768        -- 0.5 tick/lot
  , halfSpread := BitVec.ofNat 32 81920        -- 1.25 ticks
  , qMax       := BitVec.ofNat 32 (3 * 65536) }

/-- (mid price in ticks ×2^16, buyFill, sellFill) per cycle. -/
private def tape : List (BitVec 32 × Bool × Bool) :=
  let px (t : Nat) : BitVec 32 := BitVec.ofNat 32 (t * 65536)
  [ (px 100, true,  false)   -- build inventory…
  , (px 100, true,  false)
  , (px 101, true,  false)
  , (px 101, true,  false)   -- q would reach 4 — clamp pins it at 3
  , (px 102, true,  false)   -- still pinned
  , (px 102, false, false)   -- hold
  , (px 101, false, true)    -- unwind…
  , (px 101, false, true)
  , (px 100, true,  true)    -- both sides fill: dq = 0
  , (px 100, false, true)
  , (px  99, false, true)
  , (px  99, false, true)    -- q crosses 0 downward
  , (px  98, false, true)
  , (px  98, false, true) ]  -- q would reach −4 — clamp pins at −3

private def mids : Signal defaultDomain (BitVec 32) :=
  ⟨fun t => ((tape[t]?).map (·.1)).getD (BitVec.ofNat 32 (98 * 65536))⟩
private def buys : Signal defaultDomain Bool :=
  ⟨fun t => ((tape[t]?).map (·.2.1)).getD false⟩
private def sells : Signal defaultDomain Bool :=
  ⟨fun t => ((tape[t]?).map (·.2.2)).getD false⟩

private def hw : QuoteOut defaultDomain :=
  quoteEngine testParams.k1 testParams.halfSpread testParams.qMax
    mids buys sells

def main : IO Unit := do
  IO.println "=== HFT quoting engine: circuit vs pure-data reference ==="
  let expected := runQuote testParams (0#32) tape
  let mut bad := 0
  for t in [:tape.length] do
    let some (eInv, eBid, eAsk) := expected[t]? | pure ()
    let hInv := hw.inv.val t
    let hBid := hw.bid.val t
    let hAsk := hw.ask.val t
    if hInv ≠ eInv || hBid ≠ eBid || hAsk ≠ eAsk then
      bad := bad + 1
      IO.println s!"  MISMATCH t={t}: inv {hInv.toInt}/{eInv.toInt} bid {hBid.toInt}/{eBid.toInt} ask {hAsk.toInt}/{eAsk.toInt}"
  -- clamp evidence: inventory pinned at exactly +3.0 lots on cycle 5
  let pinned := hw.inv.val 5
  IO.println s!"  inventory at cycle 5 = {pinned.toInt} (expected {(3*65536 : Int)} = +3 lots, clamp active)"
  if pinned ≠ BitVec.ofNat 32 (3 * 65536) then bad := bad + 1
  if bad == 0 then
    IO.println s!"  ✓ all {tape.length} cycles match the reference (incl. both clamp hits)"
  else
    IO.println s!"  ✗ {bad} mismatches"
    (← IO.getStdout).flush
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.HFTQuoteTest

section SynthesisChecks
open Sparkle.IP.Net.HFTQuote
#synthesizeVerilog quoteBid
#synthesizeVerilog quoteAsk
#synthesizeVerilog quoteInv
end SynthesisChecks
