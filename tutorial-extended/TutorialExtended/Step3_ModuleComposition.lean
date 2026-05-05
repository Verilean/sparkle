/-
  Tutorial Step 3: composing modules with named record outputs.

  We build a tiny "monitor" pipeline:

      raw count ─→ Counter ─→ (count, parity) ─→ Monitor ─→ stable_count
                                              ╲─→ ParityCheck ─→ alert

  Three modules:
    1. Counter: produces (count, parity) using Step 2's record output
    2. Monitor: takes the count and detects when it has reached 100
    3. ParityCheck: takes the parity and detects continuous odd-streaks

  Top-level module wires them together, returning ANOTHER named
  record with three fields. The whole composition stays readable
  because every signal — input AND output, top-level AND nested —
  has a name.

  This is the design pattern the user asked about: hierarchical
  modules where output unpacking by `.fst`/`.snd` would become
  unreadable, but `.field_name` stays clear.
-/

import Sparkle
import TutorialExtended.Step2_MultipleOutputs

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open TutorialExtended.Step2 (counterAndParity_record CounterParityOut)

namespace TutorialExtended.Step3

/-! ## Module 2: Monitor — detects when count has reached a threshold.

  Returns a single Bool output. No record needed for a single-output
  module; the let-binding `reached` becomes `_gen_reached` in Verilog. -/

def monitor {dom : DomainConfig}
    (count : Signal dom (BitVec 8)) : Signal dom Bool :=
  let threshold := Signal.pure 100#8
  let reached   := count === threshold
  reached

/-! ## Module 3: ParityCheck — detects 4 consecutive odd parities.

  Has both an input (parity) and *internal state* (a 2-bit shift
  register tracking the last 4 parity values). The output is a
  single Bool flag. -/

declare_signal_state ParityCheckState
  | shiftReg : BitVec 4 := 0#4

/-- ParityCheck has internal state (`shiftReg`) plus an output (`alert`).
    Pattern: the `Signal.loop` body returns `(state, output)`. We apply
    `Signal.snd` after `loop` to peel off the output. -/
def parityCheck {dom : DomainConfig}
    (parity : Signal dom Bool) : Signal dom Bool :=
  Signal.snd (Signal.loop (α := ParityCheckState × Bool) fun self =>
    let stateOnly := Signal.fst self
    let shiftReg  := ParityCheckState.shiftReg stateOnly
    let parityBV  := parity.map (fun b => if b then 1#1 else 0#1)
    let shifted   := shiftReg.map (BitVec.extractLsb' 0 3 ·)
    let newReg    := shifted ++ parityBV
    let alert     := newReg === Signal.pure 0xF#4
    let nextState : Signal dom ParityCheckState :=
      bundleAll! [Signal.register 0#4 newReg]
    bundle2 nextState alert)

/-! ## Top-level: wire all three modules together with a NAMED RECORD output.

  The whole point: instead of returning `Signal dom (BitVec 8 × Bool × Bool)`
  (which the caller must unpack with `.fst`, `.snd.fst`, `.snd.snd`),
  return a record `MonitorReport` with named fields. -/

declare_signal_state MonitorReport
  | currentCount : BitVec 8 := 0#8
  | thresholdHit : Bool     := false
  | parityAlert  : Bool     := false

/-- Top-level module composing Counter + Monitor + ParityCheck. -/
def monitorTop {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom MonitorReport :=
  -- Use Step 2's record-output counter — projection by .count, .parity is named.
  let cp        := counterAndParity_record en
  let count     := CounterParityOut.count cp
  let parity    := CounterParityOut.parity cp
  -- Wire each downstream module by its named outputs.
  let thresholdHit := monitor count
  let parityAlert  := parityCheck parity
  -- Bundle the three named outputs into a named record.
  bundleAll! [count, thresholdHit, parityAlert]

/-! ## Demo

  Read each field by name. No `.fst.snd.fst` chains.
-/

def runDemo : IO Unit := do
  let report := monitorTop (dom := defaultDomain) (Signal.pure true)
  let counts   := (MonitorReport.currentCount report).sample 110
  let hits     := (MonitorReport.thresholdHit report).sample 110
  let alerts   := (MonitorReport.parityAlert  report).sample 110
  IO.println s!"counts (first 10): {counts.take 10}"
  IO.println s!"counts around 100: {counts.drop 98 |>.take 5}"
  IO.println s!"thresholdHit at cycle 100: {hits.drop 100 |>.head?}"
  IO.println s!"parityAlert seen?         : {alerts.contains true}"

end TutorialExtended.Step3
