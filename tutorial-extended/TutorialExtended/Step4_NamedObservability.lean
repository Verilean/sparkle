/-
  Tutorial Step 4: named outputs ⇒ probe-friendly observability.

  When you `#synthesizeVerilog` a Sparkle module, every let-bound
  Signal becomes a named wire `_gen_<bindingName>`. The JIT runtime
  can resolve these names via `JIT.findWire`, so a debug probe
  can read any internal signal *by name*, not by position.

  But: the elab + CppSim sometimes **inlines** wires whose only
  consumer is downstream logic, dropping them from the JIT struct
  layout. If you want to observe them, you have to either:

    (a) keep a `let` binding alive by referencing it once at the
        top level (e.g. via `bundleAll!`), or
    (b) explicitly tag the wire as observable in the synthesis
        descriptor (`SoCOutput.wireNames` for the RV32 SoC).

  This file shows the same module two ways:
    - inlined: just call the FSM in the body, no exposed wire
    - exposed: bind the FSM output as a top-level signal so it
      survives into the Verilog as a struct field

  The exposed version is what we used to debug 9d0704e (see
  `docs/BitNet_LTL_Investigation.md`).
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step4

declare_signal_state SmallFSMState
  | regA : BitVec 8 := 0#8
  | regB : BitVec 8 := 0#8

/-- A small two-register FSM. Output = regA + regB. -/
def fsm {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  Signal.snd (Signal.loop (α := SmallFSMState × BitVec 8) fun self =>
    let s     := Signal.fst self
    let regA  := SmallFSMState.regA s
    let regB  := SmallFSMState.regB s
    let regAN := Signal.mux en (regA + 1#8) regA
    let regBN := Signal.mux en (regB + 2#8) regB
    -- The intermediate "sum" wire — we'd like to probe this!
    let sum   := regAN + regBN
    let nextState : Signal dom SmallFSMState :=
      bundleAll! [Signal.register 0#8 regAN, Signal.register 0#8 regBN]
    bundle2 nextState sum)

/-! ## Inlined vs exposed wire — same circuit, different observability

  Both modules below have identical hardware behavior (the FSM
  produces the same trace). They differ only in how the
  `intermediate` wire is structured in the generated Verilog. -/

/-- Variant 1: just call `fsm` and forget about its internals.
    The "sum" wire is internal to `fsm` and gets inlined into the
    output expression. Probes can't see it. -/
def topInlined {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  fsm en

/-- Variant 2: bind the FSM output to a top-level let. This
    survives into the generated Verilog as a named wire `_gen_fsmOut`. -/
def topExposed {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  let fsmOut := fsm en
  fsmOut

-- Variant 3: expose multiple internal signals via a record.

declare_signal_state TopReport
  | result : BitVec 8 := 0#8

def topRecord {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom TopReport :=
  let result := fsm en
  bundleAll! [result]

/-! ## Demo -/

def runDemo : IO Unit := do
  let v1 := (topInlined (dom := defaultDomain) (Signal.pure true)).sample 6
  let v2 := (topExposed (dom := defaultDomain) (Signal.pure true)).sample 6
  let r3 := topRecord (dom := defaultDomain) (Signal.pure true)
  let v3 := (TopReport.result r3).sample 6
  IO.println s!"inlined : {v1}"
  IO.println s!"exposed : {v2}"
  IO.println s!"record  : {v3}"

end TutorialExtended.Step4
