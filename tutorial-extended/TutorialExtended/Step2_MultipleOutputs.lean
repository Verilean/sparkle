/-
  Tutorial Step 2: a module with TWO outputs — and the "unbind problem".

  Once a module produces more than one signal, you have to bundle them
  into a tuple. The caller then has to unpack the tuple by position.
  This is where readability starts to suffer.

  We show the same circuit three ways:

    (a) anonymous tuple via `bundle2` — caller uses `.fst` / `.snd`
    (b) explicit `let` names + `bundle2` — output wires are named
        but the caller still needs `.fst` / `.snd` (positional)
    (c) named record via `declare_signal_state` — caller uses
        `.fieldName`, output wires are still named, AND each
        component has a meaningful Verilog/JIT wire name

  Same hardware in all three cases. Different ergonomics.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace TutorialExtended.Step2

/-! ## (a) Anonymous tuple output

  The simplest way to return two signals: just `bundle2`. But the
  caller has no idea what `.fst` and `.snd` mean without reading
  this definition. -/
def counterAndParity_anon {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8 × Bool) :=
  Signal.loop fun self =>
    let count    := Signal.fst self
    let _parity  := Signal.snd self
    let countNext  := Signal.mux en (count + 1#8) count
    -- LSB tells us if the value is odd → parity = LSB.
    -- LSB tells us if the value is odd → parity = lowest bit (as Bool).
    let parityBV   := countNext.map (BitVec.extractLsb' 0 1 ·)
    let parityNext := parityBV === Signal.pure 1#1
    bundle2 (Signal.register 0#8 countNext)
            (Signal.register false parityNext)

/-! ## (b) Named outputs with `let` (no record yet)

  Same circuit, but each output signal gets a `let` name. The
  Sparkle elab uses these as wire-name hints, so the generated
  Verilog has `_gen_countOut` and `_gen_parityOut` instead of
  anonymous `_tmp_a_NNNN`. The caller still needs `.fst`/`.snd`. -/
def counterAndParity_letNamed {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom (BitVec 8 × Bool) :=
  Signal.loop fun self =>
    let count    := Signal.fst self
    let _parity  := Signal.snd self
    let countNext  := Signal.mux en (count + 1#8) count
    -- LSB tells us if the value is odd → parity = lowest bit (as Bool).
    let parityBV   := countNext.map (BitVec.extractLsb' 0 1 ·)
    let parityNext := parityBV === Signal.pure 1#1
    let countOut  := Signal.register 0#8 countNext
    let parityOut := Signal.register false parityNext
    bundle2 countOut parityOut

/-! ## (c) Named record output via `declare_signal_state`

  `declare_signal_state` turns a list of named fields into a
  Sparkle-compatible tuple type with accessor defs. The caller
  uses `.count` / `.parity` instead of `.fst` / `.snd`, and the
  Verilog/JIT wire names match the field names automatically. -/

declare_signal_state CounterParityOut
  | count  : BitVec 8 := 0#8
  | parity : Bool     := false

def counterAndParity_record {dom : DomainConfig}
    (en : Signal dom Bool) : Signal dom CounterParityOut :=
  Signal.loop fun self =>
    let count      := CounterParityOut.count self
    let _parity    := CounterParityOut.parity self
    let countNext  := Signal.mux en (count + 1#8) count
    -- LSB tells us if the value is odd → parity = lowest bit (as Bool).
    let parityBV   := countNext.map (BitVec.extractLsb' 0 1 ·)
    let parityNext := parityBV === Signal.pure 1#1
    let countOut   := Signal.register 0#8 countNext
    let parityOut  := Signal.register false parityNext
    bundleAll! [countOut, parityOut]

/-! ## Demo: same outputs from all three

  All three circuits produce identical traces. The difference is
  purely how callers and downstream tools (Verilator probes, JIT
  wire-lookup, formal proofs) refer to the values. -/

def runDemo : IO Unit := do
  -- (a) anonymous: project by .fst / .snd
  let outA   := counterAndParity_anon (dom := defaultDomain) (Signal.pure true)
  let countsA := (Signal.fst outA).sample 8
  let parA    := (Signal.snd outA).sample 8
  IO.println s!"(a) counts={countsA}  parity={parA}"

  -- (b) let-named: still positional
  let outB   := counterAndParity_letNamed (dom := defaultDomain) (Signal.pure true)
  let countsB := (Signal.fst outB).sample 8
  let parB    := (Signal.snd outB).sample 8
  IO.println s!"(b) counts={countsB}  parity={parB}"

  -- (c) record: project by field name
  let outC   := counterAndParity_record (dom := defaultDomain) (Signal.pure true)
  let countsC := (CounterParityOut.count outC).sample 8
  let parC    := (CounterParityOut.parity outC).sample 8
  IO.println s!"(c) counts={countsC}  parity={parC}"

end TutorialExtended.Step2
