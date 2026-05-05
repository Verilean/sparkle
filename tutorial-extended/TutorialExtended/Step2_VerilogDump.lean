/-
  Tutorial Step 2 helper: print the Verilog wire names for the
  three variants in Step2_MultipleOutputs and confirm the
  let-named / record approaches yield meaningful wire names.

  This file uses the `#synthesizeVerilog` command to produce
  Verilog at compile time. Look at the build output (or the
  `#print` blocks below) to see the actual generated wires.
-/

import Sparkle
import Sparkle.Compiler.Elab
import TutorialExtended.Step2_MultipleOutputs

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open TutorialExtended.Step2

-- Variant (b) — let-named outputs.
-- Build output should show `_gen_countOut` and `_gen_parityOut` as
-- module-level wires.
#synthesizeVerilog counterAndParity_letNamed

-- Variant (c) — declare_signal_state record output.
-- Build output should ALSO show `_gen_countOut` and `_gen_parityOut`,
-- because the let-binding gets the wire-name hint regardless of
-- whether the bundle is `bundle2` or `bundleAll!` from a record
-- type. The difference is at the *Lean type* level: callers see
-- a named record instead of an anonymous tuple.
#synthesizeVerilog counterAndParity_record
