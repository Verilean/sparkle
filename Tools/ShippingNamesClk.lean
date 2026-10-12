import Tools.ShippingNamesStable

/-! # `clk` and `rst` are sanitize-stable (G1, `designCheck` text conjuncts)

The clock and the reset are INPUT ports of a closed machine. The emitter's
width map looks a name up by the SANITIZED names of wires ++ inputs ++
outputs, so to know that an output port's entry is the output's own, the
sanitized names of the two fixed inputs must be known: they are the names
themselves. Kept in a file of its own: the proofs evaluate the characters of
string literals (as `Tools/ShippingNamesNext.lean`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNamesClk
open Sparkle.IR.NameHints (Clean charOk)

theorem clean_clk : Clean "clk" := by
  intro c hc
  have h2 : c = 'c' ∨ c = 'l' ∨ c = 'k' := by simpa using hc
  rcases h2 with e | e | e <;> rw [e] <;> decide

theorem clean_rst : Clean "rst" := by
  intro c hc
  have h2 : c = 'r' ∨ c = 's' ∨ c = 't' := by simpa using hc
  rcases h2 with e | e | e <;> rw [e] <;> decide

theorem sanitizeName_clk : Sparkle.Backend.Verilog.sanitizeName "clk" = "clk" :=
  Tools.ShippingSVBridge.sanitizeName_of_clean clean_clk

theorem sanitizeName_rst : Sparkle.Backend.Verilog.sanitizeName "rst" = "rst" :=
  Tools.ShippingSVBridge.sanitizeName_of_clean clean_rst

end Tools.ShippingNamesClk
