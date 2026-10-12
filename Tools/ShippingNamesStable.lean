import Tools.ShippingSVBridge
import Sparkle.IR.Machine

/-! # Which names of the machine route are sanitize-stable (G1, `designCheck` gap A)

`Sparkle.Backend.Verilog.sanitizeName s` is `s` when every character of `s`
is alphanumeric, `_` or `$` (`Sparkle.IR.NameHints.charOk`), and a
replacement otherwise. The names of a closed machine are of four kinds:

* ALLOCATED wires (`Sparkle.IR.NameHints.Allocated`: clean, starting with
  `_`): stable — `sanitizeName_of_allocated`;
* the NEXT-VALUE wires `nextName s = "next" ++ s` of a slot `s` (an
  allocated transition input): stable — `sanitizeName_nextName`, in the
  separate file `Tools/ShippingNamesNext.lean` (its proof evaluates the
  characters of a string literal; kept apart so that a failure there does
  not block this file);
* `clk`, `rst`: not needed by `seqCheck` (it does not test a register's
  clock or reset name); not stated;
* the declaration's PORT names — its binders' names and the result's field
  names (`layout.outs`). They come from the source. The compiler's
  `Sparkle.IR.Machine.outNameOk` constrains an output name's FIRST character
  (not `_`), its prefix (not `next`) and excludes `rst` / `clk`; it says
  nothing about the other characters, so it does NOT imply stability (a
  field name with a `'` passes `outNameOk` and is rewritten by the
  sanitizer; `Tests/Compiler/DesignTextTest.lean` evaluates one). For these
  the condition is on the data: `cleanB name = true`, decidable per
  declaration — `sanitizeName_of_cleanB`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNamesStable
open Sparkle.IR.NameHints (Allocated Clean charOk)

/-- The decidable form of `Clean`. -/
def cleanB (s : String) : Bool := s.all charOk

/-- A name of clean characters is sanitize-stable (the data condition on a
declaration's port names). -/
theorem sanitizeName_of_cleanB {s : String} (h : cleanB s = true) :
    Sparkle.Backend.Verilog.sanitizeName s = s := by
  unfold Sparkle.Backend.Verilog.sanitizeName
  exact if_pos h

/-- An allocated name is sanitize-stable. -/
theorem sanitizeName_of_allocated {s : String} (h : Allocated s) :
    Sparkle.Backend.Verilog.sanitizeName s = s :=
  Tools.ShippingSVBridge.sanitizeName_of_clean h.1

end Tools.ShippingNamesStable
