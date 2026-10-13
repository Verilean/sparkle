import Tests.AllTests
import Tools.ShippingReaderInstTyShadow

/-! # The compiler's `machInstanceS.inst` against the total one, over the `Tests.AllTests` environment

WRITTEN, NOT BUILT (par/h-1). TARGET-ONLY: not in `Tests.AllTests` (it
imports it). A MEASUREMENT by compiled code; no theorem.

`#reader_instty_shadow` (`Tools/ShippingReaderInstTyShadow.lean`) runs the
compiler's `partial` local `inst` of `machInstanceS`, its text as a `def`
(`instW`) and the total `instT` on

* a grid of 60 calls (types with 0 … 5 leading binders against 0 … 7
  arguments; a binder under `mdata`; a lambda; a type whose instantiation
  exposes more binders);
* the definitions under `Sparkle`, `Tests`, `IP`, `Examples`, `Tools` that
  use a `@[hardware_module]`: the REAL sites (`machInstCallS?`, the reader's
  own test and arguments) and, at every application of a constant, the
  constant's type against the node's arguments.

The sweep never throws (a declaration whose scan raises is logged `NOT
COMPARED`); the command throws only on a MEASURED disagreement.

PREDICTED: `INSTTY GRID: calls=60 old returned=27 disagreements=0 prediction
misses=0`; `INSTTY SWEEP: … disagreements=0 not compared=0`; last line `grid
agree=T sweep agree=T`. The numbers of sites are not predicted (`real sites`
may be 0 if no structure-result hardware module is called in the suite).

What a green run does NOT give: an equation between the two functions (the
old one is opaque to the kernel); anything about `Expr.instantiate1`. -/

#reader_instty_shadow
