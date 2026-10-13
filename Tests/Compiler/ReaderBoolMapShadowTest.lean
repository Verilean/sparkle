import Tests.AllTests
import Tools.ShippingReaderBoolMapShadow

/-! # The compiler's `machBoolMap` against the total one, over the `Tests.AllTests` environment

WRITTEN, NOT BUILT (par/h-1). TARGET-ONLY: not in `Tests.AllTests` (it
imports it). A MEASUREMENT by compiled code; no theorem.

`#reader_boolmap_shadow` (`Tools/ShippingReaderBoolMapShadow.lean`) runs the
compiler's `partial` `machBoolMap` and the total `machBoolMapT` (at the
compiler's own `machLiftScalarN`) on

* a grid of 27 bodies (six bases under 0 … 3 `!`, three more wrappers);
* the lambda bodies of the `Signal.map` / `<$>` nodes over a `BitVec` Signal
  of literal width in the definitions under `Sparkle`, `Tests`, `IP`,
  `Examples`, `Tools`.

The sweep never throws (a declaration whose scan raises is logged `NOT
COMPARED`); the command throws only on a MEASURED disagreement.

PREDICTED: `BOOLMAP GRID: calls=27 old returned=4 disagreements=0 prediction
misses=0`; `BOOLMAP SWEEP: … disagreements=0 not compared=0`; last line
`grid agree=T sweep agree=T`. The numbers of sites are not predicted.

What a green run does NOT give: an equation between the two functions (the
old one is opaque to the kernel); anything about `machLiftScalarN` (the same
compiled function is called on both sides). -/

#reader_boolmap_shadow
