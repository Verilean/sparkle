import Tests.AllTests
import Tools.ShippingReaderMatcherArityShadow

/-! # The compiler's `prodMatcherArity?` against the total one, over the `Tests.AllTests` environment

WRITTEN, NOT BUILT (par/h-1). TARGET-ONLY: not in `Tests.AllTests` (it
imports it). A MEASUREMENT by compiled code; no theorem.

`#reader_prodarity_shadow` (`Tools/ShippingReaderMatcherArityShadow.lean`)
runs the compiler's `partial` `MachRawSurface.prodMatcherArity?`, the total
`prodMatcherArityT` (the compiler's own test `==`) and `prodMatcherArityS`
(a structural test) on

* a grid of 79 synthetic matcher bodies (0 … 6 levels; the canonical body
  and eleven refused variants);
* EVERY constant of the environment;

and compares `headT` / `argsT` with `Expr.getAppFn` / `Expr.getAppArgs` at
every node of the bodies, of the values of the matchers found, and of the
definitions under `Sparkle`, `Tests`, `IP`, `Examples`, `Tools` that use a
pair matcher.

The command throws only on a MEASURED disagreement of the candidate (`old`
against `T`, or the pieces); a difference of the structural test is
reported, not thrown.

PREDICTED: `PRODARITY GRID: calls=79 old returned=7 disagreements=0
structural test differs=0 prediction misses=0 … pieces disagreements=0`;
`PRODARITY SWEEP: … disagreements=0 structural test differs=0 …`;
`PRODARITY PIECES: … disagreements=0 not compared=0`; last line `grid
agree=T sweep agree=T pieces agree=T structural test agree=T`. The numbers of
constants, of matchers and of nodes are not predicted.

What a green run does NOT give: an equation between the two functions (the
old one is opaque to the kernel); anything about `Expr.eqv` beyond the inputs
measured; anything about the other `partial` functions of the reader. -/

#reader_prodarity_shadow
