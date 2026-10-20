import Tests.AllTests
import Tools.ShippingReaderProjChainShadow

/-! # The OLD `projChain` against the compiler's and the total ones, over the `Tests.AllTests` environment

TARGET-ONLY: not in `Tests.AllTests` (it imports it). A MEASUREMENT by
compiled code; no theorem. First version BUILT and run on poc (par/f-1);
this version (branch `fix/projchain-total`) WRITTEN, NOT BUILT. It
elaborates unchanged before and after the switch-over.

## Which is which

* `old` = `Tools.ShippingReaderProjChainShadow.projChainOld`: a verbatim copy
  of the compiler's `partial` `projChain` as it was BEFORE the switch (base
  `80745d94`), compiled in the shadow file. The compiler does not use it.
* `compiler` = `Sparkle.Compiler.MachRawSurface.projChain`: the function the
  compiler runs on this tree. Before the switch: the original `partial`
  function. After: the total definition.
* `W` = `projChainW`: after the switch an abbreviation of `compiler`.
* `T` = `projChainT`: the structural definition.

The first log line, `PROJCHAIN WHICH: …`, says the same and reports
`compiler partial=T` or `=F` as read from the environment (the constant
`projChain.tail` exists only for the old `partial def`).

`#reader_projchain_shadow` (`Tools/ShippingReaderProjChainShadow.lean`) runs
the four on

* the grid of every `(length, j, last)` with length `0 … 8`, `j` `0 … 10`;
* every REAL call site of the environment: the pair-destructuring matcher
  nodes of every definition under `Sparkle`, `Tests`, `IP`, `Examples`,
  `Tools`, with the arguments `rawNode` passes, and against the `let` values
  of the real `rawNode`'s result.

The sweep never throws (a declaration whose scan raises is logged `NOT
COMPARED`); the command throws only on a MEASURED disagreement. Each
operation logs a `PROJCHAIN START …` line on standard error first.

## What a run means

* On the tree BEFORE the switch (`compiler partial=T`): `old==compiler` — the
  copy kept for the measurement behaves as the original it was copied from.
* On the tree AFTER the switch (`compiler partial=F`): `old==compiler` — the
  function the compiler now runs returns what the old one returns, on the
  grid and at every real call site of this environment.

PREDICTED on both trees: `PROJCHAIN GRID: calls=198 old returned=65
disagreements=0`; `PROJCHAIN SWEEP: … disagreements=0 not compared=0`; last
line `grid agree=T sweep agree=T`. MEASURED with the first version on poc:
1416 sites, 3521 calls (the counts move when definitions are added).

What a green run does NOT give: an equation between the old function and
anything (it is opaque to the kernel); that `old` is the object code the
compiler ran before the switch (it is the same source compiled again);
anything about inputs outside the grid other than through "the function
never inspects an expression" (READ, not proved); anything about the other
`partial` functions of the reader. -/

#reader_projchain_shadow
