import Tests.AllTests
import Tools.ShippingReaderProjChainShadow

/-! # The compiler's `projChain` against the total one, over the `Tests.AllTests` environment

WRITTEN, NOT BUILT (par/f-1). TARGET-ONLY: not in `Tests.AllTests` (it
imports it). A MEASUREMENT by compiled code; no theorem.

`#reader_projchain_shadow` (`Tools/ShippingReaderProjChainShadow.lean`) runs
the compiler's `partial` `MachRawSurface.projChain`, its transcription over
the total `tail` (`projChainW`) and the structural `projChainT` on

* the grid of every `(length, j, last)` with length `0 … 8`, `j` `0 … 10`;
* every REAL call site of the environment: the pair-destructuring matcher
  nodes of every definition under `Sparkle`, `Tests`, `IP`, `Examples`,
  `Tools`, with the arguments `rawNode` passes, and against the `let` values
  of the real `rawNode`'s result.

The sweep never throws (a declaration whose scan raises is logged `NOT
COMPARED`); the command throws only on a MEASURED disagreement. Each
operation logs a `PROJCHAIN START …` line on standard error first.

PREDICTED: `PROJCHAIN GRID: calls=198 old returned=65 disagreements=0`;
`PROJCHAIN SWEEP: … disagreements=0 not compared=0`, with `sites` at least
the six `regs`-destructuring declarations of `Tests/RunCircuitHTest.lean`
(the exact number is not predicted); last line `grid agree=T sweep agree=T`.

What a green run does NOT give: an equation between the two functions (the
old one is opaque to the kernel); anything about inputs outside the grid
other than through "the function never inspects an expression" (READ, not
proved); anything about the other `partial` functions of the reader. -/

#reader_projchain_shadow
