import Tests.AllTests
import Tools.ShippingReaderMatcherArityOldShadow

/-! # The OLD `prodMatcherArity?` (a verbatim copy) against the compiler's, over the `Tests.AllTests` environment

WRITTEN, NOT BUILT (branch `fix/reader-p1`; `docs/parallel/P-reader-2.md`).
TARGET-ONLY: not in `Tests.AllTests` (it imports it). A MEASUREMENT by
compiled code; no theorem. It elaborates on poc and on the switched tree.

Which is which (`PRODOLD WHICH`): `old` = `prodMatcherArityOld`, the text of
`Sparkle/Compiler/MachRawSurface.lean` 23–52 at c3176ef1 compiled here
(`partial`); `compiler` = `Sparkle.Compiler.MachRawSurface.prodMatcherArity?`
of the tree being built (`partial` on poc, total after the switch-over);
`T` = `prodMatcherArityT` (total, the compiler's `==`). Every comparison is
against `old`; a difference throws.

PREDICTED on both trees: `PRODOLD GRID: calls=79 old returned=7
old!=compiler=0 old!=T=0`; `PRODOLD SWEEP: … old!=compiler=0 old!=T=0`;
`PRODOLD: grid agree=T sweep agree=T`. The number of constants is not
predicted. -/

#reader_prodarity_old_shadow
