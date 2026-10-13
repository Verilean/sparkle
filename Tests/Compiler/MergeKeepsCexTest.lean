import Tests.Compiler.LeafEntryCexProbe
import Tools.ShippingMergeKeepsBridge
import Tools.ShippingMergeKeepsCheck

/-! # `mergeCex` is outside `LastNonAssign` — kernel-level (round par/a-30)

TARGET-ONLY (not for `Tests.AllTests`): the two `decide`s below make the
kernel evaluate `lastNonAssignB` on a hand-written body, which compares
`String`s; whether `decide` reduces that in this toolchain was not tried.
`Tests/Compiler/MergeKeepsCntTest.lean` asserts the same two values by
compiled evaluation and does not depend on this file.

* `mergeCex_outside`: `¬ LastNonAssign mergeCex.body` — the probe module of
  `docs/parallel/A-leaf-entry-2.md` §1 does not satisfy the hypothesis of
  `Tools.ShippingMergeKeeps.mergeChecked_keeps`;
* `okReg_inside`, `okReg_kept`: a module that does (`a = 5; register n <= a`),
  and the theorem at it — a statement, no evaluation of the merge.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.MergeKeepsCexTest
open Sparkle.IR.AST

theorem mergeCex_outside :
    ¬ Tools.ShippingMergeKeeps.LastNonAssign Tests.Compiler.LeafEntryCexProbe.mergeCex.body :=
  Tools.ShippingMergeKeeps.not_lastNonAssign (by decide)

/-- A register read by nothing, after the assignment it reads. -/
def okReg : Module :=
  { name := "okReg"
    inputs := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
    outputs := []
    wires := [{ name := "a", ty := .bitVector 8 }, { name := "n", ty := .bitVector 8 }]
    body :=
      [ .assign "a" (.const 5 8)
      , .register "n" "clk" ("rst", .synchronous) (.ref "a") 0 ] }

theorem okReg_inside : Tools.ShippingMergeKeeps.LastNonAssign okReg.body :=
  Tools.ShippingMergeKeeps.lastNonAssignB_sound _ (by decide)

theorem okReg_kept :
    (Sparkle.IR.RefineCheck.mergeChecked okReg).body.all Sparkle.IR.RegDedup.isAssign = false :=
  Tools.ShippingMergeKeeps.mergeChecked_keeps okReg_inside

end Tests.Compiler.MergeKeepsCexTest
