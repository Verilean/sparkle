import Tools.ShippingChildRunAKids
import Tools.ShippingChildComposeC
-- BUILT (unit G2): g2d exit 0 (earlier g2b, g2c exit 1: missing opens). See REPORT-G2.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Row L6 closed over `BodyStepC` / `htr`: `machine_children_realA_main`

`machine_children_realA'` with `hB : BodyStepC O` and the translator premise `htr` discharged from
`O`, `T : RefLawsATele` alone (ComposeC `bodyStepC_of_tele`, `childKeepsC_all_of_tele`,
`translate_keepsC_of_tele` at `D + 1 ≥ 1`).

Remaining premises (named): `O`, `hA`, `T` (added telescope boundary, not proved), the start world
(`JQ O.quiet D w`, `D = 0 ∨ CacheInvA O (cv w)`), `MachineDefines`, `MachineClosesAtA`
(UNRESOLVED premise: the machine synthesis does not fall back), `shape.insts ≠ []`.
`ChildrenRealA` is a HISTORY of past synthesis results, not freshness or semantic correctness.
Not a runtime-fit proof. -/

namespace Tools.ShippingChildRunAMain
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildRunAKids
open Tools.ShippingChildFresh
open Tools.ShippingChildComposeC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`htr` from `T`**: the restricted translator keeps `JQC O (D + 1)`. -/
theorem htr_of_tele (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) (D : Nat) :
    ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O (D + 1))
      (translateExprToWire tenv e hint top named) :=
  fun tenv e hint top named =>
    translate_keepsC_of_tele O T (D + 1)
      (childKeepsC_all_of_tele O T (D + 1) (by omega)) tenv mctx cctx hA e hint top named

/-- **The children of a real compile, premises `O`, `hA`, `T`, start world, `MachineDefines`,
`MachineClosesAtA` (UNRESOLVED), `shape.insts ≠ []`.** -/
theorem machine_children_realA_main (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (T : RefLawsATele O.quiet mref cref)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenRealA O shape children :=
  machine_children_realA' O (bodyStepC_of_tele O T) hA hr entry (htr_of_tele O hA T D)
    closes hw hc hi

end Tools.ShippingChildRunAMain
