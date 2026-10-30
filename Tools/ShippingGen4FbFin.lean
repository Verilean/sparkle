import Tools.ShippingGen4FbTailInv
import Tools.ShippingGen5ClosingRun
set_option autoImplicit false
-- NOT BUILT (unit FB-7): no Lean build has been run on this file yet. Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §14.1/§15.1 (rev8/rev9).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Two theorems only.

/-! # FB-7: T-FIN for `D ≥ 1` by consuming the ClosingRun `stop_of_run`

`tFin_stop`: `InvAt D w'` for the WHOLE `synthesizeCombinationalCore` run, from `hI`, `hC`, `hr` and `1 ≤ D`
(`dv w = D` comes out of `hI`). `a4_inv_tail_fin`: the K-RUNT extraction together with it, about the same `hr`.
Preservation only (P). Depth 0 is NOT covered. `stop_of_run` is consumed, not re-stated or re-proved. -/

namespace Tools.ShippingGen4FbFin
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildBndCore
open Tools.ShippingMachineOutcomeA Tools.ShippingMachineOutcomeA3 Tools.ShippingMachineOutcomeA4
open Tools.ShippingGen2 Tools.ShippingGen4FbR4 Tools.ShippingGen4FbInv Tools.ShippingGen4FbTailInv

theorem tFin_stop {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {D : Nat} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D) (hC : ChildKeepsInv L P Reach (D + 1)) (hI : InvAt L P Reach D w)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, dsg) w') :
    InvAt L P Reach D w' := by
  have hD : dv w = D := hI.1.1.2.2
  subst hD
  exact Tools.ShippingGen5ClosingRun.stop_of_run L P Reach hA h1 hC hI hr

theorem a4_inv_tail_fin {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h1 : 1 ≤ D)
    (hI : InvAt L P Reach D w) (hC : ChildKeepsInv L P Reach (D + 1))
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape) :
    (A4MachineSideA L.O mctx cctx D declName shape m d w w' ∨
       R4RunInvT L P Reach mctx cctx D declName shape m d w w') ∧ InvAt L P Reach D w' :=
  ⟨a4_inv_tail_machine_or_R4RunInvT L P Reach hA hI hC hr entry, tFin_stop L P Reach hA h1 hC hI hr⟩

end Tools.ShippingGen4FbFin
