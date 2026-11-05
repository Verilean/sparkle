import Tools.ShippingGen5ClosingRun3
import Tools.ShippingGen3HrowGateServed
import Tools.ShippingGen2KeepChild
set_option autoImplicit false
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # `hIH` / `hKI` of the closingRun theorems from the T1 rows (scripts/gen5/HORD_RUN_FREEZE.md §6; ledger row A.P-24)

The run-local closingRun theorems (`Tools.ShippingGen5ClosingRun3`) still take `hIH : IHAt L P Reach (dv w + 1)` and
`hKI : ChildKeepsInv L P Reach (dv w + 1)` (FG A.P-24, merged B.F-1, C.CR-3, C.AC-8). The T1 depth induction `ih_allPF`
gives both at every depth `≥ 1` from `T1Hyp`, `StepStmt` and the proved statements `keepChild_proved`, `servedShips0_run`
(hrow-gate, no `hrow`), `postFacts_of_run` (hrow-gate, `hrows` only) and `limitStmt_proved`. So the binders `hIH` / `hKI`
are replaced by the T1 rows `hT : T1Hyp` (T1L-06..10, with `dec` = T1L-09), `hrows` (T1L-05) and `hStep` (T1L-03).
Whether this removes a FG row is a counting question (the rows are T1 rows, counted in the T1 ledger): freeze §6. -/

namespace Tools.ShippingGen5ClosingRun4
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun Tools.ShippingGen5ClosingRun2
open Tools.ShippingGen5ClosingRun3

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **Both halves of the IH at every depth `≥ 1` from the T1 rows** (`ih_allPF` with the proved statements). -/
theorem ihKI_of_rows (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk) :
    ∀ D, 1 ≤ D → IHAt L P Reach D ∧ ChildKeepsInv L P Reach D :=
  ih_allPF L P Reach DataOk hT hStep (keepChild_proved L P Reach) (servedShips0_run L P Reach DataOk)
    (postFacts_of_run L P Reach DataOk hrows) (limitStmt_proved L)

/-- `closingRun0_of_runR` with `hIH` / `hKI` supplied from the T1 rows. -/
theorem closingRun0_of_runT1 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D :=
  have h := ihKI_of_rows L P Reach DataOk hT hrows hStep 1 (Nat.le_refl 1)
  closingRun0_of_runR L P Reach DataOk (T1Hyp.toND hT) hR hP hs hd0 h.1 h.2 hrun Gen hGen

/-- `closingRun_of_runR` with `hIH` / `hKI` supplied from the T1 rows. -/
theorem closingRun_of_runT1 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D :=
  have h := ihKI_of_rows L P Reach DataOk hT hrows hStep (dv w + 1) (Nat.succ_pos _)
  closingRun_of_runR L P Reach DataOk (T1Hyp.toND hT) hA hR hP hst h.1 h.2 h1 hrun Gen hGen

end Tools.ShippingGen5ClosingRun4

#print axioms Tools.ShippingGen5ClosingRun4.ihKI_of_rows
#print axioms Tools.ShippingGen5ClosingRun4.closingRun0_of_runT1
#print axioms Tools.ShippingGen5ClosingRun4.closingRun_of_runT1
