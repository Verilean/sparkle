import Tools.ShippingFGCircuitS2mReach2
set_option autoImplicit false
-- FG circuit pilot S2m (part 3): the steps of the main induction at `JQHR` (core chain, `synthesizeChild` miss/hit, `closeInstsM/GM`, the machine body) and `hftCoreCloses_of_kidsR`. Every step is the S2h theorem at the strengthened bundle `ropsR`; the miss premise is `missR`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §39.

namespace Tools.ShippingFGCircuitS2mReach
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Res)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingGen5Env (ReadsAt readsAt_self)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingFGCircuitS2dKids Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingChildInv Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly Tools.ShippingGateChildComb
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingMixedEntrySoundness
open Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildComposeC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Steps
variable {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
  {w₀ : Void IO.RealWorld} {hdown : AdmDownR O e w₀} {hD : DRowEnvR O e w₀} {hG : DiagEnvR O e w₀}
include hcell hdown hD hG

/-- **The machine body keeps `JQHR`** (the `bodyStepH` of the strengthened bundle; the telescope rows are `hT`) -/
theorem jqhr_bodyStep (hT : TeleR O e w₀) :
    BodyStepH (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) :=
  bodyStepH_of_tele (ropsR O hcell e w₀ hdown hD hG) hT

/-- **`synthesizeChild` keeps `JQHR` (miss and hit), at every depth `D ≥ 1`**: a hit takes the saved reads out of the entry; a miss gets them from `missR` (the invariant itself) and saves them -/
theorem jqhr_childKeeps (hT : TeleR O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀) :
    ∀ D, 1 ≤ D → ChildKeepsH (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) D :=
  childKeepsH_all_of_tele (ropsR O hcell e w₀ hdown hD hG) hT (missR h0 hs)

/-- the child entry as a triple on every outcome: the result is a `RealChildE` carrying its saved reads, and the world is again `JQHR` -/
theorem jqhr_synthesizeChild (hT : TeleR O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀)
    (hA : AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx) {D : Nat} (hDpos : 1 ≤ D) (n : Name) :
    Triple mctx mref cctx cref (JQHR O hcell e w₀ hdown hD hG D) (synthesizeChild n)
      (fun r w => RealChildE (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) n r ∧
        JQHR O hcell e w₀ hdown hD hG D w)
      (EQH (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) D) :=
  synthesizeChild_tripleH' (ropsR O hcell e w₀ hdown hD hG) hA hDpos (missR h0 hs)
    (fun {tenv} hl b ci isInst =>
      jqhr_bodyStep hT (D + 1) (by omega) (jqhr_childKeeps hT h0 hs (D + 1) (by omega))
        mctx cctx hA n tenv b ci isInst)

/-- the one-output closing keeps `JQHR`, whatever it returns -/
theorem jqhr_closeInstsM (hT : TeleR O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀)
    (hA : AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx) {D : Nat} (hDpos : 1 ≤ D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQHR O hcell e w₀ hdown hD hG D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenRealE (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) shape children ∧
      JQHR O hcell e w₀ hdown hD hG D w' :=
  closeInstsM_runH (ropsR O hcell e w₀ hdown hD hG) (jqhr_bodyStep hT) (missR h0 hs) hA hDpos hw hr

/-- the general closing keeps `JQHR`, whatever it returns -/
theorem jqhr_closeInstsGM (hT : TeleR O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀)
    (hA : AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx) {D : Nat} (hDpos : 1 ≤ D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQHR O hcell e w₀ hdown hD hG D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenRealE (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) shape children ∧
      JQHR O hcell e w₀ hdown hD hG D w' :=
  closeInstsGM_runH (ropsR O hcell e w₀ hdown hD hG) (jqhr_bodyStep hT) (missR h0 hs) hA hDpos hw hr

/-- the core entry keeps `JQHR` at every depth, on every outcome (the body premise of the core chain is `jqhr_bodyStep`) -/
theorem jqhr_core (hT : TeleR O e w₀) (h0 : ProfOffW mref cref w₀) (hs : ProfStepR O w₀)
    (hA : AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx) {D : Nat} (hDpos : 1 ≤ D) (c : Name) :
    Triple mctx mref cctx cref (JQHR O hcell e w₀ hdown hD hG D) (synthesizeCombinational c)
      (fun _ => JQHR O hcell e w₀ hdown hD hG D)
      (EQH (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) D) :=
  hentryT_of_bodyH (ropsR O hcell e w₀ hdown hD hG) hA
    (fun {tenv} hl b ci isInst =>
      jqhr_bodyStep hT (D + 1) (by omega) (jqhr_childKeeps hT h0 hs (D + 1) (by omega))
        mctx cctx hA c tenv b ci isInst)

end Steps

end Tools.ShippingFGCircuitS2mReach
