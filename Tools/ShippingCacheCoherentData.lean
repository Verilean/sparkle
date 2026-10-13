import Tools.ShippingCacheCoherentCert
import Tools.ShippingClosedKinds

/-! # The harness's result facts, from a declaration's machine data

`Tools.ShippingCacheCoherentCert.machine_all` / `entryOk_machine` /
`machine_closes_of_entryOk` take `hout`: on a returning harness run, the
closed machine is named after the declaration and the harness's design has
no module. For a declaration with reflected machine data that IS a built
theorem (`Tools.ShippingClosedKinds.closedBody_kinds_of_run`); this file
only puts it in the shape those theorems ask for. Nothing new is assumed:
the hypotheses are that theorem's (data conditions, decided per
declaration).

WRITTEN, NOT BUILT (par/a-34). -/
namespace Tools.ShippingCacheCoherentData
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingChildInv
open Tools.ShippingCallsGate

/-- `hout` of `machine_all`, for the entry's logger `profLogIO b`. -/
theorem hout_of_data {declName : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) (b : Bool) :
    ∀ (t t' : Sparkle.IR.AST.Module) (d₀ : Design),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName
        d.shape.binders d.shape.body) (t, d₀) →
      closeLets d.shape.layout.lets t = some t' →
      (closeMachine d.shape.layout t').name = Sparkle.IR.ModuleName.ofDecl declName ∧
        d₀.modules = [] :=
  fun _ _ _ run hcl =>
    (Tools.ShippingClosedKinds.closedBody_kinds_of_run d ok hbody hC hslots hdomB run hcl).2

end Tools.ShippingCacheCoherentData
