import Tools.Prototype.DGenStored2
import Tests.Compiler.DGenToggleTest

/-! # DGEN4: `toggle_connected_prov` with `StoredFromRead` replaced by its ingredients

TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.DGenToggleStoredTest`; not in `Tests.AllTests`).
Replacement is not discharge: `StoredFromRead` is gone from the binder list, replaced by `ReflExprAgree` (PREMISE: `reflExpr`, a
`partial def`, equals its structural copy), the two success facts of `dataE` (`hb`, `hl`: `reflExpr`/`layoutE` did not fail) and
`ShapeDenotes` (PREMISE (B): the stored `toggle.machineData.shape` is the denotation of the shape expression `dataE` builds).  The run
`hrun` stays a premise. -/
namespace Tests.Compiler.DGenToggleStoredTest
open Lean Elab Command Meta Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tools.Prototype.DGenConnect Tools.Prototype.DGenProv Tools.Prototype.DGenStored2
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingUnifiedSource Tools.ShippingReaderFuel
open Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness Tools.Prototype.StartDomOk
open Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
open Tools.Prototype.ReaderClosed Tools.Prototype.ReaderComposed Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand
open Sparkle.Tests.Compiler.ShippingMachineCommandTest (toggle)

theorem toggle_connected_denotes
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees) (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle allowGate)
      mctx mref cctx cref w r w')
    (hag : ReflExprAgree) {b lay : Lean.Expr}
    (hb : reflExpr r.shape.body = .ok b) (hl : layoutE r.shape.layout = some lay)
    (hK : ShapeDenotes (dataShapeE r.shape b lay) toggle.machineData.shape) :
    ∃ (ci : Lean.ConstantInfo) (env : Lean.Environment) (w1 w2 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle) mctx mref cctx cref w1 ci w2 ∧
      r.entry = GenEntry ci env ∧ GenReadsShape (GenEntry ci env) env toggle.machineData ∧
      ((∀ p : ShapePre, shapePre false [] (GenEntry ci env) (structEnv env) = some p → LetOk 0 p.e = true) →
        ShippedToProto (GenEntry ci env) (structEnv env) toggle.machineData.shape →
        machineShapeN false [] (GenEntry ci env) (structEnv env) true = some (some toggle.machineData.shape) ∧
        toggle.machineData.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName toggle.machineData.shape) :=
  Tests.Compiler.DGenToggleTest.toggle_connected_prov hroot hlift hinst1 hz hE hsig hraw hnode hrun
    (storedFromRead_of_kernelRead hag toggle.machineData r b lay hb hl hK)

#print axioms toggle_connected_denotes

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``Tests.Compiler.DGenToggleStoredTest.toggle_connected_denotes
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "RunsTo", "ReflExprAgree", "Eq", "Eq", "ShapeDenotes"])

end Tests.Compiler.DGenToggleStoredTest
