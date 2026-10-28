import Tools.Prototype.DGenConnect
import Tools.Prototype.DGenProv
import Tests.Compiler.ShippingMachineCommandTest

/-! # DGEN: `dgen_connect` instantiated on ONE generated declaration (`toggle`)

BUILT (unit DGEN): d3/d4 exit 1 (own errors: notation, name), d5, d6 exit 0.  TARGET-ONLY (`./.cluster/qbuild.sh build Tests.Compiler.DGenToggleTest`; not in `Tests.AllTests`).
`Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle` is generated there by `#machine_endpoint toggle`, which adds `toggle.machineData`, `toggle.machine_ok`, `toggle.machine_body` (kernel-checked `Eq.refl`s).  The
theorem below supplies exactly those as `d`, `d.ok`, `hbody` of `dgen_connect`; what stays PREMISE is listed by the binder audit:
A's range premises, `MachineDefines` (not generated), the three reads, `hpe`, and `ShippedToProto` (shipped↔prototype, OPEN). -/
namespace Tests.Compiler.DGenToggleTest
open Lean Elab Command Meta Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tools.Prototype.DGenConnect Tools.Prototype.DGenProv

open Sparkle.Tests.Compiler.ShippingMachineCommandTest (toggle)

#check @toggle.machine_ok
#check @toggle.machine_body

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingUnifiedSource Tools.ShippingReaderFuel
open Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness Tools.Prototype.StartDomOk
open Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
open Tools.Prototype.ReaderClosed Tools.Prototype.ReaderComposed Sparkle.Compiler.Elab

/-- `dgen_connect` at `d := toggle.machineData`, `hok := toggle.machine_ok`, `hbody := toggle.machine_body`. -/
theorem toggle_connected
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees) (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hdef : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle toggle.machineData.shape)
    {w1 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {w2 w5 : Void IO.RealWorld} {envR : Lean.Environment}
    {w6 w7 : Void IO.RealWorld} {envR' : Lean.Environment} {w8 : Void IO.RealWorld}
    (r1 : RunsTo (getConstInfo ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle) mctx mref cctx cref w1 ci w2)
    (r2 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6)
    (r3 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8)
    (hpe : ∀ p : ShapePre,
      shapePre false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') = some p → LetOk 0 p.e = true)
    (hcorr : ShippedToProto
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
      (structEnv envR') toggle.machineData.shape) :
    machineShapeN false []
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
      (structEnv envR') true = some (some toggle.machineData.shape) ∧
    toggle.machineData.letsAliasOk = true ∧
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle toggle.machineData.shape :=
  dgen_connect hroot hlift hinst1 hz hE hsig hraw hnode toggle.machineData toggle.machine_ok toggle.machine_body
    hdef r1 r2 r3 hpe hcorr

#print axioms toggle_connected

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``Tests.Compiler.DGenToggleTest.toggle_connected
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "MachineDefines", "RunsTo", "RunsTo", "RunsTo", "Eq", "ShippedToProto"])

/-- The generation-environment consumer on the SAME `d := toggle.machineData`: `hgen` (ii) and `ShippedToProto` are premises.
Only `d` is fixed (toggle's stored data); `E`/`envG` are arbitrary binders, NOT claimed to be toggle's entry constant or the real
generation environment (provenance OPEN; integrator wording, par/int-r39). -/
theorem toggle_connected_gen
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees) (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {E : Lean.ConstantInfo} {envG : Lean.Environment}
    (hgen : GenReadsShape E envG toggle.machineData)
    (hpe : ∀ p : ShapePre, shapePre false [] E (structEnv envG) = some p → LetOk 0 p.e = true)
    (hcorr : ShippedToProto E (structEnv envG) toggle.machineData.shape) :
    machineShapeN false [] E (structEnv envG) true = some (some toggle.machineData.shape) ∧
    toggle.machineData.letsAliasOk = true ∧
    ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
      (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
      Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName toggle.machineData.shape :=
  dgen_connect_gen hroot hlift hinst1 hz hE hsig hraw hnode toggle.machineData toggle.machine_ok toggle.machine_body
    hgen hpe hcorr

#print axioms toggle_connected_gen

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``Tests.Compiler.DGenToggleTest.toggle_connected_gen
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "GenReadsShape", "Eq", "ShippedToProto"])

/-- DGEN2: the provenance instance for `toggle`, with NO free `E`/`envG` binders.  The entry constant and the environment are the results of the
two reads at the start of the run of `readMachine ``toggle` (`GenEntry ci env`, produced by `dgen_connect_prov`).  PREMISES: the run `hrun`
(a hypothesis in the RunsTo style; not produced from the elaboration of `#machine_endpoint toggle` in this change), `StoredFromRead`
(`toggle.machineData.shape = r.shape`: NOT proved in this change), and, for the discovered `ci`/`env`, `hpe` and `ShippedToProto`.
`toggle.machine_ok`/`toggle.machine_body` are the kernel-checked (i) facts. -/
theorem toggle_connected_prov
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees) (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Tools.ShippingMachineCommand.Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (Tools.ShippingMachineCommand.readMachine
      ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle allowGate) mctx mref cctx cref w r w')
    (hstore : StoredFromRead toggle.machineData r) :
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
  dgen_connect_prov hroot hlift hinst1 hz hE hsig hraw hnode hrun toggle.machineData toggle.machine_ok toggle.machine_body hstore

#print axioms toggle_connected_prov

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``Tests.Compiler.DGenToggleTest.toggle_connected_prov
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "RunsTo", "StoredFromRead"])

end Tests.Compiler.DGenToggleTest
