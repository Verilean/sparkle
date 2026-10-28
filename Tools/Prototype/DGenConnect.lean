import Tools.Prototype.ReaderComposed
import Tools.ShippingMachineEntry

/-! # Unit DGEN: from the generation path's facts for ONE declaration to the conclusion of `machineShapeN_typed_all`

BUILT (unit DGEN): d1 exit 1 (missing opens), d2 exit 0, d6 exit 0 (with `dgen_connect_gen`).  No sorry/axiom/native_decide.

WHAT THE GENERATION PATH ACTUALLY GIVES (`Tools/ShippingMachineCommand.lean`, `readMachine`/`generateCore`):
* `f.machineData : MachineData` is a CLOSED constant (`dataE r`), whose `shape` is the SHIPPED `machineShape?` result read at
  generation time (`readMachine` calls `machineShape? false [] entry senv`, NOT `machineShapeN`);
* `f.machine_ok : f.machineData.ok = true` and `f.machine_body : f.machineData.shape.body = quote …` are `Eq.refl`s the KERNEL checks;
* `MachineDefines mctx mref cctx cref f f.machineData.shape` is NOT generated: it is the `entry` PREMISE of `f.machine_sound` /
  `f.machine_ships` (a statement about the run of the shipped `machineShape?` on the entry constant in the run's environment).
So `d`, `d.ok` and `hbody` come from the generator (PROVED by the kernel per declaration); `MachineDefines` stays a PREMISE; and
`d.shape = sp` for the PROTOTYPE `sp` is NOT given: `MachineDefines` only says the SHIPPED reader returns `d.shape`.

THE EXACT GAP (named, not hidden): `ShippedToProto E senv shape` — whenever `machineShape?` returns `shape` on `(E, senv)`,
`machineShapeN` returns `some (some shape)` there.  This is the shipped↔prototype correspondence for ONE input (OPEN, a PREMISE;
the same family as `TwinCoverAt`).  `dgen_connect` is the composition: it PROVES that `MachineDefines` + `ShippedToProto` at the
two environments the definition reads + the generator's `d.ok`/`hbody` turn A's premises into `d.letsAliasOk` and `LetsClose`.
On this chosen route (shipped `machineShape?` vs prototype `machineShapeN`) the connection is NOT proved without the correspondence
premise `ShippedToProto`; that is a statement about this route, not a claim that it is underivable (integrator wording, par/int-r39). -/
namespace Tools.Prototype.DGenConnect
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingEntrySoundness Tools.Prototype.StartDomOk
open Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.Prototype.ReaderTyped
open Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk Tools.Prototype.ReaderClosed Tools.Prototype.ReaderComposed

/-- PREMISE (OPEN): on the input `(E, senv)` a SHIPPED `machineShape?` answer `shape` is also the PROTOTYPE `machineShapeN` answer
(with the default `allowInsts := true` that `MachineDefines` uses). -/
def ShippedToProto (E : Lean.ConstantInfo) (senv : StructEnv) (shape : MachineShape) : Prop :=
  machineShape? false [] E senv = some shape → machineShapeN false [] E senv true = some (some shape)

/-- PREMISE (ii), NOT a kernel fact: what `readMachine` COMPUTED at generation time was this `d`'s shape — the shipped
`machineShape?` on the entry constant `E` of the declaration in the GENERATION environment (`structEnv envG`) returns `d.shape`.
(i) `d.ok = true` and `hbody` are kernel-checked about the stored constant `d` whatever produced it; (ii) says the shipped reader
returns THAT `d`'s shape.  (i) does not imply (ii); `dgen_connect_gen` takes (ii) explicitly.
`E` and `envG` are ARBITRARY binders here: nothing in this file ties them to the actual entry constant of the generated
declaration or to the actual environment of the generation run (provenance OPEN; integrator wording, par/int-r39). -/
def GenReadsShape (E : Lean.ConstantInfo) (envG : Lean.Environment) (d : MachineData) : Prop :=
  machineShape? false [] E (structEnv envG) = some d.shape

/-- **PROVED (conditional on A's premises, `GenReadsShape`, `ShippedToProto`)**: the CONSUMER at the generation environment, no
run and no `MachineDefines`.  Same `d`, same shape (the prototype answer IS `d.shape`), same environment `envG` in both
premises.  A's conclusion then holds for this `d`. -/
theorem dgen_connect_gen
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees)
    (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {E : Lean.ConstantInfo} {envG : Lean.Environment}
    (d : MachineData) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hgen : GenReadsShape E envG d)
    (hpe : ∀ p : ShapePre, shapePre false [] E (structEnv envG) = some p → LetOk 0 p.e = true)
    (hcorr : ShippedToProto E (structEnv envG) d.shape) :
    machineShapeN false [] E (structEnv envG) true = some (some d.shape) ∧
    d.letsAliasOk = true ∧
    ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
      (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
      Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape := by
  have hN := hcorr hgen
  obtain ⟨p, en, st, v, _, _, _, _, _, _, hall⟩ :=
    machineShapeN_typed_all hroot hlift hinst1 (hsig _) hz (hraw _) (hnode _) hE hpe hN
  obtain ⟨ha, hc⟩ := hall d rfl hok hbody
  exact ⟨hN, ha, hc⟩

/-- **PROVED (conditional on A's premises and `ShippedToProto`).**  Given `d` with `d.ok` and `hbody` (the generator's kernel-checked
facts) and `MachineDefines … d.shape` with the three reads it quantifies over, the entry constant `E` of the run has
`machineShapeN false [] E (structEnv envR') true = some (some d.shape)`, and A's conclusion applies to this very `d`. -/
theorem dgen_connect
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees)
    (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (d : MachineData) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hdef : MachineDefines mctx mref cctx cref declName d.shape)
    {w1 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {w2 w5 : Void IO.RealWorld} {envR : Lean.Environment}
    {w6 w7 : Void IO.RealWorld} {envR' : Lean.Environment} {w8 : Void IO.RealWorld}
    (r1 : RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2)
    (r2 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6)
    (r3 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8)
    (hpe : ∀ p : ShapePre,
      shapePre false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') = some p → LetOk 0 p.e = true)
    (hcorr : ShippedToProto
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
      (structEnv envR') d.shape) :
    machineShapeN false []
      (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
      (structEnv envR') true = some (some d.shape) ∧
    d.letsAliasOk = true ∧
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape := by
  obtain ⟨_, _, hshipped⟩ := hdef w1 ci w2 w5 envR w6 w7 envR' w8 r1 r2 r3
  have hN := hcorr hshipped
  obtain ⟨p, en, st, v, _, _, _, _, _, _, hall⟩ :=
    machineShapeN_typed_all hroot hlift hinst1 (hsig _) hz (hraw _) (hnode _) hE hpe hN
  obtain ⟨ha, hc⟩ := hall d rfl hok hbody
  exact ⟨hN, ha, hc mctx mref cctx cref⟩

#print axioms dgen_connect
#print axioms dgen_connect_gen

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``dgen_connect
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "Eq", "Eq", "MachineDefines", "RunsTo", "RunsTo", "RunsTo", "Eq", "ShippedToProto"])

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``dgen_connect_gen
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "Eq", "Eq", "GenReadsShape", "Eq", "ShippedToProto"])

end Tools.Prototype.DGenConnect
