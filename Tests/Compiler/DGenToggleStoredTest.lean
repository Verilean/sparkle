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

/-! ## Instance probe on `toggle` (meta-level evidence, NOT a proof)

Runs `readMachine` on `toggle`, and checks (1) the declared value of `toggle.machineData` is `dataE r` (as an `Expr`), (2) `evShape` of its
shape argument reads back to the fields of `r.shape`.  This tests the evaluator on the real declared term; it does not discharge `hK`. -/

open Sparkle.IR.Machine in
run_meta do
  let r ← readMachine ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle false
  let ci ← getConstInfo ``Sparkle.Tests.Compiler.ShippingMachineCommandTest.toggle.machineData
  let some v := ci.value? | throwError "toggle.machineData has no value"
  let e ← dataE r
  unless v == e do throwError "PROBE FAILED: the declared value of toggle.machineData is not `dataE r`"
  let args := e.getAppArgs
  let some sh := evShape args[0]! | throwError "PROBE FAILED: evShape does not read the shape argument"
  let s := r.shape
  unless sh.binders == s.binders && sh.body == s.body && sh.layout.slots == s.layout.slots && sh.layout.outs == s.layout.outs &&
      sh.layout.lets == s.layout.lets && sh.runs == s.runs && sh.insts == s.insts && sh.loops == s.loops &&
      sh.instFields == s.instFields && sh.instOrigins == s.instOrigins do
    throwError "PROBE FAILED: evShape of the declared shape differs from r.shape"
  logInfo m!"instance probe toggle: declared value = dataE r, evShape reads back r.shape ({s.binders.length} binders, {s.runs.length} runs, {s.layout.slots.length} slots)"

/-! ## Probe for review item (c): opaque constants reachable from the shape function

A kernel `Eq.refl` for `machineShapeN … = some (some d.shape)` can only go through if the kernel can unfold everything it meets.
`partial def`s are opaque to the kernel.  THIS probe lists the opaque constants (and `implemented_by`-style opaques) that occur in the
TEXT of the definitions reachable from `machineShapeN`.  Whether the kernel's reduction on `toggle` actually reaches one is NOT decided
by this probe; it shows that the question is live. -/

open Lean in
partial def reachOpaque (env : Environment) (todo : List Name) (seen : NameSet) (acc : Array Name) : NameSet × Array Name :=
  match todo with
  | [] => (seen, acc)
  | n :: rest =>
    if seen.contains n then reachOpaque env rest seen acc
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        reachOpaque env (d.value.getUsedConstants.toList ++ rest) seen acc
      | some (.opaqueInfo d) =>
        reachOpaque env (d.value.getUsedConstants.toList ++ rest) seen (acc.push n)
      | _ => reachOpaque env rest seen acc

run_meta do
  let env ← getEnv
  let (seen, ops) := reachOpaque env [``machineShapeN] {} #[]
  let relevant := ops.filter fun n => !(`_private).isPrefixOf n
  logInfo m!"PROBE (c): {seen.size} constants reachable from machineShapeN's definitions; {ops.size} opaque ({relevant.size} non-private), first: {relevant.toList.take 25}"

partial def pf (n : Nat) : Nat := if n = 0 then 0 else pf (n - 1)

run_meta do
  let env ← getEnv
  let k := Lean.Kernel.isDefEq env {} (Lean.mkApp (Lean.mkConst ``pf) (Lean.mkRawNatLit 0)) (Lean.mkRawNatLit 0)
  logInfo m!"PROBE (c): kernel isDefEq (pf 0) 0 for a `partial def pf` = {repr (k.toOption)} (the kernel does not unfold a partial def)"

end Tests.Compiler.DGenToggleStoredTest
