import Tests.Compiler.ShippingCloseInstsCheckTest
import Tools.ShippingReflectCtx
import Tools.ShippingCloseLetsSplit

/-! The reflection premises against the contexts a child is synthesised in.

* `MachineDefines` / `EntryDefines` asked in every context follow from the
  same in one (`MachineDefines.ctx`, `EntryDefines.ctx`): checked here to be
  theorems of that shape with standard axioms only.
* `MachineCloses` is about the machine synthesis' own runs and is NOT
  transferred. On real declarations, the run it speaks of is made twice —
  in the command's contexts and in contexts of the kind a legacy handler
  creates (a local declaration added, transparency `all`) — and must return
  the same closed module both times. A regression of one real instance of
  the premise in two reachable contexts; it is not a proof of the premise. -/
open Lean Sparkle.Compiler.Elab
open Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingReflectCtx.MachineDefines.ctx, ``Tools.ShippingReflectCtx.EntryDefines.ctx,
      ``Tools.ShippingReflectCtx.getConstInfo_ctx, ``Tools.ShippingReflectCtx.getEnv_ctx,
      ``Tools.ShippingCloseLetsSplit.closeLets_isSome_iff,
      ``Tools.ShippingCloseLetsSplit.machineCloses_noCalls_iff,
      ``Tools.ShippingCloseLetsSplit.letOperands_isSome_iff, ``Tools.ShippingCloseLetsSplit.Spine.emit,
      ``Tools.ShippingCloseLetsSplit.Spine.append] do
    let ax ← Lean.collectAxioms n
    for a in ax do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "{n} depends on {a}"
  -- the transfer is between ARBITRARY contexts over the same state refs
  let t ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingReflectCtx.MachineDefines.ctx)
  let n := t.getForallBinderNames
  unless n.contains `mctx && n.contains `mctx' && n.contains `cctx && n.contains `cctx' do
    throwError "MachineDefines.ctx: not a transfer between two pairs of contexts"
  Lean.logInfo m!"REFLECTION / CONTEXTS: MachineDefines and EntryDefines transfer between any two pairs of Meta/Core contexts over the same state refs (standard axioms); MachineCloses is not transferred"

run_cmd Lean.Elab.Command.liftTermElabM do
  let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
  let mut report := #[]
  for n in [``ctr1, ``mid1, ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller, ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested] do
    let r ← Tools.ShippingMachineCommand.readMachine n
    let here ← synthesizeMachineCertified translate (fun _ => pure ()) n r.shape
    let there ← Lean.Meta.withLocalDeclD `handlerLocal (Lean.mkConst ``Nat) fun _ =>
      Lean.Meta.withTransparency .all <|
        synthesizeMachineCertified translate (fun _ => pure ()) n r.shape
    match here, there with
    | some (m1, d1), some (m2, d2) =>
      unless toString (repr m1) == toString (repr m2) do
        throwError "{n}: the closed module differs between the two contexts"
      unless d1.modules.length == d2.modules.length do
        throwError "{n}: the design differs between the two contexts"
      report := report.push s!"{n} (lets={r.shape.layout.lets}, calls={r.shape.insts.length}, {m1.body.length} statements)"
    | none, none => report := report.push s!"{n}: machine route refuses in both contexts (MachineCloses is false of it in both)"
    | _, _ => throwError "{n}: the machine synthesis closes in one context and not in the other"
  Lean.logInfo m!"MACHINE CLOSES IN TWO CONTEXTS: {report}"

/-! The six conditions of `closeLets_isSome_iff`, evaluated on the transition
modules of real declarations with `let`s: which hold, per declaration. (The
transition module is the harness' output in this run; this is the checker on
real artifacts, not a derivation.) -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
  let mut report := #[]
  for n in [``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller,
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
      ``Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested] do
    let r ← Tools.ShippingMachineCommand.readMachine n
    let k := r.shape.layout.lets
    let (t, _) ← synthesizeMixedCertified translate (fun _ => pure ()) n r.shape.binders r.shape.body
    let some w := Sparkle.IR.Machine.packedWire? t.body | throwError "{n}: (1) no final assign out"
    let some (aliases, core) := Sparkle.IR.Machine.letOperands t.body (t.inputs.drop (t.inputs.length - k)) w
      | throwError "{n}: (2) no concatenation chain"
    let c3 := aliases.all fun pa => Sparkle.IR.Machine.wireWidth t.wires pa.2 == pa.1.ty.bitWidth &&
      decide (0 < pa.1.ty.bitWidth) && pa.1.name != "out" && pa.2 != "out"
    let c4 := aliases.all fun pa => !(Sparkle.IR.Reorder.writesOf t.body).contains pa.1.name
    let c5 := core != "out"
    let c6 := Sparkle.IR.OptCheck.assignmentOrderCheck (Tools.ShippingCloseLetsSplit.closedBody t aliases core)
    unless c3 && c4 && c5 && c6 do throwError "{n}: conditions 3–6 = {c3} {c4} {c5} {c6}"
    unless (Sparkle.IR.Machine.closeLets k t).isSome do throwError "{n}: closeLets refuses"
    report := report.push s!"{n.getString!}: lets={k}, aliases={aliases.length}, {t.body.length} statements"
  Lean.logInfo m!"CLOSELETS CONDITIONS ON REAL TRANSITIONS (all six hold): {report}"
