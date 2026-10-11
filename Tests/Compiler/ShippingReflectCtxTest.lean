import Tests.Compiler.ShippingCloseInstsCheckTest
import Tools.ShippingReflectCtx
import Tools.ShippingCloseLetsSplit
import Tools.ShippingCloseLetsRun
import Tools.ShippingSpineOrder
import Tools.ShippingClosedOrder

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
      ``Tools.ShippingCloseLetsSplit.Spine.append,
      ``Tools.ShippingUnifiedSpine.fuel_spine, ``Tools.ShippingUnifiedSpine.translateExprToWire_spine,
      ``Tools.ShippingUnifiedSpine.Spec.cached, ``Tools.ShippingUnifiedSpine.concat_spec,
      ``Tools.ShippingHarnessSpine.harness_spine_at, ``Tools.ShippingCloseLetsRun.transition_spine,
      ``Tools.ShippingCloseLetsRun.concatParts?_of_mem, ``Tools.ShippingCloseLetsRun.spine_of_packLets,
      ``Tools.ShippingCloseLetsRun.wireWidth_of_decl, ``Tools.ShippingCloseLetsRun.link_not_out,
      ``Tools.ShippingSpineOrder.spine_links, ``Tools.ShippingClosedOrder.closed_acyclic,
      ``Tools.ShippingClosedOrder.acyclic_insert] do
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

/-! `transition_spine` is about EVERY run of the harness: its statement has no
premise about the returned module beside its being the run's (no `closeLets`,
no `Spine`, no record invariant assumed). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let ty ← Lean.Meta.inferType (Lean.mkConst ``Tools.ShippingCloseLetsRun.transition_spine)
  Lean.Meta.forallTelescope ty fun xs concl => do
    for x in xs do
      let t ← Lean.Meta.inferType x
      for c in [``Sparkle.IR.Machine.closeLets, ``Tools.ShippingCloseLetsSplit.Spine,
          ``Tools.ShippingUnifiedSpine.RecQ, ``Tools.ShippingUnifiedSpine.SpineQ,
          ``Sparkle.IR.Machine.letOperands, ``Tools.ShippingMachineEntry.MachineCloses] do
        if (t.find? (·.isConstOf c)).isSome then throwError "transition_spine assumes {c}"
    unless (concl.find? (·.isConstOf ``Tools.ShippingCloseLetsRun.SpineW)).isSome &&
        (concl.find? (·.isConstOf ``Sparkle.IR.Reorder.writesOf)).isSome do
      throwError "transition_spine does not conclude the spine with widths and the undriven ports"
  Lean.logInfo m!"TRANSITION SPINE: closeLets' conditions (1) final assign, (2) concatenation spine, (3) operand wires declared at the fields' widths and not out, (4) input ports undriven, (5) core not out hold of every harness run on a packed machine body (no spine / closeLets / record premise); condition (6), the closed body's dependency order, is derived separately (closed_acyclic, transition_closes; ShippingMachineClosesTest)"

/-! Let-only sources without calls — the shapes `machineCloses_noCalls_iff`
is about (`caller` etc. above have calls). `reflSharedLet` translates the
same subexpression in two `let` fields, so the second goes through a
validated-cache hit. `reflAliasLet` writes a `let` that is another `let`'s
variable: the shape reader keeps ONE hardware `let` for it. -/
open Sparkle.Core.Domain Sparkle.Core.Signal in
/-- A `let` that is another `let`'s variable. -/
def reflAliasLet (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := rs + x
    let b := a
    r <~ a + b
    return rs

open Sparkle.Core.Domain Sparkle.Core.Signal in
/-- The same subexpression in two `let` fields (a validated-cache hit). -/
def reflSharedLet (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let a := (rs + x) + x
    let b := (rs + x) + rs
    r <~ a + b
    return rs

run_cmd Lean.Elab.Command.liftTermElabM do
  let translate : TranslateFn := fun e h t nm => translateExprToWire e h t nm
  for n in [``reflAliasLet, ``reflSharedLet] do
    try
      let r ← Tools.ShippingMachineCommand.readMachine n
      let k := r.shape.layout.lets
      let (t, _) ← synthesizeMixedCertified translate (fun _ => pure ()) n r.shape.binders r.shape.body
      let ok := (Sparkle.IR.Machine.closeLets k t).isSome
      unless r.shape.insts.isEmpty do throwError "{n}: has calls"
      unless ok do throwError "{n}: closeLets refuses this run's transition"
      Lean.logInfo m!"LET-ONLY, NO CALL (checker on this run, not a derivation): {n} lets={k} statements={t.body.length} closeLets accepts"
    catch e => throwError "{n}: {e.toMessageData}"

/-! What the REAL `closeLets` does when a `let`'s operand is another `let`'s
port, on hand-built transition modules (the shape reader does not produce
these from the sources tried — it resolves `let y := x` to `x`'s definition —
so they are built directly):

* `let0 := x` (an input), `let1 := let0`: both aliases go to the front, in
  order — ACCEPTED. `closed_acyclic` covers it (an operand may be an EARLIER
  front alias' port).
* `let0 := x + x` (driven), `let1 := let0`: `let1`'s alias goes to the front
  and reads `let0`'s port, driven only after `x + x` — REFUSED. The entry then
  takes the legacy fallback; `MachineCloses` is false of such a shape. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let p (n : String) (w : Nat) : Sparkle.IR.AST.Port := { name := n, ty := .bitVector w }
  let mk (body : List Sparkle.IR.AST.Stmt) (wires : List Sparkle.IR.AST.Port) : Sparkle.IR.AST.Module :=
    { name := "t", inputs := [p "x" 8, p "p0" 8, p "p1" 8], outputs := [p "out" 24],
      wires := wires, body := body }
  let core : Sparkle.IR.AST.Stmt := .assign "core" (.op .add [.ref "p0", .ref "p1"])
  let b1 : Sparkle.IR.AST.Stmt := .assign "b1" (.concat [.ref "p0", .ref "core"])
  let base := [p "x" 8, p "p0" 8, p "p1" 8, p "core" 8, p "b1" 16, p "w" 24]
  -- (i) let0 := x, let1 := let0
  let t1 := mk [core, b1, .assign "w" (.concat [.ref "x", .ref "b1"]), .assign "out" (.ref "w")] base
  unless (Sparkle.IR.Machine.closeLets 2 t1).isSome do
    throwError "closeLets refuses `let0 := x; let1 := let0`"
  -- (ii) let0 := x + x, let1 := let0
  let t2 := mk [.assign "a0" (.op .add [.ref "x", .ref "x"]), core, b1,
    .assign "w" (.concat [.ref "a0", .ref "b1"]), .assign "out" (.ref "w")] (p "a0" 8 :: base)
  if (Sparkle.IR.Machine.closeLets 2 t2).isSome then
    throwError "closeLets accepts `let0 := x + x; let1 := let0`"
  Lean.logInfo m!"CLOSELETS ON LET-OF-LET (real function, hand-built modules): let0 := input, let1 := let0 accepted; let0 := x + x, let1 := let0 refused"
