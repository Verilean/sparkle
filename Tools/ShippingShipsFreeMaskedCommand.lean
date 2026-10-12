import Tools.ShippingShipsFreeMasked
import Tools.ShippingShipsFreeCommand
import Tools.ShippingChecksMaskedLeaf

/-! # `#machine_no_ships_masked f n`: the depth endpoint with `designCheck` as its only check (isolated branch `fix/opt-fallback`)

`#machine_no_ships f n` (`Tools/ShippingShipsFreeCommand.lean`) gives the
endpoint without `shipsHierCheck` and `outsCheck`. This command applies
`Tools.ShippingShipsFreeMasked.machine_design_noShips_noBd` to the same
arguments (those of `f.machine_ships_hierNR{n}`) and discharges its THREE
run hypotheses with generated theorems:

* `f.machine_runFacts`, `f.machine_outsG{n}` (as `#machine_no_ships`);
* `f.machine_maskedG : kidsMaskedN D.modules b.body = true` — hypotheses:
  the core run, the post-processing fact, `f`'s reflection and closing, the
  child boundary, each called declaration's reflection. It is
  `Tools.ShippingChecksMasked.core_kidsMaskedN` at `f`'s data, per entry
  `Tools.ShippingChecksMaskedLeaf.leaf_real_kidM` (a leaf child's returned
  module has masked outputs over every run — by the masks guard `masksKept`
  of `mergeChecked`). The per-entry term is that of
  `maskedTheorem` on the branch `fix/merge-guards` (8e24967d), copied,
  without its unused `hierBinds b` binder.

It adds `f.machine_design_noShipsNoMaskedNR{n}`:

    ∀ {contexts, run} hr entry closes, ∃ raw D, … ∧ (designCheck → Bnd → …)

and its `_closed` form. The command REFUSES a produced statement that
mentions `shipsHierCheck`, `outsCheck` or `kidsMaskedN`.

Scope: that of `#machine_no_ships` (leaf machine children with a register,
their closings derived; the parent has a register).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingShipsFreeMaskedCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (scope checkMade discharge factsTheorem outsGTheorem)

/-- **`f.machine_maskedG`, generated**: the children's bound of the depth
endpoints on `f`'s core run's design. -/
def maskedTheorem (f : Name) : CommandElabM Name := do
  let name := f ++ `machine_maskedG
  if (← getEnv).contains name then return name
  let (r, calls, kids) ← scope f
  let mut nd : List (Name × Nat) := []
  for k in kids do
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    nd := nd ++ [(k, cr.nDecl)]
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := nm f "machineData"
  let fq : Term := quote f
  let hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [0:kids.length] do
    let k := kids[j]!
    let kq : Term := quote k
    binders := binders.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
        ($(nm k "machineData")).shape)))
  let nCalls := Syntax.mkNumLit (toString calls.length)
  let nDecl := Syntax.mkNumLit (toString r.nDecl)
  let mut tacM ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let h := hR (kids.idxOf k)
    let kd := Syntax.mkNumLit (toString ((nd.lookup k).getD 0))
    tacM ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingChecksMaskedLeaf.leaf_real_kidM (nDecl := $kd) $(nm k "machineData")
          $(nm k "machine_ok") $(nm k "machine_body") (by decide) (by decide) rfl
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide) $h (fun mc cc => $(nm k "machine_closes") mc _ cc _) hy
      | succ k => $tacM:tactic)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
        {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
        (hcore : Tools.ShippingEntrySoundness.RunsTo
          (Sparkle.Compiler.Elab.synthesizeCombinationalCore $fq [] false)
          mctx mref cctx cref w (raw, D) w1)
        (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
          b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
        (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $fq ($data).shape)
        (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($data).shape)
        (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders* :
        Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
      Tools.ShippingChecksMasked.core_kidsMaskedN (nDecl := $nDecl) $data
        $(nm f "machine_ok") $(nm f "machine_body") (by decide) (by decide) (by decide)
        (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tacM:tactic)
        hB hcore hpost entry closes))
  checkMade name before
  return name

/-- The constants a produced statement must not mention. -/
def forbidden : List Name :=
  [``Tools.ShippingHierPremisesBase.shipsHierCheck, ``Tools.ShippingDesignSVBack.outsCheck,
   ``Tools.ShippingMachineShipsDepth.kidsMaskedN]

/-- `f.machine_design_noShipsNoMaskedNR{n}` from `f.machine_ships_hierNR{n}`'s
arguments and the three run theorems. -/
def generate (f : Name) (n : Nat) (facts outs masked : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noShipsNoMaskedNR{n}"
  if (← getEnv).contains name then return name
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svNR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingShipsFreeMasked.machine_design_noShips_noBd args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry, xs[10] = closes
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← discharge facts p zs[5]! goal)
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← discharge outs p zs[6]! goal)
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd. The telescope is
    -- cut at 6 binders: the goal `Bd b D` is not opened further.
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← discharge masked p zs[5]! goal)
    mkLambdaFVars xs (mkApp pre hMasked)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The endpoint, its closed form, and the log line. -/
def noShipsMasked (f : Name) (n : Nat) : CommandElabM Unit := do
  let facts ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (factsTheorem f)
  let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (outsGTheorem f n)
  let masked ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (maskedTheorem f)
  let name ← liftTermElabM (generate f n facts outs masked)
  let mut made := #[name]
  let cl := f ++ `machine_closes_at
  if (← getEnv).contains cl then
    let nn := Tools.ShippingMachineClosesGen.closedName name
    if ← liftTermElabM (Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn) then
      let some ci := (← getEnv).find? nn | throwError "{nn}: not added"
      for c in forbidden do
        if (ci.type.find? (·.isConstOf c)).isSome then
          throwError "{nn}: REFUSED, the statement still mentions {c}"
      made := made.push nn
  logInfo m!"NOSHIPSMASKED {made}: the depth endpoint without the shipsHierCheck, outsCheck and kidsMaskedN antecedents (run facts by {facts}, output check under the gate by {outs}, children's bound by {masked})"

/-- `#machine_no_ships_masked f n`: an error where it is refused. -/
elab "#machine_no_ships_masked " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noShipsMasked f n.getNat

/-- The same, a refusal LOGGED (`NOSHIPSMASKED REFUSED`) instead of thrown. -/
elab "#machine_no_ships_masked_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noShipsMasked f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOSHIPSMASKED REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingShipsFreeMaskedCommand
