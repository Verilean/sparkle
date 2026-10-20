import Tools.ShippingNoKids
import Tools.ShippingNoDesignCommand
import Tools.ShippingKidsPassLeaf

/-! # `#machine_no_kids f n`: the depth endpoint without the children's check (round par/a-1)

`#machine_no_design f n` (`Tools/ShippingNoDesignCommand.lean`) gives the
endpoint whose check antecedents are `portsMatchB` and `kidsPass`. This
command applies `Tools.ShippingNoKids.machine_design_noKids` to the same
arguments (those of `f.machine_ships_hierNR{n}`) and discharges its four run
hypotheses with generated theorems:

* `f.machine_runFacts`, `f.machine_outsG{n}`, `f.machine_maskedG` (the
  existing generators are called);
* `f.machine_designK{n}`:

      hcore hpost entry closes hB (children's reflections)
      (hports : portsMatchB (childMap D.modules) (checkedOptimize b) = true) :
      designCheck (childMap D.modules) n (checkedOptimize b) = true

  — `f.machine_designG{n}` (`#machine_no_design`'s) with its `hkids`
  supplied by `Tools.ShippingKidsPassLeaf.core_kidsPass_leaf` at `f`'s data,
  whose per-child fact `hkidK` is
  `Tools.ShippingLeafTyped.leaf_real_kidK_reg` at each called declaration:
  a leaf child with a register passes `kidCheck` at every depth, its checked
  merge being the module itself or passing the print guard
  (`Sparkle.IR.RefineCheck.mergeChecked_print`). The child's two data
  conditions on its output ports are DECIDED (`hon` through the
  character-wise form and `sanitizeName_of_clean`, `hoty` directly).

It adds `f.machine_design_noKidsNR{n}`:

    ∀ {contexts, run} hr entry closes, ∃ raw D, … ∧ (portsMatchB … → Bnd → …)

and its `_closed` form. The command REFUSES a produced statement that
mentions `kidsPass`, `designCheck`, `shipsHierCheck`, `outsCheck` or
`kidsMaskedN`.

Scope: that of `#machine_no_design` (leaf machine children with a register,
their closings derived; the parent has a register; the parent's output port
names character-wise clean and its output types scalar) and the same two
conditions on every child's output ports (otherwise the generated
`f.machine_designK{n}` fails at `decide`, reported as an error).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNoKidsCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (scope checkMade factsTheorem outsGTheorem discharge)
open Tools.ShippingShipsFreeMaskedCommand (maskedTheorem)
open Tools.ShippingNoDesignCommand (dischargeUpTo designTheorem)

/-- **`f.machine_designK{n}`, generated**: `designCheck` of the shipped
module of `f`'s core run at depth `n` from the connection widths alone
(`design` is `f.machine_designG{n}`; its children's check by
`core_kidsPass_leaf` and, per called declaration, `leaf_real_kidK_reg`). -/
def kidsTheorem (f : Name) (n : Nat) (design : Name) : CommandElabM Name := do
  let name := f ++ Name.mkSimple s!"machine_designK{n}"
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
  let mut hRs : Array Term := #[]
  for j in [0:kids.length] do
    let k := kids[j]!
    let kq : Term := quote k
    binders := binders.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
        ($(nm k "machineData")).shape)))
    hRs := hRs.push ⟨(hR j).raw⟩
  let nCalls := Syntax.mkNumLit (toString calls.length)
  let nDecl := Syntax.mkNumLit (toString r.nDecl)
  let nLit := Syntax.mkNumLit (toString n)
  let mut tacK ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let h := hR (kids.idxOf k)
    let kd := Syntax.mkNumLit (toString ((nd.lookup k).getD 0))
    tacK ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingLeafTyped.leaf_real_kidK_reg (nDecl := $kd) $(nm k "machineData")
          $(nm k "machine_ok") $(nm k "machine_body") (by decide) (by decide) rfl
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide) $h (fun mc cc => $(nm k "machine_closes") mc _ cc _)
          (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
            ((show ∀ o ∈ ($(nm k "machineData")).shape.layout.outs, ∀ c ∈ o.name.toList,
                Sparkle.IR.NameHints.charOk c = true from by
              first | decide | decide +kernel) o ho))
          (by decide) hy
      | succ k => $tacK:tactic)
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
        (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders*
        (hports : Tools.ShippingDesignSV.portsMatchB
          (Tools.ShippingMachineLinked.childMap D.modules)
          (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
        Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
          $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
      $(mkIdent (`_root_ ++ design)) hcore hpost entry closes hB $hRs* hports
        (Tools.ShippingKidsPassLeaf.core_kidsPass_leaf (nDecl := $nDecl) $data
          $(nm f "machine_ok") $(nm f "machine_body") (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          (by
            intro k hk y hy
            have hk' : k < $nCalls := hk
            $tacK:tactic)
          hB hcore hpost entry closes $nLit)))
  checkMade name before
  return name

/-- The constants a produced statement must not mention. -/
def forbidden : List Name :=
  Tools.ShippingNoDesignCommand.forbidden ++ [``Tools.ShippingDesignSV.kidsPass]

/-- `f.machine_design_noKidsNR{n}` from `f.machine_ships_hierNR{n}`'s
arguments and the four run theorems (`Tools.ShippingNoDesignCommand.generate`,
copied, with the head `machine_design_noKids`). -/
def generate (f : Name) (n : Nat) (facts outs masked design : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noKidsNR{n}"
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
      (← mkAppOptM ``Tools.ShippingNoKids.machine_design_noKids args)
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
    let pre := mkApp pre hMasked
    -- `designCheck` from the connection widths: zs = raw D w1 hcore hpost hBnd.
    -- The telescope is cut at 6 binders: the goal is
    -- `portsMatchB … → designCheck …`, which `design` proves once its
    -- boundary hypotheses are supplied.
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeUpTo design p zs[5]! goal)
    mkLambdaFVars xs (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The endpoint, its closed form, and the log line. -/
def noKids (f : Name) (n : Nat) : CommandElabM Unit := do
  let facts ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (factsTheorem f)
  let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (outsGTheorem f n)
  let masked ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (maskedTheorem f)
  let designG ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (designTheorem f n)
  let design ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (kidsTheorem f n designG)
  let name ← liftTermElabM (generate f n facts outs masked design)
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
  logInfo m!"NOKIDS {made}: the depth endpoint without the kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents; check antecedent left: portsMatchB (run facts by {facts}, output check under the gate by {outs}, children's bound by {masked}, designCheck from the connection widths by {design}: {designG} with the children's check from core_kidsPass_leaf / leaf_real_kidK_reg)"

/-- `#machine_no_kids f n`: an error where it is refused. -/
elab "#machine_no_kids " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noKids f n.getNat

/-- The same, a refusal LOGGED (`NOKIDS REFUSED`) instead of thrown. -/
elab "#machine_no_kids_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noKids f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOKIDS REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingNoKidsCommand
