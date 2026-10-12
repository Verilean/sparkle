import Tools.ShippingNoDesign
import Tools.ShippingShipsFreeMaskedCommand

/-! # `#machine_no_design f n`: the depth endpoint without `designCheck` (isolated branch `fix/opt-fallback`)

`#machine_no_ships_masked f n` (`Tools/ShippingShipsFreeMaskedCommand.lean`)
gives the endpoint whose only check antecedent is `designCheck`. This
command applies `Tools.ShippingNoDesign.machine_design_noDesign` to the same
arguments (those of `f.machine_ships_hierNR{n}`) and discharges its FOUR run
hypotheses with generated theorems:

* `f.machine_runFacts`, `f.machine_outsG{n}`, `f.machine_maskedG` (as
  `#machine_no_ships_masked`; the existing generators are called);
* `f.machine_designG{n}`:

      hcore hpost entry closes hB (children's reflections)
      (hports : portsMatchB (childMap D.modules) (checkedOptimize b) = true)
      (hkids : kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n)
        (checkedOptimize b).body = true) :
      designCheck (childMap D.modules) n (checkedOptimize b) = true

  — `Tools.ShippingTextShipped.core_designCheck_run` at `f`'s data: the data
  checks by `decide`, `hkidP` / `hkidW` as in `f.machine_runFacts`, and the
  two data conditions on the output ports DECIDED: `hon` (names
  sanitize-stable) through the character-wise form and
  `sanitizeName_of_clean`, `hoty` (scalar types) directly.

It adds `f.machine_design_noDesignNR{n}`:

    ∀ {contexts, run} hr entry closes, ∃ raw D, … ∧ (portsMatchB … → kidsPass … → Bnd → …)

and its `_closed` form. The command REFUSES a produced statement that
mentions `designCheck`, `shipsHierCheck`, `outsCheck` or `kidsMaskedN`.

Scope: that of `#machine_no_ships` (leaf machine children with a register,
their closings derived; the parent has a register), and a declaration whose
output port names are character-wise clean and whose output types are
scalar (otherwise the generated `f.machine_designG{n}` fails at `decide`,
reported as an error).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNoDesignCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (scope checkMade factsTheorem outsGTheorem discharge)
open Tools.ShippingShipsFreeMaskedCommand (maskedTheorem)

/-- `Tools.ShippingShipsFreeCommand.discharge`, stopping as soon as the type
is `goal` (the goal here is itself an implication: the two check premises
stay). -/
def dischargeUpTo (thm : Name) (p0 : Lean.Expr) (hBnd goal : Lean.Expr) : MetaM Lean.Expr := do
  let parts ← Tools.ShippingShipsNoOutsCommand.andParts hBnd
  let mut p := p0
  repeat
    let t ← whnfR (← instantiateMVars (← inferType p))
    if ← isDefEq t goal then break
    let .forallE _ dom _ _ := t | break
    let mut found := false
    for q in parts do
      if ← isDefEq (← inferType q) dom then
        p := mkApp p q
        found := true
        break
    unless found do
      throwError "{thm}: asks{indentExpr dom}\nwhich is not a conjunct of the endpoint's boundary{indentExpr (← inferType hBnd)}"
  unless ← isDefEq (← inferType p) goal do
    throwError "{thm}: proves{indentExpr (← inferType p)}\nbut the head asks{indentExpr goal}"
  instantiateMVars p

/-- **`f.machine_designG{n}`, generated**: `designCheck` of the shipped
module of `f`'s core run at depth `n` from the connection widths and the
children's check (`core_designCheck_run` at `f`'s data). The per-entry terms
and the width condition are those of
`Tools.ShippingShipsFreeCommand.factsTheorem`, copied; the two data
conditions on the output ports are decided (`hon` through the
character-wise form, `sanitizeName_of_clean`). -/
def designTheorem (f : Name) (n : Nat) : CommandElabM Name := do
  let name := f ++ Name.mkSimple s!"machine_designG{n}"
  if (← getEnv).contains name then return name
  let (r, calls, kids) ← scope f
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
  let nLit := Syntax.mkNumLit (toString n)
  -- the children's layouts' output fields, per entry
  let outsOf (k : Name) : CommandElabM Term := `(($(nm k "machineData")).shape.layout.outs)
  let o0 ← outsOf kids[0]!
  let os ← calls.toArray.mapM outsOf
  -- one called declaration: the constant function (the form of the hand
  -- instance `parent_callWidths`); several: the list of the entries' layouts
  let kidOuts : Term ←
    if kids.length == 1 then `(fun _ => $o0) else `(fun k => List.getD [$os,*] k [])
  let mut tacP ← `(tactic| exact absurd hk' (by omega))
  let mut tacT ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let h := hR (kids.idxOf k)
    tacP ← `(tactic| cases k with
      | zero =>
        exact (Tools.ShippingSeqChildIface.seqChild_of_real $(nm k "machineData")
          $(nm k "machine_ok") $(nm k "machine_body") rfl (by decide) $h
          (fun mc cc => $(nm k "machine_closes") mc _ cc _) hy).outsIn
      | succ k => $tacP:tactic)
    tacT ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingChildIfaceTy.leaf_real_outTys $(nm k "machineData")
          $(nm k "machine_ok") $(nm k "machine_body") rfl
          (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide) $h
          (fun mc cc => $(nm k "machine_closes") mc _ cc _) hy
      | succ k => $tacT:tactic)
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
          (Sparkle.IR.OptCheck.checkedOptimize b) = true)
        (hkids : Tools.ShippingDesignSV.kidsPass (Tools.ShippingMachineLinked.childMap D.modules)
          (Tools.ShippingChecksDesign.kidCheck (Tools.ShippingMachineLinked.childMap D.modules)
            $nLit)
          (Sparkle.IR.OptCheck.checkedOptimize b).body = true) :
        Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
          $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
      Tools.ShippingTextShipped.core_designCheck_run (nDecl := $nDecl) $data
        $(nm f "machine_ok") $(nm f "machine_body") (by decide) (by decide) (by decide)
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (by decide) (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tacP:tactic)
        (Tools.ShippingCallWidths.hkidW_of_data
          (by decide : Tools.ShippingCallWidths.callWidthsOk $data $nDecl $kidOuts = true)
          (by
            intro k hk y hy
            have hk' : k < $nCalls := hk
            $tacT:tactic))
        hB hcore hpost entry closes
        (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
              Sparkle.IR.NameHints.charOk c = true from by
            first | decide | decide +kernel) o ho))
        (by decide) $nLit hports hkids))
  checkMade name before
  return name

/-- The constants a produced statement must not mention. -/
def forbidden : List Name :=
  [``Tools.ShippingDesignSV.designCheck, ``Tools.ShippingHierPremisesBase.shipsHierCheck,
   ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingMachineShipsDepth.kidsMaskedN]

/-- `f.machine_design_noDesignNR{n}` from `f.machine_ships_hierNR{n}`'s
arguments and the four run theorems. -/
def generate (f : Name) (n : Nat) (facts outs masked design : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noDesignNR{n}"
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
      (← mkAppOptM ``Tools.ShippingNoDesign.machine_design_noDesign args)
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
    -- `designCheck` from the two check premises: zs = raw D w1 hcore hpost hBnd.
    -- The telescope is cut at 6 binders: the goal is
    -- `portsMatchB … → kidsPass … → designCheck …`, which `design` proves once
    -- its boundary hypotheses are supplied.
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
def noDesign (f : Name) (n : Nat) : CommandElabM Unit := do
  let facts ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (factsTheorem f)
  let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (outsGTheorem f n)
  let masked ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (maskedTheorem f)
  let design ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (designTheorem f n)
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
  logInfo m!"NODESIGN {made}: the depth endpoint without the designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents; check antecedents left: portsMatchB and kidsPass (run facts by {facts}, output check under the gate by {outs}, children's bound by {masked}, designCheck from the two by {design})"

/-- `#machine_no_design f n`: an error where it is refused. -/
elab "#machine_no_design " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noDesign f n.getNat

/-- The same, a refusal LOGGED (`NODESIGN REFUSED`) instead of thrown. -/
elab "#machine_no_design_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noDesign f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NODESIGN REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingNoDesignCommand
