import Tools.ShippingShipsFree
import Tools.ShippingShipsNoOutsCommand
import Tools.ShippingCallWidths
import Tools.ShippingChildIfaceTy

/-! # `#machine_no_ships f n`: the depth endpoint without `shipsHierCheck` (isolated branch `fix/opt-fallback`)

`f.machine_ships_hierNR{n}` is `machine_ships_hierC` applied to the
generator's arguments. This command applies
`Tools.ShippingShipsFree.machine_design_noOuts_noShips` to THE SAME
arguments (read off that theorem's proof term, exactly as `#machine_no_outs`
does) and discharges its two hypotheses with two generated theorems:

* `f.machine_runFacts : RunFacts (childMap D.modules) b` — hypotheses: the
  core run, the post-processing fact, `f`'s reflection and closing, the
  child boundary of the start world, the reflection of each called
  declaration. It is `Tools.ShippingChecksRunFacts.core_runFacts` at `f`'s
  data: the data checks by `decide`; `hkidP` per entry from the real child
  (`seqChild_of_real … .outsIn`); `hkidW` from the run-free width condition
  `callWidthsOk` (ONE `decide` over `f`'s and its children's data) and the
  real child's output ports (`leaf_real_outTys`).
* `f.machine_outsG{n} : outsCheck (childMap D.modules) n (checkedOptimize b)`
  — the same hypotheses and the statement-kind gate `hierGate b` (which the
  head supplies from the run's facts): `core_outsCheck_all_gate`, per entry
  `leaf_real_kidA` / `leaf_real_kidR` as `f.machine_outs{n}` does.

It adds

    f.machine_design_noShipsNR{n} : ∀ {contexts, run} hr entry closes,
      ∃ raw D, … ∧ (designCheck → Bnd → Bd → …)

and, when `f.machine_closes_at` exists, its `_closed` form by the existing
`closeEndpointAt`. The command REFUSES (an error with the reason) a produced
statement that still mentions the constant `shipsHierCheck` or `outsCheck`.

Scope (the same as `#machine_no_outs`, anything else REFUSED with its
reason): every called declaration is a machine WITHOUT calls and WITH a
register, with its own closing derived; and `f` itself has a register
(`core_runFacts` asks `d.shape.layout.slots ≠ []`).

The children's hypotheses are found among the conjuncts of the endpoint's
boundary (`ChildBnd mref cref w` and the children's reflections); a
hypothesis that is not a conjunct of it is an error naming it.

Nothing is assumed: the theorems are kernel-checked with standard axioms.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingShipsFreeCommand
open Lean Meta Elab Command

/-- The scope test shared by the two generated theorems: the calls of `f`,
the distinct called declarations, and `f`'s reading. -/
def scope (f : Name) : CommandElabM (Tools.ShippingMachineCommand.Read × List Name × List Name) := do
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call"
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: no register (core_runFacts asks one of the parent)"
  let kids := calls.eraseDups
  for k in kids do
    if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
      throwError "{f}: {Tools.ShippingMachineCommand.memNameRefusal r.shape k "its facts are not derived here"}"
    unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
        (← getEnv).contains (k ++ `machine_body) do
      throwError "{f}: the child {k} is not a machine with an endpoint (a gate child: its facts are not derived here)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      throwError "{f}: the child {k} has calls of its own (not generated)"
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the child {k} has no register (leaf_real_outTys / leaf_real_kidA ask one)"
    unless (← liftTermElabM <| Tools.ShippingMachineClosesGen.closesTheorem? k).isSome do
      throwError "{f}: the child {k}'s own closing is not derived ({k}.machine_closes)"
  return (r, calls, kids)

/-- The generated declaration `name` exists, without an error message since
`before`, on standard axioms. -/
def checkMade (name : Name) (before : Nat) : CommandElabM Unit := do
  let msgs := (← get).messages.toList.drop before
  if msgs.any (·.severity == .error) || !(← getEnv).contains name then
    let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    throwError "{name}: the generated proof fails: {errs.take 2}"
  liftTermElabM do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"

/-- **`f.machine_runFacts`, generated**: the run's facts of the full entry's
module of `f` (`core_runFacts` at `f`'s data). -/
def factsTheorem (f : Name) : CommandElabM Name := do
  let name := f ++ `machine_runFacts
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
        (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders* :
        Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
      Tools.ShippingChecksRunFacts.core_runFacts (nDecl := $nDecl) $data
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
        hB hcore hpost entry closes))
  checkMade name before
  return name

/-- **`f.machine_outsG{n}`, generated**: the output check of `f`'s core
run's design at depth `n` under the statement-kind gate
(`core_outsCheck_all_gate` at `f`'s data; the per-entry terms are those of
`Tools.ShippingShipsNoOutsCommand.outsTheorem`, copied). -/
def outsGTheorem (f : Name) (n : Nat) : CommandElabM Name := do
  let name := f ++ Name.mkSimple s!"machine_outsG{n}"
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
  let nLit := Syntax.mkNumLit (toString n)
  let nDecl := Syntax.mkNumLit (toString r.nDecl)
  let mut tacA ← `(tactic| exact absurd hk' (by omega))
  let mut tacR ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let h := hR (kids.idxOf k)
    tacA ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingChecksRun2.leaf_real_kidA $(nm k "machineData") $(nm k "machine_ok")
          $(nm k "machine_body") rfl (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide) $h (fun mc cc => $(nm k "machine_closes") mc _ cc _) hy
      | succ k => $tacA:tactic)
    tacR ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingChecksCore.leaf_real_kidR $(nm k "machineData") $(nm k "machine_ok")
          $(nm k "machine_body") rfl (by decide) $h
          (fun mc cc => $(nm k "machine_closes") mc _ cc _) hy
      | succ k => $tacR:tactic)
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
        (hg : Sparkle.IR.RefineCheck.hierGate b = true)
        (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders* :
        Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules)
          $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
      Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := $nDecl) $data
        $(nm f "machine_ok") $(nm f "machine_body") (by decide) (by decide) (by decide)
        (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tacA:tactic)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tacR:tactic)
        hB hcore hpost entry closes hg $nLit))
  checkMade name before
  return name

/-- Apply `p` to the conjuncts of the boundary `hBnd` its remaining
hypotheses ask, until its type is `goal`. -/
def discharge (thm : Name) (p0 : Lean.Expr) (hBnd goal : Lean.Expr) : MetaM Lean.Expr := do
  let parts ← Tools.ShippingShipsNoOutsCommand.andParts hBnd
  let mut p := p0
  repeat
    let t ← whnfR (← instantiateMVars (← inferType p))
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

/-- `f.machine_design_noShipsNR{n}` from `f.machine_ships_hierNR{n}`'s
arguments, the run-facts theorem `facts` and the gated output-check theorem
`outs`. -/
def generate (f : Name) (n : Nat) (facts outs : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noShipsNR{n}"
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
    -- n Reset Bnd C Bd Inv hBd hRI {declName} d {kD ι dom src ext extB lsrc srcL extL extBL}
    -- soundL composed houtTy, then the run's binders
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingShipsFree.machine_design_noOuts_noShips args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      -- zs: raw D w1 hcore hpost hBnd ; xs[9] = entry, xs[10] = closes
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← discharge facts p zs[5]! goal)
    let pre := mkApp pre hFacts
    -- the output check under the gate
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      -- zs: raw D w1 hcore hpost hg hBnd
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← discharge outs p zs[6]! goal)
    mkLambdaFVars xs (mkApp pre hOuts)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if (type.find? (·.isConstOf ``Tools.ShippingHierPremisesBase.shipsHierCheck)).isSome then
    throwError "{name}: REFUSED, the statement still mentions shipsHierCheck"
  if (type.find? (·.isConstOf ``Tools.ShippingDesignSVBack.outsCheck)).isSome then
    throwError "{name}: REFUSED, the statement still mentions outsCheck"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The endpoint, its closed form, and the log line. -/
def noShips (f : Name) (n : Nat) : CommandElabM Unit := do
  let facts ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (factsTheorem f)
  let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (outsGTheorem f n)
  let name ← liftTermElabM (generate f n facts outs)
  let mut made := #[name]
  let cl := f ++ `machine_closes_at
  if (← getEnv).contains cl then
    let nn := Tools.ShippingMachineClosesGen.closedName name
    if ← liftTermElabM (Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn) then
      -- the closed form is checked too: the closing must not bring the checker back
      let some ci := (← getEnv).find? nn | throwError "{nn}: not added"
      if (ci.type.find? (·.isConstOf ``Tools.ShippingHierPremisesBase.shipsHierCheck)).isSome then
        throwError "{nn}: REFUSED, the statement still mentions shipsHierCheck"
      made := made.push nn
  logInfo m!"NOSHIPS {made}: the depth endpoint without the shipsHierCheck and outsCheck antecedents (run facts by {facts}, output check under the gate by {outs})"

/-- `#machine_no_ships f n`: an error where it is refused. -/
elab "#machine_no_ships " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noShips f n.getNat

/-- The same, a refusal LOGGED (`NOSHIPS REFUSED`) instead of thrown: for
measuring which declarations the generator covers. -/
elab "#machine_no_ships_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noShips f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOSHIPS REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingShipsFreeCommand
