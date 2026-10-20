import Tools.ShippingShipsNoOuts
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingMachineLinkedCommand

/-! # `#machine_no_outs f n using h`: the depth endpoint without the output check

`f.machine_ships_hierNR{n}` is `machine_ships_hierC` applied to the
generator's arguments. This command applies
`Tools.ShippingShipsNoOuts.machine_design_noOuts` to THE SAME arguments
(read off that theorem's proof term, as the existing composition does) and
discharges its hypothesis `hOuts` with the theorem `h` the user names, which
must have the explicit arguments

    h hcore hpost entry closes hb hBnd :
      outsCheck (childMap D.modules) n (checkedOptimize b) = true

(the core run, the post-processing fact, the declaration's reflection and
closing, `hierBinds b`, the endpoint's boundary). It adds

    f.machine_design_noOutsNR{n} : ∀ {contexts, run} hr entry closes,
      ∃ raw D, … ∧ (shipsHierCheck → designCheck → Bnd → Bd → …)

— the statement of `f.machine_design_svNR{n}` with the `outsCheck`
antecedent removed (checked here: the constant `outsCheck` does not occur in
the new statement) — and, when `f.machine_closes_at` exists, its `_closed`
form by the existing `closeEndpointAt`.

Nothing is assumed: the theorem is kernel-checked with standard axioms. -/
namespace Tools.ShippingShipsNoOutsCommand
open Lean Meta Elab Command

/-- A proof of a conjunction, and of every conjunct at every depth. -/
partial def andParts (h : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let t ← whnfR (← instantiateMVars (← inferType h))
  if t.isAppOfArity ``And 2 then
    return #[h] ++ (← andParts (← mkAppM ``And.left #[h])) ++
      (← andParts (← mkAppM ``And.right #[h]))
  else return #[h]

/-- **`f.machine_outs{n}`, generated**: the output check of `f`'s core run's
design at depth `n` (`Tools.ShippingChecksCore.core_outsCheck_all` at `f`'s
data), for a machine whose calls' children are machines WITHOUT calls and
WITH a register (`leaf_real_kidA`, `leaf_real_kidR` per entry). Hypotheses:
the core run, the post-processing fact, `f`'s reflection and closing,
`hierBinds b`, the child boundary of the start world, and the reflection of
each called declaration. Any other shape is REFUSED with its reason:
* a memory child, a child that is not a machine (a gate child): no output
  facts are derived for them here;
* a child with calls of its own: `kids_real_kid` applies, but it asks the
  child's `KidNames`, its closing in every context and the same facts of
  ITS children — not generated;
* a machine child without a register (`leaf_real_kidA` asks one). -/
def outsTheorem (f : Name) (n : Nat) : CommandElabM Name := do
  let name := f ++ Name.mkSimple s!"machine_outs{n}"
  if (← getEnv).contains name then return name
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call"
  let kids := calls.eraseDups
  for k in kids do
    if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
      throwError "{f}: {Tools.ShippingMachineCommand.memNameRefusal r.shape k "its output facts are not derived here"}"
    unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
        (← getEnv).contains (k ++ `machine_body) do
      throwError "{f}: the child {k} is not a machine with an endpoint (a gate child: its output facts are not derived here)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      throwError "{f}: the child {k} has calls of its own (kids_real_kid: not generated)"
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the child {k} has no register (leaf_real_kidA asks one)"
    unless (← liftTermElabM <| Tools.ShippingMachineClosesGen.closesTheorem? k).isSome do
      throwError "{f}: the child {k}'s own closing is not derived ({k}.machine_closes)"
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
        (hb : Sparkle.IR.RefineCheck.hierBinds b = true)
        (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $binders* :
        Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules)
          $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
      Tools.ShippingChecksCore.core_outsCheck_all (nDecl := $nDecl) $data
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
        hB hcore hpost entry closes hb $nLit))
  let msgs := (← get).messages.toList.drop before
  if msgs.any (·.severity == .error) || !(← getEnv).contains name then
    let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    throwError "{name}: the generated proof fails: {errs.take 2}"
  liftTermElabM do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  return name

/-- `f.machine_design_noOutsNR{n}` from `f.machine_ships_hierNR{n}` and the
output-check theorem `outs`. -/
def generate (f : Name) (n : Nat) (outs : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noOutsNR{n}"
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
      (← mkAppOptM ``Tools.ShippingShipsNoOuts.machine_design_noOuts args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    let .forallE _ T _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope T fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      -- zs: raw D w1 hcore hpost hb hBnd ; xs[9] = entry, xs[10] = closes
      let mut p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      -- the remaining hypotheses of `outs`: the boundary, or conjuncts of it
      let parts ← andParts zs[6]!
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
          throwError "{outs}: asks{indentExpr dom}\nwhich is not a conjunct of the endpoint's boundary{indentExpr (← inferType zs[6]!)}"
      unless ← isDefEq (← inferType p) goal do
        throwError "{outs}: proves{indentExpr (← inferType p)}\nbut the head asks{indentExpr goal}"
      mkLambdaFVars zs p
    mkLambdaFVars xs (mkApp pre hOuts)
  let value ← instantiateMVars value
  let type ← inferType value
  if (type.find? (·.isConstOf ``Tools.ShippingDesignSVBack.outsCheck)).isSome then
    throwError "{name}: the statement still mentions outsCheck"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The endpoint, its closed form, and the log line. -/
def noOuts (f : Name) (n : Nat) (outs : Name) : CommandElabM Unit := do
  let name ← liftTermElabM (generate f n outs)
  let mut made := #[name]
  let cl := f ++ `machine_closes_at
  if (← getEnv).contains cl then
    let nn := Tools.ShippingMachineClosesGen.closedName name
    if ← liftTermElabM (Tools.ShippingMachineClosesAtGen.closeEndpointAt f cl name nn) then
      made := made.push nn
  logInfo m!"NOOUTS {made}: the depth endpoint without the outsCheck antecedent (derived from the core run by {outs})"

/-- With a hand-written output-check theorem. -/
elab "#machine_no_outs " d:ident n:num " using " h:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let outs ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo h
  noOuts f n.getNat outs

/-- With the generated `f.machine_outs{n}` (an error where it is refused). -/
elab "#machine_no_outs " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (outsTheorem f n.getNat)
  noOuts f n.getNat outs

/-- Only the generated `f.machine_outs{n}`; success or refusal LOGGED
(`OUTSGEN`). -/
elab "#machine_outs_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
      (outsTheorem f n.getNat)
    logInfo m!"OUTSGEN {outs}: generated"
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"OUTSGEN REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

/-- The same, a refusal LOGGED (`NOOUTS REFUSED`) instead of thrown: for
measuring which declarations the generator covers. -/
elab "#machine_no_outs_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
      (outsTheorem f n.getNat)
    noOuts f n.getNat outs
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOOUTS REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

end Tools.ShippingShipsNoOutsCommand
