import Tools.ShippingNoPorts
import Tools.ShippingNoKidsCommand
import Tools.ShippingPortsMatchShippedLeaf

/-! # `#machine_no_ports f n`: the depth endpoint without any check antecedent (G1, round par/a-4)

`#machine_no_kids f n` (`Tools/ShippingNoKidsCommand.lean`) gives the
endpoint whose one check antecedent is `portsMatchB`. This command applies
`Tools.ShippingNoPorts.machine_design_noPorts` to the same arguments (those
of `f.machine_ships_hierNR{n}`) and discharges its four run hypotheses with
generated theorems:

* `f.machine_runFacts`, `f.machine_outsG{n}`, `f.machine_maskedG`,
  `f.machine_designG{n}`, `f.machine_designK{n}` (the existing generators
  are called);
* `c.machine_leafKid`, per distinct called declaration `c`:

      (entryC : MachineDefines mctx mref cctx cref c c.machineData.shape) :
      LeafKid mctx mref cctx cref c c.machineData

  — the data fields by `decide`, `leaf` by `rfl`, the closing by
  `c.machine_closes` (the form of the hand instance
  `Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid`);
* `f.machine_portsG`:

      hcore hpost entry closes hB (children's reflections) :
      portsMatchB (childMap D.modules) (checkedOptimize b) = true

  — `Tools.ShippingPortsMatchShippedLeaf.core_portsMatch_shipped_leaf` at
  `f`'s data. The data conditions are DECIDED (listed in
  `docs/parallel/A-noports.md`): the parent's checks, `callWidthsOk d nDecl
  (fun k => (kid k).shape.layout.outs)`, `callArgsOk d nDecl (fun k =>
  declWidths (kid k))`, the output names (character-wise, then
  `sanitizeName_of_clean`) and scalar output types. `kid` is the constant
  function for one called declaration and `fun k => List.getD [d₀, d₁, …] k
  d₀` over the ENTRIES' callees' data for several; `hkid` is, for one called
  declaration, a `decide` that every entry's callee is that declaration
  (independent of the entry count) and then its `machine_leafKid`; for
  several, a case split over the entries the reader counted;
* `f.machine_designP{n}`:

      hcore hpost entry closes hB (children's reflections) :
      designCheck (childMap D.modules) n (checkedOptimize b) = true

  — `f.machine_designK{n}` applied to `f.machine_portsG`.

It adds `f.machine_design_noPortsNR{n}`:

    ∀ {contexts, run} hr entry closes, ∃ raw D, … ∧ (Bnd → …)

and its `_closed` form. The command REFUSES a produced statement that
mentions `portsMatchB`, `kidsPass`, `designCheck`, `shipsHierCheck`,
`outsCheck` or `kidsMaskedN`.

Scope (anything else REFUSED with its reason): that of `#machine_no_kids`,
and stated here first with the reasons of THIS command — the parent has a
register (`core_portsMatch_raw_leaf` asks `d.shape.layout.slots ≠ []`: the
parent's `clk` / `rst` come from its own register, `core_clk`); every called
declaration is a LEAF REGISTER machine (a machine with an endpoint, without
calls, with a register: the fields `leaf` and `slots` of `LeafKid`); the
depth endpoint `f.machine_ships_hierNR{n}` exists. A declaration in that
scope whose data conditions fail fails at a `decide` of a generated theorem,
reported as an error (`… the generated proof fails`).

`#machine_no_ports_try` logs a refusal instead of throwing; `sweep` runs the
command over a list of names and logs one `NOPORTS SWEEP` line.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingNoPortsCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (scope checkMade factsTheorem outsGTheorem discharge)
open Tools.ShippingShipsFreeMaskedCommand (maskedTheorem)
open Tools.ShippingNoDesignCommand (designTheorem)
open Tools.ShippingNoKidsCommand (kidsTheorem)

/-- The scope of this command, with ITS reasons, then the shared scope test
(`Tools.ShippingShipsFreeCommand.scope`: the calls of `f`, the distinct
called declarations, `f`'s reading). -/
def scopeP (f : Name) :
    CommandElabM (Tools.ShippingMachineCommand.Read × List Name × List Name) := do
  unless (← getEnv).contains (f ++ `machineData) && (← getEnv).contains (f ++ `machine_ok) &&
      (← getEnv).contains (f ++ `machine_body) do
    throwError "{f}: not a machine with an endpoint (no {f}.machineData / machine_ok / machine_body: #machine_endpoint was not run on it)"
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call (nothing to match: no instance statement)"
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: parent without a register (core_portsMatch_raw_leaf asks d.shape.layout.slots ≠ []: the parent's clk and rst ports, which the connections of a sequential child are matched against, are derived from the parent's own register by core_clk)"
  for k in calls.eraseDups do
    if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
      throwError "{f}: {Tools.ShippingMachineCommand.memNameRefusal r.shape k "not a leaf register machine: LeafKid is about a machine declaration's data"}"
    unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
        (← getEnv).contains (k ++ `machine_body) do
      throwError "{f}: the callee {k} is not a leaf register machine: it has no machine endpoint (a gate child or a declaration #machine_endpoint was not run on: no data for LeafKid)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      throwError "{f}: the callee {k} is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)"
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the callee {k} is not a leaf register machine: it has no register (LeafKid.slots asks shape.layout.slots ≠ []; a combinational child's ports are not derived here)"
  scope f

/-- **`c.machine_leafKid`, generated**: the premises about the leaf register
machine `c` from its data and its reflection (the hand instance
`cnt_leafKid`, with the declaration's names). -/
def leafKidTheorem (c : Name) : CommandElabM Name := do
  let name := c ++ `machine_leafKid
  if (← getEnv).contains name then return name
  let nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := nm c "machineData"
  let cq : Term := quote c
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State}
        (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $cq
          ($data).shape) :
        Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref $cq $data :=
      { ok := $(nm c "machine_ok")
        body := $(nm c "machine_body")
        calls := by decide
        dom := by decide
        leaf := rfl
        slots := fun h0 => absurd (congrArg List.length h0) (by decide)
        ss := by decide
        outTy := by decide
        outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
              Sparkle.IR.NameHints.charOk c = true from by
            first | decide | decide +kernel) o ho)
        outScalar := by decide
        entry := entryC
        closes := fun mc cc => $(nm c "machine_closes") mc _ cc _ }))
  checkMade name before
  return name

/-- **`f.machine_portsG`, generated**: `portsMatchB` of the shipped module of
`f`'s core run (`core_portsMatch_shipped_leaf` at `f`'s data; `leafKids`:
the generated `machine_leafKid` of each distinct called declaration, in the
order of `scope`'s list). -/
def portsTheorem (f : Name) : CommandElabM Name := do
  let name := f ++ `machine_portsG
  if (← getEnv).contains name then return name
  let (r, calls, kids) ← scopeP f
  for k in kids do discard <| leafKidTheorem k
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
  -- the entries' callees' data
  let d0 : Term := ⟨(nm kids[0]! "machineData").raw⟩
  let ds : Array Term := calls.toArray.map fun k => ⟨(nm k "machineData").raw⟩
  -- one called declaration: the constant function (the form of the hand
  -- instances); several: the list of the ENTRIES' callees' data
  let single := kids.length == 1
  let kid : Term ← if single then `(fun _ => $d0) else `(fun k => List.getD [$ds,*] k $d0)
  let kidOuts : Term ←
    if single then `(fun _ => ($d0).shape.layout.outs)
    else `(fun k => (List.getD [$ds,*] k $d0).shape.layout.outs)
  let kidIns : Term ←
    if single then `(fun _ => Tools.ShippingPortWidthsPure.declWidths $d0)
    else `(fun k => Tools.ShippingPortWidthsPure.declWidths (List.getD [$ds,*] k $d0))
  -- `hkid`
  let tacKid ← if single then do
      let k0 := kids[0]!
      let k0q : Term := quote k0
      -- every entry's callee is the one called declaration: decided on the
      -- reflected data, independent of the entry count
      `(tactic| (
        have hall : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
            (($data).shape.insts[k]).1 = $k0q := by decide
        rw [hall k hk]
        exact $(nm k0 "machine_leafKid") $(hR 0)))
    else do
      let mut tac ← `(tactic| exact absurd hk' (by omega))
      for i' in [0:calls.length] do
        let i := calls.length - 1 - i'
        let k := calls[i]!
        let h := hR (kids.idxOf k)
        tac ← `(tactic| cases k with
          | zero => exact $(nm k "machine_leafKid") $h
          | succ k => $tac:tactic)
      `(tactic| (
        have hk' : k < $nCalls := hk
        $tac:tactic))
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
        Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
          (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
      Tools.ShippingPortsMatchShippedLeaf.core_portsMatch_shipped_leaf (nDecl := $nDecl) $data
        $(nm f "machine_ok") $(nm f "machine_body") (by decide) (by decide) (by decide)
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        (by decide) (by decide)
        (fun h0 => absurd (congrArg List.length h0) (by decide))
        $kid
        (by
          intro k hk
          $tacKid:tactic)
        (show Tools.ShippingCallWidths.callWidthsOk $data $nDecl $kidOuts = true from by
          first | decide | decide +kernel)
        (show Tools.ShippingPortsMatchRaw.callArgsOk $data $nDecl $kidIns = true from by
          first | decide | decide +kernel)
        hB hcore hpost entry closes
        (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
          ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
              Sparkle.IR.NameHints.charOk c = true from by
            first | decide | decide +kernel) o ho))
        (by decide)))
  checkMade name before
  return name

/-- **`f.machine_designP{n}`, generated**: `designCheck` of the shipped
module of `f`'s core run at depth `n` with NO check premise
(`designK` is `f.machine_designK{n}`, `ports` is `f.machine_portsG`; both
have the binders `hcore hpost entry closes hB` and the children's
reflections in the order of `scope`'s list). -/
def designPTheorem (f : Name) (n : Nat) (designK ports : Name) : CommandElabM Name := do
  let name := f ++ Name.mkSimple s!"machine_designP{n}"
  if (← getEnv).contains name then return name
  let (_, _, kids) ← scopeP f
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
  let nLit := Syntax.mkNumLit (toString n)
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
        Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
          $nLit (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
      $(mkIdent (`_root_ ++ designK)) hcore hpost entry closes hB $hRs*
        ($(mkIdent (`_root_ ++ ports)) hcore hpost entry closes hB $hRs*)))
  checkMade name before
  return name

/-- The constants a produced statement must not mention: the six checker
constants. -/
def forbidden : List Name :=
  Tools.ShippingNoKidsCommand.forbidden ++ [``Tools.ShippingDesignSV.portsMatchB]

/-- `f.machine_design_noPortsNR{n}` from `f.machine_ships_hierNR{n}`'s
arguments and the four run theorems (`Tools.ShippingNoKidsCommand.generate`,
copied, with the head `machine_design_noPorts`; the fourth hypothesis is now
discharged completely: its goal is `designCheck … = true`, no implication). -/
def generate (f : Name) (n : Nat) (facts outs masked design : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noPortsNR{n}"
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
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
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
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd. The
    -- telescope is cut at 6 binders (as above); the goal is the equation
    -- `designCheck … = true`, which `design` proves once its boundary
    -- hypotheses are supplied.
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← discharge design p zs[5]! goal)
    mkLambdaFVars xs (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The endpoint, its closed form, and the log line. -/
def noPorts (f : Name) (n : Nat) : CommandElabM Unit := do
  -- the scope, with this command's reasons, before anything is generated
  discard <| scopeP f
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  unless (← getEnv).contains ships do
    throwError "{f}: no depth endpoint at depth {n} ({ships} is not there: run #machine_design_svNR {f} {n} first)"
  let facts ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (factsTheorem f)
  let outs ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (outsGTheorem f n)
  let masked ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (maskedTheorem f)
  let designG ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (designTheorem f n)
  let designK ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (kidsTheorem f n designG)
  let ports ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (portsTheorem f)
  let design ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (designPTheorem f n designK ports)
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
  logInfo m!"NOPORTS {made}: the depth endpoint without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents; check antecedent left: none (run facts by {facts}, output check under the gate by {outs}, children's bound by {masked}, designCheck by {design}: {designK} applied to {ports}, which is core_portsMatch_shipped_leaf at the declaration's data)"

/-- `#machine_no_ports f n`: an error where it is refused. -/
elab "#machine_no_ports " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  noPorts f n.getNat

/-- The same, a refusal LOGGED (`NOPORTS REFUSED`) instead of thrown. -/
elab "#machine_no_ports_try " d:ident n:num : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    noPorts f n.getNat
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"NOPORTS REFUSED {f} at depth {n.getNat}: {ex.toMessageData}"

/-- The command over a list of names at depth `n`, LOGS ONLY: one
`NOPORTS SWEEP` line with the declarations generated and, for each of the
others, the reason of its refusal (a name that is absent is logged as such).
A refused declaration leaves nothing in the environment. -/
def sweep (n : Nat) (names : List Name) : CommandElabM Unit := do
  let mut made : Array Name := #[]
  let mut refused : Array MessageData := #[]
  for f in names do
    unless (← getEnv).contains f do
      refused := refused.push m!"{f}: absent (not a declaration of the imported files)"
      continue
    let savedEnv ← getEnv
    let savedMsgs := (← get).messages
    try
      noPorts f n
      modify fun s => { s with messages := savedMsgs }
      made := made.push f
    catch ex =>
      setEnv savedEnv
      modify fun s => { s with messages := savedMsgs }
      refused := refused.push m!"{f}: {ex.toMessageData}"
  logInfo m!"NOPORTS SWEEP: generated {made.size} of {names.length} {made} at depth {n}; refused {refused.size} with reasons:\n{MessageData.joinSep refused.toList "\n"}"

end Tools.ShippingNoPortsCommand
