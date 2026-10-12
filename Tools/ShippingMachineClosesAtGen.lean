import Tools.ShippingCallsGate
import Tools.ShippingMachineChildRun
import Tools.ShippingMachineClosesGen
import Tools.ShippingGateChildCommand
import Tools.ShippingMachineClosesAtGenG
import Tools.ShippingNameSep

/-! # Generating `f.machine_closes_at`

For a machine `f` whose calls are one-output calls of gate children
(`#gate_child` run on each) or of SLOTLESS machine children (a combinational
body with `let`s and no call, e.g. `pickByteH`; `#machine_endpoint` run on
each): the theorem

  `f.machine_closes_at : EntryDefines … c c.gateValue → … → MachineClosesAt mctx mref cctx cref f f.machineData.shape`

(`machineClosesAt_of_gateKids` at `f`'s data), and the endpoints of `f` that
ask `MachineClosesAt` with that premise replaced by the theorem's own
(`_closed`). The theorem's premises:

* the reflection of each called declaration (`EntryDefines`, already a
  premise of the endpoints);
* NAME SEPARATION, obligations about the compiler's module names that the
  kernel cannot evaluate (`Name.toString` with escaping does not reduce; the
  unescaped renderer does, but no theorem relates the two): no call's printed
  name is the parent's; with several called declarations, different
  declarations print differently; and — only when an output port's name
  starts with `i` — no output port is named as an instance.

Several instances of one declaration are covered, with any calls between: the
later call is a cache hit of the entry the earlier left, which the calls
between keep (`Tools/ShippingCallsSame.lean`).

The data conditions (the endpoint's checks, `letsAliasOk`, `gateCallsOk`, no
memory child, the argument counts) are decided by the kernel. Where one of
them fails nothing is added. -/
namespace Tools.ShippingMachineClosesAtGen
open Lean Meta Elab Command
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry

def standardAxioms (name : Name) : CoreM Unit := do
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"

/-- `name` is a theorem `∀ {mctx mref cctx cref}, … → MachineClosesAt mctx mref
cctx cref c c.machineData.shape` — the conclusion at the theorem's OWN four
context binders, every other binder a premise — on standard axioms (so not
through `sorry`). A structural check of a freshly generated theorem; an
EXISTING one is compared with the generated statement (`closesAtTheorem`). -/
def auditClosesAt (c name : Name) : MetaM Unit := do
  let some (.thmInfo info) := (← getEnv).find? name | throwError "{name}: not a theorem"
  let shape ← mkAppM ``MachineData.shape #[mkConst (c ++ `machineData)]
  let ok ← forallTelescope info.type fun xs body => do
    let body ← instantiateMVars body
    if xs.size < 4 then return false
    let tys ← (xs.extract 0 4).mapM fun x => do whnfR (← inferType x)
    let refOf (t : Lean.Expr) (st : Name) : Bool :=
      t.isAppOfArity ``ST.Ref 2 && t.getArg! 0 == mkConst ``IO.RealWorld && t.getArg! 1 == mkConst st
    unless tys[0]!.isConstOf ``Lean.Meta.Context && refOf tys[1]! ``Lean.Meta.State &&
        tys[2]!.isConstOf ``Lean.Core.Context && refOf tys[3]! ``Lean.Core.State do return false
    for x in xs.extract 4 xs.size do
      unless ← isProp (← inferType x) do return false
    if body.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && body.getArg! 4 == toExpr c &&
        (body.getAppArgs.extract 0 4) == xs.extract 0 4 then
      isDefEq (body.getArg! 5) shape
    else pure false
  unless ok do throwError "{name}: not a closing theorem of {c}'s shape at its own context binders"
  standardAxioms name

/-- The generation itself; may leave declarations and messages behind on
failure (`closesAtTheorem` restores them). `nDecl?`: the number of declaration
binders to state the data check at, instead of the reader's. -/
def closesAtCore (c : Name) (nDecl? : Option Nat) (name : Name := c ++ `machine_closes_at) :
    CommandElabM Name := do
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine c
  -- calls with several outputs or of sequential children: the general
  -- closing's generator (`machineClosesAt_of_seqKids`)
  if !r.shape.instFields.isEmpty then
    let nm ← Tools.ShippingMachineClosesAtGenG.closesAtCoreG c nDecl? name
    liftTermElabM (auditClosesAt c nm)
    return nm
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{c}: no call"
  let kids := calls.eraseDups
  -- a callee: a gate child (`#gate_child`), or a SLOTLESS machine child (a
  -- combinational body with `let`s and no call: the machine route compiles
  -- it); the number of its declaration binders, for a machine child
  let mut machKid : Std.HashMap Name Nat := {}
  for k in kids do
    if (← getEnv).contains (k ++ `gate_peel) then continue
    unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
        (← getEnv).contains (k ++ `machine_body) do
      throwError "{c}: {k} is neither a generated gate child (#gate_child) nor a machine with an endpoint (#machine_endpoint)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      throwError "{c}: the machine child {k} has calls of its own (not derived here)"
    unless cr.shape.layout.slots.isEmpty do
      throwError "{c}: the machine child {k} has registers (a sequential child: the general closing, B2)"
    if cr.shape.layout.lets == 0 then
      throwError "{c}: the machine child {k} has no `let` (K = 0: not derived)"
    unless cr.shape.layout.outs.map (·.name) == ["out"] do
      throwError "{c}: the machine child {k} does not have the one output `out`"
    unless (← liftTermElabM <| Tools.ShippingMachineClosesGen.closesTheorem? k).isSome do
      throwError "{c}: the machine child {k}'s own closing is not derived ({k}.machine_closes)"
    machKid := machKid.insert k cr.nDecl
  -- several instances of one declaration are one module by the child cache:
  -- derived from the run's order, with any calls between (the entry survives
  -- their synthesis at a positive depth) — no restriction on the call list
  let n (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := n c "machineData"
  let cq : Term := quote c
  let hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [0:kids.length] do
    let k := kids[j]!
    let kq : Term := quote k
    binders := binders.push (← if machKid.contains k then
      `(bracketedBinder|
        ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
          ($(n k "machineData")).shape))
    else `(bracketedBinder|
      ($(hR j) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $kq $(n k "gateValue"))))
  -- the names
  -- different declarations have different printed names: nothing to ask with
  -- one called declaration; otherwise a premise (`Name.toString` does not
  -- reduce in the kernel)
  let k0 : Term := quote kids[0]!
  let hnames ← if kids.length == 1 then
      `(fun c hc c' hc' _ =>
        ((by decide : ∀ c ∈ ($data).shape.insts.map (·.1), c = $k0) c hc).trans
          ((by decide : ∀ c ∈ ($data).shape.insts.map (·.1), c = $k0) c' hc').symm)
    else if kids.all (fun a => kids.all fun b => a == b || Tools.ShippingNameSep.sepB a b) then
      -- different declarations print differently: decided on the names' candidate
      -- renderings (`Tools.ShippingNameSep`), `Name.toString` never evaluated
      `(Tools.ShippingNameSep.hnames_of _ (by decide))
    else do
      binders := binders.push (← `(bracketedBinder|
        (hnames : ∀ c ∈ ($data).shape.insts.map (·.1), ∀ c' ∈ ($data).shape.insts.map (·.1),
          c.toString = c'.toString → c = c')))
      `(hnames)
  -- no call prints as the parent: by the candidate renderings when they
  -- separate, else a premise
  let hparent : Term ← if kids.all (fun k => Tools.ShippingNameSep.sepB k c) then
      `(Tools.ShippingNameSep.hparent_of _ _ (by decide))
    else do
      binders := binders.push (← `(bracketedBinder|
        (hparent : ∀ c ∈ ($data).shape.insts, c.1.toString ≠ ($cq : Lean.Name).toString)))
      `(hparent)
  let hfresh ← if r.shape.layout.outs.all (fun o => o.name.toList.head? != some 'i') then
      `(fun k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
        ((by decide : ∀ o ∈ ($data).shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) k _)
    else do
      binders := binders.push (← `(bracketedBinder|
        (hfresh : ∀ (k : Nat) (hk : k < ($data).shape.insts.length), ∀ o ∈ ($data).shape.layout.outs,
          o.name ≠ s!"inst{k}_{(($data).shape.insts[k]).1.toString}")))
      `(hfresh)
  -- each call's child, read off its `RealChild` witness
  let nCalls := Syntax.mkNumLit (toString calls.length)
  let mut tac ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let h := hR (kids.idxOf k)
    tac ← match machKid.get? k with
      | some nd =>
        let ndS := Syntax.mkNumLit (toString nd)
        `(tactic| cases k with
          | zero =>
            exact Tools.ShippingMachineChildRun.machineChild_of_real (nDecl := $ndS)
              $(n k "machineData") $(n k "machine_ok") $(n k "machine_body") (by decide) (by decide)
              rfl rfl
              ⟨_, rfl, rfl⟩ (by decide) $h
              (fun mc cc => $(n k "machine_closes") mc _ cc _) hy
          | succ k => $tac:tactic)
      | none =>
        `(tactic| cases k with
          | zero =>
            exact Tools.ShippingCallsGate.ChildFull.iface
              (Tools.ShippingCallsGate.childFull_of_real $h $(n k "gate_old") $(n k "gate_peel")
                $(n k "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
                (Tools.ShippingGateChild.bits_positions (by decide)) hy)
          | succ k => $tac:tactic)
  -- the number of input ports of each call's child
  let mut nkArr : Array Term := #[]
  for k in calls do
    nkArr := nkArr.push (← match machKid.get? k with
      | some nd =>
        let ndS := Syntax.mkNumLit (toString nd)
        `(((($(n k "machineData")).shape.binders.take $ndS).filter fun x => x.2 != .domain).length)
      | none => `((($(n k "gateBinders")).filter fun x => x.2 != .domain).length))
  let kbs ← `([$nkArr,*])
  let nDecl := Syntax.mkNumLit (toString (nDecl?.getD r.nDecl))
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $binders* :
        Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $cq ($data).shape :=
      Tools.ShippingCallsGate.machineClosesAt_of_gateKids (nDecl := $nDecl) $data
        $(n c "machine_ok") $(n c "machine_body") (by decide) (by decide)
        (fun k => List.getD $kbs k 0)
        (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tac:tactic)
        (by decide) $hnames $hparent $hfresh))
  let msgs := (← get).messages.toList.drop before
  if msgs.any (·.severity == .error) || !(← getEnv).contains name then
    let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    throwError "the generated proof fails: {errs.take 2}"
  liftTermElabM (auditClosesAt c name)
  return name

/-- `c.machine_closes_at`, generated if it is not there (an existing one is
audited: a theorem of the right statement, standard axioms). On ANY failure —
a refused shape, a generated proof that does not check, a declaration the
error recovery added, a failed audit — the environment and the message log
are restored to what they were, and the error is thrown: nothing is left. -/
def closesAtTheorem (c : Name) (nDecl? : Option Nat := none) : CommandElabM Name := do
  let name := c ++ `machine_closes_at
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let restore : CommandElabM Unit := do
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
  if (← getEnv).contains name then
    -- an existing declaration of that name is NOT trusted: it must be a
    -- theorem whose statement is the one generated now (regenerated under a
    -- scratch name, then dropped), on standard axioms
    let expected ← try
        let scratch := c ++ `machine_closes_at_expected
        discard <| withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
          (closesAtCore c nDecl? scratch)
        let t := (← getConstInfo scratch).type
        restore
        pure t
      catch ex =>
        restore
        throwError "{name} exists, and its statement cannot be regenerated: {ex.toMessageData}"
    liftTermElabM do
      let some (.thmInfo info) := (← getEnv).find? name | throwError "{name} exists and is not a theorem"
      unless ← isDefEq info.type expected do
        throwError "{name} exists with another statement than the generated one"
      standardAxioms name
    return name
  try
    withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) (closesAtCore c nDecl?)
  catch ex =>
    restore
    throwError "{c}: machine_closes_at was not generated: {ex.toMessageData}"

/-- The endpoint `thm` of `c` with its `MachineClosesAt` premise about `c`
replaced by the premises of `c.machine_closes_at` (in the same contexts):
added as `newName`. `false` where `thm` has no such premise. -/
def closeEndpointAt (c cl thm newName : Name) : MetaM Bool := do
  let info ← getConstInfo thm
  let clT := (← getConstInfo cl).type
  -- the statement and proof of the closed endpoint, from `thm` and `cl`
  let value? ← forallTelescope info.type fun xs _ => do
    let mut idx? : Option Nat := none
    for i in [0:xs.size] do
      let t ← instantiateMVars (← inferType xs[i]!)
      if t.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && t.getArg! 4 == toExpr c then
        idx? := some i
    let some idx := idx? | return none
    let t ← instantiateMVars (← inferType xs[idx]!)
    let ctx := t.getAppArgs.extract 0 4
    forallTelescope (← instantiateForall clT ctx) fun hs _ => do
      let body := (mkAppN (mkConst thm (info.levelParams.map mkLevelParam)) xs).replaceFVars
        #[xs[idx]!] #[mkAppN (mkConst cl) (ctx ++ hs)]
      return some (← mkLambdaFVars (xs.extract 0 idx ++ hs ++ xs.extract (idx + 1) xs.size) body)
  let some value := value? | return false
  let type ← inferType value
  if (type.find? fun e =>
      e.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && e.getArg! 4 == toExpr c).isSome then
    throwError "{newName}: the closed statement still asks MachineClosesAt of {c}"
  if (← getEnv).contains newName then
    -- an existing declaration of that name is NOT trusted: it must be a
    -- theorem of exactly the statement built here, on standard axioms
    let some (.thmInfo ni) := (← getEnv).find? newName
      | throwError "{newName} exists and is not a theorem"
    unless ni.levelParams == info.levelParams && (← isDefEq ni.type type) do
      throwError "{newName} exists with another statement than {thm} closed by {cl}"
    standardAxioms newName
    return true
  let saved ← getEnv
  try
    withOptions (fun o => Lean.Elab.async.set o false) do
      addDecl (.thmDecl { name := newName, levelParams := info.levelParams, type, value })
    standardAxioms newName
    return true
  catch ex =>
    setEnv saved
    throw ex

/-- `#machine_closes_at f` adds `f.machine_closes_at` and, for each endpoint
of `f` asking `MachineClosesAt`, its `_closed` form. -/
elab "#machine_closes_at " d:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let cl ← closesAtTheorem c
  let mut made := #[cl]
  -- the endpoints asking `MachineClosesAt` of `c`: the hierarchical heads and
  -- the depth heads at the depths generated so far
  let depthNames := (List.range 8).flatMap fun n =>
    [Name.mkSimple s!"machine_design_svNR{n}", Name.mkSimple s!"machine_ships_hierNR{n}"]
  for s in [`machine_design_svHR, `machine_ships_hierHR, `machine_composedRA] ++ depthNames do
    if (← getEnv).contains (c ++ s) then
      let nn := Tools.ShippingMachineClosesGen.closedName (c ++ s)
      if ← liftTermElabM (closeEndpointAt c cl (c ++ s) nn) then made := made.push nn
  logInfo m!"{made}: MachineClosesAt derived (one-output calls of gate / slotless machine children, or the general closing over machine children without calls); premises: the children's reflection and name conditions"

end Tools.ShippingMachineClosesAtGen
