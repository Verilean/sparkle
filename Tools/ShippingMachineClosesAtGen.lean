import Tools.ShippingCallsGate
import Tools.ShippingMachineClosesGen
import Tools.ShippingGateChildCommand

/-! # Generating `f.machine_closes_at`

For a machine `f` whose calls are one-output calls of gate children
(`#gate_child` run on each): the theorem

  `f.machine_closes_at : EntryDefines … c c.gateValue → … → MachineClosesAt mctx mref cctx cref f f.machineData.shape`

(`machineClosesAt_of_gateKids` at `f`'s data), and the endpoints of `f` that
ask `MachineClosesAt` with that premise replaced by the theorem's own
(`_closed`). The theorem's premises:

* the reflection of each called declaration (`EntryDefines`, already a
  premise of the endpoints);
* conditions on NAMES the kernel cannot evaluate (`Name.toString` does not
  reduce): no call names the parent; with several calls, the called
  declarations' names are distinct; and — only when an output port's name
  starts with `i` — no output port is named as an instance.

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

/-- `name` is a theorem concluding `MachineClosesAt … c c.machineData.shape`,
on standard axioms (so not through `sorry`). -/
def auditClosesAt (c name : Name) : MetaM Unit := do
  let some (.thmInfo info) := (← getEnv).find? name | throwError "{name}: not a theorem"
  let shape ← mkAppM ``MachineData.shape #[mkConst (c ++ `machineData)]
  let ok ← forallTelescope info.type fun _ body => do
    let body ← instantiateMVars body
    if body.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && body.getArg! 4 == toExpr c then
      isDefEq (body.getArg! 5) shape
    else pure false
  unless ok do throwError "{name}: does not conclude MachineClosesAt of {c}'s shape"
  standardAxioms name

/-- The generation itself; may leave declarations and messages behind on
failure (`closesAtTheorem` restores them). `nDecl?`: the number of declaration
binders to state the data check at, instead of the reader's. -/
def closesAtCore (c : Name) (nDecl? : Option Nat) : CommandElabM Name := do
  let name := c ++ `machine_closes_at
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine c
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{c}: no call"
  for k in calls do
    unless (← getEnv).contains (k ++ `gate_peel) do
      throwError "{c}: {k} is not a generated gate child (#gate_child)"
  let kids := calls.eraseDups
  -- two calls of one declaration: their modules are equal by the child cache,
  -- which `ChildrenReal` does not record — not derived, nothing is generated
  -- (the premise "distinct names" would be false)
  if kids.length != calls.length then
    throwError "{c}: two calls of one declaration (needs the cache's witness; not derived)"
  let n (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := n c "machineData"
  let cq : Term := quote c
  let hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [0:kids.length] do
    let k := kids[j]!
    let kq : Term := quote k
    binders := binders.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $kq $(n k "gateValue"))))
  -- the names
  let hnames ← if calls.length == 1 then
      `(List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil)
    else do
      binders := binders.push (← `(bracketedBinder|
        (hnames : (($data).shape.insts.map fun c => c.1.toString).Nodup)))
      `(hnames)
  binders := binders.push (← `(bracketedBinder|
    (hparent : ∀ c ∈ ($data).shape.insts, c.1.toString ≠ ($cq : Lean.Name).toString)))
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
    tac ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingCallsGate.childFull_of_real $h $(n k "gate_old") $(n k "gate_peel")
          $(n k "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)) hy
      | succ k => $tac:tactic)
  let kbArr : Array Term := (calls.map fun k => (n k "gateBinders" : Term)).toArray
  let kbs ← `([$kbArr,*])
  let nDecl := Syntax.mkNumLit (toString (nDecl?.getD r.nDecl))
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $binders* :
        Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $cq ($data).shape :=
      Tools.ShippingCallsGate.machineClosesAt_of_gateKids (nDecl := $nDecl) $data
        $(n c "machine_ok") $(n c "machine_body") (by decide) (by decide)
        (fun k => List.getD $kbs k [])
        (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tac:tactic)
        (by decide) $hnames hparent $hfresh))
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
  if (← getEnv).contains name then
    liftTermElabM (auditClosesAt c name)
    return name
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) (closesAtCore c nDecl?)
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    throwError "{c}: machine_closes_at was not generated: {ex.toMessageData}"

/-- The endpoint `thm` of `c` with its `MachineClosesAt` premise about `c`
replaced by the premises of `c.machine_closes_at` (in the same contexts):
added as `newName`. `false` where `thm` has no such premise. -/
def closeEndpointAt (c cl thm newName : Name) : MetaM Bool := do
  -- no `MachineClosesAt` premise about `c` is left, standard axioms
  let audit : MetaM Unit := do
    let some (.thmInfo ni) := (← getEnv).find? newName | throwError "{newName}: not a theorem"
    if (ni.type.find? fun e =>
        e.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && e.getArg! 4 == toExpr c).isSome then
      throwError "{newName}: still asks MachineClosesAt of {c}"
    standardAxioms newName
  if (← getEnv).contains newName then
    audit
    return true
  let saved ← getEnv
  try
   let info ← getConstInfo thm
   let clT := (← getConstInfo cl).type
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
   withOptions (fun o => Lean.Elab.async.set o false) do
     addDecl (.thmDecl { name := newName, levelParams := info.levelParams, type, value })
   audit
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
  for s in [`machine_design_svHR, `machine_ships_hierHR, `machine_composedRA] do
    if (← getEnv).contains (c ++ s) then
      let nn := Tools.ShippingMachineClosesGen.closedName (c ++ s)
      if ← liftTermElabM (closeEndpointAt c cl (c ++ s) nn) then made := made.push nn
  logInfo m!"{made}: MachineClosesAt derived (one-output calls of gate children); premises: the children's reflection and name conditions"

end Tools.ShippingMachineClosesAtGen
