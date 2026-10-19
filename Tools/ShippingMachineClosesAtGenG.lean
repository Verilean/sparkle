import Tools.ShippingCallsSeqKids
import Tools.ShippingMachineClosesGen
import Tools.ShippingMachineCommand
import Tools.ShippingNameSep
import Tools.ShippingNameDischarge
import Tools.ShippingNameMode
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # Generating `f.machine_closes_at` for the general closing

For a machine `f` whose calls have several outputs or sequential children
(`instFields ≠ []`: the compiler closes them by `closeInstsGM`) and whose
children are machines WITHOUT calls of their own (`#machine_endpoint` run on
each, their own closing derived: `c.machine_closes`): the theorem

  `f.machine_closes_at : MachineDefines … c c.machineData.shape → … → MachineClosesAt mctx mref cctx cref f f.machineData.shape`

(`machineClosesAt_of_seqKids` at `f`'s data). Premises: the reflection of
each called declaration, and the NAME CONDITIONS as in the one-output
generator (round par/b-30: proved from the declaration names,
`Tools.ShippingNameDischarge`; a binder only where the condition on the
names is false; `shipping.nameCandidates` gives the previous proofs). The data conditions — the endpoint's checks, `letsAliasOk`, S3
(`callsOk`), the slots, no memory child, the argument counts, each entry's
field an output of its child, different fields within one call — are decided
by the kernel. Refused, with the reason: a child with calls of its own, a
memory child, a child that is not a machine with an endpoint. -/
namespace Tools.ShippingMachineClosesAtGenG
open Lean Meta Elab Command
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry

/-- The generation (no audit, no restore: the caller's). -/
def closesAtCoreG (c : Name) (nDecl? : Option Nat) (name : Name) : CommandElabM Name := do
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine c
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{c}: no call"
  let kids := calls.eraseDups
  -- origin dispatch (patched compiler): a memory child is an entry of memory ORIGIN
  if r.shape.instTagged.any (fun x => x.2.child?.isSome) then
    throwError "{c}: a memory child (not derived here)"
  for k in kids do
    unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
        (← getEnv).contains (k ++ `machine_body) do
      throwError "{c}: {k} is not a machine with an endpoint (#machine_endpoint)"
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    unless cr.shape.insts.isEmpty do
      throwError "{c}: the machine child {k} has calls of its own (not derived here: B3)"
    unless (← liftTermElabM <| Tools.ShippingMachineClosesGen.closesTheorem? k).isSome do
      throwError "{c}: the machine child {k}'s own closing is not derived ({k}.machine_closes)"
  let n (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)
  let data := n c "machineData"
  let cq : Term := quote c
  let hR (j : Nat) : Ident := mkIdent (Name.mkSimple s!"hR{j}")
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for j in [0:kids.length] do
    let k := kids[j]!
    let kq : Term := quote k
    binders := binders.push (← `(bracketedBinder|
      ($(hR j) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
        ($(n k "machineData")).shape)))
  let k0 : Term := quote kids[0]!
  -- the previous path (`Tools.ShippingNameSep`), on request only
  let oldNames := shipping.nameCandidates.get (← getOptions)
  let hnames ← if !oldNames then
      -- `ofDecl` is injective: no condition, whatever the names
      `(Tools.ShippingNameDischarge.names_inj _)
    else if kids.length == 1 then
      `(fun c hc c' hc' _ =>
        ((by decide : ∀ c ∈ ($data).shape.insts.map (·.1), c = $k0) c hc).trans
          ((by decide : ∀ c ∈ ($data).shape.insts.map (·.1), c = $k0) c' hc').symm)
    else if kids.all (fun a => kids.all fun b => a == b || Tools.ShippingNameSep.sepB a b) then
      -- different declarations print differently: decided on the names' candidate
      -- renderings (`Tools.ShippingNameSep`), `Name.toString` never evaluated
      `(Tools.ShippingNameSep.Enc.hnames_of _ (by decide))
    else do
      binders := binders.push (← `(bracketedBinder|
        (hnames : ∀ c ∈ ($data).shape.insts.map (·.1), ∀ c' ∈ ($data).shape.insts.map (·.1),
          (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')))
      `(hnames)
  -- no call prints as the parent: by the candidate renderings when they
  -- separate, else a premise
  let hparent : Term ← if !oldNames && kids.all (fun k => k != c) then
      -- no call entry is a call of the parent declaration: decided on the
      -- NAMES (`Name.beq`; nothing is rendered)
      `(Tools.ShippingNameDischarge.parent_ne _ _ (by decide))
    else if oldNames && kids.all (fun k => Tools.ShippingNameSep.sepB k c) then
      `(Tools.ShippingNameSep.Enc.hparent_of _ _ (by decide))
    else do
      binders := binders.push (← `(bracketedBinder|
        (hparent : ∀ c ∈ ($data).shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl ($cq : Lean.Name)))))
      `(hparent)
  let hfresh ← if r.shape.layout.outs.all (fun o => o.name.toList.head? != some 'i') then
      `(fun gi c _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
        ((by decide : ∀ o ∈ ($data).shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi
        (Sparkle.IR.ModuleName.ofDecl c.1))
    else do
      binders := binders.push (← `(bracketedBinder|
        (hfresh : ∀ (gi : Nat), ∀ c ∈ ($data).shape.insts, ∀ o ∈ ($data).shape.layout.outs,
          o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl c.1)}")))
      `(hfresh)
  -- each entry's child, read off its `RealChild` witness
  let nCalls := Syntax.mkNumLit (toString calls.length)
  let mut tac ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let h := hR (kids.idxOf k)
    tac ← `(tactic| cases k with
      | zero =>
        exact Tools.ShippingSeqChildIface.seqChild_of_real
          $(n k "machineData") $(n k "machine_ok") $(n k "machine_body") rfl (by decide) $h
          (fun mc cc => $(n k "machine_closes") mc _ cc _) hy
      | succ k => $tac:tactic)
  let mut nkArr : Array Term := #[]
  let mut outArr : Array Term := #[]
  for k in calls do
    let kd := n k "machineData"
    nkArr := nkArr.push (← `(((($kd).shape.binders.take (($kd).shape.binders.length -
      ($kd).shape.layout.slots.length - ($kd).shape.layout.lets)).filter
        fun x => x.2 != .domain).length))
    outArr := outArr.push (← `((($kd).shape.layout.outs.map (·.name))))
  let kbs ← `([$nkArr,*])
  let kos ← `([$outArr,*])
  let nDecl := Syntax.mkNumLit (toString (nDecl?.getD r.nDecl))
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $binders* :
        Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $cq ($data).shape :=
      Tools.ShippingCallsSeqKids.machineClosesAt_of_seqKids (nDecl := $nDecl) $data
        $(n c "machine_ok") $(n c "machine_body") (by decide) (by decide) (by decide) (by decide)
        (by decide)
        (fun k => List.getD $kbs k 0) (fun k => List.getD $kos k [])
        (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tac:tactic)
        (by decide) (by decide) (by decide) $hnames $hparent $hfresh))
  let msgs := (← get).messages.toList.drop before
  if msgs.any (·.severity == .error) || !(← getEnv).contains name then
    let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    throwError "the generated proof fails: {errs.take 2}"
  return name

end Tools.ShippingMachineClosesAtGenG
