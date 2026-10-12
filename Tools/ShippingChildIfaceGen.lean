import Tools.ShippingKidsChildIface
import Tools.ShippingMachineClosesAtGen

/-! # Generating closings over children that have calls (`#machine_closes_deep`)

For a machine `f` closed by the general closing whose machine children may
have calls of their own (to any depth):

* `f.closes_deep : … → MachineClosesAt mctx mref cctx cref f f.machineData.shape`
  (`machineClosesAt_of_kidsD`), and for every machine descendant `c` that has
  calls, `c.closes_deep` and
  `c.iface_deep : … → ∀ y, RealChild mref cref c y → ChildIfaceD c … y.1 y.2`
  (`kidsChild_of_real`);
* the depth endpoints of `f` with the closing premise replaced (`_closed`).

Premises of the generated theorems: the reflection of every descendant
(`MachineDefines` / `EntryDefines`, at one context — they do not depend on
it), and NAME SEPARATION (N1, obligations: the kernel does not evaluate
`Name.toString`): per node, its children print differently from it, from
each other and from their descendants. The data conditions are decided by
the kernel. Refused with the reason: a gate child directly under a general
closing, a memory child, a slotless child with calls, a child whose own
closing is not derived. -/
namespace Tools.ShippingChildIfaceGen
open Lean Meta Elab Command
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry

abbrev Binder := TSyntax ``Lean.Parser.Term.bracketedBinder

/-- A premise of a generated theorem: its fixed name, its binder, and whether
it is a reflection (`some true`: of a machine, `some false`: of a gate). -/
structure Prem where
  name : Name
  binder : Binder
  refl : Option Bool := none
  deriving Inhabited

/-- What is known of a node once its theorems exist. -/
structure Node where
  prems : Array Prem
  nArgs : Term
  outs : Term
  names : Term
  iface : Term      -- a term of `∀ y, RealChild mref cref c y → ChildIfaceD …`, in the premises' scope
  isGate : Bool := false
  /-- The descendants' declarations (the term, and its value at generation). -/
  declsT : Term
  decls : List Name := []
  deriving Inhabited

def mangle (k : Name) : String := (k.toString.replace "." "_").replace "'" "_"

def addPrems (a b : Array Prem) : Array Prem :=
  b.foldl (fun acc p => if acc.any (·.name == p.name) then acc else acc.push p) a

def n (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

/-- The arguments of a generated theorem at OTHER contexts: reflections moved
(`.ctx`), name premises as they are. -/
def argsAt (ps : Array Prem) : CommandElabM (Array Term) :=
  ps.mapM fun p => do
    let i := mkIdent p.name
    match p.refl with
    | some true => `(Tools.ShippingReflectCtx.MachineDefines.ctx $i)
    | some false => `(Tools.ShippingReflectCtx.EntryDefines.ctx $i)
    | none => `($i)

def check (before : Nat) (name : Name) : CommandElabM Unit := do
  let msgs := (← get).messages.toList.drop before
  if msgs.any (·.severity == .error) || !(← getEnv).contains name then
    let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
    throwError "{name}: the generated proof fails: {errs.take 2}"
  Tools.ShippingMachineClosesAtGen.standardAxioms name |> liftCoreM

mutual

/-- The closing of a machine with calls: `c.closes_deep`; returns its premises. -/
partial def closesDeep (c : Name) : CommandElabM (Array Prem) := do
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine c
  let calls := r.shape.insts.map (·.1)
  let kids := calls.eraseDups
  let data := n c "machineData"
  let cq : Term := quote c
  let name := c ++ `closes_deep
  let tag := mangle c
  if r.shape.instFields.isEmpty then
    -- one-output calls: the existing generator's theorem, under this file's premise names
    let cl ← Tools.ShippingMachineClosesAtGen.closesAtTheorem c
    let info ← getConstInfo cl
    let mut prems : Array Prem := #[]
    let mut args : Array Term := #[]
    -- its premises, in order: the kids' reflections, then the name premises
    let tys ← liftTermElabM <| forallTelescope info.type fun xs _ => do
      (xs.extract 4 xs.size).mapM fun x => do instantiateMVars (← inferType x)
    let mut j := 0
    let mut q := 0
    for t in tys do
      if t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
          t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines then
        let k := kids[j]!
        j := j + 1
        let isM := t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines
        let pn := Name.mkSimple s!"hR_{mangle k}"
        let kq : Term := quote k
        let b ← if isM then `(bracketedBinder|
            ($(mkIdent pn) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
              ($(n k "machineData")).shape))
          else `(bracketedBinder|
            ($(mkIdent pn) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $kq
              $(n k "gateValue")))
        prems := addPrems prems #[{ name := pn, binder := b, refl := some isM }]
        args := args.push (mkIdent pn)
      else
        -- a name premise: closed (no context variable), stated by its type
        if t.hasFVar then throwError "{cl}: a premise that depends on the contexts"
        let pn := Name.mkSimple s!"hN_{tag}_{q}"
        q := q + 1
        let ts ← liftTermElabM <| PrettyPrinter.delab t
        let b ← `(bracketedBinder| ($(mkIdent pn) : $ts))
        prems := prems.push { name := pn, binder := b }
        args := args.push (mkIdent pn)
    unless (← getEnv).contains name do
      let before := (← get).messages.toList.length
      elabCommand (← `(command|
        theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
            {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
            {cref : ST.Ref IO.RealWorld Lean.Core.State} $(prems.map (·.binder))* :
            Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $cq ($data).shape :=
          $(mkIdent (`_root_ ++ cl)) $args*))
      check before name
    return prems
  -- the general closing: every child by its interface
  let mut prems : Array Prem := #[]
  let mut nodes : Std.HashMap Name Node := {}
  for k in kids do
    let nd ← ifaceDeep k
    if nd.isGate then throwError "{c}: a gate child ({k}) directly under the general closing (not derived)"
    nodes := nodes.insert k nd
    prems := addPrems prems nd.prems
  let k0 : Term := quote kids[0]!
  let hnames ← if kids.length == 1 then
      `(fun c hc c' hc' _ =>
        ((by decide : ∀ c ∈ ($data).shape.insts.map (·.1), c = $k0) c hc).trans
          ((by decide : ∀ c ∈ ($data).shape.insts.map (·.1), c = $k0) c' hc').symm)
    else if kids.all (fun a => kids.all fun b => a == b || Tools.ShippingNameSep.sepB a b) then
      `(Tools.ShippingNameSep.hnames_of _ (by decide))
    else do
      let pn := Name.mkSimple s!"hN_{tag}_names"
      prems := prems.push { name := pn, binder := ← `(bracketedBinder|
        ($(mkIdent pn) : ∀ c ∈ ($data).shape.insts.map (·.1),
          ∀ c' ∈ ($data).shape.insts.map (·.1), c.toString = c'.toString → c = c')) }
      `($(mkIdent pn))
  let pparent := Name.mkSimple s!"hN_{tag}_parent"
  let hparentT : Term ← if kids.all (fun k => Tools.ShippingNameSep.sepB k c) then
      `(Tools.ShippingNameSep.hparent_of _ _ (by decide))
    else do
      prems := prems.push { name := pparent, binder := ← `(bracketedBinder|
        ($(mkIdent pparent) : ∀ c ∈ ($data).shape.insts,
          c.1.toString ≠ ($cq : Lean.Name).toString)) }
      `($(mkIdent pparent))
  let hfresh ← if r.shape.layout.outs.all (fun o => o.name.toList.head? != some 'i') then
      `(fun gi c _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
        ((by decide : ∀ o ∈ ($data).shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi
        c.1.toString)
    else do
      let pn := Name.mkSimple s!"hN_{tag}_fresh"
      prems := prems.push { name := pn, binder := ← `(bracketedBinder|
        ($(mkIdent pn) : ∀ (gi : Nat), ∀ c ∈ ($data).shape.insts, ∀ o ∈ ($data).shape.layout.outs,
          o.name ≠ s!"inst{gi}_{c.1.toString}")) }
      `($(mkIdent pn))
  let nkArr := calls.toArray.map fun k => (nodes.get! k).nArgs
  let outArr := calls.toArray.map fun k => (nodes.get! k).outs
  let dArr := calls.toArray.map fun k => (nodes.get! k).declsT
  let kbs ← `([$nkArr,*])
  let kos ← `(([$outArr,*] : List (List String)))
  let kds ← `(([$dArr,*] : List (List Lean.Name)))
  let nkF ← `(fun k => List.getD $kbs k 0)
  let outF ← `(fun k => List.getD $kos k [])
  -- the descendants' printed names: the descendants' declarations, printed
  let nmF ← `(fun k => (List.getD $kds k []).map fun n => n.toString)
  let declsAt (k : Name) : List Name := (nodes.get! k).decls
  let sepAll (a : Name) (L : List Name) : Bool := L.all fun b => Tools.ShippingNameSep.sepB a b
  let namesSep := calls.all (fun k => sepAll c (declsAt k) && sepAll k (declsAt k)) &&
    calls.all fun k => calls.all fun k' => k == k' ||
      (sepAll k (declsAt k') && (declsAt k).all fun a => sepAll a (declsAt k'))
  -- the descendants' names: nothing to ask when no child has a descendant
  let allLeaf ← kids.allM fun k => do
    let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
    pure cr.shape.insts.isEmpty
  let (hpD, hsD, hdD) ← if allLeaf then
      pure (← `(by decide), ← `(by decide), ← `(by decide))
    else if namesSep then
      -- separated by the names' candidate renderings (`Tools.ShippingNameSep`)
      pure (
        ← `(fun k hk => Tools.ShippingNameSep.not_mem_map_of _ _
          ((by decide : ∀ (k : Nat), k < ($data).shape.insts.length →
            ((List.getD $kds k []).all fun c' =>
              Tools.ShippingNameSep.sepB ($cq : Lean.Name) c') = true) k hk)),
        ← `(fun k hk => Tools.ShippingNameSep.not_mem_map_of _ _
          ((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
            ((List.getD $kds k []).all fun c' =>
              Tools.ShippingNameSep.sepB (($data).shape.insts[k]).1 c') = true) k hk)),
        ← `(fun k hk k' hk' hne =>
          ⟨Tools.ShippingNameSep.not_mem_map_of _ _
            ((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length) (k' : Nat)
              (hk' : k' < ($data).shape.insts.length),
              (($data).shape.insts[k]).1 ≠ (($data).shape.insts[k']).1 →
              ((List.getD $kds k' []).all fun c' =>
                Tools.ShippingNameSep.sepB (($data).shape.insts[k]).1 c') = true) k hk k' hk' hne),
           Tools.ShippingNameSep.disjoint_map_of _ _
            ((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length) (k' : Nat)
              (hk' : k' < ($data).shape.insts.length),
              (($data).shape.insts[k]).1 ≠ (($data).shape.insts[k']).1 →
              ((List.getD $kds k []).all fun a => (List.getD $kds k' []).all fun b =>
                Tools.ShippingNameSep.sepB a b) = true) k hk k' hk' hne)⟩))
    else do
      let p1 := Name.mkSimple s!"hN_{tag}_parentD"
      let p2 := Name.mkSimple s!"hN_{tag}_selfD"
      let p3 := Name.mkSimple s!"hN_{tag}_disjD"
      prems := prems.push { name := p1, binder := ← `(bracketedBinder|
        ($(mkIdent p1) : ∀ (k : Nat), k < ($data).shape.insts.length →
          ($cq : Lean.Name).toString ∉ ($nmF) k)) }
      prems := prems.push { name := p2, binder := ← `(bracketedBinder|
        ($(mkIdent p2) : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          (($data).shape.insts[k]).1.toString ∉ ($nmF) k)) }
      prems := prems.push { name := p3, binder := ← `(bracketedBinder|
        ($(mkIdent p3) : ∀ (k : Nat) (hk : k < ($data).shape.insts.length) (k' : Nat)
          (hk' : k' < ($data).shape.insts.length),
          (($data).shape.insts[k]).1 ≠ (($data).shape.insts[k']).1 →
          (($data).shape.insts[k]).1.toString ∉ ($nmF) k' ∧
            ∀ x ∈ ($nmF) k, x ∉ ($nmF) k')) }
      pure (← `($(mkIdent p1)), ← `($(mkIdent p2)), ← `($(mkIdent p3)))
  let nCalls := Syntax.mkNumLit (toString calls.length)
  let mut tac ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let k := calls[i]!
    let f := (nodes.get! k).iface
    tac ← `(tactic| cases k with
      | zero => exact $f y hy
      | succ k => $tac:tactic)
  let nDecl := Syntax.mkNumLit (toString r.nDecl)
  unless (← getEnv).contains name do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} $(prems.map (·.binder))* :
          Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $cq ($data).shape :=
        Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD (nDecl := $nDecl) $data
          $(n c "machine_ok") $(n c "machine_body") (by decide) (by decide) (by decide) (by decide)
          (by decide)
          $nkF $outF $nmF
          (by decide)
          (by
            intro k hk y hy
            have hk' : k < $nCalls := hk
            $tac:tactic)
          (by decide) (by decide) (by decide) $hnames $hparentT $hfresh $hpD $hsD $hdD))
    check before name
  return prems

/-- The interface of a child, as a term in the scope of its premises. -/
partial def ifaceDeep (k : Name) : CommandElabM Node := do
  let kq : Term := quote k
  if (Sparkle.Compiler.MachMemory.memChild? k).isSome then
    throwError "{k}: a memory child (not derived here)"
  if (← getEnv).contains (k ++ `gate_peel) then
    -- a gate child: only usable as a child's child (`KidNames`)
    let pn := Name.mkSimple s!"hR_{mangle k}"
    let b ← `(bracketedBinder|
      ($(mkIdent pn) : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref $kq
        $(n k "gateValue")))
    let f ← `(fun y hy => Tools.ShippingCallsGate.ChildFull.iface
      (Tools.ShippingCallsGate.childFull_of_real $(mkIdent pn) $(n k "gate_old") $(n k "gate_peel")
        $(n k "gate_wf") (Tools.ShippingGateChild.bool_positions (by decide))
        (Tools.ShippingGateChild.bits_positions (by decide)) hy))
    return { prems := #[{ name := pn, binder := b, refl := some false }], nArgs := ← `(0),
             outs := ← `(([] : List String)),
             names := ← `((([] : List Lean.Name).map fun n => n.toString)), iface := f,
             declsT := ← `(([] : List Lean.Name)), isGate := true }
  unless (← getEnv).contains (k ++ `machineData) && (← getEnv).contains (k ++ `machine_ok) &&
      (← getEnv).contains (k ++ `machine_body) do
    throwError "{k} is neither a generated gate child nor a machine with an endpoint"
  let kd := n k "machineData"
  let cr ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
  let pn := Name.mkSimple s!"hR_{mangle k}"
  let self : Prem := { name := pn, refl := some true, binder := ← `(bracketedBinder|
    ($(mkIdent pn) : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq
      ($kd).shape)) }
  let outs ← `((($kd).shape.layout.outs.map (·.name)))
  if cr.shape.insts.isEmpty then
    unless (← liftTermElabM <| Tools.ShippingMachineClosesGen.closesTheorem? k).isSome do
      throwError "{k}: its own closing is not derived ({k}.machine_closes)"
    let f ← `(fun y hy => Tools.ShippingCallsKidsD.ChildIfaceG.toD
      (Tools.ShippingSeqChildIface.seqChild_of_real $kd $(n k "machine_ok") $(n k "machine_body")
        rfl (by decide) $(mkIdent pn) (fun mc cc => $(n k "machine_closes") mc _ cc _) hy))
    return { prems := #[self], outs,
             names := ← `((([] : List Lean.Name).map fun n => n.toString)), iface := f,
             declsT := ← `(([] : List Lean.Name)),
             nArgs := ← `(((($kd).shape.binders.take (($kd).shape.binders.length -
               ($kd).shape.layout.slots.length - ($kd).shape.layout.lets)).filter
                 fun x => x.2 != .domain).length) }
  -- a machine child with calls
  if cr.shape.layout.slots.isEmpty then
    throwError "{k}: a slotless child with calls (not derived here)"
  let closePrems ← closesDeep k
  let calls := cr.shape.insts.map (·.1)
  let kids := calls.eraseDups
  let mut prems : Array Prem := addPrems #[self] closePrems
  let mut sub : Std.HashMap Name Node := {}
  for g in kids do
    let nd ← ifaceDeep g
    sub := sub.insert g nd
    prems := addPrems prems nd.prems
  let dArr := calls.toArray.map fun g => (sub.get! g).declsT
  let kds ← `(([$dArr,*] : List (List Lean.Name)))
  let dF ← `(fun k => List.getD $kds k [])
  let nmF ← `(fun k => (List.getD $kds k []).map fun n => n.toString)
  let declsT ← `(Tools.ShippingKidsChildIface.declsOf $kd $dF)
  let names ← `(($declsT).map fun n => n.toString)
  let decls : List Name := (kids ++ kids.flatMap fun g => (sub.get! g).decls).eraseDups
  let pself := Name.mkSimple s!"hN_{mangle k}_self"
  -- the declaration prints differently from its descendants: by the candidate
  -- renderings when they separate, else a premise
  let hselfT : Term ← if decls.all (fun g => Tools.ShippingNameSep.sepB k g) then
      `((by
        rw [Tools.ShippingKidsChildIface.namesOf_map $kd $dF]
        exact Tools.ShippingNameSep.not_mem_map_of _ _ (by decide)))
    else do
      prems := prems.push { name := pself, binder := ← `(bracketedBinder|
        ($(mkIdent pself) : ($kq : Lean.Name).toString ∉
          Tools.ShippingKidsChildIface.namesOf $kd $nmF)) }
      `($(mkIdent pself))
  let nCalls := Syntax.mkNumLit (toString calls.length)
  let mut tac ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:calls.length] do
    let i := calls.length - 1 - i'
    let g := calls[i]!
    let nd := sub.get! g
    let f := nd.iface
    tac ← if nd.isGate then
        `(tactic| cases k with
          | zero => exact Tools.ShippingKidsChildIface.kid_of_iface ($f y hy)
          | succ k => $tac:tactic)
      else
        `(tactic| cases k with
          | zero => exact Tools.ShippingCallsKidsD.ChildIfaceD.kid ($f y hy)
          | succ k => $tac:tactic)
  let kD := Syntax.mkNumLit (toString cr.nDecl)
  let name := k ++ `iface_deep
  let closeArgs ← argsAt closePrems
  let nArgs ← `(((($kd).bsIn.take $kD).filter (fun b => b.2 != .domain)).length)
  unless (← getEnv).contains name do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
          {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
          {cref : ST.Ref IO.RealWorld Lean.Core.State} $(prems.map (·.binder))* :
          ∀ (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
            Tools.ShippingChildInv.RealChild mref cref $kq y →
            Tools.ShippingCallsKidsD.ChildIfaceD $kq $nArgs $outs $names y.1 y.2 :=
        fun y hy => by
          rw [← Tools.ShippingKidsChildIface.namesOf_map $kd $dF]
          exact Tools.ShippingKidsChildIface.kidsChild_of_real (nDecl := $kD) $kd
            $(n k "machine_ok") $(n k "machine_body") (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) $kD (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) $nmF (by decide)
            (by
              intro k hk y hy
              have hk' : k < $nCalls := hk
              $tac:tactic)
            $hselfT $(mkIdent pn)
            (fun mc cc _ => @$(mkIdent (`_root_ ++ k ++ `closes_deep)) mc mref cc cref $closeArgs*)
            hy))
    check before name
  let args := prems.map fun p => (mkIdent p.name : Term)
  let f ← `($(mkIdent (`_root_ ++ name)) $args*)
  return { prems, nArgs, outs, names, iface := f, declsT, decls }

end

/-- `#machine_closes_deep f`: `f.closes_deep` and the closed depth endpoints. -/
elab "#machine_closes_deep " d:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  try
    discard <| withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
      (closesDeep c)
  catch ex =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    throwError "{c}: closes_deep was not generated: {ex.toMessageData}"
  let cl := c ++ `closes_deep
  let mut made := #[cl]
  for i in [0:8] do
    for s in [Name.mkSimple s!"machine_design_svNR{i}", Name.mkSimple s!"machine_ships_hierNR{i}"] do
      if (← getEnv).contains (c ++ s) then
        let nn := Tools.ShippingMachineClosesGen.closedName (c ++ s)
        if ← liftTermElabM (Tools.ShippingMachineClosesAtGen.closeEndpointAt c cl (c ++ s) nn) then
          made := made.push nn
  logInfo m!"{made}: MachineClosesAt derived over children with calls; premises: the descendants' reflection and name separation"

end Tools.ShippingChildIfaceGen
