import Tools.ShippingCallsKidsS
import Tools.ShippingChildIfaceGen

/-! # `#machine_closes_shared f`: the closing RELATIVE to the end cache, for callees that may share a descendant

For a machine `f` under the general closing, generates

    f.closes_shared : (reflections of the descendants) →
      Tools.ShippingCallsKidsS.MachineClosesAtS mctx mref cctx cref f f.machineData.shape
        (f.machineData.shape.insts.map (·.1))

by `Tools.ShippingCallsKidsS.machineClosesAtS_of_kids`, each callee read by
the interface term of the BUILT generator (`Tools.ShippingChildIfaceGen.ifaceDeep`:
`k.iface_deep` for a callee with calls, the leaf interface otherwise).

THIS IS NOT `MachineClosesAt`. `MachineClosesAtS` has one more antecedent
(the run's end world satisfies `CacheAgrees` over the callees) and no
endpoint accepts it. What the command shows on a declaration: every
hypothesis of the general closing OTHER than the disjointness `hdisjD` of
`machineClosesAt_of_kidsD` is decided on its data, with reflections as the
only premises. It also LOGS, for every pair of entries of different
declarations, whether `hdisjD` would hold (by the structural name test), so
the pairs that share a descendant are in the build log.

Unlike `#machine_closes_deep` it never turns a name condition into a
premise: when one is not decided by the candidate test it throws.

WRITTEN, NOT BUILT (par/a-17). -/
namespace Tools.ShippingCallsKidsSGen
open Lean Meta Elab Command
open Tools.ShippingChildIfaceGen (Prem Node addPrems mangle n check ifaceDeep)

/-- `f.closes_shared`; returns its premises and the log of the entry pairs. -/
def closesShared (c : Name) : CommandElabM (Array Prem × String) := do
  let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine c
  let calls := r.shape.insts.map (·.1)
  let kids := calls.eraseDups
  let data := n c "machineData"
  let cq : Term := quote c
  let name := c ++ `closes_shared
  if r.shape.instFields.isEmpty then
    throwError "{c}: instFields = [] — the one-output closing, not the general one"
  if calls.isEmpty then throwError "{c}: no call entry"
  let mut prems : Array Prem := #[]
  let mut nodes : Std.HashMap Name Node := {}
  for k in kids do
    let nd ← ifaceDeep k
    if nd.isGate then throwError "{c}: a gate child ({k}) directly under the general closing"
    nodes := nodes.insert k nd
    prems := addPrems prems nd.prems
  for p in prems do
    if p.refl.isNone then
      throwError "{c}: a callee's interface has a premise that is not a reflection ({p.name})"
  unless kids.all (fun a => kids.all fun b => a == b || Tools.ShippingNameSep.sepB a b) do
    throwError "{c}: two callees are not separated by the candidate test"
  unless kids.all (fun k => Tools.ShippingNameSep.sepB k c) do
    throwError "{c}: a callee is not separated from the parent by the candidate test"
  unless r.shape.layout.outs.all (fun o => o.name.toList.head? != some 'i') do
    throwError "{c}: an output whose name starts with 'i' (instance-name freshness not decided)"
  let declsAt (k : Name) : List Name := (nodes.get! k).decls
  let sepAll (a : Name) (L : List Name) : Bool := L.all fun b => Tools.ShippingNameSep.sepB a b
  unless calls.all (fun k => sepAll c (declsAt k) && sepAll k (declsAt k)) do
    throwError "{c}: the parent or a callee is not separated from that callee's descendants"
  -- the pairs of entries of different declarations: would the disjointness hold?
  let mut pairs : Array String := #[]
  let mut shared : Nat := 0
  for i in [0:calls.length] do
    for j in [0:calls.length] do
      let k := calls[i]!
      let k' := calls[j]!
      if k != k' then
        let c1 := sepAll k (declsAt k')
        let common := (declsAt k).filter fun a => (declsAt k').contains a
        let c2 := (declsAt k).all fun a => sepAll a (declsAt k')
        unless c1 && c2 do shared := shared + 1
        let dk := declsAt k
        let dk' := declsAt k'
        let isDesc := dk'.contains k
        pairs := pairs.push s!"entries {i} ({k}) / {j} ({k'}): descendants {dk} / {dk'}; first conjunct ({k} prints differently from every descendant of {k'}) = {c1}; second conjunct (no printed name under both) = {c2}; declarations under both: {common}; is {k} a descendant of {k'}: {isDesc}"
  let hnames ← `(Tools.ShippingNameSep.Enc.hnames_of _ (by decide))
  let hparentT ← `(Tools.ShippingNameSep.Enc.hparent_of _ _ (by decide))
  let hfresh ← `(fun gi c _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
    ((by decide : ∀ o ∈ ($data).shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi
    (Sparkle.IR.ModuleName.ofDecl c.1))
  let nkArr := calls.toArray.map fun k => (nodes.get! k).nArgs
  let outArr := calls.toArray.map fun k => (nodes.get! k).outs
  let dArr := calls.toArray.map fun k => (nodes.get! k).declsT
  let kbs ← `([$nkArr,*])
  let kos ← `(([$outArr,*] : List (List String)))
  let kds ← `(([$dArr,*] : List (List Lean.Name)))
  let nkF ← `(fun k => List.getD $kbs k 0)
  let outF ← `(fun k => List.getD $kos k [])
  let nmF ← `(fun k => (List.getD $kds k []).map fun n => Sparkle.IR.ModuleName.ofDecl n)
  let hpD ← `(fun k hk => Tools.ShippingNameSep.Enc.not_mem_map_of _ _
    ((by decide : ∀ (k : Nat), k < ($data).shape.insts.length →
      ((List.getD $kds k []).all fun c' =>
        Tools.ShippingNameSep.sep ($cq : Lean.Name) c') = true) k hk))
  let hsD ← `(fun k hk => Tools.ShippingNameSep.Enc.not_mem_map_of _ _
    ((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
      ((List.getD $kds k []).all fun c' =>
        Tools.ShippingNameSep.sep (($data).shape.insts[k]).1 c') = true) k hk))
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
  if (← getEnv).contains name then throwError "{name}: exists already"
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $(prems.map (·.binder))* :
        Tools.ShippingCallsKidsS.MachineClosesAtS mctx mref cctx cref $cq ($data).shape
          ((($data).shape.insts).map (·.1)) :=
      Tools.ShippingCallsKidsS.machineClosesAtS_of_kids (nDecl := $nDecl) $data
        $(n c "machine_ok") $(n c "machine_body") (by decide) (by decide) (by decide) (by decide)
        (by decide)
        $nkF $outF $nmF
        (by decide)
        (by
          intro k hk y hy
          have hk' : k < $nCalls := hk
          $tac:tactic)
        (by decide) (by decide) (by decide) $hnames $hparentT $hfresh $hpD $hsD))
  check before name
  let desc := kids.map fun k => (k, declsAt k)
  let log := s!"{c}: nDecl={r.nDecl}; call entries {calls}; instFields {r.shape.instFields}; descendants per callee {desc}; entry pairs of different declarations for which hdisjD of machineClosesAt_of_kidsD is NOT decided by the candidate test: {shared} of {pairs.size}\n" ++
    String.intercalate "\n" pairs.toList
  return (prems, log)

/-- `#machine_closes_shared f`: `f.closes_shared` (see the file header: it is
`MachineClosesAtS`, NOT `MachineClosesAt`). -/
elab "#machine_closes_shared " d:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let (prems, log) ← withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (closesShared c)
  let nm := c ++ `closes_shared
  logInfo m!"CLOSES SHARED {nm}: MachineClosesAtS (the closing RELATIVE to CacheAgrees of the run's end world over the callees — NOT MachineClosesAt); {prems.size} premises, all reflections: {prems.map (·.name)}\n{log}"

end Tools.ShippingCallsKidsSGen
