import Lean.Elab.Command
import Tools.ShippingNoPortsDeepCommand
import Tools.ShippingNoPortsKidsCommand
import Tools.ShippingNoPortsMemCommand
import Tools.ShippingDesignCoverage
import Tools.ShippingBndOnly
import Tools.ShippingGenKidM
import Tools.ShippingKidFactsT
import Tools.ShippingLeafKidFacts
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingMemNamesP
import Tools.ShippingChildIfaceGen
import Tools.ShippingSVBridge
import Tools.ShippingReflectCtx
import Tools.ShippingMemKidTags

/-! # `#machine_no_ports_memkid f`: the check-free depth-1 endpoint of a parent of MEMORY MACHINES (round par/e-1)

WRITTEN, NOT BUILT.

A MEMORY MACHINE is a register machine whose own call entries are all memory
placeholders (`memCounterH` of `Tests/Compiler/MemDepthProbeTest.lean`). The
built check-free generators refuse a parent of one: `#machine_no_ports_kids`
("calls of its own under the GENERAL closing"), `#machine_no_ports_deep`
(no `closes_deep`; "a memory child"), `#machine_closes_at` /
`#machine_closes_deep` ("has calls of its own" / "a memory child"). The
endpoint was built BY HAND for one declaration
(`Tests/Compiler/MemParentClosesTest.lean`,
`Tests/Compiler/MemParentFreeTest.lean`; measured: CHECK-FREE OK). This
command generates the terms of those two files from the declaration's data.

## Scope (`scopeShape`, `scopeArtifacts`; everything else REFUSED with a reason)

`f` is a machine WITH a register under the GENERAL closing
(`instFields ≠ []`), without a memory entry of its own, and each distinct
callee `k` is one of

* **leaf**: a register machine without calls, with `k.machine_closes`;
* **memory machine**: a register machine under the general closing whose
  every call entry is the placeholder of ONE memory module `(cb, aw, dw)`,
  with `k.noPortsMem_data` and `k.noPortsMem_closes`
  (`#machine_no_ports_mem k`).

Refused in particular: a memory entry of `f` itself (`hnomem` of `kidsT_*`
and of `machineClosesAt_of_kidsD` is false); a callee that is also a
descendant of another callee (the `memGrand` / `mixDeep` shape: `hdisjD` is
false); two different memory-machine callees with the SAME memory module
(the module is a shared descendant: `hdisjD` is false); a callee with calls
that are not memory placeholders (the commands for those are
`#machine_no_ports_kids` / `#machine_no_ports_deep`; mixing is not
generated); a memory machine with several different placeholders; an output
of `f` starting with `i` (`hfresh` would be a premise). Depth 1 only.

## What must have run before

For a memory-machine callee `k`: `#machine_endpoint`, `#machine_composedT`,
`#machine_ships_hier`, `#machine_no_ports_mem`, `#machine_ext_joint`,
`#machine_composed_memNR k 0`, `#machine_seq_child_memNR k 0`. For `f`:
`#machine_endpoint`, then `#machine_design_svNR f 1` (or its sub-steps
`#machine_depth_core f 1`, `#machine_depth_ships f 1`): this command reads
`f.machine_ships_hierNR1`.

## Generated, in this order (GENERATOR names; an existing one is reused)

    k.machine_leafKid                    per leaf callee (the BUILT `leafKidTheorem`)
    k.machine_genKidM0, k.kid_factsT, k.iface_deepM      per memory-machine callee
    f.machine_kidIfaceM       ChildIfaceD of every call entry's callee (per-entry tables)
    f.machine_kidTagsM        the names below every entry are its tag's memory-module name
    f.machine_closes_at_memkid           MachineClosesAt f, from the callees' reflections
    f.machine_kidsT1          KidFactsT of every call entry's callee at depth 1
    f.machine_runFactsT1, _outsGT1, _maskedGT1, _designPT1      kidsT_* at f's data
    f.machine_design_noPortsNR1          the head at f.machine_ships_hierNR1's arguments
    f.machine_design_noPortsNR1_closed   premises: the run, MachineDefines of f and of every
                                         callee; ChildBnd under ∃ raw D; DesignSV conclusion

Nothing is written to `machine_closes_at` / `closes_deep` (a constant there
changes the boundary the depth generator states for a PARENT of `f`).

`f.machine_design_noPortsNR1` is the BUILT function
`Tools.ShippingNoPortsDeepCommand.endpointTermX f [] [] 1 …` — the function
`#machine_no_ports_deep` and `#noports_open_as` call — added by the BUILT
`addOrCompare`: when the constant EXISTS its statement must be `isDefEq` the
rebuilt one (an error otherwise; the rebuilt proof is kept as `…_regen`),
and the existing constant is the one the closed form is stated from. The
statement of the endpoint is the inferred type of the head's application: it
does not depend on which run theorems discharge the head's hypotheses.

The closed form: its STATEMENT by the built `bnd_only%`
(`Tools.ShippingBndOnly.bndOnlyType`); its proof gives the depth endpoint's
boundary its components by the tactic `memkid_boundary` below (a small
goal-directed search: a hypothesis, a conjunction, a binder, a callee's
closing by `k.noPortsMem_closes` / `k.machine_closes`, a reflection moved to
other contexts). The built `closedTerm` cannot be used: the kid's closing
sits INSIDE the boundary here (`Tools/ShippingMachineDepthCommandR.lean`
682), because the kid has no `machine_closes_at` / `closes_deep`.

## The statement check

After generation, an ERROR unless (the environment is put back on any
failure): the census's own re-check `Tools.ShippingDesignCoverage.recheck`
passes on the closed constant (every proposition binder and the antecedent
under the existentials ALLOWED, no checker / closing constant, `DesignSV`
mentioned), with exactly `2 + (number of distinct callees)` proposition
binders and ONE antecedent; standard axioms for every generated constant.

## Called / copied

CALLED (built, unchanged): `Tools.ShippingNoPortsCommand.leafKidTheorem`;
`Tools.ShippingNoPortsKidsCommand.Ctx` with `binders`, `hyps`, `hR`,
`outsOf`, `insOf`; `addOrCompare`, `regenName`;
`Tools.ShippingNoPortsDeepCommand.endpointTermX`;
`Tools.ShippingNoPortsMemCommand.memParamsOf`;
`Tools.ShippingShipsFreeCommand.checkMade`;
`Tools.ShippingMachineClosesGen.closedName`; `bnd_only%`;
`Tools.ShippingDesignCoverage.recheck`.

COPIED (the built ones cannot be called for this class):
`runTheorems` of `Tools/ShippingNoPortsKidsCommand.lean` 347-479 with
`kidsT_*` for `kids_*` (and the names for `kidsT_designCheck`); the
`cases k` tactic of `kidsTheoremD`; the application of
`machineClosesAt_of_kidsD` of `Tools.ShippingChildIfaceGen.closesDeep`
288-304 (`closesDeep` / `ifaceDeep` REFUSE a memory child, 311-312).

SCOPE of what a generated endpoint says: ONE declaration, depth 1, data
conditions decided per declaration (conditions, not reductions), the run,
the reflections and the runtime boundary `ChildBnd` as premises, `DesignSV`
of the module list — not the SV string, not `#sim`. -/
namespace Tools.ShippingNoPortsMemKidCommand
open Lean Meta Elab Command
open Tools.ShippingShipsFreeCommand (checkMade)
-- the whole namespace (not a name list): `Ctx.hR`, `Ctx.outsOf`, `Kind.leaf` are
-- used qualified by their type's name; used from it: Ctx, Kind, addOrCompare,
-- regenName
open Tools.ShippingNoPortsKidsCommand
open Tools.ShippingNoPortsMemCommand (memParamsOf)

/-- What a direct callee is, for this command. -/
inductive KindM where
  /-- a leaf register machine -/
  | leaf
  /-- a register machine (declared binders `nDecl`) whose every call entry
  is the placeholder of the memory module `(cb, aw, dw)` -/
  | memMach (nDecl : Nat) (cb : Bool) (aw dw : Nat)
  deriving Inhabited

/-- What the scope scan read. -/
structure ScopeM where
  nDecl : Nat
  /-- the call entries' callees, in the reader's order -/
  calls : List Name
  /-- the distinct callees with their kinds, in the order of their first entry -/
  kinds : List (Name × KindM)
  deriving Inhabited

namespace ScopeM

def kids (s : ScopeM) : List Name := s.kinds.map (·.1)

def kindOf (s : ScopeM) (k : Name) : KindM :=
  match s.kinds.find? (·.1 == k) with
  | some (_, kd) => kd
  | none => KindM.leaf

end ScopeM

private def nm (d : Name) (s : String) : Ident := mkIdent (`_root_ ++ d ++ Name.mkSimple s)

private def noAsync {α : Type} (x : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false }) x

/-- The machines below `k` through machine callees (memory placeholders are
not machines), `fuel` levels down. A declaration the reader does not read
has none. -/
partial def machinesBelow (k : Name) (fuel : Nat) : MetaM (List Name) := do
  if fuel == 0 then return []
  let r? : Option Tools.ShippingMachineCommand.Read ← try
      pure (Option.some (← Tools.ShippingMachineCommand.readMachine k))
    catch _ => pure Option.none
  match r? with
  | Option.none => return []
  | Option.some r =>
    let cs := ((r.shape.insts.map (·.1)).eraseDups).filter fun c => (memParamsOf c).isNone
    let mut out : List Name := cs
    for c in cs do
      let more ← machinesBelow c (fuel - 1)
      out := out ++ more
    return out.eraseDups

/-- The reader on a declaration, a refusal line when it does not read it. -/
def readOr (who : String) (k : Name) : CommandElabM Tools.ShippingMachineCommand.Read := do
  let r? : Except String Tools.ShippingMachineCommand.Read ← try
      let r ← liftTermElabM <| Tools.ShippingMachineCommand.readMachine k
      pure (Except.ok r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  match r? with
  | Except.ok r => return r
  | Except.error msg => throwError "{who} {k} is not read by the machine reader: {msg}"

/-- **The shape**, read from the SOURCE declarations by the compiler's reader
(no generated constant is needed for it): a refusal line otherwise. -/
def scopeShape (f : Name) : CommandElabM ScopeM := do
  let env ← getEnv
  let r ← readOr "the declaration" f
  let calls := r.shape.insts.map (·.1)
  if calls.isEmpty then throwError "{f}: no call (nothing to match: no instance statement)"
  let ownMems := (calls.filter fun c => (memParamsOf c).isSome).eraseDups
  unless ownMems.isEmpty do
    throwError "{f}: a memory entry of {f} itself ({ownMems}): hnomem of kidsT_runFacts / kidsT_designCheck and of machineClosesAt_of_kidsD is false for it (a memory-only parent: #machine_no_ports_mem; a parent with memory entries AND machine callees: not generated)"
  if r.shape.layout.slots.isEmpty then
    throwError "{f}: parent without a register (kidsT_runFacts / kidsT_designCheck ask d.shape.layout.slots ≠ [])"
  if r.shape.instFields.isEmpty then
    throwError "{f}: a parent under the one-output closing (instFields = []; kidsT_* and machineClosesAt_of_kidsD ask the general closing)"
  if calls.contains f then
    throwError "{f}: a call of {f} itself (parent_ne is false)"
  for o in r.shape.layout.outs do
    if o.name.toList.head? == Option.some 'i' then
      throwError "{f}: the output {o.name} starts with 'i' (hfresh is decided by the first character; it would stay a premise)"
  let kids := calls.eraseDups
  -- a callee that is also a descendant of another callee: the sibling
  -- separation the closing asks is false
  for k in kids do
    let bel ← liftTermElabM (machinesBelow k 8)
    for k' in kids do
      if bel.contains k' then
        throwError "{f}: the callee {k'} is also a descendant of the callee {k} (the memGrand / mixDeep shape): the sibling separation hdisjD of machineClosesAt_of_kidsD is false for it — the closing of {f} is NOT generated (the check side is not blocked: Tools.ShippingCallSelf)"
  let mut kinds : List (Name × KindM) := []
  for k in kids do
    if env.contains (k ++ `gate_peel) then
      throwError "{f}: the callee {k} is a GATE child ({k}.gate_peel exists) under a general closing (no KidFactsT for it)"
    let cr ← readOr s!"{f}: the callee" k
    let kc := cr.shape.insts.map (·.1)
    if cr.shape.layout.slots.isEmpty then
      throwError "{f}: the callee {k} has no register (LeafKid.slots / GenKidM.slots ask one)"
    if kc.isEmpty then
      kinds := kinds ++ [(k, KindM.leaf)]
    else
      let others := (kc.filter fun c => (memParamsOf c).isNone).eraseDups
      unless others.isEmpty do
        throwError "{f}: the callee {k} has calls that are not memory placeholders ({others}): it is neither a leaf register machine nor a memory machine (one-output / general callees: #machine_no_ports_kids, #machine_no_ports_deep; beside a memory-machine callee: NOT generated)"
      if cr.shape.instFields.isEmpty then
        throwError "{f}: the memory-machine callee {k} is under the one-output closing (instFields = []; GenKidM.general asks the general closing)"
      let ps := (kc.filterMap memParamsOf).eraseDups
      match ps with
      | [(cb, aw, dw)] => kinds := kinds ++ [(k, KindM.memMach cr.nDecl cb aw dw)]
      | _ =>
        throwError "{f}: the memory-machine callee {k} has several different placeholders {kc.eraseDups} (generated for ONE memory module per memory machine: the constant name tables of GenKidM)"
  -- two different memory machines over ONE memory module share a descendant
  for (k, kd) in kinds do
    for (k', kd') in kinds do
      if k != k' then
        match kd, kd' with
        | KindM.memMach _ cb aw dw, KindM.memMach _ cb' aw' dw' =>
          if cb == cb' && aw == aw' && dw == dw' then
            throwError "{f}: the memory-machine callees {k} and {k'} have the SAME memory module (combinational read {cb}, aw {aw}, dw {dw}): the module is a shared descendant and the sibling separation hdisjD of machineClosesAt_of_kidsD is false — NOT generated"
        | _, _ => pure ()
  return { nDecl := r.nDecl, calls, kinds }

/-- **The constants the generation reads**: a refusal line naming the command
that makes the missing one. -/
def scopeArtifacts (f : Name) (s : ScopeM) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains (f ++ `machineData) && env.contains (f ++ `machine_ok) &&
      env.contains (f ++ `machine_body) do
    throwError "{f}: not a machine with an endpoint (no {f}.machineData / machine_ok / machine_body: #machine_endpoint was not run on it)"
  for (k, kd) in s.kinds do
    unless env.contains (k ++ `machineData) && env.contains (k ++ `machine_ok) &&
        env.contains (k ++ `machine_body) do
      throwError "{f}: the callee {k} has no machine endpoint ({k}.machineData / machine_ok / machine_body)"
    match kd with
    | KindM.leaf =>
      unless env.contains (k ++ `machine_closes) do
        throwError "{f}: the leaf callee {k} has no {k}.machine_closes (its closing in every context is not derived)"
    | KindM.memMach _ _ _ _ =>
      -- par/r-2: `#machine_no_ports_mem` leaves `k.noPortsMem_dataR` (MemOnlyDataR);
      -- the previous data path (`…_olddata`) leaves `k.noPortsMem_data`. Either one.
      unless env.contains (k ++ `noPortsMem_data) || env.contains (k ++ `noPortsMem_dataR) do
        throwError "{f}: the memory-machine callee {k} lacks {k ++ `noPortsMem_dataR} (and {k ++ `noPortsMem_data}) (run #machine_composedT {k}, #machine_ships_hier {k} and #machine_no_ports_mem {k} first)"
      for sfx in [`noPortsMem_closes] do
        unless env.contains (k ++ sfx) do
          throwError "{f}: the memory-machine callee {k} lacks {k ++ sfx} (run #machine_composedT {k}, #machine_ships_hier {k} and #machine_no_ports_mem {k} first)"
  let ships := f ++ `machine_ships_hierNR1
  unless env.contains ships do
    throwError "{f}: no depth endpoint at depth 1 ({ships} is not there: run #machine_design_svNR {f} 1 first — for a memory-machine callee k after #machine_ext_joint k, #machine_composed_memNR k 0, #machine_seq_child_memNR k 0)"

/-! ## The boundary tactic -/

/-- A proof of one component of a depth endpoint's boundary from the local
hypotheses `hyps` (see `memkid_boundary`). `kids`: the callees whose closing
constants may be used. -/
partial def proveBnd (kids : List Name) (hyps : Array Lean.Expr) (goal0 : Lean.Expr)
    (fuel : Nat) : MetaM Lean.Expr := do
  let goal := (← instantiateMVars goal0).headBeta
  if fuel == 0 then
    throwError "memkid_boundary: too deep at{indentExpr goal}"
  -- a hypothesis, as it is
  for h in hyps do
    let t ← instantiateMVars (← inferType h)
    if ← withReducible (isDefEq t goal) then return h
  -- a conjunction
  if goal.isAppOfArity ``And 2 then
    let a := goal.getArg! 0
    let b := goal.getArg! 1
    let pa ← proveBnd kids hyps a (fuel - 1)
    let pb ← proveBnd kids hyps b (fuel - 1)
    return mkApp4 (mkConst ``And.intro) a b pa pb
  -- a binder: introduced; a proposition becomes a hypothesis
  if goal.isForall then
    let p ← forallBoundedTelescope goal (some 1) fun zs body => do
      let mut hyps' := hyps
      for z in zs do
        let zt ← instantiateMVars (← inferType z)
        if ← isProp zt then hyps' := hyps'.push z
      let pb ← proveBnd kids hyps' body (fuel - 1)
      mkLambdaFVars zs pb
    return p
  -- the closing of a callee, in any contexts: its generated theorem
  let isAt := goal.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6
  let isCl := goal.isAppOfArity ``Tools.ShippingMachineEntry.MachineCloses 6
  if isAt || isCl then
    let args := goal.getAppArgs
    let sfx : Name := if isAt then `noPortsMem_closes else `machine_closes
    for k in kids do
      let same ← if args[4]! == toExpr k then pure true else isDefEq args[4]! (toExpr k)
      if same then
        let c := k ++ sfx
        if (← getEnv).contains c then
          let p := mkAppN (mkConst c) (args.extract 0 4)
          let ok : Bool ← try
              let pt ← inferType p
              isDefEq pt goal
            catch _ => pure false
          if ok then return p
    throwError "memkid_boundary: no closing theorem (k.noPortsMem_closes for MachineClosesAt, k.machine_closes for MachineCloses, k among {kids}) proves{indentExpr goal}"
  -- a reflection in other contexts: it does not depend on them
  if goal.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
    for h in hyps do
      let t ← instantiateMVars (← inferType h)
      if t.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
        let e ← mkConstWithFreshMVarLevels ``Tools.ShippingReflectCtx.MachineDefines.ctx
        let et ← inferType e
        let (ms, _, concl) ← forallMetaTelescope et
        let mut ok : Bool := ms.size > 0
        if ok then
          let c1 ← isDefEq concl goal
          ok := c1
        if ok then
          let lastT ← inferType ms[ms.size - 1]!
          let c2 ← isDefEq lastT t
          ok := c2
        if ok then
          let c3 ← isDefEq ms[ms.size - 1]! h
          ok := c3
        if ok then
          let p ← instantiateMVars (mkAppN e ms)
          unless p.hasMVar do return p
  -- reducible unfolding, once
  let goal' ← whnfR goal
  if goal' != goal then
    return ← proveBnd kids hyps goal' (fuel - 1)
  throwError "memkid_boundary: no proof of the boundary component{indentExpr goal}\nfrom the local hypotheses (a hypothesis as it is, a conjunction, a binder, a callee's closing, a reflection moved to other contexts)"

/-- `memkid_boundary [k₁, …]`: closes a goal that is the boundary of a depth
endpoint of a parent whose callees are `kᵢ` — the conjunction of `ChildBnd`,
the callees' reflections, and, for a callee whose closing the depth
generator did not find derived, `∀ mctx' cctx', ChildRanIn … → closing ∧
(own boundary)` — from the local hypotheses: a component is a hypothesis as
it is, a conjunction of components, a binder (introduced), the closing of a
callee in any contexts (`k.noPortsMem_closes` / `k.machine_closes`, read at
the goal's contexts), or a reflection moved to other contexts
(`Tools.ShippingReflectCtx.MachineDefines.ctx`). The proof term is checked
against the goal here and by the kernel with the enclosing declaration. -/
elab "memkid_boundary" " [" ks:ident,* "]" : tactic => do
  let mut kNs : List Name := []
  for k in ks.getElems do
    let kN ← realizeGlobalConstNoOverloadWithInfo k
    kNs := kNs ++ [kN]
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let mut hyps : Array Lean.Expr := #[]
    let lctx ← getLCtx
    for d in lctx do
      unless d.isImplementationDetail do
        let dt ← instantiateMVars d.type
        if ← isProp dt then hyps := hyps.push d.toExpr
    let gt ← g.getType
    let p ← proveBnd kNs hyps gt 64
    let pt ← inferType p
    unless ← isDefEq pt gt do
      throwError "memkid_boundary: the term found proves{indentExpr pt}\nnot{indentExpr gt}"
    g.assign p
    Lean.Elab.Tactic.replaceMainGoal []

/-! ## The generated theorems -/

def boolT (b : Bool) : CommandElabM Term :=
  if b then `(true) else `(false)

/-- The memory module's printed name, as a term. -/
def memNameT (cb : Bool) (aw dw : Nat) : CommandElabM Term := do
  let cbT ← boolT cb
  `(Sparkle.IR.ModuleName.ofMem $cbT $(Syntax.mkNumLit (toString aw))
    $(Syntax.mkNumLit (toString dw)))

/-- **`k.machine_genKidM0`, generated** (the hand `memCounterH_genKidM`,
`Tests/Compiler/MemParentFreeTest.lean` 123-170): the interface `GenKidM … 0`
of the memory machine `k`. The data conditions: the fields of the built
`k.noPortsMem_data` where it has them, the kernel's `decide` otherwise (and
as a fallback). -/
def genKidMTheorem (k : Name) (nD : Nat) (cb : Bool) (aw dw : Nat) : CommandElabM Name := do
  let name := k ++ `machine_genKidM0
  if (← getEnv).contains name then return name
  let data := nm k "machineData"
  let kq : Term := quote k
  let nDL := Syntax.mkNumLit (toString nD)
  let cbT ← boolT cb
  let awL := Syntax.mkNumLit (toString aw)
  let dwL := Syntax.mkNumLit (toString dw)
  let mn ← memNameT cb aw dw
  -- par/r-2: the reduced data (`MemOnlyDataR`, no `outTy` / `outScalar`:
  -- those two fields fall back to `decide` below) when the full one is absent
  let md := if (← getEnv).contains (k ++ `noPortsMem_data) then nm k "noPortsMem_data"
    else nm k "noPortsMem_dataR"
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mref : ST.Ref IO.RealWorld Lean.Meta.State}
        {cref : ST.Ref IO.RealWorld Lean.Core.State}
        (hR : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref $kq ($data).shape) :
        Tools.ShippingGenKidM.GenKidM mref cref $kq $data $nDL
          (fun _ => $mn) (fun _ => [$mn])
          (fun _ => Tools.ShippingMemKid.memOuts $dwL)
          (fun _ => Tools.ShippingMemKid.memIns $awL $dwL) 0 :=
      have hent : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          (($data).shape.insts[k]).1 =
            Sparkle.Compiler.MachMemory.memChildName $cbT $awL $dwL :=
        (by first | exact $(nm k "noPortsMem_entry") | decide)
      have hmem : Sparkle.Compiler.MachMemory.memChild?
            (Sparkle.Compiler.MachMemory.memChildName $cbT $awL $dwL) =
          some (Sparkle.Compiler.MachMemory.memModule $cbT $awL $dwL) :=
        (by first | rfl | decide)
      { ok := $(nm k "machine_ok")
        body := $(nm k "machine_body")
        calls := by first | exact ($md).calls | decide
        ss := by first | exact ($md).slots | decide
        dom := by first | exact ($md).domB | decide
        insts := fun h0 => absurd (congrArg List.length h0) (by decide)
        general := fun h0 => absurd (congrArg List.length h0) (by decide)
        slots := fun h0 => absurd (congrArg List.length h0) (by decide)
        outTy := by first | exact ($md).outTy | decide
        outName := by
          first
            | exact ($md).outNames
            | exact fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
                ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
                    Sparkle.IR.NameHints.charOk c = true from by
                  first | decide | decide +kernel) o ho)
        outScalar := by first | exact ($md).outScalar | decide
        hkD := by decide
        hIlen := by decide
        hSL := by decide
        hSlen := by decide
        hLlen := by decide
        hNIn := by decide
        kid := fun k hk _ hy =>
          Tools.ShippingKidsChildIfaceM.memKidNamesP
            ((congrArg Sparkle.Compiler.MachMemory.memChild? (hent k hk)).trans hmem) hy
        self := Tools.ShippingMemNamesP.ofDecl_not_mem_allMem $kq
          (Tools.ShippingMemNamesP.namesOfP_const_allMem $data $cbT $awL $dwL)
        kidsLo := fun k hk =>
          Tools.ShippingMemKid.memKid_facts
            ((congrArg Sparkle.Compiler.MachMemory.memChild? (hent k hk)).trans hmem)
        callW := by
          first
            | exact ($md).cw
            | decide
            | decide +kernel
        callA := by
          first
            | exact ($md).args
            | decide
            | decide +kernel
        entry := hR
        closes := fun _ _ => $(nm k "noPortsMem_closes") }))
  checkMade name before
  return name

/-- **`k.kid_factsT`, generated** (the hand `memCounterH_factsT`):
`KidFactsT` of the memory machine `k` at depth 1 — the check of its OWN
module (`designCheck … 0`, its instance's child the memory module). -/
def kidFactsTTheorem (k : Name) (nD : Nat) (genKid : Name) : CommandElabM Name := do
  let name := k ++ `kid_factsT
  if (← getEnv).contains name then return name
  let data := nm k "machineData"
  let kq : Term := quote k
  let nDL := Syntax.mkNumLit (toString nD)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    theorem $(mkIdent (`_root_ ++ name)) {mref : ST.Ref IO.RealWorld Lean.Meta.State}
        {cref : ST.Ref IO.RealWorld Lean.Core.State}
        (hR : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref $kq ($data).shape) :
        Tools.ShippingKidFactsT.KidFactsT mref cref $kq ($data).shape.layout.outs
          (Tools.ShippingCallsChildPorts.argWidths $data $nDL) 1 :=
      Tools.ShippingGenKidM.GenKidM.factsT ($(mkIdent (`_root_ ++ genKid)) hR)))
  checkMade name before
  return name

/-- **`k.iface_deepM`, generated** (the hand `memCounterH_iface`,
`Tests/Compiler/MemParentClosesTest.lean` 72-91): the interface of the
memory machine `k` as a kid of a general closing, over the names
`namesOfP k.machineData (fun _ => m) (fun _ => [m])`, `m` its memory
module's name. -/
def ifaceDeepMTheorem (k : Name) (nD : Nat) (cb : Bool) (aw dw : Nat) : CommandElabM Name := do
  let name := k ++ `iface_deepM
  if (← getEnv).contains name then return name
  let data := nm k "machineData"
  let kq : Term := quote k
  let nDL := Syntax.mkNumLit (toString nD)
  let cbT ← boolT cb
  let awL := Syntax.mkNumLit (toString aw)
  let dwL := Syntax.mkNumLit (toString dw)
  let mn ← memNameT cb aw dw
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State}
        (hR : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref $kq ($data).shape)
        (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
        (hy : Tools.ShippingChildInv.RealChild mref cref $kq y) :
        Tools.ShippingCallsKidsD.ChildIfaceD $kq
          ((($data).bsIn.take $nDL).filter (fun b => b.2 != .domain)).length
          (($data).shape.layout.outs.map (·.name))
          (Tools.ShippingKidsChildIfaceM.namesOfP $data (fun _ => $mn) (fun _ => [$mn]))
          y.1 y.2 :=
      have hent : ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          (($data).shape.insts[k]).1 =
            Sparkle.Compiler.MachMemory.memChildName $cbT $awL $dwL :=
        (by first | exact $(nm k "noPortsMem_entry") | decide)
      have hmem : Sparkle.Compiler.MachMemory.memChild?
            (Sparkle.Compiler.MachMemory.memChildName $cbT $awL $dwL) =
          some (Sparkle.Compiler.MachMemory.memModule $cbT $awL $dwL) :=
        (by first | rfl | decide)
      Tools.ShippingKidsChildIfaceM.kidsChild_of_realM (nDecl := $nDL) $data
        $(nm k "machine_ok") $(nm k "machine_body")
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) $nDL
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
        (fun _ => $mn) (fun _ => [$mn])
        (fun k hk y hy =>
          Tools.ShippingKidsChildIfaceM.memKidNamesP
            ((congrArg Sparkle.Compiler.MachMemory.memChild? (hent k hk)).trans hmem) hy)
        (Tools.ShippingMemNamesP.ofDecl_not_mem_allMem $kq
          (Tools.ShippingMemNamesP.namesOfP_const_allMem $data $cbT $awL $dwL))
        hR (fun _ _ _ => $(nm k "noPortsMem_closes")) hy))
  checkMade name before
  return name

/-- The names, binders and tables shared by the generated theorems of `f`. -/
structure Gen where
  f : Name
  s : ScopeM
  /-- the BUILT generator's context: the reflection binders `hR{j}` of the
  distinct callees and the per-callee table entries (a memory machine is
  entered as `.oneOut .anonymous nD`: only its declared binder count is
  read, for `argWidths k.machineData nD`) -/
  K : Ctx

def mkGen (f : Name) (s : ScopeM) : Gen :=
  let kindsK : List (Name × Kind) := s.kinds.map fun (k, kd) =>
    match kd with
    | KindM.leaf => (k, Kind.leaf)
    | KindM.memMach nD _ _ _ => (k, Kind.oneOut Lean.Name.anonymous nD)
  let K : Ctx := { f := f, n := 1, nDecl := s.nDecl, calls := s.calls, kinds := kindsK, gates := [] }
  { f := f, s := s, K := K }

namespace Gen

/-- The reflection binder of the callee `k`. -/
def hR (g : Gen) (k : Name) : Ident := Ctx.hR (g.s.kids.idxOf k)

/-- The per-entry tables of the layout outputs and of the argument widths
(always the list of the ENTRIES' callees' data, in the reader's order). -/
def kidOuts (g : Gen) : CommandElabM Term := do
  let os ← g.s.calls.toArray.mapM Ctx.outsOf
  `(fun k => List.getD [$os,*] k [])

def kidIns (g : Gen) : CommandElabM Term := do
  let os ← g.s.calls.toArray.mapM g.K.insOf
  `(fun k => List.getD [$os,*] k [])

/-- The hardware arguments of the callee `k` (the closing's `nk`). -/
def nkOf (g : Gen) (k : Name) : CommandElabM Term := do
  let kd := nm k "machineData"
  match g.s.kindOf k with
  | KindM.leaf =>
    `(((($kd).shape.binders.take (($kd).shape.binders.length -
        ($kd).shape.layout.slots.length - ($kd).shape.layout.lets)).filter
          fun x => x.2 != .domain).length)
  | KindM.memMach nD _ _ _ =>
    `(((($kd).bsIn.take $(Syntax.mkNumLit (toString nD))).filter
        (fun b => b.2 != .domain)).length)

/-- The output names of the callee `k` (the closing's `outsK`). -/
def outNamesOf (k : Name) : CommandElabM Term :=
  `((($(nm k "machineData")).shape.layout.outs.map (·.name)))

/-- The names below the callee `k` (the closing's `namesK`). -/
def namesOf (g : Gen) (k : Name) : CommandElabM Term := do
  match g.s.kindOf k with
  | KindM.leaf => `(([] : List String))
  | KindM.memMach _ cb aw dw =>
    let mn ← memNameT cb aw dw
    `(Tools.ShippingKidsChildIfaceM.namesOfP $(nm k "machineData") (fun _ => $mn)
      (fun _ => [$mn]))

/-- The tag of the callee `k` (`Tools.ShippingMemKidTags.Tagged`). -/
def tagOf (g : Gen) (k : Name) : CommandElabM Term := do
  match g.s.kindOf k with
  | KindM.leaf => `((none : Option (Bool × Nat × Nat)))
  | KindM.memMach _ cb aw dw =>
    let cbT ← boolT cb
    `((some ($cbT, $(Syntax.mkNumLit (toString aw)), $(Syntax.mkNumLit (toString dw))) :
      Option (Bool × Nat × Nat)))

def nkF (g : Gen) : CommandElabM Term := do
  let xs ← g.s.calls.toArray.mapM g.nkOf
  `(fun k => List.getD [$xs,*] k 0)

def outF (g : Gen) : CommandElabM Term := do
  let xs ← g.s.calls.toArray.mapM outNamesOf
  `(fun k => List.getD ([$xs,*] : List (List String)) k [])

def nmF (g : Gen) : CommandElabM Term := do
  let xs ← g.s.calls.toArray.mapM g.namesOf
  `(fun k => List.getD ([$xs,*] : List (List String)) k [])

def tgF (g : Gen) : CommandElabM Term := do
  let xs ← g.s.calls.toArray.mapM g.tagOf
  `(fun k => List.getD ([$xs,*] : List (Option (Bool × Nat × Nat))) k none)

/-- `cases k` over the call entries: entry `i` is closed by `exact terms[i]`;
the hypotheses `k`, `hk' : k < (number of entries)` are in scope. -/
def casesTac (terms : Array Term) : CommandElabM (TSyntax `tactic) := do
  let mut tac ← `(tactic| exact absurd hk' (by omega))
  for i' in [0:terms.size] do
    let i := terms.size - 1 - i'
    let t := terms[i]!
    tac ← `(tactic| cases k with
      | zero => exact $t
      | succ k => $tac:tactic)
  return tac

end Gen

/-- **`f.machine_kidIfaceM`, generated** (the hand `memParent_kidIface`; the
block of `memParent_closes`): `ChildIfaceD` of every call entry's callee —
a leaf by the built leaf route, a memory machine by `k.iface_deepM`. -/
def kidIfaceTheorem (g : Gen) : CommandElabM Name := do
  let name := g.f ++ `machine_kidIfaceM
  if (← getEnv).contains name then return name
  let data := nm g.f "machineData"
  let nCalls := Syntax.mkNumLit (toString g.s.calls.length)
  let nkF ← g.nkF
  let outF ← g.outF
  let nmF ← g.nmF
  let mut terms : Array Term := #[]
  for k in g.s.calls do
    let kd := nm k "machineData"
    let h := g.hR k
    let t ← match g.s.kindOf k with
      | KindM.leaf =>
        `(Tools.ShippingCallsKidsD.ChildIfaceG.toD
          (Tools.ShippingSeqChildIface.seqChild_of_real $kd $(nm k "machine_ok")
            $(nm k "machine_body") rfl (by decide) $h
            (fun mc cc => $(nm k "machine_closes") mc _ cc _) hy))
      | KindM.memMach _ _ _ _ => `($(nm k "iface_deepM") $h y hy)
    terms := terms.push t
  let tac ← Gen.casesTac terms
  let bs ← g.K.binders
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
        ∀ (k : Nat) (hk : k < ($data).shape.insts.length)
          (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
          Tools.ShippingChildInv.RealChild mref cref (($data).shape.insts[k]).1 y →
          Tools.ShippingCallsKidsD.ChildIfaceD (($data).shape.insts[k]).1
            (($nkF) k) (($outF) k) (($nmF) k) y.1 y.2 := by
      intro k hk y hy
      have hk' : k < $nCalls := hk
      $tac:tactic))
  checkMade name before
  return name

/-- **`f.machine_kidTagsM`, generated**: the names below every call entry are
the memory-module name of its tag (none below a leaf). -/
def kidTagsTheorem (g : Gen) : CommandElabM Name := do
  let name := g.f ++ `machine_kidTagsM
  if (← getEnv).contains name then return name
  let data := nm g.f "machineData"
  let nCalls := Syntax.mkNumLit (toString g.s.calls.length)
  let nmF ← g.nmF
  let tgF ← g.tgF
  let mut terms : Array Term := #[]
  for k in g.s.calls do
    let t ← match g.s.kindOf k with
      | KindM.leaf => `(Tools.ShippingMemKidTags.tagged_nil _)
      | KindM.memMach _ cb aw dw => do
        let cbT ← boolT cb
        `(Tools.ShippingMemKidTags.tagged_namesOfP_const $(nm k "machineData") $cbT
          $(Syntax.mkNumLit (toString aw)) $(Syntax.mkNumLit (toString dw)))
    terms := terms.push t
  let tac ← Gen.casesTac terms
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) :
        ∀ (k : Nat), k < ($data).shape.insts.length →
          Tools.ShippingMemKidTags.Tagged (($tgF) k) (($nmF) k) := by
      intro k hk
      have hk' : k < $nCalls := hk
      $tac:tactic))
  checkMade name before
  return name

/-- **`f.machine_closes_at_memkid`, generated** (the hand `memParent_closes`,
`Tests/Compiler/MemParentClosesTest.lean` 142-189): `MachineClosesAt f` from
the reflections of the callees, by the BUILT `machineClosesAt_of_kidsD`. The
name conditions over the descendants by the tags
(`Tools.ShippingMemKidTags`): no `decide` on a name string, no premise. -/
def closesTheorem (g : Gen) (kidIface kidTags : Name) : CommandElabM Name := do
  let name := g.f ++ `machine_closes_at_memkid
  if (← getEnv).contains name then return name
  let data := nm g.f "machineData"
  let fq : Term := quote g.f
  let nDecl := Syntax.mkNumLit (toString g.s.nDecl)
  let nkF ← g.nkF
  let outF ← g.outF
  let nmF ← g.nmF
  let tgF ← g.tgF
  let bs ← g.K.binders
  let hs := g.K.hyps
  let ifaceI := mkIdent (`_root_ ++ kidIface)
  let tagsI := mkIdent (`_root_ ++ kidTags)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
        Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref $fq ($data).shape :=
      Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD (nDecl := $nDecl) $data
        $(nm g.f "machine_ok") $(nm g.f "machine_body")
        (by decide) (by decide) (by decide) (by decide) (by decide)
        ($nkF) ($outF) ($nmF)
        (by decide)
        ($ifaceI $hs*)
        (by decide) (by decide) (by decide)
        (Tools.ShippingNameDischarge.names_inj _)
        (Tools.ShippingNameDischarge.parent_ne _ _ (by decide))
        (fun gi c _ o ho => Tools.ShippingCallsGate.instName_ne_of_head
          ((by decide : ∀ o ∈ ($data).shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho)
          gi (Sparkle.IR.ModuleName.ofDecl c.1))
        (fun k hk => Tools.ShippingMemNamesP.ofDecl_not_mem_allMem $fq
          (Tools.ShippingMemKidTags.Tagged.allMem ($tagsI k hk)))
        (fun k hk => Tools.ShippingMemNamesP.ofDecl_not_mem_allMem _
          (Tools.ShippingMemKidTags.Tagged.allMem ($tagsI k hk)))
        (fun k hk k' hk' hne =>
          ⟨Tools.ShippingMemNamesP.ofDecl_not_mem_allMem _
            (Tools.ShippingMemKidTags.Tagged.allMem ($tagsI k' hk')),
           Tools.ShippingMemKidTags.tagged_disj ($tagsI k hk) ($tagsI k' hk')
            ((by decide : ∀ (k : Nat) (hk : k < ($data).shape.insts.length) (k' : Nat)
              (hk' : k' < ($data).shape.insts.length),
              (($data).shape.insts[k]).1 ≠ (($data).shape.insts[k']).1 →
              (($tgF) k = none ∨ ($tgF) k ≠ ($tgF) k')) k hk k' hk' hne)⟩)))
  checkMade name before
  return name

/-- **`f.machine_kidsT1`, generated** (the hand `memParent_kidsT`):
`KidFactsT` of every call entry's callee at depth 1 — a leaf by the built
leaf facts `.toT`, a memory machine by `k.kid_factsT`. -/
def kidsTTheorem (g : Gen) : CommandElabM Name := do
  let name := g.f ++ `machine_kidsT1
  if (← getEnv).contains name then return name
  let data := nm g.f "machineData"
  let nCalls := Syntax.mkNumLit (toString g.s.calls.length)
  let kidOuts ← g.kidOuts
  let kidIns ← g.kidIns
  let mut terms : Array Term := #[]
  for k in g.s.calls do
    let h := g.hR k
    let t ← match g.s.kindOf k with
      | KindM.leaf =>
        `(Tools.ShippingKidFacts.KidFacts.toT
          (Tools.ShippingLeafKidFacts.leafKid_facts ($(nm k "machine_leafKid") $h) 1))
      | KindM.memMach _ _ _ _ =>
        `($(nm k "kid_factsT") (fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx $h))
    terms := terms.push t
  let tac ← Gen.casesTac terms
  let bs ← g.K.binders
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ name)) {mctx : Lean.Meta.Context}
        {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} $bs* :
        ∀ (k : Nat) (hk : k < ($data).shape.insts.length),
          Tools.ShippingKidFactsT.KidFactsT mref cref (($data).shape.insts[k]).1
            (($kidOuts) k) (($kidIns) k) 1 := by
      intro k hk
      have hk' : k < $nCalls := hk
      $tac:tactic))
  checkMade name before
  return name

/-- The four run theorems of `f` (`kidsT_runFacts`, `kidsT_outsCheck`,
`kidsT_maskedN`, `kidsT_designCheck` at `f`'s data): binders
`hcore hpost entry closes (hg) hB` and the reflections — the text of the
built `Tools.ShippingNoPortsKidsCommand.runTheorems` with `kidsT_*`, and for
the design check the names below the entries (the hand
`memParent_runFacts1` … `memParent_designP1`). -/
def runTheoremsT (g : Gen) (kidsN kidIface kidTags : Name) :
    CommandElabM (Name × Name × Name × Name) := do
  let f := g.f
  let data := nm f "machineData"
  let fq : Term := quote f
  let nDecl := Syntax.mkNumLit (toString g.s.nDecl)
  let kidOuts ← g.kidOuts
  let kidIns ← g.kidIns
  let nmF ← g.nmF
  let bs ← g.K.binders
  let hs := g.K.hyps
  let kidsI := mkIdent (`_root_ ++ kidsN)
  let ifaceI := mkIdent (`_root_ ++ kidIface)
  let tagsI := mkIdent (`_root_ ++ kidTags)
  let ok := nm f "machine_ok"
  let body := nm f "machine_body"
  let facts := f ++ `machine_runFactsT1
  let outs := f ++ `machine_outsGT1
  let masked := f ++ `machine_maskedGT1
  let design := f ++ `machine_designPT1
  unless (← getEnv).contains facts do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ facts)) {mctx : Lean.Meta.Context}
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
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
        Tools.ShippingKidFactsT.kidsT_runFacts (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          ($kidOuts) ($kidIns) 1 ($kidsI $hs*)
          (show Tools.ShippingCallWidths.callWidthsOk $data $nDecl ($kidOuts) = true from by
            first | decide | decide +kernel)
          hB hcore hpost entry closes))
    checkMade facts before
  unless (← getEnv).contains outs do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ outs)) {mctx : Lean.Meta.Context}
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
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules)
            1 (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
        Tools.ShippingKidFactsT.kidsT_outsCheck (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          ($kidOuts) ($kidIns) 1 ($kidsI $hs*)
          hB hcore hpost entry closes hg))
    checkMade outs before
  unless (← getEnv).contains masked do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ masked)) {mctx : Lean.Meta.Context}
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
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
        Tools.ShippingKidFactsT.kidsT_maskedN (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          ($kidOuts) ($kidIns) 1 ($kidsI $hs*)
          hB hcore hpost entry closes))
    checkMade masked before
  unless (← getEnv).contains design do
    let before := (← get).messages.toList.length
    elabCommand (← `(command|
      set_option maxHeartbeats 4000000 in
      theorem $(mkIdent (`_root_ ++ design)) {mctx : Lean.Meta.Context}
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
          (hB : Tools.ShippingChildInv.ChildBnd mref cref w) $bs* :
          Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules)
            1 (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
        Tools.ShippingKidFactsT.kidsT_designCheck (nDecl := $nDecl) $data $ok $body
          (by decide) (by decide) (by decide)
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (fun h0 => absurd (congrArg List.length h0) (by decide))
          (by decide) (by decide)
          ($kidOuts) ($kidIns) 1 ($kidsI $hs*)
          (show Tools.ShippingCallWidths.callWidthsOk $data $nDecl ($kidOuts) = true from by
            first | decide | decide +kernel)
          (show Tools.ShippingPortsMatchRaw.callArgsOk $data $nDecl ($kidIns) = true from by
            first | decide | decide +kernel)
          ($nmF)
          (fun k hk y hy =>
            ⟨($ifaceI $hs* k hk y hy).name, ($ifaceI $hs* k hk y hy).desNames⟩)
          (fun k _ k' hk' => Tools.ShippingMemNamesP.ofDecl_not_mem_allMem _
            (Tools.ShippingMemKidTags.Tagged.allMem ($tagsI k' hk')))
          hB hcore hpost entry closes
          (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
            ((show ∀ o ∈ ($data).shape.layout.outs, ∀ c ∈ o.name.toList,
                Sparkle.IR.NameHints.charOk c = true from by
              first | decide | decide +kernel) o ho))
          (by decide)))
    checkMade design before
  return (facts, outs, masked, design)

/-- **The closed form, generated** (the hand
`memParent_design_noPorts1_closed`): its statement is `bnd_only% openN
[callees]` (the built elaborator: the binders through `f`'s reflection, the
callees' reflections, the boundary replaced by `ChildBnd`), its proof the
open endpoint at `f.machine_closes_at_memkid`, the boundary by
`memkid_boundary`. Elaborated under the name `target`. -/
def closedCommand (g : Gen) (openN closesN target : Name) : CommandElabM Unit := do
  let kidsI : Array Ident := (g.s.kids.map fun k => mkIdent (`_root_ ++ k)).toArray
  let hKs : Array Term := ((List.range g.s.kids.length).map fun j =>
    (⟨(mkIdent (Name.mkSimple s!"hK{j}")).raw⟩ : Term)).toArray
  let openI := mkIdent (`_root_ ++ openN)
  let closesI := mkIdent (`_root_ ++ closesN)
  let before := (← get).messages.toList.length
  elabCommand (← `(command|
    set_option maxHeartbeats 4000000 in
    theorem $(mkIdent (`_root_ ++ target)) : bnd_only% $openI [$kidsI,*] := by
      intro mctx mref cctx cref w w' b design hr hP $hKs*
      obtain ⟨raw, D, hpost, h⟩ := $openI hr hP ($closesI $hKs*)
      refine ⟨raw, D, hpost, fun hB => h ?_⟩
      memkid_boundary [$kidsI,*]))
  checkMade target before

/-- What a generation made. -/
structure Made where
  /-- the log lines -/
  lines : Array String
  /-- the constant that holds the open endpoint built now -/
  openC : Name
  /-- the constant that holds the closed form built now (`…_closed`, or
  `…_closed_regen` on the compare path) -/
  closedC : Name
  /-- the endpoint existed before (the compare path) -/
  rebuilt : Bool
  /-- the census's re-check of `closedC` -/
  check : Tools.ShippingDesignCoverage.Check

/-- The generation, after the scope (may leave declarations and messages
behind on a failure: the commands put the environment back). -/
def generate (f : Name) (s : ScopeM) : CommandElabM Made := do
  let g := mkGen f s
  let mut made : Array Name := #[]
  for (k, kd) in s.kinds do
    match kd with
    | KindM.leaf =>
      let n0 ← noAsync (Tools.ShippingNoPortsCommand.leafKidTheorem k)
      made := made.push n0
    | KindM.memMach nD cb aw dw =>
      let n1 ← noAsync (genKidMTheorem k nD cb aw dw)
      let n2 ← noAsync (kidFactsTTheorem k nD n1)
      let n3 ← noAsync (ifaceDeepMTheorem k nD cb aw dw)
      made := made ++ #[n1, n2, n3]
  let kidIface ← noAsync (kidIfaceTheorem g)
  let kidTags ← noAsync (kidTagsTheorem g)
  let closesN ← noAsync (closesTheorem g kidIface kidTags)
  let kidsN ← noAsync (kidsTTheorem g)
  let (facts, outs, masked, design) ← noAsync (runTheoremsT g kidsN kidIface kidTags)
  made := made ++ #[kidIface, kidTags, closesN, kidsN, facts, outs, masked, design]
  -- the open endpoint: the BUILT function, the BUILT compare path
  let name := f ++ `machine_design_noPortsNR1
  let existed := (← getEnv).contains name
  let (openC, line1) ← liftTermElabM <|
    withOptions (fun o => Lean.Elab.async.set o false) do
      let (type, value) ←
        Tools.ShippingNoPortsDeepCommand.endpointTermX f [] [] 1 facts outs masked design
      addOrCompare name type value
  let mut lines : Array String := #[line1]
  -- the closed form: stated from the constant `name` (the existing one on
  -- the compare path — its statement is isDefEq the rebuilt one)
  let closedN := Tools.ShippingMachineClosesGen.closedName name
  let mut closedC : Name := closedN
  if (← getEnv).contains closedN then
    let rn := regenName closedN
    if (← getEnv).contains rn then
      throwError "{rn}: exists already (the compare path was run twice)"
    noAsync (closedCommand g name closesN rn)
    let same ← liftTermElabM do
      let c1 ← getConstInfo closedN
      let c2 ← getConstInfo rn
      isDefEq c1.type c2.type
    unless same do
      throwError "{closedN}: EXISTS with a different statement than the rebuilt {rn}"
    lines := lines.push s!"REBUILT {closedN}: statement isDefEq the existing one (proof kept as {rn})"
    closedC := rn
  else
    noAsync (closedCommand g name closesN closedN)
    lines := lines.push s!"GENERATED {closedN}"
  -- the statement check: the census's own re-check, and the premise counts
  let ch ← liftTermElabM <| Tools.ShippingDesignCoverage.recheck closedC
  let errLine : String := match ch.err with
    | some e => s!"; the re-check threw: {e}"
    | none => ""
  let counts : String :=
    s!"proposition binders {ch.props}, antecedents under the existentials {ch.antes}, NOT ALLOWED {ch.bad}, checker / closing constants {ch.checkers}, DesignSV mentioned: {ch.hasDesign}{errLine}"
  unless ch.ok do
    throwError "{closedC}: the statement check FAILED — {counts}"
  unless ch.props == s.kids.length + 2 && ch.antes == 1 do
    throwError "{closedC}: the statement has {ch.props} proposition binders and {ch.antes} antecedents under the existentials; expected {s.kids.length + 2} (the run, MachineDefines of {f} and of the {s.kids.length} callees) and 1 (ChildBnd)"
  -- the axioms of everything generated
  let audited := made ++ #[openC, closedC]
  liftTermElabM do
    for c in audited do
      for ax in ← Lean.collectAxioms c do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "{c} uses a non-standard axiom: {ax}"
  lines := lines.push s!"STATEMENT CHECK OK ({closedC}): {counts}"
  lines := lines.push s!"AXIOMS: standard only ([propext, Classical.choice, Quot.sound] at most) for {audited.toList}"
  return { lines, openC, closedC, rebuilt := existed, check := ch }

/-- The callees' kinds, one line each. -/
def kindLines (s : ScopeM) : List String :=
  s.kinds.map fun (k, kd) =>
    match kd with
    | KindM.leaf => s!"{k}: leaf register machine"
    | KindM.memMach nD cb aw dw =>
      let rd : String := if cb then "combinational" else "synchronous"
      s!"{k}: memory machine (nDecl {nD}; every call entry the placeholder of the {rd}-read memory aw {aw}, dw {dw})"

/-- The log line of a generation. -/
def summaryLine (f : Name) (s : ScopeM) (m : Made) : String :=
  s!"NOPORTS MEMKID {f} at depth 1: {String.intercalate "; " m.lines.toList}. Callees: {kindLines s}; call entries {s.calls}. The depth endpoint without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents and without a closing premise: premises the run of the full entry, MachineDefines of {f} and of {s.kids}; under ∃ raw D the runtime laws ChildBnd only. SCOPE: ONE declaration, depth 1, data conditions decided per declaration (conditions, not reductions), the runtime boundary a premise, DesignSV of the module list — not the SV string, not #sim"

/-- The whole command: scope, generation, checks. Throws where refused or
failed; the caller puts the environment back. -/
def noPortsMemKid (f : Name) : CommandElabM (ScopeM × Made) := do
  let s ← scopeShape f
  scopeArtifacts f s
  let m ← generate f s
  return (s, m)

/-- `#machine_no_ports_memkid f`: an ERROR where it is refused or where a
generated proof or the statement check fails; the environment is put back
on any failure. -/
elab "#machine_no_ports_memkid " d:ident : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let res : Except String (ScopeM × Made) ← try
      let r ← noPortsMemKid f
      pure (Except.ok r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (Except.error msg)
  match res with
  | Except.ok (s, m) => logInfo m!"{summaryLine f s m}"
  | Except.error msg =>
    setEnv savedEnv
    modify fun st => { st with messages := savedMsgs }
    throwError "NOPORTS MEMKID {f}: NOT GENERATED (the environment put back) — {msg}"

end Tools.ShippingNoPortsMemKidCommand
