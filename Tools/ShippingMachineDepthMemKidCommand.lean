import Tools.ShippingMachineDepthCommandR

/-! # `#machine_composed_memNR f n`: the depth generator's composed theorem of a machine whose calls are ALL memory placeholders (round par/c-2)

WRITTEN, NOT BUILT.

The grouped depth generator (`generateCoreNR`,
`Tools/ShippingMachineDepthCommandR.lean`) makes a kid with calls of its own
a kid of a deeper parent from the kid's composed theorem one depth down,
`k.machine_composedNR{n}` — which it makes by calling itself on the kid. On a
kid whose calls are all memory placeholders (`memCounterH`: a hand-written
loop with one memory read) it throws "no sequential child": the per-child
predicate `PC` is built from the first sequential child, and there is none.

That is a restriction of the GENERATOR, not of the theorem it applies:
`machine_linkedT_callsRN` (`Tools/ShippingMachineCallsLinkedTNR.lean`) takes
per call entry `MemFacts … ∨ SeqFactsRN …`, and for a memory entry the left
side; its child premise `hrunN` is about callees that are NOT placeholders.
With no sequential child the four families (`bsC`, `outsC`, `S`, `PC`) are
never read at a call. This command applies the same theorem with the
families constant (`fun _ => []`, `fun _ _ => True`):

    f.machine_composedNR{n} :
      ∀ {mctx mref cctx cref w w' m design},
        RunsTo (synthesizeCombinationalCore f [] false) mctx mref cctx cref w (m, design) w' →
        MachineDefines mctx mref cctx cref f f.machineData.shape →
        MachineClosesAt mctx mref cctx cref f f.machineData.shape →
        ChildBnd mref cref w →
        (the statement `ComposedNW n f f.machineData nDecl m design …` unfolded)

(the binders are those of the wired head `…RA` of `f`'s endpoint; 12, the
run boundary last, as `bndOfComposed` reads them). The name is the one
`generateCoreNR` looks up FIRST (`if (← getEnv).contains name then return
name`), so after this command the built `#machine_design_svNR parent n`
finds the kid's composed theorem and goes on; no built file is edited.

Every step is the built generator's for a memory entry of a mixed parent
(`memTactic` on the entry's goal; the vacuous child premise by the built
tactic; the chains `forall_getElem?_cons`), copied from `generateCoreNR` with
`seqKids = []`. Scope: a machine with a register endpoint whose head has a
wired twin (`endpointParts`), not transported, the general closing
(`instFields ≠ []`), every callee a placeholder `SparkleMem.{combo|sync}.aw.dw`.
Anything else is refused with a reason. On a failure nothing is added. -/
namespace Tools.ShippingMachineDepthMemKid
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineShipsHierCommand (conj projs)

/-- `f.machine_composedNR{dep}` for a machine whose calls are all memory
placeholders (no restore on failure: `generate`). -/
def generateCore (declName : Name) (dep : Nat) : MetaM Name := do
  let name := declName ++ Name.mkSimple s!"machine_composedNR{dep}"
  if (← getEnv).contains name then return name
  progress s!"{declName}: composedNR {dep} (memory placeholders only)"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  if r.shape.instFields.isEmpty then
    throwError "{declName}: one-output combinational calls (instFields = []: not the general closing)"
  let calls := r.shape.insts
  for (c, _, _) in calls do
    if (Tools.ShippingMachineMemCommand.memWidths? c).isNone then
      throwError "{declName}: the callee {c} is not a memory placeholder (a parent with a sequential child: #machine_design_svNR makes its composed theorem itself)"
  let (headL, args, back?) ← endpointParts declName
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  -- the head carrying `ServedReal` (under `ChildBnd`)
  let pL := mkAppN (mkConst (headL.appendAfter "RA")) args
  forallTelescope (← inferType pL) fun xs traceT => do
  unless xs.size == 12 do throwError "{declName}: the head's binders ({xs.size})"
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let dE := tyArgs[2]!
  let hsyn := xs.back!
  -- the families over the sequential children: there is none
  let bsTy ← inferType (← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[dE])
  let outsTy ← inferType (← mkAppM ``Sparkle.IR.Machine.Layout.outs
    #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE]]])
  let nat := mkConst ``Nat
  let valsTy ← mkArrow nat (mkApp (mkConst ``List [.zero]) nat)
  let obsTy := mkApp (mkConst ``List [.zero]) (← mkArrow nat nat)
  let ιP := tyArgs[5]!
  let bsC ← nameCases bsTy [] (mkApp (mkConst ``List.nil [.zero]) bsTy.appArg!)
  let outsC ← nameCases outsTy [] (mkApp (mkConst ``List.nil [.zero]) outsTy.appArg!)
  let natNat ← mkArrow nat nat
  let sDflt ← withLocalDeclD `vals valsTy fun vals =>
    mkLambdaFVars #[vals] (mkApp (mkConst ``List.nil [.zero]) natNat)
  let S ← withLocalDeclD `i ιP fun iv => do
    mkLambdaFVars #[iv] (← nameCases (← mkArrow valsTy obsTy) [] sDflt)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let pcDflt ← withLocalDeclD `mc modT fun mc => mkLambdaFVars #[mc] (mkConst ``True)
  let PC ← nameCases (← mkArrow modT (mkSort .zero)) [] pcDflt
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN #[mkNatLit dep, h]
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  p := mkApp4 p bsC outsC S PC
  let nameT := mkConst ``Name
  let names := calls.map (·.1)
  let n := names.length
  -- the calls: every entry a memory read (`MemFacts`, the left side)
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    let goalOf (k : Nat) (c : Name) : Lean.Expr :=
      ((rest.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1 (toExpr c)).bindingBody!
    let mut perK : Array Lean.Expr := #[]
    for k in [0:calls.length] do
      let some (c, argsK, _) := calls[k]? | throwError "{declName}: call {k}"
      let some (cb, aw, dw) := Tools.ShippingMachineMemCommand.memWidths? c
        | throwError "{declName}: call {k}: not a memory placeholder"
      let goalK := goalOf k c
      progress s!"{declName}: call {k} of {c}: tactic START"
      let proofK ← (try do
          let pr ← proveByTacticT goalK (do pure (← memTactic k cb aw dw argsK))
          if pr.hasSorry then
            throwError "the proof contains sorry (an error inside the tactic was recovered from)"
          pure pr
        catch ex => throwError "call {k}: {ex.toMessageData}")
      perK := perK.push proofK
    -- the chain over the call list
    let Qm (m : Nat) : MetaM Lean.Expr :=
      withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
        let rk := ((rest.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
          cv).bindingBody!
        mkLambdaFVars #[kv, cv] rk
    let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← Qm n]
    for m' in [0:n] do
      let m := n - 1 - m'
      let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
      chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
        #[nameT, ← Qm m, toExpr names[m]!, rest', perK[m]!, chain]
    -- (stated at the premise's own `k`, `c` and hypothesis, as the built generator does)
    withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
      let hkT := ((rest.bindingBody!.instantiate1 kv).bindingBody!.instantiate1 cv).bindingDomain!
      withLocalDeclD `hk hkT fun hk => do
        mkLambdaFVars (ibb ++ #[kv, cv, hk]) (mkAppN chain #[kv, cv, hk])
  p := mkApp p hcalls
  -- `hrunN`: asked of callees that are NOT placeholders — there is none
  let hrunNT := (← whnf (← inferType p)).bindingDomain!
  let mut perR : Array Lean.Expr := #[]
  for k in [0:calls.length] do
    let some (c, _, _) := calls[k]? | throwError "{declName}: call {k}"
    let goalK := ((hrunNT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
      (toExpr c)).bindingBody!
    let prK ← (try
        proveByTacticT goalK `(tactic| (intro h; first | cases h | simp [Sparkle.Compiler.MachMemory.memChild?] at h | exact absurd (congrArg Option.isNone h) (by decide) | exact absurd (congrArg Option.isNone h) (by decide +kernel)))
      catch ex => throwError "call {k} (the child premise): {ex.toMessageData}")
    if prK.hasSorry then throwError "{declName}: call {k} (the child premise): the proof contains sorry"
    perR := perR.push prK
  let QmR (m : Nat) : MetaM Lean.Expr :=
    withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
      let rk := ((hrunNT.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
        cv).bindingBody!
      mkLambdaFVars #[kv, cv] rk
  let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← QmR n]
  for m' in [0:n] do
    let m := n - 1 - m'
    let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
    chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
      #[nameT, ← QmR m, toExpr names[m]!, rest', perR[m]!, chain]
  p := mkApp p chain
  -- the boundary in the run's contexts: `ChildBnd` alone (no child premise)
  let bTypes := [← inferType hsyn]
  let bnd ← conj bTypes
  let value ← withLocalDeclD `hBnd bnd fun hBnd => do
    let ps ← projs hBnd bTypes
    let p' := p.replaceFVars #[hsyn] ps.toArray
    mkLambdaFVars (xs.pop ++ #[hBnd]) p'
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  progress s!"{name}: checked"
  return name

/-- `f.machine_composedNR{n}`; on failure nothing is added. -/
def generate (declName : Name) (n : Nat) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateCore declName n)
  catch ex =>
    setEnv saved
    throw ex

/-- `#machine_composed_memNR f n`: the depth generator's composed theorem
`f.machine_composedNR{n}` of a machine whose calls are all memory
placeholders (run it on such a kid before `#machine_design_svNR` on a parent
of it). -/
elab "#machine_composed_memNR " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM (generate declName n.getNat)
  logInfo m!"{name}: the composed theorem at depth {n.getNat} of a machine whose calls are all memory reads (machine_linkedT_callsRN, no sequential child), the run boundary ChildBnd, checked by the kernel"

end Tools.ShippingMachineDepthMemKid
