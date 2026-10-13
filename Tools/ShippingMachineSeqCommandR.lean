import Tools.ShippingMachineSeqCommand
import Tools.ShippingMachineSeqLinkedR
import Tools.ShippingMachineCallsLinkedTR
import Tools.ShippingChildRun
import Tools.ShippingReflectCtx
import Tools.ShippingMachineClosesGen
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingShipsDesignSVCommand

/-! # Generated composition, the child-run boundary derived

`#machine_composedTSR f`: as `#machine_composedTS`, from the wired endpoint
carrying `ServedReal` (the `R` heads, under `ChildBnd`), through
`machine_linkedT_callsR`: per sequential call the CHILD's own theorem on any
run of its entry (`c.seq_child_run`), and the children's reflection facts in
the parent's contexts as one premise (`hrefl`). No `BoundaryOf` premise. -/
namespace Tools.ShippingMachineSeqCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem soundArgs)

/-- `f.machine_composedTR`; with `atW`, `f.machine_composedTRA`: the same from
the head that asks `MachineClosesAt` instead of the all-worlds
`MachineCloses`. -/
def generateCoreSR (declName : Name) (atW : Bool := false) : MetaM Name := do
  let name := declName ++ (if atW then `machine_composedTRA else `machine_composedTR)
  if (← getEnv).contains name then return name
  progress s!"{declName}: composedTR (sequential, boundary derived)"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  let (headL, args, back?) ← endpointParts declName
  -- the head carrying `ServedReal` (under `ChildBnd`)
  let pL := mkAppN (mkConst (headL.appendAfter (if atW then "RA" else "R"))) args
  let calls := r.shape.insts
  let seqKids := ((calls.map (·.1)).eraseDups.filter fun c =>
    (Tools.ShippingMachineMemCommand.memWidths? c).isNone)
  -- each sequential child's own theorem at the full entry
  let mut seqRuns : Std.HashMap Name Name := {}
  for c in seqKids do
    seqRuns := seqRuns.insert c (← (try generateSeqChild c catch e => throwError "seq child {c}: {e.toMessageData}"))
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let (dE, _mE, _dsnE) := (tyArgs[2]!, tyArgs[3]!, tyArgs[4]!)
  -- the families over the sequential children
  let bsTy ← inferType (← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[dE])
  let outsTy ← inferType (← mkAppM ``Sparkle.IR.Machine.Layout.outs
    #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE]]])
  let nat := mkConst ``Nat
  let valsTy ← mkArrow nat (mkApp (mkConst ``List [.zero]) nat)
  let obsTy := mkApp (mkConst ``List [.zero]) (← mkArrow nat nat)
  let mut bsCases : List (Name × Lean.Expr) := []
  let mut outsCases : List (Name × Lean.Expr) := []
  -- the parent's family index type and domain map
  let ιP := tyArgs[5]!
  let domP := tyArgs[6]!
  -- a child's source at the child index matching parent index `iv`, and its domain
  let srcAt (c : Name) (iv : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
    let csrc := mkConst (c ++ `machineSource)
    let ιc := (← inferType csrc).bindingDomain!
    let idx ← if ιc.isConstOf ``Unit then pure (mkConst ``Unit.unit)
      else whnf (mkApp domP iv)
    let src0 := mkApp csrc idx
    let Dc := ((← whnf (← inferType src0)).bindingDomain!).bindingBody!.getAppArgs[0]!
    pure (src0, Dc, idx)
  for c in seqKids do
    let cd := mkConst (c ++ `machineData)
    let bsIn ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[cd]
    bsCases := bsCases ++ [(c, bsIn)]
    outsCases := outsCases ++ [(c, ← mkAppM ``Sparkle.IR.Machine.Layout.outs
      #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[cd]]])]
  let bsC ← nameCases bsTy bsCases (mkApp (mkConst ``List.nil [.zero]) bsTy.appArg!)
  let outsC ← nameCases outsTy outsCases (mkApp (mkConst ``List.nil [.zero]) outsTy.appArg!)
  let natNat ← mkArrow nat nat
  let sDflt ← withLocalDeclD `vals valsTy fun vals =>
    mkLambdaFVars #[vals] (mkApp (mkConst ``List.nil [.zero]) natNat)
  let S ← withLocalDeclD `i ιP fun iv => do
    let mut sCases : List (Name × Lean.Expr) := []
    for (c, bsIn) in bsCases do
      let (src0, Dc, _) ← srcAt c iv
      let sF ← withLocalDeclD `vals valsTy fun vals => do
        mkLambdaFVars #[vals] (mkApp2 src0
          (← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsIn, vals])
          (← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsIn, vals]))
      sCases := sCases ++ [(c, sF)]
    mkLambdaFVars #[iv] (← nameCases (← mkArrow valsTy obsTy) sCases sDflt)
  -- each sequential child's machine shape (its `MachineRun`)
  let shapeT := mkConst ``Sparkle.Compiler.Elab.MachineShape
  let shCases ← seqKids.mapM fun c => do
    pure (c, ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)])
  let some (_, sh0) := shCases.head? | throwError "{declName}: no sequential child"
  let shC ← nameCases shapeT shCases sh0
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTR.machine_linkedT_callsR #[h]
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  p := mkApp4 p bsC outsC S shC
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    let names := calls.map (·.1)
    -- the parent's let observations and call extension at this family point
    let lsrcE := (tyArgs[10]!).beta ibb
    let extE := (tyArgs[8]!).beta ibb
    let extBE := (tyArgs[9]!).beta ibb
    -- the call extension's definition, for the calls' argument Signals
    let unfoldExt (e : Lean.Expr) : MetaM Lean.Expr := do
      let e ← whnfCore e.headBeta
      let f := e.getAppFn
      if let .const n _ := f then
        if let some v := (← getEnv).find? n >>= (·.value?) then
          return (v.beta e.getAppArgs).headBeta
      pure e
    let extBody ← unfoldExt extE
    let extBBody ← unfoldExt extBE
    let mut perK : Array Lean.Expr := #[]
    for k in [0:calls.length] do
      let some (c, argsK, _) := calls[k]? | throwError "{declName}: call {k}"
      let goalK := ((rest.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
        (toExpr c)).bindingBody!
      let proofK ← match Tools.ShippingMachineMemCommand.memWidths? c with
        | some (cb, aw, dw) =>
          proveByTacticT goalK (do pure (← memTactic k cb aw dw argsK))
        | none => try do
          let some seqRun := seqRuns.get? c | throwError "{declName}: child {c}"
          let (src0, Dc, idxE) ← srcAt c ibb[0]!
          -- the call: its signal at the call's port, and its arguments
          let pos := r.nDecl + k
          let some sig := (sigAtPos pos extBody).orElse fun _ => sigAtPos pos extBBody
            | throwError "{declName}: call {k}: no signal at port {pos}"
          let some call := findCall c sig | throwError "{declName}: call {k}: no call of {c}"
          let callArgs := call.getAppArgs
          let cr ← readMachine c
          let bsIn : List (Name × MixedGateBinder) := cr.shape.binders.take cr.nDecl
          unless callArgs.size == bsIn.length do
            throwError "{declName}: call {k}: {callArgs.size} arguments, {bsIn.length} binders"
          -- the child's output read by this call
          let field := r.shape.instFields.getD k ""
          let some k' := cr.shape.layout.outs.findIdx? (fun (o : Sparkle.IR.Machine.OutField) => o.name == field)
            | throwError "{declName}: call {k}: field {field}"
          let bsInE ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst (c ++ `machineData)]
          let vs ← mkAppM ``Tools.ShippingMachineCallsLinkedT.valsOf
            #[lsrcE, listE nat (argsK.map mkNatLit)]
          -- the families the decoded inputs are: the call's arguments at their positions
          let mut A ← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsInE, vs]
          let mut B ← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsInE, vs]
          for (pIdx, bnd) in (List.range bsIn.length).zip bsIn do
            let kind : MixedGateBinder := bnd.2
            if kind == MixedGateBinder.bool then
              A ← mkAppM ``Tools.ShippingMachineCausal.extendBools #[A, mkNatLit pIdx, callArgs[pIdx]!]
            if let .bits w := kind then
              B ← mkAppM ``Tools.ShippingMachineAuto.extendBits
                #[B, mkNatLit pIdx, mkNatLit w, callArgs[pIdx]!]
          let kinds : List MixedGateBinder := bsIn.map (fun b => b.2)
          let tyA ← inferType A
          let tyB ← inferType B
          let tyI ← inferType idxE
          let srcE := src0
          let tyS ← inferType srcE
          let pr ← withLetDecl `famA tyA A fun aF => withLetDecl `famB tyB B fun bF =>
            withLetDecl `famI tyI idxE fun iF => withLetDecl `famS tyS srcE fun sF => do
           let pr ← proveByTacticT goalK (do
            let lit (n : Nat) := Syntax.mkNumLit (toString n)
            let argsArr : Array Term := (argsK.map fun n => (⟨lit n⟩ : Term)).toArray
            let argsS ← `([$argsArr,*])
            let srcS : Term := ⟨mkIdent `famS⟩
            let idxS : Term := ⟨mkIdent `famI⟩
            let AS : Term := ⟨mkIdent `famA⟩
            let BS : Term := ⟨mkIdent `famB⟩
            let rangeS ← rangeSyntax kinds
            let seqRunS := mkIdent (`_root_ ++ seqRun)
            `(tactic| (
              right
              unfold Tools.ShippingMachineCallsLinkedTR.SeqFactsR
              refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, $(lit k'), _, _, rfl, rfl, ?f, fun τ => rfl⟩
              case b =>
                intro mc hmr
                obtain ⟨_, _, _, _, _, _, _, hr', entry', closes'⟩ := hmr
                exact ⟨$seqRunS $idxS hr' entry' closes',
                  by rw [($seqRunS $idxS hr' entry' closes').2.2.2.2.2.1]; decide⟩
              case l =>
                exact Tools.ShippingMachineCallsLinkedT.args_facts (by decide)
                  (by simp [Tools.ShippingMachineCausal.letObsB, Tools.ShippingMachineCausal.letObsLoop,
                    Tools.ShippingMachineCausal.letObsComb])
              case r =>
                intro τ
                unfold Tools.ShippingMachineChild.InRange
                exact $rangeS
              case f =>
                exact (congrArg (fun l => l[$(lit k')]?)
                  (Tools.ShippingMachineCallsLinkedT.decoded_eq (bools' := $AS) (bits' := $BS) $srcS
                    (by
                      funext p
                      try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineCausal.extendBools]
                      (repeat' split) <;> (first
                        | (rename_i hp; subst hp; exact Tools.ShippingMachineCallsLinkedT.boolsOf_at
                            (fun τ => Tools.ShippingMachineCallsLinkedT.decB_valsOf rfl (by decide) rfl τ))
                        | rfl))
                    (by
                      funext p n
                      try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineAuto.extendBits]
                      (repeat' split) <;> (first
                        | (rename_i hp; obtain ⟨hp1, hp2⟩ := hp; subst hp1; subst hp2; (try simp only [cast_eq]); exact Tools.ShippingMachineCallsLinkedT.bitsOf_at
                            (fun τ => Tools.ShippingMachineCallsLinkedT.decV_valsOf rfl (by decide) rfl τ))
                        | rfl)))).trans rfl)))
           pure ((← instantiateMVars pr).replaceFVar aF A |>.replaceFVar bF B |>.replaceFVar iF idxE
             |>.replaceFVar sF srcE)
          pure pr
          catch e => throwError "call {k}: {e.toMessageData}"
      try check proofK catch e => throwError "call {k} proof ill-formed: {e.toMessageData}"
      perK := perK.push proofK
    -- the chain over the call list
    let nameT := mkConst ``Name
    let Qm (m : Nat) : MetaM Lean.Expr :=
      withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
        let rk := ((rest.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
          cv).bindingBody!
        mkLambdaFVars #[kv, cv] rk
    let n := names.length
    let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← Qm n]
    for m' in [0:n] do
      let m := n - 1 - m'
      let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
      chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
        #[nameT, ← Qm m, toExpr names[m]!, rest', perK[m]!, chain]
    withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
      let hkT := ((rest.bindingBody!.instantiate1 kv).bindingBody!.instantiate1 cv).bindingDomain!
      withLocalDeclD `hk hkT fun hk => do
        mkLambdaFVars (ibb ++ #[kv, cv, hk]) (mkAppN chain #[kv, cv, hk])
  try check hcalls catch e => throwError "hcalls ill-formed: {e.toMessageData}"
  p := mkApp p hcalls
  -- the children's reflection facts: ONE premise, the conjunction over the
  -- sequential children of what each child's declaration is (`MachineDefines`,
  -- in the parent's contexts) and — unless the child has no `let` and no call,
  -- where it is a theorem (`c.machine_closes`: no call, `let`s that pass `MachineData.letsOk`) — that its machine
  -- synthesis closes in the contexts the child is synthesised in
  let hreflT := (← whnf (← inferType p)).bindingDomain!
  let ctx ← forallTelescope hreflT fun _ body => do
    let some (a, _) := body.and? | throwError "{declName}: the reflection premise's shape"
    pure a.getAppArgs[0:4].toArray
  let mut rTypes : List Lean.Expr := []
  let mut freeOf : Std.HashMap Name Bool := {}
  for c in seqKids do
    let shapeE ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]
    let defs := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineDefines) (ctx ++ #[toExpr c, shapeE])
    let free ← (do pure (← Tools.ShippingMachineClosesGen.closesTheorem? c).isSome)
    freeOf := freeOf.insert c free
    if free then rTypes := rTypes ++ [defs]
    else
      let closes ← withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc' =>
        withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc' => do
          mkForallFVars #[mc', cc'] (← mkArrow
            (mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc'])
            (mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineCloses) #[mc', ctx[1]!, cc', ctx[3]!, toExpr c, shapeE]))
      rTypes := rTypes ++ [← mkAppM ``And #[defs, closes]]
  let hreflNewT ← Tools.ShippingMachineShipsHierCommand.conj rTypes
  withLocalDeclD `hrefl hreflNewT fun hrefl => do
  let ps ← Tools.ShippingMachineShipsHierCommand.projs hrefl rTypes
  let rDecls := (seqKids.zip rTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hR{j}", fun (_ : Array Lean.Expr) => pure ty)
  let hreflP ← withLocalDeclsD rDecls fun hRs => do
    let names := calls.map (·.1)
    let nameT := mkConst ``Name
    let mut perR : Array Lean.Expr := #[]
    for k in [0:names.length] do
      let c := names[k]!
      let goalK := ((hreflT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
        (toExpr c)).bindingBody!
      let hRS : Term := ⟨mkIdent (Name.mkSimple s!"hR{seqKids.idxOf c}")⟩
      let prK ← match Tools.ShippingMachineMemCommand.memWidths? c with
        | some _ => proveByTacticT goalK `(tactic| (intro h; first | cases h | simp [Sparkle.Compiler.MachMemory.memChild?] at h))
        | none =>
          if freeOf.getD c false then
            proveByTacticT goalK `(tactic| (intro _; exact ⟨$hRS, fun _ _ _ =>
              $(mkIdent (`_root_ ++ c ++ `machine_closes)) _ _ _ _⟩))
          else proveByTacticT goalK `(tactic| (intro _; exact $hRS))
      perR := perR.push prK
    let QmR (m : Nat) : MetaM Lean.Expr :=
      withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
        let rk := ((hreflT.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
          cv).bindingBody!
        mkLambdaFVars #[kv, cv] rk
    let n := names.length
    let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← QmR n]
    for m' in [0:n] do
      let m := n - 1 - m'
      let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
      chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
        #[nameT, ← QmR m, toExpr names[m]!, rest', perR[m]!, chain]
    pure (chain.replaceFVars hRs ps.toArray)
  let p := mkApp p hreflP
  -- the child boundary of the run (`ChildBnd`: the laws and the invariant in
  -- the run's start world)
  let hsyn := xs.back!
  let mut value ← mkLambdaFVars (xs.pop ++ #[hsyn, hrefl]) p
  if let some (heq, srcN) := back? then
    let T ← inferType value
    let motT ← kabstract T srcN
    unless motT.hasLooseBVars do throwError "{declName}: the theorem does not read the source"
    let hT ← mkCongrArg (.lam `s (← inferType srcN) motT .default) heq
    value ← mkEqMPR hT value
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name


def generateSR (declName : Name) (atW : Bool := false) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateCoreSR declName atW)
  catch ex =>
    setEnv saved
    throw ex

open Lean.Elab.Command in
elab "#machine_composedTSR " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generateSR declName)
  logInfo m!"{name}: the stateful linked run, its sequential children's instances derived to be runs of their entries (ChildBnd), shows the source, checked by the kernel"

/-- `f.machine_ships_hierR`: `machine_ships_hierC` from `f.machine_composedTRA`
(closing premise `MachineClosesAt`); its run boundary `Bnd` is `ChildBnd` and
the children's reflection facts, in the run's contexts. -/
def generateShipsR (declName : Name) : MetaM Name := do
  let cR ← generateSR declName (atW := true)
  let (headL, _, _) ← endpointParts declName
  Tools.ShippingMachineShipsHierCommand.generateWith declName
    cR (declName ++ `machine_ships_hierR) (headA? := some (headL.appendAfter "RA"))

/-- `f.machine_design_svR0`: source → the closed emitted texts (`ships_design_svN_all` at
depth 0) from `f.machine_ships_hierR`. -/
def generateDesignR0 (declName : Name) : MetaM Name := do
  let ships ← generateShipsR declName
  Tools.ShippingShipsDesignSVCommand.compose declName ships (declName ++ `machine_design_svR0) 0

open Lean.Elab.Command in
elab "#machine_design_svR0 " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateDesignR0 declName)
  logInfo m!"{name}: source → shipped design's closed emitted texts, the child-run boundary derived (ChildBnd at the run's start world + the children's reflection), checked by the kernel"

end Tools.ShippingMachineSeqCommand
