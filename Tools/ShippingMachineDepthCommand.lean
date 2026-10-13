import Tools.ShippingMachineSeqCommand
import Tools.ShippingMachineDepthRun
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingMachineShipsDepth
import Tools.ShippingMachineDepthH

/-! # Generated composition at depth

`#machine_composedN f n` proves `f.machine_composedN{n}`: the stateful linked
run of `f`'s module, its children stepping at depth `n` (`KSn`), shows the
source (`machine_linkedT_callsN n`, with the module's wiring). A sequential
child without calls holds at every depth (`c.seq_child_runN`,
`seqChildRunN_full`); a child with calls holds at depth `n` from its own
composed theorem at depth `n - 1` (`c.seq_child_runN_of{n-1}`,
`seqChildRunN_of_composed`), generated recursively, under the hierarchical
run boundary `MachineRunN`. The theorem's run boundaries are bundled into one
premise, `f.machineBoundN{n}`. -/
namespace Tools.ShippingMachineDepthCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem soundArgs)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineShipsHierCommand (conj projs)

/-- The run boundary of a sequential child with calls, at depth. -/
def BoundaryOfN (insts : List (Name × List Nat × MixedGateBinder)) (dsn : Sparkle.IR.AST.Design)
    (body : List Sparkle.IR.AST.Stmt) (c : Name) (shape : MachineShape)
    (Bnd : Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop) : Prop :=
  ∀ (k : Nat) (mc : Sparkle.IR.AST.Module), (insts.map (·.1))[k]? = some c →
    Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
    Tools.ShippingMachineCallsLinkedT.InstOfCall body mc k →
    Tools.ShippingMachineDepthRun.MachineRunN c shape Bnd mc dsn

def composedName (n : Nat) : Name := Name.mkSimple s!"machine_composedN{n}"
def boundName (n : Nat) : Name := Name.mkSimple s!"machineBoundN{n}"
def runOfName (n : Nat) : Name := Name.mkSimple s!"seq_child_runN_of{n}"

/-- The proof of `c.seq_child_runN` (built, not added): `seqChildRunN_full`
at the wired twin of the child's endpoint, its eight data conditions decided.
The endpoint may be built from `machine_trace_of_data` (a `circuit do`),
`machine_trace_of_loop` (a `Signal.loop`) or `machine_trace_of_regs` (a
register product): the three wired twins have the conclusion
`seqChildRunN_full` takes — the head table of the depth-0 `generateSeqChild`
(`Tools/ShippingMachineSeqCommand.lean`). -/
def seqChildNProof (c : Name) : MetaM Lean.Expr := do
  let some (.thmInfo ti) := (← getEnv).find? (c ++ `machine_sound)
    | throwError "{c}: no machine_sound"
  let v := ti.value
  let headL ← if v.isAppOf ``Tools.ShippingMachineAuto.machine_trace_of_data then
      pure ``Tools.ShippingMachineCausal.machine_traceL_of_data
    else if v.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_loop then
      pure ``Tools.ShippingMachineLoopL.machine_traceL_of_loop
    else if v.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_regs then
      pure ``Tools.ShippingMachineLoopL.machine_traceL_of_regs
    else throwError "{c}.machine_sound is not built from Tools.ShippingMachineAuto.machine_trace_of_data, _of_loop or _of_regs"
  let soundL := mkAppN (mkConst headL) v.getAppArgs
  let mut p ← mkAppOptM ``Tools.ShippingMachineDepthRun.seqChildRunN_full
    #[none, none, none, none, none, none, soundL]
  for _ in [0:8] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  return p

/-- `c.seq_child_runN`: a sequential child without calls, at every depth. An
existing constant of that name is returned as it is (not compared: see
`compareSeqChildN`). -/
def generateSeqChildN (c : Name) : MetaM Name := do
  let name := c ++ `seq_child_runN
  if (← getEnv).contains name then return name
  let p ← seqChildNProof c
  addTheorem name (← inferType p) p
  return name

/-- The compare path: `c.seq_child_runN` EXISTS (written by hand or by an
earlier generator); the statement is rebuilt by `seqChildNProof` and must be
`isDefEq` the existing one — an error otherwise. Returns the rebuilt proof
and whether the two statements are the same term. Adds nothing. -/
def compareSeqChildN (c : Name) : MetaM (Lean.Expr × Bool) := do
  let name := c ++ `seq_child_runN
  let some (.thmInfo told) := (← getEnv).find? name
    | throwError "{name}: not a theorem of the environment (nothing to compare)"
  let p ← seqChildNProof c
  let ty ← instantiateMVars (← inferType p)
  let same : Bool := ty == told.type
  unless same do
    unless ← isDefEq ty told.type do
      throwError "{name}: the statement the generator builds is NOT the existing one (isDefEq false)"
  return (p, same)

/-- The tactic: a call extension agrees with the inputs below the calls. -/
def extTactic (extName : Name) : MetaM Syntax := do
  let e := mkIdent (`_root_ ++ extName)
  `(tactic| (
    intro _ _ _ j _ hj
    delta $e:ident
    simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
    (repeat' split) <;> first | rfl | (exfalso; omega)))

def extBTactic (extName : Name) : MetaM Syntax := do
  let e := mkIdent (`_root_ ++ extName)
  `(tactic| (
    intro _ _ _ j hj
    delta $e:ident
    simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
    (repeat' split) <;> first | rfl | (exfalso; omega)))

mutual

/-- `c.seq_child_runN_of{n}`: a child with calls, at depth `n + 1`, from its
composed theorem at depth `n`. -/
partial def generateRunOf (c : Name) (n : Nat) : MetaM Name := do
  let name := c ++ runOfName n
  if (← getEnv).contains name then return name
  let cT ← generateCoreN c n
  let bnd := mkConst (c ++ boundName n)
  let mut p ← mkAppM ``Tools.ShippingMachineDepthRun.seqChildRunN_of_composed
    #[mkNatLit n, bnd, mkConst cT]
  for _ in [0:10] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  let tyB := (← whnf (← inferType p)).bindingDomain!
  p := mkApp p (← if (← getEnv).contains (c ++ `machineExtB) then
      proveByTacticT tyB (extBTactic (c ++ `machineExtB))
    else proveByTacticT tyB `(tactic| (intro _ _ _ _ _; rfl)))
  let tyE := (← whnf (← inferType p)).bindingDomain!
  p := mkApp p (← proveByTacticT tyE (extTactic (c ++ `machineExt)))
  addTheorem name (← inferType p) p
  return name

partial def generateCoreN (declName : Name) (dep : Nat) : MetaM Name := do
  let name := declName ++ composedName dep
  if (← getEnv).contains name then return name
  progress s!"{declName}: composedN {dep}"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  -- calls of one-output combinational children (`closeInsts`): the composed
  -- theorem `f.machine_composed` at depth 0 (`composedN0_of_H`)
  if r.shape.instFields.isEmpty then
    if dep != 0 then throwError "{declName}: combinational children below depth 0 (not yet)"
    unless (← getEnv).contains (declName ++ `machine_composed) do
      throwError "{declName}: run #machine_composed {declName} first"
    let thm ← mkAppOptM ``Tools.ShippingMachineDepthH.composedN0_of_H
      #[none, none, none, none, none, none, none, none, mkConst (declName ++ `machine_composed)]
    let thm ← instantiateMVars thm
    if thm.hasMVar then throwError "{declName}: the calls' premise was not read"
    -- the boundary: `BndH R declName d`, read off the theorem
    let ty ← inferType thm
    let bndE ← forallTelescope ty fun ys _ => do
      let hBT ← inferType ys[ys.size - 1]!
      unless hBT.isAppOf ``Tools.ShippingMachineDepthH.BndH do
        throwError "{declName}: the boundary's form"
      let args := hBT.getAppArgs
      pure (mkApp3 (mkConst ``Tools.ShippingMachineDepthH.BndH) args[0]! args[1]! args[2]!)
    let bName := declName ++ boundName 0
    let bTy ← inferType bndE
    let decl : DefinitionVal :=
      { name := bName, levelParams := [], type := bTy, value := bndE,
        hints := .abbrev, safety := .safe }
    addDecl (.defnDecl decl)
    addTheorem name (← inferType thm) thm
    return name
  let (headL, args, back?) ← endpointParts declName
  let pL := mkAppN (mkConst headL) args
  let calls := r.shape.insts
  let seqKids := ((calls.map (·.1)).eraseDups.filter fun c =>
    (Tools.ShippingMachineMemCommand.memWidths? c).isNone)
  -- each sequential child's own theorem: without calls at any depth; with
  -- calls, from its composed theorem one level down
  let mut seqRuns : Std.HashMap Name Name := {}
  let mut leaf : Std.HashMap Name Bool := {}
  for c in seqKids do
    let cr ← readMachine c
    let isLeaf := cr.shape.insts.isEmpty
    leaf := leaf.insert c isLeaf
    if isLeaf then
      seqRuns := seqRuns.insert c (← (try generateSeqChildN c catch e => throwError "seq child {c}: {e.toMessageData}"))
    else
      if dep == 0 then throwError "{declName}: the child {c} has children; depth 0 is too shallow"
      seqRuns := seqRuns.insert c (← (try generateRunOf c (dep - 1) catch e => throwError "child {c}: {e.toMessageData}"))
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 10 do throwError "{declName}: the trace's arguments"
  let (dE, mE, dsnE) := (tyArgs[1]!, tyArgs[2]!, tyArgs[3]!)
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
  let ιP := tyArgs[4]!
  let domP := tyArgs[5]!
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
    let bsIn0 ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[cd]
    let bsIn ← if leaf.getD c true then pure bsIn0
      else mkAppM ``List.take #[mkNatLit (← readMachine c).nDecl, bsIn0]
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
  -- the boundary: per sequential child, its instances' modules are runs of the full entry on it
  let bTypes ← seqKids.mapM fun c => do
    let insts ← mkAppM ``Sparkle.Compiler.Elab.MachineShape.insts
      #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE]]
    let body ← mkAppM ``Sparkle.IR.AST.Module.body #[mE]
    let cshape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]
    if leaf.getD c true then
      pure (mkAppN (mkConst ``Tools.ShippingMachineSeqCommand.BoundaryOf) #[insts, dsnE, body, toExpr c, cshape])
    else
      pure (mkAppN (mkConst ``BoundaryOfN)
        #[insts, dsnE, body, toExpr c, cshape, mkConst (c ++ boundName (dep - 1))])
  let bDecls := (seqKids.zip bTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hB{j}", fun (_ : Array Lean.Expr) => pure ty)
  withLocalDeclsD bDecls fun hBs => do
  let hBOf : Std.HashMap Name Lean.Expr := Id.run do
    let mut m : Std.HashMap Name Lean.Expr := {}
    for (c, hb) in seqKids.zip hBs.toList do m := m.insert c hb
    m
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTN.machine_linkedT_callsN #[mkNatLit dep, h]
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  p := mkApp3 p bsC outsC S
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    let names := calls.map (·.1)
    -- the parent's let observations and call extension at this family point
    let lsrcE := (tyArgs[9]!).beta ibb
    let extE := (tyArgs[7]!).beta ibb
    let extBE := (tyArgs[8]!).beta ibb
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
          proveByTacticT goalK (do pure (← memTactic cb aw dw argsK))
        | none => try do
          let some seqRun := seqRuns.get? c | throwError "{declName}: child {c}"
          let some hB := hBOf.get? c | throwError "{declName}: boundary {c}"
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
          let bsInE0 ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst (c ++ `machineData)]
          let bsInE ← if leaf.getD c true then pure bsInE0
            else mkAppM ``List.take #[mkNatLit cr.nDecl, bsInE0]
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
          let jB := (seqKids.idxOf c)
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
            let hBS : Term := ⟨mkIdent (Name.mkSimple s!"hB{jB}")⟩
            let srcS : Term := ⟨mkIdent `famS⟩
            let idxS : Term := ⟨mkIdent `famI⟩
            let AS : Term := ⟨mkIdent `famA⟩
            let BS : Term := ⟨mkIdent `famB⟩
            let rangeS ← rangeSyntax kinds
            let seqRunS := mkIdent (`_root_ ++ seqRun)
            let caseB ← if leaf.getD c true then
                `(tactic| (
                  obtain ⟨_, _, _, _, _, _, _, hr', entry', closes'⟩ := $hBS $(lit k) mc rfl hmc hinst
                  refine ⟨$seqRunS $idxS hr' entry' closes' _ _ _, ?_⟩
                  rw [($seqRunS $idxS hr' entry' closes' (fun _ => none)
                    { topModule := "", modules := [] } 0).2.2.2.2.2.1]
                  decide))
              else
                `(tactic| (
                  have hrn := $hBS $(lit k) mc rfl hmc hinst
                  exact ⟨$seqRunS $idxS hrn, by rw [($seqRunS $idxS hrn).2.2.2.2.2.1]; decide⟩))
            `(tactic| (
              right
              unfold Tools.ShippingMachineCallsLinkedTN.SeqFactsN
              refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, $(lit k'), _, _, rfl, rfl, ?f, fun τ => rfl⟩
              case b =>
                intro mc hmc hinst
                $caseB:tactic
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
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  -- the boundaries, bundled into one premise `machineBoundN{dep}` of the core run
  let bnd ← conj bTypes
  let bndName := declName ++ boundName dep
  let bndV ← mkLambdaFVars #[mE, dsnE] bnd
  Tools.ShippingMachineCommand.addDef bndName (← inferType bndV) bndV
  let bndApp := mkApp2 (mkConst bndName) mE dsnE
  let value ← withLocalDeclD `hBnd bndApp fun hBnd => do
    let ps ← projs hBnd bTypes
    let p' := p.replaceFVars hBs ps.toArray
    mkLambdaFVars (xs ++ #[hBnd]) p'
  let name := declName ++ composedName dep
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name

end

elab "#machine_composedN " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateCoreN declName n.getNat)
  logInfo m!"{name}: the stateful linked run, children at depth {n.getNat}, shows the source, checked by the kernel"

/-- `f.machine_ships_hierN{n}`: `machine_ships_hier` at depth `n`, the
children's output bound from the decidable `kidsMaskedN`. -/
def generateShipsN (declName : Name) (n : Nat) : MetaM Name := do
  let name := declName ++ Name.mkSimple s!"machine_ships_hierN{n}"
  if (← getEnv).contains name then return name
  let cN ← generateCoreN declName n
  let (headL, args, back?) ← endpointParts declName
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  let soundL := mkAppN (mkConst headL) args
  let cT := mkConst cN
  let data := mkConst (declName ++ `machineData)
  let bnd := mkConst (declName ++ boundName n)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let nE := mkNatLit n
  forallTelescope (← inferType cT) fun ys _ => do
    unless ys.size == 12 do throwError "{declName}: the composed theorem's binders ({ys.size})"
    let m := ys[6]!
    let memF ← mkAppM ``Tools.ConeFold.memFree #[← mkAppM ``Sparkle.IR.AST.Module.body #[m]]
    let composed ← withLocalDeclD `hm memF fun hm => do
      let inner ← mkAppM ``Tools.ShippingMachineShipsDepth.composedG_of_NW #[mkAppN cT ys]
      mkLambdaFVars (ys ++ #[hm]) inner
    let KS ← withLocalDeclD `D desT fun D => do
      mkLambdaFVars #[D] (← mkAppM ``Tools.ShippingHierStateG.KSn
        #[← mkAppM ``Tools.ShippingMachineLinked.childMap #[← mkAppM ``Sparkle.IR.AST.Design.modules #[D]], nE])
    let hloc ← withLocalDeclD `D desT fun D => do
      mkLambdaFVars #[D] (← mkAppM ``Tools.ShippingHierStateG.KSn_local
        #[← mkAppM ``Tools.ShippingMachineLinked.childMap #[← mkAppM ``Sparkle.IR.AST.Design.modules #[D]], nE])
    let reset := mkApp (mkConst ``Tools.ShippingMachineShipsDepth.ResetNk) nE
    let (Bd, hBd) ← withLocalDeclD `b modT fun b => withLocalDeclD `D desT fun D => do
      let ms ← mkAppM ``Sparkle.IR.AST.Design.modules #[D]
      let body ← mkAppM ``Sparkle.IR.AST.Module.body #[b]
      let bd ← mkEq (← mkAppM ``Tools.ShippingMachineShipsDepth.kidsMaskedN #[ms, body]) (mkConst ``Bool.true)
      let Bd ← mkLambdaFVars #[b, D] bd
      let hBd ← withLocalDeclD `h bd fun h => do
        mkLambdaFVars #[b, D, h] (mkApp (← mkAppM ``Tools.ShippingMachineShipsDepth.KSn_boundedIn
          #[ms, body, h]) nE)
      pure (Bd, hBd)
    let ktT := mkApp (mkConst ``Tools.ShippingHierStateG.KT) nE
    let inv ← withLocalDeclD `c modT fun c => withLocalDeclD `s ktT fun sv =>
      mkLambdaFVars #[c, sv] (mkConst ``True)
    let hRI ← mkAppM ``Tools.ShippingMachineShipsHier.true_inv #[reset]
    let thm ← mkAppM ``Tools.ShippingMachineShipsHier.machine_ships_hier
      #[KS, hloc, reset, ← mkAppM ``Tools.ShippingMachineShipsHier.ctxFree #[bnd], Bd, inv, hBd, hRI, data, soundL, composed]
    let ty ← inferType thm
    let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
    let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
    let name := declName ++ Name.mkSimple s!"machine_ships_hierN{n}"
    addTheorem name (← inferType thm) thm
    return name

elab "#machine_ships_hierN " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateShipsN declName n.getNat)
  logInfo m!"{name}: the shipped module's stateful linked run, children at depth {n.getNat}, shows the source, checked by the kernel"

end Tools.ShippingMachineDepthCommand
