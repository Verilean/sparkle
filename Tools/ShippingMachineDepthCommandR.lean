import Tools.ShippingMachineDepthCommand
import Tools.ShippingMachineCallsLinkedTNR
import Tools.ShippingMachineSeqLinkedR
import Tools.ShippingShipsDesignSVCommand
import Tools.ShippingMachineComposeRCommand
import Tools.ShippingMachineDepthHR
import Tools.ShippingChildRun
import Tools.ShippingReflectCtx
import Tools.ShippingMachineClosesGen
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingChildIfaceGen

/-! # Generated composition at depth `n`, the instance binding derived

`#machine_design_svNR f n`: as `#machine_design_svN`, through
`machine_linkedT_callsRN` from the wired endpoint carrying `ServedReal` (the
`R` heads, under `ChildBnd`). The run boundary, in the run's contexts, is
`ChildBnd` and per sequential child its premise: the reflection facts
(a child without calls), or that every run of its entry satisfies its depth
conditions (`MachineRunN`: its own boundary, `ExtendsAway`, `NoInstOf`). No
premise about the parent's instances (`BoundaryOf` / `BoundaryOfN`). -/
namespace Tools.ShippingMachineDepthCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem soundArgs)
open Tools.ShippingMachineSeqCommand
open Tools.ShippingMachineShipsHierCommand (conj projs)

/-- A derived composed theorem's run boundary (its last premise), as a
boundary in the run's contexts (`CtxBnd`): it depends on the contexts only. -/
def bndOfComposed (cT : Name) : MetaM Lean.Expr := do
  forallTelescope (← inferType (mkConst cT)) fun ys _ => do
    unless ys.size == 12 do throwError "{cT}: the composed theorem's binders ({ys.size})"
    mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!, ys[4]!, ys[6]!, ys[7]!] (← inferType ys[11]!)

/-- `c.machine_composedNRH{n}` for a child with one-output combinational
calls, at depth `n` (depth is an upper bound: `composedNn_of_HR` over
`c.machine_composedR`, its children combinational at every depth). -/
def generateCombNR (c : Name) (n : Nat) : MetaM Name := do
  let name := c ++ Name.mkSimple s!"machine_composedNRH{n}"
  if (← getEnv).contains name then return name
  let cR ← Tools.ShippingMachineComposeRCommand.generateComposedR c (atW := true)
  let rest ← forallTelescope (← inferType (mkConst cR)) fun ys _ => do
    unless ys.size == 12 do throwError "{cR}: binders ({ys.size})"
    let bT ← whnfR (← inferType ys[11]!)
    unless bT.isAppOfArity ``And 2 do throwError "{cR}: the boundary is not ChildBnd ∧ …"
    mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!] bT.appArg!
  let f := mkApp (mkConst ``Tools.ShippingMachineDepthHR.composedNn_of_HR) (mkNatLit n)
  let (ms, _, _) ← forallMetaBoundedTelescope (← inferType f) 7
  let f7 := mkAppN f ms
  let fR := mkApp f7 rest
  let fT ← whnf (← inferType fR)
  -- the composed theorem fixes the implicit arguments
  let compT := ((← whnf fT.bindingBody!).bindingBody!).bindingDomain!
  unless ← isDefEq compT (← inferType (mkConst cR)) do
    throwError "{c}: the derived composed theorem does not match"
  let fR ← instantiateMVars fR
  let hsT := (← whnf (← inferType fR)).bindingDomain!
  let p1 := mkApp fR (← mkDecideProof hsT)
  let hiT := (← whnf (← inferType p1)).bindingDomain!
  let p2 := mkApp p1 (← mkDecideProof hiT)
  let p ← instantiateMVars (mkApp p2 (mkConst cR))
  if p.hasMVar then throwError "{c}: arguments not inferred"
  addTheorem name (← inferType p) p
  return name

/-- The components of a proof of a conjunction. -/
partial def andParts (h : Lean.Expr) : MetaM (List (Lean.Expr × Lean.Expr)) := do
  let t ← whnfR (← inferType h)
  if t.isAppOfArity ``And 2 then
    return (← andParts (← mkAppM ``And.left #[h])) ++ (← andParts (← mkAppM ``And.right #[h]))
  else return [(t, h)]

/-- The closing theorem of `c`: `c.machine_closes_at` (one-output calls, or
the general closing over children without calls), else `c.closes_deep` (over
children with calls). -/
def closingThm? (c : Name) : MetaM (Option Name) := do
  if (← getEnv).contains (c ++ `machine_closes_at) then return some (c ++ `machine_closes_at)
  if (← getEnv).contains (c ++ `closes_deep) then return some (c ++ `closes_deep)
  return none

/-- The premises of `c`'s closing theorem that the child's boundary does not
carry, in the theorem's order: the name separation (context-free), and the
reflection of a descendant of `c` that is not a direct child — stated in the
contexts `ctx` (the run's own; a reflection does not depend on the contexts,
`Tools.ShippingReflectCtx`). `none`: no such theorem, or a premise of another
form. -/
def closesAtNames (c : Name) (ctx : Array Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let some thm ← closingThm? c | return none
  let some (.thmInfo info) := (← getEnv).find? thm | return none
  -- the child's boundary carries the reflection of its DIRECT children only
  let kids ← try pure ((← readMachine c).shape.insts.map (·.1)) catch _ => return none
  forallTelescope (← instantiateForall info.type ctx) fun xs _ => do
    let mut out : List Lean.Expr := []
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines ||
          t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines then
        let arg := t.getArg! 4
        unless ← kids.anyM fun k => isDefEq (toExpr k) arg do
          if xs.any fun y => t.containsFVar y.fvarId! then return none
          out := out ++ [t]
      else
        if t.hasFVar then return none
        out := out ++ [t]
    return some out

/-- A reflection `h` moved to the contexts of `dom` (`MachineDefines.ctx` /
`EntryDefines.ctx`); `none` when `dom` is not that reflection. -/
def reflectAt? (dom h : Lean.Expr) : MetaM (Option Lean.Expr) := do
  for lem in [``Tools.ShippingReflectCtx.MachineDefines.ctx, ``Tools.ShippingReflectCtx.EntryDefines.ctx] do
    let r ← observing? do
      let e ← mkConstWithFreshMVarLevels lem
      let (args, _, ty) ← forallMetaTelescope (← inferType e)
      unless ← isDefEq ty dom do throwError "conclusion"
      let some hArg := args.back? | throwError "no premise"
      unless ← isDefEq (← inferType hArg) (← inferType h) do throwError "premise"
      unless ← isDefEq hArg h do throwError "assign"
      let pr ← instantiateMVars (mkAppN e args)
      if pr.hasExprMVar then throwError "unassigned"
      pure pr
    if let some pr := r then return some pr
  return none

/-- `MachineClosesAt ctx c c.shape` from `c.machine_closes_at`: its reflection
premises from the components of the child's boundary `hb` (at `ctx`), its
name premises from `names`. -/
def closesAtProof (c : Name) (ctx : Array Lean.Expr) (hb : Lean.Expr) (names : List Lean.Expr) :
    MetaM Lean.Expr := do
  let parts ← andParts hb
  let some thm ← closingThm? c | throwError "{c}: no closing theorem"
  let mut p := mkAppN (mkConst thm) ctx
  let mut names := names
  for _ in [0:64] do
    let t ← instantiateMVars (← inferType p)
    if t.isAppOf ``Tools.ShippingChildInv.MachineClosesAt then return p
    unless t.isForall do throwError "{thm}: its statement"
    let dom := t.bindingDomain!
    let mut arg? : Option Lean.Expr := none
    for (pt, ph) in parts do
      if arg?.isNone then
        if ← isDefEq pt dom then arg? := some ph
    if arg?.isNone then
      if let n :: rest := names then
        if ← isDefEq (← inferType n) dom then
          arg? := some n
          names := rest
        else if let some pr ← reflectAt? dom n then
          -- a deeper descendant's reflection, asked in the run's contexts
          arg? := some pr
          names := rest
    let some arg := arg? | throwError "{thm}: no proof of its premise {dom}"
    p := mkApp p arg
  throwError "{thm}: too many premises"

mutual

/-- `c.seq_child_runN_ofR{n}`: a child with calls, at depth `n + 1`, from its
DERIVED composed theorem at depth `n`; returns it and that theorem's boundary. -/
partial def generateRunOfR (c : Name) (n : Nat) : MetaM (Name × Lean.Expr) := do
  let cr ← readMachine c
  let cT ← if cr.shape.instFields.isEmpty then generateCombNR c n
    else generateCoreNR c n
  let bnd ← bndOfComposed cT
  let name := c ++ Name.mkSimple s!"seq_child_runN_ofR{n}"
  if (← getEnv).contains name then return (name, bnd)
  let mut p ← mkAppM ``Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC
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
  return (name, bnd)

partial def generateCoreNR (declName : Name) (dep : Nat) : MetaM Name := do
  let name := declName ++ Name.mkSimple s!"machine_composedNR{dep}"
  if (← getEnv).contains name then return name
  progress s!"{declName}: composedNR {dep}"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  if r.shape.instFields.isEmpty then
    throwError "{declName}: one-output combinational calls (the derived boundary needs the general closing)"
  let (headL, args, back?) ← endpointParts declName
  -- the head carrying `ServedReal` (under `ChildBnd`)
  let pL := mkAppN (mkConst (headL.appendAfter "RA")) args
  let calls := r.shape.insts
  let seqKids := ((calls.map (·.1)).eraseDups.filter fun c =>
    (Tools.ShippingMachineMemCommand.memWidths? c).isNone)
  -- each sequential child's own theorem: without calls at any depth; with
  -- calls, from its composed theorem one level down
  let mut seqRuns : Std.HashMap Name Name := {}
  let mut leaf : Std.HashMap Name Bool := {}
  let mut bndOf : Std.HashMap Name Lean.Expr := {}
  for c in seqKids do
    let cr ← readMachine c
    let isLeaf := cr.shape.insts.isEmpty
    leaf := leaf.insert c isLeaf
    if isLeaf then
      seqRuns := seqRuns.insert c (← (try generateSeqChildN c catch e => throwError "seq child {c}: {e.toMessageData}"))
    else
      if dep == 0 then throwError "{declName}: the child {c} has children; depth 0 is too shallow"
      let (rn, bnd) ← (try generateRunOfR c (dep - 1) catch e => throwError "child {c}: {e.toMessageData}")
      seqRuns := seqRuns.insert c rn
      bndOf := bndOf.insert c bnd
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let (dE, _mE, dsnE) := (tyArgs[2]!, tyArgs[3]!, tyArgs[4]!)
  -- the run's contexts (the endpoint's binders) and its `ChildBnd` premise
  let hsyn := xs.back!
  let ctxOf (n : Name) : MetaM Lean.Expr := do
    for x in xs do
      if (← whnfR (← inferType x)).isAppOf n then return x
    throwError "{declName}: no binder of type {n}"
  let refOf (st : Name) : MetaM Lean.Expr := do
    for x in xs do
      let t ← whnfR (← inferType x)
      if t.isAppOf ``ST.Ref && (t.getAppArgs.back?.map (·.isConstOf st)).getD false then return x
    throwError "{declName}: no reference to {st}"
  let ctx := #[← ctxOf ``Lean.Meta.Context, ← refOf ``Lean.Meta.State, ← ctxOf ``Lean.Core.Context,
    ← refOf ``Lean.Core.State]
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
  -- per sequential child: its predicate `PC c` (`MachineRun` without calls,
  -- `MachineRunN` with them), and its premise in the run's contexts — the
  -- reflection facts (no calls), or that every run of its entry satisfies
  -- its depth conditions (with calls)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let mut pcCases : List (Name × Lean.Expr) := []
  let mut pTypes : List Lean.Expr := []
  let mut freeOf : Std.HashMap Name Bool := {}
  -- children with calls whose closing is derived: the name premises it asks
  let mut namesOf : Std.HashMap Name (List Lean.Expr) := {}
  for c in seqKids do
    unless leaf.getD c true do
      match ← closesAtNames c ctx with
      | some names => namesOf := namesOf.insert c names
      | none =>
        -- not silently: the endpoint will ASK this child's closing
        logWarning m!"{declName}: the closing of the child {c} stays a premise of this endpoint (MachineClosesAt in the contexts {c} is synthesised in): there is no {c}.machine_closes_at"
  for c in seqKids do
    let cshape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]
    let pcF ← withLocalDeclD `mc modT fun mc => do
      if leaf.getD c true then
        mkLambdaFVars #[mc] (← mkAppM ``Tools.ShippingGateChild.MachineRun #[toExpr c, cshape, mc])
      else
        let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
        mkLambdaFVars #[mc] (← mkAppM ``Tools.ShippingMachineDepthRun.MachineRunNC
          #[toExpr c, cshape, bnd, mc, dsnE])
    pcCases := pcCases ++ [(c, pcF)]
    -- what the child's declaration is (`MachineDefines`): asked ONCE, in the
    -- run's own contexts — it does not depend on them (`MachineDefines.ctx`).
    -- That its machine synthesis closes, and its own boundary: in the Meta
    -- and Core contexts the child is synthesised in (`ChildRanIn`: its entry
    -- has a run there, over the run's state references)
    let defs0 := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineDefines) (ctx ++ #[toExpr c, cshape])
    let pT ← withLocalDeclD `mctx' (mkConst ``Lean.Meta.Context) fun mc' =>
      withLocalDeclD `cctx' (mkConst ``Lean.Core.Context) fun cc' => do
      let ctx' := #[mc', ctx[1]!, cc', ctx[3]!]
      let closes := mkAppN (mkConst ``Tools.ShippingMachineEntry.MachineCloses) (ctx' ++ #[toExpr c, cshape])
      -- a child with calls: where the real compile runs its machine synthesis
      -- (`MachineClosesAt`) — not asked when `c.machine_closes_at` derives it
      -- from the child's own boundary (its children's reflection)
      let closesAt := mkAppN (mkConst ``Tools.ShippingChildInv.MachineClosesAt) (ctx' ++ #[toExpr c, cshape])
      let body ← if leaf.getD c true then pure closes
        else do
          -- with calls: its reflection facts and its own derived boundary, in
          -- every start world where the child boundary holds
          -- (`machineRunNC_of_real` derives the rest from the run the compile used)
          let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
          let bndHere ← withLocalDeclD `wc (mkConst ``Void [] |>.app (mkConst ``IO.RealWorld)) fun wc =>
            withLocalDeclD `raw modT fun raw => withLocalDeclD `D desT fun dD => do
            let cb := mkAppN (mkConst ``Tools.ShippingChildInv.ChildBnd) #[ctx[1]!, ctx[3]!, wc]
            mkForallFVars #[wc, raw, dD] (← mkArrow cb (bnd.beta (ctx' ++ #[wc, raw, dD])).headBeta)
          if (namesOf.get? c).isSome then pure bndHere else mkAppM ``And #[closesAt, bndHere]
      let ran := mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc']
      mkForallFVars #[mc', cc'] (← mkArrow ran body)
    -- (a leaf child without `let`s closes in every context: proved,
    -- `c.machine_closes`: no call, `let`s that pass `MachineData.letsOk` — only its `MachineDefines` is asked)
    let free ← if leaf.getD c true then (do pure (← Tools.ShippingMachineClosesGen.closesTheorem? c).isSome) else pure false
    freeOf := freeOf.insert c free
    pTypes := pTypes ++ [← if free then pure defs0
      else match namesOf.get? c with
        | some names => do mkAppM ``And #[defs0, ← mkAppM ``And #[← conj names, pT]]
        | none => mkAppM ``And #[defs0, pT]]
  let some (_, pc0) := pcCases.head? | throwError "{declName}: no sequential child"
  let PC ← nameCases (← mkArrow modT (mkSort .zero)) pcCases pc0
  let pDecls := (seqKids.zip pTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hP{j}", fun (_ : Array Lean.Expr) => pure ty)
  withLocalDeclsD pDecls fun hPs => do
  let hPOf : Std.HashMap Name Lean.Expr := Id.run do
    let mut m : Std.HashMap Name Lean.Expr := {}
    for (c, hb) in seqKids.zip hPs.toList do m := m.insert c hb
    m
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN #[mkNatLit dep, h]
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  p := mkApp4 p bsC outsC S PC
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
          proveByTacticT goalK (do pure (← memTactic cb aw dw argsK))
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
            let caseB ← if leaf.getD c true then
                `(tactic| (
                  obtain ⟨_, _, _, _, _, _, _, hr', entry', closes'⟩ := hmr
                  refine ⟨$seqRunS $idxS hr' entry' closes' _ _ _, ?_⟩
                  rw [($seqRunS $idxS hr' entry' closes' (fun _ => none)
                    { topModule := "", modules := [] } 0).2.2.2.2.2.1]
                  decide))
              else
                `(tactic| (
                  have hrn := hmr
                  exact ⟨$seqRunS $idxS hrn, by rw [($seqRunS $idxS hrn).2.2.2.2.2.1]; decide⟩))
            `(tactic| (
              right
              unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
              refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, $(lit k'), _, _, rfl, rfl, ?f, fun τ => rfl⟩
              case b =>
                intro mc hmr
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
  -- `hrunN`, call by call, from the children's premises
  let hrunNT := (← whnf (← inferType p)).bindingDomain!
  let names := calls.map (·.1)
  let mut perR : Array Lean.Expr := #[]
  for k in [0:calls.length] do
    let some (c, _, _) := calls[k]? | throwError "{declName}: call {k}"
    let goalK := ((hrunNT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
      (toExpr c)).bindingBody!
    let prK ← match Tools.ShippingMachineMemCommand.memWidths? c with
      | some _ => proveByTacticT goalK `(tactic| (intro h; first | cases h | simp [Sparkle.Compiler.MachMemory.memChild?] at h))
      | none => do
        let some hP := hPOf.get? c | throwError "{declName}: premise {c}"
        let j := seqKids.idxOf c
        let hPS : Term := ⟨mkIdent (Name.mkSimple s!"hP{j}")⟩
        let _ := hP
        if freeOf.getD c false then
          proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun _ _; exact ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx $hPS, $(mkIdent (`_root_ ++ c ++ `machine_closes)) _ _ _ _⟩))
        else if leaf.getD c true then
          proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun _ _; exact ⟨_, _, _, _, w, w', Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx ($hPS).1, ($hPS).2 mctx' cctx' (Tools.ShippingChildInv.ChildRanIn.of_run hw hrun)⟩))
        else match namesOf.get? c with
          | none =>
            proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun hcons _; exact Tools.ShippingMachineDepthRun.machineRunNC_of_real (Tools.ShippingChildInv.RealChild.of_inv hw hrun) hcons ($hPS).1 (fun mc cc ran => (($hPS).2 mc cc ran).2) (fun mc cc _ _ _ ran _ => (($hPS).2 mc cc ran).1) (by decide)))
          | some names => do
            -- the closing, from the child's boundary: `c.machine_closes_at`
            let some bnd := bndOf.get? c | throwError "{declName}: boundary of {c}"
            let worldT := mkApp (mkConst ``Void []) (mkConst ``IO.RealWorld)
            let hclE ← withLocalDeclD `mc (mkConst ``Lean.Meta.Context) fun mc' =>
              withLocalDeclD `cc (mkConst ``Lean.Core.Context) fun cc' =>
              withLocalDeclD `wc worldT fun wc =>
              withLocalDeclD `raw modT fun raw => withLocalDeclD `D desT fun dD => do
              let ctx' := #[mc', ctx[1]!, cc', ctx[3]!]
              let ran := mkAppN (mkConst ``Tools.ShippingChildInv.ChildRanIn) #[ctx[1]!, ctx[3]!, toExpr c, mc', cc']
              withLocalDeclD `ran ran fun hran =>
              withLocalDeclD `hb (bnd.beta (ctx' ++ #[wc, raw, dD])).headBeta fun hb => do
                let nameHs ← projs (← mkAppM ``And.left #[← mkAppM ``And.right #[hP]]) names
                mkLambdaFVars #[mc', cc', wc, raw, dD, hran, hb] (← closesAtProof c ctx' hb nameHs)
            withLocalDeclD `hclC (← inferType hclE) fun hclV => do
              let pr ← proveByTacticT goalK `(tactic| (intro _ mctx' cctx' mc Dc w w' hw hrun hcons _; exact Tools.ShippingMachineDepthRun.machineRunNC_of_real (Tools.ShippingChildInv.RealChild.of_inv hw hrun) hcons ($hPS).1 (fun mc cc ran => ($hPS).2.2 mc cc ran) $(mkIdent `hclC) (by decide)))
              pure ((← mkLambdaFVars #[hclV] pr).beta #[hclE])
    perR := perR.push prK
  let nameT := mkConst ``Name
  let nat := mkConst ``Nat
  let QmR (m : Nat) : MetaM Lean.Expr :=
    withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
      let rk := ((hrunNT.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
        cv).bindingBody!
      mkLambdaFVars #[kv, cv] rk
  let n := names.length
  let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil #[nameT, ← QmR n]
  for m' in [0:n] do
    let m := n - 1 - m'
    let rest' := listE nameT ((names.drop (m + 1)).map toExpr)
    chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
      #[nameT, ← QmR m, toExpr names[m]!, rest', perR[m]!, chain]
  p := mkApp p chain
  -- the boundary in the run's contexts: `ChildBnd` and the children's premises, bundled
  let bTypes := (← inferType hsyn) :: pTypes
  let bnd ← conj bTypes
  let value ← withLocalDeclD `hBnd bnd fun hBnd => do
    let ps ← projs hBnd bTypes
    let p' := p.replaceFVars (#[hsyn] ++ hPs) ps.toArray
    mkLambdaFVars (xs.pop ++ #[hBnd]) p'
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name

end

def generateShipsNR (declName : Name) (n : Nat) : MetaM Name := do
  let name := declName ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  if (← getEnv).contains name then return name
  let cN ← generateCoreNR declName n
  let (headL, args, back?) ← endpointParts declName
  if back?.isSome then throwError "{declName}: a transported endpoint (not yet at depth)"
  let soundL := mkAppN (mkConst headL) args
  let cT := mkConst cN
  let data := mkConst (declName ++ `machineData)
  let modT := mkConst ``Sparkle.IR.AST.Module
  let desT := mkConst ``Sparkle.IR.AST.Design
  let nE := mkNatLit n
  forallTelescope (← inferType cT) fun ys _ => do
    unless ys.size == 12 do throwError "{declName}: the composed theorem's binders ({ys.size})"
    let m := ys[6]!
    -- the run boundary in the run's contexts: the composed theorem's last premise
    let Bnd ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!, ys[4]!, m, ys[7]!] (← inferType ys[11]!)
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
    -- the closing premise of the composed theorem (`MachineClosesAt`), and the
    -- wired endpoint from the head asking the same, under the run boundary
    let _ := soundL
    let C ← mkLambdaFVars #[ys[0]!, ys[1]!, ys[2]!, ys[3]!] (← inferType ys[10]!)
    let pLA := mkAppN (mkConst (headL.appendAfter "RA")) args
    let soundA ← forallTelescope (← inferType pLA) fun zs _ => do
      unless zs.size == 12 do throwError "{declName}: the head's binders ({zs.size})"
      let bndT := (Bnd.beta #[zs[0]!, zs[1]!, zs[2]!, zs[3]!, zs[4]!, zs[6]!, zs[7]!]).headBeta
      withLocalDeclD `hB bndT fun hB => do
        let hsynT ← inferType zs[11]!
        let hsyn ← if ← isDefEq bndT hsynT then pure hB else mkAppM ``And.left #[hB]
        let tr ← mkAppM ``Tools.ShippingMachineTraceX.MachineTraceLBX.toLB
          #[(mkAppN pLA zs).replaceFVar zs[11]! hsyn]
        mkLambdaFVars (zs.pop ++ #[hB]) tr
    let thm ← mkAppOptM ``Tools.ShippingMachineShipsHier.machine_ships_hierC
      #[none, KS, hloc, reset, Bnd, C, Bd, inv, hBd, hRI, none, data, none, none, none, none,
        none, none, none, none, none, none, soundA, composed]
    let thm ← instantiateMVars thm
    let ty ← inferType thm
    let .forallE _ hT _ _ ← whnfR ty | throwError "{declName}: the output-width premise"
    let thm := mkApp thm (← mkExpectedTypeHint (← mkDecideProof hT) hT)
    let name := declName ++ Name.mkSimple s!"machine_ships_hierNR{n}"
    addTheorem name (← inferType thm) thm
    return name


/-- `f.machine_design_svNR{n}` from `f.machine_ships_hierNR{n}`. -/
def generateDesignNR (declName : Name) (n : Nat) : MetaM Name := do
  let ships ← generateShipsNR declName n
  Tools.ShippingShipsDesignSVCommand.compose declName ships
    (declName ++ Name.mkSimple s!"machine_design_svNR{n}") n

/-- The machine descendants of `declName` that have calls (candidates of
`c.machine_closes_at`: one-output calls, or the general closing), children
first. -/
partial def closingCandidates (declName : Name) (seen : IO.Ref (List Name)) : MetaM (List Name) := do
  let r ← try readMachine declName catch _ => return []
  let mut out : List Name := []
  for (c, _, _) in r.shape.insts do
    if (Tools.ShippingMachineMemCommand.memWidths? c).isSome || (← seen.get).contains c then continue
    seen.modify (c :: ·)
    out := out ++ (← closingCandidates c seen)
    let cr? ← try some <$> readMachine c catch _ => pure none
    if let some cr := cr? then
      if !cr.shape.insts.isEmpty then out := out ++ [c]
  return out

/-- Generate `c.machine_closes_at` for the descendants that can have one,
BEFORE the depth endpoint (which uses an existing theorem only): the result
does not depend on the order the user ran the commands in. A descendant whose
closing is not derived is reported; its closing stays a premise. -/
def preClose (declName : Name) : Command.CommandElabM Unit := do
  let cands ← Command.liftTermElabM do closingCandidates declName (← IO.mkRef [])
  for c in cands do
    unless (← getEnv).contains (c ++ `machine_closes_at) || (← getEnv).contains (c ++ `closes_deep) do
      try
        discard <| Tools.ShippingMachineClosesAtGen.closesAtTheorem c
        logInfo m!"{c}.machine_closes_at: generated for the depth endpoint of {declName}"
      catch ex =>
        -- a descendant whose children have calls: the deep generator
        let savedEnv ← getEnv
        let savedMsgs := (← get).messages
        try
          discard <| Command.withScope (fun s => { s with opts := Lean.Elab.async.set s.opts false })
            (Tools.ShippingChildIfaceGen.closesDeep c)
          logInfo m!"{c}.closes_deep: generated for the depth endpoint of {declName}"
        catch ex2 =>
          setEnv savedEnv
          modify fun s => { s with messages := savedMsgs }
          logInfo m!"{declName}: the closing of the descendant {c} is NOT derived — it stays a premise of the depth endpoint ({ex.toMessageData}; {ex2.toMessageData})"

elab "#machine_design_svNR " d:ident n:num : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  preClose declName
  let name ← Command.liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateDesignNR declName n.getNat)
  logInfo m!"{name}: source → shipped design's closed emitted texts at depth {n.getNat}, the instance binding derived (ChildBnd at the run's start world + the children's premises), checked by the kernel"

end Tools.ShippingMachineDepthCommand
