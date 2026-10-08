import Tools.ShippingMachineMemCommand
import Tools.ShippingMachineCallsLinkedT
import Tools.ShippingGateChild
import Tools.ShippingMachineLoopL

/-! # Generated composition with memory and sequential children

`#machine_composedT f` for a declaration whose calls are memory reads and
calls of sequential machine children (`circuit do`s with registers and no
calls of their own): each sequential child `c` gets `c.seq_child_run` (its
module at the full entry runs as its source over time, `seqChildRun_full`),
and `f.machine_composedT` is `machine_linkedT_calls` with, per call, its
`MemFacts` or `SeqFacts`. A sequential call's facts rest on the run boundary:
the generated theorem takes, per sequential child, that the module an
instance of its calls resolves to is a run of the full entry on the child
(`MachineRun`). The call's value is the child's source on the decoded
argument stream: the decoded inputs are the call's argument Signals
(`boolsOf_at` / `bitsOf_at`), after which the two sides agree by `rfl`. -/
namespace Tools.ShippingMachineSeqCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem soundArgs)

/-- The run boundary of a sequential child `c`: the module an instance of its
calls resolves to is a run of the full entry on `c`. -/
def BoundaryOf (insts : List (Name × List Nat × MixedGateBinder)) (dsn : Sparkle.IR.AST.Design)
    (body : List Sparkle.IR.AST.Stmt) (c : Name) (shape : MachineShape) : Prop :=
  ∀ (k : Nat) (mc : Sparkle.IR.AST.Module), (insts.map (·.1))[k]? = some c →
    Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
    Tools.ShippingMachineCallsLinkedT.InstOfCall body mc k →
    Tools.ShippingGateChild.MachineRun c shape mc

/-- Run a tactic built in the same elaboration (it may embed expressions). -/
def proveByTacticT (goal : Lean.Expr) (mkTac : Term.TermElabM Syntax) : MetaM Lean.Expr := do
  let mvar ← mkFreshExprMVar goal
  let ((), _) ← (Term.TermElabM.run (do
    let tac ← mkTac
    let gs ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
    unless gs.isEmpty do throwError "goals remain: {gs}")) {}
  instantiateMVars mvar

/-- `c.seq_child_run`: a sequential child's module at the full entry is a
`SeqChildRun` of its source (`seqChildRun_full` at the child's endpoint). -/
def generateSeqChild (c : Name) : MetaM Name := do
  let name := c ++ `seq_child_run
  if (← getEnv).contains name then return name
  -- the endpoint's wired twin (a `circuit do`, a `Signal.loop`, a register
  -- product: the same conclusion form)
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
  let mut p ← mkAppOptM ``Tools.ShippingMachineSeqInst.seqChildRun_full
    #[none, none, none, none, none, none, soundL]
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  addTheorem name (← inferType p) p
  return name

/-- The endpoint of a declaration, its wired twin's head, and a transport
back to the declaration (fused / sign-normalised values). -/
def endpointParts (declName : Name) :
    MetaM (Name × Array Lean.Expr × Option (Lean.Expr × Lean.Expr)) := do
  let some (.thmInfo ti) := (← getEnv).find? (declName ++ `machine_sound)
    | throwError "{declName}: no machine_sound"
  let mut v := ti.value
  let mut back? : Option (Lean.Expr × Lean.Expr) := none
  if v.isAppOfArity ``Eq.mpr 4 then
    let hT := v.getAppArgs[2]!
    unless hT.isAppOfArity ``congrArg 6 do throwError "{declName}: the endpoint's transport"
    let heq := hT.getAppArgs[5]!
    let some (_, _, srcN) := (← inferType heq).eq? | throwError "{declName}: the transport's equation"
    back? := some (heq, srcN)
    v := v.getAppArgs[3]!
  let headL ← if v.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_loop_causal then
      pure ``Tools.ShippingMachineCausal.machine_traceL_of_loop_causal
    else if v.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_comb_calls then
      pure ``Tools.ShippingMachineCausal.machine_traceL_of_comb_calls
    else if v.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_data_causal then
      pure ``Tools.ShippingMachineCausal.machine_traceL_of_data_causal
    else throwError "{declName}.machine_sound: no wired twin for its head"
  return (headL, v.getAppArgs, back?)

/-- `if n = c₁ then e₁ else … else dflt`, over child names. -/
def nameCases (ty : Lean.Expr) (cases : List (Name × Lean.Expr)) (dflt : Lean.Expr) :
    MetaM Lean.Expr :=
  withLocalDeclD `n (mkConst ``Name) fun n => do
    let mut e := dflt
    for (c, v) in cases.reverse do
      e ← mkAppOptM ``ite #[ty, ← mkEq n (toExpr c), none, v, e]
    mkLambdaFVars #[n] e

/-- The call `c a₀ … aₙ` (head `c`) inside a term. -/
partial def findCall (c : Name) (e : Lean.Expr) : Option Lean.Expr :=
  if e.getAppFn.isConstOf c then some e
  else match e with
    | .app f a => (findCall c f).orElse fun _ => findCall c a
    | .lam _ t b _ => (findCall c t).orElse fun _ => findCall c b
    | .letE _ t v b _ => ((findCall c t).orElse fun _ => findCall c v).orElse fun _ => findCall c b
    | .mdata _ b => findCall c b
    | .proj _ _ b => findCall c b
    | _ => none

/-- The signal an `extendBits` / `extendBools` nest puts at position `pos`. -/
partial def sigAtPos (pos : Nat) (e : Lean.Expr) : Option Lean.Expr :=
  let e := e.headBeta
  if e.isAppOfArity ``Tools.ShippingMachineAuto.extendBits 5 then
    let a := e.getAppArgs
    if a[2]!.nat? == some pos || a[2]!.rawNatLit? == some pos then some a[4]!
    else sigAtPos pos a[1]!
  else if e.isAppOfArity ``Tools.ShippingMachineCausal.extendBools 4 then
    let a := e.getAppArgs
    if a[2]!.nat? == some pos || a[2]!.rawNatLit? == some pos then some a[3]!
    else sigAtPos pos a[1]!
  else none

/-- The tactic proving a memory call's facts. -/
def memTactic (cb : Bool) (aw dw : Nat) (args : List Nat) : MetaM Syntax := do
  let [l0, l1, l2, l3] := args | throwError "a memory call with {args.length} arguments"
  let lit (n : Nat) := Syntax.mkNumLit (toString n)
  let cbE ← if cb then `(true) else `(false)
  `(tactic| (
      left
      unfold Tools.ShippingMachineCallsLinkedT.MemFacts
      refine ⟨$cbE, $(lit aw), $(lit dw), ?A, ?D, ?E, ?R, $(lit l0), $(lit l1), $(lit l2), $(lit l3),
        rfl, rfl, ?h0, by decide, ?h1, by decide, ?h2, by decide, ?h3, by decide, rfl, ?hx⟩
      case hx => (intro j; rfl)
      all_goals rfl))

/-- The range proof of a sequential call's argument stream. -/
def rangeSyntax (kinds : List MixedGateBinder) : MetaM Term := do
  let mut t : Term ← `(Tools.ShippingMachineClose.Zip₂.nil)
  for k in kinds.reverse do
    match k with
    | .bits _ => t ← `(Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _) $t)
    | .bool => t ← `(Tools.ShippingMachineClose.Zip₂.cons (Tools.ShippingMachineChild.encodeBool_lt _) $t)
    | .domain => pure ()
  pure t

def generateCoreS (declName : Name) : MetaM Name := do
  progress s!"{declName}: composedT (sequential)"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  let (headL, args, back?) ← endpointParts declName
  let pL := mkAppN (mkConst headL) args
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
  -- the boundary: per sequential child, its instances' modules are runs of the full entry on it
  let bTypes ← seqKids.mapM fun c => do
    let insts ← mkAppM ``Sparkle.Compiler.Elab.MachineShape.insts
      #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE]]
    let body ← mkAppM ``Sparkle.IR.AST.Module.body #[mE]
    let cshape ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]
    pure (mkAppN (mkConst ``BoundaryOf) #[insts, dsnE, body, toExpr c, cshape])
  let bDecls := (seqKids.zip bTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hB{j}", fun (_ : Array Lean.Expr) => pure ty)
  withLocalDeclsD bDecls fun hBs => do
  let hBOf : Std.HashMap Name Lean.Expr := Id.run do
    let mut m : Std.HashMap Name Lean.Expr := {}
    for (c, hb) in seqKids.zip hBs.toList do m := m.insert c hb
    m
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedT.machine_linkedT_calls #[h]
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
            `(tactic| (
              right
              unfold Tools.ShippingMachineCallsLinkedT.SeqFacts
              refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, $(lit k'), _, _, rfl, rfl, ?f, fun τ => rfl⟩
              case b =>
                intro mc hmc hinst
                obtain ⟨_, _, _, _, _, _, _, hr', entry', closes'⟩ := $hBS $(lit k) mc rfl hmc hinst
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
  let mut value ← mkLambdaFVars (xs ++ hBs) p
  if let some (heq, srcN) := back? then
    let T ← inferType value
    let motT ← kabstract T srcN
    unless motT.hasLooseBVars do throwError "{declName}: the theorem does not read the source"
    let hT ← mkCongrArg (.lam `s (← inferType srcN) motT .default) heq
    value ← mkEqMPR hT value
  let name := declName ++ `machine_composedT
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name

def generateS (declName : Name) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateCoreS declName)
  catch ex =>
    setEnv saved
    throw ex

/-- The composition with the children: memory reads only
(`ShippingMachineMemCommand.generate`), or memory reads and sequential calls
(`generateS`). -/
def generateAny (declName : Name) : MetaM Name := do
  let r ← readMachine declName
  if r.shape.insts.all (fun (c, _, _) => (Tools.ShippingMachineMemCommand.memWidths? c).isSome) then
    Tools.ShippingMachineMemCommand.generate declName
  else generateS declName

open Lean.Elab.Command in
elab "#machine_composedTS " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generateAny declName)
  logInfo m!"{name}: the stateful linked run of the emitted module, its memories and sequential children stepping from reset, shows the source, checked by the kernel"

end Tools.ShippingMachineSeqCommand
