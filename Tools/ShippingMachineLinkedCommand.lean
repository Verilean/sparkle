import Tools.ShippingMachineCommand
import Tools.ShippingMachineChild

/-! # Generated linked endpoints

`#machine_child c` (after `#machine_endpoint c`, for a combinational child
on the machine route) adds `c.machine_child`: a run of the full entry on
`c` returns a module that, when the run's zero-width cleanup changes
nothing, computes `c`'s source function on its argument ports
(`Tools.ShippingMachineChild.child_full`).

`#machine_linked f` (after `#machine_endpoint` on `f` and on every child
`f` calls) adds `f.machine_linked`: the LINKED run of the module the core
entry returns — each instance evaluated by the module its name resolves to
in the design — shows `f`, seeded with `f`'s own inputs only, provided every
call's module computes its child's source function
(`Tools.ShippingMachineCompose.machine_linked_calls`). The calls' equations
are discharged here, per call: the argument values are the `let` wires'
(a kernel `rfl`), in range (`BitVec.isLt`), and the child's function on
them is the call's value (decoding is the inverse of encoding, then the
child is pointwise: a kernel `rfl`). -/
namespace Tools.ShippingMachineLinkedCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)

/-- Run a tactic on a goal; the proof term. -/
def proveByTactic (goal : Lean.Expr) (tac : Syntax) : MetaM Lean.Expr := do
  let mvar ← mkFreshExprMVar goal
  let ((), _) ← (Term.TermElabM.run (do
    let gs ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
    unless gs.isEmpty do throwError "goals remain: {gs}")) {}
  instantiateMVars mvar

/-- Add a theorem (kernel-checked, axioms audited). -/
def addTheorem (name : Name) (type value : Lean.Expr) : MetaM Unit := do
  addDecl (.thmDecl { name, levelParams := [], type, value })
  for ax in ← Lean.collectAxioms name do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"

/-- The arguments of an endpoint's proof whose head is `head`. -/
def soundArgs (declName : Name) (head : Name) : MetaM (Array Lean.Expr) := do
  let ci ← getConstInfo (declName ++ `machine_sound)
  let v ← match ci with
    | .thmInfo t => pure t.value
    | _ => throwError "{declName}.machine_sound is not a theorem"
  unless v.isAppOf head do
    throwError "{declName}.machine_sound is not built from {head}"
  return v.getAppArgs

/-! ## The child -/

def generateChildCore (declName : Name) : MetaM Name := do
  let args ← soundArgs declName ``Tools.ShippingMachineLoop.machine_trace_of_comb
  let soundL := mkAppN (mkConst ``Tools.ShippingMachineChild.machine_traceL_of_comb) args
  -- args: declName d ι dom inits src checks…
  let data := args[1]!
  let ι := args[2]!
  let src := args[5]!
  let i0 ← if ι.isConstOf ``Unit then pure (mkConst ``Unit.unit)
    else pure (mkConst ``Sparkle.Core.Domain.defaultDomain)
  let mut p ← mkAppOptM ``Tools.ShippingMachineChild.child_full
    #[none, none, none, none, none, soundL]
  -- the decidable facts about the data
  for _ in [0:5] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  -- the source has one observation
  let hsrcT := (← whnf (← inferType p)).bindingDomain!
  let hsrc ← forallTelescope hsrcT fun xs eq => do
    let some (α, lhs, _) := eq.eq? | throwError "{declName}: the source's length"
    mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α lhs)
  p := mkApp p hsrc
  p := mkApp p i0
  let _ := (data, src)
  let name := declName ++ `machine_child
  addTheorem name (← inferType p) p
  return name

def generateChild (declName : Name) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => Lean.Elab.async.set o false) (generateChildCore declName)
  catch ex =>
    setEnv saved
    throw ex

open Lean.Elab.Command in
elab "#machine_child " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generateChild declName)
  logInfo m!"{name}: the child's full-entry module computes its source function, checked by the kernel"

/-! ## The parent -/

/-- The tactic for a call's range premise: one `BitVec.isLt` (or the Bool
bound) per argument port. -/
def rangeTactic (kinds : List MixedGateBinder) : MetaM Syntax := do
  let mut t ← `(Tools.ShippingMachineClose.Zip₂.nil)
  for k in kinds.reverse do
    match k with
    | .bits _ => t ← `(Tools.ShippingMachineClose.Zip₂.cons (BitVec.isLt _) $t)
    | .bool => t ← `(Tools.ShippingMachineClose.Zip₂.cons (Tools.ShippingMachineChild.encodeBool_lt _) $t)
    | .domain => pure ()
  `(tactic| (delta Tools.ShippingMachineChild.childRange; exact $t))

/-- The tactic for a call's value premise: decode the argument values
(`portIdx` by `decide`, decoding inverts encoding), then the child is
pointwise (`rfl`). -/
def valueTactic (childSrc childData : Name) (kinds : List MixedGateBinder) : MetaM Syntax := do
  let srcId := mkIdent childSrc
  let bsE ← `($(mkIdent childData).bsIn)
  -- one `portIdx` fact per binder position, by `decide`
  let mut tac ← `(tactic| (
      delta Tools.ShippingMachineChild.childValue $srcId
      simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some,
        Tools.ShippingMachineChild.decV, Tools.ShippingMachineChild.decB, *,
        List.getD_cons_zero, List.getD_cons_succ, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        Tools.ShippingMachineChild.encodeBool_ne]
      rfl))
  let mut q := 0
  let mut facts : Array (Nat × Nat) := #[]
  for (pos, k) in (List.range kinds.length).zip kinds do
    if k != .domain then
      facts := facts.push (pos, q)
      q := q + 1
  for (pos, qq) in facts.reverse do
    let posL := Syntax.mkNumLit (toString pos)
    let qL := Syntax.mkNumLit (toString qq)
    let h := mkIdent (Name.mkSimple s!"hp{pos}")
    tac ← `(tactic| (
      have $h : Tools.ShippingMachineChild.portIdx $bsE $posL = $qL := by decide
      $tac:tactic))
  return tac

def generateLinkedCore (declName : Name) : MetaM Name := do
  progress s!"{declName}: linked"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no hardware-module call"
  if r.shape.layout.slots.isEmpty || !r.shape.loops.isEmpty then
    throwError "{declName}: only a circuit do with slots (and sub-machines) is supported"
  let (head, headL) := if r.nested then
      (``Tools.ShippingMachineNest.machine_trace_of_nested_ext,
        ``Tools.ShippingMachineNest.machine_traceL_of_nested_ext)
    else (``Tools.ShippingMachineAuto.machine_trace_of_data_ext,
      ``Tools.ShippingMachineAuto.machine_traceL_of_data_ext)
  let args ← soundArgs declName head
  let pL := mkAppN (mkConst headL) args
  let data := args[1]!
  let pLT ← inferType pL
  forallTelescope pLT fun xs traceT => do
  let h := mkAppN pL xs
  let traceT ← whnfR traceT
  let tyArgs := (← instantiateMVars traceT).getAppArgs
  unless tyArgs.size == 9 do throwError "{declName}: the trace's arguments"
  let mut p := mkAppN (mkConst ``Tools.ShippingMachineCompose.machine_linked_calls)
    (tyArgs ++ #[h, mkNatLit r.nDecl])
  -- the decidable facts about the data
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  -- the children's ranges and functions
  let mut Ps : Array Lean.Expr := #[]
  let mut Fs : Array Lean.Expr := #[]
  let mut childInfo : Array (Name × Name × List MixedGateBinder) := #[]
  for (c, _, _) in r.shape.insts do
    let cData := c ++ `machineData
    let cSrc := c ++ `machineSource
    unless (← getEnv).contains cSrc do
      throwError "{declName}: run #machine_endpoint {c} first"
    let srcT ← inferType (mkConst cSrc)
    let ιc := srcT.bindingDomain!
    let i0 := if ιc.isConstOf ``Unit then mkConst ``Unit.unit
      else mkConst ``Sparkle.Core.Domain.defaultDomain
    Ps := Ps.push (mkApp (mkConst ``Tools.ShippingMachineChild.childRange) (mkConst cData))
    Fs := Fs.push (← mkAppM ``Tools.ShippingMachineChild.childValue
      #[mkConst cSrc, ← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst cData], i0])
    -- the child's binder kinds (its declaration's binders)
    let cr ← readMachine c
    childInfo := childInfo.push (cSrc, cData, cr.shape.binders.take cr.nDecl |>.map (·.2))
  let nat := mkConst ``Nat
  let listNat := mkApp (mkConst ``List [.zero]) nat
  let PT ← mkArrow listNat (mkSort .zero)
  let FT ← mkArrow listNat nat
  let PT' := PT
  let FT' := FT
  let PE ← withLocalDeclD `k nat fun k => do
    mkLambdaFVars #[k] (← mkAppM ``List.getD
      #[listE PT Ps.toList, k, ← mkLambdaFVars #[← mkFreshExprMVar listNat] (mkConst ``True)])
  let FE ← withLocalDeclD `k nat fun k => do
    mkLambdaFVars #[k] (← mkAppM ``List.getD
      #[listE FT Fs.toList, k, .lam `v listNat (mkNatLit 0) .default])
  p := mkApp2 p PE FE
  -- the calls' premise
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let argsL := r.shape.insts.map (·.2.1)
  let argsLE := listE listNat (argsL.map fun a => listE nat (a.map mkNatLit))
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    -- per call: the premise at its index and arguments, for every cycle
    let mut perK : Array Lean.Expr := #[]
    for k in [0:argsL.length] do
      let argsE := listE nat ((argsL[k]!).map mkNatLit)
      let restK := (rest.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1 argsE
      let proofK ← withLocalDeclD `j nat fun j => do
        let c := (restK.bindingBody!.instantiate1 j).bindingBody!
        -- the call over the source's state loop
        let some callV := (← getConstInfo (declName ++ Name.mkSimple s!"machineCall_{k}")).value?
          | throwError "{declName}: machineCall_{k}"
        -- the state loop(s), as the trace's extension applies them
        let extApp := (tyArgs[7]!).beta ibb
        let states := extApp.getAppArgs.extract 3 extApp.getAppNumArgs
        let call := callV.beta (ibb ++ states)
        let callArgs := call.getAppArgs
        let (cSrc, cData, kinds) := childInfo[k]!
        unless callArgs.size == kinds.length do
          throwError "{declName}: call {k} has {callArgs.size} arguments, the child {kinds.length} binders"
        -- the argument values
        let mut obs : Array Lean.Expr := #[]
        for (a, kd) in callArgs.toList.zip kinds do
          match kd with
          | .bits w =>
            obs := obs.push (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit w)
              (← mkAppM ``Sparkle.Core.Signal.Signal.val #[a, j]))
          | .bool =>
            obs := obs.push (mkApp (mkConst ``Tools.ShippingMuxLoweringSoundness.encodeBool)
              (← mkAppM ``Sparkle.Core.Signal.Signal.val #[a, j]))
          | .domain => pure ()
        let obsE := listE nat obs.toList
        -- `call_of_facts` at the premise: its implicit arguments from `c`
        let natNat ← mkArrow nat nat
        let mArgs ← (#[listNat, mkApp (mkConst ``List [.zero]) natNat, nat, nat, PT', FT'] :
          Array Lean.Expr).mapM fun t => mkFreshExprMVar (some t)
        let rhsM ← mkFreshExprMVar (some nat)
        let e := mkAppN (mkConst ``Tools.ShippingMachineChild.call_of_facts)
          (mArgs ++ #[obsE, rhsM])
        let (hs, _, concl) ← forallMetaTelescope (← inferType e)
        unless ← isDefEq concl c do
          throwError "{declName}: call {k}: the premise does not have the expected shape"
        let tys ← hs.mapM fun h => do instantiateMVars (← inferType h)
        -- length, bounds, values (kernel `rfl`s and `decide`), range, value
        let some (α0, lhs0, _) := tys[0]!.eq? | throwError "length"
        let hlen := mkApp2 (mkConst ``Eq.refl [← getLevel α0]) α0 lhs0
        let hbd ← mkDecideProof tys[1]!
        let some (α2, lhs2, _) := tys[2]!.eq? | throwError "values"
        let hv := mkApp2 (mkConst ``Eq.refl [← getLevel α2]) α2 lhs2
        let hP ← proveByTactic tys[3]! (← rangeTactic kinds)
        let hF ← proveByTactic tys[4]! (← valueTactic cSrc cData kinds)
        let q ← instantiateMVars (mkAppN e #[hlen, hbd, hv, hP, hF])
        unless ← isDefEq (← inferType q) c do
          throwError "{declName}: call {k}: the assembled premise does not match"
        let _ := (data, argsLE)
        mkLambdaFVars #[j] q
      perK := perK.push proofK
    -- `Q k a := ∀ j, premise at k, a, j`, shifted by `m`
    let Qm (m : Nat) : MetaM Lean.Expr :=
      withLocalDeclD `k nat fun k => withLocalDeclD `a listNat fun a => do
        let rk := (rest.bindingBody!.instantiate1 (← mkAdd k (mkNatLit m))).bindingBody!.instantiate1 a
        let body ← withLocalDeclD `j nat fun j => do
          mkForallFVars #[j] (rk.bindingBody!.instantiate1 j).bindingBody!
        mkLambdaFVars #[k, a] body
    -- the chain over the call list
    let n := argsL.length
    let mut chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_nil
      #[listNat, ← Qm n]
    for m' in [0:n] do
      let m := n - 1 - m'
      let rest' := listE listNat ((argsL.drop (m + 1)).map fun a => listE nat (a.map mkNatLit))
      chain ← mkAppOptM ``Tools.ShippingMachineChild.forall_getElem?_cons
        #[listNat, ← Qm m, listE nat ((argsL[m]!).map mkNatLit), rest', perK[m]!, chain]
    withLocalDeclD `k nat fun k => withLocalDeclD `a listNat fun a =>
    withLocalDeclD `j nat fun j => do
      let hkT := ((rest.bindingBody!.instantiate1 k).bindingBody!.instantiate1 a
        |>.bindingBody!.instantiate1 j).bindingDomain!
      withLocalDeclD `hk hkT fun hk => do
        mkLambdaFVars (ibb ++ #[k, a, j, hk]) (mkAppN chain #[k, a, hk, j])
  let _ := argsLE
  p := mkApp p hcalls
  let value ← mkLambdaFVars xs p
  let name := declName ++ `machine_linked
  progress s!"{name}: checking"
  addTheorem name (← inferType value) value
  return name

def generateLinked (declName : Name) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => Lean.Elab.async.set o false) (generateLinkedCore declName)
  catch ex =>
    setEnv saved
    throw ex

open Lean.Elab.Command in
elab "#machine_linked " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generateLinked declName)
  logInfo m!"{name}: the linked run of the emitted module shows the source, given its children, checked by the kernel"

end Tools.ShippingMachineLinkedCommand
