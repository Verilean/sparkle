import Tools.ShippingMachineSeqCommandR
import Tools.ShippingMachineCallsLinkedTG
import Tools.ShippingGateChildCommand
-- WRITTEN, NOT BUILT (round par/o-gdes, unit "1").

/-! # Generated composition with memory, sequential AND gate-route children

`#machine_composedTSR f` / `#machine_design_svR0 f` classify every call entry
WITHOUT a memory origin as a sequential child and ask its `machine_sound`; a
call of a combinational `@[hardware_module]` the certified unified gate
compiles (no `machine_sound`) made them fail ("seq child …: no
machine_sound"). Here:

* the entries are dispatched by their stored ORIGIN first (a memory origin is
  a memory read, whatever the callee's name — `originMem?`); a non-memory
  entry's callee is a SEQUENTIAL child when its declaration has a
  `machine_sound`, otherwise a GATE child (its declaration must pass the
  unified gate: `gateDefs`, and `c.gate_kid_run` below must elaborate);
* `#gate_kid c` / `gateKidTheorem c`: `c.gate_kid_run : ∀ mc, GateRun c
  c.gateValue mc → GateKidRun mc (range) (c's source function) n`
  (`Tools.ShippingMachineCallsLinkedTG.gateKidRun_of_gateRun` at the gate's
  reading of `c`); a callee whose name has numeric parts
  (`SparkleMem.sync.4.8`) is elaborated under an auxiliary name and added
  under `c.gate_kid_run` (as `leafKidTheorem`); an existing constant is reused;
* `#machine_composedTRG f`: `machine_linkedT_callsRG` with per call its
  `MemFacts` / `SeqFactsR` / `GateFactsR`, the children's reflection facts as
  ONE premise `hrefl` (the conjunction, per sequential child, of
  `MachineDefines` [∧ its closing], and per gate child of
  `EntryDefines c c.gateValue`), the run boundary `ChildBnd` (`hsyn`) — the
  gate children's `GateRun` is DERIVED (no `GateRun` binder);
* `#machine_design_svRG0 f`: `machine_ships_hierC` from the `MachineClosesAt`
  form (`f.machine_composedTRGA`), then `DesignSV` at depth 0
  (`ShippingShipsDesignSVCommand.compose`), as `#machine_design_svR0`. -/
namespace Tools.ShippingMachineGateMemCommand
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingMachineCommand (readMachine progress listE)
open Tools.ShippingMachineLinkedCommand (addTheorem)
open Tools.ShippingMachineSeqCommand (endpointParts nameCases findCall sigAtPos memTactic
  rangeSyntax proveByTacticT generateSeqChild)

/-! ## The gate child's theorem -/

open Lean.Elab.Command in
/-- `c.gate_kid_run` (reused when present). -/
def gateKidTheorem (c : Name) : CommandElabM Name := do
  let name := c ++ `gate_kid_run
  if (← getEnv).contains name then return name
  liftTermElabM do
    unless (← getEnv).contains (c ++ `machineSource) do
      discard <| Tools.ShippingMachineCommand.generateSourceDefs c
    withOptions (fun o => Lean.Elab.async.set o false)
      (Tools.ShippingGateChildCommand.gateDefs c)
  let nm (s : String) : Ident := mkIdent (`_root_ ++ c ++ Name.mkSimple s)
  let cq : Lean.Term := quote c
  let srcT ← liftTermElabM do inferType (mkConst (c ++ `machineSource))
  let i0 : Lean.Term ← if srcT.bindingDomain!.isConstOf ``Unit then `(Unit.unit)
    else `(Sparkle.Core.Domain.defaultDomain)
  let hasNum := c.components.any fun x => x.isNum
  let elabName : Name := if hasNum then
      `Tools.ShippingMachineGateMemCommand.gateKidAux ++ Name.mkSimple (toString (hash c)) else name
  let before := (← get).messages.toList.length
  withScope (fun s => { s with opts := maxRecDepth.set (Lean.Elab.async.set s.opts false) 100000 }) do
    elabCommand (← `(command|
      theorem $(mkIdent (`_root_ ++ elabName)) (mc : Sparkle.IR.AST.Module)
          (h : Tools.ShippingGateChild.GateRun $cq $(nm "gateValue") mc) :
          Tools.ShippingMachineCallsLinkedTG.GateKidRun mc
            (fun vs => Tools.ShippingMachineChild.InRange vs
              ((Tools.ShippingMachineAuto.MachineData.bsIn $(nm "machineData")).filter
                fun b => b.2 != .domain))
            (Tools.ShippingMachineChild.childValue $(nm "machineSource")
              (Tools.ShippingMachineAuto.MachineData.bsIn $(nm "machineData")) $i0)
            ((Tools.ShippingMachineAuto.MachineData.bsIn $(nm "machineData")).filter
                fun b => b.2 != .domain).length := by
        have hbs : Tools.ShippingMachineAuto.MachineData.bsIn $(nm "machineData") =
            $(nm "gateBinders") := by decide
        rw [hbs]
        exact Tools.ShippingMachineCallsLinkedTG.gateKidRun_of_gateRun
          (value := $(nm "gateValue")) (dom := $(nm "gateDom")) (bs := $(nm "gateBinders"))
          (kb := $(nm "gateBpos").length) (kv := $(nm "gateVpos").length)
          (vw := fun j => $(nm "gateVw").getD j 0)
          (bpos := fun j => $(nm "gateBpos").getD j 0) (vpos := fun j => $(nm "gateVpos").getD j 0)
          (srt := $(nm "gateSort")) (e := $(nm "gateTerm"))
          (fun d hd => by simp only [Sparkle.Compiler.Elab.certifiedShape?, hd]; rfl)
          (by rfl)
          (by
            delta $(nm "gateTerm") $(nm "gateSort") $(nm "gateBpos") $(nm "gateVpos") $(nm "gateVw")
            simp (config := { decide := true }) [Tools.ShippingUnifiedSource.Term.WF])
          (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide))
          (fun _ _ => rfl) h))
  if (← get).messages.toList.drop before |>.any (·.severity == .error) then
    throwError "{c}: the gate child's theorem failed"
  unless (← getEnv).contains elabName do throwError "{elabName} was not added"
  if hasNum then
    let ci ← getConstInfo elabName
    liftCoreM <| addDecl (Declaration.thmDecl (mkTheoremValEx name ci.levelParams ci.type
      (mkConst elabName (ci.levelParams.map Level.param)) [name]))
  for ax in ← liftCoreM (Lean.collectAxioms name) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{name} uses a non-standard axiom: {ax}"
  return name

/-- The non-memory callees (by ORIGIN), split into sequential (a
`machine_sound`) and gate (none) children. -/
def kidKinds (declName : Name) : MetaM (List Name × List Name) := do
  let r ← readMachine declName
  let kids ← Tools.ShippingMachineMemCommand.seqCallees r.shape
  let mut seqK : List Name := []
  let mut gateK : List Name := []
  for c in kids do
    if (← getEnv).contains (c ++ `machine_sound) then seqK := seqK ++ [c]
    else gateK := gateK ++ [c]
  pure (seqK, gateK)

open Lean.Elab.Command in
/-- The gate children's theorems of `declName`'s calls. -/
def prepareGateKids (declName : Name) : CommandElabM Unit := do
  let (_, gateK) ← liftTermElabM (kidKinds declName)
  for c in gateK do discard <| gateKidTheorem c

/-! ## The parent -/

/-- `f.machine_composedTRG`; with `atW`, `f.machine_composedTRGA` (closing
premise `MachineClosesAt`). Run `prepareGateKids f` first. -/
def generateCoreSRG (declName : Name) (atW : Bool := false) : MetaM Name := do
  let name := declName ++ (if atW then `machine_composedTRGA else `machine_composedTRG)
  if (← getEnv).contains name then return name
  progress s!"{declName}: composedTRG (memory / sequential / gate children, boundary derived)"
  let r ← readMachine declName
  if r.shape.insts.isEmpty then throwError "{declName}: no call"
  let (headL, args, back?) ← endpointParts declName
  let pL := mkAppN (mkConst (headL.appendAfter (if atW then "RA" else "R"))) args
  let calls := r.shape.insts
  let (seqKids, gateKids) ← kidKinds declName
  for c in gateKids do
    unless (← getEnv).contains (c ++ `gate_kid_run) do
      throwError "{c}: no gate_kid_run (a non-memory callee without machine_sound must pass the unified gate)"
  let mut seqRuns : Std.HashMap Name Name := {}
  for c in seqKids do
    seqRuns := seqRuns.insert c (← (try generateSeqChild c catch e => throwError "seq child {c}: {e.toMessageData}"))
  forallTelescope (← inferType pL) fun xs traceT => do
  let h := mkAppN pL xs
  let tyArgs := (← whnfR traceT).getAppArgs
  unless tyArgs.size == 11 do throwError "{declName}: the trace's arguments"
  let dE := tyArgs[2]!
  let bsTy ← inferType (← mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[dE])
  let outsTy ← inferType (← mkAppM ``Sparkle.IR.Machine.Layout.outs
    #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE]]])
  let nat := mkConst ``Nat
  let listNat := mkApp (mkConst ``List [.zero]) nat
  let valsTy ← mkArrow nat listNat
  let obsTy := mkApp (mkConst ``List [.zero]) (← mkArrow nat nat)
  let ιP := tyArgs[5]!
  let domP := tyArgs[6]!
  let srcAt (c : Name) (iv : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
    let csrc := mkConst (c ++ `machineSource)
    let ιc := (← inferType csrc).bindingDomain!
    let idx ← if ιc.isConstOf ``Unit then pure (mkConst ``Unit.unit)
      else whnf (mkApp domP iv)
    let src0 := mkApp csrc idx
    let Dc := ((← whnf (← inferType src0)).bindingDomain!).bindingBody!.getAppArgs[0]!
    pure (src0, Dc, idx)
  let bsInOf (c : Name) : MetaM Lean.Expr :=
    mkAppM ``Tools.ShippingMachineAuto.MachineData.bsIn #[mkConst (c ++ `machineData)]
  -- the binder family: sequential AND gate children
  let mut bsCases : List (Name × Lean.Expr) := []
  for c in seqKids ++ gateKids do bsCases := bsCases ++ [(c, ← bsInOf c)]
  let mut outsCases : List (Name × Lean.Expr) := []
  for c in seqKids do
    outsCases := outsCases ++ [(c, ← mkAppM ``Sparkle.IR.Machine.Layout.outs
      #[← mkAppM ``Sparkle.Compiler.Elab.MachineShape.layout
        #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)]]])]
  let bsC ← nameCases bsTy bsCases (mkApp (mkConst ``List.nil [.zero]) bsTy.appArg!)
  let outsC ← nameCases outsTy outsCases (mkApp (mkConst ``List.nil [.zero]) outsTy.appArg!)
  let natNat ← mkArrow nat nat
  let sDflt ← withLocalDeclD `vals valsTy fun vals =>
    mkLambdaFVars #[vals] (mkApp (mkConst ``List.nil [.zero]) natNat)
  let S ← withLocalDeclD `i ιP fun iv => do
    let mut sCases : List (Name × Lean.Expr) := []
    for c in seqKids do
      let bsIn ← bsInOf c
      let (src0, Dc, _) ← srcAt c iv
      let sF ← withLocalDeclD `vals valsTy fun vals => do
        mkLambdaFVars #[vals] (mkApp2 src0
          (← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsIn, vals])
          (← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsIn, vals]))
      sCases := sCases ++ [(c, sF)]
    mkLambdaFVars #[iv] (← nameCases (← mkArrow valsTy obsTy) sCases sDflt)
  -- the sequential children's shapes (default: the parent's, never read)
  let shapeT := mkConst ``Sparkle.Compiler.Elab.MachineShape
  let shCases ← seqKids.mapM fun c => do
    pure (c, ← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (c ++ `machineData)])
  let shC ← nameCases shapeT shCases (← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[dE])
  -- the callee kind, the gate children's reflected values and functions
  let gk ← nameCases (mkConst ``Bool) (gateKids.map fun c => (c, mkConst ``Bool.true))
    (mkConst ``Bool.false)
  let exprT := mkConst ``Lean.Expr
  let vC ← nameCases exprT (gateKids.map fun c => (c, mkConst (c ++ `gateValue)))
    (mkApp (mkConst ``Lean.Expr.bvar) (mkNatLit 0))
  let fnT ← mkArrow listNat nat
  let mut fCases : List (Name × Lean.Expr) := []
  for c in gateKids do
    let cSrc := mkConst (c ++ `machineSource)
    let ιc := (← inferType cSrc).bindingDomain!
    let i0 := if ιc.isConstOf ``Unit then mkConst ``Unit.unit
      else mkConst ``Sparkle.Core.Domain.defaultDomain
    fCases := fCases ++ [(c, ← mkAppM ``Tools.ShippingMachineChild.childValue #[cSrc, ← bsInOf c, i0])]
  let FC ← nameCases fnT fCases (.lam `v listNat (mkNatLit 0) .default)
  let mut p ← mkAppM ``Tools.ShippingMachineCallsLinkedTG.machine_linkedT_callsRG #[h]
  p := mkApp p (← mkDecideProof (← whnf (← inferType p)).bindingDomain!)
  p := mkApp p (mkNatLit r.nDecl)
  for _ in [0:7] do
    let ty := (← whnf (← inferType p)).bindingDomain!
    p := mkApp p (← mkDecideProof ty)
  p := mkAppN p #[bsC, outsC, S, shC, gk, vC, FC]
  let hcallsT := (← whnf (← inferType p)).bindingDomain!
  let hcalls ← forallBoundedTelescope hcallsT (some 3) fun ibb rest => do
    let names := calls.map (·.1)
    let lsrcE := (tyArgs[10]!).beta ibb
    let extE := (tyArgs[8]!).beta ibb
    let extBE := (tyArgs[9]!).beta ibb
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
      let proofK ← match ← Tools.ShippingMachineMemCommand.originMem? r.shape k with
        | some (cb, aw, dw) =>
          proveByTacticT goalK (do pure (← memTactic k cb aw dw argsK))
        | none => try do
          let isGate := gateKids.contains c
          let (src0, Dc, idxE) ← srcAt c ibb[0]!
          let pos := r.nDecl + k
          let some sig := (sigAtPos pos extBody).orElse fun _ => sigAtPos pos extBBody
            | throwError "{declName}: call {k}: no signal at port {pos}"
          let some call := findCall c sig | throwError "{declName}: call {k}: no call of {c}"
          let callArgs := call.getAppArgs
          let cr ← readMachine c (allowGate := isGate)
          let bsIn : List (Name × MixedGateBinder) := cr.shape.binders.take cr.nDecl
          unless callArgs.size == bsIn.length do
            throwError "{declName}: call {k}: {callArgs.size} arguments, {bsIn.length} binders"
          let bsInE ← bsInOf c
          let vs ← mkAppM ``Tools.ShippingMachineCallsLinkedT.valsOf
            #[lsrcE, listE nat (argsK.map mkNatLit)]
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
          let VB ← mkAppOptM ``Tools.ShippingMachineChild.boolsOf #[Dc, bsInE, vs]
          let VV ← mkAppOptM ``Tools.ShippingMachineChild.bitsOf #[Dc, bsInE, vs]
          let tyA ← inferType A
          let tyB ← inferType B
          let tyI ← inferType idxE
          let srcE := src0
          let tyS ← inferType srcE
          let lit (n : Nat) := Syntax.mkNumLit (toString n)
          let argsArr : Array Term := (argsK.map fun n => (⟨lit n⟩ : Term)).toArray
          let rangeS ← rangeSyntax kinds
          -- the decoded inputs are the call's arguments (as the sequential route)
          let hbS : MetaM Term := `(by
              funext p
              try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineCausal.extendBools]
              (repeat' split) <;> (first
                | (rename_i hp; subst hp; exact Tools.ShippingMachineCallsLinkedT.boolsOf_at
                    (fun τ => Tools.ShippingMachineCallsLinkedT.decB_valsOf rfl (by decide) rfl τ))
                | rfl))
          let hvS : MetaM Term := `(by
              funext p n
              try simp (config := { zetaDelta := true }) only [Tools.ShippingMachineAuto.extendBits]
              (repeat' split) <;> (first
                | (rename_i hp; obtain ⟨hp1, hp2⟩ := hp; subst hp1; subst hp2; (try simp only [cast_eq]); exact Tools.ShippingMachineCallsLinkedT.bitsOf_at
                    (fun τ => Tools.ShippingMachineCallsLinkedT.decV_valsOf rfl (by decide) rfl τ))
                | rfl))
          let pr ← withLetDecl `famA tyA A fun aF => withLetDecl `famB tyB B fun bF =>
            withLetDecl `famI tyI idxE fun iF => withLetDecl `famS tyS srcE fun sF =>
            withLetDecl `famVB tyA VB fun vbF => withLetDecl `famVV tyB VV fun vvF => do
           let pr ← proveByTacticT goalK (do
            let argsS ← `([$argsArr,*])
            let srcS : Term := ⟨mkIdent `famS⟩
            let idxS : Term := ⟨mkIdent `famI⟩
            let AS : Term := ⟨mkIdent `famA⟩
            let BS : Term := ⟨mkIdent `famB⟩
            let VBS : Term := ⟨mkIdent `famVB⟩
            let VVS : Term := ⟨mkIdent `famVV⟩
            let hb ← hbS
            let hv ← hvS
            if isGate then
              let gkrS := mkIdent (`_root_ ++ c ++ `gate_kid_run)
              `(tactic| (
                right; right
                refine ⟨by first | rfl | decide, ?_⟩
                unfold Tools.ShippingMachineCallsLinkedTG.GateFactsR
                refine ⟨rfl, $argsS, rfl, ?b, ?l, ?r, ?f⟩
                case b =>
                  intro mc hgr
                  exact ⟨_, $gkrS mc hgr, by first | decide | decide +kernel⟩
                case l =>
                  exact Tools.ShippingMachineCallsLinkedT.args_facts (by decide)
                    (by simp [Tools.ShippingMachineCausal.letObsB, Tools.ShippingMachineCausal.letObsLoop,
                      Tools.ShippingMachineCausal.letObsComb])
                case r =>
                  intro τ
                  unfold Tools.ShippingMachineChild.InRange
                  exact $rangeS
                case f =>
                  intro τ
                  refine Eq.trans ?pe (Eq.trans (congrArg (fun l => (l[0]?.map (· τ)).getD 0)
                    (Tools.ShippingMachineCallsLinkedT.decoded_eq (bools := $VBS) (bits := $VVS)
                      (bools' := $AS) (bits' := $BS) $srcS $hb $hv)).symm ?pv)
                  case pe => rfl
                  case pv => rfl))
            else
              let some seqRun := seqRuns.get? c | throwError "{declName}: child {c}"
              let field := r.shape.instFields.getD k ""
              let some k' := cr.shape.layout.outs.findIdx? (fun (o : Sparkle.IR.Machine.OutField) => o.name == field)
                | throwError "{declName}: call {k}: field {field}"
              let seqRunS := mkIdent (`_root_ ++ seqRun)
              `(tactic| (
                right; left
                refine ⟨by first | rfl | decide, ?_⟩
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
                      $hb $hv)).trans rfl)))
           pure ((← instantiateMVars pr).replaceFVar aF A |>.replaceFVar bF B |>.replaceFVar iF idxE
             |>.replaceFVar sF srcE |>.replaceFVar vbF VB |>.replaceFVar vvF VV)
          pure pr
          catch e => throwError "call {k}: {e.toMessageData}"
      try check proofK catch e => throwError "call {k} proof ill-formed: {e.toMessageData}"
      perK := perK.push proofK
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
  -- sequential children (`MachineDefines` [∧ closing]) and the gate children
  -- (`EntryDefines c c.gateValue`), in the parent's contexts
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
  for c in gateKids do
    rTypes := rTypes ++ [mkAppN (mkConst ``Tools.ShippingInlineSoundness.EntryDefines)
      (ctx ++ #[toExpr c, mkConst (c ++ `gateValue)])]
  let allKids := seqKids ++ gateKids
  let hreflNewT ← Tools.ShippingMachineShipsHierCommand.conj rTypes
  withLocalDeclD `hrefl hreflNewT fun hrefl => do
  let ps ← Tools.ShippingMachineShipsHierCommand.projs hrefl rTypes
  let rDecls := (allKids.zip rTypes).toArray.mapIdx fun j (_, ty) =>
    (Name.mkSimple s!"hR{j}", fun (_ : Array Lean.Expr) => pure ty)
  let names := calls.map (·.1)
  let nameT := mkConst ``Name
  -- one of the two reflection premises (`gate = false`: sequential, `true`: gate)
  let reflProof (premT : Lean.Expr) (gate : Bool) : MetaM Lean.Expr :=
    withLocalDeclsD rDecls fun hRs => do
      let mut perR : Array Lean.Expr := #[]
      for k in [0:names.length] do
        let c := names[k]!
        let goalK := ((premT.bindingBody!.instantiate1 (mkNatLit k)).bindingBody!.instantiate1
          (toExpr c)).bindingBody!
        let hRS : Term := ⟨mkIdent (Name.mkSimple s!"hR{allKids.idxOf c}")⟩
        let prK ← match ← Tools.ShippingMachineMemCommand.originMem? r.shape k with
          | some _ => proveByTacticT goalK `(tactic| (intro h; first | cases h | simp [Sparkle.Compiler.MachMemory.memChild?] at h | exact absurd (congrArg Option.isNone h) (by decide) | exact absurd (congrArg Option.isNone h) (by decide +kernel)))
          | none =>
            if gateKids.contains c != gate then
              proveByTacticT goalK `(tactic| (intro _ hg; exact absurd hg (by first | decide | decide +kernel)))
            else if gate then
              proveByTacticT goalK `(tactic| (intro _ _; exact $hRS))
            else if freeOf.getD c false then
              proveByTacticT goalK `(tactic| (intro _ _; exact ⟨$hRS, fun _ _ _ =>
                $(mkIdent (`_root_ ++ c ++ `machine_closes)) _ _ _ _⟩))
            else proveByTacticT goalK `(tactic| (intro _ _; exact $hRS))
        perR := perR.push prK
      let QmR (m : Nat) : MetaM Lean.Expr :=
        withLocalDeclD `k nat fun kv => withLocalDeclD `c nameT fun cv => do
          let rk := ((premT.bindingBody!.instantiate1 (← mkAdd kv (mkNatLit m))).bindingBody!.instantiate1
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
  let p := mkApp p (← reflProof hreflT false)
  let hreflGT := (← whnf (← inferType p)).bindingDomain!
  let p := mkApp p (← reflProof hreflGT true)
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

def generateSRG (declName : Name) (atW : Bool := false) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) (generateCoreSRG declName atW)
  catch ex =>
    setEnv saved
    throw ex

/-- `f.machine_ships_hierRG`: `machine_ships_hierC` from `f.machine_composedTRGA`. -/
def generateShipsRG (declName : Name) : MetaM Name := do
  let cR ← generateSRG declName (atW := true)
  let (headL, _, _) ← endpointParts declName
  Tools.ShippingMachineShipsHierCommand.generateWith declName
    cR (declName ++ `machine_ships_hierRG) (headA? := some (headL.appendAfter "RA"))

/-- `f.machine_design_svRG0`: source → the closed emitted texts at depth 0. -/
def generateDesignRG0 (declName : Name) : MetaM Name := do
  let ships ← generateShipsRG declName
  Tools.ShippingShipsDesignSVCommand.compose declName ships (declName ++ `machine_design_svRG0) 0

open Lean.Elab.Command in
elab "#gate_kid " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← gateKidTheorem declName
  logInfo m!"{name}: every module of a run of the gate child's full entry is a GateKidRun, checked by the kernel"

open Lean.Elab.Command in
elab "#machine_composedTRG " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  prepareGateKids declName
  let name ← liftTermElabM (generateSRG declName)
  logInfo m!"{name}: the stateful linked run with memory, sequential and gate children (boundaries derived), shows the source, checked by the kernel"

open Lean.Elab.Command in
elab "#machine_design_svRG0 " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  prepareGateKids declName
  let name ← liftTermElabM <|
    withOptions (fun o => maxRecDepth.set (Lean.Elab.async.set o false) 1000000) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 })
        (generateDesignRG0 declName)
  logInfo m!"{name}: source → shipped design's closed emitted texts, memory / sequential / gate children (boundaries derived), checked by the kernel"

end Tools.ShippingMachineGateMemCommand
