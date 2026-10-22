import Tests.Compiler.KaryThreeTest
import Tools.ShippingSeqParentGenD2MSK
import Tools.ShippingKaryReturned
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR22): r12 exit 0 (dev run, default heartbeats: no raise in this file); the final-SHA rebuild is in REPORT-SR22.md.
-- SCOPE (binding, ledger L8bb): the RETURNED / WIRED theorems `topshare3.epK_returned` / `topshare3.epK_wired` of the three-callee example of `Tests/Compiler/KaryThreeTest.lean` (the SR21 declarations are
-- reused as they are: `topshare3.epK_all`, `epK_gens`, `epK_hFP`, `epD2M_genP`, …).  The two theorems are `Tools.ShippingKaryReturned.kary_returned` / `kary_wired` applied to the K-ary blocks
-- (`Tools.ShippingSeqParentGenD2MSK.returnedK`, the text that the opt-in generator emits; here it is HAND-APPLIED: the generator is not run).  Then (1) the FULL forall-type of each is compared by `isDefEq`
-- with a HAND-WRITTEN statement (`Share3Ret`, `Share3Wired`, written against the explicit callee list `Share3Cs`, independent of the generic theorems and of the generator); type-correct mutations (start
-- world, `h`'s declaration, the third entry's declaration, `y.2 = Dg` replaced by `True`, `DesignSemConcl` of the other design, callee list reordered / shortened, depth, kP) are REJECTED; (2) a closure audit.
-- CONCRETE example (`topshare3` only), not whole-class coverage; `O`, `T`, `hA`, `MachineDefines` of the parent / callees / leaf, `JQC O 0 w`, the run `h` stay premises; `RealChildA` / `JQC` are histories,
-- not freshness or semantic correctness.  No `sorry`, no `axiom`, no `native_decide`, NO heartbeat raise.
set_option Elab.async false
section
open Lean Elab Command Meta
namespace Tests.Compiler.KaryThreeReturnedTest
open Tests.Compiler.KaryThreeTest

open Lean Elab Command Meta Term in
run_cmd do
  for (nm, qr) in [(`epK_returned, "kary_returned"), (`epK_wired, "kary_wired")] do
    liftTermElabM do
      let src := Tools.ShippingSeqParentGenD2MSK.returnedK (N ++ `topshare3) (N ++ `leafK) [N ++ `wrapA, N ++ `wrapB, N ++ `wrapC] 4 qr
      let stx ← match Parser.runParserCategory (← getEnv) `term src with
        | .ok stx => pure stx
        | .error err => throwError "{nm}: parse error: {err}"
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "SR22: unassigned metavariables in the {nm} term"
      addAndCompile <| .thmDecl { name := N ++ `topshare3 ++ nm, levelParams := [], type := ty, value := e }

#print axioms Tests.Compiler.KaryThreeTest.topshare3.epK_returned
#print axioms Tests.Compiler.KaryThreeTest.topshare3.epK_wired

/-! ## the expected statements, written by hand -/

section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildPinC Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit Tools.ShippingSharedLeafNL
open Tools.ShippingMachineCloses Tools.ShippingMachineAuto
open Tools.ShippingShipsFree Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingSeqParentAt (DesignSemConcl)
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth Tools.ShippingDesignSV
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Tools.ShippingKaryRun (KCal)

/-- the callee list of `topshare3`, written out: each callee's name, machine data, number `n` of declared inputs as read by the generator (`bsIn.length - insts.length`, `3`) and source -/
noncomputable def Share3Cs : List KCal :=
  [⟨``wrapA, wrapA.machineData, 3, wrapA.machineSource⟩, ⟨``wrapB, wrapB.machineData, 3, wrapB.machineSource⟩, ⟨``wrapC, wrapC.machineData, 3, wrapC.machineSource⟩]

/-- the hand-written statement of `topshare3.epK_returned`.  `cs` = the callee list, `kJ` = the index of the start world `JQC O kJ w`, `dHr` = the declaration `h` synthesizes, `dE2` = the declaration of the third
callee's `entry2`, `eqQ` = the conjunct about `y.2` and `Dg`, `pickSem` = the design of `DesignSemConcl` (real: `(· = ·)`, `fun a _ => a`, i.e. `y.2`), `n` = the depth, `kP` = the parent's own inputs. -/
def Share3Ret (cs : List KCal) (kJ : Nat) (dHr dE2 : Name) (eqQ : Design → Design → Prop) (pickSem : Design → Design → Design) (n kP : Nat) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryP : MachineDefines mctx mref cctx cref ``topshare3 topshare3.machineData.shape)
    (entry0 : MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape)
    (entry1 : MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape)
    (entry2 : MachineDefines mctx mref cctx cref dE2 wrapC.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O kJ w)
    (h : RunsTo (synthesizeCombinational dHr) mctx mref cctx cref w y w'),
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = cs.length ∧
      closeLets topshare3.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare3.machineData.shape) topshare3.machineData.shape.insts.length
        topshare3.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshare3.machineData.shape.insts.map (·.2.1))
        topshare3.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshare3.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules) ∧
      RunsTo (synthesizeCombinationalCore ``topshare3 [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) ∧ eqQ y.2 Dg ∧
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) ``topshare3 topshare3.machineData kP M Dg
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare3.machineSource
        (fun i bools bits => topshare3.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits)))
        (fun i bools bits => topshare3.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits))) ∧
      DesignSemConcl n ``topshare3 topshare3.machineData kP
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare3.machineSource
        (fun i bools bits => topshare3.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits)))
        (fun i bools bits => topshare3.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits)))
        y.1 M (pickSem y.2 Dg)

/-- the hand-written statement of `topshare3.epK_wired` (parameters as for `Share3Ret`; real `pickSem := fun _ b => b`, i.e. `Dg`) -/
def Share3Wired (cs : List KCal) (kJ : Nat) (dHr dE2 : Name) (pickSem : Design → Design → Design) (n kP : Nat) : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryP : MachineDefines mctx mref cctx cref ``topshare3 topshare3.machineData.shape)
    (entry0 : MachineDefines mctx mref cctx cref ``wrapA wrapA.machineData.shape)
    (entry1 : MachineDefines mctx mref cctx cref ``wrapB wrapB.machineData.shape)
    (entry2 : MachineDefines mctx mref cctx cref dE2 wrapC.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``leafK leafK.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O kJ w)
    (h : RunsTo (synthesizeCombinational dHr) mctx mref cctx cref w y w'),
    ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = cs.length ∧
      closeLets topshare3.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshare3.machineData.shape) topshare3.machineData.shape.insts.length
        topshare3.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshare3.machineData.shape.insts.map (·.2.1))
        topshare3.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshare3.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w10).get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ e, (cv w10).get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules) ∧
      RunsTo (synthesizeCombinationalCore ``topshare3 [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) ``topshare3 topshare3.machineData kP M Dg
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare3.machineSource
        (fun i bools bits => topshare3.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits)))
        (fun i bools bits => topshare3.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits))) ∧
      DesignSemConcl n ``topshare3 topshare3.machineData kP
        (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare3.machineSource
        (fun i bools bits => topshare3.machineExt i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits)))
        (fun i bools bits => topshare3.machineExtB i bools bits
          (Tools.ShippingMachineSource.stateLoop topshare3.machineInits (topshare3.machineBody i bools bits)))
        y.1 M (pickSem y.2 Dg) ∧
      (∀ mn : String, mn ≠ M.name →
        Sparkle.IR.Machine.moduleByName y.2.modules mn = Sparkle.IR.Machine.moduleByName Dg.modules mn)

end


open Lean Meta in
/-- diagnostic helper (used only to report a failure): the smallest sub-term pair on which the two expressions are not defeq -/
partial def findDiff (a b : Expr) (depth : Nat := 0) : MetaM (Option (Expr × Expr)) := do
  if ← isDefEq a b then return none
  if depth > 60 then return some (a, b)
  match a, b with
  | .forallE n d t bi, .forallE _ d' t' _ =>
    if !(← isDefEq d d') then findDiff d d' (depth + 1)
    else withLocalDecl n bi d fun x => findDiff (t.instantiate1 x) (t'.instantiate1 x) (depth + 1)
  | .lam n d t bi, .lam _ d' t' _ =>
    if !(← isDefEq d d') then findDiff d d' (depth + 1)
    else withLocalDecl n bi d fun x => findDiff (t.instantiate1 x) (t'.instantiate1 x) (depth + 1)
  | .app .., .app .. =>
    let fa := a.getAppFn; let fb := b.getAppFn
    let as := a.getAppArgs; let bs := b.getAppArgs
    if (← isDefEq fa fb) && as.size == bs.size then
      for i in [0:as.size] do
        if !(← isDefEq as[i]! bs[i]!) then return (← findDiff as[i]! bs[i]! (depth + 1))
      return some (a, b)
    else return some (a, b)
  | _, _ => return some (a, b)

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let top := ``Tests.Compiler.KaryThreeTest.topshare3
  let rt ← instantiateMVars (← getConstInfo (top ++ `epK_returned)).type
  let wt ← instantiateMVars (← getConstInfo (top ++ `epK_wired)).type
  let e := mkConst
  let calT := Lean.mkApp (e ``List) (e ``Tools.ShippingKaryRun.KCal)
  let cs := e ``Share3Cs
  let csRev ← mkAppM ``List.reverse #[cs]
  let csTwo ← mkAppM ``List.take #[mkNatLit 2, cs]
  let _ := calT
  let mutR (cs : Expr) (kJ : Nat) (dHr dE2 : Name) (eqQ pick : Expr) (n kP : Nat) : Expr :=
    mkAppN (e ``Share3Ret) #[cs, mkNatLit kJ, toExpr dHr, toExpr dE2, eqQ, pick, mkNatLit n, mkNatLit kP]
  let mutW (cs : Expr) (kJ : Nat) (dHr dE2 : Name) (pick : Expr) (n kP : Nat) : Expr :=
    mkAppN (e ``Share3Wired) #[cs, mkNatLit kJ, toExpr dHr, toExpr dE2, pick, mkNatLit n, mkNatLit kP]
  let ty := mkConst ``Sparkle.IR.AST.Design
  let eqReal ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => do mkLambdaFVars #[a, b] (← mkEq a b)
  let eqTriv ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => mkLambdaFVars #[a, b] (mkConst ``True)
  let pickA ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => mkLambdaFVars #[a, b] a
  let pickB ← withLocalDeclD `a ty fun a => withLocalDeclD `b ty fun b => mkLambdaFVars #[a, b] b
  let wrapA := ``Tests.Compiler.KaryThreeTest.wrapA
  let wrapC := ``Tests.Compiler.KaryThreeTest.wrapC
  let retExp := mutR cs 0 top wrapC eqReal pickA 2 4
  let wiredExp := mutW cs 0 top wrapC pickB 2 4
  let retMuts := [(mutR cs 1 top wrapC eqReal pickA 2 4, "start world JQC O 1 w"), (mutR cs 0 wrapA wrapC eqReal pickA 2 4, "h synthesizes wrapA"),
    (mutR cs 0 top wrapA eqReal pickA 2 4, "entry2 is for wrapA"), (mutR cs 0 top wrapC eqTriv pickA 2 4, "the conjunct y.2 = Dg replaced by True"),
    (mutR cs 0 top wrapC eqReal pickB 2 4, "DesignSemConcl of Dg instead of y.2"), (mutR csRev 0 top wrapC eqReal pickA 2 4, "callee list reversed"),
    (mutR csTwo 0 top wrapC eqReal pickA 2 4, "callee list shortened to two"), (mutR cs 0 top wrapC eqReal pickA 3 4, "depth 3"),
    (mutR cs 0 top wrapC eqReal pickA 2 3, "kP = 3")]
  let wiredMuts := [(mutW cs 1 top wrapC pickB 2 4, "start world JQC O 1 w"), (mutW cs 0 wrapA wrapC pickB 2 4, "h synthesizes wrapA"),
    (mutW cs 0 top wrapA pickB 2 4, "entry2 is for wrapA"), (mutW cs 0 top wrapC pickA 2 4, "DesignSemConcl of y.2 instead of Dg"),
    (mutW csRev 0 top wrapC pickB 2 4, "callee list reversed"), (mutW csTwo 0 top wrapC pickB 2 4, "callee list shortened to two"),
    (mutW cs 0 top wrapC pickB 3 4, "depth 3"), (mutW cs 0 top wrapC pickB 2 3, "kP = 3")]
  for (x, what) in [(rt, "epK_returned"), (wt, "epK_wired"), (retExp, "expected returned"), (wiredExp, "expected wired")] ++
      (retMuts ++ wiredMuts).map fun (x, w) => (x, s!"mutation {w}") do
    if x.hasMVar || x.hasFVar then throwError "SR22 AUDIT FAILED: metavariables / free variables in {what}"
    Meta.check x
  unless (← isDefEq rt retExp) do
    let u := (← unfoldDefinition? retExp).getD retExp
    let some (x, y) ← findDiff rt u | throwError "SR22 AUDIT FAILED (diff vanished)"
    throwError "SR22 AUDIT FAILED: the FULL type of topshare3.epK_returned is not definitionally the hand-written Share3Ret; first diff:\n{x}\nVS\n{y}"
  unless (← isDefEq wt wiredExp) do throwError "SR22 AUDIT FAILED: the FULL type of topshare3.epK_wired is not definitionally the hand-written Share3Wired"
  for (x, w) in retMuts do
    if (← isDefEq rt x) then throwError "SR22 AUDIT FAILED: the mutated returned type ({w}) was ACCEPTED"
  for (x, w) in wiredMuts do
    if (← isDefEq wt x) then throwError "SR22 AUDIT FAILED: the mutated wired type ({w}) was ACCEPTED"
  unless !(← isDefEq rt wt) do throwError "SR22 AUDIT FAILED: the returned and wired types coincide"
  let names ← forallTelescope rt fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  unless names == ["mctx", "mref", "cctx", "cref", "O", "T", "hA", "entryP", "entry0", "entry1", "entry2", "hR0", "w", "w'", "y", "hw", "h"] do
    throwError "SR22 AUDIT FAILED: binder names {names}"
  logInfo m!"SR22: the FULL forall-types of topshare3.epK_returned (y.2 = Dg; DesignSemConcl for y.2) and topshare3.epK_wired (DesignSemConcl for Dg; lookup agreement) are isDefEq to the hand-written Share3Ret / Share3Wired (callee list Share3Cs); {retMuts.length} resp. {wiredMuts.length} type-correct mutations (start world, h's declaration, entry2's declaration, y.2 = Dg dropped / the design of DesignSemConcl swapped, callee list reversed / shortened, depth, kP) are REJECTED"

/-! ## closure audit -/

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  for nm in [`epK_returned, `epK_wired] do
    let c := ``Tests.Compiler.KaryThreeTest.topshare3 ++ nm
    stdAxioms c
    let cl ← depClosure c
    let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
      `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
    for f in forbidden do
      unless (← getEnv).contains f do throwError "SR22 AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
    let bad := hits cl ++ cl.toList.filter fun x => forbidden.any (·.isPrefixOf x)
    unless bad.isEmpty do throwError "SR22 AUDIT FAILED: old boundary / old child predicate in the closure of {c}: {bad}"
    let quadLemmas : List Name :=
      [``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun, ``Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np,
       ``Tools.ShippingQuadComposed.quad_ranA, ``Tools.ShippingQuadComposed.quad_hkid, ``Tools.ShippingQuadComposed.quad_runFacts,
       ``Tools.ShippingQuadComposed.quad_outsCheck, ``Tools.ShippingQuadComposed.quad_kidsMasked, ``Tools.ShippingQuadComposed.quad_designCheck,
       ``Tools.ShippingQuadComposed.quad_traceXA, ``Tools.ShippingQuadComposed.quad_soundLA, ``Tools.ShippingQuadCalls.quad_composed_split,
       ``Tools.ShippingQuadReturned.quad_returned, ``Tools.ShippingQuadReturned.quad_wired,
       ``Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np]
    for q in quadLemmas do
      if cl.contains q then throwError "SR22 AUDIT FAILED: the two-callee lemma {q} is in the closure of {c}"
    let must : List Name :=
      [(if nm == `epK_returned then ``Tools.ShippingKaryReturned.kary_returned else ``Tools.ShippingKaryReturned.kary_wired),
       ``Tools.ShippingKaryReturned.kary_returned, ``Tools.ShippingKaryLeafGeneric.kary_entry_run, ``Tools.ShippingTopShareNoParent.returned_design_eq,
       ``Tools.ShippingSeqParentAt.machine_design_noShips_noBd_dc_at, ``Tools.ShippingKaryCalls.kary_composed_split, ``Tools.ShippingKaryComposed.kary_soundLA,
       ``Tools.ShippingKaryComposed.kary_runFacts, ``Tools.ShippingKaryComposed.kary_outsCheck, ``Tools.ShippingKaryComposed.kary_kidsMasked,
       ``Tools.ShippingKaryComposed.kary_designCheck]
    for m in must do
      unless cl.contains m do throwError "SR22 AUDIT FAILED: {m} not in the closure of {c}"
    for old in [`Tests.Compiler.KaryThreeTest.topshare3.epK_endpoint] do
      if cl.contains old then throwError "SR22 AUDIT FAILED: {old} is in the closure of {c}"
    logInfo m!"SR22 CLOSURE AUDIT: {c}: standard axioms; closure {cl.size} constants; no ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC, no RefLaws/RefLawsCore/toAOps/toA; none of the {quadLemmas.length} two-callee lemmas; the K-ary theorem, kary_entry_run, returned_design_eq, machine_design_noShips_noBd_dc_at and the K-ary blocks are in it"


end Tests.Compiler.KaryThreeReturnedTest
end
