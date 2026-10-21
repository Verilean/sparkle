import Tests.Compiler.ParentHoutTyTest
-- BUILT (unit SR3h): h3 exit 0 (h1,h2 exit 1: opens, Expr ambiguity). In-test audit THROWS on failure.
-- SCOPE (binding): `parent_noShips_noBdA_dcH` = SR3f's `_dc` with `houtTy` SUPPLIED by SR3g's `parent_houtTy`. soundL / composed /
-- hr / entry / closes remain premises; BndA (existential) stays in the conclusion. NOT unconditional semantic equivalence.
namespace Tests.Compiler.ParentHoutTyTest
open Tests.Compiler.ParentDesignCheckFATest
open Tests.Compiler.ParentEndpointFactsATest Tests.Compiler.ParentEndpointMaskedATest
open Tests.Compiler.ParentEndpointMaskedATest Tests.Compiler.KidsMaskedParentATest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

set_option maxHeartbeats 4000000 in
/-- `parent_noShips_noBdA_dc` with `houtTy` actually passed as `parent_houtTy`. -/
theorem parent_noShips_noBdA_dcH (n : Nat)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc srcL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    -- the wired endpoint, for the cleanup facts only (its source may be the
    -- fused / sign-normalised one a transported endpoint rewrites)
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref ``parent parent.machineData.shape →
      C mctx mref cctx cref →
      BndA mctx mref cctx cref w m design →
      MachineTraceLB ``parent parent.machineData m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref ``parent parent.machineData.shape →
      C mctx mref cctx cref →
      BndA mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      ComposedG (fun D => KSn (childMap D.modules) n) (ResetNk n) ``parent parent.machineData kD m design dom src ext extB)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational ``parent) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (closes : C mctx mref cctx cref) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (-- NO checker premise: `designCheck` is proved (`parent_designCheckFA`)
        BndA mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = parent.machineData.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = parent.machineData.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs ``parent (parent.machineData.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              parent.machineData.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            -- the emitted widths' use conditions: inputs, start registers, instance states
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
              childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) n gc (kids iname)) →
            -- a closed run of the emitted texts showing the source exists ...
            (∃ envsO,
              DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                parent.machineData.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', DesignSV (childMap D.modules) n (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  parent.machineData.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j) :=
  parent_noShips_noBdA_dc n C soundL composed parent_houtTy hr entry closes

open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := ``parent_noShips_noBdA_dcH
  stdAxioms new
  let premises ← Meta.forallTelescope (← getConstInfo new).type fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← Meta.inferType x
      if (← Meta.isProp t) then
        ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["soundL : [anonymous]", "composed : [anonymous]",
    "hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : [anonymous]"]
  unless premises.toList == expected do throwError "SR3h AUDIT FAILED: premises {premises}, expected {expected}"
  let cl ← depClosure new
  unless cl.contains ``parent_houtTy do throwError "SR3h AUDIT FAILED: parent_houtTy not in closure"
  -- conclusion: isDefEq to _dc's with the shared binders as fvars (houtTy removed)
  Meta.forallTelescope (← getConstInfo ``parent_noShips_noBdA_dc).type fun oldXs co => do
    let names ← oldXs.mapM fun x => x.fvarId!.getUserName
    Meta.forallTelescope (← getConstInfo new).type fun newXs cn => do
      let nn ← newXs.mapM fun x => x.fvarId!.getUserName
      unless nn.toList == (names.toList.filter (· != `houtTy)) do throwError "SR3h AUDIT FAILED: binder lists differ"
      let mut ni := 0
      let mut repl : Array Lean.Expr := #[]
      for x in oldXs do
        let nm ← x.fvarId!.getUserName
        if nm == `houtTy then repl := repl.push (mkConst ``parent_houtTy)
        else
          repl := repl.push newXs[ni]!
          ni := ni + 1
      let co' := (co.abstract oldXs).instantiateRev repl
      unless (← Meta.isDefEq co' cn) do throwError "SR3h AUDIT FAILED: conclusion differs from _dc's"
  logInfo m!"SR3h AUDIT OK: {new}: standard axioms; premises {premises}; houtTy absent, supplied by parent_houtTy; conclusion defeq to _dc's with the shared binders as fvars"

#print axioms parent_noShips_noBdA_dcH
end Tests.Compiler.ParentHoutTyTest
