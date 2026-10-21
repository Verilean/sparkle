import Tests.Compiler.KidsMaskedParentATest
import Tools.ShippingShipsFreeMasked
import Tests.Compiler.ShipsFreeMaskedTest
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit SR3d, par/u-sr3d): sr3d3 exit 0 (sr3d1 exit 1: missing open `cv`; sr3d2 exit 1: audit syntax). In-test audit + conclusion check THROW on failure.
-- SR3e (par/u-sr3e): audit strengthened (premise list ASSERTED, shared args as FVARS in the old/new comparison): sr3e5 exit 0.
-- SCOPE (binding): the DEPTH-HEAD hypothesis `hBdRun` (`Bd b D`, here `kidsMaskedN D.modules b.body = true`) of
-- `Tools/ShippingShipsFreeMasked.lean:37` `machine_design_noShips_noBd` is discharged for `parent` on the NEW boundary.
-- That is the statement reached; soundL / composed / hFacts / hOuts stay PREMISES (OPEN on the new boundary).
-- Not a semantic-equivalence head completion; not runtime fit.

/-! # Unit SR3d: `parent`'s depth endpoint with the children's bound (`kidsMaskedN`) discharged on `AdmCtx`/`JQ`

The mask is CONSUMED at `Tools/ShippingShipsFreeMasked.lean:152-160`: `design_at_free … (hBdRun hcore hpost hBnd)`, where
`Bd b D := kidsMaskedN D.modules b.body = true` feeds `hBd := KSn_boundedIn` (`Tools/ShippingMachineShipsDepth.lean:171`)
inside `machine_ships_hierC_at_free`.  The old generated instance is `parent.machine_design_noShipsNoMaskedNR1`
(`Tests/Compiler/ShipsFreeMaskedTest.lean`), whose `machine_maskedG` takes `hB : ChildBnd mref cref w`.

Here the head is applied with the run boundary `Bnd := BndA` (laws `O`, `T`, `AdmCtx`, `MachineDefines` of the callee `cnt`,
the start world `JQ O.quiet D₀ w` with `D₀ = 0 ∨ CacheInvA`) and `hBdRun` is proved from
`KidsMaskedParentATest.parent_kidsMaskedN_topA` (`hkidM` from `leaf_real_kidMA`, closing `parent_closesA`).
Statement: that of the head at `declName := parent` with `Bnd := BndA`, `hBdRun` REMOVED; every other hypothesis is the
head's, unchanged. -/

namespace Tests.Compiler.ParentEndpointMaskedATest
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

/-- The run boundary of the NEW endpoint of `parent`: laws `O`, `T` (PREMISES, a separate assumption family), the
admissible contexts, `MachineDefines` of the callee `cnt`, and a start world in `JQ`.  It replaces `ChildBnd`. -/
def BndA : CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

set_option maxHeartbeats 4000000 in
/-- **`parent`'s depth endpoint, `kidsMaskedN` discharged on the new boundary.** -/
theorem parent_noShips_noBdA (n : Nat)
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
    (houtTy : ∀ o ∈ parent.machineData.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational ``parent) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref ``parent parent.machineData.shape)
    (closes : C mctx mref cctx cref)
    -- the run's facts of the full entry's module, from the CORE run the full entry contains
    (hFacts : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      BndA mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b)
    -- the output check, from the same core run, under the statement-kind gate
    (hOuts : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore ``parent [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      hierGate b = true → BndA mctx mref cctx cref w raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (-- checker premises: only `designCheck` (the success condition of this implication)
        -- the shipped design's emitted-text checks
        designCheck (childMap D.modules) n (checkedOptimize b) = true →
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
                  (envs'[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  refine ⟨raw, D, hpost, ?_⟩
  intro hdc hBnd
  have hBdRun : kidsMaskedN D.modules b.body = true := by
    obtain ⟨O, T, hA, hR0, D₀, hw, hc⟩ := hBnd
    exact KidsMaskedParentATest.parent_kidsMaskedN_topA O T hA hcore entry hR0 hw hc hpost
  exact design_at_free n (ResetNk n) (BndA mctx mref cctx cref w) (fun b D => kidsMaskedN D.modules b.body = true)
    (machine_ships_hierC_at_free (fun D => KSn (childMap D.modules) n)
      (fun D => KSn_local (childMap D.modules) n) (ResetNk n) BndA C
      (fun b D => kidsMaskedN D.modules b.body = true) (fun _ _ => True)
      (fun b D h => KSn_boundedIn D.modules b.body h n) (true_inv (ResetNk n)) parent.machineData soundL composed
      houtTy hcore hpost entry closes (fun hBnd => hFacts hcore hpost hBnd))
    (fun hBnd => hOuts hcore hpost (hFacts hcore hpost hBnd).gate hBnd) hdc hBnd hBdRun

open Lean Elab Command Meta Term in
/-- Split `∃ raw D, hp ∧ (dc → B → rest)` into `(hp, dc, B, rest)` over shared `raw D`. -/
def splitConcl (e : Lean.Expr) (raw D : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let e ← whnfR e
  unless e.getAppFn.isConstOf ``Exists do throwError "not ∃: {e}"
  let e1 := (e.appArg!.bindingBody!).instantiate1 raw
  unless e1.getAppFn.isConstOf ``Exists do throwError "not ∃ (2): {e1}"
  let e2 := (e1.appArg!.bindingBody!).instantiate1 D
  let hp := e2.appFn!.appArg!
  let imp := e2.appArg!
  let .forallE _ dc b1 _ := imp | throwError "no dc: {imp}"
  let .forallE _ B rest _ := b1 | throwError "no B: {b1}"
  return (hp, dc, B, rest)

open Lean Elab Command Meta Term in
/-- Instantiate the binders of `ty` one by one.  A binder whose user name matches an entry of `shared` (fvars of the OTHER
theorem's telescope) AND whose domain is `isDefEq` to that fvar's type is instantiated with THAT FVAR (aligned).  A binder named
in `gen` (a parameter the new theorem GENERALISES: the old one fixes it to a concrete value) becomes a metavariable, to be
solved by the comparison and then printed / asserted.  Any other binder gets a fresh fvar. -/
partial def alignInst {α : Type} (shared : Array Lean.Expr) (gen : List String) (ty : Lean.Expr)
    (k : Lean.Expr → Array String → Array String → Array (String × Lean.Expr) → MetaM α)
    (al fr : Array String := #[]) (ms : Array (String × Lean.Expr) := #[]) : MetaM α := do
  match ty with
  | .forallE n d b bi =>
    let mut hit : Option Lean.Expr := none
    for x in shared do
      if hit.isNone && (← x.fvarId!.getUserName) == n then
        if ← isDefEq d (← inferType x) then hit := some x
    match hit with
    | some x => alignInst shared gen (b.instantiate1 x) k (al.push n.toString) fr ms
    | none =>
      if gen.contains n.toString then
        let m ← mkFreshExprMVar d
        alignInst shared gen (b.instantiate1 m) k al fr (ms.push (n.toString, m))
      else
        withLocalDecl n bi d fun x => alignInst shared gen (b.instantiate1 x) k al (fr.push n.toString) ms
  | _ => k ty al fr ms

open Lean Elab Command Meta Term in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := ``parent_noShips_noBdA
  let old := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent.machine_design_noShipsNoMaskedNR1
  stdAxioms new
  let ty := (← getConstInfo new).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      let nm := (← x.fvarId!.getUserName).toString
      if (← isProp t) then ps := ps.push s!"{nm} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let cl ← depClosure new
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{new}: old boundary in closure: {bad}"
  for must in [``Tests.Compiler.KidsMaskedParentATest.parent_kidsMaskedN_topA, ``Tools.ShippingShipsFree.design_at_free,
      ``Tools.ShippingKidsSelfA.core_kidsMaskedN_topA, ``Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA] do
    unless cl.contains must do throwError "SR3d AUDIT FAILED: {must} not in the closure"
  let to := (← getConstInfo old).type
  forallTelescope to fun oldXs co => do
    let oldNames ← oldXs.mapM fun x => do return (← x.fvarId!.getUserName).toString
    let gen := ["kD", "n", "ι", "dom", "src", "ext", "extB"]
    alignInst oldXs gen ty (fun cn al fr ms => do
      let expAl := ["mctx", "mref", "cctx", "cref", "w", "w'", "b", "design", "hr", "entry"]
      unless al.toList == expAl do throwError "SR3e AUDIT FAILED: aligned shared binders {al}, expected {expAl}"
      logInfo m!"SR3e ALIGNMENT: shared binders are the OLD theorem's FVARS (same name, defeq type): {al}; GENERALISED parameters (metavariables, solved below): {ms.map (·.1)}; other new-only binders (fresh fvars, not in the conclusion): {fr}; old binders {oldNames}"
      withLocalDeclD `raw (mkConst ``Sparkle.IR.AST.Module) fun raw => withLocalDeclD `D (mkConst ``Sparkle.IR.AST.Design) fun D => do
        let (hpO, dcO, BO, restO) ← splitConcl co raw D
        let (hpN, dcN, BN, restN) ← splitConcl cn raw D
        let ok1 ← isDefEq hpN hpO
        let ok2 ← isDefEq dcN dcO
        let ok3 ← isDefEq restN restO
        unless ok1 && ok2 && ok3 do
          throwError "conclusion parts differ (post {ok1}, designCheck {ok2}, rest {ok3}):\n old rest {restO}\n new rest {restN}"
        let mut sol : Array String := #[]
        for (nm, m) in ms do
          let v ← instantiateMVars m
          if v.hasExprMVar then throwError "SR3e AUDIT FAILED: generalised parameter {nm} not solved: {v}"
          sol := sol.push s!"{nm} := {← ppExpr v}"
        unless sol.any (·.startsWith "n := 1") && sol.any (·.startsWith "kD := 1") do
          throwError "SR3e AUDIT FAILED: depth/kD not instantiated to 1: {sol}"
        let BNu ← whnfD (← instantiateMVars BN)
        logInfo m!"SR3e SOLUTION of the generalised parameters (old = new at these): {sol}"
        logInfo m!"SR3e CONCLUSION CHECK OK (shared arguments are FVARS of the old theorem; only the GENERALISED parameters were unified, listed in SOLUTION; fvars-aligned, so defeq for arbitrary values of the shared arguments): {new} and {old} agree on post-processing, designCheck and the body of the run-implication; only the boundary differs.\n OLD boundary: {BO}\n NEW boundary (BndA unfolded, an EXISTENTIAL over the laws / contexts / reflections / start world, NOT a proof that it holds): {BNu}")
  logInfo m!"SR3e AUDIT: {new}: closure {cl.size}; outer Prop premises ({premises.size}): {premises}"
  let expected := ["soundL : [anonymous]", "composed : [anonymous]", "houtTy : [anonymous]",
    "hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines",
    "closes : [anonymous]", "hFacts : [anonymous]", "hOuts : [anonymous]"]
  unless premises.toList == expected do
    throwError "SR3e AUDIT FAILED: outer Prop premises (name : head, [anonymous] = a ∀/→ binder) are {premises}, expected {expected}"
  logInfo m!"SR3e PREMISE LIST ASSERTED: exactly the {expected.length} outer Prop premises {expected}"

#print axioms parent_noShips_noBdA

end Tests.Compiler.ParentEndpointMaskedATest
