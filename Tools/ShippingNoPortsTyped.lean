import Tools.ShippingNoPorts
import Tools.ShippingKidsTyped
-- Round par/o-typed. BUILT as written: ty2 (`lake build Tools.ShippingNoPortsTyped`, exit 0), committed
-- in 64e813fd; axioms standard (audited in `Tests.Compiler.MemNameCollisionGateTypedTest`).

/-! # The depth-0 head with a TYPED children bound (round par/o-typed, Option A)

`Tools.ShippingNoPorts.machine_design_noPorts` at depth `0` asks a children bound `Bd b D` with
`hBd : Bd b D → KSBoundedIn (childMap D.modules) flatKS b.body Inv`: every child's outputs within
their ports' widths in EVERY environment. Its only consumer is `fitX_of_run` inside
`machine_ships_hierC_at_free` (the accepted-candidate branch). A combinational GATE child is
bounded only on bounded inputs.

`machine_design_noPortsT`: the same head at depth `0` (`KSn _ 0`), its proof
`machine_ships_hierC_at_free`'s and `design_at_free`'s joined at the run's own `raw`, `D`, with

* `Bd` / `hBd` / `hBdRun` REPLACED by ONE hypothesis from the core run, `hTyped :
  … → TypedRun (childMap D.modules) b Inv` (`Tools.ShippingKidsTyped`): typed assignments,
  extracted inputs off the outputs, each instance FREE-bounded (the `KSBoundedIn` clause of
  that instance) or TYPED;
* `fitX_of_run` replaced by `Tools.ShippingKidsTyped.fitX_of_runTyped`. A typed instance's start
  state is read off the existing `InvN` hypothesis of the conclusion (the shipped module has the
  full entry's instance statements, `hierRefineCheck_inst_iff`), through `TypedKid`'s width-table
  clause;
* ONE added run hypothesis of the conclusion (the initial-state condition):

      BoundOff (declWidth b) (b.outputs.map (·.name)) st0

  (the start state within the full entry's declared widths off its output ports — the
  condition `Tools.ShippingOneOutHead.machine_design_svH_free` already asks, in place of the
  extracted-input one, for the same reason: a width-typed run is bounded only from a bounded
  state). The other hypotheses of the conclusion are unchanged.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingNoPortsTyped
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier
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
/-- **The depth-0 head with NO check antecedent and the TYPED children bound**: the boundary
`Bnd` is the only antecedent of the conclusion; the children are bounded by `hTyped` from the
core run. -/
theorem machine_design_noPortsT
    (Reset : Sparkle.IR.AST.Module → Design → (String → KT 0) → Prop)
    (Bnd : CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    (Inv : Sparkle.IR.AST.Module → KT 0 → Prop)
    (hRI : ResetImpliesInv Reset Inv)
    {declName : Name} (d : MachineData) {kD : Nat}
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
    -- the wired endpoint, for the cleanup facts only
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceLB declName d m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      ComposedG (fun D => KSn (childMap D.modules) 0) Reset declName d kD m design dom src ext extB)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref)
    -- the run's facts of the full entry's module, from the CORE run the full entry contains
    (hFacts : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Bnd mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b)
    -- the output check, from the same core run, under the statement-kind gate
    (hOuts : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      hierGate b = true → Bnd mctx mref cctx cref w raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) 0 (checkedOptimize b) = true)
    -- the TYPED children bound, from the same core run (in place of `Bd` / `hBd` / `hBdRun`)
    (hTyped : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Bnd mctx mref cctx cref w raw D →
      Tools.ShippingKidsTyped.TypedRun (childMap D.modules) b Inv)
    -- `designCheck` of the shipped module from the same core run
    (hDesign : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Bnd mctx mref cctx cref w raw D →
      designCheck (childMap D.modules) 0 (checkedOptimize b) = true) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (-- NO checker premise: the boundary is the only antecedent
        Bnd mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT 0),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            Reset raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            -- ADDED: the start state within the declared widths off the output ports
            Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 →
            -- the emitted widths' use conditions: inputs, start registers, instance states
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
            Bounded (weS (checkedOptimize b)) st0 →
            (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
              childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)) →
            -- a closed run of the emitted texts showing the source exists ...
            (∃ envsO,
              DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j)
            -- ... and EVERY closed run from the same seeding and states shows it
            ∧ ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                envs'.length = T ∧
                ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envs'[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  refine ⟨raw, D, hpost, ?_⟩
  intro hBnd
  have hdc := hDesign hcore hpost hBnd
  have hTy := hTyped hcore hpost hBnd
  -- `machine_ships_hierC_at_free`'s proof (copied), `fitX_of_run` replaced
  have hL := soundL hcore entry closes hBnd
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, hlink, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  have hFc := hFacts hcore hpost hBnd
  obtain ⟨hgate, hwfB, hndB, hself, hOut, hrstIn, hIW⟩ := hFc
  have hoc := hOuts hcore hpost hgate hBnd
  have hOutM := Tools.ShippingHierPremisesBase.outsExtracted_sound hOut
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  have hmf : Tools.ConeFold.memFree raw.body := by
    rw [← hbB]; exact memFree_of_linkedWF _ hwfB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := composed hcore entry closes hBnd hmf
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstZ hclk hinit hreset hinsFit _hstX hstR
    hstB hinsW hstW hkidsW
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T (seedIn b ins) st0 mems kids hsrc hpass hrst
    hclk hinit hreset
  have hrunB : runModuleTG (KSn (childMap D.modules) 0) (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T ⟨st0, mems, kids⟩ = some envs := by
    rw [hbW, hbB]; exact hrun
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  -- the shipped module's linked run, by cases on the compiler's branches
  have hship : ∃ envsO, runModuleTG (KSn (childMap D.modules) 0) (declWidth (checkedOptimize b))
      (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
      envsO.length = T ∧
      ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
        d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
        (envsO[j]'hj) o.name = f j := by
    by_cases hbind : hierBinds b = true
    · have hopt := Tools.ShippingGuardsSound.checkedOptimize_binding hbind
      by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
      · -- accepted: the guards give conjuncts 2 and 4, the instance statements 5
        obtain ⟨hwfO, hndO⟩ := Tools.ShippingGuardsSound.deinline_guards
          (o := Sparkle.IR.Optimize.optimizeModule b) hacc hwfB hndB hOut
        have hselfO : Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules)
            (deinline b (Sparkle.IR.Optimize.optimizeModule b)).body = true :=
          Tools.ShippingChecksDerived2.all_inst_transfer _
            (fun mn iname conns =>
              (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp)
            (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hself
        have hnofb := Tools.ShippingHierPremisesBase.noSelfRead_sound hselfO
        -- the instances' states: the reset's invariant, and a typed instance's registers
        -- within its declared widths (from `InvN` at the shipped module's instance statement)
        have hkO : Tools.ShippingKidsTyped.KidsOk (childMap D.modules) (declWidth b)
            (b.outputs.map (·.name)) b.body Inv kids := by
          intro mn iname conns hm child cwe hc
          refine ⟨hRI raw D kids hreset mn iname conns (by rw [← hbB]; exact hm) child cwe hc,
            fun hTK => ?_⟩
          have hmO : Stmt.inst mn iname conns ∈ (checkedOptimize b).body := by
            rw [hopt, if_pos hacc]
            exact (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mpr hm
          have hB0 := hkidsW mn iname conns child cwe hmO hc
          intro x hx
          -- (writing-time guess, accepted by build ty2): `InvN _ 0 child ks` unfolds to `Bounded (weS child) ks.st`
          have h1 : (kids iname).st x < 2 ^ weS child x := hB0 x
          exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (hTK.2.2.2 x hx))
        -- (writing-time guess, accepted by build ty2): `KSn _ 0` / `KT 0` against `flatKS` / `KidState` (definitional)
        have hfit := Tools.ShippingKidsTyped.fitX_of_runTyped (childMap D.modules) b Inv hTy
          hwfB hndB hIW ins hinsFit T _ envs hrunB hstB hkO
        rw [hopt, if_pos hacc]
        obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linked
          (KSn (childMap D.modules) 0) (KSn_local (childMap D.modules) 0) (childMap D.modules) hacc
          hwfB hwfO hndB hndO hnofb hOutM ins hinsFit hrstIn hrstZ hrunB hfit hstR
        refine ⟨envsO, hrunO, by omega, ?_⟩
        intro j hj k o f hk hf
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (houtSrc k o hk)
        rw [← hpn, hcorr p hp j hj (by omega), hpn]
        exact hobs j (by omega) k o f hk hf
      · rw [hopt, if_neg hacc]
        exact ⟨envs, hrunB, hlen, hobs⟩
    · -- the check does not bind: the module is shipped as it is
      have hb0 : hierBinds b = false := by simpa using hbind
      rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate hb0]
      exact ⟨envs, hrunB, hlen, hobs⟩
  obtain ⟨envsO, hrunS, hlenS, hobsS⟩ := hship
  -- `design_at_free`'s proof (copied)
  have hD : DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T
      ⟨st0, mems, kids⟩ envsO :=
    design_sv_runN D.modules 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc hrunS
      (svBounds_of_checks D.modules 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc
        (seedIn_bound hinsW) hstW hkidsW hrunS)
  refine ⟨⟨envsO, hD, hlenS, hobsS⟩, fun envs' hD' => ?_⟩
  exact Tools.ShippingDesignSVBack.design_sv_all D.modules 0 (checkedOptimize b) (seedIn b ins) T
    ⟨st0, mems, kids⟩ envsO
    (fun e => e.length = T ∧ ∀ j (hj : j < e.length) (k : Nat) (o : OutField) (f : Nat → Nat),
      d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f → (e[j]'hj) o.name = f j)
    hdc hoc (seedIn_bound hinsW) hstW hkidsW hD ⟨hlenS, hobsS⟩ envs' hD'

end Tools.ShippingNoPortsTyped
