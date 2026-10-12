import Tools.ShippingShipsDesignSVAll
import Tools.ShippingMachineShipsHierH
import Tools.ShippingGuardsSound
import Tools.ShippingChecksDepthGate
import Tools.ShippingOneOutFacts

/-! # The COMBINATIONAL head without its four check antecedents (G1, round par/a-6)

The deepest endpoint of a parent of combinational one-output children
(`caller` and the other parents closed by `closeInsts`) is

    f.machine_design_svHR = ships_design_svH_all ∘ f.machine_ships_hierHR
                          = ships_design_svH_all ∘ machine_ships_hierHC …

whose conclusion is `∃ raw D, … ∧ (shipsHierHCheck D.modules b = true → Bnd →
kidsComb D.modules o.body = true → designCheck C 0 o = true → outsCheck C 0 o
= true → …)` (`o = checkedOptimize b`, `C = childMap D.modules`).

`machine_design_svH_free` takes `machine_ships_hierHC`'s arguments (the same
`R`, `Bnd`, `C`, data, wired endpoint, composed theorem, output-width fact)
and concludes `ships_design_svH_all`'s conclusion with those four
antecedents REMOVED and replaced by ONE antecedent `Extra b D` — the
residual check premises, chosen by the instance (`fun _ _ => True` when
there is none). In exchange it takes four hypotheses, each "from the core
run the full entry contains" (the form of `machine_design_noPorts`):

* `hFacts`: `Tools.ShippingOneOutFacts.RunFactsH D.modules b` — the
  statement-kind gate, distinct instance names, the self-read test, the
  extraction of the instance-driven wires, the reset input, the children's
  combinational check, all of the full entry's module `b`;
* `hTyped`: `hierTyped (childMap D.modules) b` (the width typing the
  accepted-candidate branch needs), possibly from `Extra`;
* `hDesign`: `designCheck (childMap D.modules) 0 (checkedOptimize b)`,
  possibly from `Extra`;
* `hOuts`: `outsCheck (childMap D.modules) 0 (checkedOptimize b)` under the
  gate.

How the four antecedents go:

* `shipsHierHCheck = hierCheck && kidsLocal && hierTyped`. `hierCheck`'s
  first conjunct `hierBinds b` is NOT derived and not needed: the proof
  splits on the compiler's own branches (not binding: the module is shipped
  as it is; binding and rejected: the same; binding and accepted: the
  guards `deinline_guards` give conjuncts 2 and 4 of the candidate, the
  instance statements carry conjunct 5 and `kidsLocal`) — the route of
  `machine_ships_hierC_free`. Conjuncts 3, 5, 6, 7 are `hFacts`; `kidsLocal`
  is `kidsLocal_of_comb` of `hFacts.comb`; `hierTyped` is `hTyped`.
* `kidsComb … o.body`: `hFacts.comb` moved along the instance statements.
* `designCheck`, `outsCheck`: `hDesign`, `hOuts`.

The proof is `machine_ships_hierHC`'s, `ships_design_svH`'s and
`ships_design_svH_all`'s, joined at the run's own `raw`, `D`
(`synthesizeCombinational_checked`); the statement's hypothesis block and
conclusion are copied by a script from `Tools/ShippingMachineShipsHierH.lean`
and `Tools/ShippingShipsDesignSVAll.lean`.

SCOPE. Nothing here is specific to a declaration; the head says nothing
about WHICH parents satisfy its four hypotheses. `hFacts.rst` is `"rst" ∈
b.inputs`: a parent WITHOUT a register and with combinational children has
no `rst` input, so this head does not apply to it as it stands.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOneOutHead
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingMachineShipsHierH (ComposedH)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

set_option maxHeartbeats 4000000 in
/-- **A machine with combinational one-output children, from the source to
every closed run of its design's emitted texts, with NO check antecedent
but the residual `Extra`.** -/
theorem machine_design_svH_free (R : Nat → Sparkle.IR.AST.Module → Prop)
    (Bnd : Tools.ShippingMachineShipsHier.CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {declName : Name} (d : MachineData) {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {srcL lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceL declName d m design dom srcL extL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      ComposedH R declName d kD m design dom src ext)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    -- the residual check premises on the full entry's module and the run's
    -- design (`fun _ _ => True` when every check is derived)
    (Extra : Sparkle.IR.AST.Module → Design → Prop)
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
      Tools.ShippingOneOutFacts.RunFactsH D.modules b)
    -- the width typing of the full entry's module (asked where the optimizer's
    -- candidate is accepted), from the same core run
    (hTyped : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Bnd mctx mref cctx cref w raw D → Extra b D →
      Tools.ShippingHierTyped.hierTyped (childMap D.modules) b = true)
    -- `designCheck` of the shipped module, from the same core run
    (hDesign : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Bnd mctx mref cctx cref w raw D → Extra b D →
      designCheck (childMap D.modules) 0 (checkedOptimize b) = true)
    -- the output check, from the same core run, under the statement-kind gate
    (hOuts : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      hierGate b = true → Bnd mctx mref cctx cref w raw D →
      Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) 0 (checkedOptimize b) = true) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (-- the residual check premises (none when `Extra` is `fun _ _ => True`)
        Extra b D →
        -- the run boundary, in the run's contexts
        Bnd mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KidState),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (bools j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ raw.body →
              Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
                d.shape.layout.slots.length
                ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
              moduleByName D.modules mc.name = some mc →
              R k mc) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
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
  intro hX hBnd
  have hL := soundL hcore entry closes hBnd
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, hlink, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  -- the run's facts
  have hF := hFacts hcore hpost hBnd
  have hgate : hierGate b = true := hF.gate
  have hndB : (Tools.ShippingHierState.instNames b.body).Nodup := hF.ndB
  have hOut : Tools.ShippingHierPremisesBase.outsExtracted (childMap D.modules) b = true :=
    hF.outs
  have hrstIn : "rst" ∈ b.inputs.map (·.name) := hF.rst
  have hOutM := Tools.ShippingHierPremisesBase.outsExtracted_sound hOut
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact Tools.ShippingMachineShipsHier.mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hwfB : Tools.ShippingHierOpen.linkedWF (childMap D.modules) b.body = true := by
    rw [hbB, ← Tools.ShippingMachineLinked.linkedOk_eq]; exact hlink
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  -- the shipped module, whatever branch the compiler took
  obtain ⟨hwfS, hndS, hselfS, hcombS⟩ := Tools.ShippingOneOutFacts.shipped_factsH hF hwfB
  have hdc := hDesign hcore hpost hBnd hX
  have hoc := hOuts hcore hpost hgate hBnd
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, _, _, _, H⟩ := composed hcore entry closes hBnd
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstZ hinit hcalls hinsFit hstX hstR hinsW
    hstW hkidsW
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T (seedIn b ins) st0 mems hsrc hpass hrst
    hinit hcalls
  have hrunB : runModuleH (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T st0 mems = some envs := by
    rw [hbW, hbB]; exact hrun
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  -- the shipped module's combinational linked run, by cases on the compiler's branches
  have hship : ∃ envsO, runModuleH (declWidth (checkedOptimize b))
      (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T st0 mems = some envsO ∧
      envsO.length = T ∧
      ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
        d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
        (envsO[j]'hj) o.name = f j := by
    by_cases hbind : hierBinds b = true
    · have hopt := Tools.ShippingGuardsSound.checkedOptimize_binding hbind
      by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
      · -- accepted: the guards give conjuncts 2 and 4, the instance statements the rest
        obtain ⟨hwfO, hndO⟩ := Tools.ShippingGuardsSound.deinline_guards
          (o := Sparkle.IR.Optimize.optimizeModule b) hacc hwfB hndB hOut
        have hselfO : Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules)
            (deinline b (Sparkle.IR.Optimize.optimizeModule b)).body = true :=
          Tools.ShippingChecksDerived2.all_inst_transfer _
            (fun mn iname conns =>
              (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp)
            (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hF.self
        have hnofb := Tools.ShippingHierPremisesBase.noSelfRead_sound hselfO
        have hcombO : Tools.ShippingMachineDepthH.kidsComb D.modules
            (deinline b (Sparkle.IR.Optimize.optimizeModule b)).body = true :=
          Tools.ShippingChecksDerived2.all_inst_transfer _
            (fun mn iname conns =>
              (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp)
            (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hF.comb
        have hlocO := Tools.ShippingOneOutClose.kidsLocal_of_comb hcombO
        have hkm := hTyped hcore hpost hBnd hX
        rw [hopt, if_pos hacc]
        obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ :=
          Tools.ShippingHierOptRunH.hierRefineCheck_linkedH D.modules hacc
            hwfB hwfO hndB hndO hlocO hnofb hOutM ins hinsFit hrstIn hrstZ hrunB
            (Tools.ShippingHierTyped.fitX_of_typed D.modules b ins hkm hinsFit hrunB hstX) hstR
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
  obtain ⟨envsO, hrunH, hlenO, hobsO⟩ := hship
  -- the depth-0 run from any children's states, then the emitted texts
  have hrunT := Tools.ShippingMachineDepthH.runModuleTG_flat_of_H _ D.modules
    (checkedOptimize b).body (seedIn b ins)
    (Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwfS) hcombS T st0 mems kids envsO hrunH
  have hD : DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T
      ⟨st0, mems, kids⟩ envsO :=
    design_sv_runN D.modules 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO hdc
      hrunT
      (svBounds_of_checks D.modules 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩
        envsO hdc (Tools.ShippingShipsDesignSV.seedIn_bound hinsW) hstW hkidsW hrunT)
  refine ⟨⟨envsO, hD, hlenO, hobsO⟩, fun envs' hD' => ?_⟩
  exact Tools.ShippingDesignSVBack.design_sv_all D.modules 0 (checkedOptimize b) (seedIn b ins) T
    ⟨st0, mems, kids⟩ envsO
    (fun e => e.length = T ∧ ∀ j (hj : j < e.length) (k : Nat) (o : OutField) (f : Nat → Nat),
      d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f → (e[j]'hj) o.name = f j)
    hdc hoc (Tools.ShippingShipsDesignSV.seedIn_bound hinsW) hstW hkidsW hD ⟨hlenO, hobsO⟩ envs' hD'

end Tools.ShippingOneOutHead
