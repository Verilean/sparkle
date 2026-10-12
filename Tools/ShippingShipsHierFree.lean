import Tools.ShippingMachineShipsHier
import Tools.ShippingGuardsSound

/-! # The shipping head WITHOUT the bundled checker (isolated branch `fix/opt-fallback`)

`machine_ships_hierC` asks `shipsHierCheck (childMap D.modules) b = true`.
On this branch `checkedOptimize` falls back to the input module whenever
its hierarchical check does not bind, and its candidate is guarded
(`Sparkle.IR.HierCheck.deinline`), so the head follows from what the core
run PROVIDES of the full entry's module (`RunFacts`: `core_hierGate`,
`core_linkedWF`, `core_raw_facts`, `core_outsExtracted`,
`core_instOutWidthsOk`) by cases on the compiler's own branches:

* `hierBinds b = false`: the shipped module is `b` (the gate holds), the
  conclusion is the core run itself;
* binding, `hierRefineCheck b (deinline b o)` rejected: `b` again;
* accepted: conjunct 2 and 4 of the candidate are the guards
  (`deinline_guards`), conjunct 5 moves along the instance statements, 6, 7,
  8 are the run's — `hierRefineCheck_linked`, as in `machine_ships_hierC`.

`machine_ships_hierC_free` is `machine_ships_hierC`'s statement with the
checker antecedent REMOVED and one hypothesis added, `facts`: the run's
facts from the core run, in the shape of `soundL` / `composed` (it is
`core_runFacts`, `Tools/ShippingChecksRunFacts.lean`, for a machine with
calls). The proof is `machine_ships_hierC`'s (statement and proof lines
copied by a script), with the case split in place of the checker.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingShipsHierFree
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
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineShipsHier

/-- **A machine with instances, to its shipped module, with no checker
premise.** -/
theorem machine_ships_hierC_free {σ : Type} (KS : Design → KStep σ) (hloc : ∀ D, KSLocal (KS D))
    (Reset : Sparkle.IR.AST.Module → Design → (String → σ) → Prop)
    (Bnd : CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    (Bd : Sparkle.IR.AST.Module → Design → Prop) (Inv : Sparkle.IR.AST.Module → σ → Prop)
    (hBd : ∀ b D, Bd b D → KSBoundedIn (childMap D.modules) (KS D) b.body Inv)
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
    -- the wired endpoint, for the cleanup facts only (its source may be the
    -- fused / sign-normalised one a transported endpoint rewrites)
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
      ComposedG KS Reset declName d kD m design dom src ext extB)
    -- what the core run provides of the full entry's module
    (facts : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      ∀ b : Sparkle.IR.AST.Module, (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) →
      Tools.ShippingGuardsSound.RunFacts (childMap design.modules) b)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (-- NO checker premise: the run's facts are derived (`facts`)
        -- the run boundary of the children (in the run's contexts)
        Bnd mctx mref cctx cref w raw D →
        -- the children's outputs within their ports' widths
        Bd b D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → σ),
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
            ∃ envsO, runModuleTG (KS D) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  refine ⟨raw, D, hpost, ?_⟩
  intro hBnd hBdb
  have hL := soundL hcore entry closes hBnd
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, hlink, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  obtain ⟨hgate, hwfB, hndB, hself, hOut, hrstIn, hIW⟩ := facts hcore entry closes hBnd b hpost
  have hOutM := Tools.ShippingHierPremisesBase.outsExtracted_sound hOut
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hKSb := hBd b D hBdb
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbI : b.inputs = raw.inputs := by rw [hbr]; exact hi
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  have hmf : Tools.ConeFold.memFree raw.body := by
    rw [← hbB]; exact memFree_of_linkedWF _ hwfB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := composed hcore entry closes hBnd hmf
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstZ hclk hinit hreset hinsFit hstX hstR
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T (seedIn b ins) st0 mems kids hsrc hpass hrst
    hclk hinit hreset
  have hrunB : runModuleTG (KS D) (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T ⟨st0, mems, kids⟩ = some envs := by
    rw [hbW, hbB]; exact hrun
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  by_cases hbind : hierBinds b = true
  · -- the optimizer: checked on the extracted interface, or not applied
    have hopt : checkedOptimize b = (if hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b))
        then deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
      unfold checkedOptimize
      simp only [simpleBody_inst hI, not_all_seqOk hI, hbind, Bool.false_eq_true, if_false, if_true]
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
      rw [hopt, if_pos hacc]
      obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linked
        (KS D) (hloc D) (childMap D.modules) hacc
        hwfB hwfO hndB hndO hnofb hOutM ins hinsFit hrstIn hrstZ hrunB
        (fitX_of_run _ (childMap D.modules) b Inv hKSb ins hwfB hndB hIW T _ envs hrunB
          (fun mn iname conns hm child cwe hc => hRI raw D kids hreset mn iname conns
            (by rw [← hbB]; exact hm) child cwe hc) hstX) hstR
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

end Tools.ShippingShipsHierFree
