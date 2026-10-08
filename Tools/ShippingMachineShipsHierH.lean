import Tools.ShippingHierTyped
import Tools.ShippingGateChild

/-! # A machine with combinational children, at the full entry and the optimizer

A machine whose calls are one-output combinational children (`closeInsts`)
has its composed theorem (`f.machine_composed`, `runs_of_linked`) in the
combinational linked semantics `runModuleH` of the CORE module, with the
premise that each call's module is a run of its child's full entry (`R`).
At the full entry the module is the core one (the zero-width cleanup is the
identity on machine modules, the checked merge the identity on an
instance-bearing body), and the printer is given `checkedOptimize` of it,
which keeps the optimizer's output only when `hierRefineCheck` accepts it:
`hierRefineCheck_linkedH` carries the run over to the optimized module when
the children compute from their input ports (`kidsLocal`). -/
namespace Tools.ShippingMachineShipsHierH
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierOptRun Tools.ShippingHierOptRunH
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineShipsHier
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The composed theorem of a machine with combinational children
(`runs_of_linked`'s conclusion): the combinational linked run of `m` shows
the source, given that each call's module satisfies `R`. -/
def ComposedH (R : Nat → Sparkle.IR.AST.Module → Prop) (declName : Name) (d : MachineData) (kD : Nat)
    (m : Sparkle.IR.AST.Module) (dsn : Design) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (bools j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
        Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
          d.shape.layout.slots.length
          ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
        moduleByName dsn.modules mc.name = some mc →
        R k mc) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

/-- **A machine with combinational children, at the full entry and the
optimizer.** From its wired endpoint (`soundL`, for the cleanup facts) and
its composed theorem, a run of the full entry returns a module `b` whose
shipped optimization `checkedOptimize b`, in the combinational linked
semantics over the children of the core design, shows the source — when the
optimizer check binds on `b` and the decidable design facts hold, and given
(as the composed theorem does) that each call's module satisfies `R`. -/
theorem machine_ships_hierH (R : Nat → Sparkle.IR.AST.Module → Prop)
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
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom srcL extL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      ComposedH R declName d kD m design dom src ext)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (hierBinds b = true →
        -- the design facts (decidable on the run's modules)
        linkedWF (childMap D.modules) b.body = true →
        linkedWF (childMap D.modules) (checkedOptimize b).body = true →
        (instNames b.body).Nodup → (instNames (checkedOptimize b).body).Nodup →
        kidsLocal D.modules (checkedOptimize b).body = true →
        (∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → ∀ child cwe,
          childMap D.modules mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
            c.2 = .ref w → w ∉ instOutWires child.outputs conns) →
        (∀ w ∈ bodyInstOuts (childMap D.modules) b.body, w ∈ (openIns b).map (·.name)) →
        Tools.ShippingHierTyped.hierTyped (childMap D.modules) b = true →
        "rst" ∈ b.inputs.map (·.name) →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (bools j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            -- each call's module is its child's (the composed theorem's premise)
            (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ raw.body →
              Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
                d.shape.layout.slots.length
                ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
              moduleByName D.modules mc.name = some mc →
              R k mc) →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 →
            (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
            ∃ envsO, runModuleH (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T st0 mems = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  refine ⟨raw, D, hpost, ?_⟩
  intro hbind hwfB hwfO hndB hndO hloc hnofb hOutM hkm hrstIn
  have hI := hasInst_of_hierBinds hbind
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := composed hcore entry closes
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems hsrc hpass hrstZ hinit hcalls hinsFit hstX hstR
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T (seedIn b ins) st0 mems hsrc hpass hrst
    hinit hcalls
  have hrunB : runModuleH (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T st0 mems = some envs := by
    rw [hbW, hbB]; exact hrun
  -- the optimizer: checked on the extracted interface, or not applied
  have hopt : checkedOptimize b = (if hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b))
      then deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
    unfold checkedOptimize
    simp only [simpleBody_inst hI, not_all_seqOk hI, hbind, Bool.false_eq_true, if_false, if_true]
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
  · rw [hopt, if_pos hacc] at hwfO hndO hnofb hloc ⊢
    obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linkedH D.modules hacc
      hwfB hwfO hndB hndO hloc hnofb hOutM ins hinsFit hrstIn hrstZ hrunB
      (Tools.ShippingHierTyped.fitX_of_typed D.modules b ins hkm hinsFit hrunB hstX) hstR
    refine ⟨envsO, hrunO, by omega, ?_⟩
    intro j hj k o f hk hf
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (houtSrc k o hk)
    rw [← hpn, hcorr p hp j hj (by omega), hpn]
    exact hobs j (by omega) k o f hk hf
  · rw [hopt, if_neg hacc]
    exact ⟨envs, hrunB, hlen, hobs⟩

end Tools.ShippingMachineShipsHierH
