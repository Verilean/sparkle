import Tools.ShippingNoPortsTyped

/-! # The initial-state condition off the input ports (round o-bo)

`Tools.ShippingNoPortsTyped.machine_design_noPortsT` adds one run hypothesis to its conclusion:

    BoundOff (declWidth b) (b.outputs.map (·.name)) st0

That is, every name off the output ports is within the full entry's DECLARED width. `declWidth`
reads the wires only and gives `0` to every other name.

**This is not derivable from the head's other hypotheses.** The head's other start-state
hypotheses are:
* `Bounded (weS (checkedOptimize b)) st0` (the EMITTED widths: wires, inputs, outputs);
* the register bound;
* the extracted-input bound.

They bound a name by its emitted width, and an input port that is not a wire has emitted width
≥ 1 but declared width `0`. On the certified compile of `collMixSame` (shadow probe bo2, both
post-processing branches), the only names with `weS (checkedOptimize b) x > declWidth b x` off
the outputs are `clk` and `rst` (emitted 1, declared 0). The state `st0 "clk" = 1` (all else as
any admissible start) satisfies every other hypothesis and violates `BoundOff`.

**State correspondence.** The run reads its state only through `seedIn b ins t st`, which
overwrites every input port with `ins t`; `applyNexts` carries the other names. So the start
state's input-port values are never read, and the typed invariant needs the state bounded only
off the outputs AND the inputs (`runModuleTG_typedS`, `fitX_of_runTypedS`; the inputs are bounded
in every cycle's environment by `hinsFit`).

`machine_design_noPortsTI`: `machine_design_noPortsT` with the run hypothesis WEAKENED to

    BoundOff (declWidth b) (b.outputs.map (·.name) ++ b.inputs.map (·.name)) st0

(`boundOffI_of_boundOff`: the old hypothesis implies the new one). The proof is
`machine_design_noPortsT`'s, with `fitX_of_runTyped` replaced by `fitX_of_runTypedS`.

What remains open is the width relation `weS (checkedOptimize b) x ≤ declWidth b x` off the
ports. Given it, `boundOffI_of_bounded` derives the weakened hypothesis from `Bounded (weS …) st0`
(already a hypothesis of the conclusion). The relation reduces (`weS_checkedOptimize_le`) to `b`'s
wire names being distinct and all its port and wire names sanitize-stable; this is not yet
exported by the machine route's run facts.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingNoPortsTypedI
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingHierTyped (BoundOff)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingKidsTyped

/-! ## The typed run with the state bounded off the inputs too -/

theorem boundOffI_of_boundOff {we : WEnv} {X I : List String} {env : Env}
    (h : BoundOff we X env) : BoundOff we (X ++ I) env :=
  fun n hn => h n (fun hx => hn (List.mem_append_left _ hx))

/-- **`runModuleTG_typed` with the state invariant off `Xp ++ I`**: the seeds lift a state bounded
off `Xp ++ I` to an environment bounded off `Xp`. -/
theorem runModuleTG_typedS (C : String → Option (Module × WEnv)) (m : Module)
    (Inv : Module → KidState → Prop) (ht : TypedRun C m Inv)
    (hwf : linkedWF C m.body = true) (hnd : (instNames m.body).Nodup)
    (hIW : instOutWidthsOk C (declWidth m) m.body = true) (I : List String)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, BoundOff (declWidth m) (m.outputs.map (·.name) ++ I) st →
      BoundOff (declWidth m) (m.outputs.map (·.name)) (seed t st)) :
    ∀ (T : Nat) (s : KState KidState) (envs : List Env),
      runModuleTG flatKS (declWidth m) C m.body seed T s = some envs →
      BoundOff (declWidth m) (m.outputs.map (·.name) ++ I) s.st →
      KidsOk C (declWidth m) (m.outputs.map (·.name)) m.body Inv s.kids →
      ∀ j (hj : j < envs.length), BoundOff (declWidth m) (m.outputs.map (·.name)) (envs[j]'hj)
  | 0, _, envs, h, _, _, j, hj => by
    simp only [runModuleTG, Option.some.injEq] at h; subst h; cases hj
  | k + 1, s, envs, h, hst, hkids, j, hj => by
    have hmf := memFree_of_linkedWF _ hwf
    simp only [runModuleTG] at h
    cases hS : stepModuleTG flatKS (declWidth m) C m.body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG flatKS (declWidth m) C m.body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG flatKS (declWidth m) C s.kids s.mems m.body (seed k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts (declWidth m) s.mems m.body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    have hM : memNexts (declWidth m) m.body s.mems envF' = some s.mems :=
      Tools.ConeFold.memNexts_memFree _ m.body hmf s.mems envF'
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    -- an instance's outputs fit the wires they drive, on a bounded environment
    have hI : ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body → ∀ child cwe,
        C mn = some (child, cwe) → ∀ e cres s1, BoundOff (declWidth m) (m.outputs.map (·.name)) e →
        flatKS child cwe (inConns child.outputs conns) e (s.kids iname) = some (cres, s1) →
        ∀ p ∈ child.outputs, ∀ w, conns.lookup p.name = some (.ref w) →
          w ∉ m.outputs.map (·.name) → cres p.name < 2 ^ declWidth m w := by
      intro mn iname conns hm child cwe hc e cres s1 hbe hk p hp w hl _
      rw [instOutWidthsOk_at hIW hm hc p hp w hl]
      obtain ⟨hinv, hbst⟩ := hkids mn iname conns hm child cwe hc
      rcases ht.kids mn iname conns hm child cwe hc with hfree | htk
      · exact (hfree e (s.kids iname) cres s1 hinv hk).1 p hp
      · exact typed_step_out htk.1 (connEnvS_boundOffT hbe htk.2.1 (hbst htk)) hk p hp
    have hbF : BoundOff (declWidth m) (m.outputs.map (·.name)) envF' :=
      evalAssignsKG_boundOff flatKS (declWidth m) (m.outputs.map (·.name)) C s.kids s.mems m.body
        _ envF' s.kids kids' hmf ht.asg hI (hseed k s.st hst) hK
    cases j with
    | zero => exact hbF
    | succ j =>
      refine runModuleTG_typedS C m Inv ht hwf hnd hIW I seed hseed k _ rest hR ?_ ?_ j
        (by simpa using hj)
      · exact boundOff_applyNexts hst
          (Tools.ShippingHierTyped.regNexts_bounded' (noMemB_of_memFree hmf) hN)
      · intro mn iname conns hm child cwe hc
        obtain ⟨child', cwe', envAt, cres, hc', hk, -, -⟩ :=
          Tools.ShippingHierOptLinked.linked_consistentKG flatKS (declWidth m) C s.kids s.mems
            m.body _ envF' s.kids kids' hwf hnd hK mn iname conns hm
        rw [hc] at hc'
        cases hc'
        obtain ⟨hinv, hbst⟩ := hkids mn iname conns hm child cwe hc
        rcases ht.kids mn iname conns hm child cwe hc with hfree | htk
        · exact ⟨(hfree envAt (s.kids iname) cres (kids' iname) hinv hk).2,
            fun htk' => typed_step_state htk'.1 (hbst htk') hk⟩
        · exact ⟨htk.2.2.1 _, fun htk' => typed_step_state htk.1 (hbst htk') hk⟩

/-- **`fitX_of_runTyped` from a start state bounded off the outputs and the inputs**: `seedIn`
overwrites the inputs, bounded by `hinsFit`. -/
theorem fitX_of_runTypedS (C : String → Option (Module × WEnv)) (m : Module)
    (Inv : Module → KidState → Prop) (ht : TypedRun C m Inv)
    (hwf : linkedWF C m.body = true) (hnd : (instNames m.body).Nodup)
    (hIW : instOutWidthsOk C (declWidth m) m.body = true) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (T : Nat) (s : KState KidState) (envs : List Env)
    (hrun : runModuleTG flatKS (declWidth m) C m.body (seedIn m ins) T s = some envs)
    (hst : BoundOff (declWidth m) (m.outputs.map (·.name) ++ m.inputs.map (·.name)) s.st)
    (hkids : KidsOk C (declWidth m) (m.outputs.map (·.name)) m.body Inv s.kids) :
    ∀ j (hj : j < envs.length), ∀ x ∈ (Sparkle.IR.HierCheck.openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x := by
  have hB := runModuleTG_typedS C m Inv ht hwf hnd hIW (m.inputs.map (·.name)) (seedIn m ins)
    (fun t st hb n hn => by
      simp only [seedIn]
      split
      · rename_i hi
        exact hinsFit t n (by simpa [List.contains_eq_mem] using hi)
      · rename_i hi
        refine hb n (fun hm => ?_)
        rcases List.mem_append.mp hm with h | h
        · exact hn h
        · exact hi (by simpa [List.contains_eq_mem] using h)) T s envs hrun hst hkids
  intro j hj x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact hB j hj p.name (ht.openX p hp)

/-! ## From the emitted widths -/

/-- **The weakened condition from `Bounded (weS o) st0`** and the width relation off the ports. -/
theorem boundOffI_of_bounded {o b : Module} {st0 : String → Nat}
    (hW : Bounded (Tools.ShippingDesignSV.weS o) st0)
    (hle : ∀ x, x ∉ b.outputs.map (·.name) → x ∉ b.inputs.map (·.name) →
      Tools.ShippingDesignSV.weS o x ≤ declWidth b x) :
    BoundOff (declWidth b) (b.outputs.map (·.name) ++ b.inputs.map (·.name)) st0 := by
  intro n hn
  have ho : n ∉ b.outputs.map (·.name) := fun h => hn (List.mem_append_left _ h)
  have hi : n ∉ b.inputs.map (·.name) := fun h => hn (List.mem_append_right _ h)
  exact Nat.lt_of_lt_of_le (hW n) (Nat.pow_le_pow_right (by omega) (hle n ho hi))

/-- **The emitted width of a module with `b`'s ports and a sub-list of `b`'s wires is at most
`b`'s declared width off the ports**, when `b`'s wire names are distinct and all its names are
sanitize-stable. -/
theorem weS_le_of_sub {o b : Module} (hi : o.inputs = b.inputs) (ho : o.outputs = b.outputs)
    (hsub : ∀ p ∈ o.wires, p ∈ b.wires) (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs,
      Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (x : String) (hxo : x ∉ b.outputs.map (·.name)) (hxi : x ∉ b.inputs.map (·.name)) :
    Tools.ShippingDesignSV.weS o x ≤ declWidth b x := by
  simp only [Tools.ShippingDesignSV.weS, Tools.ShippingDesignSV.wofOf, Tools.SVParser.EmitSem.weOf,
    Tools.SVParser.RoundtripProof.moduleWof]
  cases hf : (o.wires ++ o.inputs ++ o.outputs).find?
      (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) with
  | none => simp
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpx : Sparkle.Backend.Verilog.sanitizeName p.name = x := by
      have h := List.find?_some hf
      simpa using h
    rw [hi, ho] at hp
    rcases List.mem_append.mp hp with hp' | hpo
    · rcases List.mem_append.mp hp' with hpw | hpi
      · have hpb := hsub p hpw
        have hname : p.name = x :=
          (hs p (List.mem_append_left _ (List.mem_append_left _ hpb))).symm.trans hpx
        have hfd : b.wires.find? (fun q => q.name == x) = some p := by
          rw [← hname]; exact Tools.ShippingEntrySoundness.find?_of_nodup hnd hpb
        simp only [declWidth, hfd]
        obtain ⟨pn, pty⟩ := p
        cases pty <;> simp
      · exact absurd (List.mem_map.mpr ⟨p, hpi,
          (hs p (List.mem_append_left _ (List.mem_append_right _ hpi))).symm.trans hpx⟩) hxi
    · exact absurd (List.mem_map.mpr ⟨p, hpo,
        (hs p (List.mem_append_right _ hpo)).symm.trans hpx⟩) hxo

/-- **The shipped module keeps `b`'s ports and a sub-list of its wires**, whatever branch the
compiler took (instance modules: `hierGate`). -/
theorem checkedOptimize_ports_wires {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true) :
    (Sparkle.IR.OptCheck.checkedOptimize b).inputs = b.inputs ∧
      (Sparkle.IR.OptCheck.checkedOptimize b).outputs = b.outputs ∧
      ∀ p ∈ (Sparkle.IR.OptCheck.checkedOptimize b).wires, p ∈ b.wires := by
  by_cases hbind : Sparkle.IR.RefineCheck.hierBinds b = true
  · rw [Tools.ShippingGuardsSound.checkedOptimize_binding hbind]
    split
    · rename_i hacc
      refine ⟨Tools.ShippingHierShipsSV.hierRefineCheck_inputs hacc, ?_, ?_⟩
      · have h := hacc
        simp only [Sparkle.IR.RefineCheck.hierRefineCheck, Bool.and_eq_true] at h
        obtain ⟨_, hrc⟩ := h
        simpa [Sparkle.IR.HierCheck.openFlat] using (Tools.ShippingRefineSoundness.refineCheck_ports hrc).2
      · intro p hp
        rcases Sparkle.IR.HierCheck.deinline_cases b (Sparkle.IR.Optimize.optimizeModule b) with
          ⟨e, -, -⟩ | e
        · rw [e] at hp
          simp only [Sparkle.IR.HierCheck.deinlineRaw] at hp
          exact (List.mem_filter.mp hp).1
        · rw [e] at hp; exact hp
    · exact ⟨rfl, rfl, fun p hp => hp⟩
  · rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate (by simpa using hbind)]
    exact ⟨rfl, rfl, fun p hp => hp⟩

/-- **The width relation off the ports, for the shipped module** (`weS_le_of_sub` at
`checkedOptimize_ports_wires`). Its premises are facts about `b`'s names: distinct wire names,
sanitize-stable names. -/
theorem weS_checkedOptimize_le {b : Module} (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs,
      Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    ∀ x, x ∉ b.outputs.map (·.name) → x ∉ b.inputs.map (·.name) →
      Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x ≤ declWidth b x := by
  obtain ⟨hi, ho, hsub⟩ := checkedOptimize_ports_wires hgate
  exact weS_le_of_sub hi ho hsub hnd hs

end Tools.ShippingNoPortsTypedI

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
theorem machine_design_noPortsTI
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
            Tools.ShippingHierTyped.BoundOff (declWidth b)
              (b.outputs.map (·.name) ++ b.inputs.map (·.name)) st0 →
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
          -- (writing-time guess, accepted by build ty2 for the original in `Tools.ShippingNoPortsTyped`; this copy built in bo4): `InvN _ 0 child ks` unfolds to `Bounded (weS child) ks.st`
          have h1 : (kids iname).st x < 2 ^ weS child x := hB0 x
          exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (hTK.2.2.2 x hx))
        -- (writing-time guess, accepted by build ty2 for the original in `Tools.ShippingNoPortsTyped`; this copy built in bo4): `KSn _ 0` / `KT 0` against `flatKS` / `KidState` (definitional)
        have hfit := Tools.ShippingNoPortsTypedI.fitX_of_runTypedS (childMap D.modules) b Inv hTy
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
