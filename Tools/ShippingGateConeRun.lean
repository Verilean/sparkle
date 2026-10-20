import Tools.ShippingGateConeW
import Tools.ShippingGateParentRunG

variable {tenv : Lean.Environment}

/-! # The cone parent at world level: `HierConePreservesK`, `cone_harness_runK`, `gate_cone_runG` (worker N, round 3)

WRITTEN, NOT BUILT.

The S6 cone result `HierConePreserves` with the instance leaves read off the
run's OWN child cache: `HierConePreservesK tenv mF declName bs body m` is
`HierConePreserves` where

* the cone ranges over the fragment `cfrag` (leaves, literals, canonical
  binary operators — `parentMix = childAdd a b + a` is in it);
* every leaf is a `LeafK`: a world-free leaf contract (an input binder, …)
  OR an instance leaf whose child is `mF`'s entry of the callee
  (`InstLeafK`: the child facts are asked of THAT pair only).

`cone_harness_runK`: a returning run of the mixed harness from an invariant
world of positive depth gives `HierConePreservesK tenv (L.val wT') …` for
the world `wT'` in which the translation of the body ended — `mF` is the
child cache at the end of the parent's translation, and every entry is a
`RealChild` (a run of the real full entry on its callee, over these state
references). No `SubSynthDefinesAll`, no `HardwareTagged`.

`gate_cone_runG`: the same from a returning run of the FULL entry
`synthesizeCombinational f` from a `ChildBnd` world under the gate reflection
`GateDefines f bs body` (NOT in the classifier's ALLOWED list, ruling
pending — the round-2 premise): the cleaned module's core `M` has
`HierConePreservesK envR mF f bs body M` at the environment `envR` the entry
read (that read, and the gate's acceptance at it, are in the conclusion: the
tags an instance leaf's `InstLeafK` asks are facts of THAT value). -/
namespace Tools.ShippingGateParentRun
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedEntrySoundness (lookup_of_ports)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingHierTermSoundness (HierValue InstsLinked LeafMeaning initial_link)
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingMixedBinarySoundness (Frame)
open Tools.ShippingChildInv (RefLaws InvV Res CacheInv ChildBnd bodyRel profLogIO)
open Tools.ShippingCacheCoherentRun (SubMap sub_refl)
open Tools.ShippingGateDefines (GateDefines)

set_option linter.unusedSectionVars false

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## The prepared context and state do not depend on the valuation -/

theorem prepare_cs (b1 b2 : FVarId → Bool) (t1 t2 : (id : FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × FVarId)) (a a' : Setup),
      a.context = a'.context → a.state = a'.state →
      (prepare b1 t1 L a).context = (prepare b2 t2 L a').context ∧
        (prepare b1 t1 L a).state = (prepare b2 t2 L a').state
  | [], _, _, hc, hs => ⟨hc, hs⟩
  | ((name, kind), id) :: rest, a, a', hc, hs => by
    cases kind with
    | domain => exact prepare_cs b1 b2 t1 t2 rest a a' hc hs
    | bool =>
      exact prepare_cs b1 b2 t1 t2 rest (extend a ((name, .bool), id) b1 t1)
        (extend a' ((name, .bool), id) b2 t2)
        (by
          show inputContext a.context id (inputWire a.state name.toString .bit) =
            inputContext a'.context id (inputWire a'.state name.toString .bit)
          rw [hc, hs])
        (by
          show inputState a.state name.toString .bit = inputState a'.state name.toString .bit
          rw [hs])
    | bits n =>
      exact prepare_cs b1 b2 t1 t2 rest (extend a ((name, .bits n), id) b1 t1)
        (extend a' ((name, .bits n), id) b2 t2)
        (by
          show inputContext a.context id (inputWire a.state name.toString (.bitVector n)) =
            inputContext a'.context id (inputWire a'.state name.toString (.bitVector n))
          rw [hc, hs])
        (by
          show inputState a.state name.toString (.bitVector n) =
            inputState a'.state name.toString (.bitVector n)
          rw [hs])

/-! ## The output port after the translator (the texts of the built
`emitLeaves_structure_link` / `emitLeaves_runs_link`, over one run's facts) -/

theorem outStructure [Tools.ShippingLinkCtx.LinkCtx] {s sm t : CircuitState} {w : String} {ty : Sparkle.IR.Type.HWType}
    (frame : Frame s sm) (wires : WiresOk s)
    (ht : t = (CircuitM.emitAssign "out" (.ref w) (CircuitM.addOutput "out" ty sm).2).2) :
    DeclGrows s t ∧ WiresOk t := by
  have wm := frame.wires wires
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; rw [ht, emitAssign_wires]; exact frame.decls q hq
  · rw [ht, emitAssign_wires]; exact wm.1
  · intro q hq
    rw [ht, emitAssign_wires] at hq
    have hu := wm.2 q hq
    rw [ht, emitAssign_usedNames, addOutput_state]
    simp [Std.HashSet.contains_insert, hu]

section generic
variable [LinkCtx] [ChildSem]

theorem outRuns {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv}
    {initial prior : Env} {s sm t : CircuitState} {w : String} {ty : Sparkle.IR.Type.HWType}
    {v : Value}
    (step : Outcome ctx inputs we mems initial prior s sm w v)
    (ht : t = (CircuitM.emitAssign "out" (.ref w) (CircuitM.addOutput "out" ty sm).2).2) :
    ∃ result, LinkCtx.Runs we mems initial t result ∧ result "out" = v.toNat ∧
      LinkCtx.Typed we sm := by
  obtain ⟨middle, inv, val, -⟩ := step.execution
  refine ⟨write middle "out" v.toNat, ?_, by simp [write], inv.typed⟩
  rw [ht]
  exact LinkCtx.runs_emit (LinkCtx.runs_body (s := sm) rfl inv.runs)
    (by simpa [evalExpr] using congrArg some val)

end generic

/-! ## The cone result over the run's own child cache -/

/-- **`HierConePreserves` with the instance leaves read off `mF`** (on the
fragment `cfrag`). -/
def HierConePreservesK (tenv : Lean.Environment) (mF : Std.HashMap Lean.Name Res)
    (declName : Lean.Name) (bs : List (Lean.Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (Lean.ExprStructMap String),
    ∀ (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    Separate p.bools p.bits ∧
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bE vE : Nat → Lean.Expr)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (w : Nat) → BitVec w)
      {srt : SType} (e : Term srt),
    e.WF kb kv vw → cfrag e = true →
    (∀ j, j < kb → LeafMeaning C (inputValues p.bools p.bits) (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafMeaning C (inputValues p.bools p.bits) (vE j)
      (.bits (vw j) (vvals j (vw j)))) →
    (∀ j, j < kb → LeafK tenv children C mF p.context (inputValues p.bools p.bits)
      mems initial (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafK tenv children C mF p.context (inputValues p.bools p.bits)
      mems initial (vE j) (.bits (vw j) (vvals j (vw j)))) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body = quote dom bE vE e →
    HierValue children m initial mems (pack srt (eval bvals vvals e)).toNat ∧
      InstsLinked children m

/-- **The cone, from a run of the mixed harness** from an invariant world of
positive depth `D`: the guarantee holds over the child cache `L.val wT'` at
the end of the translation of the body, whose entries are `RealChild`s. -/
theorem cone_harness_runK (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesK tenv (L.val wT') declName bs body m := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, -, hm, -⟩ :=
    mixedHarness_runs L hw hd hr
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, ids, nd, len, cache, ?_⟩
  intro children C bools bits initial mems a p values
  obtain ⟨hpc, hps⟩ := prepare_cs bools (fun _ => false) bits (fun _ _ => 0) (bs.zip ids)
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) rfl rfl
  rw [← hpc, ← hps] at htr
  have empty := empty_layout (entryCompilerState false cache)
    (Sparkle.IR.ModuleName.ofDecl declName) initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  refine ⟨prepared.1.separate prepared.2.1, ?_⟩
  intro dom kb kv vw bE vE bvals vvals srt e he hf hbM hvM hbK hvK qeq
  letI : HierCtx := hierLink children
  letI : ChildSem := C
  rw [qeq] at htr
  have contract : ContractW L (L.val wT') D
      (translateFuelFix (translateStep tenv) translateFuelLimit)
      p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      (quote dom bE vE e) (pack srt (eval bvals vvals e)) :=
    fuel_contractW L hD translateFuelLimit (L.val wT') hbM hvM
      (fun j hj fuel => leafK_contractW L hD (declaredWidths st) (hbK j hj) (hbM j hj) fuel)
      (fun j hj fuel => leafK_contractW L hD (declaredWidths st) (hvK j hj) (hvM j hj) fuel)
      e he hf
  have frame := contract.frame mctx cctx "out" false true p.state sm0 wire wT wT'
    (lookup_of_ports prepared.1 prepared.2.1) hwT hdT (sub_refl _) htr
  obtain ⟨growth, finalWires⟩ := outStructure frame prepared.2.1 hst
  have widths := declaredWidths_agree finalWires
  have inv0 : Inv p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      p.state initial :=
    initial_link prepared.2.2.1 prepared.2.2.2 (prepared.1.inputs prepared.2.1 growth widths)
  have wsm : ScalarWidthsAgree (declaredWidths st) sm0 := by
    intro q hq; apply widths q; rw [hst, emitAssign_wires]; exact hq
  have step := contract.sem mctx cctx "out" false true p.state sm0 wire initial wT wT'
    inv0 wsm hwT hdT (sub_refl _) htr
  obtain ⟨result, evalr, value, typedSm⟩ := outRuns step hst
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  refine ⟨⟨result, ?_, value⟩, ?_⟩
  · rw [moduleWidths_finish wireEq finalWires, bodyEq]
    exact evalr
  · intro mn iname conns hmem
    have hmem' : Stmt.inst mn iname conns ∈ st.module.body := by
      rw [bodyEq] at hmem
      exact List.mem_reverse.mp hmem
    rw [hst, emitAssign_body_cons] at hmem'
    rcases List.mem_cons.mp hmem' with hbad | hmem'
    · cases hbad
    · obtain ⟨child, cwe, hc, hl⟩ := HierCtx.typed_linked typedSm hmem'
      refine ⟨child, cwe, hc, hl.mono ?_ ?_⟩
      · intro q hq
        rw [wireEq, List.mem_reverse, hst, emitAssign_wires]
        exact hq
      · intro q hq
        rw [hm]
        show q ∈ (addClockResetIfSequential st.module).inputs.reverse
        rw [List.mem_reverse]
        exact (addClockReset_facts st.module).2.2.2 q (by rw [hst]; exact hq)

/-- **The cone parent, from a run of the FULL entry** under the gate
reflection (`GateDefines`, NOT ALLOWED until ruled) and `ChildBnd`: the
returned module is the cleaned (possibly merged) core module `M` (same name;
the design is the core's when no module of it is named like `M`); the entry
read `envR` (and the gate accepted the body at it); and `M` has the cone
guarantee over a child cache `mF` of `RealChild`s — the cache at the end of
the parent's translation. -/
theorem gate_cone_runG {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (Dd : Sparkle.IR.AST.Design) (envR : Lean.Environment)
      (a5 a6 : Void IO.RealWorld) (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      b.name = M.name ∧
      ((∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) ∧
      CacheInv mref cref mF ∧ HierConePreservesK envR mF f bs body M := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  obtain ⟨M, Dd, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : Lean.ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (Lean.getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, Dd) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
    by_cases h0 : L.dval w = 0
    · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
        Tools.ShippingCacheCoherentOuter.core_reads_val0 L (fun L' => bodyRel L') hsv hq h0 hcore
      exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
    · rcases hdep with hz | hci
      · exact absurd hz h0
      · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
          Tools.ShippingCacheCoherentVia.core_reads_val L (fun L' => bodyRel L')
            ⟨hci, hsv, hq⟩ h0 hcore
        exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
  obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩ := hreads
  -- the reflection at the run's own reads
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L hold hshape hw3 run
  obtain ⟨wT', hcache, hcone⟩ :=
    cone_harness_runK (tenv := envR) L (D := L.dval wa) (by rw [hda]; exact hd3) hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone⟩

end Tools.ShippingGateParentRun
