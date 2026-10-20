import Tools.ShippingGateDesignWalk

variable {tenv : Lean.Environment}

/-! # Gate-route parents, obstacle (A): the harness and the full entry with the design conjunct (worker N, round 11)

WRITTEN, NOT BUILT.

Verbatim copies (generated) of the three harness / full-entry pairs the seven
gate-route parents use — `cone_harness_runKE` / `gate_cone_runGE` (cone over
`cfrag`), `cone_harness_runKCE` / `gate_cone_runGCE` (over `cfragC`),
`cone_harness_runKER` / `gate_cone_runGER` (`LeafKR` leaves) — each with ONE
more conjunct, derived from the SAME run (`mixedHarness_runs`'s translation,
so the child cache `mF` is the cone's): for a design predicate `G` whose
`DesW` (`Tools.ShippingGateDesignWalk`) holds of the instantiated body, and
positive bit-vector binders, the returned core module `M` and core design
`Dd` satisfy `FinalOk G (ofDecl f) M Dd` (`desFinal_of_run`). The old
theorems are kept; premises unchanged (the run, `GateDefines` NOT ALLOWED,
`ChildBnd`). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

section harnessD
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

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **`cone_harness_runKED`**: `cone_harness_runKE` (a copy of its proof; the old theorem is kept)
with the design conjunct: for a design predicate `G`, the body's `DesW`
at every fresh id list gives `FinalOk G` of the returned core module and
design (`desFinal_of_run`). Docstring of the original: **`cone_harness_runK` with the entry conjunct** (a copy of its proof;
the old theorem is kept): every callee whose `EntryWN` holds of the body
instantiated at fresh ids has an entry in the cache `L.val wT'` of the cone. -/
theorem cone_harness_runKED (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesK tenv (L.val wT') declName bs body m ∧
      (∀ mn : Lean.Name,
        (∀ ids : List FVarId, ids.length = bs.length →
          EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, (L.val wT').get? mn = some y) ∧
      ∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
          ids'.length = bs.length →
          DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (Sparkle.IR.ModuleName.ofDecl declName)
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, hty, hm,
    hdd⟩ :=
    mixedHarness_runs L hw hd hr
  have entry : ∀ mn : Lean.Name,
      (∀ ids : List FVarId, ids.length = bs.length →
        EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
      ∃ y : Res, (L.val wT').get? mn = some y :=
    fun mn hE => hE ids len mctx cctx "out" false true _ _ sm0 wire wT wT' rfl hwT hdT htr
  have design : ∀ G : Sparkle.IR.AST.Module → Prop,
      (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
        ids'.length = bs.length →
        DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
            (start (entryCompilerState false cache')
              (Sparkle.IR.ModuleName.ofDecl declName))).context
          G (Sparkle.IR.ModuleName.ofDecl declName)
          (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true) →
      (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
      FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d :=
    fun G hE hpos => desFinal_of_run (hE cache ids nd len) hpos hwT hdT (sub_refl _) htr hst
      hty hm hdd
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, ⟨ids, nd, len, cache, ?_⟩, entry, design⟩
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


/-- **`gate_cone_runGED`**: `gate_cone_runGE` (a copy of its proof; the old theorem is kept)
with the design conjunct: for a design predicate `G` whose `DesW` holds of the
instantiated body (every law witness, positive depth, cache and fresh ids),
the returned core module `M` and core design `Dd` satisfy `FinalOk G`. -/
theorem gate_cone_runGED {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
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
      CacheInv mref cref mF ∧ HierConePreservesK envR mF f bs body M ∧
      (∀ mn : Lean.Name,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 → ∀ ids : List FVarId,
          ids.length = bs.length →
          EntryWN L' D (translateFuelFix (translateStep envR) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, mF.get? mn = some y) ∧
      (∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
          ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
          ids.length = bs.length →
          DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0)
              (bs.zip ids)
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl f))).context
            G (Sparkle.IR.ModuleName.ofDecl f)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl f) M Dd) := by
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
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hcone, hentry, hdes⟩ :=
    cone_harness_runKED (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone,
    fun mn hE => hentry mn (fun ids len => hE L (L.dval wa) hDa ids len),
    fun G hE hpos => hdes G (fun cache ids nd len => hE L (L.dval wa) hDa cache ids nd len)
      hpos⟩


/-- **`cone_harness_runKCED`**: `cone_harness_runKCE` (a copy of its proof; the old theorem is kept)
with the design conjunct: for a design predicate `G`, the body's `DesW`
at every fresh id list gives `FinalOk G` of the returned core module and
design (`desFinal_of_run`). Docstring of the original: **`cone_harness_runKC` with the entry conjunct** (a copy of
`cone_harness_runKE`'s proof over `cfragC`; the old theorems are kept). -/
theorem cone_harness_runKCED (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesKC tenv (L.val wT') declName bs body m ∧
      (∀ mn : Lean.Name,
        (∀ ids : List FVarId, ids.length = bs.length →
          EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, (L.val wT').get? mn = some y) ∧
      ∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
          ids'.length = bs.length →
          DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (Sparkle.IR.ModuleName.ofDecl declName)
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, hty, hm,
    hdd⟩ :=
    mixedHarness_runs L hw hd hr
  have entry : ∀ mn : Lean.Name,
      (∀ ids : List FVarId, ids.length = bs.length →
        EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
      ∃ y : Res, (L.val wT').get? mn = some y :=
    fun mn hE => hE ids len mctx cctx "out" false true _ _ sm0 wire wT wT' rfl hwT hdT htr
  have design : ∀ G : Sparkle.IR.AST.Module → Prop,
      (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
        ids'.length = bs.length →
        DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
            (start (entryCompilerState false cache')
              (Sparkle.IR.ModuleName.ofDecl declName))).context
          G (Sparkle.IR.ModuleName.ofDecl declName)
          (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true) →
      (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
      FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d :=
    fun G hE hpos => desFinal_of_run (hE cache ids nd len) hpos hwT hdT (sub_refl _) htr hst
      hty hm hdd
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, ⟨ids, nd, len, cache, ?_⟩, entry, design⟩
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
    fuel_contractWC L hD translateFuelLimit (L.val wT') hbM hvM
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


/-- **`gate_cone_runGCED`**: `gate_cone_runGCE` (a copy of its proof; the old theorem is kept)
with the design conjunct: for a design predicate `G` whose `DesW` holds of the
instantiated body (every law witness, positive depth, cache and fresh ids),
the returned core module `M` and core design `Dd` satisfy `FinalOk G`. -/
theorem gate_cone_runGCED {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
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
      CacheInv mref cref mF ∧ HierConePreservesKC envR mF f bs body M ∧
      (∀ mn : Lean.Name,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 → ∀ ids : List FVarId,
          ids.length = bs.length →
          EntryWN L' D (translateFuelFix (translateStep envR) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, mF.get? mn = some y) ∧
      (∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
          ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
          ids.length = bs.length →
          DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0)
              (bs.zip ids)
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl f))).context
            G (Sparkle.IR.ModuleName.ofDecl f)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl f) M Dd) := by
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
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hcone, hentry, hdes⟩ :=
    cone_harness_runKCED (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone,
    fun mn hE => hentry mn (fun ids len => hE L (L.dval wa) hDa ids len),
    fun G hE hpos => hdes G (fun cache ids nd len => hE L (L.dval wa) hDa cache ids nd len)
      hpos⟩


/-- **`cone_harness_runKERD`**: `cone_harness_runKER` (a copy of its proof; the old theorem is kept)
with the design conjunct: for a design predicate `G`, the body's `DesW`
at every fresh id list gives `FinalOk G` of the returned core module and
design (`desFinal_of_run`). Docstring of the original: **`cone_harness_runKE` over `LeafKR` leaves** (a copy of its proof; only
the leaf lemma is `leafKR_contractW`). -/
theorem cone_harness_runKERD (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesKR tenv (L.val wT') declName bs body m ∧
      (∀ mn : Lean.Name,
        (∀ ids : List FVarId, ids.length = bs.length →
          EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, (L.val wT').get? mn = some y) ∧
      ∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
          ids'.length = bs.length →
          DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (Sparkle.IR.ModuleName.ofDecl declName)
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, hty, hm,
    hdd⟩ :=
    mixedHarness_runs L hw hd hr
  have entry : ∀ mn : Lean.Name,
      (∀ ids : List FVarId, ids.length = bs.length →
        EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
      ∃ y : Res, (L.val wT').get? mn = some y :=
    fun mn hE => hE ids len mctx cctx "out" false true _ _ sm0 wire wT wT' rfl hwT hdT htr
  have design : ∀ G : Sparkle.IR.AST.Module → Prop,
      (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
        ids'.length = bs.length →
        DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
            (start (entryCompilerState false cache')
              (Sparkle.IR.ModuleName.ofDecl declName))).context
          G (Sparkle.IR.ModuleName.ofDecl declName)
          (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true) →
      (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
      FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d :=
    fun G hE hpos => desFinal_of_run (hE cache ids nd len) hpos hwT hdT (sub_refl _) htr hst
      hty hm hdd
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, ⟨ids, nd, len, cache, ?_⟩, entry, design⟩
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
      (fun j hj fuel => leafKR_contractW L hD (declaredWidths st) (hbK j hj) (hbM j hj) fuel)
      (fun j hj fuel => leafKR_contractW L hD (declaredWidths st) (hvK j hj) (hvM j hj) fuel)
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


/-- **`gate_cone_runGERD`**: `gate_cone_runGER` (a copy of its proof; the old theorem is kept)
with the design conjunct: for a design predicate `G` whose `DesW` holds of the
instantiated body (every law witness, positive depth, cache and fresh ids),
the returned core module `M` and core design `Dd` satisfy `FinalOk G`. -/
theorem gate_cone_runGERD {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
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
      CacheInv mref cref mF ∧ HierConePreservesKR envR mF f bs body M ∧
      (∀ mn : Lean.Name,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 → ∀ ids : List FVarId,
          ids.length = bs.length →
          EntryWN L' D (translateFuelFix (translateStep envR) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, mF.get? mn = some y) ∧
      (∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
          ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
          ids.length = bs.length →
          DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (Tools.ShippingMixedEntrySoundness.prepare (fun _ => false) (fun _ _ => 0)
              (bs.zip ids)
              (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
                (Sparkle.IR.ModuleName.ofDecl f))).context
            G (Sparkle.IR.ModuleName.ofDecl f)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl f) M Dd) := by
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
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hcone, hentry, hdes⟩ :=
    cone_harness_runKERD (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone,
    fun mn hE => hentry mn (fun ids len => hE L (L.dval wa) hDa ids len),
    fun G hE hpos => hdes G (fun cache ids nd len => hE L (L.dval wa) hDa cache ids nd len)
      hpos⟩

end harnessD

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.gate_cone_runGED
#print axioms Tools.ShippingGateParentRun.gate_cone_runGCED
#print axioms Tools.ShippingGateParentRun.gate_cone_runGERD
