import Tools.ShippingGateConeEntry
import Tools.ShippingGateConeRunC

variable {tenv : Lean.Environment}

/-! # Entry existence at a COMPARISON root; the cone over `cfragC` with the entry conjunct (worker N, round 8)

WRITTEN, NOT BUILT.

`EntryWN` (round 6) was proved for a canonical binary root only
(`binary_entryWN`). A comparison `compareE le dom n a b` is NOT routed through
the core: the step hands it to the fallback's Bool arm (`compare_step`,
`translateFallback_bool`), i.e. the validated-cache wrapper
`translateControlCachedWith` around `translateSignalCompare`. On the runs
that skip the lookup (`(!named && !e.isFVar && !top) = false`, the harness
root) the wrapper runs the lowering (operand `a`, operand `b`, one Bool wire
and its assign) and the record; every step keeps the child cache's entries.

* **`compare_entryWN`**: either operand's `EntryW` survives a comparison root
  on the lookup-free runs (the worlds of `compare_contractW`'s miss branch).
* `cone_harness_runKCE` / `gate_cone_runGCE`: verbatim copies of
  `cone_harness_runKE` / `gate_cone_runGE` (round 6) with
  `HierConePreservesK` → `HierConePreservesKC` and `fuel_contractW` →
  `fuel_contractWC` (round 7's `cone_harness_runKC` / `gate_cone_runGC` plus
  the entry conjunct). The originals are unchanged. Premises of
  `gate_cone_runGCE`: the run (ALLOWED), `GateDefines` (NOT ALLOWED, ruling
  pending, unchanged), `ChildBnd` (ALLOWED). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

section entryLemmasC
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx
open Tools.ShippingHierarchySoundness
open Tools.ShippingChildInv (RefLaws InvV J KeepsC Res
  cacheLookupValidated_keepsC recordTranslation_keepsC makeWire_keepsC emitAssign_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **A canonical comparison root, on the runs that skip the lookup, keeps an
operand's entry**: the operand's end cache is contained in the root's end
cache (lowering: operand `a`, operand `b`, `makeWire`, the assign; then the
record). -/
theorem compare_entryWN (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {dom ae be : Lean.Expr} {n : Nat} {le : SignalCompareKind} {mn : Lean.Name}
    (hent : EntryW L D (translateFuelFix (translateStep tenv) fuel) ae mn ∨
      EntryW L D (translateFuelFix (translateStep tenv) fuel) be mn) :
    EntryWN L D (translateFuelFix (translateStep tenv) (fuel + 1))
      (compareE le dom n ae be) mn := by
  intro mctx cctx hint top named ctx s t w w0 w1 hnc hw0 hd0 hr
  change RunsC (translateStepWith (translateFallback tenv)
    (translateFuelFix (translateStep tenv) fuel) (compareE le dom n ae be) hint top named) ctx s
    mctx mref cctx cref w0 (w, t) w1 at hr
  rw [Tools.ShippingMixedRecursion.compare_step,
    translateFallback_bool (translateFuelFix (translateStep tenv) fuel)
      (compareE le dom n ae be) hint top named (by cases le <;> rfl)] at hr
  unfold translateControlCachedWith at hr
  dsimp only at hr
  split at hr
  · -- the lookup branch: excluded (`cacheable = false`)
    rename_i hc
    first
      | (rw [hnc] at hc; simp at hc)
      | simp [hnc] at hc
      | exact absurd hc (by simp [hnc])
  · -- the lowering, then the record
    obtain ⟨r, sm, wl, hl, h3⟩ := RunsC.bind hr
    obtain ⟨u, sr, wr, hrec, h4⟩ := RunsC.bind h3
    obtain ⟨-, hw1⟩ := RunsC.pure h4
    rw [translateBoolUncachedWith_compare] at hl
    unfold translateSignalCompare at hl
    obtain ⟨a, sa, wa1, ra, rest⟩ := RunsC.bind hl
    obtain ⟨b, sb, wb1, rb, re⟩ := RunsC.bind rest
    obtain ⟨hwa1, hda1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hw0 hd0 ra
    obtain ⟨hwb1, hdb1, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa1 hda1 rb
    have reE : RunsC (emitBoolResult (.op (signalCompareOp le) [.ref a, .ref b]) hint named)
        ctx sb mctx mref cctx cref wb1 (r, sm) wl := re
    unfold emitBoolResult at reE
    obtain ⟨r1, s1, wq, rm, rest2⟩ := RunsC.bind reE
    obtain ⟨u2, s2, wq2, rem, fin⟩ := RunsC.bind rest2
    obtain ⟨-, hwq⟩ := RunsC.pure fin
    obtain ⟨hwm, hdm, hs1⟩ :=
      keepsW L (fun L' => makeWire_keepsC L' D hint .bit named) hwb1 hdb1 rm
    obtain ⟨hwq', hdq', hs2⟩ :=
      keepsW L (fun L' => emitAssign_keepsC L' D r1 (.op (signalCompareOp le) [.ref a, .ref b]))
        hwm hdm rem
    rw [← hwq] at hwq' hdq' hs2
    obtain ⟨-, -, hsr⟩ :=
      keepsW L (fun L' => recordTranslation_keepsC L' D (compareE le dom n ae be) r
        (!named && !(compareE le dom n ae be).isFVar && !top)) hwq' hdq' hrec
    have tail : SubMap (L.val wb1) (L.val w1) := by
      rw [hw1]; exact sub_trans hs1 (sub_trans hs2 hsr)
    rcases hent with ha | hb
    · obtain ⟨y, hy⟩ := ha mctx cctx _ _ _ ctx s sa a w0 wa1 hw0 hd0 ra
      exact ⟨y, sub_trans hsab tail mn y hy⟩
    · obtain ⟨y, hy⟩ := hb mctx cctx _ _ _ ctx sa sb b wa1 wb1 hwa1 hda1 rb
      exact ⟨y, tail mn y hy⟩

end entryLemmasC

/-! ## The harness and the full entry over `cfragC`, with the entry conjunct -/

section harnessC
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

/-- **`cone_harness_runKC` with the entry conjunct** (a copy of
`cone_harness_runKE`'s proof over `cfragC`; the old theorems are kept). -/
theorem cone_harness_runKCE (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      HierConePreservesKC tenv (L.val wT') declName bs body m ∧
      ∀ mn : Lean.Name,
        (∀ ids : List FVarId, ids.length = bs.length →
          EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, (L.val wT').get? mn = some y := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, -, hm, -⟩ :=
    mixedHarness_runs L hw hd hr
  have entry : ∀ mn : Lean.Name,
      (∀ ids : List FVarId, ids.length = bs.length →
        EntryWN L D (translateFuelFix (translateStep tenv) translateFuelLimit)
          (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
      ∃ y : Res, (L.val wT').get? mn = some y :=
    fun mn hE => hE ids len mctx cctx "out" false true _ _ sm0 wire wT wT' rfl hwT hdT htr
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, ⟨ids, nd, len, cache, ?_⟩, entry⟩
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

/-- **`gate_cone_runGC` with the entry conjunct** (a copy of
`gate_cone_runGE`'s proof over `cfragC`; the old theorems are kept): every
callee whose `EntryWN` holds of the instantiated body — for every law
witness, every positive depth and every list of fresh ids — HAS an entry in
the cone's child cache `mF`. -/
theorem gate_cone_runGCE {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
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
      ∀ mn : Lean.Name,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 → ∀ ids : List FVarId,
          ids.length = bs.length →
          EntryWN L' D (translateFuelFix (translateStep envR) translateFuelLimit)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) mn) →
        ∃ y : Res, mF.get? mn = some y := by
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
  obtain ⟨wT', hcache, hcone, hentry⟩ :=
    cone_harness_runKCE (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, a5, a6, L.val wT', hpost, hname, hmods, henv, ⟨dv, hshape⟩, hcache, hcone,
    fun mn hE => hentry mn (fun ids len => hE L (L.dval wa) hDa ids len)⟩

end harnessC

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.compare_entryWN
#print axioms Tools.ShippingGateParentRun.gate_cone_runGCE
